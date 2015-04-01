open Smtlib_ast
open Smtlib_ast_print
(** Compute negation normal form of a formula *)
let rec nnf = function
  | Not (Relation (rel, t1, t2)) -> Relation (negate_rel rel, t1, t2)
  | Not (LinearRelation (rel, t, c)) -> LinearRelation (negate_rel rel, t, c)
  | Not (Not f) -> nnf f
  | Not (And (fs)) ->
    Or (List.map (function f -> nnf (Not f)) fs)
  | Not (Or (fs)) ->
    And (List.map (function f -> nnf (Not f)) fs)
  | Not True -> False
  | Not False -> True
  | Not (Implication (f1, f2)) -> And [nnf f1; nnf (Not f2)]
  | Not (ITE(f1, f2, f3)) -> And [Or [nnf (Not f1); nnf (Not f2)]; Or [nnf f1; nnf (Not f3)]]
  | And fs -> And (List.map nnf fs)
  | Or fs -> Or (List.map nnf fs)
  | Implication (f1, f2) -> Or [nnf (Not f1); nnf f2]
  | ITE (f1, f2, f3) -> Or [And [nnf f1; nnf f2]; And [nnf (Not f1); nnf f3]]
  | f -> f

let mk_not f =
  nnf (Not f)

let rec normalize_term t = 
  let flatten_nested_mults lst = 
    let fs1, fs2 =  List.partition 
      (fun (f) -> match f with | Mult(_) -> false | _ -> true) lst in
    let fs2_extracted =
      List.map (fun (f) -> match f with | Mult(gs) -> gs | _ -> []) fs2
    in
    List.append fs1 (List.concat fs2_extracted)
  in
  let flatten_nested_sums lst = 
    let fs1, fs2 =  List.partition 
      (fun (f) -> match f with | Sum(_) -> false | _ -> true) lst in
    let fs2_extracted =
      List.map (fun (f) -> match f with | Sum(gs) -> gs | _ -> []) fs2
    in
    List.append fs1 (List.concat fs2_extracted)
  in
  match t with
  (* Handle constants *)
  | Sum [x] -> x
  | Mult [x] -> x
  (* do we want to distribute mults across sums ??? *)
    
  (* Normalize so that sums and mults always have the variable(s) on the left *)
  | Sum(lst) -> 
    let lst = List.map normalize_term lst in
    let (vars,vals,rest) = split_vars_vals lst in
    let vals = simplify_vals vals Int64.add 0L in
    let rest = flatten_nested_sums rest in
    Sum(vars @ vals  @ rest)
  | Mult(lst) -> begin
    let lst = List.map normalize_term lst in
    let (vars,vals,rest) = split_vars_vals lst in
    let vals = simplify_vals vals (Int64.mul) 1L in
    let rest = flatten_nested_mults rest in
    (* distribute multiplication inside addition
     * this opens up more normalization oppertunities *)
    match vars,vals,rest with
    | [],[Value v],[Sum l] -> Sum (List.map (fun x -> Mult [Value v; x]) l)
    | [],[],[] -> Value(1L) (* if there are no values, then it is the identity of Mult, i.e., 1 *)
    | _ -> Mult(vars @ vals  @ rest)
  end
  | Variable _ | Value _ | UnsupportedTerm _ -> t
and simplify_vals vals op identity =
  let v = List.fold_left 
    (fun a x -> match x with 
    | Value v -> op a v
    | _ -> failwith "should be only values here"
    ) identity vals in
  (* If + simplified to 0, then no need to add it.  Same for * and 1 *) 
  if v = identity then []
  else [Value(v)]

(* simplify the term as much as possible *)
(* remove the value to the rhs *)
(* turn to coefficient form *)
(* sort by variable *)
(* combine similar vars to one coefficient *)
(* remove 0 coefficients *)
let normalize_relation op lhs rhs = 
  (* should only be called on terms of the form
   * -x, a*x, or x
   *)
  let convert_to_coeff = function 
    | Variable var -> (1L,var)
    | Mult lst -> begin
      let (vars,vals,rest) = split_vars_vals lst in
      match (vars,vals,rest) with 
      | [Variable var],[Value value],[] -> (value,var)
      | _ -> failwith "cannot convert" 
    end
    | _ -> failwith "cannot convert to coefficient"
  in  
  let simplify_coeff coeffs =
    let sort_coeff = List.sort (fun (c1,v1) (c2,v2) -> compare v1 v2) in
    let rec aux = function
      | [] -> [] 
      | (c1,v1)::(c2,v2)::rest when v1 = v2 -> aux ((Int64.add c1 c2,v1)::rest)
      | a::rest -> a::(aux rest)
    in 
    let coeffs = sort_coeff coeffs in
    let coeffs = aux coeffs in
    let coeffs = List.filter (fun (c,v) -> c <> 0L) coeffs in
    coeffs
  in
  (* returns a sorted, normalized list of coefficients *)
  let get_coeffs tl = 
    let coeffs = List.map convert_to_coeff tl in
    simplify_coeff coeffs
  in
  let remove_common_factors lhs value = 
    let coeffs = List.map (fun (c,v) -> c) lhs in
    let common_factor = list_gcd (value::coeffs) in
    assert(common_factor > 0L);
    if (common_factor <> 1L) then 
      (List.map (fun (c,v) -> (Int64.div c common_factor,v)) lhs, Int64.div value common_factor)
    else 
      (lhs,value)
  in
  (*ensure that the first coefficient has positive polarity*)
  let begin_with_positive op lhs value = 
    match lhs with
    | [] -> LinearRelation(op, lhs, value)
    | _ -> begin
      let (c,v) = List.hd lhs in
      if c < 0L then begin
        let op = invert_rel op in
        let value = Int64.neg value in
        let lhs = List.map (fun (c,v) -> (Int64.neg c,v)) lhs in
        LinearRelation(op,lhs,value)
      end else
        LinearRelation(op,lhs,value)
      end
  in
  let get_value = function 
    | [] -> 0L
    | [Value v] -> v 
    | _ -> failwith "should really have been a value here"
  in
  (*first, move everything interresting to the lhs *)
  (* RHS is implicitly 0 now *)
  let newLHS = Sum[lhs; Mult [Value (Int64.minus_one); rhs]] in
  let newLHS = run_fixpt normalize_term newLHS in
  let linearList,newRHS =  
    match newLHS with 
    | Sum tl -> 
      let (vars,vals,sums,mults,rest) = split_term_list tl in
      assert (sums = []);
      get_coeffs (vars @ mults @ rest), Int64.neg (get_value vals)
    | Value v -> [], Int64.neg v
    | _ -> get_coeffs[newLHS], 0L
  in
  let linearList,newRHS = remove_common_factors linearList newRHS in
  begin_with_positive op linearList newRHS
