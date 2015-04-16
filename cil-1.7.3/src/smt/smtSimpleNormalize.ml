open SmtSimpleAst
open SmtSimpleAstBuilder
open Smtlib_util
(** Compute negation normal form of a formula *)

(* tries to make a linear relation. 
 * Throws if it cannot*)
(* simplify the term as much as possible *)
(* remove the value to the rhs *)
(* turn to coefficient form *)
(* sort by variable *)
(* combine similar vars to one coefficient *)
(* remove 0 coefficients *)
let rec make_linear_relation op lhs rhs = 
  (* should only be called on terms of the form
   * -x, a*x, or x
   *)
  (* returns a sorted, normalized list of coefficients *)
  let get_coeffs tl = 
    let convert_to_coeff = function 
      | Ident (var,IntSort) -> (1L,var)
      | App(Mult,lst,IntSort) -> (
	let (vars,rest) = List.partition is_ident lst in
	let vals,rest = List.partition is_intconst rest in
	match (vars,vals,rest) with 
	| [Ident (var,IntSort)],[IntConst value],[] -> (value,var)
	| _ -> failwith "cannot convert" 
      )
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
    | [] -> mk_linearRelation op lhs value
    | (c,v)::rest -> (
      if c < 0L then (
        let op = invert_rel op in
        let value = Int64.neg value in
        let lhs = List.map (fun (c,v) -> (Int64.neg c,v)) lhs in
	mk_linearRelation op lhs value
      ) else
	mk_linearRelation op lhs value
    )
  in
  let get_value = function 
    | [] -> 0L
    | [IntConst v] -> v 
    | _ -> failwith "should really have been a value here"
  in
  (*first, move everything interresting to the lhs *)
  (* RHS is implicitly 0 now *)
  let newLHS = mk_add [lhs; mk_uminus rhs] in
  let newLHS = run_fixpt normalize_term newLHS in
  let linearList,newRHS =  
    match newLHS with 
    | App(Add,tl,_) -> 
      let sums,rest = List.partition is_sum tl in
      assert (sums = []);
      let vals,rest = List.partition is_intconst rest in
      get_coeffs (rest), Int64.neg (get_value vals)
    | IntConst v -> [], Int64.neg v
    | _ -> get_coeffs[newLHS], 0L
  in
  let linearList,newRHS = remove_common_factors linearList newRHS in
  begin_with_positive op linearList newRHS
    
and normalize_term t = 
  let simplify_vals vals op identity =
    let v = List.fold_left 
      (fun a x -> match x with 
      | IntConst v -> op a v
      | _ -> failwith "should be only values here"
      ) identity vals in
    mk_intConst v
  in
  let flatten_nested op lst = 
    List.flatten 
      (List.map 
	 (function
	 | App (o,f,s) when o = op -> f
	 | f -> [f]) 
	 lst)
  in 
  let rec aux = function
    (* Handle constants *)
    | LinearRelation(op,[],v) -> apply_op op 0L v
    | BoolConst _ | IntConst _ | Ident _ | LinearRelation _ as f -> f
    (* 0 list length *)
    | App(And,[],_) -> BoolConst true
    | App(Or,[],_) -> BoolConst false
    | App(Mult,[],_)|App(Add,[],_) -> failwith "didn't expect this"
    (* 1 list length *)
    | App(Add,[x],_) | App(Mult,[x],_) | App(And,[x],_) | App(Or,[x],_) -> aux x
    (* n list length*)
    | App(Add,lst,_) -> 
      let lst = List.map aux lst in
      let lst = flatten_nested Add lst in
      let vals,rest = List.partition is_intconst lst in
      let value = simplify_vals vals Int64.add 0L in
      mk_add (value::rest)
    | App(Mult,lst,_) -> (
      let lst = List.map aux lst in
      let lst = flatten_nested Mult lst in
      let vals,rest = List.partition is_intconst lst in
      let value = simplify_vals vals Int64.mul 1L in
      (* now, distribute the mult across adds, if possible *)
      match rest with 
      | [App (Add,al,_)] -> mk_add (List.map (fun x -> mk_mult [value;x]) al)
      | _ -> mk_mult (value::rest)
    )
    | App(And,lst,_) -> (
      let lst = List.map aux lst in
      let lst = flatten_nested And lst in
      if (List.exists is_falseconst lst) then
	mk_boolConst false
      else (
	let lst = List.filter (fun x -> not (is_boolconst x)) lst in
	mk_and lst	  
      )
    )
    | App(Or,lst,_) -> (
      let lst = List.map aux lst in
      let lst = flatten_nested Or lst in
      if (List.exists is_trueconst lst) then
	mk_boolConst true
      else (
	let lst = List.filter (fun x -> not (is_boolconst x)) lst in
	mk_or lst	  
      )
    )
    | App(Not,_,_)  | App(Ite,_,_) | App(Impl,_,_) as f -> nnf f
    | App(op,[lhs;rhs],_) as f when is_relation op -> 
      let lhs = aux lhs in
      let rhs = aux rhs in
      if (is_intsort lhs && is_intsort rhs) then
	try make_linear_relation op lhs rhs 
	with _ -> failwith ("can't make relation out of " ^ SmtSimpleFns.string_of_term f)
(*mk_rel op lhs rhs*)
      else
	mk_rel op lhs rhs
    | t -> failwith ("malformed term: " ^ SmtSimpleFns.string_of_term t)
  in run_fixpt aux t
