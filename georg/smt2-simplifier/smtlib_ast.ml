type variable = string

type term = 
| Variable of variable
| Value of int 
| Sum of term list
| Mult of term list
| UnsupportedTerm of string
(* division, subtraction? *)
;;

type binop = | EQ | LEQ | LT  | GEQ | GT | NEQ 

type formula = 
| True
| False
| Not of formula
| And of formula list
| Or of formula list
| Implication of formula * formula
(* relations: *)
| Relation of binop * term * term
| LinearRelation of binop * (int * variable) list * int
| ITE of formula * formula * formula
| Boolvar of string
| UnsupportedFormula of string
;; 

let negate_rel = function
  | EQ -> NEQ
  | LEQ -> GT
  | LT -> GEQ
  | GEQ -> LT
  | GT -> LEQ
  | NEQ -> EQ

let invert_rel = function
  | EQ  -> EQ 
  | LEQ -> GEQ
  | LT  -> GT
  | GEQ -> LEQ
  | GT  -> LT
  | NEQ -> NEQ

let string_of_relation = function
  | EQ  -> "=" 
  | LEQ -> "<="
  | LT  -> "<"
  | GEQ -> ">="
  | GT  -> ">"
  | NEQ -> "!="

let gcd a b =
  let open Big_int in
  int_of_big_int (gcd_big_int (big_int_of_int a) (big_int_of_int b))

(* assumes that the list has length >1 *)
let list_gcd = function
  | [] -> 1
  | [x] -> x
  | lst -> List.fold_left gcd (List.hd lst) lst

let rec run_fixpt fn term = 
  let newTerm = fn term in
  if newTerm = term 
  then term 
  else run_fixpt fn newTerm

let sort_vars = List.sort 
  (fun x y -> match x,y with 
  | Variable x, Variable y -> compare x y
  | _ -> failwith "not a var???")

(*Could make this slightly faster but who cares *)
let split_term_list tl = 
  let (vars,rest) = List.partition 
    (fun x -> match x with | Variable _ -> true | _ -> false) tl in
  let vars = sort_vars vars in
  let (vals,rest) = List.partition
    (fun x -> match x with  Value _ -> true | _ -> false) rest in
  let (sums,rest)  = List.partition
    (fun x -> match x with  Sum _ -> true | _ -> false) rest in
  let (mults,rest)  = List.partition
    (fun x -> match x with  Mult _ -> true | _ -> false) rest in
  (vars,vals,sums,mults,rest)

let split_vars_vals tl : (term list * term list * term list)= 
  let (vars,rest) = List.partition 
    (fun x -> match x with | Variable _ | _ -> false) tl in
  let vars = sort_vars vars in
  let (vals,rest) = List.partition
    (fun x -> match x with  Value _ -> true | _ -> false) rest in
  (vars,vals,rest)


let print_relation rel = 
  print_string " ";
  print_string (string_of_relation rel);
  print_string " "
    
let relation_of_linearrelation op lhs rhs= 
  let mults = List.map (fun (coeff,var) ->
    match coeff with 
    | 0 -> failwith "shouldn't have 0 coefficients"
    | 1 -> Variable var
    | x -> Mult[Value x; Variable var]) lhs
  in
  Relation(op,Sum mults,Value rhs)
(* todo could normalize here to something more readable *)

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
    let vals = simplify_vals vals (+) 0 in
    let rest = flatten_nested_sums rest in
    Sum(vars @ vals  @ rest)
  | Mult(lst) -> begin
    let lst = List.map normalize_term lst in
    let (vars,vals,rest) = split_vars_vals lst in
    let vals = simplify_vals vals ( * ) 1 in
    let rest = flatten_nested_mults rest in
    (* distribute multiplication inside addition
     * this opens up more normalization oppertunities *)
    match vars,vals,rest with
    | [],[Value v],[Sum l] -> Sum (List.map (fun x -> Mult [Value v; x]) l)
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
    | Variable var -> (1,var)
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
      | (c1,v1)::(c2,v2)::rest when v1 = v2 -> aux ((c1+c2,v1)::rest)
      | a::rest -> a::(aux rest)
    in 
    let coeffs = sort_coeff coeffs in
    let coeffs = aux coeffs in
    let coeffs = List.filter (fun (c,v) -> c <> 0) coeffs in
    coeffs
  in
  (* returns a sorted, normalized list of coefficients *)
  let get_coeffs tl = 
    let coeffs = List.map convert_to_coeff tl in
    simplify_coeff coeffs
  in
  (*ensure that the first coefficient has positive polarity*)
  let begin_with_positive op lhs value = 
    let (c,v) = List.hd lhs in
    if c < 0 then begin
      let op = negate_rel op in
      let value = -value in
      let lhs = List.map (fun (c,v) -> (-c,v)) lhs in
      LinearRelation(op,lhs,value)
    end else
      LinearRelation(op,lhs,value)
  in
  let get_value = function 
    | [] -> 0
    | [Value v] -> v 
    | _ -> failwith "should really have been a value here"
  in
  (*first, move everything interresting to the lhs *)
  (* RHS is implicitly 0 now *)
  let newLHS = Sum[lhs; Mult [Value (-1); rhs]] in
  let newLHS = run_fixpt normalize_term newLHS in
  let linearList,newRHS =  
    match newLHS with 
    | Sum tl -> 
      let (vars,vals,sums,mults,rest) = split_term_list tl in
      assert (sums = []);
      get_coeffs (vars @ mults @ rest), get_value vals
    | _ -> get_coeffs[newLHS], 0
  in
  begin_with_positive op linearList newRHS


let rec print_formula f indentation =
  match f with
  | Boolvar s -> print_string (indentation ^ s ^ "\n")
  | True -> print_string(indentation ^ "TRUE\n")
  | False -> print_string(indentation ^ "FALSE\n")
  | Not(g) -> print_string(indentation ^ "NOT (\n"); print_formula g (indentation ^ "  "); print_string(indentation ^ ")\n")
  | And(fs) -> print_string(indentation ^ "AND (\n"); List.iter (fun (f2) -> print_formula f2 (indentation ^ "  ")) fs; print_string(indentation ^ ")\n")
  | Or(fs) -> print_string(indentation ^ "OR (\n"); List.iter (fun (f2) -> print_formula f2 (indentation ^ "  ")) fs; print_string(indentation ^ ")\n")
  | Implication(f1, f2) -> print_string(indentation ^ "IMPLICATION (\n"); print_formula f1 (indentation ^ "  "); print_formula f2 (indentation ^ "  "); print_string(indentation ^ ")\n")
  | Relation(rel,t1,t2) -> 
    print_string indentation; 
    print_term t1; 
    print_relation rel;
    print_term t2;
    print_newline ()
  | LinearRelation(op,lst,value) ->
    print_formula (relation_of_linearrelation op lst value) indentation
  | ITE(f_cond, f_then, f_else) -> 
    print_string(indentation ^ "IF (\n");
    print_formula f_cond (indentation ^ "  ");
    print_string(indentation ^ ") THEN (\n");
    print_formula f_then (indentation ^ "  ");
    print_string(indentation ^ ") ELSE (\n");
    print_formula f_else (indentation ^ "  ");
    print_string(indentation ^ ")\n")
  | UnsupportedFormula(s) -> print_string(indentation ^ "UNSUPPORTED FORMULA: " ^ s ^ "\n")
and
    print_term t = 
  match t with
  | Variable(s) -> print_string(s)
  | Value(v) -> print_int(v)
  | Sum([ t1 ]) -> print_term t1
  | Sum(t1 :: ts) -> print_string("("); print_term t1; print_string(" + "); print_term (Sum(ts)); print_string(")")
  | Mult [ t1 ]  -> print_term t1
  | Mult(t1 :: ts) -> print_string("("); print_term t1; print_string(" * "); print_term (Mult(ts)); print_string(")")
  | UnsupportedTerm(s) -> print_string("UNSUPPORTED TERM: [" ^ s ^ "]")
  | _ -> print_string("*print_term_TODO*")  

