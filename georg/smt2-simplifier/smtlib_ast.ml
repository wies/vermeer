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

let op_of_rel = function
  | EQ -> (=)
  | LEQ -> (<=)
  | LT -> (<)
  | GEQ -> (>=)
  | GT -> (>)
  | NEQ -> (<>)

let apply_op op lhs rhs = 
  let ocaml_op = op_of_rel op in
  if (ocaml_op lhs rhs) then True else False

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
  if a = 0 || b = 0 then 
    1
  else 
    let open Big_int in
    let result = int_of_big_int (gcd_big_int (big_int_of_int a) (big_int_of_int b)) in
    assert (result > 0);
    result

(* assumes that the list has length >1 *)
let list_gcd = function
  | [] -> 1
  | [x] -> abs(x)
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
    (fun x -> match x with | Variable _ -> true | _ -> false) tl in
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
