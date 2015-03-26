type variable = string

type term = 
| Variable of variable
| Value of int 
| Sum of term list
| Mult of term list
| UMinus of term
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

let print_relation rel = 
  print_string " ";
  print_string (string_of_relation rel);
  print_string " "
  
let relation_of_linearrelation op lhs rhs= 
  let mults = List.map (fun (coeff,var) ->
    match coeff with 
    | -1 -> UMinus (Variable var)
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

