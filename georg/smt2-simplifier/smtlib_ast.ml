
type term = 
| Variable of string
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
| ITE of formula * formula * formula
| UnsupportedFormula of string
;; 

let mk_not_rel = function
  | EQ -> NEQ
  | LEQ -> GT
  | LT -> GEQ
  | GEQ -> LT
  | GT -> LEQ
  | NEQ -> EQ

let rec nnf = function
  | Not (Relation (rel, t1, t2)) -> Relation (mk_not_rel rel, t1, t2)
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
