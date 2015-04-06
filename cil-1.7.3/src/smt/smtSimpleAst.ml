type variable = string
type intsort = int64

type sort = IntSort | BoolSort

type op = 
| Eq | Leq | Lt  | Geq | Gt | Neq 
| And | Or
| Not
| Add | Mult
| Impl | Ite
    
type term = 
| BoolConst of bool
| IntConst of intsort * sort
| Ident of variable *sort
| App of op * term list * sort
| LinearRelation of op * (intsort * variable) list * intsort

let ocaml_of_op = function
  | Eq -> (=)
  | Leq -> (<=)
  | Lt -> (<)
  | Geq -> (>=)
  | Gt -> (>)
  | Neq -> (<>)
  | _ -> failwith "cannot create ocaml op"

let is_rel = function
  | Eq 
  | Leq 
  | Lt 
  | Geq 
  | Gt
  | Neq -> true
  | _ -> false

let negate_rel = function
  | Eq -> Neq
  | Leq -> Gt
  | Lt -> Geq
  | Geq -> Lt
  | Gt -> Leq
  | Neq -> Eq
  | _ -> failwith "not a relation"

let invert_rel = function
  | Eq  -> Eq
  | Leq -> Geq
  | Lt  -> Gt
  | Geq -> Leq
  | Gt  -> Lt
  | Neq-> Neq
  | _ -> failwith "not a relation"

let string_of_op = function
  | Eq -> "="
  | Leq -> "<="
  | Lt -> "<"
  | Geq -> ">="
  | Gt -> ">"
  | Neq -> "distinct"
  | And -> "and"
  | Or -> "or"
  | Not -> "not"
  | Add -> "+"
  | Mult -> "*"
  | Impl -> "=>"
  | Ite -> "ite"
