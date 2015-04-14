type variable = string
module Variable = struct type t=variable let compare = Pervasives.compare end
type intsort = int64

type sort = IntSort | BoolSort
let string_of_sort = function | IntSort -> "Int" | BoolSort -> "Bool"
let string_of_var v = v
module VarSortMap = Map.Make(Variable)
module VarSet = Set.Make(Variable)

type varSortMap = sort VarSortMap.t

type op = 
| Eq | Leq | Lt  | Geq | Gt | Neq 
| And | Or
| Not
| Add | Mult 
| Impl | Ite
    
type term = 
| BoolConst of bool
| IntConst of intsort
| Ident of variable * sort
| App of op * term list * sort
| LinearRelation of op * (intsort * variable) list * intsort

type assertion =  string * term * VarSet.t

let zero = IntConst 0L
let one = IntConst 1L
let minus_one = IntConst (- (1L))

let ocaml_of_op = function
  | Eq -> (=)
  | Leq -> (<=)
  | Lt -> (<)
  | Geq -> (>=)
  | Gt -> (>)
  | Neq -> (<>)
  | _ -> failwith "cannot create ocaml op"

let apply_op op lhs rhs = 
  let ocaml_op = ocaml_of_op op in
  if (ocaml_op lhs rhs) then BoolConst true  else BoolConst false

let is_intconst  = function | IntConst _ -> true  | _ -> false
let is_boolconst = function | BoolConst _ -> true | _ -> false
let is_trueconst = function | BoolConst true -> true | _ -> false
let is_falseconst = function | BoolConst false -> true | _ -> false
let is_ident = function | Ident _ -> true | _ -> false
let is_sum = function | App(Add,_,_) -> true | _ -> false
let is_mult = function | App(Mult,_,_) -> true | _ -> false

let is_relation = function
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

let get_sort = function
  | BoolConst _ -> BoolSort
  | IntConst _ -> IntSort
  | Ident (v,s) -> s
  | App(o,a,s) -> s
  | LinearRelation _ -> BoolSort

let is_boolsort form = (get_sort form) = BoolSort
let is_intsort form = (get_sort form) = IntSort
let sorts_match t1 t2 = (get_sort t1) = (get_sort t2)

let sort_term_list tl = 
  List.sort compare tl


