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
let list_sorts_match lst = 
  let rec f = function
    | [] -> true
    | [x] -> true
    | x::y::rest -> 
      if (not (sorts_match x y)) then false
      else f (y::rest)
  in f lst
 
let compare_lex compare_fn fs gs = 
  let rec aux fs gs = 
    match fs, gs with
    | f :: fs1, g :: gs1 ->
      let c = compare_fn f g in
      if c = 0
      then aux fs1 gs1
      else c
    | [], _ :: _ -> -1
    | _ :: _, [] -> 1
    | _, _ -> 0
  in
  aux fs gs

let compare_coeffs (c1,v1) (c2,v2) = 
  match compare v1 v2 with
  | 0 -> compare c1 c2
  | x -> x

let rec compare_term t1 t2 = 
  match t1,t2 with
  | BoolConst b1, BoolConst b2 -> compare b1 b2
  | IntConst i1, IntConst i2 -> compare i1 i2
  | Ident (v1,s1), Ident (v2,s2) -> 
    (match compare v1 v2 with
    | 0 -> compare s1 s2
    | x -> x
  )  
  | App (o1,t1,s1), App(o2,t2,s2) -> 
    (match compare o1 o2 with
    | 0 -> (match compare_lex compare_term t1 t2 with
      | 0 -> compare s1 s2
      | x -> x
    )
    | x -> x
  )
  | LinearRelation(o1,l1,r1),LinearRelation(o2,l2,r2) -> 
    (* we want to make sure that thing with similar lists end up side by side *)       
    (match compare_lex compare_coeffs l1 l2 with
    | 0 -> (match compare 01 02 with 
      | 0 -> compare r1 r2
      | x -> x
    )
    | x -> x
    )
  | _,_ -> compare t1 t2
  

let sort_term_list tl = 
  List.sort compare_term tl


