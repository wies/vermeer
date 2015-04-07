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
| IntConst of intsort
| Ident of variable * sort
| App of op * term list * sort
| LinearRelation of op * (intsort * variable) list * intsort

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

let mk_and terms = 
  assert(List.for_all is_boolsort terms);
  App(And, sort_term_list terms, BoolSort)
let mk_or terms = 
  assert(List.for_all is_boolsort terms);
  App(Or, sort_term_list terms, BoolSort)

let mk_add lst = 
  assert(List.for_all is_intsort lst);
  App(Add,sort_term_list lst,IntSort)
let mk_mult lst =   
  assert(List.for_all is_intsort lst);
  App(Mult,sort_term_list lst,IntSort)

let mk_rel op lhs rhs =
  assert(sorts_match lhs rhs);
  assert(is_relation op);
  App(op, [lhs;rhs], BoolSort)

let mk_ite i t e = 
  assert(is_boolsort i);
  assert(sorts_match t e);
  App(Ite,[i;t;e],get_sort t)

let mk_impl lhs rhs = 
  assert(is_boolsort lhs);
  assert(is_boolsort rhs);
  App(Impl,[lhs;rhs],BoolSort)

let mk_boolConst c = BoolConst c
let mk_intConst c = IntConst c
let rec mk_app o f = 
  match o with 
  | Eq | Leq | Lt  | Geq | Gt | Neq -> (match f with 
    | [t1;t2] -> mk_rel o t1 t2
    | _ -> failwith "wrong args for relation")
  | And -> mk_and f 
  | Or -> mk_or f
  | Not -> (match f with | [t1] -> mk_not t1 | _ -> failwith "bad not")
  | Add -> mk_add f
  | Mult -> mk_mult f
  | Impl -> (match f with |[t1;t2] -> mk_impl t1 t2 | _ -> failwith "bad impl")
  | Ite ->  (match f with |[t1;t2;t3] -> mk_ite t1 t2 t3 | _ -> failwith "bad ite")
and  nnf f = 
  (* shadow the other mk_not to avoid infinite recursion*)
  let mk_not term =  
    assert(is_boolsort term);
    App(Not, [term], BoolSort)
  in
  match f with 
  | App(Not,[l],BoolSort) -> (
    let l = nnf l in 
    match l with
    | App(r,[t1;t2],s) when is_relation r -> mk_rel (negate_rel r) (nnf t1) (nnf t2)
    | App(Not,[f],s) -> nnf f
    | App(And,fs,s) -> mk_or (List.map nnf (List.map mk_not fs))
    | App(Or,fs,s) -> mk_and (List.map nnf  (List.map mk_not fs))
    | BoolConst b -> mk_boolConst (not b)
    | App(Impl,[f1;f2],s) -> mk_or [nnf (mk_not f1); nnf f2]
    | App(Ite, [f1; f2; f3],s) -> 
      mk_or [mk_and [nnf f1; nnf f2]; 
	     mk_and [nnf (mk_not f1); nnf f3]]
    | _ -> failwith "malformed"
  )
  | App(o,f,s) -> mk_app o (List.map nnf f) 
  | IntConst _ | BoolConst _ | Ident _ | LinearRelation _ -> f
and mk_not term = 
  assert(is_boolsort term);
  nnf (App(Not, [term], BoolSort))

let mk_linearRelation op lhs value = 
  LinearRelation (op,lhs,value)
