open SmtSimpleAst

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
let mk_uminus t = mk_mult [minus_one;t]

let mk_minus t = 
  match t with 
  | [t1] -> mk_uminus t1
  | [t1;t2] -> mk_add [t1;mk_uminus t2]
  | _ -> failwith ("minus with wrong number of ops " ^ string_of_int (List.length t))

let mk_rel op lhs rhs =
  assert(sorts_match lhs rhs);
  assert(is_relation op);
  App(op, [lhs;rhs], BoolSort)

let mk_eq lhs rhs = mk_rel Eq lhs rhs

let mk_ite i t e = 
  assert(is_boolsort i);
  assert(sorts_match t e);
  App(Ite,[i;t;e],get_sort t)

let mk_impl lhs rhs = 
  assert(is_boolsort lhs);
  assert(is_boolsort rhs);
  App(Impl,[lhs;rhs],BoolSort)

let mk_boolConst c = BoolConst c
let mk_true = mk_boolConst true
let mk_false = mk_boolConst false
let mk_intConst c = IntConst c
let mk_ident v s = Ident(v,s)

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
    | Ident _ -> f
    | App(r,[t1;t2],s) when is_relation r -> mk_rel (negate_rel r) (nnf t1) (nnf t2)
    | App(Not,[f],s) -> nnf f
    | App(And,fs,s) -> mk_or (List.map nnf (List.map mk_not fs))
    | App(Or,fs,s) -> mk_and (List.map nnf  (List.map mk_not fs))
    | BoolConst b -> mk_boolConst (not b)
    | _ -> failwith ("malformed: " ^ SmtSimpleFns.string_of_term l)
  )
  | App(Impl,[f1;f2],s) -> mk_or [nnf (mk_not f1); nnf f2]
  | App(Ite, [f1; f2; f3],s) -> 
    mk_or [mk_and [nnf f1; nnf f2]; 
	   mk_and [nnf (mk_not f1); nnf f3]]
  | App(o,f,s) -> mk_app o (List.map nnf f) 
  | IntConst _ | BoolConst _ | Ident _ | LinearRelation _ -> f
and mk_not term = 
  assert(is_boolsort term);
  nnf (App(Not, [term], BoolSort))

let mk_linearRelation op lhs value = 
  LinearRelation (op,lhs,value)

let relation_of_linearrelation op lhs rhs=
  let mults = List.map (fun (coeff,var) ->
    match coeff with
    | 0L -> failwith "shouldn't have 0 coefficients"
    | 1L -> mk_ident var IntSort
    | x -> mk_mult [mk_intConst x; mk_ident var IntSort]
  ) lhs 
  in
  mk_rel op (mk_add mults) (mk_intConst rhs)

let cast_to_bool f = 
  match get_sort f with
  | IntSort -> mk_rel Neq f zero
  | BoolSort -> f

let cast_to_int f = 
  match get_sort f with   
  | IntSort -> f
  | BoolSort -> mk_ite f one zero
