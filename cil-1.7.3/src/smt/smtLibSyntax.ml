(** SMT-LIB v2 abstract syntax *)

(** {6 Source position} *)

type source_position = {
    sp_file : string;
    sp_start_line : int;
    sp_start_col : int;
    sp_end_line : int;
    sp_end_col : int;
  }

let dummy_position = 
  { sp_file = "";
    sp_start_line = max_int;
    sp_start_col = max_int;
    sp_end_line = 0;
    sp_end_col = 0 
  }

let global_scope =
  { sp_file = "";
    sp_start_line = 0;
    sp_start_col = 0;
    sp_end_line = max_int; 
    sp_end_col = max_int;
  }

let string_of_src_pos pos =
  if pos.sp_end_line = pos.sp_start_line 
  then 
    Printf.sprintf "File \"%s\", line %d, columns %d-%d" 
      pos.sp_file pos.sp_start_line pos.sp_start_col pos.sp_end_col
  else 
    Printf.sprintf "File \"%s\", line %d, column %d to line %d, column %d" 
      pos.sp_file pos.sp_start_line pos.sp_start_col pos.sp_end_line pos.sp_end_col

let string_of_ident ident = ident

let merge_src_pos pos1 pos2 =
  assert (pos1.sp_file = "" || pos2.sp_file = "" || pos1.sp_file = pos2.sp_file);
  let file = max pos1.sp_file pos2.sp_file in
  let start_line, start_col =
    if pos1.sp_start_line < pos2.sp_start_line 
    then pos1.sp_start_line, pos1.sp_start_col
    else if pos2.sp_start_line < pos1.sp_start_line
    then pos2.sp_start_line, pos2.sp_start_col
    else if pos1.sp_start_col < pos2.sp_start_col
    then pos1.sp_start_line, pos1.sp_start_col
    else pos2.sp_start_line, pos2.sp_start_col
  in
  let end_line, end_col =
    if pos1.sp_end_line > pos2.sp_end_line 
    then pos1.sp_end_line, pos1.sp_end_col
    else if pos2.sp_end_line > pos1.sp_end_line
    then pos2.sp_end_line, pos2.sp_end_col
    else if pos1.sp_end_col > pos2.sp_end_col
    then pos1.sp_end_line, pos1.sp_end_col
    else pos2.sp_end_line, pos2.sp_end_col
  in
  { sp_file = file;
    sp_start_line = start_line;
    sp_start_col = start_col;
    sp_end_line = end_line;
    sp_end_col = end_col;
  }

let in_same_file pos1 pos2 = 
  pos1.sp_file = "" ||
  pos2.sp_file = "" ||
  pos1.sp_file = pos2.sp_file

let starts_before_src_pos pos1 pos2 =
  in_same_file pos1 pos2 &&
  (pos1.sp_start_line < pos2.sp_start_line || 
   pos1.sp_start_line = pos2.sp_start_line && pos1.sp_start_col <= pos2.sp_start_col)
  
let ends_before_src_pos pos1 pos2 =
  in_same_file pos1 pos2 &&
  (pos1.sp_end_line < pos2.sp_end_line || 
  pos1.sp_end_line = pos2.sp_end_line && pos1.sp_end_col <= pos2.sp_end_col)

let contained_in_src_pos pos1 pos2 =
  starts_before_src_pos pos2 pos1 && ends_before_src_pos pos1 pos2    
  
let compare_src_pos pos1 pos2 =
  let cf = compare pos1.sp_file pos2.sp_file in
  if cf <> 0 then cf else
  if starts_before_src_pos pos1 pos2 then
    if starts_before_src_pos pos2 pos1 then 0
    else -1
  else 1


(** {6 Identifiers, sorts, and symbols} *)

(** identifiers *)
type ident = string
type pos = source_position
module IdSet = Set.Make(struct
    type t = ident
    let compare = compare
  end)

module IdMap = Map.Make(struct
    type t = ident
    let compare = compare
  end)

type sort = 
  | IntSort | BoolSort
  | FreeSort of ident * sort list

type symbol =
  | BoolConst of bool
  | IntConst of int
  | Ident of ident
  | Minus | Plus | Mult | Div
  | Eq | Gt | Lt | Geq | Leq | Neq
  | And | Or | Impl | Not | Ite

type annotation =
  | Name of ident

type binder = Exists | Forall

type term =
  | App of symbol * term list * pos option
  | Binder of binder * (ident * sort) list * term * pos option
  | Let of (ident * term) list * term * pos option
  | Annot of term * annotation * pos option

type command =
  | DeclareSort of ident * int * pos option
  | DefineSort of ident * ident list * sort * pos option
  | DeclareFun of ident * sort list * sort * pos option
  | DefineFun of ident * (ident * sort) list * sort * term * pos option
  | Assert of term * pos option

type response =
  | Sat
  | Unsat
  | Unknown
  | Model of command list
  | UnsatCore of string list
  | Error of string

(** Constructor functions *)

let mk_const ?pos sym = App (sym, [], pos)

let mk_app ?pos sym ts = 
  match sym, ts with
  | Minus, [App (IntConst i, [], _)] -> 
      App (IntConst (-i), [], pos)
  | _, _ -> 
      App (sym, ts, pos)

let mk_binder ?pos b vs t = Binder (b, vs, t, pos)

let mk_let ?pos defs t = Let (defs, t, pos)

let mk_annot ?pos t a = Annot (t, a, pos)

let mk_declare_sort ?pos id arity = DeclareSort (id, arity, pos)

let mk_declare_fun ?pos id arg_srts res_srt = DeclareFun (id, arg_srts, res_srt, pos)

let mk_define_sort ?pos id args srt = DefineSort (id, args, srt, pos)

let mk_define_fun ?pos id args res_srt t = DefineFun (id, args, res_srt, t, pos)

let mk_assert ?pos t = Assert (t, pos)

(** Utility functions *)

let idents_in_term t =
  let rec iot acc = function
    | App (sym, ts, _) -> 
        let acc1 = match sym with
        | Ident id -> IdSet.add id acc
        | _ -> acc
        in
        List.fold_left iot acc1 ts
    | Binder (_, vs, t, _) ->
        let acc1 = List.fold_left (fun acc1 (id, _) -> IdSet.add id acc1) acc vs in
        iot acc1 t
    | Let (defs, t, _) ->
        let acc1 = List.fold_left (fun acc1 (id, t) -> iot (IdSet.add id acc1) t) acc defs in
        iot acc1 t
    | Annot (t, _, _) -> iot acc t
  in iot IdSet.empty t

(** Computes the set of identifiers of free variables occuring in term [t]
 ** union the accumulated set of identifiers [vars]. *)
let fv_in_term_acc vars t =
  let rec fvt bvs vars = function
  | App (sym, ts, _) -> 
      let vars1 = match sym with
      | Ident id when not (IdSet.mem id bvs) ->
          IdSet.add id vars
      | _ -> vars
      in
      List.fold_left (fvt bvs) vars1 ts
  | Annot (t, _, _) ->
      fvt bvs vars t
  | Binder (_, vs, t, _) ->
      let bvs1 =
        List.fold_left 
          (fun bvs1 (v, _) -> IdSet.add v bvs1)
          bvs vs 
      in
      fvt bvs1 vars t
  | Let (defs, t, _) ->
      let bvs1, vars1 = 
        List.fold_left (fun (bvs1, vars1) (v, t) ->
          IdSet.add v bvs1, fvt bvs vars1 t)
          (bvs, vars) defs
      in
      fvt bvs vars1 t
  in fvt IdSet.empty vars t

let fv_in_term t = fv_in_term_acc IdSet.empty t

let identIdx = ref 0
(* For now, just be really simple here.  Can be more clever later *)
let fresh_ident s = 
  incr identIdx;
  s ^ (string_of_int !identIdx)

(** Substitutes all free variables in term [t] according to substitution [sm].
 ** Capture avoiding. *)
let subst sm t =
  let rename_vars vs sm =
    let not_bound id _ = not (List.mem_assoc id vs) in
    let sm1 = IdMap.filter not_bound sm in
    let occuring = IdMap.fold (fun _ t acc -> fv_in_term_acc acc t) sm IdSet.empty in
    let vs1, sm2 =
      List.fold_right
	(fun (x, srt) (vs1, sm2) ->
	  if IdSet.mem x occuring
	  then
	    let x1 = fresh_ident x in
	    (x1, srt) :: vs1, IdMap.add x (App (Ident x1, [], None)) sm2
	  else (x, srt) :: vs1, sm2)
	vs ([], sm1)
    in vs1, sm2
  in
  let rec sub sm = function
    | App (Ident id, [], pos) as t ->
        (try IdMap.find id sm
        with Not_found -> t)
    | App (sym, ts, pos) ->
        App (sym, List.map (sub sm) ts, pos)
    | Binder (b, vs, t, pos) ->
        let vs1, sm1 = rename_vars vs sm in
        Binder (b, vs1, sub sm1 t, pos)
    | Let (defs, t, pos) ->
        let vs = List.map (fun (v, _) -> (v, IntSort)) defs in
        let vs1, sm1 = rename_vars vs sm in
        let defs1 = List.map2 (fun (v, _) (_, t) -> (v, sub sm t)) vs1 defs in
        Let (defs1, sub sm1 t, pos)
    | Annot (t, a, pos) ->
        Annot (sub sm t, a, pos)
  in sub sm t

let unletify t =
  let rec ul = function
  | App (sym, ts, pos) ->
      App (sym, List.map ul ts, pos)
  | Binder (b, vs, t, pos) ->
      Binder (b, vs, ul t, pos)
  | Let (defs, t, pos) ->
      let sm =
        List.fold_left (fun sm (v, t) -> IdMap.add v (ul t) sm) IdMap.empty defs
      in
      ul (subst sm t)
  | Annot (t, a, pos) ->
      Annot (ul t, a, pos)
  in ul t

