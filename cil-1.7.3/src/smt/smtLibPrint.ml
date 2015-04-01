(** Abstract syntax tree for GRASS formulas (a sorted first-order logic) *)

open Util

(** {6 Source position} *)

type source_position = {
    sp_file : string;
    sp_start_line : int;
    sp_start_col : int;
    sp_end_line : int;
    sp_end_col : int;
  }


(** {6 Identifiers, sorts, and symbols} *)

(** identifiers *)
type ident = string * int

module IdSet = Set.Make(struct
    type t = ident
    let compare = compare
  end)

module IdMap = Map.Make(struct
    type t = ident
    let compare = compare
  end)

(** sorts *)
type sort =
  | Bool | Loc | Int (** basic sorts *)
  | Set of sort (** sets *)
  | Map of sort * sort (** maps *)
  | FreeSrt of ident (** uninterpreted sorts *)

module IdSrtSet = Set.Make(struct
    type t = ident * sort
    let compare = compare
  end)

module SortSet = Set.Make(struct
    type t = sort
    let compare = compare
  end)

module SortMap = Map.Make(struct
    type t = sort
    let compare = compare
  end)

type sorted_ident = ident * sort

type arity = sort list * sort

(** symbols *)
type symbol =
  (* interpreted constant symbols *)
  | BoolConst of bool
  | IntConst of int
  (* interpreted function symbols *)
  | Null | Read | Write | EntPnt
  | UMinus | Plus | Minus | Mult | Div 
  | Empty | SetEnum | Union | Inter | Diff
  (* interpreted predicate symbols *)
  | Eq
  | LtEq | GtEq | Lt | Gt
  | Btwn | Frame
  | Elem | SubsetEq 
  (* uninterpreted constants, functions, and predicates *)
  | FreeSym of ident

let symbols = 
  [BoolConst true; BoolConst false; 
   Null; Read; Write; EntPnt;
   UMinus; Plus; Minus; Mult;
   Empty; SetEnum; Union; Inter; Diff;
   Eq; LtEq; GtEq; Lt; Gt;
   Btwn; Frame; Elem; SubsetEq]

module SymbolSet = Set.Make(struct
    type t = symbol
    let compare = compare
  end)

module SymbolMap = Map.Make(struct
    type t = symbol
    let compare = compare
  end)

module SortedSymbolMap = Map.Make(struct
    type t = symbol * arity
    let compare = compare
  end)

type signature = arity SymbolMap.t

(** {6 Terms and formulas} *)

(** terms *)
type term = 
  | Var of ident * sort
  | App of symbol * term list * sort

type subst_map = term IdMap.t

module TermSet = Set.Make(struct
    type t = term
    let compare = compare
  end)

module TermMap = Map.Make(struct
    type t = term
    let compare = compare
  end)

(** filters for term generators *)
type filter =
  | FilterTrue
  | FilterNotOccurs of symbol
  | FilterGeneric of (subst_map -> term -> bool)

(** matching guards for term generators *)
type guard =
  | Match of term * filter
  
(** annotations *)
type annot =
  | Comment of string
  | SrcPos of source_position
  | ErrorMsg of source_position * string
  | Label of ident
  | Name of ident
  | TermGenerator of sorted_ident list * sorted_ident list * guard list * term

(** Boolean operators *)
type bool_op =
  | And | Or | Not

(** quantifiers *)
type binder =
  | Forall | Exists

(** GRASS formulas *)
type form =
  | Atom of term * annot list
  | BoolOp of bool_op * form list
  | Binder of binder * (ident * sort) list * form * annot list

module FormSet = Set.Make(struct
    type t = form
    let compare = compare
  end)

(** {6 Pretty printing} *)

(** {5 SMT-LIB 2 Notation} **)

open Format

let string_of_src_pos pos =
  if pos.sp_end_line = pos.sp_start_line 
  then 
    Printf.sprintf "File \"%s\", line %d, columns %d-%d" 
      pos.sp_file pos.sp_start_line pos.sp_start_col pos.sp_end_col
  else 
    Printf.sprintf "File \"%s\", line %d, column %d to line %d, column %d" 
      pos.sp_file pos.sp_start_line pos.sp_start_col pos.sp_end_line pos.sp_end_col

let string_of_ident0 (name, n) =
  Printf.sprintf "%s_%d" name n

let string_of_ident (name, n) =
  if n = 0 then name else
  Printf.sprintf "%s_%d" name n

let string_of_symbol = function
  (* function symbols *)
  | BoolConst b -> Printf.sprintf "%b" b
  | IntConst i -> string_of_int i
  | Null -> "null"
  | Read -> 
      if !Config.encode_fields_as_arrays 
      then "select"
      else "read"
  | Write -> 
      if !Config.encode_fields_as_arrays 
      then "store"
      else "write"
  | EntPnt -> "ep"
  | UMinus -> "-"
  | Plus -> "+"
  | Minus -> "-"
  | Mult -> "*"
  | Div -> "div"
  | Empty -> "emptyset"
  | SetEnum -> "singleton"
  | Union -> "union"
  | Inter -> "intersection"
  | Diff -> "setminus"
  (* predicate symbols *)
  | Eq -> "="
  | LtEq -> "<="
  | GtEq -> ">="
  | Lt -> "<"
  | Gt -> ">"
  | Btwn -> "Btwn"
  | Elem -> "member"
  | SubsetEq -> "subset"
  | Frame -> "Frame"
  (* uninterpreted symbols *)
  | FreeSym id -> string_of_ident id

let pr_ident ppf id = fprintf ppf "%s" (string_of_ident id)

let rec pr_ident_list ppf = function
  | [] -> ()
  | [id] -> pr_ident ppf id
  | id :: ids -> fprintf ppf "%a,@ %a" pr_ident id pr_ident_list ids

let loc_sort_string = "Loc"
let map_sort_string = "Map"
let set_sort_string = "Set"
let bool_sort_string = "Bool"
let int_sort_string = "Int"

let rec pr_sort0 ppf srt = match srt with
  | Loc | Bool | Int -> fprintf ppf "%a" pr_sort srt
  | FreeSrt id -> pr_ident ppf id
  | _ -> fprintf ppf "@[<1>%a@]" pr_sort srt
  (*| _ -> fprintf ppf "@[<1>(%a)@]" pr_sort srt*)

and pr_sort ppf = function
  | Loc -> fprintf ppf "%s" loc_sort_string
  | Bool -> fprintf ppf "%s" bool_sort_string
  | Int -> fprintf ppf "%s" int_sort_string
  | FreeSrt id -> pr_ident ppf id
  | Map (d, r) -> fprintf ppf "@[<4>(%s@ %a %a)@]" map_sort_string pr_sort0 d pr_sort0 r
  | Set s -> fprintf ppf "@[<4>(%s@ %a)@]" set_sort_string pr_sort0 s

let pr_sym ppf sym = fprintf ppf "%s" (string_of_symbol sym)

let rec pr_term ppf = function
  | Var (id, _) -> fprintf ppf "%a" pr_ident id
  | App (Empty as sym, [], srt) -> fprintf ppf "(as@ %a@ %a)" pr_sym sym pr_sort0 srt
  | App (sym, [], _) -> fprintf ppf "%a" pr_sym sym
  | App (sym, ts, _) -> fprintf ppf "@[<2>(%a@ %a)@]" pr_sym sym pr_terms ts

and pr_terms ppf = function
  | [] -> ()
  | [t] -> fprintf ppf "%a" pr_term t
  | t :: ts -> fprintf ppf "%a@ %a" pr_term t pr_terms ts

let rec pr_term_list ppf = function
  | [] -> ()
  | [t] -> pr_term ppf t
  | t :: ts -> fprintf ppf "%a,@ %a" pr_term t pr_term_list ts
      
let pr_binder ppf b =
  let b_str = match b with
  | Forall -> "forall"
  | Exists -> "exists"
  in 
  fprintf ppf "%s" b_str

let pr_boolop ppf op =
  let op_str = match op with
  | And -> "and"
  | Or -> "or"
  | Not -> "not"
  in 
  fprintf ppf "%s" op_str

let pr_var ppf (x, srt) =
  fprintf ppf "@[<1>(%a@ %a)@]" pr_ident x pr_sort0 srt

let rec pr_vars ppf = function
  | [] -> ()
  | [v] -> fprintf ppf "%a" pr_var v
  | v :: vs -> fprintf ppf "%a@ %a" pr_var v pr_vars vs

let extract_name smt ann =
  let names = Util.filter_map 
      (function Name _ -> Config.named_assertions && true | _ -> false) 
      (function Name id -> string_of_ident id | _ -> "")
      ann 
  in
  if smt 
  then Str.global_replace (Str.regexp " ") "_" (String.concat "_" (List.rev names))
  else String.concat "; " (List.rev names)

let rec extract_src_pos = function
  | SrcPos pos :: _ -> Some pos
  | _ :: ann -> extract_src_pos ann
  | [] -> None  

let rec pr_form ppf = function
  | Binder (b, vs, f, a) -> 
      let name = extract_name true a in
      (match name with
      |	"" -> fprintf ppf "%a" pr_quantifier (b, vs, f)
      |	n -> fprintf ppf "@[<3>(! %a@ @[:named@ %s@])@]" pr_quantifier (b, vs, f) n)
  | Atom (t, a) -> 
      let name = extract_name true a in
      (match name with
      | "" -> fprintf ppf "%a" pr_term t
      | n -> fprintf ppf "@[<3>(! %a@ @[:named@ %s@])@]" pr_term t n)
  | BoolOp (And, []) -> fprintf ppf "%s" "true"
  | BoolOp (Or, []) -> fprintf ppf "%s" "false"
  | BoolOp (Or, fs) -> fprintf ppf "@[<4>(%a@ %a)@]" pr_boolop Or pr_forms fs
  | BoolOp (op, fs) -> fprintf ppf "@[<5>(%a@ %a)@]" pr_boolop op pr_forms fs

and pr_quantifier ppf = 
  let rec is_pattern below_app = function
    | App (_, ts, _) -> List.exists (is_pattern true) ts
    | Var _ -> below_app
  in
  let rec find_patterns acc = function
    | BoolOp (_, fs) ->
        List.fold_left find_patterns acc fs
    | Binder (_, _, f, _) -> find_patterns acc f
    | Atom (App (_, ts, _), _) ->
        let pts = List.filter (is_pattern false) ts in
        List.fold_left (fun acc t -> TermSet.add t acc) acc pts
    | Atom _ -> acc
  in
  let fvt t =
    let rec fvt1 vars = function
      | Var (id, _) -> IdSet.add id vars
      | App (_, ts, _) -> List.fold_left fvt1 vars ts
    in fvt1 IdSet.empty t
  in
  function
  | (_, [], f) -> fprintf ppf "%a" pr_form f
  | (b, vs, f) -> 
      let fun_patterns = find_patterns TermSet.empty f in
      let patterns =
        let pvs = 
          TermSet.fold 
            (fun t pvs -> IdSet.union (fvt t) pvs)
            fun_patterns IdSet.empty
        in 
        List.fold_left
          (fun patterns (id, srt) ->
            if IdSet.mem id pvs 
            then patterns 
            else TermSet.add (Var (id, srt)) patterns)
          fun_patterns vs
      in
      if not !Config.smtpatterns && !Config.instantiate || TermSet.is_empty patterns
      then fprintf ppf "@[<8>(%a@ @[<1>(%a)@]@ %a)@]" pr_binder b pr_vars vs pr_form f
      else 
        fprintf ppf "@[<8>(%a@ @[<1>(%a)@]@ @[<3>(! %a@ @[:pattern@ (%a)@])@])@]" 
          pr_binder b pr_vars vs pr_form f pr_terms (TermSet.elements patterns)


and pr_forms ppf = function
  | [] -> ()
  | [t] -> fprintf ppf "%a" pr_form t
  | t :: ts -> fprintf ppf "%a@ %a" pr_form t pr_forms ts


let print_smtlib_sort out_ch s = pr_sort (formatter_of_out_channel out_ch) s
let print_smtlib_term out_ch t = fprintf (formatter_of_out_channel out_ch) "%a@?" pr_term t
let print_smtlib_form out_ch f =  fprintf (formatter_of_out_channel out_ch) "@[<8>%a@]@?" pr_form f

let string_of_smtlib_sort s = pr_sort str_formatter s; flush_str_formatter ()

(** Print term [t] to out channel [out_chan]. *)
let print_term out_ch t = fprintf (formatter_of_out_channel out_ch) "%a@?" pr_term t

(** Print formula [f] to out channel [out_chan]. *)
let print_form out_ch f = fprintf (formatter_of_out_channel out_ch) "%a@?" pr_form f


(** {5 Infix Notation} *)

let rec pr_sort ppf = function
  | Loc -> fprintf ppf "%s" loc_sort_string
  | Bool -> fprintf ppf "%s" bool_sort_string
  | Int -> fprintf ppf "%s" int_sort_string
  | FreeSrt id -> pr_ident ppf id
  | Map (d, r) -> fprintf ppf "%s<@[%a,@ %a@]>" map_sort_string pr_sort d pr_sort r
  | Set s -> fprintf ppf "%s<@[%a@]>" set_sort_string pr_sort s
		
let pr_var ppf (x, srt) =
  fprintf ppf "@[%a: %a@]" pr_ident x pr_sort srt

let rec pr_vars ppf = function
  | [] -> ()
  | [v] -> pr_var ppf v
  | v :: vs -> fprintf ppf "%a,@ %a" pr_var v pr_vars vs 

let rec pr_term0 ppf t =
  match t with
  | App (sym, _, _) ->
      (match sym with
      | Diff | Union | Inter | Plus | Minus | Mult | Div -> 
          fprintf ppf "(%a)" pr_term t
      | _ -> pr_term ppf t)
  | _ -> pr_term ppf t

and pr_term ppf = function
  | Var (id, _) -> fprintf ppf "%a" pr_ident id
  | App (Empty, _, _) -> fprintf ppf "{}"
  | App (sym, [], _) -> fprintf ppf "%a" pr_sym sym
  | App (Read, [map; t], _) -> fprintf ppf "%a.%a" pr_term t pr_term map
  | App (Write, [map; t1; t2], _) -> fprintf ppf "%a[%a := %a]" pr_term map pr_term t1 pr_term t2
  | App (Minus, [t1; t2], _) -> fprintf ppf "%a - @[<2>%a@]" pr_term0 t1 pr_term0 t2
  | App (Plus, [t1; t2], _) -> fprintf ppf "%a + @[<2>%a@]" pr_term0 t1 pr_term0 t2
  | App (Mult, [t1; t2], _) -> fprintf ppf "%a * @[<2>%a@]" pr_term0 t1 pr_term0 t2
  | App (Div, [t1; t2], _) -> fprintf ppf "%a / @[<2>%a@]" pr_term0 t1 pr_term0 t2
  | App (Diff, [t1; t2], _) -> fprintf ppf "%a -- @[<2>%a@]" pr_term0 t1 pr_term0 t2
  | App (Inter, ss, _) -> pr_inter ppf ss
  | App (Union, ss, _) -> pr_union ppf ss
  | App (Eq, [t1; t2], _) -> fprintf ppf "@[%a@] == @[<2>%a@]" pr_term t1 pr_term t2
  | App (SubsetEq, [t1; t2], _)
  | App (LtEq, [t1; t2], _) -> fprintf ppf "%a <= @[<2>%a@]" pr_term t1 pr_term t2
  | App (GtEq, [t1; t2], _) -> fprintf ppf "%a >= @[<2>%a@]" pr_term t1 pr_term t2
  | App (Lt, [t1; t2], _) -> fprintf ppf "%a < @[<2>%a@]" pr_term t1 pr_term t2
  | App (Gt, [t1; t2], _) -> fprintf ppf "%a > @[<2>%a@]" pr_term t1 pr_term t2
  | App (Elem, [t1; t2], _) -> fprintf ppf "@[%a@] in @[<2>%a@]" pr_term t1 pr_term t2
  | App (SetEnum, ts, _) -> fprintf ppf "{@[%a@]}" pr_term_list ts
  | App (sym, ts, _) -> fprintf ppf "%a(@[%a@])" pr_sym sym pr_term_list ts

and pr_term_list ppf = function
  | [] -> ()
  | [t] -> pr_term ppf t
  | t :: ts -> fprintf ppf "%a,@ %a" pr_term t pr_term_list ts

and pr_inter ppf = function
  | [] -> fprintf ppf "Univ"
  | [App (Diff, _, _) as s] -> 
      fprintf ppf "(@[%a@])" pr_term s
  | [s] -> pr_term ppf s
  | App (Inter, ss1, _) :: ss2 -> 
      pr_inter ppf (ss1 @ ss2)
  | (App (Union, _, _) as s) :: ss 
  | (App (Diff, _, _) as s) :: ss -> 
      fprintf ppf "(@[<2>%a@]) ** %a" pr_term s pr_inter ss
  | s :: ss -> 
      fprintf ppf "@[<2>%a@] ** %a" pr_term s pr_inter ss

and pr_union ppf = function
  | [] -> fprintf ppf "{}"
  | [App (Diff, _, _) as s] -> 
      fprintf ppf "(@[%a@])" pr_term s
  | [s] -> pr_term ppf s
  | (App (Diff, _, _) as s) :: ss -> 
      fprintf ppf "(@[<2>%a@]) ++ %a" pr_term s pr_union ss
  | s :: ss -> 
      fprintf ppf "@[<2>%a@] ++ %a" pr_term s pr_union ss

let rec pr_form ppf = function
  | Binder (b, vs, f, a) -> 
      fprintf ppf "@[(%a%a)@]" pr_quantifier (b, vs, f) pr_annot a
  | BoolOp (And, fs) -> pr_ands ppf fs
  | BoolOp (Or, fs) -> pr_ors ppf fs
  | BoolOp (Not, [f]) -> pr_not ppf f
  | BoolOp (_, _) -> ()
  | Atom (t, []) -> fprintf ppf "@[%a@]" pr_term t
  | Atom (t, a) -> fprintf ppf "@[(%a%a)@]" pr_term t pr_annot a
      
and pr_annot ppf a =
  let name = extract_name false a in
  let pos = extract_src_pos a in
  (match name, pos with
  | "", None -> fprintf ppf ""
  | "", Some pos -> fprintf ppf "@ /* %s */" (string_of_src_pos pos)
  | n, Some pos -> fprintf ppf "@ /* %s: %s */" (string_of_src_pos pos) n
  | n, None -> fprintf ppf "@ /* %s */" n)
 

and pr_ands ppf = function
  | [] -> fprintf ppf "%s" "true"
  | [f] -> fprintf ppf "@[<2>%a@]" pr_form f
  | (BoolOp (Or, _) as f) :: fs -> fprintf ppf "(@[<2>%a@]) &&@ %a" pr_form f pr_ands fs
  | f :: fs -> fprintf ppf "@[<2>%a@] &&@ %a" pr_form f pr_ands fs

and pr_ors ppf = function
  | [] -> fprintf ppf "%s" "false"
  | [f] -> fprintf ppf "@[<2>%a@]" pr_form f
  | f :: fs -> fprintf ppf "@[<2>%a@] ||@ %a" pr_form f pr_ors fs

and pr_not ppf = function
  | Atom (App (Eq, [t1; t2], _), a) ->
      fprintf ppf "@[(@[%a@]@ !=@ @[<2>%a@]%a)@]" pr_term t1 pr_term t2 pr_annot a
  | Atom (App (Elem, [t1; t2], _), a) ->
      fprintf ppf "@[(@[%a@]@ !in@ @[<2>%a@]%a)@]" pr_term t1 pr_term t2 pr_annot a
  | Atom (App (_, [], _), _) as f -> 
      fprintf ppf "!@[%a@]" pr_form f
  | f -> fprintf ppf "!(@[%a@])" pr_form f

and pr_quantifier ppf = function
  | (_, [], f) -> fprintf ppf "%a" pr_form f
  | (b, vs, f) -> fprintf ppf "@[<2>%a @[%a@] ::@ %a@]" pr_binder b pr_vars vs pr_form f


and pr_forms ppf = function
  | [] -> ()
  | [t] -> fprintf ppf "%a" pr_form t
  | t :: ts -> fprintf ppf "%a@ %a" pr_form t pr_forms ts


let string_of_sort s = pr_sort0 str_formatter s; flush_str_formatter ()

let string_of_term t = 
  let margin = pp_get_margin str_formatter () in
  pp_set_margin str_formatter 9999;
  pr_term str_formatter t; 
  let res = flush_str_formatter () in
  pp_set_margin str_formatter margin;
  res

let string_of_form f = 
  pr_form str_formatter f; 
  flush_str_formatter ()

let print_forms ch fs = 
  List.iter (fun f -> print_form ch f;  output_string ch "\n") fs
  
let print_subst_map subst_map =
  Printf.printf "[";
  IdMap.iter (fun id t -> Printf.printf "  %s -> %s\n" (string_of_ident id) (string_of_term t)) subst_map;
  print_endline "]"
