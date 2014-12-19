(* various useful utils can go here *)

open Cil


module Int = struct                       
  type t = int                                              
  let compare x y = if x < y then -1 else if x > y then 1 else 0 end ;;  

(********************* Printing ***********************************)

let errormsg = 0
let warnmsg = 1
let debugmsg = 2
let debugLevel = ref errormsg

let debug_level_endline dl l =  if !debugLevel >= dl then print_endline l
let warn_endline l = debug_level_endline warnmsg l
let debug_endline l =  debug_level_endline debugmsg l
let errormsg_endline l =  debug_level_endline errormsg l


let d_string (fmt : ('a,unit,Pretty.doc,string) format4) : 'a = 
  let f (d: Pretty.doc) : string = 
    Pretty.sprint 800 d
  in
  Pretty.gprintf f fmt 

let print_bars msg str = print_string (msg ^ " |" ^ str ^"|\n")


(************************* utils *************************)
let time f x =
  let start = Unix.gettimeofday () in 
  let res = f x in 
  let stop = Unix.gettimeofday () in 
  let duration = stop -. start in 
  debug_endline ("Execution time: " ^ string_of_float duration);
  (res, duration)

let safe_mkdir name mask = 
  if not (Sys.file_exists name) then Unix.mkdir name mask

let get_basedir () = 
  try Unix.getenv "VERMEER_PATH" 
  with Not_found -> failwith "VERMEER_PATH must be set to the base directory of the repository in your environment"


(************************* list handeling *************************)

let rec sublist b e l = 
  match l with
      [] -> failwith "sublist"
    | h :: t -> 
      let tail = if e=0 then [] else sublist (b-1) (e-1) t in
      if b>0 then tail else h :: tail

(* returns the list split in two.  The left hand side is reversed *)
let split_off_n_reversed n l = 
  let rec helper n l leftAcc = 
    if n <= 0 then Some(leftAcc,l)
    else 
      match l with 
	| [] -> None
	| x::xs -> helper (n-1) xs (x::leftAcc) 
  in
  helper n l [] 

let rec last = function
  | [] -> None
  | [x] -> Some x
  | _ :: t -> last t;;

let all_but_last lst = 
  List.rev  (List.tl (List.rev lst))

let split_last l = 
  let r = List.rev l in
  (List.rev (List.tl r), List.hd r)

(* could be made tailrec *)
let rec compress = function
  | a :: (b :: _ as t) -> if a = b then compress t else a :: compress t
  | smaller -> smaller


(********************* Printing ***********************************)
let get_fn_name = function
  | Call(lv_o, e, al, _) -> d_string "%a" d_exp e
  | _ -> failwith "not a call!"

let is_assert_fnname = function
  | "assert" | "dsn_assert" | "assume" -> true
  | _ -> false
    
let is_assert_fn f = is_assert_fnname (get_fn_name f)
  
let assert_is_assert f = 
  let fname = (get_fn_name f) in
  if not (is_assert_fnname fname) then  
    failwith ("shouldn't have non-assert calls in a concrete trace: " ^ fname)

let d_labels (l : label list) : string = 
  List.fold_left (fun a x -> a ^ (d_string "%a" d_label x)) "" l
