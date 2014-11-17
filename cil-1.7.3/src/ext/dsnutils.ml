(* various useful utils can go here *)

(************************* utils *************************)
let time f x =
  let start = Unix.gettimeofday ()
  in let res = f x
     in let stop = Unix.gettimeofday ()
	in let () = Printf.printf "Execution time: %fs\n%!" (stop -. start)
	   in
	   flush stdout; res

let safe_mkdir name mask = 
  if not (Sys.file_exists name) then Unix.mkdir name mask

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

let d_string (fmt : ('a,unit,Pretty.doc,string) format4) : 'a = 
  let f (d: Pretty.doc) : string = 
    Pretty.sprint 800 d
  in
  Pretty.gprintf f fmt 

let print_bars msg str = print_string (msg ^ " |" ^ str ^"|\n")
