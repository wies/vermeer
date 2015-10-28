open Xml

let run () = 
  (try
    let x = (Xml.parse_string "<bla>hello</bla>")
    in 
      print_endline (Xml.to_string_fmt x)
  with
    | Xml.Error msg as e -> Printf.printf "Xml error: %s\n" (Xml.error msg)
  )
    
let () = run()
