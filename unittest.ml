type result = Success | Failure of string | Crash of exn

type t = string * t'
and t' =
  | Test of (unit -> result)
  | List of t list

let fulltest name thunk = (name, Test (fun () -> try thunk() with e -> Crash e))

let test name thunk =
  let testcase () =
    try
      if thunk() then Success else Failure ""
    with
      e -> Crash e
  in 
  (name, Test testcase)

let crashtest name body handler =
  (name, Test(fun () ->
    try
      let _ = body() in Failure ""
    with 
      e -> if handler e then Success else Failure ""))

let group name ts = (name, List ts)

let result out = function
  | Success -> Format.fprintf out "passed"
  | Failure msg -> Format.fprintf out "FAILED: %s" msg
  | Crash e -> Format.fprintf out "CRASH: %s" (Printexc.to_string e)

let rec space out n = if n <= 0 then () else (Format.fprintf out " "; space out (n-1))

let run out t =
  let print fmt = Format.fprintf out fmt in 
  let rec loop n (name, t) =
    let () = space out n in 
    let () = print "%s: " name in 
    match t with 
    | List ts -> print "\n"; List.iter (loop (n+2)) ts
    | Test t  -> (result out (t())); print "\n"
  in
  loop 0 t 


	
