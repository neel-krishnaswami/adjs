type printer' = int -> int -> out_channel -> int 

let p   = Printf.fprintf
let len = String.length

let spaces n out = for i = 0 to n-1 do p out " " done

let nl' n col out         = (p out "\n"; spaces n out; n)
let nil' n col out        = col 
let str' s                = if String.contains s '\n'
                            then assert false
                            else fun n col out -> (p out "%s" s; col + len s)
let int' x                = str' (string_of_int x)
let float' x              = str' (string_of_float x)
let bool' b               = str' (string_of_bool b)
let qstr' s               = str' (Printf.sprintf "\"%s\"" (String.escaped s))
let atcol' p _ col out    = p col col out 
let indent' k p n col out = p (n+k) col out
let sequence p1 p2 n col out  = p2 n (p1 n col out) out 
let seq' ps = List.fold_right sequence ps nil' 

type printer = bool * printer'

let nl              = (true, nl')
let nil             = (false, nil')
let str s           = (false, str' s)
let int x           = (false, int' x)
let float x         = (false, float' x)
let bool b          = (false, bool' b)
let qstr s          = (false, qstr' s)
let atcol (b, p)    = (b, atcol' p)
let indent k (b, p) = (b, indent' k p)
let (>>) (b1,p1) (b2,p2) = (b1 || b2, sequence p1 p2)
let seq bps         = List.fold_right (>>) bps nil 
let break b         = if b then nl else str " "

let multiline (b, p) = b 

let print (_, p) out = let _ = p 0 0 out in ()


















