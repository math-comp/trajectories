(** link code **)

open Js_of_ocaml
open Add

let rec n2pos n = if n < 2 then XH else 
                  if n mod 2 == 0 then 
                  XO (n2pos (n / 2)) else XI (n2pos (n / 2))

let rec pos2n n = 
  match n with XH -> 1 | XO n -> 2 * (pos2n n) | XI n -> 2 * (pos2n n) + 1

let n2z n = if n = 0 then Z0 else 
            if 0 < n then Zpos (n2pos n)
            else Zneg (n2pos n)

let z2n n = match n with
| Z0 -> 0
| Zpos n -> pos2n n
| Zneg n -> - pos2n n

let string2lr s =
  let le = String.length s in
  let rec iter i si vi = if i = le then Nil else
    let v = String.get s i in 
    if (v == '-') then iter (i + 1) (-1) vi else
    if (v == '+') then iter (i + 1) (1) vi else
    if (v == ' ') then Cons (n2z (si * vi), iter (i + 1) 1 0) else
    iter (i + 1) si (vi * 10 + (Char.code v - 48)) in
  iter 0 1 0

let rec string2lr1 l = 
match l with 
| Cons (n , Cons (Z0, l)) -> Cons ({qnum = n; qden = XH}, (string2lr1 l))
| Cons (n, Cons (Zpos d, l)) -> Cons ({qnum = n; qden = d}, (string2lr1 l))
| _ -> Nil

let string2l s = string2lr1 (string2lr s)

let rec l2stringr s l =
  match l with
    Nil -> s
  | Cons (n,l) ->  l2stringr (s ^ (string_of_int (z2n n.qnum)) ^ " " ^
                                  (string_of_int (pos2n n.qden)) ^ " ")
                             l

let l2string l = l2stringr "" l

let main s =
  let l = string2l s in l2string (sum_val l)

let _ =
  Js.export_all
    (object%js
      method add s = Js.string (main (Js.to_string s))
    end)

