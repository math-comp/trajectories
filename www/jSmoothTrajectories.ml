(** link code **)

open Js_of_ocaml
open SmoothTrajectories

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

let n2q n d = {qnum = n2z n; qden = n2pos d}

let q2n v =
let v1 = qred v in  [z2n v1.qnum; pos2n v1.qden]

let n2pt n1 d1 n2 d2 = {p_x = n2q n1 d1; p_y = n2q n2 d2}

let pt2n p = (q2n p.p_x) @ (q2n p.p_y)

let n2edge n1 d1 n2 d2 n3 d3 n4 d4 = 
  if (n1 <= n3) then
  { left_pt = n2pt n1 d1 n2 d2; right_pt = n2pt n3 d3 n4 d4}
  else 
  { left_pt = n2pt n3 d3 n4 d4; right_pt = n2pt n1 d1 n2 d2}
  
let edge2n e = (pt2n e.left_pt) @ (pt2n e.right_pt)

let string2ln s =
  let le = String.length s in
  let rec iter i si vi = if i = le then [] else
    let v = String.get s i in 
    if (v == '-') then iter (i + 1) (-1) vi else
    if (v == '+') then iter (i + 1) (1) vi else
    if (v == ' ') then (si * vi) :: iter (i + 1) 1 0 else
    iter (i + 1) si (vi * 10 + (Char.code v - 48)) in
  iter 0 1 0

let rec list2es l = 
  match l with
  | en1 :: ed1 :: en2 :: ed2 :: en3 :: ed3 :: en4 :: ed4 :: l1
    ->
      Cons (n2edge en1 ed1 en2 ed2 en3 ed3 en4 ed4, list2es l1)
  | [] -> Nil


let annotated_point2n ap = pt2n ap.apt_val
    
let curve_element2n ce =
  match ce with
| Straight (ap1, ap2) -> 1 :: 0 :: (annotated_point2n ap1 @ annotated_point2n ap2)
| Bezier (ap1, ap2, ap3) ->
    2 :: 0 :: (annotated_point2n ap1 @ annotated_point2n ap2 @ annotated_point2n ap3)

let rec curve_elements2n ces =
  match ces with
  |  Cons (ce, ces1) -> curve_element2n ce @ curve_elements2n ces1 
  |  Nil -> []

let rec l2stringr l =
  match l with
    [] -> ""
  | a :: l1 -> if (0 <= a) then 
               ("+" ^ (string_of_int a) ^ " " ^ l2stringr l1)
               else 
               ((string_of_int a) ^ " " ^ l2stringr l1)

let call_smooth s = 
  let l = string2ln s in
  match l with
  | p1n1 :: p1d1 :: p1n2 :: p1d2 :: p2n1 :: p2d1 :: p2n2 ::p2d2 ::
    e1n1 :: e1d1 :: e1n2 :: e1d2 :: e1n3 :: e1d3 :: e1n4 :: e1d4 ::
    e2n1 :: e2d1 :: e2n2 :: e2d2 :: e2n3 :: e2d3 :: e2n4 :: e2d4 ::
    ls ->
    let es = list2es ls in 
    let v = qsmooth_point_to_point (n2edge e1n1 e1d1 e1n2 e1d2 e1n3 e1d3 e1n4 e1d4)
      (n2edge e2n1 e2d1 e2n2 e2d2 e2n3 e2d3 e2n4 e2d4)
      es 
      (n2pt p1n1 p1d1 p1n2 p1d2)
      (n2pt p2n1 p2d1 p2n2 p2d2) in 
    l2stringr (curve_elements2n v)


let call_straight s = 
  let l = string2ln s in
  match l with
  | p1n1 :: p1d1 :: p1n2 :: p1d2 :: p2n1 :: p2d1 :: p2n2 ::p2d2 ::
    e1n1 :: e1d1 :: e1n2 :: e1d2 :: e1n3 :: e1d3 :: e1n4 :: e1d4 ::
    e2n1 :: e2d1 :: e2n2 :: e2d2 :: e2n3 :: e2d3 :: e2n4 :: e2d4 ::
    ls ->
    let es = list2es ls in 
    let v = qstraight_point_to_point (n2edge e1n1 e1d1 e1n2 e1d2 e1n3 e1d3 e1n4 e1d4)
      (n2edge e2n1 e2d1 e2n2 e2d2 e2n3 e2d3 e2n4 e2d4)
      es 
      (n2pt p1n1 p1d1 p1n2 p1d2)
      (n2pt p2n1 p2d1 p2n2 p2d2) in 
    l2stringr (curve_elements2n v)


let rec cells_element2n ce =
  match ce with
  | Nil -> []
  | Cons (a, Nil) -> []
  | Cons (a, Cons (b, Nil)) -> pt2n a @ pt2n b
  | Cons (a, Cons (b, c)) -> cells_element2n (Cons (a, c))
  
let rec cells_elements2n ces =
  match ces with
  |  Cons (ce, ces1) -> cells_element2n (ce.left_pts) @ cells_elements2n ces1 
  |  Nil -> []

let call_cells s = 
  let l = string2ln s in
  match l with
  | e1n1 :: e1d1 :: e1n2 :: e1d2 :: e1n3 :: e1d3 :: e1n4 :: e1d4 ::
    e2n1 :: e2d1 :: e2n2 :: e2d2 :: e2n3 :: e2d3 :: e2n4 :: e2d4 ::
    ls ->
    let es = list2es ls in 
    let v = qedges_to_cells (n2edge e1n1 e1d1 e1n2 e1d2 e1n3 e1d3 e1n4 e1d4)
      (n2edge e2n1 e2d1 e2n2 e2d2 e2n3 e2d3 e2n4 e2d4)
      es  in 
    l2stringr (cells_elements2n v)

let _ =
  Js.export "ocamlLib"
    (object%js
      method straight s = Js.string (call_straight (Js.to_string s))
      method smooth s = Js.string (call_smooth (Js.to_string s))
      method cells s = Js.string (call_cells (Js.to_string s))
    end)
