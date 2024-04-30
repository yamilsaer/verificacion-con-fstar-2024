module Clase6.BST

open FStar.Mul
open FStar.List.Tot
open FStar.Ghost

let max (x y : int) : int = if x > y then x else y

type bst0 =
  | L
  | N of bst0 & int & bst0

let rec all_lt (x: int) (t: bst0) : GTot bool =
  match t with
  | L -> true
  | N (l, y, r) -> all_lt x l && y < x && all_lt x r

let rec all_gt (x: int) (t: bst0) : GTot bool =
  match t with
  | L -> true
  | N (l, y, r) -> all_gt x l && y > x && all_gt x r

let rec is_bst (t: bst0) : GTot bool =
  match t with
  | L -> true
  | N (l, x, r) -> is_bst l && is_bst r && all_lt x l && all_gt x r

type bst = b:bst0{is_bst b}

let rec insert0 (x: int) (t: bst0) : bst0 =
  match t with
  | L -> N (L, x, L)
  | N (l, y, r) ->
    (* Nota: NO admite duplicados *)
    if x = y then t
    else if x < y then N (insert0 x l, y, r)
    else N (l, y, insert0 x r)

let rec insert0_all_lt (x:int) (t:bst0) (y:int)
  : Lemma (requires all_lt y t /\ x < y)
          (ensures all_lt y (insert0 x t))
= match t with
  | L -> ()
  | N (l, z, r) ->
    insert0_all_lt x l y;
    insert0_all_lt x r y

let rec insert0_all_gt (x:int) (t:bst0) (y:int)
  : Lemma (requires all_gt y t /\ x > y)
          (ensures all_gt y (insert0 x t))
= match t with
  | L -> ()
  | N (l, _, r) ->
    insert0_all_gt x l y;
    insert0_all_gt x r y

    
let rec insert0_bst (x:int) (t:bst0) : Lemma (requires is_bst t) (ensures is_bst (insert0 x t)) =
  match t with
  | L -> ()
  | N (l, y, r) ->
    if x < y then (
      insert0_bst x l;
      insert0_all_lt x l y)
    else if x > y then (
      insert0_bst x r;
      insert0_all_gt x r y)
    else ()

let insert (x:int) (t:bst) : bst =
  insert0_bst x t;
  insert0 x t

(* Nota: al usar GTot nos aseguramos que esta función sólo se usa
en contextos de especificación, y nunca en código ejecutable. ¿Hay otras
funciones que pueden marcarse así? *)
let rec in_tree (x:int) (t:bst0) : GTot bool =
  match t with
  | L -> false
  | N (l, y, r) ->
    x = y || in_tree x l || in_tree x r

let rec member (x: int) (t: bst) : bool =
  match t with
  | L -> false
  | N (l, y, r) ->
    if x < y then member x l
    else if x > y then member x r
    else true

let rec in_tree_r (x y:int) (t:bst0) 
  : Lemma (requires all_gt y t /\ x <= y)(ensures not (in_tree x t))
= match t with
  | L -> ()
  | N (l, _, r) ->
    in_tree_r x y l;
    in_tree_r x y r

let rec in_tree_l (x y:int) (t:bst0)
  : Lemma (requires all_lt y t /\ x >= y)(ensures not (in_tree x t))
= match t with
  | L -> ()
  | N (l, _, r) ->
    in_tree_l x y l;
    in_tree_l x y r

let rec member_ok (x:int) (t:bst) : Lemma (member x t == in_tree x t) =
  match t with
  | L -> ()
  | N (l, y, r) ->
    if x < y then (
      member_ok x l;
      in_tree_r x y r
      )
    else if x > y then (
      member_ok x r;
      in_tree_l x y l
    )
    else ()


let rec to_list (t: bst) : list int =
  match t with
  | L -> []
  | N (l, x, r) -> to_list l @ [x] @ to_list r

let rec from_list (l: list int) : bst =
  match l with
  | [] -> L
  | x :: xs -> insert x (from_list xs)

let rec size (t: bst) : nat =
  match t with
  | L -> 0
  | N (l, _, r) -> 1 + size l + size r

let rec height (t: bst) : nat =
  match t with
  | L -> 0
  | N (l, _, r) -> 1 + max (height l) (height r)

let rec insert_size (x:int) (t:bst) : Lemma (size (insert x t) <= 1 + size t) =
  match t with
  | L -> ()
  | N (l, y, r) ->
    insert_size x l;
    insert_size x r

let rec insert_height (x:int) (t:bst)
: Lemma (height t <= height (insert x t) /\ height (insert x t) <= 1 + height t)
= match t with
  | L -> ()
  | N (l, y, r) ->
    insert_height x l;
    insert_height x r

let rec insert_mem (x:int) (t:bst) : Lemma (member x (insert x t)) =
  match t with
  | L -> ()
  | N (l, y, r) ->
    if x <= y
    then insert_mem x l
    else insert_mem x r
  
let rec all_lt_trans (x y : int) (t : bst0) : Lemma (requires all_lt x t /\ y >= x) (ensures all_lt y t) =
  match t with
  | L -> ()
  | N (l, _, r) ->
    all_lt_trans x y l;
    all_lt_trans x y r

let rec all_gt_trans (x y : int) (t : bst0) : Lemma (requires all_gt x t /\ y <= x) (ensures all_gt y t) =
  match t with
  | L -> ()
  | N (l, _, r) ->
    all_gt_trans x y l;
    all_gt_trans x y r

// NB: cambiado para fortalecer la precondición, y no devolver una opción.
let rec extract_min0 (t: bst0{N? t}) : int & bst0 =
  match t with
  | N (L, x, r) -> (x, r)
  | N (l, x, r) ->
    let (min, l') = extract_min0 l in
    let t : bst0 = N (l', x, r) in
    (min, t)

let rec extract_min_preserva_all_lt (y:int) (t : bst0{N? t})
  : Lemma (requires is_bst t /\ all_lt y t)
          (ensures all_lt y (snd (extract_min0 t)) /\ y > fst (extract_min0 t))
= match t with
  | N (L, x, r) -> ()
  | N (l, x, r) -> extract_min_preserva_all_lt y l

let rec extract_min_preserva_all_gt (y:int) (t : bst0{N? t})
  : Lemma (requires is_bst t /\ all_gt y t)
          (ensures all_gt y (snd (extract_min0 t)) /\ y < fst (extract_min0 t))
= match t with
  | N (L, x, r) -> ()
  | N (l, x, r) -> extract_min_preserva_all_gt y l

let rec extract_min_es_bst (t:bst0{N? t})
: Lemma (requires is_bst t)
        (ensures is_bst (snd (extract_min0 t)))
= match t with
  | N (L, x, r) -> ()
  | N (l, x, r) ->
    extract_min_es_bst l; 
    extract_min_preserva_all_lt x l

let extract_min (t: bst{N? t}) : (int & bst) =
  extract_min_es_bst t;
  let (min,t') = extract_min0 t in (min,t')

let rec extract_min_ok (t: bst{N? t})
  : Lemma (ensures all_gt (fst (extract_min0 t)) (snd (extract_min0 t)))
= match t with
  | N (L, x, r) -> ()
  | N (l, x, r) -> 
    extract_min_ok l;
    extract_min_es_bst l;
    all_gt_trans x (fst (extract_min0 t)) r

let delete_root0 (t: bst0{N? t}) : bst0 =
  let N (l, _, r) = t in
  if r = L then l
  else
    let (x, r') = extract_min0 r in
    N (l, x, r')

let rec delete0 (x: int) (t: bst0) : bst0 =
  match t with
  | L -> L
  | N (l, y, r) ->
    if x < y then N (delete0 x l, y, r)
    else if x > y then N (l, y, delete0 x r)
    else delete_root0 t
    
(* Se puede demostrar que delete preserva BSTs... pero es engorroso. Sólo
intentar si completaron todo y tienen ganas de renegar un rato. *)
let rec extract_min_lt (y:int) (t:bst0{N? t}) 
  : Lemma (requires all_lt y t) (ensures all_lt y (snd (extract_min0 t)) /\ y > (fst (extract_min0 t)))
= match t with
  | N (L, x, r) -> ()
  | N (l, x, r) -> extract_min_lt y l

let rec extract_min_gt (y:int) (t:bst0{N? t}) 
  : Lemma (requires all_gt y t) (ensures all_gt y (snd (extract_min0 t)) /\ y < (fst (extract_min0 t)))
= match t with
  | N (L, x, r) -> ()
  | N (l, x, r) -> extract_min_gt y l

let delete_root_lt (y:int) (t:bst0{N? t})
  : Lemma (requires all_lt y t) (ensures all_lt y (delete_root0 t))
= match t with
  | N (l, x, L) -> ()
  | N (l, x, r) -> (
    extract_min_lt y r)

let delete_root_gt (y:int) (t:bst0{N? t})
  : Lemma (requires all_gt y t) (ensures all_gt y (delete_root0 t))
= match t with
  | N (l, x, L) -> ()
  | N (l, x, r) -> (
    extract_min_gt y r)  

let rec delete0_all_lt (x:int) (t:bst0) (y:int)
  : Lemma (requires all_lt y t /\ x < y) (ensures all_lt y (delete0 x t))
= match t with
  | L -> ()
  | N (l, z, r) ->
    if x < z then delete0_all_lt x l y
    else if x > z then delete0_all_lt x r y 
    else delete_root_lt y t

let rec delete0_all_gt (x:int) (t:bst0) (y:int)
  : Lemma (requires all_gt y t /\ x > y) (ensures all_gt y (delete0 x t))
= match t with
  | L -> ()
  | N (l, z, r) ->
    if x < z then delete0_all_gt x l y
    else if x > z then delete0_all_gt x r y 
    else delete_root_gt y t

let delete_root_bst (t:bst0{N? t})
  : Lemma (requires is_bst t) (ensures is_bst (delete_root0 t))
= match t with
  | N (l, x, L) -> ()
  | N (l, x, r) -> (
    extract_min_es_bst r;
    extract_min_preserva_all_gt x r;
    all_lt_trans x (fst (extract_min0 r)) l;
    extract_min_ok r)

let rec delete0_bst (x: int)(t:bst0)
  : Lemma (requires is_bst t) (ensures is_bst (delete0 x t))
= match t with
  | L -> ()
  | N (l, y, r) ->
    if x < y then (
      delete0_bst x l;
      delete0_all_lt x l y
    )
    else if x > y then (
      delete0_bst x r;
      delete0_all_gt x r y
    )
    else delete_root_bst t

let delete (x: int) (t:bst) : bst =
  delete0_bst x t;
  delete0 x t