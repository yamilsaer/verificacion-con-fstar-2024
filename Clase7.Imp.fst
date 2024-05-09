module Clase7.Imp

open FStar.Mul

type var = string

type expr =
  | Var   : var -> expr
  | Const : int -> expr
  | Plus  : expr -> expr -> expr
  | Minus : expr -> expr -> expr
  | Times : expr -> expr -> expr
  | Eq    : expr -> expr -> expr

type stmt =
  | Assign : var -> expr -> stmt
  | IfZ    : expr -> stmt -> stmt -> stmt
  | Seq    : stmt -> stmt -> stmt
  | Skip   : stmt
  | While  : expr -> stmt -> stmt

type state = var -> int

let rec eval_expr (s : state) (e : expr) : int =
  match e with
  | Var x -> s x
  | Const n -> n
  | Plus  e1 e2 -> eval_expr s e1 + eval_expr s e2
  | Minus e1 e2 -> eval_expr s e1 - eval_expr s e2
  | Times e1 e2 -> eval_expr s e1 * eval_expr s e2
  | Eq e1 e2 -> if eval_expr s e1 = eval_expr s e2 then 0 else 1

let override (#a:eqtype) (#b:Type) (f : a -> b) (x:a) (y:b) : a -> b =
  fun z -> if z = x then y else f z

(* Relación de evaluación big step. *)
noeq
type runsto : (p:stmt) -> (s0:state) -> (s1:state) -> Type0 =
  | R_Skip : s:state -> runsto Skip s s
  | R_Assign : s:state -> #x:var -> #e:expr -> runsto (Assign x e) s (override s x (eval_expr s e))

  | R_Seq :
    #p:stmt -> #q:stmt ->
    #s:state -> #t:state -> #u:state ->
    runsto p s t -> runsto q t u -> runsto (Seq p q) s u

  | R_IfZ_True :
    #c:expr -> #t:stmt -> #e:stmt ->
    #s:state -> #s':state -> runsto t s s' ->
    squash (eval_expr s c = 0) ->
    runsto (IfZ c t e) s s'

  | R_IfZ_False :
    #c:expr -> #t:stmt -> #e:stmt ->
    #s:state -> #s':state -> runsto e s s' ->
    squash (eval_expr s c <> 0) ->
    runsto (IfZ c t e) s s'

  | R_While_True :
    #c:expr -> #b:stmt -> #s:state -> #s':state -> #s'':state ->
    runsto b s s' ->
    squash (eval_expr s c = 0) ->
    runsto (While c b) s' s'' ->
    runsto (While c b) s s''

  | R_While_False :
    #c:expr -> #b:stmt -> #s:state ->
    squash (eval_expr s c <> 0) ->
    runsto (While c b) s s

// Demostrar que esta regla es admisible, es decir, que
// podemos "asumir" que la tenemos para demostrar, pero no
// necesitamos analizarla cuando destruímos una prueba:
//
// | R_While :
//   #c:expr -> #b:stmt ->
//   #s:state -> #s':state ->
//   runsto (IfZ c (Seq b (While c b)) Skip) s s' ->
//   runsto (While c b) s s'
let r_while (#c:expr) (#b:stmt) (#s #s'' : state) (pf : runsto (IfZ c (Seq b (While c b)) Skip) s s'')
  : runsto (While c b) s s''
= if eval_expr s c = 0 
  then let R_IfZ_True (R_Seq s1 s2) () = pf in
    R_While_True s1 () s2
  else R_While_False ()
    

type cond = state -> bool

let override_cond (c:cond) (x:var) (e:expr) : cond = 
  fun st -> c (override st x (eval_expr st e))

let cond_expr_t (c:cond) (e:expr) : cond =
  fun s -> c s && eval_expr s e = 0

let cond_expr_f (c:cond) (e:expr) : cond =
  fun s -> c s && eval_expr s e <> 0

noeq
type hoare : (pre:cond) -> (p:stmt) -> (post:cond) -> Type0 =
  | H_Skip : pre:cond -> hoare pre Skip pre // {P} Skip {P}
  | H_Seq :
    #p:stmt -> #q:stmt ->
    #pre:cond -> #mid:cond -> #post:cond ->
    hoare pre p mid -> hoare mid q post ->
    hoare pre (Seq p q) post  // {pre} p {mid} /\ {mid} q {post}    ==>    {pre} p;q {post}
  | H_Assign : 
    #x:var -> #e:expr -> 
    #post:cond ->
    hoare (override_cond post x e) (Assign x e) post
  | H_IfZ :
    #c:expr -> #t:stmt -> #e:stmt ->
    #pre:cond -> #post:cond ->
    hoare (cond_expr_t pre c) t post -> hoare (cond_expr_f pre c) e post ->
    hoare pre (IfZ c t e) post
  | H_While :
    #c:expr -> #b:stmt ->
    #inv:cond ->
    hoare (cond_expr_t inv c) b inv ->
    hoare inv (While c b) (cond_expr_f inv c)

let rec hoare_ok (p:stmt) (pre:cond) (post:cond) (pf : hoare pre p post)
                 (s0 s1 : state) (e_pf : runsto p s0 s1)
  : Lemma (requires pre s0)
          (ensures post s1)
= match p with
  | Skip -> ()

  | Assign x e -> ()

  | Seq sq1 sq2 ->
    let H_Seq #_ #_ #_ #mid #_ h1 h2 = pf in
    let R_Seq #_ #_ #_ #t #_ r1 r2 = e_pf in
    hoare_ok sq1 pre mid h1 s0 t r1;
    hoare_ok sq2 mid post h2 t s1 r2

  | While c b ->
    if eval_expr s0 c = 0 then (
      let H_While #_ #_ #_ h1 = pf in
      let R_While_True #_ #_ #_ #s' #s'' r1 _ r2 = e_pf in
      hoare_ok b (cond_expr_t pre c) pre h1 s0 s' r1;
      hoare_ok p pre (cond_expr_f pre c) pf s' s'' r2
    )
    else ()

  | IfZ c t e ->
    if eval_expr s0 c = 0 then (
      let H_IfZ #_ #_ #_ #_ #_ h1 h2 = pf in
      let R_IfZ_True #_ #_ #_ #_ #_ r1 _ = e_pf in
      hoare_ok t (cond_expr_t pre c) post h1 s0 s1 r1
    )
    else (
      let H_IfZ #_ #_ #_ #_ #_ _ h2 = pf in
      let R_IfZ_False #_ #_ #_ #_ #_ r1 _ = e_pf in
      hoare_ok e (cond_expr_f pre c) post h2 s0 s1 r1
    )

let st0 : state = fun _ -> 0

let test1 : hoare (fun _ -> true) (Assign "x" (Const 1)) (fun s -> s "x" = 1) =
  H_Assign

