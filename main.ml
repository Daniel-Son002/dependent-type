module StringSet = Set.Make(String)

type expr =
  | Var of string
  | Star
  | Pi of string * expr * expr
  | Lam of string * expr * expr
  | App of expr * expr
  | NatConst
  | Zero
  | Succ of expr
  | ElimNat of expr * expr * expr * expr

(* Alpha-equivalence check *)
(* let rec alpha_equiv e1 e2 =
  match (e1, e2) with
  | (Var x1, Var x2) -> x1 = x2
  | (Lam (x1, t1, body1), Lam (x2, t2, body2)) ->
      alpha_equiv t1 t2 && alpha_equiv (rename x1 x2 body1) body2
  | (App (f1, a1), App (f2, a2)) -> alpha_equiv f1 f2 && alpha_equiv a1 a2
  | (Succ e1', Succ e2') -> alpha_equiv e1' e2'
  | (ElimNat (n1, z1, s1, p1), ElimNat (n2, z2, s2, p2)) ->
      alpha_equiv n1 n2 && alpha_equiv z1 z2 && alpha_equiv s1 s2 && alpha_equiv p1 p2
  | _ -> false *)

(* Rename variables to avoid capture *)
let rec rename old new_name e =
  match e with
  | Var x -> if x = old then Var new_name else Var x
  | Lam (x, t, body) ->
      let new_var = if x = old then new_name else x in
      Lam (new_var, t, rename old new_name body)
  | App (f, a) -> App (rename old new_name f, rename old new_name a)
  | Succ e' -> Succ (rename old new_name e')
  | ElimNat (n, z, s, p) ->
      ElimNat (rename old new_name n, rename old new_name z, rename old new_name s, rename old new_name p)
  | _ -> e

(* Free variables extraction *)
let rec free_vars e =
  match e with
  | Var x -> StringSet.singleton x
  | Pi (x, e1, e2) -> StringSet.union (free_vars e1) (StringSet.remove x (free_vars e2))
  | Lam (x, _, body) -> StringSet.remove x (free_vars body)
  | App (f, a) -> StringSet.union (free_vars f) (free_vars a)
  | Succ e' -> free_vars e'
  | ElimNat (n, z, s, p) ->
      StringSet.union (free_vars n) (StringSet.union (free_vars z) (StringSet.union (free_vars s) (free_vars p)))
  | _ -> StringSet.empty

(* Capture avoiding substitution *)
let rec subst x e s =
  match s with
  | Var y -> if x = y then e else Var y
  | Lam (y, t, body) ->
      let body' = if x = y then body else subst x e body in
      Lam (y, t, body')
  | App (f, a) -> App (subst x e f, subst x e a)
  | Succ e' -> Succ (subst x e e')
  | ElimNat (n, z, s', p) ->
      ElimNat (subst x e n, subst x e z, subst x e s', subst x e p)
  | _ -> s

type abbs = (string * expr) list

let rec normal_form_abbs (abbs:abbs) (t:expr):expr =
    match abbs with
    | (x, e) :: tl -> normal_form_abbs tl (subst x e t)
    | [] -> t
    
let rec eval_step e =
  match e with
  | App (Lam (x, _, e1), e2) -> subst x e2 e1 
  | App (f, a) -> 
    let f' = eval_step f in
    if f' = f then App (f, eval_step a) else App (f', a)
  | Lam (x, t, body) -> 
    Lam (x, t, eval_step body)
  | Succ e' -> 
    let e'' = eval_step e' in
    if e'' = e' then Succ e' else Succ e''
  | ElimNat (Zero, z, _, _) -> z 
  | ElimNat (Succ n', z, s, p) -> App ((App (s, n')), (ElimNat (n', z, s, p)))
  | ElimNat (n, z, s, p) ->
    let n' = eval_step n in
    if n' = n then ElimNat (n, z, s, p) else ElimNat (n', z, s, p)
  | Pi (x, t1, t2) ->
    let t1' = eval_step t1 in
    let t2' = eval_step t2 in
    if t1 = t1' && t2 = t2' then Pi (x, t1, t2)
    else Pi (x, t1', t2')
  | _ -> e
  

let rec eval_complete e = 
  let e' = eval_step e in
  if e' = e then
    e
  else
    eval_complete e'

let rec print e =
  match e with
  | Var x -> Printf.sprintf "Var(%s)" x
  | Star -> "Star"
  | NatConst -> "Nat"
  | Zero -> "Zero"
  | Pi (x, t1, t2) -> Printf.sprintf "Pi(%s, %s, %s)" x (print t1) (print t2)
  | Lam (x, t1, e2) -> Printf.sprintf "Lambda(%s, %s, %s)" x (print t1) (print e2)
  | App (e1, e2) -> Printf.sprintf "App(%s, %s)" (print e1) (print e2)
  | Succ e1 -> Printf.sprintf "Succ(%s)" (print e1)
  | ElimNat (e1, e2, e3, e4) -> Printf.sprintf "ElimNat(%s, %s, %s, %s)" (print e1) (print e2) (print e3) (print e4)

let () =
  Printf.printf "Show: %s\n" (print (App (Lam ("x", NatConst, Var "x"), Zero)))

let add_expr = 
  Lam ("a", NatConst,
  Lam ("b", NatConst,
  ElimNat (Var "a", 
    Var "b", 
    Lam ("a'", NatConst, Lam ("_", NatConst, Succ (App (App (Var "add", Var "a'"), Var "b")))),
    Var "a"
  )
  )
)

let comm_add_expr = 
  Lam ("a", NatConst,
    Lam ("b", NatConst,
    ElimNat (Var "a", 
      App (App (Var "add", Var "b"), Zero),
      Lam ("a'", NatConst, 
      Lam ("_", NatConst, 
          App (Succ (App (App (Var "add", Var "b"), Var "a'")), Var "b")
      )
      ),
      Var "a"
  )
  )
)
  
let () = 
  let expr = App (App (comm_add_expr, Zero), Succ Zero) in
  Printf.printf "Show: %s\n" (print expr)
