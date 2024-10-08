type term =
    | Lam of (term -> term)
    | Pi of term * (term -> term)
    | Appl of term * term
    | Ann of term * term
    | FreeVar of intoh what 
    | Star
    | Box

type lterm = 
    | LId of string
    | LLam of string * lterm
    | LApp of lterm * lterm

(* module LambdaParse = struct
    let lexer = Genlex.make_lexer["("; ")"; "."; "/"]

    let lex s =
        let  *)

type nat =
    | Zero
    | Succ of nat

type ('a, 'b) pi =
    | Lam : ('a -> 'b) -> ('a, 'b) pi
    | App : ('a, 'b) pi -> 'a -> 'b

type nat_type =
    | TNat
    | TZero
    | TSucc of nat_type

let rec eval_nat n =
    match n with
    | Zero -> Zero
    | Succ n' -> Succ (eval_nate n')

let rec elim_nat f base step n =
    match n with
    | Zero -> base
    | Succ n' -> step n' (elim_nat f base step n')

let id_fun : ('a, ('a, 'a) pi) pi =
    Lam (fun n -> Lam (fun m -> m))

let rec free_variables t =
    match t with
    | LId x -> [x]
    | LLam (x, t) -> remove (free_variables t) x
    | LApp (t1, t2) -> union (free_variables t1) (free_variables t2) ;;

let rec substitute (m:lterm) (s:string) (n:lterm):lterm =
    let p = LambdaParser.parse in
    let pp = LambdaParser.pp in
    let num = ref(0) in
    let gensym (s: string) : string =
        let name = s ^"_"^ string_of_int !num in
        num := !num + 1;
        name in
    match m with
    | LId y -> if (s = pp m) then n else m
    | LApp(t1, t2) -> LApp((substitute t1 s n), (substitute t2 s n))
    | LLam(y, t') -> if (y = s) then m else
                     if (not (List.mem y (free_variables n))) then LLam(y, (substitute t' s n)) else
                     let new_var = gensym y in
                     LLam(new_var, (substitute(substitute t' y (p new_var)) s n)) ;;

let rec reduce (t:lterm):lterm option =
    match t with
    | LLam(x, t') -> (match reduce t' with
                      | Some t'' -> Some(LLam(x, t''))
                      | None -> None)
    | LApp(LLam(x, t1), t2) -> Some(substitute t1 x t2)
    | LApp(t1, t2) -> (match reduce t1 with
                       | Some t1' -> Some(LApp(t1', t2))
                       | None -> None)
    | _ -> None
;;

let rec normal_form (t:lterm):lterm = 
    match reduce t with
    | Some t' -> normal_form t'
    | None -> t
;;

let eval (input:string):string =
    let term = LambdaParser.parse input in
    LambdaParser.pp (normal_form term)

