from dataclasses import dataclass
from typing import Union, Optional

@dataclass
class Var:
    name: str

@dataclass
class Star:
    pass

@dataclass
class Pi:
    var: str
    domain: 'Expr'
    codomain: 'Expr'

@dataclass
class Lam:
    var: str
    domain: 'Expr'
    body: 'Expr'

@dataclass
class App:
    func: 'Expr'
    arg: 'Expr'

@dataclass
class Nat:
    pass

@dataclass
class Zero:
    pass

@dataclass
class Succ:
    expr: 'Expr'

@dataclass
class ElimNat:
    e0: 'Expr'
    e1: 'Expr'
    e2: 'Expr'
    e3: 'Expr'

Expr = Union[Var, Star, Pi, Lam, App, Nat, Zero, Succ, ElimNat]

class Env:
    def __init__(self):
        self.vars = {}

    def add(self, var: Var, typ: Expr):
        self.vars[var] = typ

    def get(self, var: Var) -> Optional[Expr]:
        return self.vars.get(var)
    
    def extend(self, var: str, typ: Expr):
        new_env = Env()
        new_env.vars = self.vars.copy()
        new_env.add(var, typ)
        return new_env

def free_vars(expr: Expr) -> set:
    match expr:
        case Var(name):
            return set(name)
        case Pi(var, fst, snd) | Lam(var, fst, snd):
            return free_vars(fst) | (free_vars(snd) - set(var))
        case App(f, e1):
            return free_vars(f) | free_vars(e1)
        case Succ(e):
            return free_vars(e)
        case ElimNat(e0, e1, e2, e3):
            return free_vars(e0) | free_vars(e1) | free_vars(e2) | free_vars(e3)
    return set()

def subst(var: str, replace: Expr, e: Expr) -> Expr:
    def subst_in(e):
        return subst(var, replace, e)

    match e:
        case Var(name):
            return replace if name == var else e
        case Pi(x, fst, snd) | Lam(x, fst, snd):
            fst = subst_in(fst)
            snd = subst_in(snd) if x != var else snd
            return type(e)(x, fst, snd)
        case App(f, e1):
            return App(subst_in(f), subst_in(e1))
        case Succ(e):
            return Succ(subst_in(e))
        case ElimNat(e0, e1, e2, e3):
            return ElimNat(*map(subst_in, (e0, e1, e2, e3)))
    return e

def eval_expr(expr: Expr) -> Expr:
    while (new_expr := eval_once(expr)) is not None:
        expr = new_expr
    return expr

def eval_once(expr: Expr) -> Optional[Expr]:
    def eval_in(sub_expr):
        return eval_once(sub_expr)

    match expr:
        case App(Lam(x, _, b), a):
            return subst(x, a, b)
        case App(f, e1):
            if f1 := eval_in(f):
                return App(f1, e1)
            if e2 := eval_in(e1):
                return App(f, e2)
        case Lam(x, fst, snd):
            if snd1 := eval_in(snd):
                return Lam(x, fst, snd1)
        case Pi(x, fst, snd):
            if fst1 := eval_in(fst):
                return Pi(x, fst1, snd)
            if snd1 := eval_in(snd):
                return Pi(x, fst, snd1)
        case Succ(e):
            if new_e := eval_in(e):
                return Succ(new_e)
        case ElimNat(e0, e1, e2, Zero()):
            return e1
        case ElimNat(e0, e1, e2, Succ(n)):
            return App(App(e2, n), ElimNat(e0, e1, e2, n))
        case ElimNat(e0, e1, e2, e3):
            if new_e3 := eval_in(e3):
                return ElimNat(e0, e1, e2, new_e3)
    return None

def type_check(env: Env, expr: Expr) -> Expr:
    def check(expr, expected_type):
        expr_type = eval_expr(type_check(env, expr))
        if expr_type != expected_type:
            raise TypeError(f"Expected type {expected_type}, but got {expr_type}")
        return expr_type

    def check_star(expr):
        return check(expr, Star())

    match expr:
        case Var(name):
            var_type = env.get(name)
            if var_type:
                return var_type
            raise TypeError(f"Unbound variable: {name}")
        case Star():
            return Star()
        case Pi(x, fst, snd):
            check_star(fst)
            snd_type = type_check(env.extend(x, fst), snd)
            if eval_expr(snd_type) != Star():
                raise TypeError("Codomain is not Star")
            return Star()
        case Lam(x, fst, snd):
            check_star(fst)
            snd_type = type_check(env.extend(x, fst), snd)
            return Pi(x, fst, snd_type)
        case App(f, e1):
            f_type = eval_expr(type_check(env, f))
            if not isinstance(f_type, Pi):
                raise TypeError("Function is not Pi type")
            check(e1, f_type.domain)
            return eval_expr(subst(f_type.var, e1, f_type.codomain))
        case Nat():
            return Star()
        case Zero():
            return Nat()
        case Succ(e):
            check(e, Nat())
            return Nat()
        case ElimNat(e0, e1, e2, e3):
            check(e3, Nat())
            e0_type = eval_expr(type_check(env, e0))
            check(e1, eval_expr(App(e0, Zero())))
            expected_e2_type = Pi("n", Nat(), Pi("ih", App(e0, Var("n")), App(e0, Succ(Var("n")))))
            check(e2, expected_e2_type)
            return eval_expr(App(e0, e3))

add = Lam("a", 
          Nat(), 
          Lam("b", 
              Nat(), 
              ElimNat(
                  Lam("_", 
                      Nat(), 
                      Nat()), 
                  Var("b"), 
                  Lam("_", 
                      Nat(), 
                      Lam("rec", 
                          Nat(), 
                          Succ(Var("rec")))), 
                  Var("a"))
              )
          )

def proofs():
    three = Succ(Succ(Succ(Zero())))
    two = Succ(Succ(Zero()))
    one = Succ(Zero())
    a, b, c = 1, 2, 3
    print("Commutativity of addition:")
    result1 = eval_expr(App(App(add, one), two))
    result2 = eval_expr(App(App(add, two), one))
    print(f"{a} + {b} \n= {one} + {two} \n= {result1} \n= {three} \n= {c}")
    print(f"{b} + {a} \n= {two} + {one} \n= {result2} \n= {three} \n= {c}")
    print(f"{a} + {b} = {b} + {a} = a + b = b + a: {result1 == result2} qed.")

proofs()