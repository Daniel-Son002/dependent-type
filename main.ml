type term =
    | Lam of (term -> term)
    | Pi of term * (term -> term)
    | Appl of term * term
    | Ann of term * term
    | FreeVar of intoh what 
    | Star
    | Box