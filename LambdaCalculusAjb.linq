<Query Kind="FSharpProgram">
  <Reference>P:\Program Files\Linqpad\Newtonsoft.Json.dll</Reference>
  <Namespace>Newtonsoft.Json.Linq</Namespace>
</Query>

let lambdaSymbol = System.Char.ConvertFromUtf32(0x000003BB)

type Token = 
    | LamTok
    | VarTok of string
    | DotTok
    | OpenTok
    | CloseTok
    | SpaceTok
    | ErrorTok

let regex = new Regex(@"(?<Lam>\\|\u03BB)|(?<Var>[a-zA-Z']+)|(?<Dot>\.)|(?<Open>\()|(?<Close>\))", RegexOptions.Compiled ||| RegexOptions.ExplicitCapture ||| RegexOptions.Singleline)

let token (g: GroupCollection) =
    if      g.["Lam"].Success   then LamTok
    else if g.["Var"].Success   then VarTok g.["Var"].Value
    else if g.["Dot"].Success   then DotTok
    else if g.["Open"].Success  then OpenTok
    else if g.["Close"].Success then CloseTok
    else                              ErrorTok
       
                       
type Name = string * int

type Expr =
     | Var of Name 
     | Lambda of Name * Expr 
     | App of Expr * Expr

 
(* Parser uses pattern matching recursive descent where each pattern matches 
   Some(thing, t) or fails with None
   t is the remainder of the input which can be matched with
   another parse.
 *)
let rec (|ExprM|_|) = function
    | TermM(f, ExprM(a, t)) -> Some(App(f, a), t)
    | TermM(x, t) -> Some(x, t)
    | _ -> None

and (|TermM|_|) = function
    | LamTok :: LambdaM(l, t) -> Some (l, t)
    | OpenTok :: ExprM(e, CloseTok :: t) -> Some(e, t)
    | VarM(v, t) -> Some (v, t)
    | _ -> None
  
and (|VarM|_|) = function
    | VarTok c :: t -> Some(Var(c, -1), t)
    | _ -> None
    
and (|LambdaM|_|) = function
    | VarM(Var(name), LambdaM(a, t)) -> Some (Lambda (name, a), t)
    | DotTok :: ExprM(b, t) -> Some(b, t)
    | _ -> None

let parse (s: string) = 
    let m = regex.Matches(s)
    let (ExprM (e : Expr, t : Token list)) = List.ofSeq (seq { for t in m do yield (token t.Groups) })
    (e, t)

(* Printing expressions with the minimum number of parentheses
   This function prints without parentheses and the one below 
   applies parentheses only where required
*)
let rec exprToString (e : Expr) = 
    match e with
    | Var (c, n) when n < 1 -> c
    | Var (c, n) -> n.ToString()
    | Lambda ((name, n), b) when n < 1 -> lambdaSymbol + name + "." + exprToString b
    | Lambda ((_, _), b) -> lambdaSymbol + " " + exprToString b 
    | App (f, a) -> exprToStringParen (f, true) + " " + exprToStringParen (a, false)
    
and exprToStringParen e = 
    match e with
    | (Var _, _) -> exprToString  (fst e)
    | (Lambda _, _) -> "(" + exprToString (fst e) + ")"
    | (e', true) -> "(" + exprToString e' + ")"
    | (e', _) -> exprToString e'   

let getIndex (c: string) (vars: string list) =
    match List.tryFindIndex (fun v -> v = c) vars with
    | Some n -> n + 1
    | None -> 0

(* Create de Bruijn indices for all local variables
*)
let deBruijn e =
    let rec deBruijnAux e vars =
        match e with
        | Var (c, _) -> Var (c, getIndex c vars)
        | Lambda ((c, n), b) -> Lambda ((c, 1), (deBruijnAux b (c :: vars)))
        | App (f, a) -> App((deBruijnAux f vars), (deBruijnAux a vars))
    in deBruijnAux e []

(* Get the free variables in one level of lambda *)
let rec free1 e (s: Set<string>) =
    match e with
    | Var (x, 0) -> s.Add(x)   // free
    | App (f, a) -> free1 f (free1 a s) 
    | _ -> s 

let renameLambdaArg a b (s: Set<string>)  =
    let (name, _) = a
    let name' = if(s.Contains(name)) then name + "'" else name
    Lambda ((name', -1), b)
    
(* rename lambda vars *)
let rec rename e =
    match e with
    | Var (x, 0) -> (e, Set.singleton(x)) 
    | Lambda (a, b) -> let (b', sb) = rename b
                       ((renameLambdaArg a b' sb), sb) 
    | App (f, a) -> let (f', sf) = rename f 
                    let (a', sa) = rename a 
                    (App(f', a'), (Set.union sa sf))                
    | _ -> (e, Set.empty)
    
(* Perform a single beta reduction and return a pair of
   (result, true) or (e, false) if no reduction was possible
*)
let rec betaReduce e =
    (* substitute variable n with x in b *)
    let rec betaReduceAux b x n =
       match b with
       | Var (_, n') when n' = n -> x
       | Lambda (name, b') -> Lambda (name, betaReduceAux b'  x  (n + 1))
       | App (f, a) -> App ((betaReduceAux f x n), (betaReduceAux a x n)) 
       | _ -> b
       
    in match e with
       | App (Lambda (_, b), x) -> (betaReduceAux b x 1, true)               // Apply the lambda and remove it
       | App (f, a) -> let f' = betaReduce f in                              // otherwise dig deeper
                       let a' = if snd f' then (a, true) else betaReduce a in
                       (App((fst f'), (fst a')), (snd a'))
       | _ -> (e, false)

let rec etaReduce e =
   match e with
   | Lambda (_, App (f, Var(_, 1))) -> etaReduce f
   | Lambda (name, f) -> Lambda (name, etaReduce f)
   | App (f, x) -> App (etaReduce f , etaReduce x) 
   | _ -> e
  
let test s =
    let e = parse s
    printf "%s \r\nrest = %A \r\n" (exprToString (fst e)) (snd e)
    let db = deBruijn (fst e)
    
    let rec reduce e =
        printf "%s\r\n"  (exprToString e)
        match betaReduce e with
        | (r, true) -> reduce r
        | _ -> ()
    in reduce db
    printf "\r\n"
    
// test @"(λg.(λx.g(xx))(λx.g(xx)))z"

test @"x y(y z)x z(\x.(x y) z)"

test "((λx.λy.λz.x y z)y)z"

test "((λx.λy.x y)(x y))(y x)"

test "(λa.λx.(a x))x"