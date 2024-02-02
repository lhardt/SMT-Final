open Printf
 
type tipo = 
    TyInt 
  | TyBool
  | TyFn of tipo * tipo
  | TyRef of tipo
  | TyUnit
    
let rec ttos (t:tipo) : string =
  match t with
  | TyInt  -> "int"
  | TyBool -> "bool"
  | TyFn(t1,t2)   ->  "("  ^ (ttos t1) ^ " --> " ^ (ttos t2) ^ ")"
  | TyRef(t) ->  "Ref("  ^ (ttos t) ^ ")"
  | TyUnit -> "unit"

type ident = string

type bop = Sum | Sub | Mult | Eq | Gt | Lt | Geq | Leq

type expr =
  | Num of int
  | Var of ident
  | True
  | False
  | Binop of bop * expr * expr
  | If of expr * expr * expr
  | Fn of ident * tipo * expr
  | App of expr * expr
  | Let of ident * tipo * expr * expr
  | LetRec of ident * tipo * expr  * expr
  | Asg of expr * expr
  | Dref of expr
  | New of expr
  | Seq of expr * expr
  | Whl of expr * expr
  | Skip
  | Unit
              
type amb = (ident * tipo) list

type valor =
  | ValNum of int
  | ValTrue
  | ValFalse
  | ValClos  of ident * expr * gamma
  | ValRclos of ident * ident * expr * gamma
  | ValSkip
  | ValIdent of ident
and
  gamma = (ident * valor) list
  
    
let rec vtos (v: valor) : string =
  match v with
  | ValNum n -> string_of_int n
  | ValTrue -> "True"
  | ValFalse -> "False"
  | ValClos _ ->  "fn"
  | ValRclos _ -> "fn"
  | ValSkip -> "Skip"
  | ValIdent _ -> "Ident"
  
type mem = (ident * valor) list
    
let rec lookup_location loc x =
  match loc with
  | [] -> None
  | (y,i) :: tl -> if (y=x) then Some i else lookup_location tl x

let rec update_location loc value mem = 
  (match loc with
   | [] -> (value,mem) :: loc
   | (y,loc) :: tl -> 
       if (y=value) then (value,mem) :: tl
       else (y,loc) :: (update_location tl value mem)) 
  
let rec max_address a m =
  (match a with
   | [] -> m 
   | (y,a) :: tl -> 
       let v = int_of_string y in 
       max_address tl (max v m))
  
exception BugParser 
exception BugTypeInfer
exception TypeError of string

let rec typeinfer (amb:amb) (e:expr) : tipo =
  match e with
  | Num _ -> TyInt
    
  | Var x ->
      (match lookup_location amb x with
         Some t -> t
       | None -> raise (TypeError ("variavel nao declarada:" ^ x)))

  | True  -> TyBool
    
  | False -> TyBool
    
  | Binop(oper,e1,e2) ->
      let t1 = typeinfer amb e1 in
      let t2 = typeinfer amb e2 in
      if t1 = TyInt && t2 = TyInt then
        (match oper with
           Sum | Sub | Mult -> TyInt
         | Eq | Lt | Gt | Geq | Leq -> TyBool)
      else raise (TypeError "operando nao é do tipo int")

  | If(e1,e2,e3) ->
      (match typeinfer amb e1 with
         TyBool ->
           let t2 = typeinfer amb e2 in
           let t3 = typeinfer amb e3
           in if t2 = t3 then t2
           else raise (TypeError "then/else com tipos diferentes")
       | _ -> raise (TypeError "condição de IF não é do tipo bool"))

  | Fn(x,t,e1) ->
      let t1 = typeinfer (update_location amb x t) e1
      in TyFn(t,t1)

  | App(e1,e2) ->
      (match typeinfer amb e1 with
         TyFn(t, t') ->  if (typeinfer amb e2) = t then t'
           else raise (TypeError "tipo argumento errado" )
       | _ -> raise (TypeError "tipo função era esperado"))

  | Let(x,t,e1,e2) ->
      if (typeinfer amb e1) = t then typeinfer (update_location amb x t) e2
      else raise (TypeError "expr nao é do tipo declarado em Let" )

  | LetRec(f,(TyFn(t1,t2) as tf), Fn(x,tx,e1), e2) ->
      let amb_tf = update_location amb f tf in
      let amb_tf_tx = update_location amb_tf x tx in
      if (typeinfer amb_tf_tx e1) = t2
      then typeinfer amb_tf e2
      else raise (TypeError "tipo da funcao diferente do declarado")

  | LetRec _ -> raise BugParser

  | Skip -> TyUnit

  | Asg(e1, e2) ->
      let t1 = typeinfer amb e1 in
      let t2 = typeinfer amb e2 in
      if t1 = TyRef t2 then TyUnit
      else raise (TypeError "Atribuição inválida.")
  | Dref e ->
      (match typeinfer amb e with
         TyRef t -> t
       | _ -> raise (TypeError "Desreferenciamento de um valor que não é uma referência."))
  |New e ->
      let t = typeinfer amb e in
      TyRef t
        
  | Whl (e1, e2) ->
      if typeinfer amb e1 = TyBool then
        if typeinfer amb e2 = TyUnit then
          TyUnit
        else
          raise (TypeError "Corpo do while deve ter tipo unit")
      else
        raise (TypeError "Condição do while deve ter tipo bool")
          
  | Seq (e1, e2) ->
      let _ = typeinfer amb e1 in
      typeinfer amb e2
        
  |Unit -> TyUnit

(*------Avaliador------*)
              (*------Funções do Binop------*)

let compute(op: bop) (v1: valor) (v2:valor) = match (op,v1,v2) with
    (Sum, ValNum(n1),  ValNum(n2)) -> ValNum(n1+n2) 
  | (Sub, ValNum(n1),  ValNum(n2)) -> ValNum(n1-n2)
  | (Mult, ValNum(n1), ValNum(n2)) -> ValNum(n1*n2)
  | (Eq, ValNum(n1), ValNum(n2)) -> if (n1 = n2) then ValTrue else ValFalse
  | (Gt, ValNum(n1), ValNum(n2)) -> if (n1 > n2) then ValTrue else ValFalse
  | (Lt, ValNum(n1), ValNum(n2)) -> if (n1 < n2) then ValTrue else ValFalse
  | (Geq, ValNum(n1), ValNum(n2)) -> if (n1 >= n2) then ValTrue else ValFalse
  | (Leq, ValNum(n1), ValNum(n2)) -> if (n1 <= n2) then ValTrue else ValFalse
  | _ -> raise BugTypeInfer
  


  
let rec eval (gamma: gamma) (mem: mem) (e:expr) : valor * mem = 
  match e with
    Num n-> (ValNum n, mem)
            

  | Var x ->
      (match lookup_location gamma x with
         Some v -> (v, mem)
       | None -> raise BugTypeInfer)
       
  
  | True -> (ValTrue, mem)
            
  | False  -> (ValFalse, mem)
              
  | Binop(op,e1,e2) ->
      let (v1, mem) = eval gamma mem e1 in
      let (v2, mem) = eval gamma mem e2 in
      (compute op v1 v2, mem)
      
  | If(e1,e2,e3) ->
      let (v1, _) = eval gamma mem e1 in
      (match v1 with
         ValTrue  -> eval gamma mem e2
       | ValFalse -> eval gamma mem e3
       | _ -> raise BugTypeInfer)

  | Fn (x,_,e1) ->  (ValClos(x,e1,gamma), mem)
                    
  | App (e1, e2) ->
      let (v1, _) = eval gamma mem e1 in
      let (v2, _) = eval gamma mem e2 in
      (match v1 with
       | ValClos (x, ebdy, gamma') ->
           let gamma'' = update_location gamma' x v2 in
           eval gamma'' mem ebdy
       | ValRclos (f, x, ebdy, gamma') ->
           let gamma'' = update_location gamma' x v2 in
           let gamma''' = update_location gamma'' f v1 in
           eval gamma''' mem ebdy
       | _ -> raise BugTypeInfer)


  (* Memory allocated on e1 should be carried on to e2   *)
  | Let(x,_,e1,e2) ->
      let (v1, m_new) = eval gamma mem e1
      in eval (update_location gamma x v1) m_new e2 
                                  
  | LetRec(f,TyFn(t1,t2),Fn(x,tx,e1), e2) when t1 = tx ->
      let gamma'= update_location gamma f (ValRclos(f,x,e1,gamma))
      in eval gamma' mem e2
        
  | LetRec _ -> raise BugParser
                  
  | Skip -> (ValSkip, mem)
            
  | Asg(e1,e2) ->
      let (v1, _) = eval gamma mem e1 in 
      let (v2, _) = eval gamma mem e2 in
      (match v1 with 
         ValIdent(t) -> 
           (match lookup_location mem t with
              Some a -> (ValSkip, update_location mem t v2) 
            | None -> raise BugTypeInfer) 
       | _ -> raise BugTypeInfer)

  | Dref(e) -> 
      let (v, mem) = eval gamma mem e in
      (match v with 
         ValIdent(t) ->
          (match lookup_location mem t with
            Some a -> (a, mem)
          | None -> raise BugTypeInfer)   
        | _ -> raise BugTypeInfer) 

  | Whl(e1, e2) ->  eval gamma mem (If (e1, Seq(e2, Whl(e1, e2)), Skip)) 
                      
  | Seq(e1,e2) ->
      let (v1, mem) = eval gamma mem e1 in
      (match v1 with
         ValSkip -> eval gamma mem e2
       | _ -> raise BugTypeInfer)
      
  | New(e) ->
      let (v, mem) = eval gamma mem e in
      let i = sprintf "%d" ((max_address mem 0) + 1) in
      (ValIdent(i), update_location mem i v)

  | Unit-> (ValSkip, mem)
          
let int_st (e:expr) : unit =
  try
    let t = typeinfer [] e in
    let (v, _) = eval [] [] e
    in  print_string ((vtos v) ^ " : " ^ (ttos t))
  with 
    TypeError msg ->  print_string ("erro de tipo - " ^ msg) 
  | BugTypeInfer  ->  print_string "corrigir bug em typeinfer"
  | BugParser     ->  print_string "corrigir bug no parser para let rec"

          
                       
(*------Tests ------*) 

let teste0 = Binop(Sum, Num 10, Num 20 )

let teste01 = Let("x",  TyInt,  Num 10, Binop( Sum, Num 3,  Var "x" )) 

let teste02 = Let("x",  TyRef TyInt,  New (Num 10), Binop( Sum, Num 3,  Num 8 )) 

let teste03 = Let("x",  TyRef TyInt,  New (Num 10), Binop( Sum, Num 3,  Dref(Var "x") )) 
      
      
let teste1 = Let("x", TyRef TyInt, New (Num 3),
                 Let("y", TyInt, Dref (Var "x"),
                     Seq(Asg(Var "x", Binop(Sum, Dref(Var "x"), Num 1)),
                         Binop(Sum, Var "y",  Dref (Var "x")))))

let teste2 = Let("x", TyRef TyInt, New (Num 0),
                 Let("y", TyRef TyInt, Var "x",
                     Seq(Asg(Var "x", Num 1),
                         Dref (Var "y"))))

let counter1 = Let("counter", TyRef TyInt, New (Num 0),
                   Let("next_val", TyFn(TyUnit, TyInt),
                       Fn("w", TyUnit,
                          Seq(Asg(Var "counter",Binop(Sum, Dref(Var "counter"), Num 1)),
                              Dref (Var "counter"))),
                       Binop(Sum, App (Var "next_val", Skip),
                             App (Var "next_val", Skip))))
  
let whilefat = Whl(Binop(Gt, Dref (Var "z"), Num 0),
                   Seq( Asg(Var "y", Binop(Mult, Dref (Var "y"), Dref (Var "z"))),
                        Asg(Var "z", Binop(Sub, Dref (Var "z"), Num 1)))
                  )
                             
let bodyfat = Let("z", TyRef TyInt, New (Var "x"),
                  Let("y", TyRef TyInt, New (Num 1), Seq (whilefat, Dref (Var "y"))))
    
let impfat = Let("fat", TyFn(TyInt,TyInt), Fn("x", TyInt, bodyfat), App(Var "fat", Num 5))

