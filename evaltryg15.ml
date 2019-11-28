type ide = Ide of string;;

type exp = Val of ide
| Eint of int
| Echar of char
| True
| False
| Empty
| Sum of exp * exp
| Diff of exp * exp
| Times of exp * exp
| And of exp * exp
| Or of exp * exp
| Not of exp
| Eq of exp * exp
| Less of exp * exp
| Cons of exp * exp
| Head of exp
| Tail of exp
| Fst of exp
| Snd of exp
| Epair of exp * exp
| Ifthenelse of exp * exp * exp
| Let of ide * exp * exp
| Fun of ide * exp
| Appl of exp * exp
| Rec of ide * exp
| Try of exp * ide * exp
| Raise of ide;;

type etype = TBool
| TInt
| TChar
| TVar of string
| TPair of etype * etype
| TList of etype list
| TFun of etype * etype;;

let nextsym = ref (-1);;
let newvar = fun () -> nextsym := !nextsym + 1;
  TVar ("?T" ^ string_of_int (!nextsym));;

let newtypenv = if(false) then [(Ide "", TInt)] else [];;
let applytypenv a (Ide x) = let l1 = List.filter (fun b -> fst b = (Ide x)) a in if(List.length l1 = 1) then snd (List.hd l1) else newvar();;
let bindtyp a (Ide x) t = if(true) then (Ide x, t)::a else newtypenv;;

(* try - raise *)

let rec t e i = match e with
  Raise j -> i = j
| Ifthenelse (a,b,c) -> t b i || t c i
| Try (a,j,b) -> t a i
| _ -> false;;

(*generiamo le coppie *)

let rec coppie es am = match es with
  Val i -> (applytypenv am i, [])
| Eint n -> (TInt, [])
| Echar c -> (TChar, [])
| True
| False -> (TBool, [])
| Empty -> (TList [newvar()], [])
      
| Sum (a,b)
| Diff (a,b)
| Times (a,b) -> let c1 = coppie a am in
  let c2 = coppie b am in
  let c = [(fst c1,TInt);(fst c2,TInt)] in
  (TInt, c @ snd c1 @ snd c2)
    
    (*generiamo le coppie per ogni elemento dell'operazione (coppie formate da tipo e lista di vincoli), uniamo i risultati come nell'algoritmo, prima di applicare sostituzione e unificazione. Si suppone che fst c1 e fst c2 siano int così da poter cancellare la coppia e ottenere come risultato finale il tipo della funzione e una lista vuota *)
    
| And (a,b)
| Or (a,b) -> let c1 = coppie a am in
  let c2 = coppie b am in
  let c = [(fst c1,TBool);(fst c2,TBool)] in
  (TBool, c @ snd c1 @ snd c2)
    
| Not a -> let c1 = coppie a am in
  let c = [(fst c1,TBool)] in
  (TBool, c @ snd c1)
    
| Eq (a,b) -> let c1 = coppie a am in
  let c2 = coppie b am in
  let c = [(fst c1,fst c2);(fst c1,fst c1);(fst c2,fst c2)] in
  (TBool, c @ snd c1 @ snd c2)
    
| Less (a,b) -> let c1 = coppie a am in
  let c2 = coppie b am in
  let c = [(fst c1,TInt);(fst c2,TInt)] in
  (TBool, c @ snd c1 @ snd c2)
    
| Cons (a,b) -> let c1 = coppie a am in
  let c2 = coppie b am in
  let c = [(fst c1, fst c1);(fst c2, TList [fst c1])] in
  (TList [fst c1], c @ snd c1 @ snd c2)
    
| Head b -> let a = newvar() in let c1 = coppie b am in (match (fst c1) with
    TList s -> (List.hd s, [(fst c1, fst c1)] @ snd c1 ) (* corrisponde al solito c *)
  | TVar s -> (a, [(TList [a], fst c1)] @ snd c1)
  | _ -> failwith "Errore testa")
  
| Tail b -> let a = newvar() in let c1 = coppie b am in (match (fst c1) with
    TList s -> c1 (* corrisponde al solito c *)
  | TVar s -> (TList [TVar s], [TList [a], fst c1] @ snd c1)
  | _ -> failwith "Errore coda")
    
| Fst b -> let a = newvar() in let c1 = coppie b am in (match (fst c1) with
    TPair(c,d) -> (c, [fst c1, TPair(c,d)] @ snd c1)
  | TVar s -> (a, [fst c1, TPair(a,newvar())] @ snd c1)
  | _ -> failwith "Errore fst")           
| Snd b -> let a = newvar() in let c1 = coppie b am in (match (fst c1) with
    TPair(c,d) -> (d, [fst c1, TPair(c,d)] @ snd c1)
  | TVar s -> (a, [fst c1, TPair(newvar(),a)] @ snd c1)
  | _ -> failwith "Errore snd") 
| Epair (a,b) -> let c1 = coppie a am in
  let c2 = coppie b am in
  let c = [(fst c1,fst c1); (fst c2,fst c2)] in
  (TPair (fst c1, fst c2), c @ snd c1 @ snd c2)
    
| Ifthenelse (a,b,c) -> let c1 = coppie a am in
    let c2  = coppie b am in
    let c3  = coppie c am in
    let c = [(fst c1,TBool); (fst c2, fst c3)] in
    (fst c3, c @ snd c1 @ snd c2 @ snd c3)
      
| Let (i,a,b) -> let c = newvar() in let c1 = coppie a am in
    let c2 = coppie b (bindtyp am i c) in
    (fst c2, [(fst c1, c)] @ snd c1 @ snd c2)
| Fun (i,a) -> let v = newvar() in
  let c1 = coppie a (bindtyp am i v) in
    (TFun (v,fst c1), snd c1)
| Appl (a,b) -> let v = newvar() in
    let c1 = coppie a am in
    let c2 = coppie b am in
    (v, [(fst c1, TFun (fst c2, v))] @ snd c1 @ snd c2)
| Rec (i,b) -> let a = newvar() in (match b with
    Fun (j,c) -> let c1 = coppie b (bindtyp am i a) in
    (fst c1, [(fst c1, a)] @ snd c1)
  | _ -> failwith "Errore ricorsione")
| Try (a,i,b) -> if(t a i) then coppie b am else coppie a am
| Raise i -> coppie (Val i) am;;

(* sostituzione: una volta applicata la funzione type all'espressione e generati i vincoli, si procede applicando la sostituzione nelle coppie presenti nei vincoli, fino a quando non si raggiunge l'insieme vuoto - lista vuota *)

(* risoluzione delle singole coppie, tipo della coppia, stringa, tipo da eguagliare *)
(* sostituzione del singolo termine in ogni coppia *)
let rec risolvi ti st t = match ti with
  TInt (* identita *)
| TChar
| TBool -> ti
| TVar s -> if(st = s) then t else ti
| TPair (a,b) -> TPair (risolvi a st t, risolvi b st t)
| TList l -> TList [risolvi (List.hd l) st t]
| TFun (a,b) -> TFun (risolvi a st t, risolvi b st t);;

(* sostituzione: lista di vincoli, stringa (Tvar "stringa"), tipo da sostituire. restituisce la lista di vincoli per il tipo "risolta"*)

let rec sostituzione li st ti = List.fold_right (fun a b -> (risolvi (fst a) st ti, risolvi (snd a) st ti)::b) li [];;

(* controlla se c'è qualche occorrenza nel tipo (stringa di TVar) *)
let rec occorrenza st ti = match ti with
  TVar s -> s = st
| TPair (a,b) -> occorrenza st a || occorrenza st b
| TFun (a,b) -> occorrenza st a || occorrenza st b
| TList a -> occorrenza st (List.hd a)
| _ -> false;;

(* unificazione delle coppie: se gli elementi sono uguali si toglie la coppia altrimenti si applica la sostituzione; quando avvengono tutte le unificazioni si restituisce lista vuota. seguendo il pdf, per le espressioni composte, si verifica che i costruttori dei due elementi siano uguali e poi si procede *)

let rec unificazione li = match li with
  [] -> [] (* gia unificato *)
| (TPair (a,b), TPair (c,d))::tl
| (TFun (a,b), TFun (c,d))::tl -> unificazione ((a,c)::(b,d)::tl)
| (TList a, TList b)::tl -> unificazione (((List.hd a),(List.hd b))::tl)
| (TVar s, a)::tl -> if(occorrenza s a)
                     then unificazione tl
                     else (TVar s, a)::unificazione (sostituzione tl s a)
| (a, TVar s)::tl -> if(occorrenza s a)
                     then unificazione tl
                     else (a, TVar s)::unificazione (sostituzione tl s a)
| (a,b)::tl when a = b -> unificazione tl
| _ -> failwith "Non unificabile";;

(* passo finale: dopo l'unificazione si controlla che i vincoli siano una lista vuota, quindi si restituisce il tipo. se esistono ancora vincoli allora si applica la sostituzione *)
let rec app ti li = (match li with
  [] -> ti           
| (TVar s, a)::tl
| (a, TVar s)::tl ->  app (risolvi ti s a) tl
| _ -> failwith "Sostituzione non risolta");;

let typeinf e = let a = coppie e newtypenv in
  app (fst a) (unificazione (snd a));;


type eval = Undefined
| Int of int
| Bool of bool
| Char of char
| List of eval list
| Pair of eval * eval
| Closure of exp * env and env = ide -> eval;;

let emptyenv = fun (Ide x) -> Undefined;;

let applyenv (r,Ide x) = if(false) then Int 1 else r (Ide x);;
 
let bind (r,Ide x,e) = if(false) then emptyenv else fun (Ide y) -> if (Ide x = Ide y) then e else r (Ide y);; 

let valutaInt e = match e with
  Int n -> n
| _ -> failwith "Operazione non valida: int";;
let valutaBool e = match e with
  Bool b -> b
| _ -> failwith "Operazione non valida: bool";;
let valutaChar e = match e with
  Char c -> c
| _ -> failwith "Operazione non valida: char";;
let valutaList e = match e with
  List l -> l
| _ -> failwith "Operazione non valida: list";;

let sost ex v = match ex with
  Let(ide,e1,e2) -> (match e1 with
    Rec(y,a) -> (match a with
      Fun(x,t) -> (match t with
	Ifthenelse (a,b,c) -> (match c with
	  And(d,e) -> (match e with
	    Appl(f,g) -> (match f with
	      Val i -> if i = v then Let(ide,Rec(y, Fun(x, Ifthenelse(a, b, And(d, Appl(Rec(y, Fun(x, Ifthenelse(a, b, And(d,e)))), g))))),e2) else ex
	    | _ -> ex)
	  | _ -> ex)
	| Or(d,e) -> (match e with
	    Appl(f,g) -> (match f with
	      Val i -> if i = v then Let(ide,Rec(y, Fun(x, Ifthenelse(a, b, Times(d, Appl(Rec(y, Fun(x, Ifthenelse(a, b, Times(d,e)))), g))))),e2) else ex
	    | _ -> ex)
	  | _ -> ex)
	| Times(d,e) -> (match e with
	    Appl(f,g) -> (match f with
	      Val i -> if i = v then Let(ide,Rec(y, Fun(x, Ifthenelse(a, b, Times(d, Appl(Rec(y, Fun(x, Ifthenelse(a, b, Times(d,e)))), g))))),e2) else ex
	    | _ -> ex)
	  | _ -> ex)
	| Sum(d,e) -> (match e with
	    Appl(f,g) -> (match f with
	      Val i -> if i = v then Let(ide,Rec(y, Fun(x, Ifthenelse(a, b, Sum(d, Appl(Rec(y, Fun(x, Ifthenelse(a, b, Sum(d,e)))), g))))),e2) else ex
	    | _ -> ex)
	  | _ -> ex)
	| Diff(d,e) -> (match e with
	    Appl(f,g) -> (match f with
	      Val i -> if i = v then Let(ide,Rec(y, Fun(x, Ifthenelse(a, b, Diff(d, Appl(Rec(y, Fun(x, Ifthenelse(a, b, Diff(d,e)))), g))))),e2) else ex
		| _ -> ex)
	  | _ -> ex)
	| Cons(d,e) -> (match e with
	    Appl(f,g) -> (match f with
	      Val i -> if i = v then Let(ide,Rec(y, Fun(x, Ifthenelse(a, b, Cons(d, Appl(Rec(y, Fun(x, Ifthenelse(a, b, Cons(d,e)))), g))))),e2) else ex
	    | _ -> ex)
	  | _ -> ex)
	| _ -> ex)
      | _ -> ex)
    | _ -> ex)
  | _ -> ex)
| _ -> ex;;
	
	let applicaSost e = match e with
	  Let(ide,(Rec(y,a)),e2) -> sost e y
	| _ -> e;;

let rec semtry ex en  = match (typeinf ex) with
  z -> (match (applicaSost ex) with
    Val ide -> applyenv (en,ide)
  | Eint n -> Int n
  | Echar c -> Char c
  | True -> Bool true
  | False -> Bool false
  | Empty -> List []
  | Sum (a,b) -> (let c = semtry a en  in
    let d = semtry b en  in
    match c,d with
      Undefined, _
    | _, Undefined -> Undefined
    | _ -> Int (valutaInt c + valutaInt d))
  | Diff (a,b) -> (let c = semtry a en  in
    let d = semtry b en  in
    match c,d with
      Undefined, _
    | _, Undefined -> Undefined
    | _ -> Int (valutaInt c - valutaInt d))
  | Times (a,b) -> (let c = semtry a en  in
    let d = semtry b en  in
    match c,d with
      Undefined, _
    | _, Undefined -> Undefined
    | _ -> Int (valutaInt c * valutaInt d))
  | And (a,b) -> (let c = semtry a en  in
    let d = semtry b en  in
    match c,d with
      Undefined, _
    | _, Undefined -> Undefined
    | _ -> Bool (valutaBool c && valutaBool d))
  | Or (a,b) -> (let c = semtry a en  in
    let d = semtry b en  in
    match c,d with
      Undefined, _
    | _, Undefined -> Undefined
    | _ -> Bool (valutaBool c || valutaBool d))
  | Not a -> (let b = semtry a en  in
    match b with
      Undefined -> Undefined
    | _ -> Bool (not (valutaBool (semtry a en ))))
  | Eq (a,b) -> Bool (semtry a en  = semtry b en )
  | Less (a,b) -> Bool (valutaInt (semtry a en ) < valutaInt (semtry b en ))
  | Cons (a,b) -> (let c = semtry b en in match c with
      Undefined -> Undefined
    | _ -> List ([semtry a en] @ valutaList (semtry b en)))
  | Head l -> (match (semtry l en ) with
      List a when List.length a != 0 -> List.hd a
    | _ -> failwith "Inserire una lista non vuota.")
  | Tail l -> (match (semtry l en ) with
      List a -> (match a with
	hd::tl -> List tl
      | _ -> failwith "Lista vuota.")
    | _ -> failwith "Inserire una lista.")
  | Fst p -> (match (semtry p en ) with
      Pair (a,b) -> a
    | _ -> failwith "Fst opera solo su coppie.")
  | Snd p -> (match (semtry p en ) with
      Pair (a,b) -> b
    | _ -> failwith "Snd opera solo su coppie.")
  | Epair (a,b) -> Pair (semtry a en , semtry b en )
  | Ifthenelse (a,b,c) -> if(valutaBool (semtry a en))
      then semtry b en
      else semtry c en 
  | Let (i,a,b) -> let c = semtry a en in let d = bind (en,i,c) in semtry b d
  | Fun (i,a) -> (let r = semtry a en  in
    let s = applyenv(en,i) in
    if(s = Undefined && r = Undefined)
    then Closure (ex,en)
    else if(s = Undefined)
    then Closure (ex,en)
    else r)
  | Appl (a,b) -> let c = semtry a en in let d = semtry b en in (match c with
      Closure (f,e) -> (match f with
	Fun(x,t) -> let g = bind (e,x,d) in semtry t g (*bind en,x,d*)
      | _ -> failwith "??? apply")
    | Undefined -> c
    | _ -> failwith "Apply si aspetta una funzione!")
  | Rec (i,a) -> let b = semtry a en in (match b with
      Closure(c,d) -> Closure(c,bind(d,i,b))
    | _ -> Closure(a,bind(en,i,Closure(a,en))))
  | Raise i -> semtry (Val i) en
  | Try (a,i,b) -> if(t a i) then semtry b en else semtry a en);;
