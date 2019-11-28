exception Exception;;
exception Exception2 of string;;
exception WrongOp;;
exception DontCare;;
exception NotSubProp;;
exception NotSatisfiable;;


type prop = T | F | L of string 
                  | Not of prop
                  | And of prop * prop | Or of prop * prop | Impl of prop * prop | Iff of prop * prop;;
;;


let rec ht p= match p with 
			T ->0| F -> 0| L s-> 0
			| Not p1 -> 1+ (ht p1)
			| And(p1,p2) -> if (ht p1)>(ht p2) then 1+ (ht p1) else 1+(ht p2)
			| Or(p1,p2) -> if (ht p1)>(ht p2) then 1+ (ht p1) else 1+(ht p2)
			| Impl(p1,p2) -> if (ht p1)>(ht p2) then 1+ (ht p1) else 1+(ht p2)
			| Iff(p1,p2) -> if (ht p1)>(ht p2) then 1+ (ht p1) else 1+(ht p2)  
;;

let rec size p= match p with 	
			T ->1 | F -> 1 | L s->1
			| Not p1 -> 1+ (size p1)
			| And(p1,p2) -> 1+ (size p1) +(size p2)
			| Or(p1,p2) -> 1+ (size p1) +(size p2)
			| Impl(p1,p2) -> 1+ (size p1) +(size p2)
			| Iff(p1,p2) ->	1+ (size p1) +(size p2)
;;

let rec union l1 l2 =match l1 with
		[]-> l2
		|x::xs-> if (List.mem x l2) then union xs l2 else [x]@(union xs l2)
;;		 

let rec letters p=match p with 
			| T ->[] | F -> [] | L s->[s]
			| Not p1 -> letters p1
			| And(p1,p2) -> union (letters p1) (letters p2)
			| Or(p1,p2) -> union (letters p1) (letters p2)
			| Impl(p1,p2) -> union (letters p1) (letters p2)
			| Iff(p1,p2) ->	union (letters p1) (letters p2)
;;

let rec subprop_help p1 p2 l=match p2 with
			T-> (if p1=T then l else raise NotSubProp)
			| F-> (if p1=F then l else raise NotSubProp)
			| L s -> (if p1=(L s) then l else raise NotSubProp)
			| Not q-> if p1=q then l else (try (subprop_help p1 q l@[2]) with NotSubProp -> raise NotSubProp)
			| And(q1,q2)-> if p1=q1 then l@[0] else if p1=q2 then l@[1] else (try (subprop_help p1 q1 l@[0]) with NotSubProp-> (try (subprop_help p1 q2 l@[1]) with NotSubProp-> raise NotSubProp))
			| Or(q1,q2)-> if p1=q1 then l@[0] else if p1=q2 then l@[1] else (try (subprop_help p1 q1 l@[0]) with NotSubProp-> (try (subprop_help p1 q2 l@[1]) with NotSubProp-> raise NotSubProp))
			| Impl(q1,q2)-> if p1=q1 then l@[0] else if p1=q2 then l@[1] else (try (subprop_help p1 q1 l@[0]) with NotSubProp-> (try (subprop_help p1 q2 l@[1]) with NotSubProp-> raise NotSubProp))
			| Iff(q1,q2)-> if p1=q1 then l@[0] else if p1=q2 then l@[1] else (try (subprop_help p1 q1 l@[0]) with NotSubProp-> (try (subprop_help p1 q2 l@[1]) with NotSubProp-> raise NotSubProp))
;;			

let rec subprop_at p1 p2= (try List.rev(subprop_help p1 p2 []) with NotSubProp-> raise NotSubProp)
;;

let rec truth p rho = match p with 
		T-> true
		| F-> false
		| L s -> (try rho s with DontCare-> raise DontCare)
		| Not p1 -> not (truth p1 rho)
		| And(p1,p2) -> (truth p1 rho) && (truth p2 rho)
		| Or(p1,p2) -> (truth p1 rho) || (truth p2 rho)	  
		| Impl(p1,p2) -> (not (truth p1 rho)) || (truth p2 rho)	
		| Iff(p1,p2) -> ((not (truth p1 rho)) || (truth p2 rho)) && ((not (truth p2 rho)) || (truth p1 rho))
;;

let rec nnf_help p = match p with
		 T-> p | F-> p | L s -> p
		| Not T -> F
		| Not F -> T
		| Not L s -> p		
		| Not Not p1 -> nnf_help p1
		| Not And(p1, p2) -> Or(nnf_help (Not p1),nnf_help (Not p2))
	    | Not Or(p1, p2) -> And(nnf_help (Not p1),nnf_help (Not p2))
	    | And(p1,p2) -> And(nnf_help p1, nnf_help p2)
		| Or(p1,p2) -> Or(nnf_help p1, nnf_help p2)
;;

let rec rem p=match p with
		 T-> p | F-> p | L s -> p
		| Not T -> F
		| Not F -> T
		| Not p -> Not (rem p)
		| And(p1,p2) -> And(rem p1, rem p2)
		| Or(p1,p2) -> Or(rem p1, rem p2)
		| Impl(p1,p2) -> Or(rem (Not (p1)),rem p2)
		| Iff(p1,p2) -> And(Or(rem (Not (p1)),rem p2),Or(rem (Not (p2)),rem p1))
;;

let nnf p=nnf_help (rem p);;


let rec nnf_to_cnf p= match p with
		T-> p | F-> p | L s -> p 
		| Not T -> F
		| Not F -> T
		| Not (L s)-> p
		| And(p1,p2)-> And(nnf_to_cnf p1, nnf_to_cnf p2)
		| Or(And(p1,p2),And(p3,p4))-> And(And(nnf_to_cnf (Or(p1, p3)),nnf_to_cnf (Or(p1, p4))), And(nnf_to_cnf (Or(p2, p3)), nnf_to_cnf (Or(p2, p4))))		
  		| Or(And(p2, p3), p1) -> And(nnf_to_cnf (Or(p1, p2)),nnf_to_cnf (Or(p1, p3)))
  		| Or(p1, And(p2, p3)) -> And(nnf_to_cnf (Or(p1, p2)),nnf_to_cnf (Or(p1, p3)))
		| Or(p1,p2)-> Or(nnf_to_cnf p1, nnf_to_cnf p2)
;;

let rec nnf_to_dnf p= match p with 
		T-> p | F-> p | L s -> p 
		| Not T -> F
		| Not F -> T
		| Not p1-> Not (nnf_to_dnf p1)
		| Or(p1,p2)-> Or(nnf_to_dnf p1, nnf_to_dnf p2)
		| And(Or(p1,p2),Or(p3,p4))-> Or(Or(nnf_to_dnf (And(p1, p3)),nnf_to_dnf (And(p1, p4))), Or(nnf_to_dnf (And(p2, p3)),nnf_to_dnf (And(p2, p4))))
		| And(Or(p1,p2),p3)-> Or(nnf_to_dnf (And(p1, p2)),nnf_to_dnf (And(p1, p3)))
		| And(p1,Or(p2,p3))-> Or(nnf_to_dnf (And(p1, p2)),nnf_to_dnf (And(p1, p3)))
		| And(p1,p2)-> And(nnf_to_dnf p1, nnf_to_dnf p2)		
;;

let cnf1 p=nnf_to_cnf (nnf p)
;;
let dnf1 p=nnf_to_dnf (nnf p)
;; 

let rec cnf p= let x= (cnf1 p) in if x=(cnf1 x) then x else cnf x
;;
let rec dnf p= let x= (dnf1 p) in if x=(dnf1 x) then x else dnf x
;;

 


let rho s=match s with
	"p"-> true
	|"q"-> true
	|"r"-> false
	|"s"-> false
(* 	|"x1"-> false
	|"x2"-> true
	|"x3"-> true *)
;;



let initT tt = let s=List.length (letters tt) in [(1,(s+1,-1,-1));(0,(s+1,-1,-1))]
;;

let add tt u (i,h,l)= (u,(i,h,l))::tt
;;

let rec get_tup tt u = match tt with
	[]->(-1,-1,-1)
	|(u1,x)::xs-> if (u=u1) then x else get_tup xs u
;;	

let var tt u = let x = get_tup tt u in match x with (i,l,h)->i
;;
let low tt u = let x = get_tup tt u in match x with (i,l,h)->l
;;
let high tt u = let x = get_tup tt u in match x with (i,l,h)->h
;;


let initH=[];;

let rec member hh (i,l,h) = match hh with 
	[]->false
	|((i1,l1,h1),u1)::xs -> if (i=i1)&&(l=l1)&&(h=h1) then true else member xs (i,l,h)
;;

let rec lookup hh (i,h,l) = match hh with 
	[] -> -1
	|((i1,l1,h1),u1)::xs -> if (i=i1)&&(l=l1)&&(h=h1) then u1 else lookup xs (i,l,h)
;;

let rec insert hh u (i,h,l) = ((i,h,l),u)::hh
;;

let u_current = ref (1);;

let tableT = ref (initT T);;

let tableH =ref (initH) ;; 

let mk (i,h,l) = if (l=h) then l else 
				(
					if (member (!tableH) (i,h,l)) then (lookup (!tableH) (i,h,l)) else 
					(
						let x=(!u_current)+1 in 
							(tableT := ( add (!tableT) x (i,h,l)) ; tableH := (insert (!tableH) x (i,h,l)) ; u_current := x;
							 x )
					)
				)
;;

(* let mk (i,h,l)= (mk_help (i,h,l) tableH tableT u_current)
;; *)


let rec sub p x n = match p with 
		T-> T
		| F-> F
		| L s -> if (s=x) then n else (L s)
		| Not p1 ->  Not (sub p1 x n)
		| And(p1,p2) -> And((sub p1 x n),(sub p2 x n))
		| Or(p1,p2) -> Or((sub p1 x n), (sub p2 x n))	  
		| Impl(p1,p2) -> Impl((sub p1 x n), (sub p2 x n))	
		| Iff(p1,p2) -> Iff((sub p1 x n), (sub p2 x n))	
;;	

let rec build_dash t i l1 n=(if (i>n) then (if (truth t rho) then 1 else 0) else
				(let h=(build_dash (sub t (List.nth l1 (i-1)) F) (i+1) l1 n) in let l=(build_dash (sub t (List.nth l1 (i-1)) T) (i+1) l1 n) in (mk (i,h,l)) ) )
;;

let build t = tableT := (initT t); tableH := initH; u_current := 1; let l=(letters t) in let n=(List.length l) in (build_dash t 1 l n);;

let fun_op op u1 u2=match op with
		"AND" -> if (u1=1&&u2=1) then 1 else 0
	  |"OR" -> if (u1=1||u2=1) then 1 else 0
	  |"IMPL" -> if ((u1=0) || (u2=1)) then 1 else 0
	  |"IFF" ->  if (u1=u2) then 1 else 0
	  |_ -> (raise WrongOp)
;;


let rec presentinGraph g u1 u2= match g with
	[] -> false
	|(u11,u22,u)::xs-> if ((u1=u11)&&(u2=u22)) then true else (presentinGraph xs u1 u2)
;;
let rec findinGraph g u1 u2= match g with
	[] -> -1
	|(u11,u22,u)::xs-> if ((u1=u11)&&(u2=u22)) then u else (findinGraph xs u1 u2)
;;
let addtoGraph g u1 u2 u= (u1,u2,u)::g
;;

let tableT1 = ref (initT T);;
let tableT2 = ref (initT T);;
let g = ref ([])

let rec app op u1 u2 = if (presentinGraph (!g) u1 u2) then (findinGraph (!g) u1 u2) else 
				(if ((u1=0||u1=1)&&(u2=0||u2=1)) then (let x=(fun_op op u1 u2) in g:=(addtoGraph (!g) u1 u2 x); x) 
					else (if ((var (!tableT1) u1)=(var (!tableT2) u2)) then let x1=(mk ((var (!tableT1) u1), (app op (low (!tableT1) u1) (low (!tableT2) u2) ), (app op (high (!tableT1) u1) (high (!tableT2) u2) )) ) in g:=(addtoGraph (!g) u1 u2 x1); x1
					else (if ((var (!tableT1) u1)<(var (!tableT2) u2)) then let x2=(mk ((var (!tableT1) u1), (app op (low (!tableT1) u1) u2 ), (app op (high (!tableT1) u1) u2 )) ) in g:=(addtoGraph (!g) u1 u2 x2); x2
					else (let x3=(mk ((var (!tableT2) u2), (app op u1 (low (!tableT2) u2) ), (app op u1 (high (!tableT2) u2) )) ) in g:=(addtoGraph (!g) u1 u2 x3); x3)
				)))
;;


let apply op u1 u2 = (* tableT1 := table1 ; tableT2 := table2 ; *) g := [] ; (app op u1 u2)
;;


let rec res u j b= if ((var (!tableT) u)>j) then u else 
				(if ((var (!tableT) u)<j) then (mk ((var (!tableT) u),(res (low (!tableT) u) j b),(res (high (!tableT) u) j b))) else
					(if (b=0) then (res (low (!tableT) u) j b) else (res (high (!tableT) u) j b)
					)
				) 
;;

let restrict u j b= u_current := 1;(res u j b)
;;

let rec anysat u = if (u=0) then (raise NotSatisfiable) else 
				(if (u=1) then [] else
					(if ((low (!tableT) u)=0) then (((var (!tableT) u),1)::(anysat (high (!tableT) u))) else
						(((var (!tableT) u),0)::(anysat (low (!tableT) u)))
				))
;;


let rec addatFront f l= match l with
	[]->[]
	|x::xs-> (f::x)::(addatFront f xs)
;;

let rec allsat u = if (u=0) then [] else 
				(if (u=1) then [[]] else
					( (addatFront ((var (!tableT) u),0) (allsat (low (!tableT) u)))@(addatFront ((var (!tableT) u),1) (allsat (high (!tableT) u)))
				))
;;

let rec sim d u= if (d=0) then 0 else
			(if (u<=1) then u else 
			(if (d=1) then (mk ((var (!tableT1) u), (sim d (low (!tableT1) u)), (sim d (high (!tableT1) u)))) else
			(if ((var (!tableT2) d)=(var (!tableT1) u)) then 
							( if ((low (!tableT2) d)=0) then (sim (high (!tableT2) d) (high (!tableT1) u)) else 
							( if ((high (!tableT2) d)=0) then (sim (low (!tableT2) d) (low (!tableT1) u)) else
								( mk ((var (!tableT1) u), (sim (low (!tableT2) d) (low (!tableT1) u)), (sim (high (!tableT2) d) (high (!tableT1) u))) )
							)) else
			( if ((var (!tableT2) d)<(var (!tableT1) u)) then (mk ((var (!tableT2) d), (sim (low (!tableT2) d) u), (sim (high (!tableT2) d) u))) else 
				( mk ((var (!tableT1) u), (sim d (low (!tableT1) u)), (sim d (high (!tableT1) u))))
			))))
;;	

let simplify d u= u_current := 1; (sim d u)
;;



(* let vx1 = L "x1";;
let vx2 = L "x2";;
let vx3 = L "x3";;

let p0 = Iff(vx1, vx2);;
let p1 = Or(p0,vx3);;
let p2 = Or(vx2,vx3);;
let np1 = Not(p1);;

(* compute NNF, CNF of p1 and Not(p1) *)
let p1' = nnf(p1);;
let p1'' = cnf(p1);;
let np1' = nnf(np1);;
let np1'' = cnf(np1);;

(* build ROBDDs *)
let tt = build T;;
let tf = build F;;

let tvx1 = build vx1;;
let tp2 = build p2;;
let tp0 = build p0;;
let tp1 = build p1;;
let tp1' = build p1';;
let tp1'' = build p1'';;

let tnp1 = build np1;;
let tnp1' = build np1';;
let tnp1'' = build np1'';;

(* Testcase #1 *)
tp1 = tp1';;
tp1 = tp1'';;
tnp1 = tnp1';;
tnp1 = tnp1'';;

(* Testcase #2 *)
let tp1 = build p1;;
tableT1 := !tableT;;
let tnp1 = build np1;;
tableT2 := !tableT;;
let tp1anp1 = apply "AND" tp1 tnp1;;
tp1anp1 = tf;;
let tp1onp1 = apply "OR" tp1 tnp1;;
tp1onp1 = tt;;

(* Testcase #3 *)
let tp1 = build p1;;
let tp1rv30 = restrict tp1 3 0;;
tp1rv30 = tp0;;

let tp1 = build p1;;
let tp1rv31 = restrict tp1 3 1;;
tp1rv31 = tt;;

(* Testcase #4 *)
let tp1 = build p1;;
allsat tp1;; (* 4 solutions: { {x1 = 0, x2 = 0}, {x1 = 1, x2 = 1}, {x1 = 1, x2 = 0, x3 = 1}, {x1 = 0, x2 = 1, x3 = 1}} *)
anysat tp1;; (* any of the above *)

(* Testcase #5 *)
let tp1 = build p1;;
tableT1 := !tableT;;
let tp2 = build p2;;
tableT2 := !tableT;;
let tstp2tp1 = simplify tp2 tp1;;
tstp2tp1 == tt;;


let tp1 = build p1;;
tableT1 := !tableT;;
let tvx1 = build vx1;;
tableT2 := !tableT;;
let tstvx1tp1 = simplify tvx1 tp1;;
tstvx1tp1 = tp2;; *)




