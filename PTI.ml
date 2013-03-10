(********************************************************)
(*	Inférence de types polymorphes en Caml				*)
(*  Interpreteur: Caml Light							*)
(*	Version: 1.0 Build: 1132.160112						*)
(*														*)
(* 	Cpyright BABIC Benjamin, (2010) 					*)
(*  benjamin.babic@homail.fr							*)
(*														*)
(*  Ce logiciel est un programme informatique servant 	*)
(*  à inférer des types en caml. 						*)
(*  Ce logiciel est régi par la licence CeCILL-C 		*)
(*	soumise au droit français et respectant les 		*)
(*	principes de diffusion des logiciels libres. 		*)
(*	Vous pouvez	utiliser, modifier et/ou redistribuer 	*)
(*	ce programme sous les conditions de la licence 		*)
(*	CeCILL-C telle que diffusée par le CEA, le CNRS 	*)
(*	et l'INRIA sur le site "http://www.cecill.info".	*)
(*														*)
(*  En contrepartie de l'accessibilité au code source 	*)
(*  et des droits de copie, de modification et de 		*)
(*  redistribution accordés par cette licence, il n'est *)
(*  offert aux utilisateurs qu'une garantie limitée.  	*)
(*  Pour les mêmes raisons, seule une responsabilité  	*)
(*  restreinte pèse sur l'auteur du programme, le		*)
(*  titulaire des droits patrimoniaux et les 			*)
(*  concédants successifs.								*)
(*  A cet égard  l'attention de l'utilisateur est 		*)
(*  attirée sur les risques associés au chargement,  	*)
(*  à l'utilisation,  à la modification et/ou au 		*)
(*  développement et à la reproduction du logiciel par 	*)
(*  l'utilisateur étant donné sa spécificité de 		*)
(*  logiciel libre, qui peut le rendre complexe à 		*)
(*  manipuler et qui le réserve donc à des développeurs *)
(*  et des professionnels avertis possédant des  		*)
(*  connaissances informatiques approfondies. Les		*)
(*  utilisateurs sont donc invités à charger et 		*)
(*  tester l'adéquation du logiciel à leurs besoins 	*)
(*  dans des conditions permettant d'assurer la			*)
(*  sécurité de leurs systèmes et ou de leurs données 	*)
(*  et, plus généralement, à l'utiliser et l'exploiter  *)
(*  dans les mêmes conditions de sécurité. 				*)
(*  													*)
(*  Le fait que vous puissiez accéder à cet en-tête 	*)
(*  signifie que vous avez pris connaissance de la 		*)
(*  licence CeCILL-C, et que vous en avez accepté les	*)
(*  termes.												*)
(********************************************************)

(*
I/ Objectif
	L'objectif de ce projet est de réaliser un système d'inférence de type en Caml.
Certaines fonctionnalité d'un système d'inférence de type réel seront omises; nous 
ne traiterons pas par exemple les fonction de type dans ce projet. Ceci exclut par
exemple les listes. 
*)

exception UnexceptedError;; (*définition triviale d'une erreur innatendue*)
exception Fail of string;; (*Ici on utilise un chaine pour présicer la nature et l'endroit de l'erreur.(CF partie 3) *)
exception Failure of string;;(*définition d'une erreur dans la recherche du type d'une variable (CF partie 4)*)

(* 
II/ Types polymorphes et substitutions
*)


(*Définition d'un type polymorphe*)
type tpoly = 
Tvar of string
|Tconst of string
|Tfonc of tpoly*tpoly
|Tpaire of tpoly*tpoly;;


(*EXEMPLES*)
(* [F(x)->int,bool] *)	
let tp1 = Tpaire(Tfonc(Tvar "x",Tconst "int"),Tconst("bool"));; 
(* F(x)->y *)
let tp2 = Tfonc(Tvar "x",Tvar "y");; 
(* [z,bool] *)
let tp3 = Tpaire(Tvar "z",Tconst("bool"));;
(* F(int)->[int,bool] *)
let tp4 = Tfonc(Tconst "int",Tpaire(Tconst "int",Tconst "bool"));;



(********************************************************) 
(* Description: Définition d'une substitution 			*)
(* Trace: string*Tpoly list 							*)
(********************************************************)
let sl1 = [("x",Tconst "int");("y",Tvar "x")];;
let sl2 = [("x",Tpaire(Tconst "int",Tconst "bool"))];;


(********************************************************) 
(* Description: Fonction qui a partir d'un Tpoly (Tvar  *)
(* ou Tconst) renvoie son image dans la liste de substi *)
(* tution. 												*)
(* Exemple: img (Tvar x,sl1) renvoie Tconst int.		*)
(* Trace: tpoly * (string * tpoly) list -> tpoly 		*)
(********************************************************) 
let rec img = fun 
(x,[])-> x
|(Tconst x,(a,b)::l) -> if x=a then b else img (Tconst x,l)
|(Tvar x,(a,b)::l) -> if x=a then b else img (Tvar x,l)
|(_,_) -> raise UnexceptedError;;


(********************************************************) 
(* Description: construit la fonction de substitution a *)
(* partir de la définition. 							*)
(* Trace: (string * tpoly) list -> tpoly -> tpoly		*)
(********************************************************) 
let rec build_sub  =  fun l -> fun
		(Tvar x) -> img(Tvar x,l)
		|(Tconst x) -> img(Tconst x,l)
		|(Tfonc (a,b)) -> Tfonc(build_sub l a,build_sub l b)
		|(Tpaire (a,b)) -> Tpaire(build_sub l a,build_sub l b);;
		

(********************************(*Test de la fonction: *)*******************************************) 
let s1 = build_sub sl1;;
let s2 = build_sub sl2;;

s1 (Tvar "x");;
(*tpoly = Tconst "int"*)
s2 tp1;;
(* tpoly = Tpaire (Tfonc (Tpaire (Tconst "int", Tconst "bool"), Tconst "int"), Tconst "bool") *)
(****************************************************************************************************) 


(********************************************************) 
(* Description: construit la subsitution obtenue par su *)
(* bstitutions successives de s1 puis s2				*)
(* Trace: (tpoly -> tpoly) -> 							*)
(*		  (tpoly -> tpoly) -> tpoly -> tpoly   			*)
(********************************************************) 
let compose_sub = fun (s1:tpoly->tpoly) -> fun (s2:tpoly->tpoly) -> fun tp -> s2 (s1 tp);;


(********************************(*Test de la fonction: *)*******************************************) 
(compose_sub s1 s2) tp2;;
(* tpoly = Tfonc (Tconst "int", Tpaire (Tconst "int", Tconst "bool")) *)


(compose_sub s2 s1) tp2;;
(* tpoly = Tfonc (Tpaire (Tconst "int", Tconst "bool"), Tvar "x") *)

(****************************************************************************************************) 

(*
III/ Unification
*)

(********************************************************) 
(* Description: applique une substitution a un systeme 	*)
(* d'equations représenté par une tpoly*tpoly list		*)
(* Trace: (tpoly -> tpoly) -> 							*)
(* (tpoly * tpoly) list -> (tpoly * tpoly) list 		*)
(********************************************************)
let rec sub_eq = fun (s:tpoly->tpoly) -> fun
[] -> []
|((tp1,tp2)::l) -> (s tp1,s tp2)::sub_eq s l;; 

(********************************(*Test de la fonction: *)*******************************************) 
let eq = [(tp1,tp3);(tp2,tp4)];;
(*(tpoly * tpoly) list =
 [Tpaire (Tfonc (Tvar "x", Tconst "int"), Tconst "bool"),
  Tpaire (Tvar "z", Tconst "bool");
  Tfonc (Tvar "x", Tvar "y"),
  Tfonc (Tconst "int", Tpaire (Tconst "int", Tconst "bool"))]*)
sub_eq s1 eq;;
(*(tpoly * tpoly) list =
 [Tpaire (Tfonc (Tconst "int", Tconst "int"), Tconst "bool"),
  Tpaire (Tvar "z", Tconst "bool");
  Tfonc (Tconst "int", Tvar "x"),
  Tfonc (Tconst "int", Tpaire (Tconst "int", Tconst "bool"))]*)

(****************************************************************************************************) 

(********************************************************) 
(* Description: renvoie true si x est libre dans tp 	*)
(********************************************************)
let rec is_free = fun x -> fun
(Tvar y) -> x<>y
|(Tconst y) -> x<>y
|(Tfonc (a,b)) -> is_free x a && is_free x b
|(Tpaire (a,b)) -> is_free x a && is_free x b;;

(********************************(*Test de la fonction: *)*******************************************) 
is_free "y" tp2;;
(* false *)
is_free "y" tp1;;
(* true *)
(****************************************************************************************************) 


(********************************************************) 
(* Description: revoie la chaine de caractère représen 	*)
(* tant le tpoly 										*)
(* Trace: tpoly -> string						 		*)
(********************************************************)
let rec printTpoly = fun
(Tvar x) -> x
| (Tconst c) -> c
| (Tfonc (tp1,tp2)) -> "("^printTpoly(tp1)^" -> "^printTpoly(tp2)^")"
| (Tpaire  (tp1,tp2)) -> "("^printTpoly(tp1)^" , "^printTpoly(tp2)^")";;


(********************************************************) 
(* Description: Fonction qui étant donné un système d'é	*)
(* quations et une subsitution renvoie la substitution 	*)
(* a telle que les tpoly du système puissent être unifi *)
(* és par a. 											*)
(* Trace: (tpoly * tpoly) list * (tpoly -> tpoly) 		*)
(*			-> tpoly -> tpoly						 	*)
(********************************************************)
let rec unif = fun 
([],s) -> s
| ((Tconst c1,Tconst c2)::l,s) -> 
	if c1<>c2 
	then raise (Fail("Clash between "^printTpoly(Tconst c1)^" and "^printTpoly(Tconst c2))) (*Clash*)
	else unif (l,s) (*Delete*)
| ((Tvar x,tp)::l,s) -> 
	let s2=compose_sub s (build_sub [(x,tp)]) in 
		if (Tvar x<>tp) then 
			if (is_free x tp) 
			then unif (sub_eq s2 l,s2)  (*Eleminate*)
			else raise (Fail("Checking failed: "^x^" is not free in "^printTpoly (tp))) (*Check*)
		else unif (l,s) (*Delete*)
| ((tp,Tvar x)::l,s) -> 
	let s2=compose_sub s (build_sub [(x,tp)]) in 
		if (Tvar x<>tp) then 
			if (is_free x tp) 
			then unif (sub_eq s2 l,s2)  (*Eleminate*)
			else raise (Fail("Checking failed: "^x^" is not free in "^printTpoly (tp))) (*Check*)
		else unif (l,s) (*Delete*)			
| ((Tconst c,tp)::l,s) -> raise (Fail("Fail near "^printTpoly(Tconst c)^" does not match with "^printTpoly(tp))) (*Fail*)
| ((tp,Tconst c)::l,s) -> raise (Fail("Fail near "^printTpoly(Tconst c)^" does not match with "^printTpoly(tp))) (*Fail*)
| ((Tfonc (tp1,tp2),Tfonc (tp3,tp4))::l,s) ->
	if (tp1=tp3 && tp2=tp4) 
	then unif(l,s) (*Delete*)
	else unif ([(tp1,tp3);(tp2,tp4)]@l,s) (*Decompose*)
| ((Tpaire (tp1,tp2),Tpaire (tp3,tp4))::l,s) ->
	if (tp1=tp3 && tp2=tp4) 
	then unif(l,s) (*Delete*)
	else unif ([(tp1,tp3);(tp2,tp4)]@l,s) (*Decompose*) 
| (_,_) -> raise UnexceptedError;;




(********************************(*Test de la fonction: *)*******************************************)
 let svide = build_sub [];;
 (*svide : tpoly -> tpoly*)
 
 let sres = unif ( [(tp2,tp4)],svide );;
 (*sres : tpoly -> tpoly*)
 sres (Tvar "x");;
 (*tpoly = Tconst "int"*)
 sres (Tvar "y");;
 (*tpoly = Tpaire (Tconst "int", Tconst "bool")*)
 sres (Tvar "z");;
 (*tpoly = Tvar "z"*)

 unif ([tp1,Tvar "x"],svide);;
 (*Exception non rattrapée: Fail "Checking failed on trying to associate x with ((x -> int) , bool)"*)
 
 let sres = unif ([(tp1,tp3);(tp2,tp4)],svide);;
 (*sres : tpoly -> tpoly*)
 sres (Tvar "x");;
 (*tpoly = Tconst "int"*)
 sres (Tvar "y");;
 (*tpoly = Tpaire (Tconst "int", Tconst "bool")*)
 sres (Tvar "z");;
 (*tpoly = Tfonc (Tvar "int", Tconst "int")*)
 
(****************************************************************************************************) 

(*
IV/ Inférence de types.
*)

(********************************************************) 
(* Description: Representation d'une constante.         *)
(********************************************************)
type constants =
Lint of int
| Lbool of bool;;

(********************************************************) 
(* Description: Representation d'une expression.        *)
(********************************************************)
type expression =
Lconst of constants
| Lvar of string
| Lapp of expression * expression
| Lfunc of string * expression;;


(********************************************************) 
(* Description: Crée une nouvelle variable dans un      *)
(* environnement donné, de sorte que cette nouvelle 	*)
(* variable de type soit libre dans env.				*)
(* RAPPEL: une variable considerée comme libre si elle  *)
(* n'apparait pas dans un environnement: d'ou la        *) 
(* différence avec le sujet.							*)
(* Trace: new_var : new_var : ('a * tpoly) list -> 		*)
(*								string = <fun>			*)
(********************************************************)
let new_var = fun env -> 
	let rec nv = fun n -> fun env -> fun
		([]) -> "h"^(string_of_int n)
		|((_,t)::r) -> if (not is_free("h"^(string_of_int n)) t) then (nv (n+1) env env) else (nv n env r) in  
(nv 0 env env);;


(********************************************************) 
(* Description: renvoie le type d'une variable d'un 	*)
(* environnement										*)
(* Trace: get_env_type : string -> 						*)
(*				(string * tpoly) list -> tpoly = <fun>	*)
(********************************************************)
let rec get_env_type = fun (v:string) -> fun 
 [] -> raise (Failure("Var "^v^" undeclared."))		
 |((a,(t:tpoly))::l) -> if v=a then t else get_env_type v l;;
 
 
(********************************(*Test des  fonctions et des types: *)******************************)
(*type expression*)
let e1 = Lfunc ("x", Lapp (Lvar "carre",Lvar "x"));; 
let e2 = Lfunc ("x", Lapp (Lvar "x", Lvar "x"));;
let e3 = Lapp (Lapp (Lvar "f", Lconst (Lint 3)), Lconst (Lbool true));;
let e4 = Lapp (Lapp ( Lfunc ("x", Lfunc ("y", Lapp (Lapp (Lvar "g", Lvar "x"), Lvar "y"))), Lconst (Lint 4)), Lapp (Lfunc ("z", Lapp (Lvar "h", Lvar "z")),  Lconst(Lbool true)));;

let  env1  =  [  ("carre",  Tfonc  (Tconst  "int",  Tconst  "int"));
				("h",  Tfonc  (Tvar  "a",  Tconst  "bool"));
				("g",  Tvar  "b")];;

new_var [("x", Tvar "h0");("y", Tvar "h1");("z", Tvar "h2");("w", Tvar "h4")];;
(*- : string = "h3"*)	 
get_env_type "carre" env1;;
(*- : tpoly = Tfonc (Tconst "int", Tconst "int")*)
get_env_type "x" env1;;
(*Exception non rattrapée: Failure "variable non declarée"*)
(****************************************************************************************************) 

(********************************************************) 
(* Description: applique une substtution a un environem-*)
(* ment													*)
(* Trace: get_env_type : (tpoly -> tpoly) -> 			*)
(*						(string * tpoly) list -> 		*)
(*						(string * tpoly) list = <fun>	*)
(********************************************************)
let rec map_unif = fun (sigma:(tpoly->tpoly)) -> fun 
([]) -> []
|((a,t)::(l:(string*tpoly) list)) -> (a,sigma t)::(map_unif sigma l);;
	
 
let rec principal_type = fun (env:(string*tpoly) list) -> fun 
(Lconst (Lint _)) -> (env,Tconst "int")
|(Lconst (Lbool _)) -> (env,Tconst "bool")
|(Lvar x) -> (env,(get_env_type x env)) 
|(Lfunc (x,e)) -> let C=Tvar (new_var env) in 
				  let ((x,A)::env1,B)=(principal_type ((x, C)::env) e) in 
				  (env1,Tfonc (A,B)) 
|(Lapp (f,a)) -> let (env1,F)=(principal_type env f) in 
				 let (env2,A)=(principal_type env1 a) in
				 let B=Tvar (new_var env2) in
				 let sigma=unif ([(F,Tfonc (A,B))],svide) in
				 ((map_unif sigma env2),sigma B);;

				 
(********************************(*Test des  fonctions *)******************************)
(*principal_type*)

principal_type  env1  e1;;
(*(string * tpoly) list * tpoly =
 ["carre", Tfonc (Tconst "int", Tconst "int");
  "h", Tfonc (Tvar "a", Tconst "bool"); "g", Tvar "b"],
 Tfonc (Tconst "int", Tconst "int")*)
 
principal_type  env1  e2;;
(*Exception non rattrapée: Fail "Checking failed: h0 is not free in (h0 -> h1)"*)

principal_type  env1  e3;;
(*Exception non rattrapée: Failure "Var f undeclared."*)

principal_type  [("f",  Tvar  "a")]  e3;;
(*["f", Tfonc (Tconst "int", Tfonc (Tconst "bool", Tvar "h1"))], Tvar "h1"*)

principal_type  env1  e4;;
(*(string * tpoly) list * tpoly =
 [("z", Tconst "bool"); ("y", Tconst "bool"); ("x", Tconst "int");
"carre", Tfonc (Tconst "int", Tconst "int");
  "h", Tfonc (Tconst "bool", Tconst "bool");
  "g", Tfonc (Tconst "int", Tfonc (Tconst "bool", Tvar "h0"))],
 Tvar "h0"*)
(****************************************************************************************************) 



