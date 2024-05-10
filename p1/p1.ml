(* Práctica 1 *)
open Conj;;
open Auto;;
open Ergo;;
open Graf;;


let afd1 = af_of_string "0 1 2; 	a b; 	0; 	2;	    0 1 a; 1 1 b; 1 2 a;";;

let afd2 = af_of_string "1 2 3;		a b; 	1; 	3; 	    1 2 a; 2 2 b; 2 3 a;";;

let afd3 = af_of_string "0 1 2; 	a b; 	0; 	0 2;    0 1 a; 1 1 a; 1 2 b; 2 2 a; 2 2 b;";;

let afd4 = af_of_string "0 1 2 3;   a b;    0;  0 2 3;  0 1 a; 1 2 b; 2 3 a; 3 3 a; 3 3 b; 1 1 a; 2 2 b;";;

(*
equivalentes afd1 afd2 (true);;
equivalentes afd1 afd3 (false);;
equivalentes afd3 afd4 (true);;
*)

(* Ejercicio 1 *)

(* Implemente una función es_afne : Auto.af -> bool que reciba como argumento un autómata
finito, y que devuelva true si se trata de un autómata que presenta alguna épsilon-transición, o false en
caso contrario. *)
let es_afne = function Af (_,_,_,(Conjunto transc),_) ->
	let rec aux = function
		| [] -> false
		| Arco_af (_,_,simb)::t -> if simb = Terminal "" then true else aux t
in aux transc;; 

(* Implemente una función es_afn : Auto.af -> bool que reciba como argumento un autómata
finito, y que devuelva true si se trata de un autómata que presenta algún tipo de no determinismo
(excepto épsilon-transiciones), o false en caso contrario. *)
let es_afn = function Af (_,_,_,(Conjunto transc),_) -> 
	let rec aux c1 c2 = match c1 with
	| [] -> false
	| Arco_af (a,b,s)::t -> let par = (a,b) in if pertenece par c2 then true else aux t (agregar par c2)  
in aux transc (Conjunto []);;

(* Implemente una función es_afd : Auto.af -> bool que reciba como argumento un autómata
finito, y que devuelva true si se trata de un autómata totalmente determinista, o false en caso contrario. *)
let es_afd auto = if es_afn auto then false else not (es_afne auto);;

(* Ejercicio 2 *)

(* Implemente una función equivalentes : Auto.af -> Auto.af -> bool que reciba como
argumentos dos autómatas finitos y que devuelva true cuando ambos autómatas acepten el mismo
lenguaje, o false en caso contrario. *)



(* Esta función auxiliar se usa para comprobar si dos estados pf1 y pf2, 
   dados el conjunto de estados finales f1 y f2, los dos son finales. En el
   caso de que sean se devuelve true, en caso contrario false. *)
let dispares (Conjunto f1) (Conjunto f2) (pf1, pf2) = 
    if ((pertenece pf1 (Conjunto f1)) && (not (pertenece pf2 (Conjunto f2)))) 
    || ((not (pertenece pf1 (Conjunto f1))) && (pertenece pf2 (Conjunto f2))) 
then true else false;;

(* Esta otra función auxiliar se usa para conseguir el conjunto de estados
   a los que se puede ir desde un origen con un símbolo en concreto. *)
let estadosPosibles (Conjunto transc) estado simbolo =
	let rec aux transc estado simb = match transc with
	| Arco_af (og, dest, simb)::t -> if (estado = og) && (simb = simbolo) then dest else aux t estado simb
    | [] -> Estado "NULL"
in aux transc estado simbolo;;


let equivalentes (Af (e1, a, i1, t1, f1)) (Af (e2, _, i2, t2, f2)) =
  let rec colaVaciaONo visitados cola =
    if cola = [] then true
    (* Si esta vacía la cola, eso significa que se han recorrido todos
    los estados y que los automatas aceptan el mismo lenguaje. *)
    else 

        let (ea1, ea2) = List.hd cola in 
        if pertenece (ea1, ea2) visitados then colaVaciaONo visitados (List.tl cola)
        (* Si el estado actual ya fue visitado, no se agrega a la cola *)
        else 
            
            if dispares f1 f2 (ea1, ea2) then false
            (* Si los estados son dispares (un estado es final y el otro no),
            los automatas no son equivalentes, por lo tanto se devuelve false *)
            else 
                
                let rec aux alfab cola2 visitados2 =
                if alfab = [] then colaVaciaONo visitados2 cola2
                (* Si la lista del alfabeto queda vacía, ejecuta colaVaciaONo con el nuevo 
                conjunto de visitados y la cola con los siguientes estados a visitar *)
                else  
                    (* Se calculan los estados a los que se puede transicionar desde ea1 y ea2 utilizando el primer símbolo del alfabeto. *)
                    let (ne1, ne2) = (estadosPosibles t1 ea1 (List.hd alfab), estadosPosibles t2 ea2 (List.hd alfab)) in
                    
                    (* Se verifica si ambos estados resultantes (ne1 y ne2) son nulos. *)
                    if ne1 = Estado "NULL" && ne2 = Estado "NULL" 

                    (* Si ambos estados son NULL, no se agrega a la cola y se sigue con el siguiente símbolo del alabeto. *)
                    then aux (List.tl alfab) cola2 visitados2

                    (* Si al menos uno de los estados no es nulo, se agrega el par de estados a la cola. *)
                    else aux (List.tl alfab) (List.rev_append (List.rev cola2) [(ne1, ne2)]) visitados2

                (* Seguimos la búsqueda de estados. *)
                in aux (list_of_conjunto a) cola (agregar (ea1, ea2) visitados)

in colaVaciaONo conjunto_vacio [(i1, i2)];; (* Para empezar se meten en la cola los dos estados iniciales de cada autómata. *)