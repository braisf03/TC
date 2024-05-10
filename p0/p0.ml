(* Práctica 0 *)
(* Ejercicio 1 *) 

let mapdoble f1 f2 l = 
  let rec aux  l1 l2 = match l1 with 
    | [] -> List.rev l2
    | h::[] -> List.rev ((f1 h)::l2)
    | h1::h2::t -> aux t ((f2 h2)::(f1 h1)::l2)
  in aux l [];;

(* 
 Indique el tipo de la función mapdoble.
val mapdoble : ('a -> 'b) -> ('a -> 'b) -> 'a list -> 'b list = <fun> 

 Indique el valor de:
 mapdoble (function x -> x*2) (function x -> "x") [1;2;3;4;5];;
 Error: This expression has type string but an expression was expected of type int.
 Esto se debe a que las listas en ocaml son homogéneas y no pueden tener dos 
 tipos de datos en la misma lista.

 Indique el tipo de:
 let y = function x -> 5 in mapdoble y;;
 - : ('_weak1 -> int) -> '_weak1 list -> int list = <fun> 
 Significa que toma una función que toma un tipo no especificado
*)




(* Ejercicio 2 *) 
(* Devuelve el primer elemento de la lista que cumple con el predicado f *)
let primero_que_cumple f l = 
  let rec aux l = match l with
    | [] -> raise (Not_found)
    | (h::t) -> if f h then h else aux t
  in aux l;;

(* val primero_que_cumple : ('a -> bool) -> 'a list -> 'a = <fun> *)

let rec existe f l = try f (primero_que_cumple f l) with Not_found -> false;;
(* Esta funcion hace uso de un try para que en el caso de un Not_found de un false.*)

let rec asociado l key = snd (primero_que_cumple (function (a,b) -> a = key) l);;
(* Esta función coge una lista y un elemento y coge el segundo elemento del par que devuelve
 la funcion primero_que_cumple con la key*)


(* Ejercicio 3 *)
  
type 'a arbol_binario =
    Vacio
  | Nodo of 'a * 'a arbol_binario * 'a arbol_binario;;

(* El recorrido in_orden saca los elementos i-r-d por eso hace primero la izquierda luego
concatena las raices y luego la derecha. *)
let in_orden tree = 
  let rec aux l arb = match arb with
    | Vacio -> l
    | Nodo (r,i,d) -> aux ( r :: aux l d) i
  in aux [] tree
;;

(* El recorrido pre_orden saca los elementos r-i-d por eso hace primero las raíces luego
la parte izquierda y luego la derecha. *)
let pre_orden tree = 
  let rec aux l arb = match arb with
    | Vacio -> l
    | Nodo (r, i, d) -> r :: aux (aux l d) i
  in aux [] tree;;
  
(* El recorrido post_orden saca los elementos i-d-r por eso hace primero la parte izquierda
luego la parte derecha y por último concatena las raíces.  *)
let post_orden tree =
  let rec aux l1 arb = match arb with
    | Vacio -> List.rev l1
    | Nodo (r, i, d) -> let l2 = r :: l1 in aux (aux l2 d) i
  in aux [] tree;;
  
(* El recorrido en anchura lo que hace es recorrer el árbol por sus alturas, primero hace el
h=1 luego el h=2 y así sucesivamente. *)
let anchura arb = 
  let rec aux cola l = match cola with
    | [] -> List.rev l
    | Vacio :: t -> aux t l
    | Nodo (r, i, d) :: t -> let cola' = t @ [i; d] in aux cola' (r::l)
  in aux [arb] [];;
  

(* Ejercicio 4 *)

type 'a conjunto = Conjunto of 'a list;;

(* val pertenece : 'a -> 'a conjunto -> bool = <fun> *)
let pertenece e (Conjunto c) = List.mem e c;;

(* val agregar : 'a -> 'a conjunto -> 'a conjunto = <fun> *)
let agregar e (Conjunto c) = if List.mem e c 
  then (Conjunto c) else Conjunto (e::c);;

(* val conjunto_of_list : 'a list -> 'a conjunto = <fun> *)
let conjunto_of_list l = Conjunto l;;

(* val suprimir : 'a -> 'a conjunto -> 'a conjunto = <fun> *)
let suprimir e (Conjunto c) = Conjunto (List.filter (fun y -> y <> e) c);;

(* val cardinal : 'a conjunto -> int = <fun> *)
let cardinal (Conjunto c) = List.length c;;

(* val union : 'a conjunto -> 'a conjunto -> 'a conjunto = <fun> *) 
let union (Conjunto c1) (Conjunto c2) =
  let rec aux ca cb = match ca with 
      [] -> Conjunto (List.rev cb)
    | h::t -> if List.mem h cb then aux t cb 
        else aux t (h::cb)
  in aux c1 c2;;

(* val interseccion : 'a conjunto -> 'a conjunto -> 'a conjunto = <fun> *)
let interseccion (Conjunto c1) (Conjunto c2) =
  let rec aux (ca,cb) = match ca with 
      [] -> Conjunto (List.rev cb)
    | h::t -> if List.mem h c2 then aux (t,(h::cb)) else aux (t,cb)
  in aux (c1,[]);;

(* val diferencia : 'a conjunto -> 'a conjunto -> 'a conjunto = <fun> *)
let diferencia (Conjunto c1) (Conjunto c2) =
  let rec aux (ca,cb) = match ca with 
      [] -> Conjunto (List.rev cb)
    | h::t -> if List.mem h c2 then aux (t,cb) else aux (t,(h::cb))
  in aux (c1,[]);;

(* val incluido : 'a conjunto -> 'a conjunto -> bool = <fun> *)
let incluido (Conjunto c1) (Conjunto c2) =
  let rec aux c = match c with 
      [] -> true
    | h::t -> if List.mem h c2 then aux t else false
  in aux c1;;

(* val igual : 'a conjunto -> 'a conjunto -> bool = <fun> *)
let igual (Conjunto c1) (Conjunto c2) =
  if List.length c1 <> List.length c2 then false 
  else let rec aux c = match c with 
        [] -> true
      | h::t -> if List.mem h c2 then aux t else false
    in aux c1;;

(* val producto_cartesiano : 'a conjunto -> 'b conjunto -> ('a * 'b) conjunto = <fun> *)
(*  ca es la lista de elementos restantes en el primer conjunto.
    cb es el segundo conjunto.
    cc es una lista acumulativa que contiene los pares ordenados del producto cartesiano.
    cd es una copia del primer conjunto original. *)
    
let producto_cartesiano (Conjunto c1) (Conjunto c2) = 
  let rec aux (ca,cb,cc,cd) = match (ca,cb) with 
      ([],_) -> (Conjunto (List.rev cc))
    | (_,[]) -> aux ((List.tl cd),c2,cc,(List.tl cd))
    | (h1::t1,h2::t2) -> aux (h1::t1,t2,((h1,h2)::cc),cd)
  in aux (c1,c2,[],c1);;
  
(* val list_of_conjunto : 'a conjunto -> 'a list = <fun> *)
let list_of_conjunto (Conjunto c) = c;;
