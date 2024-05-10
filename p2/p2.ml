(* Práctica 2 *)
#load "tald.cma";;
open Conj;;
open Auto;;
open Ergo;;
open Graf;;

let gic0 = gic_of_string "S A B C; a b; S;
                          S -> A B | B C;
                          A -> B A| a;
                          B -> C C | b;
                          C -> A B | a;";;



let gic1 = gic_of_string "S A B; a b c; S;  
                          S -> a A;
                          A -> a b c A | b B;
                          B -> b c B | a;";;

let cadena0 = cadena_of_string "b b a b";;

let cadena1 = cadena_of_string "b b b b";;

(* ----Ejercicio1---- *)

(* Esta función lo que hace es comprobar si el GIC esta en Forma Normal de Chomsky, lo que hace
es pasar por todas las reglas confirmando que se va a un simbolo terminal o a dos simbolos no
terminales. Si pasa todas las reglas y se cumplen las condiciones, entonces da true, false en
caso contrario. *)
let es_fnc (Gic(_,_,Conjunto r,_)) = 
  let rec aux rs = match rs with 
  | [] -> true 
  | Regla_gic (No_terminal _,[No_terminal _; No_terminal _])::t
  | Regla_gic (No_terminal _,[Terminal _])::t -> aux t
  | _ -> false 
in aux r;;

(* ----Ejercicio2---- *)

(* Esta función busca las reglas de la gramática que pueden generar un símbolo terminal y las devuelve en un conjunto. *)
let rec primeraFila acc sim = function
    [] -> acc
  | (Regla_gic (valor,listaSim))::t -> if List.mem sim listaSim then primeraFila (agregar valor acc) sim t else primeraFila acc sim t
;;

(* Esta funcion busca los simbolos no terminales que se pueden generar dada una secuencia de dos simbolos a y b *)
let rec buscar_simbolos_no_terminales a b acc = function
    [] -> acc
  | (Regla_gic (c,[d; e]))::t -> if ((d = a) && (e = b)) then buscar_simbolos_no_terminales a b (agregar c acc) t else buscar_simbolos_no_terminales a b acc t 
  | _::t -> buscar_simbolos_no_terminales a b acc t
;;

(* Esta funcion lo que hace es que para un conjunto de símbolos de la cadena, busca los no terminales y los une para luego
en cyk colocarlos en la casilla que los corresponde. *)
let rec combinar_simbolos_no_terminales acc r = function
    Conjunto [] -> acc
  | Conjunto ((a,b)::t) -> combinar_simbolos_no_terminales (union (buscar_simbolos_no_terminales a b conjunto_vacio r) acc) r (Conjunto t)
;;

let cyk cadena (Gic (_, _, Conjunto reglas, s) as gic) =
  (* Primero comprobamos si el GIC está en FNC; si lo está seguimos, si no damos un fallo. *)
  if not (es_fnc gic) then raise (Failure "El gic no esta en Forma Normal de Chomsky.")

  (* Luego comprobamos que la cadena a analizar no está vacía; si lo está damos un fallo,
  si no se crea la matriz sobre la que vamos a trabajar con longitud n x n. *)
  else let n = List.length cadena in if n = 0 then raise (Failure "La cadena está vacía.")
  else let matriz = Array.make_matrix n n conjunto_vacio in
  
  (* Aqui lo que hacemos es rellenar la primera fila de la matriz valiéndonos de un bucle 
  for y usando la función auxiliar primeraFila, que para un simbolo terminal dado, devuelve
  el conjunto de no terminales desde los que se puede llegar a éste. *)
  for i = 0 to n-1 do
    let c = List.nth cadena i in
    matriz.(0).(i) <- primeraFila conjunto_vacio c reglas;
  done;

  (* En estos 3 bucles for anidados se hace todo el algoritmo, se va iterando sobre las lineas
  siguientes a la primera haciendo los pasos necesarios para llegar a la útima fila. *)
  for i = 1 to n-1 do 
    for j = 0 to n-1-i do
      for k = 0 to i-1 do
        let simbolos1 = matriz.(k).(j) in
        let simbolos2 = matriz.(i-k-1).(j+k+1) in
        matriz.(i).(j) <- union matriz.(i).(j) (combinar_simbolos_no_terminales conjunto_vacio reglas (cartesiano simbolos1 simbolos2)) 
      done;
    done;
  done;

  (* Si al completar el algoritmo cyk vemos que en la casilla matriz.(n-1).(0) se encuentra el
  símbolo no terminal S, entonces la cadena es generada por el lenguaje y si no está entonces 
  no es generado por el lenguaje. *)
  if (pertenece (No_terminal "S") matriz.(n-1).(0)) then true else false
;;

(* Pruebas *)

es_fnc gic0;; (* true *)
es_fnc gic1;; (* false *)

cyk cadena0 gic0;; (* true *)
cyk cadena1 gic0;; (* false *)
cyk cadena0 gic1;; (* Failure *)
cyk cadena1 gic1;; (* Failure *)