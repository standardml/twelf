(* Sparse 1-Dimensional Arrays *)
(* Author: Roberto Virga *)

signature SPARSE_ARRAY =
sig

  type 'a array

  val array : 'a -> 'a array
  val sub : ('a array * int) -> 'a
  val update : ('a array * int * 'a) -> unit
  val extract : ('a array * int * int) -> 'a Vector.vector
  val copyVec : {src : 'a Vector.vector, si : int, len : int option, dst : 'a array, di : int} -> unit
  val app : ((int * 'a) -> unit) -> ('a array * int * int) -> unit
  val foldl : ((int * 'a * 'b) -> 'b) -> 'b -> ('a array * int * int) -> 'b
  val foldr : ((int * 'a * 'b) -> 'b) -> 'b -> ('a array * int * int) -> 'b
  val modify : ((int * 'a) -> 'a) -> ('a array * int * int) -> unit
end; (* signature SPARSE_ARRAY *)