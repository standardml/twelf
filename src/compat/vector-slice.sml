(* Compatibility shim from Basis-current VectorSlice to Basis-97 Vector *)
(* Author: Christopher Richards *)

structure VectorSlice :> VECTOR_SLICE =
struct
  type 'a slice = 'a Vector.vector * int * int option
  fun slice s = s
  val appi = Vector.appi
  val mapi = Vector.mapi
end;
