(* Compatibility shim from Basis-02 Word8ArraySlice to Basis-97 Word8Array *)
(* Author: Christopher Richards *)

structure Word8ArraySlice :> MONO_ARRAY_SLICE
			       where type array = Word8Array.array
			       where type vector = Word8Array.vector =
struct
  type array = Word8Array.array
  type slice = Word8Array.array * int * int option
  type vector = Word8Array.vector
  fun slice s = s
  val vector = Word8Array.extract
end;
