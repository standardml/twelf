(* Compatibility shim from Basis-02 Word8VectorSlice to Basis-97 Word8Vector *)
(* Author: Christopher Richards *)

signature MONO_VECTOR_SLICE =
sig
  type slice
  type vector
  val slice : vector * int * int option -> slice
  val vector : slice -> vector
  val full : vector -> slice
end;

structure Word8VectorSlice :> MONO_VECTOR_SLICE
			       where type vector = Word8Vector.vector =
struct
  type vector = Word8Vector.vector
  type slice = Word8Vector.vector * int * int option
  fun slice s = s
  val vector = Word8Vector.extract
  fun full v = (v, 0, NONE)
end;

signature COMPAT_WORD8_VECTOR_SLICE =
sig
  val full : Word8Vector.vector -> Word8VectorSlice.slice
end;

structure Word8VectorSlice97 :> COMPAT_WORD8_VECTOR_SLICE =
struct
  type vector = Word8Vector.vector
  type slice = Word8VectorSlice.slice
  val full = Word8VectorSlice.full
end;
