(* Trailer Which Does Not Record EVar Instantiations *)
(* Author: Carsten Schuermann *)

functor NoTrail (structure IntSyn' : INTSYN)
  : TRAIL =
struct
  structure IntSyn = IntSyn'

  type Trail = unit

  local
    structure  I = IntSyn

    fun reset () = ()
    fun trail f = f () 
    fun instantiateEVar (r, U) = (r := SOME U)

  in
    val reset = reset
    val trail = trail
    val instantiateEVar = instantiateEVar
  end (* local *)
end; (* functor Trail *)
