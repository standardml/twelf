(* Trailing EVar Instantiations *)
(* Author: Carsten Schuermann *)

functor Trail (structure IntSyn' : INTSYN)
  : TRAIL =
struct

  structure IntSyn = IntSyn'

  (* Trails must be compared for equality, so the tail
     of a trail is a cell.  An alternative implementation
     would keep a global count of trail depth, which would
     be remembered by the function `trail'.
  *)
  datatype Trail' =
    Cons of (IntSyn.Exp option ref) * (Trail' ref)
  | Nil

  type Trail = Trail' ref

  local
    structure I = IntSyn

    val globalTrail = ref (ref Nil)
    
    fun reset () = (globalTrail := ref Nil)

    fun unwindTrail (shortTrail, longTrail) =
        let fun ut (tr) =
	    if shortTrail = tr
	      then globalTrail := shortTrail
	    else (case !tr
		    of Cons (r, tr') =>
		       (r := NONE; ut tr'))
	in
	  ut longTrail
	end

    fun trail f =
        let
	  val oldTrail = !globalTrail
	  val r = f ()
	  (* Note: if f does not return normally, trail *)
	  (* will not be unwound here.  May need to reset globally! *)
	  val _ = unwindTrail (oldTrail, !globalTrail)
	in
	  r
	end

    fun instantiateEVar (r, U) =
          (r := SOME U;
	   globalTrail := ref (Cons (r, !globalTrail)))

  in
    val reset = reset
    val trail = trail
    val instantiateEVar = instantiateEVar
  end (* local ... *)
end; (* functor Trail *)
