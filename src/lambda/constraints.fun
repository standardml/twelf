(* Manipulating Constraints *)
(* Author: Jeff Polakow, Frank Pfenning *)
(* Modified: Roberto Virga *)

functor Constraints
    ((*! structure IntSyn' : INTSYN !*)
     structure Conv : CONV
     (*! sharing Conv.IntSyn = IntSyn' !*)
       )
       : CONSTRAINTS =
struct

  (*! structure IntSyn = IntSyn' !*)

  exception Error of IntSyn.cnstr list

  (*
     Constraints cnstr are of the form (X<I>[s] = U).
     Invariants:
       G |- s : G'  G' |- X<I> : V
       G |- U : W
       G |- V[s] == W : L
       (X<>,s) is whnf, but X<>[s] is not a pattern
     If X<I> is uninstantiated, the constraint is inactive.
     If X<I> is instantiated, the constraint is active.

     Constraints are attached directly to the EVar X
     or to a descendent  -fp?
  *)

  local
    structure I = IntSyn

    (* simplify cnstrs = cnstrs'
       Effects: simplifies the constraints in cnstrs by removing constraints
         of the form U = U' where G |- U == U' : V (mod beta/eta)
         Neither U nor U' needs to be a pattern
         *)
    fun simplify nil = nil
      | simplify ((ref I.Solved) :: cnstrs) =
          simplify cnstrs
      | simplify ((Eqn as ref (I.Eqn (G, U1, U2))) :: cnstrs) =
        if Conv.conv ((U1, I.id), (U2, I.id))
          then simplify cnstrs
        else Eqn :: (simplify cnstrs)
      | simplify ((FgnCnstr as ref (I.FgnCnstr csfc)) :: cnstrs) =
        if I.FgnCnstrStd.Simplify.apply csfc ()
          then simplify cnstrs
        else FgnCnstr :: (simplify cnstrs)

    fun namesToString (name::nil) = name ^ "."
      | namesToString (name::names) = name ^ ", " ^ namesToString names

    fun warnConstraints (nil) = ()
      | warnConstraints (names) = print ("Constraints remain on " ^ namesToString names ^ "\n")

  in
    val simplify = simplify
    val namesToString = namesToString
    val warnConstraints = warnConstraints
  end

end;  (* functor Constraints *)
