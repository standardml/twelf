(* Assignment *)
(* Author: Larry Greenfield *)

functor Assign (structure IntSyn' : INTSYN
		structure Whnf : WHNF
		  sharing Whnf.IntSyn = IntSyn'
		structure Unify : UNIFY
		  sharing Unify.IntSyn = IntSyn')
  : ASSIGN =
struct
  structure IntSyn = IntSyn'
    
  exception Assign of string

  local
    open IntSyn

   (* 
     templates
           p ::= Root(n, NIL) | Root(c, SP) | X
                   where X is uninstantiated and occurs uniquely
          SP ::= p ; SP | NIL

   *)

    (* expandPattern (U, s) = (U', s')

       Invariant:
       If   G |- s  : G'       G'  |- U : V    G' |- U is template
       then G |- s' : G''      G'' |- U' : V'
       and  G |- V [s] == V' [s'] == V'' : L
       and  G |- U [s] == U' [s'] : V''
       and the pattern now contains EVar's instead of BVar's *)

    fun expandPattern (Uni L, s) = (Uni L, s)
      | expandPattern (Root (BVar k, Nil), s) =
          (case bvarSub (k, s)
	     of Exp (U, V) => (U, id))
	     (* no other cases *)
      | expandPattern (Root (H, S), s) =
	     (Root(H, SClo (S, s)), id)

    fun assignUni (Type, Type) = ()
      | assignUni (Kind, Kind) = ()
      | assignUni _ = raise Assign "Universe level mismatch"
      
  (* assignExpW ((U1, s1), (U2, s2)) = ()

     invariant:
     G |- s1 : G1    G1 |- U1 : V1   (U1, s1) in whnf
     G |- s2 : G2    G2 |- U2 : V2   (U2, s2) is template *)
    and assignExpW ((Uni L1, _), (Uni L2, _)) = assignUni (L1, L2)
      | assignExpW (Us1 as (Root (H1, S1), s1), Us2 as (Root (H2, S2), s2)) =
	 (case (H1, H2) of
	    (Const(c1), Const(c2)) => 
		if (c1 = c2) then assignSpine ((S1, s1), (S2, s2))
		else raise Assign "Constant clash"
	  | (Def d1, _) => 
		  assignExp (Whnf.expandDef Us1, Us2)
	  | _ => raise Assign "head mismatch")
      | assignExpW (Us1 as (U, s1),
		    Us2 as (EVar(r2, V2, nil), s2)) =
	    (* s2 = id *)
	    r2 := SOME (EClo Us1)

      | assignExpW (Us1 as (EVar(r, V, Cnstr), s), Us2) =
	    Unify.unify (Us1, Us2)

      | assignExpW _ = (print "huh\n"; raise Assign "huh")
	    
    and assignSpine ((Nil, _), (Nil, _)) = ()
      | assignSpine ((SClo (S1, s1'), s1), Ss) = 
            assignSpine ((S1, comp (s1', s1)), Ss)
      | assignSpine (Ss, (SClo (S2, s2'), s2)) =
	    assignSpine (Ss, (S2, comp (s2', s2)))
      | assignSpine ((App (U1, S1), s1), (App (U2, S2), s2)) =
	    (assignExp ((U1, s1), (U2, s2));
	     assignSpine ((S1, s1), (S2, s2)))
      
    and assignExp (Us1, Us2 as (U2, s2)) = 
      assignExpW (Whnf.whnf Us1, expandPattern Us2)
      
  in
    val assign = assignExp
      
    fun assignable (Us1, Us2) = 
      (assignExp (Us1, Us2); true) 
         handle (Assign _) => false
	      | (Unify.Unify _) => false
  end
end; (* functor Assign *)
