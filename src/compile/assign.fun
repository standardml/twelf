(* Assignment *)
(* Author: Brigitte Pientka *)

functor Assign ((*! structure IntSyn' : INTSYN !*)
		structure Whnf : WHNF
		(*! sharing Whnf.IntSyn = IntSyn' !*)
		structure Unify : UNIFY
		(*! sharing Unify.IntSyn = IntSyn' !*)
		structure Print : PRINT
		(*! sharing Print.IntSyn = IntSyn' !*)
		      )
  : ASSIGN =
struct
  (*! structure IntSyn = IntSyn' !*)
    
  exception Assignment of string

  local
    open IntSyn

   (* 
     templates
           p ::= Root(n, NIL) | Root(c, SP) | EVar (X, V) | AVar A |
	         Lam (D, p)
                   where X is uninstantiated and occurs uniquely
		   any multiple occurrence of X has been renamed to A.
                  
                 any eta-expanded EVar remains an EVar 
                 but it may be lowered during whnf (or in the special case here 
                 expansion)

          SP ::= p ; SP | NIL

   *)

  (* assignExpW (G, (U1, s1), (U2, s2)) = ()

     invariant:
     G |- s1 : G1    G1 |- U1 : V1   (U1, s1) in whnf
     G |- s2 : G2    G2 |- U2 : V2   (U2, s2) is template 
  *)   
    fun assignExpW (G, (Uni L1, _), (Uni L2, _), cnstr) = (* L1 = L2 by invariant *)
          cnstr
      | assignExpW (G, Us1 as (Root (H1, S1), s1), Us2 as (Root (H2, S2), s2), cnstr) =
	 (case (H1, H2) of
	    (Const(c1), Const(c2)) => 
		if (c1 = c2) then assignSpine (G, (S1, s1), (S2, s2), cnstr)
		else raise Assignment "Constant clash"

	  | (BVar(k1), BVar(k2)) => 
		  if (k1 = k2) then assignSpine (G, (S1, s1), (S2, s2), cnstr)
	       else raise Assignment "Bound variable clash"

	   | (Skonst(c1), Skonst(c2)) => 	  
	       if (c1 = c2) then assignSpine (G, (S1, s1), (S2, s2), cnstr)
	       else raise Assignment "Skolem constant clash"

	  | (Def (d1), Def (d2)) =>
	    (* cannot occur by invariant; all definitions in clause heads have been 
               replaced by AVars Tue Jun 18 19:47:39 2002 -bp *)
	       if (d1 = d2) then (* because of strict *) 
		 assignSpine (G, (S1, s1), (S2, s2), cnstr)
	       else assignExp (G, Whnf.expandDef (Us1), Whnf.expandDef (Us2), cnstr)
	  | (Def d1, _) => 
		  assignExp (G, Whnf.expandDef Us1, Us2, cnstr)
	  | (_, Def(d2)) => 
	    (* cannot occur by invariant; all definitions in clause heads have been 
               replaced by AVars Tue Jun 18 19:47:44 2002 -bp *)
  	    assignExp (G, Us1, Whnf.expandDef Us2, cnstr)

          | (FgnConst (cs1, ConDec (n1, _, _, _, _, _)), FgnConst (cs2, ConDec (n2, _, _, _, _, _))) =>
            (* we require unique string representation of external constants *)
               if (cs1 = cs2) andalso (n1 = n2) then cnstr
               else raise Assignment "Foreign Constant clash"

	  | (FgnConst (cs1, ConDef (n1, _, _, W1, _, _, _)), 
		  FgnConst (cs2, ConDef (n2, _, _, V, W2, _, _))) =>	       
               (if (cs1 = cs2) andalso (n1 = n2) then cnstr
               else assignExp (G, (W1, s1), (W2, s2), cnstr))

           | (FgnConst (_, ConDef (_, _, _, W1, _, _, _)), _) =>
               assignExp (G, (W1, s1), Us2, cnstr)

           | (_, FgnConst (_, ConDef (_, _, _, W2, _, _, _))) =>
               assignExp (G, Us1, (W2, s2), cnstr)               

	  | _ => (raise Assignment ("Head mismatch ")))

      | assignExpW (G, (Lam (D1, U1), s1), (Lam (D2, U2), s2), cnstr) =           
          (* D1[s1] = D2[s2]  by invariant *)
	  assignExp (Decl (G, decSub (D1, s1)), (U1, dot1 s1), (U2, dot1 s2), cnstr)

      | assignExpW (G, (U1, s1), (Lam (D2, U2), s2), cnstr) =                     
          (* Cannot occur if expressions are eta expanded *)
	  assignExp (Decl (G, decSub (D2, s2)), 
		    (Redex (EClo (U1, shift), App (Root (BVar (1), Nil), Nil)), dot1 s1),
		    (U2, dot1 s2), cnstr)  
	   (* same reasoning holds as above *)

      | assignExpW (G, Us1 as (U, s1),
		    Us2 as (EVar(r2, _, _, _), s2), cnstr) =
	    (* s2 = id *)
	    (* don't trail, because EVar has been created since most recent choice point *)
	    (* Tue Apr  2 10:23:19 2002 -bp -fp *)
	    (r2 := SOME (EClo(Us1));
	     cnstr)

      | assignExpW (G, Us1 as (U, s1),
		    Us2 as (AVar(r2), s2), cnstr) =
	    (* s2 = id *)
            (* don't trail, because AVars never survive local scope *)
	    (r2 := SOME(EClo Us1);
	     cnstr)

      | assignExpW (G, (Lam (D1, U1), s1), (U2, s2), cnstr) =	                   
	  (* ETA: can't occur if eta expanded *)
	  assignExp (Decl (G, decSub (D1, s1)), (U1, dot1 s1), 
		    (Redex (EClo (U2, shift), App (Root (BVar (1), Nil), Nil)), dot1 s2), cnstr)
           (* for rhs:  (U2[s2])[^] 1 = U2 [s2 o ^] 1 = U2 [^ o (1. s2 o ^)] 1
                        = (U2 [^] 1) [1.s2 o ^] *)

      | assignExpW (G, Us1, Us2 as (EClo(U,s'), s), cnstr) = 
	  assignExp(G, Us1, (U, comp(s', s)), cnstr)

      | assignExpW (G, Us1 as (EVar(r, _, V, Cnstr), s), Us2, cnstr) =
	   (Eqn(G, EClo(Us1), EClo(Us2))::cnstr)

      | assignExpW (G, Us1 as (EClo(U,s'), s), Us2, cnstr) = 
	  assignExp(G, (U, comp(s', s)), Us2, cnstr)

      | assignExpW (G, Us1 as (FgnExp (_, fe), _), Us2, cnstr) =
	  (* by invariant Us2 cannot contain any FgnExp *)
	    (Eqn(G, EClo(Us1), EClo(Us2))::cnstr)

      | assignExpW (G, Us1, Us2 as (FgnExp (_, fe), _), cnstr) =
	    (Eqn(G, EClo(Us1), EClo(Us2))::cnstr)
	  
    and assignSpine (G, (Nil, _), (Nil, _), cnstr) = cnstr
      | assignSpine (G, (SClo (S1, s1'), s1), Ss, cnstr) = 
         assignSpine (G, (S1, comp (s1', s1)), Ss, cnstr)
      | assignSpine (G, Ss, (SClo (S2, s2'), s2), cnstr) =
	 assignSpine (G, Ss, (S2, comp (s2', s2)), cnstr)
      | assignSpine (G, (App (U1, S1), s1), (App (U2, S2), s2), cnstr) =
	 let 
	   val cnstr' = assignExp (G, (U1, s1), (U2, s2), cnstr)
	 in 
	   assignSpine (G, (S1, s1), (S2, s2), cnstr')
	 end 
	     
    and assignExp (G, Us1, Us2 as (U2, s2), cnstr) = 
	 assignExpW (G, Whnf.whnf Us1, Whnf.whnf Us2, cnstr)  

    fun solveCnstr nil = true
      | solveCnstr (Eqn(G, U1, U2)::Cnstr) = 
        (Unify.unifiable(G, (U1, id), (U2, id)) andalso solveCnstr Cnstr)
	
    fun unifyW (G, (Xs1 as AVar(r as ref NONE), s), Us2) = 
        (* s = id *)
          r := SOME(EClo(Us2))
      | unifyW (G, Xs1, Us2) = 
	  (* Xs1 should not contain any uninstantiated AVar anymore *)
	  Unify.unifyW(G, Xs1, Us2)
      
    fun unify(G, Xs1, Us2) = unifyW(G, Whnf.whnf Xs1, Whnf.whnf Us2)

  in
    val solveCnstr = solveCnstr

    fun unifiable (G, Us1, Us2) = 
        (unify(G, Us1, Us2); true)
         handle Unify.Unify msg => false

    (*
    fun assign(G, Us1, Us2) = assignExp(G, Us1, Us2, [])
    *)

    fun assignable (G, Us1, Uts2) = 
        (SOME(assignExp (G, Us1, Uts2, []))
         handle (Assignment(msg)) => NONE)
  end
end; (* functor Assign *)
