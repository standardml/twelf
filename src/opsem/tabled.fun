(* Abstract Machine for tabling*)
(* Author: Iliano Cervesato *)
(* Modified: Jeff Polakow, Frank Pfenning, Larry Greenfield, Roberto Virga *)

functor Tabled (structure IntSyn' : INTSYN
		    structure CompSyn' : COMPSYN
		      sharing CompSyn'.IntSyn = IntSyn'
		    structure Unify : UNIFY
		      sharing Unify.IntSyn = IntSyn'
		    (*
                    structure Assign : ASSIGN
		      sharing Assign.IntSyn = IntSyn'
		    *)
		  structure Subordinate : SUBORDINATE
		    sharing Subordinate.IntSyn = IntSyn'

		    structure Index : INDEX
		      sharing Index.IntSyn = IntSyn'
		    structure Queue : QUEUE
		    structure TableIndex : TABLEINDEX
		      sharing TableIndex.IntSyn = IntSyn'
		    structure AbstractTabled : ABSTRACTTABLED
		      sharing AbstractTabled.IntSyn = IntSyn'
		    structure Whnf : WHNF
		      sharing Whnf.IntSyn = IntSyn'
 

		    (* CPrint currently unused *)
		    structure CPrint : CPRINT 
                      sharing CPrint.IntSyn = IntSyn'
                      sharing CPrint.CompSyn = CompSyn'
					    (* CPrint currently unused *)
		    structure Print : PRINT 
                      sharing Print.IntSyn = IntSyn'

		    structure Names : NAMES 
                      sharing Names.IntSyn = IntSyn'
		    structure CSManager : CS_MANAGER
		      sharing CSManager.IntSyn = IntSyn')
  : TABLED =
struct

  structure IntSyn = IntSyn'
  structure CompSyn = CompSyn'
  structure Unify = Unify

  local
    structure I = IntSyn
    structure C = CompSyn
    structure A = AbstractTabled
  in
    
    (* ---------------------------------------------------------------------- *)
    val SuspGoals : ((((IntSyn.Exp * IntSyn.Sub) * CompSyn.DProg * (IntSyn.Exp  -> unit)) * 
		      Unify.unifTrail)  list) ref  = ref []

    (* ---------------------------------------------------------------------- *)

    fun expToString (G,U) = Print.expToString(G, U)

    (* ---------------------------------------------------------------------- *)

    fun concat (I.Null, G') = G'
      | concat (I.Decl(G, D), G') = I.Decl(concat(G,G'), D)

    fun reverse (I.Null, G') = G'
      | reverse (I.Decl(G, D), G') = 
          reverse (G, I.Decl(G', D))


    (* ---------------------------------------------------------------------- *)

    (* strengthenExp (U, s) = U' 
     
       Invariant:
       If   G |- s : G'
       and  G |- U : V
       then G' |- U' = U[s^-1] : V [s^-1] 
    *)
    fun strengthenExp (U, s) = Whnf.normalize (Whnf.cloInv (U, s), I.id)

    (* strengthenDec (x:V, s) = x:V'
     
       Invariant:
       If   G |- s : G'
       and  G |- V : L
       then G' |- V' = V[s^-1] : L
    *)
    fun strengthenDec (I.Dec (name, V), s) = I.Dec (name, strengthenExp (V, s))

    (* strengthenCtx (G, s) = (G', s')
     
       If   G0 |- G ctx
       and  G0 |- s G1 
       then G1 |- G' = G[s^-1] ctx
       and  G0 |- s' : G1, G'  
    *)
    fun strengthenCtx (I.Null, s) = (I.Null, s)
      | strengthenCtx (I.Decl (G, D), s) = 
        let 
	  val (G', s') = strengthenCtx (G, s)
	in
	  (I.Decl (G', strengthenDec (D, s')), I.dot1 s')
	end


    (* ---------------------------------------------------------------------- *)
    (* We write
       G |- M : g
     if M is a canonical proof term for goal g which could be found
     following the operational semantics.  In general, the
     success continuation sc may be applied to such M's in the order
     they are found.  Backtracking is modeled by the return of
     the success continuation.

     Similarly, we write
       G |- S : r
     if S is a canonical proof spine for residual goal r which could
     be found following the operational semantics.  A success continuation
     sc may be applies to such S's in the order they are found and
     return to indicate backtracking.
  *)

    (* ---------------------------------------------------------------------- *)

    (* reinstSub (Gdp, Gs, s) = s'
     
       if Gdp |- s : Gs, Gdp (closed) 
	 then Gdp |- s' : Gdp (evars)
    *) 

    fun reinstSub (Gdp, I.Null, s) = s
      | reinstSub (Gdp, I.Decl(G,I.Dec(_,A)), s) = 
      let
	val X = I.newEVar (I.Null, I.EClo (A,s))   (* ???? *)
      in
	I.Dot(I.Exp(X), reinstSub (Gdp, G, s))
      end 

   (* ---------------------------------------------------------------------- *)

   (* retrieve' (G, ((M, V), s), answ_i, sc) = ()
   
     G |- s : G'
     G' |- M : V atomic goal 

     and answ_i = s_1 .... s_n
   
     for all k from 1 to n:

     if G |- M [s_k] : V[s_k]
     then sc M[s_k] is evaluated 
          where any bound var in Gas, is replaced by
            an existential variable

     Effects: instantiation of EVars in V, s, and dp
              any effect  sc M  might have
     
   *)

   fun retrieve' (n, Gdp, MVs, (Gdp', Gs', N, U), [], (G, sc), L)  = 
         retrieve (Gdp, MVs, L, (G, sc))
     | retrieve' (n, Gdp, MVs as ((M, V),s), (Gdp', Gs', N, U), ((Gs1, s1)::A),  (G, sc), L) =  
     let 
       val Vpi = A.raiseType(Gdp, V)
       val Upi = A.raiseType(Gdp', U)

       val Mpi = A.raiseType(Gdp, M)
       val Npi = A.raiseType(Gdp', N)

       val s1' = reinstSub (Gdp', Gs1, I.id)  

       val _ = if (!Global.chatter) >= 5 then 
	        (print (Int.toString n ^ " retrieve' answers for: " );
		 print (Print.expToString(I.Null, I.EClo(Vpi, s)) ^ " \n");
		 print ("Answer in table: " );
		 print (Print.expToString(I.Null, A.raiseType(Gs1, I.EClo(Upi, s1)))
		      ^ " : \n" );
		 print ("\n retrieved and reinstantiated : ");
		 print (Print.expToString(I.Null, I.EClo(I.EClo(Upi,s1), s1')) ^ "\n"))
	       else 
		 ()		 
       fun shift (0, s) = s
	 | shift (n, s) = shift(n-1, I.dot1 s)
     in
       CSManager.trail  
       (fn () =>  
	(if Unify.unifiable (I.Null, (Vpi, s), (I.EClo(Upi, s1),s1')) 
	   andalso Unify.unifiable(I.Null, (Mpi, s), (I.EClo(Npi, s1), s1')) then 
	   
	   (* sideeffect: (V,s) is now instantiated with answer *)
	   ((if (!Global.chatter) >= 5 then
	       (print ("            After Unification : ");
		print (Print.expToString(IntSyn.Null, I.EClo(Vpi, s)) ^ "\n");
		print ("           Proof Term : ");
		print (Print.expToString(IntSyn.Null, I.EClo(Mpi, s)) ^ "\n");
		print "1 "; 
		print (Print.expToString(IntSyn.Null, A.raiseType(Gdp, I.EClo(M, shift (IntSyn.ctxLength(Gdp),s)))) ^ "\n"))
	     else 
	       ());
(*	       sc (I.EClo(I.EClo(M, s1), s1')) *)
	       (* problem: M is possibly strengthened! but should not be, when passed into sc 
		* solution 1: strengthen every new evar so everything is max. strengthened
		* solution 2: pass in strengthened and non-strengthened ? 
		* apply weakening to it!!!!!!! bp Fri Sep 28 18:08:07 2001 
		*)

	       let 
		 val w = if (!TableIndex.strengthen) then
		            Subordinate.weaken (G, IntSyn.targetFam(I.EClo(V, s)))
			 else 
			   I.id
(* 		 val _ =  print "2 " *)
(* 		 val _  = print (Print.expToString(I.Null, A.raiseType(G,I.EClo(M, I.comp(shift(I.ctxLength(G),s), w)))) ^ "\n") *)
	       in 
	       sc (I.EClo(M, I.comp(shift(I.ctxLength(Gdp),s), w)))
	       end)
	 else 
	   ()));
       retrieve' (n+1, Gdp, MVs, (Gdp', Gs', N, U), A, (G, sc), L)
     end 
   


   (* retrieve (G, (V,s), T, sc) = ()
    
     G |- s : G'
     G' |- V atomic goal 
     T  sub-table s.t. (H_1, answ_1) ... (Hn, answ_n)
     H_i = (dp', G', (V',s')
     and (G', (V',s')) ~ (G, (V,s))
     and answ_i = s_1 .... s_n

     if G |- M : V[s_k]
     then sc M is evaluated

     Effects: instantiation of EVars in V, s, and dp
              any effect  sc M  might have
     
   *)
    and retrieve (Gdp, ((M, V), s), [], (G, sc)) = ()
      | retrieve (Gdp, MVs as ((M, V), s), ((H as ((Gdp', Gs', N, U), answ))::L), (G, sc)) =
        retrieve' (0, Gdp, MVs, (Gdp', Gs', N, U), TableIndex.solutions(answ), (G, sc), L)
(*	 retrieve (Gdp, Vs, L, sc)) *)


  (* ---------------------------------------------------------------------- *)

  fun cidFromHead (I.Const a) = a
    | cidFromHead (I.Def a) = a

  fun eqHead (I.Const a, I.Const a') = a = a'
    | eqHead (I.Def a, I.Def a') = a = a'
    | eqHead _ = false
                              
  (* solve ((g, s), dp, sc) => ()
     Invariants:
       dp = (G, dPool) where  G ~ dPool  (context G matches dPool)
       G |- s : G'
       G' |- g  goal
       if  G |- M : g[s]
       then  sc M  is evaluated
     Effects: instantiation of EVars in g, s, and dp
              any effect  sc M  might have
  *)
  fun solve ((C.Atom(p), s'), dp as C.DProg (G, dPool), sc) =     
      let
	val N = I.newEVar(G, I.EClo(p, s'))
(*	val (Gdp1, Gex, U1, sex) = A.abstractEVarECloCtx (G, I.EClo(p,s')) *)
(*	val (abstract, Gdp1, Gex, U1, sex) = A.abstractEVarCtx (G, (p, s')) *) 
	val (Gdp, Gs, N', U, s) = A.abstractEVarCtx (G, (N, p), s')
(*	val (abstract', Gdp', Gs', M, s'') = A.abstractEVarCtx (G, (M, I.id)) 
         -- extend abstraction: abstractEVarCtx(G, (p,s'), M) 
            return Gdp, Gs, U, M', s 
	    where  Gsm, Gdp |- M : U
                   Gdp |- s : Gsm, Gdp
		   

            after this goal is solved: 
	           Gex, Gdp |- s : Gsm, Gdp  (closed)
		   Gex, Gdp |- M[s]:U[s]     (closed answer)

		   *)

	val _ = if (!Global.chatter) >= 5 then 
	         (print "\n solve : " ;
		  print (Print.expToString(I.Null,
					   A.raiseType(G, IntSyn.EClo(p,s')))
			 ^ "\n");

		  print "\n abstracted \n ";
		  print ("    " ^ Print.expToString(I.Null, A.raiseType(concat(Gdp, Gs), U)) ^ "\n") ;

		  print ("     \t" ^ Print.expToString(I.Null, I.EClo(A.raiseType(Gdp, U), s)) ^ "\n"))
		else 
		  ()

      in 
	case TableIndex.callCheck (Gdp, Gs, N', U) 
	  of NONE => 
	    (* dp |= (p,s) was not in table 
	     * SIDE EFFECT: dp |= (p,s): added to table
	     * 
	     * new subcomputation with own 
	     * success continutation is started 
	     *)
            (matchAtom ((p,s'), dp,   
 		       (fn M => 
			(* M' = abstract M in ctx dp! 
			 pass M' into callAnswerCheck ! *)
			let
			  val _ = if (!Global.chatter) >= 5 then 
			           (print ("\n ANSWER : ");
				    print (Print.expToString(I.Null, 
							     A.raiseType(G, I.EClo(p, s'))) 
					   ^ "\n");

				    print "\n Proof term: ";
				    (print (Print.expToString (I.Null, 
							      A.raiseType(G,  M)) ^ "\n") 
				     handle _ => ()); 

				    print ("\n insert answer for ");
				    print (Print.expToString (I.Null, 
							      A.raiseType(concat(Gdp, Gs), 
									  I.EClo(U, I.id)))))
				  else 
				    ()
			  val w = if (!TableIndex.strengthen) then
			            Subordinate.weaken (G, IntSyn.targetFam(I.EClo(U, s)))
				   else 
				     I.id
			    
			  val _ = Unify.unifiable (I.Null, (A.raiseType(G, M), I.id),
						   (A.raiseType(Gdp, N'), I.comp(s, w)))
                          (* side effect: s contains the instantiation of 
			   all ex. vars and the proof term instantiation
  			   Trail ???
			   *)

			  val _ = if (!Global.chatter) >= 5 then 
			             (print "\n Proof term: ";
				      (print (Print.expToString (I.Null, 
					A.raiseType(G,  I.EClo(N, I.comp(s, w)))) ^ "\n ok \n")
				     handle _ => 
				       (print "\n             \n";
					print (Print.expToString (I.Null, 
					A.raiseType(G, M)) ^ "\n")
				       )))
				  else 
				    ()


(*			  val _ = if (!Global.chatter) >= 5 then 
				    (print "\n Proof term (abstract) 1 : ";
				      print (Print.expToString (I.Null, 
							       A.raiseType(G,  N)) ^ "\n") 

(*				     print "\n Proof term (abstract) 2  : ";
				     print (Print.expToString (I.Null,
							       A.raiseType(concat(Gdp, Gs), I.EClo(N', s))) ^ "\n")*)
				     )
				  else 
				    ()
*)
			in
			  case TableIndex.answerCheck (Gdp, Gs, (N', U), s)
			    of TableIndex.repeated => ()
			     | TableIndex.new      => sc M (* should we fail here ? *)
			end )))
	    
	    
	| SOME(L) => 
	    if TableIndex.noAnswers L then 	    
	      (* loop detected
	       * no answers available from previous stages 
	       * (could generate recursive proof term -- not done)
	       * suspend current goal 
	       * fail
	       *
	       * NOTE: we might suspend goals more than once.
	       *     case: answer list for goal (p,s) is saturated
	       *           but not the whole table is saturated.
	       *)
	      let 
		val t = Unify.suspend()		      
	      in 
		(if (!Global.chatter) >= 4 then		   
		   print ("Suspend " ^ 
			  Print.expToString(IntSyn.Null, A.raiseType(G, IntSyn.EClo(p,s'))) 
			  ^"\n")
		 else 
		   ());
		SuspGoals :=  (((p,s'), dp, sc), t)::(!SuspGoals); ()
	      end
	    else 
	      (* loop detected
	       * new answers available from previous stages
	       * resolve current goal with all possible answers
	       * 
	       * note: as we do not keep track which answers where
	       *       already used in previous stages we generate
	       *       answers more than once. (to be improved)
	       * 
	       * note : we do not need to suspend goal as it is already
	       *        suspended; as we are not allowed to use answers 
	       *        from the current stage, we can only enter this
	       *        case if we are in stage 2 or greater. 
	       *    
	       *)	
	      (*  (Gdp |- n'[s]:u[s].... but
                    G |- N     G |- sc (n'[s])
                   if we apply strengthening then  we switch ctx !???) *)
	       retrieve (Gdp, ((N', U) ,s), L, (G, sc))
      end 
    
    | solve ((C.Impl(r, A, Ha, g), s), C.DProg (G, dPool), sc) =
      let
	val D' = I.Dec(NONE, I.EClo(A,s))
      in
	solve ((g, I.dot1 s), C.DProg (I.Decl(G, D'), I.Decl (dPool, SOME(r, s, Ha))),
	       (fn M => sc (I.Lam (D', M))))
      end
    | solve ((C.All(D, g), s), C.DProg (G, dPool), sc) =
      let
	val D' = I.decSub (D, s)
      in
	solve ((g, I.dot1 s), C.DProg (I.Decl(G, D'), I.Decl(dPool, NONE)),
	       (fn M => sc (I.Lam (D', M))))
      end

  (* rsolve ((p,s'), (r,s), dp, sc) = ()
     Invariants:
       dp = (G, dPool) where G ~ dPool
       G |- s : G'
       G' |- r  resgoal
       G |- s' : G''
       G'' |- p : H @ S' (mod whnf)
       if G |- S : r[s]
       then sc S is evaluated
     Effects: instantiation of EVars in p[s'], r[s], and dp
              any effect  sc S  might have
  *)
  and rSolve (ps', (C.Eq(Q), s), C.DProg (G, dPool), sc) =    
    (if Unify.unifiable (G, ps', (Q, s)) (* effect: instantiate EVars *)
	then 
	  sc I.Nil		  (* call success continuation *)
      else ()				  (* fail *)
	)
    (* Fri Jan 15 14:29:28 1999 -fp,cs
    | rSolve (ps', (Assign(Q, ag), s), dp, sc) = 
     (if Assign.assignable (ps', (Q, s)) then
	aSolve ((ag, s), dp, (fn () => sc I.Nil))
      else ())
    *)
    | rSolve (ps', (C.And(r, A, g), s), dp as C.DProg (G, dPool), sc) =
      let
	(* is this EVar redundant? -fp *)
	val X = I.newEVar(G, I.EClo(A, s)) 
      in
        rSolve (ps', (r, I.Dot(I.Exp(X), s)), dp,
		(fn S => solve ((g, s), dp,
				(fn M => sc (I.App (M, S))))))
      end
    | rSolve (ps', (C.Exists(I.Dec(_,A), r), s), dp as C.DProg (G, dPool), sc) =
      let
	val X = I.newEVar(G, I.EClo(A, s)) 
      in
	rSolve (ps', (r, I.Dot(I.Exp(X), s)), dp,
		(fn S => sc (I.App(X,S))))
      end
    (*
    | rSolve (ps', (C.Exists'(I.Dec(_,A), r), s), dp as C.DProg (G, dPool), sc) =
      let
	val X = I.newEVar (G, I.EClo (A,s))
      in
	rSolve (ps', (r, I.Dot(I.Exp(X), s)), dp, sc)
   	          (* we don't increase the proof term here! *)
      end
     *)

  (* aSolve ((ag, s), dp, sc) = ()
     Invariants:
       dp = (G, dPool) where G ~ dPool
       G |- s : G'
       if G |- ag[s] auxgoal then
       sc () is evaluated
     Effects: instantiation of EVars in ag[s], dp and sc () *)
  and aSolve ((C.Trivial, s), dp, sc) = sc ()
    (* Fri Jan 15 14:31:20 1999 -fp,cs
    | aSolve ((Unify(I.Eqn(e1, e2), ag), s), dp, sc) =
    (if Unify.unifiable ((e1, s), (e2, s)) then aSolve ((ag, s), dp, sc)
     else ())
    *)

  (* matchatom ((p, s), dp, sc) => ()
     Invariants:
       dp = (G, dPool) where G ~ dPool
       G |- s : G'
       G' |- p : type, p = H @ S mod whnf
       if G |- M :: p[s]
       then sc M is evaluated
     Effects: instantiation of EVars in p[s] and dp
              any effect  sc M  might have

     This first tries the local assumptions in dp then
     the static signature.
  *)
  and matchAtom (ps' as (I.Root(Ha,S),s), dp as C.DProg (G,dPool), sc) =
      let
        (* matchSig [c1,...,cn] = ()
	   try each constant ci in turn for solving atomic goal ps', starting
           with c1.
        *)
	fun matchSig nil = ()	(* return indicates failure *)
	  | matchSig (Hc::sgn') =
	    let
	      val C.SClause(r) = C.sProgLookup (cidFromHead Hc)
	    in
	      (* trail to undo EVar instantiations *)
	      CSManager.trail (fn () =>
			       (rSolve (ps', (r, I.id), dp,
					(fn S => sc (I.Root(Hc, S)))))) ;
	      matchSig sgn'
	    end

        (* matchDProg (dPool, k) = ()
	   where k is the index of dPool in global dPool from call to matchAtom.
           Try each local assumption for solving atomic goal ps', starting
           with the most recent one.
        *)
	fun matchDProg (I.Null, _) =
	    (* dynamic program exhausted, try signature *)
	    matchSig (Index.lookup (cidFromHead Ha))
	  | matchDProg (I.Decl (dPool', SOME(r, s, Ha')), k) =
	    if eqHead (Ha, Ha')
	      then (* trail to undo EVar instantiations *)
		(CSManager.trail (fn () =>
		                      rSolve (ps', (r, I.comp(s, I.Shift(k))), dp,
				              (fn S => sc (I.Root(I.BVar(k), S))))) ;
		 matchDProg (dPool', k+1))
	    else matchDProg (dPool', k+1)
	  | matchDProg (I.Decl (dPool', NONE), k) =
	      matchDProg (dPool', k+1)
        fun matchConstraint (solve, try) =
              let
                val succeeded =
                  CSManager.trail
                    (fn () =>
                       case (solve (G, I.SClo (S, s), try))
                         of SOME(U) => (sc U ; true)
                          | NONE => false)
              in
                if succeeded
                then matchConstraint (solve, try+1)
                else ()
              end      
      in
	(* assume all predicates are tabled *)
	 
        case I.constStatus(cidFromHead Ha)
          of (I.Constraint (cs, solve)) => matchConstraint (solve, 0)
           | _ => matchDProg (dPool, 1)
      end



  fun retrieval ((p,s'), dp as C.DProg(G, dPool), sc, t) =    
    let
	val N = I.newEVar(G, I.EClo(p, s')) 

      val (Gdp, Gs, N', U, s) =   A.abstractEVarCtx (G, (N, p), s')
    in 
      case TableIndex.callCheck (Gdp, Gs, N', U) 
	of NONE => print ("\n should not happen! \n")	    	    
      | SOME(L) => 
	  if TableIndex.noAnswers L then 	    
	    (* loop detected
	     * no answers available from previous stages 
	     * suspend current goal 
	     * fail
	     *
	     * NOTE: do not add the susp goal to suspGoal list
	     *       because it is already in the suspGoal list
	     *)
	    ((if (!Global.chatter) >= 5 then		   
		print ("Suspend " ^ 
		       Print.expToString(IntSyn.Null, A.raiseType(G, IntSyn.EClo(p,s'))) 
		       ^"\n")
	      else 
		());
		())
	  else 
	    (* loop detected
	     * new answers available from previous stages
	     * resolve current goal with all possible answers
	     *    
	     *)		      
	    retrieve (Gdp, ((N', U), s), L, (G, sc))
    end 
  
  (* fun nextStage () = bool 
   
   if updateTable then 
     revive suspended goals
     resolve with answers 
     true
   else      
     false
     
     SIDE EFFECT: advances lookup pointers

   *)

 fun nextStage () = 
   let   
     fun resume ([],n) = ()
       | resume (((((p,s), dp as C.DProg (G, _), sc), trail)::Goals), n) =
       (CSManager.trail	(fn () => (Unify.resume trail; 	 
				   (if (!Global.chatter) >= 4 then
				      print ("\n " ^ Int.toString n ^ " RESUME " ^ 
					     Print.expToString(I.Null, A.raiseType(G, I.EClo(p,s)))^ "\n")
				    else   
				      ());  
				      retrieval ((p,s), dp, sc, trail)));
	resume (Goals, n-1))   
       (* less efficient version *)
       (* CSManager.trail(fn () => solve ((C.Atom(p),s), dp, sc)))); *)
     val SG = rev(!SuspGoals) 
(*    val SG = !SuspGoals *)
     val l = length(SG)
   in    
     if (!Global.chatter) >= 4 then 
       (TableIndex.printTable () ;
	print ("\n #Suspended goals " ^ Int.toString (length(SG)) ^ "\n"))
     else 
       ();
     if TableIndex.updateTable () then 
       (* table changed during previous stage *)
	(resume (SG, l);
	true)
     else 
       (* table did not change during previous stage *)
       false
   end 


 fun reset () = (SuspGoals := []; TableIndex.reset())

  end (* local ... *)

end; (* functor Tabled *)



