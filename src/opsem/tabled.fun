(* Abstract Machine for tabling*)
(* Author: Iliano Cervesato *)
(* Modified: Jeff Polakow, Frank Pfenning, Larry Greenfield, Roberto Virga *)

functor Tabled (structure IntSyn' : INTSYN
		    structure CompSyn' : COMPSYN
		      sharing CompSyn'.IntSyn = IntSyn'
		    structure Unify : UNIFY
		      sharing Unify.IntSyn = IntSyn'
		    structure TabledSyn : TABLEDSYN
		      sharing TabledSyn.IntSyn = IntSyn'

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
  structure TabledSyn = TabledSyn

  local
    structure I = IntSyn
    structure C = CompSyn
    structure A = AbstractTabled
    structure TI = TableIndex
  in
    
    (* ---------------------------------------------------------------------- *)
    (* bp Wed Feb 13 16:16:33 2002 *)
    (* added pointer: what answers have been reused already, hence do not have to
       be re-used again for this goal
     *)

    val SuspGoals : ((((IntSyn.Exp * IntSyn.Sub) * CompSyn.DProg * (IntSyn.pskeleton -> unit)) * 
		      Unify.unifTrail * int ref)  list) ref  = ref []


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

    (* reinstSub (G, D, s) = s'
     
       if D, G |- s : D', G  (closed) 
	 then G |- s' : D', G (evars)
    *) 

    fun reinstSub (Gdp, I.Null, s) = s
      | reinstSub (Gdp, I.Decl(G,I.Dec(_,A)), s) = 
      let
(*	val X = I.newEVar (I.Null, I.EClo (A,s))   (* ???? *) bp Wed Feb 20 11:06:51 2002 *)
	val X = I.newEVar (I.Null, A)
      in
	I.Dot(I.Exp(X), reinstSub (Gdp, G, s))
      end 

   (* ---------------------------------------------------------------------- *)

   (* retrieve' (n, G, ((M, V), s), answ_i, sc) = ()
   
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

    n is just a counter which answer substitution
    we are currently considering -- only for debugging 
     
   *)

   fun retrieve' (n, G, Vs, (G', D', U'), [], sc)  = ()
     | retrieve' (n, G, Vs as (V,s), (G', D', U'), (((D1, s1), O1)::A),  sc) =  
     let 
       val Vpi = A.raiseType(G, V)
       val Upi = A.raiseType(G', U')

       val s1' = reinstSub (G', D1, I.id)  

       val _ = if (!Global.chatter) >= 4 then 
	        (print (Int.toString n ^ " retrieve' answers for: " );
		 print (Print.expToString(I.Null, I.EClo(Vpi, s)) ^ " \n");
		 print ("Answer in table: " );
		 print (Print.expToString(I.Null, A.raiseType(D1, I.EClo(Upi, s1))) 
		      ^ " : \n" ))
		else ()

       val _ = if (!Global.chatter) >= 5 then 
	        (print ("\n retrieved and reinstantiated : ");
		 print (Print.expToString(I.Null, I.EClo(I.EClo(Upi, s1), s1')) ^ "\n"))
	       else 
		 ()		 
     in
       CSManager.trail  
       (fn () =>  
	(if Unify.unifiable (I.Null, (Vpi, s), (I.EClo(Upi, s1), s1')) then 
	   
	   (* sideeffect: (V,s) is now instantiated with answer *)
	   ((if (!Global.chatter) >= 5 then
	       (print ("            After Unification : ");
		print (Print.expToString(IntSyn.Null, I.EClo(Vpi, s)) ^ "\n"))
	     else 
	       ());
	    sc O1)
	 else 
	   ()));
       retrieve' (n+1, G, Vs, (G', D', U'), A, sc)
     end 
   


   (* retrieve (G, (V, s), ((G', D', U'), A), sc) = ()
    
     G |- s : D, G    (s contains free vars)
     D, G |- V
        G |- V[s]

     D', G' |- U'
     for each i where i in [0...k] and  ((Di, si), Oi) in A 
       return match G |- V[si] against Di, G' |- U'[si] 
              and execute (sc Oi)

     Effects: instantiation of EVars in s, and dp
              any effect  sc M  might have
     
   *)
    and retrieve (k, G, Vs as (V, s), (H as ((G', D', U), answ)), sc) =
        let
	  val lkp  = TableIndex.lookup(answ) 
	  val asw' = List.take(rev(TableIndex.solutions(answ)), TableIndex.lookup(answ))
	  val answ' = List.drop(asw', !k) 
	  val _ = (if (!Global.chatter) >= 4 then		     
 			 print ("use answers from " ^ Int.toString(!k) ^ " to " ^ Int.toString(lkp) ^
				"\n")
 		       else  
 			 ())
	in 
	k := lkp;
        retrieve' (0, G, Vs, (G', D', U), answ', sc)
	end



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
  fun solve ((C.Atom(p), s), dp as C.DProg (G, dPool), sc) =     
      let
	(* -- extend abstraction: abstractEVarCtx(G, (p,s)) 
            return G', D', U', s' 
	    where  D', G' |- U
                   G' |- s' : D', G'
		   
            after this goal is solved: 
	                G' |- s' : D', G'    (open answer subsitution)
	           Dk', G' |- sk' : D', G'   (closed answer substitution)
		   Dk', G' |- U'[sk']         (closed answer)
		   *)
	
	val _ = if (!Global.chatter) >= 4 then 
	         (print "\n solve : " ;
		  print (Print.expToString(I.Null,
					   A.raiseType(G, IntSyn.EClo(p,s))) ^ "\n"))
		else 
		  ()

      in 
	if TabledSyn.tabledLookup (I.targetFam p) then 
	  let 
	    val (G', D', U', s') = A.abstractEVarCtx (G, p, s)
	  in
	    (case TableIndex.callCheck (G', D', U') 
	       of NONE => 
	       (* D', G' |- U'  was not in table 
		* SIDE EFFECT: D', G' |- U' added to table
		* 
		* new subcomputation with own 
		* success continutation is started 
		*)
	       (matchAtom ((p,s), dp,   
 		       (fn pskeleton => 
			(* when the success continuation is executed:
			 * 
			 * Table entry   :D', G' |- U'
			 * Answer(table) :    G' |- U'[s']
			 * 
			 *)
			let
			  val (Dk, sk) = A.abstractAnswSub' (G', I.ctxLength(G'), s')
			  val (G1, D1, U1, _) = A.abstractEVarCtx (G', U', s')
			  val _ = if (!Global.chatter) >= 5 then 
			           (print ("\n ANSWER : ");
				    print (Print.expToString(I.Null, 
							     A.raiseType(G, I.EClo(p, s))) 
					   ^ "\n");
				    print ("\n TABLE ENTRY ANSWER : ");
				    print (Print.expToString(I.Null, 
							     A.raiseType(G', I.EClo(U', s'))) 
					   ^ "\n");
				    print ("\n TABLE ENTRY ANSWER (closed): ");
				    print (Print.expToString(I.Null,
			                A.raiseType(concat(G', Dk), I.EClo(U', sk))) ^ "\n");

				    print ("\n insert answer for ");
				    print (Print.expToString (I.Null, 
							      A.raiseType(concat(G', D'), 
									  I.EClo(U', I.id)))))
				  else 
				    ()
			in
			  case TableIndex.answerCheck (G', D', U', s', pskeleton)
			    of TableIndex.repeated => ()
			     | TableIndex.new      => sc pskeleton
			end )))
	    
	    
	| SOME(L) => 
	    if TableIndex.noAnswers L then 	    
	      (* loop detected
	       * no answers available from previous stages 
	       * suspend current goal and fail
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
			  Print.expToString(IntSyn.Null, A.raiseType(G, IntSyn.EClo(p,s))) 
			  ^"\n")
		 else 
		   ());
		SuspGoals :=  (((p,s), dp, sc), t, ref 0)::(!SuspGoals); ()
	      end
	    else 
	      (* loop detected
	       * new answers available from previous stages
	       * resolve current goal with all possible answers
	       * 
	       *)	
	      (*  (G' |- U'[s'].... but
                   if we apply strengthening then  we switch ctx !???) *)
	       (let 
		  val t = Unify.suspend()		  
		  val [(entry,answ)] = L 
		  val le = TableIndex.lookup(answ)
		in 
		(if (!Global.chatter) >= 4 then		   
		   print ("Suspend (solve because retrieving answers) " ^ 
			  Print.expToString(IntSyn.Null, A.raiseType(G, IntSyn.EClo(p,s))) 
			  ^"\n")
		 else 
		   ());
		  SuspGoals := (((p,s), dp, sc), t, ref le)::(!SuspGoals);
		  retrieve (ref 0, G', (U' , s'), (entry, answ), sc)
		end))
	  end
	else 
	  matchAtom ((p, s), dp, sc)
      end 
    
    | solve ((C.Impl(r, A, Ha, g), s), C.DProg (G, dPool), sc) =
      let
	val D' = I.Dec(NONE, I.EClo(A,s))
      in
	solve ((g, I.dot1 s), C.DProg (I.Decl(G, D'), I.Decl (dPool, SOME(r, s, Ha))),
	       (fn O => sc O)) 
      end
    | solve ((C.All(D, g), s), C.DProg (G, dPool), sc) =
      let
	val D' = I.decSub (D, s)
      in
	solve ((g, I.dot1 s), C.DProg (I.Decl(G, D'), I.Decl(dPool, NONE)),
	       (fn O => sc O))
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
  	  sc [] 		          (* call success continuation *) 
      else ()				  (* fail *)
	)    
    | rSolve (ps', (C.And(r, A, g), s), dp as C.DProg (G, dPool), sc) =
      let
	(* is this EVar redundant? -fp *)
	val X = I.newEVar(G, I.EClo(A, s)) 
      in
        rSolve (ps', (r, I.Dot(I.Exp(X), s)), dp,
		(fn S1 => solve ((g, s), dp, (fn S2 => sc (S1@S2)))))
      end
    | rSolve (ps', (C.Exists(I.Dec(_,A), r), s), dp as C.DProg (G, dPool), sc) =
      let
	val X = I.newEVar(G, I.EClo(A, s)) 
      in
	rSolve (ps', (r, I.Dot(I.Exp(X), s)), dp, (fn S => sc S))
    (* (fn S => sc I.App(X,S)) *)
      end
    

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
	  | matchSig ((Hc as I.Const c)::sgn') =
	    let
	      val C.SClause(r) = C.sProgLookup (cidFromHead Hc)
	    in
	      (* trail to undo EVar instantiations *)
	      CSManager.trail (fn () =>
			       (rSolve (ps', (r, I.id), dp,
					(fn S => sc ((I.pc c)::S)))));
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
				              (fn S => sc ((I.dc k)::S)))); 
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
                         of SOME(U) => (sc [I.csolver]; true)
                          | NONE => false)
              in
                if succeeded
                then matchConstraint (solve, try+1)
                else ()
              end      

      in
        case I.constStatus(cidFromHead Ha)
          of (I.Constraint (cs, solve)) => matchConstraint (solve, 0)
           | _ => matchDProg (dPool, 1)

(*	matchDProg (dPool, 1) *)
      end


  (* bp Wed Feb 13 16:18:56 2002 *)
  (* add when loop detected only use answers k - n *)
  fun retrieval ((p,s), dp as C.DProg(G, dPool), sc, t, n) =    
    let
      val (G', D', U', s') =   A.abstractEVarCtx (G, p, s)
    in 
      case TableIndex.callCheck (G', D', U') 
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
	    ((if (!Global.chatter) >= 4 then		   
		print ("Suspend (resumed + susp)" ^ 
		       Print.expToString(IntSyn.Null, A.raiseType(G, IntSyn.EClo(p,s))) 
		       ^"\n")
	      else 
		());
		())
	  else 
	    (* loop detected
	     * new answers available from previous stages
	     * resolve current goal with all "new" possible answers
	     *    
	     *)
	    let 
	      val [(entry,answ)] = L 
	    in 
		retrieve (n, G', (U', s'),(entry, answ), sc)
	    end 
    end 
  
    fun updateAbsParam () = 
      (case (!TableIndex.termDepth) of
 	   NONE => ()
	 | SOME(n) => TableIndex.termDepth := SOME(n+1);
       case (!TableIndex.ctxDepth) of
 	   NONE => ()
	 | SOME(n) => TableIndex.ctxDepth := SOME(n+1);

       case (!TableIndex.ctxLength) of
 	   NONE => ()
	 | SOME(n) => TableIndex.ctxLength := SOME(n+1)
	     )


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
       | resume (((((p,s), dp as C.DProg (G, _), sc), trail, k)::Goals),n) =
       (CSManager.trail	(fn () => (Unify.resume trail; 	 
				   (if (!Global.chatter) >= 4 then
				      print ("\n " ^ Int.toString n ^ " RESUME " ^ 
					     Print.expToString(I.Null, A.raiseType(G, I.EClo(p,s)))^ "\n")
				    else   
				      ());  
				      retrieval ((p,s), dp, sc, trail, k)));
	resume (Goals, n-1))   
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
	(updateAbsParam (); 
	 resume (SG, l);
	true)
     else 
       (* table did not change during previous stage *)
       false
   end 


 fun solExists (p,s) = 
   let
     val (G', D', U', s') = A.abstractEVarCtx (I.Null, p, s)       
   in 
     case TableIndex.callCheck (G', D', U') of
       NONE => false
     | SOME(L) => true
   end 


 fun reset () = (SuspGoals := []; TableIndex.reset())

  fun solveQuery ((g as C.Atom(p), s), dp as C.DProg (G, dPool), sc) =
    (* only work when query is atomic *)
     case (!TableIndex.strategy) of
       TableIndex.Variant =>  solve((g, s), dp, sc)
     |  TableIndex.Subsumption => 
	 if TabledSyn.tabledLookup (I.targetFam p) then 
	   let 
	     val (G', D', U', s') = A.abstractEVarCtx (G, p, s)
	     fun scinit O = ()
	   in 
	     (TableIndex.query := SOME(G', D', U', s', sc); 
	      solve((g, s), dp, scinit))
	   end
	 else 
	   solve((g, s), dp, sc)	   
    

  end (* local ... *)

 val solve = solveQuery

end; (* functor Tabled *)



