(* Indexing for table *)
(* Author: Brigitte Pientka *)

functor TableIndex (structure Global : GLOBAL
		    structure Queue : QUEUE
		    structure IntSyn': INTSYN
		    structure CompSyn': COMPSYN
		      sharing CompSyn'.IntSyn = IntSyn'
		    structure Conv: CONV
		      sharing Conv.IntSyn = IntSyn'
		    structure Unify : UNIFY
		      sharing Unify.IntSyn = IntSyn'
		    structure AbstractTabled : ABSTRACTTABLED
		      sharing AbstractTabled.IntSyn = IntSyn'
		    structure Whnf : WHNF
		      sharing Whnf.IntSyn = IntSyn'
		    structure Print : PRINT 
 		      sharing Print.IntSyn = IntSyn'
		    structure CPrint : CPRINT 
                      sharing CPrint.IntSyn = IntSyn'
                      sharing CPrint.CompSyn = CompSyn'
		    structure TypeCheck : TYPECHECK
		      sharing TypeCheck.IntSyn = IntSyn'
		 )
  : TABLEINDEX =
struct
  structure IntSyn = IntSyn'
  structure CompSyn = CompSyn'
  structure Conv = Conv


  (* TABLE 

   table entry : Gs, Gdp  |- u 


   Answer substitution: 

                 Gas, Gdp  |- as : Gs, Gdp
		 Gas, Gdp  |- M             ( currently proof terms are not always generated )

   Answer : 
                 Gas, Gdp |- u[as] : M
   *)
 
  (* solution: (Gas, as) * (Gm, M) (currently )
     solution: (Gas, (as, M))      (should be eventually)

   * lookup  : pointer to the i-th element in solution list
   *)

  (* proof term skeleton could be stored with tabled call ? *)
  type answer = {solutions : ((IntSyn.dctx * IntSyn.Sub) * 
			      (IntSyn.dctx * IntSyn.Exp)) list,
		 lookup: int}


  type entry = ((IntSyn.dctx * IntSyn.dctx * IntSyn.Exp) * answer)

  type entries = entry list 

  type index = entry list

  datatype answState = new | repeated

  datatype Strategy = Variant | Subsumption

  val added = ref false;

  (* ---------------------------------------------------------------------- *)
  (* global search parameters *)

  val strategy  = ref Variant (* Subsumption *) (* Variant *)

  (* term abstraction after term depth is greater than 5 *) 
  val globalTermDepth = ref NONE : int option ref;

  val termDepth = ref (!globalTermDepth);

  (* apply strengthening during abstraction *)
  val strengthen = AbstractTabled.strengthen ;


  (* ---------------------------------------------------------------------- *)

  local
    structure I = IntSyn
    structure A = AbstractTabled

    (* Global Table *)

    val table : index ref = ref []

    (* concat(Gdp, G) = G'' 
     *
     * if Gdp = ym...y1 
     *    G   = xn...x1
     * then 
     *    Gdp, G = G'' 
     *    ym...y1, xn...x1
     *
     *)
    fun concat (I.Null, G') = G'
      | concat (I.Decl(G, D), G') = I.Decl(concat(G,G'), D)


    (* ---------------------------------------------------------------------- *)

    (* printTable () = () *)

    fun printTable () = 
      let 
        fun proofTerms (Gdp, Gs, U, []) = print ""
	  | proofTerms (Gdp, Gs, U, (((Gs', s'), (Gm, M'))::S)) = 
          ((print (Print.expToString (I.Null, 
		     A.raiseType(Gs',
			I.EClo(A.raiseType(Gdp, U), s'))))
	    handle _ => print "EXCEPTION" );	    
	  print " : ";
	   (* printing proof terms *)
	   print ", \n\t";
	   proofTerms (Gdp, Gs, U, S))

	fun printT [] = ()
	  | printT (((Gdp, Gs, U),
		     {solutions =  S, lookup = i})::T) = 
	    case S
	      of [] => (printT T ; 
			print (Print.expToString (I.Null, 
						  A.raiseType(concat(Gdp, Gs), U))
			       ^ ", NONE\n"))
	      | (a::answ) => (printT T; 
			      print (Print.expToString (I.Null, 
							A.raiseType(concat(Gdp, Gs), U)) ^
				     ", [\n\t");
			      proofTerms (Gdp, Gs, U, (rev S));
			      print (" ] -- lookup : " ^ Int.toString i ^ "\n\n")) 
      in
	print ("Table: \n");
	printT (!table);
	print ("End Table\n")
      end 			       	    

    
    (* ---------------------------------------------------------------------- *)

    (* Term Abstraction *)

    fun lengthSpine (I.Nil) = 0
      | lengthSpine (I.SClo(S, s')) = 1 + lengthSpine(S)

    fun exceedsLength (i) = 
      case (!termDepth) of 
	NONE => false
      | SOME(n) => (n <= (i +1))
      
    fun exceedsTermDepth U = 
      let
	fun exceeds (0, _ ) = true
	  | exceeds (depth, (U as I.Uni (L))) = false
	  | exceeds (depth, I.Pi ((D, _), V)) =
 	     exceedsDec(depth-1 , D) orelse exceeds(depth-1, V)
	  | exceeds (depth, I.Root (F, S)) =
	     exceedsSpine ((depth-1), S)
	  | exceeds (depth, I.Redex (U, S)) =
	     exceedsLength(lengthSpine(S)) 
	     orelse
	     exceeds(depth, U) 
	     orelse 
	     exceedsSpine' ((depth-1), S)	     
	  | exceeds (depth, I.Lam (D, U)) =
	     exceeds (depth, U)
	  | exceeds (depth, (X as I.EVar _)) = 
	     (* shouldn't happen *)
	     true
	  | exceeds (depth, I.EClo(E, s)) = 
	     exceeds (depth, E)
	  | exceeds (depth, (F as I.FgnExp (cs, ops))) = 
	     (* shouldn't happen *)
	     true
(*	  | exceeds (depth, _) = (print "\nexceeds anything else ??? \n"; true) *)
	  
	and exceedsSpine (depth, I.Nil)  = (depth = 0) 
	  | exceedsSpine (depth, I.SClo (S, s')) = 
	     (* ? *)
	      exceedsSpine (depth, S)
	  | exceedsSpine (depth, I.App (U, S)) =
	      (exceeds (depth, U) orelse
	       exceedsSpine (depth-1, S))

	and exceedsSpine' (depth, I.Nil)  = (depth = 0) 
	  | exceedsSpine' (depth, I.SClo (S, s')) = 
	     (* ? *)
	      exceedsSpine' (depth, S)
	  | exceedsSpine' (depth, I.App (U, S)) =
	      (exceeds (depth, U) orelse
	       exceedsSpine' (depth, S))


	and exceedsDec (depth, I.Dec(_, U)) = 
	  exceeds (depth, U)
      in 
	case (!termDepth) of
	  NONE => false
	  | SOME(k) => 	exceeds(k, U)
      end 

   (* ---------------------------------------------------------------------- *)
   (* reinstantiate term ! *)
   fun reinstantiate (Gdp, I.Null, (U, s')) = 
         (U, s')
     | reinstantiate (Gdp, I.Decl(G, I.Dec(_,A)), (U, s')) = 
	 let
	   val X = I.newEVar (I.Null, I.EClo (A,s'))
	 in
	   reinstantiate (Gdp, G, (U, I.Dot(I.Exp(X), s')))
	 end 

   (* reinstSub (Gdp, G, s) = s' 
    *
    * If Gdp, G |= s
    * then Gdp |= s'
    *)

   fun reinstSub (Gdp, I.Null, s) = s
      | reinstSub (Gdp, I.Decl(G,I.Dec(_,A)), s) = 
      let
(*	val X = I.newEVar (Gdp, I.EClo (A,s')) *)
	val X = I.newEVar (I.Null, A)
(*	val X = I.newEVar (I.Null, I.EClo (A,s))   (* ???? *) *)
      in
	I.Dot(I.Exp(X), reinstSub (Gdp, G, s))

      end 


   (* ---------------------------------------------------------------------- *)
   (* variant (U,s) (U',s')) = bool   *)
      
    fun variant (Us, Us') = Conv.conv (Us, Us') 

    (* subsumes ((G, Gs, U), (G', Gs', U')) = bool
     * 
     * if
     *    Gs, G   |- U 
     *    Gs', G' |- U'
     * then  
     *      G' |- s' : Gs', G'
     *    return true if Gs, G |- U is an instance of G' |- U'[s'] 
     *    otherwise false
     *
     *)
    fun subsumes ((Gdp, Gs, U), (Gdp', Gs', U')) = 
      let 
	val Upi = A.raiseType (Gdp, U)
	val Upi' = A.raiseType (Gdp', U')
	val s' = reinstSub (Gdp', Gs', I.id)
      in 
	CSManager.trail (fn () =>
			 Unify.unifiable (Gs, (Upi', s'), (Upi, I.id)))
      end 

    fun equalSub (I.Shift k, I.Shift k') = (k = k')
      | equalSub (I.Dot(F, S), I.Dot(F', S')) = 
        equalFront (F, F') andalso equalSub (S, S')
      | equalSub (I.Dot(F,S), I.Shift k) = false
      | equalSub (I.Shift k, I.Dot(F,S)) = false

    and equalFront (I.Idx n, I.Idx n') = (n = n')
      | equalFront (I.Exp U, I.Exp V) = Conv.conv ((U, I.id), (V, I.id))
      | equalFront (I.Undef, I.Undef) = true

    (* ---------------------------------------------------------------------- *)
    (* Call check and insert *)

    (* callCheck (Gdp, Gs, U) = callState
     
       check whether Gs, Gdp |- U is in the table
 
     returns NONE, 
        if Gs, Gdp |- U is not already in the table
	  Sideeffect: add Gs, Gdp |- U to table
     
     returns SOME(A) 
        if Gs, Gdp |- U is in table and 
	  A is the list of active answers to the index

    *)

    fun callCheckVariant (Gdp, Gs, U) = 
      let
	val Upi = A.raiseType(concat(Gdp, Gs), U)
	fun lookup (Gdp, Gs, U) [] (NONE) = 
	     (table := ((Gdp, Gs, U), {solutions = [],lookup = 0})::(!table); 
	      (if (!Global.chatter) >= 4 then 
		 (print ("\n \n Added " );
		  print (Print.expToString (I.Null, Upi) ^ "\n to Table \n"))
	       else 
		 ());
	       added := true;
	      (* if termdepth(U) > n then force the tabled engine to suspend
	       * and treat it like it is already in the table, but no answ available *)
	       case (!globalTermDepth) of 
		    NONE => NONE
		 | SOME(_) => 
		      (if exceedsTermDepth Upi then 
			 ((if (!Global.chatter) >= 5 then 
			     print ("\n term " ^ Print.expToString (I.Null, Upi) ^ 
				    " exceeds termdepth \n")
			   else 
			     ());
			     SOME([]))
		       else 
			 NONE))
	  | lookup (Gdp, Gs, U) [] (SOME(L)) = 
	     SOME(L)
	  | lookup (Gdp, Gs, U) ((H as ((Gdp', Gs', U'), answ))::T) opt =
	     if variant ((Upi, I.id), (A.raiseType(concat(Gdp',Gs'), U'), I.id)) then
	       let
		 val opt' = case opt of 
		               NONE => SOME([H]) 
			     | SOME(L) => SOME(H::L) 
	       in  
		 (if (!Global.chatter) >= 5 then
		    print ("call " ^ Print.expToString (I.Null, Upi) ^ " found in table \n ")
		  else 
		    ());
		  lookup (Gdp, Gs, U) T opt' 
	       end 
	     else  
	       lookup (Gdp, Gs, U) T opt
      in 
	lookup (Gdp, Gs, U) (!table) NONE
      end



    fun callCheckSubsumes (Gdp, Gs, U) = 
      let 		
	val Upi = A.raiseType(concat(Gdp, Gs), U)
	fun lookup ((Gdp, Gs, U), [], NONE) = 
	    (table := ((Gdp, Gs, U), {solutions = [],lookup = 0})::(!table); 
	     (if (!Global.chatter) >= 5 then
		print ("Added " ^  Print.expToString (I.Null, Upi) ^ " to Table \n")
	      else 
		());
	     added := true;
	     if exceedsTermDepth Upi then 
		((if (!Global.chatter) >= 5 then 
		    print ("\n term " ^ Print.expToString (I.Null, Upi) ^ 
			   " exceeds termdepth  \n")
		  else 
		    ());
		SOME([]))
	      else 
		NONE)
	  | lookup ((Gdp, Gs, U), [], SOME(L)) = 
	     SOME(L)
	  | lookup ((Gdp, Gs, U), (((Gdp', Gs', U'), answ)::T), opt) =
	    if (subsumes ((Gdp, Gs, U), (Gdp', Gs', U'))) then	       
	      let
		 val opt' = case opt of 
		               NONE => SOME([((Gdp', Gs', U'), answ)]) 
			     | SOME(L) => SOME(((Gdp', Gs', U'), answ)::L) 
	       in 
		 (if (!Global.chatter) >= 5 then
		    print ("call " ^ Print.expToString (I.Null, Upi) ^ "found in table \n ")
		  else 
		    ());
		  lookup ((Gdp, Gs, U), T, opt') 
	      end
	    else 
	      lookup ((Gdp, Gs, U), T, opt)
      in 
	lookup ((Gdp, Gs, U), (!table), NONE)
      end

    (* ---------------------------------------------------------------------- *)
    (* answer check and insert 
      
      if     Gdp |- U[s]
         Gs, Gdp |- U
	     Gdp |- s : Gdp 
      
      answerCheck (Gdp, Gs, (U,s), _) = repeated
         if s already occurs in answer list for U
      answerCheck (Gdp, Gs, (U,s), _) = new
         if s did not occur in answer list for U
         Sideeffect: update answer list for U
      
     *) 
    fun answCheckVariant (Gdp, Gs, (U,s), (Gmdp, M)) =  
      let 
	val Upi = A.raiseType(concat(Gdp, Gs), I.EClo(U, I.id))

	val _ = if (!Global.chatter) >= 5 then 
	          (print "\n AnswCheckInsert: ";
		   print (Print.expToString(I.Null, 
					    I.EClo(A.raiseType(Gdp, U),s)) ^ "\n");
		   print "\n Table Index : " ;
		   print (Print.expToString (I.Null,  Upi) ^ "\n"))
		else 
		  ()

	fun member ((Gus, us), []) = false
	  | member ((Gus, us), (((Gs1, s1),_)::S)) = 

	  (* for variance checking we only need to compare abstract substitutions 
	   * should we compare Gus and Gs1 ?
	   *)
	  if equalSub (us,s1) then  
	    true
	  else 
	    member ((Gus, us), S)
	
	fun lookup  (Gdp, Gs, (U,s)) [] T = 
	  (* cannot happen ! *) 
	  (print (Print.expToString(I.Null, I.EClo(A.raiseType(Gdp,U),s))  
		  ^ " call should always be already in the table !\n") ; 
	   repeated)
	  | lookup (Gdp, Gs, (U,s)) ((H as ((Gdp', Gs', U'), 
					    {solutions = S, lookup = i}))::T) T' = 
	  if variant ((Upi, I.id),
		      (A.raiseType(concat(Gdp', Gs'), 
					    I.EClo(U', I.id)),I.id))
	    then 
	      let 
		val (Gus, us) = A.abstractAnswSub s
		val (Gus, us) = A.abstractAnswSub s

		val Mpi = A.raiseType(Gmdp, M)
	      in 	       	       
		(* answer check *)
		if member ((Gus, us), S) then  
		  repeated
		else 
		  (table := (rev T')@(((Gdp', Gs', U'),
				       {solutions = (((Gus, us), (Gmdp, M))::S), 
					lookup = i})::T); 
		   
		   (if (!Global.chatter) >= 5 then 
		      (print ("\n solution added  -- " ); 
		       print (Print.expToString(I.Null, 
						A.raiseType(Gus,
							    I.EClo(A.raiseType(Gdp',U'), us))))
		       (* print ("\n proof term : "); *)
		       (* print (Print.expToString(I.Null, Mpi ) ^ "\n");   *)
		       )
		    else 
		      ());
		   new)
	      end
	   else 
	      lookup (Gdp, Gs, (U,s)) T (H::T')
      in 
	lookup (Gdp, Gs, (U,s)) (!table) []
      end 

   fun reverse (I.Null, G') = G'
     | reverse (I.Decl(G, D), G') = 
         reverse (G, I.Decl(G', D))

    fun memberSubsumes ((Gdp, Gs, U, s), (Gdp', U', [])) = false
      | memberSubsumes ((Gdp, Gs, U, s), (Gdp', U', (((Gs1, s1),_)::S))) = 
        let
	  val Upi = A.raiseType(Gdp, U)
	  val Upi' = A.raiseType(Gdp',U')
	  val Gs1' = reverse(Gs1, I.Null)
	  val Vpis = reinstantiate (Gdp', Gs1', (I.EClo(Upi', s1), I.id))
	  (* assume G' and G are the same for now *)
	  val b = CSManager.trail (fn () => 
				   Unify.unifiable (Gs, (Upi, s), (Vpis)))
	in 
	  if b then
	    ((if (!Global.chatter) >= 5 then 
		print "\n answer in table subsumes answer \n "
	      else 
		());
	     true)
	  else 
	    memberSubsumes ((Gdp, Gs, U, s), (Gdp', U', S)) 
	end 
	
   fun answCheckSubsumes (Gdp, Gs, (U,s), (Gmdp, M)) = 
      let
	val Upi = A.raiseType(Gdp, U)
	val _ = if (!Global.chatter) >= 4 then 
	            (print ("\n AnswCheckInsert (subsumes): " );
		     print(Print.expToString(I.Null, I.EClo(Upi, s))
		       ^ "\n"))
		else ()
	fun lookup ((Gdp, Gs, (U,s)), [], T) = 
	  (* cannot happen ! *) 
	  (print (Print.expToString(concat(Gdp, Gs), I.EClo(U,s)) 
		  ^ " call should always be already in the table !\n") ; 
	   repeated)
	  | lookup ((Gdp, Gs, (U,s)), (((Gdp', Gs', U'), {solutions = S, lookup = i})::T), T') = 
	  if (subsumes ((Gdp, Gs, U), (Gdp', Gs', U'))) then
	     let 
	      val (Gus, us) = A.abstractAnswSub s
	      val Mpi = A.raiseType(Gmdp, M)
	     in 
	       if memberSubsumes ((Gdp, Gus, U, us), (Gdp', U', S)) then
		 repeated
	       else 
		 let
		   val s' = reinstSub (Gdp', Gs', I.id)
		   val _ = if (!Global.chatter) >= 4 then 
		            (print "\n new answer to be added to Index \n";
			     print (Print.expToString(I.Null, 
						    A.raiseType(concat(Gdp', Gs'), U')) ^"\n");
			     print "\n reinstantiated Table index\n";
			     print (Print.expToString(I.Null,
						    I.EClo(A.raiseType(Gdp', U'), s'))
				    ^ "\n");
			     print "\n answer to be added \n";
			     print (Print.expToString(I.Null,
			                A.raiseType(Gus, I.EClo(A.raiseType(Gdp, U), us))) ^ "\n"))
			   else 
			     ()
		   (*  higher-order matching *)
		   val _ = if Unify.unifiable (Gus, (A.raiseType(Gdp, U), us),  
					       (A.raiseType(Gdp', U'), s'))			    
			     then (if (!Global.chatter) >= 4 then 
				     (print "\n1 unification successful !\n";
				      print (Print.expToString(I.Null,
			                       A.raiseType(Gus, I.EClo(A.raiseType(Gdp', U'), s')))
					     ^ "\n"))
				   else 
				     ())
			   else print "\n1 unification failed! -- should never happen ?"
		   val (Gus', us') = A.abstractAnsw (Gus, s')
		 (*			  val Gus'' = reverse(Gus', I.Null) *)
		in 			   
		  table := ((rev T')@(((Gdp', Gs', U'),
				       {solutions = (((Gus', us'), (Gmdp, M))::S), 
					lookup = i})::T));
		  (if (!Global.chatter) >= 5 then 
		     (print ("\n \n solution (original) was: \n");
		      print(Print.expToString(I.Null, I.EClo(A.raiseType(Gdp, U), s)) 
			    ^ "\n");
		      print ("\n \n solution (deref) was: \n");
		      print(Print.expToString(I.Null, A.raiseType(Gus, I.EClo(A.raiseType(Gdp, U), us)))
			    ^ "\n"); 		  
		      print ("\n solution added  --- ");
		      print (Print.expToString(I.Null,
					       A.raiseType(Gus, I.EClo(A.raiseType(Gdp',U'), s')))
			     ^ "\n"); 		  
		      print ("\n solution added (dereferenced) --- "); 		  
		      print (Print.expToString(I.Null,
					       A.raiseType(Gus',
							   I.EClo(A.raiseType(Gdp',U'), us')))
			     ^ "\n"))
		  else 
		    ());
		  new 
		end
	     end 
	  else 
	    lookup ((Gdp, Gs, (U,s)), T, (((Gdp', Gs', U'), 
					   {solutions = S, lookup = i})::T')) 	   
      in 
	lookup ((Gdp, Gs, (U,s)), (!table), [])
      end 

   (* ---------------------------------------------------------------------- *)
   (* TOP LEVEL *)

    fun reset () = (table := []; termDepth := (!globalTermDepth))


    fun solutions {solutions = S, lookup = i} = S
    fun lookup {solutions = S, lookup = i} = i


    fun noAnswers [] = true
      | noAnswers ((H as ((Gdp', G', U'), answ))::T) = 
          case (List.take (solutions(answ), lookup(answ))) 
	    of [] => noAnswers T
	  | L  => false


    fun callCheck (Gdp, Gs, U) = 
          case (!strategy) of 
	    Variant => callCheckVariant (Gdp, Gs, U)
	  | Subsumption => callCheckSubsumes (Gdp, Gs, U)

    fun answCheck (Gdp, Gs, Us, (Gdp', M)) = 
          case (!strategy) of
	    Variant => answCheckVariant (Gdp, Gs, Us, (Gdp',M))
	  | Subsumption => answCheckSubsumes (Gdp, Gs, Us, (Gdp', M))
	      

    (* needs to take into account previous size of table *)
    fun updateTable () = 
          let 
	    fun update [] T Flag = (Flag, T)
	      | update (((dp, G, U), {solutions = S, lookup = i})::T) T' Flag =
	      let 
		val l = length(S) 
	      in 
		if (l = i) then 
		  (* no new solutions were added in the previous stage *) 	      
		  update T (((dp, G, U), {solutions = S, lookup = List.length(S)})::T') Flag
		else 
		  (* new solutions were added *)
		  update T (((dp, G, U), {solutions = S, lookup = List.length(S)})::T') true
	      end 
	    val (Flag, T) = update (!table) [] false
	    val r = Flag orelse (!added)
	  in  
	    added := false;
	    table := rev(T);
            (* in each stage incrementally increase termDepth *)
(*	    termDepth := (!termDepth +1); *)
	    r
	  end 

  in

    val termDepth = globalTermDepth
    val table = table
    val solutions = solutions
    val lookup = lookup
    val noAnswers = noAnswers

    val reset = reset

    val printTable = printTable

    val callCheck = callCheck
    val answerCheck = answCheck

    val updateTable = updateTable


  end (* local *)

end;  (* functor TableIndex *)

