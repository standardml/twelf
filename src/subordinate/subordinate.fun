(* Subordination a la Virga [Technical Report 96] *)
(* Author: Carsten Schuermann *)

functor Subordinate
  (structure Global : GLOBAL
   structure IntSyn': INTSYN
   structure Whnf : WHNF
     sharing Whnf.IntSyn = IntSyn'
   structure Names : NAMES
     sharing Names.IntSyn = IntSyn'
   structure Table : TABLE where type key = int)
  : SUBORDINATE =
struct
  structure IntSyn = IntSyn'

  exception Error of string
 
  local
    structure I = IntSyn

    (* Subordination array

       Definition:
       soArray is valid 
       iff For all b:
           If   soArray (b) = BL,BR
           then for all a:K
                a < b iff a in BL
		(a is subordinate to b)
           and  for all c:K
    	        b < c iff c in BR
		(b is subordinate to c)
	   where subordination is transitive but not necessarily
	   reflexive
    *)
    val soTable : (I.cid list * I.cid list) Table.Table = Table.new (32)
    val lookup = Table.lookup soTable
    val insert = Table.insert soTable

    val fTable : bool Table.Table = Table.new (32)
    val fLookup = Table.lookup fTable
    val fInsert = Table.insert fTable

    (* reset () = ()

       Effect: Empties soTable, fTable
    *)
    fun reset () = (Table.clear soTable;
                    Table.clear fTable)

    (* get (a) = (AL, AR)
       where AL <| a <| AR

       Invariant: a must be defined
    *)
    fun get (a) =
        (case lookup a
	   of SOME ALAR => ALAR
	    (* not sure why next line is needed *)
            (* Wed Mar 28 19:39:20 2001 -fp *)
	    | NONE => (nil, nil))

    (* set (a, (AL, AR)) = ()
       Effect: set AL <| a <| AR
    *)
    fun set (a, ALAR) = insert (a, ALAR)

    fun fGet (a) =
        (case fLookup a
           of SOME frozen => frozen
            | NONE => false)

    fun fSet (a, frozen) = fInsert (a, frozen)

    (* pre: a is not a type definition *)
    fun checkFreeze (c, a) =
        if fGet a
        then raise Error ("Freezing violation: constant "
                          ^ Names.qidToString (Names.constQid (c))
                          ^ "\nextends type family "
                          ^ Names.qidToString (Names.constQid (a)))
        else ()

    fun frozenSubError (a, b) =
        raise Error ("Freezing violation: frozen type family "
                     ^ Names.qidToString (Names.constQid b)
                     ^ "\nwould depend on unfrozen type family "
                     ^ Names.qidToString (Names.constQid a))

    (* pre: a, b are not type definitions *)
    fun checkFrozenSub (a, b) =
        (case (fGet a, fGet b)
           of (false, true) => frozenSubError (a, b)
            | _ => ())

    (* pre: b is not a type definition *)
    fun checkMakeFrozen (b, otherFrozen) =
        let
          fun check a =
              if fGet a orelse List.exists (fn x => x = a) otherFrozen
              then ()
              else frozenSubError (a, b)
          val (BL, BR) = get (b)
        in
          if fGet b then ()
          else List.app check BL
        end

    fun expandFamilyAbbrevs a =
        (case I.constUni a
           of I.Type => raise Error ("Constant " ^ Names.qidToString (Names.constQid a)
                                     ^ " must be a type family to be frozen")
            | I.Kind =>
        (case IntSyn.sgnLookup a
           of IntSyn.ConDec _ => a
            | IntSyn.ConDef _ =>
                IntSyn.targetFam (IntSyn.constDef a)
            | IntSyn.SkoDec _ => a
            | IntSyn.AbbrevDef _ =>
                IntSyn.targetFam (IntSyn.constDef a)))

    fun installFrozen (L) =
        let
          val L = map expandFamilyAbbrevs L
        in
          List.app (fn a => checkMakeFrozen (a, L)) L;
          List.app (fn a => fSet (a, true)) L
        end

    (* a <| b = true iff a is (transitively) subordinate to b

       Invariant: a, b families
    *)
    fun below (a, b) =
	let 
	  val (BL, BR) = get (b)
	in
	  List.exists (fn x => x = a) BL
	end

    (* a <* b = true iff a is transitively and reflexively subordinate to b

       Invariant: a, b families
    *)
    fun belowEq (a, b) = (a = b) orelse below (a, b)

    (* a == b = true iff a and b subordinate each other

       Invariant: a, b families
    *)
    fun equiv (a, b) = belowEq (a, b) andalso belowEq (b, a)

    (* merge (L1, L2) = L'
     
       Invariant: 
       L' is shortest list s.t.
       L1 subset L' and L2 subset L'
    *)
    fun merge (nil, L2) = L2 
      | merge (a :: L1, L2) =
        if List.exists (fn x => x = a) L2
	  then merge (L1, L2)
	else merge (L1, a :: L2)

    (* mergeLeft (a, R, seen) = seen'

       Effect: updates the soArray to record that a is subordinate
               to every type family in R and, transitively, every
	       a' which is subordinate to a is also subordinate
	       to R.

               seen is maintained for termination and contains
	       those families a' such that a' < R has already
	       been recorded.
    *)
    fun mergeLeft (a, R, seen) = 
        let 
	  val (AL, AR) = get a
	in
	  (set (a, (AL, merge (AR, R)));
	   mergeLeftList (AL, R, a::seen))
	end

    and mergeLeftList (nil, R, seen) = seen
      | mergeLeftList (a::AL, R, seen) = 
        if List.exists (fn x => x = a) seen
	  then mergeLeftList (AL, R, seen)
	else mergeLeftList (AL, R, mergeLeft (a, R, seen))

    (* mergeRight (L, b, seen) = seen'

       Effect: updates the soArray to record that b subordinates
               every type family in L and, transitively, every
	       b' which subordinates b also subordinates L.

               seen is maintained for termination and contains
	       those families b' such that L < b' has already
	       been recorded.
    *)
    fun mergeRight (L, b, seen) = 
      let 
	val (BL, BR) = get b 
      in
	(set (b, (merge (L, BL), BR));
	 mergeRightList (L, BR, b::seen))
      end

    and mergeRightList (L, nil, seen) = seen
      | mergeRightList (L, b::BR, seen) = 
	if List.exists (fn x => x = b) seen
	  then mergeRightList (L, BR, seen)
	else mergeRightList (L, BR, mergeRight (L, b, seen))

    (* transClosure (a, b) = ()

       Invariant:
       If   soArray is valid
       then soArray is updated according to the information a < b
       and  soArray is still valid

       Also checks for violations of %frozen
    *)
    fun transClosure (a, b) = 
	if below (a, b) then ()
	else 
	  let 
	    val (AL, AR) = get a
	    val (BL, BR) = get b
	  in
            (checkFrozenSub (a, b);
             mergeLeft (a, b :: BR, nil);
             mergeRight (a :: AL, b, nil);
             ())
	  end

    (* installKind (V, a) = ()
 
       Invariant:
       If   G |- V : L and V in nf
       and  a = targetFam V
       and  soArray is valid
       then soArray is updated according to all dependencies in V
       and  soArray is valid
    *)
    fun installKind (I.Uni(L), a) =
        ( set (a, (nil, nil)) ; () )
      | installKind (I.Pi ((I.Dec (_, V1), P), V2), a) =
	( installKind (V2, a);
          transClosure (I.targetFam V1, a) )

    (* Passing around substitutions and calling whnf below is
       redundant, since the terms starts in normal form and
       we only refer to the target families.
    *)

    (* installExp (G, (U1, s1), (V2, s2)) = ()

       Invariant: 
       If   G  |- s1 : G1, and G1 |- U1 : V1
       and  G  |- s2 : G2, and G2 |- V2 : L
       and  G  |- V1[s1] = V2[s2] : L
       and  soArray valid	 
       then soArray is updated according to all dependencies in U1[s1]
       and  soArray is valid
    *)
    (*
    fun installExp (G, Us, Vs) = installExpW (G, Whnf.whnf Us, Whnf.whnf Vs)
    and installExpW (G, (I.Uni (L), _), _) = ()
      | installExpW (G, (I.Pi ((D as I.Dec (_, V1), _) , V2), s), 
		        (I.Uni I.Type, t)) = 
          (transClosure (I.targetFam V1, I.targetFam V2);
	   installExpW (G, (V1, s), (I.Uni I.Type, t));
	   installExpW (I.Decl (G, I.decSub (D, s)), (V2, I.dot1 s), 
				(I.Uni I.Type, t)))
      | installExpW (G, (I.Root (C, S), s), _) =
	  installSpine (G, (S, s), Whnf.whnf (inferCon (G, C), I.id))
      | installExpW (G, (I.Lam (D1 as I.Dec (_, V1), U), s) , 
		     (I.Pi ((D2 (* = D1 *), _), V2), t)) = 
	  (transClosure (I.targetFam V1, I.targetFam V2);
	   installExpW (G, (V1, s), (I.Uni I.Type, I.id));
	   installExpW (I.Decl (G, I.decSub (D1, s)), (U, I.dot1 s), 
			(V2, I.dot1 t)))
      | installExpW (G, (I.FgnExp (cs, ops), s), Vs) =
          installExpW (G, (#toInternal(ops) (), s), Vs)
    *)
    (* installSpine (G, (S, s1), (V2, s2)) = ()

       Invariant: 
       If   G  |- s1 : G1, and G1 |- S : V1 > V1'
       and  G  |- s2 : G2, and G2 |- V2 : L
       and  G  |- V1[s1] = V2[s2] : L
       and  soArray valid	 
       then soArray is updated accorindg to all dependencies in U1[s1]
       and  soArray is valid
     *)
    (*
    and installSpine (G, (I.Nil, _), Vs) = ()
      | installSpine (G, (I.SClo (S, s'), s), Vs) = 
	  installSpine (G, (S, I.comp (s', s)), Vs)
      | installSpine (G, (I.App (U, S), s1), 
		      (I.Pi ((I.Dec (_, V1), _), V2), s2)) =
	  (installExp (G, (U, s1), (V1, s2));
	   installSpine (G, (S, s1), 
			 Whnf.whnf (V2, I.Dot (I.Exp (I.EClo (U, s1)), s2))))
    *)

    (* Changed the functions above to use only approximate types
       and take advantage of normal form invariant.
       Tue Mar 27 21:27:59 2001 -fp
    *)

    (* inferConApprox (G, C) = V'
       where V' is an approximate type of C
       V' ~nf

       Invariant: G nf, G |- C ~:~ V for some V.
    *)
    fun inferConApprox (G, I.BVar (k')) = 
	let
          (* why not I.ctxLookup? -kw *)
	  (* ignore shift: type is approximate, only shape is important *)
	  val I.Dec (_, V) = I.ctxDec (G, k')
	  (* in case result of ctxDec is shifted *)
	  fun approx (I.EClo (V, _)) = V
            | approx V = V		(* not shifted: must be NF *)
	in
	  (* accurate, but not NF would be: V *)
	  approx V
	end
      | inferConApprox (G, I.Const(c)) = I.constType (c)
      | inferConApprox (G, I.Def(d))  = I.constType (d)
      | inferConApprox (G, I.Skonst(c)) = I.constType (c)
      | inferConApprox (G, I.FgnConst(cs, conDec)) = I.conDecType (conDec)

    (* installExp (G, U, V) = ()
       where G |- U ~:~ V  (U has shape V)
       G nf, U nf, V nf (approx)
       Effect: add subordination info from U into table
    *)
    fun installExp (G, I.Uni (L), _) = ()
      | installExp (G, I.Pi ((D as I.Dec (_, V1), _), V2), I.Uni(I.Type)) = 
          (transClosure (I.targetFam V1, I.targetFam V2);
	   installExp (G, V1, I.Uni(I.Type));
	   installExp (I.Decl (G, D), V2, I.Uni(I.Type)))
      | installExp (G, I.Root (C, S), _) =
	  installSpine (G, S, inferConApprox (G, C))
      | installExp (G, I.Lam (D1 as I.Dec (_, V1), U), I.Pi (_, V2)) =
	  (transClosure (I.targetFam V1, I.targetFam V2);
	   installExp (G, V1, I.Uni(I.Type));
	   installExp (I.Decl (G, D1), U, V2))
      | installExp (G, I.FgnExp (cs, ops), V) =
          installExp (G, Whnf.normalize (#toInternal(ops) (), I.id), V)
      | installExp (G, U, V as I.Root (I.Def _, _)) =
	(* bugfix -rv 2/27/02 *)
          let
            val V' = Whnf.normalize (Whnf.expandDef(V, I.id))
          in
            installExp (G, U, V')
          end

    (* installSpine (G, S, V) = ()
       where G |- S ~:~ V => V'  (S has shape V => V' for some V')
       G nf, S nf, V nf
       Effect: add subordination info from S into table
     *)
    and installSpine (G, I.Nil, V) = ()
      | installSpine (G, I.App (U, S), I.Pi ((I.Dec (_, V1), _), V2)) =
	  (installExp (G, U, V1);
	   installSpine (G, S, V2))
	  (* accurate would be instead of V2: *)
	  (* Whnf.whnf (V2, I.Dot (I.Exp (I.EClo (U, s1)), s2)) *)
      | installSpine (G, S as I.App _, V as (I.Root (I.Def (d), S'))) =
	  (* ignore S' because we only use approximate type *)
	  (* correct??? -fp Tue Feb 19 14:26:31 2002 *)
	  (* installSpine (G, S, I.constDef(d))*)
	  (* bugfix -rv 2/27/02 *)
          let
            val V' = Whnf.normalize (Whnf.expandDef(V, I.id))
          in
            installSpine (G, S, V')
           end

    (* install c = ()

       Invariant:
       If   soArray is valid
       and  c is a constant
       then soArray is updated accorindg to all dependencies in U1[s1]
       and  soArray is valid
    *)
    fun install c = 
	let 
	  val V = I.constType c
	in
	  case I.targetFamOpt V
	    of NONE => installKind (V, c)
	     | SOME a => (case IntSyn.sgnLookup c
                            of IntSyn.ConDec _ => checkFreeze (c, a)
                             | IntSyn.SkoDec _ => checkFreeze (c, a)
                               (* FIX: skolem types should probably be created frozen -kw *)
                             | _ => ();
                          (* installExp (I.Null, (V, I.id), (I.Uni I.Type, I.id)) *)
			  (* simplified  Tue Mar 27 20:58:31 2001 -fp *)
			  installExp (I.Null, V, I.Uni(I.Type)))
	end

    (* Respecting subordination *)


    (* checkBelow (a, b) = () iff a <| b
       Effect: raise Error(msg) otherwise
    *)
    fun checkBelow (a, b) =
        if not (below (a, b))
	  then raise Error ("Subordination violation: "
			    ^ Names.qidToString (Names.constQid (a)) ^ " not <| " ^ Names.qidToString (Names.constQid (b)))
	else ()

    (* respectsExp (G, U, V) = () iff U respects current subordination
       where G |- U ~:~ V  (U has shape V)
       G nf, U nf, V nf (approx)
       Effect: raise Error (msg)
    *)
    fun respectsExp (G, I.Uni (L), _) = ()
      | respectsExp (G, I.Pi ((D as I.Dec (_, V1), _), V2), I.Uni(I.Type)) = 
          (checkBelow (I.targetFam V1, I.targetFam V2);
	   respectsExp (G, V1, I.Uni(I.Type));
	   respectsExp (I.Decl (G, D), V2, I.Uni(I.Type)))
      | respectsExp (G, I.Root (C, S), _) =
	  respectsSpine (G, S, inferConApprox (G, C))
      | respectsExp (G, I.Lam (D1 as I.Dec (_, V1), U), I.Pi (_, V2)) =
	  (checkBelow (I.targetFam V1, I.targetFam V2);
	   respectsExp (G, V1, I.Uni(I.Type));
	   respectsExp (I.Decl (G, D1), U, V2))
      | respectsExp (G, I.FgnExp (cs, ops), V) =
          respectsExp (G, Whnf.normalize (#toInternal(ops) (), I.id), V)

    (* respectsSpine (G, S, V) = () iff S respects current subordination
       where G |- S ~:~ V => V'  (S has shape V => V' for some V')
       G nf, S nf, V nf
       Effect: raise Error (msg)
     *)
    and respectsSpine (G, I.Nil, V) = ()
      | respectsSpine (G, I.App (U, S), I.Pi ((I.Dec (_, V1), _), V2)) =
	  (respectsExp (G, U, V1);
	   respectsSpine (G, S, V2))
	  (* accurate would be instead of V2: *)
	  (* Whnf.whnf (V2, I.Dot (I.Exp (I.EClo (U, s1)), s2)) *)

    fun respects (G, (V, s)) = respectsN (G, Whnf.normalize (V, s))

    and respectsN (G, V) = respectsExp (G, V, I.Uni(I.Type))

    (* Printing *)

    (* Right now, AL is in always reverse order *)
    (* Reverse again --- do not sort *)
    (* Right now, Table.app will pick int order -- do not sort *)
    fun famsToString (nil, msg) = msg
      | famsToString (a::AL, msg) = famsToString (AL, Names.qidToString (Names.constQid a) ^ " " ^ msg)

    fun showFam (a, (AL, AR)) =
        (print (Names.qidToString (Names.constQid a) ^ " |> "
		^ famsToString (AL, "\n")))

    fun show () = Table.app showFam soTable;

    (* weaken (G, a) = (w')
    *)
    fun weaken (I.Null, a) = I.id
      | weaken (I.Decl (G', D as I.Dec (name, V)), a) = 
        let 
	  val w' = weaken (G', a) 
	in
	  if belowEq (I.targetFam V, a) then I.dot1 w'
	  else I.comp (w', I.shift)
	end

  in
    val reset = reset
     
    val install = install
    val installFrozen = installFrozen

    val below = below
    val belowEq = belowEq
    val equiv = equiv

    val respects = respects
    val respectsN = respectsN

    val weaken = weaken
    val show = show

  end (* local *)
end; (* functor Subordinate *)
