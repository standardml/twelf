(* Subordination a la Virga [Technical Report 96] *)
(* Author: Carsten Schuermann *)

(* Reverse subordination order *)

functor Subordinate
  (structure Global : GLOBAL
   (*! structure IntSyn' : INTSYN !*)
   structure Whnf : WHNF
   (*! sharing Whnf.IntSyn = IntSyn' !*)
   structure Names : NAMES
   (*! sharing Names.IntSyn = IntSyn' !*)
   structure Table : TABLE where type key = IDs.mid * IDs.cid
   structure CidTable : TABLE where type key =  IDs.cid
   structure MemoTable : TABLE where type key = IDs.cid * IDs.cid
   structure IntSet : INTSET
     )
  : SUBORDINATE =
struct
  (*! structure IntSyn = IntSyn' !*)

  exception Error of string
 
  local
    structure I = IntSyn

    (* Subordination graph

       soGraph is valid
       iff for any type families a and b
       if b > a then there a path from b to a in the graph.

       Subordination is transitive, but not necessarily reflexive.
    *)
    val soGraph : (IntSet.intset) Table.Table = Table.new (32)
    fun adjNodes a = valOf (Table.lookup soGraph (ModSyn.currentMod(), a))  (* must be defined! *)
    fun insertNewFam a =
           Table.insert soGraph ((ModSyn.currentMod(), a), IntSet.empty)
    fun updateFam (a, is)  = Table.insert soGraph ((ModSyn.currentMod(), a), is)
    val insert = updateFam


    (* memotable to avoid repeated graph traversal *)
    (* think of hash-table model *)
    val memoTable : (bool * int) MemoTable.Table = MemoTable.new (2048)
    val memoInsert = MemoTable.insert memoTable
    val memoLookup = MemoTable.lookup memoTable
    val memoClear = fn () => MemoTable.clear memoTable
    val memoCounter = ref 0

    (* Apply f to every node reachable from b *)
    (* Includes the node itself (reflexive) *)
    fun appReachable f b =
        let fun rch (b, visited) =
	        if IntSet.member (b, visited)
		  then visited
		else (f b ;
		      IntSet.foldl rch (IntSet.insert (b, visited)) (adjNodes b))
	in
	  (rch (b, IntSet.empty) ; ())
	end

    exception Reachable
    fun reach (b, a, visited) =
        let fun rch (b, visited) =
	        if IntSet.member (b, visited)
		  then visited
		else let val adj = adjNodes b
		     in
		       if IntSet.member (a, adj)
			 then raise Reachable
		       else IntSet.foldl rch (IntSet.insert (b, visited)) adj
		     end
	in
	  rch  (b, visited)
	end

    fun reachable (b, a) = reach (b, a, IntSet.empty)

    (* b must be new *)
    (* this is sometimes violated below, is this a bug? *)
    (* Thu Mar 10 13:13:01 2005 -fp *)
    fun addNewEdge (b, a) =
        ( memoCounter := !memoCounter+1 ;
	  memoInsert ((b,a), (true, !memoCounter)) ;
	  updateFam (b, IntSet.insert(a,adjNodes(b))) )

    val fTable : bool Table.Table = Table.new (32)
    fun fLookup a = Table.lookup fTable (ModSyn.currentMod (), a)
    fun fInsert (a, is) = Table.insert fTable ((ModSyn.currentMod (), a), is)

    (*
       Freezing type families

       Frozen type families cannot be extended later with additional
       constructors.
     *)
    fun fGet (a) =
        (case fLookup a
           of SOME frozen => frozen
            | NONE => false)

    fun fSet (a, frozen) =
        let val _ = Global.chPrint 5
	            (fn () => (if frozen then "Freezing " else "Thawing ")
		              ^ IntSyn.conDecFoldName (ModSyn.sgnLookup a) ^ "\n")
	in
	  fInsert (a, frozen)
	end

    (* pre: a is not a type definition *)
    fun checkFreeze (c, a) =
        if fGet a
        then raise Error ("Freezing violation: constant "
                          ^ IntSyn.conDecFoldName (ModSyn.sgnLookup a)
                          ^ "\nextends type family "
                          ^ IntSyn.conDecFoldName (ModSyn.sgnLookup c))
        else ()

    (* no longer needed since freeze is now transitive *)
    (* Sat Mar 12 21:40:15 2005 -fp *)
    (*
    fun frozenSubError (a, b) =
        raise Error ("Freezing violation: frozen type family "
                     ^ Names.qidToString (Names.constQid b)
                     ^ "\nwould depend on unfrozen type family "
                     ^ Names.qidToString (Names.constQid a))
    *)

    (* no longer needed since freeze is now transitive *)
    (* Sat Mar 12 21:40:15 2005 -fp *)
    (* pre: a, b are not type definitions *)
    (*
    fun checkFrozenSub (a, b) =
        (case (fGet a, fGet b)
           of (false, true) => frozenSubError (a, b)
            | _ => ())
    *)

    (* pre: b is not a type definition *)
    (* no longer needed since freeze is transitive *)
    (* Sat Mar 12 21:38:58 2005 -fp *)
    (*
    fun checkMakeFrozen (b, otherFrozen) =
        (* Is this broken ??? *)
        (* Mon Nov 11 16:54:29 2002 -fp *)
        (* Example:
	   a : type.
	   b : type.
	   %freeze a b.
	   h : (a -> b) -> type.
           is OK, but as b |> a in its subordination
        *)
        let
	  fun check a =
	    if fGet a orelse List.exists (fn x => x = a) otherFrozen
	      then ()
	    else frozenSubError (a, b)
	in
	  if fGet b then ()
	  else appReachable check b
	end
    *)

    fun expandFamilyAbbrevs a =
        (case ModSyn.constUni a
           of I.Type => raise Error ("Constant " ^ IntSyn.conDecFoldName (ModSyn.sgnLookup a)
                                     ^ " must be a type family to be frozen or thawed")
            | I.Kind =>
        (case ModSyn.sgnLookup a
           of IntSyn.ConDec _ => a
            | IntSyn.ConDef _ =>
                ModSyn.targetFam (ModSyn.constDef a)
            | IntSyn.SkoDec _ => a
            | IntSyn.AbbrevDef _ =>
                ModSyn.targetFam (ModSyn.constDef a)))

    (* superseded by freeze *)
    (*
    fun installFrozen (L) =
        let
          val L = map expandFamilyAbbrevs L
	  (* val _ = print ("L = " ^ (foldl (fn (c,s) => Names.qidToString (Names.constQid c) ^ s) "\n" L)); *)
        in
          List.app (fn a => checkMakeFrozen (a, L)) L;
          List.app (fn a => fSet (a, true)) L
        end
    *)

    (* freeze L = ()
       freezes all families in L, and all families transitively
       reachable from families in L

       Intended to be called from programs
    *)
    val freezeList : IntSet.intset ref = ref IntSet.empty
    fun freeze (L) =
        let
	  val _ = freezeList := IntSet.empty
	  val L' = map expandFamilyAbbrevs L
	  val _ = List.app (fn a =>
			    appReachable (fn b =>
					  (fSet (b, true);
					   freezeList := IntSet.insert(b, !freezeList))) a)
	          L'
	  val cids = IntSet.foldl (op::) nil (!freezeList)
	in
	  cids
	end

    (* frozen L = true if one of the families in L is frozen *)
    fun frozen (L) =
        let
	  val L' = map expandFamilyAbbrevs L
	in
	  List.exists (fn a => fGet a) L'
	end

    (* a <| b = true iff a is (transitively) subordinate to b

       Invariant: a, b families
    *)
    fun computeBelow (a, b) =
        (reachable (b, a); memoInsert ((b,a), (false,!memoCounter)); false)
	handle Reachable => (memoInsert ((b,a), (true, !memoCounter)); true)

    fun below (a, b) =
        case memoLookup (b, a)
	  of NONE => computeBelow (a, b)
           | SOME(true,c) => true	(* true entries remain valid *)
           | SOME(false,c) => if c = !memoCounter then false
			      else computeBelow (a, b) (* false entries are invalidated *)

    (* a <* b = true iff a is transitively and reflexively subordinate to b

       Invariant: a, b families
    *)
    fun belowEq (a, b) = (a = b) orelse below (a, b)

    (* a == b = true iff a and b subordinate each other

       Invariant: a, b families
    *)
    fun equiv (a, b) = belowEq (a, b) andalso belowEq (b, a)

    fun addSubord (a, b) =
        if below (a, b) then ()
	else if fGet b
	       (* if b is frozen and not already b #> a *)
	       (* subordination would change; signal error *)
	       then raise Error ("Freezing violation: "
				 ^ IntSyn.conDecFoldName (ModSyn.sgnLookup b)
				 ^ " would depend on "
				 ^ IntSyn.conDecFoldName (ModSyn.sgnLookup a))
	     else addNewEdge (b, a)

    (* Thawing frozen families *)
    (* Returns list of families that were thawed *)
    val aboveList : IntSyn.cid list ref = ref nil
    fun addIfBelowEq a's =
        fn b => if List.exists (fn a => belowEq (a, b)) a's
		  then aboveList := b::(!aboveList)
		else ()

    fun thaw a's =
        let
	  val a's' = map expandFamilyAbbrevs a's
	  val _ = aboveList := nil
          val curr = ModSyn.currentMod()
	  val _ = Table.app (fn ((m, c),_) => if m = curr then addIfBelowEq a's' c else ()) soGraph;
	  val _ = List.app (fn b => fSet(b, false)) (!aboveList)
	in
	  !aboveList
	end

    (*
       Definition graph
       The definitions graph keeps track of chains of
       definitions for type families (not object-level definitions)

       We say b <# a if b = [x1:A1]...[xn:An] {y1:B1}...{y1:Bm} a @ S

       The definition graph should be interpreted transitively.
       It can never be reflexive.

       The #> relation is stored in order to prevent totality
       checking on type families involved in definitions, because
       in the present implementation this would yield unsound
       results.

       NOTE: presently, the head "a" is always expanded until it is
       no longer a definition.  So if a #> b then a is always declared,
       never defined and b is always defined, never declared.

       Fri Dec 27 08:37:42 2002 -fp (just before 1.4 alpha)
    *)

    (* While implmenting the Modulesystem, we have decided that
       the defGraph in on cids and not on (mid, cid) pairs. 
       --cs --fr Wed Jan 28 16:06:37 2009
    *)
    val defGraph : (IntSet.intset) CidTable.Table = CidTable.new (32)

    (* occursInDef a = true
       iff there is a b such that a #> b
    *)
    fun occursInDef a =
        (case CidTable.lookup defGraph a
	   of NONE => false
            | SOME _ => true)

    (* insertNewDef (b, a) = ()
       Effect: update definition graph.

       Call this upon seeing a type-level definition
           b = [x1:A1]...[xn:An] {y1:B1}...{y1:Bm} a @ S : K
       to record a #> b.
    *)
    fun insertNewDef (b, a) =
        (case CidTable.lookup defGraph a
	   of NONE => CidTable.insert defGraph (a, IntSet.insert (b, IntSet.empty))
            | SOME(bs) => CidTable.insert defGraph (a, IntSet.insert (b, bs)))

    (* installDef (c) = ()
       Effect: if c is a type-level definition,
               update definition graph.
    *)
    fun installConDec (b, I.ConDef (_, _, _, A, K, I.Kind, _)) =
          (* ModSyn.targetFam must be defined, but expands definitions! *)
          insertNewDef (b, ModSyn.targetFam A) 
      | installConDec _ = ()

    fun installDef c = installConDec (c, ModSyn.sgnLookup c)

    fun installInclude(ModSyn.SigIncl from) =
      Table.app (fn ((m, c), is) =>
                    if m = from
                    then (
                       insertNewFam c; 
                       IntSet.foldl  (fn (d, ()) => addSubord(c,d)) () is
		    ) else ()
                )
                soGraph 
      
    (* checkNoDef a = ()
       Effect: raises Error(msg) if there exists a b such that b <# a
               or b <# a' for some a' < a in the current signature.
    *)
    fun checkNoDef a =
        if occursInDef a
	  then raise Error ("Definition violation: family "
			    ^ IntSyn.conDecFoldName (ModSyn.sgnLookup a)
			    ^ "\noccurs as right-hand side of type-level definition")
	else appReachable (fn a' =>
	     if occursInDef a'
	       then raise Error ("Definition violation: family "
				 ^ IntSyn.conDecFoldName (ModSyn.sgnLookup a)
				 ^ " |> "
				 ^ IntSyn.conDecFoldName (ModSyn.sgnLookup a')
				 ^ ",\nwhich occurs as right-hand side of a type-level definition")
	     else ())
	     a

    (* reset () = ()

       Effect: Empties soGraph, fTable, defGraph
    *)
    fun reset () = (Table.clear soGraph;
                    Table.clear fTable;
		    MemoTable.clear memoTable;
		    CidTable.clear defGraph)

    (* 
       Subordination checking no longer traverses spines,
       so approximate types are no longer necessary.
       This takes stronger advantage of the normal form invariant.
       Mon Nov 11 16:59:52 2002  -fp
    *)

    (* installTypeN' (V, a) = ()
       installTypeN (V) = ()
       V nf, V = {x1:A1}...{xn:An} a @ S

       Effect: add subordination info from V into table
    *)
    and installTypeN' (I.Pi ((D as I.Dec (_, V1), _), V2), a) = 
          (addSubord (ModSyn.targetFam V1, a);
	   installTypeN (V1);
	   installTypeN' (V2, a))
      | installTypeN' (V as I.Root (I.Def _, _), a) =
	(* this looks like blatant overkill ... *)
	(* Sun Nov 10 11:15:47 2002 -fp *)
	let
	  val V' = Whnf.normalize (Whnf.expandDef (V, I.id))
	in
	  installTypeN' (V', a)
	end
      | installTypeN' (I.Root _, _) = ()
    and installTypeN (V) = installTypeN' (V, ModSyn.targetFam V)

    (* installKindN (V, a) = ()
       V nf, a : {x1:A1}...{xn:An} type, V = {xi:Ai}...{xn:An}type
       Effect: add subordination info from V into table
    *)
    (* there are no kind-level definitions *)
    fun installKindN (I.Uni(L), a) = ()
      | installKindN (I.Pi ((I.Dec (_, V1), P), V2), a) =
	  (addSubord (ModSyn.targetFam V1, a);
	   installTypeN (V1);
	   installKindN (V2, a))

    (* install c = ()

       Effect: if c : V, add subordination from V into table
    *)
    fun install c = 
	let 
	  val V = ModSyn.constType c
	in
	  case ModSyn.targetFamOpt V
	    of NONE => (insertNewFam (c);
			installKindN (V, c))
	     | SOME a => (case ModSyn.sgnLookup c
                            of IntSyn.ConDec _ => checkFreeze (c, a)
                             | IntSyn.SkoDec _ => checkFreeze (c, a)
                               (* FIX: skolem types should probably be created frozen -kw *)
                             | _ => ();
			  (* simplified  Tue Mar 27 20:58:31 2001 -fp *)
			  installTypeN' (V, a))
	end

    (* installBlock b = ()
       Effect: if b : Block, add subordination from Block into table
    *)
    (* BDec, ADec, NDec are disallowed here *)
    fun installDec (I.Dec(_,V)) = installTypeN V

    fun installSome (I.Null) = ()
      | installSome (I.Decl(G, D)) =
        ( installSome G; installDec D )

    (* b must be block *)
    fun installBlock b =
        let
	  val I.BlockDec(_, _, G, Ds) = ModSyn.sgnLookup b
	in
	  installSome G;
	  List.app (fn D => installDec D) Ds
	end

    (* Respecting subordination *)

    (* checkBelow (a, b) = () iff a <| b
       Effect: raise Error(msg) otherwise
    *)
    fun checkBelow (a, b) =
        if not (below (a, b))
	  then raise Error ("Subordination violation: "
			    ^ IntSyn.conDecFoldName (ModSyn.sgnLookup a) ^ " not <| " ^ IntSyn.conDecFoldName (ModSyn.sgnLookup b))
	else ()

    (* respectsTypeN' (V, a) = () iff V respects current subordination
       respectsTypeN (V) = ()
       V nf, V = {x1:A1}...{xn:An} a @ S

       Effect: raise Error (msg)
    *)
    fun respectsTypeN' (I.Pi ((D as I.Dec (_, V1), _), V2), a) =
          (checkBelow (ModSyn.targetFam V1, a);
	   respectsTypeN (V1);
	   respectsTypeN' (V2, a))
      | respectsTypeN' (V as I.Root (I.Def _, _), a) =
	(* this looks like blatant overkill ... *)
	(* Sun Nov 10 11:15:47 2002 -fp *)
	let
	  val V' = Whnf.normalize (Whnf.expandDef (V, I.id))
	in
	  respectsTypeN' (V', a)
	end
      | respectsTypeN' (I.Root _, _) = ()
    and respectsTypeN (V) = respectsTypeN' (V, ModSyn.targetFam V)

    fun respects (G, (V, s)) = respectsTypeN (Whnf.normalize (V, s))
    fun respectsN (G, V) = respectsTypeN (V)

    (* Printing *)

    (* Right now, AL is in always reverse order *)
    (* Reverse again --- do not sort *)
    (* Right now, Table.app will pick int order -- do not sort *)
    fun famsToString (bs, msg) =
        IntSet.foldl (fn (a, msg) => IntSyn.conDecFoldName (ModSyn.sgnLookup a) ^ " " ^ msg) "\n" bs
    (*
    fun famsToString (nil, msg) = msg
      | famsToString (a::AL, msg) = famsToString (AL, Names.qidToString (Names.constQid a) ^ " " ^ msg)
    *)

    fun showFam (a, bs) =
        (print (IntSyn.conDecFoldName (ModSyn.sgnLookup a)
		^ (if fGet a then " #> " else " |> ")
		^ famsToString (bs, "\n")))

    fun showOne m = Table.app (fn ((m', a), bs) => if m = m' then showFam (a, bs) else ()) soGraph;
    fun show () = ModSyn.modApp (fn m => (case ModSyn.modLookup m 
				           of ModSyn.SigDec (name) =>
					      (print("signature " ^ Names.foldQualifiedName name ^ "\n");
					      showOne m;
					      print("\n"))
					    | _ => ()) )

    (* weaken (G, a) = (w') *)
    fun weaken (I.Null, a) = I.id
      | weaken (I.Decl (G', D as I.Dec (name, V)), a) = 
        let 
	  val w' = weaken (G', a) 
	in
	  if belowEq (ModSyn.targetFam V, a) then I.dot1 w'
	  else I.comp (w', I.shift)
	end

 
    (* showDef () = ()
       Effect: print some statistics about constant definitions
    *)
    local
      val declared = ref 0
      val defined = ref 0
      val abbrev = ref 0
      val other = ref 0
      val heightArray = Array.array (32, 0)
      val maxHeight = ref 0

      fun inc (r) = (r := !r+1)
      fun incArray (h) = (Array.update (heightArray, h, Array.sub (heightArray, h)+1))
      (* ignore blocks and skolem constants *)
      fun max (h) = (maxHeight := Int.max (h, !maxHeight))
      fun reset () = (declared := 0; defined := 0; abbrev := 0; other := 0;
		      Array.modify (fn i => 0) heightArray;
	              maxHeight := 0)
    in
      fun analyzeAnc (I.Anc (NONE, _, _)) = ( incArray 0 )
	| analyzeAnc (I.Anc (_, h, _)) = ( incArray h ; max h )
      fun analyze (I.ConDec (_, _, _, _, _, L)) =
	  ( inc declared ) 
        | analyze (I.ConDef (_, _, _, _, _, L, ancestors)) =
	  ( inc defined ; analyzeAnc ancestors )
        | analyze (I.AbbrevDef (_, _, _, _, _, L)) =
	  ( inc abbrev )
	| analyze _ = ( inc other )
      fun showDef () =
	  let
	    val _ = reset ()
	    val _ = ModSyn.sgnAppC (fn c => analyze (ModSyn.sgnLookup c))
	    val _ = print ("Declared: " ^ Int.toString (!declared) ^ "\n")
	    val _ = print ("Defined : " ^ Int.toString (!defined) ^ "\n")
	    val _ = print ("Abbrevs : " ^ Int.toString (!abbrev) ^ "\n")
	    val _ = print ("Other   : " ^ Int.toString (!other) ^ "\n")
	    val _ = print ("Max definition height: " ^ Int.toString (!maxHeight) ^ "\n")
	    val _ = ArraySlice.appi
	              (fn (h, i) => print (" Height " ^ Int.toString h ^ ": "
					   ^ Int.toString i ^ " definitions\n"))
		      (ArraySlice.slice (heightArray, 0, SOME(!maxHeight+1)))
	  in
	    ()
	  end
    end
  in
    val reset = reset
     
    val install = install
    val installDef = installDef
    val installBlock = installBlock
    val installInclude = installInclude

    (* val installFrozen = installFrozen *)

    val freeze = freeze
    val frozen = frozen
    val thaw = thaw

    val addSubord = addSubord

    val below = below
    val belowEq = belowEq
    val equiv = equiv

    val checkNoDef = checkNoDef

    val respects = respects
    val respectsN = respectsN

    val weaken = weaken

    val show = show
    val showDef = showDef

  end (* local *)
end; (* functor Subordinate *)
