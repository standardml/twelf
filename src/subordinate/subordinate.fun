(* Subordination a la Virga [Technical Report 96] *)
(* Author: Carsten Schuermann *)

(* Reverse subordination order *)

functor Subordinate
  (structure Global : GLOBAL
   structure IntSyn': INTSYN
   structure Whnf : WHNF
     sharing Whnf.IntSyn = IntSyn'
   structure Names : NAMES
     sharing Names.IntSyn = IntSyn'
   structure Table : TABLE where type key = int
   structure IntSet : INTSET
     )
  : SUBORDINATE =
struct
  structure IntSyn = IntSyn'

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
    val insert = Table.insert soGraph
    val lookup = Table.lookup
    fun adjNodes a = valOf (Table.lookup soGraph a)  (* must be defined! *)
    fun insertNewFam a =
           Table.insert soGraph (a, IntSet.empty)
    val updateFam = Table.insert soGraph

    (* Apply f to every node reachable from b *)
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
    fun addNewEdge (b, a) =
          updateFam (b, IntSet.insert(a,adjNodes(b)))

    val fTable : bool Table.Table = Table.new (32)
    val fLookup = Table.lookup fTable
    val fInsert = Table.insert fTable

    (* reset () = ()

       Effect: Empties soGraph, fTable
    *)
    fun reset () = (Table.clear soGraph;
                    Table.clear fTable)

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
        (reachable (b, a); false)
	handle Reachable => true

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
	else addNewEdge (b, a)

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
          (addSubord (I.targetFam V1, a);
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
    and installTypeN (V) = installTypeN' (V, I.targetFam V)

    (* installKindN (V, a) = ()
       V nf, a : {x1:A1}...{xn:An} type, V = {xi:Ai}...{xn:An}type
       Effect: add subordination info from V into table
    *)
    (* there are no kind-level definitions *)
    fun installKindN (I.Uni(L), a) = ()
      | installKindN (I.Pi ((I.Dec (_, V1), P), V2), a) =
	  (addSubord (I.targetFam V1, a);
	   installTypeN (V1);
	   installKindN (V2, a))

    (* install c = ()

       Effect: if c : V, add subordination from V into table
    *)
    fun install c = 
	let 
	  val V = I.constType c
	in
	  case I.targetFamOpt V
	    of NONE => (insertNewFam (c);
			installKindN (V, c))
	     | SOME a => (case IntSyn.sgnLookup c
                            of IntSyn.ConDec _ => checkFreeze (c, a)
                             | IntSyn.SkoDec _ => checkFreeze (c, a)
                               (* FIX: skolem types should probably be created frozen -kw *)
                             | _ => ();
			  (* simplified  Tue Mar 27 20:58:31 2001 -fp *)
			  installTypeN' (V, a))
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

    (* respectsTypeN' (V, a) = () iff V respects current subordination
       respectsTypeN (V) = ()
       V nf, V = {x1:A1}...{xn:An} a @ S

       Effect: raise Error (msg)
    *)
    fun respectsTypeN' (I.Pi ((D as I.Dec (_, V1), _), V2), a) =
          (checkBelow (I.targetFam V1, a);
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
      | respectsTypeN' (I. Root _, _) = ()
    and respectsTypeN (V) = respectsTypeN' (V, I.targetFam V)

    fun respects (G, (V, s)) = respectsTypeN (Whnf.normalize (V, s))
    fun respectsN (G, V) = respectsTypeN (V)

    (* Printing *)

    (* Right now, AL is in always reverse order *)
    (* Reverse again --- do not sort *)
    (* Right now, Table.app will pick int order -- do not sort *)
    fun famsToString (bs, msg) =
        IntSet.foldl (fn (a, msg) => Names.qidToString (Names.constQid a) ^ " " ^ msg) "\n" bs
    (*
    fun famsToString (nil, msg) = msg
      | famsToString (a::AL, msg) = famsToString (AL, Names.qidToString (Names.constQid a) ^ " " ^ msg)
    *)

    fun showFam (a, bs) =
        (print (Names.qidToString (Names.constQid a) ^ " |> "
		^ famsToString (bs, "\n")))

    fun show () = Table.app showFam soGraph;

    (* weaken (G, a) = (w') *)
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
