(* Compiler *)
(* Author: Iliano Cervesato *)
(* Modified: Jeff Polakow *)
(* Modified: Carsten Schuermann *)
(* Modified: Larry Greenfield *)

functor Compile (structure IntSyn' : INTSYN
		 structure CompSyn' : COMPSYN
		   sharing CompSyn'.IntSyn = IntSyn'
		 structure Whnf : WHNF
		   sharing Whnf.IntSyn = IntSyn'
 		 structure TypeCheck : TYPECHECK
		   sharing TypeCheck.IntSyn = IntSyn'
		 structure Names : NAMES
		   sharing Names.IntSyn = IntSyn')
  : COMPILE =
struct

  structure IntSyn = IntSyn'
  structure CompSyn = CompSyn'

  local
    structure I = IntSyn
    structure C = CompSyn
  in

    val optimize = ref false

  (* compileGoalN A => g
     if A is a type interpreted as a subgoal in a clause and g is its
     compiled form.  No optimization is performed.

     Invariants:
     If G |- A : type,  A enf
        A has no existential type variables
     then G |- A ~> g  (A compiles to goal g)
     and  G |- g  goal
  *)
  fun compileGoalN (G, R as I.Root _) =
      (* A = H @ S *)
        C.Atom (R)
    | compileGoalN (G, I.Pi((I.Dec(_,A1), I.No), A2)) =
      (* A = A1 -> A2 *)
      let
	val a1 = I.targetFam A1
      in
	(* A1 is used to build the proof term, a1 for indexing *)
	C.Impl (compileClauseN false (G, A1), A1, a1, 
		compileGoalN (I.Decl(G, I.Dec(NONE, A1)), A2))
      end
    | compileGoalN (G, I.Pi((D as I.Dec(_, A1), I.Virtual), A2)) =
      (* A = A1 -> A2 *)
      let
	val a1 = I.targetFam A1
      in
	(* A1 is used to build the proof term, a1 for indexing *)
	C.Impl (compileClauseN false (G, A1), A1, a1, 
		compileGoalN (I.Decl(G, D), A2))
      end
    | compileGoalN (G, I.Pi((D, I.Maybe), A2)) =
      (* A = {x:A1} A2 *)
       C.All (D, compileGoalN (I.Decl(G, D), A2))
  (*  compileGoalN _ should not arise by invariants *)

  (* temporarily disabled because of missing context information *)
  (* Fri Jan 15 14:26:21 1999, -fp,cs *)
  (*
  and compileRootN (G, R as I.Root (h as (I.Const cid | I.Def cid), S)) =
    let
      fun findDupsS (I.Nil, (seen, dups, n)) = (seen, dups, n)
	| findDupsS (I.App(e, S'), sd) = 
	    findDupsS (S', findDupsE (e, sd))

      and findDupsE (I.Uni(u), sd) = sd
	| findDupsE (I.Pi((I.Dec(_, e1), _), e2), (s, d, n)) = 
	    (s, d, n+1)
	| findDupsE (I.Root(I.BVar(i), I.Nil), sd) = 
	    match(i, sd)
	| findDupsE (I.Root(I.BVar(i), S), (s, d, n)) =
	    (s, d, n+1)

	(* currently don't traverse spines with 
	     bvars at the head *)
	| findDupsE (I.Root(I.Const(i), S), sd) =
	    findDupsS (S, sd)
	| findDupsE (I.Root(I.Def(i), S), sd) =
	    findDupsS (S, sd)
	| findDupsE (I.Lam(I.Dec(_, e1), e2), (s, d, n)) =
	    (s, d, n+1)
                (* findDupsE (e1, findDupsE (e2, (s, d, n+1))) *)

      and match (i, (seen, dups, n)) =
	if List.exists (fn x => (x = i)) seen then 
	  (seen, i::dups, n+1)
	else (i::seen, dups, n)

      val (_, dupvars, totalsubs) = findDupsE(R, (nil, nil, 0))

      (* we now want to rewrite R so that
         any bound variables listed in dupvars are rewritten to
	 brand new variables.

	 any Pi or Lam's are rewritten to be brand new variables

	 also returns a list of types of vars to instantiate and
	 a list of eqns to unify after assignment is done
       *)

      (* returns true if a is in dupvars, and then removes one occurance
         of a from dupvars.  uses state just to make the code a little
	 easier to read below *)
      val dv = ref dupvars
      fun replaceIt a =
	let
	  fun member l1 nil = false
	    | member l1 (x::l2) =
	    if a = x then
	      (dv := (l1 @ l2); true)
	    else
	      member (x::l1) l2
	in
	  member nil (!dv)
	end

      (* rewriteE (e, A, n) = (e', evar list, Eqn list, n)

         if   G  |- e : A
	 then G' |- e' is template
	      G' = G extended by evar list
	      G' |- e' : A
       *)
      fun rewriteS (G, I.Nil, n) = (I.Nil, nil, nil, n)
	| rewriteS (G, I.App(e, S), n) =
	let
	  val (e', tv1, eqns1, n) = rewriteE(G, e, n)
	  val (S', tv2, eqns2, n) = rewriteS(G, S, n)
	in
	  (I.App(e', S'), tv1 @ tv2, eqns1 @ eqns2, n)
	end

      and rewriteE (G, e as I.Pi (_, _), n) = 
	   let
	     val X = I.Root(I.BVar(n+1), I.Nil)
	     val e' = I.EClo(e, I.Shift(totalsubs))
	     val A' = I.EClo(TypeCheck.infer' (G, e), I.Shift(totalsubs-n-1))
	   in
	     (X, A'::nil, I.Eqn(X, e')::nil, n+1)
	   end
	| rewriteE (G, e as I.Lam (_, _), n) =
	   let
	     val X = I.Root(I.BVar(n+1), I.Nil)
	     val e' = I.EClo(e, I.Shift(totalsubs))
	     val A' = I.EClo(TypeCheck.infer' (G, e), I.Shift(totalsubs-n-1))
	   in
	     (X, A'::nil, I.Eqn(X, e')::nil, n+1)
	   end
	| rewriteE (G, e as I.Root(I.BVar(i), I.Nil), n) =
	   if replaceIt i then
	     let
	       val X = I.Root(I.BVar(n+1), I.Nil)
	       val e' = I.Root(I.BVar(i + totalsubs), I.Nil)
	       val A' = I.EClo(TypeCheck.infer' (G, e), I.Shift(totalsubs-n-1))
	     in
	       (X, A'::nil, I.Eqn(X, e')::nil, n+1)
	     end
	   else (I.Root(I.BVar(i + totalsubs), I.Nil), nil, nil, n)
	| rewriteE (G, e as I.Root(I.BVar(i), S), n) =
	     let
	       val X = I.Root(I.BVar(n+1), I.Nil)
	       val e' = I.EClo(e, I.Shift(totalsubs))
	       val A' = I.EClo(TypeCheck.infer' (G, e), I.Shift(totalsubs-n-1))
	     in
	       (X, A'::nil, I.Eqn(X, e')::nil, n+1)
	     end
	| rewriteE (G, e as I.Root(I.Const cid, S), n) =
	     let
	       val (S', tv, eqns, n) = rewriteS(G, S, n)
	     in
	       (I.Root(I.Const cid, S'), tv, eqns, n)
	     end
	| rewriteE (G, e as I.Root(I.Def cid, S), n) =
	     let
	       val (S', tv, eqns, n) = rewriteS(G, S, n)
	     in
	       (I.Root(I.Const cid, S'), tv, eqns, n)
	     end

      val (R', tv, eqns, n) = rewriteE (G, R, 0)
					(* note that the type of R
					   really doesn't matter *)

      (* we now create the auxgoal's from eqns *)
      val ag = foldl (fn (eqn, ag') => C.Unify(eqn, ag')) C.Trivial eqns

      (* and here's the assignment *)
      val i = foldl (fn (A, i) => (C.Exists'(I.Dec(NONE, A), i)))
	            (C.Assign (R', ag)) tv
    in
      i
    end
  *)

  (* compileClauseN A => G
     if A is a type interpreted as a clause and G is its compiled form.

     Some optimization is attempted if so flagged.

     Invariants:
     If G |- A : type, A enf
        A has no existential type variables
     then G |- A ~> r  (A compiles to residual goal r)
     and  G |- r  resgoal
  *)

  and compileClauseN opt (G, R as I.Root (h, S)) =
      (*
      if opt andalso !optimize then
        compileRootN (G, R)
      else
      *)
	C.Eq(R)
    | compileClauseN opt (G, I.Pi((D as (I.Dec(_,A1)),I.No), A2)) =
      (* A = A1 -> A2 *)
	C.And (compileClauseN opt (I.Decl(G, D), A2), A1, 
	       compileGoalN (G, A1))
    | compileClauseN opt (G, I.Pi((D as (I.Dec(_,A1)),I.Virtual), A2)) =
      (* A = {x: A1} A2, x virtually occurring in A2 *)
	C.And (compileClauseN opt (I.Decl(G, D), A2), A1, 
	       compileGoalN (G, A1))
    | compileClauseN opt (G, I.Pi((D,I.Maybe), A2)) =
      (* A = {x:A1} A2 *)
        C.Exists (D, compileClauseN opt (I.Decl(G, D), A2))
    (*  compileClauseN _ should not arise by invariants *)

  fun compileClause opt (G, A) = 
        compileClauseN opt (G, Whnf.normalize (A, I.id))
  fun compileGoal (G, A) = compileGoalN (G, Whnf.normalize (A, I.id))

  (* compileCtx G = (G, dPool)

     Invariants:
     If |- G ctx,
     then |- G ~> dPool  (context G compile to clause pool dPool)
     and  |- dPool  dpool
  *)
  fun compileCtx opt G =
      let 
	fun compileCtx' I.Null = I.Null
	  | compileCtx' (I.Decl (G, D as I.Dec (_, A))) =
	    let 
	      val a = I.targetFam A
	    in
	      I.Decl (compileCtx' G, SOME (compileClause opt (G, A), I.id, a))
	    end
      in
	(G, compileCtx' G)
      end

  (* compileConDec (a, condec) = ()
     Effect: install compiled form of condec in program table.
             No effect if condec has no operational meaning
  *)
  (* Defined constants are currently not compiled *)
  fun compileConDec (a, I.ConDec(_, _, A, I.Type)) =
        C.sProgInstall (a, C.SClause (compileClauseN true (I.Null, A)))
    | compileConDec (a, I.SkoDec(_, _, A, I.Type)) =
        C.sProgInstall (a, C.SClause (compileClauseN true (I.Null, A)))
    | compileConDec _ = ()

  fun install (cid) = compileConDec (cid, I.sgnLookup cid)

  end  (* local open ... *)
end; (* functor Compile *)
