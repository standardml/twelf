(* Compiler *)
(* Author: Iliano Cervesato *)
(* Modified: Jeff Polakow *)
(* Modified: Carsten Schuermann *)

functor Compile (structure IntSyn' : INTSYN
		 structure CompSyn' : COMPSYN
		   sharing CompSyn'.IntSyn = IntSyn'
		 structure Whnf : WHNF
		   sharing Whnf.IntSyn = IntSyn')
  : COMPILE =
struct

  structure IntSyn = IntSyn'
  structure CompSyn = CompSyn'

  local
    structure I = IntSyn
    structure C = CompSyn
  in

  (* compileGoalN A => g
     if A is a type interpreted as a subgoal in a clause and g is its
     compiled form.  No optimization is performed.

     Invariants:
     If G |- A : type,  A enf
        A has no existential type variables
     then G |- A ~> g  (A compiles to goal g)
     and  G |- g  goal
  *)
  fun compileGoalN (R as I.Root _) =
      (* A = H @ S *)
        C.Atom (R)
    | compileGoalN (I.Pi((I.Dec(_,A1), I.No), A2)) =
      (* A = A1 -> A2 *)
      let
	val a1 = I.targetFam A1
      in
	(* A1 is used to build the proof term, a1 for indexing *)
	C.Impl (compileClauseN A1, A1, a1, compileGoalN A2)
      end
    | compileGoalN (I.Pi((D, I.Maybe), A2)) =
      (* A = {x:A1} A2 *)
       C.All (D, compileGoalN A2)
  (*  compileGoalN _ should not arise by invariants *)

  (* compileClauseN A => G
     if A is a type interpreted as a clause and G is its compiled form.
     No optimization is performed.
     Invariants:
     If G |- A : type, A enf
        A has no existential type variables
     then G |- A ~> r  (A compiles to residual goal r)
     and  G |- r  resgoal
  *)
  and compileClauseN (R as I.Root _) =
      (* A = H @ S *)
        C.Eq (R)
    | compileClauseN (I.Pi((d as (I.Dec(_,A1)),I.No), A2)) =
      (* A = A1 -> A2 *)
	C.And (compileClauseN A2, A1, compileGoalN A1)
    | compileClauseN (I.Pi((D,I.Maybe), A2)) =
      (* A = {x:A1} A2 *)
        C.Exists (D, compileClauseN A2)
    (*  compileClauseN _ should not arise by invariants *)

  fun compileClause (A) = compileClauseN (Whnf.normalize (A, I.id))
  fun compileGoal (A) = compileGoalN (Whnf.normalize (A, I.id))

  (* compileCtx G = (G, dPool)

     Invariants:
     If |- G ctx,
     then |- G ~> dPool  (context G compile to clause pool dPool)
     and  |- dPool  dpool
  *)
  fun compileCtx G =
      let 
	fun compileCtx' I.Null = I.Null
	  | compileCtx' (I.Decl (G, D as I.Dec (_, A))) =
	    let 
	      val a = I.targetFam A
	    in
	      I.Decl (compileCtx' G, SOME (compileClause A, I.id, a))
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
        C.sProgInstall (a, C.SClause (compileClauseN A))
    | compileConDec _ = ()

  fun install (cid) = compileConDec (cid, I.sgnLookup cid)

  end  (* local open ... *)
end; (* functor Compile *)
