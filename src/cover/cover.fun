(* Coverage Checking *)
(* Author: Frank Pfenning *)

functor Cover
  (structure IntSyn' : INTSYN
   structure Whnf : WHNF
     sharing Whnf.IntSyn = IntSyn'
   structure Unify : UNIFY
     sharing Unify.IntSyn = IntSyn'
   structure ModeSyn' : MODESYN
     sharing ModeSyn'.IntSyn = IntSyn'
   structure Index : INDEX
     sharing Index.IntSyn = IntSyn'
   structure CompSyn : COMPSYN
     sharing CompSyn.IntSyn = IntSyn'
   structure Paths : PATHS)
  : COVER =
struct
  structure IntSyn = IntSyn'
  structure ModeSyn = ModeSyn'

  exception Error of string

  local
    structure I = IntSyn
    structure M = ModeSyn
    structure C = CompSyn
    structure P = Paths

    datatype CForm =
      InCover of I.Dec * CForm
    | OutCover of I.Dec * CForm
    | Ignore of I.Dec * CForm
    | Atom of I.Exp			(* always I.Root (a, S) *)

    fun buildSpine 0 = I.Nil
      | buildSpine k = (* k > 0 *)
        I.App (I.Root (I.BVar(k), I.Nil), buildSpine (k-1))

    fun modeToCForm' (a, k, I.Pi ((D,_), V), M.Mapp (M.Marg(M.Plus,_), ms)) =
        InCover (D, modeToCForm' (a, k+1, V, ms))
      | modeToCForm' (a, k, I.Pi ((D,_), V), M.Mapp (M.Marg(M.Minus,_), ms)) =
	OutCover (D, modeToCForm' (a, k+1, V, ms))
      | modeToCForm' (a, k, I.Pi ((D,_), V), M.Mapp (M.Marg(M.Star,_), ms)) =
	Ignore (D, modeToCForm' (a, k+1, V, ms))
      | modeToCForm' (a, k, I.Uni (I.Type), M.Mnil) =
	Atom (I.Root (a, buildSpine k))

    fun modeToCForm (a, ms) =
        modeToCForm' (I.Const a, 0, I.constType a, ms)

    (* CFormToGoal (G, (F, s)) = (G', (V, s')) *)
    fun CFormToCGoal (G, (InCover (D, F), s)) =
           CFormToCGoal (I.Decl (G, D), (F, I.dot1 s))
      | CFormToCGoal (G, (OutCover (I.Dec (_, V), F), s)) =
	let
	  val X = I.newEVar (G, I.EClo (V, s))
	  (* val X' = Whnf.lowerEVar X *)
	in
	  CFormToCGoal (G, (F, I.Dot (I.Exp X, s)))
	end
      | CFormToCGoal (G, (Ignore (I.Dec (_, V), F), s)) =
	let
	  val X = I.newEVar (G, I.EClo (V, s))
	in
	  CFormToCGoal (G, (F, I.Dot (I.Exp X, s)))
	end
      | CFormToCGoal (G, (Atom (V), s)) = (G, (V, s))

    fun matchClause (G, ps', (C.Eq Q, s)) =
          Unify.unifiable (G, ps', (Q, s))
      | matchClause (G, ps', (C.Assign _, s)) =
	  raise Error ("Coverage: Assignment not supported")
      | matchClause (G, ps', (C.And (r, A, g), s)) =
	let
	  val X = I.newEVar (G, I.EClo(A, s)) (* redundant? *)
	in
	  matchClause (G, ps', (r, I.Dot(I.Exp(X), s)))
	end
      | matchClause (G, ps', (C.In _, s)) =
	  raise Error ("Coverage: Virtual subgoals not supported")
      | matchClause (G, ps', (C.Exists (I.Dec (_, A), r), s)) =
	let
	  val X = I.newEVar (G, I.EClo(A, s))
	in
	  matchClause (G, ps', (r, I.Dot (I.Exp (X), s)))
	end
      | matchClause (G, ps', (C.Exists' _, s)) =
	  raise Error ("Coverage: Assignable EVars not supported")

    fun matchSig (G, ps', nil) = false
      | matchSig (G, ps', I.Const(c)::sgn') =
        let
	  val C.SClause(r) = C.sProgLookup c
	  val b = CSManager.trail
                  (fn () => matchClause (G, ps', (r, I.id)))
	in
	  b orelse matchSig (G, ps', sgn')
	end
      | matchSig (G, ps', _::sgn') = matchSig (G, ps', sgn')

    (* match *)
    (* no local assumptions *)
    fun match (G, ps' as (I.Root (I.Const (a), S), s)) =
        matchSig (G, ps', Index.lookup a)

  in
    fun checkCovers (a, ms) =
        let
	  val _ = print "Coverage checking not yet implemented!\n"
(*
	  val F0 = modeToCForm (a, ms)
	  val (G0, (V, s)) = CFormToCGoal (I.Null, (F0, I.id))
	  val b = match (G0, (V, s))
	  val _ = if b then print "Coverage satisfied!\n"
		  else print "Coverage failed!\n"
*)
	in
	  ()
	end
  end
end;  (* functor Cover *)
