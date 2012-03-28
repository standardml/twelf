(* State definition for Proof Search *)
(* Author: Carsten Schuermann *)

functor State
  (structure Formatter : FORMATTER) : STATE =
struct
  (*! structure IntSyn = IntSyn' !*)
  (*! structure Tomega = Tomega' !*)
  structure Formatter = Formatter

  datatype State =
    State of Tomega.Worlds
      * Tomega.Dec IntSyn.Ctx * Tomega.Prg * Tomega.For
  | StateLF of IntSyn.Exp    (* StateLF X, X is always lowered *)

  datatype Focus =
    Focus of Tomega.Prg * Tomega.Worlds
  | FocusLF of IntSyn.Exp

 (* datatype State
    = State of (Tomega.Dec IntSyn.Ctx * Tomega.For) * Tomega.Worlds
 *)
(*  datatype SideCondition  (* we need some work here *)
    = None
    | All   of SideCondition
    | And   of SideCondition * SideCondition
    | Order of Order.Predicate
*)

  exception Error of string

  local
    structure T = Tomega
    structure I = IntSyn



    (* find P = [X1 .... Xn]
       Invariant:
       If   P is a well-typed program
       then [X1 .. Xn] are all the open subgoals that occur within P
    *)
    fun findPrg (T.Lam (_, P)) = findPrg P
      | findPrg (T.New P) = findPrg P
      | findPrg (T.Choose P) = findPrg P
      | findPrg (T.PairExp (_, P)) = findPrg P
      | findPrg (T.PairBlock (B, P)) = findPrg P
      | findPrg (T.PairPrg (P1, P2)) = findPrg P1 @ findPrg P2
      | findPrg (T.Unit) = []
      | findPrg (T.Rec (_, P)) = findPrg P
      | findPrg (T.Case (T.Cases C)) = findCases C
      | findPrg (T.PClo (P, t)) = findPrg P @ findSub t
      | findPrg (T.Let (D, P1, P2)) = findPrg P1 @ findPrg P2
      | findPrg (T.LetPairExp (D1, D2, P1, P2)) = findPrg P1 @ findPrg P2
      | findPrg (T.LetUnit (P1, P2)) = findPrg P1 @ findPrg P2
      | findPrg (X as T.EVar (_, ref NONE, _, _, _, _)) = [X]
      | findPrg (X as T.EVar (_, ref (SOME P), _, _, _, _)) = findPrg P
      | findPrg (T.Const _) = []
      | findPrg (T.Var _) = []
      | findPrg (T.Redex (P, S)) = findPrg P @ findSpine S

    and findCases nil = []
      | findCases ((_, _, P) :: C) = findPrg P @ findCases C

    and findSub (T.Shift _) = []
      | findSub (T.Dot (F, t)) = findFront F @ findSub t

    and findFront (T.Idx _) = []
      | findFront (T.Prg P) = findPrg P
      | findFront (T.Exp _) = []
      | findFront (T.Block _) = []
      | findFront (T.Undef) = []

    and findSpine (T.Nil) = []
      | findSpine (T.AppPrg (P, S)) = findPrg P @ findSpine S
      | findSpine (T.AppExp (_, S)) = findSpine S
      | findSpine (T.AppBlock (_, S)) = findSpine S   (* by invariant: blocks don't contain free evars *)

    (* find P = [X1 .... Xn]
       Invariant:
       If   P is a well-typed program
       then [X1 .. Xn] are all the open subgoals that occur within P
    *)
    fun findExp (Psi, T.Lam (D, P)) K = findExp (I.Decl (Psi, D), P) K
      | findExp (Psi, T.New P) K = findExp (Psi, P) K
      | findExp (Psi, T.Choose P) K = findExp (Psi, P) K
      | findExp (Psi, T.PairExp (M, P)) K =
          findExp (Psi, P) (Abstract.collectEVars (T.coerceCtx Psi, (M, I.id), K))
      | findExp (Psi, T.PairBlock (B, P)) K = findExp (Psi, P) K
          (* by invariant: Blocks don't contain free evars. *)
      | findExp (Psi, T.PairPrg (P1, P2)) K = findExp (Psi, P2) (findExp (Psi, P1) K)
      | findExp (Psi, T.Unit) K = K
      | findExp (Psi, T.Rec (D, P)) K = findExp (Psi, P) K
      | findExp (Psi, T.Case (T.Cases C)) K = findExpCases (Psi, C) K
      | findExp (Psi, T.PClo (P, t)) K =
          findExpSub (Psi, t) (findExp (Psi, P) K)
      | findExp (Psi, T.Let (D, P1, P2)) K =
          findExp (I.Decl (Psi, D), P2) (findExp (Psi, P1) K)
      | findExp (Psi, T.LetPairExp (D1, D2, P1, P2)) K =
          findExp (I.Decl (I.Decl (Psi, T.UDec D1), D2), P2) (findExp (Psi, P1) K)
      | findExp (Psi, T.LetUnit (P1, P2)) K =
          findExp (Psi, P2) (findExp (Psi, P1) K)
      | findExp (Psi, X as T.EVar _) K = K
      | findExp (Psi, T.Const _) K = K
      | findExp (Psi, T.Var _) K = K
      | findExp (Psi, T.Redex (P, S)) K = findExpSpine (Psi, S) K

    and findExpSpine (Psi, T.Nil) K = K
      | findExpSpine (Psi, T.AppPrg (_, S)) K = findExpSpine (Psi, S) K
      | findExpSpine (Psi, T.AppExp (M, S)) K = findExpSpine (Psi, S) (Abstract.collectEVars (T.coerceCtx Psi, (M, I.id), K))
      | findExpSpine (Psi, T.AppBlock (_, S)) K = findExpSpine (Psi, S) K


    and findExpCases (Psi, nil) K = K
      | findExpCases (Psi, (_, _, P) :: C) K =
          findExpCases (Psi, C) (findExp (Psi, P) K)
    and findExpSub (Psi, T.Shift _)  K = K
      | findExpSub (Psi, T.Dot (F, t)) K =
          findExpSub (Psi, t) (findExpFront (Psi, F) K)

    and findExpFront (Psi, T.Idx _) K  = K
      | findExpFront (Psi, T.Prg P) K = findExp (Psi, P) K
      | findExpFront (Psi, T.Exp M) K =
          Abstract.collectEVars (T.coerceCtx Psi,  (M, I.id), K)
      | findExpFront (Psi, T.Block _) K = K
      | findExpFront (Psi, T.Undef) K = K


    (* init F = S

       Invariant:
       S = (. |> F) is the initial state
    *)
    fun init (F, W) =
        let
          val X = T.newEVar (I.Null, F)
        in State (W, I.Null, X, F)
        end


    (* close S = B

       Invariant:
       If  B holds iff S  doesn't contain any free subgoals
    *)
    fun close (State (W, _, P, _)) =
         (case (findPrg P, findExp (I.Null, P) [])
            of (nil, nil) => true
             | _ => false)


  in
    val close = close
    val init = init

    val collectT = findPrg
    val collectLF = fn P => findExp (I.Null, P) []
    val collectLFSub = fn s => findExpSub (I.Null, s) []
  end
end