(* Filling  Version 1.4 *)
(* Author: Carsten Schuermann *)

functor Fill 
  (structure MTPGlobal : MTPGLOBAL
   (*! structure IntSyn' : INTSYN !*)
   (*! structure Tomega' : TOMEGA !*)
   (*! sharing Tomega'.IntSyn = IntSyn' !*)
   structure State' : STATE
   (*! sharing State'.IntSyn = IntSyn' !*)
   (*! sharing State'.Tomega = Tomega' !*)
   structure Abstract : ABSTRACT
   (*! sharing Abstract.IntSyn = IntSyn' !*)
   (*! sharing Abstract.Tomega = Tomega' !*)
   structure TypeCheck : TYPECHECK
   (*! sharing TypeCheck.IntSyn = IntSyn' !*)
   structure MTPData : MTPDATA
   structure Search  : SEARCH
   (*! sharing Search.IntSyn = IntSyn' !*)
   (*! sharing Search.Tomega = Tomega' !*)
     sharing Search.State = State'
   structure Normalize : NORMALIZE
   (*! sharing Normalize.IntSyn = IntSyn' !*)
   (*! sharing Normalize.Tomega = Tomega' !*)
   structure Whnf : WHNF
   (*! sharing Whnf.IntSyn = IntSyn' !*)
       )
     : FILL =
struct
  (*! structure IntSyn = IntSyn' !*)
  (*! structure Tomega = Tomega' !*)
  structure State = State'

  exception Error of string

  type operator = (Tomega.Dec IntSyn.Ctx * Tomega.For) * Tomega.Worlds * (unit -> int * Tomega'.Prg)

  local
    structure S = State
    structure T = Tomega
    structure I = IntSyn
    structure N = Normalize

    exception Success of int

    (* Checking for constraints: Used to be in abstract, now must be done explicitly! --cs*)

    (* createEVars (G, F) = (Xs', P')
      
       Invariant:
       If   |- G ctx
       and  G |- F = [[x1:A1]] .. [[xn::An]] formula
       then Xs' = (X1', .., Xn') a list of EVars
       and  G |- Xi' : A1 [X1'/x1..X(i-1)'/x(i-1)]          for all i <= n
       and  G; D |- P' = <X1', <.... <Xn', <>> ..> in F     for some D
    *)
    fun createEVarsN (G, T.Ex (I.Dec (_, V), F)) = 
	let 
	  val X = I.newEVar (G, V)
	  val X' = Whnf.lowerEVar X
	  val (Xs, P, F') = createEVars (G, (F, T.Dot (T.Exp X, T.id)))
	in
	  (X' :: Xs, T.PairExp (X, P), F')
	end
      | createEVarsN (G, F) = (nil, T.Unit, F)
    and createEVars (G, (F, t)) = createEVarsN (G, N.normalizeFor (F, t))
       

(*    fun checkConstraints nil = raise Success
      | checkConstraints (X :: L) = 
        if Abstract.closedExp (I.Null, (Whnf.normalize (X, I.id), I.id)) then checkConstraints L
	else ()
*)

    (* expand' S = op'

       Invariant:
       If   |- S state
       then op' is an operator which performs the filling operation
    *)
    fun expand (S as S.State ((Psi, F), W)) = 
	let 
	  val G = T.coerceCtx Psi
	  val (Xs, P, F') = createEVars (G, (F, T.id))
(*	  val _ = if (!Global.doubleCheck) then TypeCheck.typeCheckCtx (G) else () *)
(*	  val (G, w, s) = T.strengthenCtx Psi
	  val (Xs, P, F') = createEVars (G, (F, s))
*)	in
	  ((Psi, F'), W, fn () => ((Search.searchEx (!MTPGlobal.maxFill, Xs, fn max => (if (!Global.doubleCheck) then 
						       map (fn (X as I.EVar (_, G', V, _)) => 
							    TypeCheck.typeCheck (G', (X, V))) Xs
						     else []; raise Success max));
		     raise Error "Filling unsuccessful")
	            handle Success max => (MTPData.maxFill := Int.max (!MTPData.maxFill, max);
					   (max, P))))
	end
    

    (* apply op = B' 

       Invariant:
       If op is a filling operator
       then B' holds iff the filling operation was successful
    *)
    fun apply ((Psi, F), W, f) = (f ();  S.State ((Psi, F), W)) 

    (* menu op = s'
       
       Invariant: 
       If op is a filling operator
       then s' is a string describing the operation in plain text
    *)
    fun menu _ =  "Fill" 
      
  in
    val expand = expand
    val apply = apply
    val menu = menu
  end (* local *)
end; (* functor Filling *)
