(* Internal Syntax *)
(* Author: Frank Pfenning, Carsten Schuermann *)
(* Modified: Roberto Virga *)

functor IntSyn (structure Global : GLOBAL) :> INTSYN =
struct

  type cid = int			(* Constant identifier        *)
  type name = string			(* Variable name              *)
  type csid = int                       (* CS module identifier       *)

  (* Contexts *)
  datatype 'a Ctx =			(* Contexts                   *)
    Null				(* G ::= .                    *)
  | Decl of 'a Ctx * 'a			(*     | G, D                 *)

  (* ctxPop (G) => G'
     Invariant: G = G',D
  *)
  fun ctxPop (Decl (G, D)) = G

  (* ctxLookup (G, k) = D, kth declaration in G from right to left
     Invariant: 1 <= k <= |G|, where |G| is length of G
  *)
  fun ctxLookup (Decl (G', D), 1) = D
    | ctxLookup (Decl (G', _), k') = ctxLookup (G', k'-1)
    (* ctxLookup (Null, k')  should not occur by invariant *)

  (* ctxLength G = |G|, the number of declarations in G *)
  fun ctxLength G =
      let 
	fun ctxLength' (Null, n) = n
	  | ctxLength' (Decl(G, _), n)= ctxLength' (G, n+1)
      in
	ctxLength' (G, 0)
      end
    
  datatype Depend =                     (* Dependency information     *)
    No                                  (* P ::= No                   *)
  | Maybe                               (*     | Maybe                *)
  | Meta				(*     | Meta                 *)

  (* Expressions *)

  datatype Uni =			(* Universes:                 *)
    Kind				(* L ::= Kind                 *)
  | Type				(*     | Type                 *)

  datatype Exp =			(* Expressions:               *)
    Uni   of Uni			(* U ::= L                    *)
  | Pi    of (Dec * Depend) * Exp       (*     | bPi (D, P). V         *)
  | Root  of Head * Spine		(*     | C @ S                *)
  | Redex of Exp * Spine		(*     | U @ S                *)
  | Lam   of Dec * Exp			(*     | lam D. U             *)
  | EVar  of Exp option ref * Dec Ctx * Exp * (Cnstr ref) list ref
                                        (*     | X<I> : G|-V, Cnstr   *)
  | EClo  of Exp * Sub			(*     | U[s]                 *)
  | FgnExp of csid *                    (*     | (foreign expression) *)
      {
        toInternal : unit -> Exp,       (* convert to internal syntax *)
        map : (Exp -> Exp) -> Exp,      (* apply to subterms          *)
        equalTo : Exp -> bool,
                                        (* test for equality          *)
        unifyWith : Dec Ctx * Exp -> FgnUnify
                                        (* unify with another term    *)
      }
    
  and Head =				(* Heads:                     *)
    BVar  of int			(* H ::= k                    *)
  | Const of cid			(*     | c                    *)
  | Skonst of cid			(*     | c#                   *)
  | Def   of cid			(*     | d                    *)
  | NSDef of cid			(*     | d (non strict)       *)
  | FVar  of name * Exp * Sub		(*     | F[s]                 *)
  | FgnConst of csid * ConDec           (*     | (foreign constant)   *)
    
  and Spine =				(* Spines:                    *)
    Nil					(* S ::= Nil                  *)
  | App   of Exp * Spine		(*     | U ; S                *)
  | SClo  of Spine * Sub		(*     | S[s]                 *)

  and Sub =				(* Explicit substitutions:    *)
    Shift of int			(* s ::= ^n                   *)
  | Dot   of Front * Sub		(*     | Ft.s                 *)

  and Front =				(* Fronts:                    *)
    Idx of int				(* Ft ::= k                   *)
  | Exp of Exp				(*     | U                    *)
  | Undef				(*     | _                    *)

  and Dec =				(* Declarations:              *)
    Dec of name option * Exp		(* D ::= x:V                  *)

  (* Constraints *)

  and Cnstr =				(* Constraint:                *)
    Solved                      	(* Cnstr ::= solved           *)
  | Eqn      of Dec Ctx * Exp * Exp     (*         | G|-(U1 == U2)    *)
  | FgnCnstr of csid *                  (*         | (foreign)        *)
      {
        toInternal : unit -> (Dec Ctx * Exp) list,
                                        (* convert to internal syntax *)
        awake : unit -> bool,           (* awake                      *)
        simplify : unit -> bool         (* simplify                   *)
      }

  and Status =                          (* Status of a constant:      *)
    Normal                              (*   inert                    *)
  | Constraint of csid * (Dec Ctx * Spine * int -> Exp option)
                                        (*   acts as constraint       *)
  | Foreign of csid * (Spine -> Exp)    (*   is converted to foreign  *)

  and FgnUnify =                        (* Result of foreign unify    *)
    Succeed of FgnUnifyResidual list
    (* succeed with a list of residual operations *)
  | Fail

  and FgnUnifyResidual =                (* Residual of foreign unify  *)
    Assign of Dec Ctx * Exp * Exp * Sub
    (* perform the assignment G |- X = U [ss] *)
  | Delay of Exp * Cnstr ref
    (* delay cnstr, associating it with all the rigid EVars in U  *)

  (* Global signature *)

  and ConDec =			        (* Constant declaration       *)
    ConDec of string * int * Status    	(* a : K : kind  or           *)
              * Exp * Uni	        (* c : A : type               *)
  | ConDef of string * int		(* a = A : K : kind  or       *)
              * Exp * Exp * Uni		(* d = M : A : type           *)
  | AbbrevDef of string * int		(* a = A : K : kind  or       *)
              * Exp * Exp * Uni		(* d = M : A : type           *)
  | SkoDec of string * int		(* sa: K : kind  or           *)
              * Exp * Uni	        (* sc: A : type               *)

  (* Type abbreviations *)
  type dctx = Dec Ctx			(* G = . | G,D                *)
  type eclo = Exp * Sub   		(* Us = U[s]                  *)
  type cnstr = Cnstr ref

  exception Error of string             (* raised if out of space     *)

  fun conDecName (ConDec (name, _, _, _, _)) = name
    | conDecName (ConDef (name, _, _, _, _)) = name
    | conDecName (AbbrevDef (name, _, _, _, _)) = name
    | conDecName (SkoDec (name, _, _, _)) = name

  fun conDecImp (ConDec (_, i, _, _, _)) = i
    | conDecImp (ConDef (_, i, _, _, _)) = i
    | conDecImp (AbbrevDef (_, i, _, _, _)) = i
    | conDecImp (SkoDec (_, i, _, _)) = i

  fun conDecStatus (ConDec (_, _, status, _, _)) = status
    | conDecStatus _ = Normal

  fun conDecType (ConDec (_, _, _, V, _)) = V
    | conDecType (ConDef (_, _, _, V, _)) = V
    | conDecType (AbbrevDef (_, _, _, V, _)) = V
    | conDecType (SkoDec (_, _, V, _)) = V

  local
    val maxCid = Global.maxCid
    val sgnArray = Array.array (maxCid+1, ConDec("", 0, Normal, Uni (Kind), Kind))
      : ConDec Array.array
    val nextCid  = ref(0)

  in
    (* Invariants *)
    (* Constant declarations are all well-typed *)
    (* Constant declarations are stored in beta-normal form *)
    (* All definitions are strict in all their arguments *)
    (* If Const(cid) is valid, then sgnArray(cid) = ConDec _ *)
    (* If Def(cid) is valid, then sgnArray(cid) = ConDef _ *)

    fun sgnReset () = (nextCid := 0)
    fun sgnSize () = (!nextCid)

    fun sgnAdd (conDec) = 
        let
	  val cid = !nextCid
	in
	  if cid > maxCid
	    then raise Error ("Global signature size " ^ Int.toString (maxCid+1) ^ " exceeded")
	  else (Array.update (sgnArray, cid, conDec) ;
		nextCid := cid + 1;
		cid)
	end

    (* 0 <= cid < !nextCid *)
    fun sgnLookup (cid) = Array.sub (sgnArray, cid)

    fun sgnApp (f) =
        let
	  fun sgnApp' (cid) = 
	      if cid = !nextCid then () else (f cid; sgnApp' (cid+1)) 
	in
	  sgnApp' (0)
	end

  end

  fun constDef (d) =
      (case sgnLookup (d)
	 of ConDef(_, _, U,_, _) => U
	  | AbbrevDef (_, _, U,_, _) => U)

  fun constType (c) = conDecType (sgnLookup (c))

  fun constImp (c) =
      (case sgnLookup(c)
	 of ConDec (_,i,_,_,_) => i
          | ConDef (_,i,_,_,_) => i
          | AbbrevDef (_,i,_,_,_) => i
	  | SkoDec (_,i,_,_) => i)

  fun constStatus (c) =
      (case sgnLookup (c)
	 of ConDec (_, _, status, _, _) => status
          | _ => Normal)

  fun constUni (c) =
      (case sgnLookup(c)
	 of ConDec (_,_,_,_,L) => L
          | ConDef (_,_,_,_,L) => L
          | AbbrevDef (_,_,_,_,L) => L
	  | SkoDec (_,_,_,L) => L)

  (* Declaration Contexts *)

  (* ctxDec (G, k) = x:V
     Invariant: 
     If      |G| >= k, where |G| is size of G,
     then    G |- k : V  and  G |- V : L
  *)
  fun ctxDec (G, k) =
      let (* ctxDec' (G'', k') = x:V
	     where G |- ^(k-k') : G'', 1 <= k' <= k
           *)
	fun ctxDec' (Decl (G', Dec (x, V')), 1) = Dec (x, EClo (V', Shift (k)))
	  | ctxDec' (Decl (G', _), k') = ctxDec' (G', k'-1)
	 (* ctxDec' (Null, k')  should not occur by invariant *)
      in
	ctxDec' (G, k)
      end

  (* Explicit Substitutions *)

  (* id = ^0 
  
     Invariant:
     G |- id : G        id is patsub
  *)
  val id = Shift(0)

  (* shift = ^1
  
     Invariant:
     G, V |- ^ : G       ^ is patsub
  *)
  val shift = Shift(1)

  (* invShift = ^-1 = _.^0
     Invariant:
     G |- ^-1 : G, V     ^-1 is patsub
  *)
  val invShift = Dot(Undef, id)

  (* bvarSub (n, s) = Ft'
   
      Invariant: 
     If    G |- s : G'    G' |- n : V
     then  Ft' = Ftn         if  s = Ft1 .. Ftn .. ^k
       or  Ft' = ^(n+k)     if  s = Ft1 .. Ftm ^k   and m<n
     and   G |- Ft' : V [s]
  *)
  fun bvarSub (1, Dot(Ft, s)) = Ft
    | bvarSub (n, Dot(Ft, s)) = bvarSub (n-1, s)
    | bvarSub (n, Shift(k))  = Idx (n+k)

  (* frontSub (Ft, s) = Ft'

     Invariant:
     If   G |- s : G'     G' |- Ft : V
     then Ft' = Ft [s]
     and  G |- Ft' : V [s]

     NOTE: EClo (U, s) might be undefined, so if this is ever
     computed eagerly, we must introduce an "Undefined" exception,
     raise it in whnf and handle it here so Exp (EClo (U, s)) => Undef
  *)
  and frontSub (Idx (n), s) = bvarSub (n, s)
    | frontSub (Exp (U), s) = Exp (EClo (U, s))
    | frontSub (Undef, s) = Undef

  (* decSub (x:V, s) = D'

     Invariant:
     If   G  |- s : G'    G' |- V : L
     then D' = x:V[s]
     and  G  |- V[s] : L
  *)
  (* First line is an optimization suggested by cs *)
  (* D[id] = D *)
  (* Sat Feb 14 18:37:44 1998 -fp *)
  (* seems to have no statistically significant effect *)
  (* undo for now Sat Feb 14 20:22:29 1998 -fp *)
  (*
  fun decSub (D, Shift(0)) = D
    | decSub (Dec (x, V), s) = Dec (x, EClo (V, s))
  *)
  fun decSub (Dec (x, V), s) = Dec (x, EClo (V, s))

  (* comp (s1, s2) = s'

     Invariant:
     If   G'  |- s1 : G 
     and  G'' |- s2 : G'
     then s'  = s1 o s2
     and  G'' |- s1 o s2 : G

     If  s1, s2 patsub
     then s' patsub
   *)
  fun comp (Shift (0), s) = s
    (* next line is an optimization *)
    (* roughly 15% on standard suite for Twelf 1.1 *)
    (* Sat Feb 14 10:15:16 1998 -fp *)
    | comp (s, Shift (0)) = s
    | comp (Shift (n), Dot (Ft, s)) = comp (Shift (n-1), s)
    | comp (Shift (n), Shift (m)) = Shift (n+m)
    | comp (Dot (Ft, s), s') = Dot (frontSub (Ft, s'), comp (s, s'))

  (* dot1 (s) = s'

     Invariant:
     If   G |- s : G'
     then s' = 1. (s o ^)
     and  for all V s.t.  G' |- V : L
          G, V[s] |- s' : G', V 

     If s patsub then s' patsub
  *)
  (* first line is an optimization *)
  (* roughly 15% on standard suite for Twelf 1.1 *)
  (* Sat Feb 14 10:16:16 1998 -fp *)
  fun dot1 (s as Shift (0)) = s
    | dot1 s = Dot (Idx(1), comp(s, shift))

  (* invDot1 (s) = s'
     invDot1 (1. s' o ^) = s'

     Invariant:
     s = 1 . s' o ^
     If G' |- s' : G
     (so G',V[s] |- s : G,V)
  *)
  fun invDot1 (s) = comp (comp(shift, s), invShift)

  (* EVar related functions *)

  (* newEVar (G, V) = newEVarCnstr (G, V, nil) *)
  fun newEVar (G, V) = EVar(ref NONE, G, V, ref nil)

  (* newTypeVar (G) = X, X new
     where G |- X : type
  *)
  fun newTypeVar (G) = EVar(ref NONE, G, Uni(Type), ref nil)

  (* Type related functions *)

  (* targetFamOpt (V) = SOME(cid) or NONE
     where cid is the type family of the atomic target type of V,
     NONE if V is a kind or object or have variable type.
  *)
  fun targetFamOpt (Root (Const(cid), _)) = SOME(cid)
    | targetFamOpt (Pi(_, V)) = targetFamOpt V
    | targetFamOpt (Root (Def(cid), _)) = SOME(cid)
    | targetFamOpt (Redex (V, S)) = targetFamOpt V
    | targetFamOpt (Lam (_, V)) = targetFamOpt V
    | targetFamOpt (EVar (ref (SOME(V)),_,_,_)) = targetFamOpt V
    | targetFamOpt (EClo (V, s)) = targetFamOpt V
    | targetFamOpt _ = NONE
      (* Root(Bvar _, _), Root(FVar _, _), Root(FgnConst _, _),
         EVar(ref NONE,..), Uni, FgnExp _
      *)
      (* Root(Skonst _, _) can't occur *)
  (* targetFam (A) = a
     as in targetFamOpt, except V must be a valid type
  *)
  fun targetFam (A) = valOf (targetFamOpt A)

end;  (* functor IntSyn *)
