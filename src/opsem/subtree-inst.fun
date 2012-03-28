(* Linear Substitution Tree indexing *)
(* Linearity: Any variables occurring inside the substitution tree are linear *)
(* Any term we insert into the substitution tree is in normalform ! *)
(* Instance Checking *)
(* Author: Brigitte Pientka *)

functor MemoTableInst ((*! structure IntSyn' : INTSYN !*)
                       (*! structure CompSyn' : COMPSYN !*)
                       (*! sharing CompSyn'.IntSyn = IntSyn' !*)
                       structure Conv: CONV
                       (*! sharing Conv.IntSyn = IntSyn' !*)
                       structure Whnf : WHNF
                       structure Match : MATCH
                       (*! sharing Whnf.IntSyn = IntSyn' !*)
                       (*! structure RBSet : RBSET !*)
                       structure Assign : ASSIGN
                       (*! structure TableParam : TABLEPARAM !*)
                       (*! sharing TableParam.IntSyn = IntSyn' !*)
                       (*! sharing TableParam.CompSyn = CompSyn' !*)
                       (*! sharing TableParam.RBSet = RBSet !*)
                       structure AbstractTabled : ABSTRACTTABLED
                       (*! sharing AbstractTabled.IntSyn = IntSyn' !*)
                       structure Print : PRINT
                       (*! sharing Print.IntSyn = IntSyn'!*))
  : MEMOTABLE =
  struct
  (*! structure IntSyn = IntSyn' !*)
  (*! structure CompSyn = CompSyn' !*)
  structure AbstractTabled = AbstractTabled
  (*! structure TableParam = TableParam !*)

  (* ---------------------------------------------------------------------- *)

  (* Linear substitution tree for linear terms *)

  (* normalSubsts: key = int = nvar  (key, (depth, U))

   example:  \x. f( i1, a)   then i1 = (1, X) = X[x/x]

   *)
  (* property: linear *)

  type normalSubsts  = (int (* local depth *) * IntSyn.Exp) RBSet.ordSet

  type exSubsts  = IntSyn.Front RBSet.ordSet

  val nid : unit -> normalSubsts = RBSet.new
  val asid : unit -> exSubsts = RBSet.new

  val aid = TableParam.aid

  fun isId s = RBSet.isEmpty s

  (* ---------------------------------------------------------------------- *)
  (* Context for existential variable *)

  type ctx = ((int * IntSyn.Dec) list) ref

  (* functions for handling context for existential variables *)

  fun emptyCtx () :  ctx = ref []

  fun copy L : ctx = ref (!L)

  (* destructively updates L *)
  fun delete (x, L : ctx ) =
    let
      fun del (x, [], L) = NONE
        | del (x, ((H as (y,E))::L), L') =
            if x = y then SOME((y,E), (rev L')@ L) else del(x, L, H::L')
    in
      case del (x, (!L), [])
        of NONE => NONE
      | SOME((y,E), L') => (L := L'; SOME((y,E)))
    end

  fun member (x, L:ctx) =
    let
      fun memb (x, []) = NONE
        | memb (x, (H as (y,E as IntSyn.Dec(n,U))::L)) =
            if x = y then SOME(y,E) else memb(x, L)
        | memb (x, (H as (y,E as IntSyn.ADec(n,d))::L)) =
            (if x = y then SOME((y,E)) else memb(x, L))
    in
      memb (x, (!L))
    end

  fun insertList (E, L) = (L := (E::(!L)))

 (* ---------------------------------------------------------------------- *)

  (* Substitution Tree *)
  (* It is only possible to distribute the evar-ctx because
     all evars occur exactly once, i.e. they are linear.
     This allows us to maintain invariant, that every occurrence of an evar is
     defined in its evar-ctx
  *)
  datatype Tree =
      Leaf of (ctx *  normalSubsts) *
      (((int (* #EVar *) * int (* #G *)) *
        ctx  (* D *) * IntSyn.dctx (* G *) *
        TableParam.ResEqn * TableParam.answer *
        int * TableParam.Status) list) ref
    | Node of (ctx *  normalSubsts) * (Tree ref) list

  fun makeTree () = ref (Node ((emptyCtx(), nid ()), []))

  fun noChildren C = (C=[])

  datatype Retrieval =
      Variant of (int * IntSyn.Exp)
    | NotCompatible

  datatype CompSub =
      SplitSub of ((ctx * normalSubsts (* sigma *)) *
                   (ctx * normalSubsts (* rho1 *)) *
                   (ctx * normalSubsts (* rho2 *)))
    | InstanceSub of (exSubsts * (ctx * normalSubsts (* rho2 *)))
    | VariantSub of  (ctx * normalSubsts (* rho2 *))
    | NoCompatibleSub

  (* Index array

   All type families have their own substitution tree and all substitution trees
   are stored in an array [a1,...,an]   where ai is a substitution tree for type family ai
   *)

  val indexArray = Array.tabulate (Global.maxCid, (fn i => (ref 0, makeTree ())));

  exception Error of string

  local

    structure I   = IntSyn
    structure C   = CompSyn
    structure S   = RBSet
    structure A   = AbstractTabled
    structure T   = TableParam


    exception Assignment of string

    exception Instance of string

    exception Generalization of string

    exception DifferentSpines

    fun emptyAnswer () = T.emptyAnsw ()

    val answList : (TableParam.answer list) ref = ref []

    val added = ref false;

    type nvar = int      (* index for normal variables *)
    type bvar = int      (* index for bound variables *)
    type bdepth = int    (* depth of locally bound variables *)


  (* ------------------------------------------------------ *)
  (* for debugging only *)
    fun expToS (G,U) = (Print.expToString (G, U) handle _ => " <_ >")

    fun printSub (G, I.Shift n) = print ("I.Shift " ^ Int.toString n ^ "\n")
      | printSub (G, I.Dot(I.Idx n, s)) =
        (print ("Idx " ^ Int.toString n ^ " . "); printSub (G, s))
      | printSub (G, I.Dot (I.Exp(X as I.EVar (ref(SOME(U)),_ ,  _, _)), s)) =
        (print ("Exp ( EVar " ^ expToS(G, X) ^ ").")  ; printSub (G, s))
      | printSub (G, I.Dot (I.Exp(X as I.EVar (_, _, _, _)), s)) =
        (print ("Exp ( EVar  " ^ expToS(G, X) ^ ").")  ; printSub (G, s))
      | printSub (G, I.Dot (I.Exp(I.AVar (_)), s)) =
        (print ("Exp (AVar _ ). "); printSub (G, s))
      | printSub (G, I.Dot (I.Exp(I.EClo (I.AVar (ref (SOME(U))), s')), s)) =
        (print ("Exp (AVar " ^ expToS (G, I.EClo(U,s'))  ^ ").") ; printSub (G, s))
      | printSub (G, I.Dot (I.Exp(X as I.EClo (I.EVar (ref(SOME(U)), _, _, _),s')), s)) =
        (print ("Exp (EVarClo " ^ expToS (G, I.EClo(U,s')) ^ ") "); printSub (G, s))
      | printSub (G, I.Dot (I.Exp(X as I.EClo (U, s')), s)) =
        (print ("Exp (EClo " ^ expToS (G, Whnf.normalize(U,s')) ^ ") "); printSub (G, s))
      | printSub (G, I.Dot (I.Exp(E), s)) =
        (print ("Exp ( " ^ expToS (G,E) ^ " ). "); printSub (G, s))
      | printSub (G, I.Dot (I.Undef, s)) = (print ("Undef . "); printSub (G, s))

  (* auxiliary function  -- needed to dereference AVars -- expensive?*)
    fun normalizeSub (I.Shift n) = I.Shift n
      | normalizeSub (I.Dot(I.Exp(I.EClo(I.AVar (ref (SOME(U))), s')), s)) =
      I.Dot(I.Exp(Whnf.normalize (U, s')), normalizeSub s)
    | normalizeSub (I.Dot (I.Exp(I.EClo(I.EVar(ref(SOME(U)), _, _, _), s')), s)) =
      I.Dot(I.Exp(Whnf.normalize (U, s')), normalizeSub s)

    | normalizeSub (I.Dot (I.Exp(U), s)) =
      I.Dot(I.Exp(Whnf.normalize (U, I.id)), normalizeSub s)
    | normalizeSub (I.Dot(I.Idx n, s)) =
      I.Dot (I.Idx n, normalizeSub s)

  (* ------------------------------------------------------ *)
  (* Auxiliary functions *)
  (* etaSpine (S, n) = true

   iff S is a spine n;n-1;..;1;nil

   no permutations or eta-expansion of arguments are allowed
   *)

  fun etaSpine (I.Nil, n) = (n=0)
    | etaSpine (I.App(I.Root(I.BVar k, I.Nil), S), n) =
       (k = n andalso etaSpine(S, n-1))
    | etaSpine (I.App(A, S), n) = false


    fun cidFromHead (I.Const c) = c
      | cidFromHead (I.Def c) = c

    fun dotn (0, s) = s
      | dotn (i, s) = dotn (i-1, I.dot1 s)

    fun raiseType (I.Null, V) = V
      | raiseType (I.Decl (G, D), V) = raiseType (G, I.Lam (D, V))

    (* compose (Decl(G',D1'), G) =   G. .... D3'. D2'.D1'
       where G' = Dn'....D3'.D2'.D1' *)
    fun compose(IntSyn.Null, G) = G
      | compose(IntSyn.Decl(G', D), G) = IntSyn.Decl(compose(G', G), D)

    fun shift (IntSyn.Null, s) = s
      | shift (IntSyn.Decl(G, D), s) = I.dot1 (shift(G, s))

    (* ---------------------------------------------------------------------- *)
    (* ctxToEVarSub D = s

     if D is a context for existential variables,
        s.t. u_1:: A_1,.... u_n:: A_n = D
     then . |- s : D where s = X_n....X_1.id

    *)

    fun ctxToEVarSub (I.Null, s) = s
      | ctxToEVarSub (I.Decl(G,I.Dec(_,A)), s) =
      let
        val X = I.newEVar (I.Null, A)
      in
        I.Dot(I.Exp(X), ctxToEVarSub (G, s))
      end

 (* ---------------------------------------------------------------------- *)
 (* Matching for linear terms based on assignment *)

    (* lowerEVar' (G, V[s]) = (X', U), see lowerEVar *)
    fun lowerEVar' (X, G, (I.Pi ((D',_), V'), s')) =
        let
          val D'' = I.decSub (D', s')
          val (X', U) = lowerEVar' (X, I.Decl (G, D''), Whnf.whnf (V', I.dot1 s'))
        in
          (X', I.Lam (D'', U))
        end
      | lowerEVar' (X, G, Vs') =
        let
          val X' = X
        in
          (X', X')
        end
    (* lowerEVar1 (X, V[s]), V[s] in whnf, see lowerEVar *)
    and (* lowerEVar1 (X, I.EVar (r, G, _, _), (V as I.Pi _, s)) = *)
      lowerEVar1 (X, I.EVar (r, G, _, _), (V as I.Pi _, s)) =
        let
          val (X', U) = lowerEVar' (X, G, (V,s))
        in
          I.EVar(ref (SOME(U)), I.Null, V, ref nil)
        end
      | lowerEVar1 (_, X, _) = X

    (* lowerEVar (X) = X'

       Invariant:
       If   G |- X : {{G'}} P
            X not subject to any constraints
       then G, G' |- X' : P

       Effect: X is instantiated to [[G']] X' if G' is empty
               otherwise X = X' and no effect occurs.
    *)
    and
      lowerEVar (E, X as I.EVar (r, G, V, ref nil)) =
        lowerEVar1 (E, X, Whnf.whnf (V, I.id))
      | lowerEVar (E, I.EVar _) =
        (* It is not clear if this case can happen *)
        (* pre-Twelf 1.2 code walk, Fri May  8 11:05:08 1998 *)
        raise Error "abstraction : LowerEVars: Typing ambiguous -- constraint of functional type cannot be simplified"

    fun ctxToAVarSub (G', I.Null, s) = s
      | ctxToAVarSub (G', I.Decl(D,I.Dec(_,A)), s) =
      let
        val E as I.EVar (r, _, _, cnstr) = I.newEVar (I.Null, A)
      in
        I.Dot(I.Exp(E), ctxToAVarSub (G', D, s))
      end

      | ctxToAVarSub (G', I.Decl(D,I.ADec(_,d)), s) =
      let
        val X = I.newAVar ()
      in
        I.Dot(I.Exp(I.EClo(X, I.Shift(~d))), ctxToAVarSub (G', D, s))
      end


   (* assign(d, Dec(n, V), X as I.Root(BVar k, S), U, asub) = ()
      Invariant:
      if D ; G |- U : V
         D ; G |- X : V
      then
         add (X, U) to asub
         where  assub is a set of substitutions for existential variables)
    *)

  (* [asub]E1  = U *)
  fun assign ((* total as (t, passed)*)d, Dec1 as I.Dec(n, V), E1 as I.Root(I.BVar k, S1), U, asub) =
     (* it is an evar -- (k-d, EVar (SOME(U), V)) *)
     let
       val E as I.EVar(r, _, _ , cnstr) = I.newEVar (I.Null, V)
       val X = lowerEVar1 (E, I.EVar(r, I.Null, V, cnstr), Whnf.whnf(V, I.id))
       val _ = (r := SOME(U))
     in
        S.insert asub (k - d, I.Exp(X))
     end

     | assign ((* total as (t, passed)*) d, Dec1 as I.ADec(n, d'), E1 as I.Root(I.BVar k, S1), U, asub) =
       (* it is an Avar and d = d' (k-d, AVar(SOME(U)) *)
       let
         val A as I.AVar(r) = I.newAVar ()
         val _ = (r := SOME(U))
         val Us = Whnf.whnf (U, I.Shift(~d'))
       in
         S.insert asub (k - d, I.Exp(I.EClo(A, I.Shift(~d'))))
       end

  (* terms are in normal form *)
  (* exception Assignment of string *)
  (* assignExp (fasub, (l, ctxTotal as (r, passed), d) (D1, U1), (D2, U2))) = fasub'

     invariant:
      G, G0 |- U1 : V1   U1 in nf
      G, G0 |- U2 : V2   U2 in nf
     and U1, U2 are linear higher-order patterns
      D1 contains all existential variables of U1
      D2 contains all existential variables of U2

      ctxTotal = (r + passed) = |G|
            where G refers to the globally bound variables
      d = |G0| where G' refers to the locally bound variables

      then fasub' is a success continuation
        which builds up a substitution s
              with domain D1 and  U1[s] = U2

      NOTE: We only allow assignment for fully applied evars --
      and we will fail otherwise. This essentially only allows first-order assignment.
      To generalize this, we would need to linearize the ctx and have more complex
      abstraction algorithm.

   *)
   fun assignExp (fasub, (ctxTotal as (r,passed), d), (D1, U1 as I.Root (H1, S1)), (D2, U2 as I.Root (H2, S2))) =
     (case (H1, H2) of
        (I.Const(c1), I.Const(c2)) =>
          if (c1 = c2)
            then assignSpine (fasub, (ctxTotal, d), (D1, S1), (D2, S2))
          else raise Assignment "Constant clash"

      | (I.Def(c1), I.Def(c2)) =>
         (* we do not expand definitions here -- this is very conservative! *)
          if (c1 = c2)
            then assignSpine (fasub, (ctxTotal, d), (D1, S1), (D2, S2))
          else
            let
              val U1' = Whnf.normalize(Whnf.expandDef (U1, I.id))
              val U2' = Whnf.normalize(Whnf.expandDef (U2, I.id))
            in
              assignExp (fasub, (ctxTotal, d), (D1, U1'), (D2, U2'))
            end

      | (I.Def(c1), _) =>
         (* we do not expand definitions here -- this is very conservative! *)
            let
              val U1' = Whnf.normalize(Whnf.expandDef (U1, I.id))
            in
              assignExp (fasub, (ctxTotal, d), (D1, U1'), (D2, U2))
            end
      | (_, I.Def(c2)) =>
         (* we do not expand definitions here -- this is very conservative! *)
            let
              val U2' = Whnf.normalize(Whnf.expandDef (U2, I.id))
            in
              assignExp (fasub, (ctxTotal, d), (D1, U1), (D2, U2'))
            end
      | (I.BVar(k1), I.BVar k2) =>
        (if k1 <= (r + d) (* if (k1 - d) >= l *)
           then
             (* k1 is a globally bound variable *)
             if k2 <= (r + d) then
               (* k2 is globally bound *)
               (if k2 = k1 then fasub else raise Assignment "BVar clash")
             else raise Assignment "BVar - EVar clash"
         else
           (* k1 is an existial variable *)
           (case member (k1 - d + passed, D1)
              of NONE =>  raise Assignment "EVar nonexistent"
            | SOME(x, Dec) =>
                if k2 <= (r + d) then
                  (* k2 is globally bound *)
                  raise Assignment "EVar - BVar clash"
                else
                  (if k2 = k1 then (* denote the same evar *)
                     (fn asub => (fasub asub; assign ((* ctxTotal,*) d, Dec, U1, U2, asub)))
                else raise Assignment "EVars are different -- outside of the allowed fragment" )
              ))

      | (I.Skonst(c1), I.Skonst(c2)) =>
           if (c1 = c2) then assignSpine (fasub, (ctxTotal, d), (D1, S1), (D2, S2))
           else raise Assignment "Skolem constant clash"
      (* can this happen ? -- definitions should be already expanded ?*)
      | _ => (raise Assignment ("Head mismatch ")))

     | assignExp (fasub, (ctxTotal, d), (D1, I.Lam (Dec1, U1)), (D2, I.Lam (Dec2, U2))) =
        (* type labels are ignored *)
        assignExp (fasub, (ctxTotal, d + 1),  (D1, U1), (D2, U2))


     | assignExp (fasub, (ctxTotal, d),
                  (D1, I.Pi ((Dec1 as I.Dec (_, V1), _), U1)),
                  (D2, I.Pi ((Dec2 as I.Dec(_, V2), _), U2))) =
        let
          (* is this necessary? Tue Aug  3 11:56:17 2004 -bp *)
          val fasub' = assignExp (fasub, (ctxTotal, d), (D1, V1), (D2, V2))
        in
          assignExp (fasub', (ctxTotal, d + 1), (D1, U1), (D2, U2))
        end
     (* the closure cases should be unnecessary, if everything is in nf *)
     | assignExp (fasub, (ctxTotal, d), (D1, I.EClo(U, s' as I.Shift(0))), (D2, U2)) =
        assignExp (fasub, (ctxTotal, d), (D1, U), (D2, U2))
     | assignExp (fasub, (ctxTotal, d), (D1, U1), (D2, I.EClo(U, s as I.Shift(0)))) =
        assignExp (fasub, (ctxTotal, d), (D1, U1), (D2, U))


   and assignSpine (fasub, (ctxTotal, d), (D1, I.Nil), (D2, I.Nil)) = fasub
     | assignSpine (fasub, (ctxTotal, d), (D1, I.App (U1, S1)), (D2, I.App (U2, S2))) =
     let
       val fasub' = assignExp (fasub, (ctxTotal, d), (D1, U1), (D2, U2))
     in
       assignSpine (fasub', (ctxTotal, d), (D1, S1), (D2, S2))
     end

   (* assignCtx (fasub, ctxTotal as (r, passed), (D1, G), (D2, G')) = fasub'
      invariant
         |G| = |G'| = r
         |G0| = |G0'| = passed
         |G, G0| = |G', G0'| = (r + passed) = ctxTotal

         D1 contains all existential variables occuring in (G, G0)
         D2 contains all existential variables occuring in (G', G0')

         fasub' is a success continuation
            which builds up a substitution s
              with domain D1 and  (G, G0)[s] = (G, G0)

         NOTE : [fasub]G = G' Sun Nov 28 18:55:21 2004 -bp
    *)
   fun assignCtx (fasub, ctxTotal, (D1,  I.Null), (D2, I.Null)) = fasub
     | assignCtx (fasub, (ctxTotal as (r, passed)),
                  (D1, I.Decl(G1, I.Dec(_, V1))),
                  (D2, I.Decl(G2, I.Dec(_, V2)))) =
     let
       val fasub' = assignExp (fasub, ((r - 1, passed + 1), 0), (D1, V1), (D2, V2))
     in
       assignCtx (fasub', ((r - 1, passed + 1)), (D1, G1), (D2, G2))
     end


   (* ------------------------------------------------------ *)

   (*  Variable b    : bound variable
    Variable n    : index variable
    linear term  U ::=  Root(c, S) | Lam (D, U) | Root(b, S)
    linear Spine S ::= p ; S | NIL
    indexed term t ::= Root(n, NIL) |  Root(c, S) | Lam (D, p) | Root(b, S)
    indexed spines S_i ::= t ; S_i | NIL
    Types   A
    Context G : context for bound variables (bvars)
    (type information is stored in the context)

       G ::= . | G, x : A
       Set of all index variables:  N

    linear terms are well-typed in G:     G |- p
    indexed terms are well-typed in (N ; G) |- t

    Let s is a substitution for index variables (nvar)
    and s1 o s2 o .... o sn = s, s.t.
    forall nvar in CODOM(sk).
     exists i . nvar in DOM(si) and i > k.

    IMAGE (s) = the index variables occurring in the CODOM(s)

    Let N1 ... Nn be the path from the root N1 to the leaf Nn,
    and si the substitution associated with node Ni.

    IMAGE(sn) = empty
    s1 o s2 o ... o sn = s and IMAGE(s) = empty
    i.e. index variables are only internally used and no
         index variable is left.

    A linear term U (and an indexed term t) can be decomposed into a term t' together with
    a sequenence of substitutions s1, s2, ..., sn such that s1 o s2 o .... o sn = s
    and the following holds:

    If    N  ; G |- t
    then  N' ; G |- t'
          N  ; G |- s : N' ; G
          N  ; G |- t'[s]     and t'[s] = t

   if we have a linear term then N will be empty, but the same holds.

   In addition:
   all expressions in the index are closed and linear and in normalform i.e.
   an expression is first linearized before it is inserted into the index

   *)


  (* ---------------------------------------------------------------*)

  (* nctr = |D| =  #index variables *)
   val nctr = ref 1

   fun newNVar () =
     (nctr := !nctr + 1;
      I.NVar(!nctr))

   fun equalDec (I.Dec(_, U), I.Dec(_, U')) = Conv.conv ((U, I.id), (U', I.id))
     | equalDec (I.ADec(_, d), I.ADec(_, d')) = (d = d')
     | equalDec (_, _) = false

    (* too restrictive if we require order of both eqn must be the same ?
     Sun Sep  8 20:37:48 2002 -bp *)
    (* s = s' = I.id *)
    fun equalCtx (I.Null, s, I.Null, s') = true
      | equalCtx (I.Decl(G, D as  I.Dec(_, A)), s, I.Decl(G', D' as  I.Dec(_, A')), s') =
          Conv.convDec((D, s), (D', s')) andalso (equalCtx (G, I.dot1 s, G', I.dot1 s'))
      | equalCtx (_, s, _, s') = false



    (* equalEqn (e, e') = (e = e') *)
    fun equalEqn (T.Trivial, T.Trivial) = true
      | equalEqn (T.Unify(G, X, N, eqn), (T.Unify(G', X', N', eqn'))) =
        equalCtx (G, I.id, G', I.id) andalso Conv.conv ((X, I.id), (X', I.id))
        andalso Conv.conv ((N, I.id), (N', I.id)) andalso equalEqn(eqn, eqn')
      | equalEqn (_, _) = false


    (* equalEqn' (d, (D, e), (D', e'), asub) = (e = e')

       destructively updates asub such that all the evars occurring in D'
       will be instantiated and  D |- asub : D'

       if D |- e and D' |- e'  and d = depth of context G'
          asub partially instantiates variables from D'
       then
         D |- asub : D'

    *)
    fun equalEqn' (d, (D, T.Trivial), (D', T.Trivial), asub) = true
      | equalEqn' (d, (D, T.Unify(G, X as I.Root(I.BVar k, S), N (* AVar *), eqn)),
                     (D', T.Unify(G', X', N' (* AVar *), eqn')), asub) =
      if (equalCtx (G, I.id, G', I.id) andalso
          Conv.conv ((X, I.id), (X', I.id)) andalso
          Conv.conv ((N, I.id), (N', I.id)))
        then
          (let
            (* X is the evar in the query, X' is the evar in the index,
             potentially X' is not yet instantiated and X' in D' but X' not in asub *)
             val d' = d + I.ctxLength(G')
          in
             (if (k - d') > 0 then
                (case member (k - d', D') of
                   NONE =>  ()
                 | SOME(x, Dec) => (* k refers to an evar *)
                     (case RBSet.lookup asub (k - d') of
                        NONE => ((* it is not instantiated yet *)
                                 delete (x, D');
                                 S.insert asub (k - d', I.Idx(k - d')))
                      | SOME (_ ) => ()))(* it is instantiated;
                                          since eqn were solvable, eqn' would be solvable too *)
              else
                (* k refers to a bound variable *)
                (print "Impossible -- Found BVar instead of EVar\n";
                 raise Error "Impossibe -- Found BVar instead of EVar "));
            equalEqn'(d,(D, eqn), (D',eqn'), asub)
          end)
      else
        false

      | equalEqn' (d, _, _, asub) = false


    (* equalSub (s, s') = (s=s') *)
    fun equalSub (I.Shift k, I.Shift k') = (k = k')
      | equalSub (I.Dot(F, S), I.Dot(F', S')) =
        equalFront (F, F') andalso equalSub (S, S')
      | equalSub (I.Dot(F,S), I.Shift k) = false
      | equalSub (I.Shift k, I.Dot(F,S)) = false

    (* equalFront (F, F') = (F=F') *)
    and equalFront (I.Idx n, I.Idx n') = (n = n')
      | equalFront (I.Exp U, I.Exp V) = Conv.conv ((U, I.id), (V, I.id))
      | equalFront (I.Undef, I.Undef) = true

    (* equalCtx' (G, G') = (G=G') *)
    fun equalCtx' (I.Null, I.Null) = true
      | equalCtx' (I.Decl(Dk, I.Dec(_, A)), I.Decl(D1, I.Dec(_, A1))) =
        (Conv.conv ((A, I.id), (A1, I.id)) andalso equalCtx'(Dk, D1))
      | equalCtx' (I.Decl(Dk, I.ADec(_, d')), I.Decl(D1, I.ADec(_, d))) =
        ((d = d') andalso equalCtx'(Dk, D1))
      | equalCtx' (_, _) = false

   (* ---------------------------------------------------------------*)

    (* destructively may update asub ! *)
    fun instanceCtx (asub, (D1, G1) , (D2, G2)) =
      let
        val d1 = I.ctxLength G1
        val d2 = I.ctxLength G2
      in
       if d1 = d2
         then
           (let
              val fasub = assignCtx ((fn asub => ()), ((d1, 0)), (D1, G1), (D2, G2))
            in
              (fasub asub; true)
            end ) handle Assignment msg => ((* print msg;*) false)
       else false
      end


   (* ---------------------------------------------------------------*)
   (* collect EVars in sub *)
   (* collectEVar (D, sq) = (D_sub, D')
     if D |- sq where D is a set of free variables
     then Dsq |- sq  and (Dsq u D') = D
          Dsq contains all the free variables occuring in sq
          D' contains all the free variables corresponding to Gsq
   *)
   fun collectEVar (D, nsub) =
     let
       val D' = emptyCtx ()
       fun collectExp (d, D', D, I.Lam(_, U)) = collectExp (d+1, D', D, U)
         | collectExp (d, D', D, I.Root(I.Const c, S)) = collectSpine (d, D', D, S)
         | collectExp (d, D', D, I.Root(I.BVar k, S)) =
           (case (member (k-d, D))
             of NONE => collectSpine (d, D', D, S)
           | SOME(x, Dec) => (delete (x-d, D); insertList ((x-d, Dec), D')))

         | collectExp (d, D', D, U as I.Root(I.Def k, S)) =
           let
             val U' = Whnf.normalize(Whnf.expandDef(U, I.id))
           in
             collectExp (d, D', D, U')
           end
       and collectSpine (d, D', D, I.Nil) = ()
         | collectSpine (d, D', D, I.App(U, S)) = (collectExp(d, D', D, U); collectSpine(d, D', D, S))
     in
       S.forall nsub (fn (nv, (du, U)) => collectExp (0, D', D, U));
       (D', D)
     end



   (* ---------------------------------------------------------------*)
   (* most specific linear common generalization *)

   (* compatible (T, U) = (T', rho_u, rho_t) opt
    if T is an indexed term
       U is a linear term
       U and T share at least the top function symbol
   then
       T'[rho_u] = U and T'[rho_t] = T
   *)

   fun convAssSub' (G, idx_k, D, asub, d, evarsl as (evars, avars)) =
    (case (RBSet.lookup asub d) of
       NONE => (case member (d, D) of
                  NONE => IntSyn.Shift (evars + avars (* 0 *))

                | SOME(x, IntSyn.Dec(n,V)) =>
                    (* Found an EVar which is not yet
                     instantiated -- must be instantiated when
                     solving residual equations! *)
                    let
                      val s = convAssSub' (G, idx_k + 1, D, asub, d+1, evarsl)
                      val E as I.EVar(r, _, _ , cnstr) = I.newEVar (I.Null, V)
                    in
                      I.Dot(I.Exp(I.EClo(E, I.Shift(evars + avars))), s)
                    end

                | SOME(x, IntSyn.ADec(n,V)) =>
                    (* should never happen -- all avars should
                     have been assigned! *)
                    (print ("convAssSub' -- Found an uninstantiated AVAR\n");
                     raise Error "Unassigned AVar -- should never happen\n")
                    )
     | SOME (F as I.Exp(E)) =>
         let
           val E' = Whnf.normalize (E, I.id)
        in
          I.Dot(I.Exp(E'), convAssSub'(G, idx_k +1, D, asub, d+1, evarsl))
         end)

   fun convAssSub (G, asub, Glength, D', evarsl) =
     convAssSub' (G, 0, D', asub, Glength, evarsl)

   fun isExists (d, I.BVar k, D) = member (k-d, D)

   (* [s']T = U so U = query and T is in the index *)
   fun instance ((D_t, (dt, T)), (D_u, (du,U)), rho_u, ac) =
     let
       fun instRoot (depth, T as I.Root(H1 as I.Const k, S1), U as I.Root(I.Const k', S2), ac) =
           if (k = k') then
             instSpine(depth, S1, S2, ac)
           else
             raise Instance "Constant mismatch\n"
         | instRoot (depth, T as I.Root(H1 as I.Def k, S1), U as I.Root(I.Def k', S2), ac) =
           if (k = k') then
             instSpine(depth, S1, S2, ac)
           else
             let
               val T' = Whnf.normalize(Whnf.expandDef (T, I.id))
               val U' = Whnf.normalize(Whnf.expandDef(U, I.id))
             in
               instExp (depth, T', U', ac)
             end

         | instRoot (depth, T as I.Root(H1 as I.Def k, S1), U as I.Root(H2, S2), ac) =
             let
               val T' = Whnf.normalize(Whnf.expandDef (T, I.id))
             in
               instExp (depth, T', U, ac)
             end
         | instRoot (d,  T as I.Root(H1 as I.BVar k, S1), U as I.Root(I.BVar k', S2), ac) =
           if (k > d) andalso (k' > d)
             then (* globally bound variable *)
               let
                 val k1 = (k - d)
                 val k2 = (k' - d)
               in
                 case (member (k1, D_t), member(k2, D_u))
                 of(NONE, NONE) =>
                   ((* both refer to the same globally bound variable in G *)
                    if (k1 = k2)
                      then
                        instSpine(d, S1, S2, ac)
                    else
                      raise Instance "Bound variable mismatch\n")
                 | (SOME(x, Dec1), SOME(x', Dec2)) =>
                   (* k, k' refer to the existential *)
                   (if ((k1 = k2) andalso equalDec(Dec1, Dec2))
                      then (* they refer to the same existential variable *)
                        let
                          (* this is unecessary *)
                          (* since existential variables have the same type
                             and need to be fully applied in order, S1 = S2 *)
                          val ac' = instSpine(d, S1, S2, ac)
                          val ac'' = (fn asub =>
                                      (ac' asub; (* S.insert asub (k - d, I.Idx (k-d)) *)
                                       assign ((* ctxTotal,*) d, Dec1, T, U, asub) ))
                        in
                          ac''
                        end
                    else
                      (* instance checking only Sun Oct 27 12:16:10 2002 -bp *)
                      (fn asub => (ac asub;
                                   assign ((* ctxTotal,*) d, Dec1, T, U, asub))))

                        (* instance checking only Sun Oct 27 12:18:53 2002 -bp *)
                 | (SOME(x, Dec1 as I.ADec(n,d')), NONE) =>
                   (fn asub => (ac asub;
                                assign ((* ctxTotal,*) d, Dec1, T, U, asub)))

                 | (SOME(x, Dec1), NONE) =>
                   (fn asub => (ac asub;
                                assign ((* ctxTotal,*) d, Dec1, T, U, asub)))

                 | (_, _) =>  raise Instance "Impossible\n"
               end

           else (* locally bound variables *)
               raise Instance "Bound variable mismatch\n"
       | instRoot (d, T as I.Root (H1 as I.BVar k, S1), U as I.Root(I.Const k', S2), ac) =
         (* this case only should happen during instance checking *)
         (case isExists (d, I.BVar k, D_t)
          of NONE => raise Instance "Impossible\n"

          | SOME(x, Dec1 as I.ADec(_,_)) =>
              (fn asub => (ac asub;  assign ((* ctxTotal,*) d, Dec1, T, U, asub)))

          | SOME(x, Dec1) =>
              (fn asub => (ac asub;  assign ((* ctxTotal, *) d, Dec1, T, U, asub))))

       | instRoot (d, T as I.Root (H1 as I.BVar k, S1), U as I.Root(I.Def k', S2), ac) =
         (* this case only should happen during instance checking *)
         (case isExists (d, I.BVar k, D_t)
          of NONE => raise Instance "Impossible\n"

          | SOME(x, Dec1 as I.ADec(_,_)) =>
              (fn asub => (ac asub;  assign ((* ctxTotal,*) d, Dec1, T, U, asub)))

          | SOME(x, Dec1) =>
              (fn asub => (ac asub;  assign ((* ctxTotal, *) d, Dec1, T, U, asub))))

         | instRoot (depth, T as I.Root(H1, S1), U as I.Root(I.Def k', S2), ac) =
             let
               val U' = Whnf.normalize(Whnf.expandDef (U, I.id))
             in
               instExp (depth, T, U', ac)
             end

       | instRoot (d, T as I.Root(H1, S1), U as I.Root(H2, S2), ac) =
              raise Instance "Other Cases impossible\n"

     and instExp (d, T as I.NVar n, U as I.Root(H, S), ac) =
         (S.insert rho_u (n, (d,U)); ac)

       | instExp (d, T as I.Root(H1, S1), U as I.Root(H2, S2), ac) =
         instRoot(d, I.Root(H1, S1), I.Root(H2, S2), ac)

       | instExp (d, I.Lam(D1 as I.Dec(_,A1), T1), I.Lam(D2 as I.Dec(_, A2), U2), ac) =
       (* by invariant A1 = A2 -- actually this invariant may be violated, but we ignore it. *)
             instExp (d+1, T1,  U2, ac)

       | instExp (d, T, U, ac) =
           (* U = EVar, EClo -- can't happen -- Sun Oct 20 13:41:25 2002 -bp *)
       (print "instExp -- falls through?\n";
        raise Instance "Impossible\n")

     and instSpine (d, I.Nil, I.Nil, ac) = ac
       | instSpine (d, I.App(T, S1), I.App(U, S2), ac) =
       let
         val ac' = instExp (d, T, U, ac)
         val ac'' = instSpine (d, S1, S2, ac')
       in
         ac''
       end
       | instSpine (d, I.Nil, I.App (_ , _), ac) =
          (print ("Spines are not the same -- (first one is Nil) -- cannot happen!\n");
           raise Instance "DifferentSpines\n")
       | instSpine (d, I.App (_ , _), I.Nil, ac) =
          (print ("Spines are not the same -- second one is Nil -- cannot happen!\n");
           raise Instance "DifferentSpines\n")

       | instSpine (d, I.SClo (_ , _), _, ac) =
          (print ("Spine Closure!(1) -- cannot happen!\n");
           raise Instance "DifferentSpines\n")
       | instSpine (d, _ , I.SClo (_ , _), ac) =
          (print ("Spine Closure! (2) -- cannot happen!\n");
           raise Instance " DifferentSpines\n")
     in
       (* by invariant dt = du *)
      ac := instExp (dt, T, U, !ac)
      (* if it succeeds then it will return a continuation which will
         instantiate the "evars" and rho_t will contain all
         nvar instantiations
         otherwise it will raise Instance *)
     end


   fun compHeads ((D_1, I.Const k), (D_2, I.Const k')) = (k = k')
     | compHeads ((D_1, I.Def k), (D_2, I.Def k')) = (k = k')
     | compHeads ((D_1, I.BVar k), (D_2, I.BVar k')) =
       (case isExists (0, I.BVar k, D_1)
          of NONE => (k = k')
        | SOME(x,Dec) => true)
     | compHeads ((D_1, I.BVar k), (D_2, H2)) =
        (case isExists (0, I.BVar k, D_1)
          of NONE => false
        | SOME(x,Dec) => true)
     | compHeads ((D_1, H1), (D_2, H2)) = false


   fun compatible' ((D_t, (dt,T)), (D_u, (du,U)), Ds, rho_t, rho_u) =
     let
       fun genNVar ((rho_t, T), (rho_u, U)) =
         (S.insert rho_t (!nctr+1, T);
          S.insert rho_u (!nctr+1, U); (* by invariant dt = du *)
          newNVar())

       fun genRoot (d, T as I.Root(H1 as I.Const k, S1), U as I.Root(I.Const k', S2)) =
         if (k = k') then
           let
             val S' = genSpine(d, S1, S2)
           in
             I.Root(H1, S')
           end
         else
           genNVar ((rho_t, (d, T)), (rho_u, (d, U)))
         | genRoot (d, T as I.Root(H1 as I.Def k, S1), U as I.Root(I.Def k', S2)) =
         if (k = k') then
           let
             val S' = genSpine(d, S1, S2)
           in
             I.Root(H1, S')
           end
         else
           (* could expand definitions here ? -bp*)
           genNVar ((rho_t, (d, T)), (rho_u, (d, U)))


         | genRoot (d,  T as I.Root(H1 as I.BVar k, S1), U as I.Root(I.BVar k', S2)) =
           if (k > d) andalso (k' > d)
             then (* globally bound variable *)
               let
                 val k1 = (k - d)
                 val k2 = (k' - d)
               in
                 case (member (k1, D_t), member(k2, D_u)) of
                   (NONE, NONE) =>  (* should never happen *)
                     (if (k1 = k2)
                       then
                         (let
                            val S' = genSpine(d, S1, S2)
                          in
                            I.Root(H1, S')
                          end)  handle DifferentSpine => genNVar ((rho_t, (d,T)), (rho_u, (d,U)))
                     else
                       genNVar ((rho_t, (d,T)), (rho_u, (d,U))))
                 | (SOME(x, Dec1), SOME(x', Dec2)) =>
                 (* k, k' refer to the existential *)
                   if ((k1 = k2) andalso equalDec(Dec1, Dec2))
                     then (* they refer to the same existential variable *)
                       let
                         (* this is unecessary -- since existential variables have the same type
                            and need to be fully applied in order, S1 = S2 *)
                         val S' = genSpine(d, S1, S2)
                       in
                         (delete (x, D_t) ;
                          delete (x', D_u);
                          insertList ((x, Dec1), Ds);
                          I.Root(H1, S'))
                       end
                   else
                     (* variant checking only *)
                     genNVar ((rho_t, (d,T)), (rho_u, (d,U)))

                 | (_, _) =>
                     genNVar ((rho_t, (d,T)), (rho_u, (d,U)))
               end
           else (* locally bound variables *)
             if (k = k') then
               (let
                  val S' = genSpine(d, S1, S2)
                in
                  I.Root(H1, S')
                end) handle DifferentSpines => genNVar ((rho_t, (d,T)), (rho_u, (d,U)))
             else
               genNVar ((rho_t, (d,T)), (rho_u, (d,U)))
        | genRoot (d, T as I.Root (H1 as I.BVar k, S1), U as I.Root(I.Const k', S2)) =
               genNVar ((rho_t, (d,T)), (rho_u, (d,U)))

        | genRoot (d, T as I.Root (H1 as I.BVar k, S1), U as I.Root(I.Def k', S2)) =
               genNVar ((rho_t, (d,T)), (rho_u, (d,U)))

        | genRoot (d, T as I.Root(H1, S1), U as I.Root(H2, S2)) =
               genNVar ((rho_t, (d,T)), (rho_u, (d,U)))

     and genExp (d, T as I.NVar n, U as I.Root(H, S)) =
         (S.insert rho_u (n, (d,U)); T)
       | genExp (d, T as I.Root(H1, S1), U as I.Root(H2, S2)) =
         genRoot(d, I.Root(H1, S1), I.Root(H2, S2))
       | genExp (d, I.Lam(D1 as I.Dec(_,A1), T1), I.Lam(D2 as I.Dec(_, A2), U2)) =
         (* by invariant A1 = A2 *)
         let
           val E = genExp (d+1, T1,  U2)
         in
           I.Lam(D1, E)
         end
         | genExp (d, T, U) =
         (* U = EVar, EClo -- can't happen -- Sun Oct 20 13:41:25 2002 -bp *)
         (print "genExp -- falls through?\n";
          genNVar ((rho_t, (d,T)), (rho_u, (d,U))))

       and genSpine (d, I.Nil, I.Nil) =  I.Nil
         | genSpine (d, I.App(T, S1), I.App(U, S2)) =
         let
           val  E = genExp (d, T, U)
           val  S' = genSpine (d, S1, S2)
         in
           I.App(E, S')
         end
         | genSpine (d, I.Nil, I.App (_ , _)) = raise DifferentSpines
         | genSpine (d, I.App (_ , _), I.Nil) = raise DifferentSpines

         | genSpine (d, I.SClo (_ , _), _) =  raise DifferentSpines
         | genSpine (d, _ , I.SClo (_ , _)) = raise DifferentSpines
     in
       (* by invariant dt = du *)
       Variant(dt, genExp (dt, T, U))
     end


   fun compatible ((D_t, T as (d1,I.Root(H1, S1))), (D_u, U as (d2, I.Root (H2, S2))),
                   Ds, rho_t, rho_u) =
     if compHeads ((D_t, H1), (D_u, H2))
       then
         compatible' ((D_t, T), (D_u, U), Ds, rho_t, rho_u)
     else NotCompatible
     |compatible ((D_t, T), (D_u, U), Ds, rho_t, rho_u) =
       compatible' ((D_t, T), (D_u, U), Ds, rho_t, rho_u)

  (* compatibleCtx (asub, (Dsq, Gsq, eqn_sq), GR) = option

    if Dsq is a subset of Dsq_complete
       where Dsq_complete encompasses all evars and avars in the original query
       Dsq |- Gsq ctx
       Dsq, Gsq |- eqn_sq
       there exists (_, D', G', eqn', ansRef', _, status') in GR
       s.t.
       Gsq is an instance of G'
       (andalso eqn_sq = eqn')
    then
      SOME((D', G', eqn'), answRef', status)
      and asub is destructively updated s.t. Dsq_complete |- Gsq = [asub]G'

    else
      NONE
   *)
  fun compatibleCtx (asub, (Dsq, Gsq, eqn_sq), []) = NONE
    | compatibleCtx (asub, (Dsq, Gsq, eqn_sq),
                     ((_, Delta', G', eqn', answRef', _, status')::GRlist)) =
      if instanceCtx (asub, (Dsq, Gsq), (Delta', G'))
        then
          SOME((Delta', G', eqn'), answRef', status')
       else
         compatibleCtx(asub, (Dsq, Gsq, eqn_sq), GRlist)

  (* ---------------------------------------------------------------*)
  (* instanceSub(nsub_t, squery) = (rho_u, asub)

   if DOM(nsub_t) <= DOM(nsub_u)
      CODOM(nsub_t) : index terms
      CODOM(nsub_u) : linear terms
        G_u, Glocal_u |- nsub_u
    N ; G_t, Glocal_t |- nsub_t
   then
     nsub_t = sigma o rho_t
     nsub_e = sigma o rho_u

    Glocal_e ~ Glocal_t  (have "approximately" the same type)
    l_g = |Glocal_u|


    [asub]nsub_t = squery
   *)

  fun instanceSub ((D_t, nsub_t), (Dsq, squery), asub) =
    let
      val rho_u = nid()
      val D_r2 = copy Dsq
      val ac = ref (fn (asub :exSubsts) => ())
     (* by invariant rho_t = empty, since nsub_t <= squery *)
    in
     ((S.forall squery
      (fn (nv, (du,U)) =>
       (case (S.lookup nsub_t nv)
          of SOME ((dt,T)) =>
            (* note by invariant Glocal_e ~ Glocal_t *)
            (* [ac]T = U *)
             instance((D_t, (dt,T)), (D_r2, (du,U)), rho_u, ac)
            (* if U is an instance of T then [ac][rc_u]T = U *)
            (* once the continuations ac are triggered *)
              | NONE => S.insert rho_u (nv, (du,U)))));
      (!ac) (asub);
      InstanceSub (asub, (D_r2, rho_u)))
      handle Instance msg => NoCompatibleSub
    end


  (* [asub]nsub_t = sq  where sq is the query substitution *)
  fun instChild (N as Leaf((D_t, nsub_t), GList), (D_sq, sq), asub) =
        instanceSub ((D_t, nsub_t), (D_sq,  sq), asub)
    | instChild (N as Node((D_t, nsub_t), Children'), (D_sq, sq), asub) =
        instanceSub ((D_t, nsub_t), (D_sq, sq), asub)

  fun findAllInst (G_r, children, Ds, asub) =
    let
      fun findAllCands (G_r, nil, (Dsq, sub_u), asub, IList) = IList
        | findAllCands (G_r, (x::L), (Dsq, sub_u), asub, IList) =
        let
          val asub' = S.copy asub
        in
          case instChild (!x, (Dsq, sub_u), asub)
            (* will update asub *)
            of NoCompatibleSub => findAllCands (G_r, L, (Dsq, sub_u), asub', IList)
            | InstanceSub(asub, Drho2) => findAllCands (G_r, L, (Dsq, sub_u), asub', ((x, Drho2, asub)::IList))
        end
    in
      findAllCands (G_r, children, Ds, asub, nil)
    end

 (* Solving  variable definitions *)
 (* solveEqn ((VarDef, s), G) = bool

    if G'' |- VarDef and G   |- s : G''
       G   |- VarDef[s]
    then
       return true, if VarDefs are solvable
              false otherwise
 *)
  fun solveEqn ((T.Trivial, s), G) = true
    | solveEqn ((T.Unify(G',e1, N (* evar *), eqns), s), G) =
      let
        val G'' = compose (G', G)
        val s' = shift (G'', s)
      in
        Assign.unifiable (G'', (N, s'),(e1, s'))
        andalso solveEqn ((eqns, s), G)
     end

(* Mon Dec 27 11:57:35 2004 -bp *)
 (* solveEqn' ((VarDef, s), G) = bool

    if G'' |- VarDef and G   |- s : G''
       G   |- VarDef[s]
    then
       return true, if VarDefs are solvable
              false otherwise
 *)
  fun solveEqn' ((T.Trivial, s), G) = true
    | solveEqn' ((T.Unify(G',e1, N (* evar *), eqns), s), G) =
      let
        val G'' = compose (G', G)
        val s' = shift (G', s)
      in
        Assign.unifiable (G'', (N, s'),(e1, s'))
        andalso solveEqn' ((eqns, s), G)
     end

(* Mon Dec 27 12:20:45 2004 -bp
 (* solveEqn' ((VarDef, s), G) = bool

    if G'' |- VarDef and G   |- s : G''
       G   |- VarDef[s]
    then
       return true, if VarDefs are solvable
              false otherwise
 *)
  fun solveEqn' (T.Trivial, s) = true
    | solveEqn' (T.Unify(G',e1, N (* evar *), eqns), s) =
      let
        val s' = shift (G', s)
      in
        Assign.unifiable (G', (N, s'),(e1, s'))
        andalso solveEqn' (eqns, s)
     end

 (* solveEqnI' ((VarDef, s), G) = bool

    if G'' |- VarDef and G   |- s : G''
       G   |- VarDef[s]
    then
       return true, if VarDefs are solvable
              false otherwise
 *)
  fun solveEqnI' (T.Trivial, s) = true
    | solveEqnI' (T.Unify(G',e1, N (* evar *), eqns), s) =
      let
        val s' = shift (G', s)
        (* note: we check whether N[s'] is an instance of e1[s'] !!! *)
        (* at this point all AVars have been instantiated, and we could use Match.instance directly *)
      in
        Assign.instance (G', (e1, s'), (N, s'))
        andalso solveEqnI' (eqns, s)
     end
 Mon Dec 27 11:58:21 2004 -bp *)
 (* solveEqnI' ((VarDef, s), G) = bool

    if G'' |- VarDef and G   |- s : G''
       G   |- VarDef[s]
    then
       return true, if VarDefs are solvable
              false otherwise
 *)
  fun solveEqnI' ((T.Trivial, s), G) = true
    | solveEqnI' ((T.Unify(G',e1, N (* evar *), eqns), s), G) =
      let
        val G'' = compose (G', G)
        val s' = shift (G', s)
        (* note: we check whether N[s'] is an instance of e1[s'] !!! *)
        (* at this point all AVars have been instantiated, and we could use Match.instance directly *)
      in
        Assign.instance (G'', (e1, s'), (N, s'))
        andalso solveEqnI' ((eqns, s), G)
     end

   (* retrieve all Instances from substitution tree *)
   (* retreiveInst (Nref, (Dq, sq), s', GR) = callCheckResult

      Invariant:

      If there exists a path r1 ... rn = p
         in the substitution tree with root Nref
         and there exists an assignable substitution s' (D
         s.t. [r']
      then
         return RepeatedEntry
      else raises exception instance
    *)
   fun retrieveInst (Nref, (Dq, sq), asub, GR) =
     let
      fun retrieve' (N as Leaf ((D, s), GRlistRef), (Dq, sq), asubst,
                     GR' as (DAEVars as (DEVars, DAVars), G_r, eqn, stage, status)) =
        (* s and sq are compatible by invariant *)
        (* [asub]s = sq   and there exists a path (D1, s1) ... (Dn,sn) from the root to the leaf (D,s)
           s.t. [asub]s1 o s2 o ... sn o s corresponds to original query
           *)
        let
          val (Dsq, D_G) = collectEVar (Dq, sq)
            (* Dq = (Dsq' u Dg) where Dsq' = evars occurring in sq
                                      D_G = evars occuring in G_sq or only in eqn_sq

               and Dsq = D since there exists a path s1 ... sn from the root to the leaf (D,s)
                 s.t. [asub]s1 o s2 o ... sn o s corresponds to original query
             *)
        in
          (case compatibleCtx (asubst, (D_G, G_r, eqn), (!GRlistRef))
             (* compatibleCtx may destructively update asub ! *)
           of NONE => ((* compatible path -- but different ctx *)
                       raise Instance "Compatible path -- different ctx\n")
         | SOME((D', G', eqn'), answRef', status') =>
             (* compatible path -- SAME ctx *)
             ((* note: previously we checked eqn' = eqn! -- this is too restrictive
                 now - Dec  6 2004 -bp we check whether eqn is an instance of eqn'
                 note: this is very delicate code.
               *)
              let
                val DAEVars = compose (DEVars, DAVars)
                (* Since there exists a path (D1, s1) ... (Dn,sn) from the root to the leaf (D,s)
                   D1', ...., Dn', D, D' = D*
                   and          G' |- esub' : DAEVars, G'        and       .   |- esub : DAEVars
                        DAEVars, G |- asub' : D*, G'                   DAEVars |- asub : D*

                  note: asub' may refer to free variables which denote evars in D*
                        which only occur in eqn' and hence have not yet been instantiated
                        however: all avars in D* have been instantiated!
                 *)
                val esub = ctxToAVarSub (G', DAEVars, I.Shift(0))
                val asub = convAssSub(G', asubst, (I.ctxLength G') + 1,  D',  (I.ctxLength(DAVars), I.ctxLength(DEVars)))
                (* Residual equation of query:
                   DAEVars, G' |- eqn  hence we solve : G' |= [esub']eqn *)
                val _ = if solveEqn' ((eqn, shift(G',esub)), G' (* = G_r *))
                          then () else print " failed to solve eqn_query\n"

(*              val _ = if solveEqn' (eqn, esub)
                          then () else print " failed to solve eqn_query\n"  *)
                val easub = normalizeSub(I.comp(asub, esub))

                (* Residual equations in index:
                   D*, G' |- eqn'    where eqn' = AVar1 = E1 .... AVarn = En
                                      and  Ei may contain free variables
                      G'  |= [esub](asub) (eqn')

                      solve eqn' from path in index using instance or matching ONLY
                      to instantiate the free variables Ei

                   remark: DAEVars, G' |= [asub]eqn'   should work in theory too,
                           if the free variables in asub are created in such a way that they may depend on DAVars.
                           otherwise unification or instance checking will fail or the resulting instantiation
                           for the free variables in asub is too restrictive, s.t. retrieval fails
                   *)
              in
                if solveEqnI' ((eqn', shift(G',easub)), G')
(*              if solveEqnI' (eqn', easub) *)
                   (* solve residual equations using higher-order matching Wed Dec 22 2004 -bp *)
                  then T.RepeatedEntry((esub, asub), answRef', status')
                else raise Instance "Compatible path -- resdidual equ. not solvable\n"
              end
              ))
        end

      | retrieve' (N as Node((D, sub), children), (Dq, sq), asub,
                   GR as (DAEVars, G_r, eqn, stage, status)) =
        let
          val InstCand = findAllInst (G_r, children, (Dq, sq), asub)

          fun checkCandidates nil =
             (* no child is compatible with sq *)
             raise Instance "No compatible child\n"

            | checkCandidates ((ChildRef, Drho2, asub)::ICands) =
              (* there is an instance  *)
              (retrieve' (!ChildRef, Drho2, asub, GR))
               handle Instance msg =>  ((* print msg; *)checkCandidates ICands)
        in
          checkCandidates InstCand
        end
  in
    (fn () => (), retrieve' (!Nref, (Dq, sq), asub, GR))
  end

(*---------------------------------------------------------------------------*)
(* insert new entry into substitution tree *)
(* assuming there is no compatible entry already *)
 (* compatibleSub(nsub_t, squery) = (sigma, rho_t, rho_u) opt

   if DOM(nsub_t) <= DOM(squery)
      CODOM(nsub_t) : index terms
      CODOM(squery) : linear terms
        G_u, Glocal_u |- squery
    N ; G_t, Glocal_t |- nsub_t
   then
     nsub_t = sigma o rho_t
     nsub_e = sigma o rho_u

    Glocal_e ~ Glocal_t  (have "approximately" the same type)

   *)
  fun compatibleSub ((D_t, nsub_t), (Dsq, squery)) =
    let
      val (sigma, rho_t, rho_u) = (nid(), nid (), nid ())
      val Dsigma = emptyCtx ()
      val D_r1 = copy D_t
      val D_r2 = copy Dsq
      val choose = ref (fn match : bool => ())
     (* by invariant rho_t = empty, since nsub_t <= squery *)
      val _ =  S.forall squery
        (fn (nv, U) =>
         (case (S.lookup nsub_t nv)
            of SOME (T) =>     (* note by invariant Glocal_e ~ Glocal_t *)
              (case compatible ((D_r1, T), (D_r2, U), Dsigma, rho_t, rho_u)
                 of NotCompatible => (S.insert rho_t (nv, T);
                                      S.insert rho_u (nv, U))
                  | Variant(T') =>
                   let
                     val restc = (!choose)
                   in
                     (S.insert sigma (nv, T');
                     choose := (fn match => (restc match; if match then () else ())))
                     end)

          (* here Glocal_t will be only approximately correct! *)
          | NONE => S.insert rho_u (nv, U)))
    in
      if isId (rho_t)
        then
          (* perfect match under asub and rho_t = nsub_t
           sigma = rho_t and sigma o asub = rho_u *)
          ((!choose) true ;
           VariantSub(D_r2, rho_u))
      else
        ((* split -- asub is unchanged *)
         (!choose) false ;
         if isId(sigma)
           then NoCompatibleSub
         else
           SplitSub((Dsigma, sigma), (D_r1, rho_t), (D_r2, rho_u)))
          (* Dsigma |~ sigma, D_r1 |~ rho_t, D_r1 |~ rho_u *)
    end


 (* ---------------------------------------------------------------------- *)

(*  fun mkLeaf (Ds, GR, n) = Leaf (Ds, GR)*)

  fun mkNode (Node(_, Children), Dsigma as (Ds, sigma),
              Drho1 as (D1, rho1), GR as ((evarl, l), dp, eqn, answRef, stage, status),
              Drho2 as (D2, rho2)) =
      let
        val (D_rho2, D_G2) = collectEVar (D2, rho2)
        val GR' = ((evarl, l), D_G2, dp, eqn, answRef, stage, status)
        val (sizeSigma, sizeRho1, sizeRho2) = ((S.size sigma), (S.size rho1), (S.size rho2))
      in
        Node(Dsigma, [ref (Leaf((D_rho2, rho2), ref [GR'])), ref (Node(Drho1, Children))])
      end

    | mkNode (Leaf(c, GRlist), Dsigma as (Ds, sigma),
              Drho1 as (D1, rho1), GR2 as ((evarl, l), dp, eqn, answRef, stage, status),
              Drho2 as (D2, rho2)) =
       let
         val (D_rho2, D_G2) = collectEVar (D2, rho2)
         val GR2' =((evarl, l), D_G2, dp, eqn, answRef, stage, status)
       in
         Node(Dsigma,[ref(Leaf((D_rho2, rho2), ref [GR2'])), ref(Leaf(Drho1, GRlist))])
       end

  (* ---------------------------------------------------------------------- *)
  fun compChild (N as Leaf((D_t, nsub_t), GList), (D_e, nsub_e)) =
        compatibleSub ((D_t, nsub_t), (D_e,  nsub_e))
    | compChild (N as Node((D_t, nsub_t), Children'), (D_e, nsub_e)) =
        compatibleSub ((D_t, nsub_t), (D_e, nsub_e))

  fun findAllCandidates (G_r, children, Ds) =
    let
      fun findAllCands (G_r, nil, (Dsq, sub_u), VList, SList) = (VList, SList)
        | findAllCands (G_r, (x::L), (Dsq, sub_u), VList, SList) =
          case compChild (!x, (Dsq, sub_u))
            of NoCompatibleSub => findAllCands (G_r, L, (Dsq, sub_u), VList, SList)
            | SplitSub (Dsigma, Drho1, Drho2) =>
              findAllCands (G_r, L, (Dsq, sub_u),VList,
                            ((x, (Dsigma, Drho1, Drho2))::SList))
            | VariantSub (Drho2 as (D_r2, rho2)) =>
              findAllCands (G_r, L, (Dsq, sub_u), ((x, Drho2,I.id)::VList), SList)
    in
      findAllCands (G_r, children, Ds, nil,  nil)
    end

 (* ---------------------------------------------------------------------- *)
  fun divergingCtx (stage, G, GRlistRef) =
    let
      val l = I.ctxLength(G) +  3  (* this 3 is arbitrary -- lockstep *)
    in
    List.exists (fn ((_, l), D, G', _, _, stage', _) => (stage = stage' andalso (l > (I.ctxLength(G')))))
    (!GRlistRef)
    end

  fun eqHeads (I.Const k, I.Const k') =  (k = k')
    | eqHeads (I.BVar k, I.BVar k') =  (k = k')
    | eqHeads (I.Def k, I.Def k') = (k = k')
    | eqHeads (_, _) = false

 (* eqTerm (t2, (t, rho1)) = bool
    returns true iff t2 = t[rho1]
  t2 is a linear term which may not contain any nvars!
  t may contain nvars
 *)

 fun eqTerm (I.Root(H2, S2), (t as I.Root(H, S), rho1)) =
     if eqHeads (H2, H)
       then eqSpine(S2, (S, rho1))
     else
       false
   | eqTerm (T2, (I.NVar n, rho1)) =
     (case (S.lookup rho1 n)
        of NONE => false
      | SOME ((dt1, T1)) => eqTerm (T2, (T1, nid())))
   | eqTerm (I.Lam(D2, T2), (I.Lam(D, T), rho1)) =
     eqTerm (T2, (T, rho1))
   | eqTerm (_, (_, _)) = false

 and eqSpine (I.Nil, (I.Nil, rho1)) = true
  | eqSpine (I.App(T2, S2), (I.App(T, S), rho1)) =
    eqTerm (T2, (T, rho1)) andalso eqSpine (S2, (S, rho1))

 fun divergingSub ((Ds, sigma), (Dr1, rho1), (Dr2, rho2)) =
    S.exists rho2 (fn (n2, (dt2,t2)) => S.exists sigma (fn (_,(d,t)) => eqTerm (t2, (t, rho1))))

 (* ---------------------------------------------------------------------- *)
 (* Insert via variant checking *)

  fun variantCtx ((G, eqn), []) = NONE
    | variantCtx ((G,eqn), ((l', D_G, G', eqn', answRef', _, status')::GRlist)) =
      (if (equalCtx' (G, G') andalso equalEqn(eqn, eqn'))
         then SOME(l', answRef', status')
       else
         variantCtx ((G, eqn), GRlist))

 (* insert (Nref, (Dq, sq), GR) = TableResult *)
 fun insert (Nref, (Dsq, sq), GR) =
   let
     fun insert' (N as Leaf (_, GRlistRef), (Dsq, sq),
                  GR as (l, G_r, eqn, answRef, stage, status)) =
       (case variantCtx ((G_r, eqn), (!GRlistRef)) of
          NONE => ((* compatible path -- but different ctx! *)
                   let
                     val (D_nsub, D_G) = collectEVar (Dsq, sq)
                     (* D_G contains evars occurring only in eqn or G
                        D_nsub contains evars occurring only in sq
                        furthermore: D_nsub = D where Leaf((D,s), GRlistRef)
                     *)
                     val GR' = (l, D_G, G_r, eqn, answRef, stage, status)
                   in
                     (fn () => (GRlistRef := (GR'::(!GRlistRef));
                                answList := (answRef :: (!answList))),
                      T.NewEntry(answRef))
                   end)
        | SOME(_, answRef', status') => ((* compatible path -- SAME ctx and SAME eqn!
                                          this implies: SAME D_G *)
                                ((fn () => ()), T.RepeatedEntry((I.id, I.id),  answRef', status'))
                                ))


      | insert' (N as Node((D, sub), children), (Dsq, sq),
                 GR as (l, G_r, eqn, answRef, stage, status)) =
        let
          val (VariantCand, SplitCand) = findAllCandidates (G_r, children, (Dsq, sq))
          val (D_nsub, D_G) = collectEVar (Dsq, sq)
          val GR' = (l, D_G, G_r, eqn, answRef, stage, status)
          fun checkCandidates (nil, nil) =
             (* no child is compatible with sq *)
             (fn () => (Nref := Node((D, sub), (ref (Leaf((D_nsub, sq), ref [GR'])))::children);
                        answList := (answRef :: (!answList))),
                T.NewEntry(answRef))

            | checkCandidates (nil, ((ChildRef, (Dsigma, Drho1, Drho2))::_)) =
              (* split an existing node *)
              if ((!TableParam.divHeuristic) andalso
                  divergingSub (Dsigma, Drho1, Drho2))
               then
                 ((* substree diverging -- splitting node *)
                  (fn () => (ChildRef :=  mkNode((!ChildRef), Dsigma, Drho1, GR, Drho2);
                             answList := (answRef :: (!answList))),
                   T.DivergingEntry(I.id, answRef)))
             else
                ((* split existing node *)
                 (fn () => (ChildRef :=  mkNode((!ChildRef), Dsigma, Drho1, GR, Drho2);
                            answList := (answRef :: (!answList))),
                 T.NewEntry(answRef)))

            | checkCandidates (((ChildRef, Drho2, asub)::nil),  _) =
              (* unique "perfect" candidate (left) *)
                insert (ChildRef, Drho2, GR)

            | checkCandidates (((ChildRef, Drho2, asub)::L), SCands) =
              (* there are several "perfect" candidates *)
              (case (insert (ChildRef, Drho2, GR))
                 of (_, T.NewEntry(answRef)) =>  checkCandidates (L, SCands)
               | (f, T.RepeatedEntry(asub, answRef, status)) =>
                    ((f, T.RepeatedEntry(asub, answRef, status)))
               | (f, T.DivergingEntry(asub, answRef)) => ((f, T.DivergingEntry(asub, answRef))))

        in
          checkCandidates (VariantCand, SplitCand)
        end
  in
    insert' (!Nref, (Dsq, sq), GR)
  end

    (* ---------------------------------------------------------------------- *)
    (* answer check and insert

     Invariant:
        D |- Pi G.U
          |- (Pi G.U)[s]
       .  |- s : D
       {{K}} are all the free variables in s
        D_k is the linear context of all free variables in {{K}}
        D_k |- s_k : D  and eqn
        D_k |- (Pi G.U)[s_k] and eqn

      answerCheck (G, s, answRef, 0) = repeated
         if (D_k, s_k, eqn)  already occurs in answRef
      answerCheck (G,s, answRef, O) = new
         if (D_k, s_k, eqn) did not occur in answRef
         Sideeffect: update answer list for U
     *)
    fun answCheckVariant (s', answRef, O) =
      let
        fun member ((D, sk), []) = false
          | member ((D, sk), (((D1, s1),_)::S)) =
            if equalSub (sk,s1) andalso equalCtx'(D, D1) then
              true
            else
              member ((D, sk), S)

        val (DEVars, sk) = A.abstractAnswSub s'

      in
        if member ((DEVars, sk), T.solutions answRef) then
          T.repeated
        else
          (T.addSolution (((DEVars, sk), O), answRef);
          T.new)
      end

    (* ---------------------------------------------------------------------- *)
    fun reset () =
      (nctr := 1;
      (* Reset Subsitution Tree *)
       Array.modify (fn (n, Tree) => (n := 0;
                                      Tree := !(makeTree ());
                                      answList := [];
                                      added := false;
                                      (n, Tree))) indexArray)

    (* makeCtx (n, G, G') =  unit
     if G LF ctx
     then
      G' is a set
      where (i,Di) corresponds to the i-th declaration in G

    note: G' is destructively updated
    *)
    fun makeCtx (n, I.Null, DEVars : ctx) = ()
      | makeCtx (n, I.Decl(G, D), DEVars : ctx) =
        (insertList ((n, D), DEVars);
         makeCtx (n+1, G, DEVars))


   (* callCheck (a, DAVars, DEVars, G, U, eqn, status) = TableResult
    if
      U is atomic (or base type) i.e. U = a S

      DAVars, DEVars, G |- U
      DAVars, DEVars, G |- eqn

      Tree is the substitution trie associated with type family a

   then
      if there exists a path r1 o r2 o ... o rn = p in Tree
         together with some (G',eqn', answRef') at the leaf
         and DAVars', DEVars', G' |- p
      and there exists a substitution s' s.t.

          DAVars, DEVars |- s' : DAVars', DEVars'
          [s']G' = G and [s']p = U

      and moreover
          there exists a substitution r' s.t.  G |- r' : DAVars, DEVars, G
          (which re-instantiates evars)

      and
            G |= [r']eqn    and [s']G' |= [r'][s']eqn'
     then
       TableResult = RepeatedEntry(s', answRef')

     otherwise

       TableResult = NewEntry (answRef')
       and there exists a path r1 o r2 o ... o rk = U in Tree
           together with (G,eqn, answRef) at the leaf

   *)
    fun callCheck (a, DAVars, DEVars, G , U, eqn, status) =
      let
        val (n, Tree) = Array.sub (indexArray, a)
        val sq = S.new()
        val DAEVars = compose (DEVars, DAVars)
        val Dq = emptyCtx()
        val n = I.ctxLength(G)                         (* n = |G| *)
        val _ = makeCtx (n+1, DAEVars, Dq:ctx)         (* Dq = DAVars, DEVars *)
        val l = I.ctxLength(DAEVars)                   (* l = |D| *)
        val _ = S.insert sq (1, (0, U))
        val GR = ((l, n+1), G, eqn, emptyAnswer(), !TableParam.stageCtr, status)
        val GR' = ((DEVars, DAVars), G, eqn, !TableParam.stageCtr, status)
        val result = retrieveInst (Tree, (Dq, sq), asid() (* assignable subst *), GR')
          handle Instance msg => ((* sq not in index --> insert it *)
                                  insert (Tree, (Dq, sq), GR))
      in
        case result of
          (sf, T.NewEntry(answRef)) =>
            (sf(); added := true;
             T.NewEntry(answRef))
        | (_, T.RepeatedEntry(asub, answRef, status)) =>
            T.RepeatedEntry(asub, answRef, status)
        | (sf, T.DivergingEntry(asub, answRef)) =>
            (sf(); added := true;
             T.DivergingEntry(asub, answRef))
      end


    (* we assume we alsways insert new things into the tree *)
    fun insertIntoTree (a, DAVars, DEVars, G , U, eqn, answRef, status) =
      let
        val (n, Tree) = Array.sub (indexArray, a)
        val sq = S.new()             (* sq = query substitution *)
        val DAEVars = compose (DEVars, DAVars)
        val Dq = emptyCtx()
        val n = I.ctxLength(G)
        val _ = makeCtx (n+1, DAEVars, Dq:ctx)
        val l = I.ctxLength(DAEVars)
        val _ = S.insert sq (1, (0, U))
        val GR = ((l, n+1), G, eqn, emptyAnswer(), !TableParam.stageCtr, status)
        val result = insert (Tree, (Dq, sq),
                             ((l, n+1), G, eqn, answRef, !TableParam.stageCtr, status))
      in
        case result of
          (sf, T.NewEntry(answRef)) =>
            (sf(); added := true;
             T.NewEntry(answRef))
        | (_, T.RepeatedEntry(asub, answRef, status)) =>
            T.RepeatedEntry(asub, answRef, status)
        | (sf, T.DivergingEntry(asub, answRef)) =>
            (sf(); added := true;
             T.DivergingEntry(asub, answRef))
      end

    fun answCheck (s', answRef, O) = answCheckVariant (s', answRef, O)

    fun updateTable () =
      let
        fun update [] Flag = Flag
          | update (answRef::AList) Flag =
            (let

              val l = length(T.solutions(answRef))
            in
              if (l = T.lookup(answRef)) then
                (* no new solutions were added in the previous stage *)
                update AList Flag
              else
                (* new solutions were added *)
                (T.updateAnswLookup (l, answRef);
                 update AList true)
            end)
        val Flag = update (!answList) false
        val r = (Flag orelse (!added))
      in
        added := false;
        r
      end

  in
    val reset = reset
    val callCheck = (fn (DAVars, DEVars, G, U, eqn, status) =>
                        callCheck(cidFromHead(I.targetHead U), DAVars, DEVars, G, U, eqn, status))

    val insertIntoTree = (fn (DAVars, DEVars, G, U, eqn, answRef, status) =>
                          insertIntoTree(cidFromHead(I.targetHead U), DAVars, DEVars,
                                         G, U, eqn, answRef, status))

    val answerCheck = answCheck

    val updateTable = updateTable

    val tableSize = (fn () => (length(!answList)))


    (* memberCtxS ((G,V), G', n) = bool

       if G |- V and |- G' ctx
          exists a V' in G s.t.  V'[^n]  is an instance of V
       then return true
         otherwise false
    *)
    fun memberCtx ((G,V), G') =
      let
        fun instanceCtx' ((G, V), I.Null, n) = NONE
          | instanceCtx' ((G, V), I.Decl(G', D' as I.Dec(_, V')), n) =
          if Match.instance(G, (V, I.id), (V', I.Shift n))
             then SOME(D')
           else instanceCtx' ((G,V), G',n+1)
      in
        instanceCtx' ((G,V), G', 1)
      end

  end (* local *)
end; (* functor MemoTable *)


