(* Printing *)
(* Author: Frank Pfenning *)
(* Modified: Jeff Polakow, Roberto Virga *)

functor Print ((*! structure IntSyn' : INTSYN !*)
               structure Whnf : WHNF
               (*! sharing Whnf.IntSyn = IntSyn' !*)
               structure Abstract : ABSTRACT
               (*! sharing Abstract.IntSyn = IntSyn' !*)
               structure Constraints : CONSTRAINTS
               (*! sharing Constraints.IntSyn = IntSyn' !*)
               structure Names : NAMES
               (*! sharing Names.IntSyn = IntSyn' !*)
               structure Formatter' : FORMATTER
               structure Symbol : SYMBOL)
  : PRINT =
struct

  (*! structure IntSyn = IntSyn' !*)
structure Formatter = Formatter'
 structure Tomega = Tomega

(* Externally visible parameters *)

val implicit = ref (false)              (* whether to print implicit arguments *)
val printInfix = ref (false)            (* if implicit is ref true, whether to print infix ops when possible *)
val printDepth = ref (NONE:int option)  (* limit on term depth to print *)
val printLength = ref (NONE:int option) (* limit on number of arguments to print *)
val noShadow = ref (false)              (* if true, don't print shadowed constants as "%const%" *)

local

  (* Shorthands *)
  structure I = IntSyn
  structure FX = Names.Fixity
  structure F = Formatter
  structure T = Tomega

  (* Disambiguation of block logic variable names *)
  val lvars : I.Block option ref list ref
            = ref nil
  fun lookuplvar (l) =
      let
        val _ = if (List.exists (fn r => r = l) (!lvars)) then () else lvars := !lvars @ [l]   (* speed improvment possible Tue Mar  1 13:27:04 2011 --cs *)
        fun find (r :: L) n =  if r = l then n else find L (n+1)
      in
        Int.toString (find (!lvars) 0)
      end


  val Str = F.String
  fun Str0 (s, n) = F.String0 n s
  fun sym (s) = Str0 (Symbol.sym s)

  fun nameOf (SOME(id)) = id
    | nameOf (NONE) = "_"

  (* fmtEVar (G, X) = "X", the name of the EVar X *)
  (* Effect: Names.evarName will assign a name if X does not yet have one *)
  fun fmtEVar (G, X) = Str0 (Symbol.evar (Names.evarName(G, X)))
  (* should probably be a new Symbol constructor for AVars -kw *)
  fun fmtAVar (G, X) = Str0 (Symbol.evar (Names.evarName(G, X) ^ "_"))

  (* isNil S = true iff S == Nil *)
  fun isNil (I.Nil) = true
    | isNil (I.App _) = false
    | isNil (I.SClo(S,_)) = isNil S

  (* subToSpine (depth, s) = S
     Invariants:
     If  G |- s : G', Gd  with  |Gd| = depth
     then G |- S : {{Gd}} C > C  for any C

     This is used to print
      G |- Xl[s] : A[s]  for  G', Gd |- Xl : A
     as
      G |- Xr @ S : A[s]  for  G' |- Xr : {{Gd}} A
     where Xr is the raised version of Xl.
     Xr is not actually created, just printed using the name of Xl.
  *)
  fun subToSpine (depth, s) =
      let fun sTS (I.Shift(k), S) =
              if k < depth
                then sTS (I.Dot (I.Idx (k+1), I.Shift(k+1)), S)
              else (* k >= depth *) S
            | sTS (I.Dot(I.Idx(k), s), S) =
                (* Eta violation, but probably inconsequential -kw *)
                sTS (s, I.App(I.Root(I.BVar(k), I.Nil), S))
            | sTS (I.Dot(I.Exp(U), s), S) =
                sTS (s, I.App(U, S))
      in
        sTS (s, I.Nil)
      end

  (* ArgStatus classifies the number of arguments to an operator *)
  datatype ArgStatus =
      TooFew
    | Exact of I.Spine
    | TooMany of I.Spine * I.Spine

  fun sclo' (TooFew, s) = TooFew
    | sclo' (Exact(S), s) = Exact (I.SClo(S,s))
    | sclo' (TooMany (S, S'), s) = TooMany (I.SClo (S, s), I.SClo (S', s))

  fun sclo'' (TooFew, s) = TooFew
    | sclo'' (Exact(S), s) = Exact (S)
    | sclo'' (TooMany (S, S'), s) = TooMany (S, I.SClo (S', s))

  (* dropImp (i, S, n) for n >= 1
     = TooFew            if |S| < i+n
     = Exact(S')         if n >= 1, |S| = i+n, S = _ @ S' and |S'| = n
                         if n = 0, |S| = _ @ S', |_| = i
     = TooMany(S', S'')  if n >=1, |S| > i+n, S = _ @ S' and |S'| > n,
                                              S' = S0 @ S'' and |S0| = n
  *)
  fun dropImp (0, S, 0) = Exact(S)
    | dropImp (0, S, n) = (* n >= 1 *)
      let fun checkArgNumber (I.Nil, 0) = Exact(S)
            | checkArgNumber (I.Nil, k) = TooFew
            | checkArgNumber (S' as I.App _, 0) = TooMany (S, S')
            | checkArgNumber (I.App(U,S'), k) = checkArgNumber (S', k-1)
            | checkArgNumber (I.SClo(S', s), k) = sclo'' (checkArgNumber (S', k), s)
      in
        checkArgNumber (S, n)
      end
    | dropImp (i, I.App(U,S), n) = dropImp (i-1, S, n)
    | dropImp (i, I.SClo(S,s), n) =
        sclo' (dropImp (i, S, n), s)
    | dropImp (i, I.Nil, n) = TooFew

  (* exceeded (n:int, b:bound) = true if n exceeds bound b *)
  fun exceeded (_,NONE) = false
    | exceeded (n:int,SOME(m:int)) = n >= m

  (* Type ctxt is the "left context" of an expression to be printed.
     It works as an accumulator and is used to decide whether to insert of parentheses
     or elide nested subexpressions.

     Ctxt (fixity, formats, length)
     is the "left context" of an expression to be printed.  When printed
     it will be the string prefixed to the string representing the
     current expression.

     fixity is the operator and precedence in effect,
     formats is the list of formats which make up the left context
     length is the length of the left context (used for printLength elision)
  *)
  datatype ctxt = Ctxt of FX.fixity * F.format list * int

  (* Type opargs represent the operator/arguments form of roots.

     OpArgs (fixity, formats, S)
     represents the printed form of a root expression H @ S:
      fixity is the fixity of H (possibly FX.Nonfix),
      formats is a list of formats for printing H (including surrounding breaks
         and whitespace),
      S is the spine of arguments.
      There may be additional argument in S which are ignored.

     EtaLong (U)
     represents an expression U' which had to be eta-expanded to U
     in order to supply enough arguments to a prefix, postfix, or infix operator
     so it can be printed.
  *)
  datatype opargs =
      OpArgs of FX.fixity * F.format list * I.Spine
    | EtaLong of I.Exp

  val noCtxt = Ctxt (FX.Prefix(FX.dec (FX.dec (FX.dec (FX.dec FX.minPrec)))), [], 0)
                                        (* empty left context *)

  val binderPrec = FX.dec (FX.dec (FX.dec FX.minPrec))
                                        (* braces and brackets as a prefix operator *)
  (* colon is of FX.minPrec-2, but doesn't occur in printing *)
  val arrowPrec = FX.dec FX.minPrec     (* arrow as infix operator *)
  val juxPrec = FX.inc FX.maxPrec       (* juxtaposition as infix operator *)

  (* arrow (V1, V2) = oa
     where oa is the operator/argument representation of V1 -> V2
  *)
  fun arrow (V1, V2) =
         OpArgs(FX.Infix(arrowPrec, FX.Right),
                [F.Break, sym "->", F.Space],
                I.App (V1, I.App(V2, I.Nil)))

  (* Nonfix corresponds to application and therefore has precedence juxPrex (which is maximal) *)
  val appCtxt = Ctxt (FX.Nonfix, [], 0)

  (* fixityCon (c) = fixity of c *)
  fun fixityCon (I.Const(cid)) = Names.getFixity (cid)
    | fixityCon (I.Skonst(cid)) = FX.Nonfix
    | fixityCon (I.Def(cid)) = Names.getFixity (cid)
    | fixityCon (I.NSDef(cid)) = Names.getFixity (cid)
    | fixityCon _ = FX.Nonfix (* BVar, FVar *)

  (* impCon (c) = number of implicit arguments to c *)
  fun impCon (I.Const(cid)) = I.constImp (cid)
    | impCon (I.Skonst(cid)) = I.constImp (cid)
    | impCon (I.Def(cid)) = I.constImp (cid)
    | impCon (I.NSDef(cid)) = I.constImp (cid)
    | impCon _ = 0                      (* BVar, FVar *)

  (* argNumber (fixity) = number of required arguments to head with fixity *)
  fun argNumber (FX.Nonfix) = 0
    | argNumber (FX.Infix _) = 2
    | argNumber (FX.Prefix _) = 1
    | argNumber (FX.Postfix _) = 1

  (* FIX: this is certainly not correct -kw *)
  fun fmtConstPath (f, Names.Qid (ids, id)) =
        F.HVbox (foldr (fn (id, fmt) => Str0 (Symbol.str (id))::sym "."::fmt)
                       [Str0 (f (id))] ids)

  fun parmDec (D::L, 1) = D
    | parmDec (D::L, j) = parmDec (L, j-1)

  fun parmName (cid, i) =
      let
        val (Gsome, Gblock) = I.constBlock (cid)
      in
        case parmDec (Gblock, i)
          of I.Dec (SOME(pname), _) => pname
           | I.Dec (NONE, _) => Int.toString i
      end

  fun projName (G, I.Proj (I.Bidx(k), i)) =
      let
        val I.BDec (SOME(bname), (cid, t)) = I.ctxLookup (G, k)
        (* names should have been assigned by invar
         iant, NONE imppossible *)
       in
         bname ^ "_" ^ parmName (cid, i)
       end
    | projName (G, I.Proj (I.LVar(r, _, (cid, t)), i)) =
      (* note: this obscures LVar identity! *)
      (* no longer Tue Mar  1 13:32:21 2011 -cs *)
         "_"  ^ parmName (cid, i)
    | projName (G, I.Proj (I.Inst iota, i)) =
       "*"    (* to be fixed --cs *)


  fun constQid (cid) =
      if !noShadow
      then Names.conDecQid (I.sgnLookup cid)
      else Names.constQid cid

    fun cidToFmt (cid) = F.String (Names.qidToString (Names.constQid cid))
    fun formatCids (nil) = nil
      | formatCids (cid::nil) = [cidToFmt cid]
      | formatCids (cid::cids) = cidToFmt cid
                                 :: F.Break :: F.String "|" :: F.Space
                                 :: formatCids cids

    fun formatWorlds (T.Worlds cids) =
        F.Hbox [F.String "(", F.HVbox (formatCids cids), F.String ")"]


    fun worldsToString (W) = F.makestring_fmt (formatWorlds W)

  (* fmtCon (c) = "c" where the name is assigned according the the Name table
     maintained in the names module.
     FVar's are printed with a preceding "`" (backquote) character
  *)
  fun fmtCon (G, I.BVar(n)) = Str0 (Symbol.bvar (Names.bvarName(G, n)))
    | fmtCon (G, I.Const(cid)) = fmtConstPath (Symbol.const, constQid (cid))
    | fmtCon (G, I.Skonst(cid)) = fmtConstPath (Symbol.skonst, constQid (cid))
    | fmtCon (G, I.Def(cid)) = fmtConstPath (Symbol.def, constQid (cid))
    | fmtCon (G, I.NSDef (cid)) = fmtConstPath (Symbol.def, constQid (cid))
    | fmtCon (G, I.FVar (name, _, _)) = Str0 (Symbol.fvar (name))
    | fmtCon (G, H as I.Proj (I.Bidx(k), i)) =
        Str0 (Symbol.const (projName (G, H)))
    | fmtCon (G, H as I.Proj (I.LVar(r as ref NONE, sk, (cid, t)), i)) =
        let
          val n = lookuplvar (r)
        in
          (* LVar fixed Sun Dec  1 11:36:55 2002 -cs *)
          fmtConstPath (fn l0 => Symbol.const ("#[" ^ l0 ^ n ^ "]" ^ projName (G, H)),
                        constQid (cid))
        end
    | fmtCon (G, I.FgnConst (cs, conDec)) =
        let
          (* will need to be changed if qualified constraint constant
             names are introduced... anyway, why should the user be
             allowed to shadow constraint constants? -kw *)
          val name = I.conDecName conDec
        in
          case (Names.constLookup (Names.Qid (nil, name)), !noShadow)
            of (SOME _, false) => (* the user has re-defined this name *)
                 Str0 (Symbol.const ("%" ^ name ^ "%"))
             | _ =>
                 Str0 (Symbol.const name)
        end

    (* evarArgs (G, d, X, s)
     formats X[s] by printing X @ S, where S is the substitution s in spine form.
     This is an implicit form of raising.
  *)
  fun evarArgs (G, d, X, s) =
      OpArgs (FX.Nonfix, [fmtEVar(G, X)],
              subToSpine (I.ctxLength(G), s))


  fun evarArgs' (G, d, X, s) =
      OpArgs (FX.Nonfix, [fmtAVar(G, X)],
              subToSpine (I.ctxLength(G), s))

  (* fst (S, s) = U1, the first argument in S[s] *)
  fun fst (I.App (U1, _), s) = (U1, s)
    | fst (I.SClo (S, s'), s) = fst (S, I.comp (s', s))

  (* snd (S, s) = U2, the second argument in S[s] *)
  fun snd (I.App (U1, S), s) = fst (S, s)
    | snd (I.SClo (S, s'), s) = snd (S, I.comp (s', s))

  (* elide (l) = true  iff  l exceeds the optional printLength bound *)
  fun elide (l) = case !printLength
                     of NONE => false
                      | SOME(l') => (l > l')

  val ldots = sym "..."

  (* addots (l) = true  iff  l is equal to the optional printLength bound *)
  fun addots (l) = case !printLength
                     of NONE => false
                      | SOME(l') => (l = l')

  (* parens ((fixity', fixity), fmt) = fmt'
     where fmt' contains additional parentheses when the precedence of
     fixity' is greater or equal to that of fixity, otherwise it is unchanged.
  *)
  fun parens ((fixity', fixity), fmt) =
      if FX.leq (FX.prec(fixity), FX.prec(fixity'))
        then F.Hbox [sym "(", fmt, sym ")"]
      else fmt

  (* eqFix (fixity, fixity') = true iff fixity and fixity' have the same precedence
     Invariant: only called when precedence comparison is necessary to resolve
                the question if parentheses should be added
  *)
  fun eqFix (FX.Infix(p,FX.Left), FX.Infix(p',FX.Left)) = (p = p')
    | eqFix (FX.Infix(p,FX.Right), FX.Infix(p', FX.Right)) = (p = p')
      (* Infix(_,None) should never be asked *)
    | eqFix (FX.Prefix(p), FX.Prefix(p')) = (p = p')
    | eqFix (FX.Postfix(p), FX.Postfix(p')) = (p = p')
      (* Nonfix should never be asked *)
    | eqFix _ = false

  (* addAccum (fmt, fixity, accum) = fmt'
     Extend the current "left context" with operator fixity
     and format list accum by fmt.

     This is not very efficient, since the accumulator is copied
     for right associative or prefix operators.
  *)
  fun addAccum (fmt, _, nil) = fmt
    | addAccum (fmt, FX.Infix(_, FX.Left), accum) = F.HVbox ([fmt] @ accum)
    | addAccum (fmt, FX.Infix(_, FX.Right), accum) = F.HVbox (accum @ [fmt])
    | addAccum (fmt, FX.Prefix _, accum) = F.HVbox (accum @ [fmt])
    | addAccum (fmt, FX.Postfix _, accum) = F.HVbox ([fmt] @ accum)
    (* FX.Infix(None,_), FX.Nonfix should never arise *)

  (* aa (ctx, fmt) = fmt'
     Extend the current "left context" by fmt.
  *)
  fun aa (Ctxt (fixity, accum, l), fmt) = addAccum (fmt, fixity, accum)

  (* fmtUni (L) = "L" *)
  fun fmtUni (I.Type) = sym "type"
    | fmtUni (I.Kind) = sym "kind"   (* impossible, included for robustness *)

  (* fmtExpW (G, d, ctx, (U, s)) = fmt

     format the expression U[s] at printing depth d and add it to the left context
     ctx.

     Invariants:
       G is a "printing context" (names in it are unique, but
            types may be incorrect) approximating G'
       G'' |- U : V   G' |- s : G''  (so  G' |- U[s] : V[s])
       (U,s) in whnf
  *)
  fun fmtExpW (G, d, ctx, (I.Uni(L), s)) = aa (ctx, fmtUni(L))
    | fmtExpW (G, d, ctx, (I.Pi((D as I.Dec(_,V1),P),V2), s)) =
      (case P (* if Pi is dependent but anonymous, invent name here *)
         of I.Maybe => let
                         val D' = Names.decLUName (G, D) (* could sometimes be EName *)
                       in
                         fmtLevel (I.Decl (G, D'), (* I.decSub (D', s) *)
                                   d, ctx, (braces (G, d, ((D',V2), s)),
                                            I.dot1 s))
                       end
          | I.Meta => let
                         val D' = Names.decLUName (G, D)
                       in
                         fmtLevel (I.Decl (G, D'), (* I.decSub (D', s) *)
                                   d, ctx, (braces (G, d, ((D',V2), s)),
                                            I.dot1 s))
                       end
          | I.No => fmtLevel (I.Decl (G, D), (* I.decSub (D, s) *)
                              d, ctx, (arrow(I.EClo(V1,I.shift), V2), I.dot1 s)))
    | fmtExpW (G, d, ctx, (I.Pi((D as I.BDec _, P), V2), s)) =
      let
        val D' = Names.decLUName (G, D)
      in
         fmtLevel (I.Decl (G, D'), d, ctx, (braces (G, d, ((D', V2), s)),
                                            I.dot1 s))
      end
    (* -bp *)
    | fmtExpW (G, d, ctx, (I.Pi((D as I.ADec _, P), V2), s)) =
      let
(*      val D' = Names.decLUName (G, D) *)
        val braces = OpArgs(FX.Prefix(binderPrec),
                            [sym "[" , sym "_", sym "]", F.Break],
                IntSyn.App(V2, IntSyn.Nil))
      in
         fmtLevel (I.Decl (G, D), d, ctx, (braces, I.dot1 s))
      end

    | fmtExpW (G, d, ctx, (U as I.Root R, s)) = (* s = id *)
         fmtOpArgs (G, d, ctx, opargs (G, d, R), s)
    (* I.Redex not possible *)
    | fmtExpW (G, d, ctx, (I.Lam(D, U), s)) =
      let
        val D' = Names.decLUName (G, D)
      in
        fmtLevel (I.Decl (G, D'), (* I.decSub (D', s) *)
                  d, ctx, (brackets (G, d, ((D', U), s)), I.dot1 s))
      end
    | fmtExpW (G, d, ctx, (X as I.EVar _, s)) =
      (* assume dereferenced during whnf *)
      if !implicit then aa (ctx, F.HVbox (fmtEVar(G,X)::fmtSub(G,d,s)))
      else fmtOpArgs (G, d, ctx, evarArgs (G, d, X, s), I.id)

    | fmtExpW (G, d, ctx, (X as I.AVar _, s)) =
      (* assume dereferenced during whnf *)
      if !implicit then aa (ctx, F.HVbox (fmtAVar(G,X)::fmtSub(G,d,s)))
      else fmtOpArgs (G, d, ctx, evarArgs' (G, d, X, s), I.id)

    | fmtExpW (G, d, ctx, (U as I.FgnExp csfe, s)) =
      fmtExp (G, d, ctx, (I.FgnExpStd.ToInternal.apply csfe (), s))
    (* I.EClo not possible for Whnf *)

  (* for internal printing *)
  (* opargsImplicit (G, (C, S)) = oa
     converts C @ S into operator/arguments form, showing all implicit
     arguments.  In this form, infix, prefix, and postfix declarations
     are ignored.
  *)
  and opargsImplicit (G, d, (C,S)) = OpArgs (FX.Nonfix, [fmtCon(G,C)], S)

  (* for flit printing -jcreed 6/2005 *)
  (* opargsImplicit (G, (C, S)) = oa
     converts C @ S into operator/arguments form, showing all implicit
     arguments.  In this form, infix declarations are obeyed. It is an
     error to call this function if an infix declaration has been made for
     a term which has more than two arguments. (This could have happened if the term
     had two explicit arguments and further implicit arguments)

     In other words, it is an error if an infix declaration had any
     implicit arguments.
  *)
  and opargsImplicitInfix (G, d, R as (C,S)) =
      let
          val fixity = fixityCon C
      in
          case fixity of
              FX.Infix _ => opargsExplicit(G, d, R) (* Can't have implicit arguments by invariant *)
            | _          => OpArgs (FX.Nonfix, [fmtCon (G, C)], S)
      end

  (* for external printing *)
  (* opargsExplicit (G, (C, S)) = oa
     converts C @ S into operator/arguments form, eliding implicit
     arguments and taking operator fixity declarations into account.
     G |- C @ S (no substitution involved)
  *)
  and opargsExplicit (G, d, R as (C,S)) =
      let
        val opFmt = fmtCon (G, C)
        val fixity = fixityCon C
        fun oe (Exact(S')) =
            (case fixity
               of FX.Nonfix => OpArgs (FX.Nonfix, [opFmt], S')
                | FX.Prefix _ => OpArgs (fixity, [opFmt, F.Break], S')
                | FX.Postfix _ => OpArgs (fixity, [F.Break, opFmt], S')
                | FX.Infix _ => OpArgs (fixity, [F.Break, opFmt, F.Space], S'))
          | oe (TooFew) = EtaLong (Whnf.etaExpandRoot (I.Root R))
          | oe (TooMany (S', S'')) =
            (* extra arguments to infix operator *)
            (* S' - all non-implicit arguments *)
            (* S'' - extra arguments *)
            let
              val opFmt' = fmtOpArgs (G, d, noCtxt, oe (Exact (S')), I.id)
            in
              (* parens because juxtaposition has highest precedence *)
              (*
                 could be redundant for prefix or postfix operators, but
                 include anyway to avoid misreading output
              *)
              OpArgs (FX.Nonfix, [F.Hbox [sym "(", opFmt', sym ")"]], S'')
            end
      in
        oe (dropImp (impCon C, S, argNumber fixity))
      end

  (* opargs (G, d, (C, S)) = oa
     converts C @ S to operator/arguments form, depending on the
     value of !implicit
  *)
  and opargs (G, d, R) =
      if !implicit then if !printInfix then opargsImplicitInfix (G, d, R)
                        else opargsImplicit (G, d, R)
      else opargsExplicit (G, d, R)

  (* fmtOpArgs (G, d, ctx, oa, s) = fmt
     format the operator/arguments form oa at printing depth d and add it
     to the left context ctx.

     G is a printing context approximating G', and G' |- oa[s] is valid.
  *)
  and fmtOpArgs (G, d, ctx, oa as OpArgs(_, opFmts, S'), s) =
      if isNil S'
        then aa (ctx, List.hd opFmts)   (* opFmts = [fmtCon(G,C)] *)
      else fmtLevel (G, d, ctx, (oa, s))
    | fmtOpArgs (G, d, ctx, EtaLong(U'), s) =
        fmtExpW (G, d, ctx, (U', s))

  (* fmtSub (G, d, s) = fmt
     format substitution s at printing depth d and printing context G.

     This is used only when !implicit = true, that is, when the internal
     representation is printed.  Note that a substitution is not reparsable
  *)
  and fmtSub (G, d, s) = Str "[" :: fmtSub' (G, d, 0, s)
  and fmtSub' (G, d, l, s) = if elide l then [ldots] else fmtSub'' (G, d, l, s)
  and fmtSub'' (G, d, l, I.Shift(k)) = [Str ("^" ^ Int.toString k), Str "]"]
    | fmtSub'' (G, d, l, I.Dot(I.Idx(k), s)) =
        Str (Names.bvarName (G, k)) :: Str "." :: F.Break :: fmtSub' (G, d, l+1, s)
    | fmtSub'' (G, d, l, I.Dot(I.Exp(U), s)) =
        fmtExp (G, d+1, noCtxt, (U, I.id))
        :: Str "." :: F.Break :: fmtSub' (G, d, l+1, s)

  (* fmtExp (G, d, ctx, (U, s)) = fmt
     format or elide U[s] at printing depth d and add to the left context ctx.

     G is a printing context approximation G' and G' |- U[s] is valid.
  *)
  and fmtExp (G, d, ctx, (U, s)) =
         if exceeded(d,!printDepth)
            then sym "%%"
            else fmtExpW (G, d, ctx, Whnf.whnf (U, s))

  (* fmtSpine (G, d, l, (S, s)) = fmts
     format spine S[s] at printing depth d, printing length l, in printing
     context G which approximates G', where G' |- S[s] is valid
  *)
  and fmtSpine (G, d, l, (I.Nil, _)) = []
    | fmtSpine (G, d, l, (I.SClo (S, s'), s)) =
         fmtSpine (G, d, l, (S, I.comp(s',s)))
    | fmtSpine (G, d, l, (I.App(U, S), s)) =
         if elide (l) then []           (* necessary? *)
         else if addots (l) then [ldots]
              else fmtExp (G, d+1, appCtxt, (U, s))
                   :: fmtSpine' (G, d, l, (S, s))

  (* fmtSpine' (G, d, l, (S, s)) = fmts
     like fmtSpine, but will add leading "Break" and increment printing length
  *)
  and fmtSpine' (G, d, l, (I.Nil, _)) = []
    | fmtSpine' (G, d, l, (I.SClo (S, s'), s)) =
        fmtSpine' (G, d, l, (S, I.comp(s', s)))
    | fmtSpine' (G, d, l, (S, s)) =
        F.Break :: fmtSpine (G, d, l+1, (S, s))

  (* fmtLevel (G, d, ctx, (oa, s)) = fmt

     format operator/arguments form oa[s] at printing depth d and add the result
     to the left context ctx.

     This is the main function flattening out infix/prefix/postfix operator
     sequences.  It compares the fixity of the operator of the current left
     context with the operator at the head of the current operator/arguments
     form and decides how to extend the accumulator and whether to insert
     parentheses.
  *)
  and fmtLevel (G, d, Ctxt (fixity', accum, l),
                (OpArgs (fixity as FX.Nonfix, fmts, S), s)) =
      let
        val atm = fmtSpine (G, d, 0, (S,s))
        (* atm must not be empty, otherwise bug below *)
      in
        (* F.HVbox doesn't work if last item of HVbox is F.Break *)
        addAccum (parens ((fixity',fixity), F.HVbox (fmts @ [F.Break] @ atm)),
                  fixity', accum)
        (* possible improvement along the following lines: *)
        (*
           if (#2 (F.Width (F.Hbox (fmts)))) < 4
           then F.Hbox [F.Hbox(fmts), F.HVbox0 1 1 1 atm]
           else ...
        *)
      end

    | fmtLevel (G, d, Ctxt (fixity', accum, l),
                (OpArgs (fixity as (FX.Infix(p, FX.Left)), fmts, S), s)) =
      let val accMore = eqFix (fixity, fixity')
        val rhs = if accMore andalso elide(l) then []
                  else if accMore andalso addots(l) then fmts @ [ldots]
                       else fmts @ [fmtExp (G, d+1, Ctxt (FX.Infix(p,FX.None),nil,0),
                                            snd (S, s))]
      in
        if accMore
          then fmtExp (G, d, Ctxt (fixity, rhs @ accum, l+1), fst (S, s))
        else let
               val both = fmtExp (G, d, Ctxt (fixity, rhs, 0), fst (S, s))
             in
               addAccum (parens ((fixity',fixity), both), fixity', accum)
             end
      end

    | fmtLevel (G, d, Ctxt (fixity', accum, l),
                (OpArgs (fixity as FX.Infix(p, FX.Right), fmts, S), s)) =
      let
          val accMore = eqFix (fixity, fixity')
          val lhs = if accMore andalso elide(l) then []
                    else if accMore andalso addots(l) then [ldots] @ fmts
                         else [fmtExp (G, d+1, Ctxt (FX.Infix(p,FX.None),nil,0), fst(S, s))] @ fmts
      in
        if accMore
          then fmtExp (G, d, Ctxt (fixity, accum @ lhs, l+1), snd (S, s))
        else let
               val both = fmtExp (G, d, Ctxt (fixity, lhs, 0), snd (S, s))
             in
               addAccum (parens ((fixity', fixity), both), fixity', accum)
             end
      end

    | fmtLevel (G, d, Ctxt (fixity', accum, l),
                (OpArgs(fixity as (FX.Infix(_,FX.None)), fmts, S), s)) =
      let
          val lhs = fmtExp (G, d+1, Ctxt (fixity, nil, 0), fst(S, s))
          val rhs = fmtExp (G, d+1, Ctxt (fixity, nil, 0), snd(S, s))
      in
        addAccum (parens ((fixity',fixity),
                          F.HVbox ([lhs] @ fmts @ [rhs])), fixity', accum)
      end

    | fmtLevel (G, d, Ctxt (fixity', accum, l),
                (OpArgs (fixity as (FX.Prefix _), fmts, S), s)) =
      let
          val accMore = eqFix (fixity', fixity)
          val pfx = if accMore andalso elide(l) then []
                    else if accMore andalso addots(l) then [ldots, F.Break]
                         else fmts
      in
        if accMore
          then fmtExp (G, d, Ctxt (fixity, accum @ pfx, l+1), fst(S, s))
        else let
               val whole = fmtExp (G, d, Ctxt (fixity, pfx, 0), fst (S, s))
             in
               addAccum (parens ((fixity',fixity), whole), fixity', accum)
             end
      end

    | fmtLevel (G, d, Ctxt (fixity', accum, l),
                (OpArgs (fixity as (FX.Postfix _), fmts, S), s)) =
      let
          val accMore = eqFix (fixity', fixity)
          val pfx = if accMore andalso elide(l) then []
                    else if accMore andalso addots(l) then [F.Break, ldots]
                         else fmts
      in
        if accMore
          then fmtExp (G, d, Ctxt (fixity, pfx @ accum, l+1), fst(S, s))
        else let
               val whole = fmtExp (G, d, Ctxt (fixity, pfx, 0), fst (S, s))
             in
               addAccum (parens ((fixity', fixity), whole), fixity', accum)
             end
      end

  (* braces (G, d, ((D, V), s)) = oa
     convert declaration D[s] as a prefix pi-abstraction into operator/arguments
     form with prefix "{D}" and argument V at printing depth d in printing
     context G approximating G'.

     Invariants:
      G' |- D[s] decl
      G' |- V : L  [NOTE: s does not apply to V!]
  *)
  and braces (G, d, ((D,V), s)) =
         OpArgs(FX.Prefix(binderPrec),
                [sym "{" , fmtDec (G, d, (D,s)), sym "}", F.Break],
                IntSyn.App(V, IntSyn.Nil))

  (* brackets (G, d, ((D, U), s)) = oa
     convert declaration D[s] as a prefix lambda-abstraction into operator/arguments
     form with prefix "[D]" and argument U at printing depth d in printing
     context G approximating G'.

     Invariants:
      G' |- D[s] decl
      G' |- U : V  [NOTE: s does not apply to U!]
  *)
  and brackets (G, d, ((D,U), s)) =
         OpArgs(FX.Prefix(binderPrec),
                [sym "[" , fmtDec (G, d, (D,s)), sym "]", F.Break],
                IntSyn.App(U, IntSyn.Nil))

  (* fmtDec (G, d, (D, s)) = fmt
     format declaration D[s] at printing depth d in printing context G approximating G'.

     Invariants:
      G' |- D[s] decl
  *)
  and fmtDec (G, d, (I.Dec (x, V), s)) =
      F.HVbox [Str0 (Symbol.bvar (nameOf (x))), sym ":", fmtExp (G, d+1, noCtxt, (V,s))]
      (* alternative with more whitespace *)
      (* F.HVbox [Str0 (Symbol.bvar (nameOf (x))), F.Space, sym ":", F.Break,
                  fmtExp (G, d+1, noCtxt, (V,s))]
      *)
    | fmtDec (G, d, (I.BDec (x, (cid, t)), s)) =
      let
        val (Gsome, Gblock) = I.constBlock cid
      in
        F.HVbox ([Str0 (Symbol.const (nameOf (x))), sym ":"]
                 @ fmtDecList' (G, (Gblock, I.comp (t, s))))
      end
    | fmtDec (G, d, (I.ADec (x, _), s)) =
      F.HVbox [Str0 (Symbol.bvar (nameOf (x))), sym ":_"]
     | fmtDec (G, d, (I.NDec (SOME name), s)) =
      F.HVbox [ sym name]
     (* alternative with more whitespace *)
      (* F.HVbox [Str0 (Symbol.bvar (nameOf (x))), F.Space, sym ":", F.Break,
                  fmtExp (G, d+1, noCtxt, (V,s))]
      *)
  and fmtDecList' (G0, (nil, s)) = nil
    | fmtDecList' (G0, (D::nil, s)) =
        sym "{" :: fmtDec (G0, 0, (D, s)) :: sym "}" :: nil
    | fmtDecList' (G0, (D::L, s)) =
        sym "{" :: fmtDec (G0, 0, (D, s)) :: sym "}" :: F.Break
        :: fmtDecList' (I.Decl (G0, D), (L, I.dot1 s))

  fun skipI (0, G, V) = (G, V)
    | skipI (i, G, I.Pi ((D, _), V)) = skipI (i-1, I.Decl (G, Names.decEName (G, D)), V)

  fun skipI2 (0, G, V, U) = (G, V, U)
    | skipI2 (i, G, I.Pi ((D, _), V), I.Lam (D', U)) =
        skipI2 (i-1, I.Decl (G, Names.decEName (G, D')), V, U)

  fun ctxToDecList (I.Null, L) = L
    | ctxToDecList (I.Decl (G, D), L) = ctxToDecList (G, D::L)

  fun fmtDecList (G0, nil) = nil
    | fmtDecList (G0, D::nil) =
        sym"{"::fmtDec (G0, 0, (D, I.id))::sym"}"::nil
    | fmtDecList (G0, D::L) =
        sym"{"::fmtDec (G0, 0, (D, I.id))::sym"}"::F.Break
        ::fmtDecList (I.Decl (G0, D), L)

  (* Assume unique names are already assigned in G0 and G! *)
  fun fmtCtx (G0, G) = fmtDecList (G0, ctxToDecList (G, nil))


  fun fmtBlock (I.Null, Lblock)=
        [sym "block", F.Break] @ (fmtDecList (I.Null, Lblock))
    | fmtBlock (Gsome, Lblock) =
        [F.HVbox ([sym "some", F.Space] @ (fmtCtx (I.Null, Gsome))),
         F.Break,
         F.HVbox ([sym "block", F.Space] @ (fmtDecList (Gsome, Lblock)))]

  (* fmtConDec (hide, condec) = fmt
     formats a constant declaration (which must be closed and in normal form)

     This function prints the quantifiers and abstractions only if hide = false.
  *)
  fun fmtConDec (hide, condec as I.ConDec (_, _, imp, _, V, L)) =
      let
        val qid = Names.conDecQid condec
        val _ = Names.varReset IntSyn.Null
        val (G, V) = if hide then skipI (imp, I.Null, V) else (I.Null, V)
        val Vfmt = fmtExp (G, 0, noCtxt, (V, I.id))
      in
        F.HVbox [fmtConstPath (Symbol.const, qid), F.Space, sym ":", F.Break, Vfmt, sym "."]
      end
    | fmtConDec (hide, condec as I.SkoDec (_, _, imp, V, L)) =
      let
        val qid = Names.conDecQid condec
        val _ = Names.varReset IntSyn.Null
        val (G, V) = if hide then skipI (imp, I.Null, V) else (I.Null, V)
        val Vfmt = fmtExp (G, 0, noCtxt, (V, I.id))
      in
        F.HVbox [sym "%skolem", F.Break, fmtConstPath (Symbol.skonst, qid), F.Space,
                 sym ":", F.Break, Vfmt, sym "."]
      end
    | fmtConDec (hide, condec as I.BlockDec (_, _, Gsome, Lblock)) =
      let
        val qid = Names.conDecQid condec
        val _ = Names.varReset IntSyn.Null
      in
        F.HVbox ([sym "%block", F.Break, fmtConstPath (Symbol.label, qid), F.Space,
                 sym ":", F.Break] @ (fmtBlock (Gsome, Lblock))  @ [sym "."])
      end
    | fmtConDec (hide, condec as I.BlockDef (_, _, W)) =
      let
        val qid = Names.conDecQid condec
        val _ = Names.varReset IntSyn.Null
      in
        F.HVbox ([sym "%block", F.Break, fmtConstPath (Symbol.label, qid), F.Space,
                 sym "=", F.Break] @ ( formatWorlds (T.Worlds W) :: [sym "."]))
      end
    | fmtConDec (hide, condec as I.ConDef (_, _, imp, U, V, L, _)) =
      (* reset variable names in between to align names of type V and definition U *)
      let
        val qid = Names.conDecQid condec
        val _ = Names.varReset IntSyn.Null
        val (G, V, U) = if hide then skipI2 (imp, I.Null, V, U) else (I.Null, V, U)
        val Vfmt = fmtExp (G, 0, noCtxt, (V, I.id))
        (* val _ = Names.varReset () *)
        val Ufmt = fmtExp (G, 0, noCtxt, (U, I.id))
      in
        F.HVbox [fmtConstPath (Symbol.def, qid), F.Space, sym ":", F.Break,
                         Vfmt, F.Break,
                         sym "=", F.Space,
                         Ufmt, sym "."]
(* removed, when abbreviations where introduced. -- cs Mon Jun  7 16:03:30 EDT 1999
        F.Vbox0 0 1 [F.HVbox [Str0 (Symbol.def (name)), F.Space, sym ":", F.Break,
                         Vfmt, F.Break,
                         sym "=", F.Space,
                         Ufmt, sym "."],
                F.Break,
                F.HVbox [sym "%strict ", Str0 (Symbol.def (name)), sym "."]]
*)      end
    | fmtConDec (hide, condec as I.AbbrevDef (_, _, imp, U, V, L)) =
      (* reset variable names in between to align names of type V and definition U *)
      let
        val qid = Names.conDecQid condec
        val _ = Names.varReset IntSyn.Null
        val (G, V, U) = if hide then skipI2 (imp, I.Null, V, U) else (I.Null, V, U)
        val Vfmt = fmtExp (G, 0, noCtxt, (V, I.id))
        (* val _ = Names.varReset () *)
        val Ufmt = fmtExp (G, 0, noCtxt, (U, I.id))
      in
        F.HVbox [fmtConstPath (Symbol.def, qid), F.Space, sym ":", F.Break,
                         Vfmt, F.Break,
                         sym "=", F.Space,
                         Ufmt, sym "."]
(* removed, when abbreviations where introduced. -- cs Mon Jun  7 16:03:30 EDT 1999
        F.Vbox0 0 1 [F.HVbox [Str0 (Symbol.def (name)), F.Space, sym ":", F.Break,
                         Vfmt, F.Break,
                         sym "=", F.Space,
                         Ufmt, sym "."],
                F.Break,
                F.HVbox [sym "%nonstrict ", Str0 (Symbol.def (name)), sym "."]]
*)      end

  fun fmtCnstr (I.Solved) = [Str "Solved Constraint"]
    | fmtCnstr (I.Eqn (G, U1, U2)) =
        let
          val G' = Names.ctxLUName G
        in
          [F.HVbox [fmtExp (G', 0, noCtxt, (U1, I.id)),
                    F.Break, sym "=", F.Space,
                    fmtExp (G', 0, noCtxt, (U2, I.id))]]
        end
    | fmtCnstr (I.FgnCnstr (csfc as (cs, _))) =
        let
          fun fmtExpL (nil) = [Str "Empty Constraint"]
            | fmtExpL ((G, U) :: nil) =
                [fmtExp (Names.ctxLUName G, 0, noCtxt, (U, I.id))]
            | fmtExpL ((G,U) :: expL) =
                [fmtExp (Names.ctxLUName G, 0, noCtxt, (U, I.id)), Str ";", F.Break] @ fmtExpL expL
        in
          fmtExpL (I.FgnCnstrStd.ToInternal.apply csfc ())
        end

  fun fmtCnstrL (nil) = [Str "Empty Constraint"]
    | fmtCnstrL (ref Cnstr :: nil) = (fmtCnstr Cnstr) @ [Str "."]
    | fmtCnstrL (ref Cnstr :: cnstrL) =
        (fmtCnstr Cnstr) @ [Str ";", F.Break] @ (fmtCnstrL cnstrL)


  (* fmtNamedEVar, fmtEVarInst and evarInstToString are used to print
     instantiations of EVars occurring in queries.  To that end, a list of
     EVars paired with their is passed, thereby representing a substitution
     for logic variables.

     We always raise AVars to the empty context.
  *)
  fun abstractLam (I.Null, U) = U
    | abstractLam (I.Decl (G, D), U) = abstractLam (G, I.Lam (D, U))

  fun fmtNamedEVar (U as I.EVar(_,G,_,_), name) =
      let
        val U' = abstractLam (G, U)
      in
        F.HVbox [Str0 (Symbol.evar (name)), F.Space, sym "=", F.Break,
                 fmtExp (I.Null, 0, noCtxt, (U', I.id))]
      end
    | fmtNamedEVar (U, name) = (* used for proof term variables in queries *)
      F.HVbox [Str0 (Symbol.evar (name)), F.Space, sym "=", F.Break,
               fmtExp (I.Null, 0, noCtxt, (U, I.id))]

  fun fmtEVarInst (nil) = [Str "Empty Substitution"]
    | fmtEVarInst ((U,name)::nil) = [fmtNamedEVar (U, name)]
    | fmtEVarInst ((U,name)::Xs) =
        fmtNamedEVar (U, name) :: Str ";" :: F.Break :: fmtEVarInst Xs

  (* collectEVars and collectConstraints are used to print constraints
     associated with EVars in a instantiation of variables occurring in queries.
  *)
  fun collectEVars (nil, Xs) = Xs
    | collectEVars ((U,_)::Xnames, Xs) =
        collectEVars (Xnames, Abstract.collectEVars (I.Null, (U, I.id), Xs))

  fun eqCnstr r1 r2 = (r1 = r2)

  fun mergeConstraints (nil, cnstrs2) = cnstrs2
    | mergeConstraints (cnstr::cnstrs1, cnstrs2) =
        if List.exists (eqCnstr cnstr) cnstrs2
          then mergeConstraints (cnstrs1, cnstrs2)
        else cnstr::(mergeConstraints (cnstrs1, cnstrs2))

  fun collectConstraints (nil) = nil
    | collectConstraints (I.EVar(ref(NONE),_,_,cnstrs) :: Xs) =
        mergeConstraints (Constraints.simplify (!cnstrs),
                          collectConstraints Xs)
    | collectConstraints (_ :: Xs) = collectConstraints (Xs)

in

  (* In the functions below, G must be a "printing context", that is,
     (a) unique names must be assigned to each declaration which may
         actually applied in the scope (typically, using Names.decName)
     (b) types need not be well-formed, since they are not used
  *)
  fun formatDec (G, D) = fmtDec (G, 0, (D, I.id))
  fun formatDecList (G, D) = F.HVbox (fmtDecList (G, D))
  fun formatDecList' (G, (D,s)) = F.HVbox (fmtDecList' (G, (D, s)))
  fun formatExp (G, U) = fmtExp (G, 0, noCtxt, (U, I.id))
  fun formatSpine (G, S) = fmtSpine (G, 0, 0, (S, I.id))
  fun formatConDec (condec) = fmtConDec (false, condec)
  fun formatConDecI (condec) = fmtConDec (true, condec)
  fun formatCnstr (Cnstr) = F.Vbox0 0 1 (fmtCnstr Cnstr)
  fun formatCnstrs (cnstrL) = F.Vbox0 0 1 (fmtCnstrL cnstrL)
  fun formatCtx (G0, G) = F.HVbox (fmtCtx (G0, G))      (* assumes G0 and G are named *)

  fun decToString (G, D) = F.makestring_fmt (formatDec (G, D))
  fun expToString (G, U) = F.makestring_fmt (formatExp (G, U))
  fun conDecToString (condec) = F.makestring_fmt (formatConDec (condec))
  fun cnstrToString (Cnstr) = F.makestring_fmt (formatCnstr Cnstr)
  fun cnstrsToString (cnstrL) = F.makestring_fmt (formatCnstrs cnstrL)
  fun ctxToString (G0, G) = F.makestring_fmt (formatCtx (G0, G))

  fun evarInstToString Xnames =
        F.makestring_fmt (F.Hbox [F.Vbox0 0 1 (fmtEVarInst Xnames), Str "."])


  fun evarCnstrsToStringOpt Xnames =
      let
        val Ys = collectEVars (Xnames, nil)     (* collect EVars in instantiations *)
        val cnstrL = collectConstraints Ys
      in
        case cnstrL
          of nil => NONE
           | _ => SOME (cnstrsToString (cnstrL))
      end

  fun printSgn () =
      IntSyn.sgnApp (fn (cid) => (print (F.makestring_fmt (formatConDecI (IntSyn.sgnLookup cid)));
                                  print "\n"))

    val formatWorlds = formatWorlds
    val worldsToString = worldsToString


end  (* local ... *)

end  (* functor Print *)
