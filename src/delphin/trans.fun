(* Translator from Delphin external syntax to Delphin internal syntax *)
(* Author:  Carsten Schuermann *)


functor Trans (structure DextSyn' : DEXTSYN) (* : TRANS *) =

struct

  structure DextSyn = DextSyn'
  structure D = DextSyn'

  structure L = Lexer
  structure I = IntSyn
  structure LS = Stream
  structure T = Tomega
  structure TA = TomegaAbstract

  exception Error of string
  local

    datatype Internal =
      Empty
    | Const of int * int
    | Type of int

    val maxCid = Global.maxCid
    val internal = Array.array (maxCid+1, Empty)
        : Internal Array.array
    (* Invariant   for each cid which has been internalize out of a block,
       internal(cid) = Const(n, i), where n is the number of some variables and
       i is the projection index
       for each type family
       internal(cid) = Type (cid'), where cid' is the orginial type family.
    *)



   (* checkEOF f = r

      Invariant:
      If   f is the end of stream
      then r is a region

      Side effect: May raise Parsing.Error
    *)

    fun checkEOF (LS.Cons ((L.EOF, r), s')) = r (* region information useless
                                                   since it only refers to string --cs *)
      | checkEOF (LS.Cons ((t, r), _))  =
          Parsing.error (r, "Expected `}', found " ^ L.toString t)
         (* Note that this message is inapplicable when we use
            checkEOF in stringToterm --rf *)




    (* stringToDec s = dec

       Invariant:
       If   s is a string representing a declaration,
       then dec is the result of parsing it
       otherwise Parsing.error is raised.
    *)
    fun stringTodec s =
      let
        val f = LS.expose (L.lexStream (TextIO.openString s))
        val ((x, yOpt), f') = ParseTerm.parseDec' f
        val r2 = checkEOF f'
        val dec = (case yOpt            (* below use region arithmetic --cs !!!  *)
                     of NONE => ReconTerm.dec0 (x, r2)
                      | SOME y => ReconTerm.dec (x, y, r2))
      in
        dec
      end



    fun stringToblocks s =
      let
        val f = LS.expose (L.lexStream (TextIO.openString s))
        val (dl, f') = ParseTerm.parseCtx' f
      in
        dl
      end

    (* stringToWorlds s = W

       Invariant:
       If   s is a string representing an expression,
       then W is the result of parsing it
       otherwise Parsing.error is raised.
    *)
    fun stringToWorlds s =
        let
          val f = LS.expose (L.lexStream (TextIO.openString s))
          val (t, f') = ParseTerm.parseQualIds' f
          val r2 = checkEOF f'
        in
          t
        end



    (* closure (G, V) = V'

       Invariant:
       {G}V = V'
    *)
    fun closure (I.Null, V) = V
      | closure (I.Decl (G, D), V) =
          closure (G, I.Pi ((D, I.Maybe), V))

    (* internalizeBlock  (n, G, Vb, S) (L2, s) = ()

       Invariant:
       If   |- G ctx                the context of some variables
       and  G |- Vb :  type         the type of the block
       and  G |- L1, L2 decs
       and  G1, L1 |- L2 decs       block declarations still to be traversed
       and  G, b:Vb |- s : G1, L1
       and  n is the current projection
       then internalizeBlock adds new declarations into the signature that
              correspond to the block declarations.
    *)
    fun internalizeBlock _ (nil, _) = ()
      | internalizeBlock (n, G, Vb, S) (I.Dec (SOME name, V) :: L2, s) =
        let
          val name' = "o_" ^ name
          val V1 = I.EClo (V, s)        (* G, B |- V' : type *)
          val V2 = I.Pi ((I.Dec (NONE, Vb), I.Maybe), V1)
                                        (* G |- {B} V' : type *)
          val V3 = closure (G, V2)
          val m = I.ctxLength G
          val condec = I.ConDec (name', NONE, m, I.Normal, V3, I.Type)
          val _ = TypeCheck.check (V3, I.Uni I.Type)
          val _ = if !Global.chatter >= 4
                    then print (Print.conDecToString condec ^ "\n") else ()
          val cid = I.sgnAdd condec
          val _ = Names.installConstName cid
          val _ = Array.update (internal, cid, Const (m, n))
        in
          internalizeBlock (n+1, G, Vb, S) (L2, I.Dot (I.Exp (I.Root (I.Const cid, S)), s))
        end

    (* makeSpine (n, G, S) = S'

       Invariant:
       If  G0 = G, G'
       and |G'| = n
       and G0 |- S : V >> V'   for some V, V'
       then S' extends S
       and G0 |- S' : V >> type.
    *)
    fun makeSpine (_, I.Null, S) = S
      | makeSpine (n, I.Decl (G, D), S) =
          makeSpine (n+1, G, I.App (I.Root (I.BVar (n+1), I.Nil), S))


   (* interalizeCondec condec = ()

       Invariant:
       If   condec is a condec,
       then all pi declarations are internalized if condec was a blockdec
    *)
    fun internalizeCondec (cid, I.ConDec _) = ()
      | internalizeCondec (cid, I.ConDef _) = ()
      | internalizeCondec (cid, I.AbbrevDef _) = ()
      | internalizeCondec (cid, I.BlockDec (name, _, Gsome, Lpi)) =
        let
          val V' = closure (Gsome, I.Uni I.Type)
          val C = I.ConDec (name ^ "'", NONE, 0, I.Normal, V', I.Kind)
          val a = I.sgnAdd C
          val _ = Array.update (internal, a, Type cid)
          val _ = Names.installConstName a
          val S = makeSpine (0, Gsome, I.Nil)
          val Vb = I.Root (I.Const a, S)
          val S' = makeSpine (0, I.Decl (Gsome, I.Dec (NONE, Vb)), I.Nil)
        in
          internalizeBlock (1, Gsome, Vb, S') (Lpi, I.shift)
        end
      | internalizeCondec (cid, I.SkoDec _) = ()


    (* sigToCtx () = ()

       Invariant:
       G is the internal representation of the global signature
       It converts every block declaration to a type family (stored in the global
       signature) and a list of declarations.
    *)
    fun internalizeSig () =
        let
          val (max, _) = I.sgnSize  ()
            (* we might want to save max, here to restore the original
                 signature after parsing is over  --cs Thu Apr 17 09:46:29 2003 *)
          fun internalizeSig' n =
              if n>=max then ()
              else
                (internalizeCondec (n, I.sgnLookup n); internalizeSig' (n+1))
        in
          internalizeSig' 0
        end




    (* Externalization *)

    fun dropSpine (0, S) = S
      | dropSpine (n, I.App (_, S)) = dropSpine (n-1, S)

    fun makeSub (I.Nil, s) = s
      | makeSub (I.App (U, S), s) = makeSub (S, I.Dot (I.Exp U, s))

    fun externalizeExp' (U as I.Uni _)  = U
      | externalizeExp' (I.Pi ((D, DP), U)) = I.Pi ((externalizeDec D, DP), externalizeExp U)
      | externalizeExp' (I.Root (H as I.BVar _, S)) = I.Root (H, externalizeSpine S)
      | externalizeExp' (I.Root (H as I.Const c, S)) =
        (case I.constUni c
           of I.Kind => I.Root (H, externalizeSpine S)
            | I.Type => let
                          val Const (n, i) = Array.sub (internal, c)
                          val (I.App (I.Root (I.BVar b, I.Nil), S')) = dropSpine (n, S)
                        in
                          I.Root (I.Proj (I.Bidx b, i), externalizeSpine S')
                        end)
      | externalizeExp' (I.Root (I.Proj _, _)) = raise Domain
      | externalizeExp' (I.Root (I.Skonst _, _)) = raise Domain
      | externalizeExp' (I.Root (I.Def _, _)) = raise Domain
      | externalizeExp' (I.Root (I.NSDef _, _)) = raise Domain
      | externalizeExp' (I.Root (I.FVar _, _)) = raise Domain
      | externalizeExp' (I.Root (I.FgnConst _, _)) = raise Domain
      | externalizeExp' (I.Redex (U, S)) = I.Redex (externalizeExp U, externalizeSpine S)
      | externalizeExp' (I.Lam (D, U)) = I.Lam (externalizeDec D, externalizeExp U)
    and externalizeExp (U) = externalizeExp' (Whnf.normalize (U, I.id))
    (* Check : the translators hould only generate normal forms. Fix during the next pass --cs Thu Apr 17 17:06:24 2003 *)

    and externalizeBlock (B as I.Bidx _) = B
    and externalizeDec (I.Dec (name, V)) = I.Dec (name, externalizeExp V)

    and externalizeSpine I.Nil = I.Nil
      | externalizeSpine (I.App (U, S)) = I.App (externalizeExp U, externalizeSpine S)
    and externalizeSub (s as I.Shift n) = s
      | externalizeSub (I.Dot (F, s)) = I.Dot (externalizeFront F, externalizeSub s)
    and externalizeFront (F as I.Idx _) = F
      | externalizeFront (I.Exp U) = I.Exp (externalizeExp U)
      | externalizeFront (I.Block B) = I.Block (externalizeBlock B)
      | externalizeFront (F as I.Undef) = F

    fun externalizePrg (n, T.Lam (D, P)) = T.Lam (externalizeMDec (n, D), externalizePrg (n+1, P))
      | externalizePrg (n, T.New P) = T.New (externalizePrg (n, P))
      | externalizePrg (n, T.Box (W, P)) = T.Box (W, externalizePrg (n, P))
      | externalizePrg (n, T.Choose P) = T.Choose (externalizePrg (n, P))
      | externalizePrg (n, T.PairExp (U, P)) = T.PairExp (externalizeExp U, externalizePrg (n, P))
      | externalizePrg (n, T.PairPrg (P1, P2)) = T.PairPrg (externalizePrg (n, P1), externalizePrg (n, P2))
      | externalizePrg (n, T.PairBlock (B, P)) = T.PairBlock (externalizeBlock B, externalizePrg (n, P))
      | externalizePrg (n, T.Unit) =  T.Unit
      | externalizePrg (n, T.Var k) = T.Var k
      | externalizePrg (n, T.Const c) = T.Const c
      | externalizePrg (n, T.Redex (P, S)) = T.Redex  (externalizePrg (n, P), externalizeMSpine (n, S))
      | externalizePrg (n, T.Rec (D, P)) = T.Rec (externalizeMDec (n, D), externalizePrg (n+1, P))
      | externalizePrg (n, T.Case (T.Cases O)) = T.Case (T.Cases (externalizeCases O))
      | externalizePrg (n, T.Let (D, P1, P2)) = T.Let (externalizeMDec (n, D), externalizePrg (n, P1), externalizePrg (n+1, P2))
      (* PClo should not be possible, since by invariant, parser
         always generates a program in normal form  --cs Thu Apr 17 16:56:07 2003
      *)
    and externalizeMDec (n, T.UDec (D as I.Dec (name, V as I.Root (I.Const a, S)))) =
        (case Array.sub (internal, a)
           of Type (a') => T.UDec (I.BDec(name, (a', makeSub (externalizeSpine S, I.Shift n))))
            | _ =>  T.UDec (externalizeDec D))
      | externalizeMDec (n, T.UDec D) = T.UDec (externalizeDec D)
      | externalizeMDec (n, T.PDec (s, F)) = T.PDec (s, externalizeFor (n, F))

    and externalizeFor (n, T.World (W, F)) = T.World (W, externalizeFor (n, F))
      | externalizeFor (n, T.All ((D, Q), F)) = T.All ((externalizeMDec (n, D), Q), externalizeFor (n+1, F))
      | externalizeFor (n, T.Ex ((D, Q), F)) = T.Ex ((externalizeDec D, Q), externalizeFor (n+1, F))
      | externalizeFor (n, T.True) = T.True
      | externalizeFor (n, T.And (F1, F2)) = T.And (externalizeFor (n, F1), externalizeFor (n, F2))

    and externalizeMSpine (n, T.Nil) = T.Nil
      | externalizeMSpine (n, T.AppExp (U, S)) = T.AppExp (externalizeExp U, externalizeMSpine (n, S))
      | externalizeMSpine (n, T.AppBlock (B, S)) = T.AppBlock (externalizeBlock B, externalizeMSpine (n, S))
      | externalizeMSpine (n, T.AppPrg (P, S)) = T.AppPrg (externalizePrg (n, P), externalizeMSpine (n, S))

    and externalizeCases nil = nil
      | externalizeCases ((Psi, t, P) :: O) =
        let
          val n = I.ctxLength Psi
        in
          (externalizeMCtx Psi, externalizeMSub (n, t), externalizePrg (n, P)) :: externalizeCases O
        end

    and externalizeMSub (n, t as (T.Shift _)) = t
      | externalizeMSub (n, T.Dot (F, t)) = T.Dot (externalizeMFront (n, F), externalizeMSub (n, t))

    and externalizeMFront (n, F as (T.Idx _)) = F
      | externalizeMFront (n, T.Prg P) = T.Prg (externalizePrg (n, P))
      | externalizeMFront (n, T.Exp U) = T.Exp (externalizeExp U)
      | externalizeMFront (n, T.Block B) = T.Block (externalizeBlock B)
      | externalizeMFront (n, F as T.Undef) =  F

    and externalizeMCtx I.Null = I.Null
      | externalizeMCtx (I.Decl (Psi, D)) =
         I.Decl (externalizeMCtx Psi, externalizeMDec (I.ctxLength Psi, D))


(* Translation starts here *)



    fun transTerm (D.Rtarrow (t1, t2)) =
        let
          val (s1, c1) = transTerm t1
          val (s2, c2) = transTerm t2
        in
          (s1 ^ " -> " ^ s2, c1 @ c2)
        end
      | transTerm (D.Ltarrow (t1, t2)) =
        let
          val (s1, c1) = transTerm t1
          val (s2, c2) = transTerm t2
        in
          (s1 ^ " <- " ^ s2, c1 @ c2)
        end
      | transTerm (D.Type) = ("type", nil)
      | transTerm (D.Id s) =
        let
          val qid = Names.Qid (nil, s)
        in
          case Names.constLookup qid
            of NONE => (s, nil)
             | SOME cid => (case (I.sgnLookup cid)
                              of I.BlockDec _ => (s ^ "'", nil)
                               | _ => (s, nil))
        end
      | transTerm (D.Pi (D, t)) =
        let
          val (s1, c1) = transDec D
          val (s2, c2) = transTerm t
        in
          ("{" ^ s1 ^ "}" ^ s2, c1 @ c2)
        end
      | transTerm (D.Fn (D, t)) =
        let
          val (s1, c1) = transDec D
          val (s2, c2) = transTerm t
        in
          ("[" ^ s1 ^ "]" ^ s2, c1 @ c2)
        end
      | transTerm (D.App (t1, t2)) =
        let
          val (s1, c1) = transTerm t1
          val (s2, c2) = transTerm t2
        in
          (s1 ^ " " ^ s2, c1 @ c2)
        end
      | transTerm (D.Omit) = ("_", nil)
      | transTerm (D.Paren (t)) =
        let
          val (s, c) = transTerm t
        in
          ("(" ^  s ^ ")", c)
        end
      | transTerm (D.Of (t1, t2)) =
        let
          val (s1, c1) = transTerm t1
          val (s2, c2) = transTerm t2
        in
          (s1 ^ ":" ^ s2, c1 @ c2)
        end
      | transTerm (D.Dot (t, s2)) =
        let
          val (s1, c1) = transTerm t
        in
          ("o_" ^ s2 ^ " " ^ s1, c1)
        end

(*      | transTerm (D.Dot (D.Id s1, s2)) =
        ("PROJ#" ^ s1 ^ "#" ^ s2, nil)
      | transTerm (D.Dot (D.Paren (D.Of (D.Id s1, t)), s2)) =
        ("PROJ#" ^ s1 ^ "#" ^ s2, [(s1, t)])
*)

    and transDec (D.Dec (s, t)) =
        let
          val (s', c) = transTerm t
        in
          (s ^ ":" ^ s', c)
        end

    fun transWorld (D.WorldIdent s) =
           (* We should use the worlds we have defined in Tomega, but this
              is not good enough, because worlds are not defined
              by a regualar expression.  Therefore this is a patch *)
        let
          val qid = Names.Qid (nil, s)
          val cid = (case Names.constLookup qid
                                    of NONE => raise Names.Error ("Undeclared label "
                                         ^ Names.qidToString (valOf (Names.constUndef qid))
                                         ^ ".")
                                     | SOME cid => cid)
        in
          [cid]
        end
      | transWorld (D.Plus (W1, W2)) = transWorld W1 @ transWorld W2
      | transWorld (D.Concat (W1, W2)) = transWorld W1 @ transWorld W2
      | transWorld (D.Times W) = transWorld W

    fun transFor' (Psi, D) =
        let
          val G = I.Decl (I.Null, D)
          val ReconTerm.JWithCtx (I.Decl (I.Null, D'), ReconTerm.JNothing) =
            ReconTerm.reconWithCtx (Psi, ReconTerm.jwithctx(G, ReconTerm.jnothing))
        in D'
        end

    (* transFor (ExtDctx, ExtF) = (Psi, F)

       Invariant:
       If   |- ExtDPsi extdecctx
       and  |- ExtF extfor
       then |- Psi <= ExtDPsi
       and  Psi |- F <= ExtF
    *)
    fun transFor (Psi, D.True) = T.True
      | transFor (Psi, D.And (EF1, EF2)) =
          T.And (transFor (Psi, EF1), transFor (Psi, EF2))
      | transFor (Psi, D.Forall (D, F)) =
        let
          val (D'', nil) = transDec D
          val D' = transFor' (Psi, stringTodec (D''))
        in
           T.All ((T.UDec D', T.Explicit), transFor (I.Decl (Psi, D'), F))
        end
      | transFor (Psi, D.Exists (D, F)) =
        let
          val (D'', nil) = transDec D
          val D' = transFor' (Psi, stringTodec (D''))
        in
           T.Ex ((D', T.Explicit), transFor (I.Decl (Psi, D'), F))
        end
      | transFor (Psi, D.ForallOmitted (D, F)) =
        let
          val (D'', nil) = transDec D
          val D' = transFor' (Psi, stringTodec (D''))
        in
           T.All ((T.UDec D', T.Implicit), transFor (I.Decl (Psi, D'), F))
        end
      | transFor (Psi, D.ExistsOmitted (D, F)) =
        let
          val (D'', nil) = transDec D
          val D' = transFor' (Psi, stringTodec (D''))
        in
           T.Ex ((D', T.Implicit), transFor (I.Decl (Psi, D'), F))
        end
      | transFor (Psi, D.World (W, EF)) =
           T.World (T.Worlds (transWorld W), transFor (Psi, EF))






    (* stringToTerm s = U

       Invariant:
       If   s is a string representing an expression,
       then U is the result of parsing it
       otherwise Parsing.error is raised.
    *)
    fun stringToterm s =
        let
          val f = LS.expose (L.lexStream (TextIO.openString s))
          val (t, f') = ParseTerm.parseTerm' f
          val r2 = checkEOF f'
        in
          t
        end




    (* head (dH) = n

       Invariant:
       n is the name of the function head dH
    *)
    fun head (D.Head s) = s
      | head (D.AppLF (H, _)) = head H
      | head (D.AppMeta (H, _)) = head H

    (* lamClosure (F, P) = P'

       Invariant:
       If   . |- F formula
       and  . |- F = all D1. ... all Dn. F' formula
         for  . |- F' formula that does not commence with a universal quantifier
       and . |- P :: F'
       then P' = lam D1 ... lam Dn P
    *)
    fun lamClosure (T.All ((D, _), F), P) = T.Lam (D, lamClosure (F, P))
      | lamClosure (T.World(_, F), P) = lamClosure (F, P)
      | lamClosure (T.Ex _, P) = P


    fun exists (c, []) = raise Error "Current world is not subsumed"
      | exists (c, c' :: cids) = if c = c' then () else exists (c, cids)

    fun subsumed ([], cids') = ()
      | subsumed (c :: cids, cids') = (exists (c, cids'); subsumed (cids, cids'))


    fun checkForWorld (T.World (W as T.Worlds cids, F), t', T.Worlds cids') =
        let
          val _ =  subsumed (cids', cids)
        (* check that W is at least as large as W' *)
        in
          (F, t', W)
        end
      | checkForWorld FtW = FtW


    (* dotn (t, n) = t'

       Invariant:
       If   Psi0 |- t : Psi
       and  |G| = n   for any G
       then Psi0, G[t] |- t : Psi, G
    *)
    fun dotn (t, 0) = t
      | dotn (t, n) = I.dot1 (dotn (t, n-1))

    (* append (Psi1, Psi2) = Psi3

       Invariant:
       If   |- Psi1 ctx
       and  |- Psi2 ctx
       then |- Psi3 = Psi1, Psi2 ctx
    *)
    fun append (Psi, I.Null) = Psi
      | append (Psi, I.Decl (Psi', D)) =
          I.Decl (append (Psi, Psi'), D)


    fun parseTerm (Psi, (s, V)) =
        let
          val (term', c) = transTerm s
          val term = stringToterm (term')
          val ReconTerm.JOf ((U, occ), (_, _), L) =
            ReconTerm.reconWithCtx (T.coerceCtx Psi, ReconTerm.jof' (term, V))
        in
          U
        end

    fun parseDec (Psi, s) =
        let
          val (dec', c) = transDec s
          val dec = stringTodec (dec')
          val ReconTerm.JWithCtx (I.Decl(I.Null, D), ReconTerm.JNothing) =
            ReconTerm.reconWithCtx (T.coerceCtx Psi, ReconTerm.jwithctx (I.Decl(I.Null, dec), ReconTerm.jnothing))
          val I.Dec (SOME n, _) = D
        in
          D
        end

    (* transDecs ((Psi, t), dDs, sc, W) = x

       Invariant:
       If   . |- t :: Psi
       and  Psi |- dDs decs
       and  W is the valid world
       and  sc is the success continuation that expects
            as input: (Psi', env')
                      where Psi' is the context after translating dDs
                      and   Psi' |- env' environment
                            are all variables introduced until this point
            as output: anything.
       then eventually x = ().     --cs
    *)

    fun transDecs (Psi, D.Empty, sc, W) = sc (Psi, W)
      | transDecs (Psi, D.FormDecl (FormD, Ds), sc, W) = (transForDec (Psi, FormD, Ds, sc, W))
      | transDecs (Psi, D.ValDecl (ValD, Ds), sc, W) = (transValDec (Psi, ValD, Ds, sc, W))
      | transDecs (Psi, D.NewDecl (D, Ds), sc, W) =
          let
            val D' = T.UDec (parseDec (Psi, D))
          in
(*          T.Let (T.PDec (NONE, T.True), T.Lam (D', transDecs (I.Decl (Psi, D'), Ds, sc, W)), T.Unit) *)
            T.Let (T.PDec (NONE, T.True), T.Lam (D', transDecs (I.Decl (Psi, D'), Ds, sc, W)), T.Var 1)
 (* T.True is not right! -- cs Sat Jun 28 11:43:30 2003  *)
          end

      | transDecs _ = raise Error "Constant declaration must be followed by a constant definition"



    and lookup (I.Null, n, s) = raise Error ("Undeclared constant " ^ s)
      | lookup (I.Decl (G, T.PDec (NONE, _)), n, s) =  lookup (G, n+1, s)
      | lookup (I.Decl (G, T.UDec _), n, s) =  lookup (G, n+1, s)
      | lookup (I.Decl (G, T.PDec (SOME s', F)), n, s) =
        if s = s' then (n, T.forSub (F, T.Shift n))
        else lookup (G, n+1, s)

    (* transHead (G, T, S) = (F', t')

       Invariant:
       If   G |- T : F
       and  G |- S : world{W}all{G'}F' >> F'
       then G |- t' : G'
    *)
    and transHead (Psi, D.Head s, args) =
        let
          val (n, F) = lookup (Psi, 1, s)
        in
          transHead' ((F, T.id), I.Nil, args)
        end
      | transHead (Psi, D.AppLF (h, t), args) = transHead (Psi, h, t::args)

    and transHead' ((T.World (_, F), s), S, args) = transHead' ((F, s), S, args)
      | transHead' ((T.All ((T.UDec (I.Dec (_, V)), T.Implicit), F'), s), S, args) =
        let
          val X = I.newEVar (I.Decl(I.Null, I.NDec), I.EClo (V, T.coerceSub s))
        in
          transHead' ((F', T.Dot (T.Exp X, s)), I.App (X, S), args)
        end
      | transHead' ((T.All ((T.UDec (I.Dec (_, V)), T.Explicit), F'), s), S, t :: args) =
        let
          val (term', c) = transTerm t
          val term = stringToterm (term')
          val ReconTerm.JOf ((U, occ), (_, _), L) =
            ReconTerm.reconWithCtx (I.Null, ReconTerm.jof' (term, I.EClo (V, T.coerceSub s)))
        in
          transHead' ((F', T.Dot (T.Exp U, s)), I.App(U, S), args)
        end
      | transHead' ((F, s), S, nil) = ((F, s), S)


    (* spineToSub ((S, t), s) = s'

       Invariant:
       If  Psi' |- S spine
       and Psi'' |- t: Psi'
       and Psi'' |- s : Psi'''
       then  Psi'' |- s' : Psi''', Psi''''
    *)

    and spineToSub ((I.Nil, _), s') = s'
      | spineToSub ((I.App (U, S), t), s') =
          T.Dot (T.Exp (I.EClo (U, t)), spineToSub((S, t), s'))

    and transPattern (p, (T.Ex ((I.Dec (_, V), T.Implicit), F'), s)) =
          transPattern (p, (F', T.Dot (T.Exp (I.EVar (ref NONE, I.Null, I.EClo (V, T.coerceSub s), ref nil)), s)))
      | transPattern (D.PatInx (t, p), (T.Ex ((I.Dec (_, V), T.Explicit), F'), s)) =
        let
          val (term', c) = transTerm t
          val term = stringToterm (term')
          val ReconTerm.JOf ((U, occ), (_, _), L) =
            ReconTerm.reconWithCtx (I.Null, ReconTerm.jof' (term, I.EClo (V, T.coerceSub s)))
        in
          T.PairExp (U, transPattern (p, (F', T.Dot (T.Exp U, s))))
        end
      | transPattern (D.PatUnit, (F, s)) = T.Unit
                                        (* other cases should be impossible by invariant
                                         F should be F.True
                                         --cs Sun Mar 23 10:38:57 2003 *)


    (* transFun1 ((Psi, env), dDs, sc, W) = x

       Invariant:
       If   Psi |- dDs :: Psi'
       and  Psi |- env environment
       and  the top declaration is a function declaration
       and  W is the valid world
       and  sc is the success continuation that expects
            as input: (Psi', env')
                      where Psi' is the context after translating dDs
                      and   Psi' |- env' environment
                            are all variables introduced until this point
            as output: anything.
       then eventually x = ().     --cs
    *)
    and transFun1 (Psi, (s', F), D.FunDecl (D.Fun (eH, eP), Ds), sc, W) =
        let
          val s = head eH
          val _ = if s = s' then () else raise Error "Function defined is different from function declared."
        in
          transFun2 (Psi, (s, F), D.FunDecl (D.Bar (eH, eP), Ds), sc, fn Cs => T.Case (T.Cases Cs), W)
        end
      | transFun1 (Psi, (s', F), D.FunDecl (D.FunAnd (eH, eP), Ds), sc, W) =
        raise Error "Mutual recursive functions not yet implemented"
      | transFun1 _ = raise Error "Function declaration expected"


    (* transFun2 ((Psi, env), s, dDs, sc, k, W) = x

       Invariant:
       If   Psi |- dDs :: Psi'
       and  Psi |- env environment
       and  s is the name of the function currently being translated
       and  the top declaration is a function declaration
       and  the top declaration is a function declaration
       and  W is the valid world
       and  sc is the success continuation that expects
            as input: (Psi', env')
                      where Psi' is the context after translating dDs
                      and   Psi' |- env' environment
                            are all variables introduced until this point
            as output: anything.
       and  k is the continuation that expects
            as input: Cs a list of cases
            as ouput: A program P that corresponds to the case list Cs
       then eventually x = ().     --cs
    *)
    and transFun2   (Psi, (s, F), D.FunDecl (D.Bar (eH, eP), Ds), sc, k, W) =
          transFun3 (Psi, (s, F), eH, eP, Ds, sc,  k, W)
      | transFun2   (Psi, (s, F), Ds, sc, k, W) =
          let
            val D = T.PDec (SOME s, F)
            val P' = T.Rec (D, lamClosure (F, k nil))
          in
            (P', Ds)
          end

    (* transFun3 ((Psi, env), s, eH, eP, Ds, sc, k, W) = x

       Invariant:
       If   Psi |- dDs :: Psi'
       and  Psi |- env environment
       and  s is the name of the function currently being translated
       and  eH is the head of the function
       and  eP its body
       and  W is the valid world
       and  Ds are the remaining declarations
       and  sc is the success continuation that expects
            as input: (Psi', env')
                      where Psi' is the context after translating dDs
                      and   Psi' |- env' environment
                            are all variables introduced until this point
            as output: anything.
       and  k is the continuation that expects
            as input: Cs a list of cases
            as ouput: A program P that corresponds to the case list Cs
       then eventually x = ().     --cs
    *)
    and transFun3 (Psi, (s, F), eH, eP, Ds, sc, k, W) =
        let
          val _ = if (head eH) <> s
                  then raise Error "Functions don't all have the same name"
                  else ()
          val _ = Names.varReset (I.Null)
          val Psi0 = I.Decl (Psi, T.PDec (SOME s, F))
          val ((F', t'), S) = transHead (Psi0, eH, nil)
(*                val F' = T.forSub (F, t) *)
          val (Psi', S') = Abstract.abstractSpine (S, I.id)
          val Psi'' = append (Psi0, T.embedCtx Psi')
          val m0 = I.ctxLength Psi0
          val m' = I.ctxLength Psi'
                                        (* |Psi''| = m0 + m' *)
          val t0 = dotn (I.Shift m0, m')
                                        (* Psi0, Psi'[^m0] |- t0 : Psi' *)
(*        val t1 = T.Dot (T.Prg (T.Root (T.Var (m'+1), T.Nil)), T.Shift (m'))   (* BUG !!!! Wed Jun 25 11:23:13 2003 *)
                                        (* Psi0, Psi'[^m0] |- t1 : F[^m0]  *)
*)        val t'' = spineToSub ((S', t0),  T.Shift m')

(*        val _ = print (TomegaPrint.forToString (Names.ctxName (T.coerceCtx Psi''), myF) ^ "\n") *)

          val P = transProgI (Psi'', eP, (F', t'), W)
        in
          transFun2 (Psi, (s, F), Ds, sc, fn Cs => k ((Psi'', t'', P) :: Cs), W)
        end

    (* transForDec ((Psi, env), eDf, dDs, sc, W) = x

       Invariant:
       If   Psi |- dDs :: Psi'
       and  Psi |- env environment
       and  Psi |- eDf is a theorem declaration.
       and  W is the valid world
       and  dDs are the remaining declarations
       and  sc is the success continuation that expects
            as input: (Psi', env')
                      where Psi' is the context after translating dDs
                      and   Psi' |- env' environment
                            are all variables introduced until this point
            as output: anything.
       then eventually x = ().     --cs
    *)
    and transForDec (Psi, D.Form (s, eF), Ds, sc, W) =
        let

          val G = Names.ctxName (T.coerceCtx Psi)
          val F = transFor (G, eF)
          val (F'' as T.World (W, F')) = T.forSub (F, T.id)
(*        val _ = print s
          val _ = print " :: "
          val _ = print (TomegaPrint.forToString (T.embedCtx G, F'') ^ "\n") *)
          val _ = TomegaTypeCheck.checkFor (Psi, F'')
          val (P, Ds') = transFun1 (Psi, (s, F'), Ds, sc, W)
          val D = T.PDec (SOME s, F'')
        in
          T.Let (D, T.Box (W, P), transDecs (I.Decl (Psi, D), Ds', (fn P' => sc P'), W))
        end


    (* transValDec ((Psi, env), dDv, dDs, sc, W) = x

       Invariant:
       If   Psi |- dDs :: Psi'
       and  Psi |- env environment
       and  Psi |- dDv value declaration
       and  W is the valid world
       and  dDs are the remaining declarations
       and  sc is the success continuation that expects
            as input: (Psi', env')
                      where Psi' is the context after translating dDs
                      and   Psi' |- env' environment
                            are all variables introduced until this point
            as output: anything.
       then eventually x = ().     --cs
    *)
    and transValDec (Psi, D.Val (EPat, eP, eFopt), Ds, sc, W) =
        let
          val (P, (F', t')) = (case eFopt
                                 of NONE => transProgS (Psi, eP, W, nil)
                                  | SOME eF => let
                                                 val F' = transFor (T.coerceCtx Psi, eF)
                                                 val P' =  transProgIN (Psi, eP, F', W)
                                               in
                                                 (P', (F', T.id))
                                               end)

          val F'' = T.forSub (F', t')
          val Pat = transPattern (EPat, (F', t'))
          val D = T.PDec (NONE, F'')
          val (Psi', Pat') = Abstract.abstractTomegaPrg (Pat)
          val m = I.ctxLength Psi'
(*        val t = T.Dot (T.Prg Pat', T.id)  was --cs Tue Jun 24 13:04:55 2003 *)
          val t = T.Dot (T.Prg Pat', T.Shift m)
          val Psi'' = append (Psi, Psi')
          val P'' = transDecs (Psi'', Ds, sc, W)
        in
          T.Let (D, P, T.Case (T.Cases [ (Psi'', t, P'') ]))
        end



    (* transProgS ((Psi, env), ExtP, F, W) = P
       transProgI ((Psi, env), ExtP, W) = (P, F)
       Invariant:
       If   ExtP contains free variables among (Psi, env)
       and  ExtP is a program defined in (Psi, env)
       and  W is a world
       and  Exists Psi |- F : formula
       then Psi |- P :: F
    *)
    and transProgI (Psi, eP, Ft, W) =
          transProgIN (Psi, eP, T.forSub Ft, W)

    and transProgIN (Psi, D.Unit, T.True, W) = T.Unit
      | transProgIN (Psi, P as D.Inx (s, EP), T.Ex ((I.Dec (_, V), T.Explicit), F'), W) =
        let
          val U = parseTerm (Psi, (s, V))
          val P' = transProgI (Psi, EP, (F', T.Dot (T.Exp U, T.id)), W)
        in
          T.PairExp (U, P')
        end
      | transProgIN (Psi, D.Let (eDs, eP), F, W) =
          transDecs (Psi, eDs, fn (Psi', W') =>
                     transProgI (Psi', eP, (F, T.Shift (I.ctxLength Psi' - I.ctxLength Psi)),W'), W)
      | transProgIN (Psi, D.Choose (eD, eP), F, W) =
          let
            val D' = parseDec (Psi, eD)
            val Psi'' = I.Decl (Psi, T.UDec D')
          in
            T.Choose (T.Lam (T.UDec D', transProgI (Psi'', eP, (F, T.Shift 1), W)))
            end
      | transProgIN (Psi, D.New (nil, eP), F, W) =
          transProgIN (Psi, eP, F, W)
      | transProgIN (Psi, D.New (eD :: eDs, eP), F, W) =
          let
            val D' = parseDec (Psi, eD)
            val Psi'' = I.Decl (Psi, T.UDec D')
          in
            T.New (T.Lam (T.UDec D', transProgI (Psi'', D.New (eD :: eDs, eP) , (F, T.Shift 1), W)))
          end
      | transProgIN (Psi, P as D.AppTerm (EP, s), F, W) =
        let
          val (P', (F', _)) = transProgS (Psi, P, W, nil)
          val ()  = ()   (* check that F == F' *)
        in
          P'
        end


(*      | transProgIN ((Psi, env), D.Pair (EP1, EP2), T.And (F1, F2), W) =
        let
          val P1 = transProgIN ((Psi, env), EP1, F1, W)
          val P2 = transProgIN ((Psi, env), EP2, F2, W)
        in
          T.PairPrg (P1, P2)
        end
      | transProgIN ((Psi, env), P as D.AppProg (EP1, EP2), F, W) =
        let
          val (P', (F', _)) = transProgS ((Psi, env), P, W)
          val ()  = ()   (* check that F == F' *)
        in
          P'
        end
      | transProgIN ((Psi, env), P as D.AppTerm (EP, s), F, W) =
        let
          val (P', (F', _)) = transProgS ((Psi, env), P, W)
          val ()  = ()   (* check that F == F' *)
        in
          P'
        end
      | transProgIN ((Psi, env), P as D.Inx (s, EP), T.Ex (I.Dec (_, V), F'), W) =
        let
          val (U, V) = parseTerm ((Psi, env), s)
          val P' = transProgI ((Psi, env), EP, (F', T.Dot (T.Exp U, T.id)), W)
        in
          T.PairExp (U, P')
        end
      | transProgIN ((Psi, env), D.Const name, F, W) =
        let
          val lemma = T.lemmaName name
          val F' = T.lemmaFor lemma
          val () = ()    (* check that F == F' *)
        in
          T.Root (T.Const lemma, T.Nil)
        end

(*      | transProgIN (Psi, D.Lam (s, EP)) =
        let
          val dec = stringTodec s
          val (I.Decl (Psi, (D, _, _)), P, F') = transProgI (I.Decl (ePsi, dec), EP)
        in
          (Psi, T.Lam (T.UDec D, P), T.All (D, F'))
        end
*)


      | transProgIN ((Psi, env), D.New (s, EP), F, W) =
          let
            val G = Names.ctxName (T.coerceCtx Psi)
            val _ = print (Print.ctxToString (I.Null, G) ^ "\n")
            val (U, V) = parseTerm ((Psi, env), s ^ " type")
            val _ = print (Print.expToString (G, U) ^ "\n")

          fun extract (G, Us) = extractW (G, Whnf.whnf Us)
          and extractW (G, (I.Pi ((D as I.Dec (_, _), _), V'), s)) =
                extract (I.Decl(G, I.decSub (D, s)), (V', I.dot1 s))
            | extractW (G, _) = G

          val G' = extract (I.Null, (U, I.id))
          val Dlist = T.ctxToBDecs (T.coerceCtx Psi, G', W)

          fun project ((G, env), []) = (env, 1)   (* is this the right starting point --cs *)
            | project ((G, env), x :: N) =
              let
                val (env', k) = project ((G, env), N)
                val U = I.Root (I.Proj (I.Bidx 1, k), I.Nil)
                val V =  TypeCheck.infer' (G, U)
              in
                ((U, V, x) :: env', k+1)
              end

          fun extend ((Psi', env'), []) = (Psi', env')
            | extend ((Psi', env'), (N, D) :: Dlist') =
              let
                val (Psi'', env'') = extend ((Psi', env'),  Dlist')
                val Psi''' = I.Decl (Psi'', T.UDec D)
                val I.BDec (_, (cid, s)) = D
                val G''' = T.coerceCtx Psi'''
                val env''' = map (fn (U, V, name) => (I.EClo (U, I.shift), I.EClo (V, I.shift), name)) env''
                val (env'''', _) = project ((G''', env'''), N)
              in
                (Psi''',  env'''')
               end

           val (Psi', env') = extend ((Psi, env), Dlist)
           val _ = printCtx (Names.ctxName (T.coerceCtx Psi'), env')

          fun universalClosure ([], F) = F
            | universalClosure ((_, D) :: Ds, F)  = T.All (T.UDec D, universalClosure (Ds, F))

          val (P', (F, t)) = transProgS ((Psi, env), EP, W)

          in
            T.Unit
          end

*)
   and transProgS (Psi, D.Unit, W, args) =
         (T.Unit, (T.True, T.id))
     | transProgS (Psi, D.AppTerm (EP, s), W, args) =
         transProgS (Psi, EP, W, s :: args)
     | transProgS (Psi, D.Const name, W, args) =
         let
(*         val lemma = T.lemmaName name
           val F = T.lemmaFor lemma *)
           val (n, F) = lookup (Psi, 1, name)
           val (S, Fs') = transProgS'  (Psi, (F, T.id), W, args)
         in
           (T.Redex (T.Var n, S), Fs')
         end
     | transProgS (Psi, D.Choose  (eD, eP), W, args) =
         let
           val D' = parseDec (Psi, eD)
           val (P, (F, t)) = transProgS (I.Decl (Psi, T.UDec D'), eP, W, args)
         in
           (T.Choose (T.Lam (T.UDec D', P)), (F, t))
         end
     | transProgS (Psi, D.New (nil, eP), W, args) =
         transProgS (Psi, eP, W, args)
     | transProgS (Psi, D.New (eD :: eDs, eP), W, args) =
         let
           val D' = parseDec (Psi, eD)
           val (P, (F, t)) = transProgS (I.Decl (Psi, T.UDec D'), D.New (eDs, eP), W, args)
           val T.UDec D'' = externalizeMDec (I.ctxLength Psi, T.UDec D')
           val (B, _) = T.deblockify  (I.Decl (I.Null, D''))
           val F' = TA.raiseFor (B, (F, T.coerceSub t))
         in
           (T.New (T.Lam (T.UDec D', P)), (F', T.id))   (* bug: forgot to raise F[t] to F' --cs Tue Jul  1 10:49:52 2003 *)
         end

    and transProgS' (Psi, (T.World (_, F), s), W, args) = transProgS' (Psi, (F, s), W, args)
      | transProgS' (Psi, (T.All ((T.UDec (I.Dec (_, V)), T.Implicit), F'), s), W, args) =
        let
          val G = T.coerceCtx Psi
          val X = I.newEVar (G, I.EClo (V, T.coerceSub s))
(*        val X = I.EVar (ref NONE, I.Null, I.EClo (V, T.coerceSub s), ref nil) *)
          val (S, Fs') = transProgS' (Psi, (F', T.Dot (T.Exp X, s)), W, args)
        in
          (T.AppExp (Whnf.normalize (X, I.id), S), Fs')
        end
      | transProgS' (Psi, (T.All ((T.UDec (I.Dec (_, V)), T.Explicit), F'), s), W, t :: args) =
        let
          val U = parseTerm (Psi, (t, I.EClo (V, T.coerceSub s)))
          val (S, Fs') = transProgS' (Psi, (F', T.Dot (T.Exp U, s)), W, args)
(*        val (F'', s'', _) = checkForWorld (F', T.Dot (T.Exp U, s), W) *)
        in
          (T.AppExp (U, S), Fs')
        end
      | transProgS' (Psi, (F, s), _,nil) = (T.Nil, (F, s))


(*
     | transProgS ((Psi, env), D.Pair (EP1, EP2), W) =
        let
          val (P1, (F1, t1)) = transProgS ((Psi, env), EP1, W)
          val (P2, (F2, t2)) = transProgS ((Psi, env), EP2, W)
        in
          (T.PairPrg (P1, P2), (T.And (F1, F2), T.comp (t1, t2)))
        end

     | transProgS ((Psi, env), D.AppProg (EP1, EP2), W) =
        let
          val (P1, (T.And (F1, F2), t)) = transProgS ((Psi, env), EP1, W)
          val P2 = transProgIN ((Psi, env), EP2, T.FClo (F1, t), W)
          val (F'', t'', W) = checkForWorld (F2, t, W)
        in
          (T.Redex (P1, T.AppPrg (P2, T.Nil)), (F'', t''))
        end


      | transProgS ((Psi, env), P as D.Inx (s, EP), W) =  raise Error "Cannot infer existential types"

(*      | transProgS ((Psi, env), D.Lam (s, EP), W) =
        let
          val dec = stringTodec s
          val (I.Decl (Psi', (D, _, _)), P, F) = transProgI (I.Decl (Psi, dec), EP)
          val (F', t', _) = checkForWorld (F, T.id, W)
        in
          (T.Lam (T.UDec D, P), (T.All (D, F'), t'))
        end
*)
      | transProgS ((Psi, env), D.New (s, eP), W)  =
        let
          val _ = print "["
          val G = Names.ctxName (T.coerceCtx Psi)
          val _ = print (Print.ctxToString (I.Null, G) ^ "\n")
          val (U, V) = parseTerm ((Psi, env), s ^ " type")
(*        val _ = print (Print.expToString (G, U) ^ "\n") *)

          fun extract (G, Us) = extractW (G, Whnf.whnf Us)
          and extractW (G, (I.Pi ((D as I.Dec (_, _), _), V'), s)) =
                extract (I.Decl(G, I.decSub (D, s)), (V', I.dot1 s))
            | extractW (G, _) = G

          val G' = extract (I.Null, (U, I.id))
          val Dlist = T.ctxToBDecs (T.coerceCtx Psi, G', W)

          fun project ((G, env), []) = (env, 1)   (* is this the right starting point --cs *)
            | project ((G, env), x :: N) =
              let
                val (env', k) = project ((G, env), N)
                val U = I.Root (I.Proj (I.Bidx 1, k), I.Nil)
                val V =  TypeCheck.infer' (G, U)
              in
                ((U, V, x) :: env', k+1)
              end

          fun extend ((Psi', env'), []) = (Psi', env')
            | extend ((Psi', env'), (N, D) :: Dlist') =
              let
                val (Psi'', env'') = extend ((Psi', env'),  Dlist')
                val Psi''' = I.Decl (Psi'', T.UDec D)
                val I.BDec (_, (cid, s)) = D
                val G''' = T.coerceCtx Psi'''
                val env''' = map (fn (U, V, name) =>
                    (I.EClo (U, I.shift), I.EClo (V, I.shift), name)) env''
                val (env'''', _) = project ((G''', env'''), N)
              in
                (Psi''',  env'''')
               end

          val (Psi', env') = extend ((Psi, env), Dlist)
          val _ = printCtx (Names.ctxName (T.coerceCtx Psi'), env')

          fun universalClosure ([], F) = F
            | universalClosure ((_, D) :: Ds, F)  = T.All (T.UDec D, universalClosure (Ds, F))

          val (P', (F, t)) = transProgS ((Psi, env), eP, W)
          val F' = T.forSub (F, t)
          val F'' = universalClosure (Dlist, F')
          val P'' = lamClosure (F'', P')
        in
          (P'', (F'', T.id))
        end
*)


    (* transProgram Ds = P

       Invariant:
       If Ds is a list of declarations then P is
       the translated program, that does not do anything
    *)
    fun transProgram Ds =
          transDecs (I.Null, Ds, fn (Psi, W) => (T.Unit), T.Worlds [])



  in
    val transFor = fn F => let val  F' = transFor (I.Null, F) in F' end


(*    val makePattern = makePattern *)
(*    val transPro = fn P => let val (P', _) = transProgS ((I.Null, []), P, T.Worlds []) in P' end *)


      val transDecs = transProgram
      val internalizeSig = internalizeSig
      val externalizePrg = fn P => externalizePrg  (0, P)

(*    val transDecs = fn Ds => transDecs ((I.Null, []), NONE, Ds, fn (Psi,  W) => T.Unit, T.Worlds [])
*)
  end
end (* functor Trans *)