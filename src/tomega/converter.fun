(* Converter from relational representation to a functional
   representation of proof terms *)
(* Author: Carsten Schuermann *)

functor Converter
  (structure Global : GLOBAL
   (*! structure IntSyn' : INTSYN !*)
   (*! structure Tomega' : TOMEGA !*)
   (*! sharing Tomega'.IntSyn = IntSyn' !*)
   structure Abstract : ABSTRACT
   (*! sharing Abstract.IntSyn = IntSyn' !*)
   structure ModeTable : MODETABLE
   (*! sharing ModeSyn.IntSyn = IntSyn' !*)
   structure Names : NAMES
   (*! sharing Names.IntSyn = IntSyn' !*)
   structure Unify : UNIFY
   (*! sharing Unify.IntSyn = IntSyn' !*)
   structure Whnf : WHNF
   (*! sharing Whnf.IntSyn = IntSyn' !*)
   structure Print : PRINT
   (*! sharing Print.IntSyn = IntSyn' !*)
   structure TomegaPrint : TOMEGAPRINT
   (*! sharing TomegaPrint.IntSyn = IntSyn' !*)
   (*! sharing TomegaPrint.Tomega = Tomega' !*)
   structure WorldSyn : WORLDSYN
   (*! sharing WorldSyn.IntSyn = IntSyn' !*)
   (*! sharing WorldSyn.Tomega = Tomega' !*)
   structure Worldify : WORLDIFY
   (*! sharing Worldify.IntSyn = IntSyn' !*)
   (*! sharing Worldify.Tomega = Tomega' !*)
   structure TomegaTypeCheck : TOMEGATYPECHECK
   (*! sharing TomegaTypeCheck.IntSyn = IntSyn' !*)
   (*! sharing TomegaTypeCheck.Tomega = Tomega' !*)
   structure Subordinate : SUBORDINATE
   (*! sharing Subordinate.IntSyn = IntSyn' !*)
   structure TypeCheck : TYPECHECK
   (*! sharing TypeCheck.IntSyn = IntSyn' !*)
   structure Redundant : REDUNDANT
   structure TomegaAbstract :TOMEGAABSTRACT
       )
     : CONVERTER =
struct
  (*! structure IntSyn = IntSyn' !*)
  (*! structure Tomega = Tomega' !*)

  exception Error of string

exception Error' of Tomega.Sub

  local
    structure T = Tomega
    structure I = IntSyn
    structure M = ModeSyn
    structure S = Subordinate
    structure A = Abstract
    structure TA = TomegaAbstract

    (* ABP - 4/20/03, determine if Front is (I.Idx 1) *)
    fun isIdx1 (I.Idx 1) = true
      | isIdx1 _ = false

    fun modeSpine a =
        case ModeTable.modeLookup a
          of NONE => raise Error "Mode declaration expected"
           | SOME mS => mS

    fun typeOf a =
        case I.sgnLookup a
          of I.ConDec (name, _, _, _, V, I.Kind) => V
           | _ => raise Error "Type Constant declaration expected"


    fun nameOf a =
        case I.sgnLookup a
          of I.ConDec (name, _, _, _, V, I.Kind) => name
           | _ => raise Error "Type Constant declaration expected"

    fun chatter chlev f =
        if !Global.chatter >= chlev
          then print ("[tomega] " ^ f ())
        else ()




    (* strengthenExp (U, s) = U'

       Invariant:
       If   G |- s : G'
       and  G |- U : V
       then G' |- U' = U[s^-1] : V [s^-1]
    *)
    fun strengthenExp (U, s) = Whnf.normalize (Whnf.cloInv (U, s), I.id)

    fun strengthenSub (s, t) = Whnf.compInv (s, t)

    (* strengthenDec (x:V, s) = x:V'

       Invariant:
       If   G |- s : G'
       and  G |- V : L
       then G' |- V' = V[s^-1] : L
    *)
    fun strengthenDec (I.Dec (name, V), s) = I.Dec (name, strengthenExp (V, s))
      | strengthenDec (I.BDec (name, (L, t)), s) =
                                        (* G0 |- t : Gsome *)
                                        (* G0  |- s : G' *)
                                        (* to show  G' |- t o s^1 : Gsome *)
          I.BDec (name, (L, strengthenSub (t, s)))

    (* strengthenCtx (G, s) = (G', s')

       If   G0 |- G ctx
       and  G0 |- w : G1
       then G1 |- G' = G[w^-1] ctx
       and  G0 |- w' : G1, G'
    *)
    fun strengthenCtx (I.Null, s) = (I.Null, s)
      | strengthenCtx (I.Decl (G, D), s) =
        let
          val (G', s') = strengthenCtx (G, s)
        in
          (I.Decl (G', strengthenDec (D, s')), I.dot1 s')
        end


    (* strengthenFor (F, s) = F'

       If   Psi0 |- F for
       and  Psi0 |- s :: Psi1
       then Psi1 |- F' = F[s^-1] ctx
    *)
    fun strengthenFor (T.True, s) = T.True
      | strengthenFor (T.And (F1, F2), s) =
          T.And (strengthenFor (F1, s), strengthenFor (F2, s))
      | strengthenFor (T.All ((T.UDec D, Q), F), s) =
          T.All ((T.UDec (strengthenDec (D, s)), Q), strengthenFor (F, I.dot1 s))
      | strengthenFor (T.Ex ((D, Q), F), s) =
          T.Ex ((strengthenDec (D, s), Q), strengthenFor (F, I.dot1 s))





    (* strengthenOrder (O, s) = O'

       If   Psi0 |- O order
       and  Psi0 |- s :: Psi1
       then Psi1 |- O' = O[s^-1] ctx
    *)
    fun strengthenOrder (Order.Arg((U,s1), (V, s2)), s) =
          Order.Arg ((U, strengthenSub (s1, s)), (V, strengthenSub (s2, s)))
      | strengthenOrder (Order.Simul Os, s) =
          Order.Simul (map (fn O => strengthenOrder (O, s)) Os)
      | strengthenOrder (Order.Lex Os, s) =
          Order.Lex (map (fn O => strengthenOrder (O, s)) Os)


    (* strengthenTC (TC, s) = TC'

       If   Psi0 |- TC : termination condition
       and  Psi0 |- s :: Psi1
       then Psi1 |- TC' = TC[s^-1] ctx
    *)
    fun strengthenTC (T.Base O, s) = T.Base (strengthenOrder (O, s))
      | strengthenTC (T.Conj (TC1, TC2), s) =
          T.Conj (strengthenTC (TC1, s), strengthenTC (TC2, s))
      | strengthenTC (T.Abs (D, TC), s) =
          T.Abs (strengthenDec (D, s), strengthenTC (TC, I.dot1 s))


    fun strengthenSpine (I.Nil, t) = I.Nil
      | strengthenSpine (I.App (U, S), t) = I.App (strengthenExp (U, t), strengthenSpine (S, t))



    (* strengthenPsi (Psi, s) = (Psi', s')

       If   Psi0 |- Psi ctx
       and  Psi0 |- s :: Psi1
       then Psi1 |- Psi' = Psi[s^-1] ctx
       and  Psi0 |- s' :: Psi1, Psi'
    *)
    fun strengthenPsi (I.Null, s) = (I.Null, s)
      | strengthenPsi (I.Decl (Psi, T.UDec D), s) =
        let
          val (Psi', s') = strengthenPsi (Psi, s)
        in
          (I.Decl (Psi', T.UDec (strengthenDec (D, s'))), I.dot1 s')
        end
      | strengthenPsi (I.Decl (Psi, T.PDec (name, F, NONE, NONE)), s) =
        let
          val (Psi', s') = strengthenPsi (Psi, s)
        in
          (I.Decl (Psi', T.PDec (name, strengthenFor (F, s'), NONE, NONE)), I.dot1 s')
        end


    (* strengthenPsi' (Psi, s) = (Psi', s')

       If   Psi0 |- Psi ctx
       and  Psi0 |- s : Psi1
       then Psi1 |- Psi' = Psi[s^-1] ctx
       and  Psi0 |- s' : Psi1, Psi'  weakening substitution
    *)
    fun strengthenPsi' (nil, s) = (nil, s)
      | strengthenPsi' (T.UDec D :: Psi, s) =
        let
          val D' = strengthenDec (D, s)
          val s' = I.dot1 s
          val (Psi'', s'') = strengthenPsi' (Psi, s')
        in
          (T.UDec D' :: Psi'', s'')
        end

    (* ctxSub (G, s) = (G', s')

       Invariant:
       if   Psi |- G ctx
       and  Psi' |- s : Psi
       then Psi' |- G' ctx
       and  Psi', G' |- s' : G
       and  G' = G [s],  declarationwise defined
    *)
    fun ctxSub (I.Null, s) = (I.Null, s)
      | ctxSub (I.Decl (G, D), s) =
        let
          val (G', s') = ctxSub (G, s)
        in
          (I.Decl (G', I.decSub (D, s')), I.dot1 s)
        end


    fun validMode (M.Mnil) = ()
      | validMode (M.Mapp (M.Marg (M.Plus, _), mS)) =
          validMode mS
      | validMode (M.Mapp (M.Marg (M.Minus, _), mS)) =
          validMode mS
      | validMode (M.Mapp (M.Marg (M.Star, _), mS)) =
          raise Error "+ or - mode expected, * found"

    fun validSig (Psi0, nil) = ()
      | validSig (Psi0, (G, V) :: Sig) =
        let
          fun append (G, I.Null) = G
            | append (G, I.Decl (G', D)) = I.Decl (append (G, G'), D)

        in
          (TypeCheck.typeCheck (T.coerceCtx (append (Psi0, T.embedCtx G)),
                                (V, I.Uni I.Type)); validSig (Psi0, Sig))
        end


    fun convertOneFor cid =
      let
        val V  = case I.sgnLookup cid
                   of I.ConDec (name, _, _, _, V, I.Kind) => V
                    | _ => raise Error "Type Constant declaration expected"
        val mS = case ModeTable.modeLookup cid
                   of NONE => raise Error "Mode declaration expected"
                    | SOME mS => mS

        val _ = validMode mS

        (* convertFor' (V, mS, w1, w2, n) = (F', F'')

           Invariant:
           If   G |- V = {{G'}} type :kind
           and  G |- w1 : G+
           and  G+, G'+, G- |- w2 : G
           and  G+, G'+, G- |- ^n : G+
           and  mS is a spine for G'
           then F'  is a formula excepting a another formula as argument s.t.
                If G+, G'+ |- F formula,
                then . |- F' F formula
           and  G+, G'+ |- F'' formula
        *)
        fun convertFor' (I.Pi ((D, _), V), M.Mapp (M.Marg (M.Plus, _), mS), w1, w2, n) =
            let
              val (F', F'') = convertFor' (V, mS, I.dot1 w1, I.Dot (I.Idx n, w2), n-1)
            in
              (fn F => T.All ((T.UDec (strengthenDec (D, w1)), T.Explicit), F' F), F'')
            end
          | convertFor' (I.Pi ((D, _), V), M.Mapp (M.Marg (M.Minus, _), mS), w1, w2, n) =
            let
              val (F', F'') = convertFor' (V, mS, I.comp (w1, I.shift), I.dot1 w2, n+1)
            in
              (F', T.Ex ((I.decSub (D, w2), T.Explicit), F''))
            end
          | convertFor' (I.Uni I.Type, M.Mnil, _, _, _) =
              (fn F => F, T.True)
          | convertFor' _ = raise Error "type family must be +/- moded"

        (* shiftPlus (mS) = s'

         Invariant:
         s' = ^(# of +'s in mS)
         *)

        fun shiftPlus mS =
          let
            fun shiftPlus' (M.Mnil, n) = n
              | shiftPlus' (M.Mapp (M.Marg (M.Plus, _), mS'), n) =
                  shiftPlus' (mS', n+1)
              | shiftPlus' (M.Mapp (M.Marg (M.Minus, _), mS'), n) =
                  shiftPlus' (mS', n)
          in
            shiftPlus' (mS, 0)
          end

        val n = shiftPlus mS
        val (F, F') = convertFor' (V, mS, I.id, I.Shift n, n)
      in
        F F'
      end



    (* createIH L = (Psi', P', F')

       Invariant:
       If   L is a list of type families
       and  Psi is a context
       then Psi' extends Psi' by declarations in L
       and  F' is the conjunction of the formuals
            that corresponds to each type family in L
       and  Psi' |- P' in F'
    *)
    fun createIH nil = raise Error "Empty theorem"
      | createIH [a] =
        let
          val name = I.conDecName (I.sgnLookup a)
          val F = convertOneFor a
        in
          (name, F)
        end
      | createIH (a :: L) =
        let
          val name = I.conDecName (I.sgnLookup a)
          val F = convertOneFor a
          val (name', F') = createIH  L
        in
          (name ^ "/" ^ name', T.And (F, F'))
        end




    fun convertFor L =
      let
        val (_, F') = createIH L
      in
        F'
      end

    (* occursInExpN (k, U) = B,

       Invariant:
       If    U in nf
       then  B iff k occurs in U
    *)
    fun occursInExpN (k, I.Uni _) = false
      | occursInExpN (k, I.Pi (DP, V)) = occursInDecP (k, DP) orelse occursInExpN (k+1, V)
      | occursInExpN (k, I.Root (H, S)) = occursInHead (k, H) orelse occursInSpine (k, S)
      | occursInExpN (k, I.Lam (D, V)) = occursInDec (k, D) orelse occursInExpN (k+1, V)
      (* | occursInExpN (k, I.FgnExp (cs, ops)) =
         occursInExpN (k, Whnf.normalize (#toInternal(ops) (), I.id)) MERGE Fri Aug 22 23:09:53 2003 --cs *)
      | occursInExpN (k, I.FgnExp csfe) =
        I.FgnExpStd.fold csfe (fn (U, DP) => DP orelse (occursInExp (k, Whnf.normalize (U, I.id)))) false

   (* no case for Redex, EVar, EClo *)


    and occursInHead (k, I.BVar (k')) = (k = k')
      | occursInHead (k, I.Const _) = false
      | occursInHead (k, I.Def _) = false
      | occursInHead (k, I.FgnConst _) = false
      | occursInHead (k, I.Proj _) = false
      (* no case for FVar *)

    and occursInSpine (_, I.Nil) = false
      | occursInSpine (k, I.App (U, S)) = occursInExpN (k, U) orelse occursInSpine (k, S)
      (* no case for SClo *)

    and occursInDec (k, I.Dec (_, V)) = occursInExpN (k, V)
    and occursInDecP (k, (D, _)) = occursInDec (k, D)

    and occursInExp (k, U) = occursInExpN (k, Whnf.normalize (U, I.id))


    (* dot1inv w = w'

       Invariant:
       If   G, A |- w : G', A
       then G |- w' : G'
       and  w = 1.w' o ^
    *)
    fun dot1inv (w) = strengthenSub (I.comp (I.shift, w), I.shift)

    (* shiftinv (w) = w'

       Invariant:
       If   G, A |- w : G'
       and  1 does not occur in w
       then w  = w' o ^
    *)
    fun shiftinv (w) = strengthenSub (w, I.shift)

    fun peel w =
      if isIdx1(I.bvarSub (1, w)) then dot1inv w else shiftinv w

    fun peeln (0, w) = w
      | peeln (n, w) = peeln (n-1, peel w)

    fun popn (0, Psi) = (Psi, I.Null)
      | popn (n, I.Decl (Psi, T.UDec D)) =
        let
          val (Psi', G') = popn (n-1, Psi)
        in
          (Psi', I.Decl (G', D))
        end


    (* domain (G2, w) = n'

       Invariant:
       If   G2 |- w: G1   and w weakening substitution
       then n' = |G1|
    *)
    fun domain (G, I.Dot (I.Idx _, s)) = domain (G, s) + 1
      | domain (I.Null, I.Shift 0) = 0
      | domain (G as I.Decl _, I.Shift 0) = domain (G, I.Dot (I.Idx 1, I.Shift 1))
      | domain (I.Decl (G, _), I.Shift n) = domain (G, I.Shift (n-1))


    (* strengthen (Psi, (a, S), w, m) = (Psi', w')

       This function traverses the spine, and finds
       all variables in a position input/output position m
       (hence strenghten might not be a good name for it, because it is to general.)

       Invariant:
       If   |- Psi ctx
       and  |- Psi1 ctx      where Psi1 is a subcontext of Psi
       and  Sigma (a) = {x1:A1} .. {xn:An} type
       and  Psi |- S : m1{x1:A1} .. mn{xn:An} > type
       and  Psi |- w : Psi1
       and  m mode
       then |- Psi' ctx
       and  Psi |- w' : Psi'
       where Psi' extends Psi1 (but is a subset of Psi?)
    *)

    fun strengthen (Psi, (a, S), w, m) =
      let
        val mS = modeSpine a

        fun args (I.Nil, M.Mnil) = nil
          | args (I.App (U, S'), M.Mapp (M.Marg (m', _), mS)) =
              let
                val L = args (S', mS)
              in
                (case M.modeEqual (m, m')
                   of true => U :: L
                    | false => L)
              end


        fun strengthenArgs (nil, s) =  nil
          | strengthenArgs (U :: L, s) =
              strengthenExp (U, s) :: strengthenArgs (L, s)

        fun occursInArgs (n, nil) = false
          | occursInArgs (n, U :: L) =
            (occursInExp (n, U) orelse occursInArgs (n, L))

        fun occursInPsi (n, (nil, L)) =
              occursInArgs (n, L)
          | occursInPsi (n, (T.UDec (I.Dec (_, V)) :: Psi1, L)) =
              occursInExp (n, V) orelse occursInPsi (n+1, (Psi1, L))
          | occursInPsi (n, (T.UDec (I.BDec (_, (cid, s))) :: Psi1, L)) =
              let
                val I.BlockDec (_, _, G, _) = I.sgnLookup cid
              in
                occursInSub (n, s, G) orelse occursInPsi (n+1, (Psi1, L))
              end
        and occursInSub (_, _, I.Null) = false
          | occursInSub (n, I.Shift k, G) =
              occursInSub (n, I.Dot (I.Idx (k+1), I.Shift (k+1)), G)
          | occursInSub (n, I.Dot (I.Idx k, s), I.Decl (G, _)) =
              (n = k) orelse occursInSub (n, s, G)
          | occursInSub (n, I.Dot (I.Exp U, s), I.Decl (G, _)) =
              occursInExp (n, U) orelse occursInSub (n, s, G)
          | occursInSub (n, I.Dot (I.Block _, s), I.Decl (G, _)) =
              occursInSub (n, s, G)   (* is this ok? -- cs *)
          (* no other cases *)

        and occursInG (n, I.Null, k) = k n
          | occursInG (n, I.Decl (G, I.Dec (_, V)), k) =
              occursInG (n, G, fn n' => occursInExp (n', V) orelse k (n'+ 1))

        fun occursBlock (G, (Psi2, L)) =
          let
            fun occursBlock (I.Null, n) = false
              | occursBlock (I.Decl (G, D), n) =
                  occursInPsi (n, (Psi2, L)) orelse occursBlock (G, n+1)
          in
            occursBlock (G, 1)
          end

        (* testBlock (G, (bw, w1)) = (bw', w')

           Invariant:
           If   |- G ctx
           and  |- G1 ctx
           and  |- G2 ctx
           and  G1 |- w1 : G2, G
           and  bw is a boolean value
           then there ex. a G1'
           s.t. |- G1' ctx
           and  G1' |- w' : G2
           and  bw' = bw or (G1 =/= G1')
         *)
        fun inBlock (I.Null, (bw, w1)) = (bw, w1)
          | inBlock (I.Decl (G, D), (bw, w1)) =
            if isIdx1(I.bvarSub (1, w1)) then
              inBlock (G, (true, dot1inv w1))
            else inBlock (G, (bw, strengthenSub (w1, I.shift)))

        fun blockSub (I.Null, w) = (I.Null, w)
          | blockSub (I.Decl (G, I.Dec (name, V)), w) =
            let
              val (G', w') = blockSub (G, w)
              val V' = strengthenExp (V, w')
            in
              (I.Decl (G', I.Dec (name, V')), I.dot1 w')
            end

        (* strengthen' (Psi1, Psi2, S, w1) =  (Psi', w')

           Invariant:
           If   |- Psi1 ctx
           and  Psi1 |- Psi2 ctx      (Psi2 is a list to maintain order)
           and  |- Psi3 ctx
           and  Psi1 |- w1 : Psi3     where w1 is a weakening substitution
           and  Psi1, Psi2 |- S : V1 > V2
           then |- Psi' ctx
           and  Psi1 |- w' : Psi'     where w' is a weakening substitution
           where Psi3 < Psi' < Psi1   (Psi' contains all variables of Psi3
                                       and all variables occuring in m
                                       position in S)
        *)
        fun strengthen' (I.Null, Psi2, L, w1 (* =  I.id *)) = (I.Null, I.id, I.id)
          | strengthen' (I.Decl (Psi1, LD as T.UDec (I.Dec (name, V))), Psi2, L, w1) =
            if isIdx1(I.bvarSub (1, w1)) then
              let
                val w1' = dot1inv w1
                val (Psi1', w', z') = strengthen' (Psi1, LD :: Psi2, L, w1')
                val V' = strengthenExp (V, w')
              in
                (I.Decl (Psi1', T.UDec (I.Dec (name, V'))), I.dot1 w', I.dot1 z')
              end
            else
              if occursInPsi (1, (Psi2, L)) then
                let
                  val w1' = strengthenSub (w1, I.shift)
                  val (Psi1', w', z') = strengthen' (Psi1, LD :: Psi2, L, w1')
                  val V' = strengthenExp (V, w')
                in
                  (I.Decl (Psi1', T.UDec (I.Dec (name, V'))), I.dot1 w', I.comp (z', I.shift))
                end
              else
                let
                  val w1' = strengthenSub (w1, I.shift)
                  val w2 = I.shift
                  val (Psi2', w2') = strengthenPsi' (Psi2, w2)
                  val L' = strengthenArgs (L, w2')
                  val (Psi1'', w', z') = strengthen' (Psi1, Psi2', L', w1')
                in
                  (Psi1'', I.comp (w', I.shift), z')
                end
          | strengthen' (I.Decl (Psi1, D as T.PDec (name, F, NONE, NONE)), Psi2, L, w1) =
            let
              val w1' = dot1inv w1
              val (Psi1', w', z') = strengthen' (Psi1, D :: Psi2, L, w1')
              val F' = strengthenFor (F, w')
            in
              (I.Decl (Psi1', T.PDec (name, F', NONE, NONE)), I.dot1 w', I.dot1 z')
            end
          | strengthen' (I.Decl (Psi1, LD as T.UDec (I.BDec (name, (cid, s)))), Psi2, L, w1) =
            let  (* blocks are always used! *)
              val w1' = dot1inv w1
              val (Psi1', w', z') = strengthen' (Psi1, LD :: Psi2, L, w1')
              val s' = strengthenSub (s, w')
            in
              (I.Decl (Psi1', T.UDec (I.BDec (name, (cid, s')))), I.dot1 w', I.dot1 z')
            end
      in
        strengthen' (Psi, nil, args (S, mS), w)
      end





    fun lookupIH (Psi, L, a) =
        let
          fun lookupIH' (b::L, a, k)=
              if a = b then k
              else lookupIH' (L, a, k-1)
        in
          lookupIH' (L, a, I.ctxLength Psi)
        end


    (* createSub (Psi, L) = t'

       Invariant:
       If  |- Psi = Psi0, Psi1 ctx
       and Psi0 contains all declarations for invariants in L
       and |Psi0| = n
       and |L| = k
       and n = k + m - 1
       then Psi |- t' = m, m+1 ... n. ^n :  Psi0
    *)
    fun createIHSub (Psi, L) =
         T.Shift (I.ctxLength Psi - 1 (*List.length L *))


    (* transformInit (Psi, (a, S), w1) = (w', s')

       Invariant:
       If   |- Psi ctx
       and  Sigma (a) = {x1:A1} .. {xn:An} type
       and  Psi |- S : m1{x1:A1} .. mn{xn:An} type > type
       and  Psi |- w1 : Psi+
       then |- Gamma+ ctx
       and  Gamma+ = +x(k1):A(k1), ... +x(km):A(km)
       and  Psi+ |- s' : Gamma+
       and  x1:A1 .. xn:An |- w: Gamma+    (w weakening substitution)
    *)
    fun transformInit (Psi, L, (a, S), w1) =
      let
        val mS = modeSpine a
        val V = typeOf a

        (* transformInit' ((S, mS), V, (w, s)) = (w', s')

           Invariant:
           If   Psi |- S : V > type
           and  x1:A1...x(j-1):A(j-1) |- V = mj{xj:Aj} .. mn{xn:An} type : kind
           and  x1:A1...x(j-1):A(j-1) |- w : +x1:A1... +x(j-1):A(j-1)
           and  Psi |- w1 : Psi+
           and  Psi+ |- s : +x1:A1... +x(j-1):A(j-1)
           then x1:A1...xn:An |- w' : +x1:A1... +xn:An
           and  Psi+ |- s' : +x1:A1 .. +xn:An
        *)

        fun transformInit' ((I.Nil, M.Mnil), I.Uni I.Type, (w, s)) = (w, s)
          | transformInit' ((I.App (U, S), M.Mapp (M.Marg (M.Minus, _), mS)),
                            I.Pi (_, V2), (w, s)) =
            let
              val w' = I.comp (w, I.shift)
              val s' = s
            in
              transformInit' ((S, mS), V2, (w', s'))
            end
          | transformInit' ((I.App (U, S), M.Mapp (M.Marg (M.Plus, _), mS)),
                            I.Pi ((I.Dec (name, V1), _), V2), (w, s)) =
            let
              val V1' = strengthenExp (V1, w)
              val w' = I.dot1 w
              val U' = strengthenExp (U, w1)
              val s' = T.dotEta (T.Exp U', s)
            in
              transformInit' ((S, mS), V2, (w', s'))
            end
      in
        transformInit' ((S, mS), V, (I.id, createIHSub (Psi, L)))
      end

    (* transformConc ((a, S), w) = P

       Invariant:
       If   Sigma (a) = {x1:A1} .. {xn:An} type
       and  Psi |- S : m1{x1:A1} .. mn{xn:An} type > type
       and  Psi |- w : PsiAll
       then P is proof term consisting of all - objects of S,
            defined in PsiAll
    *)
    fun transformConc ((a, S), w) =
      let

        fun transformConc' (I.Nil, M.Mnil) =
              T.Unit
          | transformConc' (I.App (U, S'), M.Mapp (M.Marg (M.Plus, _), mS')) =
              transformConc' (S', mS')
          | transformConc' (I.App (U, S'), M.Mapp (M.Marg (M.Minus, _), mS')) =
              T.PairExp (strengthenExp (U, w), transformConc' (S', mS'))
      in
        transformConc' (S, modeSpine a)
      end


    (* renameExp f U = U'

       Invariant:
       U' = U module application of f to any projectoin contained
       in U.
    *)
    fun renameExp f (U as I.Uni _) = U
      | renameExp f (I.Pi ((D, DP), V)) =
          I.Pi ((renameDec f D, DP), renameExp f V)
      | renameExp f (I.Root (H, S)) =
          I.Root (renameHead f H, renameSpine f S)
      | renameExp f (I.Lam (D, U)) =
          I.Lam (renameDec f D, renameExp f U)
    and renameDec f (I.Dec (x, V)) =
          I.Dec (x, renameExp f V)
    and renameHead f (I.Proj bi) = f bi
      | renameHead f H = H
    and renameSpine f I.Nil = I.Nil
      | renameSpine f (I.App (U, S)) = I.App (renameExp f U, renameSpine f S)


    fun rename (I.BDec (_, (c, s)), V) =
        let
          val (G, L) = I.constBlock c

          fun makeSubst (n, G, s, nil, f) = (G, f)
            | makeSubst (n, G, s,( D as I.Dec (x, V')) :: L, f) =
              if Subordinate.belowEq (I.targetFam V', I.targetFam V) then
                makeSubst (n+1, I.Decl (G, I.decSub (D, s)), I.dot1 s, L,
                           f)
              else
                makeSubst (n, G, I.comp (s, I.shift), L, f)

          val (G', f) = makeSubst (1, G, s, L, fn x => I.Proj x)
        in
          (G, renameExp f V)
        end


        fun append (G, I.Null) = G
          | append (G, I.Decl (G', D)) = I.Decl (append (G, G'), D)


        (* traverseNeg (L, wmap, projs)  (Psi0, Psi, V) = ([w', PQ'], L')    [] means optional

           Invariant:
           If   |- Psi0 ctx      (context that contains induction hypotheses)
           and  Psi0 |- Psi ctx  (context of all assumptions)
           and  Psi0, Psi |- V : type
           then L' list of cases
           and  Psi0, Psi |- w' : Psi0, Psi'
           and  PQ'  is a pair that can generate a proof term
        *)
        fun traverseNeg (L, wmap, projs)  ((Psi0, Psi), I.Pi ((D as I.Dec (_, V1), I.Maybe), V2), w) =
            (case traverseNeg (L, wmap, projs)  ((Psi0, I.Decl (Psi, T.UDec D)), V2, I.dot1 w)
               of (SOME (w', PQ')) => SOME (peel w', PQ'))
          | traverseNeg (L, wmap, projs)  ((Psi0, Psi), I.Pi ((D as I.Dec (_, V1), I.No), V2), w) =
            (case traverseNeg (L, wmap, projs)  ((Psi0, I.Decl (Psi, T.UDec D)), V2, I.comp (w, I.shift))
               of (SOME (w', PQ')) => traversePos (L, wmap, projs)  ((Psi0, Psi, I.Null), V1, SOME (peel w', PQ')))
          | traverseNeg (L, wmap, projs)  ((Psi0, Psi), I.Root (I.Const a, S), w) =
                                        (* Psi0, Psi |- w : Psi0, Psi' *)
                                        (* Sigma (a) = Va *)
                                        (* Psi0, Psi |- S : {G} type > type *)
            let
              val Psi1 = append (Psi0, Psi)
                                        (* Psi1 = Psi0, Psi *)
              val w0 = I.Shift (I.ctxLength Psi)
                                        (* Psi1 |- w0 : Psi0 *)
              val (Psi', w', _) = strengthen (Psi1, (a, S), w0, M.Plus)
                                        (* |- Psi' ctx *)
                                        (* Psi1 |- w' : Psi' *)
              val (w'', s'') = transformInit (Psi', L, (a, S), w')
                                        (* Psi' |- s'' : G+ *)
                                        (* G |- w'' : G+ *)
              val _ = TomegaTypeCheck.checkCtx Psi'
            in
              (SOME (w', (fn P => (Psi', s'', P), transformConc ((a, S), w))))
            end

        and traversePos (L, wmap, projs)  ((Psi0, Psi, G), I.Pi ((D as I.BDec (x, (c, s)), _), V), SOME (w1, (P, Q))) =
            let
              val c' = wmap c
              val n = I.ctxLength Psi0 + I.ctxLength G

              val (Gsome, Lpi) = I.constBlock c
              val _ = TypeCheck.typeCheckCtx (T.coerceCtx (append(append(Psi0, Psi), T.embedCtx G)))
              val _ = TypeCheck.typeCheckSub (T.coerceCtx (append(append(Psi0, Psi), T.embedCtx G)), s, Gsome)
              val (Gsome', Lpi') = I.constBlock c'
              val _ = TypeCheck.typeCheckCtx (T.coerceCtx (append(append(Psi0, Psi), T.embedCtx G)))
              val _ = TypeCheck.typeCheckSub (T.coerceCtx (append(append(Psi0, Psi), T.embedCtx G)), s, Gsome')
            in
              traversePos (L, wmap, projs)  ((Psi0, Psi,
                            I.Decl (G,  (* T.UDec *) (I.BDec (x, (c', s))))),
                           V, SOME (I.dot1 w1, (P, Q)))
            end
          | traversePos (L, wmap, projs)  ((Psi0, G, B), V as I.Root (I.Const a, S), SOME (w1, (P, Q))) =
                                        (* Psi0 = x1::F1 ... xn::Fn *)
                                        (* |- Psi0 matches L *)
                                        (* Psi0, G, B |- V : type *)
                                        (* Psi0, G, B |- w1 : Psi0, G', B' *)
            let
              val Psi1 = append (Psi0, append (G, T.embedCtx B))
                                        (* Psi1 = Psi0, G, B *)
              val _ = TomegaTypeCheck.checkCtx (append(append(Psi0, G), T.embedCtx B))
              val n = domain (Psi1, w1) (* n = |Psi0, G', B'| *)
              val m = I.ctxLength Psi0  (* m = |Psi0| *)

              fun lookupbase a =
                  let
                    val s = I.conDecName (I.sgnLookup a)
                    val l = T.lemmaName s
                    val T.ValDec (_, P, F) = T.lemmaLookup l
                  in
                    (T.Const l, F)
                  end

              fun lookup (([b], NONE, F), a) =
                  if a=b then
                    let
                      val P = T.Var n
                    in
                      (P, F)
                    end
                  else lookupbase a
                | lookup (([b], SOME [lemma], F), a) =
                  if a = b then
                    let
                      val P = T.Redex (T.Const lemma, T.AppPrg (T.Var n, T.Nil))
                    in
                      (P, F)
                    end
                  else lookupbase a
                | lookup ((b :: L, SOME (lemma :: lemmas), T.And (F1, F2)), a) =
                  if a = b then
                    let
                      val P = T.Redex (T.Const lemma, T.AppPrg (T.Var n, T.Nil))
                    in
                      (P, F1)
                    end
                  else lookup ((L, SOME lemmas, F2), a)

              (* strengthened invariant Psi0 might be empty --cs Fri Apr 11 15:25:32 2003 *)
              val (HP, F) = if I.ctxLength Psi0 > 0 then
                              let
                                val T.PDec(_, F0, _, _) =  I.ctxLookup (Psi0, 1)
                              in
                                lookup ((L, projs, F0), a)
                              end
                            else lookupbase a


              (* apply ((S, mS), F')= (S'', F'')

                 Invariant:
                 Psi0, G, B |- S : V >> type
                   (mS is the corresponding mode spine)
                 and  Psi0, G', B |- F'  :: for
                 then Psi0, G', B |- F'' :: for
                 and  Psi0, G', B |- S'' :: F' >> F''
              *)

              fun apply ((S, mS), Ft) = applyW ((S, mS), T.whnfFor (Ft))
              and applyW ((I.Nil, M.Mnil), Ft') = (T.Nil, T.forSub Ft')
                | applyW ((I.App (U, S), M.Mapp (M.Marg (M.Plus, _), mS)),
                         (T.All (D, F'), t')) =
                                        (* Psi0, G', B' |- D = x:V' : type *)
                                        (* Psi0, G', B', x:V' |- F' :: for *)
                  let
                    val U' = strengthenExp (U, w1)
                                        (* Psi0, G', B' |- U' : V' *)
                    val (S'', F'') = apply ((S, mS), (F', T.Dot (T.Exp U', t')))
                                        (* Psi0, G', B' |- F'' :: for *)
                                        (* Psi0, G', B' |- S'' : F' [t'] >> F'' *)
                  in
                   (T.AppExp (U', S''), F'')
                                        (* Psi0, G', B' |- U' ; S''
                                                       : all {x:V'} F' >> F'' *)
                  end
                | applyW ((I.App (U, S), M.Mapp (M.Marg (M.Minus, _), mS)), Ft) =
                    applyW ((S, mS), Ft)

              val (S'', F'') = apply ((S, modeSpine a), (F, T.id))
                                        (* Psi0, G', B' |- F'' :: for *)
                                        (* Psi0, G', B' |- S'' :: F' >> F'' *)
              val _ = TomegaTypeCheck.checkFor (append (append (Psi0, G), T.embedCtx B),
                                                (T.forSub(F'', T.embedSub w1)))



              val P'' = T.Redex (HP (*T.Var k' *) , S'')  (* was T.Root  -cs Sun Jan  5 23:15:06 2003 *)
                                        (* Psi0, G', B' |- P'' :: F'' *)

              val b = I.ctxLength B     (* b = |B| = |B'| *)
              val w1' = peeln (b, w1)   (* Psi0, G |- w1' : Psi0, G' *)


              val (B', _) = strengthenCtx (B, w1')
                                        (* |- Psi0, G', B' ctx *)

              val n' = n - I.ctxLength B'   (* n' = |Psi0, G'| *)


              fun subCtx (I.Null, s) = (I.Null, s)
                | subCtx (I.Decl (G, D), s) =
                  let val (G', s') = subCtx (G, s)
                  in (I.Decl (G', I.decSub (D, s')), I.dot1 s')
                  end

              val (B'', _) = subCtx (B', w1')
              val _ = TomegaTypeCheck.checkCtx (append (append (Psi0, G), T.embedCtx B''))

              val (GB', iota) = T.deblockify  B'    (* Psi0, G' |- GB' ctx *)

              val _ = TypeCheck.typeCheckSub (GB', T.coerceSub iota, B')
                         handle TypeCheck.Error _ => raise Error' iota

              val RR = T.forSub (F'', iota)
                                        (* Psi0, G, B |- w1 : Psi0, G', B' *)
                                        (* Psi0, G', GB'  |- s' : Psi0, G', B' *)
                                        (* Psi0, G', GB' |- RR for *)

              val F''' = TA.raiseFor (GB', (RR, I.id))
                                          (* Psi0, G |- w1' : Psi0, G' *)
                                          (* Psi0, G' |- F''' for *)


              (* lift (B, (P, F)) = (P', F')

                 Invariant:
                 If   Psi0, G, B |- P :: F
                 then Psi0, G |- P'  :: F'
                 and  P' =  (lam B. P)
                 and  F' = raiseFor (B, F)
              *)
              fun lift (I.Null, P) = P
                | lift (I.Decl (G, D), P) =
                  let
                    val (Bint, _) = T.deblockify (I.Decl (I.Null, D))
                  in
                    lift (G, T.New (T.Lam (T.UDec D, P)))
                  end

              val P''' = lift (B', P'') (* Psi0, G' |- P''' :: F''' *)


              val _ = TomegaTypeCheck.checkCtx (append (Psi0, G))
              val _ = TomegaTypeCheck.checkFor (append (Psi0, G),
                                                (T.forSub(F''', T.embedSub w1')))

              val (Psi1'', w2, z2) = strengthen (Psi1, (a, S), w1, M.Minus)
                                        (* |- Psi0, Psi1'' ctx *)
                                        (* Psi0, G, B |- w2 : Psi1'' *)
                                        (* Psi1'' = Psi0, G3, B3' *)
                                        (* |B| = |GB'| *)
                                        (* Psi'' |-  z2 : Psi0, G', B' *)
                                        (* Psi0, G, B |- w2 : Psi0, G3, B3' *)
              val w3 = peeln (b, w2)    (* Psi0, G |- w3 : Psi0, G3 *)
              val z3 = peeln (b, z2)    (* Psi0, G3 |-  z3 : Psi0, G' *)


              val (Psi2, B3') = popn (b, Psi1'')
                                        (* Psi2 = Psi0, G3 *)

              val Pat' = transformConc ((a, S), w2)

                                        (* Psi0, G3, B3' |- Pat' :: For *)
              val F4 = T.forSub (F''', T.embedSub z3)
                                        (* Psi0, G3 |- F4 for *)
              val _ = TomegaTypeCheck.checkCtx (Psi1'')
              val _ = TomegaTypeCheck.checkCtx (append (Psi2, T.embedCtx B3'))

              val _ = TomegaTypeCheck.checkFor (Psi2, F4)
                handle _ => raise Error ""(* ' F4 *)

              val (B3, sigma3) = T.deblockify  B3'

              val Pat'' = T.normalizePrg (Pat', sigma3)
              val Pat = TA.raisePrg (B3, Pat'', F4)
                                        (* Psi0, G3 |- Pat :: F4  *)
                                        (* Here's a commutative diagram
                                           at work which one has to prove
                                           correct
                                        *)
              val _ = TomegaTypeCheck.checkPrg (Psi2, (Pat, F4))
              val t = T.Dot (T.Prg Pat, T.embedSub z3)
                                        (* Psi0, G3 |- t :: Psi0, G', x :: F4  *)
            in
              (SOME (w3,
                     (fn p => P (T.Let (T.PDec (NONE, F''', NONE, NONE), P''',
                                        T.Case (T.Cases [(Psi2, t, p)]))), Q)))
            end




    (* traverse (Psi0, L, Sig, wmap) = C'

       Invariant:
       If   |- Psi0  ctx
       and  L is a the theorem we would like to transform
       and  Sig is a signature
       and  forall (G, V) in Sig the following holds:
                    Psi0, G |- V : type
               and  head (V) in L
       and  wmap is a mapping of old labels L to L'
            where L' is a new label and w' is a weakensub
            with the following properties.
            If   Sig (L) = (Gsome, Lblock)
            and  Sig (L') = (Gsome, Lblock')
       then C' is a list of cases (corresponding to each (G, V) in Sig)
    *)
    fun traverse (Psi0, L, Sig, wmap, projs) =
      let


        fun traverseSig' nil = nil
          | traverseSig' ((G, V) :: Sig) =
            (TypeCheck.typeCheck (append (T.coerceCtx Psi0, G), (V, I.Uni I.Type));
             case traverseNeg (L, wmap, projs) ((Psi0, T.embedCtx G), V, I.id)
               of (SOME (wf, (P', Q'))) =>  traverseSig' Sig @ [(P' Q')])
      in
        traverseSig' Sig
      end




    (* transformWorlds (fams, W) = (W', wmap)

       Invariant:
       If   fams is the theorem to be compiled
       and  W a world with declarations,
       then W' is the new world stripped of all dynamic extensions
       and  wmap is a mapping of old labels L to L'
            where L' is a new label and w' is a weakensub
            with the following properties.
            If   Sig (L) = (Gsome, Lblock)
            and  Sig (L') = (Gsome, Lblock')
    *)
    fun transformWorlds (fams, T.Worlds cids) =
        let
          (* convertList (a, L, w) = L'

             Invariant:
             If   G0 |- G, L : ctx
             and  G0, G |- w : G0, G'
             then G0 |- G', L' ctx
          *)
          fun transformList (nil, w) = nil
            | transformList ((D as I.Dec (x, V)) :: L, w) =
              if List.foldr (fn (a, b) => b andalso Subordinate.belowEq (a, I.targetFam V)) true fams then
                transformList (L,  I.comp (w, I.shift))
              else
                let
                  val  L' = transformList (L, I.dot1 w)
                in
                  (I.Dec (x, strengthenExp (V, w))) :: L'
                end

          fun transformWorlds' (nil) = (nil, fn c => raise Error "World not found")
            | transformWorlds' (cid :: cids') =
              let
                val I.BlockDec (s, m, G, L) = I.sgnLookup cid
                (* Design decision: Let's keep all of G *)
                val L' = transformList (L, I.id)
                val (cids'', wmap) = transformWorlds' (cids')
                val cid' = I.sgnAdd (I.BlockDec (s, m, G, L'))
              in
                (cid' :: cids'', fn c => if c = cid then cid' else wmap c)
              end

          val (cids', wmap) = transformWorlds' (cids)

        in
          (T.Worlds cids', wmap)
        end


    (* dynamicSig (Psi0, fams, W) = Sig'

       Invariant:
       If   |- Psi0 ctx
       and  fams are the typfamilies to be converted
       and  W is the world in which the translation takes place
       then Sig' = (G1;V1) ... (Gn;Vn)
       and  |- Psi0, Gi ctx
       and  Psi, Gi |- Vi : type.
    *)
    fun dynamicSig (Psi0, a, T.Worlds cids) =
        let


          (* findDec (G, n, L, s, S) = S'

             Invariant:
             If   G |-  L : ctx
             and  G |- w: G'
             then |- G', L' ctx
          *)
          fun findDec (G, _, nil, w, Sig) = Sig
            | findDec (G, n, D :: L, w, Sig) =
              let
                val (D' as I.Dec (x, V')) = I.decSub (D, w)
                val b = I.targetFam V'
                val Sig' = if b = a then  (G, Whnf.normalize (V',I.id)) :: Sig
                           else Sig
              in
                findDec (G, n+1, L, I.Dot (I.Exp (I.Root (I.Proj (I.Bidx 1, n), I.Nil)), w), Sig')
              end

          (* mediateSub G = (G0, s)

             Invariant:
             If   . |- G ctx
             then Psi0 |- G0 ctx
             and  Psi0, G0 |- s : G
          *)
          fun mediateSub (I.Null) = (I.Null, I.Shift (I.ctxLength Psi0))
            | mediateSub (I.Decl (G, D)) =
                let
                  val (G0, s') = mediateSub G
                  val D' = I.decSub (D, s')
                in
                  (I.Decl (G0, D'), I.dot1 s')
                end


          fun findDecs' (nil, Sig) = Sig
            | findDecs' (cid :: cids', Sig) =
              let
                val I.BlockDec (s, m, G, L) = I.sgnLookup cid
                                        (* G |- L ctx *)
                val (G0, s') = mediateSub G
                                        (* Psi0, G0 |- s'' : G *)
                val D' = Names.decName (G0, I.BDec (NONE, (cid, s')))
                                        (* Psi0, G0 |- D : dec *)
                val s'' = I.comp (s', I.shift)
                                        (* Psi0, G0, D' |- s'' : G *)

                val Sig' = findDec (I.Decl (G0, D'), 1, L, s'', Sig)
              in
                findDecs' (cids', Sig')
              end
        in
          findDecs' (cids, nil)
        end

    (* staticSig Sig = Sig'

       Invariant:
       If   |- Psi0 ctx
       then Sig' = (c1:V1) ... (cn:Vn)
       and  . |- Vi : type.
    *)
    fun staticSig (Psi0, nil) = nil
      | staticSig (Psi0, I.ConDec (name, _, _, _, V, I.Type) :: Sig) =
          (I.Null, Whnf.normalize (V, I.Shift (I.ctxLength Psi0))) :: staticSig (Psi0, Sig)

    fun name [a] = I.conDecName (I.sgnLookup a)
      | name (a :: L) = I.conDecName (I.sgnLookup a) ^ "/" ^ (name L)

    (* convertPrg L = P'

       Invariant:
       If   L is a list of type families
       then P' is a conjunction of all programs resulting from converting
            the relational encoding of the function expressed by each type
            family in L into functional form
    *)

    fun convertPrg (L, projs) =
      let
        val (name, F0) = createIH L
        val D0 = T.PDec (SOME name, F0, NONE, NONE)
        val Psi0 = I.Decl (I.Null, D0)
        val Prec = fn p => T.Rec (D0, p)
        fun convertWorlds [a] =
            let
              val W = WorldSyn.lookup a (* W describes the world of a *)
            in
              W
            end
          | convertWorlds (a :: L') =
            let
              val W = WorldSyn.lookup a (* W describes the world of a *)
              val W' = convertWorlds L'
            in
              if T.eqWorlds (W, W') then W' else raise Error "Type families different in different worlds"
            end

        val W = convertWorlds L
        val (W', wmap) = transformWorlds (L, W)

        fun convertOnePrg (a, F) =
          let
            val name = nameOf a
            val V = typeOf a            (* Psi0 |- {x1:V1} ... {xn:Vn} type *)
            val mS = modeSpine a        (* |- mS : {x1:V1} ... {xn:Vn} > type *)
            val Sig = Worldify.worldify a
                                        (* Sig in LF(reg)   *)
            val dynSig = dynamicSig (Psi0, a, W)
            val statSig = staticSig (Psi0, Sig)
            val _ = map (fn (I.ConDec (_, _,_,_,U,V)) => TypeCheck.check (U, I.Uni  V)) Sig
            val _ = validSig (Psi0, statSig)
            val _ = validSig (Psi0, dynSig)

            val C0 = traverse (Psi0, L, dynSig, wmap, projs)
            (* init' F = P'

               Invariant:
               If   F = All x1:A1. ... All xn:An. F'
               and  f' does not start with a universal quantifier
               then P' P'' = Lam x1:A1. ... Lam xn:An P''
                    for any P''
            *)
            fun init (T.All ((D, _), F')) =
                let
                  val (F'', P') = init F'
                in
                  (F'', fn p => T.Lam (D, P' p))
                end
              | init F' = (F', fn p => p)

            val (F', Pinit) = init F
            val C = traverse (Psi0, L, statSig, wmap, projs)
                                        (* Psi0, x1:V1, ..., xn:Vn |- C :: F *)
          in
            Pinit (T.Case ((* F', *) T.Cases (C0 @ C)))
          end

        fun convertPrg' (nil, _) = raise Error "Cannot convert Empty program"
          | convertPrg' ([a], F) = convertOnePrg (a, F)
          | convertPrg' (a :: L', T.And (F1, F2)) = T.PairPrg (convertOnePrg (a, F1), convertPrg' (L', F2))

        val P = Prec (convertPrg' (L, F0))
      in
        P
      end

    fun installFor [cid] =
        let
          val F = convertFor [cid]
          val name = I.conDecName (I.sgnLookup cid)
          val _ = T.lemmaAdd (T.ForDec (name, F))
        in
          ()
        end


    fun depthConj (T.And (F1, F2)) =
        1+ depthConj F2
      | depthConj F = 1

    fun createProjection (Psi, depth, F as T.And (F1, F2), Pattern) =
          createProjection (I.Decl (Psi, T.PDec (NONE, F1, NONE, NONE)), depth+1,
                            T.forSub (F2, T.Shift 1),
                            T.PairPrg (T.Var (depth+2), Pattern))
      | createProjection (Psi, depth, F,  Pattern) =
          let
            val Psi' = I.Decl (Psi, T.PDec (NONE, F, NONE, NONE))
            val depth' = depth + 1
          in
            fn k => let
                      val T.PDec (_, F', _, _) = T.ctxDec (Psi', k)
                    in
                      (T.Case (T.Cases [(Psi',
                                       T.Dot (T.Prg (Pattern),
                                              T.Shift (depth')),
                                       T.Var k)]), F')
                    end
          end

    fun installProjection (nil, _, F, Proj) = nil
      | installProjection (cid :: cids, n, F, Proj) =
        let
          val (P', F') = Proj n
          val P = T.Lam (T.PDec (NONE, F, NONE, NONE), P')
          val F'' = T.All ((T.PDec (NONE, F, NONE, NONE), T.Explicit), F')
          val name = I.conDecName (I.sgnLookup cid)
          val _ = TomegaTypeCheck.checkPrg (I.Null, (P, F''))
          val lemma = T.lemmaAdd (T.ValDec ("#" ^ name, P, F''))
        in
          lemma :: installProjection (cids, n-1, F, Proj)
        end


    fun installSelection ([cid], [lemma], F1, main) =
        let
          val P = T.Redex (T.Const lemma, T.AppPrg (T.Const main, T.Nil))
          val name = I.conDecName (I.sgnLookup cid)
          val _ = TomegaTypeCheck.checkPrg (I.Null, (P, F1))
          val lemma' = T.lemmaAdd (T.ValDec (name, P, F1))
        in
          [lemma']
        end
      | installSelection (cid :: cids, lemma :: lemmas, T.And (F1, F2), main) =
        let
          val P = T.Redex (T.Const lemma, T.AppPrg (T.Const main, T.Nil))
          val name = I.conDecName (I.sgnLookup cid)
          val _ = TomegaTypeCheck.checkPrg (I.Null, (P, F1))
          val lemma' = T.lemmaAdd (T.ValDec (name, P, F1))
        in
          lemma' :: installSelection (cids, lemmas, F2, main)
        end


    fun installPrg [cid] =
        let
          val F = convertFor [cid]
          val P = convertPrg ([cid], NONE)
          val name = I.conDecName (I.sgnLookup cid)
          val _ = TomegaTypeCheck.checkPrg (I.Null, (P, F))
          val _ = if (!Global.chatter >= 4) then print ("[Redundancy Checker (factoring) ...") else ()
          val factP = Redundant.convert P
          val _ = if (!Global.chatter >= 4) then print ("done]\n") else ()

          val lemma = T.lemmaAdd (T.ValDec (name, factP, F))


        in
          (lemma, [], [])
        end
      | installPrg cids =
        let
          val F = convertFor cids
          val _ = TomegaTypeCheck.checkFor (I.Null, F)

          val Proj = createProjection (I.Null, 0, F, T.Var 1)
          val projs = installProjection (cids, depthConj F, F, Proj)

          val P = convertPrg (cids, SOME projs)
          val s = name cids
          val _ = TomegaTypeCheck.checkPrg (I.Null, (P, F))
          val _ = if (!Global.chatter >= 4) then print ("[Redundancy Checker (factoring) ...") else ()
          val factP = Redundant.convert P
          val _ = if (!Global.chatter >= 4) then print ("done]\n") else ()

          val lemma = T.lemmaAdd (T.ValDec (s, factP, F))

          val sels = installSelection (cids, projs, F, lemma)

        in
          (lemma, projs, sels)
        end



    fun mkResult 0 = T.Unit
      | mkResult n = T.PairExp (I.Root (I.BVar n, I.Nil), mkResult (n-1))

    fun convertGoal (G, V)  =
      let
        val a = I.targetFam V
        val W = WorldSyn.lookup a
        val (W', wmap) = transformWorlds ([a], W)
        val SOME (_, (P', Q')) = traversePos ([], wmap, NONE)
                                  ((I.Null, G, I.Null), V,
                                   SOME (I.Shift (I.ctxLength G),
                                         (fn P => (I.Null, T.id, P),  mkResult (I.ctxLength G))))
        val (_, _, P'') = P' Q'
      in
        P''
      end

  in
    val convertFor = convertFor
    val convertPrg = fn L => convertPrg (L, NONE)
    val installFor = installFor
    val installPrg = installPrg
    val traverse = traverse
    val convertGoal = convertGoal
  end
end (* functor FunSyn *)
