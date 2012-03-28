(* Printing of functional proof terms *)
(* Author: Carsten Schuermann *)

functor FunPrint ((*! structure FunSyn' : FUNSYN !*)
                  structure Formatter : FORMATTER
                  structure Names : NAMES
                  (*! sharing Names.IntSyn = FunSyn'.IntSyn !*)
                  structure Print : PRINT
                    sharing Print.Formatter = Formatter
                    (*! sharing Print.IntSyn = FunSyn'.IntSyn !*)
                      )
  : FUNPRINT =
struct
  (*! structure FunSyn = FunSyn' !*)
  structure Formatter = Formatter

  local
    structure F = FunSyn
    structure I = IntSyn
    structure Fmt = Formatter
    structure P = Print

    (* Invariant:

       The proof term must satisfy the following conditions:
       * proof term must have the structure
           Rec.     Lam ... Lam Case
                And Lam ... Lam Case
                ...
                And Lam ... Lam Case
         and the body of every case must be of the form
           (Let Decs in Case ...
           or
           Inx ... Inx Unit) *
         where Decs are always of the form
           New ... New App .. App Split .. Split Empty
     *)




    (* formatCtxBlock (G, (G1, s1)) = (G', s', fmts')

       Invariant:
       If   |- G ctx
       and  G |- G1 ctx
       and  G2 |- s1 : G
       then G' = G2, G1 [s1]
       and  G' |- s' : G, G1
       and  fmts is a format list of G1[s1]
    *)
    fun formatCtxBlock (G, (I.Null, s)) = (G, s, nil)
      | formatCtxBlock (G, (I.Decl (I.Null, D), s)) =
        let
          val D' = I.decSub (D, s)
          val fmt = P.formatDec (G, D')
        in
          (I.Decl (G, D'), I.dot1 s, [fmt])
        end
      | formatCtxBlock (G, (I.Decl (G', D), s)) =
        let
          val (G'', s'', fmts) = formatCtxBlock (G, (G', s))
          val D'' = I.decSub (D, s'')
          val fmt = P.formatDec (G'', D'')
        in
          (I.Decl (G'', D''), I.dot1 s'', fmts @
           [Fmt.String ",", Fmt.Break, fmt])
        end


    (* formatFor' (G, (F, s)) = fmts'

       Invariant:
       If   |- G ctx
       and  G |- s : Psi'
       and  Psi' |- F formula
       then fmts' is a list of formats for F
    *)
    fun formatFor' (G, (F.All (LD, F), s)) =
        (case LD
           of F.Prim D =>
             let
               val D' = Names.decName (G, D)
             in
               [Fmt.String "{{", P.formatDec
                (G, I.decSub (D', s)),
                Fmt.String "}}", Fmt.Break] @
               formatFor' (I.Decl (G, D'), (F, I.dot1 s))
             end
           | F.Block (F.CtxBlock (l, G')) =>
             let
               val (G'', s'', fmts) = formatCtxBlock (G, (G', s))
             in
               [Fmt.String "{",
                Fmt.Hbox fmts,
                Fmt.String "}", Fmt.Break] @
               formatFor' (G'', (F, s''))
             end)
      | formatFor' (G, (F.Ex (D, F), s)) =
        let
          val D' = Names.decName (G, D)
        in
          [Fmt.String "[[", P.formatDec
           (G, I.decSub (D', s)), Fmt.String "]]", Fmt.Break] @
          formatFor' (I.Decl (G, D'), (F, I.dot1 s))
        end
      | formatFor' (G, (F.True, s)) =
        [Fmt.String "True"]


    (* formatFor (Psi, F) names = fmt'
       formatForBare (Psi, F) = fmt'

       Invariant:
       If   |- Psi ctx
       and  Psi |- F = F1 ^ .. ^ Fn formula
       and  names is a list of n names,
       then fmt' is the pretty printed format
    *)
    fun formatFor (Psi, F) names =
      let

        fun nameLookup index = List.nth (names, index)

        (* formatFor1 (index, G, (F, s)) = fmts'

           Invariant:
           If   |- G ctx
           and  G |- s : Psi
           and  Psi |- F1 ^ .. ^ F(index-1) ^ F formula
           then fmts' is a list of pretty printed formats for F
        *)
        fun formatFor1 (index, G, (F.And (F1, F2), s)) =
              formatFor1 (index, G, (F1, s)) @ [Fmt.Break] @
              formatFor1 (index+1, G, (F2, s))
          | formatFor1 (index, G, (F, s)) =
              [Fmt.String (nameLookup index), Fmt.Space,
               Fmt.String "::",
               Fmt.Space, Fmt.HVbox (formatFor' (G, (F, s)))]

        fun formatFor0 Args =
          Fmt.Vbox0 0 1 (formatFor1 Args)
      in
        (Names.varReset I.Null; formatFor0 (0, F.makectx Psi, (F, I.id)))
      end

    fun formatForBare (G, F) = Fmt.HVbox (formatFor' (G, (F, I.id)))



    (* formatPro (Psi, P) names = fmt'

       Invariant:
       If   |- Psi ctx
       and  Psi; . |- P = rec x. (P1, P2, .. Pn) in F
       and  names is a list of n names,
       then fmt' is the pretty printed format of P
    *)
    fun formatPro Args names =
      let
        fun nameLookup index = List.nth (names, index)

        (* blockName (G1, G2) = G2'

           Invariant:
           If   G1 |- G2 ctx
           then G2' = G2 modulo new non-conficting variable names.
        *)
        fun blockName (G1, G2) =
          let
            fun blockName' (G1, I.Null) = (G1, I.Null)
              | blockName' (G1, I.Decl (G2, D)) =
                let
                  val (G1', G2') = blockName' (G1, G2)
                  val D' = Names.decName (G1, D)
                in
                  (I.Decl (G1', D'), I.Decl (G2', D'))
                end
            val (G1', G2') = blockName' (G1, G2)
          in
            G2'
          end

        (* ctxBlockName (G1, CB) = CB'

           Invariant:
           If   G1 |- CB ctxblock
           then CB' = CB modulo new non-conficting variable names.
        *)
        fun ctxBlockName (G1, F.CtxBlock (name, G2)) =
          F.CtxBlock (name, blockName (G1, G2))

        (* decName (G, LD) = LD'

           Invariant:
           If   G1 |- LD lfdec
           then LD' = LD modulo new non-conficting variable names.
        *)
        fun decName (G, F.Prim D) =  F.Prim (Names.decName (G, D))
          | decName (G, F.Block CB)= F.Block (ctxBlockName (G, CB))

        (* numberOfSplits Ds = n'

           Invariant:
           If   Psi, Delta |- Ds :: Psi', Delta'
           then n'= |Psi'| - |Psi|
        *)
        fun numberOfSplits Ds =
            let
              fun numberOfSplits' (F.Empty, n) = n
                | numberOfSplits' (F.New (_, Ds), n) = numberOfSplits' (Ds, n)
                | numberOfSplits' (F.App (_, Ds), n) = numberOfSplits' (Ds, n)
                | numberOfSplits' (F.Lemma (_, Ds), n) = numberOfSplits' (Ds, n)
                | numberOfSplits' (F.Split (_, Ds), n) = numberOfSplits' (Ds, n+1)
                | numberOfSplits' (F.Left (_, Ds), n) = numberOfSplits' (Ds, n)
                | numberOfSplits' (F.Right (_, Ds), n) = numberOfSplits' (Ds, n)
            in
              numberOfSplits' (Ds, 0)
            end

        (* psiName (Psi1, s, Psi2, l) = Psi1'

           Invariant:
           If   |- Psi1 ctx
           and  |- Psi1' ctx
           and  |- Psi2 ctx
           and  Psi2 = Psi2', Psi2''
           and  Psi1 |- s : Psi2
           and  |Psi2''| = l
           then Psi1' = Psi1 modulo variable naming
           and  for all x in Psi2 s.t. s(x) = x in Psi1'
        *)
        fun psiName (Psi1, s, Psi2, l) =
          let
            fun nameDec (D as I.Dec (SOME _, _), name) = D
              | nameDec (I.Dec (NONE, V), name) = I.Dec (SOME name, V)

            fun namePsi (I.Decl (Psi, F.Prim D), 1, name) =
                  I.Decl (Psi, F.Prim (nameDec (D, name)))
              | namePsi (I.Decl (Psi, LD as F.Prim D), n, name) =
                  I.Decl (namePsi (Psi, n-1, name), LD)
              | namePsi (I.Decl (Psi, F.Block (F.CtxBlock (label, G))), n, name) =
                let
                  val (Psi', G') = nameG (Psi, G, n, name, fn n' => namePsi (Psi, n', name))
                in
                  I.Decl (Psi', F.Block (F.CtxBlock (label, G')))
                end

            and nameG (Psi, I.Null, n, name, k) = (k n, I.Null)
              | nameG (Psi, I.Decl (G, D), 1, name, k) = (Psi, I.Decl (G, nameDec (D, name)))
              | nameG (Psi, I.Decl (G, D), n, name, k) =
                let
                  val (Psi', G') = nameG (Psi, G, n-1, name, k)
                in
                  (Psi', I.Decl (G', D))
                end


            fun ignore (s, 0) = s
              | ignore (I.Dot (_, s), k) = ignore (s, k-1)
              | ignore (I.Shift n, k) =
                  ignore (I.Dot (I.Idx (n+1), I.Shift (n+1)), k-1)

            fun copyNames (I.Shift n, G as I.Decl _) Psi1=
                  copyNames (I.Dot (I.Idx (n+1), I.Shift (n+1)), G) Psi1
              | copyNames (I.Dot (I.Exp _, s), I.Decl (G, _)) Psi1=
                  copyNames (s, G) Psi1
              | copyNames (I.Dot (I.Idx k, s), I.Decl (G, I.Dec (NONE, _))) Psi1 =
                  copyNames (s, G) Psi1
              | copyNames (I.Dot (I.Idx k, s), I.Decl (G, I.Dec (SOME name, _))) Psi1 =
                let
                  val Psi1' = namePsi (Psi1, k, name)
                in
                  copyNames (s, G) Psi1'
                end
              | copyNames (I.Shift _, I.Null) Psi1 = Psi1

            fun psiName' (I.Null) = I.Null
              | psiName' (I.Decl (Psi, D)) =
                let
                  val Psi' = psiName' Psi
                in
                  I.Decl (Psi', decName (F.makectx Psi', D))
                end
          in
            psiName' (copyNames (ignore (s, l), F.makectx Psi2) Psi1)
          end


        (* merge (G1, G2) = G'

           Invariant:
           G' = G1, G2
        *)
        fun merge (G1, I.Null) = G1
          | merge (G1, I.Decl (G2, D)) =
              I.Decl (merge (G1, G2), D)

        (* formatCtx (Psi, G) = fmt'

           Invariant:
           If   |- Psi ctx
           and  Psi |- G ctx
           then fmt' is a pretty print format of G
        *)
        fun formatCtx (Psi, G) =
          let
            val G0 = F.makectx Psi

            fun formatCtx' (I.Null) = nil
              | formatCtx' (I.Decl (I.Null, I.Dec (SOME name, V))) =
                  [Fmt.String name, Fmt.String ":",
                   Print.formatExp (G0, V)]
              | formatCtx' (I.Decl (G, I.Dec (SOME name, V))) =
                  (formatCtx' G) @
                  [Fmt.String ",", Fmt.Break,
                   Fmt.String name, Fmt.String ":",
                   Print.formatExp (merge (G0, G), V)]
          in
            Fmt.Hbox (Fmt.String "|" :: (formatCtx' G @ [Fmt.String "|"]))
          end

        (* formatTuple (Psi, P) = fmt'

           Invariant:
           If   |- Psi ctx
           and  Psi; Delta |- P = Inx (M1, Inx ... (Mn, Unit))
           then fmt' is a pretty print format of (M1, .., Mn)
        *)
        fun formatTuple (Psi, P) =
          let
            fun formatTuple' (F.Unit) = nil
              | formatTuple' (F.Inx (M, F.Unit)) =
              [Print.formatExp (F.makectx Psi, M)]
              | formatTuple' (F.Inx (M, P')) =
              (Print.formatExp (F.makectx Psi, M) ::
               Fmt.String "," :: Fmt.Break :: formatTuple' P')
          in
            case P
              of (F.Inx (_, F.Unit)) => Fmt.Hbox (formatTuple' P)
              | _ => Fmt.HVbox0 1 1 1
                (Fmt.String "(" :: (formatTuple' P @ [Fmt.String ")"]))
          end

        (* formatSplitArgs (Psi, L) = fmt'

           Invariant:
           If   |- Psi ctx
           and  L = (M1, .., Mn)
           and  Psi |- Mk:Ak for all 1<=k<=n
           then fmt' is a pretty print format of (M1, .., Mn)
        *)
        fun formatSplitArgs (Psi, L) =
          let
            fun formatSplitArgs' (nil) = nil
              | formatSplitArgs' (M :: nil) =
                  [Print.formatExp (F.makectx Psi, M)]
              | formatSplitArgs' (M :: L) =
                  (Print.formatExp (F.makectx Psi, M) ::
                   Fmt.String "," :: Fmt.Break :: formatSplitArgs' L)
          in
            if List.length L = 1 then Fmt.Hbox (formatSplitArgs' L)
            else Fmt.HVbox0 1 1 1
              (Fmt.String "(" :: (formatSplitArgs' L @ [Fmt.String ")"]))
          end

        (* frontToExp (Ft) = U'

           Invariant:
           G |- Ft = U' : V   for a G, V
        *)
        fun frontToExp (I.Idx k) = I.Root (I.BVar k, I.Nil)
          | frontToExp (I.Exp (U)) = U


        (* formatDecs1 (Psi, Ds, s, L) = L'

           Invariant:
           If   |- Psi ctx
           and  Psi; Delta |- Ds : Psi'; Delta'
           and  Psi' = x1:A1 .. xn:An
           and  Psi'' |- s : Psi
           and  for i<=n
                L = (M1 .. Mi)
                s.t   Psi'' |- Mi : Ai
           then L' extends L
           s.t. L = (M1 .. Mn)
                for all i <=n
                Psi'' |- Mi : Ai
                (and Mi is a splitting of a the result of an inductive call)
        *)
        fun formatDecs1 (Psi, F.Split (xx, Ds), I.Dot (Ft, s1), L) =
              formatDecs1 (Psi, Ds, s1, frontToExp (Ft) :: L)
          | formatDecs1 (Psi, F.Empty, s1, L) = L
          | formatDecs1 (Psi, Ds, I.Shift n, L) =
              formatDecs1 (Psi, Ds, I.Dot (I.Idx (n+1), I.Shift (n+1)), L)


        (* formatDecs0 (Psi, Ds) = (Ds', S')

           Invariant:
           If   |- Psi ctx
           and  Psi ; Delta |- Ds : Psi', Delta'
           and  Ds = App M1 ... App Mn Ds'   (where Ds' starts with Split)
           then S' = (M1, M2 .. Mn)
           and  Psi1, Delta1 |- Ds' : Psi1', Delta1'
                (for some Psi1, Delta1, Psi1', Delta1')
        *)
        fun formatDecs0 (Psi, F.App ((xx, M), Ds)) =
            let
              val (Ds', S) =
                formatDecs0 (Psi, Ds)
            in
              (Ds', I.App (M, S))
            end
          | formatDecs0 (Psi, Ds) = (Ds, I.Nil)


        (* formatDecs (index, Psi, Ds, (Psi1, s1)) = fmt'

           Invariant:
           If   |- Psi ctx
           and  Psi; Delta |- Ds : Psi'; Delta'
           and  Psi1 |- s1 : Psi, Psi'
           then fmt' is a pretty print format of Ds
        *)
        fun formatDecs (index, Psi, Ds as F.App ((xx, _), P), (Psi1, s1)) =
            let
              val (Ds', S) = formatDecs0 (Psi, Ds)
              val L' = formatDecs1 (Psi, Ds', s1, nil)
              val name = nameLookup index
            in
              Fmt.Hbox [formatSplitArgs (Psi1, L'), Fmt.Space,
                        Fmt.String "=", Fmt.Break,
                        Fmt.HVbox (Fmt.String name :: Fmt.Break ::
                                   Print.formatSpine (F.makectx Psi, S))]
            end
          | formatDecs (index, Psi, F.New (B as F.CtxBlock (_, G), Ds),
                        (Psi1, s1)) =
            let
              val B' = ctxBlockName (F.makectx Psi, B)
              val fmt =
                formatDecs (index, I.Decl (Psi, F.Block B'), Ds, (Psi1, s1))
            in
              Fmt.Vbox [formatCtx (Psi, G), Fmt.Break, fmt]
            end
          | formatDecs (index, Psi, F.Lemma (lemma, Ds), (Psi1, s1)) =
            let
              val (Ds', S) = formatDecs0 (Psi, Ds)
              val L' = formatDecs1 (Psi, Ds', s1, nil)
              val (F.LemmaDec (names, _, _)) = F.lemmaLookup lemma
            in
              Fmt.Hbox [formatSplitArgs (Psi1, L'), Fmt.Space,
                        Fmt.String "=", Fmt.Break,
                        Fmt.HVbox (Fmt.String (List.nth (names, index)) :: Fmt.Break ::
                                   Print.formatSpine (F.makectx Psi, S))]
            end
          | formatDecs (index, Psi, F.Left (_, Ds), (Psi1, s1)) =
            let
              val fmt =
                formatDecs (index, Psi, Ds, (Psi1, s1))
            in
              fmt
            end
          | formatDecs (index, Psi, F.Right (_, Ds), (Psi1, s1)) =
            let
              val fmt =
                formatDecs (index+1, Psi, Ds, (Psi1, s1))
            in
              fmt
            end

        (* formatLet (Psi, P, fmts) = fmts'

           Invariant:
           If   |- Psi ctx
           and  Psi; Delta |- P = Let . Case P' :: F
           and  fmts is a list of pretty print formats of P
           then fmts' extends fmts
           and  fmts also includes a pretty print format for P'
        *)
        fun formatLet (Psi, F.Let (Ds, F.Case (F.Opts
                                ((Psi1, s1, P1 as F.Let _) ::  nil))), fmts) =
            let
              val Psi1' = psiName (Psi1, s1, Psi, numberOfSplits Ds)
              val fmt = formatDecs (0, Psi, Ds, (Psi1', s1))
            in
              formatLet (Psi1', P1, fmts @ [fmt, Fmt.Break])
            end
          | formatLet (Psi, F.Let (Ds, F.Case (F.Opts
                                ((Psi1, s1, P1) ::  nil))), fmts) =
            let
              val Psi1' = psiName (Psi1, s1, Psi, numberOfSplits Ds)
              val fmt = formatDecs (0, Psi, Ds, (Psi1', s1))
            in
              Fmt.Vbox0 0 1 ([Fmt.String "let", Fmt.Break,
                              Fmt.Spaces 2, Fmt.Vbox0 0 1 (fmts @ [fmt]),
                              Fmt.Break,
                              Fmt.String "in", Fmt.Break,
                              Fmt.Spaces 2, formatPro3 (Psi1', P1),
                              Fmt.Break,
                              Fmt.String "end"])
            end


        (* formatPro3 (Psi, P) = fmt

           Invariant:
           If   |- Psi ctx
           and  Psi; Delta |- P :: F
           and  P = let .. in .. end | <..,..> | <>
           then fmt is a pretty print of P
        *)
        and formatPro3 (Psi, P as F.Unit) = formatTuple (Psi, P)
          | formatPro3 (Psi, P as F.Inx _) = formatTuple (Psi, P)
          | formatPro3 (Psi, P as F.Let _) = formatLet (Psi, P, nil)

        (* argsToSpine (Psi1, s, S) = S'

           Invariant:
           If   Psi1 |- s = M1 . M2 .. Mn. ^|Psi1|: Psi2
           and  Psi1 |- S : V1 > {Psi2} V2
           then Psi1 |- S' : V1 > V2
           and S' = S, M1 .. Mn
           where
           then Fmts is a list of arguments
        *)
        fun argsToSpine (s, I.Null, S) = S
          | argsToSpine (I.Shift (n), Psi, S) =
              argsToSpine (I.Dot (I.Idx (n+1), I.Shift (n+1)), Psi, S)
          | argsToSpine (I.Dot (Ft, s), I.Decl (Psi, D), S) =
              argsToSpine (s, Psi, I.App (frontToExp Ft, S))


        (* formatHead (index, Psi1, s, Psi2) = fmt'

           Invariant:
           If    Psi1 |- s : Psi2
           then  fmt is a format of the entire head
           where index represents the function name
           and   s the spine.
        *)
        fun formatHead (index, Psi', s, Psi) =
              Fmt.Hbox [Fmt.Space,
                        Fmt.HVbox (Fmt.String (nameLookup index) :: Fmt.Break ::
                                   Print.formatSpine (F.makectx Psi',
                                                      argsToSpine (s, Psi, I.Nil)))]


        (* formatPro2 (index, Psi, L) = fmts'

           Invariant:
           If   |- Psi ctx
           and  Psi |- L a list of cases
           then fmts' list of pretty print formats of L
        *)
        fun formatPro2 (index, Psi, nil) = nil
          | formatPro2 (index, Psi, (Psi', s, P) :: nil) =
            let
              val Psi'' = psiName (Psi', s, Psi, 0)
              val fhead = if index=0 then "fun" else "and"
            in
              [Fmt.HVbox0 1 5 1
               [Fmt.String fhead, formatHead (index, Psi'', s, Psi),
                Fmt.Space, Fmt.String "=", Fmt.Break,
                formatPro3 (Psi'', P)], Fmt.Break]
            end
          | formatPro2 (index, Psi, (Psi', s, P) :: O) =
            let
              val
                Psi'' = psiName (Psi', s, Psi, 0)
            in
              formatPro2 (index, Psi, O) @
              [Fmt.HVbox0 1 5 1
               [Fmt.String "  |", formatHead (index, Psi'', s, Psi),
                Fmt.Space, Fmt.String "=", Fmt.Break,
                formatPro3 (Psi'', P)], Fmt.Break]
            end

        (* formatPro1 (index, Psi, P) = fmts'

           Invariant:
           If   |- Psi ctx
           and  Psi; . |- P :: F
           and  P is either a Lam .. | Case ... | Pair ...
           then fmts' is alist of pretty print formats of P
        *)
        fun formatPro1 (index, Psi, F.Lam (D, P)) =
              formatPro1 (index, I.Decl (Psi, decName (F.makectx Psi, D)), P)
          | formatPro1 (index, Psi, F.Case (F.Opts Os)) =
              formatPro2 (index, Psi, Os)
          | formatPro1 (index, Psi, F.Pair (P1, P2)) =
              formatPro1 (index, Psi, P1) @ formatPro1 (index+1, Psi, P2)


        (* formatPro0 (Psi, P) = fmt'
           If   |- Psi ctx
           and  Psi; . |- P :: F
           then fmt' is a pretty print format of P
        *)
        fun formatPro0 (Psi, F.Rec (DD, P)) =
          Fmt.Vbox0 0 1 (formatPro1 (0, Psi, P))
      in
        (Names.varReset I.Null; formatPro0 Args)
      end

    fun formatLemmaDec (F.LemmaDec (names, P, F)) =
      Fmt.Vbox0 0 1 [formatFor (I.Null, F) names, Fmt.Break,
                     formatPro (I.Null, P) names]

    fun forToString Args names = Fmt.makestring_fmt (formatFor Args names)
    fun proToString Args names = Fmt.makestring_fmt (formatPro Args names)
    fun lemmaDecToString Args = Fmt.makestring_fmt (formatLemmaDec Args)

  in
    val formatFor = formatFor
    val formatForBare = formatForBare
    val formatPro = formatPro
    val formatLemmaDec = formatLemmaDec

    val forToString = forToString
    val proToString = proToString
    val lemmaDecToString = lemmaDecToString
  end
end;  (* signature FUNPRINT *)

