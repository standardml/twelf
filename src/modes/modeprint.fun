(* Printing Mode Declarations *)
(* Author: Carsten Schuermann *)

functor ModePrint ((*! structure ModeSyn' : MODESYN !*)
                   structure Names : NAMES
                   (*! sharing Names.IntSyn = ModeSyn'.IntSyn !*)
                   structure Formatter : FORMATTER
                   structure Print : PRINT
                   (*! sharing Print.IntSyn = ModeSyn'.IntSyn !*)
                     sharing Print.Formatter = Formatter)
  : MODEPRINT =
struct
  (* structure ModeSyn = ModeSyn' *)

  local
    structure I = IntSyn
    structure M = ModeSyn
    structure F = Formatter
    structure P = Print

    fun modeToString M.Plus = "+"
      | modeToString M.Star = "*"
      | modeToString M.Minus = "-"
      | modeToString M.Minus1 = "-1"

    fun argToString (M.Marg (m, _)) = modeToString m

    fun nameDec (I.Dec (_, V) , M.Marg (_, name as SOME _)) = I.Dec (name, V)
      | nameDec (D, M.Marg (_, NONE)) = D

    fun makeSpine (G) =
        let
          fun makeSpine' (I.Null, _, S) = S
            | makeSpine' (I.Decl (G, _), k, S) =
                makeSpine' (G, k+1, I.App (I.Root (I.BVar k, I.Nil), S))
        in
          makeSpine' (G, 1, I.Nil)
        end

    fun fmtModeDec (cid, mS) =
        let
          val V = I.constType cid
          fun fmtModeDec' (G, _, M.Mnil) =
                [F.String "(",
                 P.formatExp (G, I.Root (I.Const (cid), makeSpine G)),
                 F.String ")"]
            | fmtModeDec' (G, I.Pi ((D, _), V'), M.Mapp (marg, S)) =
                let
                  val D' = nameDec (D, marg)
                  val D'' = Names.decEName (G, D')
                in
                  [F.String (argToString marg), F.String "{", P.formatDec (G, D''),
                   F.String "}", F.Break] @ (fmtModeDec' (I.Decl (G, D''), V', S))
                end
        in
          F.HVbox (fmtModeDec' (I.Null, V, mS))
        end

    fun fmtModeDecs ((cid, mS)::nil) = fmtModeDec (cid, mS)::nil
      | fmtModeDecs ((cid, mS)::mdecs) =
        fmtModeDec (cid, mS)::F.Break::fmtModeDecs mdecs

    fun modeToString cM = F.makestring_fmt (fmtModeDec cM)
    fun modesToString mdecs = F.makestring_fmt (F.Vbox0 0 1 (fmtModeDecs mdecs))
  in
    val modeToString = modeToString
    val modesToString = modesToString
  end (* local *)

end; (* functor ModePrint *)
