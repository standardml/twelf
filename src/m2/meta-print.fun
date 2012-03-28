(* Meta printer for proof states *)
(* Author: Carsten Schuermann *)

functor MetaPrint (structure Global : GLOBAL
                   structure MetaSyn' : METASYN
                   structure Formatter : FORMATTER
                   structure Print : PRINT
                   (*! sharing Print.IntSyn = MetaSyn'.IntSyn !*)
                     sharing Print.Formatter = Formatter
                   structure ClausePrint : CLAUSEPRINT
                   (*! sharing ClausePrint.IntSyn = MetaSyn'.IntSyn !*)
                     sharing ClausePrint.Formatter = Formatter)

  : METAPRINT =
struct
  structure MetaSyn = MetaSyn'

  local
    structure M = MetaSyn
    structure I = IntSyn
    structure F = Formatter

    fun modeToString M.Top = "+"
      | modeToString M.Bot = "-"

    (* depthToString is used to format splitting depth *)
    fun depthToString (b) = if b <= 0 then "" else Int.toString b

    fun fmtPrefix (GM) =
        let
          fun fmtPrefix' (M.Prefix (I.Null, I.Null, I.Null), Fmt) = Fmt
            | fmtPrefix' (M.Prefix (I.Decl (I.Null, D), I.Decl (I.Null, mode),
                                    I.Decl (I.Null, b)), Fmt) =
                [F.String (depthToString b),
                 F.String (modeToString mode),
                 Print.formatDec (I.Null, D)] @ Fmt
            | fmtPrefix' (M.Prefix (I.Decl (G, D), I.Decl (M, mode), I.Decl (B, b)), Fmt) =
                fmtPrefix' (M.Prefix (G, M, B),
                            [F.String ",", F.Space, F.Break,
                             F.String (depthToString b),
                             F.String (modeToString mode),
                             Print.formatDec (G, D)] @ Fmt)
        in
          F.HVbox (fmtPrefix' (GM, []))
        end

    fun prefixToString GM = F.makestring_fmt (fmtPrefix GM)

    fun stateToString (M.State (name, GM as M.Prefix (G, M, B), V)) =
          name ^ ":\n"
          ^ prefixToString GM ^ "\n--------------\n"
          ^ ClausePrint.clauseToString (G, V) ^ "\n\n"

    fun sgnToString (M.SgnEmpty) = ""
      | sgnToString (M.ConDec (e, S)) =
        (if !Global.chatter >= 4
           (* use explicitly quantified form *)
           then Print.conDecToString e ^ "\n"
         else
           if !Global.chatter >= 3
             (* use form without quantifiers, which is reparsable *)
             then ClausePrint.conDecToString e ^ "\n"
           else "")
        ^ sgnToString S
  in

    val modeToString = modeToString
    val sgnToString = sgnToString
    val stateToString = stateToString
    val conDecToString = ClausePrint.conDecToString

  end (* local *)
end; (* functor MetaPrint *)
