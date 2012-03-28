(* Meta Printer Version 1.3 *)
(* Author: Carsten Schuermann *)

functor StatePrint
  (structure Global : GLOBAL
   (*! structure IntSyn' : INTSYN !*)
   (*! structure Tomega' : TOMEGA !*)
   (*! sharing Tomega'.IntSyn = IntSyn' !*)
   structure State'  : STATE
   (*! sharing State'.IntSyn = IntSyn' !*)
   (*! sharing State'.Tomega = Tomega' !*)
   structure Names : NAMES
   (*! sharing Names.IntSyn = IntSyn' !*)
   structure Formatter' : FORMATTER
   structure Print : PRINT
     sharing Print.Formatter = Formatter'
     (*! sharing Print.IntSyn = IntSyn' !*)
   structure TomegaPrint : TOMEGAPRINT
   (*! sharing TomegaPrint.IntSyn = IntSyn' !*)
   (*! sharing TomegaPrint.Tomega = Tomega' !*)
     sharing TomegaPrint.Formatter = Formatter')
     : STATEPRINT =
struct
  structure Formatter = Formatter'
  (*! structure IntSyn = IntSyn' !*)
  (*! structure Tomega = Tomega' !*)
  structure State = State'


  exception Error of string

  local
    structure I = IntSyn
    structure T = Tomega
    structure S = State'
    structure N = Names
    structure Fmt = Formatter


(*
    fun nameCtx I.Null = I.Null
      | nameCtx (I.Decl (Psi, T.UDec D)) =
          I.Decl (nameCtx Psi,
                  T.UDec (Names.decName (T.coerceCtx Psi, D)))
      | nameCtx (I.Decl (Psi, T.PDec (_, F, TC))) =
          I.Decl (nameCtx Psi,
                  T.PDec (SOME "s", F, TC))   (* to be fixed! --cs *)

*)

      fun nameCtx Psi = Psi


    (* nameState S = S'

       Invariant:
       If   |- S state     and S unnamed
       then |- S' State    and S' named
       and  |- S = S' state
    *)
    fun nameState (S) = S

(*
    fun formatOrder (G, S.Arg (Us, Vs)) =
          [Print.formatExp (G, I.EClo Us), Fmt.String ":",
           Print.formatExp (G, I.EClo Vs)]
      | formatOrder (G, S.Lex Os) =
          [Fmt.String "{", Fmt.HVbox0 1 0 1 (formatOrders (G, Os)), Fmt.String "}"]
      | formatOrder (G, S.Simul Os) =
          [Fmt.String "[", Fmt.HVbox0 1 0 1 (formatOrders (G, Os)), Fmt.String "]"]

    and formatOrders (G, nil) = nil
      | formatOrders (G, O :: nil) = formatOrder (G, O)
      | formatOrders (G, O :: Os) = formatOrder (G, O) @
          [Fmt.String ",", Fmt.Break]  @ formatOrders (G, Os)

    (* format T = fmt'

       Invariant:
       If   T is a tag
       then fmt' is a a format descibing the tag T
    *)
    fun formatTag (G, S.Parameter l) = [Fmt.String "<p>"]
      | formatTag (G, S.Lemma (S.Splits k)) = [Fmt.String "<i",
                                                 Fmt.String (Int.toString k),
                                                 Fmt.String ">"]
      | formatTag (G, S.Lemma (S.RL)) = [Fmt.String "<i >"]
      | formatTag (G, S.Lemma (S.RLdone)) = [Fmt.String "<i*>"]
(*      | formatTag (G, S.Assumption k) = [Fmt.String "<a",
                                         Fmt.String (Int.toString k),
                                         Fmt.String ">"] *)

*)
    (* formatCtx (Psi) = fmt'

       Invariant:
       If   |- Psi ctx       and Psi is already named
       then fmt' is a format describing the context Psi
    *)
    fun formatCtx (I.Null) = []
      | formatCtx (I.Decl (I.Null, T.UDec D)) =
        if !Global.chatter >= 4 then
          [Fmt.HVbox ([Fmt.Break, Print.formatDec (I.Null, D)])]
        else
          [Print.formatDec (I.Null, D)]
      | formatCtx (I.Decl (I.Null, T.PDec (SOME s, F, _))) =
        if !Global.chatter >= 4 then
          [Fmt.HVbox ([Fmt.Break, Fmt.String s, Fmt.Space,
                       Fmt.String "::", Fmt.Space, TomegaPrint.formatFor (I.Null, F)])]
        else
          [Fmt.String s, Fmt.Space, Fmt.String "::", Fmt.Space,
           TomegaPrint.formatFor (I.Null, F)]
      | formatCtx (I.Decl (Psi, T.UDec D)) =
        let
          val G = T.coerceCtx Psi
        in
          if !Global.chatter >= 4 then
            formatCtx Psi @ [Fmt.String ",", Fmt.Break, Fmt.Break] @
            [Fmt.HVbox ([Fmt.Break, Print.formatDec (G, D)])]
          else
            formatCtx Psi @ [Fmt.String ",",  Fmt.Break] @
            [Fmt.Break, Print.formatDec (G, D)]
        end
      | formatCtx (I.Decl (Psi, T.PDec (SOME s, F, _))) =
        if !Global.chatter >= 4 then
          formatCtx Psi @ [Fmt.String ",", Fmt.Break, Fmt.Break] @
          [Fmt.HVbox ([Fmt.Break, Fmt.String s, Fmt.Space, Fmt.String "::", Fmt.Space, TomegaPrint.formatFor (Psi, F)])]
        else
          formatCtx Psi @ [Fmt.String ",",  Fmt.Break] @
          [Fmt.Break, Fmt.String s, Fmt.Space, Fmt.String "::", Fmt.Space,
           TomegaPrint.formatFor (Psi, F)]

    (* formatState S = fmt'

       Invariant:
       If   |- S state      and  S named
       then fmt' is a format describing the state S
    *)
    fun formatState (S.State (W, Psi, P, F, _)) =
          Fmt.Vbox0 0 1
          [Fmt.String "------------------------", Fmt.Break,
           Fmt.String "------------------------", Fmt.Break,
           TomegaPrint.formatPrg (Psi, P)]

    (* formatState S = S'

       Invariant:
       If   |- S state      and  S named
       then S' is a string descring state S in plain text
    *)
    fun stateToString S =
      (Fmt.makestring_fmt (formatState S))


  in
    val nameState = nameState
    val formatState = formatState
    val stateToString = stateToString
  end (* local *)
end (* functor MTPrint *)