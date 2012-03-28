(* Weakening substitutions for meta substitutions *)
(* Author: Carsten Schuermann *)

functor FunWeaken ((*! structure FunSyn' : FUNSYN !*)
                   structure Weaken : WEAKEN
                   (*! sharing Weaken.IntSyn = FunSyn'.IntSyn !*)
                     ) : FUNWEAKEN =
struct
  (*! structure FunSyn = FunSyn' !*)

  local
    structure F = FunSyn
    structure I = IntSyn

    (* strengthenPsi (Psi, s) = (Psi', s')

       If   Psi0 |- Psi ctx
       and  Psi0 |- s Psi1
       then Psi1 |- Psi' = Psi[s^-1] ctx
       and  Psi0 |- s' : Psi1, Psi'
    *)
    fun strengthenPsi (I.Null, s) = (I.Null, s)
      | strengthenPsi (I.Decl (Psi, F.Prim D), s) =
        let
          val (Psi', s') = strengthenPsi (Psi, s)
        in
          (I.Decl (Psi', F.Prim (Weaken.strengthenDec (D, s'))), I.dot1 s')
        end
      | strengthenPsi (I.Decl (Psi, F.Block (F.CtxBlock (l, G))), s) =
        let
          val (Psi', s') = strengthenPsi (Psi, s)
          val (G'', s'') = Weaken.strengthenCtx (G, s')
        in
          (I.Decl (Psi', F.Block (F.CtxBlock (l, G''))), s'')
        end

    (* strengthenPsi' (Psi, s) = (Psi', s')

       If   Psi0 |- Psi ctx
       and  Psi0 |- s : Psi1
       then Psi1 |- Psi' = Psi[s^-1] ctx
       and  Psi0 |- s' : Psi1, Psi'  weakening substitution
    *)
    fun strengthenPsi' (nil, s) = (nil, s)
      | strengthenPsi' (F.Prim D :: Psi, s) =
        let
          val D' = Weaken.strengthenDec (D, s)
          val s' = I.dot1 s
          val (Psi'', s'') = strengthenPsi' (Psi, s')
        in
          (F.Prim D' :: Psi'', s'')
        end
      | strengthenPsi' (F.Block (F.CtxBlock (l, G)) :: Psi, s) =
        let
          val (G', s') = Weaken.strengthenCtx (G, s)
          val (Psi'', s'') = strengthenPsi' (Psi, s')
        in
          (F.Block (F.CtxBlock (l, G')) :: Psi'', s'')
        end
  in
    val strengthenPsi = strengthenPsi
    val strengthenPsi' = strengthenPsi'
  end
end (* functor FunWeaken *)
