(* Mode Table *)
(* Author: Carsten Schuermann *)
(* Modified: Frank Pfenning, Roberto Virga *)

functor ModeTable
  ((*! structure IntSyn' : INTSYN !*)
   (* structure Names : NAMES *)
   (*! sharing Names.IntSyn = IntSyn' !*)
   structure Table : TABLE where type key = int
   (* structure Index : INDEX *)
   (*! sharing Index.IntSyn = IntSyn' !*)
   ) : MODETABLE =
struct
  (*! structure IntSyn = IntSyn' !*)
  exception Error of string

  local
    structure I = IntSyn
    structure M = ModeSyn

    val modeSignature : (M.ModeSpine list) Table.Table = Table.new(0);

    (* reset () = ()

       Effect: Resets mode array
    *)

    fun reset () = Table.clear modeSignature

    (* modeLookup a = mSOpt

       Looks up the mode of a in the mode array (if they are multiple, returns the last one
       inserted.
    *)
    fun modeLookup a =
          case (Table.lookup modeSignature a)
            of SOME (mS :: _) => SOME(mS)
             | NONE => NONE


    (* mmodeLookup a = mSs

       Looks up the modes of a in the mode array.
    *)
    fun mmodeLookup a =
          case (Table.lookup modeSignature a)
            of SOME mSs => mSs
             | NONE => nil


    (* installMode (a, mS) = ()

       Effect: the ModeSpine mS is stored with the type family a; if there were previous
               modes stored with a, they are replaced by mS
    *)
    fun installMode (a, mS) =
          Table.insert modeSignature (a, [mS])

    (* uninstallMode a = true iff a was declared in mode table
       Effect: the mode stored with a is removed
    *)
    fun uninstallMode a =
        case modeLookup a
          of NONE => false
           | SOME _ => (Table.delete modeSignature a; true)

    (* installMmode (a, mS) = ()

       Effect: the ModeSpine mS is stored with the type family a; if there were previous
               models stored with a, the new mode mS is added to them.
    *)
    fun installMmode (a, mS) =
          let
            val mSs = mmodeLookup a
          in
            Table.insert modeSignature (a, mS :: mSs)
          end

  in
    val reset = reset

    val installMode = installMode
    val modeLookup = modeLookup
    val uninstallMode = uninstallMode

    val installMmode = installMmode
    val mmodeLookup = mmodeLookup
  end
end;  (* functor ModeTable *)
