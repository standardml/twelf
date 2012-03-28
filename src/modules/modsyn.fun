(* Syntax for elaborated modules *)
(* Author: Kevin Watkins *)

functor ModSyn
  (structure Global : GLOBAL
   (*! structure IntSyn' : INTSYN !*)
   structure Names' : NAMES
   (*! sharing Names'.IntSyn = IntSyn' !*)
   (*! structure Paths' : PATHS !*)
   structure Origins : ORIGINS
   (*! sharing Origins.Paths = Paths' !*)
   structure Whnf : WHNF
   (*! sharing Whnf.IntSyn = IntSyn' !*)
   structure Strict : STRICT
   (*! sharing Strict.IntSyn = IntSyn' !*)
   structure IntTree : TABLE where type key = int
   structure HashTable : TABLE where type key = string)
  : MODSYN =
struct

  (*! structure IntSyn = IntSyn' !*)
  structure Names = Names'
  (*! structure Paths = Paths' !*)

  structure I = IntSyn

  exception Error of string

  datatype ConstInfo =
      ConstInfo of IntSyn.ConDec * Names.Fixity.fixity * (string list * string list) option * (string * Paths.occConDec option)

  datatype StructInfo =
      StructInfo of IntSyn.StrDec

  (* A module consists of:
     1. a map from cids to constant entries containing
          a. a constant declaration entry (IntSyn.ConDec)
          b. the fixity of the constant
          c. the name preference for the constant (if any)
     2. a map from mids to structure entries containing
          a. a structure declaration entry (IntSyn.StrDec)
          b. the namespace of the structure
     3. the top-level namespace of the module *)

  type module =
      StructInfo IntTree.Table * ConstInfo IntTree.Table * Names.namespace

  type action = IntSyn.cid * (string * Paths.occConDec option) -> unit
  type transform = IntSyn.cid * IntSyn.ConDec -> IntSyn.ConDec

  (* invariant: U in nf, result in nf *)
  fun mapExpConsts f U =
      let
        open IntSyn

        fun trExp (Uni L) = Uni L
          | trExp (Pi ((D, P), V)) = Pi ((trDec D, P), trExp V)
          | trExp (Root (H, S)) = Root (trHead H, trSpine S)
          | trExp (Lam (D, U)) = Lam (trDec D, trExp U)
          | trExp (U as FgnExp csfe) = FgnExpStd.Map.apply csfe trExp

        and trDec (Dec (name, V)) = Dec (name, trExp V)

        and trSpine Nil = Nil
          | trSpine (App (U, S)) = App (trExp U, trSpine S)

        and trHead (BVar n) = BVar n
          | trHead (Const cid) = trConst cid
          | trHead (Skonst cid) = trConst cid
          | trHead (Def cid) = trConst cid
          | trHead (NSDef cid) = trConst cid
          | trHead (FgnConst (csid, condec)) =
              FgnConst (csid, mapConDecConsts f condec)

        and trConst cid =
            let
              val cid' = f cid
            in
              case IntSyn.sgnLookup cid'
                of IntSyn.ConDec _ => Const cid'
                 | IntSyn.SkoDec _ => Skonst cid'
                 | IntSyn.ConDef _ => Def cid'
                 | IntSyn.AbbrevDef _ => NSDef cid'
            end
      in
        Whnf.normalize (trExp U, IntSyn.id)
      end

  and mapConDecConsts f (IntSyn.ConDec (name, parent, i, status, V, L)) =
        IntSyn.ConDec (name, parent, i, status, mapExpConsts f V, L)
    | mapConDecConsts f (IntSyn.ConDef (name, parent, i, U, V, L, Anc)) =
        IntSyn.ConDef (name, parent, i, mapExpConsts f U,
                       mapExpConsts f V, L, Anc) (* reconstruct Anc?? -fp *)
    | mapConDecConsts f (IntSyn.AbbrevDef (name, parent, i, U, V, L)) =
        IntSyn.AbbrevDef (name, parent, i, mapExpConsts f U,
                          mapExpConsts f V, L)
    | mapConDecConsts f (IntSyn.SkoDec (name, parent, i, V, L)) =
        IntSyn.SkoDec (name, parent, i, mapExpConsts f V, L)

  fun mapStrDecParent f (IntSyn.StrDec (name, parent)) =
        IntSyn.StrDec (name, f parent)

  fun mapConDecParent f (IntSyn.ConDec (name, parent, i, status, V, L)) =
        IntSyn.ConDec (name, f parent, i, status, V, L)
    | mapConDecParent f (IntSyn.ConDef (name, parent, i, U, V, L, Anc)) =
        IntSyn.ConDef (name, f parent, i, U, V, L, Anc) (* reconstruct Anc?? -fp *)
    | mapConDecParent f (IntSyn.AbbrevDef (name, parent, i, U, V, L)) =
        IntSyn.AbbrevDef (name, f parent, i, U, V, L)
    | mapConDecParent f (IntSyn.SkoDec (name, parent, i, V, L)) =
        IntSyn.SkoDec (name, f parent, i, V, L)

  fun strictify (condec as IntSyn.AbbrevDef (name, parent, i, U, V, IntSyn.Type)) =
      ((Strict.check ((U, V), NONE);
        IntSyn.ConDef (name, parent, i, U, V, IntSyn.Type, IntSyn.ancestor(U)))
       handle Strict.Error _ => condec)
    | strictify (condec as IntSyn.AbbrevDef _) = condec

  fun abbrevify (cid, condec) =
      (case condec
         of I.ConDec (name, parent, i, _, V, L) =>
            let
              val U = Whnf.normalize (I.Root (I.Const cid, I.Nil), I.id)
            in
              I.AbbrevDef (name, parent, i, U, V, L)
            end
          | I.SkoDec (name, parent, i, V, L) =>
            let
              val U = Whnf.normalize (I.Root (I.Skonst cid, I.Nil), I.id)
            in
              I.AbbrevDef (name, parent, i, U, V, L)
            end
          | I.ConDef (name, parent, i, U, V, L, Anc) =>
              I.AbbrevDef (name, parent, i, U, V, L)
          | I.AbbrevDef data => I.AbbrevDef data)

  (* In order to install a module, we walk through the mids in preorder,
     assigning global mids and building up a translation map from local
     mids to global mids.  Then we walk through the cids in dependency
     order, assigning global cids, building up a translation map from
     local to global cids, and replacing the cids contained in the terms
     with their global equivalents.

     NOTE that a module might not be closed with respect to the local
     cids; that is, it might refer to global cids not defined by the
     module.  It is a global invariant that such cids will still be in
     scope whenever a module that refers to them is installed. *)

  fun installModule ((structTable, constTable, namespace),
                     topOpt, nsOpt,
                     installAction, transformConDec) =
      let
        val structMap : IntSyn.mid IntTree.Table =
              IntTree.new (0)
        val constMap : IntSyn.cid IntTree.Table =
              IntTree.new (0)

        fun mapStruct mid = valOf (IntTree.lookup structMap mid)

        fun mapParent NONE = topOpt
          | mapParent (SOME parent) = SOME (mapStruct parent)

        fun mapConst cid =
            (case IntTree.lookup constMap cid
               of NONE => cid
                | SOME cid' => cid')

        fun doStruct (mid, StructInfo strdec) =
            let
              val strdec' = mapStrDecParent mapParent strdec
              val mid' = IntSyn.sgnStructAdd strdec'

              val parent = IntSyn.strDecParent strdec'
              val nsOpt = (case parent
                             of NONE => nsOpt
                              | SOME mid => SOME (Names.getComponents mid))
              val _ = (case nsOpt
                         of SOME ns => Names.insertStruct (ns, mid')
                          | _ => ())
              val _ = (case parent
                         of NONE => Names.installStructName mid'
                          | _ => ())

              val ns = Names.newNamespace ()
              val _ = Names.installComponents (mid', ns)
            in
              IntTree.insert structMap (mid, mid')
            end

        fun doConst (cid, ConstInfo (condec, fixity, namePrefOpt, origin)) =
            let
              val condec1 = mapConDecParent mapParent condec
              val condec2 = mapConDecConsts mapConst condec1
              val condec3 = transformConDec (cid, condec2)
              val cid' = IntSyn.sgnAdd condec3

              val parent = IntSyn.conDecParent condec3
              val nsOpt = (case parent
                             of NONE => nsOpt
                              | SOME mid => SOME (Names.getComponents mid))
              val _ = (case nsOpt
                         of SOME ns => Names.insertConst (ns, cid')
                          | _ => ())
              val _ = (case parent
                         of NONE => Names.installConstName cid'
                          | _ => ())

              val _ = installAction (cid', origin)

              val _ = (case fixity
                         of Names.Fixity.Nonfix => ()
                          | _ => Names.installFixity (cid', fixity))
              val _ = (case namePrefOpt
                         of NONE => ()
                          | SOME (n1, n2) =>
                              Names.installNamePref (cid', (n1, n2)))
            in
              IntTree.insert constMap (cid, cid')
            end
      in
        IntTree.app doStruct structTable;
        IntTree.app doConst constTable
      end

  val decToDef = strictify o abbrevify

  fun installStruct (strdec, module, nsOpt, installAction, isDef) =
      let
        val transformConDec = if isDef then decToDef
                              else (fn (_, condec) => condec)
        val mid = IntSyn.sgnStructAdd strdec
        val _ = case nsOpt
                  of SOME namespace => Names.insertStruct (namespace, mid)
                   | _ => ()
        val _ = Names.installStructName mid
        val ns = Names.newNamespace ()
        val _ = Names.installComponents (mid, ns)
      in
        installModule (module, SOME mid, NONE,
                       installAction, transformConDec)
      end

  fun installSig (module, nsOpt, installAction, isDef) =
      let
        val transformConDec = if isDef then decToDef
                              else (fn (_, condec) => condec)
      in
        installModule (module, NONE, nsOpt,
                       installAction, transformConDec)
      end

  fun abstractModule (namespace, topOpt) =
      let
        val structTable : StructInfo IntTree.Table =
              IntTree.new (0)
        val constTable : ConstInfo IntTree.Table =
              IntTree.new (0)

        val mapParent =
            (case topOpt
               of NONE => (fn parent => parent)
                | SOME mid => (fn SOME mid' => if mid = mid' then NONE
                                               else SOME mid'))

        fun doStruct (_, mid) =
            let
              val strdec = IntSyn.sgnStructLookup mid
              val strdec' = mapStrDecParent mapParent strdec
              val ns = Names.getComponents mid
            in
              IntTree.insert structTable (mid, StructInfo strdec');
              doNS ns
            end

        and doConst (_, cid) =
            let
              val condec = IntSyn.sgnLookup cid
              val condec' = mapConDecParent mapParent condec
              val fixity = Names.getFixity cid
              val namePref = Names.getNamePref cid
              val origin = Origins.originLookup cid
            in
              IntTree.insert constTable (cid, ConstInfo (condec', fixity, namePref, origin))
            end

        and doNS ns =
            (Names.appStructs doStruct ns;
             Names.appConsts doConst ns)
      in
        doNS namespace;
        (structTable, constTable, namespace)
      end

  fun instantiateModule (module as (_, _, namespace), transform) =
      let
        val transformConDec = transform namespace
        val mid = IntSyn.sgnStructAdd (IntSyn.StrDec ("wheresubj", NONE))
        val ns = Names.newNamespace ()
        val _ = Names.installComponents (mid, ns)
        val _ = installModule (module, SOME mid, NONE,
                               fn _ => (), transformConDec)
      in
        abstractModule (ns, SOME mid)
      end

  local
    val defList : string list ref = ref nil
    val defCount : int ref = ref 0
    val defs : module HashTable.Table = HashTable.new (4096)
    fun defsClear () = HashTable.clear defs
    val defsInsert = HashTable.insertShadow defs
    val defsLookup = HashTable.lookup defs
    val defsDelete = HashTable.delete defs
  in

    fun reset () = (defList := nil; defCount := 0;
                    defsClear ())

    fun resetFrom mark =
        let
          fun ct (l, i) = if i <= mark then l
                          else
                            let
                              val h::t = l
                            in
                              defsDelete h;
                              ct (t, i-1)
                            end
        in
          defList := ct (!defList, !defCount);
          defCount := mark
        end

    fun sigDefSize () = !defCount

    fun installSigDef (id, module) =
        (case defsInsert (id, module)
           of NONE => (defList := id::(!defList);
                       defCount := !defCount + 1)
            | SOME entry => (raise Error ("Shadowing: A signature named " ^ id
                                          ^ "\nhas already been declared");
                             defsInsert entry;
                             ()))

    val lookupSigDef = defsLookup

  end

end
