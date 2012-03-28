(* Names of Constants and Variables *)
(* Author: Carsten Schuermann *)

functor FunNames (structure Global : GLOBAL
                  (*! structure FunSyn' : FUNSYN !*)
                  structure HashTable : TABLE where type key = string)
  : FUNNAMES =
struct

  (*! structure FunSyn = FunSyn' !*)

  exception Error of string

  (****************************************)
  (* Constants Names and Name Preferences *)
  (****************************************)

  (*
     Names (strings) are associated with constants (cids) in two ways:
     (1) There is an array nameArray mapping constants to print names (string),
     (2) there is a hashtable sgnHashTable mapping identifiers (strings) to constants.

     The mapping from constants to their print names must be maintained
     separately from the global signature, since constants which have
     been shadowed must be marked as such when printing.  Otherwise,
     type checking can generate very strange error messages such as
     "Constant clash: c <> c".

     In the same table we also record the fixity property of constants,
     since it is more a syntactic then semantic property which would
     pollute the lambda-calculus core.

     The mapping from identifers (strings) to constants is used during
     parsing.

     There are global invariants which state the mappings must be
     consistent with each other.
  *)

  (* nameInfo carries the print name and fixity for a constant *)
  datatype nameInfo = NameInfo of string

  local
    val maxCid = Global.maxCid
    (* nameArray maps constants to print names and fixity *)
    val nameArray = Array.array (maxCid+1, NameInfo "")
      : nameInfo Array.array

    (* sgnHashTable maps identifiers (strings) to constants (cids) *)
    val sgnHashTable : IntSyn.cid HashTable.Table = HashTable.new (4096)
    val hashInsert = HashTable.insertShadow sgnHashTable (* returns optional shadowed entry *)
    val hashLookup = HashTable.lookup sgnHashTable (* returns optional cid *)
    fun hashClear () = HashTable.clear sgnHashTable

  in
    (* reset () = ()
       Effect: clear name tables related to constants

       nameArray does not need to be reset, since it is reset individually
       for every constant as it is declared
    *)
    fun reset () = (hashClear ())

    (* override (cid, nameInfo) = ()
       Effect: mark cid as shadowed --- it will henceforth print as %name%
    *)
    fun override (cid, NameInfo (name)) =
        (* should shadowed identifiers keep their fixity? *)
          Array.update (nameArray, cid, NameInfo("%" ^ name ^ "%"))

    fun shadow NONE = ()
      | shadow (SOME(_,cid)) =
          override (cid, Array.sub (nameArray, cid))

    (* installName (name, cid) = ()
       Effect: update mappings from constants to print names and identifiers
               to constants, taking into account shadowing
    *)
    fun installName (name, lemma) =
        let
          val shadowed = hashInsert (name, lemma)       (* returns optional shadowed entry *)
        in
          (Array.update (nameArray, lemma, NameInfo (name));
           shadow shadowed)
        end

    (* nameLookup (name) = SOME(cid),  if cid has name and is not shadowed,
                         = NONE,   if there is no such constant
    *)
    fun nameLookup name = hashLookup name

    (* constName (cid) = name,
       where `name' is the print name of cid
    *)
    fun constName (cid) =
        (case Array.sub (nameArray, cid)
           of (NameInfo (name)) => name)

  end  (* local ... *)
end;  (* functor Names *)
