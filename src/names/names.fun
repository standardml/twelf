(* Names of Constants and Variables *)
(* Author: Frank Pfenning *)
(* Modified: Jeff Polakow *)

functor Names (structure Global : GLOBAL
	       structure IntSyn' : INTSYN
	       structure HashTable : TABLE where type key = string
               structure RedBlackTree : TABLE where type key = string
               structure IntTree : TABLE where type key = int)
  : NAMES =
struct

  structure IntSyn = IntSyn'

  exception Error of string

  (***********************)
  (* Operator Precedence *)
  (***********************)

  structure Fixity :> FIXITY =
  struct
    (* Associativity ascribed to infix operators
       assoc ::= left    e.g. `<-'
               | right   e.g. `->'
               | none    e.g. `==' from some object language
    *)
    datatype associativity = Left | Right | None

    (* Operator Precedence *)
    datatype precedence = Strength of int

    (* Maximal and minimal precedence which can be declared explicitly *)
    val maxPrec = Strength(9999)
    val minPrec = Strength(0)

    fun less (Strength(p), Strength(q)) = (p < q)
    fun leq (Strength(p), Strength(q)) = (p <= q)
    fun compare (Strength(p), Strength(q)) = Int.compare (p, q)

    fun inc (Strength(p)) = Strength(p+1)
    fun dec (Strength(p)) = Strength(p-1)

    (* Fixities ascribed to constants *)
    datatype fixity =
        Nonfix
      | Infix of precedence * associativity
      | Prefix of precedence
      | Postfix of precedence

    (* prec (fix) = precedence of fix *)
    fun prec (Infix(p,_)) = p
      | prec (Prefix(p)) = p
      | prec (Postfix(p)) = p
      | prec (Nonfix) = inc (maxPrec)

    (* toString (fix) = declaration corresponding to fix *)
    fun toString (Infix(Strength(p),Left)) = "%infix left " ^ Int.toString p
      | toString (Infix(Strength(p),Right)) = "%infix right " ^ Int.toString p
      | toString (Infix(Strength(p),None)) = "%infix none " ^ Int.toString p
      | toString (Prefix(Strength(p))) = "%prefix " ^ Int.toString p
      | toString (Postfix(Strength(p))) = "%postfix " ^ Int.toString p
      | toString (Nonfix) = "%nonfix"	(* not legal input *)

  end  (* structure Fixity *)

  (* argNumber (fix) = # of explicit arguments required *)
  (* for operator with fixity fix (0 if there are no requirements) *)
  fun argNumber (Fixity.Nonfix) = 0
    | argNumber (Fixity.Infix _) = 2
    | argNumber (Fixity.Prefix _) = 1
    | argNumber (Fixity.Postfix _) = 1

  (* checkAtomic (name, V, n) = ()
     if V expects exactly n arguments,
     raises Error(msg) otherwise
  *)
  fun checkAtomic (name, IntSyn.Pi (D, V), 0) =
      raise Error ("Constant " ^ name ^ " takes too many explicit arguments for given fixity")
    | checkAtomic (name, IntSyn.Pi (D, V), n) =
	checkAtomic (name, V, n-1)
    | checkAtomic (_, IntSyn.Uni _, 0) = ()
    | checkAtomic (_, IntSyn.Root _, 0) = ()
    | checkAtomic (name, _, _) =
      raise Error ("Constant " ^ name ^ " takes too few explicit arguments for given fixity")

  (* checkArgNumber (c, n) = ()
     if constant c expects exactly n explicit arguments,
     raises Error (msg) otherwise
  *)
  fun checkArgNumber (IntSyn.ConDec (name, i, V, L), n) =
	checkAtomic (name, V, i+n)
    | checkArgNumber (IntSyn.SkoDec (name, i, V, L), n) =
	checkAtomic (name, V, i+n)
    | checkArgNumber (IntSyn.ConDef (name, i, _, V, L), n) =
	checkAtomic (name, V, i+n)

  (* checkFixity (name, cidOpt, n) = ()
     if n = 0 (no requirement on arguments)
     or name is declared and has n exactly explicit arguments,
     raises Error (msg) otherwise
  *)
  fun checkFixity (_, _, 0) = ()
    | checkFixity (name, NONE, n) =
      raise Error ("Undeclared identifier " ^ name ^ " cannot be given fixity")
    | checkFixity (name, SOME(cid), n) =
	checkArgNumber (IntSyn.sgnLookup (cid), n)

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
  datatype nameInfo = NameInfo of string * Fixity.fixity

  local
    val maxCid = Global.maxCid
    (* nameArray maps constants to print names and fixity *)
    val nameArray = Array.array (maxCid+1, NameInfo ("", Fixity.Nonfix))
      : nameInfo Array.array

    (* sgnHashTable maps identifiers (strings) to constants (cids) *)
    val sgnHashTable : IntSyn.cid HashTable.Table = HashTable.new (4096)
    val hashInsert = HashTable.insertShadow sgnHashTable (* returns optional shadowed entry *)
    val hashLookup = HashTable.lookup sgnHashTable (* returns optional cid *)
    fun hashClear () = HashTable.clear sgnHashTable

    (* namePrefTable maps constants (cids) to name preferences (strings) *)
    val namePrefTable : (string * string) IntTree.Table = IntTree.new (0)
    val namePrefInsert = IntTree.insert namePrefTable
    val namePrefLookup = IntTree.lookup namePrefTable
    fun namePrefClear () = IntTree.clear namePrefTable
  in
    (* reset () = ()
       Effect: clear name tables related to constants

       nameArray does not need to be reset, since it is reset individually
       for every constant as it is declared
    *)
    fun reset () = (hashClear (); namePrefClear ())
    
    (* override (cid, nameInfo) = ()
       Effect: mark cid as shadowed --- it will henceforth print as %name%
    *)
    fun override (cid, NameInfo (name, fixity)) =
        (* should shadowed identifiers keep their fixity? *)
          Array.update (nameArray, cid, NameInfo("%" ^ name ^ "%", fixity))

    fun shadow NONE = ()
      | shadow (SOME(_,cid)) =
          override (cid, Array.sub (nameArray, cid))

    (* installName (name, cid) = ()
       Effect: update mappings from constants to print names and identifiers
               to constants, taking into account shadowing
    *)
    fun installName (name, cid) =
        let
	  val shadowed = hashInsert (name, cid)	(* returns optional shadowed entry *)
	in
	  (Array.update (nameArray, cid, NameInfo (name, Fixity.Nonfix));
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
	   of (NameInfo (name, _)) => name)

    (* installFixity (name, fixity) = ()
       Effect: install fixity for constant called name,
               possibly print declaration depending on chatter level
       raise Error if name does not refer to a constant
    *)
    fun installFixity (name, fixity) = 
        let
	  val cidOpt = hashLookup name
	in
	  (checkFixity (name, cidOpt, argNumber fixity);
	   if !Global.chatter >= 3
	     then print ((if !Global.chatter >= 4 then "%" else "")
				^ Fixity.toString fixity ^ " " ^ name ^ ".\n")
	   else ();
	   Array.update (nameArray, valOf cidOpt,
			 NameInfo (name, fixity)))
	end

    (* getFixity (cid) = fixity
       fixity defaults to Fixity.Nonfix, if nothing has been declared
    *)
    fun getFixity (cid) =
        (case Array.sub (nameArray, cid)
	   of (NameInfo (_, fixity)) => fixity)

    (* fixityLookup (name) = fixity
       where fixity is the associated with constant name,
       defaults to Fixity.Nonfix if name or fixity are undeclared
    *)
    fun fixityLookup (name) =
        (case hashLookup (name)
	   of SOME(cid) => getFixity (cid)
            | NONE => Fixity.Nonfix)

    (* Name Preferences *)
    (* ePref is the name preference for existential variables of given type *)
    (* uPref is the name preference for universal variables of given type *)

    (* installNamePref' (name, cidOpt, ePref, uPref) see installNamePref *)
    fun installNamePref' (name, NONE, (ePref, uPref)) =
        raise Error ("Undeclared identifier " ^ name ^ " cannot be given name preference")
      | installNamePref' (name, SOME(cid), (ePref, uPref)) =
	let
	  val L = IntSyn.constUni (cid)
	  val _ = case L
	            of IntSyn.Type =>
		       raise Error ("Object constant " ^ name ^ " cannot be given name preference\n"
				    ^ "Name preferences can only be established for type families")
		     | IntSyn.Kind => ()
	in
	  namePrefInsert (cid, (ePref, uPref))
	end

    (* installNamePref (name, (ePref, uPrefOpt)) = ()
       Effect: install name preference for type family named by 'name'
       raise Error if name is undeclared or name does not refer to a type family
    *)
    fun installNamePref (name, (ePref, SOME(uPref))) =
          installNamePref' (name, nameLookup name, (ePref, uPref))
      | installNamePref (name, (ePref, NONE)) =
	  installNamePref' (name, nameLookup name, (ePref, String.map Char.toLower ePref))

    (* local names are more easily re-used: they don't increment the
       counter associated with a name
    *)
    datatype Extent = Local | Global
    datatype Role = Exist | Univ of Extent

    fun extent (Exist) = Global
      | extent (Univ (ext)) = ext

    fun namePrefOf'' (Exist, NONE) = "X"
      | namePrefOf'' (Univ _, NONE) = "x"
      | namePrefOf'' (Exist, SOME(ePref, uPref)) = ePref
      | namePrefOf'' (Univ _, SOME(ePref, uPref)) = uPref

    fun namePrefOf' (Exist, NONE) = "X"
      | namePrefOf' (Univ _, NONE) = "x"
      | namePrefOf' (role, SOME(cid)) = namePrefOf'' (role, namePrefLookup (cid))

    (* namePrefOf (role, V) = name
       where name is the preferred base name for a variable with type V

       V should be a type, but the code is robust, returning the default "X" or "x"
    *)
    fun namePrefOf (role, V) = namePrefOf' (role, IntSyn.targetFamOpt V)

  end  (* local ... *)

  (******************)
  (* Variable Names *)
  (******************)

  (*
     Picking variable names is tricky, since we need to avoid capturing.
     This is entirely a matter of parsing and printing, since the
     internal representation relies on deBruijn indices and explicit
     substitutions.

     During parsing, a name is resolved as follows:
       lower case id => bound variable, constant, error
       upper case id => bound variable, constant, free variable
     where a free variable could become either an FVar
     (in constant declarations) or an EVar (in queries).

     Names are either given by the declaration or query itself, or
     assigned as late as possible.  For example, EVars which are never
     printed are never assigned a name.

     This may be a problem for contexts: if a name is not assigned when
     a declaration is entered into the context, terms in this context
     may not be printable.  Function decName below guarantees that new
     names are assigned to variables added to a context.
  *)

  (*
     There are three data structures:
     1. varTable mapping names (strings) to EVars and FVar types
     2. evarList mapping EVars to names (string)
     3. indexTable mapping base names B to integer suffixes to generate
        new names B1, B2, ...

     These are reset for each declaration or query, since
     EVars and FVars are local.
  *)
  local
    datatype varEntry =
        FVAR of IntSyn.Exp		(* global type V for F:V *)
      | EVAR of IntSyn.Exp		(* EVar X *)

    (* varTable mapping identifiers (strings) to EVars and FVars *)
    (* A hashtable is too inefficient, since it is cleared too often; *)
    (* so we use a red/black trees instead *)
    val varTable : varEntry RedBlackTree.Table = RedBlackTree.new (0) (* initial size hint *)
    val varInsert = RedBlackTree.insert varTable
    val varLookup = RedBlackTree.lookup varTable
    fun varClear () = RedBlackTree.clear varTable

    (* evarList mapping EVars to names *)
    (* names are assigned only when EVars are parsed or printed *)
    (* the mapping must be implemented as an association list *)
    (* since EVars are identified by reference *)
    (* an alternative becomes possible if time stamps are introduced *)
    val evarList : (IntSyn.Exp * string) list ref = ref nil

    fun evarReset () = (evarList := nil)
    fun evarLookup (IntSyn.EVar(r,_,_,_)) =
        let fun evlk (nil) = NONE
	      | evlk ((IntSyn.EVar(r',_,_,_), name)::l) =
	        if r = r' then SOME(name) else evlk l
	in
	  evlk (!evarList)
	end
    fun evarInsert entry = (evarList := entry::(!evarList))

    fun namedEVars () = !evarList

    (* Since constraints are not printable at present, we only *)
    (* return a list of names of EVars that have constraints on them *)
    (* Note that EVars which don't have names, will not be considered! *)
    fun evarCnstr' (nil, acc) = acc
      | evarCnstr' ((Xn as (IntSyn.EVar(ref(NONE), _, _, Constr as (_::_)), name))::l, acc) =
          evarCnstr' (l, Xn::acc)
      | evarCnstr' (_::l, acc) = evarCnstr' (l, acc)
    fun evarCnstr () = evarCnstr' (!evarList, nil)

    (* The indexTable maps a name to the last integer suffix used for it.
       The resulting identifer is not guaranteed to be new, and must be
       checked against the names of constants, FVars, EVars, and BVars.
    *)
    val indexTable : int RedBlackTree.Table = RedBlackTree.new (0)
    val indexInsert = RedBlackTree.insert indexTable
    val indexLookup = RedBlackTree.lookup indexTable
    fun indexClear () = RedBlackTree.clear indexTable

    fun nextIndex' (name, NONE) = (indexInsert (name, 1); 1)
      | nextIndex' (name, SOME(i)) = (indexInsert (name, i+1); i+1)

    (* nextIndex (name) = i
       where i is the next available integer suffix for name,
       starting at 1.
       Effect: initialize or increment the indexTable entry for name
    *)
    fun nextIndex (name) = nextIndex' (name, indexLookup (name))
  in
    (* varReset () = ()
       Effect: clear variable tables
       This must be called for each declaration or query
    *)
    fun varReset () = (varClear (); evarReset (); indexClear ())

    (* getFVarType (name) = V
       where V is the type ascribed to free variable `name'.
       Returns a new type variable, if `name' has not been seen yet
       Used in parsing declarations.
       Effect: if `name' is new, enter the new type variable into the varTable.
    *)
    fun getFVarType (name) =
        (case varLookup name
	   of NONE => let
			val V = IntSyn.newTypeVar (IntSyn.Null)	(* FVars typed in empty Ctx *)
			val _ = varInsert (name, FVAR (V));
		      in 
			 V
		      end
            | SOME(FVAR(V)) => V)
	    (* other cases should be impossible *)

    (* getEVar (name) = X
       where X is the EVar with name `name'.
       If no EVar with this name exists, a new one will be
       created in the empty context with variable type.
       Used in parsing a query.
       Effect: if `name' is new, enter the type EVar into the varTable and evarList.
    *)
    fun getEVar (name) =
        (case varLookup name
	   of NONE => let
			(* free variables typed in empty context *)
			val V = IntSyn.newTypeVar (IntSyn.Null)
			val (X as (IntSyn.EVar(r,_,_,_))) = IntSyn.newEVar (IntSyn.Null, V)
			val _ = varInsert (name, EVAR (X))
			val _ = evarInsert (X, name)
		      in 
			 X
		      end
            | SOME(EVAR(X)) => X)
	    (* other cases should be impossible *)

    fun getEVarOpt (name) =
        (case varLookup name
	  of NONE => NONE
           | SOME(EVAR(X)) => SOME(X)
           | SOME(FVAR(X)) => NONE)

    (* varDefined (name) = true iff `name' refers to a free variable, *)
    (* which could be an EVar for constant declarations or FVar for queries *)
    fun varDefined (name) =
        (case varLookup name
	   of NONE => false
            | SOME _ => true)

    (* conDefined (name) = true iff `name' refers to a constant *)
    fun conDefined (name) =
        (case nameLookup name
	   of NONE => false
            | SOME _ => true)

    (* ctxDefined (G, name) = true iff `name' is declared in context G *)
    fun ctxDefined (G, name) =
        let fun cdfd (IntSyn.Null) = false
	      | cdfd (IntSyn.Decl(G', IntSyn.Dec(SOME(name'),_))) =
                  name = name' orelse cdfd G'
	      | cdfd (IntSyn.Decl(G', _)) = cdfd G'
	in
	  cdfd G
	end

    (* tryNextName (G, base) = baseN
       where N is the next suffix such that baseN is unused in
       G, as a variable, or as a constant.
    *)
    fun tryNextName (G, base) =
        let
	  val name = base ^ Int.toString (nextIndex (base))
	in
	  if varDefined name orelse conDefined name
	     orelse ctxDefined (G,name)
	    then tryNextName (G, base)
	  else name
	end

    fun findNameLocal (G, base, i) =
        let val name = base ^ (if i = 0 then "" else Int.toString (i))
	in
	  if varDefined name orelse conDefined name
	     orelse ctxDefined (G, name)
	    then findNameLocal (G, base, i+1)
	  else name
	end

    fun findName (G, base, Local) = findNameLocal (G, base, 0)
      | findName (G, base, Global) = tryNextName (G, base)
        

    val takeNonDigits = Substring.takel (not o Char.isDigit)

    (* baseOf (name) = name',
       where name' is the prefix of name not containing a digit
    *)
    fun baseOf (name) = Substring.string (takeNonDigits (Substring.all name))

    (* newEvarName (G, X) = name
       where name is the next unused name appropriate for X,
       based on the name preference declaration for A if X:A
    *)
    fun newEVarName (G, X as IntSyn.EVar(r, _, V, Cnstr)) =
        let
	  (* use name preferences below *)
	  val name = tryNextName (G, namePrefOf (Exist, V))
	in
	  (evarInsert (X, name);
	   name)
	end

    (* evarName (G, X) = name
       where `name' is the print name X.
       If no name has been assigned yet, assign a new one.
       Effect: if a name is assigned, update varTable
    *)
    fun evarName (G, X) =
        (case evarLookup X
	   of NONE => let
			val name = newEVarName (G, X)
		      in
			(varInsert (name, EVAR(X));
			 name)
		      end
            | SOME (name) => name)

    (* bvarName (G, k) = name
       where `name' is the print name for variable with deBruijn index k.
       Invariant: 1 <= k <= |G|
                  G_k must assign a name
       If no name has been assigned, the context might be built the wrong
       way---check decName below instread of IntSyn.Dec
    *)
    fun bvarName (G, k) =
        (case IntSyn.ctxLookup (G, k)
	   of IntSyn.Dec(SOME(name), _) => name)
              (* NONE should not happen *)

    (* decName' role (G, D) = G,D'
       where D' is a possible renaming of the declaration D
       in order to avoid shadowing other variables or constants
       If D does not assign a name, this picks, based on the name
       preference declaration.
    *)
    fun decName' role (G, IntSyn.Dec (NONE, V)) =
        let
	  val name = findName (G, namePrefOf (role, V), extent (role))
	in
	  IntSyn.Dec (SOME(name), V)
	end
      | decName' role (G, D as IntSyn.Dec (SOME(name), V)) =
	if varDefined name orelse conDefined name
	  orelse ctxDefined (G, name)
	  then IntSyn.Dec (SOME (tryNextName (G, baseOf name)), V)
	else D

    val decName = decName' Exist
    val decEName = decName' Exist
    val decUName = decName' (Univ (Global))
    val decLUName = decName' (Univ (Local))

    (* ctxName G = G'
       
        Invariant:
	|- G == G' ctx
	where some Declaration in G' have been named/renamed
    *)
    fun ctxName (IntSyn.Null) = IntSyn.Null
      | ctxName (IntSyn.Decl (G, D)) = 
        let
	  val G' = ctxName G
	in
	  IntSyn.Decl (G', decName (G', D))
	end

    (* ctxLUName G = G'
       like ctxName, but names assigned are local universal names.
    *)
    fun ctxLUName (IntSyn.Null) = IntSyn.Null
      | ctxLUName (IntSyn.Decl (G, D)) = 
        let
	  val G' = ctxLUName G
	in
	  IntSyn.Decl (G', decLUName (G', D))
	end

    (* pisEName' (G, V) = V'
       Assigns names to dependent Pi prefix of V.
       Used for implicit EVar in constant declarations after abstraction.
    *)
    fun pisEName' (G, IntSyn.Pi ((D, IntSyn.Maybe), V)) =
        let
	  val D' = decEName (G, D)
	in
	  IntSyn.Pi ((D', IntSyn.Maybe),
		     pisEName' (IntSyn.Decl (G, D'), V))
	end
      | pisEName' (G, V) = V

    fun pisEName (V) = pisEName' (IntSyn.Null, V)

    (* defEName' (G, (U,V)) = (U',V')
       Invariant: G |- U : V  and G |- U' : V' since U == U' and V == V'.
       Assigns name to dependent Pi prefix of V and corresponding lam prefix of U.
       Used for implicit EVar in constant definitions after abstraction.
    *)
    fun defEName' (G, (IntSyn.Lam (D, U), IntSyn.Pi ((_, P), V))) =
        let
	  val D' = decEName (G, D)
	  val (U', V') = defEName' (IntSyn.Decl (G, D'), (U, V))
	in
	  (IntSyn.Lam (D', U'), IntSyn.Pi ((D', P), V'))
	end
      | defEName' (G, (U, V)) = (U, V)

    fun defEName UV = defEName' (IntSyn.Null, UV)

    fun nameConDec' (IntSyn.ConDec (name, imp, V, L)) =
          IntSyn.ConDec (name, imp, pisEName V, L)
      | nameConDec' (IntSyn.ConDef (name, imp, U, V, L)) =
	let 
	  val (U', V') = defEName (U, V)
	in
	  IntSyn.ConDef (name, imp, U', V', L)
	end
      | nameConDec' (skodec) = skodec (* fix ??? *)

    (* Assigns names to variables in a constant declaration *)
    (* The varReset (); is necessary so that explicitly named variables keep their name *)
    fun nameConDec (conDec) =
        (varReset ();			(* declaration is always closed *)
	 nameConDec' conDec)

    fun skonstName (name) =
          tryNextName (IntSyn.Null, name)

    val namedEVars = namedEVars
    val evarCnstr = evarCnstr

  end  (* local varTable ... *)

end;  (* functor Names *)
