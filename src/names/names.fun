(* Names of Constants and Variables *)
(* Author: Frank Pfenning *)
(* Modified: Jeff Polakow *)

functor Names (structure Global : GLOBAL
	       (*! structure IntSyn' : INTSYN !*)
               structure Constraints : CONSTRAINTS
	       (*! sharing Constraints.IntSyn = IntSyn' !*)
	       structure HashTable : TABLE where type key = string
               structure StringTree : TABLE where type key = string)
  : NAMES =
struct

  (*! structure IntSyn = IntSyn' !*)

  exception Error of string

  (*
     Unprintable is raised when trying to resolve the names
     of unnamed variables.  Usually, this signals an error
     in Twelf; the only exception is the use of anonymous
     bound variables [_] or {_} in the source.
  *)
  exception Unprintable

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
    val maxPrecInt = 9999
    val maxPrec = Strength(maxPrecInt)
    val minPrecInt = 0
    val minPrec = Strength(minPrecInt)

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

    (* returns integer for precedence such that lower values correspond to higher precedence, useful for exports *)
    fun precToIntAsc(Infix(Strength n,_)) = maxPrecInt + 1 - n
      | precToIntAsc(Prefix(Strength n)) = maxPrecInt + 1 - n
      | precToIntAsc(Postfix(Strength n)) = maxPrecInt + 1 - n
      | precToIntAsc(Nonfix) = minPrecInt

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

  (* argNumber (fix) = minimum # of explicit arguments required *)
  (* for operator with fixity fix (0 if there are no requirements) *)
  fun argNumber (Fixity.Nonfix) = 0
    | argNumber (Fixity.Infix _) = 2
    | argNumber (Fixity.Prefix _) = 1
    | argNumber (Fixity.Postfix _) = 1

  (* checkAtomic (name, V, n) = ()
     if V expects exactly n arguments,
     raises Error(msg) otherwise
  *)
  fun checkAtomic (name, IntSyn.Pi (D, V), 0) = true
      (* allow extraneous arguments, Sat Oct 23 14:18:27 1999 -fp *)
      (* raise Error ("Constant " ^ name ^ " takes too many explicit arguments for given fixity") *)
    | checkAtomic (name, IntSyn.Pi (D, V), n) =
	checkAtomic (name, V, n-1)
    | checkAtomic (_, IntSyn.Uni _, 0) = true
    | checkAtomic (_, IntSyn.Root _, 0) = true
    | checkAtomic (name, _, _) = false

  (* checkArgNumber (c, n) = ()
     if constant c expects exactly n explicit arguments,
     raises Error (msg) otherwise
  *)
  fun checkArgNumber (IntSyn.ConDec (name, _, i, _, V, L), n) =
	checkAtomic (name, V, i+n)
    | checkArgNumber (IntSyn.SkoDec (name, _, i, V, L), n) =
	checkAtomic (name, V, i+n)
    | checkArgNumber (IntSyn.ConDef (name, _, i, _, V, L, _), n) =
	checkAtomic (name, V, i+n)
    | checkArgNumber (IntSyn.AbbrevDef (name, _, i, _, V, L), n) =
	checkAtomic (name, V, i+n)

  (* checkFixity (cid, n) = ()
     if n = 0 (no requirement on arguments)
     or cid is declared and has n exactly explicit arguments,
     raises Error (msg) otherwise
  *)
  fun checkFixity (_, 0) = ()
    | checkFixity (cid, n) =
      if checkArgNumber (IntSyn.sgnLookup (cid), n) then ()
      else raise Error ("Constant " ^ (IntSyn.conDecFoldName (IntSyn.sgnLookup cid)) ^ " takes too few explicit arguments for given fixity")

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

  local
    structure SH = HashTable (type key' = (IDs.mid * string list)
             val hash = fn (m,l) => 1000 * m + StringHash.stringListHash(l)
             val eq = (op =));
    structure CH = CidHashTable
    type cid = IDs.cid

    val nameTable : cid SH.Table = SH.new(4096)
    
    type namePref = (string list * string list) option
    val namePrefTable : namePref CH.Table = CH.new(4096)
    val insertNamePref : cid * namePref -> unit = CH.insert namePrefTable

    val fixityTable : Fixity.fixity CH.Table = CH.new(4096)

    val inCurrent = IntSyn.inCurrent
  in

    fun installName(c : cid, l : string list) = SH.insert nameTable ((IDs.midOf c, l), c) 
    val nameLookup : IDs.mid * string list -> cid option = SH.lookup nameTable
    fun nameLookupC(l : string list) = nameLookup(IntSyn.currentMod(), l)
    (* installFixity (cid, fixity) = ()
       Effect: install fixity for constant cid,
               possibly print declaration depending on chatter level
    *)
    fun installFixity (cid, fixity) = (
	  checkFixity (cid, argNumber fixity);
          CH.insert fixityTable (cid, fixity)
    )

    (* fixityLookup cid = fixity
       where fixity is the fixity associated with constant cid,
       defaults to Fixity.Nonfix if fixity undeclared
    *)
    fun fixityLookup cid =
        (case CH.lookup fixityTable cid
           of NONE => Fixity.Nonfix
            | SOME fix => fix
        )
    val fixityLookupC = fixityLookup o inCurrent

    (* Name Preferences *)
    (* ePref is the name preference for existential variables of given type *)
    (* uPref is the name preference for universal variables of given type *)

    (* installNamePref (cid, (ePref, uPrefOpt)) = ()
       Effect: install name preference for type family cid
       raise Error if cid does not refer to a type family
    *)
    local   
       fun installNamePref' (cid, (ePref, uPref)) =
         let
	    val L = IntSyn.constUni (cid)
	    val _ = case L
	            of IntSyn.Type =>
		       raise Error ("Object constant " ^ (IntSyn.conDecFoldName (IntSyn.sgnLookup cid)) ^ " cannot be given name preference\n"
				    ^ "Name preferences can only be established for type families")
		     | IntSyn.Kind => ()
	in
	  insertNamePref (cid, SOME (ePref, uPref))
	end
    in
      fun installNamePref (cid, (ePref, nil)) =
            installNamePref' (cid, (ePref, [String.map Char.toLower (hd ePref)]))
        | installNamePref (cid, (ePref, uPref)) =
            installNamePref' (cid, (ePref, uPref))
    end
    val namePrefLookup = Option.join o (CH.lookup namePrefTable)
    val namePrefLookupC = namePrefLookup o inCurrent

    fun reset () = (SH.clear nameTable; CH.clear fixityTable; CH.clear namePrefTable)

    (* this must be replaced with the parsing method for qualified names -fr *)
     fun parseQualifiedName (name : string) =
        String.fields (fn c => c = #".") name
     fun foldQualifiedName l = foldl (fn (x,y) => x ^ "." ^ y) (hd l) (tl l)

    (* local names are more easily re-used: they don't increment the
       counter associated with a name
    *)
    datatype Extent = Local | Global
    datatype Role = Exist | Univ of Extent

    fun extent (Exist) = Global
      | extent (Univ (ext)) = ext

    fun namePrefOf'' (Exist, NONE) = "X"
      | namePrefOf'' (Univ _, NONE) = "x"
      | namePrefOf'' (Exist, SOME(ePref, uPref)) = hd ePref
      | namePrefOf'' (Univ _, SOME(ePref, uPref)) = hd uPref

    fun namePrefOf' (Exist, NONE) = "X"
      | namePrefOf' (Univ _, NONE) = "x"
      | namePrefOf' (role, SOME(IntSyn.Const cid)) = namePrefOf'' (role, namePrefLookup cid)
      | namePrefOf' (role, SOME(IntSyn.Def cid)) = namePrefOf'' (role, namePrefLookup cid)
        (* the following only needed because reconstruction replaces
           undetermined types with FVars *)
      | namePrefOf' (role, SOME(IntSyn.FVar _)) = namePrefOf'' (role, NONE)

      | namePrefOf' (role, SOME(IntSyn.NSDef cid)) = namePrefOf'' (role, namePrefLookup cid)

    (* namePrefOf (role, V) = name
       where name is the preferred base name for a variable with type V

       V should be a type, but the code is robust, returning the default "X" or "x"
    *)
    fun namePrefOf (role, V) = namePrefOf' (role, IntSyn.targetHeadOpt V)

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
          -- Actually, FVar types now handled entirely in recon-term.fun
          -- where there needs to be more info for approximate types.
          -- I don't see why EVar/BVar names should be generated apart from
          -- FVar names anyway, since the latter are printed with "`".
          -- -kw
     2. evarList mapping EVars to names (string)
     3. indexTable mapping base names B to integer suffixes to generate
        new names B1, B2, ...

     These are reset for each declaration or query, since
     EVars and FVars are local.
  *)
  local
    datatype varEntry = EVAR of IntSyn.Exp (* X *)
      (* remove this datatype? -kw *)

    (* varTable mapping identifiers (strings) to EVars and FVars *)
    (* A hashtable is too inefficient, since it is cleared too often; *)
    (* so we use a red/black trees instead *)
    val varTable : varEntry StringTree.Table = StringTree.new (0) (* initial size hint *)
    val varInsert = StringTree.insert varTable
    val varLookup = StringTree.lookup varTable
    fun varClear () = StringTree.clear varTable

    (* what is this for?  -kw *)
    val varContext : IntSyn.dctx ref = ref IntSyn.Null

    (* evarList mapping EVars to names *)
    (* names are assigned only when EVars are parsed or printed *)
    (* the mapping must be implemented as an association list *)
    (* since EVars are identified by reference *)
    (* an alternative becomes possible if time stamps are introduced *)
    val evarList : (IntSyn.Exp * string) list ref = ref nil

    fun evarReset () = (evarList := nil)
    fun evarLookup (X) =
        let fun evlk (r, nil) = NONE
	      | evlk (r, (IntSyn.EVar(r',_,_,_), name)::l) =
	        if r = r' then SOME(name) else evlk (r, l)
	      | evlk (r, ((IntSyn.AVar(r'), name)::l)) =
	        if r = r' then SOME(name) else evlk (r, l)
	in
	  case X of
	    IntSyn.EVar(r,_,_,_) => evlk (r, (!evarList))
	  | IntSyn.AVar(r) => evlk (r, (!evarList))
	end
    fun evarInsert entry = (evarList := entry::(!evarList))

    fun namedEVars () = !evarList

    (* Since constraints are not printable at present, we only *)
    (* return a list of names of EVars that have constraints on them *)
    (* Note that EVars which don't have names, will not be considered! *)
    fun evarCnstr' (nil, acc) = acc
      | evarCnstr' ((Xn as (IntSyn.EVar(ref(NONE), _, _, cnstrs), name))::l, acc) =
          (case Constraints.simplify (!cnstrs)
             of nil => evarCnstr' (l, acc)
              | (_::_) => evarCnstr' (l, Xn::acc))
      | evarCnstr' (_::l, acc) = evarCnstr' (l, acc)
    fun evarCnstr () = evarCnstr' (!evarList, nil)

    (* The indexTable maps a name to the last integer suffix used for it.
       The resulting identifer is not guaranteed to be new, and must be
       checked against the names of constants, FVars, EVars, and BVars.
    *)
    val indexTable : int StringTree.Table = StringTree.new (0)
    val indexInsert = StringTree.insert indexTable
    val indexLookup = StringTree.lookup indexTable
    fun indexClear () = StringTree.clear indexTable

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
    fun varReset G = (varClear (); evarReset (); indexClear ();
                      varContext := G)

    (* addEVar (X, name) = ()
       effect: adds (X, name) to varTable and evarList
       assumes name not already used *)
    fun addEVar (X, name) =
        (evarInsert (X, name);
         varInsert (name, EVAR(X)))

    fun getEVarOpt (name) =
        (case varLookup name
	  of NONE => NONE
           | SOME(EVAR(X)) => SOME(X))

    (* varDefined (name) = true iff `name' refers to a free variable, *)
    (* which could be an EVar for constant declarations or FVar for queries *)
    fun varDefined (name) =
        (case varLookup name
	   of NONE => false
            | SOME _ => true)

    (* conDefined (name) = true iff `name' refers to a constant *)
    fun conDefined (name) =
        case nameLookupC (name :: nil)
	     of NONE => false
              | SOME _ => true

    (* ctxDefined (G, name) = true iff `name' is declared in context G *)
    fun ctxDefined (G, name) =
        let fun cdfd (IntSyn.Null) = false
	      | cdfd (IntSyn.Decl(G', IntSyn.Dec(SOME(name'),_))) =
                  name = name' orelse cdfd G'
              | cdfd (IntSyn.Decl(G', IntSyn.BDec(SOME(name'),_))) =
		  name = name' orelse cdfd G'
              | cdfd (IntSyn.Decl(G', IntSyn.NDec(SOME(name')))) =
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
    fun baseOf (name) = Substring.string (takeNonDigits (Compat.Substring.full name))

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
      | newEVarName (G, X as IntSyn.AVar(r)) =
        let
	  (* use name preferences below *)
	  val name = tryNextName (G, namePrefOf' (Exist, NONE))
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
        case IntSyn.ctxLookup (G, k)
	  of IntSyn.Dec(SOME(name), _) => name
	   | IntSyn.ADec(SOME(name), _) =>  name
	   | IntSyn.NDec(SOME(name)) =>  name (* Evars can depend on NDec :-( *)
	   | IntSyn.ADec(None, _) => "ADec_" 
	   | IntSyn.Dec(None, _) => "Dec_" 
	   | _ => raise Unprintable

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
      | decName' role (G, D as IntSyn.BDec (NONE, b as (cid, t))) =
        (* use #l as base name preference for label l *)
	let
	  val name = findName (G, "#" ^ IntSyn.conDecFoldName (IntSyn.sgnLookup cid), Local)
	in
	  IntSyn.BDec (SOME(name), b)
	end
      | decName' role (G, D as IntSyn.BDec (SOME(name), b as (cid, t))) =
	if varDefined name orelse conDefined name
	  orelse ctxDefined (G, name)
	  then IntSyn.BDec (SOME (tryNextName (G, baseOf name)), b)
	else D
      | decName' role (G, IntSyn.ADec (NONE, d)) =
        let
	  val name = findName (G, namePrefOf' (role, NONE), extent (role))
	in
	  IntSyn.ADec (SOME(name), d)
	end
      | decName' role (G, D as IntSyn.ADec (SOME(name), d)) =
(*	IntSyn.ADec(SOME(name), d) *)
	if varDefined name orelse conDefined name
	  orelse ctxDefined (G, name)
	  then IntSyn.ADec (SOME (tryNextName (G, baseOf name)), d)
	else D
      | decName' role (G, D as IntSyn.NDec NONE) = 
	let 
	  val name = findName (G, "@x", Local)
	    val _ = print name
	     
	in 
	  IntSyn.NDec (SOME name)
	end
      | decName' role (G, D as IntSyn.NDec (SOME name)) = 
	if varDefined name orelse conDefined name
	  orelse ctxDefined (G, name)
	  then IntSyn.NDec (SOME (tryNextName (G, baseOf name)))
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

    (* pisEName' (G, i, V) = V'
       Assigns names to dependent Pi prefix of V with i implicit abstractions
       Used for implicit EVar in constant declarations after abstraction.
    *)
    fun pisEName' (G, 0, V) = V
      | pisEName' (G, i, IntSyn.Pi ((D, IntSyn.Maybe), V)) =
        (* i > 0 *)
        let
	  val D' = decEName (G, D)
	in
	  IntSyn.Pi ((D', IntSyn.Maybe),
		     pisEName' (IntSyn.Decl (G, D'), i-1, V))
	end
      (* | pisEName' (G, i, V) = V *)

    fun pisEName (i, V) = pisEName' (IntSyn.Null, i, V)

    (* defEName' (G, i, (U,V)) = (U',V')
       Invariant: G |- U : V  and G |- U' : V' since U == U' and V == V'.
       Assigns name to dependent Pi prefix of V and corresponding lam prefix of U
       with i implicit abstractions
       Used for implicit EVar in constant definitions after abstraction.
    *)
    fun defEName' (G, 0, UV) = UV
      | defEName' (G, i, (IntSyn.Lam (D, U), IntSyn.Pi ((_ (* = D *), P), V))) =
        (* i > 0 *)
        let
	  val D' = decEName (G, D)
	  val (U', V') = defEName' (IntSyn.Decl (G, D'), i-1, (U, V))
	in
	  (IntSyn.Lam (D', U'), IntSyn.Pi ((D', P), V'))
	end
      (* | defEName' (G, i, (U, V)) = (U, V) *)

    fun defEName (imp, UV) = defEName' (IntSyn.Null, imp, UV)

    fun nameConDec' (IntSyn.ConDec (name, parent, imp, status, V, L)) =
          IntSyn.ConDec (name, parent, imp, status, pisEName (imp, V), L)
      | nameConDec' (IntSyn.ConDef (name, parent, imp, U, V, L, Anc)) =
	let 
	  val (U', V') = defEName (imp, (U, V))
	in
	  IntSyn.ConDef (name, parent, imp, U', V', L, Anc)
	end
      | nameConDec' (IntSyn.AbbrevDef (name, parent, imp, U, V, L)) =
	let 
	  val (U', V') = defEName (imp, (U, V))
	in
	  IntSyn.AbbrevDef (name, parent, imp, U', V', L)
	end
      | nameConDec' (skodec) = skodec (* fix ??? *)

    (* Assigns names to variables in a constant declaration *)
    (* The varReset (); is necessary so that explicitly named variables keep their name *)
    fun nameConDec (conDec) =
        (varReset IntSyn.Null;			(* declaration is always closed *)
	 nameConDec' conDec)

    fun skonstName (name) =
          tryNextName (IntSyn.Null, name)

    val namedEVars = namedEVars
    val evarCnstr = evarCnstr

  end  (* local varTable ... *)

end;  (* functor Names *)
