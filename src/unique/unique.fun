(* Uniqueness Checking *)
(* Author: Frank Pfenning *)

functor Unique
  (structure Global : GLOBAL
   structure Whnf : WHNF
   structure Abstract : ABSTRACT
   structure Unify : UNIFY		(* must be trailing! *)
   structure Constraints : CONSTRAINTS
   structure ModeSyn' : MODESYN
   structure Index : INDEX
   structure Subordinate : SUBORDINATE

   structure WorldSyn : WORLDSYN
   structure Names : NAMES
   structure Print : PRINT
   structure TypeCheck : TYPECHECK
   structure Timers : TIMERS)
  : UNIQUE =
struct

  structure ModeSyn = ModeSyn'

  exception Error of string

  local
    structure I = IntSyn
    structure M = ModeSyn
    structure W = WorldSyn
    structure P = Paths
    structure F = Print.Formatter
    structure N = Names

    fun chatter chlev f =
        if !Global.chatter >= chlev
	  then print (f ())
	else ()

    fun cName (cid) = N.qidToString (N.constQid cid)

    (* instEVars ({x1:V1}...{xn:Vn}a@S, id) = (a @ S, s)
       where . |- s : {x1:V1}...{xn:Vn}
       substitutes new EVars for x1,...,xn

       Invariants: {x1:V1}...{xn:Vn}a@S NF
    *)
    fun instEVars (I.Pi ((I.Dec (_, V1), _), V2), s) =
        let
	  val X1 = I.newEVar (I.Null, I.EClo (V1, s))
	in
	  instEVars (V2, (I.Dot (I.Exp (X1), s)))
	end
      | instEVars (Vs as (I.Root _, _)) = Vs

    (* unifiable ((U, s), (U', s')) = truee
       iff U[s] = U'[s']
       Effect: may instantiate EVars in all inputs
    *)
    fun unifiable ((U, s), (U', s')) =
        Unify.unifiable (I.Null, (U, s), (U', s'))

    (* unifiableSpines ((a @ S, s), (a @ S', s'), ms) = true
       iff S[s] == S'[s'] on input ( + ) arguments according to ms
       Effect: may instantiate EVars in all inputs
    *)
    fun unifiableSpines ((I.Nil, s), (I.Nil, s'), M.Mnil) = true
      | unifiableSpines ((I.App (U1, S2), s), (I.App (U1', S2'), s'),
				 M.Mapp (M.Marg (M.Plus, x), ms2)) =
	  unifiable ((U1, s), (U1', s'))
	  andalso unifiableSpines ((S2, s), (S2', s'), ms2)
      | unifiableSpines ((I.App (U1, S2), s), (I.App (U1', S2'), s'),
				 M.Mapp (M.Marg (mode, x), ms2)) =
	(* skip output ( - ) or ignore ( * ) arguments *)
	  unifiableSpines ((S2, s), (S2', s'), ms2)

    (* unifiableRoots ((a @ S, s), (a @ S', s'), ms) = true
       iff S[s] == S'[s'] on input ( + ) arguments according to ms
       Effect: may instantiate EVars in all inputs
    *)
    fun unifiableRoots ((I.Root (I.Const (a), S), s),
				(I.Root (I.Const (a'), S'), s'), ms) =
        (* a = a' by invariant *)
        unifiableSpines ((S, s), (S', s'), ms)

    (* checkNotUnifable (c, c', ms) = ()
       check if c:A overlaps with c':A' on input arguments ( + )
       according to mode spine ms
       Effect: raises Error(msg) otherwise
    *)
    fun checkNotUnifiable (I.Const(cid), I.Const(cid'), ms) =
        (* c <> c' by invariant *)
        let
	  val _ = chatter 6 (fn () => cName cid ^ " ~ " ^ cName cid' ^ "\n")
	  val Vs = instEVars (I.constType cid, I.id)
	  val Vs' = instEVars (I.constType cid', I.id)
	  val _ = CSManager.trail (fn () =>
				   if unifiableRoots (Vs, Vs', ms)
				     then raise Error (cName cid ^ " and " ^ cName cid' ^ " overlap\n")
				   else ())
	in
	  ()
	end

    (* checkUnique2 (c, cs, ms) = ()
       checks if c:A overlaps with any c':A' in cs on input arguments ( + )
       according to mode spine ms
       Effect: raises Error(msg) otherwise
    *)
    fun checkUnique2 (c, nil, ms) = ()
      | checkUnique2 (c, c'::cs', ms) =
        ( checkNotUnifiable (c, c', ms) ;
	  checkUnique2 (c, cs', ms) )

    (* checkUnique1 (cs, ms) = ()
       checks if no two pairs of constant types in cs overlap on input arguments ( + )
       according to mode spine ms
       Effect: raises Error(msg) otherwise
    *)
    fun checkUnique1 (nil, ms) = ()
      | checkUnique1 (c::cs, ms) =
        ( checkUnique2 (c, cs, ms);
	  checkUnique1 (cs, ms) )

  in
    (* checkNoDef (a) = ()
       Effect: raises Error if a is a defined type family
    *)
    fun checkNoDef (a) =
        (case I.sgnLookup a
           of I.ConDef _ =>
	        raise Error ("Uniqueness checking " ^ N.qidToString (N.constQid a)
			     ^ ":\ntype family must not be defined.")
            | _ => ())

    (* checkUnique (a, ms) = ()
       checks uniqueness of applicable cases with respect to mode spine ms
       Effect: raises Error (msg) otherwise
    *)
    fun checkUnique (a, ms) =
        let
	  val _ = chatter 4 (fn () => "Uniqueness checking family " ^ cName a
			     ^ "\n")
	  val _ = checkNoDef (a)
	  val _ = Subordinate.checkNoDef (a)
	          handle Subordinate.Error (msg) =>
		    raise Error ("Coverage checking " ^ cName a ^ ":\n"
				 ^ msg)


          val cs = Index.lookup a	(* lookup constants defining a *)
	  val W = W.lookup a		(* worlds declarations for a *)
                  handle W.Error (msg)
		         => raise Error ("Uniqueness checking " ^ cName a
					 ^ ":\nMissing world declaration for "
					 ^ cName a)

	  val _ = case W
	            of W.Worlds nil => ()
		     | W.Worlds (b1::bs) =>
		       raise Error ("Uniqueness checking " ^ cName a
				    ^ ":\nWorlds must be empty.")

          val _ = checkUnique1 (cs, ms)

	in
	  ()
	end

  end
end;  (* functor Unique *)
