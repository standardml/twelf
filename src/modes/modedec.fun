(* Modes: short and full mode declarations *)
(* Author: Carsten Schuermann *)
(* Modified: Frank Pfenning *)

functor ModeDec ((*! structure ModeSyn' : MODESYN !*)
                 (*! structure Paths' : PATHS !*)
                   )
  : MODEDEC =
struct
  (*! structure ModeSyn = ModeSyn' !*)
  (*! structure Paths = Paths' !*)

  exception Error of string

  local
    structure M = ModeSyn
    structure I = IntSyn
    structure P = Paths

    datatype Arg = Implicit | Explicit | Local

    (* Representation invariant:

       The modes of parameters are represented in the following mode list

       M ::= . | M, <Marg, Arg>

       G corresponds to a context. We say M is a mode list for U, if
       G |- U : V and M assigns modes to parameters in G
         (and similarly for all other syntactic categories)

       The main function of this module is to
        (a) assign modes to implicit arguments in a type family
        (b) check the mode specification for consistency

       Example:

         a : type.
         b : a -> a -> type.
         c : b X X -> b X Y -> type.

       Then

         %mode c +M -N.

       will infer X to be input and Y to be output

         %mode +{X:a} -{Y:a} +{M:b X Y} -{N:b X Y} (c M N).

       Generally, it is inconsistent
       for an unspecified ( * ) or output (-) argument to occur
       in the type of an input (+) argument
    *)

    fun error (r, msg) = raise Error (P.wrap (r, msg))

    (* checkname mS = ()

       Invariant:
       mS modeSpine, all modes are named.
       If mS contains two entries with the same name
       then Error is raised
    *)
    fun checkName (M.Mnil) = ()
      | checkName (M.Mapp (M.Marg (_, SOME name), mS)) =
        let
          fun checkName' (M.Mnil) = ()
            | checkName' (M.Mapp (M.Marg (_, SOME name'), mS)) =
              if name = name' then
                raise Error ("Variable name clash: " ^ name ^ " is not unique")
              else checkName' mS
        in
          checkName' mS
        end

    (* modeConsistent (m1, m2) = true
       iff it is consistent for a variable x with mode m1
           to occur as an index object in the type of a variable y:V(x) with mode m2

       m1\m2 + * - -1
        +    Y Y Y Y
        *    N y n n
        -    N y Y n
        -1   N Y Y Y

       The entries y,n constitute a bug fix, Wed Aug 20 11:50:27 2003 -fp
       The entry n specifies that the type
    *)
    fun modeConsistent (M.Star, M.Plus) = false    (* m1 should be M.Plus *)
      | modeConsistent (M.Star, M.Minus) = false   (* m1 should be M.Minus *)
      | modeConsistent (M.Star, M.Minus1) = false  (* m1 should be M.Minus1 *)
      | modeConsistent (M.Minus, M.Plus) = false   (* m1 should be M.Plus *)
      | modeConsistent (M.Minus, M.Minus1) = false (* m1 should be M.Minus1 *)
      | modeConsistent (M.Minus1, M.Plus) = false  (* m1 should be M.Plus *)
      | modeConsistent _ = true

    (* empty (k, ms, V) = (ms', V')

       Invariant:
       If    V = {A_1} .. {A_n} V1   in Sigma
       and   V has k implicit arguments
       then  ms' = ms, <( *, NONE), Implicit>  ... <( *, NONE), Implicit>   (k times)
       and   V' = V1
    *)
    fun empty (0, ms, V) = (ms, V)
      | empty (k, ms, I.Pi (_, V)) =
          empty (k-1, I.Decl (ms, (M.Marg (M.Star, NONE), Implicit)), V)


    (* inferVar (ms, m, k) = ms'

       Invariant:
       If  ms is a mode list,
       and k is declared with mode mk in ms
       and m is the mode for a variable y in whose type k occurs
       then ms' is the same as ms replacing only mk by
       mk' = m o mk

        m o mk  + * - -1
        ----------------
        +       + + + +
        *       + * - -1
        -       + - - -1
        -1      + -1-1-1

        Effect: if the mode mk for k was explicitly declared and inconsistent
                with m o mk, an error is raised
    *)
    fun inferVar (I.Decl (ms, (M.Marg (M.Star, nameOpt), Implicit)), mode, 1) =
          I.Decl (ms, (M.Marg (mode, nameOpt), Implicit))
      | inferVar (I.Decl (ms, (M.Marg (_, nameOpt), Implicit)), M.Plus, 1) =
          I.Decl (ms, (M.Marg (M.Plus, nameOpt), Implicit))
      | inferVar (I.Decl (ms, (M.Marg (M.Minus, nameOpt), Implicit)), M.Minus1, 1) =
          I.Decl (ms, (M.Marg (M.Minus1, nameOpt), Implicit))
      | inferVar (ms as I.Decl (_, (_, Implicit)), _, 1) = ms
      | inferVar (ms as I.Decl (_, (_, Local)), _, 1) = ms
      | inferVar (ms as I.Decl (_, (M.Marg (mode', SOME name), Explicit)), mode, 1) =
        if modeConsistent (mode', mode)
          then ms
        else raise Error ("Mode declaration for " ^ name ^ " expected to be "
                          ^ M.modeToString mode)
      | inferVar (I.Decl (ms, md), mode, k) =
          I.Decl (inferVar (ms, mode, k-1), md)


    (* inferExp (ms, m, U) = ms'

       Invariant:
       If  ms is a mode list for U,   (U in nf)
       and m is a mode
       then ms' is the mode list consistently updated for all parameters occurring in U,
         wrt. to m. (see inferVar)
    *)
    fun inferExp (ms, mode, I.Root (I.BVar (k), S)) =
          inferSpine (inferVar (ms, mode, k), mode, S)
      | inferExp (ms, mode, I.Root (I.Const (cid), S)) =
          inferSpine (ms, mode, S)
      | inferExp (ms, mode, I.Root (I.Def (cid), S)) =
          inferSpine (ms, mode, S)
      | inferExp (ms, mode, I.Root (I.FgnConst (cs, conDec), S)) =
          inferSpine (ms, mode, S)
      | inferExp (ms, mode, I.Lam (D as I.Dec (nameOpt, _), U)) =
          I.ctxPop (inferExp (I.Decl (inferDec (ms, mode, D),
                                      (M.Marg (mode, nameOpt), Local)), mode, U))
      | inferExp (ms, mode, I.Pi ((D as I.Dec (nameOpt, _), _), V)) =
          I.ctxPop (inferExp (I.Decl (inferDec (ms, mode, D),
                                      (M.Marg (mode, nameOpt), Local)), mode, V)) (* cannot make any assumptions on what is inside a foreign object *)
      | inferExp (ms, mode, I.FgnExp _) = ms

    (* inferSpine (ms, m, S) = ms'

       Invariant:
       If  ms is a mode list for S,   (S in nf)
       and m is a mode
       then ms' is the mode list consistently updated for all parameters occurring in S,
         wrt. to m. (see inferVar)
    *)
    and inferSpine (ms, mode, I.Nil) = ms
      | inferSpine (ms, mode, I.App (U, S)) =
          inferSpine (inferExp (ms, mode, U), mode, S)


    (* inferDec (ms, m, x:V) = ms'

       Invariant:
       If  ms is a mode list for V,   (V in nf)
       and m is a mode
       then ms' is the mode list consistently updated for all parameters occurring in V,
         wrt. to m.   (see inferVar)
    *)
    and inferDec (ms, mode, I.Dec (_, V)) =
          inferExp (ms, mode, V)

    (* inferMode ((ms, V), mS) = ms'

       Invariant:
       If  ms is a mode list for V,
       and mS is a mode spine,
       then ms' is the mode list for V which is consistent with V.
    *)
    fun inferMode ((ms, I.Uni(I.Type)), M.Mnil) = ms
      | inferMode ((_, I.Uni(I.Type)), _) = raise Error "Too many modes specified"
      | inferMode ((ms, I.Pi ((I.Dec (name, V1), _), V2)), M.Mapp (M.Marg (mode, _), mS)) =
          I.ctxPop (inferMode ((I.Decl (inferExp (ms, mode, V1),
                                        (M.Marg (mode, name), Explicit)), V2), mS))
      | inferMode ((ms, I.Root _), _) =
          raise Error "Expected type family, found object constant"
      | inferMode _ = raise Error "Not enough modes specified"

    (* abstractMode (ms, mS) = mS'

       Invariant:
       If    V = {A1} .. {An} V1  is a type (with n implicit parameter)
       and   ms is a mode list for V,
       then  mS' = {m1} .. {mn} mS
       where m1 .. mn are the infered modes for the implicit parameters
    *)
    fun abstractMode (ms, mS) =
        let
          fun abstractMode' (I.Null, mS, _) = mS
            | abstractMode' (I.Decl (ms, (marg, _)), mS, k) =
                abstractMode' (ms, M.Mapp (marg, mS), k+1)
        in
          abstractMode' (ms, mS, 1)
        end

    (* shortToFull (cid, mS, r) = mS'

       Invariant:
       mS modeSpine, all modes are named.
       r is the text region of the mode declaration
       if mS is a mode spine in short form (implicit parameters are not moded),
       then mS' is a mode spine in full form (all parameters are moded)

       Full form can be different then intended by the user.
    *)
    fun shortToFull (a, mS, r) =
      let
        fun calcImplicit' (I.ConDec (_, _, k, _, V, _))  =
              abstractMode (inferMode (empty (k, I.Null, V), mS), mS)
          | calcImplicit' (I.ConDef (_, _, k, _, V, _, _)) =
            (* ignore definition for defined type family since they are opaque *)
              abstractMode (inferMode (empty (k, I.Null, V), mS), mS)
      in
        (checkName mS; calcImplicit' (I.sgnLookup a))
        handle Error (msg) => error (r, msg)  (* re-raise Error with location *)
      end

    (* checkFull (a, mS, r) = ()

       Invariant:
       mS modeSpine, all modes are named.
       r is the text region of the mode declaration
       if mS is not a valid mode spine in full form then
       exception Error is raised.
    *)
    fun checkFull (a, mS, r) =
        (checkName mS;
         case I.sgnLookup a
           of I.ConDec (_, _, _, _, V, _)  =>
               (inferMode ((I.Null, V), mS); ())
              (* defined type families treated as separate types for
                 purposes of mode checking (as the operational
                 semantics doesn't expand type definitions) *)
            | I.ConDef (_, _, _, _, V, _, _) =>
               (inferMode ((I.Null, V), mS); ()))
        handle Error (msg) => error (r, msg)  (* re-raise error with location *)

    (* checkPure (a, mS, r) = ()
       Effect: raises Error(msg) if the modes in mS mention (-1)
    *)
    fun checkPure ((a, M.Mnil), r) = ()
      | checkPure ((a, M.Mapp (M.Marg (M.Minus1, _), mS)), r) =
        error (r, "Uniqueness modes (-1) not permitted in `%mode' declarations (use `%unique')")
      | checkPure ((a, M.Mapp (_, mS)), r) = checkPure ((a, mS), r)

  in
    val shortToFull = shortToFull
    val checkFull = checkFull
    val checkPure = checkPure
  end
end;  (* functor ModeDec *)
