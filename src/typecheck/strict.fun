(* Checking Definitions for Strict *)
(* Author: Carsten Schuermann *)

functor Strict ((*! structure IntSyn' : INTSYN !*)
                structure Whnf : WHNF
                (*! sharing Whnf.IntSyn = IntSyn' !*)
                (*! structure Paths' : PATHS !*)
                  )
  : STRICT =
struct
  (*! structure IntSyn = IntSyn' !*)
  (*! structure Paths = Paths' !*)

  exception Error of string

  local
    structure I = IntSyn

    (* Definition of normal form (nf) --- see lambda/whnf.fun *)

    (* patSpine (k, S) = B

       Invariant:
       If  G, D |- S : V > V', S in nf
       and |D| = k
       then B iff S = (k1 ; k2 ;...; kn ; NIL), kn <= k, all ki pairwise distinct
    *)
    fun patSpine (_, I.Nil) = true
      | patSpine (k, I.App (I.Root (I.BVar (k'), I.Nil), S)) =
        (* possibly eta-contract? -fp *)
        let fun indexDistinct (I.Nil) = true
              | indexDistinct (I.App (I.Root (I.BVar (k''), I.Nil), S)) =
                  k' <> k'' andalso indexDistinct S
              | indexDistinct _ = false
        in
          k' <= k andalso patSpine (k, S) andalso indexDistinct S
        end
      | patSpine _ = false

    (* strictExp (k, p, U) = B

       Invariant:
       If  G, D |- U : V
       and U is in nf (normal form)
       and |D| = k
       then B iff U is strict in p
    *)
    fun strictExp (_, _, I.Uni _) = false
      | strictExp (k, p, I.Lam (D, U)) =
          (* checking D in this case might be redundant -fp *)
          strictDec (k, p, D) orelse strictExp (k+1, p+1, U)
      | strictExp (k, p, I.Pi ((D, _), U)) =
          strictDec (k, p, D) orelse strictExp (k+1, p+1, U)
      | strictExp (k, p, I.Root (H, S)) =
          (case H
             of (I.BVar (k')) =>
                if (k' = p) then patSpine (k, S)
                else if (k' <= k) then strictSpine (k, p, S)
                     else false
              | (I.Const (c)) => strictSpine (k, p, S)
              | (I.Def (d))  => strictSpine (k, p, S)
              | (I.FgnConst (cs, conDec)) => strictSpine (k, p, S))
              (* no other cases possible *)
      | strictExp (k, p, I.FgnExp (cs, ops)) = false
          (* this is a hack - until we investigate this further   -rv *)
    (* no other cases possible *)

    (* strictSpine (k, S) = B

       Invariant:
       If  G, D |- S : V > W
       and S is in nf (normal form)
       and |D| = k
       then B iff S is strict in k
    *)
    and strictSpine (_, _, I.Nil) = false
      | strictSpine (k, p, I.App (U, S)) =
          strictExp (k, p, U) orelse strictSpine (k, p, S)

    and strictDec (k, p, I.Dec (_, V)) =
          strictExp (k, p, V)

    (* strictArgParm (p, U) = B

       Traverses the flexible abstractions in U.

       Invariant:
       If   G |- U : V
       and  G |- p : V'
       and  U is in nf
       then B iff argument parameter p occurs in strict position in U
                  which starts with argument parameters
    *)
    fun strictArgParm (p, U as I.Root _) = strictExp (0, p, U)
      | strictArgParm (p, U as I.Pi _) = strictExp (0, p, U)
      | strictArgParm (p, U as I.FgnExp _) = strictExp (0, p, U)
      | strictArgParm (p, I.Lam (D, U)) = strictArgParm (p+1, U)

    fun occToString (SOME(ocd), occ) = Paths.wrap (Paths.occToRegionDef1 ocd occ, "")
      | occToString (NONE, occ) = "Error: "

    fun decToVarName (I.Dec (NONE, _)) = "implicit variable"
      | decToVarName (I.Dec (SOME(x), _)) = "variable " ^ x

    (* strictTop ((U, V), ocdOpt) = ()

       Invariant:
       condec has form c = U : V where . |- U : V
       and U is in nf (normal form)
       then function returns () if U every argument parameter of U
            has at least one strict and rigid occurrence in U
       raises Error otherwise

       ocdOpt is an optional occurrence tree for condec for error messages
    *)
    fun strictTop ((U, V), ocdOpt) =
        let fun strictArgParms (I.Root (I.BVar _, _), _, occ) =
                raise Error (occToString (ocdOpt, occ) ^ "Head not rigid, use %abbrev")
              | strictArgParms (I.Root _, _, _) = ()
              | strictArgParms (I.Pi _, _, _) = ()
              | strictArgParms (I.FgnExp _, _, _) = ()
                  (* may not be sound in general *)
                  (* Wed Aug 25 16:39:57 2004 -fp *)
              | strictArgParms (I.Lam (D, U'), I.Pi (_, V'), occ) =
                if strictArgParm (1, U')
                  then strictArgParms (U', V', Paths.body occ)
                else raise Error (occToString (ocdOpt, occ)
                                  ^ "No strict occurrence of " ^ decToVarName D ^ ", use %abbrev")
              | strictArgParms (U as I.Lam _, V as I.Root (I.Def _, _), occ) =
                  strictArgParms (U, Whnf.normalize (Whnf.expandDef (V, I.id)), occ)

        in
          strictArgParms (U, V, Paths.top)
        end

   fun occursInType ((i, V), ocdOpt) =
       let fun oit ((0, V), occ) = ()
             | oit ((i, I.Pi((D,P), V)), occ) =
               (case Abstract.piDepend ((D,P), V)
                  of I.Pi ((D', I.Maybe), V) => oit ((i-1, V), Paths.body occ)
                   | _ => raise Error (occToString (ocdOpt, occ)
                                       ^ "No occurrence of " ^ decToVarName D ^ " in type, use %abbrev"))
             | oit _ = ()
       in
         oit ((i, V), Paths.top)
       end

  in
    val check = strictTop
    val checkType = occursInType
  end
end;  (* functor Strict *)
