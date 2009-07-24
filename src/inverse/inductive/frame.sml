
structure Frame :> FRAME =
struct

structure List = ListExt
structure F = Formula
structure Prover = FolInstance
structure O = Prover.Output
structure U = TwelfUtil
structure S = Subst
structure T = Term
structure I = IntSyn
structure MS = ModeSyn
structure MT = ModeTable

open GeneralExt 

(* -------------------------------------------------------------------------- *)
(*  Frame type                                                                *)
(* -------------------------------------------------------------------------- *)

datatype induct = Simple of Var.t
                | Lex    of Var.t list

type fvar = (Var.t * I.cid) list

type fclause = (Var.t * Rel.t * I.cid) list

datatype frame = Frame of { univ   : fvar list
                          , assums : fclause list
                          , exis   : fvar list
                          , goals  : fclause
                          , induct : induct
                          }

val subst : Subst.t * frame -> frame =
 fn (theta, Frame {univ, assums, exis, goals, induct}) => 
    let
       fun mapFn (x, r, cid) = (x, Rel.apply theta r, cid)
       val assums' = map mapFn assums
       val goals' = map mapFn goals
    in
       Frame { univ = univ
             , assums = assums'
             , exis = exis
             , goals = goals'
             , induct = induct
             }
    end

(* Remove unused variables *) 
val cleanup : frame -> frame =
 fn Frame {univ, assums, exis, goals, induct} => 
    let
       val arels = map #2 assums
       val grels = map #2 goals
       val vars = Var.Set.unions (map Rel.vars (arels @ grels))
       val fvs = Var.Set.difference(vars, Var.Set.fromList (map fst exis))
    in
       Frame{ univ = List.filter (fn (x, _) => Var.Set.member(fvs, x)) univ
            , assums = assums
            , exis = exis
            , goals = goals
            , induct = induct
            }
    end

local
   open PP.Ops
in

val pp : frame -> PP.pp =
 fn Frame {univ, assums, exis, goals, ...} => 
    let
       val univP = PP.listHoriz (fn (x, cid) => %[Var.pp x, $" : ", $(U.cidName cid)]) univ
       fun ppAssum (x, r, id) = 
           %[Var.pp x, $" : ", Rel.pp r, $" (", PP.int id, $")"]
       val assumsP = PP.listVert ppAssum assums
       val exisP = PP.listHoriz (fn (x, cid) => %[Var.pp x, $" : ", $(U.cidName cid)]) exis
       val goalsP = PP.listVert ppAssum goals
    in
       %[$"Frame: ", &[ univP
                      , assumsP
                      , $"==================================="
                      , exisP
                      , goalsP
                      ]]
    end

end (* local *) 

(* -------------------------------------------------------------------------- *)
(*  Initial Frame                                                             *)
(* -------------------------------------------------------------------------- *)

val fromDec : I.cid -> frame = 
 fn cid => 
    let 
       val U.Frame {univ, assums, exis, goals} = U.decFrame cid
    in
       Frame { univ = univ
             , assums = assums
             , exis = exis
             , goals = goals
             , 
             }
    end

(* -------------------------------------------------------------------------- *)
(*  Filling                                                                   *)
(* -------------------------------------------------------------------------- *)

val toFormula : frame -> F.formula =
 fn Frame {univ, assums, exis, goals, ...} => 
    let
       val univ' = map fst univ
       val assums' = map (F.Atom o #2) assums
       val exis' = map fst exis
       val goals' = map (F.Atom o #2) goals
    in
       F.listAll(univ',
                 F.Imp(F.listConj assums',
                       F.listEx(exis', F.listConj goals')))
    end

val prove : F.formula -> bool =
 fn f => case Prover.simpleProve (PFormula.formulate f) of
            O.Success _ => true
          | _ => false

val fill : frame -> bool = prove o toFormula 

(* -------------------------------------------------------------------------- *)
(*  Splitting                                                                 *)
(* -------------------------------------------------------------------------- *)

val split : frame * Var.t -> frame list =
 fn (frame as Frame {univ, assums, exis, goals, induct}, x) => 
    case List.findRem (fn (y, _) => Var.eq(x, y)) univ of
       (* Induction on a variable *)
       SOME ((_, cid), univ') => 
       let
          val cons = map U.decToTerm (U.getCons cid)
          fun mapFn con = 
              let
                 val newVars = 
                     case con of 
                        T.Fn(_, xs) => map (fn T.Var x => x | _ => raise Impossible) xs
                      | _ => raise Impossible 
                 val theta = S.extend(S.id, x, con)
              in
                 cleanup(subst(theta, frame))
              end
       in
          map mapFn cons
       end
     (* Induction on a clause *)
     | NONE => 
       case List.findRem (fn (y, _, _) => Var.eq(x, y)) assums of
          NONE => raise Impossible 
        | SOME ((_, rel, cid), assums') => 
          let
             val cons = map U.decToFormula (U.getCons cid)
             fun mapFn con = 
                 case U.unifyConcl(con, rel) of
                    NONE => raise Impossible 
                  | SOME rels => 
                    let
                       fun mapFn rel = (Var.newNamed "D", rel, cid (* XXX wrong cid *))
                       val rels' = map mapFn rels
                    in
                       Frame { univ = univ
                             , assums = rels' @ assums'
                             , exis = exis
                             , goals = goals
                             , induct = induct
                             }
                    end
          in
             map mapFn cons
          end

(* val fromGoal  : Formula.formula -> frame *)
(* val toFormula : frame -> Formula.formula *)
(* val invert    : int -> frame list *)
(* val recurse   : frame -> frame *)
(* val fill      : frame -> bool *)

end
