
(* 
 Each split yields a new clause of the proof.
 Each appeal to an induction hypothesis or lemma yields a hypothesis
 of the clause.
 *) 
structure Ind = 
struct 

open GeneralExt 
open PP.Ops
structure F = Formula
structure I = FolInstance
structure O = I.Output

type cid = IntSyn.cid

(* -------------------------------------------------------------------------- *)
(*  Types                                                                     *)
(* -------------------------------------------------------------------------- *)

datatype decl = 

(* Types *)
datatype tp = Tp of { cid: cid
                    , name: string
                    , cons: con list 
                    }

(* Constructors *)
     and con = Con of { cid: cid
                      , name: string
                      , args: tp list 
                      }



datatype form = Form of { vars: Var.t list
                        , hyps: Rel.t list
                        , concl: Rel.t
                        , formula: F.formula
                        }

(* Relations *)
datatype rel = Rel of { cid: cid
                      , name: string
                      , args: tp list
                      , clauses: clause list
                      }

(* Clauses *)
     and clause = Clause of { cid: cid
                            , name: string 
                            , form: F.formula 
                            }

(* -------------------------------------------------------------------------- *)
(*  Global Signature                                                          *)
(* -------------------------------------------------------------------------- *)

(* 
 We translate the Twelf signature into one easier to use for our purposes.
 We call IntSyn.sgnApp to walk over the Twelf signature.
 *) 

structure Signat :
             sig 
                val cons: cid -> con list
                val formulas: unit -> F.formula list
             end =
   struct 
      datatype signat = Signat of { tps: tp list
                                  , cons: con list
                                  , forms: form list
                                  , rels: rel list
                                  }
      type t = signat
      fun cons cid = raise Unimplemented 
      fun formulas () = raise Unimplemented 
      val emptySignat = Signat { tps = []
                               , cons = []
                               , forms = []
                               , rels = []
                               }

      val globalSignat: signat ref = ref emptySignat

      val twelfSignat: unit -> signat =
       fn () => 
          let
             val tps: tp list ref = ref []
             val cons: con list ref = ref []
             val forms: form list ref = ref []
             val rels: rel list ref = ref []
             fun appFn cid = raise Unimplemented 
          in
             IntSyn.sgnApp appFn
           ; Signat { tps = !tps
                    , cons = !cons
                    , forms = !forms
                    , rels = !rels
                    }
          end
   end 

structure S = Signat

(* -------------------------------------------------------------------------- *)
(*  Frames                                                                    *)
(* -------------------------------------------------------------------------- *)

structure Label = SymFn(val defaultName = "L")

datatype frame = Frame of { assums: (Label.t * Rel.t) list
                          , ihs: (Label.t * F.formula) list
                          , concl: Rel.t 
                          }

val ppFrame: frame -> PP.pp =
 fn Frame { ihs, assums, concl } => 
    &[ PP.listVert (fn (l, f) => PP.pair(Label.pp l, F.pp f)) ihs
     , PP.listHoriz (fn (l, r) => PP.pair(Label.pp l, Rel.pp r)) assums
     , $"=================================="
     , Rel.pp concl
     ]

type state = frame list

val frameToFormula: frame -> F.formula =
 fn Frame {assums, ihs, concl } => 
    let 
       val sigfs = Signat.formulas ()
    in
       F.listImp (sigfs @ map (F.Atom o snd) assums @ map snd ihs, F.Atom concl)
    end

(* -------------------------------------------------------------------------- *)
(*  Filling                                                                   *)
(* -------------------------------------------------------------------------- *)

val solve: F.formula -> ND.nd option =
 fn f => 
    let
       val input = { typ = PFormula.formulate f
                   , strategy = ProverUtil.VarRule
                   , proofterm = true
                   , maxSeconds = 600
                   , verbose = ProverUtil.none
                   , globalize = true
                   , statusInterval = 100
                   , heuristics = I.Heuristics.default
                   , selectionPolicy = DatabaseUtil.ExhaustSeqs
                   , subsumptionPolicy = DatabaseUtil.RecursiveDelete
                   , ruleSubsumption = true
                   , printLength = 100
                   , swapInterval = 4
                   , depthInterval = 4
                   , timer = Timer.startCPUTimer()
                   }
    in
       case I.prove input of
          O.Success (SOME (nd, _), t, stats) => 
          SOME nd
        | O.Saturated _ => NONE 
        | TimeOut => NONE
    end

val fill: frame -> ND.nd option =
 fn fr => solve (frameToFormula fr)

(* -------------------------------------------------------------------------- *)
(*  Splitting                                                                 *)
(* -------------------------------------------------------------------------- *)

val generalizeCon: con -> Term.term =
 fn Con { cid, name, args } =>
    let
       val args = List.tabulate
                     (length args, fn _ => Term.Var (Var.newNamed "X"))
    in
       Term.Fn(Func.hashString name, args)
    end

val substFrame: Subst.t * frame -> frame =
 fn (theta, Frame { assums, ihs, concl }) => 
    Frame { assums = map (fn (l, r) => (l, Rel.apply theta r)) assums
          , ihs = map (fn (l, f) => (l, F.apply(theta, f))) ihs
          , concl = Rel.apply theta concl
          }

(* Each split generates a new clause of the proof.
   split(fr, x, tau)
   tau is the cid representing the type of x
 *) 
val split: frame * Var.t * cid -> frame list =
 fn (frame as Frame { assums, ihs, concl }, x, cid) => 
    let
       val cons = S.cons cid
       val terms = map generalizeCon cons
       fun mapFn f = 
           let
              val theta = Subst.extend(Subst.id, x, f)
           in
              substFrame(theta, frame)
           end
    in
       map mapFn terms
    end

(* -------------------------------------------------------------------------- *)
(*  Recursion                                                                 *)
(* -------------------------------------------------------------------------- *)

val recurse: F.formula * frame -> frame =
 fn _ => raise Unimplemented 

(* -------------------------------------------------------------------------- *)
(*  Inversion                                                                 *)
(* -------------------------------------------------------------------------- *)

val invert: frame -> frame =
 fn _ => raise Unimplemented 

val mkState: F.formula -> state =
 fn _ => raise Unimplemented 

val mkSignat: unit -> unit =
 fn _ => ()

(* For now, pick a single induction variable. *)
type hints = Var.t * cid

val prove: F.formula * hints -> unit =
 fn (f, (x, cid)) => 
    let 
       val goal = f
       val signat = mkSignat ()
       fun loop [] = 
           let in 
              printl "Formula is proved!"
           end
         | loop (f::fs) =
           case fill f of
              SOME nd => loop fs
            | NONE => 
              let
                 val fs' = split(f, x, cid)
                 val fs' = map (fn fr => recurse(goal, invert fr)) fs'
              in
                 loop (fs' @ fs)
              end
       val state = mkState f
    in
       loop state
    end

end
