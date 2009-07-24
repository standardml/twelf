
(* 
val cidName : IntSyn.cid -> string

getConForm id
   Collect the clauses defining the constructors of id, and
   conjoin the corresponding formulas.  
val getConForm : IntSyn.cid -> Formula.formula

val getMode : IntSyn.cid -> ModeSyn.ModeSpine option

val getGoal : IntSyn.cid -> Formula.formula

sgnToFormulas id
   Translate all decs before id to formulas. 
val sgnToFormulas : IntSyn.cid -> Formula.formula list

*) 

fun getIds () = 
    let
       val ids = ref []
       fun appFn cid = ids := cid :: !ids
    in
       S.sgnApp appFn
     ; !ids
    end

val getConForm : cid -> F.formula =
 fn id => 
    let
       val cs = getCons id
       val fs = map decToFormula cs
    in
       F.listConj fs
    end

(* val swapPis : Exp -> Exp = *)
(*  fn (Pi(dec1, Pi(dec2, exp))) => Pi(dec2, Pi(dec1, exp)) *)
(*   | _ => raise TwelfUtil "Not a nested pi" *)

(* val swapMspine : ModeSpine -> ModeSpine = *)
(*  fn Mnil => Mnil *)
(*   | Mapp(marg1, Mapp(marg2, mspine)) => Mapp(marg2, Mapp(marg1, mspine)) *)
(*   | _ => raise Impossible  *)

val decExp : cid -> Exp =
 fn id =>
    case sgnLookup id of
       ConDec(_, _, _, _, exp, _) => exp
     | _ => raise Unimplemented

val decMode : cid -> MS.ModeSpine =
 fn cid => 
    case MT.modeLookup cid of
       NONE => raise TwelfUtil ("No mode declaration for " ^ U.cidName cid)
     | SOME mspine => mspine

val expToString : Env.t * Exp -> string =
 fn (env, exp) => Print.expToString (Env.toDctx env, exp)

val modeToString : Mode -> string =
 fn Plus => "+"
  | Minus => "-"
  | _ => raise Unimplemented 

val rec mspineToString : ModeSpine -> string =
 fn Mnil => "[]"
  | Mapp(Marg(m, _), t) => modeToString m ^ " :: " ^ mspineToString t

val rec negativeModeSpine : ModeSpine -> bool =
 fn Mnil => true
  | Mapp(Marg(Minus, _), mspine) => negativeModeSpine mspine
  | _ => false

val expCid : Exp -> cid =
 fn Root (Const cid, _) => cid

val rec decFrame : Env.t * Exp * ModeSpine -> 
                   fvar list * fclause list * fvar list * fclause list =
 fn (env, exp, mspine) => 
    let in 
       printl ("exp   : " ^ expToString(env, exp));
       printl ("mspine: " ^ mspineToString mspine);
       case (exp, mspine) of 
          (* Output variable *)
          (Pi((dec as Dec (SOME x, exp1), _), exp2), Mapp(Marg(Minus, _), mspine')) =>
          if not(negativeModeSpine mspine) then
             raise TwelfUtil ("Bad mode: " ^ mspineToString mspine)
          else 
             let
                val env' = Env.push(SOME x, dec, env)
                val (u, a, e, g) = decFrame (env', exp2, mspine')
             in
                ((x, expCid exp1) :: u, a, e, g)
             end
        (* Output clause *)
        | (Pi((dec as Dec (NONE, exp1), _), exp2), Mapp(Marg(Minus, _), mspine)) =>
          let
             val env' = Env.push(NONE, dec, env)
             val (u, a, e, g) = decFrame(env', exp2, mspine)
          in
             F.And(expToFormula(env, exp1), )
          end
        (* Input variable *) 
        | (Pi((dec as Dec(SOME x, _), _), exp2), Mapp(Marg(Plus, _), mode)) =>
          let
             val env' = Env.push(SOME x, dec, env)
          in
             F.All(Var.hashString x, goalToFormula (env', exp2, mode))
          end
        (* Input clause *)
        | (Pi((dec as Dec(NONE, exp1), _), exp2), Mapp(Marg(Plus, _), mode)) =>
          let
             val env' = Env.push(NONE, dec, env)
          in
             F.Imp(expToFormula(env, exp1), goalToFormula (env', exp2, mode))
          end
        | (Uni Type, _) => F.Top
        | _ => let in 
                  printl("Error: " ^ expToString(env, exp))
                ; printl("       " ^ mspineToString mspine)
                ; raise Unimplemented
               end 
    end
