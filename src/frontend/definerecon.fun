(* Reconstructing Define Declarations in Solve Queries *)
(* Author: Roberto Virga *)

functor DefineRecon (structure IntSyn' : INTSYN
                     structure Names : NAMES
                       sharing Names.IntSyn = IntSyn'
                     structure TpRecon' : TP_RECON
                       sharing TpRecon'.IntSyn = IntSyn'
                     structure Paths' : PATHS)
		   
  : DEFINE_RECON =
struct

  structure ExtSyn = TpRecon'
  structure Paths = Paths'
  structure IntSyn = IntSyn'

  datatype Define =
    Define of string * IntSyn.Exp option * string

  exception Error of string

  (* error (r, msg) raises a syntax error within region r with text msg *)
  fun error (r, msg) = raise Error (Paths.wrap (r, msg))

  local
    structure I = IntSyn'
    structure T = TpRecon'

  (* define := <constant name> * <type> option * <variable name> * <region> *)
  type define = string * IntSyn.Exp option * string * Paths.region

  (* define (name, optT, var, r) = (name, optV, var, r)
     where
       optV is the term optT, reconstructed in the empty context.
  *)
  fun define (name, NONE, var, r) = (name, NONE, var, r)
    | define (name, SOME (t), var, r) =
        let
          val _ = Names.varReset (I.Null)
          val (_, V, _, _) = T.termToExp (I.Null, t)
          val Xs =  Names.namedEVars ()
        in
          case Xs
            of nil => (name, SOME (V), var, r)
             | _ => error (r, "Type contains free variables")
        end

  fun defineToDefine (name, optV, var, r) = (Define (name, optV, var), r)

  in    
    type define = define

    val define = define

    val defineToDefine = defineToDefine
  end   (* local ... *)

end;  (* functor DefineRecon *)
