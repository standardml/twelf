(*
  A simple traverser to generate input for the SPASS prover.
  Author: Frank Pfenning

Sample Session:

% cd /afs/cs/project/twelf/research/twelf/
% sml-cm
- CM.make ();
- use "examples/ccc/spass.sml";

This will print the SPASS representation for a bunch of axioms and theorems
of cartesian closed categories.  The encoding maps any morphism f : A -> B
(even compound ones) to the term mor(f,A,B) to guarantee type safety.

See

  spass.elf

for the definitions and status of various declarations.  Information on
the proofs can be found in pf.dvi (written by Andrzej Filinski) and
the other .elf files.
*)

structure Spass : TRAVERSER =
struct

  datatype tp =
    QFProp of string			(* Quantifier-free proposition *)
  | Prop of string * string		(* Proposition ("xs", "A") *)
  | Mor of string			(* Morphism "A,B" *)
  | Term of string                      (* Term "A" *)
  | Env of string                       (* Environment "E" *)
  | Obj					(* Object "A" *)
  | What of string			(* What "?error?" *)

  type obj = string

  type head = string
  type spine = string option

  type dec = string

  type condec = string

  fun par (s) = "(" ^ s ^ ")"

  (* types *)
  fun atom ("==", SOME(S)) = QFProp ("equal" ^ par (S))
    | atom ("mor", SOME(S)) = Mor ("arrow" ^ par (S)) 
    (* | atom ("mor", SOME(S)) = Mor (S) *)
    | atom ("term", SOME(S)) = Term (S)
    | atom ("conv", SOME(S)) = QFProp ("conv" ^ par (S))
    | atom ("env", SOME(S)) = Env (S)
    | atom ("absv", SOME(S)) = QFProp ("absv" ^ par (S))
    | atom ("abse", SOME(S)) = QFProp ("abse" ^ par (S))
    | atom ("obj", NONE) = Obj
    | atom _ = What "?atom?"

  fun arrow (QFProp(A1), QFProp(A2)) = 
        QFProp ("implies" ^ par (A1 ^ ", " ^ A2))	(* ?? *)
    | arrow _ = What "?arrow?"

  fun pi (x, Prop(xs,A)) = Prop (xs ^ "," ^ x, A)
    | pi (x, QFProp (A)) = Prop (x, "and" ^ par (A))
    | pi _ = What "?pi?"

  (* terms *)
  fun mor (f, A) = "mor" ^ par (f ^ "," ^ A)
  fun term (f, A) = "term" ^ par (f ^ "," ^ A)
  fun env (f, A) = "env" ^ par (f ^ "," ^ A)

  fun root ("id", NONE, Mor (A)) = mor ("id", A)	(* constants *)
    | root ("@", SOME(S), Mor(A)) = mor ("comp" ^ par (S), A)
    | root ("1", NONE, Obj) = "one"
    | root ("*", SOME(S), Obj) = "prod" ^ par(S)
    | root ("drop", NONE, Mor(A)) = mor ("drop", A)
    | root ("fst", NONE, Mor(A)) = mor ("fst", A)
    | root ("snd", NONE, Mor(A)) = mor ("snd", A)
    | root ("pair", SOME(S), Mor(A)) = mor ("pair" ^ par (S), A)
    | root ("=>", SOME(S), Obj) = "func" ^ par(S)
    | root ("app", NONE, Mor(A)) = mor ("app", A)
    | root ("cur", SOME(S), Mor(A)) = mor ("cur" ^ par (S), A)
    | root (x, NONE, Obj) = x		  (* object variables *)
    | root (x, NONE, Mor(A)) = mor (x, A) (* morphism variables *)
    (* lambda terms *)
    | root (x, NONE, Term(A)) = term (x, A)
    | root ("lpair", SOME(S), Term(A)) = term ("lpair" ^ par (S), A)
    | root ("lfst", SOME(S), Term(A)) = term ("lfst" ^ par (S), A)
    | root ("lsnd", SOME(S), Term(A)) = term ("lsnd" ^ par (S), A)
    | root ("lunit", SOME(S), Term(A)) = term ("lunit" ^ par (S), A)
    | root ("llam", SOME(S), Term(A)) = term ("llam" ^ par (S), A)
    | root ("lapp", SOME(S), Term(A)) = term ("lapp" ^ par (S), A)
    (* Evironments *)
    | root ("addv", SOME(S), Env(A)) = env ("addv" ^ par (S), A)
    | root ("empty", NONE, Env(A))   = env ("empty", A)
    | root (x, NONE, Env(A))        = env (x, A) (* environment variables *)
    | root _ = "?root?"
 
  (* val lam : dec * obj -> obj  *)
     fun lam _ = "?lam?" 

  fun bvar (x) = x
  fun const (c) = c
  fun def (d) = d

  val nils = NONE
  fun app (M, NONE) = SOME(M)
    | app (M, SOME(S)) = SOME(M ^ "," ^ S)

  (* declarations *)

  fun dec (x, A) = x

  fun objdec (c, Prop(xs,A)) =
      "%% " ^ c ^ " :\n"
      ^ "formula" ^ par ("forall" ^ par("[" ^ xs ^ "],\n"
      ^ A)) ^ ".\n"
    | objdec (c, QFProp(A)) =
      "%% " ^ c ^ " :\n"
      ^ "formula" ^ par ("and" ^ par(A)) ^ ".\n"
    | objdec (c, _) = "%% " ^ c ^ " : skipped.\n"

end;  (* structure Spass *)

structure Spass =
  Traverse (structure IntSyn' = IntSyn
	    structure Whnf = Whnf
	    structure Names = Names
	    structure Traverser' = Spass);


Twelf.Config.load (Twelf.Config.read "examples/ccc/spass.cfg");

 fun ccc (c) = (print (Spass.const (c)); print "\n"); 
 fun lambda (l) = (print (Spass.const (l)); print "\n"); 
 fun absenv (e) = (print (Spass.const (e)); print "\n");
 fun theorems (t) = (print (Spass.const (t)); print "\n");

(
lambda "c_fst";
lambda "c_snd";
lambda "c_pair";
lambda "c_lam";    (* is not translated because of parameter x *)
lambda "c_app";
lambda "c_unit";
lambda "c_prl";
lambda "c_prr";
lambda "c_surj";
(* 
lambda "c_test";
lambda "c_beta";   
lambda "c_eta";
*)
(*
absenv "av_x";
absenv "av_y";
absenv "avar";
absenv "aunit";
absenv "apair";
absenv "afst";
absenv "asnd";
absenv "alam"; 
absenv "aapp";
*)
theorems "case_lam1";
theorems "step1";
theorems "case_lam2";
theorems "IH";
theorems "weakv";
theorems "weak";
theorems "subv";




(* Equality *)  
(* refl, then, sym *)  

  (* identity and composition *)  
  (* =@= *)  
(*
  ccc "id_l";  
  ccc "id_r";  
  ccc "ass";  
*)
  (* products *)  
  (* =pair= *)  
(*  
  ccc "term_u";  
  ccc "prod_l";  
  ccc "prod_r";  
  ccc "prod_u";  
*)
  (* exponentials *)  
  (* =cur= *)  
(*  
  ccc "exp_e";  
  ccc "exp_u";  
*)
  (* lemmas *)  
(*
  ccc "distp";  
  ccc "appl";  
  ccc "distc";  
*)
  ()  
  );  
