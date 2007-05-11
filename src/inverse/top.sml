
Control.Print.printDepth := 10;;
Control.Print.printLength := 1000;;
Control.Print.stringDepth := 1000;;

CM.make "sources.cm"; 
Twelf.make "examples/sources.cfg"; 
exception Success;

Twelf.make "/Users/seanmcl/save/projects/twelf/test/lf/sources-chk.cfg"
Twelf.make "/Users/seanmcl/save/projects/twelf/test/lf/sources.cfg"

val sgn = 
(Translate.translate_signature();raise Success)
handle Fail x => x





handle Translate.Trans1 x => x
     | Translate.Fail3 x => x

val s = SpineLF.Sgn.array sgn;

(* -------------------------------------------------------------------------- *)
(*  Debug                                                                     *)
(* -------------------------------------------------------------------------- *)




val n = Lib.fst (IntSyn.sgnSize()); 
val cs = map IntSyn.sgnLookup (Lib.upto(0,n-1)); 
structure L = Lib
structure T = Translate
structure S = SpineLF
structure Sgn = S.Sgn
structure I = IntSyn
fun name n = I.conDecName (I.sgnLookup n)
name 2
name 42


structure C = ClausePrint
structure Ctx = Context
val sgn = Sgn.empty
val dec0 = T.translate_condec (0,(L.ith 0 cs))
val sgn0 = Sgn.insert sgn dec0
val dec1 = T.translate_condec (1,(L.ith 1 cs))
val sgn1 = Sgn.insert sgn0 dec1
val dec2 = T.translate_condec (2,(L.ith 2 cs))
val sgn2 = Sgn.insert sgn1 dec2
val dec3 = T.translate_condec (3,(L.ith 3 cs))
val sgn3 = Sgn.insert sgn2 dec3
val dec4 = T.translate_condec (4,(L.ith 4 cs))
val sgn4 = (Sgn.insert sgn3 dec4;raise Fail "success")
  handle S.Check s => (print s;raise Fail "")
       | S.Fail2(s,v1,v2) => (s,v1,v2)


open S


val tm = (ExpLam
              (ExpApp
                 (HdConst 3,
                  SpCons
                    (ExpApp (HdVar 1,SpNil),
                     SpCons
                       (ExpApp (HdVar 1,SpNil),
                        SpCons (ExpLam (ExpApp (HdVar 1,SpNil)),SpNil))))))

val ty = ExpPi
           (ExpApp (HdConst 0,SpNil),
            ExpApp
              (HdConst 2,
               SpCons
                 (ExpApp
                    (HdConst 1,
                     SpCons
                       (ExpApp (HdVar 1,SpNil),
                        SpCons (ExpApp (HdVar 1,SpNil),SpNil))),SpNil)))

exception Success
(* -------------------------------------------------------------------------- *)

val ctx = C.empty
val sgn = sgn3
val M = tm
val A = ty

(* -------------------------------------------------------------------------- *)

val (ExpLam M,ExpPi(A1,A2)) = (M,A)
val ctx = (C.push ctx A1) 
check' sgn ctx M A2
  handle Check s => (print s;raise Fail "")

(* -------------------------------------------------------------------------- *)

val ExpApp(HdConst con,S) = M
val SOME (Dec decl) = Sig.lookup sgn con 
focus sgn ctx S (#exp decl) 
  handle Check s => (print s;raise Fail "")

(* -------------------------------------------------------------------------- *)

val A = #exp decl
val (SpCons(M,S),ExpPi(A1,A2)) = (S,A)
check' sgn ctx M A1
focus sgn ctx S (apply_exp (SubCons(M,SubId)) A2)
  handle Check s => (print s;raise Fail "")

(* -------------------------------------------------------------------------- *)


val A = (apply_exp (SubCons(M,SubId)) A2)
val (SpCons(M,S),ExpPi(A1,A2)) = (S,A)
check' sgn ctx M A1
(focus sgn ctx S (apply_exp (SubCons(M,SubId)) A2);raise Success)
  handle S.Fail2(s,v1,v2) => (s,v1,v2)

(* -------------------------------------------------------------------------- *)

val A = (apply_exp (SubCons(M,SubId)) A2)
val (SpCons(M,S),ExpPi(A1,A2)) = (S,A)
check' sgn ctx M A1
focus sgn ctx S (apply_exp (SubCons(M,SubId)) A2)
  handle Check s => (print s;raise Fail "")

val tm1 = ExpLam (ExpApp (HdVar 1,SpNil)) 
val ty1 = ExpPi
           (ExpApp (HdConst 3,SpCons (ExpApp (HdVar 1,SpNil),SpNil)),
            ExpApp (HdConst 3,SpCons (ExpApp (HdVar 2,SpNil),SpNil)))

val (ExpLam M,ExpPi(A1,A2)) = (tm1,ty1)
check' sgn (C.push ctx A1) M A2

val (ExpApp(HdVar i,S)) = M
val SOME A = C.lookup ctx (i-1)
focus sgn (C.push ctx A1) S A
 A2

check' sgn ctx tm1 ty1


(* -------------------------------------------------------------------------- *)

val A = A2
val (SpCons(M,S),ExpPi(A1,A2)) = (S,A)
check' sgn ctx M A1
focus sgn ctx S (apply_exp (SubCons(M,SubId)) A2)
  handle Check s => (print s;raise Fail "")



check' sgn4 ctx tm ty


check' sgn4 ctx1 M A2
  handle Check s => (print s;raise Fail "")


val (ExpApp(HdConst con,S)) = M
val SOME (Dec decl) = Sig.lookup sgn con

focus sgn ctx S (#exp decl) 
  handle Check s => (print s;raise Fail "")






S.print_exp sgn4 tm

(* -------------------------------------------------------------------------- *)
(*  Junk                                                                      *)
(* -------------------------------------------------------------------------- *)



Twelf.make "../../sources.cfg"; 
exception Success;
(Translate.translate_signature();raise Success)
  handle Translate.Translate s => (print s; raise Fail "")
       | SpineLF.Check s => (print s; raise Fail "")
       | SpineLF.Fail2(s,u1,u2) => (s,u1,u2)


Twelf.make "../../sources.cfg"; 
Translate.translate_signature();
