local 
  structure F = FunSyn;
  structure I = IntSyn 

  fun load file =
    case Twelf.Config.load (Twelf.Config.read file)
      of Twelf.OK => Twelf.OK
       | Twelf.ABORT => raise Domain;
	

  fun test names =
    (let 
      val a = map (fn x => valOf (Names.constLookup (valOf (Names.stringToQid x)))) names
      val name = foldr op^ "" names
      val _ = Names.varReset IntSyn.Null
      val P = RelFun.convertPro a
      val F = RelFun.convertFor a
      val _ = (FunTypeCheck.check (P, F); Twelf.OK) 
      val LD = F.LemmaDec (names, P, F)
      val _ = TextIO.print (FunPrint.lemmaDecToString LD)
    in
      FunNames.installName (name, F.lemmaAdd LD)
    end)
in
  val _ = Twelf.chatter := 1
  val _ = FunNames.reset();

  val _ = Twelf.loadFile "TEST/cp.elf";
  val _ = test ["new"]

  val _ = raise Domain

  (* Regression test for Mini-ML *)
  val _ = load "examples/mini-ml/sources.cfg"
  val _ = Twelf.loadFile "examples/mini-ml/reduce.elf"
  val _ = test ["eval"]
  val _ = test ["value"]
  val _ = test ["vs"]
  val _ = test ["tps"]
  val _ = test ["==>"]
  val _ = test ["==>*"]  
    
  (* Regression test for copy *)
  val _ = Twelf.loadFile "TEST/cp.elf"
  val _ = test ["cpt"]


  (* Regression test for ccc *)
  val _ = load "examples/ccc/sources.cfg"
  val _ = test ["conc"]

  (* Regression test for prop-calc *)
  val _ = load "examples/prop-calc/sources.cfg"
  val _ = test ["combdefn"]

  (* Regression test for compile *)
  val _ = load "examples/compile/cpm/sources.cfg"
  val _ = test ["ccp"]
  val _ = test ["peq"]

  (* Regression test for logic programming *)
  val _ = load "examples/lp/sources.cfg"
  val _ = test ["can", "atm"]
  val _ = test ["iscan", "isatm"]
  val _ = test ["s_sound", "h_sound", "i_sound"]
  val _ = test ["cmpcs", "cmpai"]
  val _ = test ["gl", "pg"]
  val _ = test ["r_total"]
  (* Cannot work yet because we do not have mutual
     recursive functions.
  *)

  (* Regression test for compile *)
  val _ = load "examples/compile/cls/sources.cfg"
  val _ = test ["trans", "vtrans"]
  val _ = test ["feval"]
  val _ = test ["=>"]
  val _ = test [">=>*"]
  val _ = test [">ceval"] 
  val _ = test ["append"]
  val _ = test ["subcomp"] 
  val _ = test ["cev_complete"]
  val _ = test ["<"]
  val _ = test ["trans*"]
  val _ = test ["spl"]
  val _ = test ["cls_sound"]

  (* Regression test for Church-Rosser *)
  val _ = load "examples/church-rosser/sources.cfg"
  val _ = test ["identity"]
  val _ = test ["append"]
(*  val _ = test ["subst"] 
  val _ = test ["dia"]
  val _ = test ["strip"] 
  val _ = test ["conf"]
  val _ = test ["cr"] *)

  (* Regression test for Cut-Elimination *)
  val _ = load "examples/cut-elim/sources.cfg"
  val _ = test ["ca"]
  val _ = test ["ce"]
  val _ = test ["ca'"]
  val _ = test ["ce'"]

  val _ = load "examples/kolm/sources.cfg"
  val _ = test ["kolm"]
  val _ = test ["existskolm"]
  val _ = test ["nj_nk"]
  val _ = test ["equiv"]
  val _ = test ["complete"]
end

