

local
  structure I = IntSyn
  structure T = Tomega

  fun load file =
    case Twelf.Config.load (Twelf.Config.read file)
      of Twelf.OK => Twelf.OK
       | Twelf.ABORT => raise Domain;
	

  fun printS nil = ()
    | printS (condec :: S) =
        (TextIO.print ((Print.conDecToString condec) ^ "\n"); printS S)
in

 val _ = Compiler.Control.Print.printDepth := 100;


  fun test names =
    (let 
      val a = map (fn x => valOf (Names.constLookup (valOf (Names.stringToQid x)))) names
      val name = foldr op^ "" names
      val _ = Names.varReset IntSyn.Null 
      val Ss = map Worldify.worldify a
      val S = foldr op@ nil Ss
      val _ = printS S
      val _ = TextIO.print "[convertPrg "
      val P = Converter.convertPrg a
      val _ = TextIO.print "convertFor... "
      val F = Converter.convertFor a
      val _ = TextIO.print "installPrg... "
      val _ = Converter.installPrg a
      val _ = TextIO.print "printing... "
      val _ = TextIO.print (TomegaPrint.forToString (I.Null, F) ^ "\n")
      val _ = TextIO.print (TomegaPrint.funToString P ^ "\n")
      val _ = TextIO.print "checking ... "
      val _ = TomegaTypeCheck.checkPrg (I.Null, (P, F))
      val _ = TextIO.print "]"
(*      val _ = (FunTypeCheck.check (P, F); Twelf.OK)   *)
(*      val LD = F.LemmaDec (names, P, F) *)
(*      val _ = TextIO.print (FunPrint.lemmaDecToString LD) *)
    in P
(*      FunNames.installName (name, F.lemmaAdd LD) *)
    end)

       
  fun print names =
    let
      val P = test names
    in
      (TextIO.print (TomegaPrint.funToString P ^ "\n"); P)
    end


  val _ = Twelf.chatter := 1
(*  val _ = FunNames.reset(); --cs *)

  val _ = load "/home/carsten/people/KarlCrary/sources.cfg";
  val _ = print ["foo"]

  val _ = load "examples/guide/sources.cfg"
  val _ = print ["cp"]


  (* Regression print for Mini-ML *)
  val _ = load "examples/mini-ml/sources.cfg"
  val _ = Twelf.loadFile "examples/mini-ml/reduce.elf"
  val _ = print ["eval"]
  val _ = print ["value"]
  val _ = print ["vs"]
  val _ = print ["tps"]
  val _ = print ["==>"]
  val _ = print ["==>*"]
  val _ = print ["closed"]

  (* Regression print for prop-calc *)
  val _ = load "examples/prop-calc/sources.cfg"
  val _ = print ["combdefn"]

  (* Regression print for ccc *)
  val _ = load "examples/ccc/sources.cfg"
  val _ = print ["conc"]

  (* Regression print for compile *)
  val _ = load "examples/compile/cpm/sources.cfg"
  val _ = print ["ccp"]
  val _ = print ["peq"]


  (* Regression print for copy *)
  val _ = Twelf.loadFile "TEST/cp.elf"
  val _ = print ["cpt"] 
  val _ = print ["new"]

(*  (* Regression test for Church-Rosser *)
  val _ = load "examples/church-rosser/sources.cfg"
  val _ = print ["identity"]
  val _ = print ["append"]
  val _ = print ["subst"] 
  val _ = print ["dia"] 
  val _ = print ["strip"] 
  val _ = print ["conf"]
  val _ = print ["cr"]
  val _ = print ["appd"]
  val _ = print ["lm1*"]
  val _ = print ["apr1*"]
  val _ = print ["apl1*"]
  val _ = print ["eq1"]
  val _ = print ["eq2"]

  (* Regression test for logic programming *)
  val _ = Twelf.loadFile "TEST/evenodd.elf"
  val _ = print ["even", "odd"]

*)
  (* Regression test for logic programming *)
  val _ = load "examples/lp-horn/sources.cfg"
  val _ = print ["can", "atm"]
  val _ = print ["iscan", "isatm"]
  val _ = print ["s_sound", "h_sound", "i_sound"]
  val _ = print ["cmpcs", "cmpai"]


  (* Regression test for logic programming *)
  val _ = load "examples/lp/sources.cfg"
  val _ = print ["can", "atm"]
  val _ = print ["iscan", "isatm"]
  val _ = print ["s_sound", "h_sound", "i_sound"]
  val _ = print ["cmpcs", "cmpai"]

  (* Regression test for Cut-Elimination *)
  val _ = load "examples/cut-elim/sources.cfg"
  val _ = print ["ca"]
  val _ = print ["ce"]
  val _ = print ["ca'"]
  val _ = print ["ce'"]

  (* Regression test for Kolmogoroff translation *)
  val _ = load "examples/kolm/sources.cfg"
  val _ = print ["kolm"]
  val _ = print ["existskolm"]
  val _ = print ["nj_nk"]
  val _ = print ["equiv"]
  val _ = print ["complete"]


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



end

