
local 
  structure F = FunSyn
  structure I = IntSyn 
  structure S = StateSyn

  fun load file =
    case Twelf.Config.load (Twelf.Config.read file)
      of Twelf.OK => Twelf.OK
       | Twelf.ABORT => raise Domain;
	

  (* just for non-inductive types *)
  fun transformOrder' (G, Order.Arg k) = 
      let 
	val k' = (I.ctxLength G) -k+1
	val I.Dec (_, V) = I.ctxDec (G, k')
      in
	S.Arg ((I.Root (I.BVar k', I.Nil), I.id), (V, I.id))
      end
    | transformOrder' (G, Order.Lex Os) = 
        S.Lex (map (fn O => transformOrder' (G, O)) Os)
    | transformOrder' (G, Order.Simul Os) = 
        S.Simul (map (fn O => transformOrder' (G, O)) Os)

  fun transformOrder (G, F.All (F.Prim D, F), Os) =
	S.All (D, transformOrder (I.Decl (G, D), F, Os))
    | transformOrder (G, F.And (F1, F2), O :: Os) =
	S.And (transformOrder (G, F1, [O]),
	       transformOrder (G, F2, Os))
    | transformOrder (G, F.Ex _, [O]) = transformOrder' (G, O) 

  fun select c = (Order.selLookup c handle _ => Order.Lex [])
    
  fun test (depth, names) =
    (let 
      val a = map (fn x => valOf (Names.nameLookup x)) names
      val name = foldr op^ "" names
      val _ = Names.varReset ()
      val F = RelFun.convertFor a
      val Os =  map select a
      val _ = Twelf.chatter := 5
      val _ = MTPi.reset ()
      val _ = MTPi.init (depth, (F, transformOrder(I.Null, F, Os)))
val _ = raise Domain
      val _ = MTPi.auto ()
      val _ = Twelf.chatter := 3
    in
      ()
    end)
in
  val _ = Twelf.chatter := 3
  val _ = FunNames.reset();

(*
  (* Regression test for Mini-ML *)
  val _ = load "examples/mini-ml/test.cfg"
  val _ = Twelf.loadFile "examples/mini-ml/reduce.elf"
  val _ = test (5,["vs"])
  val _ = test (9, ["evalRed"])
(*  val _ = test ["tps"] *)


  val _ = load "examples/ccc/test.cfg";
  val _ = test (6, ["conc"])

  val _ = load "examples/prop-calc/test.cfg";
  val _ = test (6, ["abst"])


  (* Regression test for compile *)
  val _ = load "examples/compile/cpm/test.cfg"
  val _ = test (20, ["ccf"])
  val _ = test (6, ["peqr"])


  val _ = load "examples/lp-horn/test.cfg";
  val _ = test (4, ["s_snd", "h_snd", "i_snd"])
  val _ = test (4, ["ss_cn", "hs_at", "is_at"])
  val _ = test (4, ["compcs", "compai"])
*)

  val _ = load "examples/arith/test.cfg";
  val _ = test (3, ["assoc"]);

(* -----------------------
  val _ = load "TEST/fol.cfg";
 
  val _ = MTPGlobal.maxFill := 5
  val _ = test ["identity"]
  val _ = MTPGlobal.maxFill := 12
  val _ = test ["curry"]
(*  val _ = test ["uncurry"] 
  val _ = MTPGlobal.maxFill := 15
  val _ = test ["split"]  *)
(*  val _ = MTPGlobal.maxFill := 13
  val _ = test ["join"] *)
*)
end