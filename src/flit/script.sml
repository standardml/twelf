fun dumpText(tcb, semant, checker, output) =
    let 
	val _ =	Twelf.reset()
	val _ = Flit.initForText()
	val _ = Twelf.Print.width := Option.valOf Int.maxInt
	val _ = Twelf.Print.implicit := true
	val _ = Twelf.Print.printInfix := true
	val _ = Twelf.Print.noShadow := true
	val _ = Twelf.chatter := 1
	val _ = Twelf.reset();
	val _ = Twelf.Config.load(Twelf.Config.define ["word32.elf"]);
	val tcbConfig = Twelf.Config.read tcb
	val _ = Twelf.Config.append(tcbConfig)
	val _ = Flit.setEndTcb()
	val semantConfig = Twelf.Config.readWithout (semant, tcbConfig)
	val _ = Twelf.Config.append(semantConfig)
	val _ = Flit.setFlag()
	val _ = Twelf.Config.append(Twelf.Config.read checker)
	val _ = Flit.dumpText output
    in 
    () 
    end;

dumpText("pcc/flit/ltal.cfg",
	 "pcc/ltal/semant.cfg",
	 "pcc/ltal/checker.cfg",
	 "dump");
