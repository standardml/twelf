structure ThmSyn = 
  ThmSyn (structure IntSyn' = IntSyn
	  structure Abstract = Abstract
	  structure ModeSyn' = ModeSyn
	  structure Whnf = Whnf
	  structure Paths' = Paths);

structure ThmPrint =
  ThmPrint (structure ThmSyn' = ThmSyn
	    structure Formatter = Formatter);

structure Thm =
  Thm (structure Global = Global
       structure ThmSyn' = ThmSyn
       structure Order = Order
       structure ModeSyn' = ModeSyn
       structure ThmPrint = ThmPrint
       structure Paths' = Paths);
