structure Index =
  Index (structure Global = Global
	 structure Queue = Queue
	 (*! structure IntSyn' = IntSyn !*));

structure IndexSkolem =
  IndexSkolem (structure Global = Global
	       structure Queue = Queue
	       (*! structure IntSyn' = IntSyn !*));
