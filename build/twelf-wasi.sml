(*
 *
 * This file makes twelf into a library that can be called directly from WASI Preview 1,
 * which specifies an API by which WebAssembly programs can interact with the outside world.
 * It is somewhat like POSIX.
 *
 * https://github.com/WebAssembly/WASI/blob/main/legacy/preview1/docs.md
 *
 * It provides two entry points:
 *
 * allocate : int -> CharArray.array
 *   expects to be called with the length of the twelf source string
 *   we want to evaluate, so that the sml side can allocate a buffer.
 *   The caller is then expected to write the twelf source into the
 *   buffer returned.
 *
 * execute : unit -> unit
 *   has the side effect of loading the string found in the allocated
 *   buffer, which will result in various print statements. The caller
 *   is expected to implement the WASI fd_write endpoint so that they
 *   can see the output so printed.
 *)

val bref: CharArray.array option ref = ref NONE

val e = _export "allocate": (int -> CharArray.array) -> unit;
val _ = e (fn size =>
				  let
					 val b = CharArray.tabulate (size, fn _ => Char.chr 0)
				  in
					 bref := SOME b; b
				  end)

val e = _export "execute": (unit -> unit) -> unit;
val _ = e (fn () => (case !bref of
								 NONE => print "No input buffer allocated"
							 | SOME b => (Twelf.loadString (CharArray.vector b); ())))
