signature REDUNDANT  =
  sig
    exception Error of string

    val convert : Tomega.Prg -> Tomega.Prg
  end