signature EXTLFRDEC =
sig
  structure ExtSyn : EXTSYN

  datatype lfrdec =
        condec of (string * Paths.region) * ExtSyn.term
      | sortdec of string * (string * Paths.region)
      | subdec of (string * Paths.region) * (string * Paths.region)

  (* only for debugging *)
  val toString : lfrdec -> string
end

signature RECON_LFRDEC =
sig
  include EXTLFRDEC

  exception Error of string

  val lfrdecToConDec : lfrdec * Paths.location -> IntSyn.ConDec * Paths.occConDec option
end
