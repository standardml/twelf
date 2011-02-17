signature URISIG = sig
   type authority = {userinfo: string option, host: string, port: int option}
   type uri = {scheme: string option, authority: authority option, abs: bool, path: string list,
               query: string option, fragment: string option}
   val resolve     : uri * uri -> uri
   exception Error of string
   val parseURI    : string -> uri
   val uriToString : uri -> string
   (* turns an OS-specific path into a file:/... URI; if the first argument is "true",
      an empty path segment is appended (needed to make it a directory URI) *)
   val makeFileURI : bool * string -> uri
   val toFilePath  : uri -> string
   val relPathToString : string list -> string
end

structure URI : URISIG = struct
   type authority = {userinfo: string option, host: string, port: int option}
   val emptyAuth = {userinfo = NONE, host = "", port = NONE}
   (* note: the empty path is always relative *)
   type uri = {scheme: string option, authority: authority option, abs: bool, path: string list,
               query: string option, fragment: string option}
   fun makeURI(s,a,ab,p,q,f) : uri = {scheme = s, authority = a, abs = ab, path = p, query = q, fragment = f}

   fun makeFileURI(isDir : bool, fileName: string) : uri = 
      let
   	 val path = OS.Path.fromString (OS.Path.mkCanonical fileName)
   	 val volarcs = if #vol path = "" then #arcs path else (#vol path) :: (#arcs path)
      in
	 {scheme = SOME "file", authority = SOME emptyAuth,
	                    abs = #isAbs path,
	                    path = if isDir then volarcs @ [""] else volarcs,
	                    query = NONE, fragment = NONE}
      end
   
   (* s from and including index n, starting at 0 *)
   fun from(s, n) = if n >= String.size s then "" else String.extract(s, n, NONE)
   (* s until and including index n, starting at 0 *)
   fun till(s, n) = if n >= String.size s then s else String.substring(s, 0, n + 1)
   (* position of first occurrence of e in s, starting at 0; if none, ~1 (pos) or String.size s (pos') *)
   fun pos'(s, e) = if s = "" orelse String.isPrefix e s then 0 else 1 + pos'(from(s, 1), e)
   fun pos(s, e) = let val p = pos'(s,e) in if p = String.size s then ~1 else p end
   (* s until and excluding the first occurrence of e, possibly s *)
   fun bef(s, e) = till(s, pos'(s,e) - 1)
   (* s after and excluding the first occurrence of e, possibly "" *)
   fun aft(s,e)  = from(s, pos'(s,e) + String.size e)
   (* true iff s starts with e *)
   fun startsWith(s,e) = if pos(s,e) = 0 then true else false
   
   (* note: parsing does not cover query and fragment yet *)
   
   exception Error of string
   
   (* parses a URI *)
   fun parseURI s : uri =
      let
          val scheme = bef(s, ":")
      in
          (* no :, thus no scheme *)
          if pos(s,":") = ~1 then parseHierPart(NONE,s)
          (* no /?# before :, thus scheme *)
          else if pos(scheme, "/") = ~1 andalso pos(scheme, "?") = ~1 andalso pos(scheme, "#") = ~1
               then parseHierPart(SOME scheme, aft(s, ":"))
               (* /?# before :, thus no scheme *)
               else parseHierPart(NONE,s)
      end
   
   (* parses a URI without scheme (given by scheme) *)
   and parseHierPart(scheme, s) : uri =
      if startsWith(s, "//")
      (* // authority [/ path] [? query] [# fragment], path always absolute and possibly empty *)
      then let val authrest = aft(s, "//")
               val i = Int.min(Int.min(pos'(authrest, "/"), pos'(authrest, "?")), pos'(authrest, "#"))
               val (auth,rest) = (till(authrest, i-1), from(authrest, i))
           in parsePath(scheme, SOME (parseAuthority auth), rest)
           end
      (* [[/] path] [? query] [# fragment], path relative or absolute *)
      else parsePath(scheme, NONE, s)   

   (* parses a URI without scheme (given by scheme), authority (given by authority) *)
   (* note: currently no check for [? query] [# fragment] *)
   and parsePath(scheme, authority, s) : uri =
      let val (abs, path) = if s = "" then (false, nil) (* empty path *)
          else if startsWith(s, "/") then (true, parseRelPath(aft(s, "/"))) (* / path *)
          else (false, parseRelPath s) (* path *)
      in
         {scheme = scheme, authority = authority, abs = abs, path = path, query = NONE, fragment = NONE}
      end
  (* parses a /-separated path, no starting /, all segments may be empty *)
  and parseRelPath(s) : string list =
     (* segment *)
     if pos(s, "/") = ~1 then [s]
     (* segment / path *)
     else bef(s,"/") :: parseRelPath(aft(s, "/"))

  (* parses an authority component *)
   and parseAuthority(s) : authority =
      if pos(s, "@") = ~1
      then parseAuthority'(NONE, s)
      else parseAuthority'(SOME (bef(s, "@")), aft(s, "@"))
   (* parses an authority component without user info (given by userinfo) *)
   and parseAuthority'(userinfo, s) : authority =
      if pos(s, ":") = ~1
      then {userinfo = userinfo, host = s, port = NONE}
      else let val port = case Int.fromString(aft(s, ":"))
                of SOME i => i | NONE => raise Error("port must be integer: " ^ s)
           in {userinfo = userinfo, host = bef(s, ":"), port = SOME port}
           end

   fun resolve(base : uri, uriref : uri) : uri =
      let val {scheme = bs, authority = ba, abs = babs, path = bp, query = bq, fragment = _} = base
          val {scheme = rs, authority = ra, abs = rabs, path = rp, query = rq, fragment = rf} = uriref
          (* remove last, nil if nil *)
          fun init'(hd::nil) = nil | init'(hd::tl) = hd :: (init' tl) | init' nil = nil
          (* remove dot segments (cases refer to 5.2.4 in RFC 3986)
             if the input path is absolute/relative, so is the output: result is /"" or nil if all segments are cancelled *)
          fun rem'(nil, abs, outp) = outp
            | rem'(hd::tl, abs, outp) =
               if hd = "." then rem'(tl, abs, outp) (* . is dropped (cases ABD) *)
               else if hd = ".."
                    then if abs then rem'(if tl = nil then [""] else tl, true, init' outp) (* .. cancels previous if any (case C), possibly append "" to make sure path stays absolute *)
                                else rem'(tl, false, outp)      (* .. at beginning of relative path is dropped (case AD) *)
                    else rem'(tl, true, outp @ [hd])            (* normal segment (case E) *)
          fun rem(inp, abs) = rem'(inp, abs, nil)
          (* merge paths *)
          fun merge(nil,r) = r
            | merge(b,r) = init' b @ r
      in
          if isSome rs then makeURI(rs, ra, rabs, rem(rp, rabs), rq, rf)
          else if isSome ra then makeURI(bs, ra, rabs, rem(rp,rabs), rq, rf)
          else if rp = nil
               then if isSome rq then makeURI(bs, ba, babs, rem(bp, rabs), rq, rf)
                                 else makeURI(bs, ba, babs, rem(bp, babs), bq, rf)
               else if rabs      then makeURI(bs, ba, rabs, rem(rp, rabs), rq, rf)
                                 else makeURI(bs, ba, babs, rem ((merge(bp, rp)), rabs), rq, rf)
      end

   (* prints optional string with delimiters, "" if NONE *)
   fun po(bef: string, it: string option, aft: string) = case it
      of SOME s => bef ^ s ^ aft
       | NONE => ""

   (* prints an authority *)
   fun authToString(auth: authority option) = case auth
      of SOME a => "//" ^ po("", #userinfo a, "@") ^ #host a ^ po(":", Option.map Int.toString (#port a), "")
       | NONE => ""
   
   (* prints a relative path *)
   fun relPathToString(nil) = ""
     | relPathToString(hd::nil) = hd
     | relPathToString(hd::tl) = hd ^ "/" ^ relPathToString tl

   (* prints a path, abs=true iff absolute path *)
   fun pathToString(path, abs) = (if abs then "/" else "") ^ relPathToString path

   (* prints a uri *)
   fun uriToString(uri: uri) = po("", #scheme uri, ":") ^ authToString(#authority uri) ^ pathToString (#path uri, #abs uri) ^
                         po("?", #query uri, "") ^ po("#", #fragment uri, "")

   fun toFilePath(uri: uri) : string =
     let
        val _ = if #scheme uri = SOME "file" then () else raise Error("not a file URI: " ^ uriToString uri)
        val _ = if #authority uri = SOME emptyAuth orelse #authority uri = NONE then ()
                else raise Error("not a local file URI: " ^ uriToString uri)
        val _ = if isSome (#query uri) orelse isSome (#fragment uri)
                then raise Error("file URI with query or fragment cannot be converted to file path: " ^ uriToString uri)
                else ()
        (* seems to be the only way to check if the OS expects the first path segement to be a volume label *)
        val p = #path uri
        val path = if p = nil then {vol = "", isAbs = false, arcs = nil}
                   else if #vol (OS.Path.fromString (List.hd p)) = ""
                        then {vol = "", arcs = p, isAbs = #abs uri}
                        else {vol = List.hd p, arcs = List.tl p, isAbs = #abs uri}
     in OS.Path.mkCanonical (OS.Path.toString path)
     end
   
end