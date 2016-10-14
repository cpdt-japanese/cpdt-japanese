let read_line () = 
  try
    Some (read_line ())
  with End_of_file -> None

let strstr' p s n =
  try
    Some (Str.search_forward (Str.regexp_string p) s n)
  with Not_found -> None

let strstr p s = strstr' p s 0

let prefix s1 s2 = String.length s2 >= String.length s1 && Str.string_before s2 (String.length s1) = s1

let sanitize s =
  let rec san n acc =
    try
      let pos = Str.search_forward (Str.regexp "\\[\\|%\\|#") s n in
      let ender = match s.[pos] with
      | '[' -> ']'
      | _ -> s.[pos] in
      let pos' = String.index_from s (pos+1) ender in
      san (pos'+1) (acc ^ String.sub s n (pos-n))
    with Not_found -> acc ^ Str.string_after s n
  in san 0 ""

let rec initial () =
  match read_line () with
  | None -> ()
  | Some line ->
      match strstr "(**" line with
      | None -> initial ()
      | Some pos ->
	  match strstr "*)" line with
	  | None ->
	      begin match strstr "[[" line with
	      | None ->
		  print_endline (sanitize (Str.string_after line (pos+3)));
		  comment ()
	      | Some _ -> runTo "]]"
	      end
	  | Some pos' ->
	      let rest = Str.string_after line (pos+3) in
	      if not (prefix " printing" rest || prefix " begin" rest || prefix " end" rest) then
		print_endline (sanitize (String.sub line (pos+3) (pos' - (pos+3))));
	      initial ()

and comment () =
  match read_line () with
  | None -> ()
  | Some line ->
      match strstr "*)" line with
      | None ->
	  begin match strstr "[[" line with
	  | None ->
	      begin match strstr "<<" line with
	      | None ->
		  print_endline (sanitize line);
		  comment ()
	      | Some _ -> runTo ">>"
	      end
	  | Some _ -> runTo "]]"
	  end
      | Some pos ->
	  print_endline (sanitize (Str.string_before line pos));
	  initial ()

and runTo ender =
  match read_line () with
  | None -> ()
  | Some line ->
      match strstr ender line with
      | None -> runTo ender
      | _ ->
	  match strstr "*)" line with
	  | None -> comment ()
	  | _ -> initial ()

let () = initial ()
