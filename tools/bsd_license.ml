let read_line () = 
  try
    Some (read_line ())
  with End_of_file -> None

let print_bsd_licence () = begin
  print_endline " * Three-clause BSD Licence";
  print_endline " *";
  print_endline " * All rights reserved.";
  print_endline " *";
  print_endline " * Redistribution and use in source and binary forms, with or without";
  print_endline " * modification, are permitted provided that the following conditions are met:";
  print_endline " *";
  print_endline " * - Redistributions of source code must retain the above copyright notice,";
  print_endline " *   this list of conditions and the following disclaimer.";
  print_endline " * - Redistributions in binary form must reproduce the above copyright notice,";
  print_endline " *   this list of conditions and the following disclaimer in the documentation";
  print_endline " *   and/or other materials provided with the distribution.";
  print_endline " * - The names of contributors may not be used to endorse or promote products";
  print_endline " *   derived from this software without specific prior written permission.";
  print_endline " *";
  print_endline " * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS \"AS IS\"";
  print_endline " * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE";
  print_endline " * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE";
  print_endline " * ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE";
  print_endline " * LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR ";
  print_endline " * CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF";
  print_endline " * SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS";
  print_endline " * INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN";
  print_endline " * CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)";
  print_endline " * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE";
  print_endline " * POSSIBILITY OF SUCH DAMAGE."
end
   
let rec initial () =
  match read_line () with
  | None -> ()
  | Some line ->
      let trimmed = String.trim line in
      if String.length trimmed >= 12 && String.sub trimmed 0 12 = "(* Copyright" then begin
        print_endline line;
        copyright_block ()
      end else
        print_endline line;
      initial ()

and copyright_block () =
  match read_line () with
  | None -> ()
  | Some line ->
      let trimmed = String.trim line in
      if String.length trimmed >= 2 && String.sub trimmed 0 2 = "*)" then begin
        print_endline line;
        initial ()
      end else if String.length trimmed >= 31 && String.sub trimmed 0 31 = "* This work is licensed under a" then begin
        print_endline line;
        print_bsd_licence ();
        drop_to_end_comment ()
      end else
        print_endline line;
      copyright_block ()

and drop_to_end_comment () =
  match read_line () with
  | None -> ()
  | Some line ->
      let trimmed = String.trim line in
      if String.length trimmed >= 2 && String.sub trimmed 0 2 = "*)" then begin
        print_endline line;
        initial ()
      end else
        drop_to_end_comment ()

let () = initial ()
