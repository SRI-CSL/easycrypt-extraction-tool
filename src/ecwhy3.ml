(** 
Main module. 

Contains functions that deal with input/output interaction, using the Format and Arg OCaml modules.
 *)

(* ================================================================== *)
open Containers
open Format
open Lexing
open List
open String
   
open EcIo
open EcLocation

open Dependencies

let easycrypt_path = ref "/Users/vm2p/.opam/default/lib/easycrypt"
let easycrypt_options = ref []

(* ================================================================== *)
(** Option of the ECWHY3 program *)
let options =
  Arg.(align
         [
           ("-lib",
            String (fun s -> easycrypt_path := s),
            " sets the path for easycrypt (default is /usr/local/lib/easycrypt)");
           ("-ec",
            Rest (fun s -> easycrypt_options := s::!easycrypt_options),
            " every argument following -ec is an option to be interpreted by Easycrypt")
  ])

(** Usage message *)
let usage = "EasyCrypt to Why3 translation. Usage:
  ecwhy3.native [OPTIONS] <FILENAMES> [-ec <EASYCRYPT_OPTIONS>]
 Options available:"
          
(* ================================================================== *)
(** Input file name *)
let ifile = ref ""

(** Working directory *)
let idir = ref ""

(** Checks if the file argument is valid *)
let parses_file file =
  ifile := file ;

  if String.is_empty !ifile then begin eprintf "Nothing to translate\n@?"; exit 1 end;

  if not (Filename.check_suffix !ifile ".ec") then begin
      eprintf "Source file must have a .ec extension\n@?";
      Arg.usage options usage;
      exit 1
    end

(* ================================================================== *)
(** Gets the location of an error in the input file *)
let localisation pos =
  let l = pos.pos_lnum in
  let c = pos.pos_cnum - pos.pos_bol + 1 in
  eprintf "File \"%s\", line %d, characters %d-%d:\n" !ifile l (c-1) c

(* ================================================================== *)
(** Performs lexical analysis over some file buffer *)
let lex file = Lexing.from_channel file

(* ================================================================== *)
let confname = "easycrypt.conf"

let rec rem_all x = function
  | [] -> []
  | y :: ys -> if x = y then rem_all x ys else y :: rem_all x ys

let rec undup = function
  | [] -> []
  | x :: xs -> if List.mem x xs then x :: undup (rem_all x xs) else x :: undup xs

let rec get_file_path search_paths f =
  match search_paths with
  | [] -> None
  | d :: ds ->
     let file_name = Filename.concat d (f ^ ".ec") in
     if Sys.file_exists file_name then
       Some file_name
     else get_file_path ds f

let rec get_all_dependencies search_paths unvisited visited =
  match unvisited with
  | [] -> visited
  | f :: fs ->
     let ofp = get_file_path search_paths f in
     match ofp with
     | None -> assert false
     | Some fp ->
        let p = parseall (from_file fp) in
        let deps = get_dependencies_global_list p in
        get_all_dependencies search_paths (deps @ fs) (fp :: visited)

let mk_dummy_loc x =
  { pl_loc = _dummy ; pl_desc = x; }

let pervasive =
  "module Pervasive\n\nuse int.Int\nuse real.Real\n\nval function tt : unit\n\ntype distr 'a\n\nlet boolean_and (b : bool) (b' : bool) : bool = b && b'\n\nlet boolean_or (b : bool) (b' : bool) : bool = b || b'\n\nlet boolean_not (b : bool) : bool = not b\n\nval function logical_equality (x : 'a) (y : 'a) : bool\n\tensures { result <-> x = y }\n\nlet b2i (b : bool) : int = if b then 1 else 0\n\nval function iteri : int -> (int -> 'a -> 'a) -> 'a -> 'a\n\nlet iter (n : int) (f : 'a -> 'a) (x0 : 'a) : 'a = iteri n (fun i -> f) x0\n\nval function witness : 'a\n\nlet max (a : int) (b : int) = if (a < b) then b else a\n\nend\n\n"

let rec get_imports f = function
  | [] -> ["int.Int"; "real.Real"]
  | dep :: deps ->
     if String.equal (fst dep) f then get_imports f []
     else get_imports f deps @ [fst dep]
                                      
let main file =
  (* Get ignore files *)
  Format.printf "size no_extraction %d@." (List.length !no_extraction) ;

  let ic = open_in "no_extract.config" in
  let line = try input_line ic with e -> close_in_noerr ic; raise e in
  close_in ic ;
  Format.printf "line %s@." line ;
  set_no_extraction (String.split_on_char ',' line) ;
  set_no_imports (String.split_on_char ',' line) ;

  Format.printf "size no_extraction %d@." (List.length !no_extraction) ;
  
  parses_file file ;
  let myname  = Filename.basename Sys.executable_name
  and mydir   = Filename.dirname  Sys.executable_name in

  let eclocal =
    let rex = EcRegexp.regexp "^ec\\.(?:native|byte)(?:\\.exe)?$" in
    EcRegexp.match_ (`C rex) myname
  in

  let resource name =
    match eclocal with
    | true ->
        if String.equal (Filename.basename (Filename.dirname mydir)) "_build" then
          List.fold_left Filename.concat mydir
            ([Filename.parent_dir_name;
              Filename.parent_dir_name] @ name)
        else
          List.fold_left Filename.concat mydir name

    | false ->
        List.fold_left Filename.concat ""
          ([Filename.parent_dir_name; "lib"; "easycrypt"] @ name)
  in

  (* Parse command line arguments *)
  let options =
    let ini =
      let xdgini =
        XDG.Config.file ~exists:true ~mode:`All ~appname:EcVersion.app
          confname
      in List.hd (List.append xdgini [resource ["etc"; "easycrypt.conf"]]) in

    let ini =
      try  Some (EcOptions.read_ini_file ini)
      with
      | Sys_error _ -> None
      | EcOptions.InvalidIniFile (lineno, file) ->
          Format.eprintf "%s:%l: cannot read INI file@." file lineno;
          exit 1

    in EcOptions.parse_cmdline ?ini Sys.argv in

  let get_name f = Filename.chop_extension (Filename.basename f) in
  let name = get_name !ifile in

  (* Initialize load path *)
  Format.printf "Loading library path...@." ;

  let t0 = Sys.time () in
    
  let ldropts = options.o_options.o_loader in

  let theories_path = Filename.concat !easycrypt_path "theories" in
  let ec_lib =
    try
      Array.to_list (Sys.readdir theories_path)
    with
      e ->
      Format.printf "Easycrypt path\n  %s\nis probably wrong. The correct path should be passed with option -easycrypt_path XXX@." !easycrypt_path;
      raise e
  in
  let ec_lib = List.map (Filename.concat theories_path) ec_lib in
  let theories = List.map (fun x -> let (x1,x2,x3) = x in x2) ldropts.ldro_idirs @ ec_lib in
    
  let search_paths = Filename.dirname !ifile :: theories in

  let p = Filter_predicate.filter_global_list (parseall (from_file !ifile)) in

  let ec_prelude = [Filename.concat (Filename.concat theories_path "prelude") "Logic.ec"] in
      
  let t1 = Sys.time () in
  let tlp = (t1 -. t0) *. 1000. in

  Format.printf "Library path loaded in %f milliseconds\n@." tlp ;

  let get_file_dependencies f =
    let p = parseall (from_file f) in
    let deps = get_imports_global_list p in
    undup deps
  in

  Format.printf "Searching dependencies...@." ;

  let t0 = Sys.time () in
  
  let deps = get_dependencies_global_list p in
  let deps = get_all_dependencies search_paths deps [] in
  let deps = undup (ec_prelude @ deps) in

  let file_info f =
    let p = Filter_predicate.filter_global_list (parseall (from_file f)) in
    (get_name f, get_file_dependencies f, p)
  in

  let to_extract = List.map (fun f -> file_info f) deps @ [(name, get_imports_global_list p, p)] in

  let t1 = Sys.time () in
  let tdep = (t1 -. t0) *. 1000. in

  Format.printf "Dependencies found in %f milliseconds\n@." tdep ;
  
  let extraction_function name_dep_p =
    let (name, dep, p) = name_dep_p in
    Extraction.whyml_global_list name dep p ""
  in

  Format.printf "Extracting EasyCrypt to WhyML code...@." ;
  
  let t0 = Sys.time () in
  
  let whymls = List.map extraction_function to_extract in
  let whyml = String.concat "\n" whymls in
  let whyml = pervasive ^ whyml in

  let oc = open_out ("extraction.mlw") in
  Printf.fprintf oc "%s" whyml ;

  let t1 = Sys.time () in
  let twhyml = (t1 -. t0) *. 1000. in

  Format.printf "WhyML file generated in %f milliseconds\n\n@." twhyml ;

  Format.printf "EasyCrypt to WhyML code extraction total time: %f milliseconds@." (tlp +. tdep +. twhyml)
      

let () = Arg.parse options main usage 
