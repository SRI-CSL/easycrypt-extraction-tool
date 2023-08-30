open List

open Core
open EcParsetree
open EcLocation

let no_extract_headers = ["AllCore"; "Core"; "Int" ; "Real"; "Monoid"; "FinType"; "Bigop"; "Bool"; "IntMin";
                          "IntDiv"; "Finite"; "Ring"; "StdRing"; "Number"; "StdOrder"; "Bigalg"; "StdBigop"; "RealSeq";
                          "RealLub"; "Discrete"; "RealSeries"; "Binomial"; "Distr"; "AlgTactic"; "Tactics"; "DBool"]
let no_extraction = ref []
let set_no_extraction libs = no_extraction := no_extract_headers @ libs
(* ================================================================== *)
let no_imports_headers = ["Core"; "Monoid"; "FinType"; "Bigop"; "Bool"; "IntMin";
                          "Finite"; "Ring"; "StdRing"; "Number"; "StdOrder"; "Bigalg"; "StdBigop"; "RealSeq";
                          "RealLub"; "Discrete"; "RealSeries"; "Binomial"; "Distr"; "AlgTactic"; "Tactics"; "DBool"]
let no_imports = ref []
let set_no_imports libs = no_imports := no_imports_headers @ libs
               
(* ================================================================== *)
(** EasyCrypt constructors *)
let ec_words = [
    ("[]", "Nil") ;
    ("::", "Cons")
  ]

(* ================================================================== *)
(** Extraction of EasyCrypt symbols *)
let symbol_to_string s =
  try assoc s ec_words with | Not_found -> s
               
let psymbol_to_string psy = symbol_to_string (unloc psy)
                                     
(* ================================================================== *)
(** Extraction of EasyCrypt global action (= statement) *)
let get_dependencies_global_action = function
  | GthRequire threq ->
     let (_, psy_psyo_s, _) = threq in
     List.map (fun psy_psyo -> let (psy,_) = psy_psyo in psymbol_to_string psy) psy_psyo_s
  | _ -> []
       
let get_dependencies_global g = get_dependencies_global_action (unloc g.gl_action)

(* ================================================================== *)
(** Extraction of EasyCrypt script *)
let rec get_dependencies_global_list' = function
  | [] -> []
  | g :: gs -> get_dependencies_global g @ get_dependencies_global_list' gs

(* ================================================================== *)
(** Extraction of EasyCrypt script *)             
let rec get_dependencies_global_list gs =
  let deps = get_dependencies_global_list' gs in
  List.filter (fun dep -> not (mem dep !no_extraction)) deps

let rec replacements = function
  | [] -> []
  | imp :: imps ->
     if imp = "AllCore" then
       "Logic" :: "Int" :: "Real" :: replacements imps
     else imp :: replacements imps
               
let rec get_imports_global_list gs =
  let deps = get_dependencies_global_list' gs in
  let deps = replacements deps in
  List.filter (fun dep -> not (mem dep !no_imports)) deps
