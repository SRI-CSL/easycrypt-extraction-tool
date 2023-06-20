open List

open Core
open EcParsetree
open EcLocation
open EcBigInt

(* ================================================================== *)
(** EasyCrypt constructors *)
let ec_words = [
    ("[]", "Nil") ;
    ("::", "Cons") ;
    ("=", "logical_equality") ;
    ("/\\", "boolean_and") ;
    ("&&", "boolean_and") ;
    ("\\/", "boolean_or") ;
    ("*", "( * )") ;
    ("+", "( + )") ;
    ("-", "( - )") ;
    ("/", "( / )") ;
    ("^", "( ^ )") ;
    ("[-]", "( -_ )") ;
    ("++", "( ++ )") ;
    ("[!]", "boolean_not") ;
    ("\\c", "ofcomp") ;
    ("\\o", "fcomp") ;
    ("\\o2", "fcomp2") ;
    ("\\in", "membership") ;
  ]

(* ================================================================== *)
(** Extraction of EasyCrypt symbols *)
let whyml_symbol s =
  try assoc s ec_words with | Not_found -> s

let rec whyml_symbol_list ss sep = String.concat sep (List.map whyml_symbol ss)

let whyml_pqsymbol pqsy =
  let pqsy = unloc pqsy in
  if fst pqsy = [] then
    whyml_symbol (snd pqsy)
  else
    whyml_symbol_list (fst pqsy) "." ^ "." ^ whyml_symbol (snd pqsy)
               
let whyml_psymbol psy = whyml_symbol (unloc psy)

let whyml_psymbol_list psys sep = String.concat sep (List.map whyml_psymbol psys)

let whyml_osymbol_r = function
  | None -> "_"
  | Some psy -> whyml_psymbol psy
                                
let whyml_osymbol osy = whyml_osymbol_r (unloc osy)

let whyml_osymbol_list osys sep = String.concat sep (List.map whyml_osymbol osys)

(* ================================================================== *)
(** Extraction of EasyCrypt type parameters *)
let rec whyml_ptyparams ptyps sep = String.concat sep (List.map (fun p -> whyml_psymbol (fst p)) ptyps)

(* ================================================================== *)
(** Extraction of EasyCrypt type definitions *)
let rec whyml_pty pty = whyml_pty_r (unloc pty)

and whyml_pty_list ptys sep = String.concat sep (List.map whyml_pty ptys)
    
and whyml_pty_r = function
  | PTunivar -> "univar"
  | PTtuple  ptys -> "(" ^ whyml_pty_list ptys ", " ^ ")"
  | PTnamed  pqsy -> whyml_pqsymbol pqsy
  | PTvar    psy -> whyml_psymbol psy
  | PTapp    (pqsy, ptys) -> whyml_pqsymbol pqsy ^ " (" ^ whyml_pty_list ptys ") " ^ ")"
  | PTfun    (pty1, pty2) -> "(" ^ whyml_pty pty1 ^ ") -> " ^ whyml_pty pty2
  | PTglob   _ -> "glob"

(* ================================================================== *)
(** Extraction of EasyCrypt inductive datatype *)
let whyml_constructor ptd =
  let (cons_id, cons_params) = ptd in
  if cons_params = [] then
    "| " ^ whyml_psymbol cons_id
  else
    "| " ^ whyml_psymbol cons_id ^ " (" ^ whyml_pty_list cons_params ") (" ^ ")"
                      
let whyml_pdatatype ptds sep = String.concat sep (List.map whyml_constructor ptds)

(* ================================================================== *)
(** Extraction of EasyCrypt records *)
let whyml_record_field prec =
  let (rec_id, rec_ty) = prec in
  whyml_psymbol rec_id ^ " : " ^ whyml_pty rec_ty 
                             
let whyml_precord precs sep = String.concat sep (List.map whyml_record_field precs)             

(* ================================================================== *)
(** Extraction of EasyCrypt type declaration *)
let whyml_ptydecl ptyd =
  match ptyd.pty_body with
  | PTYD_Abstract _ -> "type " ^ whyml_psymbol ptyd.pty_name ^ " " ^ whyml_ptyparams ptyd.pty_tyvars " "
  | PTYD_Alias pty -> "type " ^ whyml_psymbol ptyd.pty_name ^ " " ^ whyml_ptyparams ptyd.pty_tyvars " " ^ " = " ^ whyml_pty pty
  | PTYD_Record prec -> "type " ^ whyml_psymbol ptyd.pty_name ^ " " ^ whyml_ptyparams ptyd.pty_tyvars " " ^ " = { " ^ whyml_precord prec " ; " ^ " }"
  | PTYD_Datatype pdt -> "type " ^ whyml_psymbol ptyd.pty_name ^ " " ^ whyml_ptyparams ptyd.pty_tyvars " " ^ " =\n" ^ whyml_pdatatype pdt "\n"

let rec whyml_ptydecl_list ptyds sep = String.concat sep (List.map whyml_ptydecl ptyds)

(* ================================================================== *)
(** Extraction of EasyCrypt arguments *)
let rec whyml_ptybinding arg =
  let (osys, pty) = arg in
  match osys, (unloc pty) with
  | ([], _) -> ""
  | ([osy], PTunivar) -> "(" ^ whyml_osymbol osy ^ ")"
  | ([osy], _) -> "(" ^ whyml_osymbol osy ^ " : " ^ whyml_pty pty ^ ")"
  | (_, PTunivar) -> "(" ^ String.concat (") (") (List.map whyml_osymbol osys) ^ ")"
  | (_, _) -> "(" ^ String.concat (" : " ^ whyml_pty pty ^ ") (") (List.map whyml_osymbol osys) ^ " : " ^ whyml_pty pty ^ ")"
  
let whyml_ptybindings args sep = String.concat sep (List.map whyml_ptybinding args)

(* ================================================================== *)
(** Extraction of EasyCrypt expressions *)
let whyml_plpattern_r = function
  | LPSymbol psy -> whyml_psymbol psy
  | LPTuple osys -> "(" ^ whyml_osymbol_list osys ", " ^ ")"
  | LPRecord _ -> "LPRecord"
                               
let whyml_plpattern plpat = whyml_plpattern_r (unloc plpat)

let whyml_ptyannot_r = function
  | TVIunamed ptys -> whyml_pty_list ptys " "
  | TVInamed psy_pty_s -> String.concat " " (List.map (fun psy_pty -> let (psy, pty) = psy_pty in whyml_psymbol psy ^ " " ^ whyml_pty pty) psy_pty_s)
                          
let whyml_ptyannot ptya = whyml_ptyannot_r (unloc ptya)
                                             
let rec whyml_pexpr_r = function
  | PEcast _ -> "cast"
  | PEint  (zi) -> to_string zi
  | PEdecimal _ -> "decimal literal" 
  | PEident   (pqsy, _) -> whyml_pqsymbol pqsy
  | PEapp     (pe, pes) -> whyml_pexpr pe ^ " " ^ whyml_pexpr_list pes " "
  | PElet     (plpat, pewty, pe) -> "let " ^ whyml_plpattern plpat ^ " = " ^ whyml_pexpr_wty pewty ^ " in " ^ whyml_pexpr pe
  | PEtuple   (pes) -> whyml_pexpr_list pes ", "
  | PEif      (pe, pet, pef) -> "if " ^ whyml_pexpr pe ^ " then " ^ whyml_pexpr pet ^ " else " ^ whyml_pexpr pef
  | PEforall  _ -> "forall"
  | PEexists  _ -> "exists"
  | PElambda  (ptybs, pe) -> "fun " ^ whyml_ptybindings ptybs " " ^ " -> " ^ whyml_pexpr pe
  | PErecord  (peo, rfields) -> whyml_record_literal peo rfields
  | PEproj    (pe, pqsy) -> whyml_pexpr pe ^ "." ^ whyml_pqsymbol pqsy
  | PEproji   (pe, i) -> if i = 0 then "let (a,b) = " ^ whyml_pexpr pe ^ " in a"
                         else if i = 1 then "let (a,b) = " ^ whyml_pexpr pe ^ " in b"
                         else "tuple projection not supported"
  | PEscope   _ -> "scope selection"

and whyml_pexpr_list pes sep = String.concat sep (List.map whyml_pexpr pes)

and whyml_pexpr_wty pewty =
  let (pe, ptyo) = pewty in
  match ptyo with
  | None -> whyml_pexpr pe
  | Some pty -> whyml_pexpr pe ^ " : " ^ whyml_pty pty

and whyml_record_literal peo rfields =
  match peo with
  | None -> "{ " ^ whyml_rfields rfields "; " ^ " }"
  | Some pe -> whyml_pexpr pe ^ "with { " ^ whyml_rfields rfields "; " ^ " }"

and whyml_rfield rfield =
  match rfield.rf_tvi with
  | None -> whyml_pqsymbol rfield.rf_name ^ " = " ^ whyml_pexpr rfield.rf_value
  | Some ptya -> whyml_pqsymbol rfield.rf_name ^ " : " ^ whyml_ptyannot ptya ^ " = " ^ whyml_pexpr rfield.rf_value

and whyml_rfields rfields sep = String.concat sep (List.map whyml_rfield rfields)
                               
and whyml_pexpr pe = "(" ^ whyml_pexpr_r (unloc pe) ^ ")"
                               
(* ================================================================== *)
(** Extraction of EasyCrypt abstract operator *)
let whyml_abstr_poperator pop pty =
  "val function " ^ whyml_psymbol pop.po_name ^ " : " ^ whyml_pty pty

(* ================================================================== *)
(** Extraction of EasyCrypt concrete operator *)
let whyml_concr_poperator_type pop pty pe =
  if pop.po_args = [] then
    "let " ^ whyml_psymbol pop.po_name ^ " : " ^ whyml_pty pty ^ " = " ^ whyml_pexpr pe
  else
    "let " ^ whyml_psymbol pop.po_name ^ " " ^ whyml_ptybindings pop.po_args " " ^ " : " ^ whyml_pty pty ^ " = " ^ whyml_pexpr pe

let whyml_concr_poperator_no_type pop pe =
  if pop.po_args = [] then
    "let " ^ whyml_psymbol pop.po_name ^ " = " ^ whyml_pexpr pe
  else
    "let " ^ whyml_psymbol pop.po_name ^ " " ^ whyml_ptybindings pop.po_args " " ^ " = " ^ whyml_pexpr pe
  
let whyml_concr_poperator pop pty pe =
  match unloc pty with
  | PTunivar -> whyml_concr_poperator_no_type pop pe
  | _ -> whyml_concr_poperator_type pop pty pe

(* ================================================================== *)
(** Extraction of EasyCrypt pattern matching operator *)
let whyml_pop_pattern = function
  | PPApp ((pqsy,_), osys) -> whyml_pqsymbol pqsy ^ " " ^ whyml_osymbol_list osys " "

let whyml_matches popbs = String.concat "," (List.map (fun p -> whyml_psymbol p.pop_name) ((List.hd popbs).pop_patterns))

let whyml_pop_pattern_list popps = String.concat ", " (List.map (fun popp -> whyml_pop_pattern popp.pop_pattern) popps)

let whyml_pop_branches popbs = String.concat "\n" (List.map (fun popb -> "| " ^ whyml_pop_pattern_list popb.pop_patterns ^ " -> " ^ whyml_pexpr popb.pop_body) popbs)

let whyml_case_poperator_type pop pty brs =
  let ms = whyml_matches brs in
  
  if pop.po_args = [] then
    "let rec " ^ whyml_psymbol pop.po_name ^ " : " ^ whyml_pty pty ^ " = match " ^ ms ^ " with\n" ^ whyml_pop_branches brs ^ "\nend"
  else
    "let rec " ^ whyml_psymbol pop.po_name ^ " " ^ whyml_ptybindings pop.po_args " " ^ " : " ^ whyml_pty pty ^ " = match " ^ ms ^ " with\n" ^ whyml_pop_branches brs ^ "\nend"

let whyml_case_poperator_no_type pop brs =
  let ms = whyml_matches brs in
  
  if pop.po_args = [] then
    "let rec " ^ whyml_psymbol pop.po_name ^ " = match " ^ ms ^ " with\n" ^ whyml_pop_branches brs ^ "\nend"
  else
    "let rec " ^ whyml_psymbol pop.po_name ^ " " ^ whyml_ptybindings pop.po_args " " ^ " = match " ^ ms ^ " with\n" ^ whyml_pop_branches brs ^ "\nend"

let whyml_case_poperator pop pty brs =
  match unloc pty with
  | PTunivar -> whyml_case_poperator_no_type pop brs
  | _ -> whyml_case_poperator_type pop pty brs

(* ================================================================== *)
(** Extraction of EasyCrypt operator *)
let whyml_poperator pop =
  match pop.po_def with
  | PO_abstr pty -> whyml_abstr_poperator pop pty
  | PO_concr (pty, pe) -> whyml_concr_poperator pop pty pe
  | PO_case (pty, brs) -> whyml_case_poperator pop pty brs
  | PO_reft _ -> "reft operator"

(* ================================================================== *)
(** Extraction of EasyCrypt abbrevs *)
let whyml_pabbrev pabbrev =
  let (pty,pe) = pabbrev.ab_def in

  if unloc pty = PTunivar then
    "let " ^ whyml_psymbol pabbrev.ab_name ^ " " ^ whyml_ptybindings pabbrev.ab_args " " ^ " = " ^ whyml_pexpr pe
  else
    "let " ^ whyml_psymbol pabbrev.ab_name ^ " " ^ whyml_ptybindings pabbrev.ab_args " " ^ " : " ^ whyml_pty pty ^ " = " ^ whyml_pexpr pe
                         
(* ================================================================== *)
(** Extraction of EasyCrypt global action (= statement) *)
let whyml_global_action = function
  | Gtype ptydecls -> whyml_ptydecl_list ptydecls "\n" ^ "\n\n"
  | Goperator pop -> whyml_poperator pop ^ "\n\n"
  | Gabbrev pabbrev -> whyml_pabbrev pabbrev ^ "\n\n"
  (*| GthOpen (il, b, psy) -> "scope " ^ whyml_psymbol psy ^ "\n\n"
  | GthClose (thcl, psy) -> "end\n\n"*)
  | _ -> ""
   
let whyml_global g = whyml_global_action (unloc g.gl_action)

(* ================================================================== *)
(** Extraction of EasyCrypt script *)
let imports_mapping = [
    ("Int", "int.Int") ;
    ("Real", "real.Real") ;
  ]
                   
let whyml_imports mod_name imports =
  if mod_name = "Logic" then
    "use Pervasive\n" ^ String.concat "\n" (List.map (fun imp -> "use " ^ try assoc imp imports_mapping with | _ -> imp) imports)
  else 
    "use Pervasive\nuse Logic\n" ^ String.concat "\n" (List.map (fun imp -> "use " ^ try assoc imp imports_mapping with | _ -> imp) imports)
               
let rec whyml_global_list mod_name imports gs sep =
  "module " ^ mod_name ^ "\n\n" ^ whyml_imports mod_name imports ^ "\n\n"^
    String.concat sep (List.map whyml_global gs) ^ "end\n"
