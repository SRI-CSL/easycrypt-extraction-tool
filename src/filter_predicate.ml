open List

open Core
open EcParsetree
open EcLocation

(* ================================================================== *)
(** Extraction of EasyCrypt expressions *)
let rec filter_pexpr_r = function
  | PEcast _ -> false
  | PEint  _ -> false
  | PEdecimal _ -> false
  | PEident   _ -> false
  | PEapp     (pe, pes) -> filter_pexpr pe || filter_pexpr_list pes
  | PElet     (_, _, pe) -> filter_pexpr pe
  | PEtuple   (pes) -> filter_pexpr_list pes
  | PEif      (pe, pet, pef) -> filter_pexpr pe || filter_pexpr pet || filter_pexpr pef
  | PEforall  _ -> true
  | PEexists  _ -> true
  | PElambda  (_, pe) -> filter_pexpr pe
  | PErecord  _ -> false
  | PEproj    (pe, _) -> filter_pexpr pe
  | PEproji   (pe, _) -> filter_pexpr pe
  | PEscope   (_, pe) -> filter_pexpr pe

and filter_pexpr_list pes = fold_right (fun pe b -> filter_pexpr pe || b) pes false
                               
and filter_pexpr pe = filter_pexpr_r (unloc pe)

(* ================================================================== *)
(** Extraction of EasyCrypt operator *)
let filter_poperator pop =
  match pop.po_def with
  | PO_abstr _ -> false
  | PO_concr (_, pe) -> filter_pexpr pe
  | PO_case _ -> false
  | PO_reft _ -> false

(* ================================================================== *)
(** Extraction of EasyCrypt abbrevs *)
let filter_pabbrev pabbrev =
  let (_,pe) = pabbrev.ab_def in
  filter_pexpr pe
                       
(* ================================================================== *)
(** Extraction of EasyCrypt global action (= statement) *)
let filter_global_action = function
  | Goperator pop -> filter_poperator pop
  | Gabbrev pabbrev -> filter_pabbrev pabbrev
  | _ -> false
   
let filter_global g = filter_global_action (unloc g.gl_action)

(* ================================================================== *)
(** Extraction of EasyCrypt script *)
let rec filter_global_list gs =
  filter (fun g -> not (filter_global g)) gs
