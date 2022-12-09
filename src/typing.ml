open Format
open Lib
open Ast
open Tast

let debug = ref false
let dummy_loc = (Lexing.dummy_pos, Lexing.dummy_pos)

exception Error of Ast.location * string
exception Anomaly of string

let error loc e = raise (Error (loc, e))

(* TOFINISH environnement pour les types structure *)

module Env_struct = struct
  let struct_tabl = Hashtbl.create 17
  let find = Hashtbl.find struct_tabl
  let add str = Hashtbl.add struct_tabl str.s_name str

  let new_struct str field size =
    { s_name = str; s_fields = field; s_size = size }

  let struct_create str field size =
    let champs = Hashtbl.create 2 in
    let rec aux l =
      match l with
      | [] -> ()
      | (nom, field_var) :: q -> Hashtbl.add champs nom field_var
    in
    aux field;
    let s = new_struct str champs size in
    add s;
    ()

  let empty str = struct_create str [] 0
  let exists str = Hashtbl.mem struct_tabl str
end

module Env_fnct = struct
  let fnct_tbl = Hashtbl.create 17
  let find = Hashtbl.find fnct_tbl
  let add f = Hashtbl.add fnct_tbl f.fn_name f
  let new_fun f params ty_l = { fn_name = f; fn_params = params; fn_typ = ty_l }

  let fun_create f params ty_l =
    let s = new_fun f params ty_l in
    add s;
    ()

  let exists f = Hashtbl.mem fnct_tbl f
end

let rec type_type = function
  | PTident { id = "int" } -> Tint
  | PTident { id = "bool" } -> Tbool
  | PTident { id = "string" } -> Tstring
  | PTptr ty -> Tptr (type_type ty)
  | _ -> error dummy_loc "unknown struct "
(* TODO type structure *)

let rec eq_type ty1 ty2 =
  match (ty1, ty2) with
  | Tint, Tint | Tbool, Tbool | Tstring, Tstring -> true
  | Tstruct s1, Tstruct s2 -> s1 == s2
  | Tptr ty1, Tptr ty2 -> eq_type ty1 ty2
  | Twild, _ -> true
  | _, Twild -> true
  | Tmany el1, Tmany el2 ->
      let rec aux l1 l2 =
        match (l1, l2) with
        | [], [] -> true
        | [], a :: q -> false
        | a :: q, [] -> false
        | a :: q, b :: v -> eq_type a b
      in
      aux el1 el2
  | _, _ -> false

let fmt_used = ref false
let fmt_imported = ref false
let evar v = { expr_desc = TEident v; expr_typ = v.v_typ }

let new_var =
  let id = ref 0 in
  fun x loc ?(used = false) ty ->
    incr id;
    {
      v_name = x;
      v_id = !id;
      v_loc = loc;
      v_typ = ty;
      v_used = used;
      v_addr = 0;
      v_depth = 0;
    }

module Env_var = struct
  module M = Map.Make (String)

  type t = var M.t

  let empty = M.empty
  let find = M.find
  let add env v = M.add v.v_name v env
  let all_vars = ref []

  let check_unused () =
    let check v =
      if v.v_name <> "_" && (not v.v_used) then
        error v.v_loc "unused variable"
    in
    List.iter check !all_vars

  let var x loc ?used ty env =
    let v = new_var x loc ?used ty in
    all_vars := v :: !all_vars;
    (add env v, v)

  (* TODO type () et vecteur de types *)
end

let tvoid = Tmany []
let make d ty = { expr_desc = d; expr_typ = ty }
let stmt d = make d tvoid

let rec is_l_value e =
  match e.expr_desc with
  | TEident _ -> true
  | TEdot (e2, _) -> is_l_value e2
  | TEunop (Ustar, e2) -> e2.expr_desc <> TEnil
  | _ -> false

let list_to_many = function [ x ] -> x | _ as a -> Tmany a
let ret_type = ref tvoid (*TODO INITIALISER EN PHASE 3*)

let rec expr env e =
  let e, ty, rt = expr_desc env e.pexpr_loc e.pexpr_desc in
  ({ expr_desc = e; expr_typ = ty }, rt)

and expr_desc env loc = function
  | PEskip -> (TEskip, tvoid, false)
  | PEconstant c ->
      let ty =
        match c with Cbool _ -> Tbool | Cint _ -> Tint | Cstring _ -> Tstring
      in
      (TEconstant c, ty, false)
  | PEbinop (((Beq | Bne) as op), e1, e2) ->
      let desc1, _ = expr env e1 in
      let desc2, _ = expr env e2 in
      if not (desc1.expr_desc != TEnil && desc2.expr_desc != TEnil) then
        error loc "L'égualité ne peut être testée sur nil"
      else if not (desc1.expr_typ = desc2.expr_typ) then
        error loc "Les deux membres de l'égalité doivent avoir le même type"
      else (TEbinop (op, desc1, desc2), Tbool, false)
  | PEbinop (op, e1, e2) ->
      let desc1, _ = expr env e1 in
      let desc2, _ = expr env e2 in
      let ty_sortie, ty_entree =
        match op with
        | Blt | Ble | Bgt | Bge -> (Tbool, Tint)
        | Badd | Bsub | Bmul | Bdiv | Bmod -> (Tint, Tint)
        | Band | Bor -> (Tbool, Tbool)
        | _ -> (Twild, Twild)
        (*Cas jamais utile*)
      in
      if desc1.expr_typ = ty_entree && desc2.expr_typ = ty_entree then
        (TEbinop (op, desc1, desc2), ty_sortie, false)
      else error loc "Mauvais type pour l'operation binaire"
  | PEunop (Uamp, e1) ->
      let desc1, _ = expr env e1 in
      if is_l_value desc1 then (TEunop (Uamp, desc1), Tptr desc1.expr_typ, false)
      else error loc "& ne s'applique qu'à une l-value"
  | PEunop (((Uneg | Unot | Ustar) as op), e1) ->
      let desc1, _ = expr env e1 in
      let ty1 = desc1.expr_typ in
      let ty_sortie, ty_entree =
        match op with
        | Uneg -> (Tint, Tint)
        | Unot -> (Tbool, Tbool)
        | Ustar -> (Tptr ty1, ty1)
        | _ -> (Twild, Twild)
        (*Cas jamais utile*)
      in
      if op = Ustar then
        if desc1.expr_desc = TEnil then
          error loc "Impossible de déréférencer un pointeur vide"
        else (TEunop (op, desc1), ty_sortie, false)
      else (TEunop (op, desc1), ty_sortie, false)
  | PEcall ({ id = "fmt.Print" }, el) ->
      if not !fmt_imported then error loc "fmt used but not imported";
      fmt_used := true;
      let l = List.map (fun x -> fst (expr env x)) el in
      (TEprint l, tvoid, false)
  | PEcall ({ id = "new" }, [ { pexpr_desc = PEident { id } } ]) ->
      let ty =
        match id with
        | "int" -> Tint
        | "bool" -> Tbool
        | "string" -> Tstring
        | s -> (
            try Tstruct (Env_struct.find s)
            with Not_found -> error loc ("Le type suivant est inconnu " ^ id))
      in
      (TEnew ty, Tptr ty, false)
  | PEcall ({ id = "new" }, _) -> error loc "new attends un type en entrée"
  | PEcall (id, el) -> (
      try
        let f = Env_fnct.find id.id in
        let el_typed = List.map (fun x -> fst (expr env x)) el in
        let el_typed_ty = List.map (fun x -> x.expr_typ) el_typed in
        let f_typed_ty = List.map (fun x -> x.v_typ) f.fn_params in
        if eq_type (Tmany el_typed_ty) (Tmany f_typed_ty) then
          (TEcall (f, el_typed), Tmany f_typed_ty, false)
        else error loc "Argument incorrect"
      with Not_found -> error loc "Fonction non définie")
  | PEfor (e, b) ->
      let e_tast, _ = expr env e in
      let b_tast, ret = expr env b in
      if not (e_tast.expr_typ = Tbool) then
        error e.pexpr_loc "Cette expression doit être un booléen"
      else (TEfor (e_tast, b_tast), tvoid, ret)
  | PEif (e1, e2, e3) ->
      let e1_tast, _ = expr env e1 in
      let e2_tast, ret2 = expr env e2 in
      let e3_tast, ret3 = expr env e3 in
      if not (e1_tast.expr_typ = Tbool) then
        error e1.pexpr_loc "Cette expression doit être un booléen"
      else (TEif (e1_tast, e2_tast, e3_tast), tvoid, ret2 && ret3)
  | PEnil -> (TEnil, Tptr Twild, false)
  | PEident { id } -> (
      if id = "_" then
        error loc " _ ne peut pas être utilisé comme une variable";
      try
        let v = Env_var.find id env in
        v.v_used <- true;
        (TEident v, v.v_typ, false)
      with Not_found -> error loc ("unbound variable " ^ id))
  | PEdot (e, id) -> (
      let e_tast, ret = expr env e in
      let s =
        match e_tast.expr_typ with
        | Tstruct str | Tptr (Tstruct str) -> str
        | _ -> error loc "Le type utilisé n'a pas de champs"
      in
      try
        let e_field = Hashtbl.find (Env_struct.find s.s_name).s_fields id.id in
        let ty = e_field.f_typ in
        (TEdot (e_tast, e_field), ty, false)
      with Not_found ->
        error loc ("Le champ suivant n'est pas défini " ^ id.id))
  | PEassign (lvl, el) ->
      let el_typed = List.map (fun x -> fst (expr env x)) el in
      let rec aux lv expr_l =
        match (lv, expr_l) with
        | [], [] -> ([], [])
        | { pexpr_desc = PEident { id = "_" } } :: q, _ :: r -> aux q r
        | pe :: q, exp1 :: r ->
            let pe_exp = fst (expr env pe) in
            if is_l_value pe_exp then
              if eq_type pe_exp.expr_typ exp1.expr_typ then
                let l1, l2 = aux q r in
                (pe_exp :: l1, exp1 :: l2)
              else error loc "Erreur de typage dans l'assignation"
            else error loc "Le membre de gauche doit être une l-value"
        | _ -> error loc "Mauvaise arité du membre de droite"
      in
      let l1, l2 = aux lvl el_typed in
      (TEassign (l1, l2), tvoid, false)
  | PEreturn el ->
      if
        !ret_type
        <> list_to_many (List.map (fun x -> (fst (expr env x)).expr_typ) el)
      then error loc "Type du return différent de celui de la fonction"
      else (TEreturn (List.map (fun x -> fst (expr env x)) el), tvoid, true)
  | PEblock el -> (
      match el with
      | [] -> (TEblock [], tvoid, false)
      | a :: q ->
          let a_typed, reta = expr env a in
          let new_env =
            match a_typed.expr_desc with
            | TEvars (lvl, el) -> List.fold_left Env_var.add env lvl
            | _ -> env
          in
          let rest =
            match expr new_env { pexpr_desc = PEblock q; pexpr_loc = loc } with
            (* loc a mettre au premier elem de q mais jai la flemme *)
            | { expr_desc = TEblock el }, ret -> (el, ret)
            | _ -> error loc "Ce cas n'arrive jamais !"
          in
          (TEblock (a_typed :: fst rest), tvoid, snd rest || reta))
  | PEincdec (e, op) ->
      let ne, _ = expr env e in
      if ne.expr_typ <> Tint then
        error loc
          "L'incrémentation/décrémentation doit se faire sur un type int";
      if not (is_l_value ne) then
        error e.pexpr_loc
          "L'incrémentation/décrémentation doit se faire sur une l-value";
      (TEincdec (ne, op), tvoid, false)
  | PEvars (ids, None, pexprs) ->
      let el = List.map (fun x -> fst (expr env x)) pexprs in
      let rec aux id_l exp_l env =
        match (id_l, exp_l) with
        | [], [] -> ([], [])
        | { id = "_" } :: q, _ :: r -> aux q r env
        | id :: q, exp :: r -> (
            try
              let _ = Env_var.find id.id env in
              error loc "Variable déjà définie"
            with Not_found ->
              let rec1, rec2 = aux q r env in
              (snd (Env_var.var id.id loc exp.expr_typ env) :: rec1, exp :: rec2)
            )
        | _ -> error loc "Mauvaise arité du membre de droite"
      in
      let vars, expr2 = aux ids el env in
      (TEvars (vars, expr2), tvoid, false)
  | PEvars (ids, Some pty, pexprs) ->
      let pty_typed = type_type pty in
      let el =
        if List.length pexprs == 0 then
          List.map (fun x -> { expr_desc = TEskip; expr_typ = pty_typed }) ids
        else List.map (fun x -> fst (expr env x)) pexprs
      in
      let rec aux id_l exp_l =
        match (id_l, exp_l) with
        | [], [] -> ([], [])
        | { id = "_" } :: q, _ :: r -> aux q r
        | id :: q, exp :: r ->
            if eq_type pty_typed exp.expr_typ then
              try
                let _ = Env_var.find id.id env in
                error loc "Variable déjà utilisée"
              with Not_found ->
                let rec1, rec2 = aux q r in
                ( snd (Env_var.var id.id loc exp.expr_typ env) :: rec1,
                  exp :: rec2 )
            else error loc "Erreur de typage dans la déclaration"
        | _ -> error loc "Mauvaise arité du membre de droite"
      in
      let vars, expr2 = aux ids el in
      let is_def = if List.length pexprs == 0 then false else true in
      if is_def then (TEvars (vars, expr2), tvoid, false)
      else (TEvars (vars, []), tvoid, false)

let found_main = ref false

(* 1. declare structures *)
let phase1 = function
  | PDstruct { ps_name = { id; loc } } ->
      if Env_struct.exists id then
        error loc ("La structure" ^ id ^ "est déjà définie")
      else Env_struct.empty id
  | PDfunction _ -> ()

let rec sizeof = function
  | Tint | Tbool | Tstring | Tptr _ -> 8
  | Tstruct s -> Hashtbl.fold (fun _ b c -> c + sizeof b.f_typ) s.s_fields 0
  | Tmany l -> List.fold_left (fun i x -> i + sizeof x) 0 l
  | _ -> assert false

(* 2. declare functions and type fields *)

let rec are_distinct l =
  match l with
  | [] -> true
  | a :: q ->
      let rec aux q =
        match q with [] -> true | b :: r -> if a == b then false else aux r
      in
      aux q

let rec is_well_formed = function
  | PTident { id = "int" } | PTident { id = "bool" } | PTident { id = "string" }
    ->
      true
  | PTptr ty -> is_well_formed ty
  | PTident { id = s } -> Env_struct.exists s

let phase2 = function
  | PDfunction { pf_name = { id; loc }; pf_params = pl; pf_typ = tyl } ->
      if id = "main" then (
        if pl <> [] then error loc "La fonction main ne prend pas d'arguments";
        if tyl <> [] then error loc "La fonction main n'a pas de retour";
        found_main := true);
      if
        List.for_all is_well_formed (List.map snd pl)
        && List.for_all is_well_formed tyl
      then
        if Env_fnct.exists id then
          error loc ("La fonction " ^ id ^ " est déjà définie")
        else
          Env_fnct.fun_create id
            (List.map
               (fun (a, b) ->
                 {
                   v_name = a.id;
                   v_loc = a.loc;
                   v_typ = type_type b;
                   v_id = 0;
                   v_depth = 0;
                   v_used = false;
                   v_addr = 0;
                 })
               pl)
            (List.map (fun x -> type_type x) tyl)
      else error loc ("La fonction " ^ id ^ " est mal formée")
  | PDstruct ({ ps_name = { id; loc }; ps_fields = fl } as s) ->
      if not (List.for_all is_well_formed (List.map snd fl)) then
        error loc ("Types mal formés dans la structure :" ^ id);
      if not (are_distinct (List.map (fun (a, b) -> a.id) fl)) then
        error loc
          ("Attributs présents plusieurs fois dans la structure " ^ s.ps_name.id);
      Env_struct.struct_create id
        (List.map
           (fun (a, b) ->
             (a.id, { f_name = a.id; f_typ = type_type b; f_ofs = 0 }))
           fl)
        (sizeof (Tmany (List.map (fun (a, b) -> type_type b) fl)))

(* 3. type check function bodies *)

let is_recursive name =
  let s = Env_struct.find name in
  let recurse = ref false in
  let rec aux f =
    match f.f_typ with
    | Tstruct s' ->
        if s'.s_name = name then recurse := true
        else Hashtbl.iter (fun _ x -> aux x) s'.s_fields
    | _ -> ()
  in
  Hashtbl.iter (fun _ x -> aux x) s.s_fields;
  !recurse

let decl = function
  | PDfunction { pf_name = { id; loc }; pf_body = e } ->
      (* TODO check name and type *)
      let f = Env_fnct.find id in
      let env = Env_var.empty in
      let rec aux l envir =
        match l with [] -> envir | a :: q -> aux q (Env_var.add envir a)
      in
      let env_init = aux f.fn_params env in
      ret_type := list_to_many f.fn_typ;
      let e, rt = expr env_init e in
      if (not rt) && List.length f.fn_typ > 0 then
        error loc "Pas de return dans le bloc"
      else TDfunction (f, e)
  | PDstruct { ps_name = { id; loc } } ->
      if is_recursive id then error loc ("La structure " ^ id ^ " est récursive")
      else
        let s = Env_struct.find id in
        TDstruct s

let file ~debug:b (imp, dl) =
  debug := b;
  fmt_imported := imp;
  List.iter phase1 dl;
  List.iter phase2 dl;
  if not !found_main then error dummy_loc "missing method main";
  let dl = List.map decl dl in
  Env_var.check_unused ();
  if imp && not !fmt_used then error dummy_loc "fmt imported but not used";
  dl
