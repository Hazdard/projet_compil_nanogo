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

let new_struct str field size =
  { s_name = str; s_fields = field; s_size = size }

module Env_struct = struct
  module M = Map.Make (String)

  type t = structure M.t

  let empty = M.empty
  let find = M.find
  let add env str = M.add str.s_name str env
  let all_vars = ref []

  let var str field size env =
    let v = new_struct str field size in
    all_vars := v :: !all_vars;
    (add env v, v)

  (* TODO type () et vecteur de types *)
end

(* TODO environnement pour les fonctions *)

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
  | _ -> false
(* TODO autres types *)

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
      if v.v_name <> "_" && (* TODO used *) true then
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
      (TEprint (List.map (fun x -> fst (expr env x)) el), tvoid, false)
  | PEcall ({ id = "new" }, [ { pexpr_desc = PEident { id } } ]) ->
      let ty =
        match id with
        | "int" -> Tint
        | "bool" -> Tbool
        | "string" -> Tstring
        | s -> (
            try Env_struct.find s
            with Not_found -> error loc ("no such type " ^ id))
      in
      (TEnew ty, Tptr ty, false)
  | PEcall ({ id = "new" }, _) -> error loc "new expects a type"
  | PEcall (id, el) -> (* TODO *) assert false
  | PEfor (e, b) -> (* TODO *) assert false
  | PEif (e1, e2, e3) -> (* TODO *) assert false
  | PEnil -> (* TODO *) assert false
  | PEident { id } -> (
      (* TODO *)
      try
        let v = Env_var.find id env in
        (TEident v, v.v_typ, false)
      with Not_found -> error loc ("unbound variable " ^ id))
  | PEdot (e, id) -> (* TODO *) assert false
  | PEassign (lvl, el) -> (* TODO *) (TEassign ([], []), tvoid, false)
  | PEreturn el -> (* TODO *) (TEreturn [], tvoid, true)
  | PEblock el -> (* TODO *) (TEblock [], tvoid, false)
  | PEincdec (e, op) -> (* TODO *) assert false
  | PEvars _ -> (* TODO *) assert false

let found_main = ref true (* A CHANGER *)

(* 1. declare structures *)
let phase1 = function
  | PDstruct { ps_name = { id; loc } } -> (* TODO *) ()
  | PDfunction _ -> ()

let sizeof = function
  | Tint | Tbool | Tstring | Tptr _ -> 8
  | _ -> (* TODO *) assert false

(* 2. declare functions and type fields *)
let phase2 = function
  | PDfunction { pf_name = { id; loc }; pf_params = pl; pf_typ = tyl } ->
      (* TODO *) ()
  | PDstruct { ps_name = { id }; ps_fields = fl } -> (* TODO *) ()

(* 3. type check function bodies *)
let decl = function
  | PDfunction { pf_name = { id; loc }; pf_body = e; pf_typ = tyl } ->
      (* TODO check name and type *)
      let f = { fn_name = id; fn_params = []; fn_typ = [] } in
      let e, rt = expr Env_var.empty e in
      TDfunction (f, e)
  | PDstruct { ps_name = { id } } ->
      (* TODO *)
      let s = { s_name = id; s_fields = Hashtbl.create 5; s_size = 0 } in
      TDstruct s

let file ~debug:b (imp, dl) =
  debug := b;
  (* fmt_imported := imp; *)
  List.iter phase1 dl;
  List.iter phase2 dl;
  if not !found_main then error dummy_loc "missing method main";
  let dl = List.map decl dl in
  Env_var.check_unused ();
  (* TODO variables non utilisees *)
  if imp && not !fmt_used then error dummy_loc "fmt imported but not used";
  dl
