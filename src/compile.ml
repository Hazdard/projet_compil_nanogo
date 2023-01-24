(* étiquettes
     F_function      entrée fonction
     E_function      sortie fonction
     L_xxx           sauts
     S_xxx           chaîne

   expression calculée avec la pile si besoin, résultat final dans %rdi

   fonction : arguments sur la pile, résultat dans %rax ou sur la pile

            res k
            ...
            res 1
            arg n
            ...
            arg 1
            adr. retour
   rbp ---> ancien rbp
            ...
            var locales
            ...
            calculs
   rsp ---> ...
*)

open Format
open Ast
open Tast
open X86_64
open Typing

exception Anomaly of string

let debug = ref false
let strings = Hashtbl.create 32

let alloc_string =
  let r = ref 0 in
  fun s ->
    incr r;
    let l = "S_" ^ string_of_int !r in
    Hashtbl.add strings l s;
    l

let malloc n = movq (imm n) (reg rdi) ++ call "malloc"
let allocz n = movq (imm n) (reg rdi) ++ call "allocz"
let sizeof = Typing.sizeof

let new_label =
  let r = ref 0 in
  fun () ->
    incr r;
    "L_" ^ string_of_int !r

type env = { exit_label : string; mutable nb_locals : int (* maximum *) }

let empty_env = { exit_label = ""; nb_locals = 0 }
let fun_env f = { exit_label = "E_" ^ f.fn_name; nb_locals = 0 }
let mk_bool d = { expr_desc = d; expr_typ = Tbool }

let push_ret arg_s ret_s =
  let c = ref nop in
  for i = 1 to ret_s / 8 do
    c := !c ++ pushq (ind rsp ~ofs:(-8 - arg_s))
  done;
  !c

(* f reçoit le label correspondant à ``renvoyer vrai'' *)
let compile_bool f =
  let l_true = new_label () and l_end = new_label () in
  f l_true
  ++ movq (imm 0) (reg rdi)
  ++ jmp l_end ++ label l_true
  ++ movq (imm 1) (reg rdi)
  ++ label l_end

let rec expr env e =
  match e.expr_desc with
  | TEskip -> nop
  | TEconstant (Cbool true) -> movq (imm 1) (reg rdi)
  | TEconstant (Cbool false) -> movq (imm 0) (reg rdi)
  | TEconstant (Cint x) -> movq (imm64 x) (reg rdi)
  | TEnil -> xorq (reg rdi) (reg rdi)
  | TEconstant (Cstring s) ->
      let l = alloc_string s in
      movq (ilab l) (reg rdi)
  | TEbinop (Band, e1, e2) ->
      let l_false = new_label () in
      let l_end = new_label () in
      expr env e1
      ++ testq (reg rdi) (reg rdi)
      ++ jz l_false ++ expr env e2
      ++ testq (reg rdi) (reg rdi)
      ++ jz l_false
      ++ movq (imm 1) (reg rdi)
      ++ jmp l_end ++ label l_false
      ++ movq (imm 0) (reg rdi)
      ++ label l_end
  | TEbinop (Bor, e1, e2) ->
      let l_true = new_label () in
      let l_end = new_label () in
      expr env e1
      ++ testq (reg rdi) (reg rdi)
      ++ jnz l_true ++ expr env e2
      ++ testq (reg rdi) (reg rdi)
      ++ jnz l_true
      ++ movq (imm 0) (reg rdi)
      ++ jmp l_end ++ label l_true
      ++ movq (imm 1) (reg rdi)
      ++ label l_end
  | TEbinop ((Blt | Ble | Bgt | Bge), e1, e2) ->
      let l_true = new_label () in
      let l_end = new_label () in
      expr env e1
      ++ movq (reg rdi) (reg rsi)
      ++ expr env e2
      ++ cmpq (reg rsi) (reg rdi)
      ++ (match e.expr_desc with
         | TEbinop (Blt, _, _) -> jl l_true
         | TEbinop (Ble, _, _) -> jle l_true
         | TEbinop (Bgt, _, _) -> jg l_true
         | TEbinop (Bge, _, _) -> jge l_true
         | _ -> raise (Error (dummy_loc, "This can't happen cmp_binop1")))
      ++ movq (imm 0) (reg rdi)
      ++ jmp l_end ++ label l_true
      ++ movq (imm 1) (reg rdi)
      ++ label l_end
  | TEbinop (((Badd | Bsub | Bmul | Bdiv | Bmod) as op), e1, e2) -> (
      expr env e1
      ++ pushq (reg rdi)
      ++ expr env e2 ++ popq rax
      ++
      match op with
      | Badd -> addq (reg rax) (reg rdi)
      | Bsub -> subq (reg rdi) (reg rax) ++ movq (reg rax) (reg rdi)
      | Bmul -> imulq (reg rax) (reg rdi)
      | Bdiv -> cqto ++ idivq (reg rdi) ++ movq (reg rax) (reg rdi)
      | Bmod -> cqto ++ idivq (reg rdi) ++ movq (reg rdx) (reg rdi)
      | _ -> raise (Error (dummy_loc, "This can't happen cmp_binop2")))
  | TEbinop (((Beq | Bne) as op), e1, e2) ->
      let l_true = new_label () in
      let l_end = new_label () in
      expr env e1
      ++ movq (reg rdi) (reg rsi)
      ++ expr env e2
      ++ cmpq (reg rdi) (reg rsi)
      ++ (match op with
         | Beq -> je l_true
         | Bne -> jne l_true
         | _ -> raise (Error (dummy_loc, "This can't happen cmp_binop3")))
      ++ movq (imm 0) (reg rdi)
      ++ jmp l_end ++ label l_true
      ++ movq (imm 1) (reg rdi)
      ++ label l_end
  | TEunop (Uneg, e1) -> expr env e1 ++ negq (reg rdi)
  | TEunop (Unot, e1) ->
      expr env e1 ++ cmpq (imm 0) (reg rdi) ++ compile_bool jz
  | TEunop (Uamp, e1) -> (* TODO code pour & *) assert false
  | TEunop (Ustar, e1) -> expr env e1 ++ movq (ind rdi) (reg rdi)
  | TEprint el ->
      let rec aux l =
        match l with
        | [] -> nop
        | e :: t ->
            expr env e
            ++ (match e.expr_typ with
               | Tbool -> call "print_bool"
               | Tstring -> call "print_string"
               | Tstruct s | Tptr (Tstruct s) ->
                   call "print_space"
                   (* Je n'ai pas réussi à implémenter les structures*)
               | Tint | Tptr _ -> call "print_int"
               | _ -> raise (Error (dummy_loc, "This can't happen cmp_print")))
            ++ (if t <> [] then ( ++ ) (call "print_space") else fun x -> x)
                 (aux t)
      in
      aux el ++ call "print_space"
  | TEident x -> movq (ind ~ofs:x.v_addr rbp) (reg rdi)
  | TEassign ([ lv ], [ e1 ]) ->
      let lv_addr =
        (* met l'addresse de lv dans %rdi *)
        match lv.expr_desc with
        | TEident x -> movq (reg rbp) (reg rdi) ++ addq (imm x.v_addr) (reg rdi)
        | TEunop (Ustar, e) -> expr env e
        | TEdot (e, x) -> expr env e ++ addq (imm x.f_ofs) (reg rdi)
        | _ -> raise (Error (dummy_loc, "This can't happen cmp_assign"))
        (* Ce cas n'arrive jamais car lv est une l-value *)
      in
      lv_addr
      ++ pushq (reg rdi)
      ++ expr env e ++ popq rsi
      ++ movq (reg rdi) (ind rsi)
  | TEassign (vl, el) ->
      (* Pareil que le cas précédent mais on l'applique récursivement à toute une liste *)
      let rec aux a b =
        match (a, b) with
        | x :: r, y :: q ->
            expr env { expr_desc = TEassign ([ x ], [ y ]); expr_typ = Twild }
            ++ aux r q
        | _, _ -> nop
      in
      aux vl el
  | TEblock block ->
      let rec aux env el =
        match el with
        | [] -> nop
        | { expr_desc = TEvars (vl, el) } :: t ->
            let id = ref (-8 * (env.nb_locals + 1)) in
            List.iter
              (fun v ->
                v.v_addr <- !id;
                id := !id - 8)
              vl;
            env.nb_locals <- env.nb_locals + List.length vl;
            (if el = [] then
             List.fold_left
               (fun c v -> c ++ xorq (reg rdi) (reg rdi) ++ pushq (reg rdi))
               nop vl
            else
              List.fold_left
                (fun c exp ->
                  c ++ expr env exp
                  ++
                  match exp.expr_typ with
                  | Tmany _ -> nop
                  | _ -> pushq (reg rdi))
                nop el)
            ++ aux env t
        | h :: t -> expr env h ++ aux env t
      in
      aux env block
  | TEif (e1, e2, e3) ->
      let l_else = new_label () and l_end = new_label () in
      expr env e1
      ++ testq (reg rdi) (reg rdi)
      ++ jz l_else ++ expr env e2 ++ jmp l_end ++ label l_else ++ expr env e3
      ++ label l_end
  | TEfor (e1, e2) ->
      let l_cond = new_label () and l_end = new_label () in
      label l_cond ++ expr env e1
      ++ testq (reg rdi) (reg rdi)
      ++ jz l_end ++ expr env e2 ++ jmp l_cond ++ label l_end
  | TEnew ty ->
      movq (imm (sizeof ty)) (reg rdi)
      ++ call "allocz"
      ++ movq (reg rax) (reg rdi)
  | TEcall (f, el) -> (
      let arg_s = List.length f.fn_params * 8 in
      let ret_s = List.length f.fn_typ * 8 in
      List.fold_left
        (fun c exp ->
          c ++ expr env exp
          ++ match exp.expr_typ with Tmany _ -> nop | _ -> pushq (reg rdi))
        nop el
      ++ call ("F_" ^ f.fn_name)
      ++
      match e.expr_typ with
      | Tmany _ -> addq (imm (ret_s + arg_s)) (reg rsp) ++ push_ret arg_s ret_s
      | _ -> addq (imm arg_s) (reg rsp))
  | TEdot (e1, f) -> assert false
  | TEvars _ -> assert false (* fait dans block *)
  | TEreturn [] -> jmp env.exit_label
  | TEreturn [ e1 ] -> expr env e1 ++ jmp env.exit_label
  | TEreturn el ->
      List.fold_left (fun c exp -> c ++ expr env exp ++ pushq (reg rdi)) nop el
      ++ jmp env.exit_label
  | TEincdec (e1, op) ->
      let as_op =
        match op with Inc -> incq (ind rdi) | Dec -> decq (ind rdi)
      in
      (match e1.expr_desc with
      | TEident x -> movq (reg rbp) (reg rdi) ++ addq (imm x.v_addr) (reg rdi)
      | TEunop (Ustar, e) -> expr env e
      | TEdot (e, x) -> expr env e ++ addq (imm x.f_ofs) (reg rdi)
      | _ -> assert false (* Ce cas n'arrive jamais car e1 est une l-value *))
      ++ as_op

let function_ f e =
  if !debug then eprintf "function %s:@." f.fn_name;
  let s = f.fn_name in
  let env = fun_env f in
  let args_addr = ref ((List.length f.fn_params * 8) + 8) in
  List.iter
    (fun v ->
      v.v_addr <- !args_addr;
      args_addr := !args_addr - 8)
    f.fn_params;
  label ("F_" ^ s)
  ++ pushq (reg rbp)
  ++ movq (reg rsp) (reg rbp)
  ++ expr env e
  ++ label ("E_" ^ s)
  ++ movq (reg rbp) (reg rsp)
  ++ popq rbp
  ++ (if List.length f.fn_typ > 1 then
      popq r15 ++ push_ret 16 (List.length f.fn_typ * 8) ++ pushq (reg r15)
     else nop)
  ++ ret

(* Fonctions d'affichage *)

let print_bool =
  let l_false = new_label () in
  label "print_bool"
  ++ xorq (reg rax) (reg rax)
  ++ cmpq (imm 0) (reg rdi)
  ++ je l_false
  ++ movq (ilab "S_true") (reg rdi)
  ++ call "printf" ++ ret ++ label l_false
  ++ movq (ilab "S_false") (reg rdi)
  ++ call "printf" ++ ret

let print_int =
  label "print_int"
  ++ movq (reg rdi) (reg rsi)
  ++ movq (ilab "S_int") (reg rdi)
  ++ xorq (reg rax) (reg rax)
  ++ call "printf" ++ ret

let print_ptr =
  label "print_ptr"
  ++ testq (reg rdi) (reg rdi)
  ++ je "print_nil"
  ++ movq (reg rdi) (reg rsi)
  ++ movq (ilab "S_hexint") (reg rdi)
  ++ xorq (reg rax) (reg rax)
  ++ call "printf" ++ ret

let print_string =
  label "print_string"
  ++ testq (reg rdi) (reg rdi)
  ++ je "print_nil"
  ++ movq (reg rdi) (reg rsi)
  ++ movq (ilab "S_string") (reg rdi)
  ++ xorq (reg rax) (reg rax)
  ++ call "printf" ++ ret

let print_nil =
  label "print_nil"
  ++ movq (ilab "S_nil") (reg rdi)
  ++ xorq (reg rax) (reg rax)
  ++ call "printf" ++ ret

let print_space =
  label "print_space"
  ++ movq (ilab "S_space") (reg rdi)
  ++ xorq (reg rax) (reg rax)
  ++ call "printf" ++ ret

let allocz =
  let loop_lab = new_label () in
  label "allocz"
  ++ pushq (reg rbx)
  ++ movq (reg rdi) (reg rbx)
  ++ call "malloc" ++ label loop_lab
  ++ decq (reg rbx)
  ++ movb (imm 0) (ind rax ~index:rbx)
  ++ testq (reg rbx) (reg rbx)
  ++ jnz loop_lab ++ popq rbx ++ ret

let decl code = function
  | TDfunction (f, e) -> code ++ function_ f e
  | TDstruct _ -> code

let file ?debug:(b = false) dl =
  debug := b;
  (* TODO calcul offset champs *)
  (* TODO code fonctions *)
  let funs = List.fold_left decl nop dl in
  {
    text =
      globl "main" ++ label "main" ++ call "F_main"
      ++ xorq (reg rax) (reg rax)
      ++ ret ++ funs ++ print_int ++ print_ptr ++ print_bool ++ print_string
      ++ print_nil ++ print_space ++ allocz;
    (* TODO print pour d'autres valeurs *)
    (* TODO appel malloc de stdlib *)
    data =
      label "S_int" ++ string "%ld" ++ label "S_hexint" ++ string "0x%x"
      ++ label "S_true" ++ string "true" ++ label "S_false" ++ string "false"
      ++ label "S_string" ++ string "%s" ++ label "S_nil" ++ string "<nil>"
      ++ label "S_space" ++ string " "
      ++ Hashtbl.fold (fun l s d -> label l ++ string s ++ d) strings nop;
  }
