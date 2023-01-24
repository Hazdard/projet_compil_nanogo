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

type env = {
  exit_label : string;
  ofs_this : int;
  nb_locals : int ref; (* maximum *)
  next_local : int; (* 0, 1, ... *)
}

let empty_env =
  { exit_label = ""; ofs_this = -1; nb_locals = ref 0; next_local = 0 }

let mk_bool d = { expr_desc = d; expr_typ = Tbool }

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
        match lv.expr_desc with
        | TEident x ->
            if x.v_name = "_" then nop
            else movq (reg rdi) (ind ~ofs:x.v_addr rbp)
        | TEunop (Ustar, e) -> expr env e
        | TEdot (e, x) -> expr env e ++ addq (imm x.f_ofs) (reg rdi)
        | _ -> raise (Error (dummy_loc, "This can't happen cmp_assign"))
        (* Ce cas n'arrive jamais car lv est une l-value *)
      in
      lv_addr
      ++ pushq (reg rdi)
      ++ expr env e ++ popq rsi
      ++ movq (reg rdi) (ind rsi)
  | TEassign (_, _) -> assert false
  | TEblock el -> (* TODO code pour block *) assert false
  | TEif (e1, e2, e3) -> (* TODO code pour if *) assert false
  | TEfor (e1, e2) -> (* TODO code pour for *) assert false
  | TEnew ty -> (* TODO code pour new S *) assert false
  | TEcall (f, el) -> (* TODO code pour appel fonction *) assert false
  | TEdot (e1, { f_ofs = ofs }) -> (* TODO code pour e.f *) assert false
  | TEvars _ -> assert false (* fait dans block *)
  | TEreturn [] -> (* TODO code pour return e *) assert false
  | TEreturn [ e1 ] -> (* TODO code pour return e1,... *) assert false
  | TEreturn _ -> assert false
  | TEincdec (e1, op) -> (* TODO code pour return e++, e-- *) assert false

let function_ f e =
  if !debug then eprintf "function %s:@." f.fn_name;
  (* TODO code pour fonction *)
  let s = f.fn_name in
  label ("F_" ^ s) ++ expr empty_env e

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
      ++ ret ++ funs
      ++ inline
           "\n\
            print_int:\n\
           \        movq    %rdi, %rsi\n\
           \        movq    $S_int, %rdi\n\
           \        xorq    %rax, %rax\n\
           \        call    printf\n\
           \        ret\n";
    (* TODO print pour d'autres valeurs *)
    (* TODO appel malloc de stdlib *)
    data =
      label "S_int" ++ string "%ld"
      ++ Hashtbl.fold (fun l s d -> label l ++ string s ++ d) strings nop;
  }
