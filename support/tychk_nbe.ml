(* Source: https://gist.github.com/mb64/f49ccb1bbf2349c8026d8ccf29bd158e#file-tychk_nbe-ml courtesy of MBones,
  with some modifications *)
(* Build with: ocamlfind ocamlc -package angstrom,stdio -linkpkg tychk_nbe.ml -o tychk *)
module AST = struct
  type ty =
    | TNamed of string
    | TFun of ty * ty
    | TForall of string * ty
  type exp =
    | Var of string
    | App of exp * exp
    | Annot of exp * ty
    | Lam of string * exp
    | Let of string * exp * exp
end

let elem_index a = (* wish OCaml had this in the stdlib *)
  let rec go i = function
    | [] -> None
    | x :: xs -> if x = a then Some i else go (i+1) xs in
  go 0

module Infer = struct
  type idx = int
  type lvl = int
  type ty =
    | TVar of idx
    | TFun of ty * ty
    | TForall of string * ty
  and vty =
    | VVar of lvl
    | VFun of vty * vty
    | VForall of string * (vty -> vty)
    | VHole of hole ref
  and hole =
    | Empty of { scope: lvl }
    | Filled of vty

  type ctx = { type_names: string list; lvl: lvl; env: (string * vty) list }

  let initial_ctx: ctx = { type_names = []; lvl = 0; env = [] }

  exception TypeError of string

  let add_ty_to_ctx (name: string) (ctx: ctx): ctx =
    { type_names = name :: ctx.type_names
    ; lvl = ctx.lvl + 1
    ; env = ctx.env }

  let add_var_to_ctx (name: string) (ty: vty) (ctx: ctx): ctx =
    { type_names = ctx.type_names
    ; lvl = ctx.lvl
    ; env = (name, ty) :: ctx.env }

  let lookup_var (name: string) (ctx: ctx) =
    match List.assoc_opt name ctx.env with
    | Some ty -> ty
    | None -> raise (TypeError ("variable " ^ name ^ " not in scope"))

  let ast_ty_to_ty (ast_ty: AST.ty) =
    let rec helper (env: string list) (ast_ty: AST.ty) = match ast_ty with
      | TNamed n -> (match elem_index n env with
          | Some idx -> TVar idx
          | None -> raise (TypeError ("type variable " ^ n ^ " not in scope")))
      | TFun(a, b) -> TFun (helper env a, helper env b)
      | TForall(n, a) -> TForall (n, helper (n::env) a) in
    helper [] ast_ty

  let rec eval (env: vty list) = function
    | TVar idx -> List.nth env idx
    | TFun(a, b) -> VFun(eval env a, eval env b)
    | TForall(name, ty) -> VForall(name, fun x -> eval (x::env) ty)

  let deref = function
    | VHole hole ->
        let rec helper h = match !h with
          | Filled (VHole h') ->
              (* path compression *)
              let a = helper h' in h := Filled a; a
          | Filled a -> a
          | _ -> VHole h in
        helper hole
    | a -> a

  let print_ty (ctx: ctx) ty =
    let parens p s = if p then "(" ^ s ^ ")" else s in
    let rec helper ctx p t = match deref t with
      | VVar lvl -> List.nth ctx.type_names (ctx.lvl - lvl - 1)
      | VFun(a, b) -> parens p (helper ctx true a ^ " -> " ^ helper ctx false b)
      | VForall(n, a) ->
          let rec freshen_name n =
            if List.mem n ctx.type_names then freshen_name (n ^ "'") else n in
          let n' = freshen_name n in
          let pr_a = helper (add_ty_to_ctx n' ctx) false (a (VVar ctx.lvl)) in
          parens p ("forall " ^ n' ^ ". " ^ pr_a)
      | VHole { contents = Empty { scope = lvl } } ->
          Printf.sprintf "?[at lvl %d]" lvl
      | VHole _ -> raise (invalid_arg "this should've been handled by deref") in
    helper ctx false ty

  (* when filling in a hole, a few things need to be checked:
     - occurs check: check that you aren't making recursive types
     - scope check: check that you aren't using bound vars outside its scope
  *)
  let unify_hole_prechecks (ctx: ctx) (hole: hole ref) (scope: lvl) ty =
    let initial_lvl = ctx.lvl in
    let rec helper ctx t = match deref t with
      | VVar lvl ->
          if lvl >= scope && lvl < initial_lvl
          then raise (TypeError ("type variable " ^ print_ty ctx (VVar lvl) ^ " escaping its scope"))
      | VFun(a, b) -> helper ctx a; helper ctx b;
      | VForall(n, a) ->
          helper (add_ty_to_ctx n ctx) (a (VVar ctx.lvl))
      | VHole ({ contents = Empty { scope = l } } as h) ->
          if h = hole
          then raise (TypeError "occurs check: can't make infinite type")
          else if l > scope then h := Empty { scope }
      | _ -> raise (invalid_arg "unify_hole_prechecks")
    in helper ctx ty

  let rec unify (ctx: ctx) a b = match deref a, deref b with
    | VHole hole_a, _ -> unify_hole_ty ctx hole_a b
    | _, VHole hole_b -> unify_hole_ty ctx hole_b a
    | VVar lvl_a, VVar lvl_b when lvl_a = lvl_b -> ()
    | VFun(a1, a2), VFun(b1, b2) -> unify ctx a1 b1; unify ctx a2 b2
    | VForall(n, a_fun), VForall(_, b_fun) ->
        let new_ctx = add_ty_to_ctx n ctx in
        unify new_ctx (a_fun (VVar ctx.lvl)) (b_fun (VVar ctx.lvl))
    | _ ->
        let a', b' = print_ty ctx a, print_ty ctx b in
        raise (TypeError ("mismatch between " ^ a' ^ " and " ^ b'))

  and unify_hole_ty (ctx: ctx) hole ty =
      match !hole with
      | Empty { scope } ->
          if ty <> VHole hole
          then (unify_hole_prechecks ctx hole scope ty; hole := Filled ty)
      | Filled _ -> raise (invalid_arg "unify_hole_ty")

  let rec eagerly_instantiate (ctx: ctx) = function
    | VForall(n, a) ->
        let new_hole = ref (Empty { scope = ctx.lvl }) in
        eagerly_instantiate ctx (a (VHole new_hole))
    | a -> a

  (* The mutually-recursive typechecking functions *)

  let rec check (ctx: ctx) (term: AST.exp) (ty: vty) = match term, deref ty with
    | _, VForall(n, a) ->
        check (add_ty_to_ctx n ctx) term (a (VVar ctx.lvl))
    | Lam(var, body), VFun(a, b) ->
        check (add_var_to_ctx var a ctx) body b
    | Let(var, exp, body), a ->
        let exp_ty = infer ctx exp in
        check (add_var_to_ctx var exp_ty ctx) body a
    | _, a ->
        let inferred_ty = infer_and_inst ctx term in
        unify ctx inferred_ty a

  and infer (ctx: ctx) (term: AST.exp) = match term with
    | Var var -> lookup_var var ctx
    | Annot(e, ast_ty) ->
        let ty = eval [] (ast_ty_to_ty ast_ty) in
        check ctx e ty; ty
    | App(f, arg) ->
        let f_ty = infer_and_inst ctx f in
        begin match deref f_ty with
          | VFun(a, b) -> check ctx arg a; b
          | VHole ({ contents = Empty { scope } } as hole) -> 
              let a = VHole (ref (Empty { scope })) in
              let b = VHole (ref (Empty { scope })) in
              hole := Filled (VFun(a, b));
              check ctx arg a;
              b
          | _ -> raise (TypeError "not a function type")
        end
    | Lam(var, body) ->
        let arg_ty = VHole (ref (Empty { scope = ctx.lvl })) in
        let res_ty = infer_and_inst (add_var_to_ctx var arg_ty ctx) body in
        VFun(arg_ty, res_ty)
    | Let(var, exp, body) ->
        let exp_ty = infer ctx exp in
        infer (add_var_to_ctx var exp_ty ctx) body

  and infer_and_inst (ctx: ctx) (term: AST.exp) =
    let ty = infer ctx term in eagerly_instantiate ctx ty

end

(* module Parser = struct
  open AST
  open Angstrom (* parser combinators library *)

  let keywords = ["forall"; "let"; "in"; "fun"]

  let whitespace = take_while (String.contains " \n\t")
  let lexeme a = a <* whitespace
  let ident = lexeme (
    let is_ident_char c =
      c = '_' || ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z') in
    let* i = take_while is_ident_char in
    if String.length i > 0 then return i else fail "expected ident")

  let str s = lexeme (string s) *> return ()
  let name =
    let* i = ident in
    if List.mem i keywords then fail (i ^ " is a keyword") else return i
  let keyword k =
    let* i = ident in
    if i = k then return () else fail ("expected " ^ k)
  let parens p = str "(" *> p <* str ")"

  let ty = fix (fun ty ->
    let simple_ty = parens ty <|> lift (fun n -> TNamed n) name in
    let forall_ty =
      let+ () = keyword "forall"
      and+ names = many1 name
      and+ () = str "."
      and+ a = ty in
      List.fold_right (fun n a -> TForall(n, a)) names a in
    let fun_ty =
      let+ arg_ty = simple_ty
      and+ () = str "->"
      and+ res_ty = ty in
      TFun(arg_ty, res_ty) in
    forall_ty <|> fun_ty <|> simple_ty <?> "type")

  let exp = fix (fun exp ->
    let atomic_exp = parens exp <|> lift (fun n -> Var n) name in
    let make_app (f::args) =
      List.fold_left (fun f arg -> App(f,arg)) f args in
    let simple_exp = lift make_app (many1 atomic_exp) in
    let annot_exp = 
      let+ e = simple_exp
      and+ annot = option (fun e -> e)
        (lift (fun t e -> Annot(e,t)) (str ":" *> ty)) in
      annot e in
    let let_exp =
      let+ () = keyword "let"
      and+ n = name
      and+ () = str "="
      and+ e = exp
      and+ () = keyword "in"
      and+ body = exp in
      Let(n, e, body) in
    let fun_exp =
      let+ () = keyword "fun"
      and+ args = many1 name
      and+ () = str "->"
      and+ body = exp in
      List.fold_right (fun arg body -> Lam(arg, body)) args body in
    let_exp <|> fun_exp <|> annot_exp <?> "expression")

  let parse (s: string) =
    match parse_string ~consume:All (whitespace *> exp) s with
    | Ok e -> e
    | Error msg -> failwith msg
end

let main () =
  let stdin = Stdio.In_channel.(input_all stdin) in
  let exp = Parser.parse stdin in
  let () = print_endline "parsed" in
  let open Infer in
  let ctx = initial_ctx in
  let ty = infer ctx exp in
  print_endline ("input : " ^ print_ty ctx ty)

let () = main () *)