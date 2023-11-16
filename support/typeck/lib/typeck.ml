(* Based on tychk_nbe.ml and Andras Kovacs's elab-zoo `03_holes` *)

open Core

module Dependent = struct
  open Sexplib.Std

  type meta_var = MetaVar of int [@@deriving sexp]
  type name = string [@@deriving sexp]

  type raw =
    | RVar of name
    | RLam of name * raw
    | RApp of raw * raw
    | RU
    | RPi of name * raw * raw
    | RLet of name * raw * raw * raw
    | RHole
  [@@deriving sexp]

  type ix = Ix of int [@@deriving sexp]
  type bd = Bound | Defined [@@deriving sexp]

  type ty = tm [@@deriving sexp]

  and tm =
    | Var of ix
    | Lam of name * tm
    | App of tm * tm
    | U
    | Pi of name * ty * ty
    | Let of name * ty * tm * tm
    | Meta of meta_var
    | InsertedMeta of meta_var * bd list
  [@@deriving sexp]

  type lvl = Lvl of int [@@deriving sexp]

  type env = value list [@@deriving sexp]
  and spine = value list [@@deriving sexp]
  and closure = Closure of env * tm [@@deriving sexp]
  and vty = value [@@deriving sexp]

  and value =
    | VFlex of meta_var * spine
    | VRigid of lvl * spine
    | VLam of name * closure
    | VPi of name * vty * closure
    | VU
  [@@deriving sexp]

  type meta_entry = Solved of value | Unsolved [@@deriving sexp]

  let next_meta = ref 0
  let mcxt : meta_entry Map.M(Int).t ref = ref (Map.empty (module Int))

  let lookup_meta (MetaVar m) =
    match Map.find !mcxt m with
    | Some x -> x
    | None -> raise (invalid_arg "impossible")

  let reset () =
    mcxt := Map.empty (module Int);
    next_meta := 0;
    ()

  let snoc xs y = y :: xs

  let rec closure_apply (Closure (env, t)) u = eval (snoc env u) t

  and v_app t u =
    match t with
    | VLam (_, t) -> closure_apply t u
    | VFlex (m, sp) -> VFlex (m, snoc sp u)
    | VRigid (x, sp) -> VRigid (x, snoc sp u)
    | _ -> raise (invalid_arg "impossible")

  and v_app_sp t = function [] -> t | u :: sp -> v_app (v_app_sp t sp) u

  and v_meta m =
    match lookup_meta m with Solved v -> v | Unsolved -> VFlex (m, [])

  and v_app_bds env v bds =
    match (env, bds) with
    | [], [] -> v
    | t :: env, Bound :: bds -> v_app (v_app_bds env v bds) t
    | _ :: env, Defined :: bds -> v_app_bds env v bds
    | _ -> raise (invalid_arg "impossible")

  and eval env = function
    | Var (Ix x) -> List.nth_exn env x
    | App (t, u) -> v_app (eval env t) (eval env u)
    | Lam (x, t) -> VLam (x, Closure (env, t))
    | Pi (x, a, b) -> VPi (x, eval env a, Closure (env, b))
    | Let (_, _, t, u) -> eval (snoc env (eval env t)) u
    | U -> VU
    | Meta m -> v_meta m
    | InsertedMeta (m, bds) -> v_app_bds env (v_meta m) bds

  let rec force t =
    match t with
    | VFlex (m, sp) -> (
        match lookup_meta m with Solved t -> force (v_app_sp t sp) | _ -> t)
    | t -> t

  let lvl_2_ix (Lvl l) (Lvl x) = Ix (l - x - 1)
  let inc_lvl (Lvl l) = Lvl (l + 1)

  let rec quote_sp l t = function
    | [] -> t
    | u :: sp -> App (quote_sp l t sp, quote l u)

  and quote l t =
    match force t with
    | VFlex (m, sp) -> quote_sp l (Meta m) sp
    | VRigid (x, sp) -> quote_sp l (Var (lvl_2_ix l x)) sp
    | VLam (x, t) ->
        Lam (x, quote (inc_lvl l) (closure_apply t (VRigid (l, []))))
    | VPi (x, a, b) ->
        Pi (x, quote l a, quote (inc_lvl l) (closure_apply b (VRigid (l, []))))
    | VU -> U

  let nf env t = quote (Lvl (List.length env)) (eval env t)

  type types = (string * vty) list
  type cxt = { env : env; lvl : lvl; types : types; bds : bd list }

  let fresh_meta cxt =
    let m = !next_meta in
    next_meta := m + 1;
    mcxt := Map.set !mcxt ~key:m ~data:Unsolved;
    InsertedMeta (MetaVar m, cxt.bds)

  type p_ren = { dom : lvl; cod : lvl; ren : lvl Map.M(Int).t }

  exception Unify_error of unit

  let unify_error = Unify_error ()
  let unlvl (Lvl x) = x

  let lift { dom; cod; ren } =
    {
      dom = inc_lvl dom;
      cod = inc_lvl cod;
      ren = Map.set ren ~key:(unlvl cod) ~data:dom;
    }

  let invert gamma sp =
    let rec go = function
      | [] -> (0, Map.empty (module Int))
      | t :: sp -> (
          let dom, ren = go sp in
          match force t with
          | VRigid (Lvl x, []) when not (Map.mem ren x) ->
              (dom + 1, Map.set ren ~key:x ~data:(Lvl dom))
          | _ -> raise unify_error)
    in
    let dom, ren = go sp in
    { dom = Lvl dom; cod = gamma; ren }

  let rename m pren v =
    let rec go_sp pren t = function
      | [] -> t
      | u :: sp -> App (go_sp pren t sp, go pren u)
    and go pren t =
      match force t with
      | VFlex (m', _) when phys_equal m m' -> raise unify_error
      | VFlex (m', sp) -> go_sp pren (Meta m') sp
      | VRigid (Lvl x, sp) -> (
          match Map.find pren.ren x with
          | None -> raise unify_error
          | Some x' -> go_sp pren (Var (lvl_2_ix pren.dom x')) sp)
      | VLam (x, t) ->
          Lam (x, go (lift pren) (closure_apply t (VRigid (pren.cod, []))))
      | VPi (x, a, b) ->
          Pi
            ( x,
              go pren a,
              go (lift pren) (closure_apply b (VRigid (pren.cod, []))) )
      | VU -> U
    in
    go pren v

  let lams l =
    let rec go x t =
      if phys_equal x l then t
      else Lam ("x" ^ Int.to_string (x + 1), go (x + 1) t)
    in
    go 0

  let solve gamma (MetaVar m) sp rhs =
    let pren = invert gamma sp in
    let rhs = rename (MetaVar m) pren rhs in
    let solution = eval [] (lams (unlvl pren.dom) rhs) in
    mcxt := Map.set !mcxt ~key:m ~data:(Solved solution);
    ()

  let rec unify_sp l sp sp' =
    match (sp, sp') with
    | [], [] -> ()
    | t :: sp, t' :: sp' ->
        unify_sp l sp sp';
        unify l t t'
    | _ -> raise unify_error

  and unify l t u =
    match (force t, force u) with
    | VLam (_, t), VLam (_, t') ->
        unify (inc_lvl l)
          (closure_apply t (VRigid (l, [])))
          (closure_apply t' (VRigid (l, [])))
    | t, VLam (_, t') ->
        unify (inc_lvl l)
          (v_app t (VRigid (l, [])))
          (closure_apply t' (VRigid (l, [])))
    | VLam (_, t), t' ->
        unify (inc_lvl l)
          (closure_apply t (VRigid (l, [])))
          (v_app t' (VRigid (l, [])))
    | VU, VU -> ()
    | VPi (_, a, b), VPi (_, a', b') ->
        unify l a a';
        unify (inc_lvl l)
          (closure_apply b (VRigid (l, [])))
          (closure_apply b' (VRigid (l, [])))
    | VRigid (x, sp), VRigid (x', sp') when phys_equal x x' -> unify_sp l sp sp'
    | VFlex (m, sp), VFlex (m', sp') when phys_equal m m' -> unify_sp l sp sp'
    | VFlex (m, sp), t' -> solve l m sp t'
    | t, VFlex (m', sp') -> solve l m' sp' t
    | _ -> raise unify_error

  let empty_cxt = { env = []; lvl = Lvl 0; types = []; bds = [] }

  let bind { env; lvl; types; bds } x a =
    {
      env = snoc env (VRigid (lvl, []));
      lvl = inc_lvl lvl;
      types = snoc types (x, a);
      bds = snoc bds Bound;
    }

  let define { env; lvl; types; bds } x t a =
    {
      env = snoc env t;
      lvl = inc_lvl lvl;
      types = snoc types (x, a);
      bds = snoc bds Defined;
    }

  let close_val cxt t = Closure (cxt.env, quote (inc_lvl cxt.lvl) t)

  exception Real_unify_error of ty * ty

  let unify_catch cxt t t' =
    try unify cxt.lvl t t'
    with Unify_error () ->
      raise (Real_unify_error (quote cxt.lvl t, quote cxt.lvl t'))

  exception Name_not_in_scope of name

  let rec check cxt t a =
    match (t, force a) with
    | RLam (x, t), VPi (_, a, b) ->
        Lam (x, check (bind cxt x a) t (closure_apply b (VRigid (cxt.lvl, []))))
    | RLet (x, a, t, u), a' ->
        let a = check cxt a VU in
        let va = eval cxt.env a in
        let t = check cxt t va in
        let vt = eval cxt.env t in
        let u = check (define cxt x vt va) u a' in
        Let (x, a, t, u)
    | RHole, _ -> fresh_meta cxt
    | t, expected ->
        let t, inferred = infer cxt t in
        unify_catch cxt expected inferred;
        t

  and infer cxt = function
    | RVar x ->
        let rec go ix = function
          | (x', a) :: types ->
              if String.equal x x' then (Var (Ix ix), a) else go (ix + 1) types
          | [] -> raise (invalid_arg (Printf.sprintf "Name not in scope: %s" x))
        in
        go 0 cxt.types
    | RLam (x, t) ->
        let a = eval cxt.env (fresh_meta cxt) in
        let t, b = infer (bind cxt x a) t in
        (Lam (x, t), VPi (x, a, close_val cxt b))
    | RApp (t, u) ->
        let t, tty = infer cxt t in
        (* ensure that tty is Pi *)
        let a, b =
          match force tty with
          | VPi (_, a, b) -> (a, b)
          | tty ->
              let a = eval cxt.env (fresh_meta cxt) in
              let b = Closure (cxt.env, fresh_meta (bind cxt "x" a)) in
              unify_catch cxt (VPi ("x", a, b)) tty;
              (a, b)
        in
        let u = check cxt u a in
        (App (t, u), closure_apply b (eval cxt.env u))
    | RU -> (U, VU)
    | RPi (x, a, b) ->
        let a = check cxt a VU in
        let b = check (bind cxt x (eval cxt.env a)) b VU in
        (Pi (x, a, b), VU)
    | RLet (x, a, t, u) ->
        let a = check cxt a VU in
        let va = eval cxt.env a in
        let t = check cxt t va in
        let vt = eval cxt.env t in
        let u, b = infer (define cxt x vt va) u in
        (Let (x, a, t, u), b)
    | RHole ->
        let a = eval cxt.env (fresh_meta cxt) in
        let t = fresh_meta cxt in
        (t, a)

  (*
    let id : (A : U) -> A -> A = λ A x. x;
    let id1 : (A : U) -> A -> A = λ A x. id _ x;
    U
   *)

  (*

           *)
  let tm =
    RLet
      ( "id",
        RPi ("A", RU, RPi ("_", RVar "A", RVar "A")),
        RLam ("A", RLam ("x", RVar "x")),
        RLet
          ( "id1",
            RPi ("A", RU, RPi ("_", RVar "A", RVar "A")),
            RLam ("A", RLam ("x", RApp (RApp (RVar "id", RHole), RVar "x"))),
            RU ) )

  let inferred = infer empty_cxt tm

  module McxtEntry = struct
    type t = meta_entry Map.M(Int).t [@@deriving sexp]
  end

  let sexp_of_mcxt x = [%sexp_of: McxtEntry.t] x
end

module SystemF = struct
  open Core
  open Sexplib.Std

  type meta_var = MetaVar of int [@@deriving sexp]
  type name = string [@@deriving sexp]

  type raw_ty =
    | RTVar of name
    | RTFree of name
    | RTArrow of raw_ty * raw_ty
    | RTForall of name * raw_ty
    | RTHole
    | RTUnit
  [@@deriving sexp]

  type raw_tm =
    | REVar of name
    | RELam of name * raw_tm
    | REApp of raw_tm * raw_tm
    | RELet of name * raw_ty option * raw_tm * raw_tm
    | REUnit
  [@@deriving sexp]

  type ix = Ix of int [@@deriving sexp]

  let unix (Ix ix) = ix

  type lvl = Lvl of int [@@deriving sexp]

  let unlvl (Lvl lvl) = lvl

  type ty =
    | TVar of ix
    | TUnit
    | TArrow of ty * ty
    | TForall of name * ty
    | TFree of name
    | TMeta of meta_var * tspine
    | TInsertedMeta of meta_var * lvl
  [@@deriving sexp]

  and tspine = ty list [@@deriving sexp]

  type tm =
    | EVar of ix
    | ELam of name * tm
    | EApp of tm * tm
    | ELet of name * ty * tm * tm
    | ETyAbs of name * tm
    | EUnit
  [@@deriving sexp]

  type env = vty list [@@deriving sexp]
  and vspine = vty list [@@deriving sexp]
  and closure = Closure of env * ty [@@deriving sexp]

  and vty =
    | VFlex of meta_var * vspine
    | VRigid of lvl
    | VUnit
    | VArrow of vty * vty
    | VForall of name * closure
    | VFree of name
  [@@deriving sexp]

  type meta_entry = Solved of ty | Unsolved [@@deriving sexp]

  let next_meta = ref 0
  let mcxt : meta_entry Map.M(Int).t ref = ref (Map.empty (module Int))

  let lookup_meta (MetaVar m) =
    match Map.find !mcxt m with
    | Some x -> x
    | None -> raise (invalid_arg "impossible")

  let reset () =
    mcxt := Map.empty (module Int);
    next_meta := 0;
    ()

  (* Apply a type closure *)
  let rec apply_type_closure (Closure (env, t)) u = eval_ty (u :: env) t

  (* Apply a metavariable to parameters *)
  and apply_meta a sp = eval_ty sp a

  (* Evaluate a metavariable into the semantic domain *)
  and eval_meta m sp =
    match lookup_meta m with
    | Solved v -> apply_meta v sp
    | Unsolved -> VFlex (m, sp)

  (* Evaluate a type into the semantic domain *)
  and eval_ty env = function
    | TVar (Ix i) -> List.nth_exn env i
    | TUnit -> VUnit
    | TArrow (a, b) -> VArrow (eval_ty env a, eval_ty env b)
    | TFree name -> VFree name
    | TMeta (m, sp) -> eval_meta m (eval_spine env sp)
    | TInsertedMeta (m, _) -> eval_meta m env
    | TForall (x, t) -> VForall (x, Closure (env, t))

  (* Evaluate a type spine `ty list` to a semantic domain spine `vty list` *)
  and eval_spine env = function
    | [] -> []
    | a :: sp -> eval_ty env a :: eval_spine env sp

  (* Force `t` until its head is no longer a solved metavar *)
  (* TODO: path compression? *)
  let rec force t =
    match t with
    | VFlex (m, sp) -> (
        match lookup_meta m with Solved t -> force (apply_meta t sp) | _ -> t)
    | t -> t

  let lvl2ix (Lvl l) (Lvl x) = Ix (l - x - 1)
  let inc_lvl (Lvl l) = Lvl (l + 1)

  let rec quote_ty l t =
    match force t with
    | VRigid l' -> TVar (lvl2ix l l')
    | VFlex (m, sp) -> TMeta (m, quote_ty_spine l sp)
    | VUnit -> TUnit
    | VArrow (a, b) -> TArrow (quote_ty l a, quote_ty l b)
    | VForall (x, b) ->
        TForall (x, quote_ty (inc_lvl l) (apply_type_closure b (VRigid l)))
    | VFree n -> TFree n

  and quote_ty_spine l = function
    | [] -> []
    | a :: sp -> quote_ty l a :: quote_ty_spine l sp

  (* Normalize a type to type-normal form *)
  let rec tnf_ty l env = function
    | TArrow (a, b) -> TArrow (tnf_ty l env a, tnf_ty l env b)
    | TMeta _ as t -> quote_ty l (eval_ty env t)
    | TInsertedMeta _ as t -> quote_ty l (eval_ty env t)
    | TForall (x, t) -> TForall (x, tnf_ty (inc_lvl l) (VRigid l :: env) t)
    | t -> t

  (* Normalize a term to type-normal form *)
  let rec tnf_tm l env = function
    | ELam (x, e) -> ELam (x, tnf_tm l env e)
    | EApp (a, b) -> EApp (tnf_tm l env a, tnf_tm l env b)
    | ELet (x, t, e1, e2) ->
        ELet (x, tnf_ty l env t, tnf_tm l env e1, tnf_tm l env e2)
    | ETyAbs (t, e) -> ETyAbs (t, tnf_tm (inc_lvl l) (VRigid l :: env) e)
    | t -> t

  type types = string list

  type cxt = {
    env : env;
    lvl : lvl;
    types : types;
    free_types : string list;
    vals : (string * vty) list;
  }

  let fresh_meta lvl =
    let m = !next_meta in
    next_meta := m + 1;
    mcxt := Map.set !mcxt ~key:m ~data:Unsolved;
    TInsertedMeta (MetaVar m, lvl)

  type p_ren = { dom : lvl; cod : lvl; ren : lvl Map.M(Int).t }

  exception Unify_error of string

  let lift { dom; cod; ren } =
    {
      dom = inc_lvl dom;
      cod = inc_lvl cod;
      ren = Map.set ren ~key:(unlvl cod) ~data:dom;
    }

  let invert gamma sp =
    let rec go = function
      | [] -> (0, Map.empty (module Int))
      | t :: sp -> (
          let dom, ren = go sp in
          match force t with
          | VRigid (Lvl x) when not (Map.mem ren x) ->
              (dom + 1, Map.set ren ~key:x ~data:(Lvl dom))
          | _ -> raise (Unify_error "invert"))
    in
    let dom, ren = go sp in
    { dom = Lvl dom; cod = gamma; ren }

  let rec rename_sp m pren = function
    | [] -> []
    | a :: sp -> rename m pren a :: rename_sp m pren sp

  and rename m pren t =
    match force t with
    | VFlex (m', _) when phys_equal m m' ->
        raise (Unify_error "occurs") (* occurs check *)
    | VFlex (m', sp) -> TMeta (m', rename_sp m pren sp)
    | VRigid (Lvl x) -> (
        match Map.find pren.ren x with
        | None -> raise (Unify_error "scope escape") (* scope escape check *)
        | Some x' -> TVar (lvl2ix pren.dom x'))
    | VUnit -> TUnit
    | VArrow (a, b) -> TArrow (rename m pren a, rename m pren b)
    | VFree n -> TFree n
    | VForall (x, t) ->
        TForall
          (x, rename m (lift pren) (apply_type_closure t (VRigid pren.cod)))

  let solve gamma (MetaVar m) sp rhs =
    let pren = invert gamma sp in
    let sol = rename (MetaVar m) pren rhs in
    mcxt := Map.set !mcxt ~key:m ~data:(Solved sol);
    ()

  let rec unify_sp l sp sp' =
    match (sp, sp') with
    | [], [] -> ()
    | t :: sp, t' :: sp' ->
        unify_sp l sp sp';
        unify l t t'
    | _ -> raise (Unify_error "spine")

  and unify l t u =
    match (force t, force u) with
    | VFlex (m, sp), VFlex (m', sp') when phys_equal m m' -> unify_sp l sp sp'
    (* | VFlex (m, sp), VFlex (m', sp') -> *)
    (*   solve l m sp (VFlex (m', sp')); *)
    (*   solve l m' sp' (VFlex (m, sp)) *)
    (* ^ TODO: is this valid, and why? *)
    | VFlex (m, sp), t' -> solve l m sp t'
    | t, VFlex (m', sp') -> solve l m' sp' t
    | VRigid x, VRigid x' when phys_equal x x' -> ()
    | VUnit, VUnit -> ()
    | VArrow (a, b), VArrow (a', b') ->
        unify l a a';
        unify l b b'
    | VForall (_, t), VForall (_, t') ->
        let c1 = apply_type_closure t (VRigid l) in
        let c2 = apply_type_closure t' (VRigid l) in
        unify (inc_lvl l) c1 c2
    | VFree n, VFree n' when String.equal n n' -> ()
    | _ -> raise (Unify_error "rigid")

  let empty_cxt =
    { env = []; lvl = Lvl 0; types = []; free_types = []; vals = [] }

  let bind_ty { env; lvl; types; free_types; vals } x =
    {
      env = VRigid lvl :: env;
      lvl = inc_lvl lvl;
      types = x :: types;
      free_types;
      vals;
    }

  (* let define_val { env; lvl; types; free_types; vals } x t a = *)
  (*   { *)
  (*     env; *)
  (*     lvl; *)
  (*     types; *)
  (*     free_types; *)
  (*     vals = (x, t, Some a) :: vals; *)
  (*   } *)

  let bind_val { env; lvl; types; free_types; vals } x t =
    { env; lvl; types; free_types; vals = (x, t) :: vals }

  let define_free_ty { env; lvl; types; free_types; vals } x =
    { env; lvl; types; free_types = x :: free_types; vals }

  let close_ty cxt t = Closure (cxt.env, quote_ty (inc_lvl cxt.lvl) t)

  exception Real_unify_error of ty * ty

  let unify_catch cxt t t' =
    try unify cxt.lvl t t'
    with Unify_error x ->
      let a = sexp_of_vty t |> Sexp.to_string_hum in
      let b = sexp_of_vty t' |> Sexp.to_string_hum in
      printf "Failed to unify: %s:\na=%s,\nb=%s\n" x a b;
      raise (Real_unify_error (quote_ty cxt.lvl t, quote_ty cxt.lvl t'))

  exception Name_not_in_scope of name

  let rec ast_ty_to_ty lvl env = function
    | RTUnit -> TUnit
    | RTVar name -> (
        match List.findi env ~f:(fun _ x -> String.equal x name) with
        | Some (i, _) -> TVar (Ix i)
        | None -> raise (Name_not_in_scope name))
    | RTArrow (a, b) -> TArrow (ast_ty_to_ty lvl env a, ast_ty_to_ty lvl env b)
    | RTFree name -> TFree name
    | RTForall (x, t) -> TForall (x, ast_ty_to_ty (inc_lvl lvl) (x :: env) t)
    | RTHole -> fresh_meta lvl
  (* let rec ast_tm_to_tm lvl env = function *)
  (*   | REUnit -> EUnit *)
  (*   | REVar name -> *)
  (*     (match List.findi env ~f:(fun _ x -> String.equal x name) with *)
  (*      | Some(i, _) -> EVar (Ix i) *)
  (*      | None -> raise (Name_not_in_scope name)) *)
  (*   | REApp (a, b) -> EApp (ast_tm_to_tm lvl env a, ast_tm_to_tm lvl env b) *)
  (*   | RELet (a, b) *)

  let rec check cxt e t =
    match (e, force t) with
    | _, VForall (x, a) ->
        let a = apply_type_closure a (VRigid cxt.lvl) in
        let e = check (bind_ty cxt x) e a in
        ETyAbs (x, e)
    | RELam (x, e), VArrow (a, b) ->
        let e = check (bind_val cxt x a) e b in
        ELam (x, e)
    | RELet (x, None, e1, e2), _ ->
        let e1, vt_e1 = infer cxt e1 in
        let e2 = check (bind_val cxt x vt_e1) e2 t in
        ELet (x, quote_ty cxt.lvl vt_e1, e1, e2)
    | RELet (x, Some a, e1, e2), _ ->
        let a = ast_ty_to_ty cxt.lvl cxt.types a in
        let va = eval_ty cxt.env a in
        let e1 = check cxt e1 va in
        let e2 = check (bind_val cxt x va) e2 t in
        ELet (x, a, e1, e2)
    | e, expected ->
        let e, inferred = infer_and_inst cxt e in
        unify_catch cxt expected inferred;
        e

  and infer cxt = function
    | REUnit -> (EUnit, VUnit)
    | REVar name ->
        let i, t =
          match
            List.findi cxt.vals ~f:(fun _ (x, _) -> String.equal x name)
          with
          | Some (i, (_, t)) -> (i, t)
          | None -> raise (Name_not_in_scope name)
        in
        (EVar (Ix i), t)
    | REApp (t, u) ->
        let t, tty = infer cxt t in
        (* ensure that tty is VArrow *)
        let a, b =
          match force tty with
          | VArrow (a, b) -> (a, b)
          | tty ->
              let a = eval_ty cxt.env (fresh_meta cxt.lvl) in
              let b = eval_ty cxt.env (fresh_meta cxt.lvl) in
              let tty = eagerly_instantiate cxt tty in
              unify_catch cxt (VArrow (a, b)) tty;
              (a, b)
        in
        let u = check cxt u a in
        (EApp (t, u), b)
    | RELam (x, e) ->
        let a = eval_ty cxt.env (fresh_meta cxt.lvl) in
        let e, b = infer (bind_val cxt x a) e in
        (ELam (x, e), VArrow (a, b))
    | RELet (x, None, e1, e2) ->
        let e1, vt_e1 = infer cxt e1 in
        let e2, vt_e2 = infer (bind_val cxt x vt_e1) e2 in
        (ELet (x, quote_ty cxt.lvl vt_e1, e1, e2), vt_e2)
    | RELet (x, Some a, e1, e2) ->
        let a = ast_ty_to_ty cxt.lvl cxt.types a in
        let va = eval_ty cxt.env a in
        let e1 = check cxt e1 va in
        let e2, vt_e2 = infer (bind_val cxt x va) e2 in
        (ELet (x, a, e1, e2), vt_e2)

  and infer_and_inst cxt e =
    let e, t = infer cxt e in
    (e, eagerly_instantiate cxt t)

  and eagerly_instantiate cxt = function
    | VForall (_, t) ->
        let m = eval_ty cxt.env (fresh_meta cxt.lvl) in
        eagerly_instantiate cxt (apply_type_closure t m)
    | t -> t

  let tm =
    RELet
      ( "id",
        Some (RTForall ("A", RTArrow (RTVar "A", RTVar "A"))),
        RELet
          ( "foo",
            Some (RTArrow (RTVar "A", RTVar "A")),
            RELam ("x", REVar "x"),
            REVar "foo" ),
        RELet
          ( "id1",
            Some (RTForall ("B", RTArrow (RTVar "B", RTVar "B"))),
            RELam ("y", REApp (REVar "id", REVar "y")),
            REApp (REVar "id1", REUnit) ) )

  let inferred = infer empty_cxt tm

  module McxtEntry = struct
    type t = meta_entry Map.M(Int).t [@@deriving sexp]
  end

  let sexp_of_mcxt x = [%sexp_of: McxtEntry.t] x
end
