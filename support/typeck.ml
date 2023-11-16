(* Based on tychk_nbe.ml and Andras Kovacs's elab-zoo `03_holes` *)
module IntMap = Map.Make (Int)

module Dependent = struct
  type meta_var = MetaVar of int
  type name = string

  type raw =
    | RVar of name
    | RLam of name * raw
    | RApp of raw * raw
    | RU
    | RPi of name * raw * raw
    | RLet of name * raw * raw * raw
    | RHole

  type ix = Ix of int
  type bd = Bound | Defined

  type ty = tm

  and tm =
    | Var of ix
    | Lam of name * tm
    | App of tm * tm
    | U
    | Pi of name * ty * ty
    | Let of name * ty * tm * tm
    | Meta of meta_var
    | InsertedMeta of meta_var * bd list

  type lvl = Lvl of int

  type env = value list
  and spine = value list
  and closure = Closure of env * tm
  and vty = value

  and value =
    | VFlex of meta_var * spine
    | VRigid of lvl * spine
    | VLam of name * closure
    | VPi of name * vty * closure
    | VU

  type meta_entry = Solved of value | Unsolved

  let next_meta = ref 0
  let mcxt : meta_entry IntMap.t ref = ref IntMap.empty

  let lookup_meta (MetaVar m) =
    match IntMap.find_opt m !mcxt with
    | Some x -> x
    | None -> raise (invalid_arg "impossible")

  let reset () =
    mcxt := IntMap.empty;
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
    | t :: env, Defined :: bds -> v_app_bds env v bds
    | _ -> raise (invalid_arg "impossible")

  and eval env = function
    | Var (Ix x) -> List.nth env x
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
    mcxt := IntMap.add m Unsolved !mcxt;
    InsertedMeta (MetaVar m, cxt.bds)

  type p_ren = { dom : lvl; cod : lvl; ren : lvl IntMap.t }

  exception Unify_error of unit

  let unify_error = Unify_error ()
  let unlvl (Lvl x) = x

  let lift { dom; cod; ren } =
    {
      dom = inc_lvl dom;
      cod = inc_lvl cod;
      ren = IntMap.add (unlvl cod) dom ren;
    }

  let invert gamma sp =
    let rec go = function
      | [] -> (0, IntMap.empty)
      | t :: sp -> (
          let dom, ren = go sp in
          match force t with
          | VRigid (Lvl x, []) when not (IntMap.mem x ren) ->
              (dom + 1, IntMap.add x (Lvl dom) ren)
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
      | VFlex (m', sp) when m == m' -> raise unify_error
      | VFlex (m', sp) -> go_sp pren (Meta m') sp
      | VRigid (Lvl x, sp) -> (
          match IntMap.find_opt x pren.ren with
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
      if x == l then t else Lam ("x" ^ Int.to_string (x + 1), go (x + 1) t)
    in
    go 0

  let solve gamma (MetaVar m) sp rhs =
    let pren = invert gamma sp in
    let rhs = rename (MetaVar m) pren rhs in
    let solution = eval [] (lams (unlvl pren.dom) rhs) in
    mcxt := IntMap.add m (Solved solution) !mcxt;
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
    | VPi (x, a, b), VPi (x', a', b') ->
        unify l a a';
        unify (inc_lvl l)
          (closure_apply b (VRigid (l, [])))
          (closure_apply b' (VRigid (l, [])))
    | VRigid (x, sp), VRigid (x', sp') when x == x' -> unify_sp l sp sp'
    | VFlex (m, sp), VFlex (m', sp') when m == m' -> unify_sp l sp sp'
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
    | RHole, a -> fresh_meta cxt
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
          | VPi (x, a, b) -> (a, b)
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
end

