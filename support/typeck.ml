(* Based on tychk_nbe.ml, but with a different design *)
module AST = struct
  type ast_id = AstId of int
  type defn = { defn_id : ast_id; name : string; ty : ty; expr : expr }
  and ty = { ty_id : ast_id; kind : ty_kind }
  and ty_kind =
    | TyUnit
    | TyName of string
    | TyArrow of ty * ty
    | TyForall of string * ty
    | TyErr
  and expr = { expr_id : ast_id; kind : expr_kind }
  and expr_kind =
    | ExprUnit
    | ExprName of string
    | ExprApply of expr * expr
    | ExprLambda of string * expr
    | ExprLet of string * ty option * expr * expr
    | ExprErr
  and node =
    | NodeExpr of expr
    | NodeDefn of defn
    | NodeTy of ty
  and res =
    | ResDefn of ast_id
    | ResLocal of ast_id
    | ResTyVar of ast_id
    | ResErr
  
  type ast_ctx = { mutable next_id : int;
                   mutable nodes : (ast_id, node) Hashtbl.t;
                   mutable res_data: (ast_id, res) Hashtbl.t; }
  let mk_ctx = { next_id = 0; nodes = Hashtbl.create 64; res_data = Hashtbl.create 64; }
  let ctx_next_id ctx =
     let id = ctx.next_id in
        ctx.next_id <- id + 1;
        AstId id

  let mk_expr ctx kind = { expr_id = ctx_next_id ctx ; kind }
  let mk_ty ctx kind = { ty_id = ctx_next_id ctx; kind }
  let mk_defn ctx name ty expr = { defn_id = ctx_next_id ctx; name; ty; expr }

end

module Infer = struct
end