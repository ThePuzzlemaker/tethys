use typed_arena::Arena;

use crate::ast::{Hole, Level, Ty};

#[derive(Clone)]
pub struct Context<'tcx> {
    pub arena: &'tcx Arena<Ty<'tcx>>,
    pub(crate) vars: Vec<&'tcx Ty<'tcx>>,
    pub(crate) ty_level: Level,
    pub(crate) holes: Vec<Hole<'tcx>>,
    pub(crate) fresh_hole_id: HoleId,
}

pub type HoleId = usize;

impl<'tcx> Context<'tcx> {
    pub fn new(arena: &'tcx Arena<Ty<'tcx>>) -> Self {
        Self {
            arena,
            vars: vec![],
            ty_level: 0,
            holes: vec![],
            fresh_hole_id: 0,
        }
    }

    pub fn with_ty_var<T>(&mut self, f: impl FnOnce(&mut Context) -> T) -> T {
        self.ty_level += 1;
        let res = f(self);
        self.ty_level -= 1;
        res
    }

    pub fn with_var<T>(&mut self, ty: &'tcx Ty<'tcx>, f: impl FnOnce(&mut Context) -> T) -> T {
        self.vars.push(ty);
        let res = f(self);
        self.vars.pop();
        res
    }

    fn fresh_hole_id(&mut self) -> HoleId {
        let fresh = self.fresh_hole_id;
        self.fresh_hole_id += 1;
        fresh
    }

    pub fn add_hole(&mut self, hole: Hole<'tcx>) -> HoleId {
        let id = self.fresh_hole_id();
        self.holes.push(hole);
        id
    }

    pub fn get(&mut self, ty: &'tcx Ty<'tcx>) -> &'tcx Ty<'tcx> {
        match ty {
            Ty::Hole(hole) => _get_hole(self, *hole),
            a => a,
        }
    }
}

fn _get_hole<'a, 'tcx>(ctx: &'a mut Context<'tcx>, mut hole_id: HoleId) -> &'tcx Ty<'tcx> {
    let mut hole_ids = vec![];
    let ty;
    loop {
        let hole = ctx.holes.get(hole_id).expect("hole");
        match &*hole {
            Hole::Filled(ty2) => {
                if let Ty::Hole(hole2) = &**ty2 {
                    hole_ids.push(hole_id);
                    hole_id = *hole2;
                } else {
                    ty = *ty2;
                    break;
                }
            }
            _ => {
                let ty2 = ctx.arena.alloc(Ty::Hole(hole_id));
                ty = &*ty2;
                break;
            }
        }
    }
    for hole_id in hole_ids {
        ctx.holes[hole_id] = Hole::Filled(ty);
    }
    ty
}
