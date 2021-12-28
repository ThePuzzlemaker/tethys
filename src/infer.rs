// use typed_arena::Arena;

// use crate::resolve::ast::{Hole, Level, Ty};

// #[derive(Clone)]
// pub struct TyCtxt<'tcx> {
//     pub arena: &'tcx Arena<Ty<'tcx>>,
//     pub(crate) vars: Vec<Ty<'tcx>>,
//     pub(crate) ty_level: Level,
// }

// pub type HoleId = usize;

// impl<'tcx> TyCtxt<'tcx> {
//     pub fn new(arena: &'tcx Arena<Ty<'tcx>>) -> Self {
//         Self {
//             arena,
//             vars: vec![],
//             ty_level: 0,
//         }
//     }

//     pub fn with_ty_var<T>(&mut self, f: impl FnOnce(&mut TyCtxt) -> T) -> T {
//         self.ty_level += 1;
//         let res = f(self);
//         self.ty_level -= 1;
//         res
//     }

//     pub fn with_var<T>(&mut self, ty: Ty<'tcx>, f: impl FnOnce(&mut TyCtxt) -> T) -> T {
//         self.vars.push(ty);
//         let res = f(self);
//         self.vars.pop();
//         res
//     }

//     pub fn get(&mut self, ty: Ty<'tcx>) -> Ty<'tcx> {
//         match ty {
//             Ty::Hole(hole) => _get_hole(self, *hole),
//             a => a,
//         }
//     }
// }

// fn _get_hole<'a, 'tcx>(ctx: &'a mut TyCtxt<'tcx>, mut hole_id: HoleId) -> &'tcx Ty<'tcx> {
//     let mut hole_ids = vec![];
//     let ty;
//     loop {
//         let hole = ctx.holes.get(hole_id).expect("hole");
//         match &*hole {
//             Hole::Filled(ty2) => {
//                 if let Ty::Hole(hole2) = &**ty2 {
//                     hole_ids.push(hole_id);
//                     hole_id = *hole2;
//                 } else {
//                     ty = *ty2;
//                     break;
//                 }
//             }
//             _ => {
//                 let ty2 = ctx.arena.alloc(Ty::Hole(hole_id));
//                 ty = &*ty2;
//                 break;
//             }
//         }
//     }
//     for hole_id in hole_ids {
//         ctx.holes[hole_id] = Hole::Filled(ty);
//     }
//     ty
// }
