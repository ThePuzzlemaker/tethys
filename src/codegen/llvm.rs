use std::{ffi::CString, io, path::Path, ptr, rc::Rc};

use llvm_sys::{
    analysis::{LLVMVerifierFailureAction, LLVMVerifyModule},
    bit_writer::LLVMWriteBitcodeToFile,
    core::{
        LLVMAddFunction, LLVMAddIncoming, LLVMAppendBasicBlockInContext, LLVMBuildAdd, LLVMBuildBr,
        LLVMBuildCall2, LLVMBuildCondBr, LLVMBuildICmp, LLVMBuildMul, LLVMBuildPhi, LLVMBuildRet,
        LLVMBuildRetVoid, LLVMBuildSDiv, LLVMBuildSub, LLVMConstInt, LLVMConstNamedStruct,
        LLVMConstStructInContext, LLVMContextCreate, LLVMContextDispose, LLVMCountParams,
        LLVMCreateBuilderInContext, LLVMDisposeBuilder, LLVMDisposeMessage, LLVMDisposeModule,
        LLVMDumpModule, LLVMFunctionType, LLVMGetInsertBlock, LLVMGetNamedFunction, LLVMGetParam,
        LLVMInt1TypeInContext, LLVMInt64TypeInContext, LLVMModuleCreateWithNameInContext,
        LLVMPositionBuilderAtEnd, LLVMStructCreateNamed, LLVMStructTypeInContext,
        LLVMVoidTypeInContext,
    },
    prelude::{
        LLVMBasicBlockRef, LLVMBool, LLVMBuilderRef, LLVMContextRef, LLVMModuleRef, LLVMTypeRef,
        LLVMValueRef,
    },
    LLVMIntPredicate,
};

#[derive(Clone, Debug)]
pub struct Context {
    inner: Rc<ContextInner>,
}

#[derive(Debug)]
struct ContextInner(LLVMContextRef);

impl Context {
    pub fn new() -> Self {
        Self {
            // SAFETY: This is always safe.
            inner: Rc::new(ContextInner(unsafe { LLVMContextCreate() })),
        }
    }
}

impl Default for Context {
    fn default() -> Self {
        Self::new()
    }
}

impl Drop for ContextInner {
    fn drop(&mut self) {
        // SAFETY: We have not been dropped before.
        unsafe { LLVMContextDispose(self.0) }
    }
}

#[derive(Clone, Debug)]
pub struct Module {
    inner: Rc<ModuleInner>,
    ctx: Context,
}

#[derive(Debug)]
struct ModuleInner(LLVMModuleRef);

impl Module {
    pub fn new(ctx: &Context, module_id: &str) -> Self {
        let module_id = CString::new(module_id).unwrap();
        // SAFETY: ctx is valid and so is module_id
        let module = unsafe { LLVMModuleCreateWithNameInContext(module_id.as_ptr(), ctx.inner.0) };
        Module {
            inner: Rc::new(ModuleInner(module)),
            ctx: ctx.clone(),
        }
    }

    pub fn dump(&self) {
        // SAFETY: we are valid.
        unsafe {
            LLVMDumpModule(self.inner.0);
        }
    }

    pub fn add_function(&self, name: &str, ty: Type) -> Function {
        let name = CString::new(name).unwrap();
        // SAFETY: self and ty are valid
        let val = unsafe { LLVMAddFunction(self.inner.0, name.as_ptr(), ty.inner) };
        Function {
            inner: val,
            ctx: self.ctx.clone(),
        }
    }

    pub fn verify(&self) {
        let mut error = ptr::null_mut();
        // SAFETY: self.inner is valid, and error is initialized by
        // `verify` before `dispose`.
        unsafe {
            LLVMVerifyModule(
                self.inner.0,
                LLVMVerifierFailureAction::LLVMAbortProcessAction,
                &mut error,
            );
            LLVMDisposeMessage(error);
        };
    }

    pub fn write_to_file(&self, p: &Path) -> Result<(), io::Error> {
        let path = CString::new(p.as_os_str().to_str().unwrap()).unwrap();
        // SAFETY: self.inner and path are valid.
        let res = unsafe { LLVMWriteBitcodeToFile(self.inner.0, path.as_ptr()) };
        if res == 0 {
            Ok(())
        } else {
            Err(io::Error::new(
                io::ErrorKind::Other,
                "error writing bitcode to file",
            ))
        }
    }

    pub fn get_named_function(&self, name: &str) -> Option<Function> {
        let name = CString::new(name).unwrap();
        // SAFETY: self and ty are valid
        let val = unsafe { LLVMGetNamedFunction(self.inner.0, name.as_ptr()) };
        if val.is_null() {
            return None;
        }
        Some(Function {
            inner: val,
            ctx: self.ctx.clone(),
        })
    }
}

#[derive(Clone, Debug)]
pub struct Function {
    inner: LLVMValueRef,
    ctx: Context,
}

impl Function {
    pub fn append_basic_block(&self, name: &str) -> BasicBlock {
        let name = CString::new(name).unwrap();
        // SAFETY: self, ctx, and name are valid.
        let bb =
            unsafe { LLVMAppendBasicBlockInContext(self.ctx.inner.0, self.inner, name.as_ptr()) };
        BasicBlock {
            inner: bb,
            ctx: self.ctx.clone(),
        }
    }

    pub fn count_params(&self) -> usize {
        // SAFETY: self.inner is valid.
        (unsafe { LLVMCountParams(self.inner) }) as usize
    }

    pub fn get_param(&self, index: usize) -> Value {
        assert!(index < self.count_params());
        // SAFETY: self.inner and index are valid.
        let val = unsafe { LLVMGetParam(self.inner, index.try_into().unwrap()) };
        Value {
            inner: val,
            ctx: self.ctx.clone(),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Value {
    inner: LLVMValueRef,
    ctx: Context,
}

impl Value {
    pub fn const_struct(ctx: &Context, vals: &[Value], packed: bool) -> Self {
        let mut vals = vals.iter().map(|x| x.inner).collect::<Vec<_>>();
        // SAFETY: All vals are valid.
        let val = unsafe {
            LLVMConstStructInContext(
                ctx.inner.0,
                vals.as_mut_ptr(),
                vals.len().try_into().unwrap(),
                packed as LLVMBool,
            )
        };

        Value {
            inner: val,
            ctx: ctx.clone(),
        }
    }

    pub fn const_named_struct(ctx: &Context, ty: Type, vals: &[Value]) -> Self {
        let mut vals = vals.iter().map(|x| x.inner).collect::<Vec<_>>();

        // SAFETY: If ty is not a struct type, this is invalid, but
        // not UB. ty is valid otherwise. All vals are valid, too.
        let val = unsafe {
            LLVMConstNamedStruct(ty.inner, vals.as_mut_ptr(), vals.len().try_into().unwrap())
        };
        Value {
            inner: val,
            ctx: ctx.clone(),
        }
    }

    pub fn const_int(ctx: &Context, ty: Type, n: u64, sign_extend: bool) -> Self {
        // SAFETY: If ty is not an int type, this is invalid, but not UB. ty is valid otherwise.
        let val = unsafe { LLVMConstInt(ty.inner, n, sign_extend as LLVMBool) };
        Value {
            inner: val,
            ctx: ctx.clone(),
        }
    }

    pub fn add_incoming(&self, incoming: &[(Value, BasicBlock)]) {
        let (mut vals, mut blocks): (Vec<_>, Vec<_>) =
            incoming.iter().map(|(x, y)| (x.inner, y.inner)).unzip();

        // SAFETY: self, vals, and blocks are valid. We have asserted
        // they are the same length. Additionally, adding incoming to
        // a non-phi is invalid but not UB.
        unsafe {
            LLVMAddIncoming(
                self.inner,
                vals.as_mut_ptr(),
                blocks.as_mut_ptr(),
                vals.len().try_into().unwrap(),
            )
        }
    }
}

#[derive(Clone, Debug)]
pub struct BasicBlock {
    inner: LLVMBasicBlockRef,
    ctx: Context,
}

impl Drop for Module {
    fn drop(&mut self) {
        // SAFETY: We have not been dropped before.
        unsafe { LLVMDisposeModule(self.inner.0) }
    }
}

#[derive(Clone, Debug)]
pub struct Type {
    // N.B. LLVMTypeRef is destroyed with the context.
    inner: LLVMTypeRef,
    ctx: Context,
}

impl Type {
    pub fn struct_named(ctx: Context, name: &str) -> Self {
        let name = CString::new(name.as_bytes()).unwrap();
        // SAFETY: ctx is valid and so is name
        let ty = unsafe { LLVMStructCreateNamed(ctx.inner.0, name.as_ptr()) };
        Type { inner: ty, ctx }
    }

    pub fn i64(ctx: &Context) -> Self {
        let ty = unsafe { LLVMInt64TypeInContext(ctx.inner.0) };
        Type {
            inner: ty,
            ctx: ctx.clone(),
        }
    }

    pub fn i1(ctx: &Context) -> Self {
        let ty = unsafe { LLVMInt1TypeInContext(ctx.inner.0) };
        Type {
            inner: ty,
            ctx: ctx.clone(),
        }
    }

    pub fn void(ctx: &Context) -> Self {
        let ty = unsafe { LLVMVoidTypeInContext(ctx.inner.0) };
        Type {
            inner: ty,
            ctx: ctx.clone(),
        }
    }

    pub fn function(ctx: &Context, result: Type, params: &[Type]) -> Self {
        let mut tys = params.iter().map(|x| x.inner).collect::<Vec<_>>();
        // SAFETY: result and tys are valid.
        let ty = unsafe {
            LLVMFunctionType(
                result.inner,
                tys.as_mut_ptr(),
                tys.len().try_into().unwrap(),
                false as LLVMBool,
            )
        };
        Type {
            inner: ty,
            ctx: ctx.clone(),
        }
    }

    pub fn struct_(ctx: &Context, elements: &[Type], packed: bool) -> Type {
        let mut tys = elements.iter().map(|x| x.inner).collect::<Vec<_>>();
        let ty = unsafe {
            LLVMStructTypeInContext(
                ctx.inner.0,
                tys.as_mut_ptr(),
                tys.len().try_into().unwrap(),
                packed as LLVMBool,
            )
        };
        Type {
            inner: ty,
            ctx: ctx.clone(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Builder {
    inner: Rc<BuilderInner>,
    ctx: Context,
}

impl Builder {
    pub fn new(ctx: &Context) -> Self {
        Builder {
            // SAFETY: The context is valid.
            inner: Rc::new(BuilderInner(unsafe {
                LLVMCreateBuilderInContext(ctx.inner.0)
            })),
            ctx: ctx.clone(),
        }
    }

    pub fn position_at_end(&self, bb: &BasicBlock) {
        // SAFETY: self and bb are valid
        unsafe { LLVMPositionBuilderAtEnd(self.inner.0, bb.inner) }
    }

    pub fn build_ret(&self, val: Value) -> Value {
        // SAFETY: self and val are valid.
        let val = unsafe { LLVMBuildRet(self.inner.0, val.inner) };
        Value {
            inner: val,
            ctx: self.ctx.clone(),
        }
    }

    pub fn build_add(&self, left: Value, right: Value, name: &str) -> Value {
        let name = CString::new(name).unwrap();
        // SAFETY: self, left, right, and name are valid.
        let val = unsafe { LLVMBuildAdd(self.inner.0, left.inner, right.inner, name.as_ptr()) };
        Value {
            inner: val,
            ctx: self.ctx.clone(),
        }
    }

    pub fn build_sub(&self, left: Value, right: Value, name: &str) -> Value {
        let name = CString::new(name).unwrap();
        // SAFETY: self.inner, left, right, and name are valid.
        let val = unsafe { LLVMBuildSub(self.inner.0, left.inner, right.inner, name.as_ptr()) };
        Value {
            inner: val,
            ctx: self.ctx.clone(),
        }
    }

    pub fn build_mul(&self, left: Value, right: Value, name: &str) -> Value {
        let name = CString::new(name).unwrap();
        // SAFETY: self.inner, left, right, and name are valid.
        let val = unsafe { LLVMBuildMul(self.inner.0, left.inner, right.inner, name.as_ptr()) };
        Value {
            inner: val,
            ctx: self.ctx.clone(),
        }
    }

    pub fn build_sdiv(&self, left: Value, right: Value, name: &str) -> Value {
        let name = CString::new(name).unwrap();
        // SAFETY: self.inner, left, right, and name are valid.
        let val = unsafe { LLVMBuildSDiv(self.inner.0, left.inner, right.inner, name.as_ptr()) };
        Value {
            inner: val,
            ctx: self.ctx.clone(),
        }
    }

    pub fn build_icmp(&self, op: LLVMIntPredicate, left: Value, right: Value, name: &str) -> Value {
        let name = CString::new(name).unwrap();
        // SAFETY: self.inner, left, right, and name are valid.
        let val =
            unsafe { LLVMBuildICmp(self.inner.0, op, left.inner, right.inner, name.as_ptr()) };
        Value {
            inner: val,
            ctx: self.ctx.clone(),
        }
    }

    pub fn build_ret_void(&self) -> Value {
        // SAFETY: self.inner is valid.
        let val = unsafe { LLVMBuildRetVoid(self.inner.0) };
        Value {
            inner: val,
            ctx: self.ctx.clone(),
        }
    }

    pub fn build_phi(&self, ty: Type, name: &str) -> Value {
        let name = CString::new(name).unwrap();
        // SAFETY: self.inner, ty, and name are valid.
        let val = unsafe { LLVMBuildPhi(self.inner.0, ty.inner, name.as_ptr()) };
        Value {
            inner: val,
            ctx: self.ctx.clone(),
        }
    }

    pub fn build_br(&self, block: &BasicBlock) -> Value {
        // SAFETY: self and block are valid.
        let val = unsafe { LLVMBuildBr(self.inner.0, block.inner) };
        Value {
            inner: val,
            ctx: self.ctx.clone(),
        }
    }

    pub fn build_cond_br(&self, cond: &Value, then: &BasicBlock, then_else: &BasicBlock) -> Value {
        // SAFETY: self, cond, then, and then_else are valid.
        let val = unsafe { LLVMBuildCondBr(self.inner.0, cond.inner, then.inner, then_else.inner) };
        Value {
            inner: val,
            ctx: self.ctx.clone(),
        }
    }

    pub fn build_call(&self, func: &Function, ty: &Type, args: &[Value], name: &str) -> Value {
        let name = CString::new(name).unwrap();
        let mut args = args.iter().map(|x| x.inner).collect::<Vec<_>>();
        let val = unsafe {
            LLVMBuildCall2(
                self.inner.0,
                ty.inner,
                func.inner,
                args.as_mut_ptr(),
                args.len().try_into().unwrap(),
                name.as_ptr(),
            )
        };
        Value {
            inner: val,
            ctx: self.ctx.clone(),
        }
    }

    pub fn get_insert_block(&self) -> Option<BasicBlock> {
        // SAFETY: self is valid
        let block = unsafe { LLVMGetInsertBlock(self.inner.0) };
        if block.is_null() {
            None
        } else {
            Some(BasicBlock {
                inner: block,
                ctx: self.ctx.clone(),
            })
        }
    }
}

#[derive(Debug)]
struct BuilderInner(LLVMBuilderRef);

impl Drop for BuilderInner {
    fn drop(&mut self) {
        // SAFETY: We haven't been dropped before.
        unsafe { LLVMDisposeBuilder(self.0) }
    }
}
