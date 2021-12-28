index_vec::define_index_type! {
    pub struct DefnId = u32;

    DISABLE_MAX_INDEX_CHECK = cfg!(not(debug_assertions));
    DEBUG_FORMAT = "DefnId({})";
    DISPLAY_FORMAT = "{}";
    IMPL_RAW_CONVERSIONS = true;
}

index_vec::define_index_type! {
    pub struct LocalId = u32;

    DISABLE_MAX_INDEX_CHECK = cfg!(not(debug_assertions));
    DEBUG_FORMAT = "LocalId({})";
    DISPLAY_FORMAT = "{}";
    IMPL_RAW_CONVERSIONS = true;
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct IrId {
    pub owner: DefnId,
    pub local_id: LocalId,
}
