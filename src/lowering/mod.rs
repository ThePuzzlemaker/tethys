//! This module implements lowering from the surface language (i.e.,
//! [`crate::parse::ast`]), to Tethys's core language (i.e., [`crate::ir`]).
//!
//! At the moment, this lowering is very simple, just performing name
//! resolution, but as Tethys becomes more complex (and it surely will), this
//! lowering will become more complex, and may even end up being intertwined
//! with typechecking/inference.
//!
//! A good place to start for this module is [`lower_code_unit`].
