//! The global reporting context for diagnostics.

use std::fmt;

use crate::parse::Span;

pub type Diagnostic = ariadne::Report<Span>;

/// The global reporting context for diagnostics.
pub struct DiagReportCtxt {
    errors: Vec<Diagnostic>,
    nonfatals: Vec<Diagnostic>,
    fatal: Option<Diagnostic>,
}

impl fmt::Debug for DiagReportCtxt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("DiagReportCtxt").finish_non_exhaustive()
    }
}

impl Default for DiagReportCtxt {
    fn default() -> Self {
        Self::new()
    }
}

impl DiagReportCtxt {
    /// Create a new `DiagReportCtxt`.
    #[must_use]
    pub fn new() -> Self {
        Self {
            errors: Vec::new(),
            nonfatals: Vec::new(),
            fatal: None,
        }
    }

    /// Clear the list of synchronized errors.
    pub fn clear_syncd(&mut self) {
        self.errors.clear();
    }

    /// Clear the list of nonfatals.
    pub fn clear_nonfatals(&mut self) {
        self.nonfatals.clear();
    }

    /// Clear the current fatal error.
    pub fn clear_fatal(&mut self) {
        self.fatal = None;
    }

    /// Clear the entire reporting context
    pub fn clear(&mut self) {
        self.clear_fatal();
        self.clear_nonfatals();
        self.clear_syncd();
    }

    /// Report an error that was synchronizable.
    pub fn report_syncd(&mut self, value: Diagnostic) {
        self.errors.push(value);
    }

    /// Report a non-fatal error.
    pub fn report_non_fatal(&mut self, value: Diagnostic) {
        self.nonfatals.push(value);
    }

    /// Report a fatal error. If there is already a fatal error reported, it
    /// will not be replaced.
    pub fn report_fatal(&mut self, value: Diagnostic) {
        if self.fatal.is_none() {
            self.fatal = Some(value);
        }
    }

    /// Get the list of nonfatal errors.
    #[must_use]
    pub fn nonfatals(&self) -> &[Diagnostic] {
        &self.nonfatals
    }

    /// Get the current fatal error, if any.
    #[must_use]
    pub fn fatal(&self) -> Option<&Diagnostic> {
        self.fatal.as_ref()
    }

    /// Get the list of synchronizable errors.
    #[must_use]
    pub fn errors(&self) -> &[Diagnostic] {
        &self.errors
    }
}
