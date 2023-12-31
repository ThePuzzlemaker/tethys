use serde::Deserialize;

#[derive(Clone, Debug, Deserialize, PartialEq, Eq)]
pub struct UitestHeader {
    /// The test's description.
    pub desc: String,
    /// Which mode should this test be run in?
    pub mode: UitestMode,
    /// Which diagnostics should we expect?
    #[serde(default)]
    pub diags: Vec<UitestDiag>,
}

#[derive(Copy, Clone, Debug, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "kebab-case")]
pub enum UitestMode {
    /// Typechecking this file should pass.
    CheckPass,
    /// This file should be typechecked and errors should be collected.
    Diag,
}

#[derive(Clone, Debug, Deserialize, PartialEq, Eq)]
pub struct UitestDiag {
    pub kind: UitestDiagKind,
    pub message: String,
    #[serde(default)]
    pub labels: Vec<UitestLabel>,
}

#[derive(Clone, Debug, Deserialize, PartialEq, Eq)]
pub struct UitestLabel {
    pub loc: String,
    pub message: String,
}

#[derive(Clone, Debug, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "kebab-case")]
pub enum UitestDiagKind {
    Error,
}
