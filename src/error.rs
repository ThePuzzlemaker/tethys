use std::fmt::{Debug, Display};

use thiserror::Error;

/// The error type used within Tethys.
#[derive(Error, Debug)]
pub enum TysError {
    /// IO errors
    #[error("i/o error")]
    Io(#[from] std::io::Error),
    /// UTF-8 decoding errors
    #[error("utf-8 decoding error")]
    FromUtf8(#[from] std::string::FromUtf8Error),
    /// Formatting errors
    #[error("formatting error")]
    Fmt(#[from] std::fmt::Error),
    /// A fatal error was reported within the global diagnostic reporting
    /// context.
    #[error(
        "internal diagnostic representation was printed incorrectly, please file a bug report"
    )]
    Diagnostic,
    /// Any other error, using [`eyre`]
    #[error(transparent)]
    Other(#[from] eyre::Report),
}

impl TysError {
    /// Try to downcast the error into a concrete type, if the error is a
    /// [`TysError::Other`].
    ///
    /// # Errors
    ///
    /// `self` is returned if the error could not be downcast.
    pub fn try_downcast<E>(self) -> Result<E, Self>
    where
        E: Display + Debug + Send + Sync + 'static,
    {
        if let TysError::Other(err) = self {
            let x = err.downcast()?;
            Ok(x)
        } else {
            Err(self)
        }
    }

    /// Try to downcast a reference to the error into a reference to a concrete
    /// type, if the error is a [`TysError::Other`].
    #[must_use]
    pub fn try_downcast_ref<E>(&self) -> Option<&E>
    where
        E: Display + Debug + Send + Sync + 'static,
    {
        if let TysError::Other(err) = self {
            err.downcast_ref()
        } else {
            None
        }
    }

    /// Try to downcast a mutable reference to the error into a mutable
    /// reference to a concrete type, if the error is a [`TysError::Other`].
    pub fn try_downcast_mut<E>(&mut self) -> Option<&mut E>
    where
        E: Display + Debug + Send + Sync + 'static,
    {
        if let TysError::Other(err) = self {
            err.downcast_mut()
        } else {
            None
        }
    }
}

/// A handy alias for [`Result<T, TysError>`], genericized over `T`.
pub type TysResult<T> = Result<T, TysError>;
