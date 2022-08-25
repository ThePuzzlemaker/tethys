use std::{env, fs};

use tethys::ctxt::TyCtxt;

use color_eyre::eyre;

fn main() -> eyre::Result<()> {
    tracing_subscriber::fmt::init();
    color_eyre::install()?;
    let src = fs::read_to_string(env::args().nth(1).expect("Expected file argument"))
        .expect("Failed to read file");

    let tcx = TyCtxt::default();
    let _ = tethys::run(&src, &tcx, false);

    Ok(())
}
