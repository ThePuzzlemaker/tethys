use std::{env, fs};

use tethys::*;

use color_eyre::eyre;
use ctxt::Arenas;

fn main() -> eyre::Result<()> {
    tracing_subscriber::fmt::init();
    color_eyre::install()?;
    let src = fs::read_to_string(env::args().nth(1).expect("Expected file argument"))
        .expect("Failed to read file");

    let arenas = Arenas::default();
    let tcx = tethys::get_tcx(&arenas);
    let _ = tethys::run(&src, &tcx, false);

    Ok(())
}
