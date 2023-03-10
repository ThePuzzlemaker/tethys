use clap::Parser;
use eyre::{bail, eyre, Context};
use header::UitestHeader;
use indicatif::{MultiProgress, ProgressBar, ProgressStyle};
use runners::run_test;
use std::path::PathBuf;
use std::{fs, thread};
use walkdir::WalkDir;

pub mod header;
pub mod runners;

#[derive(Clone, Debug, Parser, PartialEq, Eq)]
/// The UI testing framework used in Tethys.
struct Args {
    #[clap(short = 'v')]
    #[clap(long = "verbose")]
    verbose: bool,
    #[clap(required = true)]
    tests: Vec<PathBuf>,
}

fn main() -> eyre::Result<()> {
    tracing_subscriber::fmt::init();
    color_eyre::install()?;

    let args = Args::parse();
    let mut tests = vec![];
    for path in args.tests {
        if !path.exists() {
            bail!("Test directory or file does not exist: {}", path.display());
        }
        if path.is_dir() {
            for entry in WalkDir::new(path).sort_by_file_name() {
                let entry = entry.wrap_err(eyre!("While searching for tests"))?;
                if entry.file_type().is_file() {
                    let path = entry.path();
                    if path.extension().and_then(|s| s.to_str()).unwrap_or("") == "tys" {
                        tests.push(path.to_path_buf());
                    }
                }
            }
        } else if path.is_file() {
            tests.push(path);
        } else {
            bail!(
                "Test path was neither a file nor a directory: {}",
                path.display()
            );
        }
    }

    let tests = tests
        .into_iter()
        .map(|path| {
            fs::read_to_string(&path)
                .wrap_err(eyre!("While reading test: `{}`", path.display()))
                .map(|x| (path.to_str().unwrap().to_string(), x))
        })
        .collect::<Result<Vec<_>, _>>()?
        .into_iter()
        .map(|(path, contents)| {
            let (header, code): (Vec<&str>, Vec<&str>) =
                contents.lines().partition(|&x| x.starts_with('#'));
            let header = header
                .into_iter()
                .map(|line| line.strip_prefix("# ").unwrap())
                .collect::<Vec<&str>>()
                .join("\n");
            let code = code.join("\n");
            if header.is_empty() {
                bail!("Test `{}` does not have a header", &path);
            }
            let header = serde_yaml::from_str::<UitestHeader>(&header)
                .wrap_err(eyre!("While parsing test header of `{}`", &path));
            header.map(|x| (path, x, code))
        })
        .collect::<Result<Vec<_>, _>>()?;

    todo!();

    let pb = MultiProgress::new();
    let total_pb = pb.add(
        ProgressBar::new(tests.len() as u64).with_style(
            ProgressStyle::default_bar()
                .template("[{bar}] {pos:>3}/{len:3} Elapsed: {elapsed} ETA: {eta}")
                .progress_chars(".. "),
        ),
    );
    let fail_spin = pb.add(
        ProgressBar::new_spinner()
            .with_style(ProgressStyle::default_spinner().tick_chars(r#"|/-\"#)),
    );
    thread::spawn(move || {
        pb.join().unwrap();
    });
    let mut failures = vec![];
    for (path, header, code) in tests {
        let failure = run_test(&path, header, code);
        total_pb.inc(1);
        if let Some(failure) = failure {
            failures.push((path, failure));
            fail_spin.set_message(format!("{} failures", failures.len()));
        }
    }
    fail_spin.finish_and_clear();

    Ok(())
}
