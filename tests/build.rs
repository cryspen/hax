// build.rs
use std::{
    env,
    ffi::OsStr,
    fs::{self, File},
    io::{self, Write},
    path::{Path, PathBuf},
};

fn main() -> io::Result<()> {
    println!("cargo:rerun-if-changed=src");
    println!("cargo:rerun-if-changed=build.rs");

    let manifest_dir = PathBuf::from(env::var("CARGO_MANIFEST_DIR").unwrap());
    let src_dir = manifest_dir.join("src");

    let mut entries = Vec::new();
    collect_rs_files(&src_dir, &mut entries)?;
    entries.sort();

    let out_path = src_dir.join("generated.rs");
    let mut out = File::create(&out_path)?;

    for abs_path in entries {
        let rel = abs_path.strip_prefix(&src_dir).unwrap().to_path_buf();
        let rel_str = forward_slashes(&rel);
        let ident = path_to_ident(&rel);

        if ident == "lib" || ident == "generated" {
            continue;
        }

        writeln!(
            out,
            "#[path = r##\"{rel}\"##] mod {ident};",
            rel = rel_str,
            ident = ident
        )?;
    }

    Ok(())
}

fn collect_rs_files(dir: &Path, out: &mut Vec<PathBuf>) -> io::Result<()> {
    for entry in fs::read_dir(dir)? {
        let entry = entry?;
        let path = entry.path();

        if path.is_dir() {
            collect_rs_files(&path, out)?;
        } else if path.extension() == Some(OsStr::new("rs")) {
            out.push(path);
        }
    }
    Ok(())
}

fn path_to_ident(rel_path: &Path) -> String {
    rel_path
        .with_extension("")
        .to_string_lossy()
        .into_owned()
        .replace('\\', "/")
        .replace('/', "__")
        .chars()
        .map(|c| if c.is_ascii_alphanumeric() { c } else { '_' })
        .collect()
}

fn forward_slashes(p: &Path) -> String {
    p.to_string_lossy().replace('\\', "/")
}
