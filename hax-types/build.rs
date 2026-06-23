macro_rules! set_empty_env_var_with {
    ($var:literal, $f: expr) => {{
        println!("cargo:rurun-if-env-changed={}", $var);
        match option_env!($var) {
            Some(value) => value.to_string(),
            None => {
                let value = $f;
                println!("cargo:rustc-env={}={}", $var, value);
                value
            }
        }
    }};
}

const UNKNOWN: &str = "unknown";

fn git_command(args: &[&str]) -> String {
    std::process::Command::new("git")
        .args(args)
        .output()
        .map(|output| String::from_utf8(output.stdout).unwrap().trim().to_string())
        .ok()
        .filter(|s| !s.is_empty())
        .unwrap_or(UNKNOWN.to_string())
}

/// Every (section, key) that a complete `pins.toml` must define, across all
/// consumers (the baked `hax_types::pins` and the `install-aeneas.sh` installer).
const REQUIRED_PINS: &[(&str, &str)] = &[
    ("aeneas", "tag"),
    ("aeneas", "commit"),
    ("aeneas", "repo"),
    ("charon", "tag"),
    ("charon", "version"),
    ("lean", "toolchain"),
    ("hax-lean-lib", "commit"),
    ("hax-lean-lib", "repo"),
];

/// Bake the workspace-root tool pins (`pins.toml`) so they are available as
/// `hax_types::pins` (used by the aeneas-lean backend's version checks, generated
/// lakefiles, and `--help`). Read here once, in the shared crate, rather than in
/// each consumer. `pins.toml` is required and must be complete: a missing,
/// malformed, or incomplete file (any [`REQUIRED_PINS`] key missing or empty)
/// fails the build outright, so there is never a half-pinned binary.
fn pin_env_vars() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("pins.toml");
    println!("cargo:rerun-if-changed={}", path.display());
    let content = std::fs::read_to_string(&path).unwrap_or_else(|e| {
        panic!(
            "pins.toml is required but could not be read at {}: {e}",
            path.display()
        )
    });
    let pins: toml::Value = content
        .parse()
        .unwrap_or_else(|e| panic!("pins.toml at {} is not valid TOML: {e}", path.display()));

    let get = |section: &str, key: &str| -> &str {
        pins.get(section)
            .and_then(|t| t.get(key))
            .and_then(|v| v.as_str())
            .unwrap_or("")
            .trim()
    };

    let missing: Vec<String> = REQUIRED_PINS
        .iter()
        .filter(|(section, key)| get(section, key).is_empty())
        .map(|(section, key)| format!("[{section}].{key}"))
        .collect();
    if !missing.is_empty() {
        panic!(
            "pins.toml at {} is incomplete: missing or empty {}",
            path.display(),
            missing.join(", ")
        );
    }

    println!(
        "cargo:rustc-env=HAX_AENEAS_PIN_VERSION={}",
        get("aeneas", "commit")
    );
    println!(
        "cargo:rustc-env=HAX_AENEAS_PIN_REPO={}",
        get("aeneas", "repo")
    );
    println!(
        "cargo:rustc-env=HAX_CHARON_PIN_VERSION={}",
        get("charon", "version")
    );
    println!(
        "cargo:rustc-env=HAX_LEAN_PIN_TOOLCHAIN={}",
        get("lean", "toolchain")
    );
    println!(
        "cargo:rustc-env=HAX_LEAN_LIB_PIN_REPO={}",
        get("hax-lean-lib", "repo")
    );
    println!(
        "cargo:rustc-env=HAX_LEAN_LIB_PIN_COMMIT={}",
        get("hax-lean-lib", "commit")
    );
}

fn main() {
    pin_env_vars();

    let commit_hash =
        set_empty_env_var_with!("HAX_GIT_COMMIT_HASH", git_command(&["rev-parse", "HEAD"]));

    set_empty_env_var_with!("HAX_VERSION", {
        if commit_hash == UNKNOWN {
            env!("CARGO_PKG_VERSION").into()
        } else {
            git_command(&["tag", "--contains", &commit_hash])
                .lines()
                .next()
                .and_then(|tag| tag.split_once("hax-v"))
                .map(|(_, version)| version.trim().to_string())
                .unwrap_or_else(|| format!("untagged-git-rev-{}", &commit_hash[0..10]))
        }
    });
}
