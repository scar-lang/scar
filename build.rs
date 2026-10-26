use std::{env, fs, path::Path, process::Command};

fn main() {
    let manifest_dir = env::var("CARGO_MANIFEST_DIR").unwrap_or_else(|_| ".".to_string());
    let git_dir = Path::new(&manifest_dir).join(".git");
    let head_path = git_dir.join("HEAD");
    println!("cargo:rerun-if-changed={}", head_path.display());
    if let Ok(head) = fs::read_to_string(&head_path) {
        if let Some(reference) = head.trim().strip_prefix("ref: ") {
            println!(
                "cargo:rerun-if-changed={}",
                git_dir.join(reference).display()
            );
        }
    }

    let hash = Command::new("git")
        .current_dir(&manifest_dir)
        .args(["rev-parse", "--short", "HEAD"])
        .output()
        .ok()
        .filter(|output| output.status.success())
        .and_then(|output| String::from_utf8(output.stdout).ok())
        .map(|hash| hash.trim().to_string())
        .filter(|hash| !hash.is_empty())
        .or_else(|| read_head_hash(&git_dir))
        .unwrap_or_else(|| "unknown".to_string());

    println!("cargo:rustc-env=SCAR_GIT_COMMIT={hash}");
}

fn read_head_hash(git_dir: &Path) -> Option<String> {
    let head = fs::read_to_string(git_dir.join("HEAD")).ok()?;
    if let Some(reference) = head.trim().strip_prefix("ref: ") {
        let hash = fs::read_to_string(git_dir.join(reference)).ok()?;
        let hash = hash.trim();
        return (!hash.is_empty()).then(|| hash[..hash.len().min(7)].to_string());
    }
    let hash = head.trim();
    (!hash.is_empty()).then(|| hash[..hash.len().min(7)].to_string())
}
