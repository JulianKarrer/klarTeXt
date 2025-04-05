use std::{
    fs::{self, File, OpenOptions},
    io::Write,
    path::Path,
};

/// Given a path to a file, returns the file stem, i.e. the file name without an extension.
pub fn get_file_name<P: AsRef<Path>>(path: P) -> String {
    let path = path.as_ref();
    path.file_stem()
        .and_then(|stem| stem.to_str())
        .map(|s| s.to_string())
        .unwrap_or_else(|| panic!("Invalid path: No valid file name"))
}

// Returns a `File` to a file with the specified `sibling_name` in the same directory as the file specified by `original_path`, i.e. a sibling file in the directory hierarchy.
pub fn create_sibling_file<P: AsRef<Path>>(
    original_path: P,
    sibling_name: &str,
    append: bool,
) -> File {
    let original_path = original_path.as_ref();
    if let Some(parent) = original_path.parent() {
        let sibling_path = parent.join(sibling_name);
        match OpenOptions::new()
            .create(true)
            .append(append)
            .write(!append)
            .open(&sibling_path)
        {
            Ok(f) => f,
            Err(e) => panic!("Error creating file {:?}: {}", sibling_path, e),
        }
    } else {
        panic!("Invalid path: No parent directory");
    }
}

/// Writes the `content` to a file with the specified `sibling_name` in the same directory as the file specified by `original_path`, i.e. a sibling file in the directory hierarchy.
pub fn write_to_sibling_file<P: AsRef<Path>>(original_path: P, sibling_name: &str, content: &str) {
    let mut f = create_sibling_file(original_path, sibling_name, false);
    f.write_all(content.as_bytes())
        .expect("Unable to write data");
}

/// Attempts to delete all files:
/// - starting with `klarTeXt_{}` where `{}` is the specified `file_name`
/// - in the same directory as the file specified by `path`
///
/// This is intended to clean up output files left behind by a previous program invocation as siblings of the source code file. Otherwise, a crash in the current invocation would not prevent the most recent result from being displayed.
pub fn delete_matching_files(path: &str, file_name: &str) -> std::io::Result<()> {
    let dir = Path::new(path)
        .parent()
        .ok_or_else(|| std::io::Error::new(std::io::ErrorKind::Other, "Invalid path"))?;

    if dir.is_dir() {
        for entry in fs::read_dir(dir)? {
            let entry = entry?;
            let file_name_str = entry.file_name();
            let file_name_os = file_name_str.to_string_lossy();

            if file_name_os.starts_with(&format!("klarTeXt_{}", file_name)) {
                fs::remove_file(entry.path())?;
            }
        }
    }
    Ok(())
}
