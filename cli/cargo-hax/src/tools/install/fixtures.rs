//! Fixtures shared by the tests of the install pipeline: tar archives,
//! native-executable headers, and a local server to publish them from.
//!
//! `cargo-hax` is a binary crate, so its `#[cfg(test)]` modules cannot reach
//! the fixtures the integration tests under `tests/` share.

use std::collections::HashMap;

/// A gzipped tar of `(path, contents)` files, mode 0755.
pub fn make_archive(files: &[(&str, &[u8])]) -> Vec<u8> {
    let mut builder = tar::Builder::new(flate2::write::GzEncoder::new(
        Vec::new(),
        flate2::Compression::fast(),
    ));
    for (path, contents) in files {
        let mut header = tar::Header::new_gnu();
        header.set_size(contents.len() as u64);
        header.set_mode(0o755);
        header.set_cksum();
        builder.append_data(&mut header, path, *contents).unwrap();
    }
    builder.into_inner().unwrap().finish().unwrap()
}

/// Serve a fixed set of paths on localhost, and return the base URL.
pub fn serve(files: HashMap<String, Vec<u8>>) -> String {
    let server = tiny_http::Server::http("127.0.0.1:0").unwrap();
    let port = server.server_addr().to_ip().unwrap().port();
    std::thread::spawn(move || {
        for request in server.incoming_requests() {
            match files.get(request.url()) {
                Some(data) => request
                    .respond(tiny_http::Response::from_data(data.clone()))
                    .unwrap(),
                None => request.respond(tiny_http::Response::empty(404)).unwrap(),
            }
        }
    });
    format!("http://127.0.0.1:{port}")
}

pub fn sha256_hex(data: &[u8]) -> String {
    hex::encode(<sha2::Sha256 as sha2::Digest>::digest(data))
}

/// A little-endian 64-bit ELF header for `machine`, padded to a plausible
/// file.
pub fn elf(machine: u16) -> Vec<u8> {
    let mut bytes = vec![0u8; 64];
    bytes[..4].copy_from_slice(b"\x7FELF");
    bytes[4] = 2; // 64-bit
    bytes[5] = 1; // little-endian
    bytes[18..20].copy_from_slice(&machine.to_le_bytes());
    bytes
}

/// A little-endian 64-bit Mach-O header for `cputype`, padded likewise.
pub fn macho(cputype: u32) -> Vec<u8> {
    let mut bytes = vec![0u8; 64];
    bytes[..4].copy_from_slice(&0xFEED_FACFu32.to_le_bytes());
    bytes[4..8].copy_from_slice(&cputype.to_le_bytes());
    bytes
}

/// An executable that reads as built for `platform`.
pub fn binary_for(platform: &str) -> Vec<u8> {
    match platform {
        "linux-x86_64" => elf(0x3E),
        "linux-aarch64" => elf(0xB7),
        "macos-aarch64" => macho(0x0100_000C),
        other => panic!("no executable fixture for platform {other}"),
    }
}
