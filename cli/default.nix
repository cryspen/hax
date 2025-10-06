{ craneLib, stdenv, makeWrapper, lib, rustc, rustc-docs, gcc, hax-engine
, doCheck ? true, libz, just, libiconv }:
let
  pname = "hax";
  is-webapp-static-asset = path:
    builtins.match ".*(script[.]js|index[.]html)" path != null;
  buildInputs = lib.optionals stdenv.isDarwin [ libiconv libz.dev ];
  binaries = [ hax hax-engine.bin rustc gcc hax_rust_engine ] ++ buildInputs;
  commonArgs = {
    version = "0.0.1";
    src = lib.cleanSourceWith {
      src = craneLib.path ./..;
      filter = path: type:
        craneLib.filterCargoSources path type || is-webapp-static-asset path;
    };
    inherit buildInputs doCheck;
    doNotRemoveReferencesToRustToolchain = true;
  } // (if doCheck then {
    # [cargo test] builds independent workspaces. Each time another
    # workspace is added, it's corresponding lockfile should be added
    # in the [cargoLockList] list below.
    cargoVendorDir = craneLib.vendorMultipleCargoDeps {
      cargoLockList = [ ../Cargo.lock ../tests/Cargo.lock ];
    };
  } else
    { });
  cargoArtifacts = craneLib.buildDepsOnly (commonArgs // { pname = pname; });
  hax = stdenv.mkDerivation {
    name = hax_with_artifacts.name;
    unpackPhase = "true";
    buildPhase = "true";
    installPhase = ''
      mkdir -p $out
      cp -r ${hax_with_artifacts}/bin $out/bin
    '';
  };
  hax_with_artifacts = craneLib.buildPackage (commonArgs // {
    inherit cargoArtifacts pname;
    doInstallCargoArtifacts = true;
  });
  hax_rust_engine = craneLib.buildPackage (commonArgs // {
    inherit cargoArtifacts;
    buildInputs = buildInputs ++ [ makeWrapper ];
    pname = "hax-rust-engine";
    cargoExtraArgs = "--manifest-path rust-engine/Cargo.toml --locked";
  });
  docs = craneLib.cargoDoc (commonArgs // {
    # preBuildPhases = [ "addRustcDocs" ];
    cargoDocExtraArgs = "--document-private-items";
    # addRustcDocs = ''
    #   mkdir -p target/doc
    #   cp --no-preserve=mode -rf ${rustc-docs}/share/doc/rust/html/rustc/* target/doc/
    # '';
    inherit cargoArtifacts pname;
  });
  tests = craneLib.buildPackage (commonArgs // {
    inherit cargoArtifacts;
    pname = "hax-tests";
    doCheck = true;
    CI = "true";
    cargoBuildCommand = "true";
    checkPhaseCargoCommand = ''
      cp ${../justfile} justfile
      mv tests/snapshots tests/old-snapshots
      just test
      diff tests/snapshots tests/old-snapshots
    '';
    buildInputs = binaries ++ [ just ];
  });
in stdenv.mkDerivation {
  name = hax.name;
  buildInputs = [ makeWrapper ];
  phases = [ "installPhase" ];
  installPhase = ''
    mkdir -p $out/bin
    makeWrapper ${hax}/bin/cargo-hax $out/bin/cargo-hax \
      --prefix PATH : ${lib.makeBinPath binaries} \
      ${
        lib.optionalString stdenv.isDarwin ''
          --prefix RUSTFLAGS : "-C link-arg=-L${libiconv}/lib" \
          --suffix DYLD_LIBRARY_PATH : ${lib.makeLibraryPath [ libz rustc ]}
        ''
      }
  '';
  meta.mainProgram = "cargo-hax";
  passthru = {
    unwrapped = hax;
    hax-engine-names-extract = craneLib.buildPackage (commonArgs // {
      pname = "hax_engine_names_extract";
      cargoLock = ../Cargo.lock;
      cargoToml = ../engine/names/extract/Cargo.toml;
      cargoArtifacts = hax_with_artifacts;
      nativeBuildInputs = [ hax_with_artifacts ];
      postUnpack = ''
        cd $sourceRoot/engine/names/extract
        sourceRoot="."
      '';
    });
    inherit docs tests;
  };
}
