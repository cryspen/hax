{ stdenv, buildPythonPackage, fetchPypi, setuptools, wheel, mkdocs
, mkdocs-material, fetchFromGitHub, natsort, wcmatch, hax-frontend-docs
, mkdocs-awesome-nav }:
let
  mkdocs-glightbox = buildPythonPackage rec {
    pname = "mkdocs-glightbox";
    version = "0.4.0";

    src = fetchPypi {
      inherit pname version;
      hash = "sha256-OSs0IHv5WZEHGhbV+JFtHS8s1dW7Wa4pl0hczXeMcNk=";
    };

    doCheck = false;

    pyproject = true;
    build-system = [ setuptools wheel ];
  };
  mkdocs-nav-weight = buildPythonPackage rec {
    pname = "mkdocs-nav-weight";
    version = "0.0.7";

    src = fetchPypi {
      inherit pname version;
      hash = "sha256-gAQGD3U3/NmWW/3uUSrCjo/T+rqdIlMkKn83TjDgbp0=";
    };

    doCheck = false;

    pyproject = true;
    build-system = [ setuptools wheel mkdocs ];
  };

  # Latest hax release on GitHub. Its Manual is built as the "Version <x>"
  # subsection of the Manual, alongside "Branch main" (docs/manual/main/, the
  # current commit). To surface a new release, bump `manualReleaseVersion` and
  # `manual-release` (rev + sha256) below. Everything else — the subsection
  # title, URL and nav entry — is derived from these.
  manualReleaseVersion = "v0.3.7";
  manual-release = fetchFromGitHub {
    owner = "cryspen";
    repo = "hax";
    rev = "cargo-hax-v0.3.7"; # commit d8b5b3d3b666fee8943a351445d2b680105e8ea3
    sha256 = "sha256-mynIwfxaMA2w/36W74nvzvbO9433zp2vWg1RvsWGdZY=";
  };

in stdenv.mkDerivation {
  name = "hax-docs";
  src = ./..;
  buildInputs = [
    mkdocs
    mkdocs-material
    mkdocs-glightbox
    mkdocs-nav-weight
    mkdocs-awesome-nav
  ];
  buildPhase = ''
    # Add the latest release's Manual as the "Version ${manualReleaseVersion}"
    # subsection, next to "Branch main" (docs/manual/main/). It lives at
    # docs/manual/${manualReleaseVersion}/ -> /manual/${manualReleaseVersion}/,
    # and its nav title is set via .nav.yml.
    cp -r --no-preserve=mode,ownership \
      ${manual-release}/docs/manual docs/manual/${manualReleaseVersion}
    chmod -R u+w docs/manual/${manualReleaseVersion}
    printf 'title: Version ${manualReleaseVersion}\n' \
      > docs/manual/${manualReleaseVersion}/.nav.yml

    mkdocs build
  '';
  installPhase = ''
    mv site $out
    cp -rf ${hax-frontend-docs}/share/doc/ $out/frontend/docs
    mkdir -p $out/engine/docs/hax-engine
    echo 'Sorry, this page is temporarily unavailable (see <a href="https://github.com/cryspen/hax/issues/1675">issue</a>)' > $out/engine/docs/hax-engine/index.html
  '';
}
