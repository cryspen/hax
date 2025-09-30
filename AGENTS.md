## Runtime
You are running inside a **Nix-enabled Docker ephemeral container**.  
All package management should be done via **Nix**. Do **not** use apt, yum, or other system-level package managers.
Since the docker is ephemeral, feel free to install whatever you like with `nix profile nixpkgs#the_package_you_want`.

## How to install packages (persistent)

```bash
nix profile install nixpkgs#<package>
# Example:
nix profile install nixpkgs#curl
```

## How to use packages temporarily (on the fly)

```bash
nix shell nixpkgs#<pkg1> nixpkgs#<pkg2>
# Example:
nix shell nixpkgs#git nixpkgs#jq
```

## Preinstalled packages

`rustup`, `ripgrep`, `util-linux`, `file`, `gnused`, `tree`, `clang`, `jq`, `python3`, `nodejs`

## Notes

- Search for packages:
  ```bash
  nix search nixpkgs <term>
  ```
