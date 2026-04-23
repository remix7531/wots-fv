{
  description = "WOTS+ formal verification (RFC 8391, XMSS-SHA2_10_256) - Rocq + VST";

  inputs = {
    vst-nix.url = "github:remix7531/vst-nix";
    nixpkgs.follows = "vst-nix/nixpkgs";
    flake-utils.follows = "vst-nix/flake-utils";
    flake-compat = {
      url = "github:NixOS/flake-compat";
      flake = false;
    };
  };

  outputs = { self, nixpkgs, flake-utils, flake-compat, vst-nix, ... }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {
          inherit system;
          config.allowUnfreePredicate = pkg:
            builtins.elem (pkgs.lib.getName pkg) [ "compcert" ];
        };

        # Project-specific: upstream xmss-reference as static lib + headers.
        xmss-reference = pkgs.callPackage ./.nix/xmss-reference.nix { };

      in {
        devShells.default = pkgs.mkShell {
          inputsFrom = [ vst-nix.devShells.${system}.default ];
          buildInputs = [
            pkgs.openssl
            xmss-reference
            # OCaml toolchain for building libwots_ocaml.a (see ocaml/).
            # Pin to 4.14 to match vst-nix's findlib (different OCaml
            # versions on the same shell cause a findlib multi-def).
            pkgs.ocaml-ng.ocamlPackages_4_14.ocaml
            pkgs.ocaml-ng.ocamlPackages_4_14.digestif
            pkgs.ocaml-ng.ocamlPackages_4_14.ocaml-lsp
          ];
          shellHook = ''
            export XMSSREF_PREFIX=${xmss-reference}
          '';
        };

        packages = {
          inherit xmss-reference;
          default = xmss-reference;
        };
      });
}
