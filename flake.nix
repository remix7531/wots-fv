{
  description = "WOTS+ formal verification (RFC 8391, XMSS-SHA2_10_256) - Rocq + VST";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    flake-compat = {
      url = "github:NixOS/flake-compat";
      flake = false;
    };

    # NOTE: pinned to the `feat/nix-flake` branch on the remix7531 fork while
    # the Nix flake is in review upstream. Swap to
    # `github:LLM4Rocq/rocq-mcp/<tag>` once the flake lands there.
    rocq-mcp.url = "github:remix7531/rocq-mcp/feat/nix-flake";
    rocq-mcp.inputs.flake-utils.follows = "flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils, flake-compat, rocq-mcp, ... }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {
          inherit system;
          config.allowUnfreePredicate = pkg:
            builtins.elem (pkgs.lib.getName pkg) [ "compcert" ];
        };

        coqPkgs = pkgs.coqPackages_9_0;

        # Project-specific: upstream xmss-reference as static lib + headers.
        xmss-reference = pkgs.callPackage ./.nix/xmss-reference.nix { };
      in {
        devShells.default = pkgs.mkShell {
          shellHook = ''
            unset COQPATH
            export XMSSREF_PREFIX=${xmss-reference}
          '';
          packages = (with coqPkgs; [
            VST
            compcert
            coq
            coq-lsp
            flocq
          ]) ++ (with pkgs; [
            clang
            gcc
            gmp
            gmp.dev
            gnumake
            m4
            openssl
            pkg-config
            rocqPackages_9_0.vsrocq-language-server
            which
            # OCaml toolchain for building libwots_ocaml.a (see ocaml/).
            ocaml-ng.ocamlPackages_4_14.ocaml
            ocaml-ng.ocamlPackages_4_14.findlib
            ocaml-ng.ocamlPackages_4_14.digestif
            ocaml-ng.ocamlPackages_4_14.ocaml-lsp
          ]) ++ [
            xmss-reference
            rocq-mcp.packages.${system}.rocq-mcp
          ];
        };

        packages = {
          inherit xmss-reference;
          default = xmss-reference;
        };
      });
}
