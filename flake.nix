{
  description = "WOTS+ formal verification (RFC 8391, XMSS-SHA2_10_256) - Rocq + VST on Iris (v3.2beta)";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-26.05";
    flake-utils.url = "github:numtide/flake-utils";
    flake-compat = {
      url = "github:NixOS/flake-compat";
      flake = false;
    };
  };

  outputs = { self, nixpkgs, flake-utils, flake-compat, ... }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {
          inherit system;
          config.allowUnfreePredicate = pkg:
            builtins.elem (pkgs.lib.getName pkg) [ "compcert" ];
        };
        lib = pkgs.lib;

        # VST 3.2beta supports Rocq 9.0 to 9.1, Iris 4.5.0 and CompCert 3.17.
        coqPkgs = pkgs.coqPackages_9_1;
        rocqPkgs = coqPkgs.coq.rocqPackages;
        coqV = coqPkgs.coq.coq-version;

        stdpp = rocqPkgs.stdpp.override { version = "1.13.0"; };
        iris = rocqPkgs.iris.override { version = "4.5.0"; inherit stdpp; };
        compcert = coqPkgs.compcert.override { version = "3.17"; };

        vst-ora = rocqPkgs.callPackage ./.nix/vst-ora.nix {
          inherit iris;
        };

        vst-on-iris = coqPkgs.callPackage ./.nix/vst-on-iris.nix {
          inherit compcert iris;
          ora = vst-ora;
          version = "3.2beta";
          src = pkgs.fetchFromGitHub {
            owner = "PrincetonUniversity";
            repo = "VST";
            rev = "0850e1372d3cf68e09ac8b01d76613825212224e"; # v3.2beta
            hash = "sha256-LsbQz7jG93KMkM4v5UlQCRqKRBJP056pUUNzOzcp8Bg=";
          };
        };

        # CompCert's proof libraries live in its separate lib output.
        rocqPath = lib.makeSearchPath "lib/coq/${coqV}/user-contrib" [
          vst-on-iris
          compcert.lib
          iris
          stdpp
          vst-ora
          rocqPkgs.stdlib
          coqPkgs.flocq
          coqPkgs.MenhirLib
        ];

        # Project-specific: upstream xmss-reference as static lib + headers.
        xmss-reference = pkgs.callPackage ./.nix/xmss-reference.nix { };
      in {
        devShells.default = pkgs.mkShell {
          packages = (with coqPkgs; [
            coq
            coq-lsp
            vsrocq-language-server
          ]) ++ [
            compcert
            iris
            vst-on-iris
          ] ++ (with pkgs; [
            clang
            gcc
            gmp
            gmp.dev
            gnumake
            m4
            openssl
            pkg-config
            valgrind
            which
            # OCaml toolchain for building libwots_ocaml.a (see ocaml/).
            ocaml-ng.ocamlPackages_4_14.ocaml
            ocaml-ng.ocamlPackages_4_14.findlib
            ocaml-ng.ocamlPackages_4_14.digestif
            ocaml-ng.ocamlPackages_4_14.ocaml-lsp
          ]) ++ [
            xmss-reference
          ];
          shellHook = ''
            export ROCQPATH="${rocqPath}"
            unset COQPATH
            export XMSSREF_PREFIX=${xmss-reference}
          '';
        };

        packages = {
          inherit vst-on-iris vst-ora xmss-reference;
          default = xmss-reference;
        };
      });
}
