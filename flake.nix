{
  description = "WOTS+ formal verification (RFC 8391, XMSS-SHA2_10_256) - Rocq + VST on Iris (v3.1beta2)";

  inputs = {
    # nixos-26.05 ships coqPackages_8_20 (Coq 8.20.1) plus the Iris 4.3.0 and
    # CompCert 3.15 the beta wants in its release tables, so the binary cache has
    # prebuilt Coq/CompCert artifacts and the closure stays internally consistent.
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-26.05";
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
        lib = pkgs.lib;

        # VST v3.1beta2 ("VST on Iris") targets Coq 8.19-8.20 + Iris 4.3.0 +
        # CompCert 3.15. Pin Iris and CompCert to those exact versions (both in
        # the nixpkgs release tables) on top of Coq 8.20.1, keeping a single
        # consistent Coq so the .vo are mutually loadable.
        coqPkgs = pkgs.coqPackages_8_20;
        coqV = coqPkgs.coq.coq-version; # "8.20"

        stdpp_1_11    = coqPkgs.stdpp.override    { version = "1.11.0"; };
        iris_4_3      = coqPkgs.iris.override     { version = "4.3.0"; stdpp = stdpp_1_11; };
        compcert_3_15 = coqPkgs.compcert.override { version = "3.15"; };

        # coq-vst-ora (logical namespace `iris_ora`): the ORA library VST on Iris
        # was split onto. Not in nixpkgs; built from mansky1/ora. Use v1.0 -- the
        # companion release of the VST 3.1beta line (tagged one day before
        # v3.1beta, pins Iris 4.3.0). v1.1 (2026) changed `Uora` to 3 args and
        # breaks v3.1beta2's shared/dshare.v.
        vst-ora = coqPkgs.callPackage ./.nix/vst-ora.nix {
          iris = iris_4_3;
          version = "1.0";
          src = pkgs.fetchFromGitHub {
            owner = "mansky1";
            repo = "ora";
            rev = "664c07ef73999dd53038a799fecabfbc8b28cb4e"; # v1.0
            hash = "sha256-Yd/mtnyxdV8cieT6HGQ4ZnBuDeu8NqGecZuHdPbadXI=";
          };
        };

        vst-on-iris = coqPkgs.callPackage ./.nix/vst-on-iris.nix {
          compcert = compcert_3_15;
          iris = iris_4_3;
          ora = vst-ora;
          version = "3.1beta2";
          src = pkgs.fetchFromGitHub {
            owner = "PrincetonUniversity";
            repo = "VST";
            rev = "835680c0ff66d89d9ade65b4bd4465b7c09bf60a"; # v3.1beta2
            hash = "sha256-YWU9o4t2GlDGa7t2W4H2kzuuAyHi6t/rQYQh7fZ9HmI=";
          };
        };

        # Full COQPATH for the proof: VST + its CompCert / Iris / std++ / Flocq
        # closure. (CompCert's .vo live in its `lib` output.)
        coqPath = lib.makeSearchPath "lib/coq/${coqV}/user-contrib" [
          vst-on-iris
          compcert_3_15.lib
          iris_4_3
          stdpp_1_11
          vst-ora
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
            compcert_3_15 # CompCert 3.15 .vo + clightgen
            iris_4_3
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
            rocq-mcp.packages.${system}.rocq-mcp
          ];
          shellHook = ''
            export COQPATH="${coqPath}"
            export XMSSREF_PREFIX=${xmss-reference}
          '';
        };

        packages = {
          inherit vst-on-iris vst-ora xmss-reference;
          default = xmss-reference;
        };
      });
}
