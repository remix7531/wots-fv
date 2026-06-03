# VST v3.1beta2 ("VST on Iris") built from source against nixpkgs
# coqPackages_8_20, with Iris pinned to 4.3.0 and CompCert to 3.15 (see flake.nix).
#
# Only the `vst` target (msl veric floyd simpleconc) is built -- the core the
# WOTS+ proof needs -- not the progs/sha/hmac/aes test suites. This mirrors
# upstream CI (.github/workflows/coq-action.yml @ v3.1beta2):
#     make vst BITSIZE=64 COMPCERT=bundled IGNORECOQVERSION=true \
#              IGNORECOMPCERTVERSION=true
# except we swap COMPCERT=bundled -> inst_dir so CompCert is the prebuilt nixpkgs
# package (and clightgen comes from it) rather than rebuilt in-tree.
#
# mkCoqDerivation gives us the Coq library setup hooks (iris/std++/CompCert/Flocq
# land on COQPATH automatically) plus a setup hook that puts VST on COQPATH for
# downstream consumers (the proof, the devShell).
{ lib
, coq
, mkCoqDerivation
, compcert
, iris
, ora
, version
, src
}:

mkCoqDerivation {
  pname = "VST-on-iris";
  namePrefix = [ ];
  inherit version src;

  # ora provides the `iris_ora` namespace veric requires; iris propagates std++;
  # compcert propagates Flocq + MenhirLib.
  buildInputs = [ iris ora ];
  propagatedBuildInputs = [ compcert ];

  preConfigure = ''
    patchShebangs util
  '';

  enableParallelBuilding = true;

  # Explicit: build only the `vst` target against the prebuilt CompCert located
  # by store path (COMPCERT=inst_dir). Iris/std++/Flocq come in via COQPATH.
  buildPhase = ''
    runHook preBuild
    make vst -j''${NIX_BUILD_CORES:-1} \
      BITSIZE=64 \
      ZLIST=bundled \
      COMPCERT=inst_dir \
      COMPCERT_INST_DIR=${compcert.lib}/lib/coq/${coq.coq-version}/user-contrib/compcert \
      IGNORECOQVERSION=true \
      IGNORECOMPCERTVERSION=true
    runHook postBuild
  '';

  installPhase = ''
    runHook preInstall
    dest=$out/lib/coq/${coq.coq-version}/user-contrib/VST
    mkdir -p "$dest"
    # Directories `make vst` populates with .vo (deps of msl/veric/floyd/simpleconc).
    for d in shared msl sepcomp veric zlist floyd concurrency atomics; do
      [ -d "$d" ] && cp -r "$d" "$dest/"
    done
    install -Dm444 VERSION "$dest/VERSION"
    runHook postInstall
  '';

  meta = {
    description = "Verified Software Toolchain v3.1beta2 (VST on Iris)";
    homepage = "https://vst.cs.princeton.edu/";
    license = lib.licenses.bsd2;
  };
}
