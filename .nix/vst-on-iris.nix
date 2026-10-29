# Build the VST core against the same external CompCert used by clightgen.
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
  # Release strings absent from mkCoqDerivation's release table are treated
  # as development refs.
  version = { inherit version; };
  inherit src;

  # ora provides the `iris_ora` namespace veric requires; iris propagates std++;
  # compcert propagates Flocq + MenhirLib.
  propagatedBuildInputs = [ compcert iris ora ];

  preConfigure = ''
    patchShebangs util
  '';

  # Explicit: build only the `vst` target against the prebuilt CompCert located
  # by store path (COMPCERT=inst_dir). Iris/std++/Flocq come in via COQPATH.
  buildPhase = ''
    runHook preBuild
    make vst -j''${NIX_BUILD_CORES:-1} \
      BITSIZE=64 \
      ZLIST=bundled \
      COMPCERT=inst_dir \
      COMPCERT_INST_DIR=${compcert.lib}/lib/coq/${coq.coq-version}/user-contrib/compcert
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
    description = "Verified Software Toolchain ${version} (VST on Iris)";
    homepage = "https://vst.cs.princeton.edu/";
    license = lib.licenses.bsd2;
  };
}
