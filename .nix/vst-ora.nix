# coq-vst-ora ("Ordered Resource Algebras for Iris"), logical namespace
# `iris_ora`. This is the ORA library VST v3.1beta2 ("VST on Iris") was split
# onto: veric/external_state.v and friends `Require iris_ora.algebra.*` /
# `iris_ora.logic.*`. It is NOT vendored in the VST repo and NOT in nixpkgs, so
# we build it from upstream (mansky1/ora). Version 1.1 pins coq-iris = 4.3.0,
# matching the Iris the beta itself targets.
#
# Plain Iris-style project (Makefile -> coq_makefile -f _CoqProject), so
# mkCoqDerivation's default build/install phases install `iris_ora` to
# user-contrib unchanged.
{ lib
, mkCoqDerivation
, iris
, version
, src
}:

mkCoqDerivation {
  pname = "vst-ora";
  namePrefix = [ ];
  inherit version src;

  # iris (= 4.3.0) propagates std++; both land on COQPATH for the build and for
  # downstream consumers (VST, the proof).
  propagatedBuildInputs = [ iris ];

  meta = {
    description = "Ordered Resource Algebras for Iris (the iris_ora library, VST on Iris)";
    homepage = "https://github.com/mansky1/ora";
    license = lib.licenses.bsd3;
  };
}
