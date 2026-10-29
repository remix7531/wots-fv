# ORA supplies the iris_ora namespace consumed by VST.
{ lib
, mkRocqDerivation
, iris
, version ? null
}:

mkRocqDerivation {
  pname = "vst-ora";
  owner = "mansky1";
  repo = "ora";
  inherit version;
  defaultVersion =
    let
      case = case: out: { inherit case out; };
    in
    with lib.versions;
    lib.switch iris.version [
      (case (isEq "4.5.0") "1.2.1")
    ] null;
  release."1.2.1".hash = "sha256-o6+BnqYe3JA0VVWRNw9yhYKsoPm1Xjjx71pNdLQ1U6M=";
  releaseRev = v: "v${v}";

  propagatedBuildInputs = [ iris ];

  meta = {
    description = "Ordered Resource Algebras for Iris (the iris_ora library, VST on Iris)";
    homepage = "https://github.com/mansky1/ora";
    license = lib.licenses.bsd3;
  };
}
