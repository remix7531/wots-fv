# Upstream RFC 8391 XMSS reference implementation, built unmodified
# against OpenSSL and installed as a static library + headers.
#
# Downstream (this repo's `test/gen_vectors.c`) consumes:
#   -I${xmss-reference}/include  -lxmssref  -lcrypto

{ lib, stdenv, fetchFromGitHub, openssl }:

stdenv.mkDerivation {
  pname = "xmss-reference";
  version = "unstable-2021-03-16";

  src = fetchFromGitHub {
    owner = "XMSS";
    repo = "xmss-reference";
    rev = "171ccbd26f098542a67eb5d2b128281c80bd71a6";
    hash = "sha256-YOqzlirQLpOS8n8WM2pDU5B7N7CXxd127KJ9yDFvXRs=";
  };

  buildInputs = [ openssl ];

  # No Makefile targets build a library; compile the sources directly.
  dontConfigure = true;

  buildPhase = ''
    runHook preBuild
    $CC -O2 -fPIC -std=c99 -c \
        params.c hash.c fips202.c hash_address.c randombytes.c \
        wots.c xmss.c xmss_core.c xmss_commons.c utils.c
    $AR rcs libxmssref.a \
        params.o hash.o fips202.o hash_address.o randombytes.o \
        wots.o xmss.o xmss_core.o xmss_commons.o utils.o
    runHook postBuild
  '';

  installPhase = ''
    runHook preInstall
    install -d $out/include/xmss-reference $out/lib
    install -m644 *.h $out/include/xmss-reference/
    install -m644 libxmssref.a $out/lib/
    install -Dm644 LICENSE $out/share/licenses/xmss-reference/LICENSE
    runHook postInstall
  '';

  meta = with lib; {
    description = "RFC 8391 XMSS reference implementation (static library + headers)";
    homepage = "https://github.com/XMSS/xmss-reference";
    license = licenses.cc0;
    platforms = platforms.unix;
  };
}
