  let
    pkgs0 = import <nixpkgs> {};
    nixpkgs = pkgs0.fetchFromGitHub {
      owner  = "NixOS";
      repo   = "nixpkgs-channels";
      rev    = "3a1861fcabcdf08a0c369e49b48675242ceb3aa2";
      sha256 = "0sh2b4kb9vl4vz1y4mai986rlx80nsiv25f2lmdq06m5q7l0n0k9";
    };
    pkgs = import nixpkgs {};
  in with pkgs;
{
  stdpp = coqPackages.stdpp;
  env = stdenv.mkDerivation {
    name = "code-env";
    buildInputs = [
      coq
      coqPackages.stdpp
    ];
    enableParallelBuilding = true;
    installFlags = [ "COQLIB=$(out)/lib/coq/${coq.coq-version}/" ];
    src = ./.;
  };
}
