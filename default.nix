{pkgs ? import <nixpkgs> {} }:

with pkgs;

stdenv.mkDerivation {
  name = "formal-crypto-0.0.1-git";
  buildInputs = [coq coqPackages.mathcomp_1_9];
  src = ./.;
  enableParallelBuilding = true;
  installFlags = "COQLIB=$(out)/lib/coq/${coq.coq-version}/";
}