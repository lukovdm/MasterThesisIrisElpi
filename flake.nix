{
  description = "ElPi test";
  inputs.flake-utils.url = "github:numtide/flake-utils";
  inputs.nixpkgs.url = "nixpkgs/nixos-unstable";

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
      in
      {
        devShell = pkgs.mkShell
          {
            nativeBuildInputs = [ pkgs.gnumake pkgs.gmp pkgs.coq pkgs.coqPackages.iris pkgs.coqPackages.coq-elpi pkgs.coqPackages.hierarchy-builder ];
          };
      });
}
