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
            nativeBuildInputs = [ pkgs.opam pkgs.gnumake pkgs.gmp pkgs.coqPackages.iris pkgs.coqPackages.coq-elpi ];
            shellHook = ''
              eval $(opam env)
            '';
          };
      });
}
