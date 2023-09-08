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
        # Using released versions
        # devShell = pkgs.mkShell
        #   {
        #     nativeBuildInputs = [ pkgs.gnumake pkgs.gmp pkgs.coq pkgs.coqPackages.iris pkgs.coqPackages.coq-elpi pkgs.coqPackages.hierarchy-builder pkgs.coqPackages.stdpp ];
        #   };
        devShell = pkgs.mkShell
          {
            nativeBuildInputs = with pkgs; [ gnumake gmp opam ];
          };
        shellHook = ''
          eval $(opam env --switch=iris-dev)
        '';
      });
}
