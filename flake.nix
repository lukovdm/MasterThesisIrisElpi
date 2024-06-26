{
  description = "Master thesis Elpi Iris";
  inputs.flake-utils.url = "github:numtide/flake-utils";
  inputs.nixpkgs.url = "nixpkgs/nixos-unstable";
  inputs.ltex_pkgs.url = "tarball+https://github.com/NixOS/nixpkgs/archive/8ad5e8132c5dcf977e308e7bf5517cc6cc0bf7d8.tar.gz";

  outputs = { self, nixpkgs, flake-utils, ltex_pkgs }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        my_ltex_ls = ltex_pkgs.legacyPackages.${system}.ltex-ls;
      in
      {
        devShell = pkgs.mkShell
          {
            nativeBuildInputs = [ pkgs.gnumake pkgs.gmp pkgs.opam pkgs.python310 pkgs.python310Packages.pygments my_ltex_ls ];
          };
        shellHook = ''
          eval $(opam env --switch=iris-dev --set-switch)
        '';
      });
}
