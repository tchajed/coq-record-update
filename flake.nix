{
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/release-24.05";
    flake-utils.url = "github:numtide/flake-utils";
  };
  outputs = { self, nixpkgs, flake-utils, ... }: let

    coq-record-update = { lib, mkCoqDerivation, coq }: mkCoqDerivation rec {
      pname = "coq-record-update";
      defaultVersion = "0.3.4";
      release."0.3.4" = {
        src = lib.const (lib.cleanSourceWith {
          src = lib.cleanSource ./.;
          filter = let inherit (lib) hasSuffix; in path: type:
            (! hasSuffix ".gitignore" path)
            && (! hasSuffix "flake.nix" path)
            && (! hasSuffix "flake.lock" path)
            && (! hasSuffix "_build" path);
        });
      };
    };

  in flake-utils.lib.eachDefaultSystem (system: let
    pkgs = import nixpkgs {
      inherit system;
      overlays = [ self.overlays.default ];
    };
  in {
    devShells = {
      coq-record-update = self.packages.${system}.coq-record-update;
      default = self.packages.${system}.coq-record-update;
    };

    packages = {
      coq-record-update = pkgs.coqPackages_8_19.coq-record-update;
      default = self.packages.${system}.coq-record-update;
    };
  }) // {
    # NOTE: To use this flake, apply the following overlay to nixpkgs and use
    # the injected package from its respective coqPackages_VER attribute set!
    overlays.default = final: prev: let
      injectPkg = name: set:
        prev.${name}.overrideScope (self: _: {
          coq-record-update = self.callPackage coq-record-update {};
        });
    in (nixpkgs.lib.mapAttrs injectPkg {
      inherit (final) coqPackages_8_19;
    });
  };
}
