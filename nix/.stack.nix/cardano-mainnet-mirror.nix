{ system, compiler, flags, pkgs, hsPkgs, pkgconfPkgs, ... }:
  {
    flags = {};
    package = {
      specVersion = "2.0";
      identifier = { name = "cardano-mainnet-mirror"; version = "0.1.0.0"; };
      license = "MIT";
      copyright = "";
      maintainer = "operations@iohk.io";
      author = "IOHK";
      homepage = "";
      url = "";
      synopsis = "A convenient wrapper for the mirror of Cardano mainnet";
      description = "This package provides a list of FilePaths to the Cardano mainnet data files";
      buildType = "Custom";
      };
    components = {
      "library" = {
        depends = [ (hsPkgs.base) (hsPkgs.directory) (hsPkgs.filepath) ];
        };
      };
    } // {
    src = pkgs.fetchgit {
      url = "https://github.com/input-output-hk/cardano-mainnet-mirror";
      rev = "74ca63f8ad6b47beba2f565c73592cede63ce4b5";
      sha256 = "0kkgfdw6z2k7wrsjgcs1w3scm9d397nz5nacadw1jpan8l56xa5y";
      };
    }