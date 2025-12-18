{

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs?ref=nixos-unstable";
  };

  outputs = { self, nixpkgs }: 
    let pkgs = import nixpkgs{system="x86_64-linux";};
    mgr = pkgs.agdaPackages.mkDerivation {
      version = "0.1";
      pname = "mgr";
      src = ./.;
      buildInputs = [ pkgs.agdaPackages.standard-library ];
      meta = {};
    };
    in{
    packages.x86_64-linux.default = mgr;
    devShells.x86_64-linux.default = pkgs.mkShell{
      name = "bla";
      buildInputs = with pkgs;[(agda.withPackages [agdaPackages.standard-library])];
    };
  };
}

