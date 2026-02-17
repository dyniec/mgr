{

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs?ref=nixos-unstable";
  };

  outputs = { self, nixpkgs }: 
    let pkgs = import nixpkgs{system="x86_64-linux";};
    mgr = pkgs.agdaPackages.mkDerivation {
      version = "0.1";
      pname = "mgr";
      src = ./mgr;
      buildInputs = [ pkgs.agdaPackages.standard-library ];
      meta = {};
    };
    doc = with pkgs; stdenv.mkDerivation {
      version = "0.1";
      pname = "doc";
      src = ./.;
      buildInputs = [ texliveFull pandoc python313Packages.pandoc-latex-environment (agda.withPackages [agdaPackages.standard-library])];
      buildPhase = "make doc.pdf";
      installPhase = "mkdir -p $out ;cp doc.pdf $out/";
      meta = {};
    };
    in{
    packages.x86_64-linux.default = mgr;
    packages.x86_64-linux.mgr = mgr;
    packages.x86_64-linux.doc = doc;
    devShells.x86_64-linux.default = pkgs.mkShell{
      name = "bla";
      buildInputs = with pkgs;[
        (agda.withPackages [agdaPackages.standard-library])
        pandoc
	texliveFull
	python313Packages.pandoc-latex-environment
        ];
    };
  };
}

