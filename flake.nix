{
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-23.11";
    flake-utils.url = "github:numtide/flake-utils";
  };
  outputs = { self, nixpkgs, flake-utils, ... }:
    flake-utils.lib.eachSystem
      [
        "x86_64-linux"
      ]

      (system:
        let
          pkgs = import nixpkgs { inherit system; };
          lib = pkgs.lib;

          mkSpotApps = appNames:
            pkgs.lib.genAttrs appNames
              (name: flake-utils.lib.mkApp {
                drv = self.packages.${system}.spot;
                name = name;
              });

          spotPackage =
            let
              inherit (builtins)
                filter
                head
                isString
                match
                readFile
                split
              ;

              # NOTE: Maintaining the version separately would be a pain, and we
              # can't have a flake.nix.in with a @VERSION@ because it would make
              # the flake unusable without running autoconf first, defeating some
              # of its purpose.
              #
              # So let's get it the hard way instead :)
              extractVersionRegex = ''^AC_INIT\(\[spot], \[([^]]+)], \[spot@lrde\.epita\.fr]\)$'';
              getLines = (fileContent:
                filter isString (split "\n" fileContent)
              );
              findVersionLine = (lines:
                lib.lists.findFirst
                  (l: lib.strings.hasPrefix "AC_INIT(" l)
                  null
                  lines
              );
              getVersion = (file:
                let
                  lines = getLines (readFile file);
                  versionLine = findVersionLine lines;
                  version = head (match extractVersionRegex versionLine);
                in
                  version
              );
            in
              {
                lib,
                pkgs,
                stdenv,
                # FIXME: do we want this flag?
                buildOrgDoc ? false,
                # Whether to enable Spot's Python 3 bindings
                enablePython ? false
              }:
              stdenv.mkDerivation {
                pname = "spot";
                version = getVersion ./configure.ac;

                src = self;

                enableParallelBuilding = true;

                # NOTE: Nix enables a lot of hardening flags by default, some of
                # these probably harm performance so I've disabled everything
                # (haven't benchmarked with vs without these, though).
                hardeningDisable = [ "all" ];

                # NOTE: mktexpk fails without a HOME set
                preBuild = ''
                  export HOME=$TMPDIR
                  patchShebangs tools
                '' + (if buildOrgDoc then ''
                ln -s ${pkgs.plantuml}/lib/plantuml.jar doc/org/plantuml.jar
              '' else ''
                  touch doc/org-stamp
                '');

                configureFlags = [
                  "--disable-devel"
                  "--enable-optimizations"
                ] ++ lib.optional (!enablePython) [
                  "--disable-python"
                ];

                nativeBuildInputs = with pkgs; [
                  autoreconfHook

                  autoconf
                  automake
                  bison
                  flex
                  libtool
                  perl
                ] ++ lib.optional buildOrgDoc [
                  graphviz
                  groff
                  plantuml
                  pdf2svg
                  R
                ] ++ lib.optional enablePython [
                  python3
                  swig4
                ];

                buildInputs = with pkgs; [
                  # should provide the minimum amount of packages necessary for
                  # building tl.pdf
                  (texlive.combine {
                    inherit (texlive)
                      scheme-basic
                      latexmk

                      booktabs
                      cm-super
                      doi
                      doublestroke
                      etoolbox
                      koma-script
                      mathabx-type1
                      mathpazo
                      metafont
                      microtype
                      nag
                      pgf
                      standalone
                      stmaryrd
                      tabulary
                      todonotes
                      wasy-type1
                      wasysym
                    ;
                  })
                ];
              };
        in
          {
            defaultPackage = self.packages.${system}.spot;

            packages = {
              # binaries + library only
              spot = pkgs.callPackage spotPackage {};

              # NOTE: clang build is broken on Nix when linking to stdlib++, using
              #       libcxx instead. See:
              #       https://github.com/NixOS/nixpkgs/issues/91285
              spotClang = pkgs.callPackage spotPackage {
                stdenv = pkgs.llvmPackages.libcxxStdenv;
              };

              spotWithOrgDoc = pkgs.callPackage spotPackage {
                buildOrgDoc = true;
              };

              spotWithPython = pkgs.python3Packages.toPythonModule (
                pkgs.callPackage spotPackage {
                  enablePython = true;
                }
              );

              spotFull = pkgs.python3Packages.toPythonModule (
                pkgs.callPackage spotPackage {
                  buildOrgDoc = true; enablePython = true;
                }
              );
            };

            apps = mkSpotApps [
              "autcross"
              "autfilt"
              "dstar2tgba"
              "genaut"
              "genltl"
              "ltl2tgba"
              "ltl2tgta"
              "ltlcross"
              "ltldo"
              "ltlfilt"
              "ltlgrind"
              "ltlsynt"
              "randaut"
              "randltl"
            ];

            devShell = pkgs.mkShell {
              name = "spot-dev";
              inputsFrom = [ self.packages.${system}.spotFull ];
              buildInputs = [
                pkgs.gdb

                (pkgs.python3.withPackages (p: [
                  p.jupyter
                  p.ipython # otherwise ipython module isn't found when running ipynb tests
                ]))
              ];
            };
          });
}
