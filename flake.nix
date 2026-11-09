
{
  description = "Разработка булевой алгебры и логики на Rocq Prover";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        # Используем стабильную/последнюю версию пакетов Rocq (Coq)
        rocqPackages = pkgs.rocqPackages; 
      in
      {
        devShells.default = pkgs.mkShell {
          buildInputs = [
            rocqPackages.coq      # Сам компилятор (coqc / rocqc)
            rocqPackages.rocqide   # Стандартная IDE, если нужна
            pkgs.dune_3           # Современная система сборки для Rocq проектов
          ];

          shellHook = ''
            echo "=== Окружение Rocq Prover (Nix Flake) успешно загружено ==="
            echo "Версия компилятора: $(coqc --version)"
          '';
        };
      });
}

