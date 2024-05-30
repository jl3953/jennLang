# Turnpike

The repository is organized as follows:

```
bin/            # main.ml and CRAQ specifications (for example, CRAQ.jenn) here
lib/            # compiler front-end (lexer, parser, ast) here + simulator
README.md       
jennLang.opam   # ignore
output.csv      # main.ml generates trace to this file, to be passed to python script
```

## Getting started

Install [OCaml](https://ocaml.org/install).
```
bash -c "sh <(curl -fsSL https://raw.githubusercontent.com/ocaml/opam/master/shell/install.sh)"
opam init 
```

Install [Dune](https://dune.build/).
```
opam install ocaml-lsp-server odoc ocamlformat utop
```

Clone this repository, and run the simulator.
```
git clone https://github.com/jl3953/jennLang # clone
dune exec \\_build/default/bin/main.exe # run
```


```
eval $(opam env --switch=default)
```
