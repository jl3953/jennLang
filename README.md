# Turnpike

The repository is organized as follows:

```
bin/            # main.ml and CRAQ specifications (for example, CRAQ.jenn) here
lib/            # compiler front-end (lexer, parser, ast) here + Zak's simulator
README.md       
jennLang.opam   # ignore
output.csv      # main.ml generates trace to this file, to be passed to python script
'''

## Getting started

Please build and install dependencies following instructions:


Install OCaml and Dune.
```
# install OCaml
bash -c "sh <(curl -fsSL https://raw.githubusercontent.com/ocaml/opam/master/shell/install.sh)"
opam init 

# install Dune
opam install ocaml-lsp-server odoc ocamlformat utop
```

Clone this repository, and run the simulator.
```
git clone https://github.com/jl3953/jennLang # clone
dune exec \_build/default/bin/main.exe # run
```


```
eval $(opam env --switch=default)
```
