# Installation and Compilation Guide

## Prerequisites

- Rocq/Coq ≥ 8.16 (8.18 recommended)
- Opam for installing Rocq/Coq (or system packages on your OS)

## Quick Install (opam)

```bash
opam switch create rocq-8.18.0 ocaml-base-compiler.4.14.0
eval $(opam env --switch=rocq-8.18.0)
opam install coq.8.18.0
```

## Build

```bash
cd Rocq
# Using coqc directly
coqc ComplexEnvelope.v

# Or using Makefile
coq_makefile -f _CoqProject -o Makefile
make
```

The main file `ComplexEnvelope.v` now compiles without admits.
