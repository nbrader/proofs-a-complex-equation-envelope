# Complex Envelope Rocq Formalization

This directory contains a Rocq (formerly Coq) formalization of the proof for the complex equation envelope problem.

## Project Structure

- `ComplexEnvelope.v` - Main proof file formalizing the equation a·E·Ē + b·Ē + c = 0
- `_CoqProject` - Coq/Rocq project configuration
- `dune-project` - Dune project configuration
- `dune` - Dune build file

## Building the Project

### Using the build script (Recommended - provides detailed feedback)

```bash
# Build with Dune (default, verbose output)
./build_coq.sh

# Build with Make (alternative, verbose output)
./build_coq.sh make
```

The build script provides:
- Environment setup for rocq-8.18.0
- Verbose progress feedback
- Build summaries
- Error handling

### Using Dune directly

```bash
# Standard build
dune build

# Verbose build
dune build --verbose --display=short
```

### Using Make directly with _CoqProject

```bash
coq_makefile -f _CoqProject -o Makefile
make
```

### Using Rocq/Coq directly

```bash
coqc ComplexEnvelope.v
```

## Requirements

- Rocq/Coq >= 8.16
- Dune >= 3.8 (if using Dune build system)

## Project Description

This formalization proves conditions under which the equation:

```
a·E·Ē + b·Ē + c = 0
```

has solutions for E ∈ ℂ, where Ē denotes the complex conjugate of E.

The proof analyzes:
1. The case when a = 0
2. The case when a ≠ 0 (envelope analysis)

## Development

To work with this project in your favorite Rocq/Coq IDE (CoqIDE, Proof General, VSCoq, etc.), ensure the `_CoqProject` file is recognized by your editor.
