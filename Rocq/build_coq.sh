#!/bin/bash

set -e  # Exit on error

echo "=========================================="
echo "Building Rocq Project: ComplexEnvelope"
echo "=========================================="
echo ""

# Ensure we use the same opam switch as the IDE (rocq-8.18.0)
echo "Setting up opam environment (rocq-8.18.0)..."
eval $(opam env --switch=rocq-8.18.0)
echo "✓ Environment configured"
echo ""

# Choose build method: dune (default) or make
BUILD_METHOD=${1:-dune}

if [ "$BUILD_METHOD" = "dune" ]; then
    echo "Building with Dune (verbose mode)..."
    echo "------------------------------------------"
    dune clean
    dune build --verbose --display=short
    echo ""
    echo "✓ Build completed successfully with Dune"
elif [ "$BUILD_METHOD" = "make" ]; then
    echo "Building with Make (verbose mode)..."
    echo "------------------------------------------"

    # Clean up old build artifacts
    echo "Cleaning old build artifacts..."
    make clean 2>/dev/null || true

    # Generate Makefile from _CoqProject
    echo "Generating Makefile from _CoqProject..."
    coq_makefile -f _CoqProject -o Makefile
    echo "✓ Makefile generated"
    echo ""

    # Build the project using the generated Makefile
    echo "Compiling Rocq files..."
    make
    echo ""
    echo "✓ Build completed successfully with Make"
else
    echo "Error: Unknown build method '$BUILD_METHOD'"
    echo "Usage: $0 [dune|make]"
    exit 1
fi

echo ""
echo "=========================================="
echo "Build Summary"
echo "=========================================="
echo "Build method: $BUILD_METHOD"
echo "Files compiled: ComplexEnvelope.v"
echo "Output location: _build/ (dune) or .vo/.glob files (make)"
echo ""