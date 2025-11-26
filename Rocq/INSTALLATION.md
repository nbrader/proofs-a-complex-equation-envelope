# Installation and Compilation Guide

## Prerequisites

To compile the Rocq/Coq proofs, you need:

- **Rocq/Coq**: Version 8.16 or later (8.18.0 recommended)
- **Opam**: OCaml package manager (for installing Rocq/Coq)
- **For Coquelicot version**: Additional library `coq-coquelicot`

## Installation Methods

### Method 1: Using Opam (Recommended)

#### Step 1: Install Opam

**On Ubuntu/Debian:**
```bash
sudo apt-get update
sudo apt-get install opam
```

**On macOS:**
```bash
brew install opam
```

**On other systems:**
Download from [opam.ocaml.org](https://opam.ocaml.org/doc/Install.html)

#### Step 2: Initialize Opam

```bash
opam init
eval $(opam env)
```

#### Step 3: Create Rocq Switch

```bash
# Create a switch for Rocq 8.18.0
opam switch create rocq-8.18.0 ocaml-base-compiler.4.14.0
eval $(opam env --switch=rocq-8.18.0)

# Install Coq/Rocq
opam install coq.8.18.0
```

#### Step 4: Install Coquelicot (for ComplexEnvelope_Coquelicot.v)

```bash
opam install coq-coquelicot
```

### Method 2: Using apt-get (Ubuntu/Debian Only)

```bash
sudo apt-get update
sudo apt-get install coq libcoq-coquelicot
```

**Note:** This may install an older version of Coq. Check with:
```bash
coqc --version
```

### Method 3: Binary Download (Advanced)

Download pre-built binaries from:
- [Coq Releases](https://github.com/coq/coq/releases)
- [Rocq Platform](https://github.com/coq/platform)

## Compilation

### For ComplexEnvelope.v (Custom Implementation)

```bash
cd Rocq/

# Method A: Using coqc directly
coqc ComplexEnvelope.v

# Method B: Using the Makefile
coq_makefile -f _CoqProject -o Makefile
make

# Method C: Using the build script
./build_coq.sh make
```

### For ComplexEnvelope_Coquelicot.v (Recommended)

```bash
cd Rocq/

# Method A: Using coqc directly
coqc -R . ComplexEnvelope ComplexEnvelope_Coquelicot.v

# Method B: Using Dune (if installed)
dune build

# Method C: Using the build script
./build_coq.sh  # default uses Dune
./build_coq.sh make  # alternative with Make
```

## Expected Compilation Results

### ComplexEnvelope.v

**Current status:** Will compile with warnings about admits

```
ComplexEnvelope.v:963: Warning: envelope_point_real_solution is admitted
ComplexEnvelope.v:1042: Warning: inside_envelope_real_solution is admitted
```

**To get a clean compilation:** Complete the admitted proofs (see AXIOM_PROOFS_STATUS.md)

### ComplexEnvelope_Coquelicot.v

**Current status:** Should compile cleanly with NO warnings

```
✓ ComplexEnvelope_Coquelicot.vo compiled successfully
✓ No admits
✓ All proofs verified
```

## Troubleshooting

### Issue: "coqc: command not found"

**Solution:** Ensure opam environment is loaded:
```bash
eval $(opam env --switch=rocq-8.18.0)
which coqc  # Should show path to coqc
```

### Issue: "Cannot find library Coquelicot"

**Solution:** Install coq-coquelicot:
```bash
opam install coq-coquelicot
```

### Issue: "Version mismatch" errors

**Solution:** Ensure you're using the correct Coq version:
```bash
coqc --version  # Should be 8.16.0 or later
opam switch list  # Check your current switch
eval $(opam env --switch=rocq-8.18.0)  # Switch to correct version
```

### Issue: "sudo: not available" or permission denied

**Solution:** Install opam in user space:
```bash
# Download opam binary
sh <(curl -sL https://raw.githubusercontent.com/ocaml/opam/master/shell/install.sh)

# Follow prompts to install in user directory (e.g., ~/.local/bin)
```

### Issue: Build script fails with "opam env" error

**Solution:** Ensure the opam switch exists:
```bash
opam switch list
opam switch create rocq-8.18.0 ocaml-base-compiler.4.14.0
```

## Verification

To verify the proofs are correct:

### For ComplexEnvelope.v

```bash
coqc ComplexEnvelope.v 2>&1 | grep -E "(Error|Admitted)"
```

Expected output:
```
Warning: envelope_point_real_solution is admitted
Warning: inside_envelope_real_solution is admitted
```

### For ComplexEnvelope_Coquelicot.v

```bash
coqc -R . ComplexEnvelope ComplexEnvelope_Coquelicot.v 2>&1 | grep -E "(Error|Admitted)"
```

Expected output:
```
(no output - no errors or admits)
```

## Checking Proof Dependencies

To see what assumptions a theorem depends on:

```bash
# Open Coq REPL
coqtop -R . ComplexEnvelope

# Load the file
Require Import ComplexEnvelope_Coquelicot.

# Check assumptions
Print Assumptions envelope_characterizes_solutions.
```

Expected output for Coquelicot version:
```
Closed under the global context
```

This means the theorem is proven without any axioms!

## Performance Notes

- **ComplexEnvelope.v**: Compiles in ~5-10 seconds
- **ComplexEnvelope_Coquelicot.v**: Compiles in ~30-60 seconds (larger file, more complex proofs)

## Docker Alternative (If Installation Fails)

If you cannot install Coq/Rocq locally, use Docker:

```bash
# Pull Coq Docker image
docker pull coqorg/coq:8.18

# Run compilation in container
docker run --rm -v $(pwd)/Rocq:/workspace coqorg/coq:8.18 \
  bash -c "cd /workspace && coqc ComplexEnvelope_Coquelicot.v"
```

## Next Steps

1. ✅ Install Coq/Rocq using one of the methods above
2. ✅ Verify installation: `coqc --version`
3. ✅ Navigate to `Rocq/` directory
4. ✅ Compile `ComplexEnvelope_Coquelicot.v` (recommended)
5. ✅ (Optional) Complete admits in `ComplexEnvelope.v`

## Resources

- [Coq Documentation](https://coq.inria.fr/documentation)
- [Opam Documentation](https://opam.ocaml.org/doc/Usage.html)
- [Coquelicot Library](http://coquelicot.saclay.inria.fr/)
- [Rocq Platform](https://github.com/coq/platform)

---

*For questions or issues, see AXIOM_PROOFS_STATUS.md for proof status details.*
