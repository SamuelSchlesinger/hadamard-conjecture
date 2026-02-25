# Hadamard Conjecture: Lean 4 Formalization

Lean 4 formalization work for the classical Hadamard conjecture over integer
matrices.

## Conjecture

Every positive integer `n` divisible by `4` is the order of a Hadamard matrix,
i.e. an `n × n` matrix with entries in `{1, -1}` satisfying

`H * Hᵀ = n I`.

## Current State

This repository currently includes:

- core definitions (`IsHadamardMatrix`, `HasHadamardMatrix`),
- equivalent conjecture formulations (`4 ∣ n` vs `n = 4k`),
- explicit constructions for orders `1` and `2`,
- a fully proved Sylvester/Kronecker doubling theorem,
- a fully proved infinite family theorem for orders `2^k`,
- the final conjecture statement left open as `sorry`.

### Completed Theorems

- `hasHadamardMatrix_one`
- `isHadamardMatrix_two`
- `hasHadamardMatrix_double_of_hasHadamardMatrix`
- `hasHadamardMatrix_pow_two`
- `hadamard_family_pow_two`

## File Layout

```
Hadamard/
  Defs.lean            -- definitions for Hadamard matrices and existence
  Constructions.lean   -- base examples + Sylvester/Kronecker constructions
  EquivalentForms.lean -- equivalent conjecture statements
  Main.lean            -- final conjecture theorem stub
Hadamard.lean          -- top-level imports
```

## Remaining Work

1. Extend constructions beyond powers of two (for example Paley/Williamson families).
2. Add normalization results and equivalence with unnormalized existence where useful.
3. Continue reducing the gap between known families and the full conjecture.
4. Keep `hadamard_conjecture` as the final open target theorem.

## Build

```sh
lake build
```

Requires Lean `v4.28.0` and Mathlib `v4.28.0`.
