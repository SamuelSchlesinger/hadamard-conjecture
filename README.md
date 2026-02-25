# Hadamard Conjecture: Lean 4 Formalization

Lean 4 formalization work for the classical Hadamard conjecture over integer
matrices.

## Conjecture

Classically, this is stated as:

- for every admissible order `n` (`n = 1`, `n = 2`, or `4 ∣ n`),
  there exists an `n × n` Hadamard matrix.

In this repository, the primary conjecture is represented in the equivalent
Lean-friendly form over natural numbers:

- for every `n : ℕ`, if `4 ∣ n`, then there exists an `n × n` Hadamard matrix.

`H * Hᵀ = n I`.

Note: this formulation includes `n = 0` because the quantification is over
`ℕ`.

## Current State

This repository currently includes:

- core definitions (`IsHadamardMatrix`, `HasHadamardMatrix`),
- equivalent conjecture formulations (`4 ∣ n`, `n = 4k`, and classical `1/2/4k`),
- explicit constructions for orders `1` and `2`,
- a fully proved Sylvester/Kronecker doubling theorem,
- a fully proved infinite family theorem for orders `2^k`,
- literature-aligned statement objects:
  `HadamardNecessaryCondition`,
  `HadamardDeterminantCharacterization`,
  `HadamardNormalizationEquivalence`,
- the final conjecture statement left open as `sorry`.

### Completed Theorems

- `hasHadamardMatrix_one`
- `isHadamardMatrix_two`
- `hasHadamardMatrix_two`
- `hasHadamardMatrix_double_of_hasHadamardMatrix`
- `hasHadamardMatrix_pow_two`
- `hadamard_family_pow_two`
- `hadamard_conjecture_iff_classical`

## File Layout

```
Hadamard/
  Defs.lean            -- core definitions + normalized/determinant predicates
  Constructions.lean   -- base examples + Sylvester/Kronecker constructions
  EquivalentForms.lean -- equivalent conjecture forms + literature statements
  Main.lean            -- proved infinite family + open conjecture theorem
Hadamard.lean          -- top-level imports
```

## Remaining Work

1. Extend constructions beyond powers of two (for example Paley/Williamson families).
2. Prove `HadamardNormalizationEquivalence` for nonempty orders.
3. Prove `HadamardDeterminantCharacterization`.
4. Formalize/prove `HadamardNecessaryCondition`.
5. Continue reducing the gap between known families and the full conjecture.
6. Keep `hadamard_conjecture` as the final open target theorem.

## Build

```sh
lake build
```

Requires Lean `v4.28.0` and Mathlib `v4.28.0`.

## References

- SageMath Hadamard matrix documentation:
  <https://doc.sagemath.org/html/en/reference/combinat/sage/combinat/matrices/hadamard_matrix.html>
- Survey: Browne, Egan, Hegarty, Ó Catháin,
  *A survey of the Hadamard conjecture* (2021),
  <https://arxiv.org/abs/2104.06756>
- Database/status paper: Cati, Pasechnik,
  *The Hadamard Matrix Database* (2024/2025),
  <https://arxiv.org/abs/2411.18897>
