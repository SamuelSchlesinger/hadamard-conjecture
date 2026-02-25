import Mathlib

/-!
# Hadamard Conjecture — Core Definitions

This file defines Hadamard matrices over `ℤ` using the classical `±1`
entry condition and orthogonality equation.
-/

namespace Hadamard

/-- A square `n × n` integer matrix is Hadamard if every entry is `±1`
and `H * Hᵀ = n I`. -/
def IsHadamardMatrix (n : ℕ) (H : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  (∀ i j, H i j = 1 ∨ H i j = -1) ∧
    H * H.transpose = (n : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ)

/-- Existence predicate for Hadamard matrices of order `n`. -/
def HasHadamardMatrix (n : ℕ) : Prop :=
  ∃ H : Matrix (Fin n) (Fin n) ℤ, IsHadamardMatrix n H

end Hadamard
