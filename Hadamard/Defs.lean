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

/-- Classical admissible orders for real Hadamard matrices: `1`, `2`, or a multiple of `4`. -/
def HadamardOrderAdmissible (n : ℕ) : Prop :=
  n = 1 ∨ n = 2 ∨ 4 ∣ n

/-- Normalized Hadamard matrices have all first-row/first-column entries equal to `1`. -/
def IsNormalizedHadamardMatrix (n : ℕ) (H : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  IsHadamardMatrix n H ∧ ∀ i j, (i.1 = 0 ∨ j.1 = 0) → H i j = 1

/-- Existence predicate for normalized Hadamard matrices of order `n`. -/
def HasNormalizedHadamardMatrix (n : ℕ) : Prop :=
  ∃ H : Matrix (Fin n) (Fin n) ℤ, IsNormalizedHadamardMatrix n H

/-- Determinant-form characterization used in the literature. -/
def IsHadamardMatrixDeterminantForm (n : ℕ) (H : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  (∀ i j, H i j = 1 ∨ H i j = -1) ∧ Int.natAbs (Matrix.det H) = n ^ (n / 2)

theorem IsNormalizedHadamardMatrix.isHadamard
    {n : ℕ} {H : Matrix (Fin n) (Fin n) ℤ}
    (hH : IsNormalizedHadamardMatrix n H) : IsHadamardMatrix n H :=
  hH.1

theorem hasHadamardMatrix_of_hasNormalizedHadamardMatrix
    {n : ℕ} (h : HasNormalizedHadamardMatrix n) : HasHadamardMatrix n := by
  rcases h with ⟨H, hH⟩
  exact ⟨H, hH.isHadamard⟩

end Hadamard
