import Hadamard.Defs

/-!
# Hadamard Conjecture — First Constructions

This file contains baseline constructions and proved theorems for the
Sylvester/Kronecker doubling pipeline.
-/

namespace Hadamard

open scoped Kronecker

/-- The unique `1 × 1` Hadamard matrix. -/
def hadamardOne : Matrix (Fin 1) (Fin 1) ℤ :=
  fun _ _ => 1

theorem isHadamardMatrix_one : IsHadamardMatrix 1 hadamardOne := by
  constructor
  · intro i j
    left
    simp [hadamardOne]
  · ext i j
    fin_cases i
    fin_cases j
    simp [hadamardOne, Matrix.mul_apply]

theorem hasHadamardMatrix_one : HasHadamardMatrix 1 :=
  ⟨hadamardOne, isHadamardMatrix_one⟩

/-- The `2 × 2` Sylvester seed matrix. -/
def sylvesterTwo : Matrix (Fin 2) (Fin 2) ℤ :=
  !![1, 1; 1, -1]

lemma sylvesterTwo_entry (i j : Fin 2) :
    sylvesterTwo i j = 1 ∨ sylvesterTwo i j = -1 := by
  fin_cases i <;> fin_cases j <;> simp [sylvesterTwo]

theorem isHadamardMatrix_two : IsHadamardMatrix 2 sylvesterTwo := by
  constructor
  · intro i j
    exact sylvesterTwo_entry i j
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num [sylvesterTwo, Matrix.mul_apply]

theorem hasHadamardMatrix_two : HasHadamardMatrix 2 :=
  ⟨sylvesterTwo, isHadamardMatrix_two⟩

lemma mul_eq_one_or_neg_one_of_eq_one_or_neg_one {a b : ℤ}
    (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) :
    a * b = 1 ∨ a * b = -1 := by
  rcases ha with ha | ha
  · rcases hb with hb | hb
    · left
      simp [ha, hb]
    · right
      simp [ha, hb]
  · rcases hb with hb | hb
    · right
      simp [ha, hb]
    · left
      simp [ha, hb]

theorem hasHadamardMatrix_double_of_hasHadamardMatrix
    {n : ℕ} (h : HasHadamardMatrix n) : HasHadamardMatrix (2 * n) := by
  rcases h with ⟨H, hH⟩
  rcases hH with ⟨hH_entry, hH_orth⟩
  let e : Fin 2 × Fin n ≃ Fin (2 * n) := finProdFinEquiv
  refine ⟨Matrix.reindex e e (sylvesterTwo ⊗ₖ H), ?_⟩
  constructor
  · intro i j
    change (sylvesterTwo ⊗ₖ H) (e.symm i) (e.symm j) = 1 ∨
        (sylvesterTwo ⊗ₖ H) (e.symm i) (e.symm j) = -1
    rcases e.symm i with ⟨i₁, i₂⟩
    rcases e.symm j with ⟨j₁, j₂⟩
    change sylvesterTwo i₁ j₁ * H i₂ j₂ = 1 ∨ sylvesterTwo i₁ j₁ * H i₂ j₂ = -1
    exact mul_eq_one_or_neg_one_of_eq_one_or_neg_one (sylvesterTwo_entry i₁ j₁) (hH_entry i₂ j₂)
  · have hKroneckerOrth :
        (sylvesterTwo ⊗ₖ H) * (sylvesterTwo ⊗ₖ H).transpose =
          (2 * n : ℤ) • (1 : Matrix (Fin 2 × Fin n) (Fin 2 × Fin n) ℤ) := by
      have hTwoOrth :
          sylvesterTwo * sylvesterTwo.transpose =
            ((2 : ℕ) : ℤ) • (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
        simpa using isHadamardMatrix_two.2
      calc
        (sylvesterTwo ⊗ₖ H) * (sylvesterTwo ⊗ₖ H).transpose
            = (sylvesterTwo ⊗ₖ H) * (sylvesterTwo.transpose ⊗ₖ H.transpose) := by
                rw [← Matrix.kroneckerMap_transpose (f := fun a b : ℤ => a * b) sylvesterTwo H]
        _ = (sylvesterTwo * sylvesterTwo.transpose) ⊗ₖ (H * H.transpose) := by
              simpa using
                (Matrix.mul_kronecker_mul sylvesterTwo sylvesterTwo.transpose H H.transpose).symm
        _ = ((((2 : ℕ) : ℤ) • (1 : Matrix (Fin 2) (Fin 2) ℤ)) ⊗ₖ
              ((n : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ))) := by
              rw [hTwoOrth, hH_orth]
        _ = (((2 : ℕ) : ℤ)) •
              ((1 : Matrix (Fin 2) (Fin 2) ℤ) ⊗ₖ ((n : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ))) := by
              simpa using
                (Matrix.smul_kronecker (r := (((2 : ℕ) : ℤ)))
                  (A := (1 : Matrix (Fin 2) (Fin 2) ℤ))
                  (B := ((n : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ))))
        _ = (((2 : ℕ) : ℤ)) •
              ((n : ℤ) • ((1 : Matrix (Fin 2) (Fin 2) ℤ) ⊗ₖ
                (1 : Matrix (Fin n) (Fin n) ℤ))) := by
              rw [Matrix.kronecker_smul (r := (n : ℤ))
                (A := (1 : Matrix (Fin 2) (Fin 2) ℤ))
                (B := (1 : Matrix (Fin n) (Fin n) ℤ))]
        _ = ((((2 : ℕ) : ℤ) * (n : ℤ))) •
              ((1 : Matrix (Fin 2) (Fin 2) ℤ) ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℤ)) := by
              simp
        _ = ((((2 : ℕ) : ℤ) * (n : ℤ))) •
              (1 : Matrix (Fin 2 × Fin n) (Fin 2 × Fin n) ℤ) := by
              rw [Matrix.one_kronecker_one]
        _ = (2 * n : ℤ) • (1 : Matrix (Fin 2 × Fin n) (Fin 2 × Fin n) ℤ) := by
              norm_num [Nat.cast_mul]
    calc
      (Matrix.reindex e e (sylvesterTwo ⊗ₖ H)) *
          (Matrix.reindex e e (sylvesterTwo ⊗ₖ H)).transpose
          = Matrix.reindex e e
              ((sylvesterTwo ⊗ₖ H) * (sylvesterTwo ⊗ₖ H).transpose) := by
              rw [Matrix.transpose_reindex]
              exact
                (Matrix.reindexAlgEquiv_mul (R := ℤ) (A := ℤ) e
                  (sylvesterTwo ⊗ₖ H) ((sylvesterTwo ⊗ₖ H).transpose)).symm
      _ = Matrix.reindex e e
            ((2 * n : ℤ) • (1 : Matrix (Fin 2 × Fin n) (Fin 2 × Fin n) ℤ)) := by
            rw [hKroneckerOrth]
      _ = (2 * n : ℤ) • (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℤ) := by
            calc
              Matrix.reindex e e ((2 * n : ℤ) •
                  (1 : Matrix (Fin 2 × Fin n) (Fin 2 × Fin n) ℤ))
                  = Matrix.reindexLinearEquiv ℤ ℤ e e ((2 * n : ℤ) •
                      (1 : Matrix (Fin 2 × Fin n) (Fin 2 × Fin n) ℤ)) := by
                      simp [Matrix.reindexLinearEquiv_apply]
              _ = (2 * n : ℤ) • Matrix.reindexLinearEquiv ℤ ℤ e e
                    (1 : Matrix (Fin 2 × Fin n) (Fin 2 × Fin n) ℤ) := by
                    simpa using
                      (Matrix.reindexLinearEquiv ℤ ℤ e e).map_smul (2 * n : ℤ)
                        (1 : Matrix (Fin 2 × Fin n) (Fin 2 × Fin n) ℤ)
              _ = (2 * n : ℤ) • (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℤ) := by
                    simp [Matrix.reindexLinearEquiv_apply]

theorem hasHadamardMatrix_pow_two (k : ℕ) : HasHadamardMatrix (2 ^ k) := by
  induction k with
  | zero =>
      simpa using hasHadamardMatrix_one
  | succ k hk =>
      simpa [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
        hasHadamardMatrix_double_of_hasHadamardMatrix hk

end Hadamard
