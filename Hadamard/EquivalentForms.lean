import Hadamard.Constructions

/-!
# Hadamard Conjecture — Equivalent Forms

Two convenient formulations:
- every order divisible by `4` admits a Hadamard matrix,
- every order of the form `4k` admits a Hadamard matrix.
- the classical admissible-order form (`1`, `2`, or multiple of `4`).

All quantification is over natural numbers.
-/

namespace Hadamard

/-- Multiplicative form: every order `4k` is realizable. -/
def HadamardConjectureMul4 : Prop :=
  ∀ k : ℕ, HasHadamardMatrix (4 * k)

/-- Divisibility form: every order divisible by `4` is realizable. -/
def HadamardConjectureDvd : Prop :=
  ∀ n : ℕ, 4 ∣ n → HasHadamardMatrix n

theorem hadamardConjectureMul4_implies_dvd :
    HadamardConjectureMul4 → HadamardConjectureDvd := by
  intro h n hdiv
  rcases hdiv with ⟨k, rfl⟩
  simpa [Nat.mul_comm] using h k

theorem hadamardConjectureDvd_implies_mul4 :
    HadamardConjectureDvd → HadamardConjectureMul4 := by
  intro h k
  exact h (4 * k) ⟨k, rfl⟩

theorem hadamardConjectureMul4_iff_dvd :
    HadamardConjectureMul4 ↔ HadamardConjectureDvd := by
  constructor
  · exact hadamardConjectureMul4_implies_dvd
  · exact hadamardConjectureDvd_implies_mul4

/-- Classical form: every admissible order (`1`, `2`, or multiple of `4`) is realizable. -/
def HadamardConjectureClassical : Prop :=
  ∀ n : ℕ, HadamardOrderAdmissible n → HasHadamardMatrix n

theorem hadamardConjectureClassical_implies_dvd :
    HadamardConjectureClassical → HadamardConjectureDvd := by
  intro h n hdiv
  exact h n (Or.inr (Or.inr hdiv))

theorem hadamardConjectureDvd_implies_classical :
    HadamardConjectureDvd → HadamardConjectureClassical := by
  intro h n hn
  rcases hn with h1 | h2_or_hdiv
  · subst h1
    exact hasHadamardMatrix_one
  · rcases h2_or_hdiv with h2 | hdiv
    · subst h2
      exact hasHadamardMatrix_two
    · exact h n hdiv

theorem hadamardConjectureDvd_iff_classical :
    HadamardConjectureDvd ↔ HadamardConjectureClassical := by
  constructor
  · exact hadamardConjectureDvd_implies_classical
  · exact hadamardConjectureClassical_implies_dvd

/-- Standard necessary-condition statement from the literature. -/
def HadamardNecessaryCondition : Prop :=
  ∀ n : ℕ, HasHadamardMatrix n → HadamardOrderAdmissible n

/-- Standard determinant characterization statement from the literature. -/
def HadamardDeterminantCharacterization : Prop :=
  ∀ n : ℕ, ∀ H : Matrix (Fin n) (Fin n) ℤ,
    IsHadamardMatrix n H ↔ IsHadamardMatrixDeterminantForm n H

/-- Standard normalization equivalence statement for nonempty orders. -/
def HadamardNormalizationEquivalence : Prop :=
  ∀ n : ℕ, 0 < n → (HasHadamardMatrix n ↔ HasNormalizedHadamardMatrix n)

/-- The project's primary statement of the Hadamard conjecture. -/
abbrev HadamardConjecture : Prop :=
  HadamardConjectureDvd

end Hadamard
