import Hadamard.Defs

/-!
# Hadamard Conjecture — Equivalent Forms

Two convenient formulations:
- every order divisible by `4` admits a Hadamard matrix,
- every order of the form `4k` admits a Hadamard matrix.
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

/-- The project's primary statement of the Hadamard conjecture. -/
abbrev HadamardConjecture : Prop :=
  HadamardConjectureDvd

end Hadamard
