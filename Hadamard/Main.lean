import Hadamard.Constructions
import Hadamard.EquivalentForms

/-!
# Hadamard Conjecture — Main Results and Conjecture Stub
-/

namespace Hadamard

/-- Confirmed infinite family: powers of two admit Hadamard matrices. -/
theorem hadamard_family_pow_two (k : ℕ) : HasHadamardMatrix (2 ^ k) :=
  hasHadamardMatrix_pow_two k

/-- The project's primary conjecture is equivalent to the classical `1/2/4k` form. -/
theorem hadamard_conjecture_iff_classical :
    HadamardConjecture ↔ HadamardConjectureClassical :=
  hadamardConjectureDvd_iff_classical

/--
**Hadamard conjecture**: every `n` divisible by `4` admits an `n × n`
Hadamard matrix (formalized over `n : ℕ`).
-/
theorem hadamard_conjecture : HadamardConjecture := by
  sorry

end Hadamard
