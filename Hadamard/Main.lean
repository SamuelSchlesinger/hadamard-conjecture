import Hadamard.Constructions
import Hadamard.EquivalentForms

/-!
# Hadamard Conjecture — Main Theorem Stub
-/

namespace Hadamard

/-- Confirmed infinite family: powers of two admit Hadamard matrices. -/
theorem hadamard_family_pow_two (k : ℕ) : HasHadamardMatrix (2 ^ k) :=
  hasHadamardMatrix_pow_two k

/--
**Hadamard conjecture**: every `n` divisible by `4` admits an `n × n`
Hadamard matrix.
-/
theorem hadamard_conjecture : HadamardConjecture := by
  sorry

end Hadamard
