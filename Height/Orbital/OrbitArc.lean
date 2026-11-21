import Height.Orbital.Saturation
import Isotropy.FieldLemma
import Isotropy.DPow

/-!
# Nilpotence exponent for square matrices

This module supplies the bridge from `Matrix.IsNilpotent M` to the fixed
exponent `M ^ n = 0` used by the kernel-flag machinery.
-/

namespace Height.Orbital

open Matrix

universe u

variable {K : Type u} [Field K] {n : ℕ}

/-- Over a field, a nilpotent `n × n` matrix satisfies `M ^ n = 0`
(Cayley–Hamilton plus `charpoly = X ^ n`).  The kernel-flag machinery is
stated with `P ^ n = 0`, so this is the bridge from `IsNilpotent`. -/
theorem pow_card_eq_zero_of_isNilpotent {M : Matrix (Fin n) (Fin n) K}
    (h : IsNilpotent M) : M ^ n = 0 := by
  have hchar : M.charpoly = (Polynomial.X : Polynomial K) ^ n := by
    have h0 : M.charpoly - (Polynomial.X : Polynomial K) ^ (Fintype.card (Fin n)) = 0 :=
      IsNilpotent.eq_zero (Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent h)
    have := sub_eq_zero.mp h0
    simpa using this
  have hCH := M.aeval_self_charpoly
  rw [hchar] at hCH
  simpa using hCH

end Height.Orbital
