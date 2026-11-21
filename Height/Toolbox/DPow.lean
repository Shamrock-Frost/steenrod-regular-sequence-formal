import Isotropy.DPow

/-!
# Derivatives of powers along commutators (`prop:transporter`)

The proof of `prop:transporter` differentiates the lift equation `y^c u =
y^{c-1} v`; the derivative of a power is `D_ẏ(y^m) = Σ_{i+j=m-1} y^i ẏ y^j`,
and for `ẏ = [γ, y]` that sum telescopes to `[γ, y^m]`.  This file is that
telescoping, `leibniz_dpow`, on top of
`Isotropy.dpow`; no duplicate definition is introduced here.
-/

namespace Height.Toolbox

open Matrix
open Isotropy

variable {K : Type*} [CommRing K] {n : ℕ}

/-- The Leibniz step of `prop:transporter`: differentiating a power in a
commutator direction again gives a commutator. -/
theorem leibniz_dpow (y γ : Matrix (Fin n) (Fin n) K) (m : ℕ) :
    dpow y (γ * y - y * γ) m = γ * y ^ m - y ^ m * γ := by
  have dpow_neg (Q : Matrix (Fin n) (Fin n) K) :
      dpow y (-Q) m = -dpow y Q m := by
    simp only [dpow, mul_neg, neg_mul, Finset.sum_neg_distrib]
  rw [show γ * y - y * γ = -(y * γ - γ * y) by abel, dpow_neg,
    dpow_commutator]
  abel

end Height.Toolbox
