import Height.Toolbox.DPow

/-!
# The first-order equation for an arc in a chain stratum

This is the algebraic coefficient calculation `tangent_equation`.
The existence of the lifted vector over the power-series DVR is a
separate saturation statement; once its constant and linear coefficients are
known, the argument here is characteristic-free.
-/

namespace Height.Orbital

open Matrix
open Isotropy
open Height.Toolbox

variable {K : Type*} [CommRing K] {n : ℕ}

/-- `prop:transporter`, coefficient-of-`s` calculation.  If the constant
equation is `y^c u = y^(c-1) v`, its derivative in a commutator direction
forces the residual last-column velocity into `K_c(y)`. -/
theorem tangent_equation (y dy γ : Matrix (Fin n) (Fin n) K)
    (u du v dv : Fin n → K) (c : ℕ)
    (hdy : dy = γ * y - y * γ)
    (hbase : (y ^ c).mulVec u = (y ^ (c - 1)).mulVec v)
    (htangent :
      (dpow y dy (c - 1)).mulVec v + (y ^ (c - 1)).mulVec dv =
        (dpow y dy c).mulVec u + (y ^ c).mulVec du) :
    (y ^ (c - 1)).mulVec (dv - γ.mulVec v) =
      (y ^ c).mulVec (du - γ.mulVec u) := by
  subst dy
  rw [leibniz_dpow, leibniz_dpow] at htangent
  simp only [sub_mulVec] at htangent ⊢
  simp_rw [← mulVec_mulVec] at htangent
  rw [← hbase] at htangent
  change (y ^ (c - 1)).mulVecLin (dv - γ.mulVec v) =
    (y ^ c).mulVecLin (du - γ.mulVec u)
  rw [map_sub, map_sub]
  change (y ^ (c - 1)).mulVec dv - (y ^ (c - 1)).mulVec (γ.mulVec v) =
    (y ^ c).mulVec du - (y ^ c).mulVec (γ.mulVec u)
  abel_nf at htangent ⊢
  exact add_left_cancel htangent

end Height.Orbital
