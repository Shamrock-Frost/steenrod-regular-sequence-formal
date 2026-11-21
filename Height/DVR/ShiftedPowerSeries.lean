import Height.DVR.Residue

/-!
# Shifted evaluation in the local model `K⟦u⟧`

In the local model, `R = PowerSeries K`,
`L = LaurentSeries K`, and `u = X`.  The residue identity used by
`cor:shifted-eval`, `res_x u^{-1} f\,du = \bar f`, identifies reduction with
the constant term and is recorded below as `constantCoeff_eq_residue`.
-/

namespace Height.DVR

open Matrix

universe u

variable {K : Type u} [Field K]

section Residue

/-- `cor:shifted-eval`, residue half: for an integral `f`, the residue of
`u^{-1} f\,du` is the reduction `\bar f`, i.e. the constant term. -/
theorem constantCoeff_eq_residue (f : PowerSeries K) :
    laurentResidue K
        (uInvPow K 1 * algebraMap (PowerSeries K) (LaurentSeries K) f) =
      PowerSeries.constantCoeff f := by
  simpa using laurentResidue_uInvPow_mul (K := K) 1 le_rfl f

end Residue

end Height.DVR
