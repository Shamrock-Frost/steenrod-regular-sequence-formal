import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.Algebra.Module.SpanRankOperations

/-!
# Embedding dimension

For a Noetherian local ring the Krull dimension is at most the dimension of the
Zariski cotangent space `𝔪/𝔪²` over the residue field (Krull's height theorem
`ringKrullDim_le_ringKrullDim_quotient_add_spanFinrank` with `I = 𝔪`, and
`spanFinrank_maximalIdeal_eq_finrank_cotangentSpace`).  Equality is
`IsRegularLocalRing.iff_finrank_cotangentSpace`.  A mathlib candidate.
-/

namespace Height.Toolbox

open IsLocalRing

variable (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-! ### Embedding dimension -/

/-- **Embedding-dimension bound**: `dim R ≤ dim_κ 𝔪/𝔪²`. -/
theorem ringKrullDim_le_finrank_cotangentSpace :
    ringKrullDim R ≤ Module.finrank (ResidueField R) (CotangentSpace R) := by
  rw [← spanFinrank_maximalIdeal_eq_finrank_cotangentSpace R]
  exact ringKrullDim_le_spanFinrank_maximalIdeal R


variable {R} in
/-- The dimension of the Zariski cotangent space is invariant under a ring equivalence: both
sides are the `spanFinrank` of the maximal ideal (`IsLocalRing.map_ringEquiv_maximalIdeal`
and `Ideal.spanFinrank_map_eq_of_ringEquiv`).  A mathlib candidate. -/
theorem finrank_cotangentSpace_of_ringEquiv {R' : Type*} [CommRing R'] [IsLocalRing R']
    (e : R ≃+* R') :
    Module.finrank (ResidueField R) (CotangentSpace R) =
      Module.finrank (ResidueField R') (CotangentSpace R') := by
  have := isNoetherianRing_of_ringEquiv R e
  rw [← spanFinrank_maximalIdeal_eq_finrank_cotangentSpace,
    ← spanFinrank_maximalIdeal_eq_finrank_cotangentSpace,
    ← map_ringEquiv_maximalIdeal e, Ideal.spanFinrank_map_eq_of_ringEquiv]

end Height.Toolbox
