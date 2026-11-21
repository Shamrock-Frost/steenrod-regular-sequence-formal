import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-!
# Dimension bound for isotropic subspaces (`lem:residue-form`, `lem:divided-form`)

The residue and divided-residue arguments both end with this finite-dimensional
linear-algebra inequality.
-/

namespace Height.Toolbox

universe u v

variable {K : Type u} [Field K]
variable {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- A totally isotropic subspace of a nondegenerate bilinear space has at
most half the ambient dimension.  This formulation works in characteristic
two and does not infer alternation from skew-symmetry. -/
theorem finrank_isotropic_le_half
    (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate)
    (W : Submodule K V)
    (hW : ∀ x ∈ W, ∀ y ∈ W, B x y = 0) :
    2 * Module.finrank K W ≤ Module.finrank K V := by
  have hsub : W ≤ B.orthogonal W := by
    intro y hy x hx
    exact hW x hx y hy
  have hle := Submodule.finrank_mono hsub
  rw [B.finrank_orthogonal hB W] at hle
  have hdim := Submodule.finrank_le W
  omega

end Height.Toolbox
