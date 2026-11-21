import Height.DVR.ResidueDirectSum
import Mathlib.LinearAlgebra.BilinearForm.IsometryEquiv

/-!
# Transfer from a hyperbolic residue-block decomposition

The hard DVR input is the existence of a hyperbolic block decomposition.
This file proves all residue-form consequences from the precise linear
isometry supplied by such a decomposition.
-/

namespace Height.DVR

universe u v w x

variable {K : Type u} [Field K]
variable {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {ι : Type w} [Fintype ι]

omit [FiniteDimensional K V] in
/-- Nondegeneracy transfers back across a residue-block isometry. -/
theorem residueForm_nondegenerate_of_isometry (B : LinearMap.BilinForm K V)
    (m : ι → ℕ)
    (e : B.IsometryEquiv (residueDirectSumBilinForm (K := K) m)) :
    B.Nondegenerate := by
  have hblock :=
    (residueDirectSumBilinForm_alt_nondegenerate (K := K) m).2
  constructor
  · intro x hx
    apply e.injective
    have hz : e x = 0 := hblock.1 (e x) fun z => by
      obtain ⟨y, rfl⟩ := e.surjective z
      change residueDirectSumBilinForm m (e x) (e y) = 0
      rw [e.map_app]
      exact hx y
    simpa using hz
  · intro y hy
    apply e.injective
    have hz : e y = 0 := hblock.2 (e y) fun z => by
      obtain ⟨x, rfl⟩ := e.surjective z
      change residueDirectSumBilinForm m (e x) (e y) = 0
      rw [e.map_app]
      exact hy x
    simpa using hz

omit [FiniteDimensional K V] in
/-- A residue-block isometry determines the dimension of its source. -/
theorem finrank_eq_sum_residueBlocks_of_isometry
    (B : LinearMap.BilinForm K V) (m : ι → ℕ)
    (e : B.IsometryEquiv (residueDirectSumBilinForm (K := K) m)) :
    Module.finrank K V = ∑ i, 2 * m i := by
  rw [e.toLinearEquiv.finrank_eq]
  exact finrank_residueBlockFamily (K := K) m

/-- Once the hyperbolic normal form is supplied, every isotropic subspace of
the original residue space has at most half its block dimension. -/
theorem residueForm_isotropic_bound_of_isometry
    (B : LinearMap.BilinForm K V) (m : ι → ℕ)
    (e : B.IsometryEquiv (residueDirectSumBilinForm (K := K) m))
    (W : Submodule K V)
    (hW : ∀ x ∈ W, ∀ y ∈ W, B x y = 0) :
    2 * Module.finrank K W ≤ ∑ i, 2 * m i := by
  have h := Height.Toolbox.finrank_isotropic_le_half B
    (residueForm_nondegenerate_of_isometry B m e) W hW
  rwa [finrank_eq_sum_residueBlocks_of_isometry B m e] at h

end Height.DVR
