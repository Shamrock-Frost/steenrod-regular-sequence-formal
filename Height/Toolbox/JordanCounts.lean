import Height.Toolbox.Jordan
import Height.Toolbox.PartitionCounts

/-!
# Finite sums of kernel-dimension Jordan columns (`lem:springer-dim`)

For a nilpotent endomorphism killed by its `r`th power, the first `r`
successive kernel jumps contain the whole conjugate Jordan partition.

These are the sums `c(λ) = Σ_m λ'^2_m` and `n(λ) = Σ_m C(λ'_m, 2)` of
`lem:springer-dim`, and the identity `c(λ) = n + 2 n(λ)` it uses.
-/

namespace Height.Toolbox

open scoped BigOperators

universe u v

variable {K : Type u} [Field K]
variable {W : Type v} [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/-- The finite family of conjugate Jordan column lengths through exponent
`r`. -/
noncomputable def jordanColumns (y : Module.End K W) (r : ℕ) : Fin r → ℕ :=
  fun i => conj y (i + 1)

/-- If `y^r = 0`, its Jordan column lengths sum to the dimension of the
space. -/
theorem diagramSize_jordanColumns (y : Module.End K W) (r : ℕ)
    (hy : y ^ r = 0) :
    diagramSize (jordanColumns y r) = Module.finrank K W := by
  rw [diagramSize]
  simp only [jordanColumns]
  rw [Fin.sum_univ_eq_sum_range (fun i => conj y (i + 1)) r]
  change (∑ i ∈ Finset.range r,
    (Module.finrank K (LinearMap.ker (y ^ (i + 1))) -
      Module.finrank K (LinearMap.ker (y ^ i)))) = Module.finrank K W
  have hmono : Monotone
      (fun i => Module.finrank K (LinearMap.ker (y ^ i))) := by
    intro a b hab
    exact Submodule.finrank_mono ((LinearMap.iterateKer y).monotone hab)
  rw [Finset.sum_range_tsub hmono]
  rw [hy, LinearMap.ker_zero, pow_zero, Module.End.one_eq_id,
    LinearMap.ker_id, finrank_top, finrank_bot, Nat.sub_zero]

/-- For a nilpotent endomorphism, the centralizer and Springer numerical
counts attached to its kernel-dimension Jordan columns satisfy
`c = dim W + 2 n`. -/
theorem centralizerCount_jordanColumns (y : Module.End K W) (r : ℕ)
    (hy : y ^ r = 0) :
    centralizerCount (jordanColumns y r) =
      Module.finrank K W + 2 * springerCount (jordanColumns y r) := by
  apply centralizerCount_eq_of_diagramSize_eq
  exact diagramSize_jordanColumns y r hy

end Height.Toolbox
