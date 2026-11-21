import Height.DVR.ResidueBlocks

/-!
# Finite orthogonal sums of residue blocks

Once the alternating DVR matrix is in hyperbolic normal form, the residue and
divided-residue spaces are finite orthogonal sums of the elementary blocks.
This file proves all consequences after that normal-form step.
-/

namespace Height.DVR

open scoped BigOperators

universe u v

variable {K : Type u} [Field K]
variable {ι : Type v} [Fintype ι]

/-- A finite family of hyperbolic residue blocks with exponents `m i`. -/
abbrev ResidueBlockFamily (m : ι → ℕ) :=
  ∀ i, TruncatedCoeffs K (m i) × TruncatedCoeffs K (m i)

/-- Orthogonal sum of the residue pairings on a finite family of blocks. -/
def residueDirectSumBilinForm (m : ι → ℕ) :
    LinearMap.BilinForm K (ResidueBlockFamily (K := K) m) :=
  LinearMap.mk₂ K
    (fun x y => ∑ i, residueBlockForm (m i) (x i) (y i))
    (by
      intro x z y
      simp_rw [Pi.add_apply]
      simp only [← residueBlockBilinForm_apply,
        map_add, LinearMap.add_apply, Finset.sum_add_distrib])
    (by
      intro r x y
      simp_rw [Pi.smul_apply]
      simp only [← residueBlockBilinForm_apply, map_smul,
        LinearMap.smul_apply, Finset.smul_sum])
    (by
      intro x y z
      simp_rw [Pi.add_apply]
      simp only [← residueBlockBilinForm_apply,
        map_add, Finset.sum_add_distrib])
    (by
      intro r x y
      simp_rw [Pi.smul_apply]
      simp only [← residueBlockBilinForm_apply, map_smul,
        Finset.smul_sum])

@[simp] theorem residueDirectSumBilinForm_apply (m : ι → ℕ)
    (x y : ResidueBlockFamily (K := K) m) :
    residueDirectSumBilinForm m x y =
      ∑ i, residueBlockForm (m i) (x i) (y i) := rfl

private theorem residueDirectSumBilinForm_single_right (m : ι → ℕ)
    [DecidableEq ι]
    (x : ResidueBlockFamily (K := K) m) (i : ι)
    (z : TruncatedCoeffs K (m i) × TruncatedCoeffs K (m i)) :
    residueDirectSumBilinForm m x (Pi.single i z) =
      residueBlockForm (m i) (x i) z := by
  classical
  rw [residueDirectSumBilinForm_apply, Finset.sum_eq_single i]
  · rw [Pi.single_eq_same]
  · intro j _ hji
    rw [Pi.single_eq_of_ne hji]
    simp [residueBlockForm, residueCoeffPair]
  · simp

/-- A finite orthogonal sum of residue blocks is alternating and
nondegenerate. -/
theorem residueDirectSumBilinForm_alt_nondegenerate (m : ι → ℕ) :
    (residueDirectSumBilinForm (K := K) m).IsAlt ∧
      (residueDirectSumBilinForm (K := K) m).Nondegenerate := by
  classical
  have hAlt : (residueDirectSumBilinForm (K := K) m).IsAlt := by
    intro x
    simp [residueBlockForm_self]
  have hLeft : (residueDirectSumBilinForm (K := K) m).SeparatingLeft := by
    intro x hx
    funext i
    apply (residueBlock_nondegenerate (K := K) (m i)).2 (x i)
    intro z
    have h := hx (Pi.single i z)
    rw [residueDirectSumBilinForm_single_right] at h
    exact h
  refine ⟨hAlt, hLeft, ?_⟩
  intro y hy
  apply hLeft y
  intro x
  apply neg_eq_zero.mp
  rw [hAlt.neg_eq]
  exact hy x

/-- The dimension of a finite family of residue blocks is its total
length. -/
theorem finrank_residueBlockFamily (m : ι → ℕ) :
    Module.finrank K (ResidueBlockFamily (K := K) m) = ∑ i, 2 * m i := by
  rw [Module.finrank_pi_fintype]
  simp [TruncatedCoeffs, two_mul, Finset.sum_add_distrib]

end Height.DVR
