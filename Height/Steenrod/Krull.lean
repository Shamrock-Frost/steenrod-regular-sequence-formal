import Height.Steenrod.Ideal
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# The formal Krull height upper bound (`rem:krull`)

This proves the unconditional half of `rem:krull`: the Steenrod ideal is
proper and its height is at most the number of displayed generators.
-/

namespace Height.Steenrod


variable (p r N : ℕ) [Fact p.Prime]

private theorem constantCoeff_eq_zero_of_isHomogeneous_pos
    {f : QSteenrod.GenericMatrixRing p r N} {d : ℕ}
    (hf : f.IsHomogeneous d) (hd : 0 < d) :
    MvPolynomial.constantCoeff f = 0 := by
  rw [MvPolynomial.constantCoeff_eq]
  exact hf.coeff_eq_zero (Ne.symm hd.ne')

/-- The Steenrod ideal is contained in the augmentation ideal, hence is
proper. -/
theorem steenrodIdeal_ne_top [NeZero r] : steenrodIdeal p r N ≠ ⊤ := by
  let aug : QSteenrod.GenericMatrixRing p r N →+* GaloisField p r :=
    MvPolynomial.constantCoeff
  have hle : steenrodIdeal p r N ≤ RingHom.ker aug := by
    rw [steenrodIdeal, Ideal.span_le]
    intro f hf
    change MvPolynomial.constantCoeff f = 0
    obtain ⟨i, j, hj1, hjN, hij, hfeq, hhom⟩ :=
      generator_isHomogeneous p r N hf
    exact constantCoeff_eq_zero_of_isHomogeneous_pos p r N hhom (by omega)
  intro htop
  have hone : (1 : QSteenrod.GenericMatrixRing p r N) ∈ RingHom.ker aug := by
    apply hle
    rw [htop]
    simp
  change aug 1 = 0 at hone
  rw [map_one] at hone
  exact one_ne_zero hone

private theorem generatorSet_ncard_le_length :
    {f : QSteenrod.GenericMatrixRing p r N |
      f ∈ QSteenrod.powerCharacteristicCoefficients p r N}.ncard ≤
      (QSteenrod.powerCharacteristicCoefficients p r N).length := by
  classical
  let L := QSteenrod.powerCharacteristicCoefficients p r N
  have hset : {f : QSteenrod.GenericMatrixRing p r N | f ∈ L} =
      (L.toFinset : Set (QSteenrod.GenericMatrixRing p r N)) := by
    ext f
    simp
  rw [hset, Set.ncard_coe_finset]
  exact List.toFinset_card_le L

/-- `rem:krull`: Krull's height theorem bounds the Steenrod ideal by the
cardinality of its strict-triangle generating list. -/
theorem steenrodIdeal_height_le [NeZero r] :
    (steenrodIdeal p r N).height ≤ ((N + 1).choose 2 : ℕ∞) := by
  classical
  let S : Set (QSteenrod.GenericMatrixRing p r N) :=
    {f | f ∈ QSteenrod.powerCharacteristicCoefficients p r N}
  have hfinite : S.Finite := by
    rw [show S =
      ((QSteenrod.powerCharacteristicCoefficients p r N).toFinset :
        Set (QSteenrod.GenericMatrixRing p r N)) by ext f; simp [S]]
    exact Set.toFinite _
  calc
    (steenrodIdeal p r N).height ≤
        ((steenrodIdeal p r N).spanFinrank : ℕ∞) :=
      Ideal.height_le_spanFinrank _ (steenrodIdeal_ne_top p r N)
    _ ≤ (S.ncard : ℕ∞) := by
      exact_mod_cast (show (steenrodIdeal p r N).spanFinrank ≤ S.ncard by
        rw [steenrodIdeal]
        change (Ideal.span S).spanFinrank ≤ S.ncard
        exact Submodule.spanFinrank_span_le_ncard_of_finite hfinite)
    _ ≤ ((QSteenrod.powerCharacteristicCoefficients p r N).length : ℕ∞) := by
      exact_mod_cast (show S.ncard ≤
          (QSteenrod.powerCharacteristicCoefficients p r N).length by
        simpa [S] using generatorSet_ncard_le_length p r N)
    _ = ((N + 1).choose 2 : ℕ∞) := by
      rw [length_powerCharacteristicCoefficients]

end Height.Steenrod
