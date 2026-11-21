import Height.Chain.Main
import Height.Geometry.DimensionFormula
import Height.Geometry.HomogeneousHeight

/-!
# The two bridges and the theorem

`bb8` specialises the dimension formula
`Height.Geometry.mvPolynomial_height_add_ringKrullDim_quotient`
to the Steenrod ideal.  `bb7` specialises
`Height.Geometry.isRegular_of_height_eq_length_of_isHomogeneous`, the
homogeneous form of the criterion that exact height gives a regular sequence
(the general criterion, `Geometry/RegularOfHeight.lean`, needs the height of every
prefix, which for homogeneous generators of positive degree follows from the
height of the whole ideal by localising at the irrelevant maximal ideal).  The
Steenrod generators qualify: `Height.Steenrod.generator_isHomogeneous` gives
`P^i(c_j)` homogeneous of degree `j + i(q-1) ≥ 1`.  `regular` is the main
theorem.
-/

namespace Height.Chain

open Height.Steenrod QSteenrod

variable (p r n : ℕ) [Fact p.Prime] [NeZero r]

/-- The generators `P^i(c_j)` are homogeneous of
positive degree, so the height of the Steenrod ideal alone forces them to be a
regular sequence. -/
theorem bb7 : SteenrodHeightStatement p r n → SteenrodRegularSequenceStatement p r n := by
  intro hh
  refine Height.Geometry.isRegular_of_height_eq_length_of_isHomogeneous
    (QSteenrod.powerCharacteristicCoefficients p r n) ?_ ?_
  · intro f hf
    obtain ⟨i, j, hj1, hjN, hij, rfl, hhom⟩ := generator_isHomogeneous p r n hf
    exact ⟨j + i * (QSteenrod.q p r - 1), by omega, hhom⟩
  · rw [show Ideal.ofList (QSteenrod.powerCharacteristicCoefficients p r n)
        = steenrodIdeal p r n from rfl, hh, length_powerCharacteristicCoefficients]

/-- The dimension formula `height J + dim (R/J) = n²` for the Steenrod ideal `J`
in the entry polynomial ring `R`. -/
theorem bb8 : ((steenrodIdeal p r n).height : WithBot ℕ∞) +
    ringKrullDim (GenericMatrixRing p r n ⧸ steenrodIdeal p r n)
      = ((n * n : ℕ) : WithBot ℕ∞) := by
  have hne := steenrodIdeal_ne_top p r n
  have hsum :=
    Height.Geometry.mvPolynomial_height_add_ringKrullDim_quotient _ _ (steenrodIdeal p r n) hne
  have hcard : (Nat.card (Fin n × Fin n) : WithBot ℕ∞) = ((n * n : ℕ) : WithBot ℕ∞) := by
    simp
  rw [hcard] at hsum
  exact hsum

/-- **The theorem** (`thm:main`): the Steenrod generators form a regular sequence. -/
theorem regular : SteenrodRegularSequenceStatement p r n :=
  regular_of_boxes p r n (bb7 p r n) (bb8 p r n)

end Height.Chain
