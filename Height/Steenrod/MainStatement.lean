import Height.Steenrod.SteenrodZeroLocus
import Height.Steenrod.Krull

/-!
# The theorem-facing Steenrod height statements (`thm:main`, `rem:krull`)

This file is the two Props the whole development targets, and nothing else: the
exact height of the Steenrod ideal, and regularity of its fixed ordered
generator list.  They are the two sides of `rem:krull`; the general implication
between them belongs to the Cohen--Macaulay layer and is not asserted here.

Both carry `[NeZero r]`, because both are **false at `r = 0`** once `n ≥ 2`:
there `q = p⁰ = 1`, the total Steenrod operation sends a generator `x` to
`x + T·x` rather than `x + T·x^q`, so `P¹` acts as the identity on generators
and the Steenrod ideal collapses into the span of the `n` characteristic
coefficients — height at most `n`, against a target of `C(n+1,2)`.  The chain
theorems (`Chain/Main.lean`, `Chain/Boxes.lean`) carry the same hypothesis.
-/

namespace Height.Steenrod

open RingTheory.Sequence

universe u

/-- The exact-height formulation of the main theorem in matrix size `n`. -/
def SteenrodHeightStatement (p r n : ℕ) [Fact p.Prime] [NeZero r] : Prop :=
  (steenrodIdeal p r n).height = ((n + 1).choose 2 : ℕ∞)

/-- The regular-sequence formulation of the main theorem, using the
fixed order on the strict triangular family. -/
def SteenrodRegularSequenceStatement (p r n : ℕ) [Fact p.Prime] [NeZero r] : Prop :=
  IsRegular (QSteenrod.GenericMatrixRing p r n)
    (QSteenrod.powerCharacteristicCoefficients p r n)

end Height.Steenrod
