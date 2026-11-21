import Height.Chain.Edges

/-!
# The proof chain, assembled

`regular_of_boxes` is `thm:main` from the two bridges of the geometry layer:
`bb7` (Cohen–Macaulay: exact height gives a regular sequence) and `bb8` (the
dimension formula `height J + dim (R/J) = n²` in a polynomial ring over a
field).  Both are proved in `Chain/Boxes.lean`, where `regular` is the
theorem.
-/

namespace Height.Chain

open QSteenrod Height.Steenrod

variable (p r n : ℕ) [Fact p.Prime] [NeZero r]

/-- **`thm:main`** from the two bridges and the chain below. -/
theorem regular_of_boxes
    (bb7 : SteenrodHeightStatement p r n → SteenrodRegularSequenceStatement p r n)
    (bb8 : ((steenrodIdeal p r n).height : WithBot ℕ∞) +
        ringKrullDim (GenericMatrixRing p r n ⧸ steenrodIdeal p r n)
      = ((n * n : ℕ) : WithBot ℕ∞)) :
    SteenrodRegularSequenceStatement p r n :=
  bb7 (steenrodHeight_of_dimFormula p r n bb8)

end Height.Chain
