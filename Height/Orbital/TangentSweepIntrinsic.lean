import Height.Orbital.KKReindex

/-!
# Standard reindexing for one-coordinate block extensions

The block transporter uses the index type `Fin n ⊕ Unit`.  The definition
below transports such a square matrix to the standard index type
`Fin (n + 1)` using `blockIndexEquiv`.
-/

namespace Height.Orbital

open Matrix

variable {K : Type*} [Field K] {n : ℕ}

/-- Reindex a one-coordinate block extension by the standard equivalence
`Fin n ⊕ Unit ≃ Fin (n+1)`. -/
def standardBlockMatrix
    (A : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) K) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
  Matrix.reindexAlgEquiv K K (blockIndexEquiv n) A

end Height.Orbital
