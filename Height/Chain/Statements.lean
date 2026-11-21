import Height.Geometry.Coordinates
import Height.Steenrod.MainStatement
import Height.Steenrod.Krull
import Height.Steenrod.PartnerStrata
import Height.Steenrod.PartnerUniversalIdeal
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# The ground field of the chain, and the conjugation orbit

The proof of the height theorem is a chain of theorems, read top down in
`Chain/Edges.lean`:

* `Height.Chain.regular_of_boxes` (`Chain/Main.lean`) — `thm:main`,
  regular-sequence form, from the two bridges `bb7`, `bb8`;
* `steenrodHeight_of_dimFormula`, `steenrod_ringKrullDim_le`,
  `affineDim_flaglessPartners_le` (`Chain/Edges.lean`) — `thm:main` in height
  form, `rem:krull`, `cor:flagless`;
* `pencilIncidenceBound` (`Chain/H1Geometry.lean`), `markedIncidenceBound`
  (`Chain/Edges.lean`) — (H1),
  (H2′) of §3.4, as the predicates of `Chain/Incidence.lean`;
* `shiftedIsotropy` (`Chain/Edges.lean`) — `defn:si`, the predicate
  `Height.Pencil.ShiftedIsotropy`;
* `nilcone_kkIsotropic` (`Chain/Star.lean`) — `(∗)`, `thm:star`, the predicate
  `Height.Orbital.KKIsotropic`.

What is left in this file is the two objects those statements are about that
have no lower home: the ground field `Kbar p r` and the conjugation orbit.
-/

namespace Height.Chain

open QSteenrod Height.Steenrod

universe u

variable (p r n : ℕ) [Fact p.Prime]

/-- The algebraic closure of `F_q`, the field over which the geometry lives. -/
abbrev Kbar : Type := AlgebraicClosure (GaloisField p r)

section ConjOrbit

variable {K : Type u} [Field K] {m : ℕ}

/-- The conjugation orbit of a matrix. -/
def conjOrbit (N : Matrix (Fin m) (Fin m) K) : Set (Matrix (Fin m) (Fin m) K) :=
  {M | ∃ g : (Matrix (Fin m) (Fin m) K)ˣ,
    M = (g : Matrix (Fin m) (Fin m) K) * N * (↑g⁻¹ : Matrix (Fin m) (Fin m) K)}

end ConjOrbit

end Height.Chain
