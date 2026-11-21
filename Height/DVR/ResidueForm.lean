import Height.DVR.ResidueBlocks
import Height.DVR.Residue
import Isotropy.DVRCore

/-!
# The trace-residue form before block decomposition

These identities are the choice-independence and descent part of
`lem:residue-form`.  The residue is the concrete one:
`res_x f\,du = [u^{-1}] f` on `L := LaurentSeries K`, the fraction field of
`R := PowerSeries K`.  The four identities of `lem:residue-form` are stated for it.

The underlying arguments only use additivity of the residue and its vanishing
on the valuation ring, so they are proved once for an arbitrary additive map
`ρ` (the `residueFormValue_*` lemmas) and then specialised.
-/

namespace Height.DVR

open Matrix
open Isotropy

universe u v w

variable {R : Type u} [CommRing R]
variable {K : Type v} [Field K] [Algebra R K]
variable {k : Type w} [AddCommGroup k]
variable {n : ℕ}

/-- The representative-level residue pairing. -/
def residueFormValue (ρ : K →+ k) (A₁ : Matrix (Fin n) (Fin n) K)
    (Pd₂ : Matrix (Fin n) (Fin n) R) : k :=
  ρ (trace (A₁ * toK K Pd₂))

section Laurent

variable {F : Type u} [Field F]

/-- The residue pairing of `lem:residue-form` in the local model:
`ω_x(Ṗ₁, Ṗ₂) = res_x trace(A₁ Ṗ₂)\,du` with
`res_x f\,du = [u^{-1}] f` on `LaurentSeries F`. -/
noncomputable def laurentResidueFormValue
    (A₁ : Matrix (Fin n) (Fin n) (LaurentSeries F))
    (Pd₂ : Matrix (Fin n) (Fin n) (PowerSeries F)) : F :=
  residueFormValue (laurentResidue F) A₁ Pd₂

end Laurent

end Height.DVR
