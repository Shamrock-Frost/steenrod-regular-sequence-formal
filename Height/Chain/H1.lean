import Height.Pencil.Realized
import Height.Chain.Incidence
import Height.Pencil.Arcs

/-!
# `thm:h1`: the realised classes bound the dimension of the incidence

The paper, `thm:h1` (through `thm:realized-bound`,
`thm:isotropy`, `lem:selfdual-degree`).  The node of the chain is
`Height.Chain.pencilIncidenceBound` (`Chain/H1Geometry.lean`).

The count of `thm:h1` is `Height.Pencil.realized_count`, proved in
`Pencil/Realized.lean` from the two halves of `thm:realized-bound`
(`Height.Pencil.realizedDimStmt`, `Pencil/RealizedLes.lean`), `thm:isotropy`
(`Height.DVR.residueSpaceForm_isotropic_bound`) and `lem:selfdual-degree`
(`sum_b_add_half_len_eq_dimFl`):

```
α : T → ⊕_x T_x                      (the class map at a tangent-generic point)
im α isotropic for ⊕_x ω_x           (thm:isotropy)
dim ker α ≤ dim 𝒩                    (thm:realized-bound, kernel half)
Σ_x len_x + 2 Σ b_i ≤ 2 dim Fl       (lem:selfdual-degree)
dim 𝒩 = 2 dim Fl + Σ b_i             (thm:realized-bound, dimension half)
⟹ dim T ≤ 3 dim Fl .
```

This file is the last step: a `RealizedDatum` with its `Bounds` at `(τ, d)`
gives (H1) at `(τ, d)`.  The datum itself is produced in
`Chain/H1Geometry.lean` from the geometry of the incidence.
-/

namespace Height.Chain

open Matrix Height.Pencil Height.DVR Height.Steenrod
open Height.Geometry (pairCoords PairIndex)

variable {K : Type} [Field K] {n : ℕ}

/-- **`thm:h1` from the tangent datum**: the realised classes at a
tangent-generic point of a component of the cone `Î_{τ,d}` bound its dimension
by `3 dim Fl_{τ'}`. -/
theorem pencilIncidenceBound_of_bounds {τ : Nat.Partition n} {d : ℕ → ℕ}
    (R : RealizedDatum K (PairIndex (Fin n)))
    (hR : R.Bounds τ 0 0 (pairCoords '' pencilLocus (K := K) τ d)) :
    PencilIncidenceBound (K := K) τ d := by
  have hcount := hR.finrank_add_le
  refine le_trans hR.affineDim_le ?_
  have h2D := two_dimFl τ
  have hR2 := hR.two_dimFl
  have hfin : Module.finrank K R.T ≤ 3 * dimFl τ := by omega
  exact_mod_cast hfin

end Height.Chain
