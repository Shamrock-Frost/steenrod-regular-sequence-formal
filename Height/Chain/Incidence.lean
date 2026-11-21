import Height.Pencil.Basic
import Height.Pencil.Marked
import Height.Chain.Statements
import Height.Geometry.Coordinates

/-!
# The two incidence bounds (H1) and (H2′)

The graded encoding is that of `Height/Graded` (`Graded.Poly K = K[μ,ν]`,
`GradedPresentation.piece`).  The incidence `Î_{τ,d}` of the paper is, as a set, the
set of nilpotent pencils `μN + νM` of generic type `τ` and multidegree `d`
(the kernel flag is determined by the pencil), a subset of the affine space
of pairs `(N, M)`; the marked incidence `Ŷ` adds two distinct finite
parameters.  The multidegree is read off the Hilbert function of the kernel
pieces `{v ∈ (B_e)^n : P^k v = 0}`.  So both hypotheses are bounds on the
dimension (`affineDim`, in the charts `pairCoords` and `markedCoords` of
`Geometry/Coordinates.lean`) of a subset of affine space.  The pencil, its loci
and the numerical invariants live in `Pencil/Basic.lean`; `dimFl τ` is
`(n² − c(τ))/2`, whose halving is exact (`Pencil.two_dimFl`), so no `ℕ`-division
appears in a statement.
-/

namespace Height.Chain

open Height.Toolbox Height.Steenrod Height.Graded Height.Pencil
open Height.Geometry (affineDim pairCoords markedCoords)

variable {K : Type*} [Field K] {n : ℕ}

/-- **(H1) for `(τ, d)`** (`thm:h1`): the cone over the incidence `Î_{τ,d}` has
dimension at most `3 dim Fl_{τ'}` — the paper's
`dim I_{τ,d} ≤ 3 dim Fl_{τ'} − 1`, plus one for the scaling. -/
def PencilIncidenceBound (τ : Nat.Partition n) (d : ℕ → ℕ) : Prop :=
  affineDim (pairCoords '' pencilLocus (K := K) τ d) ≤ ((3 * dimFl τ : ℕ) : WithBot ℕ∞)

/-- **(H2′) for `(τ, d, N₀)`** (`thm:h2-conditional`): with `D = c(N₀) − c(τ)`,
`dim Ŷ + D ≤ 3 dim Fl_{τ'} + 2`.  `D` sits on the left, so no truncated
subtraction occurs; the node's hypothesis `cType τ < cOf N₀` makes
`cOf N₀ − cType τ` exact. -/
def MarkedIncidenceBound (τ : Nat.Partition n) (d : ℕ → ℕ)
    (N₀ : Matrix (Fin n) (Fin n) K) : Prop :=
  affineDim (markedCoords '' markedLocus τ d N₀) + ((cOf N₀ - cType τ : ℕ) : WithBot ℕ∞) ≤
    ((3 * dimFl τ + 2 : ℕ) : WithBot ℕ∞)

end Height.Chain
