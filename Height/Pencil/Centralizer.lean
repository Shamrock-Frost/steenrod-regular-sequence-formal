import Height.Pencil.Realized

/-!
# The centraliser `C = ker ad_P` and the two statements of the realised bound

The definitions shared by the realised bound and the self-dual degree count:

* `adP N M` is `ad_P : gl_n ⊗ B → gl_n ⊗ B(1)` in the coordinates `vecMat`
  (`Pencil/Local.lean`); `centralizerSub` is its kernel `C` (a graded,
  saturated `B`-submodule of `Fin (n*n) → B` for the shifts `0`) and
  `adRange` its image `im ad_P` (graded for the shifts `−1`).
* `CentralizerBasis N M b u` is a homogeneous basis of `C` with degrees `b`:
  literally the conclusion of `Graded.saturated_free`.
* `IsLocalCommutator N M Q` says the pencil direction `Q` is a commutator
  with the localised pencil at every point of `ℙ¹` — at every finite point
  in the chart `Pat`/`Qat` and at infinity in the chart `PatInf`/`atInf`.

The two results those definitions serve are `Pencil.realizedDimStmt`
(`thm:realized-bound`, `Pencil/RealizedLes.lean`: a subspace of pencil
directions consisting of local commutators has dimension at most
`n² − c(τ) + Σ bᵢ`) and `Pencil.selfDualGapStmt` (`lem:selfdual-degree`,
`Pencil/SelfDual.lean`: at a pencil whose member at infinity has the generic
type, `Σ_x len_x T + 2 Σ bᵢ = 2 dim Fl_{τ'}`, the sum over the finite drop
points).
-/

namespace Height.Pencil

open Matrix Height.Graded Height.Steenrod Height.Toolbox

variable {K : Type*} [Field K] {n : ℕ}

/-- `ad_P` on `gl_n ⊗ B` in the coordinates `vecMat`. -/
noncomputable def adP (N M : Matrix (Fin n) (Fin n) K) :
    (Fin (n * n) → Graded.Poly K) →ₗ[Graded.Poly K] (Fin (n * n) → Graded.Poly K) :=
  (adMat (pencil N M)).mulVecLin

/-- `C = ker ad_P`. -/
noncomputable def centralizerSub (N M : Matrix (Fin n) (Fin n) K) :
    Submodule (Graded.Poly K) (Fin (n * n) → Graded.Poly K) :=
  LinearMap.ker (adP N M)

/-- `im ad_P ⊆ gl_n ⊗ B(1)`. -/
noncomputable def adRange (N M : Matrix (Fin n) (Fin n) K) :
    Submodule (Graded.Poly K) (Fin (n * n) → Graded.Poly K) :=
  LinearMap.range (adP N M)

/-- A homogeneous basis `u` of `C` with degrees `b`: the graded layer's
`Graded.HomogeneousBasis` for the unshifted free presentation on `Fin (n*n)`.
The four field names are the same, so `⟨mem, homog, linInd, span⟩` and dot
notation keep working. -/
abbrev CentralizerBasis (N M : Matrix (Fin n) (Fin n) K) {ι : Type} [Fintype ι]
    (b : ι → ℤ) (u : ι → (Fin (n * n) → Graded.Poly K)) : Prop :=
  Graded.HomogeneousBasis (Graded.GradedPresentation.free K (Fin (n * n)))
    (centralizerSub N M) b u

/-- `Q` is a commutator with the localised pencil at every point of `ℙ¹`. -/
def IsLocalCommutator (N M : Matrix (Fin n) (Fin n) K)
    (Q : Matrix (Fin n) (Fin n) (Graded.Poly K)) : Prop :=
  (∀ t₀ : K, ∃ A, Qat Q t₀ = Pat N M t₀ * A - A * Pat N M t₀) ∧
  (∃ A, Q.map atInf = PatInf N M * A - A * PatInf N M)

end Height.Pencil
