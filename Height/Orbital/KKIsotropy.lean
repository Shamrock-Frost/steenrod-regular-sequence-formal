import Height.Orbital.Arcs
import Height.Orbital.KK
import Height.Geometry.Interface

/-!
# `(∗)` as a property of a closed subscheme of the nilpotent cone

`(∗)` (`thm:star`) says: on a dense open subset of an irreducible closed
`Z ⊆ 𝔫`, the velocities of arcs of `Z` through a point are commutators
`[α, z]` whose Kostant–Kirillov pairing `tr(z [α₁, α₂])` vanishes.  This file
states it as the predicate `KKIsotropic` on an ideal of the entry polynomial
ring, using the geometry API: `Geometry.GenericPts` for "generically on
`V(I)`, at `K`-points" and `Geometry.Arc` for the `K⟦u⟧`-points of the closed
subscheme `V(I)`.

The provers of `(∗)` work with matrices of power series (`ArcInLocus`), so the
file also carries the bridge `matArcEquiv` between the two notions of arc,
with the transport lemmas for the base point (`matC`) and the velocity
(`matD`).  The `∃`-form of the commutator clause avoids the well-definedness
lemma for the Kostant–Kirillov form on `[𝔤, z]`.
-/

namespace Height.Orbital

open Matrix
open Height.Geometry (matCoords matCoords_symm_apply)

universe u

/-! ### Arcs in a locus, in matrix coordinates -/

section ArcInLocus

variable {K : Type u} [Field K] {n : ℕ}

/-- An arc in the affine zero locus of `P`: a matrix of power series whose
entries satisfy every equation of `P`. -/
def ArcInLocus (P : Ideal (MvPolynomial (Fin n × Fin n) K))
    (a : Matrix (Fin n) (Fin n) (PowerSeries K)) : Prop :=
  ∀ f ∈ P, MvPolynomial.aeval (fun ij : Fin n × Fin n => a ij.1 ij.2) f = 0

end ArcInLocus

/-! ### The bridge to the API's arcs

The geometry API ties the index universe of `𝔸(ι)` to that of `K`, so the
statements below live at `K : Type` (the chain runs at `Kbar p r : Type`). -/

section Bridge

variable {K : Type} [Field K] {n : ℕ}

/-- **The arcs of `V(P) ⊆ gl_n` in matrix coordinates**: a `K⟦u⟧`-point of the
closed subscheme `V(P)` of entry space is exactly a matrix of power series
satisfying every equation of `P` (`Geometry.arcEquiv` read through the entry
chart). -/
noncomputable def matArcEquiv (P : Ideal (MvPolynomial (Fin n × Fin n) K)) :
    Height.Geometry.Arc P ≃ {a : Matrix (Fin n) (Fin n) (PowerSeries K) // ArcInLocus P a} :=
  (Height.Geometry.arcEquiv P).trans
    (Equiv.subtypeEquiv (matCoords (K := PowerSeries K) (μ := Fin n)).symm.toEquiv
      fun _ => Iff.rfl)

theorem coords_matArcEquiv_symm {P : Ideal (MvPolynomial (Fin n × Fin n) K)}
    (a : {a : Matrix (Fin n) (Fin n) (PowerSeries K) // ArcInLocus P a}) :
    ((matArcEquiv P).symm a).coords = matCoords (a : Matrix (Fin n) (Fin n) (PowerSeries K)) := by
  rw [matArcEquiv, Equiv.symm_trans_apply, Height.Geometry.coords_arcEquiv_symm]
  rfl

/-- The base point of the API arc is the constant term of the matrix arc. -/
theorem matC_matArcEquiv {P : Ideal (MvPolynomial (Fin n × Fin n) K)}
    (a : Height.Geometry.Arc P) :
    matC (matArcEquiv P a : Matrix (Fin n) (Fin n) (PowerSeries K)) = matCoords.symm a.base :=
  rfl

/-- The velocity of the API arc is the linear coefficient of the matrix arc. -/
theorem matD_matArcEquiv {P : Ideal (MvPolynomial (Fin n × Fin n) K)}
    (a : Height.Geometry.Arc P) :
    matD (matArcEquiv P a : Matrix (Fin n) (Fin n) (PowerSeries K)) = matCoords.symm a.vel :=
  rfl

/-- The base point of the matrix arc, read on the API arc. -/
theorem base_matArcEquiv_symm {P : Ideal (MvPolynomial (Fin n × Fin n) K)}
    (a : {a : Matrix (Fin n) (Fin n) (PowerSeries K) // ArcInLocus P a}) :
    ((matArcEquiv P).symm a).base
      = matCoords (matC (a : Matrix (Fin n) (Fin n) (PowerSeries K))) := by
  funext ij
  show PowerSeries.constantCoeff (((matArcEquiv P).symm a).coords ij) = _
  rw [coords_matArcEquiv_symm]
  rfl

/-- The velocity of the matrix arc, read on the API arc. -/
theorem vel_matArcEquiv_symm {P : Ideal (MvPolynomial (Fin n × Fin n) K)}
    (a : {a : Matrix (Fin n) (Fin n) (PowerSeries K) // ArcInLocus P a}) :
    ((matArcEquiv P).symm a).vel
      = matCoords (matD (a : Matrix (Fin n) (Fin n) (PowerSeries K))) := by
  funext ij
  show PowerSeries.coeff 1 (((matArcEquiv P).symm a).coords ij) = _
  rw [coords_matArcEquiv_symm]
  rfl

/-- A witness that two velocities `v₁, v₂` at `z` are commutators `[αᵢ, z]` with
vanishing Kostant–Kirillov pairing `tr(z [α₁, α₂])`.  The two equations are
tangency to the orbit; carrying the `αᵢ` avoids the well-definedness lemma for
the pairing on `[𝔤, z]`. -/
structure KKWitness (z v₁ v₂ : Matrix (Fin n) (Fin n) K) where
  /-- the direction with `v₁ = [α₁, z]` -/
  α₁ : Matrix (Fin n) (Fin n) K
  /-- the direction with `v₂ = [α₂, z]` -/
  α₂ : Matrix (Fin n) (Fin n) K
  /-- `v₁` is tangent to the orbit -/
  eq₁ : v₁ = α₁ * z - z * α₁
  /-- `v₂` is tangent to the orbit -/
  eq₂ : v₂ = α₂ * z - z * α₂
  /-- the Kostant–Kirillov pairing vanishes -/
  kk : kkForm z α₁ α₂ = 0

/-- **`(∗)`, `thm:star`, for the closed subscheme `V(I) ⊆ 𝔫`**: generically on
`V(I)`, the velocities of any two arcs of `V(I)` through the point are
commutators `[αᵢ, z]` whose Kostant–Kirillov pairing `tr(z [α₁, α₂])`
vanishes (`KKWitness`). -/
def KKIsotropic (I : Ideal (MvPolynomial (Fin n × Fin n) K)) : Prop :=
  Height.Geometry.GenericPts I fun z =>
    ∀ a₁ a₂ : Height.Geometry.Arc I, a₁.base = z → a₂.base = z →
      Nonempty (KKWitness (matCoords.symm z) (matCoords.symm a₁.vel) (matCoords.symm a₂.vel))

end Bridge

end Height.Orbital
