import Height.Pencil.Local
import Height.Pencil.Commutator
import Isotropy.DVRCore

/-!
# `lem:isotropy-core` and `thm:isotropy` in the local chart

The paper, `lem:isotropy-core` and `thm:isotropy`.

Fix a point of `ℙ¹`, trivialise, and work over `R = K⟦u⟧` with fraction field
`L = K⸨u⸩`.  Let `P ∈ gl_n(R)` be the localised pencil, with
`P ^ n = 0`, and let `Q₁, Q₂ ∈ gl_n(R)` be two directions that

* are commutators over `L`: `Q_i = [P, A_i]` with `A_i ∈ gl_n(L)`
  (`cor:arc-torsion`: realised directions are torsion classes), and
* are *kernel flat* at the point: `D_k(Q_i)` carries `ker (P ^ k)` into
  `range (P ^ k)` over `R` (`lem:flag-flat`(1)).

Then `trace (A₁ Q₂)` has no pole (`trace_regular`), so its residue vanishes
(`residue_eq_zero`), which is `thm:isotropy` at the point: the realised
classes are isotropic for the residue pairing of `lem:residue-form`.

The mathematics is the DVR core `Isotropy.trace_mem_range`
(`Isotropy/DVRCore.lean`: regular part, flag splitting, trace of a nilpotent);
this file is its statement in the notation of the pencil layer (`Dk`,
`LinearMap.ker`/`LinearMap.range` of `mulVecLin`, `laurentResidueFormValue`),
instantiated at `R = PowerSeries K`.

Kernel flatness is an abstract hypothesis here (`KernelFlat`), in the form
`Dk P Q k *ᵥ v ∈ range (P ^ k)` over `K⟦u⟧`.  The conclusion is stated for the
residue pairing `laurentResidueFormValue`, not for the form on the local
torsion model: the residue form is the strongest correct conclusion at this
level, and `Torsion.lean` turns it into the vanishing of the form of the local
model (`LocalData.omega_eq_zero`).
-/

namespace Height.Pencil

open Matrix Height.DVR Isotropy

universe u

variable {K : Type u} [Field K] {n : ℕ}

/-! ### Kernel flatness over `K⟦u⟧` -/

section KernelFlat

variable {R : Type*} [CommRing R]

/-- *Kernel flatness* of a direction `Q` at a point, in the notation of
`lem:flag-flat`(1): `D_k(Q)` carries `ker (P ^ k)` into `range (P ^ k)` for
every `k`.  Over a field this is `lem:field-commutator`'s condition
(`Pencil/Commutator.lean`); over `K⟦u⟧` it is the hypothesis of
`lem:isotropy-core`. -/
def KernelFlat (P Q : Matrix (Fin n) (Fin n) R) : Prop :=
  ∀ k, ∀ v ∈ LinearMap.ker ((P ^ k).mulVecLin),
    (Dk P Q k).mulVec v ∈ LinearMap.range ((P ^ k).mulVecLin)

/-- Kernel flatness is `Isotropy.DCond`. -/
theorem kernelFlat_iff_DCond (P Q : Matrix (Fin n) (Fin n) R) :
    KernelFlat P Q ↔ Isotropy.DCond P Q :=
  ⟨fun h k v hv => (h k v hv).imp fun _ hw => hw,
    fun h k v hv => (h k v hv).imp fun _ hw => hw⟩

end KernelFlat

/-! ### `lem:isotropy-core` over `K⟦u⟧` -/

/-- **`lem:isotropy-core`** over `R = K⟦u⟧`: if `[P, A_i] = Q_i` over
`L = K⸨u⸩` and both directions are kernel flat over `R`, then
`trace (A₁ Q₂)` is a power series — it has no pole at the point.

This is `Isotropy.trace_mem_range` at `R = PowerSeries K`,
`L = LaurentSeries K` (a discrete valuation ring, hence a principal ideal
domain, with `LaurentSeries` as its fraction field). -/
theorem trace_regular (P Q₁ Q₂ : Matrix (Fin n) (Fin n) (PowerSeries K))
    (hP : P ^ n = 0)
    (A₁ A₂ : Matrix (Fin n) (Fin n) (LaurentSeries K))
    (hA₁ : toK (LaurentSeries K) P * A₁ - A₁ * toK (LaurentSeries K) P =
      toK (LaurentSeries K) Q₁)
    (hA₂ : toK (LaurentSeries K) P * A₂ - A₂ * toK (LaurentSeries K) P =
      toK (LaurentSeries K) Q₂)
    (hQ₁ : KernelFlat P Q₁) (hQ₂ : KernelFlat P Q₂) :
    trace (A₁ * toK (LaurentSeries K) Q₂) ∈
      (algebraMap (PowerSeries K) (LaurentSeries K)).range :=
  Isotropy.trace_mem_range P Q₁ Q₂ hP A₁ A₂ hA₁ hA₂
    ((kernelFlat_iff_DCond P Q₁).mp hQ₁) ((kernelFlat_iff_DCond P Q₂).mp hQ₂)

/-- **`thm:isotropy`** at a point, in residue form: the residue pairing of
`lem:residue-form` vanishes on two kernel-flat directions that are
commutators over `K⸨u⸩`.  A function regular at the point has zero residue
there (`laurentResidue_algebraMap`). -/
theorem residue_eq_zero (P Q₁ Q₂ : Matrix (Fin n) (Fin n) (PowerSeries K))
    (hP : P ^ n = 0)
    (A₁ A₂ : Matrix (Fin n) (Fin n) (LaurentSeries K))
    (hA₁ : toK (LaurentSeries K) P * A₁ - A₁ * toK (LaurentSeries K) P =
      toK (LaurentSeries K) Q₁)
    (hA₂ : toK (LaurentSeries K) P * A₂ - A₂ * toK (LaurentSeries K) P =
      toK (LaurentSeries K) Q₂)
    (hQ₁ : KernelFlat P Q₁) (hQ₂ : KernelFlat P Q₂) :
    laurentResidueFormValue A₁ Q₂ = 0 := by
  obtain ⟨f, hf⟩ := trace_regular P Q₁ Q₂ hP A₁ A₂ hA₁ hA₂ hQ₁ hQ₂
  rw [laurentResidueFormValue, residueFormValue, ← hf]
  exact laurentResidue_algebraMap f

end Height.Pencil
