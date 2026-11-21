import Height.Chain.Statements
import Height.Orbital.StrataRank
import Height.Orbital.GenericRank
import Height.Orbital.TransporterArc
import Height.Orbital.KKIsotropy

/-!
# `(∗)` in arc form: statement and proof (`thm:star`)

The node of the proof chain is `nilcone_kkIsotropic` at the end of this file:
`(∗)` for the closed subscheme `V(I)` of the nilpotent cone, in the form
`Height.Orbital.KKIsotropic` of the geometry API.  `star_general` is its
prover, in coordinates.

`Z` is an irreducible closed subset of `𝔫` presented as the affine zero
locus `MvPolynomial.zeroLocus K P` of a prime ideal `P`; the hypothesis that
`Z ⊆ 𝔫` is that every point of the zero locus is strictly upper triangular.
An *arc in `Z`* is a matrix of power series whose entries satisfy every
equation of `P` (`Height.Orbital.ArcInLocus`); its base point is `matC` and its
velocity `matD` (`Orbital/Arcs.lean`).  The conclusion is `prop:transporter` in
arc form at every point of a dense open subset `Z ∖ V(g)`:

> the velocities of arcs in `Z` through a generic `z ∈ Z` are commutators
> `[α, z]`, and any two of them are `ω_z`-orthogonal.

The proof is the one of `subsec:chain-strata`: the chain strata cover `𝔫`,
membership of one of them is a conjunction of rank conditions on matrices
polynomial in the entries (`Orbital/StrataRank.lean`), and all those ranks
are the generic ranks of `Orbital/GenericRank.lean` both at `z` and at the
generic point of an arc through `z` — the latter because the witnessing
minor evaluated along the arc is a power series with constant term the
minor at `z`, hence nonzero.  So base point and generic point of the arc lie
in one and the same chain stratum, and
`Height.Orbital.transporter_arc`/`transporter_arc_isotropic` apply.
-/

namespace Height.Chain

open Matrix
open Height.Orbital Height.Steenrod
open Height.Geometry (matCoords)

universe u

section General

variable {K : Type u} [Field K] {n : ℕ}

/-- The generic matrix: the matrix of entry coordinates. -/
noncomputable def genMat (K : Type u) [Field K] (n : ℕ) :
    Matrix (Fin n) (Fin n) (MvPolynomial (Fin n × Fin n) K) :=
  Matrix.of fun i j => MvPolynomial.X (i, j)

theorem genMat_map_eval (z : Fin n × Fin n → K) :
    (genMat K n).map (MvPolynomial.eval z) = matCoords.symm z := by
  ext i j
  simp [genMat]

/-- The ring homomorphism "evaluate along the arc `a`, then pass to the
generic point". -/
noncomputable def arcHom (a : Matrix (Fin n) (Fin n) (PowerSeries K)) :
    MvPolynomial (Fin n × Fin n) K →+* PowerSeries K :=
  MvPolynomial.eval₂Hom (algebraMap K (PowerSeries K)) (fun ij => a ij.1 ij.2)

theorem arcHom_eq_aeval (a : Matrix (Fin n) (Fin n) (PowerSeries K))
    (f : MvPolynomial (Fin n × Fin n) K) :
    arcHom a f = MvPolynomial.aeval (fun ij : Fin n × Fin n => a ij.1 ij.2) f :=
  (MvPolynomial.aeval_eq_eval₂Hom _ f).symm

theorem constantCoeff_comp_arcHom (a : Matrix (Fin n) (Fin n) (PowerSeries K))
    (z : Fin n × Fin n → K) (hbase : matC a = matCoords.symm z) :
    (PowerSeries.constantCoeff (R := K)).comp (arcHom a) = MvPolynomial.eval z := by
  have h1 : (PowerSeries.constantCoeff (R := K)).comp (algebraMap K (PowerSeries K)) =
      RingHom.id K := by
    ext x
    simp [PowerSeries.algebraMap_eq]
  have h2 : (fun ij : Fin n × Fin n => PowerSeries.constantCoeff (a ij.1 ij.2)) = z := by
    funext ij
    have := congrFun (congrFun hbase ij.1) ij.2
    simpa [Height.Geometry.matCoords_symm_apply] using this
  rw [arcHom, MvPolynomial.comp_eval₂Hom, h1, h2]
  rfl

theorem genMat_map_arcGen (a : Matrix (Fin n) (Fin n) (PowerSeries K)) :
    (genMat K n).map ((algebraMap (PowerSeries K) (LaurentSeries K)).comp (arcHom a)) =
      Isotropy.toK (LaurentSeries K) a := by
  ext i j
  simp [genMat, arcHom, Isotropy.toK]

/-- `thm:star`: `(∗)` in arc form, over an algebraically closed field.  For every
irreducible closed `Z ⊆ 𝔫` there is a dense open subset of `Z` at each of whose
points the velocities of arcs in `Z` are commutators with vanishing
Kostant--Kirillov pairing. -/
theorem star_general (K : Type u) [Field K] [IsAlgClosed K] (n : ℕ) :
    ∀ P : Ideal (MvPolynomial (Fin n × Fin n) K), P.IsPrime →
      (∀ x ∈ MvPolynomial.zeroLocus K P, IsStrictlyUpper (matCoords.symm x)) →
      ∃ g ∉ P, ∀ z ∈ MvPolynomial.zeroLocus K P, MvPolynomial.eval z g ≠ 0 →
        ∀ a₁ a₂ : Matrix (Fin n) (Fin n) (PowerSeries K),
          ArcInLocus P a₁ → ArcInLocus P a₂ →
          matC a₁ = matCoords.symm z → matC a₂ = matCoords.symm z →
          ∃ α₁ α₂ : Matrix (Fin n) (Fin n) K,
            matD a₁ = α₁ * matCoords.symm z - matCoords.symm z * α₁ ∧
            matD a₂ = α₂ * matCoords.symm z - matCoords.symm z * α₂ ∧
            kkForm (matCoords.symm z) α₁ α₂ = 0 := by
  classical
  intro P hP hupper
  have : P.IsPrime := hP
  -- the equations of `𝔫` lie in `P` (Nullstellensatz)
  have hXP : ∀ i j : Fin n, j ≤ i →
      (MvPolynomial.X (i, j) : MvPolynomial (Fin n × Fin n) K) ∈ P := by
    intro i j hij
    rw [← MvPolynomial.IsPrime.vanishingIdeal_zeroLocus (K := K) P]
    intro x hx
    simpa [Height.Geometry.matCoords_symm_apply] using hupper x hx i j hij
  -- the generic ranks of the matrices cutting out the chain strata
  choose rM δM hM using fun (i : Fin n) (m : ℕ) =>
    exists_genericRank P (chainMat (genMat K n) i m)
  choose rA δA hA using fun (i : Fin n) (m : ℕ) =>
    exists_genericRank P (augCol (chainMat (genMat K n) i m) (chainVec (genMat K n) i m))
  set s : Finset (Fin n × ℕ) := Finset.univ ×ˢ Finset.range (n + 1) with hs
  refine ⟨∏ c ∈ s, δM c.1 c.2 * δA c.1 c.2, ?_, ?_⟩
  · intro hmem
    obtain ⟨c, -, hc⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
    rcases hP.mem_or_mem hc with h | h
    · exact (hM c.1 c.2).1 h
    · exact (hA c.1 c.2).1 h
  intro z hz hgz a₁ a₂ harc₁ harc₂ hb₁ hb₂
  have hzu : IsStrictlyUpper (matCoords.symm z) := hupper z hz
  -- the rank profile at any field-valued homomorphism killing `P` but not `g`
  have key : ∀ (S : Type u) (_ : Field S) (φ : MvPolynomial (Fin n × Fin n) K →+* S),
      (∀ f ∈ P, φ f = 0) → φ (∏ c ∈ s, δM c.1 c.2 * δA c.1 c.2) ≠ 0 →
      ∀ (i : Fin n) (m : ℕ), m ≤ n →
        (chainMat ((genMat K n).map φ) i m).rank = rM i m ∧
          (augCol (chainMat ((genMat K n).map φ) i m)
            (chainVec ((genMat K n).map φ) i m)).rank = rA i m := by
    intro S _ φ hφ hne i m hm
    rw [map_prod] at hne
    have hmem : (i, m) ∈ s := by
      simp only [hs, Finset.mem_product, Finset.mem_univ, Finset.mem_range, true_and]
      omega
    have hfac := Finset.prod_ne_zero_iff.mp hne (i, m) hmem
    rw [map_mul] at hfac
    have h1 : φ (δM i m) ≠ 0 := fun h => hfac (by rw [h, zero_mul])
    have h2 : φ (δA i m) ≠ 0 := fun h => hfac (by rw [h, mul_zero])
    refine ⟨?_, ?_⟩
    · rw [chainMat_map]
      exact (hM i m).2 S φ hφ h1
    · rw [chainAug_map]
      exact (hA i m).2 S φ hφ h2
  -- the ranks at the point `z`
  have hzP : ∀ f ∈ P, MvPolynomial.eval z f = 0 := by
    intro f hf
    rw [← MvPolynomial.aeval_eq_eval]
    exact hz f hf
  have hzrank := key K inferInstance (MvPolynomial.eval z) hzP hgz
  rw [genMat_map_eval] at hzrank
  -- every arc in `Z` through `z` is an arc in the chain stratum of `z`
  have arcOf : ∀ a : Matrix (Fin n) (Fin n) (PowerSeries K), ArcInLocus P a →
      matC a = matCoords.symm z →
      ∃ arc : ArcIn (fun i => chainCol (matCoords.symm z) hzu i) (matCoords.symm z), arc.vel = matD a := by
    intro a harc hbase
    set φ : MvPolynomial (Fin n × Fin n) K →+* LaurentSeries K :=
      (algebraMap (PowerSeries K) (LaurentSeries K)).comp (arcHom a) with hφdef
    have hinj : Function.Injective (algebraMap (PowerSeries K) (LaurentSeries K)) :=
      IsFractionRing.injective (PowerSeries K) (LaurentSeries K)
    have hφP : ∀ f ∈ P, φ f = 0 := by
      intro f hf
      have : arcHom a f = 0 := by rw [arcHom_eq_aeval]; exact harc f hf
      rw [hφdef, RingHom.comp_apply, this, map_zero]
    have hψg : arcHom a (∏ c ∈ s, δM c.1 c.2 * δA c.1 c.2) ≠ 0 := by
      intro h
      apply hgz
      have := congrArg (PowerSeries.constantCoeff (R := K)) h
      rw [← RingHom.comp_apply, constantCoeff_comp_arcHom a z hbase, map_zero] at this
      exact this
    have hφg : φ (∏ c ∈ s, δM c.1 c.2 * δA c.1 c.2) ≠ 0 := by
      intro h
      exact hψg (hinj (by rw [← RingHom.comp_apply, ← hφdef, h, map_zero]))
    have harank := key (LaurentSeries K) inferInstance φ hφP hφg
    rw [genMat_map_arcGen] at harank
    have hgu : IsStrictlyUpper (Isotropy.toK (LaurentSeries K) a) := by
      intro i j hij
      have : (genMat K n).map φ i j = φ (MvPolynomial.X (i, j)) := rfl
      rw [← genMat_map_arcGen a, ← hφdef, this]
      exact hφP _ (hXP i j hij)
    have hcol : ∀ i : Fin n,
        chainCol (Isotropy.toK (LaurentSeries K) a) hgu i = chainCol (matCoords.symm z) hzu i :=
      fun i => chainCol_eq_of_rank_eq hgu hzu
        (fun i' m hm => ((harank i' m hm).1).trans ((hzrank i' m hm).1).symm)
        (fun i' m hm => ((harank i' m hm).2).trans ((hzrank i' m hm).2).symm) i
    exact ⟨{ toArc := ⟨a⟩
             base_eq := hbase
             base_mem := ⟨hzu, fun i => rfl⟩
             gen_mem := ⟨hgu, hcol⟩ }, rfl⟩
  obtain ⟨arc₁, hv₁⟩ := arcOf a₁ harc₁ hb₁
  obtain ⟨arc₂, hv₂⟩ := arcOf a₂ harc₂ hb₂
  obtain ⟨α₁, hα₁⟩ := transporter_arc _ (matCoords.symm z) arc₁
  obtain ⟨α₂, hα₂⟩ := transporter_arc _ (matCoords.symm z) arc₂
  refine ⟨α₁, α₂, ?_, ?_, transporter_arc_isotropic _ (matCoords.symm z) arc₁ arc₂ α₁ α₂ hα₁ hα₂⟩
  · rw [← hv₁]; exact hα₁
  · rw [← hv₂]; exact hα₂

end General

section Node

variable {K : Type} [Field K] [IsAlgClosed K] {n : ℕ}

/-- **`thm:star`**, the node `(∗)`: a closed subscheme `V(I)` of the nilpotent
cone is Kostant--Kirillov isotropic.  "`V(I) ⊆ 𝔫`" is the algebraic form
`strictUpperIdeal K n ≤ I`, and the direction used — every zero of `I` is
strictly upper triangular — needs no Nullstellensatz.

The proof is `star_general` read through the two interface lemmas of the
geometry API: `Height.Geometry.genericPts_iff` for the generic quantifier and
`Height.Orbital.matArcEquiv` for the arcs. -/
theorem nilcone_kkIsotropic (I : Ideal (MvPolynomial (Fin n × Fin n) K)) [hI : I.IsPrime]
    (hn : strictUpperIdeal K n ≤ I) : KKIsotropic I := by
  rw [KKIsotropic, Height.Geometry.genericPts_iff]
  obtain ⟨g, hg, hmain⟩ :=
    star_general K n I hI fun x hx => isStrictlyUpper_of_le hn hx
  refine ⟨g, hg, fun z hz hgz a₁ a₂ hb₁ hb₂ => ?_⟩
  have hgz' : MvPolynomial.eval z g ≠ 0 := by rwa [← MvPolynomial.aeval_eq_eval]
  have hbase : ∀ a : Height.Geometry.Arc I, a.base = z →
      matC (matArcEquiv I a : Matrix (Fin n) (Fin n) (PowerSeries K)) = matCoords.symm z :=
    fun a ha => by rw [matC_matArcEquiv, ha]
  obtain ⟨α₁, α₂, h₁, h₂, hkk⟩ := hmain z hz hgz'
    (matArcEquiv I a₁ : Matrix (Fin n) (Fin n) (PowerSeries K))
    (matArcEquiv I a₂ : Matrix (Fin n) (Fin n) (PowerSeries K))
    (matArcEquiv I a₁).2 (matArcEquiv I a₂).2 (hbase a₁ hb₁) (hbase a₂ hb₂)
  rw [matD_matArcEquiv] at h₁ h₂
  exact ⟨⟨α₁, α₂, h₁, h₂, hkk⟩⟩

end Node

end Height.Chain
