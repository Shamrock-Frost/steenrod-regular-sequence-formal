import Height.Geometry.Dimension.Trdeg
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.KrullDimension.Integral
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field

/-!
# The generic fibre bound: fibres over a dense open are small

For an injective map `φ : A →ₐ[K] B` of finitely generated domains over a field `K`
there is a nonzero `a ∈ A` such that every fibre over a maximal ideal `m` of `A` with
`a ∉ m` satisfies

```
ringKrullDim (B ⧸ mB) + ringKrullDim A ≤ ringKrullDim B,
```

i.e. the fibres over the dense open `D(a)` have dimension at most `dim B − dim A`.

The proof is the classical spreading-out argument,
organised in three independent pieces.

* `exists_dims` (the numerology): with `F := Frac A` and
  `BF := B[φ(A ∖ 0)⁻¹]` the generic fibre, `dim B = dim A + dim BF`.  Each of the three
  Krull dimensions is a transcendence degree by `ringKrullDim_eq_trdeg`, and the
  identity is the tower law `trdeg_add_eq` applied three times, using that a
  localisation of a domain at nonzerodivisors is algebraic over it
  (`isAlgebraic_of_isLocalization`) so contributes nothing.
* `exists_spread_out` (clearing denominators): a Noether normalisation
  `ν : F[X₁ … X_g] → BF` is rescaled by an `F`-linear change of variables so that the
  images of the variables lie in `B`; writing `μ` for the rescaled map, each algebra
  generator of `B` over `A` is integral over `μ`, and
  `IsLocalization.integerNormalization` — applied to the localisation
  `A[X]⁻¹ → F[X]` of `MvPolynomial.isLocalization` — clears the denominators, producing
  a relation over `A[y]` whose top coefficient is a constant `a ∈ A ∖ 0`.  A single `a`
  serves all generators after multiplying by the complementary products.
* `fibre_dim_le_of_relations` (the fibre): for `m` maximal with `a ∉ m` the image of `a`
  is a unit in the field `A ⧸ m`, so the relations become monic over the image of
  `(A ⧸ m)[Y₁ … Y_g]` in `B ⧸ mB`.  Hence `B ⧸ mB` is integral over that image and
  `RingHom.IsIntegral.ringKrullDim_le` bounds its dimension by
  `dim (A ⧸ m)[Y₁ … Y_g] = g`.

`IsAlgClosed K` is **not** assumed; it plays no role (the
residue fields `A ⧸ m` need not equal `K`, only be fields).
-/

universe u v w

open nonZeroDivisors Cardinal

namespace Height.Geometry

/-- Lifting an integral ring homomorphism along a surjection. -/
theorem isIntegral_comp_surjective {R R' S : Type*} [CommRing R] [Nontrivial R]
    [CommRing R'] [CommRing S] {f : R →+* S} (hf : f.IsIntegral) {h : R' →+* R}
    (hh : Function.Surjective h) :
    (f.comp h).IsIntegral := by
  intro x
  obtain ⟨p, hpm, hpx⟩ := hf x
  obtain ⟨q, hq, -, hqm⟩ :=
    Polynomial.lifts_and_degree_eq_and_monic (Polynomial.mem_lifts_of_surjective hh p) hpm
  exact ⟨q, hqm, by rw [← hpx, ← hq, Polynomial.eval₂_map]⟩

/-- The fibre bound, given explicit integral relations after inverting `a`.

`y : Fin gdim → B` are the "generic Noether coordinates"; `s` generates `B` as an
`A`-algebra; each generator satisfies a relation whose top coefficient is the constant
`a`.  Modulo a maximal ideal `m` avoiding `a` the relations become monic over the image
of `(A ⧸ m)[Y₁ … Y_gdim]`, so the fibre `B ⧸ mB` is integral over a quotient of that
polynomial ring, whence its Krull dimension is at most `gdim`. -/
theorem fibre_dim_le_of_relations {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    {gdim : ℕ} (y : Fin gdim → B) (a : A) (s : Finset B)
    (hs : Algebra.adjoin A (↑s : Set B) = ⊤)
    (hrel : ∀ x ∈ s, ∃ (N : ℕ) (q : Polynomial (MvPolynomial (Fin gdim) A)),
      q.natDegree ≤ N ∧ q.coeff N = MvPolynomial.C a ∧
      Polynomial.eval₂ (MvPolynomial.eval₂Hom (algebraMap A B) y) x q = 0)
    (m : Ideal A) (hm : m.IsMaximal) (ha : a ∉ m) :
    ringKrullDim (B ⧸ (m.map (algebraMap A B))) ≤ (gdim : WithBot ℕ∞) := by
  have _ : m.IsMaximal := hm
  let _instF : Field (A ⧸ m) := Ideal.Quotient.field m
  set I : Ideal B := m.map (algebraMap A B) with hI
  set π : B →+* B ⧸ I := Ideal.Quotient.mk I with hπ
  have hkill : ∀ z ∈ m, (π.comp (algebraMap A B)) z = 0 := by
    intro z hz
    simp only [hπ, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, hI]
    exact Ideal.mem_map_of_mem _ hz
  set ψ₁ : (A ⧸ m) →+* B ⧸ I := Ideal.Quotient.lift m (π.comp (algebraMap A B)) hkill with hψ₁
  set Ψ : MvPolynomial (Fin gdim) (A ⧸ m) →+* B ⧸ I :=
    MvPolynomial.eval₂Hom ψ₁ (fun j => π (y j)) with hΨ
  set Θ : MvPolynomial (Fin gdim) A →+* B :=
    MvPolynomial.eval₂Hom (algebraMap A B) y with hΘ
  set φm : MvPolynomial (Fin gdim) A →+* MvPolynomial (Fin gdim) (A ⧸ m) :=
    MvPolynomial.map (Ideal.Quotient.mk m) with hφm
  have hcomp : Ψ.comp φm = π.comp Θ := by
    refine MvPolynomial.ringHom_ext (fun z => ?_) (fun j => ?_)
    · simp [hΨ, hφm, hΘ, hψ₁, hπ]
    · simp [hΨ, hφm, hΘ]
  -- algebra structures
  let _instPR : Algebra (MvPolynomial (Fin gdim) (A ⧸ m)) (B ⧸ I) := Ψ.toAlgebra
  have halgPR : algebraMap (MvPolynomial (Fin gdim) (A ⧸ m)) (B ⧸ I) = Ψ := rfl
  have _ : IsScalarTower A (MvPolynomial (Fin gdim) (A ⧸ m)) (B ⧸ I) := by
    refine IsScalarTower.of_algebraMap_eq fun z => ?_
    have h1 : algebraMap A (MvPolynomial (Fin gdim) (A ⧸ m)) z
        = MvPolynomial.C (Ideal.Quotient.mk m z) := rfl
    have h2 : algebraMap A (B ⧸ I) z = π (algebraMap A B z) := by
      rw [IsScalarTower.algebraMap_apply A B (B ⧸ I), Ideal.Quotient.algebraMap_eq]
    rw [h1, halgPR, hΨ, MvPolynomial.eval₂Hom_C, hψ₁,
      Ideal.Quotient.lift_mk, RingHom.comp_apply, h2]
  -- the generators are integral
  have hint : ∀ x ∈ ((π : B → B ⧸ I) '' (↑s : Set B)),
      IsIntegral (MvPolynomial (Fin gdim) (A ⧸ m)) x := by
    rintro _ ⟨x₀, hx₀, rfl⟩
    obtain ⟨N, q, hqdeg, hqcoeff, hqeval⟩ := hrel x₀ hx₀
    have hq'eval : Polynomial.eval₂ Ψ (π x₀) (q.map φm) = 0 := by
      rw [Polynomial.eval₂_map, hcomp, ← Polynomial.hom_eval₂, hqeval, map_zero]
    have hq'coeff : (q.map φm).coeff N = MvPolynomial.C (Ideal.Quotient.mk m a) := by
      rw [Polynomial.coeff_map, hqcoeff, hφm]
      simp
    have hq'deg : (q.map φm).natDegree ≤ N := le_trans Polynomial.natDegree_map_le hqdeg
    have hane : (Ideal.Quotient.mk m a) ≠ 0 := fun h =>
      ha (Ideal.Quotient.eq_zero_iff_mem.mp h)
    set r : Polynomial (MvPolynomial (Fin gdim) (A ⧸ m)) :=
      Polynomial.C (MvPolynomial.C (Ideal.Quotient.mk m a)⁻¹) * (q.map φm) with hr
    have hrcoeff : r.coeff N = 1 := by
      rw [hr, Polynomial.coeff_C_mul, hq'coeff, ← map_mul, inv_mul_cancel₀ hane, map_one]
    have hrdeg : r.natDegree ≤ N :=
      le_trans (Polynomial.natDegree_C_mul_le _ _) hq'deg
    have hrN : r.natDegree = N :=
      le_antisymm hrdeg (Polynomial.le_natDegree_of_ne_zero (by rw [hrcoeff]; exact one_ne_zero))
    have hrmonic : r.Monic := by
      unfold Polynomial.Monic Polynomial.leadingCoeff
      rw [hrN, hrcoeff]
    refine ⟨r, hrmonic, ?_⟩
    rw [halgPR, hr, Polynomial.eval₂_mul, hq'eval, mul_zero]
  -- the fibre is generated by the images of `s`
  have hadjA : Algebra.adjoin A ((π : B → B ⧸ I) '' (↑s : Set B)) = ⊤ := by
    have h1 : Algebra.adjoin A ((Ideal.Quotient.mkₐ A I : B → B ⧸ I) '' (↑s : Set B))
        = (Algebra.adjoin A (↑s : Set B)).map (Ideal.Quotient.mkₐ A I) :=
      Algebra.adjoin_image A _ _
    rw [hs, Algebra.map_top] at h1
    rw [show ((π : B → B ⧸ I) '' (↑s : Set B))
        = ((Ideal.Quotient.mkₐ A I : B → B ⧸ I) '' (↑s : Set B)) from rfl, h1,
      AlgHom.range_eq_top]
    exact Ideal.Quotient.mkₐ_surjective A I
  have hadj : Algebra.adjoin (MvPolynomial (Fin gdim) (A ⧸ m))
      ((π : B → B ⧸ I) '' (↑s : Set B)) = ⊤ := by
    refine Subalgebra.restrictScalars_injective A ?_
    rw [Subalgebra.restrictScalars_top]
    refine le_antisymm le_top ?_
    rw [← hadjA]
    refine Algebra.adjoin_le ?_
    rw [Subalgebra.coe_restrictScalars]
    exact fun z hz => Algebra.subset_adjoin hz
  have hfg := _root_.fg_adjoin_of_finite (Set.Finite.image _ s.finite_toSet) hint
  rw [hadj] at hfg
  have _ : Module.Finite (MvPolynomial (Fin gdim) (A ⧸ m)) (B ⧸ I) := by
    constructor
    simpa using hfg
  have hΨint : Ψ.IsIntegral := fun x =>
    Algebra.IsIntegral.isIntegral (R := MvPolynomial (Fin gdim) (A ⧸ m)) x
  calc ringKrullDim (B ⧸ I) ≤ ringKrullDim (MvPolynomial (Fin gdim) (A ⧸ m)) :=
        hΨint.ringKrullDim_le
    _ = (gdim : WithBot ℕ∞) := by
        rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
        simp

section SpreadOut

attribute [local instance] MvPolynomial.algebraMvPolynomial

variable {A : Type v} {B : Type w} [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
  [Algebra A B] [FaithfulSMul A B]

/-- The image of the nonzero elements of `A` consists of nonzerodivisors of `B`. -/
theorem algebraMapSubmonoid_le_nonZeroDivisors (A B : Type*) [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B] [Algebra A B] [FaithfulSMul A B] :
    Algebra.algebraMapSubmonoid B (A⁰) ≤ B⁰ := by
  rintro _ ⟨a, ha, rfl⟩
  refine mem_nonZeroDivisors_of_ne_zero ?_
  intro h
  exact (mem_nonZeroDivisors_iff_ne_zero.mp ha)
    (FaithfulSMul.algebraMap_injective A B (by simpa using h))

instance : IsDomain (Localization (Algebra.algebraMapSubmonoid B (A⁰))) :=
  IsLocalization.isDomain_of_le_nonZeroDivisors _ (algebraMapSubmonoid_le_nonZeroDivisors A B)

/-- Spreading out a Noether normalisation of the generic fibre.  Given an integral
`(FractionRing A)`-algebra map `ν` from a polynomial ring into
`BF = B[φ(A∖0)⁻¹]`, there is a single `a ≠ 0` in `A` and coordinates `y : Fin gdim → B`
such that every algebra generator of `B` over `A` satisfies a relation over `A[y]` whose
top coefficient is the constant `a`. -/
theorem exists_spread_out {gdim : ℕ}
    (ν : MvPolynomial (Fin gdim) (FractionRing A) →ₐ[FractionRing A]
      Localization (Algebra.algebraMapSubmonoid B (A⁰)))
    (hνint : RingHom.IsIntegral
      (ν : MvPolynomial (Fin gdim) (FractionRing A) →+*
        Localization (Algebra.algebraMapSubmonoid B (A⁰))))
    (s : Finset B) :
    ∃ a : A, a ≠ 0 ∧ ∃ y : Fin gdim → B, ∀ x ∈ s, ∃ (N : ℕ)
      (q : Polynomial (MvPolynomial (Fin gdim) A)), q.natDegree ≤ N ∧
        q.coeff N = MvPolynomial.C a ∧
        Polynomial.eval₂ (MvPolynomial.eval₂Hom (algebraMap A B) y) x q = 0 := by
  classical
  set BF := Localization (Algebra.algebraMapSubmonoid B (A⁰)) with hBF
  set F := FractionRing A with hF
  -- Step 1: write the images of the variables as fractions with numerator in `B`.
  have hstep : ∀ j : Fin gdim, ∃ (bj : B) (aj : A), aj ∈ A⁰ ∧
      algebraMap B BF bj
        = ν (MvPolynomial.C (algebraMap A F aj) * MvPolynomial.X j) := by
    intro j
    obtain ⟨bj, cj, hbc⟩ :=
      IsLocalization.exists_mk'_eq (Algebra.algebraMapSubmonoid B (A⁰)) (ν (MvPolynomial.X j))
    obtain ⟨aj, haj, hcaj⟩ := cj.2
    refine ⟨bj, aj, haj, ?_⟩
    have h1 : algebraMap B BF (cj : B) = algebraMap F BF (algebraMap A F aj) := by
      rw [← hcaj, ← IsScalarTower.algebraMap_apply A B BF,
        IsScalarTower.algebraMap_apply A F BF]
    have h2 : ν (MvPolynomial.C (algebraMap A F aj)) = algebraMap F BF (algebraMap A F aj) := by
      rw [← MvPolynomial.algebraMap_eq]
      exact ν.commutes _
    rw [← IsLocalization.mk'_spec BF bj cj, hbc, h1, map_mul, h2, mul_comm]
  choose bb aa haa hbb using hstep
  -- Step 2: rescale the Noether map so that the variables land in the image of `B`.
  set u : Fin gdim → F := fun j => algebraMap A F (aa j) with hu
  have hune : ∀ j, u j ≠ 0 := by
    intro j h
    exact (mem_nonZeroDivisors_iff_ne_zero.mp (haa j))
      (IsFractionRing.injective A F (by simpa [hu] using h))
  set σ : MvPolynomial (Fin gdim) F →ₐ[F] MvPolynomial (Fin gdim) F :=
    MvPolynomial.aeval (fun j => MvPolynomial.C (u j) * MvPolynomial.X j) with hσ
  set τ : MvPolynomial (Fin gdim) F →ₐ[F] MvPolynomial (Fin gdim) F :=
    MvPolynomial.aeval (fun j => MvPolynomial.C (u j)⁻¹ * MvPolynomial.X j) with hτ
  have hστ : σ.comp τ = AlgHom.id F (MvPolynomial (Fin gdim) F) := by
    refine MvPolynomial.algHom_ext (fun j => ?_)
    rw [AlgHom.comp_apply, hτ, MvPolynomial.aeval_X, map_mul, hσ, MvPolynomial.aeval_X,
      MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, ← mul_assoc, ← map_mul,
      inv_mul_cancel₀ (hune j), map_one, one_mul, AlgHom.id_apply]
  have hσsurj : Function.Surjective σ := fun z =>
    ⟨τ z, by rw [← AlgHom.comp_apply, hστ, AlgHom.id_apply]⟩
  set μ : MvPolynomial (Fin gdim) F →ₐ[F] BF := ν.comp σ with hμ
  have hμX : ∀ j, μ (MvPolynomial.X j) = algebraMap B BF (bb j) := by
    intro j
    rw [hμ, AlgHom.comp_apply, hσ, MvPolynomial.aeval_X, hbb j]
  have hμint : RingHom.IsIntegral (μ : MvPolynomial (Fin gdim) F →+* BF) := by
    have hcast : (μ : MvPolynomial (Fin gdim) F →+* BF)
        = (ν : MvPolynomial (Fin gdim) F →+* BF).comp
          (σ : MvPolynomial (Fin gdim) F →+* MvPolynomial (Fin gdim) F) := rfl
    rw [hcast]
    exact isIntegral_comp_surjective hνint hσsurj
  -- Step 3: the integral evaluation map over `A`.
  set Θ : MvPolynomial (Fin gdim) A →+* B :=
    MvPolynomial.eval₂Hom (algebraMap A B) bb with hΘ
  have hμΘ : (μ : MvPolynomial (Fin gdim) F →+* BF).comp
      (algebraMap (MvPolynomial (Fin gdim) A) (MvPolynomial (Fin gdim) F))
      = (algebraMap B BF).comp Θ := by
    refine MvPolynomial.ringHom_ext (fun z => ?_) (fun j => ?_)
    · rw [RingHom.comp_apply, RingHom.comp_apply, MvPolynomial.algebraMap_def,
        MvPolynomial.map_C]
      show μ (MvPolynomial.C (algebraMap A F z)) = algebraMap B BF (Θ (MvPolynomial.C z))
      rw [← MvPolynomial.algebraMap_eq, μ.commutes, hΘ, MvPolynomial.eval₂Hom_C,
        ← IsScalarTower.algebraMap_apply A B BF, ← IsScalarTower.algebraMap_apply A F BF]
    · rw [RingHom.comp_apply, RingHom.comp_apply, MvPolynomial.algebraMap_def,
        MvPolynomial.map_X]
      show μ (MvPolynomial.X j) = algebraMap B BF (Θ (MvPolynomial.X j))
      rw [hμX j, hΘ, MvPolynomial.eval₂Hom_X']
  -- Step 4: clear denominators, one generator at a time.
  have key : ∀ x ∈ s, ∃ a : A, a ≠ 0 ∧ ∃ (N : ℕ) (q : Polynomial (MvPolynomial (Fin gdim) A)),
      q.natDegree ≤ N ∧ q.coeff N = MvPolynomial.C a ∧ Polynomial.eval₂ Θ x q = 0 := by
    intro x _
    obtain ⟨p, hpm, hpx⟩ := hμint (algebraMap B BF x)
    set M : Submonoid (MvPolynomial (Fin gdim) A) :=
      (A⁰).map (MvPolynomial.C : A →+* MvPolynomial (Fin gdim) A) with hM
    set q := IsLocalization.integerNormalization M p with hq
    have h1 := IsLocalization.integerNormalization_eval₂_eq_zero M
      (μ : MvPolynomial (Fin gdim) F →+* BF) p hpx
    rw [hμΘ] at h1
    have h2 : algebraMap B BF (Polynomial.eval₂ Θ x q) = 0 := by
      rw [Polynomial.hom_eval₂]; exact h1
    have h3 : Polynomial.eval₂ Θ x q = 0 := by
      refine IsLocalization.injective BF (algebraMapSubmonoid_le_nonZeroDivisors A B) ?_
      rw [h2, map_zero]
    obtain ⟨b', hb'M, hb'⟩ := IsLocalization.integerNormalization_spec M p
    obtain ⟨a₀, ha₀, ha₀'⟩ := hb'M
    have hinjmap : Function.Injective
        (algebraMap (MvPolynomial (Fin gdim) A) (MvPolynomial (Fin gdim) F)) := by
      rw [MvPolynomial.algebraMap_def]
      exact MvPolynomial.map_injective _ (IsFractionRing.injective A F)
    have hcoeff : q.coeff p.natDegree = MvPolynomial.C a₀ := by
      refine hinjmap ?_
      rw [hq, ← Polynomial.coeff_map, hb', Polynomial.coeff_smul, hpm.coeff_natDegree,
        Algebra.smul_def, mul_one, ha₀']
    have hdeg : q.natDegree ≤ p.natDegree := by
      refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun n hn => ?_
      by_contra hne
      have hmem : n ∈ p.support :=
        IsLocalization.integerNormalization_support M p (Polynomial.mem_support_iff.mpr hne)
      exact absurd (Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hmem))
        (not_le.mpr hn)
    exact ⟨a₀, mem_nonZeroDivisors_iff_ne_zero.mp ha₀, p.natDegree, q, hdeg, hcoeff, h3⟩
  -- Step 5: a single `a` works for every generator.
  choose! aaa haaa NN qq hqq1 hqq2 hqq3 using key
  refine ⟨∏ x ∈ s, aaa x, Finset.prod_ne_zero_iff.mpr fun x hx => haaa x hx, bb, ?_⟩
  intro x hx
  refine ⟨NN x, Polynomial.C (MvPolynomial.C (∏ z ∈ s.erase x, aaa z)) * qq x, ?_, ?_, ?_⟩
  · exact le_trans (Polynomial.natDegree_C_mul_le _ _) (hqq1 x hx)
  · rw [Polynomial.coeff_C_mul, hqq2 x hx, ← map_mul]
    congr 1
    rw [mul_comm]
    exact Finset.mul_prod_erase s aaa hx
  · rw [Polynomial.eval₂_mul, hqq3 x hx, mul_zero]

end SpreadOut

section Assembly

variable (K : Type u) (A : Type v) (B : Type w) [Field K] [CommRing A] [CommRing B]
  [IsDomain A] [IsDomain B] [Algebra K A] [Algebra K B] [Algebra A B]
  [IsScalarTower K A B] [FaithfulSMul A B]
  [Algebra.FiniteType K A] [Algebra.FiniteType K B]

omit [IsDomain B] [Algebra K A] [Algebra K B] [IsScalarTower K A B] [FaithfulSMul A B]
  [Algebra.FiniteType K A] [Algebra.FiniteType K B] in
/-- The generic fibre `B ⊗_A Frac A` is of finite type over `Frac A`. -/
theorem finiteType_localization [Algebra.FiniteType A B] :
    Algebra.FiniteType (FractionRing A) (Localization (Algebra.algebraMapSubmonoid B (A⁰))) := by
  classical
  obtain ⟨s, hs⟩ := (‹Algebra.FiniteType A B›).1
  set BF := Localization (Algebra.algebraMapSubmonoid B (A⁰)) with hBF
  set f : B →ₐ[A] BF := IsScalarTower.toAlgHom A B BF with hf
  refine ⟨⟨s.image (algebraMap B BF), ?_⟩⟩
  set T : Subalgebra (FractionRing A) BF := Algebra.adjoin (FractionRing A)
    ↑(s.image (algebraMap B BF)) with hT
  have himg : (↑(s.image (algebraMap B BF)) : Set BF) = (f : B → BF) '' ↑s := by
    simp [hf, Finset.coe_image]
  have hsub : Algebra.adjoin A ((f : B → BF) '' (↑s : Set B))
      ≤ Subalgebra.restrictScalars A T := by
    refine Algebra.adjoin_le ?_
    rw [Subalgebra.coe_restrictScalars, hT, ← himg]
    exact fun y hy => Algebra.subset_adjoin hy
  have hrange : Set.range (algebraMap B BF) ⊆ (T : Set BF) := by
    have h1 : Algebra.adjoin A ((f : B → BF) '' (↑s : Set B))
        = (Algebra.adjoin A (↑s : Set B)).map f := Algebra.adjoin_image A f _
    rw [hs, Algebra.map_top] at h1
    intro x hx
    have hx' : x ∈ Algebra.adjoin A ((f : B → BF) '' (↑s : Set B)) := by
      rw [h1]; exact hx
    exact hsub hx'
  rw [eq_top_iff]
  rintro x -
  obtain ⟨b, m, rfl⟩ := IsLocalization.exists_mk'_eq (Algebra.algebraMapSubmonoid B (A⁰)) x
  obtain ⟨a, ha, hma⟩ := m.2
  have hane : algebraMap A (FractionRing A) a ≠ 0 := by
    intro h
    exact (mem_nonZeroDivisors_iff_ne_zero.mp ha)
      (IsFractionRing.injective A (FractionRing A) (by simpa using h))
  have hm : algebraMap B BF (m : B)
      = algebraMap (FractionRing A) BF (algebraMap A (FractionRing A) a) := by
    rw [← hma, ← IsScalarTower.algebraMap_apply A B BF,
      IsScalarTower.algebraMap_apply A (FractionRing A) BF]
  have key : algebraMap B BF b
        * algebraMap (FractionRing A) BF (algebraMap A (FractionRing A) a)⁻¹
      = IsLocalization.mk' BF b m := by
    rw [IsLocalization.eq_mk'_iff_mul_eq, hm, mul_assoc, ← map_mul,
      inv_mul_cancel₀ hane, map_one, mul_one]
  rw [← key]
  exact mul_mem (hrange ⟨b, rfl⟩) (Subalgebra.algebraMap_mem T _)

/-- A localization at nonzerodivisors of a domain is algebraic over it. -/
theorem isAlgebraic_of_isLocalization {R : Type*} [CommRing R] [IsDomain R] (M : Submonoid R)
    (S : Type*) [CommRing S] [Algebra R S] [IsLocalization M S] (hM : M ≤ R⁰) :
    Algebra.IsAlgebraic R S := by
  refine ⟨fun x => ?_⟩
  obtain ⟨r, m, rfl⟩ := IsLocalization.exists_mk'_eq M x
  refine ⟨Polynomial.C ((m : R)) * Polynomial.X - Polynomial.C r, ?_, ?_⟩
  · intro h
    have h1 : (Polynomial.C ((m : R)) * Polynomial.X - Polynomial.C r).coeff 1 = (m : R) := by
      simp [Polynomial.coeff_C]
    rw [h] at h1
    exact nonZeroDivisors.coe_ne_zero (⟨(m : R), hM m.2⟩ : R⁰) h1.symm
  · simp

include K in
/-- `dim B = dim A + dim (generic fibre)`, all three finite. -/
theorem exists_dims [Algebra.FiniteType (FractionRing A)
      (Localization (Algebra.algebraMapSubmonoid B (A⁰)))] :
    ∃ d e g : ℕ, ringKrullDim A = d ∧ ringKrullDim B = e ∧
      ringKrullDim (Localization (Algebra.algebraMapSubmonoid B (A⁰))) = g ∧ e = d + g := by
  obtain ⟨d, hdA, hdt⟩ := ringKrullDim_eq_trdeg K A
  obtain ⟨e, heB, het⟩ := ringKrullDim_eq_trdeg K B
  obtain ⟨g, hgBF, hgt⟩ := ringKrullDim_eq_trdeg (FractionRing A)
    (Localization (Algebra.algebraMapSubmonoid B (A⁰)))
  refine ⟨d, e, g, hdA, heB, hgBF, ?_⟩
  have hBBF : Algebra.IsAlgebraic B (Localization (Algebra.algebraMapSubmonoid B (A⁰))) :=
    isAlgebraic_of_isLocalization _ _ (algebraMapSubmonoid_le_nonZeroDivisors A B)
  have hAF : Algebra.IsAlgebraic A (FractionRing A) :=
    isAlgebraic_of_isLocalization _ _ le_rfl
  have _ : FaithfulSMul B (Localization (Algebra.algebraMapSubmonoid B (A⁰))) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (IsLocalization.injective _ (algebraMapSubmonoid_le_nonZeroDivisors A B))
  have hinjF : Function.Injective (algebraMap (FractionRing A)
      (Localization (Algebra.algebraMapSubmonoid B (A⁰)))) := RingHom.injective _
  have _ : FaithfulSMul (FractionRing A) (Localization (Algebra.algebraMapSubmonoid B (A⁰))) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinjF
  have hinjKA : Function.Injective (algebraMap K A) := RingHom.injective _
  have _ : FaithfulSMul K A := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinjKA
  have h1 : Algebra.trdeg A B + Algebra.trdeg B (Localization (Algebra.algebraMapSubmonoid B (A⁰)))
      = Algebra.trdeg A (Localization (Algebra.algebraMapSubmonoid B (A⁰))) :=
    trdeg_add_eq A B
  have h2 : lift.{w} (Algebra.trdeg A (FractionRing A))
      + lift.{v} (Algebra.trdeg (FractionRing A)
        (Localization (Algebra.algebraMapSubmonoid B (A⁰))))
      = lift.{v} (Algebra.trdeg A (Localization (Algebra.algebraMapSubmonoid B (A⁰)))) :=
    lift_trdeg_add_eq A (FractionRing A) _
  have h3 : lift.{w} (Algebra.trdeg K A) + lift.{v} (Algebra.trdeg A B)
      = lift.{v} (Algebra.trdeg K B) := lift_trdeg_add_eq K A B
  rw [trdeg_eq_zero (R := B), add_zero] at h1
  rw [trdeg_eq_zero (R := A) (A := FractionRing A), Cardinal.lift_zero, zero_add, hgt] at h2
  have h4 : Algebra.trdeg A (Localization (Algebra.algebraMapSubmonoid B (A⁰)))
      = (g : Cardinal.{w}) := Cardinal.lift_inj.{w, v}.mp h2.symm
  rw [h1, h4, hdt, het] at h3
  rw [Cardinal.lift_natCast, Cardinal.lift_natCast, Cardinal.lift_natCast] at h3
  exact_mod_cast h3.symm

include K in
/-- **The generic fibre bound, algebra form.**  For `B` a faithful `A`-algebra,
both finitely generated domains over `K`, the fibres of `B` over the maximal
ideals of `A` avoiding some `a ≠ 0` have dimension at most `dim B − dim A`. -/
theorem exists_fibre_dim_le_algebra :
    ∃ a : A, a ≠ 0 ∧ ∀ m : Ideal A, m.IsMaximal → a ∉ m →
      ringKrullDim (B ⧸ (m.map (algebraMap A B))) + ringKrullDim A ≤ ringKrullDim B := by
  have hAB : Algebra.FiniteType A B := Algebra.FiniteType.of_restrictScalars_finiteType K A B
  have hFT : Algebra.FiniteType (FractionRing A)
      (Localization (Algebra.algebraMapSubmonoid B (A⁰))) := finiteType_localization A B
  obtain ⟨d, e, g, hdA, heB, hgBF, hedg⟩ := exists_dims K A B
  obtain ⟨g', hg', ν, hνinj, hνint⟩ := exists_integral_inj_algHom_of_fg (FractionRing A)
    (Localization (Algebra.algebraMapSubmonoid B (A⁰)))
  have hgg : g' = g := by
    have : ((g' : ℕ) : WithBot ℕ∞) = ((g : ℕ) : WithBot ℕ∞) := by rw [hg', hgBF]
    exact_mod_cast this
  subst hgg
  obtain ⟨s, hs⟩ := hAB.1
  obtain ⟨a, ha, y, hrel⟩ := exists_spread_out ν hνint s
  refine ⟨a, ha, fun m hm ham => ?_⟩
  have hfib := fibre_dim_le_of_relations y a s hs hrel m hm ham
  rw [hdA, heB, hedg]
  calc ringKrullDim (B ⧸ (m.map (algebraMap A B))) + ((d : ℕ) : WithBot ℕ∞)
      ≤ ((g' : ℕ) : WithBot ℕ∞) + ((d : ℕ) : WithBot ℕ∞) := add_le_add hfib le_rfl
    _ = ((d + g' : ℕ) : WithBot ℕ∞) := by push_cast; ring

end Assembly

/-- **The generic fibre bound.**  For an injective map `φ : A →ₐ[K] B` of
finitely generated domains over a field, the fibres over the maximal ideals of
`A` avoiding some `a ≠ 0` have dimension at most `dim B − dim A`. -/
theorem exists_fibre_dim_le (K A B : Type*) [Field K] [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B] [Algebra K A] [Algebra K B]
    [Algebra.FiniteType K A] [Algebra.FiniteType K B] (φ : A →ₐ[K] B)
    (hφ : Function.Injective φ) :
    ∃ a : A, a ≠ 0 ∧ ∀ m : Ideal A, m.IsMaximal → a ∉ m →
      ringKrullDim (B ⧸ (m.map φ)) + ringKrullDim A ≤ ringKrullDim B := by
  let _instAB : Algebra A B := (φ : A →+* B).toAlgebra
  have _ : IsScalarTower K A B :=
    IsScalarTower.of_algebraMap_eq fun x => (φ.commutes x).symm
  have _ : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr hφ
  exact exists_fibre_dim_le_algebra K A B

end Height.Geometry
