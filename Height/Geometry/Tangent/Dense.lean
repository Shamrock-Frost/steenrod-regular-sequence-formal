import Height.Geometry.Dimension.Trdeg
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.FieldTheory.SeparablyGenerated
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# Tangent-generic points of an irreducible affine variety are dense

`Height/Geometry/Tangent/Generic.lean` produces arcs at a point `z` of `V(P)` at which some
`c = card ι - dim` elements of the prime `P` have an invertible `c × c` Jacobian minor.  This file
supplies the missing input: over a **perfect** field such data exists, and the locus where the minor
is invertible is a nonempty (hence dense) principal open of `V(P)`.

## The statement

`Height.Geometry.exists_tangent_generic`: for `P` prime in `K[x_ι]` with
`dim (K[x_ι] ⧸ P) = d` and `c + d = card ι` there are `f₁, …, f_c ∈ P`, an embedding
`S : Fin c ↪ ι` and a polynomial `g ∉ P` such that at every `z` with `g(z) ≠ 0` the minor
`det (∂f_j/∂x_{S k}) (z)` is invertible.  The witness `g` is literally that determinant, so the
locus in question is the principal open `D(g) ∩ V(P)`, nonempty because `g ∉ P`.

Algebraic closedness is **not** used: the proof needs only `PerfectField K`, and the statement
is recorded in that generality (`[IsAlgClosed K]` is a special case).

## The proof

Write `A = K[x_ι] ⧸ P` and `L = Frac A`, the residue field at the generic point of `V(P)`, and
`ξ_i ∈ L` for the image of `x_i`.

1. **Separability** (`span_D_image_eq_top`, `finrank_kaehler_le_of_trdeg`).  `L/K` is a finitely
   generated extension of a perfect field, so it has a separating transcendence basis `s`
   (`exists_isTranscendenceBasis_and_isSeparable_of_perfectField`).  If `L` is separable over an
   intermediate field `F`, then `Ω[L⁄F] = 0` (`Algebra.FormallyUnramified.of_isSeparable`), so the
   first fundamental exact sequence makes `L ⊗_F Ω[F⁄K] → Ω[L⁄K]` surjective and `Ω[L⁄K]` is spanned
   by `d(F)`.  Since `{x | d x ∈ N}` is an intermediate field for every submodule `N`
   (`derivSubfield`), `Ω[L⁄K]` is spanned by `d(s)`; hence
   `dim_L Ω[L⁄K] ≤ #s = trdeg_K L = d` (`Height.Geometry.ringKrullDim_eq_trdeg`).
2. **The conormal sequence** (`ker_resDiff_eq_jacSpan`).  `A ⊗_{K[x]} Ω[K[x]⁄K]` is free on
   `1 ⊗ d x_i` (`KaehlerDifferential.mvPolynomialBasis`), and
   `KaehlerDifferential.range_kerCotangentToTensor` identifies the kernel of
   `A ⊗ Ω[K[x]⁄K] → Ω[A⁄K]` with the span of the Jacobian rows of `P`.  Clearing denominators and
   using that `Ω[A⁄K] → Ω[L⁄K]` is a localisation (`KaehlerDifferential.isLocalizedModule_map`)
   transports this to `L`: the kernel of `v ↦ ∑ v_i d ξ_i` is exactly the `L`-span `jacSpan P` of
   the Jacobian rows of the elements of `P`.
3. **Rank count** (`le_finrank_jacSpan`).  `dim jacSpan P = card ι - dim (image of the differential)
   ≥ card ι - dim Ω[L⁄K] ≥ card ι - d = c`.
4. **Minors** (`exists_isUnit_det_of_le_finrank`).  A family spanning a subspace of `L^ι` of
   dimension `≥ c` contains `c` linearly independent members, and the resulting `c × ι` matrix has
   `c` independent columns, i.e. an invertible `c × c` minor.
-/

universe u v

open MvPolynomial TensorProduct

namespace Height.Geometry.Tangent

/-! ### Kähler differentials of a separably generated field extension -/

section Field

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- The elements `x : L` whose differential lies in a submodule `N` of `Ω[L⁄K]` form an
intermediate field: the Leibniz rule makes the condition stable under products and, through
`Derivation.leibniz_inv`, under inverses. -/
def derivSubfield (N : Submodule L (Ω[L⁄K])) : IntermediateField K L where
  carrier := {x | KaehlerDifferential.D K L x ∈ N}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at *
    rw [Derivation.leibniz]
    exact N.add_mem (N.smul_mem _ hb) (N.smul_mem _ ha)
  one_mem' := by simp
  add_mem' := by intro a b ha hb; simpa using N.add_mem ha hb
  zero_mem' := by simp
  algebraMap_mem' := by intro r; simp [Set.mem_ofPred_eq]
  inv_mem' := by
    intro x hx
    simp only [Set.mem_ofPred_eq] at *
    rw [Derivation.leibniz_inv]
    exact N.smul_mem _ hx

@[simp] lemma mem_derivSubfield {N : Submodule L (Ω[L⁄K])} {x : L} :
    x ∈ derivSubfield N ↔ KaehlerDifferential.D K L x ∈ N := Iff.rfl

/-- If `L` is separable over an intermediate field `F`, the differentials of the elements of `F`
span `Ω[L⁄K]`. -/
theorem span_D_image_coe_eq_top (F : IntermediateField K L) [Algebra.IsSeparable F L] :
    Submodule.span L (KaehlerDifferential.D K L '' (F : Set L)) = ⊤ := by
  set N : Submodule L (Ω[L⁄K]) := Submodule.span L (KaehlerDifferential.D K L '' (F : Set L))
    with hN
  have _ : Algebra.FormallyUnramified F L := Algebra.FormallyUnramified.of_isSeparable F L
  have hrange : LinearMap.range (KaehlerDifferential.mapBaseChange K F L) = ⊤ := by
    rw [KaehlerDifferential.range_mapBaseChange]
    exact LinearMap.ker_eq_top.2 (Subsingleton.elim _ _)
  have key : ∀ w : Ω[F⁄K], KaehlerDifferential.map K K F L w ∈ N := by
    intro w
    have h1 : w ∈ (⊤ : Submodule F (Ω[F⁄K])) := trivial
    rw [← KaehlerDifferential.span_range_derivation K F] at h1
    induction h1 using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨y, rfl⟩ := hx
        rw [KaehlerDifferential.map_D]
        exact Submodule.subset_span ⟨algebraMap F L y, y.2, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact N.add_mem hx hy
    | smul a x _ hx =>
        rw [map_smul, ← algebraMap_smul L a (KaehlerDifferential.map K K F L x)]
        exact N.smul_mem _ hx
  refine top_le_iff.1 ?_
  rw [← hrange]
  rintro _ ⟨z, rfl⟩
  induction z with
  | zero => simp
  | tmul l w => rw [KaehlerDifferential.mapBaseChange_tmul]; exact N.smul_mem _ (key w)
  | add x y hx hy => rw [map_add]; exact N.add_mem hx hy

/-- If `L` is separable over `K(s)`, then `Ω[L⁄K]` is spanned by `{d x | x ∈ s}`. -/
theorem span_D_image_eq_top (s : Set L)
    [Algebra.IsSeparable (IntermediateField.adjoin K s) L] :
    Submodule.span L (KaehlerDifferential.D K L '' s) = ⊤ := by
  set N : Submodule L (Ω[L⁄K]) := Submodule.span L (KaehlerDifferential.D K L '' s) with hN
  have hle : IntermediateField.adjoin K s ≤ derivSubfield N :=
    IntermediateField.adjoin_le_iff.2 fun x hx => Submodule.subset_span ⟨x, hx, rfl⟩
  refine top_le_iff.1 ?_
  rw [← span_D_image_coe_eq_top (IntermediateField.adjoin K s), Submodule.span_le]
  rintro _ ⟨x, hx, rfl⟩
  exact hle hx

variable (K L) in
/-- Over a perfect field, the differential module of a finitely generated extension is
finite-dimensional. -/
theorem finite_kaehler [PerfectField K] [Algebra.EssFiniteType K L] :
    Module.Finite L (Ω[L⁄K]) := by
  classical
  obtain ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField K L
  have hspan : Submodule.span L (KaehlerDifferential.D K L '' (s : Set L)) = ⊤ :=
    span_D_image_eq_top _
  refine ⟨⟨s.image (KaehlerDifferential.D K L), ?_⟩⟩
  rw [Finset.coe_image]
  exact hspan

variable (K L) in
/-- **Generic smoothness, algebraic form.**  Over a perfect field, the differential module of a
finitely generated field extension has dimension at most the transcendence degree. -/
theorem finrank_kaehler_le_of_trdeg [PerfectField K] [Algebra.EssFiniteType K L] {d : ℕ}
    (hd : Algebra.trdeg K L = (d : Cardinal)) :
    Module.finrank L (Ω[L⁄K]) ≤ d := by
  obtain ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField K L
  have hcard : (s.card : Cardinal) = (d : Cardinal) := by
    rw [← Cardinal.mk_coe_finset, hs.cardinalMk_eq_trdeg, hd]
  have hspan : Submodule.span L (KaehlerDifferential.D K L '' (s : Set L)) = ⊤ :=
    span_D_image_eq_top _
  refine Module.finrank_le_of_rank_le ?_
  have h1 := rank_span_le (R := L) (M := Ω[L⁄K]) (KaehlerDifferential.D K L '' (s : Set L))
  rw [hspan, rank_top] at h1
  refine h1.trans ?_
  refine Cardinal.mk_image_le.trans ?_
  simp only [Finset.coe_sort_coe, Cardinal.mk_coe_finset]
  exact hcard.le

end Field

/-! ### The conormal sequence at the generic point -/

section Conormal

variable {K : Type u} [Field K] {ι : Type v} [Fintype ι]
variable (P : Ideal (MvPolynomial ι K)) [hP : P.IsPrime]

/-- The `A`-basis `1 ⊗ d xᵢ` of `A ⊗_R Ω[R⁄K]`, where `R = K[x_ι]` and `A = R ⧸ P`. -/
noncomputable def cotBasis :
    Module.Basis ι (MvPolynomial ι K ⧸ P)
      ((MvPolynomial ι K ⧸ P) ⊗[MvPolynomial ι K] Ω[MvPolynomial ι K⁄K]) :=
  (KaehlerDifferential.mvPolynomialBasis K ι).baseChange (MvPolynomial ι K ⧸ P)

/-- The comparison map `A ⊗_R Ω[R⁄K] → Ω[A⁄K]`. -/
noncomputable def cotMap :
    ((MvPolynomial ι K ⧸ P) ⊗[MvPolynomial ι K] Ω[MvPolynomial ι K⁄K]) →ₗ[MvPolynomial ι K ⧸ P]
      Ω[(MvPolynomial ι K ⧸ P)⁄K] :=
  KaehlerDifferential.mapBaseChange K (MvPolynomial ι K) (MvPolynomial ι K ⧸ P)

omit [Fintype ι] hP in
lemma cotBasis_repr_tmul (f : MvPolynomial ι K) (i : ι) :
    (cotBasis P).repr (1 ⊗ₜ[MvPolynomial ι K] KaehlerDifferential.D K (MvPolynomial ι K) f) i
      = Ideal.Quotient.mk P (pderiv i f) := by
  rw [cotBasis, Module.Basis.baseChange_repr_tmul,
    KaehlerDifferential.mvPolynomialBasis_repr_apply, Algebra.smul_def, mul_one]
  rfl

omit hP in
lemma sum_cotBasis_eq (f : MvPolynomial ι K) :
    ∑ i, (Ideal.Quotient.mk P (pderiv i f)) • cotBasis P i
      = 1 ⊗ₜ[MvPolynomial ι K] KaehlerDifferential.D K (MvPolynomial ι K) f := by
  conv_rhs => rw [← (cotBasis P).sum_repr (1 ⊗ₜ KaehlerDifferential.D K (MvPolynomial ι K) f)]
  exact Finset.sum_congr rfl fun i _ => by rw [cotBasis_repr_tmul]

omit [Fintype ι] hP in
lemma cotMap_one_tmul' (y : Ω[MvPolynomial ι K⁄K]) :
    cotMap P (1 ⊗ₜ[MvPolynomial ι K] y)
      = KaehlerDifferential.map K K (MvPolynomial ι K) (MvPolynomial ι K ⧸ P) y :=
  IsBaseChange.lift_eq _ _ _

omit [Fintype ι] hP in
lemma cotMap_one_tmul (f : MvPolynomial ι K) :
    cotMap P (1 ⊗ₜ[MvPolynomial ι K] KaehlerDifferential.D K (MvPolynomial ι K) f)
      = KaehlerDifferential.D K _ (Ideal.Quotient.mk P f) := by
  rw [cotMap_one_tmul', KaehlerDifferential.map_D]
  rfl

omit [Fintype ι] hP in
lemma cotMap_cotBasis (i : ι) :
    cotMap P (cotBasis P i) = KaehlerDifferential.D K _ (Ideal.Quotient.mk P (X i)) := by
  rw [cotBasis, Module.Basis.baseChange_apply, KaehlerDifferential.mvPolynomialBasis_apply]
  exact cotMap_one_tmul P (X i)

omit hP in
/-- **The conormal step.**  If a combination of the basis `1 ⊗ d xᵢ` is killed by the comparison
map, its coordinates form the Jacobian row of an element of `P`. -/
lemma exists_mem_of_cotMap_eq_zero (u : ι → (MvPolynomial ι K ⧸ P))
    (h : cotMap P (∑ i, u i • cotBasis P i) = 0) :
    ∃ x ∈ P, ∀ i, u i = Ideal.Quotient.mk P (pderiv i x) := by
  have hex := KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange K (MvPolynomial ι K)
    (MvPolynomial ι K ⧸ P) Ideal.Quotient.mk_surjective
  obtain ⟨y, hy⟩ := (hex _).1 h
  obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective _ y
  rw [KaehlerDifferential.kerCotangentToTensor_toCotangent] at hy
  have hxP : (x : MvPolynomial ι K) ∈ P := by
    have h2 : Ideal.Quotient.mk P (x : MvPolynomial ι K) = 0 := RingHom.mem_ker.1 x.2
    rwa [Ideal.Quotient.eq_zero_iff_mem] at h2
  refine ⟨x, hxP, fun i => ?_⟩
  have h1 : (cotBasis P).repr (∑ j, u j • cotBasis P j) i = u i :=
    congrFun ((cotBasis P).repr_sum_self u) i
  have h2 : (cotBasis P).repr (1 ⊗ₜ[MvPolynomial ι K]
        KaehlerDifferential.D K (MvPolynomial ι K) (x : MvPolynomial ι K)) i
      = (cotBasis P).repr (∑ j, u j • cotBasis P j) i := by rw [hy]
  rw [cotBasis_repr_tmul, h1] at h2
  exact h2.symm

/-! ### The residue field at the generic point -/

/-- The image of the `i`-th coordinate in the residue field of `P`. -/
noncomputable def resCoord (i : ι) : FractionRing (MvPolynomial ι K ⧸ P) :=
  algebraMap _ _ (Ideal.Quotient.mk P (X i))

/-- The Jacobian row of `f` at the generic point of `V(P)`. -/
noncomputable def resJac (f : MvPolynomial ι K) (i : ι) : FractionRing (MvPolynomial ι K ⧸ P) :=
  algebraMap _ _ (Ideal.Quotient.mk P (pderiv i f))

/-- The differential at the generic point, `v ↦ ∑ᵢ vᵢ · d ξᵢ`. -/
noncomputable def resDiff :
    (ι → FractionRing (MvPolynomial ι K ⧸ P)) →ₗ[FractionRing (MvPolynomial ι K ⧸ P)]
      Ω[FractionRing (MvPolynomial ι K ⧸ P)⁄K] :=
  ∑ i, LinearMap.smulRight (LinearMap.proj i)
    (KaehlerDifferential.D K (FractionRing (MvPolynomial ι K ⧸ P)) (resCoord P i))

omit hP in
lemma resDiff_apply (v : ι → FractionRing (MvPolynomial ι K ⧸ P)) :
    resDiff P v = ∑ i, v i •
      KaehlerDifferential.D K (FractionRing (MvPolynomial ι K ⧸ P)) (resCoord P i) := by
  simp [resDiff]

/-- The span of the Jacobian rows of the elements of `P`, inside `ι → L`. -/
noncomputable def jacSpan : Submodule (FractionRing (MvPolynomial ι K ⧸ P))
    (ι → FractionRing (MvPolynomial ι K ⧸ P)) :=
  Submodule.span _ (Set.range fun f : P => resJac P (f : MvPolynomial ι K))

omit [Fintype ι] hP in
lemma resJac_mem_jacSpan {f : MvPolynomial ι K} (hf : f ∈ P) : resJac P f ∈ jacSpan P :=
  Submodule.subset_span ⟨⟨f, hf⟩, rfl⟩

omit hP in
/-- Transporting a combination of the basis `1 ⊗ d xᵢ` to the residue field. -/
lemma map_cotMap_sum (u : ι → (MvPolynomial ι K ⧸ P)) :
    KaehlerDifferential.map K K (MvPolynomial ι K ⧸ P) (FractionRing (MvPolynomial ι K ⧸ P))
        (cotMap P (∑ i, u i • cotBasis P i))
      = resDiff P (fun i => algebraMap _ _ (u i)) := by
  rw [resDiff_apply, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, map_smul, cotMap_cotBasis, KaehlerDifferential.map_D]
  exact (algebraMap_smul (FractionRing (MvPolynomial ι K ⧸ P)) (u i)
    (KaehlerDifferential.D K (FractionRing (MvPolynomial ι K ⧸ P)) (resCoord P i))).symm

omit hP in
lemma resJac_mem_ker {f : MvPolynomial ι K} (hf : f ∈ P) :
    resJac P f ∈ LinearMap.ker (resDiff P) := by
  have h0 : cotMap P (∑ i, (Ideal.Quotient.mk P (pderiv i f)) • cotBasis P i) = 0 := by
    rw [sum_cotBasis_eq, cotMap_one_tmul, Ideal.Quotient.eq_zero_iff_mem.2 hf, map_zero]
  have h1 := map_cotMap_sum P (fun i => Ideal.Quotient.mk P (pderiv i f))
  rw [h0, map_zero] at h1
  exact LinearMap.mem_ker.2 h1.symm

omit hP in
lemma jacSpan_le_ker : jacSpan P ≤ LinearMap.ker (resDiff P) := by
  rw [jacSpan, Submodule.span_le]
  rintro _ ⟨f, rfl⟩
  exact resJac_mem_ker P f.2

/-- **The kernel of the generic differential is the Jacobian span.**  This is the conormal exact
sequence of `P` localised at the generic point. -/
lemma ker_resDiff_le_jacSpan : LinearMap.ker (resDiff P) ≤ jacSpan P := by
  intro v hv
  obtain ⟨t, ht⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors (MvPolynomial ι K ⧸ P)) v
  choose u hu using ht
  have hu' : ∀ i, algebraMap (MvPolynomial ι K ⧸ P) (FractionRing (MvPolynomial ι K ⧸ P)) (u i)
      = algebraMap _ _ (t : MvPolynomial ι K ⧸ P) * v i := by
    intro i; rw [hu i, Algebra.smul_def]
  have hz : resDiff P (fun i => algebraMap _ _ (u i)) = 0 := by
    have : (fun i => algebraMap (MvPolynomial ι K ⧸ P) (FractionRing (MvPolynomial ι K ⧸ P)) (u i))
        = (algebraMap (MvPolynomial ι K ⧸ P) (FractionRing (MvPolynomial ι K ⧸ P))
            (t : MvPolynomial ι K ⧸ P)) • v := by
      funext i; rw [hu' i]; rfl
    rw [this, map_smul, LinearMap.mem_ker.1 hv, smul_zero]
  have hker : cotMap P (∑ i, u i • cotBasis P i) ∈ LinearMap.ker
      (KaehlerDifferential.map K K (MvPolynomial ι K ⧸ P)
        (FractionRing (MvPolynomial ι K ⧸ P))) := by
    rw [LinearMap.mem_ker, map_cotMap_sum, hz]
  obtain ⟨s, hs, hs0⟩ := (IsLocalizedModule.mem_ker_iff
    (nonZeroDivisors (MvPolynomial ι K ⧸ P))).1 hker
  have hsum : cotMap P (∑ i, (s * u i) • cotBasis P i) = 0 := by
    rw [← hs0, ← map_smul, Finset.smul_sum]
    exact congrArg _ (Finset.sum_congr rfl fun i _ => (smul_smul _ _ _).symm)
  obtain ⟨x, hxP, hx⟩ := exists_mem_of_cotMap_eq_zero P _ hsum
  have hst : (algebraMap (MvPolynomial ι K ⧸ P) (FractionRing (MvPolynomial ι K ⧸ P))
      (s * (t : MvPolynomial ι K ⧸ P))) • v = resJac P x := by
    funext i
    have h := congrArg (algebraMap (MvPolynomial ι K ⧸ P) (FractionRing (MvPolynomial ι K ⧸ P)))
      (hx i)
    rw [map_mul, hu' i] at h
    simpa [resJac, Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc] using h
  have hne : algebraMap (MvPolynomial ι K ⧸ P) (FractionRing (MvPolynomial ι K ⧸ P))
      (s * (t : MvPolynomial ι K ⧸ P)) ≠ 0 := by
    have : (s * (t : MvPolynomial ι K ⧸ P)) ∈ nonZeroDivisors (MvPolynomial ι K ⧸ P) :=
      mul_mem hs t.2
    exact IsLocalization.to_map_ne_zero_of_mem_nonZeroDivisors _ le_rfl this
  have hvv : v = (algebraMap (MvPolynomial ι K ⧸ P) (FractionRing (MvPolynomial ι K ⧸ P))
      (s * (t : MvPolynomial ι K ⧸ P)))⁻¹ • resJac P x := by
    rw [← hst, smul_smul, inv_mul_cancel₀ hne, one_smul]
  rw [hvv]
  exact Submodule.smul_mem _ _ (resJac_mem_jacSpan P hxP)

lemma ker_resDiff_eq_jacSpan : LinearMap.ker (resDiff P) = jacSpan P :=
  le_antisymm (ker_resDiff_le_jacSpan P) (jacSpan_le_ker P)

end Conormal

/-! ### Selecting an invertible minor -/

section LinearAlgebra

/-- From a family spanning a subspace of dimension at least `c`, one can select `c` members that
are linearly independent. -/
lemma exists_linearIndependent_comp {F V γ : Type*} [Field F] [AddCommGroup V] [Module F V]
    [Module.Finite F V] (g : γ → V) {c : ℕ}
    (hc : c ≤ Module.finrank F (Submodule.span F (Set.range g))) :
    ∃ f : Fin c → γ, LinearIndependent F (g ∘ f) := by
  classical
  obtain ⟨κ, a, hainj, hspan, hli⟩ := exists_linearIndependent' F g
  have : Finite κ := not_infinite_iff_finite.1 fun _ =>
    Module.Finite.not_linearIndependent_of_infinite _ hli
  have : Fintype κ := Fintype.ofFinite κ
  have hcard : Module.finrank F (Submodule.span F (Set.range g)) = Fintype.card κ := by
    rw [← hspan]
    exact finrank_span_eq_card hli
  obtain ⟨e⟩ : Nonempty (Fin c ↪ κ) :=
    Function.Embedding.nonempty_of_card_le (by simpa [hcard] using hc)
  refine ⟨a ∘ e, ?_⟩
  have := hli.comp e e.injective
  simpa [Function.comp_assoc] using this

/-- A family spanning an at-least-`c`-dimensional subspace of `ι → F` has `c` members with an
invertible `c × c` minor. -/
theorem exists_isUnit_det_of_le_finrank {F : Type*} [Field F] {ι : Type*} [Fintype ι]
    {γ : Type*} (g : γ → (ι → F)) {c : ℕ}
    (hc : c ≤ Module.finrank F (Submodule.span F (Set.range g))) :
    ∃ (f : Fin c → γ) (S : Fin c ↪ ι),
      IsUnit (Matrix.of fun j k => g (f j) (S k)).det := by
  classical
  obtain ⟨f, hf⟩ := exists_linearIndependent_comp g hc
  set M : Matrix (Fin c) ι F := Matrix.of fun j k => g (f j) k with hM
  have hrow : LinearIndependent F M.row := hf
  have hrank : M.rank = c := by simpa using hrow.rank_matrix
  have hcolspan : Submodule.span F (Set.range M.col) = ⊤ := by
    refine Submodule.eq_top_of_finrank_eq ?_
    rw [← Matrix.rank_eq_finrank_span_cols, hrank, Module.finrank_fintype_fun_eq_card,
      Fintype.card_fin]
  obtain ⟨S', hS'⟩ := exists_linearIndependent_comp M.col (c := c) (by
    rw [hcolspan, finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_fin])
  have hSinj : Function.Injective S' := by
    have h := hS'.injective
    intro a b hab
    exact h (by simp [Function.comp_apply, hab])
  refine ⟨f, ⟨S', hSinj⟩, ?_⟩
  set N : Matrix (Fin c) (Fin c) F := Matrix.of fun k j => M j (S' k) with hN
  have hNrow : LinearIndependent F N.row := hS'
  have hunit : IsUnit N := Matrix.linearIndependent_rows_iff_isUnit.1 hNrow
  have hdet : IsUnit N.det := (Matrix.isUnit_iff_isUnit_det N).1 hunit
  have hT : (Matrix.of fun j k => g (f j) ((⟨S', hSinj⟩ : Fin c ↪ ι) k)) = N.transpose := rfl
  rw [hT, Matrix.det_transpose]
  exact hdet

end LinearAlgebra

/-! ### The dimension count and the witness -/

section Witness

variable {K : Type u} [Field K] {ι : Type v} [Fintype ι]
variable (P : Ideal (MvPolynomial ι K)) [hP : P.IsPrime]

/-- The transcendence degree of the residue field of `P` is the dimension of `K[x_ι] ⧸ P`. -/
lemma trdeg_fractionRing_quotient {d : ℕ}
    (hdim : ringKrullDim (MvPolynomial ι K ⧸ P) = (d : WithBot ℕ∞)) :
    Algebra.trdeg K (FractionRing (MvPolynomial ι K ⧸ P)) = (d : Cardinal) := by
  have : Algebra.IsAlgebraic (MvPolynomial ι K ⧸ P) (FractionRing (MvPolynomial ι K ⧸ P)) :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors (MvPolynomial ι K ⧸ P))
  have : FaithfulSMul K (MvPolynomial ι K ⧸ P) :=
    (faithfulSMul_iff_algebraMap_injective K (MvPolynomial ι K ⧸ P)).mpr
      (algebraMap K (MvPolynomial ι K ⧸ P)).injective
  have : FaithfulSMul (MvPolynomial ι K ⧸ P) (FractionRing (MvPolynomial ι K ⧸ P)) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (IsFractionRing.injective (MvPolynomial ι K ⧸ P) (FractionRing (MvPolynomial ι K ⧸ P)))
  obtain ⟨d', hd1, hd2⟩ := Height.Geometry.ringKrullDim_eq_trdeg K (MvPolynomial ι K ⧸ P)
  have hdd : d' = d := by
    have h : ((d' : ℕ) : WithBot ℕ∞) = ((d : ℕ) : WithBot ℕ∞) := by rw [← hd1, hdim]
    exact_mod_cast h
  subst hdd
  rw [← trdeg_add_eq K (MvPolynomial ι K ⧸ P) (A := FractionRing (MvPolynomial ι K ⧸ P)),
    hd2, trdeg_eq_zero, add_zero]

/-- **The dimension count.**  The span of the Jacobian rows of `P` at the generic point has
dimension at least the codimension `c`. -/
lemma le_finrank_jacSpan [PerfectField K] {c d : ℕ} (hcd : c + d = Fintype.card ι)
    (hdim : ringKrullDim (MvPolynomial ι K ⧸ P) = (d : WithBot ℕ∞)) :
    c ≤ Module.finrank (FractionRing (MvPolynomial ι K ⧸ P)) (jacSpan P) := by
  have : Module.Finite (FractionRing (MvPolynomial ι K ⧸ P))
      (Ω[FractionRing (MvPolynomial ι K ⧸ P)⁄K]) :=
    finite_kaehler K (FractionRing (MvPolynomial ι K ⧸ P))
  have hle : Module.finrank (FractionRing (MvPolynomial ι K ⧸ P))
      (Ω[FractionRing (MvPolynomial ι K ⧸ P)⁄K]) ≤ d :=
    finrank_kaehler_le_of_trdeg K (FractionRing (MvPolynomial ι K ⧸ P))
      (trdeg_fractionRing_quotient P hdim)
  have h1 := LinearMap.finrank_range_add_finrank_ker (resDiff P)
  rw [ker_resDiff_eq_jacSpan, Module.finrank_fintype_fun_eq_card] at h1
  have h2 : Module.finrank (FractionRing (MvPolynomial ι K ⧸ P))
      (LinearMap.range (resDiff P)) ≤ d := le_trans (Submodule.finrank_le _) hle
  omega

/-- **The algebraic core.**  Over a perfect field there are `c` elements of the prime `P` and
`c` coordinates whose Jacobian minor is not in `P`.  The minor itself is the witness `g`: at every
point where `g` does not vanish, the minor is invertible. -/
theorem exists_jacobian_witness [PerfectField K] {c d : ℕ} (hcd : c + d = Fintype.card ι)
    (hdim : ringKrullDim (MvPolynomial ι K ⧸ P) = (d : WithBot ℕ∞)) :
    ∃ (f : Fin c → MvPolynomial ι K) (S : Fin c ↪ ι),
      (∀ j, f j ∈ P) ∧ (Matrix.of fun j k => pderiv (S k) (f j)).det ∉ P := by
  obtain ⟨F, S, hdet⟩ := exists_isUnit_det_of_le_finrank
    (F := FractionRing (MvPolynomial ι K ⧸ P))
    (fun f : P => resJac P (f : MvPolynomial ι K)) (le_finrank_jacSpan P hcd hdim)
  refine ⟨fun j => (F j : MvPolynomial ι K), S, fun j => (F j).2, ?_⟩
  set φ : MvPolynomial ι K →+* FractionRing (MvPolynomial ι K ⧸ P) :=
    (algebraMap (MvPolynomial ι K ⧸ P) (FractionRing (MvPolynomial ι K ⧸ P))).comp
      (Ideal.Quotient.mk P) with hφ
  intro hmem
  have h0 : φ ((Matrix.of fun j k => pderiv (S k) ((F j : MvPolynomial ι K))).det) = 0 := by
    rw [hφ, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 hmem, map_zero]
  rw [RingHom.map_det] at h0
  have hmat : φ.mapMatrix (Matrix.of fun j k => pderiv (S k) ((F j : MvPolynomial ι K)))
      = Matrix.of fun j k => resJac P ((F j : MvPolynomial ι K)) (S k) := rfl
  rw [hmat] at h0
  exact hdet.ne_zero h0

end Witness

end Height.Geometry.Tangent

namespace Height.Geometry

open MvPolynomial

/-- **Tangent-generic points are dense.**  Let `P` be a prime of `K[x_ι]` over a perfect field with
`dim (K[x_ι] ⧸ P) = d` and `c + d = card ι`.  Then there are `f₁, …, f_c ∈ P`, an embedding
`S : Fin c ↪ ι` and a polynomial `g ∉ P` such that the `c × c` Jacobian minor
`det (∂f_j/∂x_{S k})` is invertible at every point `z` with `g (z) ≠ 0`.

Since `g ∉ P`, the locus in question is a nonempty principal open of `V(P)`, hence dense; and `g` is
the minor itself, so the conclusion says exactly that the minor is nonzero there
(`Height.Geometry.Tangent.exists_jacobian_witness`). -/
theorem exists_tangent_generic {K : Type u} [Field K] [PerfectField K] {ι : Type v} [Fintype ι]
    (P : Ideal (MvPolynomial ι K)) [P.IsPrime] {c d : ℕ} (hcd : c + d = Fintype.card ι)
    (hdim : ringKrullDim (MvPolynomial ι K ⧸ P) = (d : WithBot ℕ∞)) :
    ∃ (g : MvPolynomial ι K) (f : Fin c → MvPolynomial ι K) (S : Fin c ↪ ι),
      g ∉ P ∧ (∀ j, f j ∈ P) ∧ ∀ z : ι → K, MvPolynomial.eval z g ≠ 0 →
        IsUnit (Matrix.of fun j k => MvPolynomial.eval z (MvPolynomial.pderiv (S k) (f j))).det := by
  obtain ⟨f, S, hfP, hdet⟩ := Tangent.exists_jacobian_witness P hcd hdim
  refine ⟨(Matrix.of fun j k => pderiv (S k) (f j)).det, f, S, hdet, hfP, ?_⟩
  intro z hz
  have h : (MvPolynomial.eval z : MvPolynomial ι K →+* K)
      ((Matrix.of fun j k => pderiv (S k) (f j)).det)
      = (Matrix.of fun j k => MvPolynomial.eval z (pderiv (S k) (f j))).det := by
    rw [RingHom.map_det]
    rfl
  rw [h] at hz
  exact isUnit_iff_ne_zero.2 hz

end Height.Geometry
