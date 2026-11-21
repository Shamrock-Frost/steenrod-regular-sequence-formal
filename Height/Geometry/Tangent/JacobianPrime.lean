import Height.Geometry.Tangent.Generic
import Height.Toolbox.RegularLocalRing
import Height.Toolbox.AffineAlgebra
import Height.Toolbox.LocalizationQuotient
import Mathlib.RingTheory.RegularLocalRing.Polynomial

/-!
# The Jacobian criterion at an arbitrary prime

`Height/Geometry/Tangent/Generic.lean` proves the Jacobian criterion at a `K`-point: `c`
equations with an invertible `c × c` minor at `w` cut out a regular local ring at `w`
(`isRegularLocalRing_quotient_map_of_jacobian`), by the first-order Taylor expansion.  There
is no Taylor expansion at a non-rational point, and this file replaces it by the derivation
argument, which works at **every** prime `q` of `K[ι]` and over every field:

* `pderiv_mem_of_mem_sq`, `pderiv_sum_mul_sub_mem`: a partial derivative carries `q²` into
  `q`, and modulo `q` it is additive on combinations of elements of `q` — the two elementary
  facts that replace the conormal exact sequence.
* `indepModSq_of_notMem_det`: if `f₁, …, f_c ∈ q` have a `c × c` Jacobian minor outside `q`,
  then their images in `K[ι]_q` are independent modulo the square of the maximal ideal
  (`Toolbox.IndepModSq`).  Clearing denominators, a relation `∑ aⱼ fⱼ ∈ 𝔪²` becomes
  `s · ∑ yⱼ fⱼ ∈ q²` with `s ∉ q`; differentiating and reducing modulo `q` kills the
  coefficient vector against the Jacobian matrix over the domain `K[ι] ⧸ q`, where the minor
  is invertible.
* `isRegularLocalRing_quotient_map_of_notMem_det`: hence `K[ι]_q ⧸ (f₁, …, f_c)` is a regular
  local ring of dimension `height q − c`, since `K[ι]_q` is regular
  (`MvPolynomial.isRegularRing_of_isRegularRing`) and a quotient of a regular local ring by a
  family independent modulo `𝔪²` is regular
  (`Toolbox.isRegularLocalRing_quotient_span_of_indepModSq`).
* `ringKrullDim_quotient_map_atPrime_add_height`: the companion dimension count for a prime
  `p ≤ q`, `dim (K[ι]_q ⧸ p K[ι]_q) + height p = height q`.

Nothing here needs a perfect field: this is "a complete intersection with an invertible minor
is smooth, hence regular".  The scheme-level consequence is
`Geometry/Spec.generic_isRegularLocalRing`.
-/

universe u v

open MvPolynomial IsLocalRing
open scoped Matrix

namespace Height.Geometry.Tangent


variable {K : Type u} [Field K] {ι : Type v} [Fintype ι]

omit [Fintype ι] in
/-- A partial derivative carries `q²` into `q`. -/
theorem pderiv_mem_of_mem_sq (q : Ideal (MvPolynomial ι K)) (i : ι) {u : MvPolynomial ι K}
    (hu : u ∈ q ^ 2) : pderiv i u ∈ q := by
  rw [pow_two] at hu
  refine Submodule.mul_induction_on hu (fun a ha b hb => ?_) (fun y z hy hz => ?_)
  · rw [Derivation.leibniz]
    exact q.add_mem (q.mul_mem_right _ ha) (q.mul_mem_right _ hb)
  · rw [map_add]
    exact q.add_mem hy hz

omit [Fintype ι] in
/-- Modulo `q`, the derivative of a combination of elements of `q` is the combination of their
derivatives. -/
theorem pderiv_sum_mul_sub_mem (q : Ideal (MvPolynomial ι K)) (i : ι) {c : ℕ}
    (y f : Fin c → MvPolynomial ι K) (hf : ∀ k, f k ∈ q) :
    pderiv i (∑ k, y k * f k) - ∑ k, y k * pderiv i (f k) ∈ q := by
  rw [map_sum, ← Finset.sum_sub_distrib]
  refine Ideal.sum_mem _ fun k _ => ?_
  have h : (pderiv i) (y k * f k) - y k * (pderiv i) (f k) = f k * (pderiv i) (y k) := by
    rw [Derivation.leibniz]
    simp only [smul_eq_mul]
    ring
  rw [h]
  exact q.mul_mem_right _ (hf k)

omit [Fintype ι] in
/-- **The Jacobian criterion at a prime, in the form of `IndepModSq`.**  If `c` elements of a
prime `q` of `K[ι]` have a `c × c` Jacobian minor outside `q`, their images in the local ring
`K[ι]_q` are independent modulo the square of the maximal ideal.

Clearing denominators, a relation `∑ aⱼ fⱼ ∈ 𝔪²` becomes `s · ∑ yⱼ fⱼ ∈ q²` with `s ∉ q` and
`yⱼ ∈ K[ι]`; differentiating, `s · ∑ yⱼ ∂ᵢfⱼ ∈ q` for every `i` (a derivative of `q²` lies in
`q`, and the terms with a factor `fⱼ` do too), so the vector `(yⱼ mod q)` is killed by the
Jacobian matrix over the domain `K[ι] ⧸ q`; the minor being invertible there, it vanishes,
i.e. `yⱼ ∈ q`, and `aⱼ ∈ q·K[ι]_q = 𝔪`. -/
theorem indepModSq_of_notMem_det {c : ℕ} (q : Ideal (MvPolynomial ι K)) [hq : q.IsPrime]
    {f : Fin c → MvPolynomial ι K} (hf : ∀ j, f j ∈ q) (S : Fin c ↪ ι)
    (hdet : (Matrix.of fun j k => pderiv (S k) (f j)).det ∉ q) :
    Height.Toolbox.IndepModSq
      (fun j => algebraMap (MvPolynomial ι K) (Localization.AtPrime q) (f j)) := by
  classical
  intro a ha j
  set φ := algebraMap (MvPolynomial ι K) (Localization.AtPrime q) with hφ
  have hmax : q.map φ = maximalIdeal (Localization.AtPrime q) :=
    IsLocalization.AtPrime.map_eq_maximalIdeal q _
  -- clear denominators
  obtain ⟨t, ht⟩ := IsLocalization.exist_integer_multiples_of_finite q.primeCompl a
  choose y hy using ht
  have hy' : ∀ k, φ (y k) = φ (t : MvPolynomial ι K) * a k := by
    intro k; rw [hy k, Algebra.smul_def]
  have hsum : φ (∑ k, y k * f k) = φ (t : MvPolynomial ι K) * ∑ k, a k * φ (f k) := by
    rw [map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [map_mul, hy' k]; ring
  have hmem2 : φ (∑ k, y k * f k) ∈ (q ^ 2).map φ := by
    rw [Ideal.map_pow, hmax, hsum]
    exact Ideal.mul_mem_left _ _ ha
  obtain ⟨s, hs, hsq⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff q.primeCompl (Localization.AtPrime q)
      (q ^ 2) _).mp hmem2
  -- differentiate
  have hfq : (∑ k, y k * f k) ∈ q := Ideal.sum_mem _ fun k _ => q.mul_mem_left _ (hf k)
  have hkey : ∀ i : ι, (∑ k, y k * pderiv i (f k)) ∈ q := by
    intro i
    have h1 : pderiv i (s * ∑ k, y k * f k) ∈ q := pderiv_mem_of_mem_sq q i hsq
    have h2 : (pderiv i) (s * ∑ k, y k * f k)
        = s * (pderiv i) (∑ k, y k * f k) + (∑ k, y k * f k) * (pderiv i) s := by
      rw [Derivation.leibniz]
      simp only [smul_eq_mul]
    have h4 : s * (pderiv i) (∑ k, y k * f k) ∈ q := by
      have h3 := q.sub_mem h1 (q.mul_mem_right ((pderiv i) s) hfq)
      rwa [h2, add_sub_cancel_right] at h3
    have h5 : s * (∑ k, y k * pderiv i (f k)) ∈ q := by
      have h6 := q.sub_mem h4 (q.mul_mem_left s (pderiv_sum_mul_sub_mem q i y f hf))
      rwa [mul_sub, sub_sub_cancel] at h6
    exact (hq.mem_or_mem h5).resolve_left hs
  -- the Jacobian matrix over the domain `K[ι] ⧸ q`
  have hdom : IsDomain (MvPolynomial ι K ⧸ q) := (Ideal.Quotient.isDomain_iff_prime q).mpr hq
  set v : Fin c → (MvPolynomial ι K ⧸ q) := fun k => Ideal.Quotient.mk q (y k) with hv
  set M : Matrix (Fin c) (Fin c) (MvPolynomial ι K ⧸ q) :=
    Matrix.of fun k l => Ideal.Quotient.mk q (pderiv (S l) (f k)) with hM
  have hvM : v ᵥ* M = 0 := by
    funext l
    show ∑ k, v k * M k l = 0
    rw [show ∑ k, v k * M k l
      = Ideal.Quotient.mk q (∑ k, y k * pderiv (S l) (f k)) by rw [map_sum]; rfl]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hkey (S l))
  have hdetM : M.det ≠ 0 := by
    have hmapdet : M.det
        = Ideal.Quotient.mk q (Matrix.of fun j k => pderiv (S k) (f j)).det := by
      rw [RingHom.map_det]
      rfl
    rw [hmapdet, Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact hdet
  have hyq : ∀ k, y k ∈ q := by
    intro k
    have h : v ᵥ* (M * M.adjugate) = 0 := by
      rw [← Matrix.vecMul_vecMul, hvM, Matrix.zero_vecMul]
    rw [Matrix.mul_adjugate] at h
    have hk := congrFun h k
    simp only [Matrix.vecMul, Matrix.smul_apply, Matrix.one_apply, dotProduct, smul_eq_mul,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
      Pi.zero_apply] at hk
    refine Ideal.Quotient.eq_zero_iff_mem.mp ?_
    exact (mul_eq_zero.mp hk).resolve_right hdetM
  -- conclude
  obtain ⟨u, hu⟩ := IsLocalization.map_units (Localization.AtPrime q) t
  have h6 : (u : Localization.AtPrime q) * a j = φ (y j) := by
    rw [hu, hy' j]
  have h7 : a j = (↑u⁻¹ : Localization.AtPrime q) * φ (y j) := by
    rw [← h6, ← mul_assoc, Units.inv_mul, one_mul]
  rw [h7, ← hmax]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (hyq j))


/-- **The Jacobian criterion at a prime.**  If `c` elements of a prime `q` of `K[ι]` have a
`c × c` Jacobian minor outside `q`, then the local ring at `q` of the complete intersection
they cut out is regular, of dimension `height q − c`.

`K[ι]_q` is a regular local ring (`MvPolynomial.isRegularRing_of_isRegularRing`), the `f j` are
independent modulo the square of its maximal ideal (`indepModSq_of_notMem_det`), and a quotient
of a regular local ring by such a family is regular
(`Toolbox.isRegularLocalRing_quotient_span_of_indepModSq`).  No hypothesis on the field. -/
theorem isRegularLocalRing_quotient_map_of_notMem_det {c : ℕ} (q : Ideal (MvPolynomial ι K))
    [q.IsPrime] {f : Fin c → MvPolynomial ι K} (hf : ∀ j, f j ∈ q) (S : Fin c ↪ ι)
    (hdet : (Matrix.of fun j k => pderiv (S k) (f j)).det ∉ q) :
    IsRegularLocalRing (Localization.AtPrime q ⧸ (Ideal.span (Set.range f)).map
        (algebraMap (MvPolynomial ι K) (Localization.AtPrime q))) ∧
      ringKrullDim (Localization.AtPrime q ⧸ (Ideal.span (Set.range f)).map
          (algebraMap (MvPolynomial ι K) (Localization.AtPrime q))) + (c : WithBot ℕ∞)
        = ((q.height : ℕ∞) : WithBot ℕ∞) := by
  have hreg : IsRegularLocalRing (Localization.AtPrime q) :=
    IsRegularRing.isRegularLocalRing_localization q
  have hmax : q.map (algebraMap (MvPolynomial ι K) (Localization.AtPrime q))
      = maximalIdeal (Localization.AtPrime q) :=
    IsLocalization.AtPrime.map_eq_maximalIdeal q _
  have hmem : ∀ j, algebraMap (MvPolynomial ι K) (Localization.AtPrime q) (f j)
      ∈ maximalIdeal (Localization.AtPrime q) := fun j => by
    rw [← hmax]; exact Ideal.mem_map_of_mem _ (hf j)
  obtain ⟨h1, h2⟩ := Height.Toolbox.isRegularLocalRing_quotient_span_of_indepModSq c
    (Localization.AtPrime q) _ hmem (indepModSq_of_notMem_det q hf S hdet)
  have hspan : Ideal.span (Set.range fun j =>
        algebraMap (MvPolynomial ι K) (Localization.AtPrime q) (f j))
      = (Ideal.span (Set.range f)).map
        (algebraMap (MvPolynomial ι K) (Localization.AtPrime q)) := by
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  rw [hspan] at h1 h2
  refine ⟨h1, ?_⟩
  rw [h2, IsLocalization.AtPrime.ringKrullDim_eq_height q (Localization.AtPrime q)]


/-- **The dimension of the local ring of `V(p)` at a prime `q ⊇ p`** is `height q − height p`:
the ring is the localisation of `K[ι] ⧸ p` at `q ⧸ p` (`Toolbox.quotientLocalizationEquiv`),
whose dimension is `height (q ⧸ p)`, and the dimension formula for the finitely generated
domain `K[ι] ⧸ p` (`Toolbox.height_add_ringKrullDim_quotient`) turns that into the
difference of the two heights. -/
theorem ringKrullDim_quotient_map_atPrime_add_height {p q : Ideal (MvPolynomial ι K)}
    [hp : p.IsPrime] [hq : q.IsPrime] (hpq : p ≤ q) :
    ringKrullDim (Localization.AtPrime q ⧸
          p.map (algebraMap (MvPolynomial ι K) (Localization.AtPrime q)))
        + ((p.height : ℕ∞) : WithBot ℕ∞) = ((q.height : ℕ∞) : WithBot ℕ∞) := by
  have hq' : (q.map (Ideal.Quotient.mk p)).IsPrime := Height.Toolbox.isPrime_map_mk hpq
  have hdomp : IsDomain (MvPolynomial ι K ⧸ p) := (Ideal.Quotient.isDomain_iff_prime p).mpr hp
  have hftp : Algebra.FiniteType K (MvPolynomial ι K ⧸ p) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ K p) Ideal.Quotient.mk_surjective
  -- the local ring is the localisation of `K[ι] ⧸ p` at `q ⧸ p`
  have h1 : ringKrullDim (Localization.AtPrime q ⧸
        p.map (algebraMap (MvPolynomial ι K) (Localization.AtPrime q)))
      = (((q.map (Ideal.Quotient.mk p)).height : ℕ∞) : WithBot ℕ∞) := by
    rw [← ringKrullDim_eq_of_ringEquiv (Height.Toolbox.quotientLocalizationEquiv hpq)]
    exact IsLocalization.AtPrime.ringKrullDim_eq_height (q.map (Ideal.Quotient.mk p))
      (Localization.AtPrime (q.map (Ideal.Quotient.mk p)))
  -- the dimension formula in `K[ι] ⧸ p`
  have h2 := Height.Toolbox.height_add_ringKrullDim_quotient (K := K) (MvPolynomial ι K ⧸ p)
    (q.map (Ideal.Quotient.mk p))
  have h3 : ringKrullDim ((MvPolynomial ι K ⧸ p) ⧸ (q.map (Ideal.Quotient.mk p)))
      = ringKrullDim (MvPolynomial ι K ⧸ q) :=
    ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hpq)
  rw [h3] at h2
  -- and in `K[ι]`
  obtain ⟨cp, dp, hcdp, hhp, hdimp⟩ := Height.Geometry.exists_ringKrullDim_quotient_eq K ι p
  obtain ⟨cq, dq, hcdq, hhq, hdimq⟩ := Height.Geometry.exists_ringKrullDim_quotient_eq K ι q
  obtain ⟨h', hh'⟩ : ∃ h' : ℕ, (q.map (Ideal.Quotient.mk p)).height = (h' : ℕ∞) :=
    ⟨_, (ENat.natCast_toNat (Ideal.height_ne_top hq'.ne_top)).symm⟩
  rw [hh', hdimq, hdimp] at h2
  have h2' : ((h' : ℕ∞) + (dq : ℕ∞) : ℕ∞) = ((dp : ℕ) : ℕ∞) := by exact_mod_cast h2
  have h4 : h' + dq = dp := by exact_mod_cast h2'
  have h5 : h' + cp = cq := by omega
  rw [h1, hh', hhp, hhq]
  exact_mod_cast congrArg (fun n : ℕ => ((n : ℕ∞) : WithBot ℕ∞)) h5

end Height.Geometry.Tangent
