import QSteenrod.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.Expand

/-!
# Evaluation of the total Steenrod operation (`lem:evaluation`)

This is the algebraic content of `lem:evaluation`: after evaluating the
coefficients at a point `M`, the total operation is ordinary substitution
`x ↦ M x + (M x)^q T`.
-/

namespace Height.Steenrod


open Polynomial

universe u v

/-- Substituting polynomials of degree at most one into a homogeneous
multivariate polynomial of degree `d` produces a polynomial of degree at most
`d`. -/
theorem natDegree_aeval_le_of_isHomogeneous
    {R S σ : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
    {f : MvPolynomial σ R} {d : ℕ} (hf : f.IsHomogeneous d)
    (g : σ → Polynomial S) (hg : ∀ x, (g x).natDegree ≤ 1) :
    (MvPolynomial.aeval g f).natDegree ≤ d := by
  rw [f.as_sum, map_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro m hm
  rw [MvPolynomial.aeval_monomial]
  refine le_trans Polynomial.natDegree_mul_le ?_
  have hprod :
      (m.prod fun x k => g x ^ k).natDegree ≤ ∑ x ∈ m.support, m x := by
    rw [Finsupp.prod]
    refine le_trans (Polynomial.natDegree_prod_le _ _) ?_
    apply Finset.sum_le_sum
    intro x hx
    exact Polynomial.natDegree_pow_le.trans (by
      simpa using Nat.mul_le_mul_left (m x) (hg x))
  have hcoeff :
      (algebraMap R (Polynomial S) (f.coeff m)).natDegree = 0 := by
    simp
  rw [hcoeff, zero_add]
  calc
    (m.prod fun x k => g x ^ k).natDegree ≤ ∑ x ∈ m.support, m x := hprod
    _ = d := by
      have hd := hf (MvPolynomial.mem_support_iff.mp hm)
      simp only [Finsupp.weight_apply, Pi.one_apply, smul_eq_mul, mul_one] at hd
      change (∑ x ∈ m.support, m x) = d at hd
      exact hd

private theorem coeff_prod_pow_top
    {S σ : Type*} [CommSemiring S] (g : σ → Polynomial S)
    (hg : ∀ x, (g x).natDegree ≤ 1) (s : Finset σ) (e : σ → ℕ) :
    (∏ x ∈ s, g x ^ e x).coeff (∑ x ∈ s, e x) =
      ∏ x ∈ s, (g x).coeff 1 ^ e x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hx ih =>
      rw [Finset.prod_insert hx, Finset.sum_insert hx, Finset.prod_insert hx]
      rw [Polynomial.coeff_mul_add_eq_of_natDegree_le]
      · have hp := Polynomial.coeff_pow_of_natDegree_le
          (p := g x) (m := e x) (n := 1) (hg x)
        simp only [mul_one] at hp
        rw [hp, ih]
      · exact Polynomial.natDegree_pow_le.trans (by
          simpa using Nat.mul_le_mul_left (e x) (hg x))
      · refine (Polynomial.natDegree_prod_le _ _).trans ?_
        apply Finset.sum_le_sum
        intro y hy
        exact Polynomial.natDegree_pow_le.trans (by
          simpa using Nat.mul_le_mul_left (e y) (hg y))

/-- For a homogeneous polynomial, the top possible coefficient after a
degree-one polynomial substitution is obtained by substituting the linear
coefficients. -/
theorem coeff_aeval_eq_aeval_coeff_one_of_isHomogeneous
    {R S σ : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
    {f : MvPolynomial σ R} {d : ℕ} (hf : f.IsHomogeneous d)
    (g : σ → Polynomial S) (hg : ∀ x, (g x).natDegree ≤ 1) :
    (MvPolynomial.aeval g f).coeff d =
      MvPolynomial.aeval (fun x => (g x).coeff 1) f := by
  classical
  rw [f.as_sum]
  simp only [map_sum]
  change (Polynomial.lcoeff S d)
    (∑ x ∈ f.support,
      MvPolynomial.aeval g (MvPolynomial.monomial x (f.coeff x))) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro m hm
  simp only [MvPolynomial.aeval_monomial]
  have hd := hf (MvPolynomial.mem_support_iff.mp hm)
  simp only [Finsupp.weight_apply, Pi.one_apply, smul_eq_mul, mul_one] at hd
  change (∑ x ∈ m.support, m x) = d at hd
  rw [← hd, Polynomial.algebraMap_apply]
  change (Polynomial.C ((algebraMap R S) (f.coeff m)) *
      m.prod fun i k => g i ^ k).coeff (∑ x ∈ m.support, m x) = _
  rw [Polynomial.coeff_C_mul, Finsupp.prod, coeff_prod_pow_top g hg]
  rfl

variable (p r : ℕ) [Fact p.Prime]
variable {ι : Type u} {K : Type v} [CommSemiring K] [Algebra (GaloisField p r) K]

/-- The zeroth Steenrod operation is the identity. -/
theorem P_zero (f : MvPolynomial ι (GaloisField p r)) :
    QSteenrod.P (ι := ι) p r 0 f = f := by
  let cc : Polynomial (MvPolynomial ι (GaloisField p r)) →ₐ[GaloisField p r]
      MvPolynomial ι (GaloisField p r) :=
    { Polynomial.constantCoeff with
      commutes' := fun x => by simp }
  let lhs : MvPolynomial ι (GaloisField p r) →ₐ[GaloisField p r]
      MvPolynomial ι (GaloisField p r) :=
    cc.comp (QSteenrod.total (ι := ι) p r)
  have h : lhs = AlgHom.id _ _ := MvPolynomial.algHom_ext fun x => by
    simp [lhs, cc, QSteenrod.totalGenerator, Polynomial.constantCoeff,
      Polynomial.coeff_monomial]
  exact DFunLike.congr_fun h f

/-- The total Steenrod operation of a homogeneous degree-`d` polynomial has
ordinary `T`-degree at most `d`. -/
theorem total_natDegree_le_of_isHomogeneous
    {f : MvPolynomial ι (GaloisField p r)} {d : ℕ}
    (hf : f.IsHomogeneous d) :
    (QSteenrod.total (ι := ι) p r f).natDegree ≤ d := by
  apply natDegree_aeval_le_of_isHomogeneous hf
  intro x
  exact Polynomial.natDegree_add_le_of_degree_le
    (by simp) (Polynomial.natDegree_monomial_le _)

/-- Steenrod powers above the homogeneous degree vanish. -/
theorem P_eq_zero_of_isHomogeneous
    {f : MvPolynomial ι (GaloisField p r)} {d i : ℕ}
    (hf : f.IsHomogeneous d) (hdi : d < i) :
    QSteenrod.P (ι := ι) p r i f = 0 := by
  rw [QSteenrod.P_apply]
  exact Polynomial.coeff_eq_zero_of_natDegree_lt
    ((total_natDegree_le_of_isHomogeneous p r hf).trans_lt hdi)

/-- The top Steenrod power of a homogeneous polynomial is obtained by the
substitution `x ↦ x^q`. -/
theorem P_top_eq_aeval_pow_of_isHomogeneous
    {f : MvPolynomial ι (GaloisField p r)} {d : ℕ}
    (hf : f.IsHomogeneous d) :
    QSteenrod.P (ι := ι) p r d f =
      MvPolynomial.aeval (fun x => MvPolynomial.X x ^ QSteenrod.q p r) f := by
  rw [QSteenrod.P_apply]
  simpa [QSteenrod.total, QSteenrod.totalGenerator] using
    (coeff_aeval_eq_aeval_coeff_one_of_isHomogeneous hf
      (QSteenrod.totalGenerator (ι := ι) p r) (fun x =>
        Polynomial.natDegree_add_le_of_degree_le
          (by simp) (Polynomial.natDegree_monomial_le _)))

/-- Over the coefficient field `F_q`, the top Steenrod power of a homogeneous
degree-`d` polynomial is its `q`th power. -/
theorem P_top_eq_pow_of_isHomogeneous [NeZero r]
    {f : MvPolynomial ι (GaloisField p r)} {d : ℕ}
    (hf : f.IsHomogeneous d) :
    QSteenrod.P (ι := ι) p r d f = f ^ QSteenrod.q p r := by
  rw [P_top_eq_aeval_pow_of_isHomogeneous p r hf]
  change MvPolynomial.expand (QSteenrod.q p r) f = _
  let := Fintype.ofFinite (GaloisField p r)
  have hcard : Fintype.card (GaloisField p r) = QSteenrod.q p r := by
    simpa only [Nat.card_eq_fintype_card] using QSteenrod.card_galoisField p r
  simpa only [hcard] using FiniteField.MvPolynomial.expand_card f

/-- `lem:evaluation`: evaluating the total Steenrod power at `M` is the
substitution `x ↦ M x + (M x)^q T`. -/
theorem evaluation (M : ι → K) (f : MvPolynomial ι (GaloisField p r)) :
    (Polynomial.mapAlgHom (MvPolynomial.aeval M))
        (QSteenrod.total (ι := ι) p r f) =
      MvPolynomial.aeval
        (fun x => C (M x) + monomial 1 (M x ^ QSteenrod.q p r)) f := by
  let lhs : MvPolynomial ι (GaloisField p r) →ₐ[GaloisField p r] Polynomial K :=
    (Polynomial.mapAlgHom (MvPolynomial.aeval M)).comp
      (QSteenrod.total (ι := ι) p r)
  let rhs : MvPolynomial ι (GaloisField p r) →ₐ[GaloisField p r] Polynomial K :=
    MvPolynomial.aeval
      (fun x => C (M x) + monomial 1 (M x ^ QSteenrod.q p r))
  have h : lhs = rhs := MvPolynomial.algHom_ext fun x => by
    simp [lhs, rhs, QSteenrod.totalGenerator]
  exact DFunLike.congr_fun h f

/-- Coefficient form of `evaluation`. -/
theorem evaluation_coeff (M : ι → K) (f : MvPolynomial ι (GaloisField p r))
    (i : ℕ) :
    MvPolynomial.aeval M (QSteenrod.P (ι := ι) p r i f) =
      (MvPolynomial.aeval
        (fun x => C (M x) + monomial 1 (M x ^ QSteenrod.q p r)) f).coeff i := by
  have h := congrArg (fun g : Polynomial K => g.coeff i) (evaluation p r M f)
  simpa using h

end Height.Steenrod
