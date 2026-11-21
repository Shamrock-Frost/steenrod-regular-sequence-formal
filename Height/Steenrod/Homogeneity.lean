import Height.Steenrod.Evaluation
import Height.Steenrod.Charpoly

/-!
# Homogeneity of the Steenrod operations (`rem:krull`)

The coefficient of `T^i` in the total operation on a homogeneous polynomial
of degree `d` is homogeneous of degree `d + i(q - 1)`.  We prove this by
keeping track of the degree of every coefficient through products of the
total images of the variables.

Homogeneity of the generators is what `rem:krull` needs to turn exact
height into a regular sequence.
-/

namespace Height.Steenrod

open Polynomial

/-- A polynomial in `T` has coefficient-degree offset `d` and step `k` if its
`i`th coefficient is homogeneous of degree `d + i*k`. -/
def HasCoefficientDegrees {R σ : Type*} [CommSemiring R]
    (k d : ℕ) (f : Polynomial (MvPolynomial σ R)) : Prop :=
  ∀ i, (f.coeff i).IsHomogeneous (d + i * k)

theorem HasCoefficientDegrees.mul {R σ : Type*} [CommSemiring R]
    {k d e : ℕ} {f g : Polynomial (MvPolynomial σ R)}
    (hf : HasCoefficientDegrees k d f)
    (hg : HasCoefficientDegrees k e g) :
    HasCoefficientDegrees k (d + e) (f * g) := by
  intro i
  rw [Polynomial.coeff_mul]
  apply MvPolynomial.IsHomogeneous.sum
  intro ij hij
  have hij' : ij.1 + ij.2 = i := Finset.mem_antidiagonal.mp hij
  convert (hf ij.1).mul (hg ij.2) using 1
  rw [← hij', Nat.add_mul]
  omega

theorem HasCoefficientDegrees.pow {R σ : Type*} [CommSemiring R]
    {k d : ℕ} {f : Polynomial (MvPolynomial σ R)}
    (hf : HasCoefficientDegrees k d f) (m : ℕ) :
    HasCoefficientDegrees k (m * d) (f ^ m) := by
  induction m with
  | zero =>
      intro i
      by_cases hi : i = 0
      · subst i
        simpa using (MvPolynomial.isHomogeneous_one σ R :
          (1 : MvPolynomial σ R).IsHomogeneous 0)
      · rw [pow_zero]
        rw [Polynomial.coeff_one, ite_eq_right hi]
        simpa only [zero_mul, zero_add] using
          MvPolynomial.isHomogeneous_zero σ R (i * k)
  | succ m ih =>
      rw [pow_succ]
      simpa only [Nat.succ_mul] using ih.mul hf

theorem HasCoefficientDegrees.prod_pow {R σ ι : Type*} [CommSemiring R]
    {k : ℕ} (s : Finset ι) (f : ι → Polynomial (MvPolynomial σ R))
    (d e : ι → ℕ) (hf : ∀ x ∈ s, HasCoefficientDegrees k (d x) (f x)) :
    HasCoefficientDegrees k (∑ x ∈ s, e x * d x) (∏ x ∈ s, f x ^ e x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.prod_empty, Finset.sum_empty]
      intro i
      by_cases hi : i = 0
      · subst i
        simpa using (MvPolynomial.isHomogeneous_one σ R :
          (1 : MvPolynomial σ R).IsHomogeneous 0)
      · rw [Polynomial.coeff_one, ite_eq_right hi]
        simpa only [zero_add] using MvPolynomial.isHomogeneous_zero σ R (i * k)
  | @insert x s hx ih =>
      rw [Finset.prod_insert hx, Finset.sum_insert hx]
      exact (hf x (Finset.mem_insert_self x s)).pow (e x) |>.mul
        (ih fun y hy => hf y (Finset.mem_insert_of_mem hy))

universe u

variable (p r : ℕ) [Fact p.Prime]
variable {ι : Type u}

private theorem totalGenerator_hasCoefficientDegrees (x : ι) :
    HasCoefficientDegrees (QSteenrod.q p r - 1) 1
      (QSteenrod.totalGenerator (ι := ι) p r x) := by
  intro i
  rcases i with _ | i
  · simpa [QSteenrod.totalGenerator] using
      (MvPolynomial.isHomogeneous_X (GaloisField p r) x)
  · rcases i with _ | i
    · have hq : 0 < QSteenrod.q p r :=
        pow_pos (Fact.out : Nat.Prime p).pos _
      have hx := MvPolynomial.isHomogeneous_X_pow
        (R := GaloisField p r) x (QSteenrod.q p r)
      have hcoeff :
          (QSteenrod.totalGenerator (ι := ι) p r x).coeff 1 =
            MvPolynomial.X x ^ QSteenrod.q p r := by
        simp [QSteenrod.totalGenerator]
      rw [hcoeff]
      convert hx using 1
      omega
    · simp [QSteenrod.totalGenerator, Polynomial.coeff_monomial,
        MvPolynomial.isHomogeneous_zero]

private theorem total_monomial_hasCoefficientDegrees
    (m : ι →₀ ℕ) (a : GaloisField p r) :
    HasCoefficientDegrees (QSteenrod.q p r - 1) m.degree
      (QSteenrod.total (ι := ι) p r (MvPolynomial.monomial m a)) := by
  classical
  rw [QSteenrod.total, MvPolynomial.aeval_monomial]
  have hconst : HasCoefficientDegrees (QSteenrod.q p r - 1) 0
      (algebraMap (GaloisField p r)
        (Polynomial (MvPolynomial ι (GaloisField p r))) a) := by
    intro i
    by_cases hi : i = 0
    · subst i
      simpa using (MvPolynomial.isHomogeneous_C ι a :
        (MvPolynomial.C a : MvPolynomial ι (GaloisField p r)).IsHomogeneous 0)
    · rw [Polynomial.algebraMap_apply]
      rw [Polynomial.coeff_C, ite_eq_right hi]
      simpa only [zero_add] using
        MvPolynomial.isHomogeneous_zero ι (GaloisField p r)
          (i * (QSteenrod.q p r - 1))
  have hprod : HasCoefficientDegrees (QSteenrod.q p r - 1)
      (∑ x ∈ m.support, m x * 1)
      (m.prod fun x e => QSteenrod.totalGenerator (ι := ι) p r x ^ e) := by
    rw [Finsupp.prod]
    exact HasCoefficientDegrees.prod_pow m.support
      (QSteenrod.totalGenerator (ι := ι) p r) (fun _ => 1) m
      (fun x _ => totalGenerator_hasCoefficientDegrees p r x)
  convert hconst.mul hprod using 1
  · rw [Finsupp.degree_apply]
    simp

/-- The `i`th `q`-Steenrod operation sends a homogeneous polynomial of degree
`d` to a homogeneous polynomial of degree `d + i(q-1)`. -/
theorem P_isHomogeneous {f : MvPolynomial ι (GaloisField p r)} {d : ℕ}
    (hf : f.IsHomogeneous d) (i : ℕ) :
    (QSteenrod.P (ι := ι) p r i f).IsHomogeneous
      (d + i * (QSteenrod.q p r - 1)) := by
  rw [f.as_sum, map_sum]
  apply MvPolynomial.IsHomogeneous.sum
  intro m hm
  rw [QSteenrod.P_apply]
  have hd := hf (MvPolynomial.mem_support_iff.mp hm)
  simp only [Finsupp.weight_apply, Pi.one_apply, smul_eq_mul, mul_one] at hd
  change m.degree = d at hd
  convert total_monomial_hasCoefficientDegrees p r m (f.coeff m) i using 1
  simp [hd]

/-- In particular, the triangular generator `P^i(c_j)` has its expected
degree `j + i(q-1)`. -/
theorem P_characteristicCoefficient_isHomogeneous (N j i : ℕ) (hj : j ≤ N) :
    (QSteenrod.P p r i (QSteenrod.c p r N j)).IsHomogeneous
      (j + i * (QSteenrod.q p r - 1)) :=
  P_isHomogeneous p r (characteristicCoefficient_isHomogeneous p r N j hj) i

end Height.Steenrod
