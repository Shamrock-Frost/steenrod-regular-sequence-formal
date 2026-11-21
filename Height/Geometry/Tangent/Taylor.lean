import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.Ideal.Operations

/-!
# First-order Taylor expansion for multivariate polynomials

The first-order expansion consumed by `Tangent/Generic.lean` (`sub_taylor_mem_sq`)
and `Tangent/Newton.lean`: for `f : MvPolynomial ι R` and a displacement `y` all of whose
coordinates lie in an ideal `J` of an `R`-algebra `A`,

```
aeval (x + y) f ≡ aeval x f + ∑ i, aeval x (pderiv i f) * y i   [mod J ^ 2].
```

`Height.Geometry.Tangent.taylorError x y f` is the left-hand side minus the
right-hand side and `taylorError_mem_sq` is the statement.  The proof is
`MvPolynomial.induction_on`; the multiplicative step is the identity

```
E (f * X n) = (∑ i, aeval x (pderiv i f) * y i) * y n + E f * (x n + y n)
```

(`taylorError_mul_X`), both of whose summands are visibly in `J ^ 2` once
`E f` is.  The first-order consequence `aeval_sub_aeval_mem` (congruence of
`aeval` along a congruence of the arguments) is recorded too.
-/

universe u v

open MvPolynomial

namespace Height.Geometry.Tangent

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
variable {ι : Type*} [Fintype ι]

/-- The first-order Taylor error of `f` at `x` in the direction `y`. -/
noncomputable def taylorError (x y : ι → A) (f : MvPolynomial ι R) : A :=
  aeval (x + y) f - aeval x f - ∑ i, aeval x (pderiv i f) * y i

lemma taylorError_def (x y : ι → A) (f : MvPolynomial ι R) :
    taylorError x y f =
      aeval (x + y) f - aeval x f - ∑ i, aeval x (pderiv i f) * y i := rfl

@[simp] lemma taylorError_C (x y : ι → A) (a : R) :
    taylorError x y (C a : MvPolynomial ι R) = 0 := by
  simp [taylorError]

lemma taylorError_add (x y : ι → A) (f g : MvPolynomial ι R) :
    taylorError x y (f + g) = taylorError x y f + taylorError x y g := by
  simp only [taylorError, map_add, add_mul, Finset.sum_add_distrib]
  ring

/-- The multiplicative step of the first-order Taylor expansion. -/
lemma taylorError_mul_X (x y : ι → A) (f : MvPolynomial ι R) (n : ι) :
    taylorError x y (f * X n) =
      (∑ i, aeval x (pderiv i f) * y i) * y n + taylorError x y f * (x n + y n) := by
  have expand : ∀ i : ι, aeval (R := R) x (pderiv i (f * X n)) * y i =
      aeval x (pderiv i f) * y i * x n + aeval x (f * pderiv i (X n)) * y i := by
    intro i
    rw [pderiv_mul]
    simp only [map_add, map_mul, aeval_X]
    ring
  have hsum : (∑ i, aeval (R := R) x (pderiv i (f * X n)) * y i) =
      (∑ i, aeval x (pderiv i f) * y i) * x n + aeval x f * y n := by
    rw [Finset.sum_congr rfl fun i _ => expand i, Finset.sum_add_distrib, ← Finset.sum_mul]
    congr 1
    rw [Finset.sum_eq_single n]
    · rw [pderiv_X_self]; simp
    · intro b _ hb; rw [pderiv_X_of_ne hb.symm]; simp
    · intro h; exact absurd (Finset.mem_univ n) h
  simp only [taylorError, map_mul, aeval_X, hsum, Pi.add_apply]
  ring

/-- **First-order Taylor.**  If every coordinate of the displacement `y` lies in
the ideal `J`, then `aeval (x + y) f` agrees with its first-order Taylor
expansion at `x` modulo `J ^ 2`. -/
theorem taylorError_mem_sq (J : Ideal A) {x y : ι → A} (hy : ∀ i, y i ∈ J)
    (f : MvPolynomial ι R) : taylorError x y f ∈ J ^ 2 := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [taylorError_add]; exact Ideal.add_mem _ hp hq
  | mul_X p n hp =>
    rw [taylorError_mul_X]
    refine Ideal.add_mem _ ?_ (Ideal.mul_mem_right _ _ hp)
    rw [sq, Finset.sum_mul]
    refine Submodule.sum_mem _ fun i _ => ?_
    have h : aeval (R := R) x (pderiv i p) * y i * y n
        = aeval x (pderiv i p) * (y i * y n) := by ring
    rw [h]
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_mul (hy i) (hy n))

/-- The Taylor expansion in the form used by the Newton iteration: an explicit
first-order expansion with an error term in `J ^ 2`. -/
theorem aeval_add_eq (J : Ideal A) {x y : ι → A} (hy : ∀ i, y i ∈ J)
    (f : MvPolynomial ι R) :
    ∃ e ∈ J ^ 2, aeval (x + y) f = aeval x f + (∑ i, aeval x (pderiv i f) * y i) + e :=
  ⟨taylorError x y f, taylorError_mem_sq J hy f, by rw [taylorError_def]; ring⟩

/-- `aeval` is a congruence for the ideal `J`: arguments congruent mod `J` give
values congruent mod `J`. -/
theorem aeval_sub_aeval_mem (J : Ideal A) {x y : ι → A} (h : ∀ i, y i - x i ∈ J)
    (f : MvPolynomial ι R) : aeval y f - aeval x f ∈ J := by
  have hxy : y = x + (y - x) := by funext i; simp
  obtain ⟨e, he, hf⟩ := aeval_add_eq (x := x) (y := y - x) J (fun i => h i) f
  have : aeval y f - aeval x f = (∑ i, aeval x (pderiv i f) * (y - x) i) + e := by
    rw [← hxy] at hf; rw [hf]; ring
  rw [this]
  refine Ideal.add_mem _ (Submodule.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ ?_) ?_
  · simpa using h i
  · exact (Ideal.pow_le_self (by norm_num)) he

end Height.Geometry.Tangent
