import Mathlib.Algebra.MvPolynomial.Division
import Height.Graded.Basic

/-!
# Reduction modulo `μ` on homogeneous pieces

The proof of `lem:free` reduces a saturated graded submodule `S ⊆ F` modulo
`μ` and works over the principal ideal domain `K[ν]`.  On a *homogeneous*
piece the whole of that reduction is carried by a single linear functional:
for `f ∈ B_d`,

```
nuLead d f := coefficient of ν^d in f,
```

because `B_d ∩ μB` is exactly the kernel of `nuLead d` (`mu_dvd_iff`), and
`B_d/(B_d ∩ μB) ≅ K` via `nuLead d`.  Reducing modulo `μ` therefore never
needs the quotient ring `B/μB ≅ K[ν]`: the graded pieces of the reduction are
the images of `nuLead`, and `K[ν]` enters only through the multiplication
rules `nuLead_nu_mul` (`ν` acts as the identity on leading coefficients) and
`nuLead_mul`.
-/

noncomputable section

namespace Height.Graded

open MvPolynomial

variable {K : Type*} [Field K]

/-! ### Homogeneity in two variables, in terms of exponent sums -/

theorem weight_one_eq (s : Fin 2 →₀ ℕ) :
    Finsupp.weight (1 : Fin 2 → ℕ) s = s 0 + s 1 := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp [Fin.sum_univ_two]

theorem exponent_sum_of_isHomogeneous {n : ℕ} {f : Poly K} (hf : f.IsHomogeneous n)
    {s : Fin 2 →₀ ℕ} (hs : f.coeff s ≠ 0) : s 0 + s 1 = n := by
  have h := hf hs
  rwa [weight_one_eq] at h

theorem isHomogeneous_of_exponent_sum {n : ℕ} {f : Poly K}
    (h : ∀ s : Fin 2 →₀ ℕ, f.coeff s ≠ 0 → s 0 + s 1 = n) : f.IsHomogeneous n := by
  intro s hs
  rw [weight_one_eq]
  exact h s hs

/-! ### The leading coefficient along `ν` -/

/-- The coefficient of `ν^d` in `f` (zero when `d < 0`).  On `B_d` this is the
reduction of `f` modulo `μ`, read in the basis `ν^d` of `(B/μB)_d`. -/
def nuLead (d : ℤ) : Poly K →ₗ[K] K :=
  if 0 ≤ d then lcoeff K (Finsupp.single 1 d.toNat) else 0

theorem nuLead_of_nonneg {d : ℤ} (hd : 0 ≤ d) (f : Poly K) :
    nuLead d f = f.coeff (Finsupp.single 1 d.toNat) := by
  simp [nuLead, hd, lcoeff]

/-- The only exponent vector of degree `n` with vanishing `μ`-exponent. -/
theorem eq_single_of_exponent {n : ℕ} {s : Fin 2 →₀ ℕ} (h : s 0 + s 1 = n) (h0 : s 0 = 0) :
    s = Finsupp.single 1 n := by
  refine Finsupp.ext fun i => ?_
  fin_cases i <;> simp [] <;> omega

/-- A homogeneous element of degree `d` is divisible by `μ` exactly when its
`ν^d`-coefficient vanishes. -/
theorem mu_dvd_iff {d : ℤ} {f : Poly K} (hf : f ∈ Bpiece K d) :
    (mu : Poly K) ∣ f ↔ nuLead d f = 0 := by
  rcases lt_or_ge d 0 with hd | hd
  · rw [Bpiece_of_neg hd, Submodule.mem_bot] at hf
    simp [hf]
  rw [mem_Bpiece_of_nonneg hd] at hf
  rw [nuLead_of_nonneg hd, mu, X_dvd_iff_modMonomial_eq_zero]
  have hnotle : ¬ Finsupp.single (0 : Fin 2) 1 ≤ Finsupp.single (1 : Fin 2) d.toNat := by
    intro hle
    have := hle 0
    simp [] at this
  constructor
  · intro h
    have h2 := congrArg (fun p : Poly K => p.coeff (Finsupp.single 1 d.toNat)) h
    simp only [AddMonoidAlgebra.coeff_zero] at h2
    rwa [MvPolynomial.coeff_modMonomial_of_not_le _ hnotle] at h2
  · intro h
    ext s
    simp only [AddMonoidAlgebra.coeff_zero]
    by_cases hle : Finsupp.single (0 : Fin 2) 1 ≤ s
    · exact MvPolynomial.coeff_modMonomial_of_le _ hle
    · rw [MvPolynomial.coeff_modMonomial_of_not_le _ hle]
      by_contra hs
      have hsum := exponent_sum_of_isHomogeneous hf hs
      have hs0 : s 0 = 0 := by
        by_contra h0
        refine hle fun i => ?_
        fin_cases i <;> simp [] <;> omega
      rw [eq_single_of_exponent hsum hs0] at hs
      exact hs h

/-- If `μ * g` is homogeneous of degree `d`, then `g` is homogeneous of degree `d - 1`. -/
theorem mem_Bpiece_of_mu_mul {d : ℤ} {g : Poly K} (h : mu * g ∈ Bpiece K d) :
    g ∈ Bpiece K (d - 1) := by
  have hmu : (mu : Poly K) ≠ 0 := by simp [mu, MvPolynomial.X_ne_zero]
  rcases lt_or_ge d 0 with hd | hd
  · rw [Bpiece_of_neg hd, Submodule.mem_bot] at h
    rw [Bpiece_of_neg (by omega), Submodule.mem_bot]
    rcases mul_eq_zero.1 h with h1 | h1
    · exact absurd h1 hmu
    · exact h1
  rw [mem_Bpiece_of_nonneg hd] at h
  have key : ∀ s : Fin 2 →₀ ℕ, g.coeff s ≠ 0 → 1 + (s 0 + s 1) = d.toNat := by
    intro s hs
    have hc : (mu * g).coeff (Finsupp.single (0 : Fin 2) 1 + s) = g.coeff s := by
      rw [mu, MvPolynomial.coeff_X_mul]
    have hsum := exponent_sum_of_isHomogeneous h (by rw [hc]; exact hs)
    have e0 : (Finsupp.single (0 : Fin 2) 1 + s : Fin 2 →₀ ℕ) 0 = 1 + s 0 := by simp
    have e1 : (Finsupp.single (0 : Fin 2) 1 + s : Fin 2 →₀ ℕ) 1 = s 1 := by simp
    rw [e0, e1] at hsum
    omega
  rcases lt_or_ge (d - 1) 0 with hd1 | hd1
  · rw [Bpiece_of_neg hd1, Submodule.mem_bot]
    by_contra hg
    obtain ⟨s, hs⟩ := MvPolynomial.ne_zero_iff.1 hg
    have := key s hs
    omega
  · rw [mem_Bpiece_of_nonneg hd1]
    exact isHomogeneous_of_exponent_sum fun s hs => by have := key s hs; omega

/-- The divisor supplied by `mu_dvd_iff` is again homogeneous, of degree `d-1`. -/
theorem exists_eq_mu_mul {d : ℤ} {f : Poly K} (hf : f ∈ Bpiece K d) (h : nuLead d f = 0) :
    ∃ g ∈ Bpiece K (d - 1), f = mu * g := by
  obtain ⟨g, hg⟩ := (mu_dvd_iff hf).2 h
  exact ⟨g, mem_Bpiece_of_mu_mul (hg ▸ hf), hg⟩

/-! ### Multiplicativity -/

theorem mu_mem : (mu : Poly K) ∈ Bpiece K 1 := by
  rw [show (1 : ℤ) = ((1 : ℕ) : ℤ) from rfl, Bpiece_natCast]
  exact MvPolynomial.isHomogeneous_X _ _

theorem nu_mem : (nu : Poly K) ∈ Bpiece K 1 := by
  rw [show (1 : ℤ) = ((1 : ℕ) : ℤ) from rfl, Bpiece_natCast]
  exact MvPolynomial.isHomogeneous_X _ _

@[simp] theorem nuLead_nu : nuLead (1 : ℤ) (nu : Poly K) = 1 := by
  classical
  rw [nuLead_of_nonneg (by norm_num)]
  simp [nu, MvPolynomial.coeff_X]

@[simp] theorem nuLead_mu : nuLead (1 : ℤ) (mu : Poly K) = 0 := by
  classical
  rw [nuLead_of_nonneg (by norm_num)]
  rw [mu, MvPolynomial.coeff_X]
  rw [ite_eq_right]
  intro hcon
  have := congrArg (fun t : Fin 2 →₀ ℕ => t 0) hcon
  simp [] at this

/-- The leading coefficient along `ν` is multiplicative on homogeneous elements:
it is the reduction modulo `μ`. -/
theorem nuLead_mul {d n : ℤ} {f g : Poly K} (hf : f ∈ Bpiece K d) (hg : g ∈ Bpiece K n) :
    nuLead (d + n) (f * g) = nuLead d f * nuLead n g := by
  classical
  rcases lt_or_ge d 0 with hd | hd
  · rw [Bpiece_of_neg hd, Submodule.mem_bot] at hf; simp [hf]
  rcases lt_or_ge n 0 with hn | hn
  · rw [Bpiece_of_neg hn, Submodule.mem_bot] at hg; simp [hg]
  rw [mem_Bpiece_of_nonneg hd] at hf
  rw [mem_Bpiece_of_nonneg hn] at hg
  rw [nuLead_of_nonneg (by omega), nuLead_of_nonneg hd, nuLead_of_nonneg hn]
  have hm : (d + n).toNat = d.toNat + n.toNat := by omega
  rw [hm, MvPolynomial.coeff_mul]
  refine Finset.sum_eq_single (Finsupp.single 1 d.toNat, Finsupp.single 1 n.toNat) ?_ ?_
  · intro b hb hne
    by_contra hcon
    have h1 : f.coeff b.1 ≠ 0 := fun h => hcon (by rw [h, zero_mul])
    have h2 : g.coeff b.2 ≠ 0 := fun h => hcon (by rw [h, mul_zero])
    have hb' : b.1 + b.2 = (Finsupp.single (1 : Fin 2) (d.toNat + n.toNat) : Fin 2 →₀ ℕ) :=
      Finset.HasAntidiagonal.mem_antidiagonal.1 hb
    have hzero := congrArg (fun t : Fin 2 →₀ ℕ => t 0) hb'
    simp only [Finsupp.add_apply] at hzero
    have hs : (Finsupp.single (1 : Fin 2) (d.toNat + n.toNat) : Fin 2 →₀ ℕ) 0 = 0 := by simp
    rw [hs] at hzero
    have hu : b.1 = Finsupp.single 1 d.toNat :=
      eq_single_of_exponent (exponent_sum_of_isHomogeneous hf h1) (by omega)
    have hv : b.2 = Finsupp.single 1 n.toNat :=
      eq_single_of_exponent (exponent_sum_of_isHomogeneous hg h2) (by omega)
    exact hne (Prod.ext hu hv)
  · intro h
    refine absurd (Finset.HasAntidiagonal.mem_antidiagonal.2 ?_) h
    show (Finsupp.single (1 : Fin 2) d.toNat : Fin 2 →₀ ℕ) +
      (Finsupp.single (1 : Fin 2) n.toNat : Fin 2 →₀ ℕ) =
      (Finsupp.single (1 : Fin 2) (d.toNat + n.toNat) : Fin 2 →₀ ℕ)
    exact (Finsupp.single_add _ _ _).symm

theorem nu_pow_mem (k : ℕ) : (nu ^ k : Poly K) ∈ Bpiece K (k : ℤ) := by
  rw [Bpiece_natCast, MvPolynomial.mem_homogeneousSubmodule]
  simpa [nu] using (MvPolynomial.isHomogeneous_X K (1 : Fin 2)).pow k

theorem mu_pow_mem (k : ℕ) : (mu ^ k : Poly K) ∈ Bpiece K (k : ℤ) := by
  rw [Bpiece_natCast, MvPolynomial.mem_homogeneousSubmodule]
  simpa [mu] using (MvPolynomial.isHomogeneous_X K (0 : Fin 2)).pow k

/-- `ν` acts as the identity on leading coefficients. -/
theorem nuLead_nu_mul {n : ℤ} {g : Poly K} (hg : g ∈ Bpiece K n) :
    nuLead (1 + n) (nu * g) = nuLead n g := by
  rw [nuLead_mul nu_mem hg, nuLead_nu, one_mul]

/-- `μ` kills leading coefficients. -/
theorem nuLead_mu_mul {n : ℤ} {g : Poly K} (hg : g ∈ Bpiece K n) :
    nuLead (1 + n) (mu * g) = 0 := by
  rw [nuLead_mul mu_mem hg, nuLead_mu, zero_mul]

@[simp] theorem nuLead_nu_pow (k : ℕ) : nuLead (k : ℤ) (nu ^ k : Poly K) = 1 := by
  induction k with
  | zero => simpa using nuLead_of_nonneg (K := K) le_rfl 1
  | succ k ih =>
      have h := nuLead_nu_mul (K := K) (nu_pow_mem k)
      rw [show (nu : Poly K) * nu ^ k = nu ^ (k + 1) by ring] at h
      rw [show (((k + 1 : ℕ) : ℤ)) = 1 + (k : ℤ) by push_cast; ring, h, ih]

end Height.Graded
