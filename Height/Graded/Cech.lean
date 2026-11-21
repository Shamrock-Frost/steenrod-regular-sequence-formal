import Height.Graded.Lead

/-!
# Homogeneous monomials in `K[μ, ν]`

A monomial is a product of powers of `μ` and `ν`; the homogeneous piece `B_n` is
their span, and each such product lies in its expected homogeneous piece.

`monExp p q` is the exponent vector of `μ^p ν^q` and `gmon K e a = μ^{e-a} ν^a`
is the `a`-th monomial of degree `e`; `sum_coeff_smul_gmon` expands a form of
degree `e` in them and `mul_gmon` multiplies one by a form.
-/

noncomputable section

namespace Height.Graded

open MvPolynomial

variable {K : Type*} [Field K]

/-! ### `B_n` as a span of monomials -/

theorem monomial_eq_mu_nu (s : Fin 2 →₀ ℕ) :
    (monomial s (1 : K) : Poly K) = mu ^ s 0 * nu ^ s 1 := by
  rw [MvPolynomial.monomial_eq, map_one, one_mul,
    Finsupp.prod_fintype _ _ (fun a => pow_zero _)]
  simp [Fin.prod_univ_two, mu, nu]

theorem Bpiece_eq_span (n : ℕ) :
    Bpiece K (n : ℤ)
      = Submodule.span K {f : Poly K | ∃ p q : ℕ, p + q = n ∧ f = mu ^ p * nu ^ q} := by
  rw [Bpiece_eq_restrictSupport, MvPolynomial.restrictSupport_eq_span]
  congr 1
  ext f
  constructor
  · rintro ⟨s, hs, rfl⟩
    refine ⟨s 0, s 1, ?_, monomial_eq_mu_nu s⟩
    have h : s.degree = n := hs
    rwa [Finsupp.degree_eq_sum, Fin.sum_univ_two] at h
  · rintro ⟨p, q, hpq, rfl⟩
    refine ⟨Finsupp.single 0 p + Finsupp.single 1 q, ?_, ?_⟩
    · show (Finsupp.single (0 : Fin 2) p + Finsupp.single (1 : Fin 2) q).degree = n
      simp only [map_add, Finsupp.degree_single]
      omega
    · show (monomial (Finsupp.single (0 : Fin 2) p + Finsupp.single (1 : Fin 2) q) (1 : K))
        = mu ^ p * nu ^ q
      rw [monomial_eq_mu_nu]
      simp

theorem monomial_mem_Bpiece (p q : ℕ) :
    (mu ^ p * nu ^ q : Poly K) ∈ Bpiece K ((p : ℤ) + q) :=
  Bpiece_smul_Bpiece (mu_pow_mem p) (nu_pow_mem q)

/-! ### The monomial basis of `B_e` -/

/-- The exponent vector of `μ^p ν^q`. -/
noncomputable def monExp (p q : ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 p + Finsupp.single 1 q

@[simp] theorem monExp_apply_zero (p q : ℕ) : monExp p q 0 = p := by
  simp [monExp]

@[simp] theorem monExp_apply_one (p q : ℕ) : monExp p q 1 = q := by
  simp [monExp]

theorem monExp_inj {p q p' q' : ℕ} (h : monExp p q = monExp p' q') : p = p' ∧ q = q' := by
  constructor
  · simpa using congrFun (congrArg (⇑) h) 0
  · simpa using congrFun (congrArg (⇑) h) 1

theorem monExp_le_iff {p q p' q' : ℕ} : monExp p q ≤ monExp p' q' ↔ p ≤ p' ∧ q ≤ q' := by
  constructor
  · intro h
    exact ⟨by simpa using h 0, by simpa using h 1⟩
  · rintro ⟨h0, h1⟩ i
    fin_cases i <;> simpa using ‹_›

theorem monExp_sub (p q p' q' : ℕ) :
    monExp p' q' - monExp p q = monExp (p' - p) (q' - q) := by
  ext i
  fin_cases i <;> simp [Finsupp.tsub_apply]

variable (K) in
/-- The monomial `μ^{e-a} ν^a` of degree `e`. -/
noncomputable def gmon (e a : ℕ) : Poly K := mu ^ (e - a) * nu ^ a

theorem gmon_eq_monomial (e a : ℕ) :
    gmon K e a = MvPolynomial.monomial (monExp (e - a) a) (1 : K) := by
  rw [monomial_eq_mu_nu]
  simp [gmon]

theorem gmon_mem {e a : ℕ} (ha : a ≤ e) : gmon K e a ∈ Bpiece K (e : ℤ) := by
  have h := monomial_mem_Bpiece (K := K) (e - a) a
  rwa [show ((e - a : ℕ) : ℤ) + (a : ℤ) = (e : ℤ) by omega] at h

theorem coeff_gmon {e a a' : ℕ} :
    (gmon K e a).coeff (monExp (e - a') a') = if a' = a then 1 else 0 := by
  classical
  rw [gmon_eq_monomial, MvPolynomial.coeff_monomial]
  by_cases h : a' = a
  · subst h
    simp
  · rw [ite_eq_right h, ite_eq_right]
    intro hc
    exact h (monExp_inj hc).2.symm

/-- A form of degree `e` is the sum of its monomials. -/
theorem sum_coeff_smul_gmon {e : ℕ} {F : Poly K} (hF : F ∈ Bpiece K (e : ℤ)) :
    ∑ a : Fin (e + 1), F.coeff (monExp (e - (a : ℕ)) (a : ℕ)) • gmon K e (a : ℕ) = F := by
  classical
  rw [Bpiece_eq_span] at hF
  induction hF using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨p, q, hpq, rfl⟩ := hf
      have hq : q ≤ e := by omega
      have hfe : (mu ^ p * nu ^ q : Poly K) = gmon K e q := by
        rw [gmon, show e - q = p by omega]
      rw [hfe, Finset.sum_eq_single (⟨q, by omega⟩ : Fin (e + 1))]
      · rw [coeff_gmon, ite_eq_left rfl, one_smul]
      · intro b _ hb
        rw [coeff_gmon (a := q) (a' := (b : ℕ)), ite_eq_right, zero_smul]
        intro h
        exact hb (Fin.ext h)
      · intro h
        exact absurd (Finset.mem_univ _) h
  | zero => simp
  | add f g _ _ ihf ihg =>
      simp only [MvPolynomial.coeff_add, add_smul]
      rw [Finset.sum_add_distrib, ihf, ihg]
  | smul c f _ ih =>
      simp only [MvPolynomial.coeff_smul, smul_eq_mul, mul_smul]
      rw [← Finset.smul_sum, ih]

/-- **Multiplication in monomial coordinates**: a form of degree `k` times the
basis monomial of degree `e` and index `a`. -/
theorem mul_gmon {k e a : ℕ} (ha : a ≤ e) {F : Poly K} (hF : F ∈ Bpiece K (k : ℤ)) :
    F * gmon K e a
      = ∑ b : Fin (e + k + 1),
          (if a ≤ (b : ℕ) ∧ (b : ℕ) ≤ a + k then
              F.coeff (monExp (k - ((b : ℕ) - a)) ((b : ℕ) - a)) else 0)
            • gmon K (e + k) (b : ℕ) := by
  classical
  have hmem : F * gmon K e a ∈ Bpiece K ((e + k : ℕ) : ℤ) := by
    have h := Bpiece_smul_Bpiece hF (gmon_mem ha)
    rwa [show (k : ℤ) + (e : ℤ) = ((e + k : ℕ) : ℤ) by push_cast; ring] at h
  conv_lhs => rw [← sum_coeff_smul_gmon hmem]
  refine Finset.sum_congr rfl fun b _ => ?_
  congr 1
  have hb : (b : ℕ) ≤ e + k := Nat.lt_succ_iff.1 b.2
  rw [gmon_eq_monomial (e := e) (a := a), MvPolynomial.coeff_mul_monomial']
  by_cases hcond : a ≤ (b : ℕ) ∧ (b : ℕ) ≤ a + k
  · rw [ite_eq_left (monExp_le_iff.2 ⟨by omega, hcond.1⟩), ite_eq_left hcond, monExp_sub,
      show e + k - (b : ℕ) - (e - a) = k - ((b : ℕ) - a) by omega, mul_one]
  · rw [ite_eq_right, ite_eq_right hcond]
    intro hle
    obtain ⟨h1, h2⟩ := monExp_le_iff.1 hle
    exact hcond ⟨h2, by omega⟩

end Height.Graded
