import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.RingTheory.PowerSeries.Basic
import Height.Graded.Presentation
import Height.Graded.Cech

/-!
# The charts of `ℙ¹` on `B = K[μ, ν]`

The parameter convention of the whole development is `t = ν/μ`: the members of
the pencil `μN + νM` are `N + tM`, the finite points of `ℙ¹` are the scalars
`t₀ : K`, and `μ = 0` is the point at infinity.  This file owns every map that
realises that convention on the homogeneous coordinate ring `B = Graded.Poly K`:

* `deh : B →ₐ[K] K[t]`, dehomogenisation `μ ↦ 1`, `ν ↦ t`; on the piece `B_d`
  it is injective (`deh_injOn`) with image the polynomials of degree `≤ d`
  (`degreeLT_le_map_deh`, `natDegree_deh_le`), and `hgz d` is its inverse there
  (`deh_hgz`).  A nonzero form is not killed (`deh_ne_zero_of_ne_zero`,
  `deh_ne_zero_of_isHomogeneous`).
* `swapAlg : B ≃ₐ[K] B`, the swap `μ ↔ ν`, and its ring-hom form `swapHom`.
* `atPoint t₀ : B →+* K⟦u⟧`, the chart at the finite point `t₀` (`μ ↦ 1`,
  `ν ↦ t₀ + u`); it factors as `iota t₀ ∘ deh`, where `iota t₀ : K[t] →+* K⟦u⟧`
  is the Taylor expansion `t ↦ t₀ + u` (`atPoint_eq_comp`).
* `atInf : B →+* K⟦u⟧`, the chart at infinity (`μ ↦ u`, `ν ↦ 1`), which is the
  chart at `0` after the swap (`atPoint_zero_comp_swapHom`).

No nonzero form vanishes in either chart (`atPoint_ne_zero_of_homogeneous`,
`atInf_ne_zero_of_homogeneous`).  Everything downstream (`Graded/LocalLength`,
`Pencil/Chart`, `Pencil/Arcs`, `Chain/Multidegree`) uses these names; there is
no other dehomogenisation or chart map in the development.
-/

noncomputable section

namespace Height.Graded

open MvPolynomial Height.Toolbox

variable {K : Type*} [Field K]

/-! ### Dehomogenisation `B → K[t]` -/

variable (K) in
/-- Dehomogenisation `B = K[μ,ν] → K[t]`, `μ ↦ 1`, `ν ↦ t`.  On `B_d` it is
the isomorphism `f ↦ f/μ^d` onto the polynomials of degree `≤ d`. -/
def deh : Poly K →ₐ[K] Polynomial K := MvPolynomial.aeval ![1, Polynomial.X]

@[simp] theorem deh_mu : deh K (mu : Poly K) = 1 := by simp [deh, mu]

@[simp] theorem deh_nu : deh K (nu : Poly K) = Polynomial.X := by simp [deh, nu]

@[simp] theorem deh_C (a : K) : deh K (MvPolynomial.C a : Poly K) = Polynomial.C a := by
  simp [deh]

/-- Homogenisation of a polynomial of degree `≤ d` to a homogeneous element of
`B_d`: `∑_i p_i μ^{d-i} ν^i`. -/
def hgz (d : ℕ) (p : Polynomial K) : Poly K :=
  ∑ i ∈ Finset.range (d + 1),
    MvPolynomial.monomial (Finsupp.single 0 (d - i) + Finsupp.single 1 i) (p.coeff i)

theorem hgz_mem (d : ℕ) (p : Polynomial K) : hgz d p ∈ Bpiece K (d : ℤ) := by
  rw [Bpiece_natCast]
  refine Submodule.sum_mem _ fun i hi => ?_
  rw [Finset.mem_range] at hi
  refine (mem_homogeneousSubmodule _ _).2 (isHomogeneous_monomial _ ?_)
  simp only [map_add, Finsupp.degree_single]
  omega

theorem deh_monomial (s : Fin 2 →₀ ℕ) (a : K) :
    deh K (MvPolynomial.monomial s a) = Polynomial.C a * Polynomial.X ^ (s 1) := by
  rw [deh, aeval_monomial, Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two]
  simp [Polynomial.algebraMap_eq]

theorem deh_hgz {d : ℕ} {p : Polynomial K} (hp : p.natDegree < d + 1) :
    deh K (hgz d p) = p := by
  rw [hgz, map_sum]
  conv_rhs => rw [Polynomial.as_sum_range' p (d + 1) hp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [deh_monomial]
  have h1 : (Finsupp.single (0 : Fin 2) (d - i) + Finsupp.single (1 : Fin 2) i) 1 = i := by
    simp
  rw [h1, Polynomial.C_mul_X_pow_eq_monomial]

/-- `deh` as a sum over the support: the `ν`-exponent becomes the degree. -/
theorem deh_eq_sum (c : Poly K) :
    deh K c = ∑ m ∈ c.support, Polynomial.C (c.coeff m) * Polynomial.X ^ (m 1) := by
  conv_lhs => rw [c.as_sum]
  rw [map_sum]
  exact Finset.sum_congr rfl fun m _ => deh_monomial m (c.coeff m)

/-- Dehomogenising a form of degree `e` gives a polynomial of degree at most `e`. -/
theorem natDegree_deh_le {e : ℕ} {c : Poly K} (hc : c ∈ Bpiece K (e : ℤ)) :
    (deh K c).natDegree ≤ e := by
  classical
  rw [Bpiece_eq_restrictSupport, MvPolynomial.mem_restrictSupport_iff] at hc
  rw [deh_eq_sum]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun m hm => ?_
  have hdeg : m.degree = e := hc hm
  have hmi : m 1 ≤ e := by
    rw [← hdeg, Finsupp.degree_eq_sum]
    exact Finset.single_le_sum (fun j _ => Nat.zero_le (m j)) (Finset.mem_univ 1)
  refine le_trans Polynomial.natDegree_mul_le ?_
  rw [Polynomial.natDegree_C]
  have h2 : ((Polynomial.X : Polynomial K) ^ (m 1)).natDegree ≤ m 1 := by simp
  omega

/-! ### `deh` is injective on homogeneous pieces -/

theorem degreeLT_le_map_deh (d : ℕ) :
    Polynomial.degreeLT K (d + 1) ≤ (Bpiece K (d : ℤ)).map (deh K).toLinearMap := by
  intro p hp
  rw [Polynomial.mem_degreeLT] at hp
  have hnat : p.natDegree < d + 1 := by
    rcases eq_or_ne p 0 with rfl | h0
    · simp
    · exact (Polynomial.natDegree_lt_iff_degree_lt h0).2 hp
  exact ⟨hgz d p, hgz_mem d p, deh_hgz hnat⟩

theorem finrank_degreeLT (n : ℕ) :
    Module.finrank K (Polynomial.degreeLT K n) = n := by
  rw [Module.finrank_eq_card_basis (Polynomial.degreeLT.basis K n)]
  simp

theorem Bpiece_inf_ker_deh (d : ℕ) :
    Bpiece K (d : ℤ) ⊓ LinearMap.ker (deh K).toLinearMap = ⊥ := by
  have : Module.Finite K ((Bpiece K (d : ℤ)).map (deh K).toLinearMap) :=
    Module.Finite.map _ _
  have hsplit := finrank_map_add_finrank_inf_ker
    (K := K) (deh K).toLinearMap (Bpiece K (d : ℤ))
  have hle : Module.finrank K (Polynomial.degreeLT K (d + 1))
      ≤ Module.finrank K ((Bpiece K (d : ℤ)).map (deh K).toLinearMap) :=
    Submodule.finrank_mono (degreeLT_le_map_deh d)
  rw [finrank_degreeLT] at hle
  rw [finrank_Bpiece] at hsplit
  have hz : Module.finrank K
      ((Bpiece K (d : ℤ) ⊓ LinearMap.ker (deh K).toLinearMap : Submodule K (Poly K))) = 0 := by
    omega
  have : Module.Finite K
      ((Bpiece K (d : ℤ) ⊓ LinearMap.ker (deh K).toLinearMap : Submodule K (Poly K))) :=
    Module.Finite.of_injective
      (Submodule.inclusion (inf_le_left : _ ≤ Bpiece K (d : ℤ)))
      (Submodule.inclusion_injective _)
  exact Submodule.finrank_eq_zero.1 hz

theorem deh_injOn {d : ℤ} {f₁ f₂ : Poly K} (h1 : f₁ ∈ Bpiece K d) (h2 : f₂ ∈ Bpiece K d)
    (h : deh K f₁ = deh K f₂) : f₁ = f₂ := by
  rcases lt_or_ge d 0 with hd | hd
  · rw [Bpiece_of_neg hd, Submodule.mem_bot] at h1 h2
    rw [h1, h2]
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, d = (n : ℤ) := ⟨d.toNat, (Int.toNat_of_nonneg hd).symm⟩
    have hmem : f₁ - f₂ ∈ Bpiece K (n : ℤ) ⊓ LinearMap.ker (deh K).toLinearMap :=
      ⟨Submodule.sub_mem _ h1 h2, by simp [LinearMap.mem_ker, map_sub, h]⟩
    rw [Bpiece_inf_ker_deh, Submodule.mem_bot, sub_eq_zero] at hmem
    exact hmem

/-- Dehomogenisation does not kill a nonzero form. -/
theorem deh_ne_zero_of_ne_zero {d : ℤ} {g : Poly K} (hg : g ∈ Bpiece K d) (hg0 : g ≠ 0) :
    deh K g ≠ 0 := fun h0 =>
  hg0 (deh_injOn hg (Submodule.zero_mem _) (h0.trans (map_zero (deh K)).symm))

/-- The same, for mathlib's homogeneity predicate. -/
theorem deh_ne_zero_of_isHomogeneous {D : ℕ} {f : Poly K} (hf : f.IsHomogeneous D)
    (hne : f ≠ 0) : deh K f ≠ 0 :=
  deh_ne_zero_of_ne_zero (d := (D : ℤ))
    (by rw [Bpiece_natCast]; exact (mem_homogeneousSubmodule _ _).2 hf) hne

/-- A homogeneous `g` with a nonzero `ν^c`-coefficient has nonzero
dehomogenisation: no zero of `g` sits at `μ = 0`. -/
theorem deh_ne_zero {c : ℤ} {g : Poly K} (hg : g ∈ Bpiece K c) (hgmu : nuLead c g ≠ 0) :
    deh K g ≠ 0 := by
  intro h0
  refine hgmu ?_
  rw [deh_injOn hg (Submodule.zero_mem _) (h0.trans (map_zero (deh K)).symm), map_zero]

/-! ### The chart swap `μ ↔ ν` -/

variable (K) in
/-- The involution of `B = K[μ, ν]` exchanging the two coordinates. -/
def swapAlg : Poly K ≃ₐ[K] Poly K := MvPolynomial.renameEquiv K (Equiv.swap (0 : Fin 2) 1)

theorem swapAlg_apply (f : Poly K) :
    swapAlg K f = MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1) f := rfl

@[simp] theorem swapAlg_mu : swapAlg K (mu : Poly K) = nu := by
  simp [swapAlg_apply, mu, nu]

@[simp] theorem swapAlg_nu : swapAlg K (nu : Poly K) = mu := by
  simp [swapAlg_apply, mu, nu]

@[simp] theorem swapAlg_swapAlg (f : Poly K) : swapAlg K (swapAlg K f) = f := by
  have h : (⇑(Equiv.swap (0 : Fin 2) 1) ∘ ⇑(Equiv.swap (0 : Fin 2) 1)) = id := by
    funext i
    exact Equiv.swap_apply_self _ _ _
  rw [swapAlg_apply, swapAlg_apply, MvPolynomial.rename_rename, h, MvPolynomial.rename_id]
  rfl

theorem swapAlg_mem_Bpiece {d : ℤ} {f : Poly K} (hf : f ∈ Bpiece K d) :
    swapAlg K f ∈ Bpiece K d := by
  rcases lt_or_ge d 0 with hd | hd
  · rw [Bpiece_of_neg hd, Submodule.mem_bot] at hf ⊢
    rw [hf, map_zero]
  · rw [mem_Bpiece_of_nonneg hd] at hf ⊢
    exact hf.rename_isHomogeneous

variable (K) in
/-- The swap as a ring homomorphism, for `Matrix.map` and `RingHom.map_mulVec`. -/
def swapHom : Poly K →+* Poly K := (swapAlg K).toAlgHom.toRingHom

@[simp] theorem swapHom_apply (f : Poly K) : swapHom K f = swapAlg K f := rfl

/-! ### The charts at the points of `ℙ¹` -/

/-- The local algebra at the finite point `t = t₀` of `ℙ¹`: `μ ↦ 1`, `ν ↦ t₀ + u`. -/
def atPoint (t₀ : K) : Poly K →+* PowerSeries K :=
  MvPolynomial.eval₂Hom (PowerSeries.C) ![1, PowerSeries.C t₀ + PowerSeries.X]

variable (K) in
/-- The Taylor expansion `K[t] → K⟦u⟧` at `t = t₀`, `t ↦ t₀ + u`. -/
def iota (t₀ : K) : Polynomial K →+* PowerSeries K :=
  Polynomial.eval₂RingHom PowerSeries.C (PowerSeries.X + PowerSeries.C t₀)

/-- The local algebra at the point at infinity: `μ ↦ u`, `ν ↦ 1`. -/
def atInf : Poly K →+* PowerSeries K :=
  MvPolynomial.eval₂Hom (PowerSeries.C) ![PowerSeries.X, 1]

@[simp] theorem iota_X (t₀ : K) :
    iota K t₀ Polynomial.X = PowerSeries.X + PowerSeries.C t₀ := by
  simp [iota]

@[simp] theorem iota_C (t₀ a : K) : iota K t₀ (Polynomial.C a) = PowerSeries.C a := by
  simp [iota]

@[simp] theorem atPoint_mu (t₀ : K) : atPoint t₀ (mu : Poly K) = 1 := by
  simp [atPoint, mu]

@[simp] theorem atPoint_nu (t₀ : K) :
    atPoint t₀ (nu : Poly K) = PowerSeries.C t₀ + PowerSeries.X := by
  simp [atPoint, nu]

@[simp] theorem atPoint_C (t₀ a : K) :
    atPoint t₀ (MvPolynomial.C a : Poly K) = PowerSeries.C a := by
  simp [atPoint]

@[simp] theorem atInf_mu : atInf (mu : Poly K) = PowerSeries.X := by
  simp [atInf, mu]

@[simp] theorem atInf_nu : atInf (nu : Poly K) = 1 := by
  simp [atInf, nu]

@[simp] theorem atInf_C (a : K) :
    atInf (MvPolynomial.C a : Poly K) = PowerSeries.C a := by
  simp [atInf]

/-- The finite chart is the Taylor expansion of the dehomogenisation. -/
theorem atPoint_eq_comp (t₀ : K) :
    atPoint t₀ = (iota K t₀).comp (deh K).toRingHom := by
  refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
  · simp [atPoint]
  · fin_cases i
    · simp [atPoint, deh]
    · simp [atPoint, deh, add_comm]

/-- The chart at infinity is the chart at `0` after the swap `μ ↔ ν`. -/
theorem atPoint_zero_comp_swapHom :
    (atPoint (0 : K)).comp (swapHom K) = (atInf : Poly K →+* PowerSeries K) := by
  refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
  · show atPoint (0 : K) (swapAlg K (MvPolynomial.C a)) = atInf (MvPolynomial.C a)
    rw [swapAlg_apply, MvPolynomial.rename_C, atPoint_C, atInf_C]
  · fin_cases i
    · show atPoint (0 : K) (swapAlg K (mu : Poly K)) = atInf mu
      rw [swapAlg_mu, atPoint_nu, atInf_mu, map_zero, zero_add]
    · show atPoint (0 : K) (swapAlg K (nu : Poly K)) = atInf nu
      rw [swapAlg_nu, atPoint_mu, atInf_nu]

/-- The value at the point: `constantCoeff ∘ atPoint t₀` is evaluation at
`(μ, ν) = (1, t₀)`.  On a homogeneous `f` of degree `e` this is the value of
`f/μ^e` at `t₀`. -/
theorem constantCoeff_atPoint (t₀ : K) (f : Poly K) :
    PowerSeries.constantCoeff (atPoint t₀ f) = MvPolynomial.eval ![1, t₀] f := by
  have h : (PowerSeries.constantCoeff (R := K)).comp (atPoint t₀)
      = (MvPolynomial.eval ![(1 : K), t₀] : Poly K →+* K) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
    · simp [atPoint]
    · fin_cases i <;> simp [atPoint]
  exact congrArg (fun φ => φ f) h

/-! ### The Taylor expansion -/

theorem iota_eq_coe_comp (t₀ : K) (p : Polynomial K) :
    iota K t₀ p
      = ((p.comp (Polynomial.X + Polynomial.C t₀) : Polynomial K) : PowerSeries K) := by
  have h : (p.comp (Polynomial.X + Polynomial.C t₀) : Polynomial K)
      = p.eval₂ Polynomial.C (Polynomial.X + Polynomial.C t₀) := rfl
  have hc : (Polynomial.coeToPowerSeries.ringHom (R := K)).comp Polynomial.C
      = (PowerSeries.C : K →+* PowerSeries K) := by
    ext a; simp
  rw [h, ← Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.hom_eval₂, hc]
  simp [iota]

/-- The Taylor expansion at a point is injective: a polynomial is determined by
its Taylor series. -/
theorem iota_injective (t₀ : K) : Function.Injective (iota K t₀) := by
  intro p q hpq
  rw [iota_eq_coe_comp, iota_eq_coe_comp] at hpq
  refine Polynomial.taylor_injective t₀ ?_
  rw [Polynomial.taylor_apply, Polynomial.taylor_apply]
  exact Polynomial.coe_injective K hpq

theorem constantCoeff_iota (t₀ : K) (p : Polynomial K) :
    PowerSeries.constantCoeff (iota K t₀ p) = p.eval t₀ := by
  have h : (PowerSeries.constantCoeff (R := K)).comp (iota K t₀)
      = (Polynomial.evalRingHom t₀ : Polynomial K →+* K) :=
    Polynomial.ringHom_ext (by simp) (by simp)
  exact congrArg (fun φ => φ p) h

theorem X_pow_dvd_iota_iff (t₀ : K) (m : ℕ) (p : Polynomial K) :
    (PowerSeries.X : PowerSeries K) ^ m ∣ iota K t₀ p
      ↔ (Polynomial.X - Polynomial.C t₀) ^ m ∣ p := by
  rw [iota_eq_coe_comp]
  constructor
  · intro h
    have hpoly : (Polynomial.X : Polynomial K) ^ m
        ∣ p.comp (Polynomial.X + Polynomial.C t₀) := by
      rw [Polynomial.X_pow_dvd_iff]
      intro d hd
      have hd' := PowerSeries.X_pow_dvd_iff.1 h d hd
      rwa [Polynomial.coeff_coe] at hd'
    obtain ⟨q, hq⟩ := hpoly
    refine ⟨q.comp (Polynomial.X - Polynomial.C t₀), ?_⟩
    have hcomp := congrArg (fun z : Polynomial K =>
      z.comp (Polynomial.X - Polynomial.C t₀)) hq
    simpa [Polynomial.comp_assoc, Polynomial.mul_comp, Polynomial.pow_comp] using hcomp
  · rintro ⟨q, rfl⟩
    refine ⟨((q.comp (Polynomial.X + Polynomial.C t₀) : Polynomial K) : PowerSeries K), ?_⟩
    rw [Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.sub_comp, Polynomial.X_comp,
      Polynomial.C_comp]
    push_cast
    simp

@[simp] theorem iota_X_sub_C (t₀ : K) :
    iota K t₀ (Polynomial.X - Polynomial.C t₀) = PowerSeries.X := by
  simp

theorem iota_comp_sub (t₀ : K) (p : Polynomial K) :
    iota K t₀ (p.comp (Polynomial.X - Polynomial.C t₀)) = (p : PowerSeries K) := by
  rw [iota_eq_coe_comp, Polynomial.comp_assoc]
  simp

theorem X_pow_dvd_sub_trunc (m : ℕ) (c : PowerSeries K) :
    (PowerSeries.X : PowerSeries K) ^ m
      ∣ c - ((PowerSeries.trunc m c : Polynomial K) : PowerSeries K) := by
  rw [PowerSeries.X_pow_dvd_iff]
  intro d hd
  simp [Polynomial.coeff_coe, PowerSeries.coeff_trunc, hd]

/-! ### No form vanishes in a chart -/

/-- The finite chart, pointwise: Taylor-expand the dehomogenisation. -/
theorem atPoint_apply_eq (t₀ : K) (f : Poly K) : atPoint t₀ f = iota K t₀ (deh K f) :=
  RingHom.congr_fun (atPoint_eq_comp t₀) f

/-- A nonzero homogeneous polynomial has nonzero image in the finite chart. -/
theorem atPoint_ne_zero_of_homogeneous (t₀ : K) {e : ℤ} {c : Poly K}
    (hc : c ∈ Bpiece K e) (hc0 : c ≠ 0) : atPoint t₀ c ≠ 0 := fun h =>
  deh_ne_zero_of_ne_zero hc hc0
    (iota_injective t₀ (((atPoint_apply_eq t₀ c).symm.trans h).trans (map_zero _).symm))

/-- The chart at infinity, pointwise: evaluate the swapped form in the chart at `0`. -/
theorem atInf_apply_eq (f : Poly K) : atInf f = atPoint 0 (swapAlg K f) :=
  (RingHom.congr_fun atPoint_zero_comp_swapHom f).symm

/-- A nonzero homogeneous polynomial has nonzero image in the chart at infinity. -/
theorem atInf_ne_zero_of_homogeneous {e : ℤ} {c : Poly K} (hc : c ∈ Bpiece K e)
    (hc0 : c ≠ 0) : (atInf : Poly K →+* PowerSeries K) c ≠ 0 := fun h =>
  atPoint_ne_zero_of_homogeneous 0 (swapAlg_mem_Bpiece hc)
    (fun h' => hc0 ((swapAlg K).injective (h'.trans (map_zero _).symm)))
    ((atInf_apply_eq c).symm.trans h)

/-! ## The charts as a bundle, and global sections

This is the projective-line half of `Height/Graded/Presentation.lean`; it lives
here because `deh`, `atPoint` and `atInf` do, and `Presentation` sits below this
file in the import order.  The module docstring of `Presentation.lean`
describes the design.
-/

/-! ### The charts of `ℙ¹`, bundled -/

/-- A **chart of `ℙ¹`** on `B = K[μ, ν]`: an expansion of forms as power series
in a local parameter that kills no nonzero form.  There are exactly two kinds,
`Chart.atPoint t₀` and `Chart.atInf`, and the non-vanishing clause is what
makes a homogeneous denominator invertible in `K⸨u⸩`.

This bundles the hypothesis
`∀ (e : ℤ) (c : Poly K), c ∈ Bpiece K e → c ≠ 0 → χ c ≠ 0`
used by `Pencil.exists_laurent_commutator_of_chart` and
`Pencil.freeClass_eq_zero_of_chart` (`Pencil/Arcs.lean`). -/
structure Chart (K : Type*) [Field K] where
  /-- The expansion `B → K⟦u⟧`. -/
  hom : Poly K →+* PowerSeries K
  /-- No nonzero form is killed. -/
  ne_zero : ∀ {e : ℤ} {c : Poly K}, c ∈ Bpiece K e → c ≠ 0 → hom c ≠ 0

/-- The chart at the finite point `t = t₀`, `μ ↦ 1`, `ν ↦ t₀ + u`.  Bundles
`Graded.atPoint` with `Graded.atPoint_ne_zero_of_homogeneous`. -/
def Chart.atPoint (t₀ : K) : Chart K where
  hom := Height.Graded.atPoint t₀
  ne_zero hce hc0 := atPoint_ne_zero_of_homogeneous t₀ hce hc0

variable (K) in
/-- The chart at the point at infinity, `μ ↦ u`, `ν ↦ 1`.  Bundles
`Graded.atInf` with `Graded.atInf_ne_zero_of_homogeneous`. -/
def Chart.atInf : Chart K where
  hom := Height.Graded.atInf
  ne_zero hce hc0 := atInf_ne_zero_of_homogeneous hce hc0

@[simp] theorem Chart.atPoint_hom (t₀ : K) :
    (Chart.atPoint t₀).hom = Height.Graded.atPoint t₀ := rfl

@[simp] theorem Chart.atInf_hom :
    (Chart.atInf K).hom = (Height.Graded.atInf : Poly K →+* PowerSeries K) := rfl

/-! ### Global sections of a graded presentation -/

namespace GradedPresentation

variable {K : Type*} [Field K] (P : GradedPresentation K)

/-- Dehomogenisation coordinatewise, `F → (idx → K[t])`: the presentation read
in the chart `μ ≠ 0`. -/
def dehVec : P.Mod →ₗ[K] (P.idx → Polynomial K) :=
  LinearMap.pi fun j => (deh K).toLinearMap.comp (LinearMap.proj j)

@[simp] theorem dehVec_apply (x : P.Mod) (j : P.idx) : P.dehVec x j = deh K (x j) := rfl

theorem dehVec_smul (f : Poly K) (x : P.Mod) :
    P.dehVec (f • x) = deh K f • P.dehVec x := by
  funext j; simp [Algebra.smul_def]

end GradedPresentation

/-! ### Monomial coordinates of an untwisted piece

The one coordinate system on `(⨁_{j : ι} B)_e`.  It can be read either as
monomial coefficients or as coefficients of the dehomogenisation, which are
the same — `coeff_deh_eq_coeff_monExp` is why.
-/

section Coords

variable {K : Type*} [Field K]

/-- On a form of degree `e`, the `a`-th coefficient of the dehomogenisation is
the coefficient of the monomial `μ^{e-a} ν^a`. -/
theorem coeff_deh_eq_coeff_monExp {e a : ℕ} (ha : a ≤ e) {F : Poly K}
    (hF : F ∈ Bpiece K (e : ℤ)) :
    (deh K F).coeff a = F.coeff (monExp (e - a) a) := by
  classical
  conv_lhs => rw [← sum_coeff_smul_gmon hF]
  have hstep : ∀ b : Fin (e + 1),
      (deh K (F.coeff (monExp (e - (b : ℕ)) (b : ℕ)) • gmon K e (b : ℕ))).coeff a
        = if (b : ℕ) = a then F.coeff (monExp (e - (b : ℕ)) (b : ℕ)) else 0 := by
    intro b
    rw [map_smul, gmon_eq_monomial, deh_monomial, monExp_apply_one]
    simp [Polynomial.coeff_X_pow, eq_comm]
  rw [map_sum, Polynomial.finsetSum_coeff,
    Finset.sum_congr rfl fun b (_ : b ∈ Finset.univ) => hstep b,
    Finset.sum_eq_single (⟨a, by omega⟩ : Fin (e + 1))]
  · simp
  · intro b _ hb
    rw [ite_eq_right (fun h => absurd (Fin.ext h) hb)]
  · intro h
    exact absurd (Finset.mem_univ _) h

variable (K) in
/-- The monomial coordinates of a tuple of forms of degree `e`: the `a`-th
coefficient of the dehomogenisation of the `j`-th entry. -/
def coordVec (ι : Type) [Fintype ι] (e : ℕ) : (ι → Poly K) →ₗ[K] (ι × Fin (e + 1) → K) :=
  LinearMap.pi fun p =>
    (Polynomial.lcoeff K (p.2 : ℕ)).comp ((deh K).toLinearMap.comp (LinearMap.proj p.1))

@[simp] theorem coordVec_apply {ι : Type} [Fintype ι] {e : ℕ} (F : ι → Poly K)
    (p : ι × Fin (e + 1)) : coordVec K ι e F p = (deh K (F p.1)).coeff (p.2 : ℕ) := rfl

theorem coordVec_eq_coeff_monExp {ι : Type} [Fintype ι] {e : ℕ} {F : ι → Poly K}
    (hF : F ∈ (GradedPresentation.free K ι).piece (e : ℤ)) (p : ι × Fin (e + 1)) :
    coordVec K ι e F p = (F p.1).coeff (monExp (e - (p.2 : ℕ)) (p.2 : ℕ)) := by
  refine coeff_deh_eq_coeff_monExp (Nat.lt_succ_iff.1 p.2.2) ?_
  simpa using (GradedPresentation.free K ι).mem_piece.1 hF p.1

variable (K) in
/-- Assembling monomial coordinates into a tuple of forms of degree `e`. -/
def ofCoordVec (ι : Type) [Fintype ι] (e : ℕ) : (ι × Fin (e + 1) → K) →ₗ[K] (ι → Poly K) :=
  LinearMap.pi fun i => ∑ a : Fin (e + 1),
    (LinearMap.toSpanSingleton K (Poly K) (gmon K e (a : ℕ))).comp (LinearMap.proj (i, a))

@[simp] theorem ofCoordVec_apply {ι : Type} [Fintype ι] {e : ℕ} (v : ι × Fin (e + 1) → K)
    (i : ι) : ofCoordVec K ι e v i = ∑ a : Fin (e + 1), v (i, a) • gmon K e (a : ℕ) := by
  simp [ofCoordVec, LinearMap.toSpanSingleton_apply]

theorem ofCoordVec_mem {ι : Type} [Fintype ι] {e : ℕ} (v : ι × Fin (e + 1) → K) :
    ofCoordVec K ι e v ∈ (GradedPresentation.free K ι).piece (e : ℤ) := by
  refine (GradedPresentation.free K ι).mem_piece.2 fun i => ?_
  rw [show ((e : ℤ) - (GradedPresentation.free K ι).shift i) = (e : ℤ) by simp,
    ofCoordVec_apply]
  exact Submodule.sum_mem _ fun a _ =>
    Submodule.smul_mem _ _ (gmon_mem (Nat.lt_succ_iff.1 a.2))

theorem coordVec_ofCoordVec {ι : Type} [Fintype ι] {e : ℕ} (v : ι × Fin (e + 1) → K) :
    coordVec K ι e (ofCoordVec K ι e v) = v := by
  funext p
  rw [coordVec_eq_coeff_monExp (ofCoordVec_mem v), ofCoordVec_apply,
    MvPolynomial.coeff_sum, Finset.sum_eq_single p.2]
  · rw [MvPolynomial.coeff_smul, coeff_gmon, ite_eq_left rfl, smul_eq_mul, mul_one]
  · intro b _ hb
    rw [MvPolynomial.coeff_smul, coeff_gmon, ite_eq_right (fun h => absurd (Fin.ext h.symm) hb), smul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem ofCoordVec_injective (ι : Type) [Fintype ι] (e : ℕ) :
    Function.Injective (ofCoordVec K ι e) :=
  Function.LeftInverse.injective (g := coordVec K ι e) coordVec_ofCoordVec

theorem ofCoordVec_coordVec {ι : Type} [Fintype ι] {e : ℕ} {F : ι → Poly K}
    (hF : F ∈ (GradedPresentation.free K ι).piece (e : ℤ)) :
    ofCoordVec K ι e (coordVec K ι e F) = F := by
  funext i
  have hFi : F i ∈ Bpiece K (e : ℤ) := by
    simpa using (GradedPresentation.free K ι).mem_piece.1 hF i
  rw [ofCoordVec_apply]
  rw [Finset.sum_congr rfl fun a (_ : a ∈ Finset.univ) => by
    rw [coordVec_eq_coeff_monExp hF (i, a)]]
  exact sum_coeff_smul_gmon hFi

variable (K) in
/-- **The coordinate equivalence.**  Global sections of `⨁_{j : ι} O(e)` in
coordinates: the degree-`e` piece of `⨁_{j : ι} B` is the space of coefficient
tuples of degree `≤ e`. -/
def coordEquiv (ι : Type) [Fintype ι] (e : ℕ) :
    (GradedPresentation.free K ι).piece (e : ℤ) ≃ₗ[K] (ι × Fin (e + 1) → K) where
  toFun x := coordVec K ι e (x : ι → Poly K)
  map_add' _ _ := map_add (coordVec K ι e) _ _
  map_smul' c _ := map_smul (coordVec K ι e) c _
  invFun v := ⟨ofCoordVec K ι e v, ofCoordVec_mem v⟩
  left_inv x := Subtype.ext (ofCoordVec_coordVec x.2)
  right_inv v := coordVec_ofCoordVec v

@[simp] theorem coordEquiv_apply {ι : Type} [Fintype ι] {e : ℕ}
    (x : (GradedPresentation.free K ι).piece (e : ℤ)) (p : ι × Fin (e + 1)) :
    coordEquiv K ι e x p = (deh K ((x : ι → Poly K) p.1)).coeff (p.2 : ℕ) := rfl

@[simp] theorem coordEquiv_symm_apply {ι : Type} [Fintype ι] {e : ℕ}
    (v : ι × Fin (e + 1) → K) :
    (((coordEquiv K ι e).symm v : (GradedPresentation.free K ι).piece (e : ℤ)) : ι → Poly K)
      = ofCoordVec K ι e v := rfl

end Coords

end Height.Graded

end
