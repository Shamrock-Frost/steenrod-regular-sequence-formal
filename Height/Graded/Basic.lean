import Mathlib.Algebra.MvPolynomial.Supported
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Height.Toolbox.FinrankSplit

/-!
# Graded modules over `B = K[μ, ν]`: the encoding

This file fixes the encoding used throughout `Height/Graded` and
`Height/Pencil`; see the paper, `\subsec:toolbox`, for the mathematics.

* `Height.Graded.Poly K = MvPolynomial (Fin 2) K` is `B = K[μ, ν]`, with
  `mu = X 0` and `nu = X 1`.
* `Height.Graded.Bpiece K d` is `B_d`, the space of homogeneous polynomials of
  degree `d`.  The degree index is `ℤ`, and `B_d = ⊥` for `d < 0`; this is what
  makes shifts `B(-a)` painless.
* `Bpiece_smul_Bpiece`, `prod_mem_Bpiece`, `det_mem_Bpiece` and
  `Bproj_smul_of_mem` are the multiplicativity of the grading.

Graded free modules `⨁ j, B(-a j)` over `B`, their pieces and projections and
their graded submodules are `Height/Graded/Presentation.lean`
(`GradedPresentation`), which sits above this file.
-/

noncomputable section

namespace Height.Graded

open MvPolynomial

/-- `B = K[μ, ν]`, the homogeneous coordinate ring of `ℙ¹`. -/
abbrev Poly (K : Type*) [CommRing K] : Type _ := MvPolynomial (Fin 2) K

section

variable {K : Type*} [CommRing K]

/-- The first homogeneous coordinate `μ`. -/
def mu : Poly K := X 0

/-- The second homogeneous coordinate `ν`. -/
def nu : Poly K := X 1

end

variable {K : Type*} [Field K]

variable (K) in
/-- The degree-`d` piece `B_d` of `B = K[μ, ν]`, indexed by `ℤ`.
It is `⊥` in negative degrees, so that the shifted module `B(-a)` has
`B(-a)_e = B_{e - a}` with no side conditions. -/
def Bpiece (d : ℤ) : Submodule K (Poly K) :=
  if 0 ≤ d then homogeneousSubmodule (Fin 2) K d.toNat else ⊥

@[simp] theorem Bpiece_of_neg {d : ℤ} (hd : d < 0) : Bpiece K d = ⊥ := by
  simp [Bpiece, not_le.2 hd]

theorem Bpiece_of_nonneg {d : ℤ} (hd : 0 ≤ d) :
    Bpiece K d = homogeneousSubmodule (Fin 2) K d.toNat := by
  simp [Bpiece, hd]

@[simp] theorem Bpiece_natCast (n : ℕ) :
    Bpiece K (n : ℤ) = homogeneousSubmodule (Fin 2) K n := by
  simp [Bpiece]

theorem mem_Bpiece_of_nonneg {d : ℤ} (hd : 0 ≤ d) (f : Poly K) :
    f ∈ Bpiece K d ↔ f.IsHomogeneous d.toNat := by
  rw [Bpiece_of_nonneg hd]; rfl

/-! ### The dimension of `B_d` -/

/-- The exponent vectors of the degree-`n` monomials in two variables. -/
def degSet (n : ℕ) : Set (Fin 2 →₀ ℕ) := {d | d.degree = n}

/-- The degree-`n` exponent vectors in two variables are indexed by
`Fin (n+1)`: the vector `(i, n - i)`. -/
def degSetEquiv (n : ℕ) : degSet n ≃ Fin (n + 1) where
  toFun d := ⟨d.1 0, by
    have h : d.1 0 + d.1 1 = n := by
      have h2 : d.1.degree = n := d.2
      rwa [Finsupp.degree_eq_sum, Fin.sum_univ_two] at h2
    omega⟩
  invFun i := ⟨Finsupp.single 0 (i : ℕ) + Finsupp.single 1 (n - (i : ℕ)), by
    have hi : (i : ℕ) ≤ n := Nat.lt_succ_iff.1 i.2
    have : ((Finsupp.single (0 : Fin 2) (i : ℕ) +
        Finsupp.single (1 : Fin 2) (n - (i : ℕ))).degree) = n := by
      simp only [map_add, Finsupp.degree_single]; omega
    exact this⟩
  left_inv d := by
    have h : d.1 0 + d.1 1 = n := by
      have h2 : d.1.degree = n := d.2
      rwa [Finsupp.degree_eq_sum, Fin.sum_univ_two] at h2
    refine Subtype.ext (Finsupp.ext fun j => ?_)
    fin_cases j
    · simp []
    · simp only [Finsupp.add_apply, Finsupp.single_apply]
      norm_num
      omega
  right_inv i := by
    have hi : (i : ℕ) ≤ n := Nat.lt_succ_iff.1 i.2
    apply Fin.ext
    simp

instance (n : ℕ) : Fintype (degSet n) := Fintype.ofEquiv _ (degSetEquiv n).symm

theorem card_degSet (n : ℕ) : Fintype.card (degSet n) = n + 1 := by
  simpa using Fintype.card_congr (degSetEquiv n)

theorem Bpiece_eq_restrictSupport (n : ℕ) :
    Bpiece K (n : ℤ) = MvPolynomial.restrictSupport K (degSet n) := by
  rw [Bpiece_natCast, MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
  rfl

variable (K) in
/-- The monomials of degree `n` form a `K`-basis of `B_n`. -/
def BpieceBasis (n : ℕ) : Module.Basis (degSet n) K (Bpiece K (n : ℤ)) :=
  (MvPolynomial.basisRestrictSupport K (degSet n)).map
    (LinearEquiv.ofEq _ _ (Bpiece_eq_restrictSupport n).symm)

variable (K) in
@[simp] theorem finrank_Bpiece (d : ℤ) :
    Module.finrank K (Bpiece K d) = (d + 1).toNat := by
  rcases lt_or_ge d 0 with hd | hd
  · rw [Bpiece_of_neg hd]
    simp only [finrank_bot]
    omega
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, d = (n : ℤ) := ⟨d.toNat, (Int.toNat_of_nonneg hd).symm⟩
    rw [Module.finrank_eq_card_basis (BpieceBasis K n), card_degSet n]
    omega

instance instFiniteBpiece (d : ℤ) : Module.Finite K (Bpiece K d) := by
  rcases lt_or_ge d 0 with hd | hd
  · rw [Bpiece_of_neg hd]; infer_instance
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, d = (n : ℤ) := ⟨d.toNat, (Int.toNat_of_nonneg hd).symm⟩
    exact Module.Finite.of_basis (BpieceBasis K n)

/-! ### Homogeneous projections on `B` -/

/-- The projection of `B` onto its degree-`d` piece, `d : ℤ`. -/
def Bproj (d : ℤ) : Poly K →ₗ[K] Poly K :=
  if 0 ≤ d then homogeneousComponent d.toNat else 0

@[simp] theorem Bproj_of_neg {d : ℤ} (hd : d < 0) : (Bproj d : Poly K →ₗ[K] Poly K) = 0 := by
  simp [Bproj, not_le.2 hd]

theorem Bproj_of_nonneg {d : ℤ} (hd : 0 ≤ d) :
    (Bproj d : Poly K →ₗ[K] Poly K) = homogeneousComponent d.toNat := by
  simp [Bproj, hd]

theorem Bproj_mem (d : ℤ) (g : Poly K) : Bproj d g ∈ Bpiece K d := by
  rcases lt_or_ge d 0 with hd | hd
  · simp [Bproj_of_neg hd]
  · rw [Bproj_of_nonneg hd, Bpiece_of_nonneg hd]
    exact homogeneousComponent_mem _ _

theorem Bproj_of_mem {d e : ℤ} {g : Poly K} (hg : g ∈ Bpiece K e) :
    Bproj d g = if d = e then g else 0 := by
  rcases lt_or_ge e 0 with he | he
  · rw [Bpiece_of_neg he, Submodule.mem_bot] at hg
    subst hg; simp
  rcases lt_or_ge d 0 with hd | hd
  · rw [Bproj_of_neg hd, ite_eq_right (by omega)]; rfl
  rw [Bpiece_of_nonneg he] at hg
  rw [Bproj_of_nonneg hd, homogeneousComponent_of_mem hg]
  congr 1
  simp only [eq_iff_iff]
  omega

theorem Bproj_eq_zero_of_lt {d : ℤ} {g : Poly K} (h : (g.totalDegree : ℤ) < d) :
    Bproj d g = 0 := by
  have hd : 0 ≤ d := le_trans (Int.natCast_nonneg _) h.le
  rw [Bproj_of_nonneg hd]
  exact homogeneousComponent_eq_zero _ _ (by omega)

/-- Every polynomial is the sum of its homogeneous components, summed over any
finite set of degrees containing the relevant window `b + [0, deg g]`. -/
theorem sum_Bproj (b : ℤ) (g : Poly K) (s : Finset ℤ)
    (hs : ∀ d : ℕ, d ≤ g.totalDegree → b + (d : ℤ) ∈ s) :
    ∑ e ∈ s, Bproj (e - b) g = g := by
  classical
  set t : Finset ℤ := (Finset.range (g.totalDegree + 1)).image (fun d : ℕ => b + (d : ℤ)) with ht
  have hts : t ⊆ s := by
    intro e he
    simp only [ht, Finset.mem_image, Finset.mem_range] at he
    obtain ⟨d, hd, rfl⟩ := he
    exact hs d (by omega)
  have hzero : ∀ e ∈ s, e ∉ t → Bproj (e - b) g = 0 := by
    intro e _ het
    rcases lt_or_ge (e - b) 0 with h | h
    · simp [Bproj_of_neg h]
    · rcases le_or_gt (e - b) (g.totalDegree : ℤ) with h' | h'
      · exact absurd (by
          simp only [ht, Finset.mem_image, Finset.mem_range]
          exact ⟨(e - b).toNat, by omega, by omega⟩) het
      · exact Bproj_eq_zero_of_lt h'
  rw [← Finset.sum_subset hts hzero, ht,
    Finset.sum_image (by
      intro x _ y _ h
      have := add_left_cancel h
      exact_mod_cast this)]
  have : ∀ d ∈ Finset.range (g.totalDegree + 1),
      Bproj (b + (d : ℤ) - b) g = homogeneousComponent d g := by
    intro d _
    rw [show b + (d : ℤ) - b = (d : ℤ) by ring, Bproj_of_nonneg (by positivity)]
    simp
  rw [Finset.sum_congr rfl this]
  exact sum_homogeneousComponent g

/-! ### Multiplicativity of the grading -/

theorem Bpiece_smul_Bpiece {d e : ℤ} {f g : Poly K}
    (hf : f ∈ Bpiece K d) (hg : g ∈ Bpiece K e) : f * g ∈ Bpiece K (d + e) := by
  rcases lt_or_ge d 0 with hd | hd
  · rw [Bpiece_of_neg hd, Submodule.mem_bot] at hf; simp [hf]
  rcases lt_or_ge e 0 with he | he
  · rw [Bpiece_of_neg he, Submodule.mem_bot] at hg; simp [hg]
  rw [Bpiece_of_nonneg hd] at hf
  rw [Bpiece_of_nonneg he] at hg
  rw [Bpiece_of_nonneg (by omega)]
  have : (d + e).toNat = d.toNat + e.toNat := by omega
  rw [this]
  exact MvPolynomial.IsHomogeneous.mul hf hg

/-- The degree-`(d+n)` component of `f · g`, for `g` homogeneous of degree `n`,
is the degree-`d` component of `f` times `g`. -/
theorem Bproj_smul_of_mem {d n : ℤ} (f : Poly K) {g : Poly K} (hg : g ∈ Bpiece K n) :
    Bproj (d + n) (f * g) = Bproj d f * g := by
  classical
  set s : Finset ℤ :=
    Insert.insert d ((Finset.range (f.totalDegree + 1)).image fun k : ℕ => (k : ℤ)) with hs
  have hsum : ∑ k ∈ s, Bproj k f = f := by
    have h := sum_Bproj (0 : ℤ) f s (fun k hk => by
      refine Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨k, Finset.mem_range.2 (by omega), ?_⟩)
      simp)
    simpa using h
  calc Bproj (d + n) (f * g)
      = Bproj (d + n) ((∑ k ∈ s, Bproj k f) * g) := by rw [hsum]
    _ = ∑ k ∈ s, Bproj (d + n) (Bproj k f * g) := by
          rw [Finset.sum_mul, map_sum]
    _ = ∑ k ∈ s, (if d + n = k + n then Bproj k f * g else 0) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          exact Bproj_of_mem (Bpiece_smul_Bpiece (Bproj_mem k f) hg)
    _ = Bproj d f * g := by
          rw [Finset.sum_congr rfl (fun k _ => by
            congr 1
            simp only [eq_iff_iff]
            constructor
            · intro hk; omega
            · intro hk; omega : ∀ k ∈ s, (if d + n = k + n then Bproj k f * g else 0)
              = (if d = k then Bproj k f * g else 0))]
          rw [Finset.sum_ite_eq s d (fun k => Bproj k f * g), ite_eq_left (by simp [hs])]

/-- A product of homogeneous elements of the same degree is homogeneous. -/
theorem prod_mem_Bpiece {ι : Type*} (s : Finset ι) (f : ι → Poly K) (c : ℤ)
    (h : ∀ i ∈ s, f i ∈ Bpiece K c) : ∏ i ∈ s, f i ∈ Bpiece K ((s.card : ℤ) * c) := by
  classical
  induction s using Finset.cons_induction with
  | empty =>
      simp only [Finset.prod_empty, Finset.card_empty, Nat.cast_zero, zero_mul]
      rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) by norm_num, Bpiece_natCast]
      exact MvPolynomial.isHomogeneous_one _ _
  | cons i s hi ih =>
      rw [Finset.prod_cons, Finset.card_cons]
      have h1 : f i ∈ Bpiece K c := h i (Finset.mem_cons_self i s)
      have h2 : ∏ j ∈ s, f j ∈ Bpiece K ((s.card : ℤ) * c) :=
        ih fun j hj => h j (Finset.mem_cons_of_mem hj)
      have := Bpiece_smul_Bpiece h1 h2
      rw [show c + (s.card : ℤ) * c = ((s.card + 1 : ℕ) : ℤ) * c by push_cast; ring] at this
      exact this

/-- The determinant of a square matrix with entries homogeneous of degree `c`
is homogeneous of degree `s · c`. -/
theorem det_mem_Bpiece {s : ℕ} (A : Matrix (Fin s) (Fin s) (Poly K)) (c : ℤ)
    (h : ∀ i j, A i j ∈ Bpiece K c) : A.det ∈ Bpiece K ((s : ℤ) * c) := by
  classical
  rw [Matrix.det_apply]
  refine Submodule.sum_mem _ fun σ _ => ?_
  have hp : ∏ i, A (σ i) i ∈ Bpiece K ((s : ℤ) * c) := by
    have := prod_mem_Bpiece (K := K) Finset.univ (fun i => A (σ i) i) c fun i _ => h _ _
    simpa using this
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> rw [hs]
  · simpa using hp
  · simpa using Submodule.neg_mem _ hp

end Height.Graded
