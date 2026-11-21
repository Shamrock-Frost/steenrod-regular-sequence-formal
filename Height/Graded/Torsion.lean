import Mathlib.RingTheory.Polynomial.Basic
import Height.Graded.Free

/-!
# `lem:local-length`, first half: `dim N_e` is constant in high degrees

For a finitely generated graded torsion module `N` over `B = K[μ, ν]`,
`lem:local-length` asserts that `dim_K N_e` is constant for `e ≫ 0` and that
the constant is the sum of the lengths of the localizations `N_(x)` over the
points `x ∈ ℙ¹`.  This file proves the first half — the one that makes
`len(N) := dim_K N_e` (`e ≫ 0`) a definition — for `N = F/S` with `F` graded
free and `S` a graded submodule containing `g · F` for a homogeneous `g` that
is not divisible by `μ` (the paper's normalization "no zero of `g` lies on
`μ = 0`", achieved there by a change of coordinates).

The proof is the one in the paper, run through the reduction modulo `μ` of
`Height/Graded/Lead.lean`.  Writing `S_e` for the degree-`e` piece and
`(S : μ) = {y | μ y ∈ S}`:

* writing `P = GradedPresentation.of K a`, the reduction `P.redMu e` maps `S_e`
  onto `P.redFil S e` with kernel `μ · (S : μ)_{e-1}`, so
  `dim S_e = dim (P.redFil S e) + dim (S : μ)_{e-1}`;
* `P.redFil S e = ⊤` once `e` is large, because `g · F ⊆ S` and `nuLead g ≠ 0`;
* `dim F_e = r + dim F_{e-1}` once `e` is large;

hence `dim F_e − dim S_e = dim F_{e-1} − dim (S : μ)_{e-1}`.  The chain
`S ⊆ (S : μ) ⊆ (S : μ²) ⊆ ⋯` stabilizes because `B` is Noetherian, and at the
stable index the displayed identity says the difference is constant.
-/

noncomputable section

namespace Height.Graded

open MvPolynomial Height.Toolbox

variable {K : Type*} [Field K] {r : ℕ}

/-! ### The colon submodule `(S : μ)` -/

variable (K) in
/-- `(S : μ) = {y | μ y ∈ S}`. -/
def colonMu (S : Submodule (Poly K) (Fin r → Poly K)) :
    Submodule (Poly K) (Fin r → Poly K) :=
  S.comap (LinearMap.lsmul (Poly K) (Fin r → Poly K) mu)

theorem mem_colonMu {S : Submodule (Poly K) (Fin r → Poly K)} {y : Fin r → Poly K} :
    y ∈ colonMu K S ↔ (mu : Poly K) • y ∈ S := Iff.rfl

theorem le_colonMu (S : Submodule (Poly K) (Fin r → Poly K)) : S ≤ colonMu K S :=
  fun _ hx => S.smul_mem _ hx

/-! ### The rank identity `dim S_e = dim (P.redFil S e) + dim (S : μ)_{e-1}` -/

variable (K) in
/-- Multiplication by `μ`, as a `K`-linear endomorphism of `Fin r → B`. -/
def mulMuLin : (Fin r → Poly K) →ₗ[K] (Fin r → Poly K) :=
  (LinearMap.lsmul (Poly K) (Fin r → Poly K) mu).restrictScalars K

@[simp] theorem mulMuLin_apply (x : Fin r → Poly K) :
    mulMuLin K x = (mu : Poly K) • x := rfl

theorem mulMuLin_injective : Function.Injective (mulMuLin K (r := r)) := by
  intro x y hxy
  have hmu : (mu : Poly K) ≠ 0 := by simp [mu, MvPolynomial.X_ne_zero]
  funext j
  have h := congrFun hxy j
  simp only [mulMuLin_apply, Pi.smul_apply, smul_eq_mul] at h
  exact mul_left_cancel₀ hmu h

theorem inf_ker_lam (a : Fin r → ℤ) (S : Submodule (Poly K) (Fin r → Poly K)) (e : ℤ) :
    (GradedPresentation.of K a).sub S e ⊓ LinearMap.ker ((GradedPresentation.of K a).redMu e)
      = ((GradedPresentation.of K a).sub (colonMu K S) (e - 1)).map (mulMuLin K) := by
  ext x
  constructor
  · rintro ⟨hxS, hxk⟩
    obtain ⟨y, hy, rfl⟩ :=
      (GradedPresentation.of K a).exists_eq_mu_smul (Submodule.mem_inf.1 hxS).2 hxk
    refine Submodule.mem_map.2 ⟨y, Submodule.mem_inf.2 ⟨?_, hy⟩, rfl⟩
    exact (Submodule.mem_inf.1 hxS).1
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨hyS, hyf⟩ := Submodule.mem_inf.1 hy
    have hmem : (mu : Poly K) • y ∈ (GradedPresentation.of K a).piece e := by
      have h := (GradedPresentation.of K _).smul_mem_piece (mu_mem (K := K)) hyf
      rwa [show (1 : ℤ) + (e - 1) = e by ring] at h
    refine Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨hyS, hmem⟩, ?_⟩
    rw [LinearMap.mem_ker]
    have h := (GradedPresentation.of K a).redMu_smul (mu_mem (K := K)) hyf
    rw [show (1 : ℤ) + (e - 1) = e by ring, nuLead_mu, zero_smul] at h
    exact h

/-- Splitting the degree-`e` piece of `S` by the reduction modulo `μ`. -/
theorem finrank_sub_split (a : Fin r → ℤ) (S : Submodule (Poly K) (Fin r → Poly K)) (e : ℤ) :
    Module.finrank K ((GradedPresentation.of K a).redFil S e)
        + Module.finrank K ((GradedPresentation.of K a).sub (colonMu K S) (e - 1))
      = Module.finrank K ((GradedPresentation.of K a).sub S e) := by
  have h := finrank_map_add_finrank_inf_ker ((GradedPresentation.of K a).redMu e)
    ((GradedPresentation.of K a).sub S e)
  rw [inf_ker_lam] at h
  rw [show (GradedPresentation.of K a).redFil S e
      = ((GradedPresentation.of K a).sub S e).map ((GradedPresentation.of K a).redMu e) from rfl,
    (Submodule.equivMapOfInjective _ mulMuLin_injective
      ((GradedPresentation.of K a).sub (colonMu K S) (e - 1))).finrank_eq]
  exact h

/-! ### `P.redFil` is everything in high degrees -/

theorem redFil_eq_top (a : Fin r → ℤ) (S : Submodule (Poly K) (Fin r → Poly K))
    {c : ℤ} {g : Poly K} (hg : g ∈ Bpiece K c) (hgmu : nuLead c g ≠ 0)
    (hgS : ∀ x : Fin r → Poly K, g • x ∈ S) {e : ℤ} (he : ∀ j, a j + c ≤ e) :
    (GradedPresentation.of K a).redFil S e = ⊤ := by
  classical
  have hbasis : ∀ j : Fin r,
      (Pi.single j (1 : K)) ∈ (GradedPresentation.of K a).redFil S e := by
    intro j
    set y : Fin r → Poly K := Pi.single j ((nu : Poly K) ^ (e - c - a j).toNat) with hy
    have hyf : y ∈ (GradedPresentation.of K a).piece (e - c) := by
      refine (GradedPresentation.of K _).mem_piece.2 fun k => ?_
      by_cases hk : k = j
      · subst hk
        have h := nu_pow_mem (K := K) (e - c - a k).toNat
        rw [show (((e - c - a k).toNat : ℤ)) = e - c - a k by have := he k; omega] at h
        simpa [hy, Pi.single_eq_same] using h
      · simp only [hy, Pi.single_eq_of_ne hk]
        exact Submodule.zero_mem _
    have hlam : (GradedPresentation.of K a).redMu (e - c) y = Pi.single j (1 : K) := by
      funext k
      by_cases hk : k = j
      · subst hk
        have h := nuLead_nu_pow (K := K) (e - c - a k).toNat
        rw [show (((e - c - a k).toNat : ℤ)) = e - c - a k by have := he k; omega] at h
        show nuLead (e - c - a k) (y k) = _
        simpa [hy, Pi.single_eq_same] using h
      · show nuLead (e - c - a k) (y k) = _
        simp [hy, Pi.single_eq_of_ne hk]
    have hgy : g • y ∈ (GradedPresentation.of K a).sub S e := by
      refine Submodule.mem_inf.2 ⟨hgS y, ?_⟩
      have h := (GradedPresentation.of K _).smul_mem_piece hg hyf
      rwa [show c + (e - c) = e by ring] at h
    have hmem : nuLead c g • Pi.single j (1 : K) ∈ (GradedPresentation.of K a).redFil S e := by
      refine (GradedPresentation.of K a).mem_redFil.2 ⟨g • y, hgy, ?_⟩
      have h := (GradedPresentation.of K a).redMu_smul hg hyf
      rw [show c + (e - c) = e by ring, hlam] at h
      exact h
    have := Submodule.smul_mem ((GradedPresentation.of K a).redFil S e) (nuLead c g)⁻¹ hmem
    rwa [smul_smul, inv_mul_cancel₀ hgmu, one_smul] at this
  refine eq_top_iff.2 fun v _ => ?_
  have hv : v = ∑ j, v j • Pi.single j (1 : K) := by
    rw [← Finset.univ_sum_single v]
    refine Finset.sum_congr rfl fun j _ => ?_
    funext k
    by_cases hk : k = j <;> simp [Pi.single_apply, hk]
  rw [hv]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hbasis j)

/-! ### The Hilbert function of `F` grows by `r` -/

theorem finrank_piece_step (a : Fin r → ℤ) {e : ℤ} (he : ∀ j, a j + 1 ≤ e) :
    Module.finrank K ((GradedPresentation.of K a).piece e)
      = r + Module.finrank K ((GradedPresentation.of K a).piece (e - 1)) := by
  rw [GradedPresentation.finrank_piece, GradedPresentation.finrank_piece]
  have h : ∀ j : Fin r, (e - a j + 1).toNat = 1 + (e - 1 - a j + 1).toNat := by
    intro j
    have := he j
    omega
  rw [Finset.sum_congr rfl fun j _ => h j, Finset.sum_add_distrib]
  simp

/-! ### The colon chain stabilizes -/

variable (K) in
/-- The chain `S ⊆ (S : μ) ⊆ (S : μ²) ⊆ ⋯`. -/
def colonChain (S : Submodule (Poly K) (Fin r → Poly K)) :
    ℕ → Submodule (Poly K) (Fin r → Poly K)
  | 0 => S
  | k + 1 => colonMu K (colonChain S k)

@[simp] theorem colonChain_zero (S : Submodule (Poly K) (Fin r → Poly K)) :
    colonChain K S 0 = S := rfl

theorem colonChain_succ (S : Submodule (Poly K) (Fin r → Poly K)) (k : ℕ) :
    colonChain K S (k + 1) = colonMu K (colonChain K S k) := rfl

theorem colonChain_mono (S : Submodule (Poly K) (Fin r → Poly K)) :
    Monotone (colonChain K S) :=
  monotone_nat_of_le_succ fun _ => le_colonMu _

theorem le_colonChain (S : Submodule (Poly K) (Fin r → Poly K)) (k : ℕ) :
    S ≤ colonChain K S k := colonChain_mono S (Nat.zero_le k)

theorem exists_colonChain_stab (S : Submodule (Poly K) (Fin r → Poly K)) :
    ∃ m, colonChain K S m = colonChain K S (m + 1) := by
  obtain ⟨m, hm⟩ := monotone_stabilizes_iff_noetherian.2 inferInstance
    (⟨colonChain K S, colonChain_mono S⟩ : ℕ →o Submodule (Poly K) (Fin r → Poly K))
  exact ⟨m, hm (m + 1) (Nat.le_succ m)⟩

/-! ### `len N` exists -/

/-- **`lem:local-length`, first half.**  Let `F = ⨁ j, B(-a j)` and let `S` be a
submodule with `g · F ⊆ S` for some `g ∈ B_c` with `μ ∤ g` (equivalently
`nuLead c g ≠ 0`); this is the paper's normalization "no zero of `g` lies on
`μ = 0`".  Then `dim_K (F/S)_e` is constant for `e ≫ 0`.  The constant is
`len (F/S)`.

The statement is written as `dim S_e + len = dim F_e`, which is
`dim (F/S)_e = len`. -/
theorem torsion_len_exists (a : Fin r → ℤ) (S : Submodule (Poly K) (Fin r → Poly K))
    {c : ℤ} {g : Poly K} (hg : g ∈ Bpiece K c) (hgmu : nuLead c g ≠ 0)
    (hgS : ∀ x : Fin r → Poly K, g • x ∈ S) :
    ∃ (len : ℕ) (E : ℤ), ∀ e, E ≤ e →
      Module.finrank K ((GradedPresentation.of K a).sub S e) + len
        = Module.finrank K ((GradedPresentation.of K a).piece e) := by
  classical
  obtain ⟨M, hM⟩ := Finite.bddAbove_range a
  have hMa : ∀ j, a j ≤ M := fun j => hM ⟨j, rfl⟩
  set E : ℤ := M + max c 1 with hEdef
  have hE1 : ∀ j, a j + c ≤ E := fun j => by have := hMa j; simp only [hEdef]; omega
  have hE2 : ∀ j, a j + 1 ≤ E := fun j => by have := hMa j; simp only [hEdef]; omega
  have hgS' : ∀ k : ℕ, ∀ x : Fin r → Poly K, g • x ∈ colonChain K S k :=
    fun k x => le_colonChain S k (hgS x)
  have hstep : ∀ (k : ℕ) (e : ℤ), E ≤ e →
      Module.finrank K ((GradedPresentation.of K a).sub (colonChain K S k) e)
        = r + Module.finrank K
            ((GradedPresentation.of K a).sub (colonChain K S (k + 1)) (e - 1)) := by
    intro k e he
    have hV : (GradedPresentation.of K a).redFil (colonChain K S k) e = ⊤ :=
      redFil_eq_top a _ hg hgmu (hgS' k) (fun j => le_trans (hE1 j) he)
    have h := finrank_sub_split a (colonChain K S k) e
    rw [hV, finrank_top, Module.finrank_fin_fun] at h
    exact h.symm
  have hF : ∀ e : ℤ, E ≤ e →
      Module.finrank K ((GradedPresentation.of K a).piece e)
        = r + Module.finrank K ((GradedPresentation.of K a).piece (e - 1)) :=
    fun e he => finrank_piece_step a (fun j => le_trans (hE2 j) he)
  obtain ⟨m, hm⟩ := exists_colonChain_stab S
  have hAm : ∀ e : ℤ, E ≤ e →
      Module.finrank K ((GradedPresentation.of K a).sub (colonChain K S m) e)
        = r + Module.finrank K ((GradedPresentation.of K a).sub (colonChain K S m) (e - 1)) := by
    intro e he
    rw [hstep m e he, ← hm]
  set d : ℕ := Module.finrank K ((GradedPresentation.of K a).piece (E - 1))
    - Module.finrank K ((GradedPresentation.of K a).sub (colonChain K S m) (E - 1)) with hddef
  have hle : Module.finrank K ((GradedPresentation.of K a).sub (colonChain K S m) (E - 1))
      ≤ Module.finrank K ((GradedPresentation.of K a).piece (E - 1)) :=
    (GradedPresentation.of K a).finrank_sub_le _ _
  have hup : ∀ n : ℕ,
      Module.finrank K ((GradedPresentation.of K a).sub (colonChain K S m) (E - 1 + (n : ℤ))) + d
        = Module.finrank K ((GradedPresentation.of K a).piece (E - 1 + (n : ℤ))) := by
    intro n
    induction n with
    | zero =>
        rw [Nat.cast_zero, add_zero]
        omega
    | succ n ih =>
        have he : E ≤ E - 1 + ((n : ℤ) + 1) := by omega
        have h1 := hAm (E - 1 + ((n : ℤ) + 1)) he
        have h2 := hF (E - 1 + ((n : ℤ) + 1)) he
        rw [show E - 1 + ((n : ℤ) + 1) - 1 = E - 1 + (n : ℤ) by ring] at h1 h2
        rw [show ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 by push_cast; ring]
        omega
  have hAmall : ∀ e : ℤ, E - 1 ≤ e →
      Module.finrank K ((GradedPresentation.of K a).sub (colonChain K S m) e) + d
        = Module.finrank K ((GradedPresentation.of K a).piece e) := by
    intro e he
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, e = E - 1 + (n : ℤ) := ⟨(e - (E - 1)).toNat, by omega⟩
    exact hup n
  have hdown : ∀ (n : ℕ) (e : ℤ), E + (n : ℤ) ≤ e →
      Module.finrank K ((GradedPresentation.of K a).sub (colonChain K S n) (e - (n : ℤ))) + d
        = Module.finrank K ((GradedPresentation.of K a).piece (e - (n : ℤ))) →
      Module.finrank K ((GradedPresentation.of K a).sub S e) + d
        = Module.finrank K ((GradedPresentation.of K a).piece e) := by
    intro n
    induction n with
    | zero =>
        intro e _ h
        rw [Nat.cast_zero, sub_zero] at h
        exact h
    | succ n ih =>
        intro e he h
        refine ih e (by push_cast at he ⊢; omega) ?_
        have hstep' := hstep n (e - (n : ℤ)) (by push_cast at he ⊢; omega)
        have hF' := hF (e - (n : ℤ)) (by push_cast at he ⊢; omega)
        rw [show e - (n : ℤ) - 1 = e - ((n + 1 : ℕ) : ℤ) by push_cast; ring] at hstep' hF'
        omega
  refine ⟨d, E + (m : ℤ), fun e he => ?_⟩
  refine hdown m e he (hAmall (e - (m : ℤ)) ?_)
  omega

end Height.Graded
