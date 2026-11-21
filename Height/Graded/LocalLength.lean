import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.RingTheory.PowerSeries.Inverse
import Height.Graded.Torsion
import Height.Graded.ProjectiveLine

/-!
# `lem:local-length`, second half: `len N = ∑_x len_x N`

`Height/Graded/Torsion.lean` proves the first half of `lem:local-length`
(`torsion_len_exists`): for `N = F/S` with `F = ⨁ j B(-a j)` graded free and
`S` a graded submodule containing `g · F`, `g ∈ B_c` homogeneous with
`nuLead c g ≠ 0`, the dimension `dim_K N_e` is constant for `e ≫ 0`; the
constant is `len(N)`.  This file proves the second half: that constant is the
sum, over the points of `ℙ¹`, of the `K`-dimensions of the local pieces.

The local piece at a point is taken in
`K⟦u⟧` through the chart map `atPoint t₀ : B → K⟦u⟧`, `μ ↦ 1`, `ν ↦ t₀ + u`
(`Height/Graded/ProjectiveLine.lean`).  In this chart convention `μ = 0` is the point at infinity, and `nuLead c g ≠ 0` says
exactly that `g` has no zero there, so every zero of `g` is a finite point
`t₀ : K`.

## Route

Dehomogenisation `deh : B → K[t]`, `μ ↦ 1`, `ν ↦ t`, is a `K`-linear
isomorphism from `B_d` onto the polynomials of degree `≤ d`, and
`atPoint t₀ = iota t₀ ∘ deh` where `iota t₀ : K[t] → K⟦u⟧` is the Taylor
expansion `t ↦ t₀ + u`.  Writing `Shat` for the `K[t]`-submodule of
`Fin r → K[t]` spanned by `deh S`, the module `Nhat := (Fin r → K[t]) ⧸ Shat`
is `N[μ⁻¹]_0` of the paper.
-/

noncomputable section

namespace Height.Graded

open MvPolynomial Height.Toolbox

variable {K : Type*} [Field K] {r : ℕ}

/-! ### The vector-level dehomogenisation -/

variable (K r) in
/-- Dehomogenisation applied coordinatewise, `(Fin r → B) → (Fin r → K[t])`. -/
def dehVec : (Fin r → Poly K) →ₗ[K] (Fin r → Polynomial K) :=
  LinearMap.pi fun j => (deh K).toLinearMap.comp (LinearMap.proj j)

@[simp] theorem dehVec_apply (x : Fin r → Poly K) (j : Fin r) :
    dehVec K r x j = deh K (x j) := rfl

theorem dehVec_smul (f : Poly K) (x : Fin r → Poly K) :
    dehVec K r (f • x) = deh K f • dehVec K r x := by
  funext j; simp [dehVec_apply, Algebra.smul_def]

theorem dehVec_injOn {a : Fin r → ℤ} {e : ℤ} {x y : Fin r → Poly K}
    (hx : x ∈ (GradedPresentation.of K a).piece e) (hy : y ∈ (GradedPresentation.of K a).piece e)
    (h : dehVec K r x = dehVec K r y) : x = y := by
  funext j
  refine deh_injOn (d := e - a j) ((GradedPresentation.of K _).mem_piece.1 hx j)
    ((GradedPresentation.of K _).mem_piece.1 hy j) ?_
  exact congrFun h j

/-! ### `Shat`: the dehomogenised submodule, and the `μ`-saturation -/

variable (K) in
/-- `Ŝ = S[μ⁻¹]_0`, the `K[t]`-submodule of `Fin r → K[t]` spanned by the
dehomogenisation of `S`. -/
def Shat (S : Submodule (Poly K) (Fin r → Poly K)) :
    Submodule (Polynomial K) (Fin r → Polynomial K) :=
  Submodule.span (Polynomial K) (dehVec K r '' S)

variable (K) in
/-- The `μ`-saturation `(S : μ^∞)` of a submodule. -/
def satMu (S : Submodule (Poly K) (Fin r → Poly K)) :
    Submodule (Poly K) (Fin r → Poly K) :=
  ⨆ k : ℕ, colonChain K S k

theorem mem_colonChain_iff {S : Submodule (Poly K) (Fin r → Poly K)} (k : ℕ)
    {x : Fin r → Poly K} : x ∈ colonChain K S k ↔ (mu : Poly K) ^ k • x ∈ S := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
      rw [colonChain_succ, mem_colonMu, ih, pow_succ, mul_smul]

theorem mem_satMu_iff {S : Submodule (Poly K) (Fin r → Poly K)} {x : Fin r → Poly K} :
    x ∈ satMu K S ↔ ∃ k : ℕ, (mu : Poly K) ^ k • x ∈ S := by
  rw [satMu, Submodule.mem_iSup_of_directed _ ((colonChain_mono S).directed_le)]
  exact exists_congr fun k => mem_colonChain_iff k

theorem le_satMu (S : Submodule (Poly K) (Fin r → Poly K)) : S ≤ satMu K S := by
  intro x hx
  exact mem_satMu_iff.2 ⟨0, by simpa using hx⟩

theorem colonMu_satMu (S : Submodule (Poly K) (Fin r → Poly K)) :
    colonMu K (satMu K S) = satMu K S := by
  refine le_antisymm (fun x hx => ?_) (le_colonMu _)
  have hx' : (mu : Poly K) • x ∈ satMu K S := hx
  obtain ⟨k, hk⟩ := mem_satMu_iff.1 hx'
  refine mem_satMu_iff.2 ⟨k + 1, ?_⟩
  rwa [pow_succ, mul_smul]

/-! ### Pushing homogeneous pieces up by `μ` -/

theorem mu_pow_smul_mem_piece {a : Fin r → ℤ} {e : ℤ} {x : Fin r → Poly K}
    (hx : x ∈ (GradedPresentation.of K a).piece e) (k : ℕ) :
    (mu : Poly K) ^ k • x ∈ (GradedPresentation.of K a).piece (e + k) := by
  have h := (GradedPresentation.of K _).smul_mem_piece (mu_pow_mem (K := K) k) hx
  rwa [add_comm ((k : ℤ)) e] at h

theorem mu_pow_smul_mem_sub {a : Fin r → ℤ} {S : Submodule (Poly K) (Fin r → Poly K)}
    {e : ℤ} {x : Fin r → Poly K} (hx : x ∈ (GradedPresentation.of K a).sub S e) (k : ℕ) :
    (mu : Poly K) ^ k • x ∈ (GradedPresentation.of K a).sub S (e + k) :=
  Submodule.mem_inf.2 ⟨S.smul_mem _ (Submodule.mem_inf.1 hx).1,
    mu_pow_smul_mem_piece (Submodule.mem_inf.1 hx).2 k⟩

theorem dehVec_mu_pow_smul (k : ℕ) (x : Fin r → Poly K) :
    dehVec K r ((mu : Poly K) ^ k • x) = dehVec K r x := by
  rw [dehVec_smul, map_pow, deh_mu, one_pow, one_smul]

theorem map_dehVec_sub_mono {a : Fin r → ℤ} {S : Submodule (Poly K) (Fin r → Poly K)}
    {e e' : ℤ} (h : e ≤ e') :
    ((GradedPresentation.of K a).sub S e).map (dehVec K r)
      ≤ ((GradedPresentation.of K a).sub S e').map (dehVec K r) := by
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨(mu : Poly K) ^ (e' - e).toNat • x, ?_, dehVec_mu_pow_smul _ _⟩
  have := mu_pow_smul_mem_sub hx (e' - e).toNat
  rwa [show e + ((e' - e).toNat : ℤ) = e' by omega] at this

/-! ### `Ŝ` is the union of the dehomogenised graded pieces -/

theorem mem_Shat_iff {a : Fin r → ℤ} {S : Submodule (Poly K) (Fin r → Poly K)}
    (hS : (GradedPresentation.of K a).IsGraded S) {y : Fin r → Polynomial K} :
    y ∈ Shat K S ↔ ∃ e : ℤ, y ∈ ((GradedPresentation.of K a).sub S e).map (dehVec K r) := by
  constructor
  · intro hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨s, hs, rfl⟩ := hz
        obtain ⟨t, ht⟩ := (GradedPresentation.of K a).exists_sum_proj s
        obtain ⟨E, hE⟩ := t.exists_le
        refine ⟨E, ?_⟩
        rw [← ht, map_sum]
        refine Submodule.sum_mem _ fun e he => ?_
        refine map_dehVec_sub_mono (hE e he) ?_
        exact ⟨(GradedPresentation.of K a).proj e s, Submodule.mem_inf.2
          ⟨hS s hs e, (GradedPresentation.of K a).proj_mem e s⟩, rfl⟩
    | zero => exact ⟨0, Submodule.zero_mem _⟩
    | add x y hx hy ihx ihy =>
        obtain ⟨e₁, h₁⟩ := ihx
        obtain ⟨e₂, h₂⟩ := ihy
        exact ⟨max e₁ e₂, Submodule.add_mem _
          (map_dehVec_sub_mono (le_max_left _ _) h₁)
          (map_dehVec_sub_mono (le_max_right _ _) h₂)⟩
    | smul c x hx ih =>
        obtain ⟨e, z, hz, rfl⟩ := ih
        refine ⟨(c.natDegree : ℤ) + e, ?_⟩
        refine ⟨hgz c.natDegree c • z, ?_, ?_⟩
        · exact Submodule.mem_inf.2 ⟨S.smul_mem _ (Submodule.mem_inf.1 hz).1,
            (GradedPresentation.of K _).smul_mem_piece (hgz_mem c.natDegree c)
              (Submodule.mem_inf.1 hz).2⟩
        · rw [dehVec_smul, deh_hgz (Nat.lt_succ_self _)]
  · rintro ⟨e, z, hz, rfl⟩
    exact Submodule.subset_span ⟨z, (Submodule.mem_inf.1 hz).1, rfl⟩

/-! ### The dehomogenised graded pieces and the saturation -/

variable (K) in
/-- The image of `F_e` in `Fin r → K[t]`: the tuples of polynomials of degree
`≤ e - a j`. -/
def Ppiece (a : Fin r → ℤ) (e : ℤ) : Submodule K (Fin r → Polynomial K) :=
  ((GradedPresentation.of K a).piece e).map (dehVec K r)

instance instFinitePpiece (a : Fin r → ℤ) (e : ℤ) : Module.Finite K (Ppiece K a e) :=
  Module.Finite.map _ _

theorem Shat_inf_Ppiece {a : Fin r → ℤ} {S : Submodule (Poly K) (Fin r → Poly K)}
    (hS : (GradedPresentation.of K a).IsGraded S) (e : ℤ) :
    (Shat K S).restrictScalars K ⊓ Ppiece K a e
      = ((GradedPresentation.of K a).sub (satMu K S) e).map (dehVec K r) := by
  refine le_antisymm ?_ ?_
  · rintro y ⟨hy1, x, hxf, rfl⟩
    obtain ⟨e', x', hx', hxx'⟩ := (mem_Shat_iff hS).1 hy1
    obtain ⟨E, hEe, hEe'⟩ : ∃ E : ℤ, e ≤ E ∧ e' ≤ E :=
      ⟨max e e', le_max_left _ _, le_max_right _ _⟩
    have h1 : (mu : Poly K) ^ (E - e).toNat • x ∈ (GradedPresentation.of K a).piece E := by
      have := mu_pow_smul_mem_piece hxf (E - e).toNat
      rwa [show e + (((E - e).toNat : ℤ)) = E by omega] at this
    have h2 : (mu : Poly K) ^ (E - e').toNat • x' ∈ (GradedPresentation.of K a).sub S E := by
      have := mu_pow_smul_mem_sub hx' (E - e').toNat
      rwa [show e' + (((E - e').toNat : ℤ)) = E by omega] at this
    have heq : (mu : Poly K) ^ (E - e).toNat • x = (mu : Poly K) ^ (E - e').toNat • x' := by
      refine dehVec_injOn (a := a) (e := E) h1 (Submodule.mem_inf.1 h2).2 ?_
      rw [dehVec_mu_pow_smul, dehVec_mu_pow_smul, hxx']
    refine ⟨x, Submodule.mem_inf.2 ⟨mem_satMu_iff.2 ⟨(E - e).toNat, ?_⟩, hxf⟩, rfl⟩
    rw [heq]
    exact (Submodule.mem_inf.1 h2).1
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨hxS, hxf⟩ := Submodule.mem_inf.1 hx
    obtain ⟨k, hk⟩ := mem_satMu_iff.1 hxS
    refine ⟨?_, ⟨x, hxf, rfl⟩⟩
    refine (mem_Shat_iff hS).2 ⟨e + k, ?_⟩
    exact ⟨(mu : Poly K) ^ k • x,
      Submodule.mem_inf.2 ⟨hk, mu_pow_smul_mem_piece hxf k⟩, dehVec_mu_pow_smul k x⟩

theorem finrank_map_dehVec {a : Fin r → ℤ} {e : ℤ} (V : Submodule K (Fin r → Poly K))
    (hV : V ≤ (GradedPresentation.of K a).piece e) [Module.Finite K V] :
    Module.finrank K (V.map (dehVec K r)) = Module.finrank K V := by
  have h := finrank_map_add_finrank_inf_ker (K := K) (dehVec K r) V
  have hbot : V ⊓ LinearMap.ker (dehVec K r) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    rw [Submodule.mem_bot]
    refine dehVec_injOn (a := a) (e := e) (hV hx1) (Submodule.zero_mem _) ?_
    rw [map_zero]
    exact hx2
  rw [hbot, finrank_bot, add_zero] at h
  exact h

theorem finrank_Ppiece (a : Fin r → ℤ) (e : ℤ) :
    Module.finrank K (Ppiece K a e) = Module.finrank K ((GradedPresentation.of K a).piece e) :=
  finrank_map_dehVec (a := a) (e := e) _ le_rfl

theorem finrank_map_dehVec_sub (a : Fin r → ℤ) (S : Submodule (Poly K) (Fin r → Poly K))
    (e : ℤ) :
    Module.finrank K (((GradedPresentation.of K a).sub S e).map (dehVec K r))
      = Module.finrank K ((GradedPresentation.of K a).sub S e) :=
  finrank_map_dehVec (a := a) (e := e) _ inf_le_right

/-! ### `Nhat = N[μ⁻¹]_0` -/

variable (K) in
/-- `Ŝ` read as a `K`-submodule.  The quotient `N̂` is formed in the category of
`K`-modules so that `Submodule.liftQ` and `Submodule.mapQ` are available over
`K`; the `K[t]`-action survives as the endomorphisms `NhatMul p`. -/
abbrev ShatK (S : Submodule (Poly K) (Fin r → Poly K)) :
    Submodule K (Fin r → Polynomial K) :=
  (Shat K S).restrictScalars K

variable (K) in
/-- `N̂ = N[μ⁻¹]_0`, the degree-zero part of the localisation at `μ`, realised
as `(Fin r → K[t]) ⧸ Ŝ`. -/
abbrev Nhat (S : Submodule (Poly K) (Fin r → Poly K)) : Type _ :=
  (Fin r → Polynomial K) ⧸ ShatK K S

variable (K) in
/-- The image of `F_e` in `N̂`. -/
def Imge (a : Fin r → ℤ) (S : Submodule (Poly K) (Fin r → Poly K)) (e : ℤ) :
    Submodule K (Nhat K S) :=
  (Ppiece K a e).map (ShatK K S).mkQ

theorem finrank_Imge_add {a : Fin r → ℤ} {S : Submodule (Poly K) (Fin r → Poly K)}
    (hS : (GradedPresentation.of K a).IsGraded S) (e : ℤ) :
    Module.finrank K (Imge K a S e)
        + Module.finrank K ((GradedPresentation.of K a).sub (satMu K S) e)
      = Module.finrank K ((GradedPresentation.of K a).piece e) := by
  have h := finrank_map_add_finrank_inf_ker (K := K) (ShatK K S).mkQ (Ppiece K a e)
  rw [Submodule.ker_mkQ, inf_comm, Shat_inf_Ppiece hS,
    finrank_map_dehVec_sub, finrank_Ppiece] at h
  exact h

/-! ### The saturation does not change the Hilbert function in high degrees -/

theorem finrank_sub_step {a : Fin r → ℤ} (S : Submodule (Poly K) (Fin r → Poly K))
    {c : ℤ} {g : Poly K} (hg : g ∈ Bpiece K c) (hgmu : nuLead c g ≠ 0)
    (hgS : ∀ x : Fin r → Poly K, g • x ∈ S) {e : ℤ} (he : ∀ j, a j + c ≤ e) :
    Module.finrank K ((GradedPresentation.of K a).sub S e)
      = r + Module.finrank K ((GradedPresentation.of K a).sub (colonMu K S) (e - 1)) := by
  have hV := redFil_eq_top a S hg hgmu hgS he
  have h := finrank_sub_split a S e
  rw [hV, finrank_top, Module.finrank_fin_fun] at h
  omega

theorem finrank_sub_colonChain {a : Fin r → ℤ} (S : Submodule (Poly K) (Fin r → Poly K))
    {c : ℤ} {g : Poly K} (hg : g ∈ Bpiece K c) (hgmu : nuLead c g ≠ 0)
    (hgS : ∀ x : Fin r → Poly K, g • x ∈ S) (k : ℕ) {e : ℤ}
    (he : ∀ j, a j + c ≤ e - k) :
    Module.finrank K ((GradedPresentation.of K a).sub S e)
      = k * r + Module.finrank K ((GradedPresentation.of K a).sub (colonChain K S k) (e - k)) := by
  induction k generalizing e with
  | zero =>
      rw [colonChain_zero, Nat.cast_zero, sub_zero, zero_mul, zero_add]
  | succ k ih =>
      have he' : ∀ j, a j + c ≤ e - (k : ℤ) := fun j => by
        have := he j; push_cast at this; omega
      have hstep := finrank_sub_step (a := a) (colonChain K S k) hg hgmu
        (fun x => le_colonChain S k (hgS x)) (e := e - (k : ℤ)) he'
      have hcast : e - (k : ℤ) - 1 = e - ((k + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [ih he', hstep, ← colonChain_succ, hcast]
      ring

theorem colonChain_add_stab {S : Submodule (Poly K) (Fin r → Poly K)} {m : ℕ}
    (hm : colonChain K S m = colonChain K S (m + 1)) (j : ℕ) :
    colonChain K S (m + j) = colonChain K S m := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [show m + (j + 1) = (m + j) + 1 from by ring, colonChain_succ, ih,
        ← colonChain_succ, ← hm]

theorem satMu_eq_colonChain {S : Submodule (Poly K) (Fin r → Poly K)} {m : ℕ}
    (hm : colonChain K S m = colonChain K S (m + 1)) :
    satMu K S = colonChain K S m := by
  refine le_antisymm ?_ ?_
  · rw [satMu]
    refine iSup_le fun k => ?_
    rcases le_or_gt k m with h | h
    · exact colonChain_mono S h
    · rw [show k = m + (k - m) from by omega, colonChain_add_stab hm]
  · exact (le_iSup (fun k : ℕ => colonChain K S k) m)

theorem colonChain_satMu (S : Submodule (Poly K) (Fin r → Poly K)) (k : ℕ) :
    colonChain K (satMu K S) k = satMu K S := by
  induction k with
  | zero => rfl
  | succ k ih => rw [colonChain_succ, ih, colonMu_satMu]

theorem exists_finrank_sub_satMu {a : Fin r → ℤ} (S : Submodule (Poly K) (Fin r → Poly K))
    {c : ℤ} {g : Poly K} (hg : g ∈ Bpiece K c) (hgmu : nuLead c g ≠ 0)
    (hgS : ∀ x : Fin r → Poly K, g • x ∈ S) :
    ∃ E : ℤ, ∀ e, E ≤ e →
      Module.finrank K ((GradedPresentation.of K a).sub (satMu K S) e)
        = Module.finrank K ((GradedPresentation.of K a).sub S e) := by
  obtain ⟨m, hm⟩ := exists_colonChain_stab S
  obtain ⟨M, hM⟩ := Finite.bddAbove_range a
  have hMa : ∀ j, a j ≤ M := fun j => hM ⟨j, rfl⟩
  refine ⟨M + c + m, fun e he => ?_⟩
  have hcond : ∀ j, a j + c ≤ e - (m : ℤ) := fun j => by have := hMa j; omega
  have h1 := finrank_sub_colonChain (a := a) S hg hgmu hgS m hcond
  have h2 := finrank_sub_colonChain (a := a) (satMu K S) hg hgmu
    (fun x => le_satMu S (hgS x)) m hcond
  rw [colonChain_satMu] at h2
  rw [← satMu_eq_colonChain hm] at h1
  omega

/-! ### `dim_K N̂ = len(N)` -/

theorem Ppiece_mono (a : Fin r → ℤ) {e e' : ℤ} (h : e ≤ e') :
    Ppiece K a e ≤ Ppiece K a e' := by
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨(mu : Poly K) ^ (e' - e).toNat • x, ?_, dehVec_mu_pow_smul _ _⟩
  have := mu_pow_smul_mem_piece hx (e' - e).toNat
  rwa [show e + (((e' - e).toNat : ℤ)) = e' by omega] at this

theorem Imge_mono (a : Fin r → ℤ) (S : Submodule (Poly K) (Fin r → Poly K)) {e e' : ℤ}
    (h : e ≤ e') : Imge K a S e ≤ Imge K a S e' :=
  Submodule.map_mono (Ppiece_mono a h)

instance instFiniteImge (a : Fin r → ℤ) (S : Submodule (Poly K) (Fin r → Poly K)) (e : ℤ) :
    Module.Finite K (Imge K a S e) := Module.Finite.map _ _

theorem exists_mem_Ppiece (a : Fin r → ℤ) (y : Fin r → Polynomial K) :
    ∃ e : ℤ, y ∈ Ppiece K a e := by
  obtain ⟨E, hE⟩ := Finite.bddAbove_range (fun j => a j + ((y j).natDegree : ℤ))
  have hEj : ∀ j, a j + ((y j).natDegree : ℤ) ≤ E := fun j => hE ⟨j, rfl⟩
  refine ⟨E, fun j => hgz (E - a j).toNat (y j),
    (GradedPresentation.of K _).mem_piece.2 fun j => ?_, ?_⟩
  · have h := hgz_mem (K := K) (E - a j).toNat (y j)
    rwa [show (((E - a j).toNat : ℤ)) = E - a j by have := hEj j; omega] at h
  · funext j
    exact deh_hgz (by have := hEj j; omega)

theorem exists_finrank_Nhat {a : Fin r → ℤ} {S : Submodule (Poly K) (Fin r → Poly K)}
    (hS : (GradedPresentation.of K a).IsGraded S) {c : ℤ} {g : Poly K}
    (hg : g ∈ Bpiece K c) (hgmu : nuLead c g ≠ 0)
    (hgS : ∀ x : Fin r → Poly K, g • x ∈ S) {len : ℕ} {E : ℤ}
    (hlen : ∀ e, E ≤ e →
      Module.finrank K ((GradedPresentation.of K a).sub S e) + len
        = Module.finrank K ((GradedPresentation.of K a).piece e)) :
    Module.Finite K (Nhat K S) ∧ Module.finrank K (Nhat K S) = len := by
  obtain ⟨E₁, hE₁⟩ := exists_finrank_sub_satMu (a := a) S hg hgmu hgS
  set E₂ : ℤ := max E E₁ with hE₂
  have hIm : ∀ e, E₂ ≤ e → Module.finrank K (Imge K a S e) = len := by
    intro e he
    have h1 := finrank_Imge_add hS (a := a) (S := S) e
    have h2 := hE₁ e (le_trans (le_max_right E E₁) he)
    have h3 := hlen e (le_trans (le_max_left E E₁) he)
    omega
  have hstab : ∀ e, E₂ ≤ e → Imge K a S E₂ = Imge K a S e := fun e he =>
    Submodule.eq_of_le_of_finrank_eq (Imge_mono a S he)
      ((hIm E₂ le_rfl).trans (hIm e he).symm)
  have htop : Imge K a S E₂ = ⊤ := by
    refine eq_top_iff.2 fun z _ => ?_
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective (ShatK K S) z
    obtain ⟨e, he⟩ := exists_mem_Ppiece a y
    rw [hstab (max e E₂) (le_max_right _ _)]
    exact ⟨y, Ppiece_mono a (le_max_left e E₂) he, rfl⟩
  have hfin : Module.Finite K (Imge K a S E₂) := inferInstance
  rw [htop] at hfin
  have := hfin
  have hfin' : Module.Finite K (Nhat K S) := Module.Finite.equiv Submodule.topEquiv
  refine ⟨hfin', ?_⟩
  have hv := hIm E₂ le_rfl
  rw [htop, finrank_top] at hv
  exact hv

/-! ### The local piece at a point `t₀ : K` -/

variable (K r) in
/-- `iota` applied coordinatewise. -/
def iotaVec (t₀ : K) : (Fin r → Polynomial K) →ₗ[K] (Fin r → PowerSeries K) where
  toFun x := fun j => iota K t₀ (x j)
  map_add' x y := by funext j; simp
  map_smul' c x := by
    funext j
    show iota K t₀ (c • x j) = c • iota K t₀ (x j)
    rw [Polynomial.smul_eq_C_mul, map_mul, iota_C, PowerSeries.smul_eq_C_mul]

@[simp] theorem iotaVec_apply (t₀ : K) (x : Fin r → Polynomial K) (j : Fin r) :
    iotaVec K r t₀ x j = iota K t₀ (x j) := rfl

theorem iotaVec_smul (t₀ : K) (p : Polynomial K) (x : Fin r → Polynomial K) :
    iotaVec K r t₀ (p • x) = iota K t₀ p • iotaVec K r t₀ x := by
  funext j
  simp [smul_eq_mul]

variable (K r) in
/-- The chart map on vectors, `(Fin r → B) → (Fin r → K⟦u⟧)`. -/
def atPtVec (t₀ : K) (x : Fin r → Poly K) : Fin r → PowerSeries K :=
  fun j => atPoint t₀ (x j)

theorem atPtVec_eq_iotaVec (t₀ : K) (x : Fin r → Poly K) :
    atPtVec K r t₀ x = iotaVec K r t₀ (dehVec K r x) := by
  funext j
  show atPoint t₀ (x j) = iota K t₀ (deh K (x j))
  rw [atPoint_eq_comp]
  rfl

variable (K r) in
/-- `S ⊗_B K⟦u_{t₀}⟧`: the `K⟦u⟧`-submodule of `Fin r → K⟦u⟧` generated by the
image of `S` under the chart map at `t₀`. -/
def localSub (t₀ : K) (S : Submodule (Poly K) (Fin r → Poly K)) :
    Submodule (PowerSeries K) (Fin r → PowerSeries K) :=
  Submodule.span (PowerSeries K) (atPtVec K r t₀ '' S)

variable (K r) in
/-- `N ⊗_B K⟦u_{t₀}⟧`, the local piece of `N = F/S` at the point `t₀` of `ℙ¹`. -/
abbrev localQuot (t₀ : K) (S : Submodule (Poly K) (Fin r → Poly K)) : Type _ :=
  (Fin r → PowerSeries K) ⧸ localSub K r t₀ S

theorem iotaVec_mem_localSub (t₀ : K) (S : Submodule (Poly K) (Fin r → Poly K))
    {z : Fin r → Polynomial K} (hz : z ∈ Shat K S) :
    iotaVec K r t₀ z ∈ localSub K r t₀ S := by
  induction hz using Submodule.span_induction with
  | mem w hw =>
      obtain ⟨s, hs, rfl⟩ := hw
      rw [← atPtVec_eq_iotaVec]
      exact Submodule.subset_span ⟨s, hs, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul p x _ hx => rw [iotaVec_smul]; exact Submodule.smul_mem _ _ hx

theorem localSub_eq_span_Shat (t₀ : K) (S : Submodule (Poly K) (Fin r → Poly K)) :
    localSub K r t₀ S = Submodule.span (PowerSeries K) (iotaVec K r t₀ '' (Shat K S)) := by
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro _ ⟨s, hs, rfl⟩
    rw [atPtVec_eq_iotaVec]
    exact Submodule.subset_span ⟨dehVec K r s, Submodule.subset_span ⟨s, hs, rfl⟩, rfl⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact iotaVec_mem_localSub t₀ S hz

/-- Everything in the local submodule is congruent, modulo `u^m`, to the image
of an element of `Ŝ`. -/
theorem exists_mem_Shat_of_mem_localSub (t₀ : K) (S : Submodule (Poly K) (Fin r → Poly K))
    (m : ℕ) {y : Fin r → PowerSeries K} (hy : y ∈ localSub K r t₀ S) :
    ∃ z ∈ Shat K S, ∀ j, (PowerSeries.X : PowerSeries K) ^ m ∣ (y j - iotaVec K r t₀ z j) := by
  rw [localSub_eq_span_Shat] at hy
  induction hy using Submodule.span_induction with
  | mem w hw =>
      obtain ⟨z, hz, rfl⟩ := hw
      exact ⟨z, hz, fun j => by simp⟩
  | zero => exact ⟨0, Submodule.zero_mem _, fun j => by simp⟩
  | add x y _ _ ihx ihy =>
      obtain ⟨z₁, hz₁, h₁⟩ := ihx
      obtain ⟨z₂, hz₂, h₂⟩ := ihy
      refine ⟨z₁ + z₂, Submodule.add_mem _ hz₁ hz₂, fun j => ?_⟩
      have h := dvd_add (h₁ j) (h₂ j)
      have hrw : (x j - iotaVec K r t₀ z₁ j) + (y j - iotaVec K r t₀ z₂ j)
          = (x + y) j - iotaVec K r t₀ (z₁ + z₂) j := by
        rw [map_add]
        simp only [Pi.add_apply]
        ring
      rwa [hrw] at h
  | smul c x _ ih =>
      obtain ⟨z, hz, h⟩ := ih
      set pol : Polynomial K := PowerSeries.trunc m c with hpol
      refine ⟨pol.comp (Polynomial.X - Polynomial.C t₀) • z,
        Submodule.smul_mem _ _ hz, fun j => ?_⟩
      have hiz : iotaVec K r t₀ (pol.comp (Polynomial.X - Polynomial.C t₀) • z) j
          = (pol : PowerSeries K) * iotaVec K r t₀ z j := by
        rw [iotaVec_smul, iota_comp_sub]
        rfl
      rw [hiz]
      have hsplit : (c • x) j - (pol : PowerSeries K) * iotaVec K r t₀ z j
          = c * (x j - iotaVec K r t₀ z j)
            + (c - (pol : PowerSeries K)) * iotaVec K r t₀ z j := by
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
      rw [hsplit]
      exact dvd_add (Dvd.dvd.mul_left (h j) c)
        (Dvd.dvd.mul_right (X_pow_dvd_sub_trunc m c) _)

/-! ### Multiplication operators on `N̂` -/

variable (K r) in
/-- Multiplication by `p ∈ K[t]` on `N̂`, as a `K`-linear endomorphism. -/
def NhatMul (S : Submodule (Poly K) (Fin r → Poly K)) (p : Polynomial K) :
    Module.End K (Nhat K S) :=
  Submodule.mapQ _ _
    ((LinearMap.lsmul (Polynomial K) (Fin r → Polynomial K) p).restrictScalars K)
    (fun _ hx => (Shat K S).smul_mem p hx)

@[simp] theorem NhatMul_mk (S : Submodule (Poly K) (Fin r → Poly K)) (p : Polynomial K)
    (x : Fin r → Polynomial K) :
    NhatMul K r S p (Submodule.Quotient.mk x) = Submodule.Quotient.mk (p • x) := rfl

theorem NhatMul_pow (S : Submodule (Poly K) (Fin r → Poly K)) (p : Polynomial K) (k : ℕ) :
    NhatMul K r S (p ^ k) = (NhatMul K r S p) ^ k := by
  induction k with
  | zero =>
      refine LinearMap.ext fun x => ?_
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      simp
  | succ k ih =>
      rw [pow_succ, pow_succ, ← ih]
      refine LinearMap.ext fun x => ?_
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rw [Module.End.mul_apply, NhatMul_mk, NhatMul_mk, NhatMul_mk, mul_smul]

theorem NhatMul_X_sub_C (S : Submodule (Poly K) (Fin r → Poly K)) (t₀ : K) :
    NhatMul K r S (Polynomial.X - Polynomial.C t₀)
      = NhatMul K r S Polynomial.X - t₀ • (1 : Module.End K (Nhat K S)) := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hy : (Polynomial.C t₀ : Polynomial K) • y = t₀ • y := by
    funext j
    exact (Polynomial.smul_eq_C_mul (p := y j) t₀).symm
  rw [NhatMul_mk, sub_smul, hy]
  simp [Submodule.Quotient.mk_smul]

/-! ### `u^M` kills the local quotient -/

theorem atPt_smul_mem_localSub (t₀ : K) {S : Submodule (Poly K) (Fin r → Poly K)} {g : Poly K}
    (hgS : ∀ x : Fin r → Poly K, g • x ∈ S) (y : Fin r → PowerSeries K) :
    atPoint t₀ g • y ∈ localSub K r t₀ S := by
  have hbasis : ∀ j : Fin r,
      atPoint t₀ g • (Pi.single j (1 : PowerSeries K)) ∈ localSub K r t₀ S := by
    intro j
    have hEq : atPtVec K r t₀ (g • (Pi.single j (1 : Poly K)))
        = atPoint t₀ g • (Pi.single j (1 : PowerSeries K)) := by
      funext k
      by_cases h : k = j
      · subst h; simp [atPtVec]
      · simp [atPtVec, Pi.single_eq_of_ne h]
    rw [← hEq]
    exact Submodule.subset_span ⟨_, hgS _, rfl⟩
  have hy : y = ∑ j, y j • Pi.single j (1 : PowerSeries K) := by
    rw [← Finset.univ_sum_single y]
    refine Finset.sum_congr rfl fun j _ => ?_
    funext k
    by_cases h : k = j <;> simp [Pi.single_apply, h]
  rw [hy, Finset.smul_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [smul_comm]
  exact Submodule.smul_mem _ _ (hbasis j)

theorem exists_atPt_eq_X_pow_mul (t₀ : K) {g : Poly K} (hgne : deh K g ≠ 0) :
    ∃ v : PowerSeries K, IsUnit v ∧
      atPoint t₀ g = PowerSeries.X ^ ((deh K g).rootMultiplicity t₀) * v := by
  refine ⟨iota K t₀ ((deh K g) /ₘ
    (Polynomial.X - Polynomial.C t₀) ^ ((deh K g).rootMultiplicity t₀)), ?_, ?_⟩
  · rw [PowerSeries.isUnit_iff_constantCoeff, constantCoeff_iota]
    exact isUnit_iff_ne_zero.2
      (Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero t₀ hgne)
  · have hap : atPoint t₀ g = iota K t₀ (deh K g) := by rw [atPoint_eq_comp]; rfl
    rw [hap, ← iota_X_sub_C t₀, ← map_pow, ← map_mul,
      Polynomial.pow_mul_divByMonic_rootMultiplicity_eq]

theorem X_pow_smul_mem_localSub (t₀ : K) {S : Submodule (Poly K) (Fin r → Poly K)} {g : Poly K}
    (hgS : ∀ x : Fin r → Poly K, g • x ∈ S) {m M : ℕ} {v : PowerSeries K} (hv : IsUnit v)
    (hgv : atPoint t₀ g = PowerSeries.X ^ m * v) (hM : m ≤ M) (y : Fin r → PowerSeries K) :
    (PowerSeries.X : PowerSeries K) ^ M • y ∈ localSub K r t₀ S := by
  obtain ⟨u, hu⟩ := hv
  have hmul : ((PowerSeries.X : PowerSeries K) ^ m * v)
      * ((((u⁻¹ : (PowerSeries K)ˣ) : PowerSeries K)) * PowerSeries.X ^ (M - m))
      = PowerSeries.X ^ M := by
    have h1 : v * (((u⁻¹ : (PowerSeries K)ˣ) : PowerSeries K)) = 1 := by
      rw [← hu]; simp
    calc ((PowerSeries.X : PowerSeries K) ^ m * v)
          * ((((u⁻¹ : (PowerSeries K)ˣ) : PowerSeries K)) * PowerSeries.X ^ (M - m))
        = (PowerSeries.X : PowerSeries K) ^ m * PowerSeries.X ^ (M - m)
            * (v * (((u⁻¹ : (PowerSeries K)ˣ) : PowerSeries K))) := by ring
      _ = (PowerSeries.X : PowerSeries K) ^ M := by
          rw [h1, mul_one, ← pow_add]
          congr 1
          omega
  have key : (PowerSeries.X : PowerSeries K) ^ M • y
      = atPoint t₀ g • (((((u⁻¹ : (PowerSeries K)ˣ) : PowerSeries K))
          * PowerSeries.X ^ (M - m)) • y) := by
    rw [smul_smul, hgv, hmul]
  rw [key]
  exact atPt_smul_mem_localSub t₀ hgS _

/-! ### The comparison map `Ψ : N̂ → N ⊗ K⟦u⟧` -/

variable (K r) in
/-- The `K`-linear comparison map `Ψ : N̂ → N ⊗_B K⟦u_{t₀}⟧`, induced by Taylor
expansion `ι_{t₀} : K[t] → K⟦u⟧` at `t₀`. -/
def PsiMap (t₀ : K) (S : Submodule (Poly K) (Fin r → Poly K)) :
    Nhat K S →ₗ[K] localQuot K r t₀ S :=
  Submodule.liftQ (ShatK K S)
    (((localSub K r t₀ S).mkQ.restrictScalars K).comp (iotaVec K r t₀))
    (by
      intro z hz
      simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply,
        LinearMap.restrictScalars_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact iotaVec_mem_localSub t₀ S hz)

@[simp] theorem PsiMap_mk (t₀ : K) (S : Submodule (Poly K) (Fin r → Poly K))
    (x : Fin r → Polynomial K) :
    PsiMap K r t₀ S (Submodule.Quotient.mk x)
      = Submodule.Quotient.mk (iotaVec K r t₀ x) := rfl

/-- `Ψ` is surjective: truncating a power series at order `M` and substituting
`t − t₀` produces a polynomial representative. -/
theorem PsiMap_surjective (t₀ : K) {S : Submodule (Poly K) (Fin r → Poly K)} {g : Poly K}
    (hgS : ∀ x : Fin r → Poly K, g • x ∈ S) {m M : ℕ} {v : PowerSeries K} (hv : IsUnit v)
    (hgv : atPoint t₀ g = PowerSeries.X ^ m * v) (hM : m ≤ M) :
    Function.Surjective (PsiMap K r t₀ S) := by
  classical
  intro y
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  refine ⟨Submodule.Quotient.mk
    (fun j => (PowerSeries.trunc M (y j)).comp (Polynomial.X - Polynomial.C t₀)), ?_⟩
  rw [PsiMap_mk, Submodule.Quotient.eq]
  have hcoord : ∀ j, iotaVec K r t₀
      (fun j => (PowerSeries.trunc M (y j)).comp (Polynomial.X - Polynomial.C t₀)) j
      = ((PowerSeries.trunc M (y j) : Polynomial K) : PowerSeries K) := fun j => by
    rw [iotaVec_apply, iota_comp_sub]
  have hdvd : ∀ j, (PowerSeries.X : PowerSeries K) ^ M ∣
      (iotaVec K r t₀
        (fun j => (PowerSeries.trunc M (y j)).comp (Polynomial.X - Polynomial.C t₀)) - y) j := by
    intro j
    rw [Pi.sub_apply, hcoord j, ← neg_sub (y j), dvd_neg]
    exact X_pow_dvd_sub_trunc M (y j)
  choose w hw using hdvd
  have hrw : iotaVec K r t₀
      (fun j => (PowerSeries.trunc M (y j)).comp (Polynomial.X - Polynomial.C t₀)) - y
      = (PowerSeries.X : PowerSeries K) ^ M • w := by
    funext j
    rw [Pi.smul_apply, smul_eq_mul]
    exact hw j
  rw [hrw]
  exact X_pow_smul_mem_localSub t₀ hgS hv hgv hM w

/-- The kernel of `Ψ` is the image of multiplication by `(t − t₀)^M`. -/
theorem ker_PsiMap (t₀ : K) {S : Submodule (Poly K) (Fin r → Poly K)} {g : Poly K}
    (hgS : ∀ x : Fin r → Poly K, g • x ∈ S) {m M : ℕ} {v : PowerSeries K} (hv : IsUnit v)
    (hgv : atPoint t₀ g = PowerSeries.X ^ m * v) (hM : m ≤ M) :
    LinearMap.ker (PsiMap K r t₀ S)
      = LinearMap.range ((NhatMul K r S (Polynomial.X - Polynomial.C t₀)) ^ M) := by
  classical
  refine le_antisymm ?_ ?_
  · intro ξ hξ
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ ξ
    rw [LinearMap.mem_ker, PsiMap_mk, Submodule.Quotient.mk_eq_zero] at hξ
    obtain ⟨z, hz, hdvd⟩ := exists_mem_Shat_of_mem_localSub t₀ S M hξ
    have hdvd' : ∀ j, (Polynomial.X - Polynomial.C t₀) ^ M ∣ (x - z) j := by
      intro j
      rw [← X_pow_dvd_iota_iff t₀ M]
      have h := hdvd j
      rwa [iotaVec_apply, iotaVec_apply, ← map_sub] at h
    choose w hw using hdvd'
    have hxz : x - z = (Polynomial.X - Polynomial.C t₀) ^ M • w := by
      funext j
      rw [Pi.smul_apply, smul_eq_mul]
      exact hw j
    refine ⟨Submodule.Quotient.mk w, ?_⟩
    rw [← NhatMul_pow, NhatMul_mk, ← hxz, Submodule.Quotient.eq]
    simpa using (ShatK K S).neg_mem hz
  · rintro _ ⟨η, rfl⟩
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ η
    rw [LinearMap.mem_ker, ← NhatMul_pow, NhatMul_mk, PsiMap_mk,
      Submodule.Quotient.mk_eq_zero, iotaVec_smul, map_pow, iota_X_sub_C]
    exact X_pow_smul_mem_localSub t₀ hgS hv hgv hM _

/-! ### The dimension of the local piece -/

theorem finrank_localQuot_eq_finrank_ker (t₀ : K) {S : Submodule (Poly K) (Fin r → Poly K)}
    [Module.Finite K (Nhat K S)] {g : Poly K}
    (hgS : ∀ x : Fin r → Poly K, g • x ∈ S) {m M : ℕ} {v : PowerSeries K} (hv : IsUnit v)
    (hgv : atPoint t₀ g = PowerSeries.X ^ m * v) (hM : m ≤ M) :
    Module.finrank K (localQuot K r t₀ S)
      = Module.finrank K
          (LinearMap.ker ((NhatMul K r S (Polynomial.X - Polynomial.C t₀)) ^ M)) := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (PsiMap K r t₀ S)
  rw [LinearMap.range_eq_top.2 (PsiMap_surjective t₀ hgS hv hgv hM), finrank_top,
    ker_PsiMap t₀ hgS hv hgv hM] at h1
  have h2 := LinearMap.finrank_range_add_finrank_ker
    ((NhatMul K r S (Polynomial.X - Polynomial.C t₀)) ^ M)
  omega

/-- Once the exponent exceeds the dimension, `ker (T − t₀)^M` is the maximal
generalized eigenspace. -/
theorem ker_pow_eq_maxGenEigenspace {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) (t₀ : K) {M : ℕ}
    (hM : Module.finrank K V ≤ M) :
    LinearMap.ker ((T - t₀ • 1) ^ M) = T.maxGenEigenspace t₀ := by
  refine le_antisymm ?_ ?_
  · rw [← Module.End.genEigenspace_nat]
    exact T.genEigenspace_le_maximal t₀ M
  · rw [Module.End.maxGenEigenspace_eq_genEigenspace_finrank, ← Module.End.genEigenspace_nat]
    exact (T.genEigenspace t₀).monotone (by exact_mod_cast hM)

/-- **The local length at `t₀`.**  The `K`-dimension of `N ⊗_B K⟦u_{t₀}⟧` is the
multiplicity of `t₀` as a root of the characteristic polynomial of
multiplication by `t` on `N̂ = N[μ⁻¹]_0`. -/
theorem finrank_localQuot (t₀ : K) {S : Submodule (Poly K) (Fin r → Poly K)}
    [Module.Finite K (Nhat K S)] {c : ℤ} {g : Poly K} (hg : g ∈ Bpiece K c)
    (hgmu : nuLead c g ≠ 0) (hgS : ∀ x : Fin r → Poly K, g • x ∈ S) :
    Module.finrank K (localQuot K r t₀ S)
      = (LinearMap.charpoly (NhatMul K r S Polynomial.X)).rootMultiplicity t₀ := by
  obtain ⟨v, hv, hgv⟩ := exists_atPt_eq_X_pow_mul t₀ (deh_ne_zero hg hgmu)
  rw [finrank_localQuot_eq_finrank_ker t₀ hgS hv hgv
      (le_max_left ((deh K g).rootMultiplicity t₀) (Module.finrank K (Nhat K S))),
    NhatMul_X_sub_C, ker_pow_eq_maxGenEigenspace _ t₀ (le_max_right _ _),
    LinearMap.finrank_maxGenEigenspace_eq]

/-! ### Points off the zero locus of `g` contribute nothing -/

theorem eval_deh (t₀ : K) (g : Poly K) :
    Polynomial.eval t₀ (deh K g) = MvPolynomial.eval ![1, t₀] g := by
  have hf : (fun i => (Polynomial.aeval t₀ : Polynomial K →ₐ[K] K) (![1, Polynomial.X] i))
      = ![(1 : K), t₀] := by
    funext i
    fin_cases i <;> simp
  have h : (Polynomial.aeval t₀ : Polynomial K →ₐ[K] K) (deh K g)
      = MvPolynomial.aeval ![(1 : K), t₀] g := by
    rw [deh, MvPolynomial.comp_aeval_apply, hf]
  exact h

theorem localSub_eq_top (t₀ : K) {S : Submodule (Poly K) (Fin r → Poly K)} {g : Poly K}
    (hgS : ∀ x : Fin r → Poly K, g • x ∈ S) (hgne : deh K g ≠ 0)
    (ht : Polynomial.eval t₀ (deh K g) ≠ 0) :
    localSub K r t₀ S = ⊤ := by
  obtain ⟨v, hv, hgv⟩ := exists_atPt_eq_X_pow_mul t₀ hgne
  rw [Polynomial.rootMultiplicity_eq_zero ht] at hgv
  refine eq_top_iff.2 fun y _ => ?_
  simpa using X_pow_smul_mem_localSub t₀ hgS hv hgv (le_refl 0) y

theorem finrank_localQuot_of_ne (t₀ : K) {S : Submodule (Poly K) (Fin r → Poly K)} {g : Poly K}
    (hgS : ∀ x : Fin r → Poly K, g • x ∈ S) (hgne : deh K g ≠ 0)
    (ht : MvPolynomial.eval ![1, t₀] g ≠ 0) :
    Module.finrank K (localQuot K r t₀ S) = 0 := by
  have : Subsingleton (localQuot K r t₀ S) :=
    Submodule.Quotient.subsingleton_iff.2
      (localSub_eq_top t₀ hgS hgne (by rwa [eval_deh]))
  exact Module.finrank_zero_of_subsingleton

/-! ### `len N = ∑_x len_x N` -/

/-- **`lem:local-length`, second half.**  Over an algebraically closed field the
length of the graded torsion module `N = F/S` is the sum of the `K`-dimensions
of its local pieces `N ⊗_B K⟦u_{t₀}⟧`, over any finite set of points containing
the zero locus of `g` in the chart `μ = 1`.  (By `nuLead c g ≠ 0` there is no
zero of `g` at `μ = 0`, so this is the sum over all of `ℙ¹`.) -/
theorem sum_finrank_localQuot [IsAlgClosed K] (Tset : Finset K) {a : Fin r → ℤ}
    {S : Submodule (Poly K) (Fin r → Poly K)} (hS : (GradedPresentation.of K a).IsGraded S)
    {c : ℤ} {g : Poly K} (hg : g ∈ Bpiece K c) (hgmu : nuLead c g ≠ 0)
    (hgS : ∀ x : Fin r → Poly K, g • x ∈ S)
    (hTset : ∀ t₀ : K, MvPolynomial.eval ![1, t₀] g = 0 → t₀ ∈ Tset)
    {len : ℕ} {E : ℤ}
    (hlen : ∀ e, E ≤ e →
      Module.finrank K ((GradedPresentation.of K a).sub S e) + len
        = Module.finrank K ((GradedPresentation.of K a).piece e)) :
    ∑ t₀ ∈ Tset, Module.finrank K (localQuot K r t₀ S) = len := by
  classical
  obtain ⟨hfin, hdim⟩ := exists_finrank_Nhat hS hg hgmu hgS hlen
  have := hfin
  set p : Polynomial K := LinearMap.charpoly (NhatMul K r S Polynomial.X) with hp
  have hpne : p ≠ 0 := (LinearMap.charpoly_monic _).ne_zero
  have hloc : ∀ t₀ : K, Module.finrank K (localQuot K r t₀ S) = p.rootMultiplicity t₀ :=
    fun t₀ => finrank_localQuot t₀ hg hgmu hgS
  have hzero : ∀ t₀ : K, t₀ ∉ p.roots.toFinset → p.rootMultiplicity t₀ = 0 := by
    intro t₀ ht
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hpne] at ht
    exact Polynomial.rootMultiplicity_eq_zero ht
  have hsub : p.roots.toFinset ⊆ Tset := by
    intro t₀ ht
    refine hTset t₀ ?_
    by_contra hne
    have h0 : Module.finrank K (localQuot K r t₀ S) = 0 :=
      finrank_localQuot_of_ne t₀ hgS (deh_ne_zero hg hgmu) hne
    rw [hloc t₀] at h0
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hpne] at ht
    exact ((Polynomial.rootMultiplicity_pos hpne).2 ht).ne' h0
  calc ∑ t₀ ∈ Tset, Module.finrank K (localQuot K r t₀ S)
      = ∑ t₀ ∈ Tset, p.rootMultiplicity t₀ := Finset.sum_congr rfl fun t₀ _ => hloc t₀
    _ = ∑ t₀ ∈ p.roots.toFinset, p.rootMultiplicity t₀ :=
        (Finset.sum_subset hsub fun t₀ _ ht => hzero t₀ ht).symm
    _ = ∑ t₀ ∈ p.roots.toFinset, p.roots.count t₀ :=
        Finset.sum_congr rfl fun t₀ _ => (Polynomial.count_roots p).symm
    _ = Multiset.card p.roots := Multiset.toFinset_sum_count_eq _
    _ = p.natDegree := Polynomial.splits_iff_card_roots.1 (IsAlgClosed.splits p)
    _ = Module.finrank K (Nhat K S) := LinearMap.charpoly_natDegree _
    _ = len := hdim

/-- The zeros of `g` in the chart `μ = 1` form a finite set. -/
theorem exists_finset_zeros {c : ℤ} {g : Poly K} (hg : g ∈ Bpiece K c) (hgmu : nuLead c g ≠ 0) :
    ∃ Tset : Finset K, ∀ t₀ : K, MvPolynomial.eval ![1, t₀] g = 0 → t₀ ∈ Tset := by
  classical
  refine ⟨(deh K g).roots.toFinset, fun t₀ ht => ?_⟩
  rw [Multiset.mem_toFinset, Polynomial.mem_roots (deh_ne_zero hg hgmu), Polynomial.IsRoot,
    eval_deh]
  exact ht

/-- **`lem:local-length`.**  The sum of the local lengths *is* the length: for
`e ≫ 0`, `dim_K N_e = ∑_x len_x N`.  (Self-contained form, with the length
produced by `torsion_len_exists`.) -/
theorem sum_localQuot_eq_len [IsAlgClosed K] (Tset : Finset K) {a : Fin r → ℤ}
    {S : Submodule (Poly K) (Fin r → Poly K)} (hS : (GradedPresentation.of K a).IsGraded S)
    {c : ℤ} {g : Poly K} (hg : g ∈ Bpiece K c) (hgmu : nuLead c g ≠ 0)
    (hgS : ∀ x : Fin r → Poly K, g • x ∈ S)
    (hTset : ∀ t₀ : K, MvPolynomial.eval ![1, t₀] g = 0 → t₀ ∈ Tset) :
    ∃ E : ℤ, ∀ e, E ≤ e →
      Module.finrank K ((GradedPresentation.of K a).sub S e)
          + ∑ t₀ ∈ Tset, Module.finrank K (localQuot K r t₀ S)
        = Module.finrank K ((GradedPresentation.of K a).piece e) := by
  obtain ⟨len, E, hlen⟩ := torsion_len_exists a S hg hgmu hgS
  refine ⟨E, fun e he => ?_⟩
  rw [sum_finrank_localQuot Tset hS hg hgmu hgS hTset hlen]
  exact hlen e he

/-! ### The chart swap `μ ↔ ν`

`sum_finrank_localQuot` needs `nuLead c g ≠ 0`, i.e. no zero of `g` at the
point `μ = 0`.  A consumer whose `g` does vanish there can first move that
point to `∞` by the swap `μ ↔ ν`.  What is here is the swap itself (`swapVec`)
and its compatibility with the grading (`swapVec_smul`, `swapVec_mem_piece`);
the statement that the length is unchanged is **not** proved. -/

variable (K r) in
/-- The chart swap on vectors. -/
def swapVec : (Fin r → Poly K) ≃ₗ[K] (Fin r → Poly K) :=
  LinearEquiv.piCongrRight fun _ => (swapAlg K).toLinearEquiv

@[simp] theorem swapVec_apply (x : Fin r → Poly K) (j : Fin r) :
    swapVec K r x j = swapAlg K (x j) := rfl

@[simp] theorem swapVec_swapVec (x : Fin r → Poly K) : swapVec K r (swapVec K r x) = x := by
  funext j
  simp [swapVec_apply]

theorem swapVec_smul (f : Poly K) (x : Fin r → Poly K) :
    swapVec K r (f • x) = swapAlg K f • swapVec K r x := by
  funext j
  show swapAlg K (f * x j) = swapAlg K f * swapAlg K (x j)
  rw [map_mul]

theorem swapVec_mem_piece {a : Fin r → ℤ} {e : ℤ} {x : Fin r → Poly K}
    (hx : x ∈ (GradedPresentation.of K a).piece e) :
    swapVec K r x ∈ (GradedPresentation.of K a).piece e :=
  (GradedPresentation.of K _).mem_piece.2 fun j =>
    swapAlg_mem_Bpiece ((GradedPresentation.of K _).mem_piece.1 hx j)

end Height.Graded
