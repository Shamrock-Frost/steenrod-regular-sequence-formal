import Height.Pencil.Arcs
import Height.Pencil.Parabolic
import Height.Orbital.GenericRank
import Mathlib.RingTheory.Nakayama

/-!
# The local model at a point of `ℙ¹` (`lem:local-model`)

The paper, `lem:local-model`.

Everything here is over the local ring `R = K⟦u⟧` and its
fraction field `L = K⸨u⸩`; the pencil enters through `Pat N M t₀`
(`Pencil/Chart.lean`), but the two theorems are stated for an arbitrary
nilpotent `P` over `R`, since that is all they use.

## The fibre flag

`fibFlag P k ⊆ K^n` is the reduction modulo `u` of the integral kernel flag
`S_k := ker (P^k) ⊆ R^n`, i.e. `V_k := S_k(x)` of the paper.

**The fibre flag is not `ker (N₀^k)`.**  The special fibre of `S_k` differs
from `ker (N₀^k)`, `N₀ = P(x)`, at a drop point,
which is the only place the lemma is used: `dim V_k = n - rk_L P^k` is the
*generic* jump `m_k`, while `dim ker N₀^k` is strictly larger exactly when the
type drops at `x` (`fibFlag_eq_top` is the only equality of the two recorded
here).  The paper is
consistent: `lem:local-model` writes `V_k := S_k(x)` for the *fibre flag* and
applies `lem:parabolic-field` to `P̃` over `K_x`, whose kernel flag is
`V_• ⊗ K_x`, never to `N₀`.

## What is proved

1. `exists_adapted_trivialisation` (`lem:local-model`(1)): for `P^n = 0`
   there is `h ∈ GL_n(R)` with `h(x) = 1` and `h · (V_k ⊗ R) = S_k` for every
   `k`.  It provides the adapted frame at a single point and has no consumer
   in the tree.  What is *not* proved here, and what the
   paper draws from the trivialisation, is the conjugated form: that
   `P̃ := h⁻¹ P h` lowers the constant flag, i.e. `P̃ ∈ n_{V_•} ⊗ R` with
   `P̃(x) = P(x)`.
   The trivialisation is an adapted *section*
   `σ : K^n → R^n` of the reduction map (`exists_adapted_section`), whose
   matrix is `h`; that `h` is invertible is `matC h = 1` plus
   `PowerSeries.isUnit_iff_constantCoeff`, and that it is *onto* each `S_k` is
   Nakayama's lemma, the flag being saturated (`kerFlag_saturated`).

   `lem:local-model`(2) (`ker_{K_x} P̃^k = V_k ⊗ K_x`) is not needed
   downstream and is not proved: `Pencil/FlagVelocityArc.lean` applies
   `lem:parabolic-field` to `P` over `K_x` itself, whose kernel flag is the
   `h`-conjugate of `V_• ⊗ K_x`.

2. `exists_velocity_decomposition` (`lem:local-model`(3)): a direction `X` over
   `R` which is *kernel flat over `R`* — `Isotropy.DCond P X`, i.e.
   `D_k(X)(S_k) ⊆ P^k R^n` for every `k` — decomposes as
   `X = [P, W] + U` with `W` over `R` and `U` *lowering* the flag `S_•`
   (`Lowering P U`); the paper's conjugated form
   `X = [P, W] + h U h⁻¹` with `U ∈ n_{V_•} ⊗ R`, and its value at the point
   `U(x) ∈ n_{V_•}`, are not stated here.  The proof is the regular part
   (`Isotropy.exists_regular_g`, the PID form of the first half of
   `lem:field-commutator`) followed by `Isotropy.lowering_of_dpow_vanishing`.

**The hypothesis `Isotropy.DCond P X` is not discharged here.**  It is
`lem:flag-flat`(1) *localised at `x`*: for the pencil velocity of an arc in
`Î` it comes from the flatness of the arc's kernel flag over `R⟦s⟧`
(`lem:local-model`(3)'s proof), equivalently from the degreewise form of
`lem:flag-flat`(1).  `Pencil/Arcs.lean` proves only the function-field form
(`kernel_flat`: `D_k(X)(S_k) ⊆ P^k L^n` over
`L = K(ℙ¹)`), and that form is *strictly weaker*: with `P = [[0,u],[0,0]]`
(the pencil `νM`, `M = e₁₂`, at its drop point `t₀ = 0`) the direction
`X = diag(1,-1)` is `[P, u⁻¹e₂₁]`, hence a commutator over `L`, but
`X ∉ [P, gl₂(R)] + n_{V_•} ⊗ R`.  So the decomposition genuinely needs the
integral hypothesis, and it is carried as an explicit hypothesis.
-/

namespace Height.Pencil

open Matrix Height.Orbital Height.Graded

universe u

section Fibre

variable {K : Type u} [Field K] {n : ℕ}

/-- The constant vector with entries `v`. -/
noncomputable def constVec (v : Fin n → K) : Fin n → PowerSeries K :=
  fun i => PowerSeries.C (v i)

@[simp] theorem vecC_constVec (v : Fin n → K) : vecC (constVec v) = v := by
  funext i
  simp [constVec, vecC]

/-- Reduction modulo `u`, as a `K`-linear map. -/
noncomputable def vecCL : (Fin n → PowerSeries K) →ₗ[K] (Fin n → K) where
  toFun := vecC
  map_add' w w' := by
    funext i
    simp [vecC]
  map_smul' c w := by
    funext i
    show PowerSeries.constantCoeff (c • w i) = c • PowerSeries.constantCoeff (w i)
    rw [PowerSeries.constantCoeff_smul]

@[simp] theorem vecCL_apply (w : Fin n → PowerSeries K) : vecCL w = vecC w := rfl

/-- `V_k := S_k(x)`, the fibre of the integral kernel flag `S_k = ker (P^k)`
at the closed point: the paper's fibre flag. -/
noncomputable def fibFlag (P : Matrix (Fin n) (Fin n) (PowerSeries K)) (k : ℕ) :
    Submodule K (Fin n → K) :=
  Submodule.map vecCL (Submodule.restrictScalars K (Isotropy.kerFlag P k))

theorem mem_fibFlag {P : Matrix (Fin n) (Fin n) (PowerSeries K)} {k : ℕ} {v : Fin n → K} :
    v ∈ fibFlag P k ↔ ∃ w ∈ Isotropy.kerFlag P k, vecC w = v := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w, hw, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w, hw, rfl⟩

theorem vecC_mem_fibFlag {P : Matrix (Fin n) (Fin n) (PowerSeries K)} {k : ℕ}
    {w : Fin n → PowerSeries K} (hw : w ∈ Isotropy.kerFlag P k) : vecC w ∈ fibFlag P k :=
  mem_fibFlag.2 ⟨w, hw, rfl⟩

theorem fibFlag_mono (P : Matrix (Fin n) (Fin n) (PowerSeries K)) {k l : ℕ} (h : k ≤ l) :
    fibFlag P k ≤ fibFlag P l := by
  rintro _ ⟨w, hw, rfl⟩
  exact ⟨w, Isotropy.kerFlag_mono P h hw, rfl⟩

theorem fibFlag_eq_top (P : Matrix (Fin n) (Fin n) (PowerSeries K)) {k : ℕ}
    (h : P ^ k = 0) : fibFlag P k = ⊤ := by
  refine eq_top_iff.2 fun v _ => ?_
  refine mem_fibFlag.2 ⟨constVec v, ?_, vecC_constVec v⟩
  rw [Isotropy.mem_kerFlag, h, Matrix.zero_mulVec]

/-- The fibre flag starts at `⊥`. -/
@[simp] theorem fibFlag_zero (P : Matrix (Fin n) (Fin n) (PowerSeries K)) :
    fibFlag P 0 = ⊥ := by
  rw [fibFlag, Isotropy.kerFlag_zero]
  simp

/-- **The member at the point lowers the fibre flag**: `P S_{k+1} ⊆ S_k` over
`R`, and reduction modulo `u` is linear.  This is what makes
`lem:local-model`(1) — a frame in which the member is block strict — a
consequence of a frame adapted to `V_•`. -/
theorem matC_mulVec_mem_fibFlag {P : Matrix (Fin n) (Fin n) (PowerSeries K)} {k : ℕ}
    {v : Fin n → K} (hv : v ∈ fibFlag P (k + 1)) :
    matC P *ᵥ v ∈ fibFlag P k := by
  obtain ⟨w, hw, rfl⟩ := mem_fibFlag.1 hv
  refine mem_fibFlag.2 ⟨P *ᵥ w, ?_, Height.Orbital.vecC_mulVec P w⟩
  rw [Isotropy.mem_kerFlag] at hw ⊢
  rw [Matrix.mulVec_mulVec, ← pow_succ]
  exact hw

/-- The integral kernel flag is saturated: `R` is a domain, so a scalar
multiple of a vector lies in `ker (P^k)` only if the vector does. -/
theorem kerFlag_saturated (P : Matrix (Fin n) (Fin n) (PowerSeries K)) (k : ℕ)
    {f : PowerSeries K} (hf : f ≠ 0) {w : Fin n → PowerSeries K}
    (h : f • w ∈ Isotropy.kerFlag P k) : w ∈ Isotropy.kerFlag P k := by
  rw [Isotropy.mem_kerFlag] at h ⊢
  rw [Matrix.mulVec_smul] at h
  funext i
  have := congrFun h i
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
  exact (mul_eq_zero.mp this).resolve_left hf

/-- **The fibre flag has the rank of the integral kernel flag.**  The case
`R = K⟦u⟧`, `ρ = constantCoeff`, `π = u` of `Isotropy.finrank_map_kerFlag`: a
basis of `S_k = ker(P^k) ⊆ Rⁿ` reduces to a basis of `V_k = S_k(x)`, because
`S_k` is saturated. -/
theorem finrank_fibFlag (P : Matrix (Fin n) (Fin n) (PowerSeries K)) (k : ℕ) :
    Module.finrank K (fibFlag P k)
      = Module.finrank (PowerSeries K) (Isotropy.kerFlag P k) := by
  have hρ : ∀ c : K, (PowerSeries.constantCoeff (R := K)) (algebraMap K (PowerSeries K) c) = c :=
    fun c => by simp [PowerSeries.algebraMap_eq]
  have hvec : (Isotropy.redVec (n := n) (PowerSeries.constantCoeff (R := K)) hρ) = vecCL := by
    ext w i
    rfl
  rw [fibFlag, ← hvec]
  exact Isotropy.finrank_map_kerFlag _ hρ PowerSeries.X PowerSeries.X_ne_zero
    (fun r => PowerSeries.X_dvd_iff.symm) P k


/-- **The fibre flag has the dimension of the generic kernel.**  `finrank_fibFlag`
says `dim V_k` is the rank of the integral flag `S_k`, and
`Isotropy.finrank_kerFlag_toK` says that rank does not change on passing to the
fraction field `K⸨u⸩`.  So `dim V_k = n − rk_{K⸨u⸩} P^k`, the *generic* jump of
the pencil — never the jump `dim ker (P(x)^k)` at the point, which is larger
exactly when the type drops there. -/
theorem finrank_fibFlag_eq_generic {L : Type*} [Field L] [Algebra (PowerSeries K) L]
    [IsFractionRing (PowerSeries K) L] (P : Matrix (Fin n) (Fin n) (PowerSeries K)) (k : ℕ) :
    Module.finrank K (fibFlag P k)
      = Module.finrank L (Isotropy.kerFlag (Isotropy.toK L P) k) := by
  rw [finrank_fibFlag, Isotropy.finrank_kerFlag_toK]
/-- The reduction `K[u] → K` at `u = 0`, entrywise. -/
noncomputable def polyRed : (Fin n → Polynomial K) →ₗ[K] (Fin n → K) :=
  Isotropy.redVec (Polynomial.evalRingHom (0 : K)) (fun c => by simp)

/-- **The fibre flag is the reduction of the *polynomial* kernel flag.**  A
matrix polynomial in `u` has, for every vector of its kernel over `K⟦u⟧`, a
kernel vector over `K[u]` with the same value at `u = 0`.

This is a dimension count, not a structure theorem: the reduction of the
polynomial kernel flag is contained in the fibre flag, and both have dimension
`n − rk P^k`, computed over `K(u)` and over `K⸨u⸩` respectively — the same
number, because a maximal nonzero minor of `P^k` over `K[u]`
(`Orbital.exists_genericRank` at `⊥`) survives in both. -/
theorem fibFlag_eq_map_polyKerFlag (A : Matrix (Fin n) (Fin n) (Polynomial K)) (m : ℕ) :
    fibFlag (A.map Polynomial.coeToPowerSeries.ringHom) m
      = Submodule.map (polyRed (K := K) (n := n))
          (Submodule.restrictScalars K (Isotropy.kerFlag A m)) := by
  classical
  set ι : Polynomial K →+* PowerSeries K := Polynomial.coeToPowerSeries.ringHom with hι
  set P : Matrix (Fin n) (Fin n) (PowerSeries K) := A.map ι with hP
  -- the inclusion
  have hle : Submodule.map (polyRed (K := K) (n := n))
      (Submodule.restrictScalars K (Isotropy.kerFlag A m)) ≤ fibFlag P m := by
    rintro _ ⟨w, hw, rfl⟩
    have hwk : w ∈ Isotropy.kerFlag A m := hw
    refine mem_fibFlag.2 ⟨fun i => ι (w i), ?_, ?_⟩
    · rw [Isotropy.mem_kerFlag] at hwk ⊢
      have h1 : (P ^ m) *ᵥ (fun i => ι (w i)) = fun i => ι (((A ^ m) *ᵥ w) i) := by
        funext i
        show ∑ j, (P ^ m) i j * ι (w j) = ι (∑ j, (A ^ m) i j * w j)
        rw [map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_mul]
        congr 1
        show (P ^ m) i j = ι ((A ^ m) i j)
        rw [hP, show A.map ι = ι.mapMatrix A from rfl, ← map_pow]
        rfl
      rw [h1, hwk]
      funext i
      simp
    · funext i
      show PowerSeries.constantCoeff (ι (w i)) = Polynomial.eval 0 (w i)
      rw [hι]
      show PowerSeries.constantCoeff (Polynomial.coeToPowerSeries.ringHom (w i)) = _
      rw [Polynomial.coeToPowerSeries.ringHom_apply,
        ← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe,
        Polynomial.coeff_zero_eq_eval_zero]
  -- the dimensions agree
  refine (Submodule.eq_of_le_of_finrank_le hle ?_).symm
  -- the generic rank of `A^m`
  obtain ⟨r, δ, hδ, hrank⟩ := Height.Orbital.exists_genericRank (⊥ : Ideal (Polynomial K)) (A ^ m)
  have hδ0 : δ ≠ 0 := fun h => hδ (by rw [h]; exact Ideal.zero_mem _)
  have hkill : ∀ f ∈ (⊥ : Ideal (Polynomial K)), (algebraMap (Polynomial K)
      (FractionRing (Polynomial K))) f = 0 := by
    intro f hf
    rw [Ideal.mem_bot.1 hf, map_zero]
  have hpoly : Matrix.rank ((A ^ m).map (algebraMap (Polynomial K)
      (FractionRing (Polynomial K)))) = r :=
    hrank _ _ hkill
      ((map_ne_zero_iff _ (IsFractionRing.injective (Polynomial K)
        (FractionRing (Polynomial K)))).mpr hδ0)
  have hser : Matrix.rank ((A ^ m).map (((algebraMap (PowerSeries K)
      (FractionRing (PowerSeries K)))).comp ι)) = r := by
    refine hrank _ _ (fun f hf => by rw [Ideal.mem_bot.1 hf, map_zero]) ?_
    have hinjι : Function.Injective ι := by
      intro p q hpq
      exact Polynomial.coe_injective K (by simpa [hι] using hpq)
    have hcomp : Function.Injective
        (((algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))).comp ι) :=
      (IsFractionRing.injective (PowerSeries K) (FractionRing (PowerSeries K))).comp hinjι
    exact (map_ne_zero_iff _ hcomp).mpr hδ0
  simp only [Matrix.rank] at hpoly hser
  -- the polynomial side
  have hdimpoly : Module.finrank K (Submodule.map (polyRed (K := K) (n := n))
      (Submodule.restrictScalars K (Isotropy.kerFlag A m)))
      = Module.finrank (Polynomial K) (Isotropy.kerFlag A m) :=
    Isotropy.finrank_map_kerFlag _ _ Polynomial.X Polynomial.X_ne_zero
      (fun r => by
        show Polynomial.eval 0 r = 0 ↔ _
        rw [← Polynomial.coeff_zero_eq_eval_zero]
        exact Polynomial.X_dvd_iff.symm) A m
  have hpolyF : Module.finrank (Polynomial K) (Isotropy.kerFlag A m)
      = Module.finrank (FractionRing (Polynomial K))
          (Isotropy.kerFlag (Isotropy.toK (FractionRing (Polynomial K)) A) m) :=
    (Isotropy.finrank_kerFlag_toK A m).symm
  have hrk1 : Module.finrank (FractionRing (Polynomial K))
      (Isotropy.kerFlag (Isotropy.toK (FractionRing (Polynomial K)) A) m) + r = n := by
    have hker : Isotropy.kerFlag (Isotropy.toK (FractionRing (Polynomial K)) A) m
        = LinearMap.ker (((A ^ m).map (algebraMap (Polynomial K)
            (FractionRing (Polynomial K)))).mulVecLin) := by
      rw [Isotropy.kerFlag, ← Isotropy.toK_pow]
    have h3 := LinearMap.finrank_range_add_finrank_ker
      (((A ^ m).map (algebraMap (Polynomial K) (FractionRing (Polynomial K)))).mulVecLin)
    rw [show Module.finrank (FractionRing (Polynomial K))
      (Fin n → FractionRing (Polynomial K)) = n by simp] at h3
    rw [hker]
    omega
  -- the power-series side
  have hdimser : Module.finrank K (fibFlag P m)
      = Module.finrank (PowerSeries K) (Isotropy.kerFlag P m) := finrank_fibFlag P m
  have hserF : Module.finrank (PowerSeries K) (Isotropy.kerFlag P m)
      = Module.finrank (FractionRing (PowerSeries K))
          (Isotropy.kerFlag (Isotropy.toK (FractionRing (PowerSeries K)) P) m) :=
    (Isotropy.finrank_kerFlag_toK P m).symm
  have hrk2 : Module.finrank (FractionRing (PowerSeries K))
      (Isotropy.kerFlag (Isotropy.toK (FractionRing (PowerSeries K)) P) m) + r = n := by
    have hker : Isotropy.kerFlag (Isotropy.toK (FractionRing (PowerSeries K)) P) m
        = LinearMap.ker (((A ^ m).map (((algebraMap (PowerSeries K)
            (FractionRing (PowerSeries K)))).comp ι)).mulVecLin) := by
      rw [Isotropy.kerFlag, ← Isotropy.toK_pow]
      congr 2
      rw [hP, show A.map ι = ι.mapMatrix A from rfl, ← map_pow]
      rfl
    have h3 := LinearMap.finrank_range_add_finrank_ker
      (((A ^ m).map (((algebraMap (PowerSeries K)
        (FractionRing (PowerSeries K)))).comp ι)).mulVecLin)
    rw [show Module.finrank (FractionRing (PowerSeries K))
      (Fin n → FractionRing (PowerSeries K)) = n by simp] at h3
    rw [hker]
    omega
  omega


/-- The pencil in the chart at `t₀` as a matrix of *polynomials* in `u`: the
family `(N + t₀M) + u M`, which is what `Pat N M t₀` is. -/
noncomputable def PatP (N M : Matrix (Fin n) (Fin n) K) (t₀ : K) :
    Matrix (Fin n) (Fin n) (Polynomial K) :=
  Matrix.of fun i j => Polynomial.C ((N + t₀ • M) i j) + Polynomial.X * Polynomial.C (M i j)

theorem Pat_eq_map_PatP (N M : Matrix (Fin n) (Fin n) K) (t₀ : K) :
    Pat N M t₀ = (PatP N M t₀).map Polynomial.coeToPowerSeries.ringHom := by
  refine Matrix.ext fun i j => ?_
  show atPoint t₀ (pencil N M i j) = Polynomial.coeToPowerSeries.ringHom (PatP N M t₀ i j)
  rw [show pencil N M i j
      = MvPolynomial.C (N i j) * Graded.mu + MvPolynomial.C (M i j) * Graded.nu from rfl,
    map_add, map_mul, map_mul, atPoint_mu, atPoint_nu, atPoint_C, atPoint_C]
  show PowerSeries.C (N i j) * 1
      + PowerSeries.C (M i j) * (PowerSeries.C t₀ + PowerSeries.X)
    = Polynomial.coeToPowerSeries.ringHom
        (Polynomial.C ((N + t₀ • M) i j) + Polynomial.X * Polynomial.C (M i j))
  rw [map_add, map_mul]
  rw [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coeToPowerSeries.ringHom_apply,
    Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C, Polynomial.coe_X,
    Polynomial.coe_C]
  show PowerSeries.C (N i j) * 1 + PowerSeries.C (M i j) * (PowerSeries.C t₀ + PowerSeries.X)
    = PowerSeries.C (N i j + t₀ * M i j) + PowerSeries.X * PowerSeries.C (M i j)
  rw [map_add, map_mul]
  ring

/-- **The fibre flag of the pencil is the reduction of its polynomial kernel
flag**: every vector of `V_k` is the value at `u = 0` of a kernel vector of
`(N + (t₀+u)M)^k` with polynomial entries.  This is what makes the lifts of an
adapted frame's columns polynomial in `u`, hence specialisable. -/
theorem fibFlag_Pat_eq_map_polyKerFlag (N M : Matrix (Fin n) (Fin n) K) (t₀ : K) (m : ℕ) :
    fibFlag (Pat N M t₀) m
      = Submodule.map (polyRed (K := K) (n := n))
          (Submodule.restrictScalars K (Isotropy.kerFlag (PatP N M t₀) m)) := by
  rw [Pat_eq_map_PatP]
  exact fibFlag_eq_map_polyKerFlag _ m



/-- `V_k ⊗ R`, the `R`-span of the constant vectors of a `K`-subspace. -/
noncomputable def constSpan (W : Submodule K (Fin n → K)) :
    Submodule (PowerSeries K) (Fin n → PowerSeries K) :=
  Submodule.span (PowerSeries K) (constVec '' (W : Set (Fin n → K)))

theorem constVec_mem_constSpan {W : Submodule K (Fin n → K)} {v : Fin n → K} (hv : v ∈ W) :
    constVec v ∈ constSpan W :=
  Submodule.subset_span ⟨v, hv, rfl⟩

theorem constSpan_le_iff {W : Submodule K (Fin n → K)}
    {N : Submodule (PowerSeries K) (Fin n → PowerSeries K)} :
    constSpan W ≤ N ↔ ∀ v ∈ W, constVec v ∈ N := by
  rw [constSpan, Submodule.span_le]
  constructor
  · intro h v hv
    exact h ⟨v, hv, rfl⟩
  · rintro h _ ⟨v, hv, rfl⟩
    exact h v hv

end Fibre

/-! ### The adapted section and the trivialisation `h` -/

section Adapted

variable {K : Type u} [Field K] {n : ℕ}

/-- A `K`-linear map `K^n → R^n`, defined on all of `K^n`, which lifts the
fibre `V_k` into the integral kernel flag `S_k`. -/
private theorem exists_flag_section (P : Matrix (Fin n) (Fin n) (PowerSeries K)) (k : ℕ) :
    ∃ ρ : (Fin n → K) →ₗ[K] (Fin n → PowerSeries K),
      ∀ v ∈ fibFlag P k, ρ v ∈ Isotropy.kerFlag P k ∧ vecC (ρ v) = v := by
  classical
  obtain ⟨q, hq⟩ := Submodule.exists_isCompl (fibFlag P k)
  set b := Module.finBasis K (fibFlag P k) with hb
  have hex : ∀ i, ∃ w : Fin n → PowerSeries K,
      w ∈ Isotropy.kerFlag P k ∧ vecC w = ((b i : Fin n → K)) := fun i => mem_fibFlag.1 (b i).2
  choose w hw1 hw2 using hex
  refine ⟨(b.constr K w).comp ((fibFlag P k).projectionOnto q hq), fun v hv => ?_⟩
  have hproj : (fibFlag P k).projectionOnto q hq v = ⟨v, hv⟩ :=
    Submodule.projectionOnto_apply_of_mem_left hq hv
  have hval : ((b.constr K w).comp ((fibFlag P k).projectionOnto q hq)) v
      = ∑ i, b.equivFun ⟨v, hv⟩ i • w i := by
    show (b.constr K w) ((fibFlag P k).projectionOnto q hq v) = _
    rw [hproj, Module.Basis.constr_apply_fintype]
  refine ⟨?_, ?_⟩
  · rw [hval]
    have : (∑ i, b.equivFun ⟨v, hv⟩ i • w i) ∈
        Submodule.restrictScalars K (Isotropy.kerFlag P k) :=
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hw1 i)
    exact this
  · rw [hval]
    have hsum : vecCL (∑ i, b.equivFun ⟨v, hv⟩ i • w i)
        = ∑ i, b.equivFun ⟨v, hv⟩ i • (b i : Fin n → K) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_smul, vecCL_apply, hw2 i]
    have hv' : (∑ i, b.equivFun ⟨v, hv⟩ i • (b i : Fin n → K)) = v := by
      have h1 : (fibFlag P k).subtype (∑ i, b.equivFun ⟨v, hv⟩ i • b i)
          = ∑ i, b.equivFun ⟨v, hv⟩ i • ((fibFlag P k).subtype (b i)) := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun i _ => map_smul _ _ _
      rw [Module.Basis.sum_equivFun] at h1
      exact h1.symm
    show vecCL (∑ i, b.equivFun ⟨v, hv⟩ i • w i) = v
    rw [hsum, hv']

/-- `lem:local-model`(1), section form: a `K`-linear section `σ` of the
reduction `R^n → K^n` which carries every fibre `V_k` into `S_k`.  This is
the adapted basis of the paper: `σ` sends the standard flag of `K^n`
refined by `V_•` to a basis of `R^n` adapted to `S_•`. -/
theorem exists_adapted_section (P : Matrix (Fin n) (Fin n) (PowerSeries K)) (hP : P ^ n = 0) :
    ∃ σ : (Fin n → K) →ₗ[K] (Fin n → PowerSeries K),
      (∀ v, vecC (σ v) = v) ∧ ∀ k, ∀ v ∈ fibFlag P k, σ v ∈ Isotropy.kerFlag P k := by
  classical
  -- the induction: a section over `V_k` respecting all the levels `j ≤ k`
  have main : ∀ k : ℕ, ∃ σ : (Fin n → K) →ₗ[K] (Fin n → PowerSeries K),
      (∀ v ∈ fibFlag P k, vecC (σ v) = v) ∧
        ∀ j ≤ k, ∀ v ∈ fibFlag P j, σ v ∈ Isotropy.kerFlag P j := by
    intro k
    induction k with
    | zero =>
        refine ⟨0, ?_, ?_⟩
        · intro v hv
          have h0 : fibFlag P 0 = ⊥ := by
            rw [fibFlag, Isotropy.kerFlag_zero]
            simp
          rw [h0] at hv
          rw [Submodule.mem_bot] at hv
          subst hv
          funext i
          simp [vecC]
        · intro j hj v hv
          obtain rfl : j = 0 := Nat.le_zero.mp hj
          have h0 : fibFlag P 0 = ⊥ := by
            rw [fibFlag, Isotropy.kerFlag_zero]
            simp
          rw [h0, Submodule.mem_bot] at hv
          subst hv
          simp
    | succ k ih =>
        obtain ⟨σ', hσ'C, hσ'S⟩ := ih
        obtain ⟨ρ, hρ⟩ := exists_flag_section P (k + 1)
        obtain ⟨qk, hqk⟩ := Submodule.exists_isCompl (fibFlag P k)
        obtain ⟨qk1, hqk1⟩ := Submodule.exists_isCompl (fibFlag P (k + 1))
        set πk : (Fin n → K) →ₗ[K] (Fin n → K) := (fibFlag P k).projection qk hqk with hπk
        set πk1 : (Fin n → K) →ₗ[K] (Fin n → K) :=
          (fibFlag P (k + 1)).projection qk1 hqk1 with hπk1
        have hπk_mem : ∀ v, πk v ∈ fibFlag P k := fun v => Submodule.projection_apply_mem hqk v
        have hπk1_mem : ∀ v, πk1 v ∈ fibFlag P (k + 1) := fun v =>
          Submodule.projection_apply_mem hqk1 v
        have hπk_id : ∀ v ∈ fibFlag P k, πk v = v := fun v hv =>
          Submodule.projection_apply_left hqk ⟨v, hv⟩
        have hπk1_id : ∀ v ∈ fibFlag P (k + 1), πk1 v = v := fun v hv =>
          Submodule.projection_apply_left hqk1 ⟨v, hv⟩
        have hσ'C' : ∀ v ∈ fibFlag P k, vecCL (σ' v) = v := hσ'C
        have hargmem : ∀ v : Fin n → K,
            (πk1 - vecCL.comp (σ'.comp πk)) v ∈ fibFlag P (k + 1) := by
          intro v
          have h1 : vecCL (σ' (πk v)) = πk v := hσ'C' _ (hπk_mem v)
          show πk1 v - vecCL (σ' (πk v)) ∈ fibFlag P (k + 1)
          rw [h1]
          exact Submodule.sub_mem _ (hπk1_mem v)
            (fibFlag_mono P (Nat.le_succ k) (hπk_mem v))
        refine ⟨σ'.comp πk + ρ.comp (πk1 - vecCL.comp (σ'.comp πk)), ?_, ?_⟩
        · -- the section property at level `k + 1`
          intro v hv
          have h2 : vecCL (ρ ((πk1 - vecCL.comp (σ'.comp πk)) v))
              = (πk1 - vecCL.comp (σ'.comp πk)) v := (hρ _ (hargmem v)).2
          have h3 : vecCL ((σ'.comp πk + ρ.comp (πk1 - vecCL.comp (σ'.comp πk))) v)
              = vecCL (σ' (πk v)) + vecCL (ρ ((πk1 - vecCL.comp (σ'.comp πk)) v)) :=
            map_add vecCL _ _
          show vecCL ((σ'.comp πk + ρ.comp (πk1 - vecCL.comp (σ'.comp πk))) v) = v
          rw [h3, h2]
          show vecCL (σ' (πk v)) + (πk1 v - vecCL (σ' (πk v))) = v
          rw [hσ'C' _ (hπk_mem v), hπk1_id v hv]
          abel
        · -- the flag property at every level `j ≤ k + 1`
          intro j hj v hv
          rcases Nat.lt_or_ge j (k + 1) with hjk | hjk
          · -- levels `j ≤ k`: the correction vanishes
            have hjk' : j ≤ k := by omega
            have hvk : v ∈ fibFlag P k := fibFlag_mono P hjk' hv
            have hvk1 : v ∈ fibFlag P (k + 1) := fibFlag_mono P (by omega) hv
            have harg : (πk1 - vecCL.comp (σ'.comp πk)) v = 0 := by
              show πk1 v - vecCL (σ' (πk v)) = 0
              rw [hπk_id v hvk, hσ'C' v hvk, hπk1_id v hvk1, sub_self]
            show σ' (πk v) + ρ ((πk1 - vecCL.comp (σ'.comp πk)) v) ∈ Isotropy.kerFlag P j
            rw [harg, map_zero, add_zero, hπk_id v hvk]
            exact hσ'S j hjk' v hv
          · -- level `k + 1`
            obtain rfl : j = k + 1 := by omega
            show σ' (πk v) + ρ ((πk1 - vecCL.comp (σ'.comp πk)) v) ∈ Isotropy.kerFlag P (k + 1)
            exact Submodule.add_mem _
              (Isotropy.kerFlag_mono P (Nat.le_succ k) (hσ'S k le_rfl _ (hπk_mem v)))
              (hρ _ (hargmem v)).1
  obtain ⟨σ, hσC, hσS⟩ := main n
  have htop : fibFlag P n = ⊤ := fibFlag_eq_top P hP
  refine ⟨σ, fun v => hσC v (by rw [htop]; trivial), fun k v hv => ?_⟩
  rcases Nat.lt_or_ge k n with hk | hk
  · exact hσS k (le_of_lt hk) v hv
  · exact Isotropy.kerFlag_mono P hk (hσS n le_rfl v (by rw [htop]; trivial))

/-- The matrix of a `K`-linear map `K^n → R^n`: its columns are the images of
the standard basis. -/
noncomputable def sectionMat (σ : (Fin n → K) →ₗ[K] (Fin n → PowerSeries K)) :
    Matrix (Fin n) (Fin n) (PowerSeries K) :=
  Matrix.of fun i j => σ (Pi.single j 1) i

theorem sectionMat_mulVec (σ : (Fin n → K) →ₗ[K] (Fin n → PowerSeries K)) (v : Fin n → K) :
    sectionMat σ *ᵥ constVec v = σ v := by
  classical
  have hv : v = ∑ j, v j • (Pi.single j 1 : Fin n → K) := by
    funext i
    rw [Finset.sum_apply]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [Ne.symm hj]
    · intro h
      exact absurd (Finset.mem_univ i) h
  funext i
  show ∑ j, sectionMat σ i j * PowerSeries.C (v j) = σ v i
  conv_rhs => rw [hv]
  rw [map_sum]
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  show σ (Pi.single j 1) i * PowerSeries.C (v j) = v j • σ (Pi.single j 1) i
  rw [PowerSeries.smul_eq_C_mul, mul_comm]

theorem matC_sectionMat (σ : (Fin n → K) →ₗ[K] (Fin n → PowerSeries K))
    (hσ : ∀ v, vecC (σ v) = v) : matC (sectionMat σ) = 1 := by
  ext i j
  show PowerSeries.constantCoeff (σ (Pi.single j 1) i) = _
  have h : vecC (σ (Pi.single j 1)) = Pi.single j 1 := hσ _
  have hij : PowerSeries.constantCoeff (σ (Pi.single j 1) i) = (Pi.single j 1 : Fin n → K) i :=
    congrFun h i
  rw [hij, Matrix.one_apply, Pi.single_apply]

/-- A matrix over `R` with `h(x) = 1` is invertible. -/
theorem isUnit_det_of_matC_eq_one {h : Matrix (Fin n) (Fin n) (PowerSeries K)}
    (hC : matC h = 1) : IsUnit h.det := by
  rw [PowerSeries.isUnit_iff_constantCoeff]
  have hdet : PowerSeries.constantCoeff h.det = (matC h).det := by
    show PowerSeries.constantCoeff h.det = (h.map PowerSeries.constantCoeff).det
    rw [RingHom.map_det]
    rfl
  rw [hdet, hC, Matrix.det_one]
  exact isUnit_one

/-- `lem:local-model`(1): the adapted trivialisation at the point.  `h` is
invertible over `R = K⟦u⟧`, reduces to the identity at the point, and carries
the constant flag `V_• ⊗ R` onto the integral kernel flag `S_•`.

Surjectivity onto `S_k` is Nakayama's lemma: `S_k` is finitely generated, `u`
generates the maximal ideal of the local ring `R`, and every `w ∈ S_k` differs
from the lift `σ(w(x))` of its value by a multiple of `u` which is again in
`S_k` because the flag is saturated. -/
theorem exists_adapted_trivialisation (P : Matrix (Fin n) (Fin n) (PowerSeries K))
    (hP : P ^ n = 0) :
    ∃ h : Matrix (Fin n) (Fin n) (PowerSeries K), IsUnit h.det ∧ matC h = 1 ∧
      ∀ k, Submodule.map h.mulVecLin (constSpan (fibFlag P k)) = Isotropy.kerFlag P k := by
  obtain ⟨σ, hσC, hσS⟩ := exists_adapted_section P hP
  have hmul : ∀ v : Fin n → K, (sectionMat σ).mulVecLin (constVec v) = σ v := fun v => by
    rw [Matrix.mulVecLin_apply, sectionMat_mulVec]
  refine ⟨sectionMat σ, isUnit_det_of_matC_eq_one (matC_sectionMat σ hσC),
    matC_sectionMat σ hσC, fun k => ?_⟩
  have hle : Submodule.map (sectionMat σ).mulVecLin (constSpan (fibFlag P k))
      ≤ Isotropy.kerFlag P k := by
    rw [Submodule.map_le_iff_le_comap, constSpan_le_iff]
    intro v hv
    show (sectionMat σ).mulVecLin (constVec v) ∈ Isotropy.kerFlag P k
    rw [hmul]
    exact hσS k v hv
  refine le_antisymm hle ?_
  -- Nakayama
  have hFG : (Isotropy.kerFlag P k).FG := IsNoetherian.noetherian _
  have hjac : (Ideal.span {PowerSeries.X} : Ideal (PowerSeries K))
      ≤ (⊥ : Ideal (PowerSeries K)).jacobson := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal (PowerSeries K)) bot_ne_top,
      PowerSeries.maximalIdeal_eq_span_X]
  refine Submodule.le_of_le_smul_of_le_jacobson_bot hFG hjac ?_
  intro w hw
  have hvV : vecC w ∈ fibFlag P k := vecC_mem_fibFlag hw
  have hσv : σ (vecC w) ∈ Isotropy.kerFlag P k := hσS k _ hvV
  have hmap : σ (vecC w) ∈ Submodule.map (sectionMat σ).mulVecLin (constSpan (fibFlag P k)) :=
    ⟨constVec (vecC w), constVec_mem_constSpan hvV, hmul _⟩
  have hzero : ∀ i, PowerSeries.constantCoeff ((w - σ (vecC w)) i) = 0 := by
    intro i
    have h1 : PowerSeries.constantCoeff (σ (vecC w) i) = vecC w i := congrFun (hσC (vecC w)) i
    show PowerSeries.constantCoeff (w i - σ (vecC w) i) = 0
    rw [map_sub, h1]
    exact sub_self _
  have hdvd : ∀ i, (PowerSeries.X : PowerSeries K) ∣ (w - σ (vecC w)) i := fun i =>
    PowerSeries.X_dvd_iff.2 (hzero i)
  choose w' hw' using hdvd
  have hw'eq : w - σ (vecC w) = (PowerSeries.X : PowerSeries K) • w' := by
    funext i
    rw [Pi.smul_apply, smul_eq_mul, ← hw' i]
  have hw'mem : w' ∈ Isotropy.kerFlag P k := by
    refine kerFlag_saturated P k PowerSeries.X_ne_zero ?_
    rw [← hw'eq]
    exact Submodule.sub_mem _ hw hσv
  have hsplit : w = σ (vecC w) + (PowerSeries.X : PowerSeries K) • w' := by
    rw [← hw'eq]
    abel
  rw [hsplit]
  exact Submodule.add_mem _ (Submodule.mem_sup_left hmap)
    (Submodule.mem_sup_right
      (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hw'mem))

/-! ### The velocity decomposition (`lem:local-model`(3)) -/

/-- `U` lowers the integral kernel flag of `P`: the integral form of
`n_{V_•} ⊗ R`. -/
def Lowering (P U : Matrix (Fin n) (Fin n) (PowerSeries K)) : Prop :=
  ∀ k, ∀ v ∈ Isotropy.kerFlag P (k + 1), U *ᵥ v ∈ Isotropy.kerFlag P k

/-- **`lem:local-model`(3)**: a direction which is kernel flat *over `R`*
decomposes as `X = [P, W] + U` with `W` integral and `U` lowering the kernel
flag.  This is the regular part of `lem:field-commutator` (`Isotropy`'s
`exists_regular_g`, valid over any principal ideal domain) followed by the
lowering step.

The hypothesis `Isotropy.DCond P X` — `D_k(X)(S_k) ⊆ P^k R^n` for every `k` —
is `lem:flag-flat`(1) localised at the point; see the module docstring for why
the function-field form proved in `Pencil/Arcs.lean` does not suffice. -/
theorem exists_velocity_decomposition (P X : Matrix (Fin n) (Fin n) (PowerSeries K))
    (hP : P ^ n = 0) (hD : Isotropy.DCond P X) :
    ∃ W U : Matrix (Fin n) (Fin n) (PowerSeries K),
      X = (P * W - W * P) + U ∧ Lowering P U := by
  obtain ⟨g, hg⟩ := Isotropy.exists_regular_g P X hP hD
  refine ⟨g, X - (P * g - g * P), by abel, ?_⟩
  refine Isotropy.lowering_of_dpow_vanishing ?_
  intro k v hv
  have h1 : Isotropy.dpow P (X - (P * g - g * P)) k
      = Isotropy.dpow P X k - (P ^ k * g - g * P ^ k) := by
    rw [Isotropy.dpow_sub, Isotropy.dpow_commutator]
  have hv0 : (P ^ k).mulVec v = 0 := Isotropy.mem_kerFlag.mp hv
  rw [h1, Matrix.sub_mulVec, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    hv0, Matrix.mulVec_zero, hg k v hv, sub_zero, sub_self]

end Adapted

end Height.Pencil
