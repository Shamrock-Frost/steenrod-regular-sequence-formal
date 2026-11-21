import Mathlib.RingTheory.PowerSeries.Derivative
import Height.Pencil.LocalModel
import Height.Pencil.FlagVelocity
import Height.DVR.ShiftedPowerSeries

/-!
# `lem:flag-velocity`: flag velocities compute `Ω_x`

The paper, `lem:flag-velocity`.

Let `x = t₀` be a point of the chart, `P₀ = Pat N M t₀` the pencil there,
`N₀ = P₀(x) = N + t₀ M` its value, and let `(Q̇_i, ṫ_i)` be marked at `x` with
witnesses `Z_i` (`Pencil/Marked.lean`).  Suppose the shifted representatives
`Ṙ_i = Rdot N M t₀ Q̇_i ṫ_i Z_i` decompose as in `lem:local-model`(3),

```
Ṙ_i = [P₀, W_i] + U_i ,      W_i ∈ gl_n(R),  U_i lowering the flag S_• ,
```

(`Pencil/LocalModel.lean`, `exists_velocity_decomposition`; in the paper's
trivialised form `U_i` is replaced by `h U_i h⁻¹`, which does not change the
value at the point since `h(x) = 1`).  Then

* `[N₀, W_i(x)] + U_i(x) = 0` — evaluate `Ṙ_i(x) = 0` (`matC_Rdot`);
* `Ω_x(μ_x(Q̇_1, ṫ_1), μ_x(Q̇_2, ṫ_2)) = trace([N₀, W_1(x)] W_2(x))
   = ω^{KK}_{N₀}(W_1(x), W_2(x))`, the Kostant–Kirillov pairing of the fibre
  motions `Ẏ_i := U_i(x) = [W_i(x), N₀]`.

The computation is the paper's: choose `B₁ ∈ p` with `[P₀, B₁] = U₁` over
`K_x` (`lem:parabolic-field`(ii), `Pencil/Parabolic.lean` `nilrad_eq_image`,
applied to `P₀` over `K_x` — whose kernel flag is the `h`-conjugate of
`V_• ⊗ K_x`, so `U_i` lands in its nilradical, `toK_mem_nilrad`), put
`A₁ := W₁ + B₁`, so that `[P₀, A₁] = Ṙ₁`, and expand

```
trace(A₁ Ṙ₂) = trace(W₁ Ṙ₂) − trace(U₁ W₂) ,
```
using `trace(B₁ [P₀, W₂]) = −trace([P₀, B₁] W₂)` and
`trace(p · n_{V_•}) = 0` (`trace_parab_nilrad`).  The right-hand side is
*integral*, so `cor:shifted-eval` evaluates the pairing as its value at `x`
(`Height.DVR.constantCoeff_eq_residue`), and `Ṙ₂(x) = 0` kills the first
term.

## Kernel flatness over `K⟦u⟧`

`dcond_add`, `dcond_smul`, `dcond_sub`, `dcond_commutator` and `dcond_dPat`
assemble `Isotropy.DCond P (Ṙ)` from `Isotropy.DCond P` of the *pencil
velocity* alone (`dcond_Rdot`).  `exists_velocity_decomposition` gives
`Isotropy.DCond` from the decomposition of `lem:local-model`(3); the converse,
which would make the two equivalent rather than one-directional, is not proved
in the tree.  `dcond_dPat` is the paper's "for `∂P`,
apply `∂_u` to `P = h P̃ h⁻¹`", done directly: a kernel vector `v` of `P^k`
has `0 = ∂_u(P^k v) = D_k(∂_u P) v + P^k (∂_u v)`.

## `cor:shifted-eval`

`cor:shifted-eval` — `Ω_x(μ_x, μ_x) = res_x u⁻¹ trace(A₁ Ṙ₂)` — is
`Pencil/Marked.lean`'s `OmegaX_muX_eq_residue`, which needs transporters
`A₁, A₂` over `K⸨u⸩` for *both* marked directions (the second is
`cor:arc-torsion`).  `flag_velocity_of_decomposition` produces both from the
decompositions of `lem:local-model`(3) through `nilrad_eq_image`; the
one-transporter form is false (see the docstring there).
-/

namespace Height.Pencil

open Matrix Height.Orbital Height.DVR

universe u

section Trace

variable {K : Type u} [Field K] {n : ℕ}

/-- Reduction at the point commutes with the trace. -/
theorem constantCoeff_trace (X : Matrix (Fin n) (Fin n) (PowerSeries K)) :
    PowerSeries.constantCoeff (trace X) = trace (matC X) := by
  simp only [Matrix.trace, Matrix.diag, map_sum, matC, Matrix.map_apply]

/-- `trace(B [P, W]) = − trace([P, B] W)`. -/
theorem trace_mul_commutator {S : Type*} [CommRing S] (P B W : Matrix (Fin n) (Fin n) S) :
    trace (B * (P * W - W * P)) = -trace ((P * B - B * P) * W) := by
  rw [mul_sub, trace_sub, sub_mul, trace_sub, neg_sub,
    show B * (W * P) = B * W * P by rw [mul_assoc], trace_mul_comm (B * W) P,
    show P * (B * W) = P * B * W by rw [mul_assoc],
    show B * (P * W) = B * P * W by rw [mul_assoc]]

end Trace

section Nilrad

variable {K : Type u} [Field K] {n : ℕ}

/-- A matrix lowering the integral kernel flag lowers the kernel flag over the
fraction field: `n_{V_•} ⊗ R ⊆ n` for `P` over `K_x`.  The kernel flag over
`K_x` is spanned by the integral one (`Isotropy.exists_integral_kernel_vector`). -/
theorem toK_mem_nilrad {P U : Matrix (Fin n) (Fin n) (PowerSeries K)} (hU : Lowering P U) :
    Isotropy.toK (LaurentSeries K) U ∈ nilrad (Isotropy.toK (LaurentSeries K) P) := by
  intro k v hv
  obtain ⟨d, w, hd, hw, hwv⟩ :=
    Isotropy.exists_integral_kernel_vector (R := PowerSeries K) (K := LaurentSeries K) hv
  have hUw : U *ᵥ w ∈ Isotropy.kerFlag P k := hU k w hw
  have hmem : Isotropy.toKv (LaurentSeries K) (U *ᵥ w) ∈
      Isotropy.kerFlag (Isotropy.toK (LaurentSeries K) P) k := by
    rw [Isotropy.mem_kerFlag, ← Isotropy.toK_pow, Isotropy.toK_mulVec,
      Isotropy.mem_kerFlag.mp hUw]
    funext i
    simp [Isotropy.toKv]
  rw [← Isotropy.toK_mulVec, hwv, Matrix.mulVec_smul] at hmem
  have hd' : algebraMap (PowerSeries K) (LaurentSeries K) d ≠ 0 := by
    simpa using (map_ne_zero_iff _
      (IsFractionRing.injective (PowerSeries K) (LaurentSeries K))).2 hd
  have := Submodule.smul_mem _ (algebraMap (PowerSeries K) (LaurentSeries K) d)⁻¹ hmem
  rwa [smul_smul, inv_mul_cancel₀ hd', one_smul] at this

end Nilrad

/-! ### Kernel flatness over `R` is closed under the shift -/

section DCond

variable {K : Type u} [Field K] {n : ℕ}

theorem dcond_add {P X Y : Matrix (Fin n) (Fin n) (PowerSeries K)}
    (hX : Isotropy.DCond P X) (hY : Isotropy.DCond P Y) : Isotropy.DCond P (X + Y) := by
  intro k v hv
  obtain ⟨wX, hwX⟩ := hX k v hv
  obtain ⟨wY, hwY⟩ := hY k v hv
  refine ⟨wX + wY, ?_⟩
  rw [Matrix.mulVec_add, hwX, hwY,
    show Isotropy.dpow P (X + Y) k = Isotropy.dpow P X k + Isotropy.dpow P Y k from
      Dk_add P X Y k, Matrix.add_mulVec]

theorem dcond_smul {P X : Matrix (Fin n) (Fin n) (PowerSeries K)} (c : PowerSeries K)
    (hX : Isotropy.DCond P X) : Isotropy.DCond P (c • X) := by
  intro k v hv
  obtain ⟨w, hw⟩ := hX k v hv
  refine ⟨c • w, ?_⟩
  rw [Matrix.mulVec_smul, hw,
    show Isotropy.dpow P (c • X) k = c • Isotropy.dpow P X k from Dk_smul P X c k,
    Matrix.smul_mulVec]

theorem dcond_commutator (P A : Matrix (Fin n) (Fin n) (PowerSeries K)) :
    Isotropy.DCond P (P * A - A * P) := by
  intro k v hv
  rw [Isotropy.mem_kerFlag] at hv
  refine ⟨A.mulVec v, ?_⟩
  rw [Isotropy.dpow_commutator, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero, sub_zero]

theorem dcond_sub {P X Y : Matrix (Fin n) (Fin n) (PowerSeries K)}
    (hX : Isotropy.DCond P X) (hY : Isotropy.DCond P Y) : Isotropy.DCond P (X - Y) := by
  intro k v hv
  obtain ⟨wX, hwX⟩ := hX k v hv
  obtain ⟨wY, hwY⟩ := hY k v hv
  refine ⟨wX - wY, ?_⟩
  rw [Matrix.mulVec_sub, hwX, hwY,
    show Isotropy.dpow P (X - Y) k = Isotropy.dpow P X k - Isotropy.dpow P Y k from
      Dk_sub P X Y k, Matrix.sub_mulVec]

/-! #### `∂_u P` is kernel flat -/

/-- The entrywise derivative of a matrix over `K⟦u⟧`. -/
noncomputable def matDeriv (X : Matrix (Fin n) (Fin n) (PowerSeries K)) :
    Matrix (Fin n) (Fin n) (PowerSeries K) :=
  X.map (PowerSeries.derivative K)

/-- The entrywise derivative of a vector over `K⟦u⟧`. -/
noncomputable def vecDeriv (v : Fin n → PowerSeries K) : Fin n → PowerSeries K :=
  fun i => PowerSeries.derivative K (v i)

theorem matDeriv_mul (A B : Matrix (Fin n) (Fin n) (PowerSeries K)) :
    matDeriv (A * B) = matDeriv A * B + A * matDeriv B := by
  refine Matrix.ext fun i j => ?_
  show PowerSeries.derivative K (∑ l, A i l * B l j) = _
  rw [map_sum]
  show ∑ l, PowerSeries.derivative K (A i l * B l j)
    = (∑ l, matDeriv A i l * B l j) + ∑ l, A i l * matDeriv B l j
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Derivation.leibniz]
  show A i l • PowerSeries.derivative K (B l j) + B l j • PowerSeries.derivative K (A i l)
    = PowerSeries.derivative K (A i l) * B l j + A i l * PowerSeries.derivative K (B l j)
  rw [smul_eq_mul, smul_eq_mul, mul_comm (B l j)]
  ring

theorem vecDeriv_mulVec (A : Matrix (Fin n) (Fin n) (PowerSeries K))
    (v : Fin n → PowerSeries K) :
    vecDeriv (A *ᵥ v) = matDeriv A *ᵥ v + A *ᵥ vecDeriv v := by
  funext i
  show PowerSeries.derivative K (∑ l, A i l * v l) = _
  rw [map_sum]
  show ∑ l, PowerSeries.derivative K (A i l * v l)
    = (∑ l, matDeriv A i l * v l) + ∑ l, A i l * vecDeriv v l
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Derivation.leibniz]
  show A i l • PowerSeries.derivative K (v l) + v l • PowerSeries.derivative K (A i l)
    = PowerSeries.derivative K (A i l) * v l + A i l * PowerSeries.derivative K (v l)
  rw [smul_eq_mul, smul_eq_mul, mul_comm (v l)]
  ring

theorem matDeriv_pow (P : Matrix (Fin n) (Fin n) (PowerSeries K)) (k : ℕ) :
    matDeriv (P ^ k) = Isotropy.dpow P (matDeriv P) k := by
  induction k with
  | zero =>
      refine Matrix.ext fun i j => ?_
      rw [pow_zero, Isotropy.dpow_zero]
      show PowerSeries.derivative K ((1 : Matrix (Fin n) (Fin n) (PowerSeries K)) i j) = 0
      by_cases h : i = j <;> simp [Matrix.one_apply, h]
  | succ k ih => rw [pow_succ, matDeriv_mul, ih, Isotropy.dpow_succ']

theorem vecDeriv_zero : vecDeriv (0 : Fin n → PowerSeries K) = 0 := by
  funext i
  show PowerSeries.derivative K 0 = 0
  exact map_zero _

/-- `∂_u P = M` for the pencil in the chart at `t₀`, `P = (N + t₀M) + u M`. -/
theorem matDeriv_Pat (N M : Matrix (Fin n) (Fin n) K) (t₀ : K) :
    matDeriv (Pat N M t₀) = dPat M := by
  refine Matrix.ext fun i j => ?_
  rw [show Pat N M t₀ = (N + t₀ • M).map (PowerSeries.C : K →+* PowerSeries K) +
      (PowerSeries.X : PowerSeries K) • dPat M from Pat_eq_add_smul N M t₀]
  show PowerSeries.derivative K
      (PowerSeries.C ((N + t₀ • M) i j) + PowerSeries.X * PowerSeries.C (M i j))
    = PowerSeries.C (M i j)
  rw [map_add, PowerSeries.derivative_C, Derivation.leibniz, PowerSeries.derivative_C,
    PowerSeries.derivative_X]
  simp

/-- **`lem:local-model`(3) for `∂_u P`**: the derivative of the pencil in the
direction of the uniformizer is kernel flat over `K⟦u⟧`.  This is the
paper's "for `∂P`, apply `∂_u` to `P = h P̃ h⁻¹`", done directly: a kernel
vector `v` of `P^k` has `0 = ∂_u(P^k v) = D_k(∂_u P) v + P^k (∂_u v)`. -/
theorem dcond_dPat (N M : Matrix (Fin n) (Fin n) K) (t₀ : K) :
    Isotropy.DCond (Pat N M t₀) (dPat M) := by
  intro k v hv
  refine ⟨-vecDeriv v, ?_⟩
  have h := vecDeriv_mulVec (Pat N M t₀ ^ k) v
  rw [Isotropy.mem_kerFlag.mp hv, vecDeriv_zero, matDeriv_pow, matDeriv_Pat] at h
  rw [Matrix.mulVec_neg]
  exact (eq_neg_of_add_eq_zero_left h.symm).symm

/-- The shifted representative of a marked direction is kernel flat as soon as
the pencil velocity is: `∂_u P` is (`dcond_dPat`) and the correction `[P, Z]`
is a commutator. -/
theorem dcond_Rdot (N M : Matrix (Fin n) (Fin n) K) (t₀ : K)
    (Q : Matrix (Fin n) (Fin n) (Graded.Poly K)) (tdot : K) (Z : Matrix (Fin n) (Fin n) K)
    (hQ : Isotropy.DCond (Pat N M t₀) (Qat Q t₀)) :
    Isotropy.DCond (Pat N M t₀) (Rdot N M t₀ Q tdot Z) := by
  have hM : Isotropy.DCond (Pat N M t₀) (dPat M) := dcond_dPat N M t₀
  have hsmul : tdot • dPat M = (PowerSeries.C tdot : PowerSeries K) • dPat M :=
    Matrix.ext fun i j => by
      show tdot • (dPat M i j) = PowerSeries.C tdot * (dPat M i j)
      rw [PowerSeries.smul_eq_C_mul]
  refine dcond_sub (dcond_add hQ ?_) (dcond_commutator _ _)
  rw [hsmul]
  exact dcond_smul _ hM

end DCond

/-! ### `lem:flag-velocity` -/

section FlagVelocity

variable {K : Type u} [Field K] {n : ℕ}

/-- **`lem:flag-velocity`**.  Two marked directions whose shifted
representatives decompose as in `lem:local-model`(3) pair under `Ω_x` as the
Kostant–Kirillov form of the fibre motions.

The decompositions are the output of `exists_velocity_decomposition`; the
evaluation is `cor:shifted-eval` (`OmegaX_muX_eq_residue`) with the transporters
`A_i := W_i + B_i` over `K⸨u⸩`, `B_i` from `nilrad_eq_image` applied to `U_i`.
Both transporters are needed: the one-transporter form (`Ω_x(μ₁, μ₂) =
res u⁻¹ tr(A₁ Ṙ₂)` for every `A₁` transporting `Ṙ₁`) is false for every
`n ≥ 1` — take `N = M = 0`, so every invariant factor vanishes
(`DVR.AlternatingPresentation.mExp_of_g_eq_zero`), `Blocks = ∅` and `Ω_x = 0`; take `Q₁ = 0`,
`t₁ = 0`, `Z₁ = 0` (so `Ṙ₁ = 0` and `A₁ = u⁻¹ e₁₁` transports it) and
`Q₂ = (ν - t₀ μ) • e₁₁`, `t₂ = 0`, `Z₂ = 0` (marked, `Ṙ₂ = u e₁₁`); the
right-hand side is `res(u⁻¹ · tr(u⁻¹e₁₁ · u e₁₁)) = 1`. -/
theorem flag_velocity_of_decomposition
    (N M : Matrix (Fin n) (Fin n) K) (t₀ : K)
    (hnil : Pat N M t₀ ^ n = 0)
    (Q₁ Q₂ : Matrix (Fin n) (Fin n) (Graded.Poly K)) (t₁ t₂ : K)
    (Z₁ Z₂ : Matrix (Fin n) (Fin n) K)
    (hm₁ : MarkedWith N M t₀ Q₁ t₁ Z₁) (hm₂ : MarkedWith N M t₀ Q₂ t₂ Z₂)
    (W₁ W₂ U₁ U₂ : Matrix (Fin n) (Fin n) (PowerSeries K))
    (hdec₁ : Rdot N M t₀ Q₁ t₁ Z₁ = (Pat N M t₀ * W₁ - W₁ * Pat N M t₀) + U₁)
    (hdec₂ : Rdot N M t₀ Q₂ t₂ Z₂ = (Pat N M t₀ * W₂ - W₂ * Pat N M t₀) + U₂)
    (hU₁ : Lowering (Pat N M t₀) U₁) (hU₂ : Lowering (Pat N M t₀) U₂) :
    ((N + t₀ • M) * matC W₁ - matC W₁ * (N + t₀ • M)) + matC U₁ = 0 ∧
      ((N + t₀ • M) * matC W₂ - matC W₂ * (N + t₀ • M)) + matC U₂ = 0 ∧
      OmegaX N M t₀ (muX N M t₀ Q₁ t₁ Z₁) (muX N M t₀ Q₂ t₂ Z₂)
        = trace (((N + t₀ • M) * matC W₁ - matC W₁ * (N + t₀ • M)) * matC W₂) ∧
      OmegaX N M t₀ (muX N M t₀ Q₁ t₁ Z₁) (muX N M t₀ Q₂ t₂ Z₂)
        = kkForm (N + t₀ • M) (matC W₁) (matC W₂) := by
  classical
  set P₀ := Pat N M t₀ with hP₀
  set L := LaurentSeries K
  set ι : Matrix (Fin n) (Fin n) (PowerSeries K) → Matrix (Fin n) (Fin n) L :=
    Isotropy.toK L with hι
  set N₀ : Matrix (Fin n) (Fin n) K := N + t₀ • M with hN₀
  have hmatC : matC P₀ = N₀ := matC_Pat N M t₀
  -- (a) the value of the decomposition at the point
  have hval : ∀ (W U : Matrix (Fin n) (Fin n) (PowerSeries K))
      (Q : Matrix (Fin n) (Fin n) (Graded.Poly K)) (t : K) (Z : Matrix (Fin n) (Fin n) K),
      MarkedWith N M t₀ Q t Z →
      Rdot N M t₀ Q t Z = (P₀ * W - W * P₀) + U →
      (N₀ * matC W - matC W * N₀) + matC U = 0 := by
    intro W U Q t Z hm hdec
    have h0 : matC (Rdot N M t₀ Q t Z) = 0 := matC_Rdot hm
    rw [hdec] at h0
    have h1 : matC ((P₀ * W - W * P₀) + U)
        = (matC P₀ * matC W - matC W * matC P₀) + matC U := by
      ext i j
      simp [matC, Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply, map_sum]
    rw [h1, hmatC] at h0
    exact h0
  have ha₁ := hval W₁ U₁ Q₁ t₁ Z₁ hm₁ hdec₁
  have ha₂ := hval W₂ U₂ Q₂ t₂ Z₂ hm₂ hdec₂
  -- (b) the trace formula
  have hnilL : ι P₀ ^ n = 0 := by
    rw [← Isotropy.toK_pow, hnil]
    ext i j
    simp [Isotropy.toK]
  have hmapmul : ∀ X Y : Matrix (Fin n) (Fin n) (PowerSeries K), ι (X * Y) = ι X * ι Y :=
    fun X Y => Isotropy.toK_mul X Y
  have hmapsub : ∀ X Y : Matrix (Fin n) (Fin n) (PowerSeries K), ι (X - Y) = ι X - ι Y :=
    fun X Y => Isotropy.toK_sub X Y
  have hmapadd : ∀ X Y : Matrix (Fin n) (Fin n) (PowerSeries K), ι (X + Y) = ι X + ι Y := by
    intro X Y
    ext i j
    simp [hι, Isotropy.toK]
  -- the regular parts of the two directions, corrected inside the parabolic
  obtain ⟨B₁, hB₁p, hB₁⟩ := nilrad_eq_image (ι P₀) hnilL (ι U₁) (toK_mem_nilrad hU₁)
  obtain ⟨B₂, _hB₂p, hB₂⟩ := nilrad_eq_image (ι P₀) hnilL (ι U₂) (toK_mem_nilrad hU₂)
  set A₁ : Matrix (Fin n) (Fin n) L := ι W₁ + B₁ with hA₁def
  set A₂ : Matrix (Fin n) (Fin n) L := ι W₂ + B₂ with hA₂def
  have hA₁ : ι P₀ * A₁ - A₁ * ι P₀ = ι (Rdot N M t₀ Q₁ t₁ Z₁) := by
    rw [hdec₁, hmapadd, hmapsub, hmapmul, hmapmul, hA₁def, hB₁]
    noncomm_ring
  have hA₂ : ι P₀ * A₂ - A₂ * ι P₀ = ι (Rdot N M t₀ Q₂ t₂ Z₂) := by
    rw [hdec₂, hmapadd, hmapsub, hmapmul, hmapmul, hA₂def, hB₂]
    noncomm_ring
  -- the trace expansion
  have hRdot₂ : ι (Rdot N M t₀ Q₂ t₂ Z₂) = (ι P₀ * ι W₂ - ι W₂ * ι P₀) + ι U₂ := by
    rw [hdec₂, hmapadd, hmapsub, hmapmul, hmapmul]
  have htrsplit : trace (A₁ * ι (Rdot N M t₀ Q₂ t₂ Z₂))
      = trace (ι W₁ * ι (Rdot N M t₀ Q₂ t₂ Z₂)) - trace (ι U₁ * ι W₂) := by
    have h1 : trace (A₁ * ι (Rdot N M t₀ Q₂ t₂ Z₂))
        = trace (ι W₁ * ι (Rdot N M t₀ Q₂ t₂ Z₂)) + trace (B₁ * ι (Rdot N M t₀ Q₂ t₂ Z₂)) := by
      rw [hA₁def, add_mul, trace_add]
    have h2 : trace (B₁ * ι (Rdot N M t₀ Q₂ t₂ Z₂))
        = trace (B₁ * (ι P₀ * ι W₂ - ι W₂ * ι P₀)) + trace (B₁ * ι U₂) := by
      rw [hRdot₂, mul_add, trace_add]
    have h3 : trace (B₁ * ι U₂) = 0 :=
      trace_parab_nilrad (ι P₀) hnilL B₁ hB₁p (ι U₂) (toK_mem_nilrad hU₂)
    have h4 : trace (B₁ * (ι P₀ * ι W₂ - ι W₂ * ι P₀)) = -trace (ι U₁ * ι W₂) := by
      rw [trace_mul_commutator, ← hB₁]
    rw [h1, h2, h3, h4, add_zero]
    abel
  -- the right-hand side is integral
  have hintegral : trace (A₁ * ι (Rdot N M t₀ Q₂ t₂ Z₂))
      = algebraMap (PowerSeries K) (LaurentSeries K)
          (trace (W₁ * Rdot N M t₀ Q₂ t₂ Z₂) - trace (U₁ * W₂)) := by
    rw [htrsplit, map_sub, Isotropy.toK_trace, Isotropy.toK_trace,
      show Isotropy.toK (LaurentSeries K) (W₁ * Rdot N M t₀ Q₂ t₂ Z₂)
        = ι W₁ * ι (Rdot N M t₀ Q₂ t₂ Z₂) from hmapmul _ _,
      show Isotropy.toK (LaurentSeries K) (U₁ * W₂) = ι U₁ * ι W₂ from hmapmul _ _]
  -- evaluate at the point: `cor:shifted-eval` with both transporters
  have hOm := Height.Pencil.OmegaX_muX_eq_residue N M t₀
    Q₁ Q₂ t₁ t₂ Z₁ Z₂ hm₁ hm₂ A₁ A₂ hA₁ hA₂
  have hz : matC (W₁ * Rdot N M t₀ Q₂ t₂ Z₂) = 0 := by
    rw [matC_mul, matC_Rdot hm₂, Matrix.mul_zero]
  have hU₁val : matC U₁ = -(N₀ * matC W₁ - matC W₁ * N₀) := by
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact ha₁
  have hmain : OmegaX N M t₀ (muX N M t₀ Q₁ t₁ Z₁) (muX N M t₀ Q₂ t₂ Z₂)
      = trace ((N₀ * matC W₁ - matC W₁ * N₀) * matC W₂) := by
    rw [hOm, hintegral, constantCoeff_eq_residue, map_sub, constantCoeff_trace,
      constantCoeff_trace, hz, Matrix.trace_zero, zero_sub, matC_mul, hU₁val, neg_mul,
      trace_neg, neg_neg]
  refine ⟨ha₁, ha₂, hmain, ?_⟩
  rw [hmain]
  exact trace_adMatrix_mul_eq_kkForm N₀ (matC W₁) (matC W₂)

end FlagVelocity

end Height.Pencil
