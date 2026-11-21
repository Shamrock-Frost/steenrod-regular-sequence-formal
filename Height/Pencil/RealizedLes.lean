import Height.Pencil.Centralizer

/-!
# `thm:realized-bound`: the realised bound `dim 𝒩 = n² − c(τ) + Σ bᵢ`

The paper, `subsec:realized`, `lem:les`, `lem:free`, `thm:realized-bound`.

The main result is `realizedDimStmt` (`thm:realized-bound`), whose objects live in
`Pencil/Centralizer.lean`.
-/

noncomputable section

namespace Height.Pencil

open Matrix Height.Graded Height.Steenrod Height.Toolbox

variable {K : Type*} [Field K] {n : ℕ}

/-! ### The two shift vectors -/

variable (n) in
/-- The shifts of `F = gl_n ⊗ B`: all zero. -/
abbrev shiftSrc : Fin (n * n) → ℤ := fun _ => 0

variable (n) in
/-- The shifts of `F' = gl_n ⊗ B(1)`: all `-1`. -/
abbrev shiftTgt : Fin (n * n) → ℤ := fun _ => -1

/-! ### `ad_P` raises the degree by one -/

theorem adMat_pencil_mem_Bpiece (N M : Matrix (Fin n) (Fin n) K) (x y : Fin (n * n)) :
    adMat (pencil N M) x y ∈ Bpiece K 1 := by
  show adEntry (pencil N M) (glIdx n x) (glIdx n y) ∈ Bpiece K 1
  rw [show (glIdx n x) = ((glIdx n x).1, (glIdx n x).2) from rfl,
    show (glIdx n y) = ((glIdx n y).1, (glIdx n y).2) from rfl, adEntry_apply]
  refine Submodule.sub_mem _ ?_ ?_ <;> split_ifs
  · exact pencil_mem_Bpiece N M _ _
  · exact Submodule.zero_mem _
  · exact pencil_mem_Bpiece N M _ _
  · exact Submodule.zero_mem _

theorem adP_mem_piece (N M : Matrix (Fin n) (Fin n) K) {e : ℤ}
    {x : Fin (n * n) → Graded.Poly K}
    (hx : x ∈ (Graded.GradedPresentation.of K (shiftSrc n)).piece e) :
    adP N M x ∈ (Graded.GradedPresentation.of K (shiftTgt n)).piece e := by
  refine (Graded.GradedPresentation.of K _).mem_piece.2 fun j => ?_
  have hj : adP N M x j = ∑ l, adMat (pencil N M) j l * x l := rfl
  rw [hj, show e - shiftTgt n j = 1 + e by simp only [shiftTgt]; ring]
  refine Submodule.sum_mem _ fun l _ => ?_
  have := Bpiece_smul_Bpiece (adMat_pencil_mem_Bpiece N M j l)
    ((Graded.GradedPresentation.of K _).mem_piece.1 hx l)
  simpa using this

theorem proj_adP (N M : Matrix (Fin n) (Fin n) K) (e : ℤ)
    (x : Fin (n * n) → Graded.Poly K) :
    (Graded.GradedPresentation.of K (shiftTgt n)).proj e (adP N M x)
      = adP N M ((Graded.GradedPresentation.of K (shiftSrc n)).proj e x) := by
  classical
  obtain ⟨s, hs⟩ := (Graded.GradedPresentation.of K (shiftSrc n)).exists_sum_proj x
  have hsum : (Graded.GradedPresentation.of K (shiftTgt n)).proj e (adP N M x)
      = ∑ e' ∈ s, (if e = e' then
          adP N M ((Graded.GradedPresentation.of K (shiftSrc n)).proj e' x) else 0) := by
    conv_lhs => rw [← hs]
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun e' _ => ?_
    exact (Graded.GradedPresentation.of K (shiftTgt n)).proj_of_mem
      (adP_mem_piece N M ((Graded.GradedPresentation.of K (shiftSrc n)).proj_mem e' x))
  have hz : (Graded.GradedPresentation.of K (shiftSrc n)).proj e x
      = ∑ e' ∈ s, (if e = e' then
          (Graded.GradedPresentation.of K (shiftSrc n)).proj e' x else 0) := by
    conv_lhs => rw [← hs]
    rw [map_sum]
    exact Finset.sum_congr rfl fun e' _ =>
      (Graded.GradedPresentation.of K (shiftSrc n)).proj_of_mem (e := e)
        ((Graded.GradedPresentation.of K (shiftSrc n)).proj_mem e' x)
  rw [hsum, hz,
    Finset.sum_ite_eq s e
      (fun e' => adP N M ((Graded.GradedPresentation.of K (shiftSrc n)).proj e' x)),
    Finset.sum_ite_eq s e (fun e' => (Graded.GradedPresentation.of K (shiftSrc n)).proj e' x)]
  by_cases he : e ∈ s <;> simp [he]

theorem isGraded_centralizerSub (N M : Matrix (Fin n) (Fin n) K) :
    (Graded.GradedPresentation.of K (shiftSrc n)).IsGraded (centralizerSub N M) := by
  intro f hf e
  have hf' : adP N M f = 0 := hf
  show adP N M ((Graded.GradedPresentation.of K (shiftSrc n)).proj e f) = 0
  rw [← proj_adP, hf', map_zero]

theorem isGraded_adRange (N M : Matrix (Fin n) (Fin n) K) :
    (Graded.GradedPresentation.of K (shiftTgt n)).IsGraded (adRange N M) := by
  rintro _ ⟨x, rfl⟩ e
  exact ⟨(Graded.GradedPresentation.of K (shiftSrc n)).proj e x, (proj_adP N M e x).symm⟩

/-! ### Consequences of a homogeneous basis of `C` -/

section Basis

variable {N M : Matrix (Fin n) (Fin n) K} {ι : Type} [Fintype ι] {b : ι → ℤ}
  {u : ι → (Fin (n * n) → Graded.Poly K)}

/-- The degrees of a homogeneous basis of `C ⊆ F` (shifts `0`) are nonnegative:
`F` has no nonzero element in a negative degree. -/
theorem CentralizerBasis.b_nonneg (hb : CentralizerBasis N M b u) (i : ι) : 0 ≤ b i := by
  by_contra h
  push Not at h
  refine hb.linInd.ne_zero i ?_
  have hu := hb.homog i
  rwa [(Graded.GradedPresentation.free K (Fin (n * n))).piece_eq_bot (e := b i)
      (fun _ => by simpa using h), Submodule.mem_bot] at hu

/-- A homogeneous element of `C` of degree `e` is a combination of the basis
with *homogeneous* coefficients, of degrees `e - bᵢ`. -/
theorem CentralizerBasis.exists_homog_coeffs (hb : CentralizerBasis N M b u) {e : ℤ}
    {z : Fin (n * n) → Graded.Poly K}
    (hz : z ∈ (Graded.GradedPresentation.of K (shiftSrc n)).sub (centralizerSub N M) e) :
    ∃ c : ι → Graded.Poly K, (∀ i, c i ∈ Bpiece K (e - b i)) ∧ z = ∑ i, c i • u i := by
  obtain ⟨hzC, hzF⟩ := Submodule.mem_inf.1 hz
  have hzC' : z ∈ Submodule.span (Graded.Poly K) (Set.range u) := by
    rw [hb.span]; exact hzC
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hzC'
  refine ⟨fun i => Bproj (e - b i) (c i), fun i => Bproj_mem _ _, ?_⟩
  have hzz : (Graded.GradedPresentation.of K (shiftSrc n)).proj e z = z :=
    (Graded.GradedPresentation.of K (shiftSrc n)).proj_self hzF
  rw [← hzz, ← hc, map_sum]
  exact Finset.sum_congr rfl fun i _ =>
    (Graded.GradedPresentation.of K (shiftSrc n)).proj_smul (c i) (hb.homog i)

/-- A homogeneous multiple of a basis vector is a homogeneous element of `C`. -/
theorem CentralizerBasis.smul_mem_sub (hb : CentralizerBasis N M b u) (i : ι) {d : ℤ}
    {f : Graded.Poly K} (hf : f ∈ Bpiece K d) :
    f • u i ∈ (Graded.GradedPresentation.of K (shiftSrc n)).sub (centralizerSub N M) (d + b i) :=
  Submodule.mem_inf.2 ⟨(centralizerSub N M).smul_mem _ (hb.mem i),
    (Graded.GradedPresentation.of K _).smul_mem_piece hf (hb.homog i)⟩

/-- The `bᵢ = 0` part of the basis is a `K`-independent family in `C₀`, so
`dim C₀ ≥ #{i : bᵢ = 0} = ∑ᵢ (1 - bᵢ)₊`. -/
theorem CentralizerBasis.sum_le_finrank_sub_zero (hb : CentralizerBasis N M b u) :
    ∑ i, (1 - b i).toNat
      ≤ Module.finrank K
          ((Graded.GradedPresentation.of K (shiftSrc n)).sub (centralizerSub N M) 0) := by
  classical
  set E : (∀ i, Bpiece K (0 - b i)) →ₗ[K] (Fin (n * n) → Graded.Poly K) :=
    ∑ i, (LinearMap.smulRight (Bpiece K (0 - b i)).subtype (u i)).comp
      (LinearMap.proj i) with hE
  have hEapply : ∀ c : (∀ i, Bpiece K (0 - b i)), E c = ∑ i, ((c i : Graded.Poly K)) • u i := by
    intro c
    rw [hE]
    simp [LinearMap.sum_apply]
  have hEinj : Function.Injective E := by
    rw [← LinearMap.ker_eq_bot]
    refine (Submodule.eq_bot_iff _).2 fun c hc => ?_
    have hc' : ∑ i, ((c i : Graded.Poly K)) • u i = 0 := by
      rw [← hEapply c]; exact hc
    have := Fintype.linearIndependent_iff.1 hb.linInd (fun i => (c i : Graded.Poly K)) hc'
    funext i
    exact Subtype.ext (this i)
  have hrange : LinearMap.range E
      ≤ (Graded.GradedPresentation.of K (shiftSrc n)).sub (centralizerSub N M) 0 := by
    rintro _ ⟨c, rfl⟩
    rw [hEapply]
    refine Submodule.sum_mem _ fun i _ => ?_
    have := hb.smul_mem_sub i (c i).2
    rwa [show (0 - b i) + b i = 0 by ring] at this
  have hfin : Module.finrank K (LinearMap.range E) = Module.finrank K (∀ i, Bpiece K (0 - b i)) :=
    (LinearEquiv.ofInjective E hEinj).finrank_eq.symm
  have hdom : Module.finrank K (∀ i, Bpiece K (0 - b i)) = ∑ i, (1 - b i).toNat := by
    rw [Module.finrank_pi_fintype]
    exact Finset.sum_congr rfl fun i _ => by
      rw [finrank_Bpiece]; congr 1; ring
  have hmono := Submodule.finrank_mono (R := K) hrange
  calc ∑ i, (1 - b i).toNat = Module.finrank K (LinearMap.range E) := by rw [hfin, hdom]
    _ ≤ _ := hmono

/-- **The `H¹` bound.**  Modulo `μ^k C_k + ν^k C_k`, the degree-`2k` piece of
`C` is spanned by the `∑ᵢ (bᵢ - 1)₊` monomial multiples `μ^p ν^{2k-bᵢ-p} uᵢ`
with `k - bᵢ < p < k`: a monomial `μ^p ν^q uᵢ` of degree `2k` has `p ≥ k` or
`q ≥ k` unless `p` lies in that window. -/
theorem CentralizerBasis.exists_span_sub_two (hb : CentralizerBasis N M b u) (k : ℕ)
    (Zsub : Submodule K (Fin (n * n) → Graded.Poly K))
    (hmuZ : ∀ z ∈ (Graded.GradedPresentation.of K (shiftSrc n)).sub (centralizerSub N M) (k : ℤ),
        (mu : Graded.Poly K) ^ k • z ∈ Zsub)
    (hnuZ : ∀ z ∈ (Graded.GradedPresentation.of K (shiftSrc n)).sub (centralizerSub N M) (k : ℤ),
        (nu : Graded.Poly K) ^ k • z ∈ Zsub) :
    ∃ G : Finset (Fin (n * n) → Graded.Poly K),
      G.card ≤ ∑ i, (b i - 1).toNat ∧
      (Graded.GradedPresentation.of K (shiftSrc n)).sub (centralizerSub N M) (2 * (k : ℤ))
        ≤ Zsub ⊔ Submodule.span K (G : Set (Fin (n * n) → Graded.Poly K)) := by
  classical
  set g : (Σ _ : ι, ℤ) → (Fin (n * n) → Graded.Poly K) := fun x =>
    ((mu : Graded.Poly K) ^ x.2.toNat * nu ^ (2 * (k : ℤ) - b x.1 - x.2).toNat) • u x.1 with hg
  set J : Finset (Σ _ : ι, ℤ) :=
    Finset.univ.sigma (fun i : ι => Finset.Ico ((k : ℤ) - b i + 1) (k : ℤ)) with hJ
  have hgap : ∀ (j : ι) (t : ℤ), g ⟨j, t⟩ =
      ((mu : Graded.Poly K) ^ t.toNat * nu ^ (2 * (k : ℤ) - b j - t).toNat) • u j :=
    fun _ _ => rfl
  refine ⟨J.image g, ?_, ?_⟩
  · refine le_trans Finset.card_image_le ?_
    rw [hJ, Finset.card_sigma]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Int.card_Ico]
    omega
  · intro z hz
    obtain ⟨c, hc, rfl⟩ := hb.exists_homog_coeffs hz
    refine Submodule.sum_mem _ fun i _ => ?_
    rcases lt_or_ge (2 * (k : ℤ) - b i) 0 with hneg | hnonneg
    · have := hc i
      rw [Bpiece_of_neg hneg, Submodule.mem_bot] at this
      simp [this]
    · set d : ℕ := (2 * (k : ℤ) - b i).toNat with hd
      have hdc : ((d : ℤ)) = 2 * (k : ℤ) - b i := by omega
      have hci : c i ∈ Submodule.span K
          {f : Graded.Poly K | ∃ p q : ℕ, p + q = d ∧ f = mu ^ p * nu ^ q} := by
        rw [← Bpiece_eq_span, hdc]
        exact hc i
      refine (?_ : ∀ f ∈ Submodule.span K
          {f : Graded.Poly K | ∃ p q : ℕ, p + q = d ∧ f = mu ^ p * nu ^ q},
          f • u i ∈ Zsub ⊔ Submodule.span K ((J.image g : Finset _) :
            Set (Fin (n * n) → Graded.Poly K))) _ hci
      intro f hf
      induction hf using Submodule.span_induction with
      | mem f hf =>
          obtain ⟨p, q, hpq, rfl⟩ := hf
          rcases le_or_gt k p with hp | hp
          · refine Submodule.mem_sup_left (?_ : _ ∈ Zsub)
            have hsplit : ((mu : Graded.Poly K) ^ p * nu ^ q) • u i
                = (mu : Graded.Poly K) ^ k • (((mu : Graded.Poly K) ^ (p - k) * nu ^ q) • u i) := by
              rw [smul_smul, ← mul_assoc, ← pow_add]
              congr 3
              omega
            rw [hsplit]
            refine hmuZ _ ?_
            have hmem := hb.smul_mem_sub i
              (Bpiece_smul_Bpiece (mu_pow_mem (K := K) (p - k)) (nu_pow_mem (K := K) q))
            have : (((p - k : ℕ) : ℤ) + ((q : ℕ) : ℤ)) + b i = (k : ℤ) := by
              have hb0 := hb.b_nonneg i
              omega
            rwa [this] at hmem
          · rcases le_or_gt k q with hq | hq
            · refine Submodule.mem_sup_left (?_ : _ ∈ Zsub)
              have hsplit : ((mu : Graded.Poly K) ^ p * nu ^ q) • u i
                  = (nu : Graded.Poly K) ^ k • (((mu : Graded.Poly K) ^ p * nu ^ (q - k)) • u i) := by
                rw [smul_smul, ← mul_assoc, mul_comm ((nu : Graded.Poly K) ^ k), mul_assoc,
                  ← pow_add]
                congr 3
                omega
              rw [hsplit]
              refine hnuZ _ ?_
              have hmem := hb.smul_mem_sub i
                (Bpiece_smul_Bpiece (mu_pow_mem (K := K) p) (nu_pow_mem (K := K) (q - k)))
              have : (((p : ℕ) : ℤ) + ((q - k : ℕ) : ℤ)) + b i = (k : ℤ) := by
                have hb0 := hb.b_nonneg i
                push_cast [Nat.cast_sub hq]
                omega
              rwa [this] at hmem
            · refine Submodule.mem_sup_right (Submodule.subset_span ?_)
              refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨⟨i, (p : ℤ)⟩, ?_, ?_⟩)
              · rw [hJ, Finset.mem_sigma]
                refine ⟨Finset.mem_univ i, ?_⟩
                show (p : ℤ) ∈ Finset.Ico ((k : ℤ) - b i + 1) (k : ℤ)
                rw [Finset.mem_Ico]
                omega
              · rw [hgap]
                have h1 : ((p : ℤ)).toNat = p := by omega
                have h2 : (2 * (k : ℤ) - b i - (p : ℤ)).toNat = q := by omega
                rw [h1, h2]
      | zero => simp
      | add x y _ _ ihx ihy => rw [add_smul]; exact Submodule.add_mem _ ihx ihy
      | smul a x _ ihx => rw [smul_assoc]; exact Submodule.smul_mem _ a ihx

end Basis

/-! ### Divisibility by `μ` on homogeneous pieces -/

/-- If `μ^k g` is homogeneous of degree `d` then `g` is homogeneous of degree `d - k`. -/
theorem mem_Bpiece_of_mu_pow_mul {k : ℕ} : ∀ {d : ℤ} {g : Graded.Poly K},
    (mu : Graded.Poly K) ^ k * g ∈ Bpiece K d → g ∈ Bpiece K (d - k) := by
  induction k with
  | zero => intro d g h; simpa using h
  | succ m ih =>
      intro d g h
      have hrw : (mu : Graded.Poly K) * ((mu : Graded.Poly K) ^ m * g)
          = (mu : Graded.Poly K) ^ (m + 1) * g := by ring
      have h2 := ih (mem_Bpiece_of_mu_mul (by rw [hrw]; exact h))
      have hd : d - 1 - (m : ℤ) = d - ((m + 1 : ℕ) : ℤ) := by push_cast; ring
      rwa [hd] at h2

/-- The converse of `Graded.mu_pow_smul_mem_piece`. -/
theorem mem_piece_of_mu_pow_smul {r : ℕ} {a : Fin r → ℤ} {e : ℤ} {k : ℕ}
    {x : Fin r → Graded.Poly K}
    (h : (mu : Graded.Poly K) ^ k • x ∈ (Graded.GradedPresentation.of K a).piece (e + k)) :
    x ∈ (Graded.GradedPresentation.of K a).piece e := by
  refine (Graded.GradedPresentation.of K _).mem_piece.2 fun j => ?_
  have hj := (Graded.GradedPresentation.of K _).mem_piece.1 h j
  rw [Pi.smul_apply, smul_eq_mul] at hj
  have h2 := mem_Bpiece_of_mu_pow_mul hj
  rwa [show e + (k : ℤ) - a j - (k : ℤ) = e - a j by ring] at h2

/-- `μ` is prime in `B`. -/
theorem mu_prime : Prime (mu : Graded.Poly K) := by
  rw [mu]; exact MvPolynomial.X_prime

/-- `μ` does not divide a power of `ν`. -/
theorem not_mu_dvd_nu_pow (k : ℕ) : ¬ ((mu : Graded.Poly K) ∣ (nu : Graded.Poly K) ^ k) := by
  intro h
  have h1 := (mu_dvd_iff (nu_pow_mem (K := K) k)).1 h
  rw [nuLead_nu_pow] at h1
  exact one_ne_zero h1

theorem smul_left_cancel {r : ℕ} {c : Graded.Poly K} (hc : c ≠ 0)
    {x y : Fin r → Graded.Poly K} (h : c • x = c • y) : x = y := by
  funext j
  have hj := congrFun h j
  rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul] at hj
  exact mul_left_cancel₀ hc hj

/-! ### The degree-`e` piece of `im ad_P` -/

/-- `S ∩ F'_e = ad_P (F_e)`. -/
theorem adRange_inf_piece (N M : Matrix (Fin n) (Fin n) K) (e : ℤ) :
    (adRange N M).restrictScalars K ⊓ (Graded.GradedPresentation.of K (shiftTgt n)).piece e
      = ((Graded.GradedPresentation.of K (shiftSrc n)).piece e).map
        ((adP N M).restrictScalars K) := by
  refine le_antisymm ?_ ?_
  · rintro x ⟨hx1, hx2⟩
    obtain ⟨z, hz⟩ := hx1
    refine ⟨(Graded.GradedPresentation.of K (shiftSrc n)).proj e z,
      (Graded.GradedPresentation.of K _).proj_mem _ _, ?_⟩
    rw [LinearMap.restrictScalars_apply, ← proj_adP, hz,
      (Graded.GradedPresentation.of K (shiftTgt n)).proj_self hx2]
  · rintro _ ⟨y, hy, rfl⟩
    exact ⟨⟨y, rfl⟩, adP_mem_piece _ _ hy⟩

/-! ### The rank chain -/

/-- If `ρ` and `ζ` are linear on a finite-dimensional `U`, then the image of `U`
under `ρ` is no larger than the image under `ζ` plus the image under `ρ` of the
part of `U` killed by `ζ`. -/
theorem finrank_map_le_map_add_map_inf_ker {V W W' : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [AddCommGroup W'] [Module K W']
    (U : Submodule K V) [FiniteDimensional K U] (ρ : V →ₗ[K] W) (ζ : V →ₗ[K] W') :
    Module.finrank K (U.map ρ)
      ≤ Module.finrank K (U.map ζ) + Module.finrank K ((U ⊓ LinearMap.ker ζ).map ρ) := by
  have e1 := finrank_map_add_finrank_inf_ker ρ U
  have e2 := finrank_map_add_finrank_inf_ker ζ U
  have e3 := finrank_map_add_finrank_inf_ker ρ (U ⊓ LinearMap.ker ζ)
  have e4 : Module.finrank K ((U ⊓ LinearMap.ker ζ) ⊓ LinearMap.ker ρ : Submodule K V)
      ≤ Module.finrank K ((U ⊓ LinearMap.ker ρ : Submodule K V)) :=
    Submodule.finrank_mono (R := K) (inf_le_inf_right _ inf_le_left)
  omega

section Count

variable {N M : Matrix (Fin n) (Fin n) K} {ι : Type} [Fintype ι] {b : ι → ℤ}
  {u : ι → (Fin (n * n) → Graded.Poly K)}

/-- **The counting step of `thm:realized-bound`.**  Let `T` be a space of
degree-`0` elements of `F' = ⨁ B(1)` which both `μ^k` and `ν^k` push into
`S = im ad_P`.  Then `dim T + #ι ≤ n² + ∑ bᵢ`.

The proof is the five-term sequence of `lem:les` made explicit.  For `x ∈ T`
choose `ξ, η` of degree `k` with `ad_P ξ = μ^k x` and `ad_P η = ν^k x`; the
class of `ν^k ξ − μ^k η` in `C_{2k}/(μ^k C_k + ν^k C_k)` is the `H¹` obstruction,
and `x` is in the image of `ad_P` on degree `0` as soon as the obstruction
vanishes.  The two dimensions are bounded by the `H¹` spanning bound
(`CentralizerBasis.exists_span_sub_two`) and by
`dim (ad_P F₀) = n² − dim C₀ ≤ n² − ∑ (1 − bᵢ)₊`.  Choices are avoided by
taking `U` to be the space of *triples* `(x, ξ, η)`. -/
theorem finrank_le_of_mu_nu_pow (hb : CentralizerBasis N M b u)
    (T : Submodule K (Fin (n * n) → Graded.Poly K)) (k : ℕ)
    (hT : T ≤ (Graded.GradedPresentation.of K (shiftTgt n)).piece 0)
    (hmu : ∀ x ∈ T, (mu : Graded.Poly K) ^ k • x ∈ adRange N M)
    (hnu : ∀ x ∈ T, (nu : Graded.Poly K) ^ k • x ∈ adRange N M) :
    (Module.finrank K T : ℤ) + Fintype.card ι ≤ n * n + ∑ i, b i := by
  classical
  have : FiniteDimensional K T := Submodule.finiteDimensional_of_le hT
  -- the three coordinate projections of the space of triples `(x, ξ, η)`
  obtain ⟨pT, hpTa⟩ : ∃ f : (T × (Graded.GradedPresentation.of K (shiftSrc n)).piece (k : ℤ) ×
        (Graded.GradedPresentation.of K (shiftSrc n)).piece (k : ℤ)) →ₗ[K]
          (Fin (n * n) → Graded.Poly K),
      ∀ p, f p = (p.1 : Fin (n * n) → Graded.Poly K) :=
    ⟨T.subtype.comp (LinearMap.fst K T _), fun _ => rfl⟩
  obtain ⟨pX, hpXa⟩ : ∃ f : (T × (Graded.GradedPresentation.of K (shiftSrc n)).piece (k : ℤ) ×
        (Graded.GradedPresentation.of K (shiftSrc n)).piece (k : ℤ)) →ₗ[K]
          (Fin (n * n) → Graded.Poly K),
      ∀ p, f p = (p.2.1 : Fin (n * n) → Graded.Poly K) :=
    ⟨((Graded.GradedPresentation.of K (shiftSrc n)).piece (k : ℤ)).subtype.comp
      ((LinearMap.fst K _ _).comp (LinearMap.snd K T _)), fun _ => rfl⟩
  obtain ⟨pY, hpYa⟩ : ∃ f : (T × (Graded.GradedPresentation.of K (shiftSrc n)).piece (k : ℤ) ×
        (Graded.GradedPresentation.of K (shiftSrc n)).piece (k : ℤ)) →ₗ[K]
          (Fin (n * n) → Graded.Poly K),
      ∀ p, f p = (p.2.2 : Fin (n * n) → Graded.Poly K) :=
    ⟨((Graded.GradedPresentation.of K (shiftSrc n)).piece (k : ℤ)).subtype.comp
      ((LinearMap.snd K _ _).comp (LinearMap.snd K T _)), fun _ => rfl⟩
  -- multiplication by `μ^k` and by `ν^k`
  obtain ⟨smu, hsmua⟩ : ∃ f : (Fin (n * n) → Graded.Poly K) →ₗ[K]
        (Fin (n * n) → Graded.Poly K), ∀ x, f x = (mu : Graded.Poly K) ^ k • x :=
    ⟨(LinearMap.lsmul (Graded.Poly K) (Fin (n * n) → Graded.Poly K)
      ((mu : Graded.Poly K) ^ k)).restrictScalars K, fun _ => rfl⟩
  obtain ⟨snu, hsnua⟩ : ∃ f : (Fin (n * n) → Graded.Poly K) →ₗ[K]
        (Fin (n * n) → Graded.Poly K), ∀ x, f x = (nu : Graded.Poly K) ^ k • x :=
    ⟨(LinearMap.lsmul (Graded.Poly K) (Fin (n * n) → Graded.Poly K)
      ((nu : Graded.Poly K) ^ k)).restrictScalars K, fun _ => rfl⟩
  -- `μ^k C_k + ν^k C_k`
  set Zsub : Submodule K (Fin (n * n) → Graded.Poly K) :=
    ((Graded.GradedPresentation.of K (shiftSrc n)).sub (centralizerSub N M) (k : ℤ)).map snu
      ⊔ ((Graded.GradedPresentation.of K (shiftSrc n)).sub (centralizerSub N M) (k : ℤ)).map smu
    with hZsub
  have hnuZ : ∀ z ∈ (Graded.GradedPresentation.of K (shiftSrc n)).sub (centralizerSub N M) (k : ℤ),
      (nu : Graded.Poly K) ^ k • z ∈ Zsub := fun z hz =>
    Submodule.mem_sup_left ⟨z, hz, hsnua z⟩
  have hmuZ : ∀ z ∈ (Graded.GradedPresentation.of K (shiftSrc n)).sub (centralizerSub N M) (k : ℤ),
      (mu : Graded.Poly K) ^ k • z ∈ Zsub := fun z hz =>
    Submodule.mem_sup_right ⟨z, hz, hsmua z⟩
  -- the space of triples and the two maps out of it
  obtain ⟨U, hmemU⟩ : ∃ U : Submodule K
      (T × (Graded.GradedPresentation.of K (shiftSrc n)).piece (k : ℤ) ×
        (Graded.GradedPresentation.of K (shiftSrc n)).piece (k : ℤ)), ∀ p, p ∈ U ↔
      (adP N M (p.2.1 : Fin (n * n) → Graded.Poly K)
          = (mu : Graded.Poly K) ^ k • (p.1 : Fin (n * n) → Graded.Poly K) ∧
        adP N M (p.2.2 : Fin (n * n) → Graded.Poly K)
          = (nu : Graded.Poly K) ^ k • (p.1 : Fin (n * n) → Graded.Poly K)) :=
    ⟨LinearMap.ker (((adP N M).restrictScalars K).comp pX - smu.comp pT)
      ⊓ LinearMap.ker (((adP N M).restrictScalars K).comp pY - snu.comp pT), fun p => by
        simp only [Submodule.mem_inf, LinearMap.mem_ker, LinearMap.sub_apply,
          LinearMap.comp_apply, sub_eq_zero, LinearMap.restrictScalars_apply,
          hsmua, hsnua, hpTa, hpXa, hpYa]⟩
  obtain ⟨zeta, hzetaa⟩ : ∃ f : (T × (Graded.GradedPresentation.of K (shiftSrc n)).piece (k : ℤ) ×
        (Graded.GradedPresentation.of K (shiftSrc n)).piece (k : ℤ)) →ₗ[K]
          (Fin (n * n) → Graded.Poly K),
      ∀ p, f p = (nu : Graded.Poly K) ^ k • (p.2.1 : Fin (n * n) → Graded.Poly K)
        - (mu : Graded.Poly K) ^ k • (p.2.2 : Fin (n * n) → Graded.Poly K) :=
    ⟨snu.comp pX - smu.comp pY, fun p => by
      rw [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply, hsnua, hsmua,
        hpXa, hpYa]⟩
  obtain ⟨zeta', hzeta'a⟩ : ∃ f : (T × (Graded.GradedPresentation.of K (shiftSrc n)).piece (k : ℤ) ×
        (Graded.GradedPresentation.of K (shiftSrc n)).piece (k : ℤ)) →ₗ[K]
        ((Fin (n * n) → Graded.Poly K) ⧸ Zsub), ∀ p, f p = Zsub.mkQ (zeta p) :=
    ⟨Zsub.mkQ.comp zeta, fun _ => rfl⟩
  -- `U` surjects onto `T`
  have hUT : U.map pT = T := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨p, -, rfl⟩
      rw [hpTa]
      exact (p.1).2
    · intro x hx
      have hx0 : x ∈ (Graded.GradedPresentation.of K (shiftTgt n)).piece 0 := hT hx
      have hmuk : (mu : Graded.Poly K) ^ k • x
          ∈ ((Graded.GradedPresentation.of K (shiftSrc n)).piece (k : ℤ)).map
              ((adP N M).restrictScalars K) := by
        rw [← adRange_inf_piece]
        refine ⟨hmu x hx, ?_⟩
        have h := mu_pow_smul_mem_piece hx0 k
        rwa [zero_add] at h
      have hnuk : (nu : Graded.Poly K) ^ k • x
          ∈ ((Graded.GradedPresentation.of K (shiftSrc n)).piece (k : ℤ)).map
              ((adP N M).restrictScalars K) := by
        rw [← adRange_inf_piece]
        refine ⟨hnu x hx, ?_⟩
        have h := (Graded.GradedPresentation.of K _).smul_mem_piece (nu_pow_mem (K := K) k) hx0
        rwa [add_zero] at h
      obtain ⟨ξ, hξF, hξ⟩ := hmuk
      obtain ⟨η, hηF, hη⟩ := hnuk
      exact ⟨(⟨x, hx⟩, ⟨ξ, hξF⟩, ⟨η, hηF⟩), (hmemU _).2 ⟨hξ, hη⟩, hpTa _⟩
  -- `ζ` lands in `C_{2k}`
  have hzetaC : ∀ p ∈ U, zeta p
      ∈ (Graded.GradedPresentation.of K (shiftSrc n)).sub (centralizerSub N M) (2 * (k : ℤ)) := by
    intro p hp
    obtain ⟨h1, h2⟩ := (hmemU p).1 hp
    refine ⟨?_, ?_⟩
    · show adP N M (zeta p) = 0
      rw [hzetaa, map_sub, map_smul, map_smul, h1, h2, smul_smul, smul_smul,
        mul_comm ((nu : Graded.Poly K) ^ k) ((mu : Graded.Poly K) ^ k), sub_self]
    · rw [hzetaa]
      have h3 := (Graded.GradedPresentation.of K _).smul_mem_piece (nu_pow_mem (K := K) k) p.2.1.2
      have h4 := (Graded.GradedPresentation.of K _).smul_mem_piece (mu_pow_mem (K := K) k) p.2.2.2
      have h5 := Submodule.sub_mem _ h3 h4
      rwa [show (k : ℤ) + (k : ℤ) = 2 * (k : ℤ) by ring] at h5
  -- the vanishing of the obstruction puts `x` in `ad_P F₀`
  have hU0le : (U ⊓ LinearMap.ker zeta').map pT
      ≤ ((Graded.GradedPresentation.of K (shiftSrc n)).piece 0).map
          ((adP N M).restrictScalars K) := by
    rintro _ ⟨p, ⟨hp, hz⟩, rfl⟩
    obtain ⟨h1, h2⟩ := (hmemU p).1 hp
    have hzz : zeta p ∈ Zsub := by
      have h0 : Zsub.mkQ (zeta p) = 0 := by rw [← hzeta'a]; exact hz
      rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h0
    rw [hZsub, Submodule.mem_sup] at hzz
    obtain ⟨y, hy, z, hz2, hsum⟩ := hzz
    obtain ⟨α, hα, rfl⟩ := hy
    obtain ⟨β, hβ, rfl⟩ := hz2
    rw [hsnua, hsmua, hzetaa] at hsum
    have hX : (nu : Graded.Poly K) ^ k • (p.2.1 : Fin (n * n) → Graded.Poly K)
        = ((nu : Graded.Poly K) ^ k • α + (mu : Graded.Poly K) ^ k • β)
          + (mu : Graded.Poly K) ^ k • (p.2.2 : Fin (n * n) → Graded.Poly K) := by
      rw [hsum]; abel
    have hkey : (nu : Graded.Poly K) ^ k •
          ((p.2.1 : Fin (n * n) → Graded.Poly K) - α)
        = (mu : Graded.Poly K) ^ k •
          ((p.2.2 : Fin (n * n) → Graded.Poly K) + β) := by
      rw [smul_sub, smul_add, hX]; abel
    have hdvd : ∀ j, (mu : Graded.Poly K) ^ k ∣
        (((p.2.1 : Fin (n * n) → Graded.Poly K) - α) j) := by
      intro j
      have hj := congrFun hkey j
      rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul] at hj
      exact (mu_prime (K := K)).pow_dvd_of_dvd_mul_left k (not_mu_dvd_nu_pow k) ⟨_, hj⟩
    choose w hw using hdvd
    have hwe : (p.2.1 : Fin (n * n) → Graded.Poly K) - α = (mu : Graded.Poly K) ^ k • w := by
      funext j
      rw [Pi.smul_apply, smul_eq_mul, ← hw j]
    have hwF : w ∈ (Graded.GradedPresentation.of K (shiftSrc n)).piece 0 := by
      refine mem_piece_of_mu_pow_smul (e := 0) (k := k) ?_
      rw [← hwe, zero_add]
      exact Submodule.sub_mem _ p.2.1.2 hα.2
    have hα0 : adP N M α = 0 := hα.1
    have hadw : adP N M w = (p.1 : Fin (n * n) → Graded.Poly K) := by
      have h7 : (mu : Graded.Poly K) ^ k • adP N M w
          = (mu : Graded.Poly K) ^ k • (p.1 : Fin (n * n) → Graded.Poly K) := by
        rw [← map_smul, ← hwe, map_sub, h1, hα0, sub_zero]
      exact smul_left_cancel (pow_ne_zero k (mu_prime (K := K)).ne_zero) h7
    exact ⟨w, hwF, by rw [LinearMap.restrictScalars_apply, hadw, hpTa]⟩
  -- the two dimension bounds
  obtain ⟨G, hGcard, hGspan⟩ := hb.exists_span_sub_two k Zsub hmuZ hnuZ
  have hbound1 : Module.finrank K (U.map zeta') ≤ ∑ i, (b i - 1).toNat := by
    have hsub : U.map zeta'
        ≤ Submodule.span K ((G.image Zsub.mkQ : Finset _) :
            Set ((Fin (n * n) → Graded.Poly K) ⧸ Zsub)) := by
      rintro _ ⟨p, hp, rfl⟩
      rw [hzeta'a]
      have h9 : Zsub.mkQ (zeta p) ∈ (Zsub ⊔ Submodule.span K
          (G : Set (Fin (n * n) → Graded.Poly K))).map Zsub.mkQ :=
        ⟨zeta p, hGspan (hzetaC p hp), rfl⟩
      rwa [Submodule.map_sup, Submodule.mkQ_map_self, bot_sup_eq, Submodule.map_span,
        ← Finset.coe_image] at h9
    calc Module.finrank K (U.map zeta')
        ≤ Module.finrank K (Submodule.span K ((G.image Zsub.mkQ : Finset _) :
            Set ((Fin (n * n) → Graded.Poly K) ⧸ Zsub))) :=
          Submodule.finrank_mono (R := K) hsub
      _ ≤ (G.image Zsub.mkQ).card := finrank_span_finset_le_card _
      _ ≤ G.card := Finset.card_image_le
      _ ≤ ∑ i, (b i - 1).toNat := hGcard
  have hbound2 : Module.finrank K ((U ⊓ LinearMap.ker zeta').map pT)
      + ∑ i, (1 - b i).toNat ≤ n * n := by
    have h1 := Submodule.finrank_mono (R := K) hU0le
    have h2 := finrank_map_add_finrank_inf_ker ((adP N M).restrictScalars K)
      ((Graded.GradedPresentation.of K (shiftSrc n)).piece (0 : ℤ))
    have h3 : (Graded.GradedPresentation.of K (shiftSrc n)).piece (0 : ℤ)
          ⊓ LinearMap.ker ((adP N M).restrictScalars K)
        = (Graded.GradedPresentation.of K (shiftSrc n)).sub (centralizerSub N M) 0 := by
      ext z
      exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
    have h4 : Module.finrank K
        ((Graded.GradedPresentation.of K (shiftSrc n)).piece (0 : ℤ)) = n * n := by
      rw [Graded.GradedPresentation.finrank_piece]
      simp [shiftSrc]
    -- `h5` is stated in the `F_0 ∩ ker ad_P` spelling of `C_0`, and `h4` is
    -- rewritten into `h2`, so that `omega` sees one atom for each dimension and
    -- not two: a `Submodule K (of K a).Mod` carries the module instance fixed
    -- when the presentation was elaborated, which is not syntactically the one
    -- instance search finds for `Fin (n * n) → B`, and `omega` matches atoms
    -- syntactically.
    have h5 : ∑ i, (1 - b i).toNat
        ≤ Module.finrank K
            (((Graded.GradedPresentation.of K (shiftSrc n)).piece (0 : ℤ)
              ⊓ LinearMap.ker ((adP N M).restrictScalars K) :
              Submodule K (Fin (n * n) → Graded.Poly K))) := by
      rw [h3]
      exact hb.sum_le_finrank_sub_zero
    rw [h4] at h2
    omega
  -- the rank chain and the arithmetic
  have hchain := finrank_map_le_map_add_map_inf_ker U pT zeta'
  rw [hUT] at hchain
  have hnat : Module.finrank K T + ∑ i, (1 - b i).toNat
      ≤ (∑ i, (b i - 1).toNat) + n * n := by omega
  have hcast : (Module.finrank K T : ℤ) + (∑ i, ((1 - b i).toNat : ℤ))
      ≤ (∑ i, ((b i - 1).toNat : ℤ)) + (n : ℤ) * n := by exact_mod_cast hnat
  have harith : ∀ i : ι, ((b i - 1).toNat : ℤ) - ((1 - b i).toNat : ℤ) = b i - 1 := by
    intro i
    have := hb.b_nonneg i
    omega
  have hsum : (∑ i, ((b i - 1).toNat : ℤ)) - (∑ i, ((1 - b i).toNat : ℤ))
      = (∑ i, b i) - (Fintype.card ι : ℤ) := by
    rw [← Finset.sum_sub_distrib, Finset.sum_congr rfl (fun i _ => harith i),
      Finset.sum_sub_distrib]
    simp
  linarith

/-! ### The rank of the basis is `c(τ)` -/

-- the fraction-field instances make this elaboration heavy
set_option maxHeartbeats 400000 in
/-- **The count of the basis.**  Over the fraction field of `K[t]` the kernel of
`ad_P` has dimension `c(τ)` and is spanned by the dehomogenised basis `u`, so
`c(τ) ≤ #ι`. -/
theorem cType_le_card [Infinite K] (hb : CentralizerBasis N M b u) (τ : Nat.Partition n)
    (hnil : NilpotentPencil N M) (hgen : GenericType N M τ) :
    cType τ ≤ Fintype.card ι := by
  classical
  have hΦinj : Function.Injective
      (algebraMap (Polynomial K) (FractionRing (Polynomial K))) :=
    IsFractionRing.injective (Polynomial K) (FractionRing (Polynomial K))
  set Φ : Polynomial K →+* FractionRing (Polynomial K) :=
    algebraMap (Polynomial K) (FractionRing (Polynomial K)) with hΦ
  set A : Matrix (Fin (n * n)) (Fin (n * n)) (FractionRing (Polynomial K)) :=
    (adMat (pencilPoly N M)).map Φ with hA
  set uu : ι → (Fin (n * n) → FractionRing (Polynomial K)) :=
    fun i j => Φ (Graded.deh K (u i j)) with huu
  -- the generic rank
  have hrank : A.rank = n * n - cType τ := by
    have h := rank_map_adMat_pencilPoly Φ hΦinj N M τ 0 hnil hgen
    rwa [zero_smul, add_zero] at h
  have hnull : Module.finrank (FractionRing (Polynomial K))
      (LinearMap.ker A.mulVecLin) = cType τ := by
    have h := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
    have hdim : Module.finrank (FractionRing (Polynomial K))
        (Fin (n * n) → FractionRing (Polynomial K)) = n * n := by simp
    have hr : A.rank = Module.finrank (FractionRing (Polynomial K))
        (LinearMap.range A.mulVecLin) := rfl
    have h2 := cType_le τ
    omega
  -- the kernel is spanned by the basis
  have hspan : LinearMap.ker A.mulVecLin
      ≤ Submodule.span (FractionRing (Polynomial K)) (Set.range uu) := by
    intro v hv
    have hv0 : A *ᵥ v = 0 := by
      have h := LinearMap.mem_ker.1 hv
      rwa [Matrix.mulVecLin_apply] at h
    -- clear denominators
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite
      (nonZeroDivisors (Polynomial K)) v
    have hd' : ∀ j, ∃ y : Polynomial K, Φ y = (d : Polynomial K) • v j := by
      intro j
      obtain ⟨y, hy⟩ := hd j
      exact ⟨y, hy⟩
    choose w hw using hd'
    have hdne : Φ (d : Polynomial K) ≠ 0 := by
      intro h0
      refine nonZeroDivisors.coe_ne_zero d (hΦinj ?_)
      rw [h0, map_zero]
    have hwc : ∀ j, Φ (w j) = Φ (d : Polynomial K) * v j := by
      intro j
      rw [hw j, Algebra.smul_def]
    -- `w` is in the kernel over `K[t]`
    have hwker : adMat (pencilPoly N M) *ᵥ w = 0 := by
      funext i
      show (adMat (pencilPoly N M) *ᵥ w) i = 0
      apply hΦinj
      rw [map_zero, RingHom.map_mulVec Φ _ w i]
      have hfun : (Φ ∘ w) = fun j => Φ (d : Polynomial K) * v j := by
        funext j; exact hwc j
      rw [hfun]
      have hcalc : ((adMat (pencilPoly N M)).map Φ
            *ᵥ fun j => Φ (d : Polynomial K) * v j) i
          = Φ (d : Polynomial K) * (A *ᵥ v) i := by
        simp only [hA, Matrix.mulVec, dotProduct, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [hcalc, hv0]
      simp
    -- homogenise
    obtain ⟨e, he⟩ := Graded.exists_mem_Ppiece (K := K) (shiftSrc n) w
    obtain ⟨x, hxF, hxdeh⟩ := he
    have hxC : x ∈ centralizerSub N M := by
      have h1 : adP N M x ∈ (Graded.GradedPresentation.of K (shiftTgt n)).piece e :=
        adP_mem_piece N M hxF
      have h2 : Graded.dehVec K (n * n) (adP N M x) = 0 := by
        funext i
        have h3 := RingHom.map_mulVec (Graded.deh K).toRingHom (adMat (pencil N M)) x i
        have h4 : (adMat (pencil N M)).map (Graded.deh K).toRingHom
            = adMat (pencilPoly N M) := by
          rw [← adMat_map, map_deh_pencil]
        have h5 : ((Graded.deh K).toRingHom ∘ x) = w := by
          rw [← hxdeh]; funext j; rfl
        rw [h4, h5] at h3
        show ((Graded.deh K).toRingHom) ((adMat (pencil N M) *ᵥ x) i) = 0
        rw [h3, hwker]
        rfl
      refine LinearMap.mem_ker.2 (Graded.dehVec_injOn (a := shiftTgt n) (e := e) h1
        (Submodule.zero_mem _) ?_)
      rw [h2, map_zero]
    -- expand in the basis
    have hxspan : x ∈ Submodule.span (Graded.Poly K) (Set.range u) := by
      rw [hb.span]; exact hxC
    obtain ⟨c, hc⟩ :=
      (Submodule.mem_span_range_iff_exists_fun (Graded.Poly K)).1 hxspan
    have hwj : ∀ j, Φ (w j) = ∑ i, Φ (Graded.deh K (c i)) * uu i j := by
      intro j
      have h1 : w j = Graded.deh K (x j) := by rw [← hxdeh]; rfl
      have h2 : x j = ∑ i, c i * u i j := by
        rw [← hc]
        simp [Finset.sum_apply]
      rw [h1, h2, map_sum, map_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_mul, map_mul]
    have hcomb : (fun j => Φ (w j)) ∈
        Submodule.span (FractionRing (Polynomial K)) (Set.range uu) := by
      have hrw : (fun j => Φ (w j)) = ∑ i, Φ (Graded.deh K (c i)) • uu i := by
        funext j
        rw [hwj j, Finset.sum_apply]
        exact Finset.sum_congr rfl fun i _ => rfl
      rw [hrw]
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    have hvv : v = (Φ (d : Polynomial K))⁻¹ • (fun j => Φ (w j)) := by
      funext j
      rw [Pi.smul_apply, smul_eq_mul, hwc j, ← mul_assoc, inv_mul_cancel₀ hdne, one_mul]
    rw [hvv]
    exact Submodule.smul_mem _ _ hcomb
  -- conclude
  have hcoe : Set.range uu
      = ((Finset.univ.image uu : Finset (Fin (n * n) → FractionRing (Polynomial K))) :
          Set (Fin (n * n) → FractionRing (Polynomial K))) := by
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  rw [hcoe] at hspan
  calc cType τ = Module.finrank (FractionRing (Polynomial K))
        (LinearMap.ker A.mulVecLin) := hnull.symm
    _ ≤ Module.finrank (FractionRing (Polynomial K)) (Submodule.span
        (FractionRing (Polynomial K)) ((Finset.univ.image uu : Finset _) : Set _)) :=
      Submodule.finrank_mono (R := FractionRing (Polynomial K)) hspan
    _ ≤ (Finset.univ.image uu).card := finrank_span_finset_le_card _
    _ ≤ (Finset.univ : Finset ι).card := Finset.card_image_le
    _ = Fintype.card ι := Finset.card_univ

/-! ### The PID step of the local–global principle -/

theorem eq_zero_of_forall_pow_dvd {t₀ : K} {p : Polynomial K}
    (h : ∀ e : ℕ, (Polynomial.X - Polynomial.C t₀) ^ e ∣ p) : p = 0 := by
  by_contra hp
  have hmon : ((Polynomial.X - Polynomial.C t₀) ^ (p.natDegree + 1)).Monic :=
    (Polynomial.monic_X_sub_C t₀).pow _
  have hle := hmon.natDegree_le_of_dvd hp (h (p.natDegree + 1))
  rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one] at hle
  omega

/-- Over an algebraically closed field: if `β` is congruent to a multiple of `α`
modulo every power of every `X - t₀`, then `α ∣ β`. -/
theorem dvd_of_forall_pow_sub_dvd [IsAlgClosed K] {α β : Polynomial K}
    (h : ∀ (t₀ : K) (e : ℕ), ∃ c : Polynomial K,
      (Polynomial.X - Polynomial.C t₀) ^ e ∣ β - α * c) : α ∣ β := by
  classical
  rcases eq_or_ne α 0 with rfl | hα
  · have hβ : β = 0 := by
      refine eq_zero_of_forall_pow_dvd (t₀ := 0) fun e => ?_
      obtain ⟨c, hc⟩ := h 0 e
      simpa using hc
    simp [hβ]
  · obtain ⟨α₁, hα₁⟩ : EuclideanDomain.gcd α β ∣ α := EuclideanDomain.gcd_dvd_left α β
    by_cases hu : IsUnit α₁
    · obtain ⟨v, hv⟩ := isUnit_iff_exists_inv.1 hu
      refine dvd_trans ⟨v, ?_⟩ (EuclideanDomain.gcd_dvd_right α β)
      calc EuclideanDomain.gcd α β
          = EuclideanDomain.gcd α β * (α₁ * v) := by rw [hv, mul_one]
        _ = EuclideanDomain.gcd α β * α₁ * v := (mul_assoc _ _ _).symm
        _ = α * v := by rw [← hα₁]
    · exfalso
      have hα₁0 : α₁ ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at hα₁
        exact hα hα₁
      have hdeg : α₁.degree ≠ 0 := fun h0 => hu (Polynomial.isUnit_iff_degree_eq_zero.2 h0)
      obtain ⟨t₀, ht₀⟩ := IsAlgClosed.exists_root α₁ hdeg
      obtain ⟨c, hc⟩ := h t₀ (Polynomial.rootMultiplicity t₀ α)
      have h1 : (Polynomial.X - Polynomial.C t₀) ^ (Polynomial.rootMultiplicity t₀ α) ∣ α :=
        Polynomial.pow_rootMultiplicity_dvd α t₀
      have h2 : (Polynomial.X - Polynomial.C t₀) ^ (Polynomial.rootMultiplicity t₀ α) ∣ β := by
        have hsum := dvd_add hc (h1.mul_right c)
        simpa using hsum
      have h3 : (Polynomial.X - Polynomial.C t₀) ^ (Polynomial.rootMultiplicity t₀ α)
          ∣ EuclideanDomain.gcd α β := EuclideanDomain.dvd_gcd h1 h2
      have h4 : (Polynomial.X - Polynomial.C t₀) ∣ α₁ := Polynomial.dvd_iff_isRoot.2 ht₀
      have h5 : (Polynomial.X - Polynomial.C t₀) ^ (Polynomial.rootMultiplicity t₀ α + 1) ∣ α := by
        have hstep : (Polynomial.X - Polynomial.C t₀) ^ (Polynomial.rootMultiplicity t₀ α + 1)
            ∣ EuclideanDomain.gcd α β * α₁ := by
          rw [pow_succ]
          exact mul_dvd_mul h3 h4
        rwa [← hα₁] at hstep
      exact Polynomial.pow_rootMultiplicity_not_dvd hα t₀ h5

/-- **The local–global principle over `K[t]`** (`IsAlgClosed K`): a vector that
is congruent to the submodule `N` modulo every power of every `X - t₀` lies
in `N`.  Proved by Smith normal form. -/
theorem mem_of_forall_pow_dvd_sub [IsAlgClosed K] {m : ℕ}
    (Nsub : Submodule (Polynomial K) (Fin m → Polynomial K))
    (y : Fin m → Polynomial K)
    (h : ∀ (t₀ : K) (e : ℕ), ∃ z ∈ Nsub, ∀ j,
      (Polynomial.X - Polynomial.C t₀) ^ e ∣ (y j - z j)) :
    y ∈ Nsub := by
  classical
  obtain ⟨r, snf⟩ := Submodule.smithNormalForm (Pi.basisFun (Polynomial K) (Fin m)) Nsub
  have hrepr : ∀ (t₀ : K) (e : ℕ), ∃ z ∈ Nsub, ∀ j,
      (Polynomial.X - Polynomial.C t₀) ^ e ∣ (snf.bM.repr y j - snf.bM.repr z j) := by
    intro t₀ e
    obtain ⟨z, hz, hd⟩ := h t₀ e
    refine ⟨z, hz, fun j => ?_⟩
    choose w hw using hd
    have hyz : y - z = (Polynomial.X - Polynomial.C t₀) ^ e • w := by
      funext l
      rw [Pi.smul_apply, smul_eq_mul, ← hw l]
      rfl
    have hsub : snf.bM.repr (y - z) j = snf.bM.repr y j - snf.bM.repr z j := by
      rw [map_sub]
      rfl
    rw [← hsub, hyz, map_smul]
    simp only [Finsupp.smul_apply, smul_eq_mul]
    exact dvd_mul_right _ _
  have hzero : ∀ j, j ∉ Set.range snf.f → snf.bM.repr y j = 0 := by
    intro j hj
    refine eq_zero_of_forall_pow_dvd (t₀ := 0) fun e => ?_
    obtain ⟨z, hz, hdd⟩ := hrepr 0 e
    have h0 : snf.bM.repr z j = 0 := snf.repr_eq_zero_of_notMem_range ⟨z, hz⟩ hj
    have hj' := hdd j
    rwa [h0, sub_zero] at hj'
  have hdvd : ∀ i, snf.a i ∣ snf.bM.repr y (snf.f i) := by
    intro i
    refine dvd_of_forall_pow_sub_dvd fun t₀ e => ?_
    obtain ⟨z, hz, hdd⟩ := hrepr t₀ e
    refine ⟨snf.bN.repr ⟨z, hz⟩ i, ?_⟩
    have hzi : snf.bM.repr z (snf.f i) = snf.a i * snf.bN.repr ⟨z, hz⟩ i := by
      rw [snf.repr_apply_embedding_eq_repr_smul ⟨z, hz⟩, map_smul]
      simp only [Finsupp.smul_apply, smul_eq_mul]
    rw [← hzi]
    exact hdd (snf.f i)
  have himg : ∑ j : Fin m, (snf.bM.repr y j) • snf.bM j
      = ∑ i : Fin r, (snf.bM.repr y (snf.f i)) • snf.bM (snf.f i) := by
    have h1 : ∑ j ∈ Finset.univ.image snf.f, (snf.bM.repr y j) • snf.bM j
        = ∑ i : Fin r, (snf.bM.repr y (snf.f i)) • snf.bM (snf.f i) :=
      Finset.sum_image (fun x _ y _ hxy => snf.f.injective hxy)
    rw [← h1]
    refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    intro j _ hj
    have hjr : j ∉ Set.range snf.f := by
      rintro ⟨i, hi⟩
      exact hj (Finset.mem_image.2 ⟨i, Finset.mem_univ i, hi⟩)
    rw [hzero j hjr, zero_smul]
  choose c hc using hdvd
  have hy : y = ∑ i : Fin r, c i • ((snf.bN i : Fin m → Polynomial K)) := by
    conv_lhs => rw [← snf.bM.sum_repr y]
    rw [himg]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hc i, snf.snf i, smul_smul, mul_comm]
  rw [hy]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (snf.bN i).2

end Count

/-! ### The local–global principle in the `μ`-chart -/

section Local

variable (N M : Matrix (Fin n) (Fin n) K)

/-- Dehomogenising `ad_P`: `deh ∘ ad_P = ad_{N + tM} ∘ deh`. -/
theorem dehVec_adP (x : Fin (n * n) → Graded.Poly K) :
    Graded.dehVec K (n * n) (adP N M x)
      = adMat (pencilPoly N M) *ᵥ Graded.dehVec K (n * n) x := by
  have h4 : (adMat (pencil N M)).map (Graded.deh K).toRingHom = adMat (pencilPoly N M) := by
    rw [← adMat_map, map_deh_pencil]
  have hc : ((Graded.deh K).toRingHom ∘ x) = Graded.dehVec K (n * n) x := by
    funext j; rfl
  funext i
  show (Graded.deh K).toRingHom ((adMat (pencil N M) *ᵥ x) i)
      = (adMat (pencilPoly N M) *ᵥ Graded.dehVec K (n * n) x) i
  rw [RingHom.map_mulVec (Graded.deh K).toRingHom (adMat (pencil N M)) x i, h4, hc]

/-- The image of `ad_{N + tM}` over `K[t]` lies in `Ŝ = S[μ⁻¹]₀`. -/
theorem mulVec_mem_Shat_adRange (w : Fin (n * n) → Polynomial K) :
    adMat (pencilPoly N M) *ᵥ w ∈ Graded.Shat K (adRange N M) := by
  obtain ⟨e, x, hxF, hxdeh⟩ := Graded.exists_mem_Ppiece (K := K) (shiftSrc n) w
  refine Submodule.subset_span ⟨adP N M x, LinearMap.mem_range_self (adP N M) x, ?_⟩
  rw [dehVec_adP, hxdeh]

/-- **`lem:les`, the `μ`-chart.**  A degree-`0` element of `F'` whose
dehomogenisation lies in `Ŝ` is pushed into `S = im ad_P` by a power of `μ`. -/
theorem exists_mu_pow_smul_mem_adRange {q : Fin (n * n) → Graded.Poly K}
    (hq : q ∈ (Graded.GradedPresentation.of K (shiftTgt n)).piece 0)
    (hy : Graded.dehVec K (n * n) q ∈ Graded.Shat K (adRange N M)) :
    ∃ k : ℕ, (mu : Graded.Poly K) ^ k • q ∈ adRange N M := by
  obtain ⟨e, he⟩ := (Graded.mem_Shat_iff (isGraded_adRange N M)).1 hy
  obtain ⟨z, hz, hzd⟩ := Graded.map_dehVec_sub_mono (le_max_left e 0) he
  refine ⟨(max e 0).toNat, ?_⟩
  have hmem : (mu : Graded.Poly K) ^ (max e 0).toNat • q
      ∈ (Graded.GradedPresentation.of K (shiftTgt n)).piece (max e 0) := by
    have h := Graded.mu_pow_smul_mem_piece hq (max e 0).toNat
    rwa [show (0 : ℤ) + (((max e 0).toNat : ℤ)) = max e 0 by omega] at h
  have heq : (mu : Graded.Poly K) ^ (max e 0).toNat • q = z :=
    Graded.dehVec_injOn hmem (Submodule.mem_inf.1 hz).2
      (by rw [Graded.dehVec_mu_pow_smul, hzd])
  rw [heq]
  exact (Submodule.mem_inf.1 hz).1

/-- **The local approximation at a finite point.**  If the direction `Q` is a
commutator with the pencil in the chart at `t₀`, then its dehomogenisation
agrees with an element of `Ŝ` to order `e` at `t₀`. -/
theorem exists_approx_of_commutator (Q : Matrix (Fin n) (Fin n) (Graded.Poly K)) (t₀ : K)
    {A : Matrix (Fin n) (Fin n) (PowerSeries K)}
    (hA : Qat Q t₀ = Pat N M t₀ * A - A * Pat N M t₀) (e : ℕ) :
    ∃ z ∈ Graded.Shat K (adRange N M), ∀ j,
      (Polynomial.X - Polynomial.C t₀) ^ e
        ∣ (Graded.dehVec K (n * n) (vecMat Q) j - z j) := by
  classical
  have hap : ∀ f : Graded.Poly K,
      Graded.atPoint t₀ f = Graded.iota K t₀ (Graded.deh K f) := by
    intro f
    conv_lhs => rw [Graded.atPoint_eq_comp]
    rfl
  have hPat : Pat N M t₀ = (pencilPoly N M).map (Graded.iota K t₀) := by
    refine Matrix.ext fun i j => ?_
    show Graded.atPoint t₀ (pencil N M i j) = Graded.iota K t₀ (pencilPoly N M i j)
    rw [← map_deh_pencil, Matrix.map_apply]
    exact hap _
  have hadM : adMat (Pat N M t₀) = (adMat (pencilPoly N M)).map (Graded.iota K t₀) := by
    rw [hPat, adMat_map]
  have hmul : (adMat (pencilPoly N M)).map (Graded.iota K t₀) *ᵥ vecMat A
      = vecMat (Qat Q t₀) := by
    rw [← hadM, adMat_mulVec, ← hA]
  have hQvec : ∀ a, vecMat (Qat Q t₀) a
      = Graded.iota K t₀ (Graded.dehVec K (n * n) (vecMat Q) a) := by
    intro a
    show Graded.atPoint t₀ (vecMat Q a) = Graded.iota K t₀ (Graded.deh K (vecMat Q a))
    exact hap _
  obtain ⟨w, hw⟩ : ∃ w : Fin (n * n) → Polynomial K, ∀ j,
      w j = (PowerSeries.trunc e (vecMat A j)).comp (Polynomial.X - Polynomial.C t₀) :=
    ⟨_, fun _ => rfl⟩
  have hdvd : ∀ j, (PowerSeries.X : PowerSeries K) ^ e
      ∣ vecMat A j - Graded.iota K t₀ (w j) := by
    intro j
    rw [hw j, Graded.iota_comp_sub]
    exact Graded.X_pow_dvd_sub_trunc e _
  refine ⟨adMat (pencilPoly N M) *ᵥ w, mulVec_mem_Shat_adRange N M w, fun j => ?_⟩
  have hcomp : ((Graded.iota K t₀) ∘ w) = fun l => Graded.iota K t₀ (w l) := rfl
  have hkey : ((adMat (pencilPoly N M)).map (Graded.iota K t₀) *ᵥ vecMat A) j
      - ((adMat (pencilPoly N M)).map (Graded.iota K t₀)
          *ᵥ fun l => Graded.iota K t₀ (w l)) j
      = ((adMat (pencilPoly N M)).map (Graded.iota K t₀)
          *ᵥ (vecMat A - fun l => Graded.iota K t₀ (w l))) j := by
    rw [Matrix.mulVec_sub, Pi.sub_apply]
  rw [← Graded.X_pow_dvd_iota_iff t₀ e, map_sub,
    RingHom.map_mulVec (Graded.iota K t₀) (adMat (pencilPoly N M)) w j, ← hQvec j, ← hmul,
    hcomp, hkey]
  simp only [Matrix.mulVec, dotProduct, Pi.sub_apply]
  exact Finset.dvd_sum fun l _ => Dvd.dvd.mul_left (hdvd l) _

/-- **`lem:les`, the `μ`-chart, assembled.**  A degree-`0` direction that is a
commutator with the pencil in every finite chart is pushed into `S` by a power
of `μ`. -/
theorem exists_mu_pow_smul_mem_adRange_of_local [IsAlgClosed K]
    (Q : Matrix (Fin n) (Fin n) (Graded.Poly K))
    (hQ : vecMat Q ∈ (Graded.GradedPresentation.of K (shiftTgt n)).piece 0)
    (hloc : ∀ t₀ : K, ∃ A, Qat Q t₀ = Pat N M t₀ * A - A * Pat N M t₀) :
    ∃ k : ℕ, (mu : Graded.Poly K) ^ k • vecMat Q ∈ adRange N M := by
  refine exists_mu_pow_smul_mem_adRange N M hQ
    (mem_of_forall_pow_dvd_sub _ _ fun t₀ e => ?_)
  obtain ⟨A, hA⟩ := hloc t₀
  exact exists_approx_of_commutator N M Q t₀ hA e

end Local

/-! ### The chart at infinity, via the swap `μ ↔ ν` -/

theorem swapVec_adP (N M : Matrix (Fin n) (Fin n) K) (x : Fin (n * n) → Graded.Poly K) :
    Graded.swapVec K (n * n) (adP N M x) = adP M N (Graded.swapVec K (n * n) x) := by
  have hc : ((swapHom K) ∘ x) = Graded.swapVec K (n * n) x := by funext j; rfl
  funext i
  show swapHom K ((adMat (pencil N M) *ᵥ x) i)
      = (adMat (pencil M N) *ᵥ Graded.swapVec K (n * n) x) i
  rw [RingHom.map_mulVec (swapHom K) (adMat (pencil N M)) x i, ← adMat_map,
    map_swapHom_pencil, hc]

theorem swapVec_mem_adRange (N M : Matrix (Fin n) (Fin n) K)
    {x : Fin (n * n) → Graded.Poly K} (hx : x ∈ adRange N M) :
    Graded.swapVec K (n * n) x ∈ adRange M N := by
  obtain ⟨z, rfl⟩ := hx
  exact ⟨Graded.swapVec K (n * n) z, (swapVec_adP N M z).symm⟩

theorem Qat_map_swapHom_zero (Q : Matrix (Fin n) (Fin n) (Graded.Poly K)) :
    Qat (Q.map (swapHom K)) 0 = Q.map atInf := by
  refine Matrix.ext fun i j => ?_
  show Graded.atPoint (0 : K) (swapHom K (Q i j)) = atInf (Q i j)
  rw [← RingHom.comp_apply, atPoint_zero_comp_swapHom]

/-- **`lem:les`, the `ν`-chart.**  Given the `μ`-chart conclusion and the
commutator relation at infinity, a power of `ν` also pushes the direction into
`S`.  Off `t = ∞` the swapped chart needs no new geometry: `μ^k q ∈ S` already
gives the approximation, by coprimality of `t^k` and `(t − t₀)^e`. -/
theorem exists_nu_pow_smul_mem_adRange_of_local [IsAlgClosed K]
    (N M : Matrix (Fin n) (Fin n) K) (Q : Matrix (Fin n) (Fin n) (Graded.Poly K))
    (hQ : vecMat Q ∈ (Graded.GradedPresentation.of K (shiftTgt n)).piece 0) {k : ℕ}
    (hk : (mu : Graded.Poly K) ^ k • vecMat Q ∈ adRange N M)
    (hinf : ∃ A, Q.map atInf = PatInf N M * A - A * PatInf N M) :
    ∃ l : ℕ, (nu : Graded.Poly K) ^ l • vecMat Q ∈ adRange N M := by
  classical
  have hvs : vecMat (Q.map (swapHom K)) = Graded.swapVec K (n * n) (vecMat Q) := by
    funext a; rfl
  have hQs : vecMat (Q.map (swapHom K))
      ∈ (Graded.GradedPresentation.of K (shiftTgt n)).piece 0 := by
    rw [hvs]; exact Graded.swapVec_mem_piece hQ
  have hks : (nu : Graded.Poly K) ^ k • vecMat (Q.map (swapHom K)) ∈ adRange M N := by
    have h := swapVec_mem_adRange N M hk
    rwa [Graded.swapVec_smul, map_pow, Graded.swapAlg_mu, ← hvs] at h
  have hys : (Polynomial.X : Polynomial K) ^ k •
      Graded.dehVec K (n * n) (vecMat (Q.map (swapHom K)))
        ∈ Graded.Shat K (adRange M N) := by
    have h : Graded.dehVec K (n * n)
        ((nu : Graded.Poly K) ^ k • vecMat (Q.map (swapHom K)))
        ∈ Graded.Shat K (adRange M N) := Submodule.subset_span ⟨_, hks, rfl⟩
    rwa [Graded.dehVec_smul, map_pow, Graded.deh_nu] at h
  have happ : ∀ (t₀ : K) (e : ℕ), ∃ z ∈ Graded.Shat K (adRange M N), ∀ j,
      (Polynomial.X - Polynomial.C t₀) ^ e
        ∣ (Graded.dehVec K (n * n) (vecMat (Q.map (swapHom K))) j - z j) := by
    intro t₀ e
    rcases eq_or_ne t₀ 0 with rfl | ht
    · obtain ⟨A, hA⟩ := hinf
      refine exists_approx_of_commutator (A := A) M N (Q.map (swapHom K)) 0 ?_ e
      rw [Qat_map_swapHom_zero, ← PatInf_eq_Pat_zero]
      exact hA
    · have hcop1 : IsCoprime (Polynomial.X : Polynomial K)
          (Polynomial.X - Polynomial.C t₀) := by
        refine ⟨Polynomial.C t₀⁻¹, -Polynomial.C t₀⁻¹, ?_⟩
        have hr : Polynomial.C t₀⁻¹ * Polynomial.X
            + -Polynomial.C t₀⁻¹ * (Polynomial.X - Polynomial.C t₀)
            = Polynomial.C t₀⁻¹ * Polynomial.C t₀ := by ring
        rw [hr, ← Polynomial.C_mul, inv_mul_cancel₀ ht, Polynomial.C_1]
      obtain ⟨α, β, hαβ⟩ := hcop1.pow (m := k) (n := e)
      refine ⟨α • ((Polynomial.X : Polynomial K) ^ k •
        Graded.dehVec K (n * n) (vecMat (Q.map (swapHom K)))),
        Submodule.smul_mem _ _ hys, fun j => ?_⟩
      refine ⟨β * Graded.dehVec K (n * n) (vecMat (Q.map (swapHom K))) j, ?_⟩
      show Graded.dehVec K (n * n) (vecMat (Q.map (swapHom K))) j
          - α * ((Polynomial.X : Polynomial K) ^ k
            * Graded.dehVec K (n * n) (vecMat (Q.map (swapHom K))) j)
        = (Polynomial.X - Polynomial.C t₀) ^ e
            * (β * Graded.dehVec K (n * n) (vecMat (Q.map (swapHom K))) j)
      calc Graded.dehVec K (n * n) (vecMat (Q.map (swapHom K))) j
            - α * ((Polynomial.X : Polynomial K) ^ k
              * Graded.dehVec K (n * n) (vecMat (Q.map (swapHom K))) j)
          = (α * (Polynomial.X : Polynomial K) ^ k
              + β * (Polynomial.X - Polynomial.C t₀) ^ e)
            * Graded.dehVec K (n * n) (vecMat (Q.map (swapHom K))) j
            - α * ((Polynomial.X : Polynomial K) ^ k
              * Graded.dehVec K (n * n) (vecMat (Q.map (swapHom K))) j) := by
            rw [hαβ, one_mul]
        _ = (Polynomial.X - Polynomial.C t₀) ^ e
            * (β * Graded.dehVec K (n * n) (vecMat (Q.map (swapHom K))) j) := by ring
  obtain ⟨l, hl⟩ := exists_mu_pow_smul_mem_adRange M N hQs
    (mem_of_forall_pow_dvd_sub _ _ happ)
  refine ⟨l, ?_⟩
  have h := swapVec_mem_adRange M N hl
  rwa [Graded.swapVec_smul, map_pow, Graded.swapAlg_mu, hvs, Graded.swapVec_swapVec] at h

/-! ### A uniform exponent -/

/-- On a finite-dimensional space of elements each of which some power of `g`
pushes into `S`, one power works for all of them. -/
theorem exists_pow_smul_mem_of_finiteDimensional {r : ℕ}
    (Ssub : Submodule (Graded.Poly K) (Fin r → Graded.Poly K)) (g : Graded.Poly K)
    (T : Submodule K (Fin r → Graded.Poly K)) [FiniteDimensional K T]
    (h : ∀ x ∈ T, ∃ k : ℕ, g ^ k • x ∈ Ssub) :
    ∃ k : ℕ, ∀ x ∈ T, g ^ k • x ∈ Ssub := by
  classical
  obtain ⟨s, hs⟩ := (Submodule.fg_top T).1 Module.Finite.fg_top
  have hsT : ∀ x ∈ s, ∃ k : ℕ, g ^ k • x ∈ Ssub := by
    intro x hx
    exact h x (hs ▸ Submodule.subset_span hx)
  choose! kf hkf using hsT
  refine ⟨s.sup kf, fun x hx => ?_⟩
  rw [← hs] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
      have hle : kf y ≤ s.sup kf := Finset.le_sup hy
      rw [show g ^ (s.sup kf) = g ^ (s.sup kf - kf y) * g ^ (kf y) by
        rw [← pow_add]; congr 1; omega, mul_smul]
      exact Ssub.smul_mem _ (hkf y hy)
  | zero => simp
  | add y z _ _ ihy ihz =>
      rw [smul_add]
      exact Ssub.add_mem ihy ihz
  | smul c y _ ih =>
      rw [smul_comm, ← IsScalarTower.algebraMap_smul (Graded.Poly K) c]
      exact Ssub.smul_mem _ ih

/-! ### `thm:realized-bound` -/

variable (K n) in
/-- The pencil direction `(Ṅ, Ṁ) ↦ μ Ṅ + ν Ṁ`, in the coordinates `vecMat`. -/
def pencilVec :
    (Matrix (Fin n) (Fin n) K × Matrix (Fin n) (Fin n) K) →ₗ[K]
      (Fin (n * n) → Graded.Poly K) where
  toFun p := vecMat (pencil p.1 p.2)
  map_add' p q := by
    funext a
    simp only [vecMat_apply, pencil, Matrix.of_apply, Prod.fst_add, Prod.snd_add,
      Matrix.add_apply, map_add, Pi.add_apply]
    ring
  map_smul' c p := by
    funext a
    simp only [vecMat_apply, pencil, Matrix.of_apply, Prod.smul_fst, Prod.smul_snd,
      Matrix.smul_apply, smul_eq_mul, map_mul, Pi.smul_apply, RingHom.id_apply,
      MvPolynomial.smul_eq_C_mul]
    ring

theorem pencilVec_injective : Function.Injective (pencilVec K n) := by
  have hd : ∀ (N M : Matrix (Fin n) (Fin n) K) (i j : Fin n),
      Graded.deh K (pencil N M i j)
        = Polynomial.C (N i j) + Polynomial.C (M i j) * Polynomial.X := by
    intro N M i j
    simp only [pencil, Matrix.of_apply, map_add, map_mul, Graded.deh_C, Graded.deh_mu,
      Graded.deh_nu, mul_one]
  intro p q h
  have hp : pencil p.1 p.2 = pencil q.1 q.2 := vecMat_injective h
  have hcoeff : ∀ i j, Polynomial.C (p.1 i j) + Polynomial.C (p.2 i j) * Polynomial.X
      = Polynomial.C (q.1 i j) + Polynomial.C (q.2 i j) * Polynomial.X := by
    intro i j
    rw [← hd, ← hd, hp]
  refine Prod.ext ?_ ?_ <;> refine Matrix.ext fun i j => ?_
  · have h0 := congrArg (fun r : Polynomial K => r.coeff 0) (hcoeff i j)
    simpa using h0
  · have h1 := congrArg (fun r : Polynomial K => r.coeff 1) (hcoeff i j)
    simpa using h1

theorem pencilVec_mem_piece
    (p : Matrix (Fin n) (Fin n) K × Matrix (Fin n) (Fin n) K) :
    pencilVec K n p ∈ (Graded.GradedPresentation.of K (shiftTgt n)).piece 0 := by
  refine (Graded.GradedPresentation.of K _).mem_piece.2 fun j => ?_
  rw [show (0 : ℤ) - shiftTgt n j = 1 by simp only [shiftTgt]; ring]
  exact pencil_mem_Bpiece p.1 p.2 _ _

/-- **`thm:realized-bound`.**  A space of pencil directions that are local
commutators at every point of `ℙ¹` has dimension at most `n² − c(τ) + ∑ bᵢ`,
`b` the degrees of a homogeneous basis of the centraliser `C`.  (It is
`dim 𝒩` for `𝒩 = Γ₀(im ad_P)`, by the six-term sequence of `lem:les` and the
local–global description of `Γ₀`.) -/
theorem realizedDimStmt [IsAlgClosed K] :
    ∀ (N M : Matrix (Fin n) (Fin n) K) (τ : Nat.Partition n),
      NilpotentPencil N M → GenericType N M τ →
    ∀ {ι : Type} [Fintype ι] (b : ι → ℤ) (u : ι → (Fin (n * n) → Graded.Poly K)),
      CentralizerBasis N M b u →
    ∀ T : Submodule K (Matrix (Fin n) (Fin n) K × Matrix (Fin n) (Fin n) K),
      (∀ p ∈ T, IsLocalCommutator N M (pencil p.1 p.2)) →
      (Module.finrank K T : ℤ) + cType τ ≤ n * n + ∑ i, b i := by
  intro N M τ hnil hgen ι _ b u hb T hT
  classical
  have hT'le : T.map (pencilVec K n) ≤ (Graded.GradedPresentation.of K (shiftTgt n)).piece 0 := by
    rintro _ ⟨p, _, rfl⟩
    exact pencilVec_mem_piece p
  have : FiniteDimensional K (T.map (pencilVec K n)) :=
    Submodule.finiteDimensional_of_le hT'le
  have hrank : Module.finrank K (T.map (pencilVec K n)) = Module.finrank K T :=
    ((Submodule.equivMapOfInjective (pencilVec K n) pencilVec_injective T).finrank_eq).symm
  have hmu : ∀ x ∈ T.map (pencilVec K n),
      ∃ k : ℕ, (mu : Graded.Poly K) ^ k • x ∈ adRange N M := by
    rintro _ ⟨p, hp, rfl⟩
    exact exists_mu_pow_smul_mem_adRange_of_local N M (pencil p.1 p.2)
      (pencilVec_mem_piece p) (hT p hp).1
  obtain ⟨k₁, hk₁⟩ :=
    exists_pow_smul_mem_of_finiteDimensional (adRange N M) mu (T.map (pencilVec K n)) hmu
  have hnu : ∀ x ∈ T.map (pencilVec K n),
      ∃ l : ℕ, (nu : Graded.Poly K) ^ l • x ∈ adRange N M := by
    rintro _ ⟨p, hp, rfl⟩
    exact exists_nu_pow_smul_mem_adRange_of_local N M (pencil p.1 p.2)
      (pencilVec_mem_piece p) (hk₁ _ ⟨p, hp, rfl⟩) (hT p hp).2
  obtain ⟨k₂, hk₂⟩ :=
    exists_pow_smul_mem_of_finiteDimensional (adRange N M) nu (T.map (pencilVec K n)) hnu
  have hkmu : ∀ x ∈ T.map (pencilVec K n),
      (mu : Graded.Poly K) ^ (max k₁ k₂) • x ∈ adRange N M := by
    intro x hx
    rw [show max k₁ k₂ = (max k₁ k₂ - k₁) + k₁ by omega, pow_add, mul_smul]
    exact (adRange N M).smul_mem _ (hk₁ x hx)
  have hknu : ∀ x ∈ T.map (pencilVec K n),
      (nu : Graded.Poly K) ^ (max k₁ k₂) • x ∈ adRange N M := by
    intro x hx
    rw [show max k₁ k₂ = (max k₁ k₂ - k₂) + k₂ by omega, pow_add, mul_smul]
    exact (adRange N M).smul_mem _ (hk₂ x hx)
  have hcount := finrank_le_of_mu_nu_pow hb (T.map (pencilVec K n)) (max k₁ k₂) hT'le hkmu hknu
  have hc := cType_le_card hb τ hnil hgen
  omega

end Height.Pencil
