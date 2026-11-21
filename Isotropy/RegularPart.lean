/-
The regular part (steps (i)–(iv) of the DVR core in `Isotropy/DVRCore.lean`,
done once over an arbitrary PID): given the kernel-flatness conditions `DCond P Q`, a
single integral matrix `g` implements every flag motion —

    ∀ k, ∀ v ∈ ker P^k,   P^k · (g · v) = D_k(Q) · v.

Consumed twice: over the DVR `𝒪_{ℙ¹,x}` this is `exists_regular_part` (the
`B = A − g` step of the DVR core), and over a field (a field is a PID) it
reduces the D-conditions to the strictly-lowering case in
`commutator_iff_dcond`.

Construction, by induction on the level `m`.  The correction at each level
is `E = ℓ ∘ f₁ ∘ π` where

  * `π` projects `Rⁿ` onto `S_{m+1}` — the quotient `Rⁿ/S_{m+1}` is free
    (`free_quotient`), so `mkQ` splits;
  * `f₁` is `P^m` corestricted onto its image `T = P^m(S_{m+1})`, killing
    `S_m` — which protects the levels already won;
  * `ℓ` lifts the defect `ρ = D_{m+1} − P^{m+1}g` (which factors through
    `T` and lands in `im P^{m+1}` by `DCond`) through `P^{m+1}` — `T` is a
    submodule of `Rⁿ`, hence free, hence projective.
-/
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Isomorphisms
import Isotropy.DPow

namespace Isotropy

open Matrix

variable {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] {n : ℕ}

/-- Step (i), first half: `Rⁿ/S_k` is free — it embeds in `Rⁿ` via `P^k`,
so `quotKerEquivRange` identifies it with a submodule of a free module
over a PID. -/
theorem free_quotient (P : Matrix (Fin n) (Fin n) R) (k : ℕ) :
    Module.Free R ((Fin n → R) ⧸ kerFlag P k) :=
  Module.Free.of_equiv' inferInstance
    (LinearMap.quotKerEquivRange (P ^ k).mulVecLin).symm

/-- The correction step: any linear defect `ρ` on `S_{m+1}` that lands in
`im P^{m+1}` and kills `S_m` is realized as `P^{m+1}·E` for a matrix `E`
whose action on `S_{m+1}` also kills `S_m`. -/
private theorem exists_correction
    (P : Matrix (Fin n) (Fin n) R) (m : ℕ)
    (ρ : ↥(kerFlag P (m + 1)) →ₗ[R] (Fin n → R))
    (hmem : ∀ x, ρ x ∈ LinearMap.range (P ^ (m + 1)).mulVecLin)
    (hker : ∀ x : ↥(kerFlag P (m + 1)), (P ^ m).mulVec x.1 = 0 → ρ x = 0) :
    ∃ E : Matrix (Fin n) (Fin n) R,
      (∀ v (hv : v ∈ kerFlag P (m + 1)),
          (P ^ (m + 1)).mulVec (E.mulVec v) = ρ ⟨v, hv⟩) ∧
      (∀ v, v ∈ kerFlag P (m + 1) → (P ^ m).mulVec v = 0 → E.mulVec v = 0) := by
  have : Module.Free R ((Fin n → R) ⧸ kerFlag P (m + 1)) := free_quotient P (m + 1)
  -- `μ` kills exactly `S_m` inside `S_{m+1}`; its image is a submodule of
  -- `Rⁿ`, hence free, hence projective.
  set μ : ↥(kerFlag P (m + 1)) →ₗ[R] (Fin n → R) :=
    (P ^ m).mulVecLin ∘ₗ (kerFlag P (m + 1)).subtype with hμdef
  have hμ_apply : ∀ x : ↥(kerFlag P (m + 1)), μ x = (P ^ m).mulVec x.1 := fun _ => rfl
  obtain ⟨s₁, hs₁⟩ := μ.rangeRestrict.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr μ.surjective_rangeRestrict)
  set ρ' : ↥(kerFlag P (m + 1)) →ₗ[R] ↥(LinearMap.range (P ^ (m + 1)).mulVecLin) :=
    LinearMap.codRestrict _ ρ hmem with hρ'def
  obtain ⟨ℓ, hℓ⟩ := Module.projective_lifting_property
    (P ^ (m + 1)).mulVecLin.rangeRestrict (ρ' ∘ₗ s₁)
    (P ^ (m + 1)).mulVecLin.surjective_rangeRestrict
  -- `ρ'` is constant along the fibres of `μ`
  have hρ'_fib : ∀ x : ↥(kerFlag P (m + 1)), ρ' (s₁ (μ.rangeRestrict x)) = ρ' x := by
    intro x
    have h2 := LinearMap.congr_fun hs₁ (μ.rangeRestrict x)
    rw [LinearMap.comp_apply, LinearMap.id_apply] at h2
    have h3 : s₁ (μ.rangeRestrict x) - x ∈ LinearMap.ker μ.rangeRestrict := by
      rw [LinearMap.mem_ker, map_sub, h2, sub_self]
    rw [LinearMap.ker_rangeRestrict, LinearMap.mem_ker] at h3
    have h5 : ρ (s₁ (μ.rangeRestrict x) - x) = 0 := by
      refine hker _ ?_
      rw [← hμ_apply]
      exact h3
    have h6 : ρ' (s₁ (μ.rangeRestrict x) - x) = 0 := by
      apply Subtype.ext
      rw [hρ'def, LinearMap.codRestrict_apply]
      simpa using h5
    rw [map_sub, sub_eq_zero] at h6
    exact h6
  -- the projection onto `S_{m+1}`
  obtain ⟨sQ, hsQ⟩ := (kerFlag P (m + 1)).mkQ.exists_rightInverse_of_surjective
    (Submodule.range_mkQ _)
  set π₀ : (Fin n → R) →ₗ[R] (Fin n → R) :=
    LinearMap.id - sQ ∘ₗ (kerFlag P (m + 1)).mkQ with hπ₀def
  have hπmem : ∀ v, π₀ v ∈ kerFlag P (m + 1) := by
    intro v
    have h2 := LinearMap.congr_fun hsQ ((kerFlag P (m + 1)).mkQ v)
    rw [LinearMap.comp_apply, LinearMap.id_apply] at h2
    rw [← Submodule.ker_mkQ (kerFlag P (m + 1)), LinearMap.mem_ker, hπ₀def,
      LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub, h2, sub_self]
  set π : (Fin n → R) →ₗ[R] ↥(kerFlag P (m + 1)) :=
    LinearMap.codRestrict _ π₀ hπmem with hπdef
  have hπ_fix : ∀ v (hv : v ∈ kerFlag P (m + 1)), π v = ⟨v, hv⟩ := by
    intro v hv
    apply Subtype.ext
    rw [hπdef, LinearMap.codRestrict_apply]
    have h0 : (kerFlag P (m + 1)).mkQ v = 0 := by
      rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
      exact hv
    rw [hπ₀def, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, h0,
      map_zero, sub_zero]
  -- assemble
  refine ⟨LinearMap.toMatrix' (ℓ.comp (μ.rangeRestrict.comp π)), ?_, ?_⟩
  · intro v hv
    rw [LinearMap.toMatrix'_mulVec, LinearMap.comp_apply, LinearMap.comp_apply, hπ_fix v hv]
    have h1 := LinearMap.congr_fun hℓ (μ.rangeRestrict ⟨v, hv⟩)
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hρ'_fib ⟨v, hv⟩] at h1
    have h2 := congrArg Subtype.val h1
    rw [hρ'def] at h2
    simpa [Matrix.mulVecLin_apply] using h2
  · intro v hv h0
    rw [LinearMap.toMatrix'_mulVec, LinearMap.comp_apply, LinearMap.comp_apply, hπ_fix v hv]
    have h1 : μ.rangeRestrict ⟨v, hv⟩ = 0 := by
      have h3 : (⟨v, hv⟩ : ↥(kerFlag P (m + 1))) ∈ LinearMap.ker μ.rangeRestrict := by
        rw [LinearMap.ker_rangeRestrict, LinearMap.mem_ker, hμ_apply]
        exact h0
      exact h3
    rw [h1, map_zero]

/-- The bounded regular part: one `g` implementing the flag motions on all
levels `k ≤ m`. -/
theorem exists_regular_g_of_le (P Q : Matrix (Fin n) (Fin n) R) (hD : DCond P Q) (m : ℕ) :
    ∃ g : Matrix (Fin n) (Fin n) R,
      ∀ k ≤ m, ∀ v ∈ kerFlag P k, (P ^ k).mulVec (g.mulVec v) = (dpow P Q k).mulVec v := by
  induction m with
  | zero =>
    refine ⟨0, fun k hk v hv => ?_⟩
    obtain rfl : k = 0 := Nat.le_zero.mp hk
    obtain rfl : v = 0 := by simpa using hv
    simp
  | succ m ih =>
    obtain ⟨g, hg⟩ := ih
    -- the defect of `g` at level `m + 1`
    set ρ : ↥(kerFlag P (m + 1)) →ₗ[R] (Fin n → R) :=
      ((dpow P Q (m + 1)).mulVecLin - (P ^ (m + 1)).mulVecLin ∘ₗ g.mulVecLin) ∘ₗ
        (kerFlag P (m + 1)).subtype with hρdef
    have hρ_apply : ∀ (v) (hv : v ∈ kerFlag P (m + 1)),
        ρ ⟨v, hv⟩ = (dpow P Q (m + 1)).mulVec v - (P ^ (m + 1)).mulVec (g.mulVec v) :=
      fun _ _ => rfl
    -- it lands in `im P^{m+1}` (this is `DCond` at level `m + 1`) …
    have hρ_mem : ∀ x : ↥(kerFlag P (m + 1)),
        ρ x ∈ LinearMap.range (P ^ (m + 1)).mulVecLin := by
      rintro ⟨v, hv⟩
      rw [hρ_apply v hv]
      obtain ⟨w, hw⟩ := hD (m + 1) v hv
      rw [← hw]
      exact Submodule.sub_mem _ ⟨w, by simp⟩ ⟨g.mulVec v, by simp⟩
    -- … and kills `S_m` (this is level `m` of the induction)
    have hρ_ker : ∀ x : ↥(kerFlag P (m + 1)), (P ^ m).mulVec x.1 = 0 → ρ x = 0 := by
      rintro ⟨v, hv⟩ h0
      have h0' : (P ^ m).mulVec v = 0 := h0
      have hvm : v ∈ kerFlag P m := mem_kerFlag.mpr h0'
      rw [hρ_apply v hv, dpow_succ, add_mulVec, ← mulVec_mulVec, ← mulVec_mulVec,
        ← hg m le_rfl v hvm, h0', mulVec_zero, add_zero, mulVec_mulVec, ← pow_succ',
        sub_self]
    obtain ⟨E, hE1, hE2⟩ := exists_correction P m ρ hρ_mem hρ_ker
    refine ⟨g + E, fun k hk v hv => ?_⟩
    rcases Nat.lt_or_ge k (m + 1) with hk' | hk'
    · -- levels `k ≤ m`: the correction vanishes
      have hkm : k ≤ m := by omega
      have hvS : v ∈ kerFlag P (m + 1) := kerFlag_mono P (by omega : k ≤ m + 1) hv
      have hvm : (P ^ m).mulVec v = 0 := mem_kerFlag.mp (kerFlag_mono P hkm hv)
      rw [add_mulVec, hE2 v hvS hvm, add_zero]
      exact hg k hkm v hv
    · -- level `m + 1`: the correction supplies exactly the defect
      obtain rfl : k = m + 1 := by omega
      rw [add_mulVec, mulVec_add, hE1 v hv, hρ_apply v hv]
      abel

/-- The regular part over a PID:
one integral `g` implements every flag motion.  Above the nilpotency
degree both sides vanish, so the bounded version suffices. -/
theorem exists_regular_g (P Q : Matrix (Fin n) (Fin n) R) (hP : P ^ n = 0)
    (hD : DCond P Q) :
    ∃ g : Matrix (Fin n) (Fin n) R,
      ∀ k, ∀ v ∈ kerFlag P k, (P ^ k).mulVec (g.mulVec v) = (dpow P Q k).mulVec v := by
  obtain ⟨g, hg⟩ := exists_regular_g_of_le P Q hD n
  refine ⟨g, fun k => ?_⟩
  induction k with
  | zero => exact hg 0 (Nat.zero_le n)
  | succ k ihk =>
    rcases le_or_gt (k + 1) n with h | h
    · exact hg (k + 1) h
    · -- `k ≥ n`: both sides vanish
      intro v _
      have hPk : P ^ k = 0 := by
        rw [show k = n + (k - n) by omega, pow_add, hP, zero_mul]
      have hPk1 : P ^ (k + 1) = 0 := by rw [pow_succ, hPk, zero_mul]
      have h1 : (dpow P Q k).mulVec v = 0 := by
        rw [← ihk v (mem_kerFlag.mpr (by rw [hPk, zero_mulVec])), hPk, zero_mulVec]
      rw [hPk1, zero_mulVec, dpow_succ, add_mulVec, ← mulVec_mulVec,
        ← mulVec_mulVec, h1, mulVec_zero, hPk, zero_mulVec, mulVec_zero, add_zero]

end Isotropy
