import Height.DVR.CokerTorsion
import Height.Pencil.Centralizer
import Height.Pencil.RealizedLes
import Height.Toolbox.BaseChange

/-!
# `lem:selfdual-degree`: `Σₓ lenₓ T + 2 Σ bᵢ = 2 dim Fl_{τ'}`

The paper, `lem:selfdual-degree`.
-/

namespace Height.Pencil

open Matrix Height.Graded Height.Steenrod Height.Toolbox

universe u

/-! ### The trace pairing in the coordinates `vecMat` -/

section Pairing

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The trace pairing `⟨X, Y⟩ = tr (X Y)` in the coordinates `vecMat`
(`trace_mul_eq_sum_vecMat`). -/
def pairVec (x y : Fin (n * n) → R) : R := ∑ a, x a * y (swapIdx n a)

theorem pairVec_comm (x y : Fin (n * n) → R) : pairVec x y = pairVec y x := by
  rw [pairVec, pairVec, ← Equiv.sum_comp (swapIdx n) fun a => y a * x (swapIdx n a)]
  exact Finset.sum_congr rfl fun a _ => by rw [swapIdx_swapIdx]; ring

theorem pairVec_add_left (x x' y : Fin (n * n) → R) :
    pairVec (x + x') y = pairVec x y + pairVec x' y := by
  simp only [pairVec, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem pairVec_smul_left (c : R) (x y : Fin (n * n) → R) :
    pairVec (c • x) y = c * pairVec x y := by
  simp only [pairVec, Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

theorem pairVec_zero_left (y : Fin (n * n) → R) : pairVec (0 : Fin (n * n) → R) y = 0 := by
  simp [pairVec]

theorem pairVec_zero_right (x : Fin (n * n) → R) : pairVec x (0 : Fin (n * n) → R) = 0 := by
  simp [pairVec]

theorem pairVec_add_right (x y y' : Fin (n * n) → R) :
    pairVec x (y + y') = pairVec x y + pairVec x y' := by
  rw [pairVec_comm, pairVec_add_left, pairVec_comm y x, pairVec_comm y' x]

theorem pairVec_smul_right (c : R) (x y : Fin (n * n) → R) :
    pairVec x (c • y) = c * pairVec x y := by
  rw [pairVec_comm, pairVec_smul_left, pairVec_comm y x]

/-- The trace pairing is nondegenerate: the standard basis is self-dual up to
the index transposition. -/
theorem eq_zero_of_pairVec_eq_zero {x : Fin (n * n) → R}
    (h : ∀ y, pairVec x y = 0) : x = 0 := by
  funext a
  have hy := h (Pi.single (swapIdx n a) 1)
  have hval : pairVec x (Pi.single (swapIdx n a) (1 : R)) = x a := by
    unfold pairVec
    rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hb
      have hne : swapIdx n b ≠ swapIdx n a := fun hc => hb ((swapIdx n).injective hc)
      simp [hne]
    · simp
  rw [hval] at hy
  exact hy

/-- `ad_P` is skew-adjoint for the trace pairing: this is `gramMat_isAlt`. -/
theorem pairVec_adMat_add (P : Matrix (Fin n) (Fin n) R) (x y : Fin (n * n) → R) :
    pairVec (adMat P *ᵥ x) y + pairVec x (adMat P *ᵥ y) = 0 := by
  have hL : pairVec (adMat P *ᵥ x) y
      = ∑ a, ∑ b, adMat P (swapIdx n a) b * x b * y a := by
    rw [pairVec, ← Equiv.sum_comp (swapIdx n) fun a => (adMat P *ᵥ x) a * y (swapIdx n a)]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [swapIdx_swapIdx, Matrix.mulVec_apply_eq_sum, Finset.sum_mul]
  have hR : pairVec x (adMat P *ᵥ y)
      = ∑ a, ∑ b, adMat P (swapIdx n b) a * x b * y a := by
    rw [pairVec]
    rw [Finset.sum_congr rfl (fun b (_ : b ∈ Finset.univ) => by
      rw [Matrix.mulVec_apply_eq_sum, Finset.mul_sum] :
      ∀ b ∈ Finset.univ, x b * (adMat P *ᵥ y) (swapIdx n b)
        = ∑ a, x b * (adMat P (swapIdx n b) a * y a))]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  rw [hL, hR, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun b _ => ?_
  have halt := (gramMat_isAlt P).skew a b
  simp only [gramMat, Matrix.submatrix_apply, Matrix.transpose_apply, id_eq] at halt
  rw [halt]
  ring

theorem pairVec_adMat_left (P : Matrix (Fin n) (Fin n) R) (x y : Fin (n * n) → R) :
    pairVec (adMat P *ᵥ x) y = - pairVec x (adMat P *ᵥ y) :=
  eq_neg_of_add_eq_zero_left (pairVec_adMat_add P x y)

/-- The trace pairing commutes with base change along a ring map. -/
theorem pairVec_map {S : Type*} [CommRing S] (φ : R →+* S) (x y : Fin (n * n) → R) :
    φ (pairVec x y) = pairVec (fun a => φ (x a)) (fun a => φ (y a)) := by
  rw [pairVec, pairVec, map_sum]
  exact Finset.sum_congr rfl fun a _ => map_mul φ _ _

end Pairing

/-! ### The perp of a submodule -/

section Perp

variable {R : Type*} [CommRing R] {n : ℕ}

/-- `S^⊥ = {Y : ⟨Y, s⟩ = 0 for all s ∈ S}`, for the trace pairing. -/
def perpOf (S : Submodule R (Fin (n * n) → R)) :
    Submodule R (Fin (n * n) → R) where
  carrier := {x | ∀ y ∈ S, pairVec x y = 0}
  add_mem' hx hx' := fun y hy => by rw [pairVec_add_left, hx y hy, hx' y hy, add_zero]
  zero_mem' := fun y _ => pairVec_zero_left y
  smul_mem' c x hx := fun y hy => by rw [pairVec_smul_left, hx y hy, mul_zero]

theorem perpOf_antitone {S T : Submodule R (Fin (n * n) → R)}
    (h : S ≤ T) : perpOf T ≤ perpOf S :=
  fun _ hx y hy => hx y (h hy)

theorem le_perpOf_perpOf (S : Submodule R (Fin (n * n) → R)) :
    S ≤ perpOf (perpOf S) :=
  fun x hx y hy => by rw [pairVec_comm]; exact hy x hx

/-- The perp is saturated over a domain. -/
theorem saturated_perpOf [NoZeroDivisors R] (S : Submodule R (Fin (n * n) → R))
    (f : R) (x : Fin (n * n) → R) (hf : f ≠ 0)
    (hx : f • x ∈ perpOf S) : x ∈ perpOf S := by
  intro y hy
  have h := hx y hy
  rw [pairVec_smul_left] at h
  exact (mul_eq_zero.mp h).resolve_left hf

/-- Membership in the perp of a span is checked on the generators. -/
theorem mem_perpOf_span {ι : Type*} (u : ι → (Fin (n * n) → R)) {x : Fin (n * n) → R} :
    x ∈ perpOf (Submodule.span R (Set.range u)) ↔ ∀ i, pairVec x (u i) = 0 := by
  constructor
  · intro hx i
    exact hx (u i) (Submodule.subset_span ⟨i, rfl⟩)
  · intro hx y hy
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
    · rintro z ⟨i, rfl⟩; exact hx i
    · exact pairVec_zero_right x
    · intro y₁ y₂ _ _ h₁ h₂; rw [pairVec_add_right, h₁, h₂, add_zero]
    · intro c y _ h; rw [pairVec_smul_right, h, mul_zero]

end Perp

/-! ### `ad_P` and the grading -/

section Graded

variable {K : Type u} [Field K] {n : ℕ}

theorem adP_apply (N M : Matrix (Fin n) (Fin n) K) (x : Fin (n * n) → Graded.Poly K) :
    adP N M x = adMat (pencil N M) *ᵥ x := rfl

/-- `ad_P` is homogeneous of degree `1`: it intertwines the projections onto
the homogeneous pieces. -/
theorem adP_proj (N M : Matrix (Fin n) (Fin n) K) (e : ℤ)
    (f : Fin (n * n) → Graded.Poly K) :
    adP N M ((Graded.GradedPresentation.of K (shiftSrc n)).proj e f)
      = (Graded.GradedPresentation.of K (shiftSrc n)).proj (e + 1) (adP N M f) := by
  funext c
  show ∑ b, adMat (pencil N M) c b * Bproj (e - 0) (f b)
      = Bproj (e + 1 - 0) (∑ b, adMat (pencil N M) c b * f b)
  simp only [sub_zero]
  rw [map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  have h := Bproj_smul_of_mem (d := e) (n := 1) (f b) (adMat_pencil_mem_Bpiece N M c b)
  rw [mul_comm (adMat (pencil N M) c b) (Bproj e (f b)),
    mul_comm (adMat (pencil N M) c b) (f b)]
  exact h.symm

theorem isGraded_adRange_shiftSrc (N M : Matrix (Fin n) (Fin n) K) :
    (Graded.GradedPresentation.of K (shiftSrc n)).IsGraded (adRange N M) := by
  rintro f hf e
  obtain ⟨z, rfl⟩ := hf
  refine ⟨(Graded.GradedPresentation.of K (shiftSrc n)).proj (e - 1) z, ?_⟩
  rw [adP_proj]
  congr 1
  ring_nf

theorem saturated_centralizerSub (N M : Matrix (Fin n) (Fin n) K)
    (f : Graded.Poly K) (x : Fin (n * n) → Graded.Poly K) (hf : f ≠ 0)
    (hx : f • x ∈ centralizerSub N M) : x ∈ centralizerSub N M := by
  rw [centralizerSub, LinearMap.mem_ker] at hx ⊢
  rw [map_smul] at hx
  funext c
  have h : f * (adP N M x) c = 0 := congrFun hx c
  exact (mul_eq_zero.mp h).resolve_left hf

/-! ### The perp of the centraliser -/

theorem adRange_le_perpOf_centralizer (N M : Matrix (Fin n) (Fin n) K) :
    adRange N M ≤ perpOf (centralizerSub N M) := by
  rintro x ⟨z, rfl⟩ y hy
  rw [centralizerSub, LinearMap.mem_ker] at hy
  rw [adP_apply, pairVec_adMat_left, ← adP_apply, hy, pairVec_zero_right, neg_zero]

/-- `(im ad_P)^⊥ = C`: `ad_P` is skew-adjoint and the trace pairing is
nondegenerate. -/
theorem perpOf_adRange (N M : Matrix (Fin n) (Fin n) K) :
    perpOf (adRange N M) = centralizerSub N M := by
  refine le_antisymm (fun x hx => ?_) (fun x hx y hy => ?_)
  · rw [centralizerSub, LinearMap.mem_ker]
    refine eq_zero_of_pairVec_eq_zero fun z => ?_
    have h := hx (adP N M z) ⟨z, rfl⟩
    show pairVec (adMat (pencil N M) *ᵥ x) z = 0
    rw [pairVec_adMat_left]
    show -pairVec x (adP N M z) = 0
    rw [h, neg_zero]
  · obtain ⟨z, rfl⟩ := hy
    rw [centralizerSub, LinearMap.mem_ker] at hx
    have h : pairVec (adMat (pencil N M) *ᵥ x) z
        = -pairVec x (adMat (pencil N M) *ᵥ z) := pairVec_adMat_left _ _ _
    have hx0 : (adMat (pencil N M) *ᵥ x) = 0 := hx
    rw [hx0, pairVec_zero_left] at h
    show pairVec x (adMat (pencil N M) *ᵥ z) = 0
    exact neg_eq_zero.mp h.symm

/-- The double perp of the centraliser is the centraliser. -/
theorem perpOf_perpOf_centralizer (N M : Matrix (Fin n) (Fin n) K) :
    perpOf (perpOf (centralizerSub N M)) = centralizerSub N M :=
  le_antisymm
    (le_trans (perpOf_antitone (adRange_le_perpOf_centralizer N M))
      (le_of_eq (perpOf_adRange N M)))
    (le_perpOf_perpOf _)

/-! ### The Hilbert function of `im ad_P` -/

theorem adP_mem_piece_succ {N M : Matrix (Fin n) (Fin n) K} {e : ℤ}
    {x : Fin (n * n) → Graded.Poly K}
    (hx : x ∈ (Graded.GradedPresentation.of K (shiftSrc n)).piece e) :
    adP N M x ∈ (Graded.GradedPresentation.of K (shiftSrc n)).piece (e + 1) := by
  refine (Graded.GradedPresentation.of K _).mem_piece.2 fun c => ?_
  have hxb : ∀ b, x b ∈ Bpiece K e := by
    intro b
    have := (Graded.GradedPresentation.of K _).mem_piece.1 hx b
    simpa using this
  show (∑ b, adMat (pencil N M) c b * x b) ∈ Bpiece K (e + 1 - 0)
  rw [sub_zero]
  refine Submodule.sum_mem _ fun b _ => ?_
  have h := Bpiece_smul_Bpiece (adMat_pencil_mem_Bpiece N M c b) (hxb b)
  rw [show (1 : ℤ) + e = e + 1 by ring] at h
  simpa using h

/-- **The degree count of `im ad_P`.**  `ad_P` maps `F_{e-1}` onto `(im ad_P)_e`
with kernel `C_{e-1}`. -/
theorem finrank_sub_adRange (N M : Matrix (Fin n) (Fin n) K) (e : ℤ) :
    Module.finrank K ((Graded.GradedPresentation.of K (shiftSrc n)).sub (adRange N M) e)
      + Module.finrank K
          ((Graded.GradedPresentation.of K (shiftSrc n)).sub (centralizerSub N M) (e - 1))
      = Module.finrank K ((Graded.GradedPresentation.of K (shiftSrc n)).piece (e - 1)) := by
  classical
  set W := (Graded.GradedPresentation.of K (shiftSrc n)).piece (e - 1) with hW
  set φ : W →ₗ[K] (Fin (n * n) → Graded.Poly K) :=
    ((adP N M).restrictScalars K).comp W.subtype with hφ
  have hrange : LinearMap.range φ
      = (Graded.GradedPresentation.of K (shiftSrc n)).sub (adRange N M) e := by
    refine le_antisymm ?_ ?_
    · rintro y ⟨x, rfl⟩
      refine ⟨⟨(x : Fin (n * n) → Graded.Poly K), rfl⟩, ?_⟩
      have h := adP_mem_piece_succ (N := N) (M := M) x.2
      rwa [show e - 1 + 1 = e by ring] at h
    · rintro y ⟨hyR, hye⟩
      obtain ⟨z, rfl⟩ := hyR
      refine ⟨⟨(Graded.GradedPresentation.of K (shiftSrc n)).proj (e - 1) z,
        (Graded.GradedPresentation.of K _).proj_mem _ _⟩, ?_⟩
      show adP N M ((Graded.GradedPresentation.of K (shiftSrc n)).proj (e - 1) z) = adP N M z
      rw [adP_proj, show e - 1 + 1 = e by ring,
        (Graded.GradedPresentation.of K (shiftSrc n)).proj_self hye]
  have hker : (LinearMap.ker φ).map W.subtype
      = (Graded.GradedPresentation.of K (shiftSrc n)).sub (centralizerSub N M) (e - 1) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨hy, y.2⟩
    · rintro ⟨hxC, hxe⟩
      exact ⟨⟨x, hxe⟩, hxC, rfl⟩
  have h := LinearMap.finrank_range_add_finrank_ker φ
  rw [hrange] at h
  rw [← h, ← hker, Submodule.finrank_map_subtype_eq]

end Graded

/-! ### The Hilbert function of a graded submodule with a homogeneous basis -/

section BasisHilbert

variable {K : Type u} [Field K] {r : ℕ}

end BasisHilbert

/-! ### The perp is graded, and the rank bound for its Hilbert function -/

section PerpHilbert

variable {K : Type u} [Field K] {n : ℕ}

/-- The perp of a span of homogeneous elements is a graded submodule. -/
theorem isGraded_perpOf_span {ι : Type*} {b : ι → ℤ}
    {u : ι → (Fin (n * n) → Graded.Poly K)}
    (hhom : ∀ i, u i ∈ (Graded.GradedPresentation.of K (shiftSrc n)).piece (b i)) :
    (Graded.GradedPresentation.of K (shiftSrc n)).IsGraded
      (perpOf (Submodule.span (Graded.Poly K) (Set.range u))) := by
  intro f hf e
  rw [mem_perpOf_span] at hf ⊢
  intro i
  have hstep : pairVec ((Graded.GradedPresentation.of K (shiftSrc n)).proj e f) (u i)
      = Bproj (e + b i) (pairVec f (u i)) := by
    unfold pairVec
    rw [map_sum]
    refine Finset.sum_congr rfl fun cc _ => ?_
    have hui : u i (swapIdx n cc) ∈ Bpiece K (b i) := by
      have := (Graded.GradedPresentation.of K _).mem_piece.1 (hhom i) (swapIdx n cc)
      simpa using this
    have h := Bproj_smul_of_mem (d := e) (n := b i) (f cc) hui
    show Bproj (e - 0) (f cc) * u i (swapIdx n cc) = _
    rw [sub_zero, ← h]
  rw [hstep, hf i, map_zero]

/-- The pairing against a homogeneous element of degree `d` maps `F_e` into
`B_{e+d}`. -/
theorem pairVec_mem_Bpiece {e d : ℤ} {x y : Fin (n * n) → Graded.Poly K}
    (hx : x ∈ (Graded.GradedPresentation.of K (shiftSrc n)).piece e)
    (hy : y ∈ (Graded.GradedPresentation.of K (shiftSrc n)).piece d) :
    pairVec x y ∈ Bpiece K (e + d) := by
  refine Submodule.sum_mem _ fun cc _ => ?_
  have hxc : x cc ∈ Bpiece K e := by
    have := (Graded.GradedPresentation.of K _).mem_piece.1 hx cc; simpa using this
  have hyc : y (swapIdx n cc) ∈ Bpiece K d := by
    have := (Graded.GradedPresentation.of K _).mem_piece.1 hy (swapIdx n cc); simpa using this
  simpa using Bpiece_smul_Bpiece hxc hyc

/-- **The rank bound for the perp.**  The `K`-linear map `F_e → ⨁ B_{e+d_k}`,
`Y ↦ (⟨Y, w_k⟩)_k`, has kernel `(span w)^⊥_e`, so `dim F_e ≤ dim (span w)^⊥_e +
Σ_k dim B_{e+d_k}`. -/
theorem finrank_piece_le_perp {κ : Type} [Fintype κ] {d : κ → ℤ}
    {w : κ → (Fin (n * n) → Graded.Poly K)}
    (hw : ∀ k, w k ∈ (Graded.GradedPresentation.of K (shiftSrc n)).piece (d k)) (e : ℤ) :
    Module.finrank K ((Graded.GradedPresentation.of K (shiftSrc n)).piece e)
      ≤ Module.finrank K
          ((Graded.GradedPresentation.of K (shiftSrc n)).sub
            (perpOf (Submodule.span (Graded.Poly K) (Set.range w))) e)
        + ∑ k, (e + d k + 1).toNat := by
  classical
  set W := (Graded.GradedPresentation.of K (shiftSrc n)).piece e with hW
  set ρ : W →ₗ[K] (∀ k, Bpiece K (e + d k)) :=
    { toFun := fun x k => ⟨pairVec (x : Fin (n * n) → Graded.Poly K) (w k),
        pairVec_mem_Bpiece x.2 (hw k)⟩
      map_add' := by
        intro x y
        funext k
        exact Subtype.ext (pairVec_add_left _ _ _)
      map_smul' := by
        intro c x
        funext k
        apply Subtype.ext
        show pairVec (c • (x : Fin (n * n) → Graded.Poly K)) (w k)
            = c • pairVec (x : Fin (n * n) → Graded.Poly K) (w k)
        simp only [pairVec, Pi.smul_apply, smul_mul_assoc, Finset.smul_sum] } with hρ
  have hker : (LinearMap.ker ρ).map W.subtype
      = (Graded.GradedPresentation.of K (shiftSrc n)).sub
        (perpOf (Submodule.span (Graded.Poly K) (Set.range w))) e := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy0 : ∀ k, pairVec (y : Fin (n * n) → Graded.Poly K) (w k) = 0 := by
        intro k
        have hk := congrFun (LinearMap.mem_ker.mp hy) k
        exact congrArg Subtype.val hk
      exact ⟨(mem_perpOf_span w).2 hy0, y.2⟩
    · rintro ⟨hxP, hxe⟩
      refine ⟨⟨x, hxe⟩, ?_, rfl⟩
      funext k
      exact Subtype.ext ((mem_perpOf_span w).1 hxP k)
  have hfin : Module.finrank K (∀ k, Bpiece K (e + d k)) = ∑ k, (e + d k + 1).toNat := by
    rw [Module.finrank_pi_fintype]
    exact Finset.sum_congr rfl fun k _ => finrank_Bpiece K _
  have h := LinearMap.finrank_range_add_finrank_ker ρ
  have hle : Module.finrank K (LinearMap.range ρ) ≤ ∑ k, (e + d k + 1).toNat := by
    rw [← hfin]
    exact Submodule.finrank_le _
  have hkerfin : Module.finrank K (LinearMap.ker ρ)
      = Module.finrank K
          ((Graded.GradedPresentation.of K (shiftSrc n)).sub
            (perpOf (Submodule.span (Graded.Poly K) (Set.range w))) e) := by
    rw [← hker, Submodule.finrank_map_subtype_eq]
  omega

end PerpHilbert

/-! ### Transport along a homogeneous basis -/

section Transport

variable {K : Type u} [Field K] {n : ℕ}

/-- `Θ_v : (Fin r → B) → gl_n ⊗ B`, `x ↦ Σ_j x_j v_j`. -/
noncomputable abbrev theta {r : ℕ} (v : Fin r → (Fin (n * n) → Graded.Poly K)) :
    (Fin r → Graded.Poly K) →ₗ[Graded.Poly K] (Fin (n * n) → Graded.Poly K) :=
  Fintype.linearCombination (Graded.Poly K) v

theorem theta_proj {r : ℕ} {a : Fin r → ℤ} {v : Fin r → (Fin (n * n) → Graded.Poly K)}
    (hv : ∀ j, v j ∈ (Graded.GradedPresentation.of K (shiftSrc n)).piece (a j)) (e : ℤ)
    (x : Fin r → Graded.Poly K) :
    theta v ((Graded.GradedPresentation.of K a).proj e x)
      = (Graded.GradedPresentation.of K (shiftSrc n)).proj e (theta v x) := by
  simp only [Fintype.linearCombination_apply, map_sum]
  exact Finset.sum_congr rfl fun j _ =>
    ((Graded.GradedPresentation.of K (shiftSrc n)).proj_smul (x j) (hv j)).symm

theorem theta_mem_piece {r : ℕ} {a : Fin r → ℤ}
    {v : Fin r → (Fin (n * n) → Graded.Poly K)}
    (hv : ∀ j, v j ∈ (Graded.GradedPresentation.of K (shiftSrc n)).piece (a j)) {e : ℤ}
    {x : Fin r → Graded.Poly K} (hx : x ∈ (Graded.GradedPresentation.of K a).piece e) :
    theta v x ∈ (Graded.GradedPresentation.of K (shiftSrc n)).piece e := by
  rw [← (Graded.GradedPresentation.of K a).proj_self hx, theta_proj hv]
  exact (Graded.GradedPresentation.of K _).proj_mem _ _

theorem mem_piece_of_theta {r : ℕ} {a : Fin r → ℤ}
    {v : Fin r → (Fin (n * n) → Graded.Poly K)}
    (hv : ∀ j, v j ∈ (Graded.GradedPresentation.of K (shiftSrc n)).piece (a j))
    (hinj : Function.Injective (theta v)) {e : ℤ}
    {x : Fin r → Graded.Poly K}
    (hx : theta v x ∈ (Graded.GradedPresentation.of K (shiftSrc n)).piece e) :
    x ∈ (Graded.GradedPresentation.of K a).piece e := by
  have h : theta v ((Graded.GradedPresentation.of K a).proj e x) = theta v x := by
    rw [theta_proj hv, (Graded.GradedPresentation.of K (shiftSrc n)).proj_self hx]
  rw [← hinj h]
  exact (Graded.GradedPresentation.of K _).proj_mem _ _

end Transport

/-! ### `lenₓ` vanishes off the drop points -/

section LenX

variable {K : Type u} [Field K] {n : ℕ}

/-- At a point where the member has the
generic type there is no torsion: `D_x = 0` by `DX_add_cType` and
`cOf_eq_cType_of_hasType`, so the block index type is empty and `len_x T = 0`. -/
theorem lenX_eq_zero_of_not_dropPoint [Infinite K] {N M : Matrix (Fin n) (Fin n) K}
    {τ : Nat.Partition n} {t₀ : K} (hnil : NilpotentPencil N M)
    (hgen : GenericType N M τ) (h : ¬ IsDropPoint N M t₀ τ) :
    lenX N M t₀ = 0 := by
  have hty : HasType (N + t₀ • M) τ := not_not.mp h
  have hD : DX N M t₀ + cType τ = cOf (N + t₀ • M) :=
    DX_add_cType N M τ t₀ hnil hgen
  rw [cOf_eq_cType_of_hasType hty] at hD
  have hcard : Fintype.card (txData N M t₀).Blocks = 0 := by
    have hz : DX N M t₀ = 0 := by omega
    rw [DX] at hz
    omega
  have hempty : IsEmpty (txData N M t₀).Blocks := Fintype.card_eq_zero_iff.mp hcard
  rw [lenX]
  exact Finset.sum_eq_zero fun b _ => (hempty.false b).elim

end LenX

/-! ### Arithmetic of the Hilbert functions -/

section Arith

theorem exists_upper_bound {κ : Type*} [Fintype κ] (d : κ → ℤ) : ∃ E : ℤ, ∀ k, d k ≤ E := by
  classical
  refine ⟨∑ k, |d k|, fun k => ?_⟩
  calc d k ≤ |d k| := le_abs_self _
    _ ≤ ∑ j, |d j| := Finset.single_le_sum (fun j _ => abs_nonneg (d j)) (Finset.mem_univ k)

theorem cast_sum_sub {κ : Type*} [Fintype κ] (d : κ → ℤ) (e : ℤ) (h : ∀ k, d k ≤ e + 1) :
    ((∑ k, (e - d k + 1).toNat : ℕ) : ℤ) = (Fintype.card κ : ℤ) * (e + 1) - ∑ k, d k := by
  rw [Nat.cast_sum]
  rw [Finset.sum_congr rfl fun k (_ : k ∈ Finset.univ) =>
    Int.toNat_of_nonneg (by have := h k; omega : (0 : ℤ) ≤ e - d k + 1)]
  rw [Finset.sum_congr rfl fun k (_ : k ∈ Finset.univ) => (by ring : e - d k + 1 = (e + 1) - d k)]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem cast_sum_add {κ : Type*} [Fintype κ] (d : κ → ℤ) (e : ℤ) (h : ∀ k, 0 ≤ e + d k + 1) :
    ((∑ k, (e + d k + 1).toNat : ℕ) : ℤ) = (Fintype.card κ : ℤ) * (e + 1) + ∑ k, d k := by
  rw [Nat.cast_sum]
  rw [Finset.sum_congr rfl fun k (_ : k ∈ Finset.univ) => Int.toNat_of_nonneg (h k)]
  rw [Finset.sum_congr rfl fun k (_ : k ∈ Finset.univ) => (by ring : e + d k + 1 = (e + 1) + d k)]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end Arith

/-! ### The generic rank of `ad_P` over `B = K[μ, ν]` -/

section GenericRank

variable {K : Type u} [Field K]

/-- Dehomogenisation turns `ad` of the graded pencil into `ad` of the
polynomial pencil. -/
theorem map_deh_adMat_pencil {n : ℕ} (N M : Matrix (Fin n) (Fin n) K) :
    (adMat (pencil N M)).map ((deh K).toRingHom) = adMat (pencilPoly N M) := by
  rw [← adMat_map ((deh K).toRingHom) (pencil N M)]
  congr 1
  exact map_deh_pencil N M

/-- **The generic rank of `ad_P`.**  For a nilpotent pencil of generic type
`τ`, the rank of `ad_P` over the function field of `ℙ¹` is `n² − c(τ)`.

This is the graded companion of `rank_map_adMat_pencilPoly`: the two are compared
by dehomogenisation, which is injective on each graded piece
(`Graded.deh_injOn`), and the minors of `ad_P` are homogeneous
(`det_mem_Bpiece`). -/
theorem rank_frac_adMat_pencil [Infinite K] {n : ℕ} (N M : Matrix (Fin n) (Fin n) K)
    (τ : Nat.Partition n) (hnil : NilpotentPencil N M) (hgen : GenericType N M τ) :
    ((adMat (pencil N M)).map
        (algebraMap (Graded.Poly K) (FractionRing (Graded.Poly K)))).rank
      = n * n - cType τ := by
  classical
  set G : Matrix (Fin (n * n)) (Fin (n * n)) (Graded.Poly K) := adMat (pencil N M) with hG
  set ψ : Graded.Poly K →+* FractionRing (Graded.Poly K) :=
    algebraMap (Graded.Poly K) (FractionRing (Graded.Poly K)) with hψ
  have hψinj : Function.Injective ψ :=
    IsFractionRing.injective (Graded.Poly K) (FractionRing (Graded.Poly K))
  set Ψ : Polynomial K →+* LaurentSeries K :=
    (algebraMap (PowerSeries K) (LaurentSeries K)).comp
      Polynomial.coeToPowerSeries.ringHom with hΨ
  have hcoeinj : Function.Injective
      (Polynomial.coeToPowerSeries.ringHom : Polynomial K →+* PowerSeries K) := by
    intro a b h
    rw [Polynomial.coeToPowerSeries.ringHom_apply,
      Polynomial.coeToPowerSeries.ringHom_apply] at h
    exact Polynomial.coe_injective K h
  have hΨinj : Function.Injective Ψ :=
    (IsFractionRing.injective (PowerSeries K) (LaurentSeries K)).comp hcoeinj
  set χ : Graded.Poly K →+* LaurentSeries K := Ψ.comp ((deh K).toRingHom) with hχ
  -- the Laurent chart at `t₀ = 0` is dehomogenisation followed by expansion
  have hW : G.map χ = (adMat (pencilPoly (N + (0 : K) • M) M)).map Ψ := by
    rw [zero_smul, add_zero, hχ, RingHom.coe_comp, ← Matrix.map_map, hG,
      map_deh_adMat_pencil N M]
  have hrk := rank_map_adMat_pencilPoly Ψ hΨinj N M τ 0 hnil hgen
  rw [← hW] at hrk
  -- the minors of `G` are homogeneous
  have hentry : ∀ a b, G a b ∈ Bpiece K 1 := adMat_pencil_mem_Bpiece N M
  have hminor : ∀ {k : ℕ} (f g : Fin k → Fin (n * n)),
      (G.submatrix f g).det ∈ Bpiece K (k : ℤ) := by
    intro k f g
    have h := det_mem_Bpiece (G.submatrix f g) 1 fun i j => hentry _ _
    rwa [mul_one] at h
  have hdetψ : ∀ {k : ℕ} (f g : Fin k → Fin (n * n)),
      ((G.map ψ).submatrix f g).det = ψ ((G.submatrix f g).det) := by
    intro k f g
    rw [Matrix.submatrix_map]
    exact (RingHom.map_det ψ _).symm
  have hdetχ : ∀ {k : ℕ} (f g : Fin k → Fin (n * n)),
      ((G.map χ).submatrix f g).det = χ ((G.submatrix f g).det) := by
    intro k f g
    rw [Matrix.submatrix_map]
    exact (RingHom.map_det χ _).symm
  refine le_antisymm ?_ ?_
  · by_contra hcon
    rw [Nat.not_le] at hcon
    obtain ⟨f, g, hfg⟩ := Height.Toolbox.exists_submatrix_det_ne_zero (G.map ψ) hcon
    have hP : (G.submatrix f g).det ≠ 0 := by
      intro hz
      rw [hdetψ f g, hz, map_zero] at hfg
      exact hfg rfl
    have hdeh : deh K ((G.submatrix f g).det) ≠ 0 := by
      intro hz
      exact hP (Graded.deh_injOn (hminor f g) (Submodule.zero_mem _) (by rw [hz, map_zero]))
    have hne : ((G.map χ).submatrix f g).det ≠ 0 := by
      rw [hdetχ f g]
      intro hz
      refine hdeh (hΨinj ?_)
      rw [map_zero]
      exact hz
    have hle := Height.Toolbox.le_rank_of_submatrix_det_ne_zero _ f g hne
    rw [hrk] at hle
    omega
  · obtain ⟨f, g, hfg⟩ := Height.Toolbox.exists_submatrix_det_ne_zero (G.map χ) hrk.ge
    have hP : (G.submatrix f g).det ≠ 0 := by
      intro hz
      rw [hdetχ f g, hz, map_zero] at hfg
      exact hfg rfl
    refine Height.Toolbox.le_rank_of_submatrix_det_ne_zero _ f g ?_
    rw [hdetψ f g]
    intro hz
    exact hP (hψinj (by rw [hz, map_zero]))

end GenericRank

/-! ### The reduction of `ad_P` modulo `μ` -/

section NuLead

variable {K : Type u} [Field K]

/-- `nuLead` is multiplicative on products of linear forms. -/
theorem nuLead_prod {ι : Type*} (s : Finset ι) (f : ι → Graded.Poly K)
    (h : ∀ i ∈ s, f i ∈ Bpiece K 1) :
    nuLead (s.card : ℤ) (∏ i ∈ s, f i) = ∏ i ∈ s, nuLead 1 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.prod_empty, Finset.card_empty, Nat.cast_zero]
      rw [nuLead_of_nonneg le_rfl]
      simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
      have h1 : f a ∈ Bpiece K 1 := h a (Finset.mem_insert_self a s)
      have h2 : (∏ i ∈ s, f i) ∈ Bpiece K (s.card : ℤ) := by
        have hh := prod_mem_Bpiece s f 1 fun i hi => h i (Finset.mem_insert_of_mem hi)
        rwa [mul_one] at hh
      have hcast : ((s.card + 1 : ℕ) : ℤ) = 1 + (s.card : ℤ) := by push_cast; ring
      rw [hcast, nuLead_mul h1 h2, ih fun i hi => h i (Finset.mem_insert_of_mem hi)]

/-- The `ν`-leading coefficient of a `k × k` determinant of linear forms is the
determinant of the leading coefficients. -/
theorem nuLead_det {k : ℕ} {A : Matrix (Fin k) (Fin k) (Graded.Poly K)}
    (h : ∀ i j, A i j ∈ Bpiece K 1) :
    nuLead (k : ℤ) A.det = (A.map (fun x => nuLead 1 x)).det := by
  classical
  rw [Matrix.det_apply, Matrix.det_apply, map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Units.smul_def, Units.smul_def, map_zsmul]
  congr 1
  have hh := nuLead_prod (Finset.univ : Finset (Fin k)) (fun i => A (σ i) i)
    fun i _ => h _ _
  simpa using hh

/-- The pencil reduces to `M` modulo `μ`. -/
theorem nuLead_pencil {n : ℕ} (N M : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    nuLead 1 (pencil N M i j) = M i j := by
  have hC : ∀ a : K, (MvPolynomial.C a : Graded.Poly K) ∈ Bpiece K 0 := by
    intro a
    rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) by norm_num, Bpiece_natCast]
    exact MvPolynomial.isHomogeneous_C (Fin 2) a
  have hq : pencil N M i j
      = MvPolynomial.C (N i j) * mu + MvPolynomial.C (M i j) * nu := rfl
  rw [hq, map_add]
  have e1 : nuLead (1 : ℤ) (MvPolynomial.C (N i j) * mu : Graded.Poly K) = 0 := by
    rw [mul_comm]
    have hh := nuLead_mu_mul (hC (N i j))
    rwa [show (1 : ℤ) + 0 = 1 by ring] at hh
  have e2 : nuLead (1 : ℤ) (MvPolynomial.C (M i j) * nu : Graded.Poly K) = M i j := by
    rw [mul_comm]
    have hh := nuLead_nu_mul (hC (M i j))
    rw [show (1 : ℤ) + 0 = 1 by ring] at hh
    rw [hh, nuLead_of_nonneg le_rfl]
    simp
  rw [e1, e2, zero_add]

/-- `ad_P` reduces to `ad_M` modulo `μ`. -/
theorem map_nuLead_adMat_pencil {n : ℕ} (N M : Matrix (Fin n) (Fin n) K) :
    (adMat (pencil N M)).map (fun x => nuLead 1 x) = adMat M := by
  refine Matrix.ext fun a b => ?_
  show nuLead 1 (adEntry (pencil N M) (glIdx n a) (glIdx n b))
      = adEntry M (glIdx n a) (glIdx n b)
  rw [adEntry, adEntry]
  simp only [Matrix.of_apply, map_sub]
  congr 1 <;> split_ifs <;> simp [nuLead_pencil]

end NuLead

/-! ### The perp of a subspace over a field -/

section PerpField

variable {L : Type*} [Field L] {n : ℕ}

/-- The perp of a subspace of `L^{n²}` for the trace pairing has codimension at
least `dim W`: the perp is contained in the kernel of the matrix whose rows are
a basis of `W`, read through the index transposition. -/
theorem finrank_perpOf_add_le (W : Submodule L (Fin (n * n) → L)) :
    Module.finrank L (perpOf W) + Module.finrank L W ≤ n * n := by
  classical
  set k : ℕ := Module.finrank L W with hk
  set κ : Module.Basis (Fin k) L W := Module.finBasis L W with hκ
  set c : Fin k → (Fin (n * n) → L) := fun i => (κ i : Fin (n * n) → L) with hc
  have hcmem : ∀ i, c i ∈ W := fun i => (κ i).2
  have hcli : LinearIndependent L c :=
    LinearIndependent.map' κ.linearIndependent W.subtype (Submodule.ker_subtype W)
  set V : Matrix (Fin k) (Fin (n * n)) L :=
    Matrix.of (fun i a => c i (swapIdx n a)) with hV
  -- the perp sits inside the kernel of `V`
  have hle : perpOf W ≤ LinearMap.ker V.mulVecLin := by
    intro y hy
    refine LinearMap.mem_ker.2 ?_
    funext i
    have h := hy (c i) (hcmem i)
    show (V *ᵥ y) i = 0
    rw [Matrix.mulVec_apply_eq_sum]
    rw [← h, pairVec]
    exact Finset.sum_congr rfl fun a _ => by rw [hV]; simp [mul_comm]
  -- the rows of `V` are independent, so `V` has rank `k`
  have hkerT : LinearMap.ker Vᵀ.mulVecLin = ⊥ := by
    refine (Submodule.eq_bot_iff _).2 fun x hx => ?_
    have hz : ∀ a, ∑ i, x i * c i a = 0 := by
      intro a
      have h := congrFun (LinearMap.mem_ker.1 hx) (swapIdx n a)
      have h2 : Vᵀ.mulVecLin x (swapIdx n a) = ∑ i, x i * c i a := by
        show (Vᵀ *ᵥ x) (swapIdx n a) = _
        rw [Matrix.mulVec_apply_eq_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Matrix.transpose_apply, hV]
        simp [swapIdx_swapIdx, mul_comm]
      rw [h2] at h
      simpa using h
    have hsum : ∑ i, x i • c i = 0 := by
      funext a
      simpa [Finset.sum_apply, smul_eq_mul] using hz a
    have hall := Fintype.linearIndependent_iff.mp hcli x hsum
    funext i
    exact hall i
  have hrankT : Vᵀ.rank = k := by
    show Module.finrank L (LinearMap.range Vᵀ.mulVecLin) = k
    rw [LinearMap.finrank_range_of_inj (LinearMap.ker_eq_bot.mp hkerT),
      Module.finrank_fin_fun]
  have hrank : V.rank = k := by rw [← Matrix.rank_transpose, hrankT]
  have hker : Module.finrank L (LinearMap.ker V.mulVecLin) + k = n * n := by
    have h := LinearMap.finrank_range_add_finrank_ker V.mulVecLin
    rw [Module.finrank_fin_fun] at h
    have hr : Module.finrank L (LinearMap.range V.mulVecLin) = k := hrank
    omega
  have hmono : Module.finrank L (perpOf W)
      ≤ Module.finrank L (LinearMap.ker V.mulVecLin) := Submodule.finrank_mono hle
  omega

/-- Over a field, the image of `ad_P` is exactly the perp of its kernel: the
image sits inside the perp by skew-adjointness of `ad_P` for the trace pairing,
and the two subspaces have the same dimension by rank–nullity. -/
theorem range_eq_perpOf_ker_adMat (P : Matrix (Fin n) (Fin n) L) :
    LinearMap.range (adMat P).mulVecLin = perpOf (LinearMap.ker (adMat P).mulVecLin) := by
  have hle : LinearMap.range (adMat P).mulVecLin
      ≤ perpOf (LinearMap.ker (adMat P).mulVecLin) := by
    rintro x ⟨z, rfl⟩ y hy
    have hy0 : adMat P *ᵥ y = 0 := LinearMap.mem_ker.1 hy
    show pairVec (adMat P *ᵥ z) y = 0
    rw [pairVec_adMat_left, hy0, pairVec_zero_right, neg_zero]
  refine Submodule.eq_of_le_of_finrank_le hle ?_
  have h1 := finrank_perpOf_add_le (LinearMap.ker (adMat P).mulVecLin)
  have h2 := LinearMap.finrank_range_add_finrank_ker (adMat P).mulVecLin
  rw [Module.finrank_fin_fun] at h2
  omega

end PerpField

/-! ### The perp of the kernel over a domain -/

section PerpDomain

open Height.Toolbox

variable {R : Type u} [CommRing R] [IsDomain R] {n : ℕ}

/-- Clearing denominators in the fraction field. -/
theorem exists_clear_denom (y : Fin (n * n) → FractionRing R) :
    ∃ (d : R) (w : Fin (n * n) → R), d ≠ 0 ∧
      (fun i => algebraMap R (FractionRing R) (w i))
        = algebraMap R (FractionRing R) d • y := by
  obtain ⟨d, hd⟩ :=
    IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R) y
  have hd' : ∀ i, ∃ w : R, algebraMap R (FractionRing R) w = (d : R) • y i := fun i => hd i
  choose w hw using hd'
  refine ⟨(d : R), w, mem_nonZeroDivisors_iff_ne_zero.mp d.2, funext fun i => ?_⟩
  rw [hw i, Algebra.smul_def]
  rfl

/-- **Over a domain, `(ker ad_P)^⊥ = sat (im ad_P)`.**  The image sits inside the
perp of the kernel by skew-adjointness (`pairVec_adMat_left`) and the perp is
saturated (`saturated_perpOf`); conversely a vector perpendicular to the kernel
is perpendicular to the kernel over the fraction field, hence in the image there
(`range_eq_perpOf_ker_adMat`), and clearing denominators puts a nonzero multiple
of it in the image over `R`. -/
theorem perpOf_ker_adMat_eq_satOf_range (P : Matrix (Fin n) (Fin n) R) :
    perpOf (LinearMap.ker (adMat P).mulVecLin)
      = satOf (LinearMap.range (adMat P).mulVecLin) := by
  set ψ : R →+* FractionRing R := algebraMap R (FractionRing R) with hψdef
  have hψ : Function.Injective ψ := IsFractionRing.injective R (FractionRing R)
  have hle : LinearMap.range (adMat P).mulVecLin
      ≤ perpOf (LinearMap.ker (adMat P).mulVecLin) := by
    rintro x ⟨z, rfl⟩ y hy
    have hy0 : adMat P *ᵥ y = 0 := LinearMap.mem_ker.1 hy
    show pairVec (adMat P *ᵥ z) y = 0
    rw [pairVec_adMat_left, hy0, pairVec_zero_right, neg_zero]
  refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
  · have hxL : (fun i => ψ (x i))
        ∈ LinearMap.range ((adMat P).map ψ).mulVecLin := by
      rw [← adMat_map ψ P, range_eq_perpOf_ker_adMat]
      intro y hy
      obtain ⟨d, w, hd0, hw⟩ := exists_clear_denom (R := R) (n := n) y
      have hyk : adMat (P.map ψ) *ᵥ y = 0 := LinearMap.mem_ker.1 hy
      have hwk : w ∈ LinearMap.ker (adMat P).mulVecLin := by
        refine LinearMap.mem_ker.2 (funext fun i => hψ ?_)
        show ψ ((adMat P *ᵥ w) i) = ψ ((0 : Fin (n * n) → R) i)
        rw [Pi.zero_apply, map_zero, RingHom.map_mulVec]
        show ((adMat P).map ψ *ᵥ (fun i => ψ (w i))) i = 0
        rw [hw, Matrix.mulVec_smul, ← adMat_map ψ P, hyk, smul_zero]
        rfl
      have h1 : ψ d * pairVec (fun i => ψ (x i)) y = 0 := by
        rw [← pairVec_smul_right, ← hw, ← pairVec_map, hx w hwk, map_zero]
      have hd : ψ d ≠ 0 := fun h => hd0 (hψ (by rw [h, map_zero]))
      exact (mul_eq_zero.mp h1).resolve_left hd
    obtain ⟨y, hy⟩ := hxL
    obtain ⟨d, w, hd0, hw⟩ := exists_clear_denom (R := R) (n := n) y
    refine ⟨d, hd0, ⟨w, funext fun i => hψ ?_⟩⟩
    show ψ ((adMat P *ᵥ w) i) = ψ ((d • x) i)
    rw [RingHom.map_mulVec]
    show ((adMat P).map ψ *ᵥ (fun i => ψ (w i))) i = ψ (d * x i)
    rw [hw, Matrix.mulVec_smul]
    show ψ d * (((adMat P).map ψ).mulVecLin y) i = ψ (d * x i)
    rw [hy, map_mul]
  · obtain ⟨f, hf, hfx⟩ := hx
    exact saturated_perpOf _ f x hf (hle hfx)

end PerpDomain

/-! ### Dehomogenisation as a base change

`Ŝ` and the local submodule at `t₀` are `S` base-changed along `deh` and along
the chart `atPoint t₀` (`Toolbox.mapSpan`); saturation and gradedness transfer.
These three statements are about `Height.Graded` only -- their natural home is
`Height/Graded/Free.lean` and `Height/Graded/LocalLength.lean`. -/

section GradedSat

open Height.Toolbox

variable {K : Type u} [Field K] {r : ℕ}

/-- `Ŝ` is `S` base-changed along `deh`. -/
theorem mapSpan_deh (S : Submodule (Graded.Poly K) (Fin r → Graded.Poly K)) :
    mapSpan ((deh K).toRingHom) S = Shat K S := rfl

/-- The local submodule at `t₀` is `S` base-changed along the chart. -/
theorem localSub_eq_mapSpan (t₀ : K) (S : Submodule (Graded.Poly K) (Fin r → Graded.Poly K)) :
    Graded.localSub K r t₀ S = mapSpan (Graded.atPoint t₀) S := rfl

/-- The span of a family of homogeneous elements is a graded submodule. -/
theorem isGraded_span_homog {a : Fin r → ℤ} {ι : Type*} {b : ι → ℤ}
    {u : ι → (Fin r → Graded.Poly K)}
    (hhom : ∀ i, u i ∈ (Graded.GradedPresentation.of K a).piece (b i)) :
    (Graded.GradedPresentation.of K a).IsGraded (Submodule.span (Graded.Poly K) (Set.range u)) := by
  classical
  intro x hx
  induction hx using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨i, rfl⟩ := hz
      intro e
      rw [(Graded.GradedPresentation.of K a).proj_of_mem (hhom i)]
      split_ifs
      · exact Submodule.subset_span ⟨i, rfl⟩
      · exact Submodule.zero_mem _
  | zero => intro e; rw [map_zero]; exact Submodule.zero_mem _
  | add y z _ _ ihy ihz =>
      intro e
      rw [map_add]
      exact Submodule.add_mem _ (ihy e) (ihz e)
  | smul c y _ ih =>
      intro e
      obtain ⟨t, ht⟩ := (Graded.GradedPresentation.of K a).exists_sum_proj y
      rw [← ht, Finset.smul_sum, map_sum]
      refine Submodule.sum_mem _ fun d _ => ?_
      rw [(Graded.GradedPresentation.of K a).proj_smul c
        ((Graded.GradedPresentation.of K a).proj_mem d y)]
      exact Submodule.smul_mem _ _ (ih d)

/-- **Saturation descends to the dehomogenisation.**  If a graded submodule of
`Fin r → B` is saturated, then so is `Ŝ ⊆ Fin r → K[t]`: homogenise the two
sides of `f · x ∈ Ŝ`, match the degrees with a power of `μ`, and use
`dehVec_injOn`. -/
theorem satOf_Shat {a : Fin r → ℤ} {S : Submodule (Graded.Poly K) (Fin r → Graded.Poly K)}
    (hgr : (Graded.GradedPresentation.of K a).IsGraded S)
    (hsat : ∀ (f : Graded.Poly K) (x : Fin r → Graded.Poly K), f ≠ 0 → f • x ∈ S → x ∈ S) :
    satOf (Shat K S) = Shat K S := by
  refine le_antisymm (fun x hx => ?_) (le_satOf _)
  obtain ⟨f, hf, hfx⟩ := hx
  obtain ⟨e, hWe⟩ := (mem_Shat_iff hgr).1 hfx
  obtain ⟨W, hW, hWx⟩ := hWe
  obtain ⟨e', hXe⟩ := exists_mem_Ppiece a x
  obtain ⟨X, hX, hXx⟩ := hXe
  set F : Graded.Poly K := hgz f.natDegree f with hFdef
  have hFdeh : deh K F = f := deh_hgz (Nat.lt_succ_self _)
  have hFne : F ≠ 0 := fun h0 => hf (by rw [← hFdeh, h0, map_zero])
  have hFX : F • X ∈ (Graded.GradedPresentation.of K a).piece ((f.natDegree : ℤ) + e') :=
    (Graded.GradedPresentation.of K _).smul_mem_piece (hgz_mem _ _) hX
  have hWf : W ∈ (Graded.GradedPresentation.of K a).piece e := (Submodule.mem_inf.1 hW).2
  have hWS : W ∈ S := (Submodule.mem_inf.1 hW).1
  set E : ℤ := max ((f.natDegree : ℤ) + e') e with hE
  set k₁ : ℕ := (E - ((f.natDegree : ℤ) + e')).toNat with hk₁
  set k₂ : ℕ := (E - e).toNat with hk₂
  have hk₁' : (k₁ : ℤ) = E - ((f.natDegree : ℤ) + e') :=
    Int.toNat_of_nonneg (sub_nonneg.2 (le_max_left _ _))
  have hk₂' : (k₂ : ℤ) = E - e := Int.toNat_of_nonneg (sub_nonneg.2 (le_max_right _ _))
  have h1 : (Graded.mu : Graded.Poly K) ^ k₁ • (F • X)
      ∈ (Graded.GradedPresentation.of K a).piece E := by
    have h := mu_pow_smul_mem_piece hFX k₁
    rwa [show (f.natDegree : ℤ) + e' + (k₁ : ℤ) = E by rw [hk₁']; ring] at h
  have h2 : (Graded.mu : Graded.Poly K) ^ k₂ • W ∈ (Graded.GradedPresentation.of K a).piece E := by
    have h := mu_pow_smul_mem_piece hWf k₂
    rwa [show e + (k₂ : ℤ) = E by rw [hk₂']; ring] at h
  have hdeh : dehVec K r ((Graded.mu : Graded.Poly K) ^ k₁ • (F • X))
      = dehVec K r ((Graded.mu : Graded.Poly K) ^ k₂ • W) := by
    rw [dehVec_mu_pow_smul, dehVec_mu_pow_smul, dehVec_smul, hFdeh, hXx, hWx]
  have hmem : ((Graded.mu : Graded.Poly K) ^ k₁ * F) • X ∈ S := by
    rw [mul_smul, dehVec_injOn h1 h2 hdeh]
    exact S.smul_mem _ hWS
  have hne : ((Graded.mu : Graded.Poly K) ^ k₁ * F) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (MvPolynomial.X_ne_zero 0)) hFne
  rw [← hXx]
  exact Submodule.subset_span ⟨X, hsat _ _ hne hmem, rfl⟩

end GradedSat

/-! ### `lem:selfdual-degree`: the local length bridge -/

section Bridge

open Height.Toolbox

variable {K : Type u} [Field K] {n : ℕ}

/-- The matrix of `Θ_v`: its columns are the `v j`. -/
def thetaMat {r : ℕ} (v : Fin r → (Fin (n * n) → Graded.Poly K)) :
    Matrix (Fin (n * n)) (Fin r) (Graded.Poly K) :=
  Matrix.of fun i j => v j i

theorem theta_eq_mulVec {r : ℕ} (v : Fin r → (Fin (n * n) → Graded.Poly K))
    (x : Fin r → Graded.Poly K) : theta v x = thetaMat v *ᵥ x := by
  funext i
  show (∑ j, x j • v j) i = ∑ j, thetaMat v i j * x j
  rw [Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  show x j • v j i = v j i * x j
  rw [smul_eq_mul, mul_comm]

/-- The dehomogenisation of `Θ_v` is injective: homogenise and use
`dehVec_injOn`.  (Note that `deh` itself is *not* injective.) -/
theorem ker_map_deh_thetaMat {r : ℕ} {a : Fin r → ℤ}
    {v : Fin r → (Fin (n * n) → Graded.Poly K)}
    (hvhom : ∀ j, v j ∈ (Graded.GradedPresentation.of K (shiftSrc n)).piece (a j))
    (hinj : Function.Injective (theta v)) :
    LinearMap.ker (((thetaMat v).map ((deh K).toRingHom)).mulVecLin) = ⊥ := by
  refine (Submodule.eq_bot_iff _).2 fun x hx => ?_
  obtain ⟨e, hXe⟩ := exists_mem_Ppiece a x
  obtain ⟨X, hX, hXx⟩ := hXe
  have hzero : theta v X = 0 := by
    refine dehVec_injOn (a := shiftSrc n) (e := e) (theta_mem_piece hvhom hX)
      (Submodule.zero_mem _) ?_
    rw [map_zero]
    funext j
    show deh K (theta v X j) = 0
    rw [theta_eq_mulVec]
    show ((deh K).toRingHom) ((thetaMat v *ᵥ X) j) = 0
    rw [RingHom.map_mulVec]
    show (((thetaMat v).map ((deh K).toRingHom)) *ᵥ (fun i => deh K (X i))) j = 0
    have hxx : (fun i => deh K (X i)) = x := hXx
    rw [hxx]
    exact congrFun (LinearMap.mem_ker.1 hx) j
  rw [← hXx, show X = 0 from hinj (by rw [hzero, map_zero]), map_zero]

/-- **The local length bridge.**  In the coordinates given by a
homogeneous basis `v` of `C^⊥`, the local piece of `C^⊥ / im ad_P` at a finite
point `t₀` is the torsion of `coker ad_{P(t₀)}` over `K⟦u⟧`, of `K`-dimension
`len_{t₀} T`.

The mechanism is base change (`Toolbox.range_map_mulVecLin`,
`Toolbox.mapSpan_satOf`) around three identifications: `C^⊥ = sat (im ad_P)`
over `K[t]` (`perpOf_ker_adMat_eq_satOf_range`, after `map_deh_adMat_pencil`),
`Ŝ(C^⊥)` saturated (`satOf_Shat`), and the Smith count of the torsion of a
cokernel over `K⟦u⟧` (`Height.DVR.finrank_quot_comap_eq_sum_order`). -/
theorem finrank_localQuot_eq_lenX {r : ℕ} (N M : Matrix (Fin n) (Fin n) K)
    (a : Fin r → ℤ) (v : Fin r → (Fin (n * n) → Graded.Poly K))
    (hvhom : ∀ j, v j ∈ (Graded.GradedPresentation.of K (shiftSrc n)).piece (a j))
    (hvli : LinearIndependent (Graded.Poly K) v)
    (hvsp : Submodule.span (Graded.Poly K) (Set.range v) = perpOf (centralizerSub N M))
    (t₀ : K) :
    Module.finrank K (Graded.localQuot K r t₀ (Submodule.comap (theta v) (adRange N M)))
      = lenX N M t₀ := by
  classical
  set P : Submodule (Graded.Poly K) (Fin (n * n) → Graded.Poly K) :=
    perpOf (centralizerSub N M) with hPdef
  set S : Submodule (Graded.Poly K) (Fin r → Graded.Poly K) :=
    Submodule.comap (theta v) (adRange N M) with hSdef
  set Amat : Matrix (Fin (n * n)) (Fin (n * n)) (Graded.Poly K) := adMat (pencil N M) with hAdef
  set Vm : Matrix (Fin (n * n)) (Fin r) (Graded.Poly K) := thetaMat v with hVdef
  set Ahat : Matrix (Fin (n * n)) (Fin (n * n)) (Polynomial K) :=
    Amat.map ((deh K).toRingHom) with hAhat
  set Vhat : Matrix (Fin (n * n)) (Fin r) (Polynomial K) :=
    Vm.map ((deh K).toRingHom) with hVhat
  set Ach : Matrix (Fin (n * n)) (Fin (n * n)) (PowerSeries K) :=
    Amat.map (Graded.atPoint t₀) with hAch
  set Θ : (Fin r → PowerSeries K) →ₗ[PowerSeries K] (Fin (n * n) → PowerSeries K) :=
    (Vm.map (Graded.atPoint t₀)).mulVecLin with hΘ
  -- the chart factors through dehomogenisation
  have hAfac : Ach = Ahat.map (Graded.iota K t₀) := by
    rw [hAch, hAhat, Matrix.map_map, ← RingHom.coe_comp, ← Graded.atPoint_eq_comp]
  have hVfac : Vm.map (Graded.atPoint t₀) = Vhat.map (Graded.iota K t₀) := by
    rw [hVhat, Matrix.map_map, ← RingHom.coe_comp, ← Graded.atPoint_eq_comp]
  -- `Θ_v` is the matrix `Vm`
  have hθeq : theta v = Vm.mulVecLin := LinearMap.ext (theta_eq_mulVec v)
  have hθinj : Function.Injective (theta v) := by
    rw [← LinearMap.ker_eq_bot]
    refine (Submodule.eq_bot_iff _).2 fun x hx => ?_
    funext j
    exact Fintype.linearIndependent_iff.mp hvli x hx j
  have hθrange : LinearMap.range (theta v) = P := by
    rw [theta, Fintype.range_linearCombination, hvsp]
  have hPgr : (Graded.GradedPresentation.of K (shiftSrc n)).IsGraded P :=
    hvsp ▸ isGraded_span_homog hvhom
  -- the images over `B`, `K[t]` and `K⟦u⟧`
  have hAran : LinearMap.range Amat.mulVecLin = adRange N M := rfl
  have hVran : LinearMap.range Vm.mulVecLin = P := by rw [← hθeq, hθrange]
  have hAhatran : LinearMap.range Ahat.mulVecLin = Shat K (adRange N M) := by
    rw [hAhat, range_map_mulVecLin, mapSpan_deh, hAran]
  have hVhatran : LinearMap.range Vhat.mulVecLin = Shat K P := by
    rw [hVhat, range_map_mulVecLin, mapSpan_deh, hVran]
  have hAchran : LinearMap.range Ach.mulVecLin
      = mapSpan (Graded.iota K t₀) (Shat K (adRange N M)) := by
    rw [hAfac, range_map_mulVecLin, hAhatran]
  have hAchran2 : LinearMap.range Ach.mulVecLin
      = Graded.localSub K (n * n) t₀ (adRange N M) := by
    rw [hAch, range_map_mulVecLin, hAran, ← localSub_eq_mapSpan]
  have hAhateq : Ahat = adMat (pencilPoly N M) := map_deh_adMat_pencil N M
  have hG2 : satOf (LinearMap.range Ahat.mulVecLin)
      = perpOf (LinearMap.ker Ahat.mulVecLin) := by
    rw [hAhateq]
    exact (perpOf_ker_adMat_eq_satOf_range (pencilPoly N M)).symm
  -- `Ŝ(C^⊥)` is perpendicular to `ker ad_P` over `K[t]`
  have hC1 : Shat K P ≤ perpOf (LinearMap.ker Ahat.mulVecLin) := by
    intro y hy
    obtain ⟨e, hWe⟩ := (mem_Shat_iff hPgr).1 hy
    obtain ⟨W, hW, hWy⟩ := hWe
    intro z hz
    obtain ⟨e', hZe⟩ := exists_mem_Ppiece (shiftSrc n) z
    obtain ⟨Z, hZ, hZz⟩ := hZe
    have hZc : Z ∈ centralizerSub N M := by
      refine LinearMap.mem_ker.2 (dehVec_injOn (a := shiftSrc n) (e := e' + 1)
        (adP_mem_piece_succ hZ) (Submodule.zero_mem _) ?_)
      rw [map_zero]
      funext j
      show ((deh K).toRingHom) ((Amat *ᵥ Z) j) = 0
      rw [RingHom.map_mulVec]
      show (Ahat *ᵥ (fun i => deh K (Z i))) j = 0
      have hzz : (fun i => deh K (Z i)) = z := hZz
      rw [hzz]
      exact congrFun (LinearMap.mem_ker.1 hz) j
    have hWZ : pairVec W Z = 0 := (Submodule.mem_inf.1 hW).1 Z hZc
    have hyz : pairVec y z = ((deh K).toRingHom) (pairVec W Z) := by
      rw [pairVec_map ((deh K).toRingHom) W Z]
      congr 1
      · exact hWy.symm
      · exact hZz.symm
    rw [hyz, hWZ, map_zero]
  -- hence `Ŝ(C^⊥) = sat (Ŝ(im ad_P))` over `K[t]`
  have hC : Shat K P = satOf (Shat K (adRange N M)) := by
    refine le_antisymm ?_ ?_
    · rw [← hAhatran, hG2]
      exact hC1
    · rw [← satOf_Shat hPgr (saturated_perpOf (centralizerSub N M))]
      exact satOf_mono (Submodule.span_mono (Set.image_mono
        (adRange_le_perpOf_centralizer N M)))
  -- the range of `Θ` is the saturation of the image over `K⟦u⟧`
  have hΘran : LinearMap.range Θ = satOf (LinearMap.range Ach.mulVecLin) := by
    rw [hΘ, hVfac, range_map_mulVecLin, hVhatran, hC,
      mapSpan_satOf _ (Graded.iota_injective t₀), hAchran]
  have hΘinj : Function.Injective Θ := by
    rw [← LinearMap.ker_eq_bot, hΘ, hVfac]
    exact ker_map_mulVecLin_eq_bot Vhat (Graded.iota K t₀) (Graded.iota_injective t₀)
      (ker_map_deh_thetaMat hvhom hθinj)
  -- the local submodule is the preimage of the image
  have hcomm : ∀ x : Fin r → Graded.Poly K,
      Θ (Graded.atPtVec K r t₀ x) = Graded.atPtVec K (n * n) t₀ (theta v x) := by
    intro x
    funext i
    show ((Vm.map (Graded.atPoint t₀)) *ᵥ (fun j => Graded.atPoint t₀ (x j))) i
        = Graded.atPoint t₀ (theta v x i)
    rw [hθeq]
    exact (RingHom.map_mulVec (Graded.atPoint t₀) Vm x i).symm
  have hmapS : Submodule.map (theta v) S = adRange N M :=
    Submodule.map_comap_eq_self (by rw [hθrange, hPdef]
                                    exact adRange_le_perpOf_centralizer N M)
  have hmapΘ : Submodule.map Θ (Graded.localSub K r t₀ S)
      = LinearMap.range Ach.mulVecLin := by
    rw [hAchran2, Graded.localSub, Graded.localSub, Submodule.map_span]
    congr 1
    ext y
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨theta v x, hx, (hcomm x).symm⟩
    · rintro ⟨z, hz, rfl⟩
      rw [← hmapS] at hz
      obtain ⟨x, hx, rfl⟩ := hz
      exact ⟨Graded.atPtVec K r t₀ x, ⟨x, hx, rfl⟩, hcomm x⟩
  have hcomap : Graded.localSub K r t₀ S
      = Submodule.comap Θ (LinearMap.range Ach.mulVecLin) := by
    rw [← hmapΘ, Submodule.comap_map_eq_self]
    rw [LinearMap.ker_eq_bot.2 hΘinj]
    exact bot_le
  -- the Smith count over `K⟦u⟧`
  have hAdMat : adMat (Pat N M t₀) = Ach := by rw [Pat, adMat_map]
  have hquot : Module.finrank K (Graded.localQuot K r t₀ S)
      = Module.finrank K ((Fin r → PowerSeries K) ⧸
          Submodule.comap Θ (LinearMap.range (adMat (Pat N M t₀)).mulVecLin)) := by
    rw [hAdMat]
    exact ((Submodule.quotEquivOfEq _ _ hcomap).restrictScalars K).finrank_eq
  rw [hquot, (txData N M t₀).finrank_quot_comap_eq_sum_two_mBlk Θ (by rw [hAdMat]; exact hΘran)]
  rfl

end Bridge

/-! ### The two remaining inputs of `lem:selfdual-degree`

The two remaining inputs are proved below
(`centralizerRankStmt`, `adRangeMultiplier`); the local length bridge is
`finrank_localQuot_eq_lenX` above. -/

/-! ### The centraliser has rank `c(τ)` -/

section CentralizerRank

variable {K : Type u} [Field K] {n : ℕ}

/-- A `B`-linearly independent family of vectors stays linearly independent
over the fraction field of `B`: clear denominators. -/
theorem linearIndependent_algebraMap (L : Type u) [Field L] [Algebra (Graded.Poly K) L]
    [IsFractionRing (Graded.Poly K) L] {r : ℕ} {ι : Type*} [Fintype ι]
    {u : ι → (Fin r → Graded.Poly K)} (hli : LinearIndependent (Graded.Poly K) u) :
    LinearIndependent L (fun i => fun a => algebraMap (Graded.Poly K) L (u i a)) := by
  classical
  have hinj : Function.Injective (algebraMap (Graded.Poly K) L) :=
    IsFractionRing.injective (Graded.Poly K) L
  rw [Fintype.linearIndependent_iff]
  intro cc hcc i
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors (Graded.Poly K)) cc
  choose x hx using hd
  have hdne : algebraMap (Graded.Poly K) L (d : Graded.Poly K) ≠ 0 := fun hz =>
    (mem_nonZeroDivisors_iff_ne_zero.mp d.2) (hinj (by rw [hz, map_zero]))
  have hcomp : ∀ a : Fin r, ∑ j, x j * u j a = 0 := by
    intro a
    apply hinj
    rw [map_zero, map_sum]
    have hz1 : ∑ j, cc j * algebraMap (Graded.Poly K) L (u j a) = 0 := by
      have h := congrFun hcc a
      simpa [Finset.sum_apply, smul_eq_mul] using h
    calc ∑ j, algebraMap (Graded.Poly K) L (x j * u j a)
        = ∑ j, ((d : Graded.Poly K) • cc j) * algebraMap (Graded.Poly K) L (u j a) :=
          Finset.sum_congr rfl fun j _ => by rw [map_mul, hx j]
      _ = (d : Graded.Poly K) • ∑ j, cc j * algebraMap (Graded.Poly K) L (u j a) := by
          rw [Finset.smul_sum]
          exact Finset.sum_congr rfl fun j _ => by rw [smul_mul_assoc]
      _ = 0 := by rw [hz1, smul_zero]
  have hxz : ∀ j, x j = 0 := by
    refine Fintype.linearIndependent_iff.mp hli x ?_
    funext a
    simpa [Finset.sum_apply, smul_eq_mul] using hcomp a
  have h1 : (d : Graded.Poly K) • cc i = 0 := by rw [← hx i, hxz i, map_zero]
  rw [Algebra.smul_def] at h1
  exact (mul_eq_zero.mp h1).resolve_left hdne

/-- **The rank of the centraliser.**  A homogeneous `B`-basis of the centraliser of a
nilpotent pencil of generic type `τ` has exactly `c(τ)` members: over the
function field of `ℙ¹` it is a basis of `ker ad_P`, whose dimension is
`n² − rank ad_P = c(τ)` by `rank_frac_adMat_pencil`. -/
theorem centralizerRankStmt [Infinite K] :
    ∀ (N M : Matrix (Fin n) (Fin n) K) (τ : Nat.Partition n),
      NilpotentPencil N M → GenericType N M τ →
    ∀ {ι : Type} [Fintype ι] (b : ι → ℤ) (u : ι → (Fin (n * n) → Graded.Poly K)),
      CentralizerBasis N M b u → Fintype.card ι = cType τ := by
  classical
  intro N M τ hnil hgen ι _ b u hu
  have hinj : Function.Injective
      (algebraMap (Graded.Poly K) (FractionRing (Graded.Poly K))) :=
    IsFractionRing.injective _ _
  set ψ : Graded.Poly K →+* FractionRing (Graded.Poly K) :=
    algebraMap (Graded.Poly K) (FractionRing (Graded.Poly K)) with hψ
  set G : Matrix (Fin (n * n)) (Fin (n * n)) (Graded.Poly K) := adMat (pencil N M) with hG
  set A : Matrix (Fin (n * n)) (Fin (n * n)) (FractionRing (Graded.Poly K)) :=
    G.map ψ with hA
  set w : ι → (Fin (n * n) → FractionRing (Graded.Poly K)) := fun i a => ψ (u i a) with hw
  -- the images of the basis lie in the kernel
  have hkermem : ∀ i, w i ∈ LinearMap.ker A.mulVecLin := by
    intro i
    have h0 : G *ᵥ u i = 0 := by
      have := hu.mem i
      rw [centralizerSub, LinearMap.mem_ker, adP_apply] at this
      exact this
    refine LinearMap.mem_ker.2 ?_
    funext a
    have h := RingHom.map_mulVec ψ G (u i) a
    rw [h0, Pi.zero_apply, map_zero] at h
    show (A *ᵥ w i) a = 0
    exact h.symm
  -- and they span it
  have hkerle : LinearMap.ker A.mulVecLin
      ≤ Submodule.span (FractionRing (Graded.Poly K)) (Set.range w) := by
    intro z hz
    have hAz : A *ᵥ z = 0 := hz
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite
      (nonZeroDivisors (Graded.Poly K)) z
    choose y hy using hd
    have hdne : ψ (d : Graded.Poly K) ≠ 0 := fun hzz =>
      (mem_nonZeroDivisors_iff_ne_zero.mp d.2) (hinj (by rw [hzz, map_zero]))
    have hyk : y ∈ centralizerSub N M := by
      rw [centralizerSub, LinearMap.mem_ker, adP_apply]
      funext a
      show (G *ᵥ y) a = 0
      apply hinj
      rw [map_zero, RingHom.map_mulVec ψ G y a]
      have hfun : (⇑ψ ∘ y) = (d : Graded.Poly K) • z := funext hy
      rw [hfun, ← hA, Matrix.mulVec_smul, hAz, smul_zero]
      rfl
    rw [← hu.span, Submodule.mem_span_range_iff_exists_fun] at hyk
    obtain ⟨c, hc⟩ := hyk
    refine (Submodule.mem_span_range_iff_exists_fun _).2
      ⟨fun i => (ψ (d : Graded.Poly K))⁻¹ * ψ (c i), ?_⟩
    funext a
    have hya : ∑ i, c i * u i a = y a := by
      have := congrFun hc a
      simpa [Finset.sum_apply, smul_eq_mul] using this
    have hlhs : (∑ i, ((ψ (d : Graded.Poly K))⁻¹ * ψ (c i)) • w i) a
        = (ψ (d : Graded.Poly K))⁻¹ * ∑ i, ψ (c i) * ψ (u i a) := by
      rw [Finset.sum_apply]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by
        simp [hw, smul_eq_mul, mul_assoc]
    rw [hlhs]
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => (map_mul ψ (c i) (u i a)).symm]
    rw [← map_sum, hya, hy a, Algebra.smul_def, ← hψ, ← mul_assoc,
      inv_mul_cancel₀ hdne, one_mul]
  -- so the kernel has dimension `card ι`
  have hkerdim : Module.finrank (FractionRing (Graded.Poly K))
      (LinearMap.ker A.mulVecLin) = Fintype.card ι := by
    have hli : LinearIndependent (FractionRing (Graded.Poly K)) w :=
      linearIndependent_algebraMap (FractionRing (Graded.Poly K)) hu.linInd
    set w' : ι → (LinearMap.ker A.mulVecLin) := fun i => ⟨w i, hkermem i⟩ with hw'
    have hli' : LinearIndependent (FractionRing (Graded.Poly K)) w' :=
      LinearIndependent.of_comp (LinearMap.ker A.mulVecLin).subtype hli
    have hsp' : Submodule.span (FractionRing (Graded.Poly K)) (Set.range w') = ⊤ := by
      refine Submodule.map_injective_of_injective
        (Submodule.injective_subtype (LinearMap.ker A.mulVecLin)) ?_
      rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top, Submodule.range_subtype]
      refine le_antisymm (Submodule.span_le.2 ?_) hkerle
      rintro _ ⟨i, rfl⟩
      exact hkermem i
    exact Module.finrank_eq_card_basis (Module.Basis.mk hli' hsp'.ge)
  -- and the rank is `n² − c(τ)`
  have hrk : A.rank = n * n - cType τ := rank_frac_adMat_pencil N M τ hnil hgen
  have hrn := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  rw [hkerdim, Module.finrank_fin_fun] at hrn
  have hArank : A.rank = Module.finrank (FractionRing (Graded.Poly K))
      (LinearMap.range A.mulVecLin) := rfl
  have hcle : cType τ ≤ n * n := cType_le τ
  omega

end CentralizerRank

/-! ### The multiplier: Cramer's rule on a maximal minor -/

section Multiplier

variable {K : Type u} [Field K] {n : ℕ}

/-- A vector of `C^⊥` lands in the image of `ad_P` over the function field of
`ℙ¹`: over a field the image of `ad_P` is the whole perp of its kernel, and a
kernel vector over the function field is a `B`-multiple of a centraliser
vector. -/
theorem map_mem_range_of_mem_perpOf (N M : Matrix (Fin n) (Fin n) K)
    {y : Fin (n * n) → Graded.Poly K} (hy : y ∈ perpOf (centralizerSub N M)) :
    (fun a => algebraMap (Graded.Poly K) (FractionRing (Graded.Poly K)) (y a))
      ∈ LinearMap.range ((adMat (pencil N M)).map
          (algebraMap (Graded.Poly K) (FractionRing (Graded.Poly K)))).mulVecLin := by
  classical
  set ψ : Graded.Poly K →+* FractionRing (Graded.Poly K) :=
    algebraMap (Graded.Poly K) (FractionRing (Graded.Poly K)) with hψ
  set G : Matrix (Fin (n * n)) (Fin (n * n)) (Graded.Poly K) := adMat (pencil N M) with hG
  set A : Matrix (Fin (n * n)) (Fin (n * n)) (FractionRing (Graded.Poly K)) :=
    G.map ψ with hA
  have hinj : Function.Injective ⇑ψ := IsFractionRing.injective _ _
  have hAad : A = adMat ((pencil N M).map ψ) := by rw [hA, hG, adMat_map]
  rw [hAad, range_eq_perpOf_ker_adMat, ← hAad]
  intro v hv
  have hAv : A *ᵥ v = 0 := LinearMap.mem_ker.1 hv
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors (Graded.Poly K)) v
  choose v' hv' using hd
  have hdne : ψ (d : Graded.Poly K) ≠ 0 := fun hzz =>
    (mem_nonZeroDivisors_iff_ne_zero.mp d.2) (hinj (by rw [hzz, map_zero]))
  have hfun : (⇑ψ ∘ v') = (d : Graded.Poly K) • v := funext hv'
  have hv'mem : v' ∈ centralizerSub N M := by
    rw [centralizerSub, LinearMap.mem_ker, adP_apply]
    funext a
    show (G *ᵥ v') a = 0
    apply hinj
    rw [map_zero, RingHom.map_mulVec ψ G v' a, hfun, ← hA, Matrix.mulVec_smul, hAv,
      smul_zero]
    rfl
  have hzero : ψ (pairVec y v') = 0 := by rw [hy v' hv'mem, map_zero]
  have hsum : ∑ a, ψ (y a) * ψ (v' (swapIdx n a)) = 0 := by
    rw [← hzero, show pairVec y v' = ∑ a, y a * v' (swapIdx n a) from rfl, map_sum]
    exact Finset.sum_congr rfl fun a _ => (map_mul ψ (y a) (v' (swapIdx n a))).symm
  show pairVec (fun a => ψ (y a)) v = 0
  have hkey : ψ (d : Graded.Poly K) * pairVec (fun a => ψ (y a)) v = 0 := by
    rw [show pairVec (fun a => ψ (y a)) v = ∑ a, ψ (y a) * v (swapIdx n a) from rfl,
      Finset.mul_sum, ← hsum]
    refine Finset.sum_congr rfl fun a _ => ?_
    have h1 : ψ (v' (swapIdx n a)) = (d : Graded.Poly K) • v (swapIdx n a) := hv' _
    rw [h1, Algebra.smul_def, ← hψ]
    ring
  exact (mul_eq_zero.mp hkey).resolve_left hdne

/-- **The multiplier**: a homogeneous
`g` with `g · C^⊥ ⊆ im ad_P` and `μ ∤ g` (`nuLead ≠ 0`), namely an
`(n² − c(τ)) × (n² − c(τ))` minor of `ad_P` that does not vanish at
`(μ, ν) = (0, 1)`.  A maximal minor of `ad_P` whose reduction mod `μ` is a
nonvanishing minor of `ad_M` clears the denominators in Cramer's rule: it
carries all of `C^⊥` into `im ad_P`. -/
theorem adRangeMultiplier [Infinite K] (N M : Matrix (Fin n) (Fin n) K) (τ : Nat.Partition n)
    (hnil : NilpotentPencil N M) (hgen : GenericType N M τ) (hMτ : HasType M τ) :
    ∃ (d : ℤ) (g : Graded.Poly K), g ∈ Bpiece K d ∧ nuLead d g ≠ 0 ∧
      ∀ y ∈ perpOf (centralizerSub N M), g • y ∈ adRange N M := by
  classical
  set ψ : Graded.Poly K →+* FractionRing (Graded.Poly K) :=
    algebraMap (Graded.Poly K) (FractionRing (Graded.Poly K)) with hψ
  set G : Matrix (Fin (n * n)) (Fin (n * n)) (Graded.Poly K) := adMat (pencil N M) with hG
  set A : Matrix (Fin (n * n)) (Fin (n * n)) (FractionRing (Graded.Poly K)) :=
    G.map ψ with hA
  have hinj : Function.Injective ⇑ψ := IsFractionRing.injective _ _
  -- a maximal nonsingular minor of `ad_M`
  have hMnil : IsNilpotent M := by
    have h := hnil 0 1
    rwa [zero_smul, one_smul, zero_add] at h
  obtain ⟨r, hr⟩ : ∃ r : ℕ, n * n - cType τ = r := ⟨_, rfl⟩
  have hrkM : r ≤ (adMat M).rank := by
    have h := Height.Toolbox.rank_adMat_eq M hMnil
    rw [cOf_eq_cType_of_hasType hMτ] at h
    omega
  obtain ⟨f, g₀, hfg⟩ := Height.Toolbox.exists_submatrix_det_ne_zero (adMat M) hrkM
  set Sb : Matrix (Fin r) (Fin r) (Graded.Poly K) := G.submatrix f g₀ with hSb
  set Δ : Graded.Poly K := Sb.det with hΔ
  have hSbij : ∀ i j, Sb i j = G (f i) (g₀ j) := fun _ _ => rfl
  have hentry : ∀ i j, Sb i j ∈ Bpiece K 1 := fun i j => adMat_pencil_mem_Bpiece N M _ _
  have hnl : nuLead (r : ℤ) Δ = ((adMat M).submatrix f g₀).det := by
    rw [hΔ, nuLead_det hentry, hSb, ← Matrix.submatrix_map, hG,
      map_nuLead_adMat_pencil N M]
  refine ⟨(r : ℤ), Δ, ?_, ?_, ?_⟩
  · rw [hΔ]
    have h := det_mem_Bpiece Sb 1 hentry
    rwa [mul_one] at h
  · rw [hnl]; exact hfg
  -- Cramer's rule on the rows `f`
  intro y hy
  have hΔne : Δ ≠ 0 := fun hzz => hfg (by rw [← hnl, hzz, map_zero])
  have hψΔ : ψ Δ ≠ 0 := fun hzz => hΔne (hinj (by rw [hzz, map_zero]))
  set z : Fin r → Graded.Poly K := Sb.adjugate *ᵥ (fun i => y (f i)) with hz
  set xb : Fin (n * n) → Graded.Poly K :=
    fun a => ∑ j, if g₀ j = a then z j else 0 with hxb
  have hrow : ∀ i, (G *ᵥ xb) (f i) = (Δ • y) (f i) := by
    intro i
    have hinner : ∀ j : Fin r,
        ∑ a, (if g₀ j = a then G (f i) a * z j else 0) = G (f i) (g₀ j) * z j := by
      intro j
      rw [Finset.sum_eq_single (g₀ j)]
      · split_ifs with hc
        · rfl
        · exact absurd rfl hc
      · intro a _ ha
        split_ifs with hc
        · exact absurd hc.symm ha
        · rfl
      · intro hnm
        exact absurd (Finset.mem_univ (g₀ j)) hnm
    have h1 : (G *ᵥ xb) (f i) = ∑ j, G (f i) (g₀ j) * z j := by
      rw [Matrix.mulVec_apply_eq_sum]
      have hstep : ∀ a : Fin (n * n),
          G (f i) a * xb a = ∑ j, (if g₀ j = a then G (f i) a * z j else 0) := by
        intro a
        rw [hxb]
        show G (f i) a * (∑ j, if g₀ j = a then z j else 0) = _
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        split_ifs with hj
        · rfl
        · rw [mul_zero]
      rw [Finset.sum_congr rfl fun a (_ : a ∈ Finset.univ) => hstep a, Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => hinner j
    have h2 : (Sb *ᵥ z) i = ∑ j, G (f i) (g₀ j) * z j := by
      rw [Matrix.mulVec_apply_eq_sum Sb z i]
      exact Finset.sum_congr rfl fun j _ => by rw [hSbij]
    have h3 : Sb *ᵥ z = Δ • (fun i => y (f i)) := by
      rw [hz, Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec,
        Matrix.one_mulVec, ← hΔ]
    rw [h1, ← h2, h3]
    rfl
  -- the remaining rows follow: `ad_P` has rank `r`, realised by the rows `f`
  have hArank : A.rank = r := by
    rw [hA, hG, hψ, ← hr]
    exact rank_frac_adMat_pencil N M τ hnil hgen
  set ρ : (Fin (n * n) → FractionRing (Graded.Poly K)) →ₗ[FractionRing (Graded.Poly K)]
      (Fin r → FractionRing (Graded.Poly K)) :=
    LinearMap.funLeft (FractionRing (Graded.Poly K)) (FractionRing (Graded.Poly K)) f
    with hρ
  have hcomp : ρ.comp A.mulVecLin = (A.submatrix f id).mulVecLin := by
    refine LinearMap.ext fun x => ?_
    funext i
    rfl
  have hmapW : Submodule.map ρ (LinearMap.range A.mulVecLin)
      = LinearMap.range (A.submatrix f id).mulVecLin := by
    rw [← LinearMap.range_comp, hcomp]
  have hdetA : (A.submatrix f g₀).det = ψ Δ := by
    rw [hA, Matrix.submatrix_map, ← hSb, hΔ, RingHom.map_det]
    rfl
  have hrge : r ≤ (A.submatrix f id).rank := by
    refine Height.Toolbox.le_rank_of_submatrix_det_ne_zero _ id g₀ ?_
    show (A.submatrix f g₀).det ≠ 0
    rw [hdetA]
    exact hψΔ
  have hsplit := finrank_map_add_finrank_inf_ker ρ (LinearMap.range A.mulVecLin)
  have hfr : Module.finrank (FractionRing (Graded.Poly K))
      (LinearMap.range A.mulVecLin) = r := by rw [← hArank]; rfl
  have hfm : Module.finrank (FractionRing (Graded.Poly K))
      (Submodule.map ρ (LinearMap.range A.mulVecLin)) = (A.submatrix f id).rank := by
    rw [hmapW]
    rfl
  have hbot : LinearMap.range A.mulVecLin ⊓ LinearMap.ker ρ = ⊥ := by
    refine Submodule.finrank_eq_zero.1 ?_
    omega
  -- the two solutions of the linear system agree
  have hyrange := map_mem_range_of_mem_perpOf N M hy
  rw [← hψ, ← hG, ← hA] at hyrange
  set u : Fin (n * n) → Graded.Poly K := G *ᵥ xb - Δ • y with hu
  have hmap1 : (fun a => ψ ((G *ᵥ xb) a)) ∈ LinearMap.range A.mulVecLin := by
    refine ⟨fun a => ψ (xb a), ?_⟩
    funext a
    exact (RingHom.map_mulVec ψ G xb a).symm
  have hmap2 : (fun a => ψ ((Δ • y) a)) ∈ LinearMap.range A.mulVecLin := by
    have heq : (fun a => ψ ((Δ • y) a)) = ψ Δ • (fun a => ψ (y a)) := by
      funext a
      show ψ (Δ * y a) = ψ Δ * ψ (y a)
      exact map_mul ψ Δ (y a)
    rw [heq]
    exact Submodule.smul_mem _ _ hyrange
  have hume : (fun a => ψ (u a)) ∈ LinearMap.range A.mulVecLin := by
    have heq : (fun a => ψ (u a))
        = (fun a => ψ ((G *ᵥ xb) a)) - (fun a => ψ ((Δ • y) a)) := by
      funext a
      show ψ ((G *ᵥ xb) a - (Δ • y) a) = ψ ((G *ᵥ xb) a) - ψ ((Δ • y) a)
      exact map_sub ψ _ _
    rw [heq]
    exact Submodule.sub_mem _ hmap1 hmap2
  have hukr : (fun a => ψ (u a)) ∈ LinearMap.ker ρ := by
    refine LinearMap.mem_ker.2 ?_
    funext i
    show ψ (u (f i)) = 0
    have hzz : u (f i) = 0 := by
      show (G *ᵥ xb) (f i) - (Δ • y) (f i) = 0
      rw [hrow i, sub_self]
    rw [hzz, map_zero]
  have hu0 : u = 0 := by
    have hmem : (fun a => ψ (u a)) ∈
        LinearMap.range A.mulVecLin ⊓ LinearMap.ker ρ := ⟨hume, hukr⟩
    rw [hbot, Submodule.mem_bot] at hmem
    funext a
    apply hinj
    show ψ (u a) = ψ 0
    rw [map_zero]
    exact congrFun hmem a
  refine ⟨xb, ?_⟩
  rw [adP_apply, ← hG]
  rw [hu, sub_eq_zero] at hu0
  exact hu0

end Multiplier

/-! ### `lem:selfdual-degree` -/

section Assembly

variable {K : Type u} [Field K] {n : ℕ}

/-- **`lem:selfdual-degree`** at a pencil whose member at infinity has the
generic type (so every drop point is finite): for any finite set `Tset`
containing the drop points, `Σ_{t₀ ∈ Tset} len_{t₀} T + 2 Σ bᵢ = 2 dim Fl_{τ'}`.
(`lenX` vanishes off the drop points.) -/
theorem selfDualGapStmt [IsAlgClosed K] :
    ∀ (N M : Matrix (Fin n) (Fin n) K) (τ : Nat.Partition n),
      NilpotentPencil N M → GenericType N M τ → HasType M τ →
    ∀ {ι : Type} [Fintype ι] (b : ι → ℤ) (u : ι → (Fin (n * n) → Graded.Poly K)),
      CentralizerBasis N M b u →
    ∀ Tset : Finset K, (∀ t₀, IsDropPoint N M t₀ τ → t₀ ∈ Tset) →
      ((∑ t₀ ∈ Tset, lenX N M t₀ : ℕ) : ℤ) + 2 * ∑ i, b i = 2 * (dimFl τ : ℤ) := by
  classical
  intro N M τ hnil hgen hMτ ι _ b u hu Tset hTset
  -- the centraliser and its homogeneous basis
  have hbnn : ∀ i, 0 ≤ b i := by
    intro i
    by_contra hneg
    push Not at hneg
    have h0 : (Graded.GradedPresentation.free K (Fin (n * n))).piece (b i) = ⊥ :=
      Graded.GradedPresentation.piece_eq_bot _ (fun _ => hneg)
    have hui := hu.homog i
    rw [h0, Submodule.mem_bot] at hui
    exact hu.linInd.ne_zero i hui
  have hcτ : Fintype.card ι = cType τ := centralizerRankStmt N M τ hnil hgen b u hu
  set c : ℕ := Fintype.card ι with hcdef
  set C : Submodule (Graded.Poly K) (Fin (n * n) → Graded.Poly K) := centralizerSub N M with hCdef
  set P : Submodule (Graded.Poly K) (Fin (n * n) → Graded.Poly K) := perpOf C with hPdef
  have hPgr : (Graded.GradedPresentation.of K (shiftSrc n)).IsGraded P := by
    rw [hPdef, hCdef, ← hu.span]
    exact isGraded_perpOf_span hu.homog
  -- a homogeneous basis of `C^⊥`
  obtain ⟨ι', hι', a', v', hv'mem, hv'hom, hv'li, hv'sp⟩ :=
    Graded.saturated_free (shiftSrc n) P hPgr (fun f x hf hx => saturated_perpOf C f x hf hx)
  have := hι'
  set r : ℕ := Fintype.card ι' with hrdef
  set ε : Fin r ≃ ι' := (Fintype.equivFin ι').symm with hεdef
  set a : Fin r → ℤ := a' ∘ ε with hadef
  set v : Fin r → (Fin (n * n) → Graded.Poly K) := v' ∘ ε with hvdef
  have hvhom : ∀ j, v j ∈ (Graded.GradedPresentation.of K (shiftSrc n)).piece (a j) :=
    fun j => hv'hom (ε j)
  have hvmem : ∀ j, v j ∈ P := fun j => hv'mem (ε j)
  have hvli : LinearIndependent (Graded.Poly K) v := hv'li.comp ε ε.injective
  have hvsp : Submodule.span (Graded.Poly K) (Set.range v) = P := by
    rw [hvdef, ε.surjective.range_comp v', hv'sp]
  have hsuma : ∑ j, a j = ∑ i, a' i := Equiv.sum_comp ε a'
  have hann : ∀ j, 0 ≤ a j := by
    intro j
    by_contra hneg
    push Not at hneg
    have h0 : (Graded.GradedPresentation.of K (shiftSrc n)).piece (a j) = ⊥ :=
      (Graded.GradedPresentation.of K (shiftSrc n)).piece_eq_bot (fun _ => hneg)
    have hvj := hvhom j
    rw [h0, Submodule.mem_bot] at hvj
    exact hvli.ne_zero j hvj
  -- the two Hilbert functions
  have hPhil : ∀ e, Module.finrank K ((Graded.GradedPresentation.of K (shiftSrc n)).sub P e)
      = ∑ j, (e - a j + 1).toNat :=
    fun e => Graded.HomogeneousBasis.finrank_sub
      (P := Graded.GradedPresentation.free K (Fin (n * n)))
      ⟨hvmem, hvhom, hvli, hvsp⟩ e
  have hChil : ∀ e, Module.finrank K ((Graded.GradedPresentation.of K (shiftSrc n)).sub C e)
      = ∑ i, (e - b i + 1).toNat :=
    fun e => Graded.HomogeneousBasis.finrank_sub hu e
  -- the transported submodule
  have hθinj : Function.Injective (theta v) := by
    rw [← LinearMap.ker_eq_bot]
    refine (Submodule.eq_bot_iff _).2 fun x hx => ?_
    have h0 : ∑ j, x j • v j = 0 := hx
    funext j
    exact Fintype.linearIndependent_iff.mp hvli x h0 j
  have hθrange : LinearMap.range (theta v) = P := by
    rw [Fintype.range_linearCombination, hvsp]
  set S : Submodule (Graded.Poly K) (Fin r → Graded.Poly K) :=
    Submodule.comap (theta v) (adRange N M) with hSdef
  have hSgr : (Graded.GradedPresentation.of K a).IsGraded S := by
    intro x hx e
    show theta v ((Graded.GradedPresentation.of K a).proj e x) ∈ adRange N M
    rw [theta_proj hvhom]
    exact isGraded_adRange_shiftSrc N M _ hx e
  have hmapS : ∀ e, Submodule.map ((theta v).restrictScalars K)
        ((Graded.GradedPresentation.of K a).sub S e)
      = (Graded.GradedPresentation.of K (shiftSrc n)).sub (adRange N M) e := by
    intro e
    ext y
    constructor
    · rintro ⟨x, ⟨hxS, hxe⟩, rfl⟩
      exact ⟨hxS, theta_mem_piece hvhom hxe⟩
    · rintro ⟨hyR, hye⟩
      have hyP : y ∈ P := by
        rw [hPdef, hCdef]
        exact adRange_le_perpOf_centralizer N M hyR
      rw [← hθrange] at hyP
      obtain ⟨x, rfl⟩ := hyP
      exact ⟨x, ⟨hyR, mem_piece_of_theta hvhom hθinj hye⟩, rfl⟩
  have hSfin : ∀ e, Module.finrank K ((Graded.GradedPresentation.of K a).sub S e)
      = Module.finrank K ((Graded.GradedPresentation.of K (shiftSrc n)).sub (adRange N M) e) := by
    intro e
    rw [← hmapS e]
    exact (Submodule.equivMapOfInjective ((theta v).restrictScalars K) hθinj
      ((Graded.GradedPresentation.of K a).sub S e)).finrank_eq
  have hfreefin : ∀ e, Module.finrank K ((Graded.GradedPresentation.of K a).piece e)
      = Module.finrank K ((Graded.GradedPresentation.of K (shiftSrc n)).sub P e) := by
    intro e
    rw [Graded.GradedPresentation.finrank_piece, hPhil e]
  -- the multiplier
  obtain ⟨dg, g, hg, hgmu, hgP⟩ := adRangeMultiplier N M τ hnil hgen hMτ
  have hgS : ∀ x : Fin r → Graded.Poly K, g • x ∈ S := by
    intro x
    show theta v (g • x) ∈ adRange N M
    rw [map_smul]
    refine hgP _ ?_
    show theta v x ∈ P
    rw [← hθrange]
    exact ⟨x, rfl⟩
  -- the numerical bookkeeping
  obtain ⟨Ea, hEa⟩ := exists_upper_bound a
  obtain ⟨Eb, hEb⟩ := exists_upper_bound b
  set sumb : ℕ := (∑ i, b i).toNat with hsumbdef
  have hsumb : (sumb : ℤ) = ∑ i, b i :=
    Int.toNat_of_nonneg (Finset.sum_nonneg fun i _ => hbnn i)
  set E₀ : ℤ := max (max Ea Eb) 1 with hE₀
  have hFe : ∀ e : ℤ, 0 ≤ e →
      ((Module.finrank K ((Graded.GradedPresentation.of K (shiftSrc n)).piece e) : ℕ) : ℤ)
        = (n * n : ℤ) * (e + 1) := by
    intro e he
    rw [Graded.GradedPresentation.finrank_piece]
    have h := cast_sum_sub (shiftSrc n) e (fun _ => by show (0 : ℤ) ≤ e + 1; omega)
    simpa using h
  have hAe : ∀ e : ℤ, E₀ ≤ e →
      ((Module.finrank K
          ((Graded.GradedPresentation.of K (shiftSrc n)).sub (adRange N M) e) : ℕ) : ℤ)
        = (n * n : ℤ) * e - ((c : ℤ) * e - ∑ i, b i) := by
    intro e he
    have hE : Eb ≤ e ∧ (1 : ℤ) ≤ e := by
      constructor <;> [exact le_trans (le_trans (le_max_right Ea Eb) (le_max_left _ _)) he;
        exact le_trans (le_max_right _ _) he]
    have hsum := finrank_sub_adRange N M e
    have hC1 : ((Module.finrank K
          ((Graded.GradedPresentation.of K (shiftSrc n)).sub C (e - 1)) : ℕ) : ℤ)
        = (c : ℤ) * e - ∑ i, b i := by
      rw [hChil (e - 1)]
      have h := cast_sum_sub b (e - 1) (fun i => by have := hEb i; omega)
      rw [h]
      ring
    have hF1 : ((Module.finrank K
          ((Graded.GradedPresentation.of K (shiftSrc n)).piece (e - 1)) : ℕ) : ℤ)
        = (n * n : ℤ) * e := by
      have h := hFe (e - 1) (by omega)
      rw [h]; ring
    have := congrArg (fun m : ℕ => (m : ℤ)) hsum
    push_cast at this
    rw [hC1, hF1] at this
    omega
  have hPe : ∀ e : ℤ, E₀ ≤ e →
      ((Module.finrank K ((Graded.GradedPresentation.of K (shiftSrc n)).sub P e) : ℕ) : ℤ)
        = (r : ℤ) * (e + 1) - ∑ j, a j := by
    intro e he
    rw [hPhil e]
    have h := cast_sum_sub a e (fun j => by
      have h1 : Ea ≤ e := le_trans (le_trans (le_max_left Ea Eb) (le_max_left _ _)) he
      have := hEa j; omega)
    simpa using h
  -- `r + c = n²`, from the multiplier and `lem:local-length`, first half
  obtain ⟨len, E₁, hlen⟩ := Graded.torsion_len_exists a S hg hgmu hgS
  have hrc : (r : ℤ) + c = n * n := by
    have key : ∀ e : ℤ, max E₀ E₁ ≤ e →
        ((n * n : ℤ) * e - ((c : ℤ) * e - ∑ i, b i)) + len = (r : ℤ) * (e + 1) - ∑ j, a j := by
      intro e he
      have h := hlen e (le_trans (le_max_right _ _) he)
      have hE : E₀ ≤ e := le_trans (le_max_left _ _) he
      have hcast := congrArg (fun m : ℕ => (m : ℤ)) h
      push_cast at hcast
      rw [hSfin e, hAe e hE, hfreefin e, hPe e hE] at hcast
      exact hcast
    have h1 := key (max E₀ E₁) (le_refl _)
    have h2 := key (max E₀ E₁ + 1) (by omega)
    nlinarith [h1, h2]
  -- `Σ a = Σ b`, from the two rank bounds
  have hab : ∑ j, a j = ∑ i, b i := by
    have hB1 : ∀ e : ℤ, E₀ ≤ e →
        (n * n : ℤ) * (e + 1)
          ≤ ((r : ℤ) * (e + 1) - ∑ j, a j) + ((c : ℤ) * (e + 1) + ∑ i, b i) := by
      intro e he
      have h := finrank_piece_le_perp (K := K) (n := n) hu.homog e
      rw [hu.span] at h
      have hcast : ((Module.finrank K
            ((Graded.GradedPresentation.of K (shiftSrc n)).piece e) : ℕ) : ℤ)
          ≤ ((Module.finrank K ((Graded.GradedPresentation.of K (shiftSrc n)).sub P e) : ℕ) : ℤ)
            + ((∑ i, (e + b i + 1).toNat : ℕ) : ℤ) := by
        exact_mod_cast h
      have hbne : ∀ i, (0 : ℤ) ≤ e + b i + 1 := fun i => by
        have := hbnn i
        have h1 : (1 : ℤ) ≤ e := le_trans (le_max_right _ _) he
        omega
      rw [hFe e (by omega), hPe e he, cast_sum_add b e hbne] at hcast
      simpa using hcast
    have hB2 : ∀ e : ℤ, E₀ ≤ e →
        (n * n : ℤ) * (e + 1)
          ≤ ((c : ℤ) * (e + 1) - ∑ i, b i) + ((r : ℤ) * (e + 1) + ∑ j, a j) := by
      intro e he
      have h := finrank_piece_le_perp (K := K) (n := n) hvhom e
      rw [hvsp, hPdef, perpOf_perpOf_centralizer N M, ← hCdef] at h
      have hcast : ((Module.finrank K
            ((Graded.GradedPresentation.of K (shiftSrc n)).piece e) : ℕ) : ℤ)
          ≤ ((Module.finrank K ((Graded.GradedPresentation.of K (shiftSrc n)).sub C e) : ℕ) : ℤ)
            + ((∑ j, (e + a j + 1).toNat : ℕ) : ℤ) := by
        exact_mod_cast h
      have hCe : ((Module.finrank K
            ((Graded.GradedPresentation.of K (shiftSrc n)).sub C e) : ℕ) : ℤ)
          = (c : ℤ) * (e + 1) - ∑ i, b i := by
        rw [hChil e]
        have h := cast_sum_sub b e (fun i => by
          have h1 : Eb ≤ e := le_trans (le_trans (le_max_right Ea Eb) (le_max_left _ _)) he
          have := hEb i; omega)
        simpa using h
      have hane : ∀ j, (0 : ℤ) ≤ e + a j + 1 := fun j => by
        have := hann j
        have h1 : (1 : ℤ) ≤ e := le_trans (le_max_right _ _) he
        omega
      rw [hFe e (by omega), hCe, cast_sum_add a e hane] at hcast
      simpa using hcast
    have h1 := hB1 E₀ (le_refl _)
    have h2 := hB2 E₀ (le_refl _)
    have : (r : ℤ) * (E₀ + 1) + (c : ℤ) * (E₀ + 1) = (n * n : ℤ) * (E₀ + 1) := by
      rw [← add_mul, hrc]
    linarith
  -- the gap
  have hgap : ∃ E : ℤ, ∀ e, E ≤ e →
      Module.finrank K ((Graded.GradedPresentation.of K a).sub S e) + 2 * dimFl τ
        = Module.finrank K ((Graded.GradedPresentation.of K a).piece e) + 2 * sumb := by
    refine ⟨E₀, fun e he => ?_⟩
    have hdim : (2 * dimFl τ : ℤ) = (n * n : ℤ) - c := by
      have h := two_dimFl τ
      have hle := cType_le τ
      rw [hcτ]
      omega
    have hL : ((Module.finrank K ((Graded.GradedPresentation.of K a).sub S e) : ℕ) : ℤ)
        = (n * n : ℤ) * e - ((c : ℤ) * e - ∑ i, b i) := by
      rw [hSfin e, hAe e he]
    have hR : ((Module.finrank K ((Graded.GradedPresentation.of K a).piece e) : ℕ) : ℤ)
        = (r : ℤ) * (e + 1) - ∑ j, a j := by
      rw [hfreefin e, hPe e he]
    have : ((Module.finrank K ((Graded.GradedPresentation.of K a).sub S e) + 2 * dimFl τ : ℕ) : ℤ)
        = ((Module.finrank K ((Graded.GradedPresentation.of K a).piece e) + 2 * sumb : ℕ) : ℤ) := by
      push_cast
      rw [hL, hR, hsumb, hab]
      linear_combination (-(e + 1) : ℤ) * hrc + hdim
    exact_mod_cast this
  -- `lem:local-length` and the sum over the drop points
  obtain ⟨Tg, hTg⟩ := Graded.exists_finset_zeros hg hgmu
  have hmain := sum_b_add_half_len_eq_dimFl (K := K) Tg hSgr hg hgmu hgS hTg
    (dimFl τ) sumb hgap
  have hbr : ∀ t₀ : K, Module.finrank K (localQuot K r t₀ S) = lenX N M t₀ :=
    fun t₀ => finrank_localQuot_eq_lenX N M a v hvhom hvli
      (by rw [hvsp, hPdef, hCdef]) t₀
  have hzeroOffTg : ∀ t₀ : K, t₀ ∉ Tg → lenX N M t₀ = 0 := by
    intro t₀ ht
    rw [← hbr t₀]
    exact Graded.finrank_localQuot_of_ne t₀ hgS (Graded.deh_ne_zero hg hgmu)
      (fun hc => ht (hTg t₀ hc))
  have hzeroOffTset : ∀ t₀ : K, t₀ ∉ Tset → lenX N M t₀ = 0 := fun t₀ ht =>
    lenX_eq_zero_of_not_dropPoint hnil hgen (fun hdrop => ht (hTset t₀ hdrop))
  have hsum1 : ∑ t₀ ∈ Tset, lenX N M t₀ = ∑ t₀ ∈ Tset ∪ Tg, lenX N M t₀ :=
    Finset.sum_subset Finset.subset_union_left fun t₀ _ ht => hzeroOffTset t₀ ht
  have hsum2 : ∑ t₀ ∈ Tg, lenX N M t₀ = ∑ t₀ ∈ Tset ∪ Tg, lenX N M t₀ :=
    Finset.sum_subset Finset.subset_union_right fun t₀ _ ht => hzeroOffTg t₀ ht
  have hTgsum : ∑ t₀ ∈ Tg, Module.finrank K (localQuot K r t₀ S)
      = ∑ t₀ ∈ Tset, lenX N M t₀ := by
    rw [Finset.sum_congr rfl fun t₀ _ => hbr t₀, hsum2, ← hsum1]
  rw [hTgsum] at hmain
  have hz := congrArg (fun m : ℕ => (m : ℤ)) hmain
  push_cast at hz ⊢
  rw [hsumb] at hz
  linarith

end Assembly

end Height.Pencil
