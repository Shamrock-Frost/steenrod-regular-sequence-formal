import Height.Toolbox.MinorRank
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Integer

/-!
# Saturation and base change for submodules of a finite free module

The general linear algebra behind the local length bridge of `lem:selfdual-degree`,
with no pencils in it.  Throughout `D` is a principal ideal domain, `R` a domain
and `φ : D →+* R` an injective ring homomorphism; the instance used in the pencil
layer is `D = K[t]`, `R = K⟦u⟧` and `φ = Graded.iota K t₀`, the Taylor expansion at
a point of the line.

* `mapSpan φ S` is the base change `S ⊗_D R` of a submodule of `D^q`, realised as
  the `R`-span of the coordinatewise `φ`-image.
* `range_map_mulVecLin`: **images** commute with base change, with no hypothesis on
  `φ` at all.
* `ker_map_eq_mapSpan`: **kernels** commute with base change out of a principal
  ideal domain, for rectangular matrices.  `ker_map_mulVecLin_eq_bot` is the
  injective case.
* `satOf S` is the saturation `{x | ∃ f ≠ 0, f • x ∈ S}` of a submodule over a
  domain — mathlib has no submodule saturation.  `mapSpan_satOf`: **saturations**
  commute with base change out of a principal ideal domain.  The mechanism is that
  over a principal ideal domain a saturated submodule is spanned by part of a basis
  of the ambient module (`exists_basis_span_of_satOf`), and being spanned by part of
  a basis is preserved by base change (`mapBasis`).
-/

namespace Height.Toolbox

open Matrix

universe u

/-! ### Spans of a subfamily of the standard basis -/

section StdSpan

variable {F : Type u} [Field F] {n k : ℕ}

/-- The span of the standard basis vectors indexed by the range of `f`. -/
noncomputable def stdSpan (F : Type u) [Field F] {n k : ℕ} (f : Fin k ↪ Fin n) :
    Submodule F (Fin n → F) :=
  Submodule.span F (Set.range fun i : Fin k => (Pi.single (f i) 1 : Fin n → F))

theorem mem_stdSpan_of_vanishing (f : Fin k ↪ Fin n) (y : Fin n → F)
    (h : ∀ j, j ∉ Set.range f → y j = 0) : y ∈ stdSpan F f := by
  classical
  have hy : y = ∑ i : Fin k, y (f i) • (Pi.single (f i) 1 : Fin n → F) := by
    funext j
    rw [Finset.sum_apply]
    by_cases hj : j ∈ Set.range f
    · obtain ⟨i, rfl⟩ := hj
      rw [Finset.sum_eq_single i]
      · simp
      · intro b _ hb
        have hne : f b ≠ f i := fun h => hb (f.injective h)
        simp [hne]
      · intro hcon; exact absurd (Finset.mem_univ i) hcon
    · rw [h j hj, Finset.sum_eq_zero]
      intro i _
      have hne : f i ≠ j := fun hh => hj ⟨i, hh⟩
      simp [hne]
  rw [hy]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem vanishing_of_mem_stdSpan (f : Fin k ↪ Fin n) {y : Fin n → F} (hy : y ∈ stdSpan F f) :
    ∀ j, j ∉ Set.range f → y j = 0 := by
  classical
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp hy
  intro j hj
  rw [← hc, Finset.sum_apply, Finset.sum_eq_zero]
  intro i _
  have hne : f i ≠ j := fun hh => hj ⟨i, hh⟩
  simp [hne]

theorem finrank_stdSpan (f : Fin k ↪ Fin n) :
    Module.finrank F (stdSpan F f) = k := by
  classical
  have hli : LinearIndependent F (fun i : Fin k => (Pi.single (f i) 1 : Fin n → F)) := by
    have h := (Pi.basisFun F (Fin n)).linearIndependent.comp f f.injective
    simpa [Function.comp_def] using h
  rw [stdSpan, finrank_span_eq_card hli, Fintype.card_fin]

end StdSpan

/-! ### Rank is read off the minors, so it is insensitive to the coefficient field -/

section RankMinors

/-- The rank of the image of an integral matrix under an injective ring homomorphism into a
field is the largest size of a nonvanishing minor of the matrix itself. -/
theorem le_rank_map_iff {A : Type u} [CommRing A] {p q : ℕ} {F : Type u} [Field F]
    (X : Matrix (Fin p) (Fin q) A) (ψ : A →+* F) (hψ : Function.Injective ψ) (k : ℕ) :
    k ≤ (X.map ψ).rank ↔
      ∃ (f : Fin k → Fin p) (g : Fin k → Fin q), (X.submatrix f g).det ≠ 0 := by
  have hdet : ∀ M : Matrix (Fin k) (Fin k) A, (M.map (ψ : A → F)).det = ψ M.det := by
    intro M
    rw [RingHom.map_det ψ M, RingHom.mapMatrix_apply]
  rw [Height.Toolbox.le_rank_iff_exists_submatrix_det_ne_zero]
  constructor
  · rintro ⟨f, g, hd⟩
    refine ⟨f, g, fun hz => hd ?_⟩
    rw [Matrix.submatrix_map, hdet, hz, map_zero]
  · rintro ⟨f, g, hd⟩
    refine ⟨f, g, ?_⟩
    rw [Matrix.submatrix_map, hdet]
    exact fun hz => hd (hψ (by rw [hz, map_zero]))

/-- Two injective ring homomorphisms of an integral matrix into fields give the same rank. -/
theorem rank_map_eq_rank_map {A : Type u} [CommRing A] {p q : ℕ}
    {F₁ F₂ : Type u} [Field F₁] [Field F₂]
    (X : Matrix (Fin p) (Fin q) A) (ψ₁ : A →+* F₁) (ψ₂ : A →+* F₂)
    (h₁ : Function.Injective ψ₁) (h₂ : Function.Injective ψ₂) :
    (X.map ψ₁).rank = (X.map ψ₂).rank :=
  le_antisymm ((le_rank_map_iff X ψ₂ h₂ _).2 ((le_rank_map_iff X ψ₁ h₁ _).1 le_rfl))
    ((le_rank_map_iff X ψ₁ h₁ _).2 ((le_rank_map_iff X ψ₂ h₂ _).1 le_rfl))

end RankMinors

/-! ### The saturation of a submodule over a domain -/

section Sat

variable {R : Type*} [CommRing R] [IsDomain R]
variable {M : Type*} [AddCommGroup M] [Module R M]

/-- The saturation of a submodule of a module over a domain: the elements some nonzero
multiple of which lies in the submodule.  Over a domain this is again a submodule. -/
def satOf (S : Submodule R M) : Submodule R M where
  carrier := {x | ∃ f : R, f ≠ 0 ∧ f • x ∈ S}
  add_mem' := by
    rintro x y ⟨f, hf, hfx⟩ ⟨g, hg, hgy⟩
    refine ⟨f * g, mul_ne_zero hf hg, ?_⟩
    have h1 : (f * g) • (x + y) = g • (f • x) + f • (g • y) := by
      rw [smul_add]
      congr 1
      · rw [mul_comm, mul_smul]
      · rw [mul_smul]
    rw [h1]
    exact S.add_mem (S.smul_mem g hfx) (S.smul_mem f hgy)
  zero_mem' := ⟨1, one_ne_zero, by simp⟩
  smul_mem' := by
    rintro c x ⟨f, hf, hfx⟩
    exact ⟨f, hf, by rw [smul_comm]; exact S.smul_mem c hfx⟩

theorem le_satOf (S : Submodule R M) : S ≤ satOf S :=
  fun _ hx => ⟨1, one_ne_zero, by simpa using hx⟩

theorem satOf_mono {S T : Submodule R M} (h : S ≤ T) : satOf S ≤ satOf T := by
  rintro x ⟨f, hf, hfx⟩
  exact ⟨f, hf, h hfx⟩

theorem satOf_satOf (S : Submodule R M) : satOf (satOf S) = satOf S := by
  refine le_antisymm ?_ (le_satOf _)
  rintro x ⟨f, hf, g, hg, hgf⟩
  exact ⟨g * f, mul_ne_zero hg hf, by rwa [mul_smul]⟩

/-- A submodule is saturated as soon as its saturation is contained in it. -/
theorem satOf_eq_self_of_le {S : Submodule R M} (h : satOf S ≤ S) : satOf S = S :=
  le_antisymm h (le_satOf S)

end Sat

/-! ### Base change of a submodule of `D^q` -/

section MapSpan

variable {D R : Type*} [CommRing D] [CommRing R] {p q : ℕ}

/-- The base change of a `D`-submodule of `D^q` along `φ : D →+* R`: the `R`-span of the
coordinatewise `φ`-image. -/
def mapSpan (φ : D →+* R) (S : Submodule D (Fin q → D)) : Submodule R (Fin q → R) :=
  Submodule.span R ((fun v : Fin q → D => fun i => φ (v i)) '' (S : Set (Fin q → D)))

theorem mem_mapSpan {φ : D →+* R} {S : Submodule D (Fin q → D)} {v : Fin q → D} (hv : v ∈ S) :
    (fun i => φ (v i)) ∈ mapSpan φ S :=
  Submodule.subset_span ⟨v, hv, rfl⟩

theorem mapSpan_le {φ : D →+* R} {S : Submodule D (Fin q → D)} {T : Submodule R (Fin q → R)} :
    mapSpan φ S ≤ T ↔ ∀ v ∈ S, (fun i => φ (v i)) ∈ T := by
  rw [mapSpan, Submodule.span_le]
  exact ⟨fun h v hv => h ⟨v, hv, rfl⟩, by rintro h _ ⟨v, hv, rfl⟩; exact h v hv⟩

theorem mapSpan_mono {φ : D →+* R} {S T : Submodule D (Fin q → D)} (h : S ≤ T) :
    mapSpan φ S ≤ mapSpan φ T :=
  mapSpan_le.2 fun _ hv => mem_mapSpan (h hv)

theorem mapSpan_bot (φ : D →+* R) : mapSpan (q := q) φ ⊥ = ⊥ := by
  refine le_antisymm (mapSpan_le.2 fun v hv => ?_) bot_le
  rw [Submodule.mem_bot] at hv
  subst hv
  have h0 : (fun i => φ ((0 : Fin q → D) i)) = (0 : Fin q → R) := by funext i; simp
  rw [h0]
  exact Submodule.zero_mem _

theorem mapSpan_span (φ : D →+* R) (s : Set (Fin q → D)) :
    mapSpan φ (Submodule.span D s)
      = Submodule.span R ((fun v : Fin q → D => fun i => φ (v i)) '' s) := by
  refine le_antisymm (mapSpan_le.2 fun v hv => ?_) (Submodule.span_le.2 ?_)
  · induction hv using Submodule.span_induction with
    | mem w hw => exact Submodule.subset_span ⟨w, hw, rfl⟩
    | zero =>
        have h0 : (fun i => φ ((0 : Fin q → D) i)) = (0 : Fin q → R) := by funext i; simp
        rw [h0]
        exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
        have h0 : (fun i => φ ((x + y) i)) = (fun i => φ (x i)) + (fun i => φ (y i)) := by
          funext i; simp
        rw [h0]
        exact Submodule.add_mem _ hx hy
    | smul c x _ hx =>
        have h0 : (fun i => φ ((c • x) i)) = φ c • (fun i => φ (x i)) := by
          funext i; simp [smul_eq_mul]
        rw [h0]
        exact Submodule.smul_mem _ _ hx
  · rintro _ ⟨v, hv, rfl⟩
    exact mem_mapSpan (Submodule.subset_span hv)

/-- **Images commute with base change.**  No hypothesis on `φ` is needed: the image of a
matrix is spanned by its columns. -/
theorem range_map_mulVecLin (A : Matrix (Fin p) (Fin q) D) (φ : D →+* R) :
    LinearMap.range ((A.map φ).mulVecLin) = mapSpan φ (LinearMap.range A.mulVecLin) := by
  classical
  refine le_antisymm ?_ (mapSpan_le.2 ?_)
  · rintro _ ⟨w, rfl⟩
    have hsum : (A.map φ) *ᵥ w = ∑ j, w j • (fun i => φ (A i j)) := by
      funext i
      rw [Matrix.mulVec_apply_eq_sum, Finset.sum_apply]
      exact Finset.sum_congr rfl fun j _ => by
        rw [Matrix.map_apply, Pi.smul_apply, smul_eq_mul, mul_comm]
    show (A.map φ) *ᵥ w ∈ _
    rw [hsum]
    refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_
    have hcol : (fun i => φ (A i j)) = fun i => φ ((A *ᵥ Pi.single j (1 : D)) i) := by
      funext i
      rw [Matrix.mulVec_single_one, Matrix.col_apply]
    rw [hcol]
    exact mem_mapSpan ⟨Pi.single j (1 : D), rfl⟩
  · rintro _ ⟨v, rfl⟩
    exact ⟨fun j => φ (v j), funext fun i => (RingHom.map_mulVec φ A v i).symm⟩

end MapSpan

/-! ### A basis of `D^q` and its base change -/

section MapBasis

variable {D R : Type*} [CommRing D] [CommRing R] {q : ℕ}

/-- The matrix whose columns are the members of a basis of `D^q`. -/
noncomputable def basisMat (bM : Module.Basis (Fin q) D (Fin q → D)) :
    Matrix (Fin q) (Fin q) D :=
  (Pi.basisFun D (Fin q)).toMatrix bM

theorem basisMat_apply (bM : Module.Basis (Fin q) D (Fin q → D)) (i j : Fin q) :
    basisMat bM i j = bM j i := by
  rw [basisMat, Module.Basis.toMatrix_apply, Pi.basisFun_repr]

/-- The base-changed basis matrix expands a vector of coordinates in the transported
family. -/
theorem map_basisMat_mulVec (bM : Module.Basis (Fin q) D (Fin q → D)) (φ : D →+* R)
    (w : Fin q → R) :
    (basisMat bM).map φ *ᵥ w = ∑ j, w j • (fun i => φ (bM j i)) := by
  funext i
  rw [Matrix.mulVec_apply_eq_sum, Finset.sum_apply]
  exact Finset.sum_congr rfl fun j _ => by
    rw [Matrix.map_apply, basisMat_apply, Pi.smul_apply, smul_eq_mul, mul_comm]

theorem isUnit_det_map_basisMat (bM : Module.Basis (Fin q) D (Fin q → D)) (φ : D →+* R) :
    IsUnit (((basisMat bM).map φ).det) := by
  have h : basisMat bM * bM.toMatrix (Pi.basisFun D (Fin q)) = 1 :=
    Module.Basis.toMatrix_mul_toMatrix_flip _ _
  have h2 : ((basisMat bM).map φ) * ((bM.toMatrix (Pi.basisFun D (Fin q))).map φ) = 1 := by
    rw [← Matrix.map_mul, h, Matrix.map_one _ (map_zero φ) (map_one φ)]
  exact IsUnit.of_mul_eq_one _ (by rw [← Matrix.det_mul, h2, Matrix.det_one])

theorem eq_zero_of_sum_smul_map_basis_eq_zero (bM : Module.Basis (Fin q) D (Fin q → D))
    (φ : D →+* R) {w : Fin q → R}
    (h : ∑ j, w j • (fun i => φ (bM j i)) = (0 : Fin q → R)) : w = 0 := by
  have h0 : (basisMat bM).map φ *ᵥ w = 0 := by rw [map_basisMat_mulVec, h]
  have h1 := congrArg (fun y => ((basisMat bM).map φ)⁻¹ *ᵥ y) h0
  simpa [Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ (isUnit_det_map_basisMat bM φ)] using h1

/-- A basis of `D^q` transported along a ring homomorphism into a domain: the basis matrix
stays invertible, so the coordinatewise images are again a basis. -/
noncomputable def mapBasis (bM : Module.Basis (Fin q) D (Fin q → D)) (φ : D →+* R) :
    Module.Basis (Fin q) R (Fin q → R) :=
  Module.Basis.mk (v := fun j => fun i => φ (bM j i))
    (Fintype.linearIndependent_iff.2 fun w hw j =>
      congrFun (eq_zero_of_sum_smul_map_basis_eq_zero bM φ hw) j)
    (fun y _ => by
      refine (Submodule.mem_span_range_iff_exists_fun R).2
        ⟨((basisMat bM).map φ)⁻¹ *ᵥ y, ?_⟩
      rw [← map_basisMat_mulVec, Matrix.mulVec_mulVec,
        Matrix.mul_nonsing_inv _ (isUnit_det_map_basisMat bM φ), Matrix.one_mulVec])

@[simp] theorem mapBasis_apply (bM : Module.Basis (Fin q) D (Fin q → D)) (φ : D →+* R)
    (j : Fin q) : mapBasis bM φ j = fun i => φ (bM j i) := by
  rw [mapBasis, Module.Basis.mk_apply]

end MapBasis

/-! ### Base change out of a principal ideal domain -/

section BaseChange

variable {D : Type u} [CommRing D] [IsDomain D] [IsPrincipalIdealRing D]
variable {R : Type u} [CommRing R] [IsDomain R]

/-- **Kernel base change.**  Over a principal ideal domain the kernel of a matrix is spanned by
part of a basis of the ambient free module; along any injective ring homomorphism into a domain
the kernel of the image is therefore spanned by the images of the kernel.  (Concretely: the
kernel of `P^k` over `K⟦u⟧` is generated by the kernel of `P^k` over `K[t]`.) -/
theorem ker_map_eq_mapSpan {p q : ℕ} (A : Matrix (Fin p) (Fin q) D) (φ : D →+* R)
    (hφ : Function.Injective φ) :
    LinearMap.ker ((A.map φ).mulVecLin) = mapSpan φ (LinearMap.ker A.mulVecLin) := by
  classical
  obtain ⟨k, snf⟩ :=
    Submodule.smithNormalForm (Pi.basisFun D (Fin q)) (LinearMap.ker A.mulVecLin)
  -- the diagonal entries are nonzero
  have hane : ∀ i, snf.a i ≠ 0 := by
    intro i hai
    have h0 : ((snf.bN i : LinearMap.ker A.mulVecLin) : Fin q → D) = 0 := by
      rw [snf.snf i, hai, zero_smul]
    exact snf.bN.ne_zero i (Subtype.ext h0)
  -- the kernel is saturated, so the basis vectors indexed by `range f` lie in it
  have hkerf : ∀ i, snf.bM (snf.f i) ∈ LinearMap.ker A.mulVecLin := by
    intro i
    have h2 := (snf.bN i).2
    rw [snf.snf i] at h2
    have h1 : A *ᵥ (snf.a i • snf.bM (snf.f i)) = 0 := h2
    rw [Matrix.mulVec_smul] at h1
    show A *ᵥ snf.bM (snf.f i) = 0
    funext r
    have h4 := congrFun h1 r
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h4
    exact (mul_eq_zero.mp h4).resolve_left (hane i)
  have hkerf' : ∀ i, A *ᵥ snf.bM (snf.f i) = 0 := fun i => hkerf i
  -- the change-of-basis matrices
  set G : Matrix (Fin q) (Fin q) D := (Pi.basisFun D (Fin q)).toMatrix snf.bM with hGdef
  set G' : Matrix (Fin q) (Fin q) D := snf.bM.toMatrix (Pi.basisFun D (Fin q)) with hG'def
  have hGentry : ∀ i j, G i j = snf.bM j i := fun i j => by
    rw [hGdef, Module.Basis.toMatrix_apply, Pi.basisFun_repr]
  have hGG' : G * G' = 1 := Module.Basis.toMatrix_mul_toMatrix_flip _ _
  -- `G` is the matrix of the basis: `G *ᵥ y = ∑ j, y j • bM j`, over any base ring
  have hGmap : ∀ {S : Type u} [CommRing S] (ψ : D →+* S) (y : Fin q → S),
      (G.map ψ) *ᵥ y = ∑ j, y j • (fun i => ψ (snf.bM j i)) := by
    intro S _ ψ y
    funext i
    rw [Matrix.mulVec_apply_eq_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl fun j _ => by
      rw [Matrix.map_apply, hGentry, Pi.smul_apply, smul_eq_mul, mul_comm]
  have hGmulD : ∀ y : Fin q → D, G *ᵥ y = ∑ j, y j • snf.bM j := by
    intro y
    funext i
    rw [Matrix.mulVec_apply_eq_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl fun j _ => by
      rw [hGentry, Pi.smul_apply, smul_eq_mul, mul_comm]
  have hGrepr : ∀ (y : Fin q → D) (j : Fin q), snf.bM.repr (G *ᵥ y) j = y j := by
    intro y j
    have h1 : G *ᵥ y = snf.bM.equivFun.symm y := by
      rw [Module.Basis.equivFun_symm_apply]
      exact hGmulD y
    rw [h1, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  -- the matrix `H = A G`, whose columns indexed by `range f` vanish
  set H : Matrix (Fin p) (Fin q) D := A * G with hHdef
  have hHcol : ∀ i r, H r (snf.f i) = 0 := by
    intro i r
    have h1 : (A *ᵥ snf.bM (snf.f i)) r = 0 := congrFun (hkerf' i) r
    rw [Matrix.mulVec_apply_eq_sum] at h1
    rw [hHdef, Matrix.mul_apply, ← h1]
    exact Finset.sum_congr rfl fun l _ => by rw [hGentry]
  -- the kernel of `H` over any base ring contains the standard vectors indexed by `range f`
  have hHker : ∀ {S : Type u} [CommRing S] (ψ : D →+* S) (i : Fin k),
      (H.map ψ) *ᵥ (Pi.single (snf.f i) (1 : S)) = 0 := by
    intro S _ ψ i
    funext r
    show ((H.map ψ) *ᵥ (Pi.single (snf.f i) (1 : S))) r = 0
    rw [Matrix.mulVec_apply_eq_sum, Finset.sum_eq_single (snf.f i)]
    · rw [Matrix.map_apply, hHcol i r, map_zero, zero_mul]
    · intro b _ hb
      simp [hb]
    · intro hcon; exact absurd (Finset.mem_univ (snf.f i)) hcon
  -- and, over `D`, nothing else
  have hHkerD : ∀ y : Fin q → D, H *ᵥ y = 0 → ∀ j, j ∉ Set.range snf.f → y j = 0 := by
    intro y hy j hj
    have hmem : G *ᵥ y ∈ LinearMap.ker A.mulVecLin := by
      show A *ᵥ (G *ᵥ y) = 0
      rw [Matrix.mulVec_mulVec]
      exact hy
    have h0 : snf.bM.repr (G *ᵥ y) j = 0 :=
      snf.repr_eq_zero_of_notMem_range ⟨G *ᵥ y, hmem⟩ hj
    exact (hGrepr y j).symm.trans h0
  -- the two fraction fields
  set E := FractionRing D with hEdef
  set E' := FractionRing R with hE'def
  have hiD : Function.Injective (algebraMap D E) := IsFractionRing.injective D E
  have hiR : Function.Injective (algebraMap R E') := IsFractionRing.injective R E'
  -- over `E` the kernel of `H` is exactly the span of the standard vectors
  have hkerE : LinearMap.ker ((H.map (algebraMap D E)).mulVecLin) = stdSpan E snf.f := by
    refine le_antisymm ?_ ?_
    · intro y hy
      have hy' : (H.map (algebraMap D E)) *ᵥ y = 0 := hy
      obtain ⟨d, hd⟩ :=
        IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors D) y
      choose y' hy'' using fun i => RingHom.mem_rangeS.mp (hd i)
      have hcomp : (algebraMap D E : D → E) ∘ y' = (algebraMap D E (d : D)) • y := by
        funext i
        show algebraMap D E (y' i) = _
        rw [hy'' i]
        show (d : D) • y i = algebraMap D E (d : D) * y i
        rw [Algebra.smul_def]
      have hy'D : H *ᵥ y' = 0 := by
        funext r
        apply hiD
        rw [RingHom.map_mulVec (algebraMap D E) H y' r, hcomp, Matrix.mulVec_smul,
          Pi.smul_apply, congrFun hy' r]
        simp
      have hdne : (algebraMap D E (d : D)) ≠ 0 :=
        (map_ne_zero_iff _ hiD).mpr (nonZeroDivisors.coe_ne_zero d)
      refine mem_stdSpan_of_vanishing snf.f y fun j hj => ?_
      have h1 : y' j = 0 := hHkerD y' hy'D j hj
      have h2 : algebraMap D E (d : D) * y j = 0 := by
        have h3 := hy'' j
        rw [h1, map_zero, Algebra.smul_def] at h3
        exact h3.symm
      exact (mul_eq_zero.mp h2).resolve_left hdne
    · rw [stdSpan, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact hHker (algebraMap D E) i
  -- the two ranks of `H` agree
  have hcompinj : Function.Injective ((algebraMap R E').comp φ) := by
    rw [RingHom.coe_comp]
    exact hiR.comp hφ
  have hrank : (H.map (algebraMap D E)).rank = (H.map ((algebraMap R E').comp φ)).rank :=
    rank_map_eq_rank_map H (algebraMap D E) ((algebraMap R E').comp φ) hiD hcompinj
  -- so over `E'` the kernel of `H` is again exactly that span
  have hkerE' :
      LinearMap.ker ((H.map ((algebraMap R E').comp φ)).mulVecLin) = stdSpan E' snf.f := by
    have hle :
        stdSpan E' snf.f ≤ LinearMap.ker ((H.map ((algebraMap R E').comp φ)).mulVecLin) := by
      rw [stdSpan, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact hHker ((algebraMap R E').comp φ) i
    refine (Submodule.eq_of_le_of_finrank_le hle ?_).symm
    have h1 := LinearMap.finrank_range_add_finrank_ker (H.map (algebraMap D E)).mulVecLin
    have h2 := LinearMap.finrank_range_add_finrank_ker
      (H.map ((algebraMap R E').comp φ)).mulVecLin
    rw [Module.finrank_fin_fun] at h1 h2
    rw [hkerE, finrank_stdSpan] at h1
    rw [finrank_stdSpan]
    have h3 : (H.map (algebraMap D E)).rank
        = Module.finrank E (LinearMap.range (H.map (algebraMap D E)).mulVecLin) := rfl
    have h4 : (H.map ((algebraMap R E').comp φ)).rank
        = Module.finrank E' (LinearMap.range (H.map ((algebraMap R E').comp φ)).mulVecLin) := rfl
    rw [h3, h4] at hrank
    omega
  refine le_antisymm ?_ ?_
  · intro w hw
    have hw' : (A.map φ) *ᵥ w = 0 := hw
    set c : Fin q → R := (G'.map φ) *ᵥ w with hcdef
    have hGc : (G.map φ) *ᵥ c = w := by
      rw [hcdef, Matrix.mulVec_mulVec, ← Matrix.map_mul, hGG',
        Matrix.map_one (⇑φ) (map_zero φ) (map_one φ), Matrix.one_mulVec]
    have hHc : (H.map φ) *ᵥ c = 0 := by
      rw [hHdef, Matrix.map_mul, ← Matrix.mulVec_mulVec, hGc, hw']
    have hmm : H.map ((algebraMap R E').comp φ) = (H.map φ).map (algebraMap R E') := by
      rw [Matrix.map_map]
      rfl
    have hHcE :
        (H.map ((algebraMap R E').comp φ)) *ᵥ (fun j => algebraMap R E' (c j)) = 0 := by
      rw [hmm]
      funext r
      have h5 := RingHom.map_mulVec (algebraMap R E') (H.map φ) c r
      rw [congrFun hHc r, Pi.zero_apply, map_zero] at h5
      exact h5.symm
    have hcmem : (fun j => algebraMap R E' (c j)) ∈ stdSpan E' snf.f := by
      rw [← hkerE']
      exact hHcE
    have hczero : ∀ j, j ∉ Set.range snf.f → c j = 0 := fun j hj =>
      hiR (by rw [vanishing_of_mem_stdSpan snf.f hcmem j hj, map_zero])
    rw [← hGc, hGmap φ c]
    refine Submodule.sum_mem _ fun j _ => ?_
    by_cases hj : j ∈ Set.range snf.f
    · obtain ⟨i, rfl⟩ := hj
      exact Submodule.smul_mem _ _ (mem_mapSpan (hkerf i))
    · rw [hczero j hj, zero_smul]
      exact Submodule.zero_mem _
  · rw [mapSpan, Submodule.span_le]
    rintro _ ⟨v, hv, rfl⟩
    have hv' : A *ᵥ v = 0 := hv
    show (A.map φ) *ᵥ (fun i => φ (v i)) = 0
    funext r
    have h6 := RingHom.map_mulVec φ A v r
    rw [hv'] at h6
    simpa [Function.comp_def] using h6.symm

/-- **Injectivity survives base change** out of a principal ideal domain. -/
theorem ker_map_mulVecLin_eq_bot {p q : ℕ} (A : Matrix (Fin p) (Fin q) D) (φ : D →+* R)
    (hφ : Function.Injective φ) (hker : LinearMap.ker A.mulVecLin = ⊥) :
    LinearMap.ker ((A.map φ).mulVecLin) = ⊥ := by
  rw [ker_map_eq_mapSpan A φ hφ, hker, mapSpan_bot]

/-- Over a principal ideal domain a saturated submodule of `D^q` is spanned by part of a
basis of `D^q`: the Smith diagonal entries of a saturated submodule are units. -/
theorem exists_basis_span_of_satOf {q : ℕ} {S : Submodule D (Fin q → D)} (hS : satOf S = S) :
    ∃ (k : ℕ) (bM : Module.Basis (Fin q) D (Fin q → D)) (f : Fin k ↪ Fin q),
      S = Submodule.span D (Set.range fun i => bM (f i)) := by
  classical
  obtain ⟨k, snf⟩ := Submodule.smithNormalForm (Pi.basisFun D (Fin q)) S
  have hane : ∀ i, snf.a i ≠ 0 := by
    intro i hai
    have h0 : ((snf.bN i : S) : Fin q → D) = 0 := by rw [snf.snf i, hai, zero_smul]
    exact snf.bN.ne_zero i (Subtype.ext h0)
  have hmem : ∀ i, snf.bM (snf.f i) ∈ S := by
    intro i
    have hsat : snf.bM (snf.f i) ∈ satOf S :=
      ⟨snf.a i, hane i, by rw [← snf.snf i]; exact (snf.bN i).2⟩
    rwa [hS] at hsat
  refine ⟨k, snf.bM, snf.f, le_antisymm (fun x hx => ?_) ?_⟩
  · have hrepr := snf.bN.sum_repr ⟨x, hx⟩
    have h2 : ∑ i, (snf.bN.repr ⟨x, hx⟩) i • ((snf.bN i : S) : Fin q → D) = x := by
      have h3 := congrArg (Submodule.subtype S) hrepr
      rw [map_sum] at h3
      simpa using h3
    have h4 : ∑ i, (snf.bN.repr ⟨x, hx⟩) i • ((snf.bN i : S) : Fin q → D)
        = ∑ i, ((snf.bN.repr ⟨x, hx⟩) i * snf.a i) • snf.bM (snf.f i) :=
      Finset.sum_congr rfl fun i _ => by rw [snf.snf i, smul_smul]
    rw [← h2, h4]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hmem i

/-- **A saturated submodule stays saturated under base change.** -/
theorem satOf_mapSpan_of_satOf {q : ℕ} (φ : D →+* R)
    {S : Submodule D (Fin q → D)} (hS : satOf S = S) :
    satOf (mapSpan φ S) = mapSpan φ S := by
  classical
  obtain ⟨k, bM, f, hspan⟩ := exists_basis_span_of_satOf hS
  have himg : (fun v : Fin q → D => fun i => φ (v i)) '' (Set.range fun i => bM (f i))
      = mapBasis bM φ '' Set.range f := by
    ext y
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨f i, ⟨i, rfl⟩, by rw [mapBasis_apply]⟩
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨bM (f i), ⟨i, rfl⟩, by rw [mapBasis_apply]⟩
  have hmap : mapSpan φ S = Submodule.span R (mapBasis bM φ '' Set.range f) := by
    rw [hspan, mapSpan_span, himg]
  refine satOf_eq_self_of_le ?_
  rintro y ⟨c, hc, hcy⟩
  rw [hmap] at hcy ⊢
  rw [Module.Basis.mem_span_image] at hcy ⊢
  intro j hj
  refine hcy ?_
  rw [Finset.mem_coe, Finsupp.mem_support_iff] at hj ⊢
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
  exact mul_ne_zero hc hj

/-- **Saturation commutes with base change** out of a principal ideal domain. -/
theorem mapSpan_satOf {q : ℕ} (φ : D →+* R) (hφ : Function.Injective φ)
    (S : Submodule D (Fin q → D)) :
    mapSpan φ (satOf S) = satOf (mapSpan φ S) := by
  refine le_antisymm (mapSpan_le.2 ?_) ?_
  · rintro v ⟨g, hg, hgv⟩
    refine ⟨φ g, fun hz => hg (hφ (by rw [hz, map_zero])), ?_⟩
    have h0 : φ g • (fun i => φ (v i)) = fun i => φ ((g • v) i) := by
      funext i; simp [smul_eq_mul]
    rw [h0]
    exact mem_mapSpan hgv
  · have h1 : satOf (mapSpan φ (satOf S)) = mapSpan φ (satOf S) :=
      satOf_mapSpan_of_satOf φ (satOf_satOf S)
    rw [← h1]
    exact satOf_mono (mapSpan_mono (le_satOf S))

end BaseChange

/-! ### Kernel lifting from the special fibre of a power-series matrix -/

section PowerSeriesKernelLift

variable {K : Type u} [Field K]

/-- The finite-coordinate core of `exists_kernel_lift`.  The kernel over the DVR is
saturated, hence is spanned by part of an ambient basis.  `ker_map_eq_mapSpan` identifies
the generic-fibre kernel with the span of the transported part of that basis; equality of
generic and special ranks then says that its reductions span the whole special-fibre
kernel. -/
private theorem exists_kernel_lift_fin {p q : ℕ}
    (A : Matrix (Fin q) (Fin p) (PowerSeries K))
    (hrank : (A.map (algebraMap (PowerSeries K) (LaurentSeries K))).rank =
      (A.map (PowerSeries.constantCoeff (R := K))).rank)
    (v : Fin p → K)
    (hv : (A.map (PowerSeries.constantCoeff (R := K))) *ᵥ v = 0) :
    ∃ w : Fin p → PowerSeries K, A *ᵥ w = 0 ∧
      (fun i => PowerSeries.constantCoeff (w i)) = v := by
  classical
  have hsat : satOf (LinearMap.ker A.mulVecLin) = LinearMap.ker A.mulVecLin := by
    apply satOf_eq_self_of_le
    rintro x ⟨c, hc, hcx⟩
    rw [LinearMap.mem_ker] at hcx ⊢
    change A *ᵥ (c • x) = 0 at hcx
    change A *ᵥ x = 0
    rw [Matrix.mulVec_smul] at hcx
    funext i
    have hi := congrFun hcx i
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi
    exact (mul_eq_zero.mp hi).resolve_left hc
  obtain ⟨k, bM, f, hspan⟩ := exists_basis_span_of_satOf hsat
  let bK := mapBasis bM (PowerSeries.constantCoeff (R := K))
  let bL := mapBasis bM (algebraMap (PowerSeries K) (LaurentSeries K))
  have hkerBasis : ∀ i : Fin k, bM (f i) ∈ LinearMap.ker A.mulVecLin := by
    intro i
    rw [hspan]
    exact Submodule.subset_span ⟨i, rfl⟩
  have hmemK : ∀ i : Fin k, bK (f i) ∈
      LinearMap.ker (A.map (PowerSeries.constantCoeff (R := K))).mulVecLin := by
    intro i
    rw [LinearMap.mem_ker]
    have hzero : A *ᵥ bM (f i) = 0 := hkerBasis i
    funext r
    have hmap := RingHom.map_mulVec (PowerSeries.constantCoeff (R := K)) A (bM (f i)) r
    rw [hzero] at hmap
    simpa [bK, Function.comp_def] using hmap.symm
  have hinj : Function.Injective (algebraMap (PowerSeries K) (LaurentSeries K)) :=
    IsFractionRing.injective (PowerSeries K) (LaurentSeries K)
  have himgL :
      (fun x : Fin p → PowerSeries K =>
          fun i => algebraMap (PowerSeries K) (LaurentSeries K) (x i)) ''
          (Set.range fun i => bM (f i)) =
        Set.range fun i => bL (f i) := by
    ext y
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, by simp [bL]⟩
    · rintro ⟨i, rfl⟩
      exact ⟨bM (f i), ⟨i, rfl⟩, by simp [bL]⟩
  have hspanL :
      LinearMap.ker
          (A.map (algebraMap (PowerSeries K) (LaurentSeries K))).mulVecLin =
        Submodule.span (LaurentSeries K) (Set.range fun i => bL (f i)) := by
    rw [ker_map_eq_mapSpan A (algebraMap (PowerSeries K) (LaurentSeries K)) hinj,
      hspan, mapSpan_span, himgL]
  have hliL : LinearIndependent (LaurentSeries K) (fun i : Fin k => bL (f i)) :=
    bL.linearIndependent.comp f f.injective
  have hdimL : Module.finrank (LaurentSeries K)
      (LinearMap.ker
        (A.map (algebraMap (PowerSeries K) (LaurentSeries K))).mulVecLin) = k := by
    rw [hspanL, finrank_span_eq_card hliL, Fintype.card_fin]
  have hliK : LinearIndependent K (fun i : Fin k => bK (f i)) :=
    bK.linearIndependent.comp f f.injective
  have hrkL := LinearMap.finrank_range_add_finrank_ker
    (A.map (algebraMap (PowerSeries K) (LaurentSeries K))).mulVecLin
  have hrkK := LinearMap.finrank_range_add_finrank_ker
    (A.map (PowerSeries.constantCoeff (R := K))).mulVecLin
  rw [Module.finrank_fin_fun] at hrkL hrkK
  have hkerK : Module.finrank K
      (LinearMap.ker (A.map (PowerSeries.constantCoeff (R := K))).mulVecLin) = k := by
    have h1 : (A.map (algebraMap (PowerSeries K) (LaurentSeries K))).rank =
        Module.finrank (LaurentSeries K)
          (LinearMap.range
            (A.map (algebraMap (PowerSeries K) (LaurentSeries K))).mulVecLin) := rfl
    have h2 : (A.map (PowerSeries.constantCoeff (R := K))).rank =
        Module.finrank K
          (LinearMap.range (A.map (PowerSeries.constantCoeff (R := K))).mulVecLin) := rfl
    rw [h1, h2] at hrank
    omega
  have hspanK : Submodule.span K (Set.range fun i : Fin k => bK (f i)) =
      LinearMap.ker (A.map (PowerSeries.constantCoeff (R := K))).mulVecLin := by
    refine Submodule.eq_of_le_of_finrank_le ?_ ?_
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact hmemK i
    · rw [finrank_span_eq_card hliK, Fintype.card_fin, hkerK]
  have hvmem : v ∈ Submodule.span K (Set.range fun i : Fin k => bK (f i)) := by
    rw [hspanK, LinearMap.mem_ker]
    exact hv
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hvmem
  refine ⟨∑ i, PowerSeries.C (c i) • bM (f i), ?_, ?_⟩
  · have hmem : (∑ i, PowerSeries.C (c i) • bM (f i)) ∈
        LinearMap.ker A.mulVecLin :=
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hkerBasis i)
    rwa [LinearMap.mem_ker] at hmem
  · rw [← hc]
    funext j
    simp [bK]

/-- **Kernel lifting over a power-series DVR.**  If a matrix has the same rank on its
generic and special fibres, every vector in its special-fibre kernel is the constant term
of a kernel vector over the DVR.  The row and column types may be arbitrary finite types. -/
theorem exists_kernel_lift { ι κ : Type* } [Fintype ι] [Fintype κ]
    (A : Matrix κ ι (PowerSeries K))
    (hrank : (A.map (algebraMap (PowerSeries K) (LaurentSeries K))).rank =
      (A.map (PowerSeries.constantCoeff (R := K))).rank)
    (v : ι → K)
    (hv : (A.map (PowerSeries.constantCoeff (R := K))) *ᵥ v = 0) :
    ∃ w : ι → PowerSeries K, A *ᵥ w = 0 ∧
      (fun i => PowerSeries.constantCoeff (w i)) = v := by
  classical
  let eι := Fintype.equivFin ι
  let eκ := Fintype.equivFin κ
  let A' : Matrix (Fin (Fintype.card κ)) (Fin (Fintype.card ι)) (PowerSeries K) :=
    A.submatrix eκ.symm eι.symm
  have hmapL : A'.map (algebraMap (PowerSeries K) (LaurentSeries K)) =
      (A.map (algebraMap (PowerSeries K) (LaurentSeries K))).submatrix eκ.symm eι.symm := rfl
  have hmapC : A'.map (PowerSeries.constantCoeff (R := K)) =
      (A.map (PowerSeries.constantCoeff (R := K))).submatrix eκ.symm eι.symm := rfl
  have hrank' : (A'.map (algebraMap (PowerSeries K) (LaurentSeries K))).rank =
      (A'.map (PowerSeries.constantCoeff (R := K))).rank := by
    rw [hmapL, hmapC, Matrix.rank_submatrix, Matrix.rank_submatrix, hrank]
  have hv' : (A'.map (PowerSeries.constantCoeff (R := K))) *ᵥ (v ∘ eι.symm) = 0 := by
    rw [hmapC, Matrix.submatrix_mulVec_equiv]
    have : (v ∘ ⇑eι.symm) ∘ ⇑(eι.symm).symm = v := by
      funext i
      simp
    rw [this, hv]
    rfl
  obtain ⟨w', hw'0, hw'C⟩ := exists_kernel_lift_fin A' hrank' (v ∘ eι.symm) hv'
  refine ⟨fun i => w' (eι i), ?_, ?_⟩
  · have hAeq : A = A'.submatrix eκ eι := by
      refine Matrix.ext fun i j => ?_
      show A i j = A (eκ.symm (eκ i)) (eι.symm (eι j))
      rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    rw [hAeq, Matrix.submatrix_mulVec_equiv]
    have : (fun i => w' (eι i)) ∘ ⇑eι.symm = w' := by
      funext i
      simp
    rw [this, hw'0]
    rfl
  · funext i
    simpa using congrFun hw'C (eι i)

end PowerSeriesKernelLift

end Height.Toolbox
