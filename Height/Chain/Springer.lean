import Height.Chain.Counts
import Height.Chain.Incidence
import Height.Toolbox.JordanCounts
import Height.Toolbox.Flags
import Height.Toolbox.CentralizerDim
import Height.Geometry.Spec
import Height.Geometry.Dimension.Homogeneous
import Height.Geometry.GroupExamples

/-!
# The Springer bound (`prop:springer-bound`), affine form

The target is `Height.Chain.springer`
(`Chain/StrataDim.lean`): for a rational nilpotent `N`, the triangularizable partners
of `N` inside its own orbit form a set of dimension at most `C(n,2)`.

Statements are in the affine language of `Geometry/Coordinates.lean` (`affineDim`,
`matCoords`), with frames `g ∈ GL_n` in place of flags; the geometric content goes
through the geometry API (`Height/Geometry/{Interface,Spec}.lean`): the frame-chart
fibration is `affineDim_le_image_add_fibre_pts` for `polyMapEquiv (rhoPoly N)` and its
fibre bound is `affineDim_image_eq_of_finite_fibres_pts` for `chartProjPoly`, with the
loci of `𝔸` produced by `exists_isConstructible_pts_eq`.

This file adds to that what the Springer count needs and does not find there: the
dimension of a linear subspace, the dimension of a product, and the frame and Borel
charts, which are the API's own graph construction `Height.Geometry.graphSet` (adjoining
one coordinate `t` with `t det = 1`, so that `g ↦ g⁻¹ N g` — only a *rational* map on the
open locus `det ≠ 0` — becomes a polynomial map).

The Borel acting on the partner incidence is the API's `GLPair.borel` (the Borel subgroup of
the pair model of `GL_n`, `Geometry/GroupExamples.lean`) through the `ActionPresentation`
`borelIncAction`; the count it feeds is
`GroupPresentation.affineDim_image_add_le_of_orbit_le`, the lower half of the orbit
fibration (the fibres of the partner map are unions of orbits, not single orbits).
-/

namespace Height.Chain

open Height.Pencil

open QSteenrod Height.Steenrod Height.Toolbox Height.Geometry

universe u v

/-! ## The Springer number `n(λ)` of a nilpotent matrix -/

section Counts

variable {K : Type u} [Field K]

/-- A nilpotent endomorphism of a finite-dimensional space is killed by its
`finrank`-th power. -/
theorem pow_finrank_eq_zero_of_isNilpotent {W : Type v} [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] {f : Module.End K W} (hf : IsNilpotent f) :
    f ^ Module.finrank K W = 0 := by
  obtain ⟨N, hN⟩ := hf
  have h1 : LinearMap.ker (f ^ max N (Module.finrank K W)) =
      LinearMap.ker (f ^ Module.finrank K W) :=
    Module.End.ker_pow_eq_ker_pow_finrank_of_le (le_max_right _ _)
  have h2 : f ^ max N (Module.finrank K W) = 0 := pow_eq_zero_of_le (le_max_left _ _) hN
  rw [h2, LinearMap.ker_zero] at h1
  exact LinearMap.ker_eq_top.mp h1.symm

variable {n : ℕ}

/-- The `n`-th power of a nilpotent `n × n` matrix vanishes. -/
theorem pow_card_eq_zero_of_isNilpotent {X : Matrix (Fin n) (Fin n) K} (hX : IsNilpotent X) :
    (Matrix.toLinAlgEquiv' X) ^ n = 0 := by
  have hnil : IsNilpotent (Matrix.toLinAlgEquiv' X) := by
    obtain ⟨N, hN⟩ := hX
    exact ⟨N, by rw [← map_pow, hN, map_zero]⟩
  have hrank : Module.finrank K (Fin n → K) = n := Module.finrank_fin_fun K
  simpa [hrank] using pow_finrank_eq_zero_of_isNilpotent (K := K) hnil

/-- `n(λ) = Σ_m C(λ'_m, 2)`, the Springer number of the Jordan type of `X`,
read off the kernel dimensions exactly as `cOf` is. -/
noncomputable def nOf (X : Matrix (Fin n) (Fin n) K) : ℕ :=
  ∑ m ∈ Finset.Icc 1 n, (conj (Matrix.toLinAlgEquiv' X) m).choose 2

/-- Reindexing `Finset.Icc 1 n` as `Fin n`, the shape used by
`Height.Toolbox.jordanColumns`. -/
theorem sum_Icc_one_eq_sum_jordanColumns (y : Module.End K (Fin n → K)) (g : ℕ → ℕ) :
    ∑ m ∈ Finset.Icc 1 n, g (conj y m) = ∑ i : Fin n, g (jordanColumns y n i) := by
  have h1 : ∑ i : Fin n, g (jordanColumns y n i) = ∑ i ∈ Finset.range n, g (conj y (i + 1)) :=
    Fin.sum_univ_eq_sum_range (fun i => g (conj y (i + 1))) n
  rw [h1, ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  simp [Nat.add_comm]

theorem cOf_eq_centralizerCount (X : Matrix (Fin n) (Fin n) K) :
    cOf X = centralizerCount (jordanColumns (Matrix.toLinAlgEquiv' X) n) :=
  sum_Icc_one_eq_sum_jordanColumns _ (fun a => a ^ 2)

theorem nOf_eq_springerCount (X : Matrix (Fin n) (Fin n) K) :
    nOf X = springerCount (jordanColumns (Matrix.toLinAlgEquiv' X) n) :=
  sum_Icc_one_eq_sum_jordanColumns _ (fun a => a.choose 2)

/-- `c(λ) = n + 2 n(λ)` (`lem:springer-dim`). -/
theorem cOf_eq_add_two_mul_nOf {X : Matrix (Fin n) (Fin n) K} (hX : IsNilpotent X) :
    cOf X = n + 2 * nOf X := by
  rw [cOf_eq_centralizerCount, nOf_eq_springerCount]
  have := centralizerCount_jordanColumns (Matrix.toLinAlgEquiv' X) n
    (pow_card_eq_zero_of_isNilpotent hX)
  rwa [Module.finrank_fin_fun] at this

/-- `2 C(n,2) + n = n²`. -/
theorem two_mul_choose_two_add (m : ℕ) : 2 * m.choose 2 + m = m * m := by
  induction m with
  | zero => simp
  | succ m ih =>
      have h : (m + 1).choose 2 = m + m.choose 2 := by
        rw [Nat.choose_succ_succ, Nat.choose_one_right]
      have hsq : (m + 1) * (m + 1) = m * m + 2 * m + 1 := by ring
      rw [h, hsq, ← ih]
      ring

end Counts

/-! ## Affine additions to the dimension toolkit -/

section AffineExtras

variable {K : Type u} [Field K]

/-! ### Linear maps -/

/-- A `K`-linear map of coordinate spaces is a polynomial map. -/
theorem isPolyMap_of_linearMap {ι κ : Type} [Fintype ι] (L : (ι → K) →ₗ[K] (κ → K)) :
    IsPolyMap (L : (ι → K) → (κ → K)) := by
  classical
  refine ⟨fun j => ∑ i, MvPolynomial.C (L (Pi.single i 1) j) * MvPolynomial.X i, fun z j => ?_⟩
  have hz : z = ∑ i, z i • (Pi.single i 1 : ι → K) := by
    funext i
    rw [Finset.sum_apply, Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      simp [hb]
    · intro h
      exact absurd (Finset.mem_univ i) h
  conv_lhs => rw [hz]
  rw [map_sum]
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-! ### Linear subspaces -/

section Submodule

variable {ι : Type} [Fintype ι] (V : Submodule K (ι → K))

/-- A linear subspace is the image of a coordinate space of its own rank under a
polynomial (indeed linear) map. -/
theorem exists_polyMap_image_eq_submodule :
    ∃ f : (Fin (Module.finrank K V) → K) → (ι → K),
      IsPolyMap f ∧ f '' Set.univ = (V : Set (ι → K)) := by
  classical
  have _ : FiniteDimensional K (ι → K) := inferInstance
  set b := Module.finBasis K V with hb
  refine ⟨V.subtype ∘ₗ (b.equivFun.symm : (Fin (Module.finrank K V) → K) →ₗ[K] V),
    isPolyMap_of_linearMap _, ?_⟩
  refine Set.Subset.antisymm ?_ ?_
  · rintro w ⟨c, -, rfl⟩
    exact (b.equivFun.symm c).2
  · intro v hv
    exact ⟨b.equivFun ⟨v, hv⟩, Set.mem_univ _, by simp⟩

/-- Conversely, a linear projection maps a subspace onto a coordinate space of
its rank. -/
theorem exists_polyMap_image_submodule_eq_univ :
    ∃ π : (ι → K) → (Fin (Module.finrank K V) → K),
      IsPolyMap π ∧ π '' (V : Set (ι → K)) = Set.univ := by
  classical
  have _ : FiniteDimensional K (ι → K) := inferInstance
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl V
  set b := Module.finBasis K V with hb
  refine ⟨(b.equivFun : V →ₗ[K] (Fin (Module.finrank K V) → K)) ∘ₗ
    V.projectionOnto W hW, isPolyMap_of_linearMap _, ?_⟩
  refine Set.Subset.antisymm (fun _ _ => Set.mem_univ _) (fun c _ => ?_)
  refine ⟨(b.equivFun.symm c : ι → K), (b.equivFun.symm c).2, ?_⟩
  show b.equivFun (V.projectionOnto W hW ((b.equivFun.symm c : V) : ι → K)) = c
  rw [Submodule.projectionOnto_apply_left hW (b.equivFun.symm c)]
  exact b.equivFun.apply_symm_apply c

/-- **The dimension of a linear subspace is its rank.** -/
theorem affineDim_submodule [IsAlgClosed K] :
    affineDim (V : Set (ι → K)) = ((Module.finrank K V : ℕ∞) : WithBot ℕ∞) := by
  obtain ⟨f, hfpoly, hfimg⟩ := exists_polyMap_image_eq_submodule V
  obtain ⟨π, hπpoly, hπimg⟩ := exists_polyMap_image_submodule_eq_univ V
  have hcard : ((Nat.card (Fin (Module.finrank K V)) : ℕ∞) : WithBot ℕ∞) =
      ((Module.finrank K V : ℕ∞) : WithBot ℕ∞) := by simp
  refine le_antisymm ?_ ?_
  · rw [← hfimg]
    exact le_trans (affineDim_image_le hfpoly _) (le_of_eq (affineDim_univ.trans hcard))
  · rw [← hcard, ← affineDim_univ (ι := Fin (Module.finrank K V)) (K := K), ← hπimg]
    exact affineDim_image_le hπpoly _

/-- A linear subspace is irreducible. -/
theorem isPrime_vanishingIdeal_submodule [Infinite K] :
    (MvPolynomial.vanishingIdeal K (V : Set (ι → K))).IsPrime := by
  obtain ⟨f, hfpoly, hfimg⟩ := exists_polyMap_image_eq_submodule V
  rw [← hfimg]
  exact irreducible_image hfpoly isPrime_vanishingIdeal_univ

end Submodule

/-! ### Products -/

theorem isPolyMap_elim_right {α β : Type} [Fintype α] (x : β → K) :
    IsPolyMap (fun z : α → K => Sum.elim z x) := by
  refine ⟨fun j => Sum.elim (fun i => MvPolynomial.X i) (fun j => MvPolynomial.C (x j)) j,
    fun z j => ?_⟩
  cases j with
  | inl i => simp
  | inr j => simp

theorem isPolyMap_elim_left {α β : Type} [Fintype β] (x : α → K) :
    IsPolyMap (fun z : β → K => Sum.elim x z) := by
  refine ⟨fun j => Sum.elim (fun i => MvPolynomial.C (x i)) (fun j => MvPolynomial.X j) j,
    fun z j => ?_⟩
  cases j with
  | inl i => simp
  | inr j => simp

/-- The dimension of `S × {x}` is the dimension of `S`. -/
theorem affineDim_sumProd_singleton {α β : Type} [Finite α] [Finite β] [IsAlgClosed K]
    (S : Set (α → K)) (x : β → K) :
    affineDim (sumProd S {x}) = affineDim S := by
  classical
  cases nonempty_fintype α
  have himg1 : (fun w : α ⊕ β → K => fun i => w (Sum.inl i)) '' sumProd S {x} = S := by
    refine Set.Subset.antisymm ?_ (fun z hz => ⟨Sum.elim z x, ⟨hz, rfl⟩, rfl⟩)
    rintro z ⟨w, hw, rfl⟩
    exact hw.1
  have himg2 : (fun z : α → K => Sum.elim z x) '' S = sumProd S {x} := by
    refine Set.Subset.antisymm ?_ (fun w hw => ?_)
    · rintro w ⟨z, hz, rfl⟩
      exact ⟨hz, rfl⟩
    · refine ⟨fun i => w (Sum.inl i), hw.1, ?_⟩
      funext j
      cases j with
      | inl i => rfl
      | inr j =>
          have h2 : (fun j => w (Sum.inr j)) = x := hw.2
          exact (congrFun h2 j).symm
  refine le_antisymm ?_ ?_
  · have h := affineDim_image_le (isPolyMap_elim_right (K := K) (α := α) x) S
    rwa [himg2] at h
  · have h := affineDim_image_le (isPolyMap_restrict_inl (K := K) (ι := α) (κ := β)) (sumProd S {x})
    rwa [himg1] at h

/-- The dimension of `{x} × T` is the dimension of `T`. -/
theorem affineDim_singleton_sumProd {α β : Type} [Finite α] [Finite β] [IsAlgClosed K]
    (x : α → K) (T : Set (β → K)) :
    affineDim (sumProd {x} T) = affineDim T := by
  classical
  cases nonempty_fintype β
  have himg1 : (fun w : α ⊕ β → K => fun j => w (Sum.inr j)) '' sumProd {x} T = T := by
    refine Set.Subset.antisymm ?_ (fun z hz => ⟨Sum.elim x z, ⟨rfl, hz⟩, rfl⟩)
    rintro z ⟨w, hw, rfl⟩
    exact hw.2
  have himg2 : (fun z : β → K => Sum.elim x z) '' T = sumProd {x} T := by
    refine Set.Subset.antisymm ?_ (fun w hw => ?_)
    · rintro w ⟨z, hz, rfl⟩
      exact ⟨rfl, hz⟩
    · refine ⟨fun j => w (Sum.inr j), hw.2, ?_⟩
      funext j
      cases j with
      | inl i =>
          have h1 : (fun i => w (Sum.inl i)) = x := hw.1
          exact (congrFun h1 i).symm
      | inr j => rfl
  refine le_antisymm ?_ ?_
  · have h := affineDim_image_le (isPolyMap_elim_left (K := K) (β := β) x) T
    rwa [himg2] at h
  · have h := affineDim_image_le (isPolyMap_restrict_inr (K := K) (ι := α) (κ := β)) (sumProd {x} T)
    rwa [himg1] at h

/-- The Zariski closure of a product lies in the product of the closures. -/
theorem zclosure_sumProd_subset {α β : Type} {S : Set (α → K)} {T : Set (β → K)} :
    zclosure (sumProd S T) ⊆ sumProd (zclosure S) (zclosure T) := by
  intro w hw
  constructor
  · intro p hp
    have hmem : MvPolynomial.rename Sum.inl p ∈
        MvPolynomial.vanishingIdeal K (sumProd S T) := by
      intro w' hw'
      rw [MvPolynomial.aeval_rename]
      exact hp _ hw'.1
    have h := hw _ hmem
    rwa [MvPolynomial.aeval_rename] at h
  · intro p hp
    have hmem : MvPolynomial.rename Sum.inr p ∈
        MvPolynomial.vanishingIdeal K (sumProd S T) := by
      intro w' hw'
      rw [MvPolynomial.aeval_rename]
      exact hp _ hw'.2
    have h := hw _ hmem
    rwa [MvPolynomial.aeval_rename] at h

/-- The projection onto the first factor, as a family of polynomials. -/
noncomputable def projLeftPoly (K : Type u) [Field K] (α β : Type) :
    α → MvPolynomial (α ⊕ β) K :=
  fun i => MvPolynomial.X (Sum.inl i)

theorem aeval_projLeftPoly {α β : Type} :
    (fun (w : α ⊕ β → K) (i : α) => MvPolynomial.aeval w (projLeftPoly K α β i)) =
      fun w i => w (Sum.inl i) := by
  funext w i
  simp [projLeftPoly]

/-- **The product bound.** -/
theorem affineDim_sumProd_le {α β : Type} [Finite α] [Finite β] {K : Type} [Field K]
    [IsAlgClosed K] (S : Set (α → K)) (T : Set (β → K)) :
    affineDim (sumProd S T) ≤ affineDim S + affineDim T := by
  rcases Set.eq_empty_or_nonempty S with rfl | hS
  · have he : sumProd (∅ : Set (α → K)) T = ∅ := by ext w; simp [sumProd]
    rw [he, affineDim_empty]
    exact bot_le
  rcases Set.eq_empty_or_nonempty T with rfl | hT
  · have he : sumProd S (∅ : Set (β → K)) = ∅ := by ext w; simp [sumProd]
    rw [he, affineDim_empty]
    exact bot_le
  set proj : (α ⊕ β → K) → (α → K) := fun w => fun i => w (Sum.inl i) with hproj
  have hfib : ∀ z : α → K,
      affineDim (zclosure (sumProd S T) ∩ proj ⁻¹' {z}) ≤ affineDim T := by
    intro z
    refine le_trans (affineDim_mono (T := sumProd ({z} : Set (α → K)) (zclosure T)) ?_) ?_
    · rintro w ⟨hw1, hw2⟩
      exact ⟨by simpa using hw2, (zclosure_sumProd_subset hw1).2⟩
    · rw [affineDim_singleton_sumProd, affineDim_zclosure]
  obtain ⟨Z, hZ, hZpts⟩ := exists_isConstructible_pts_eq
    (IsLocClosed.of_zclosure (zclosure_zclosure (sumProd S T))).isConstructible
  have hD2 := affineDim_le_image_add_fibre_pts (projLeftPoly K α β) hZ (affineDim T) ?_
  · rw [aeval_projLeftPoly, hZpts, ← hproj, affineDim_zclosure] at hD2
    refine le_trans hD2 (add_le_add ?_ le_rfl)
    calc affineDim (proj '' zclosure (sumProd S T))
        ≤ affineDim (zclosure (proj '' sumProd S T)) :=
          affineDim_mono (image_zclosure_subset isPolyMap_restrict_inl _)
      _ = affineDim (proj '' sumProd S T) := affineDim_zclosure _
      _ ≤ affineDim S := affineDim_mono (by rintro z ⟨w, hw, rfl⟩; exact hw.1)
  · rw [aeval_projLeftPoly, hZpts]
    exact hfib

end AffineExtras

/-! ## Matrices of polynomials -/

section PolyMat

variable {K : Type u} [Field K] {n : ℕ}

/-- The matrix of coordinate variables, indexed through `e`. -/
noncomputable def coordMat {ι : Type} (e : Fin n × Fin n → ι) :
    Matrix (Fin n) (Fin n) (MvPolynomial ι K) :=
  Matrix.of fun i j => MvPolynomial.X (e (i, j))

/-- The matrix of coordinate variables under a substitution, into any commutative
`K`-algebra: the comodule laws of the Borel action substitute polynomials, not `K`-points. -/
theorem map_coordMat_aeval {α : Type} {B : Type v} [CommRing B] [Algebra K B]
    (e : Fin n × Fin n → α) (σ : α → B) :
    (coordMat (K := K) e).map (MvPolynomial.aeval σ) = Matrix.of fun i j => σ (e (i, j)) := by
  ext i j
  simp [coordMat]

/-- `map_coordMat_aeval` at a `K`-point, in `matCoords` form. -/
@[simp] theorem map_genMat {ι : Type} (e : Fin n × Fin n → ι) (w : ι → K) :
    (coordMat (K := K) e).map (MvPolynomial.aeval w) = matCoords.symm (fun ij => w (e ij)) :=
  map_coordMat_aeval e w

/-- A determinant of coordinate variables under a substitution.  This is what the Borel
action's inverse-determinant coordinate needs. -/
theorem aeval_mul_det_coordMat {α : Type} {B : Type v} [CommRing B] [Algebra K B]
    (c : α) (e : Fin n × Fin n → α) (σ : α → B) :
    MvPolynomial.aeval σ (MvPolynomial.X c * (coordMat (K := K) e).det)
      = σ c * (Matrix.of fun i j => σ (e (i, j))).det := by
  rw [map_mul, MvPolynomial.aeval_X, AlgHom.map_det]
  exact congrArg (fun M : Matrix (Fin n) (Fin n) B => σ c * M.det) (map_coordMat_aeval e σ)

@[simp] theorem map_constMat {ι : Type} (A : Matrix (Fin n) (Fin n) K) (w : ι → K) :
    (A.map (MvPolynomial.C : K → MvPolynomial ι K)).map (MvPolynomial.aeval w) = A := by
  ext i j
  simp

theorem map_mul_polyMat {ι : Type} (P Q : Matrix (Fin n) (Fin n) (MvPolynomial ι K))
    (w : ι → K) :
    (P * Q).map (MvPolynomial.aeval w) =
      P.map (MvPolynomial.aeval w) * Q.map (MvPolynomial.aeval w) :=
  Matrix.map_mul (f := (MvPolynomial.aeval w : MvPolynomial ι K →ₐ[K] K).toRingHom)

theorem map_adjugate_polyMat {ι : Type} (P : Matrix (Fin n) (Fin n) (MvPolynomial ι K))
    (w : ι → K) :
    P.adjugate.map (MvPolynomial.aeval w) = (P.map (MvPolynomial.aeval w)).adjugate :=
  AlgHom.map_adjugate (MvPolynomial.aeval w : MvPolynomial ι K →ₐ[K] K) P

theorem map_smul_polyMat {ι : Type} (c : MvPolynomial ι K)
    (P : Matrix (Fin n) (Fin n) (MvPolynomial ι K)) (w : ι → K) :
    (c • P).map (MvPolynomial.aeval w) =
      (MvPolynomial.aeval w c) • P.map (MvPolynomial.aeval w) := by
  ext i j
  show MvPolynomial.aeval w (c * P i j) = _
  rw [map_mul]
  rfl

end PolyMat

/-! ## The Springer count -/

section Springer

variable {K : Type u} [Field K] {n : ℕ}

/-- `𝔫 ∩ O_N`, in matrix coordinates. -/
def nilOrbit (N : Matrix (Fin n) (Fin n) K) : Set (Fin n × Fin n → K) :=
  matCoords '' ((standardNilradical K n : Set (Matrix (Fin n) (Fin n) K)) ∩ conjOrbit N)

/-- The space of intertwiners `N g = g X`. -/
def interMat (N X : Matrix (Fin n) (Fin n) K) : Submodule K (Matrix (Fin n) (Fin n) K) where
  carrier := {g | N * g = g * X}
  add_mem' {a c} ha hc := by
    show N * (a + c) = (a + c) * X
    rw [mul_add, add_mul, show N * a = a * X from ha, show N * c = c * X from hc]
  zero_mem' := by show N * 0 = 0 * X; simp
  smul_mem' r a ha := by
    show N * (r • a) = (r • a) * X
    rw [Matrix.mul_smul, Matrix.smul_mul, show N * a = a * X from ha]

/-- Right multiplication by an invertible matrix, as a linear automorphism of
matrix space. -/
def rightMulEquiv (k : (Matrix (Fin n) (Fin n) K)ˣ) :
    Matrix (Fin n) (Fin n) K ≃ₗ[K] Matrix (Fin n) (Fin n) K where
  toFun A := A * (k : Matrix (Fin n) (Fin n) K)
  invFun A := A * ((↑k⁻¹ : Matrix (Fin n) (Fin n) K))
  left_inv A := by
    show A * (k : Matrix (Fin n) (Fin n) K) * ((↑k⁻¹ : Matrix (Fin n) (Fin n) K)) = A
    rw [Matrix.mul_assoc]
    simp
  right_inv A := by
    show A * ((↑k⁻¹ : Matrix (Fin n) (Fin n) K)) * (k : Matrix (Fin n) (Fin n) K) = A
    rw [Matrix.mul_assoc]
    simp
  map_add' A B := add_mul _ _ _
  map_smul' r A := Matrix.smul_mul _ _ _

/-- The intertwiners are a right translate of the centraliser. -/
theorem map_centralizer_eq_interMat {N X : Matrix (Fin n) (Fin n) K}
    (k : (Matrix (Fin n) (Fin n) K)ˣ)
    (hX : X = (k : Matrix (Fin n) (Fin n) K) * N * ((↑k⁻¹ : Matrix (Fin n) (Fin n) K))) :
    (Height.Toolbox.centralizer N).map (rightMulEquiv k⁻¹).toLinearMap = interMat N X := by
  have hXk : X * (k : Matrix (Fin n) (Fin n) K) = (k : Matrix (Fin n) (Fin n) K) * N := by
    rw [hX, Matrix.mul_assoc]
    simp
  have hXinv : ((↑k⁻¹ : Matrix (Fin n) (Fin n) K)) * X =
      N * ((↑k⁻¹ : Matrix (Fin n) (Fin n) K)) := by
    rw [hX, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
    simp
  ext g
  constructor
  · rintro ⟨c, hc, rfl⟩
    have hc' : c * N = N * c := hc
    show N * (c * ((↑k⁻¹ : Matrix (Fin n) (Fin n) K))) =
      c * ((↑k⁻¹ : Matrix (Fin n) (Fin n) K)) * X
    calc N * (c * ((↑k⁻¹ : Matrix (Fin n) (Fin n) K)))
        = (N * c) * ((↑k⁻¹ : Matrix (Fin n) (Fin n) K)) := (Matrix.mul_assoc _ _ _).symm
      _ = (c * N) * ((↑k⁻¹ : Matrix (Fin n) (Fin n) K)) := by rw [hc']
      _ = c * (N * ((↑k⁻¹ : Matrix (Fin n) (Fin n) K))) := Matrix.mul_assoc _ _ _
      _ = c * (((↑k⁻¹ : Matrix (Fin n) (Fin n) K)) * X) := by rw [hXinv]
      _ = c * ((↑k⁻¹ : Matrix (Fin n) (Fin n) K)) * X := (Matrix.mul_assoc _ _ _).symm
  · intro hg
    have hg' : N * g = g * X := hg
    refine ⟨g * (k : Matrix (Fin n) (Fin n) K), ?_, ?_⟩
    · show g * (k : Matrix (Fin n) (Fin n) K) * N = N * (g * (k : Matrix (Fin n) (Fin n) K))
      calc g * (k : Matrix (Fin n) (Fin n) K) * N
          = g * ((k : Matrix (Fin n) (Fin n) K) * N) := Matrix.mul_assoc _ _ _
        _ = g * (X * (k : Matrix (Fin n) (Fin n) K)) := by rw [hXk]
        _ = (g * X) * (k : Matrix (Fin n) (Fin n) K) := (Matrix.mul_assoc _ _ _).symm
        _ = (N * g) * (k : Matrix (Fin n) (Fin n) K) := by rw [hg']
        _ = N * (g * (k : Matrix (Fin n) (Fin n) K)) := Matrix.mul_assoc _ _ _
    · show g * (k : Matrix (Fin n) (Fin n) K) * ((↑k⁻¹ : Matrix (Fin n) (Fin n) K)) = g
      rw [Matrix.mul_assoc]
      simp

theorem finrank_interMat {N X : Matrix (Fin n) (Fin n) K} (hN : IsNilpotent N)
    (hX : X ∈ conjOrbit N) : Module.finrank K (interMat N X) = cOf N := by
  obtain ⟨k, hk⟩ := hX
  rw [← map_centralizer_eq_interMat k hk, LinearEquiv.finrank_map_eq,
    Height.Toolbox.finrank_centralizer_eq N hN]

/-- The intertwiner space in coordinates. -/
def interSpace (N X : Matrix (Fin n) (Fin n) K) : Submodule K (Fin n × Fin n → K) :=
  (interMat N X).map (matCoords (K := K) (μ := Fin n)).toLinearMap

theorem mem_interSpace {N X : Matrix (Fin n) (Fin n) K} {x : Fin n × Fin n → K} :
    x ∈ interSpace N X ↔ N * matCoords.symm x = matCoords.symm x * X := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact hg
  · intro hx
    exact ⟨matCoords.symm x, hx, rfl⟩

theorem finrank_interSpace {N X : Matrix (Fin n) (Fin n) K} (hN : IsNilpotent N)
    (hX : X ∈ conjOrbit N) : Module.finrank K (interSpace N X) = cOf N := by
  rw [interSpace, LinearEquiv.finrank_map_eq, finrank_interMat hN hX]

/-! ### The frame chart -/

/-- The matrix part of a point of a matrix chart. -/
def chartMat (w : (Fin n × Fin n) ⊕ Unit → K) : Matrix (Fin n) (Fin n) K :=
  matCoords.symm (fun ij => w (Sum.inl ij))

/-- The inverse-determinant coordinate of a point of a matrix chart. -/
def chartInv (w : (Fin n × Fin n) ⊕ Unit → K) : K := w (Sum.inr ())

theorem matCoords_chartMat (w : (Fin n × Fin n) ⊕ Unit → K) :
    matCoords (chartMat w) = fun ij => w (Sum.inl ij) :=
  matCoords.apply_symm_apply _

/-- The matrix block of a matrix chart, as a family of polynomials: the shape the
geometry API's `polyMapEquiv` takes. -/
noncomputable def chartProjPoly (K : Type u) [Field K] (n : ℕ) :
    Fin n × Fin n → MvPolynomial ((Fin n × Fin n) ⊕ Unit) K :=
  fun ij => MvPolynomial.X (Sum.inl ij)

theorem aeval_chartProjPoly :
    (fun (w : (Fin n × Fin n) ⊕ Unit → K) (ij : Fin n × Fin n) =>
      MvPolynomial.aeval w (chartProjPoly K n ij)) = fun w => matCoords (chartMat w) := by
  funext w ij
  show MvPolynomial.aeval w (MvPolynomial.X (Sum.inl ij)) = matCoords (chartMat w) ij
  rw [MvPolynomial.aeval_X, matCoords_chartMat]

/-- Frames adapted to `N`: matrices `g` with `adj(g) N g` strictly upper
triangular.  Where `g` is invertible this says `g⁻¹ N g ∈ 𝔫`. -/
def frameBase (N : Matrix (Fin n) (Fin n) K) : Set (Fin n × Fin n → K) :=
  {x | Matrix.adjugate (matCoords.symm x) * N * matCoords.symm x ∈ standardNilradical K n}

/-- The frame chart of `N`: pairs `(g, t)` with `t det g = 1` and `g` adapted. -/
def frameChart (N : Matrix (Fin n) (Fin n) K) : Set ((Fin n × Fin n) ⊕ Unit → K) :=
  graphSet (frameBase N) (detPoly (K := K) (Fin n))

theorem aeval_detPoly_chart (w : (Fin n × Fin n) ⊕ Unit → K) :
    MvPolynomial.aeval (projSum w) (detPoly (K := K) (Fin n)) = (chartMat w).det :=
  aeval_detPoly _

theorem mem_frameChart_iff {N : Matrix (Fin n) (Fin n) K}
    {w : (Fin n × Fin n) ⊕ Unit → K} :
    w ∈ frameChart N ↔
      (Matrix.adjugate (chartMat w) * N * chartMat w ∈ standardNilradical K n) ∧
        chartInv w * (chartMat w).det = 1 := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by rwa [aeval_detPoly_chart] at h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by rwa [aeval_detPoly_chart]⟩

theorem det_chartMat_ne_zero {N : Matrix (Fin n) (Fin n) K}
    {w : (Fin n × Fin n) ⊕ Unit → K} (hw : w ∈ frameChart N) :
    (chartMat w).det ≠ 0 := by
  intro h0
  have h := (mem_frameChart_iff.mp hw).2
  rw [h0, mul_zero] at h
  exact zero_ne_one h

theorem isUnit_det_chartMat {N : Matrix (Fin n) (Fin n) K}
    {w : (Fin n × Fin n) ⊕ Unit → K} (hw : w ∈ frameChart N) :
    IsUnit (chartMat w).det :=
  isUnit_iff_ne_zero.mpr (det_chartMat_ne_zero hw)

theorem chartInv_eq_inv_det {N : Matrix (Fin n) (Fin n) K}
    {w : (Fin n × Fin n) ⊕ Unit → K} (hw : w ∈ frameChart N) :
    chartInv w = ((chartMat w).det)⁻¹ := by
  have hmul := (mem_frameChart_iff.mp hw).2
  have hdet := det_chartMat_ne_zero hw
  calc chartInv w = chartInv w * ((chartMat w).det * ((chartMat w).det)⁻¹) := by
        rw [mul_inv_cancel₀ hdet, mul_one]
    _ = (chartInv w * (chartMat w).det) * ((chartMat w).det)⁻¹ := by ring
    _ = ((chartMat w).det)⁻¹ := by rw [hmul, one_mul]

theorem inv_chartMat {N : Matrix (Fin n) (Fin n) K}
    {w : (Fin n × Fin n) ⊕ Unit → K} (hw : w ∈ frameChart N) :
    (chartMat w)⁻¹ = chartInv w • Matrix.adjugate (chartMat w) := by
  rw [Matrix.inv_def, chartInv_eq_inv_det hw, Ring.inverse_eq_inv]

/-- The frames adapted to `N` are Zariski closed. -/
theorem zclosure_frameBase (N : Matrix (Fin n) (Fin n) K) :
    zclosure (frameBase N) = frameBase N := by
  set P : Matrix (Fin n) (Fin n) (MvPolynomial (Fin n × Fin n) K) :=
    (coordMat (K := K) (n := n) id).adjugate *
      (N.map (MvPolynomial.C : K → MvPolynomial (Fin n × Fin n) K)) *
      (coordMat (K := K) (n := n) id) with hP
  have hPeval : ∀ (z : Fin n × Fin n → K) (i j : Fin n),
      MvPolynomial.aeval z (P i j) =
        (Matrix.adjugate (matCoords.symm z) * N * matCoords.symm z) i j := by
    intro z i j
    have : P.map (MvPolynomial.aeval z) =
        Matrix.adjugate (matCoords.symm z) * N * matCoords.symm z := by
      rw [hP, map_mul_polyMat, map_mul_polyMat, map_adjugate_polyMat, map_genMat, map_constMat]
      rfl
    calc MvPolynomial.aeval z (P i j) = (P.map (MvPolynomial.aeval z)) i j := rfl
      _ = _ := by rw [this]
  refine zclosure_eq_self_of_eqZeroLocus
    (T := {p | ∃ i j : Fin n, j ≤ i ∧ p = P i j}) (fun z => ?_)
  constructor
  · rintro hz p ⟨i, j, hij, rfl⟩
    rw [hPeval]
    exact hz i j hij
  · intro hz i j hij
    rw [← hPeval z i j]
    exact hz _ ⟨i, j, hij, rfl⟩

theorem zclosure_frameChart (N : Matrix (Fin n) (Fin n) K) :
    zclosure (frameChart N) = frameChart N :=
  zclosure_graphSet (zclosure_frameBase N) _

/-- `ρ (g, t) = g⁻¹ N g`, as a polynomial map. -/
noncomputable def rhoMap (N : Matrix (Fin n) (Fin n) K) :
    ((Fin n × Fin n) ⊕ Unit → K) → (Fin n × Fin n → K) :=
  fun w => matCoords (chartInv w • (Matrix.adjugate (chartMat w) * N * chartMat w))

/-- The polynomial matrix of `ρ`: `t · adj(g) N g` over the chart coordinates. -/
noncomputable def rhoPolyMat (N : Matrix (Fin n) (Fin n) K) :
    Matrix (Fin n) (Fin n) (MvPolynomial ((Fin n × Fin n) ⊕ Unit) K) :=
  (MvPolynomial.X (Sum.inr ()) : MvPolynomial ((Fin n × Fin n) ⊕ Unit) K) •
    ((coordMat (K := K) (n := n) Sum.inl).adjugate *
      (N.map (MvPolynomial.C : K → MvPolynomial ((Fin n × Fin n) ⊕ Unit) K)) *
      (coordMat (K := K) (n := n) Sum.inl))

/-- `ρ` as a family of polynomials: the shape the geometry API's `polyMapEquiv` takes. -/
noncomputable def rhoPoly (N : Matrix (Fin n) (Fin n) K) :
    Fin n × Fin n → MvPolynomial ((Fin n × Fin n) ⊕ Unit) K :=
  fun ij => rhoPolyMat N ij.1 ij.2

theorem aeval_rhoPoly (N : Matrix (Fin n) (Fin n) K) :
    (fun (w : (Fin n × Fin n) ⊕ Unit → K) (ij : Fin n × Fin n) =>
      MvPolynomial.aeval w (rhoPoly N ij)) = rhoMap N := by
  funext w ij
  have hmap : (rhoPolyMat N).map (MvPolynomial.aeval w) =
      chartInv w • (Matrix.adjugate (chartMat w) * N * chartMat w) := by
    rw [rhoPolyMat, map_smul_polyMat, map_mul_polyMat, map_mul_polyMat, map_adjugate_polyMat,
      map_genMat, map_constMat, MvPolynomial.aeval_X]
    rfl
  calc MvPolynomial.aeval w (rhoPoly N ij)
      = ((rhoPolyMat N).map (MvPolynomial.aeval w)) ij.1 ij.2 := rfl
    _ = (chartInv w • (Matrix.adjugate (chartMat w) * N * chartMat w)) ij.1 ij.2 := by rw [hmap]
    _ = rhoMap N w ij := rfl

theorem isPolyMap_rhoMap (N : Matrix (Fin n) (Fin n) K) : IsPolyMap (rhoMap N) :=
  ⟨rhoPoly N, fun w ij => (congrFun (congrFun (aeval_rhoPoly N) w) ij).symm⟩

theorem rhoMap_eq_conj {N : Matrix (Fin n) (Fin n) K}
    {w : (Fin n × Fin n) ⊕ Unit → K} (hw : w ∈ frameChart N) :
    matCoords.symm (rhoMap N w) = (chartMat w)⁻¹ * N * chartMat w := by
  rw [rhoMap, matCoords.symm_apply_apply, inv_chartMat hw, Matrix.smul_mul, Matrix.smul_mul]

theorem rhoMap_mem_nilOrbit {N : Matrix (Fin n) (Fin n) K}
    {w : (Fin n × Fin n) ⊕ Unit → K} (hw : w ∈ frameChart N) :
    rhoMap N w ∈ nilOrbit N := by
  have hunit : IsUnit (chartMat w) :=
    (Matrix.isUnit_iff_isUnit_det (chartMat w)).mpr (isUnit_det_chartMat hw)
  refine ⟨matCoords.symm (rhoMap N w), ⟨?_, ?_⟩, matCoords.apply_symm_apply _⟩
  · rw [rhoMap, matCoords.symm_apply_apply]
    exact Submodule.smul_mem _ _ (mem_frameChart_iff.mp hw).1
  · refine ⟨(Matrix.nonsingInvUnit (chartMat w) (isUnit_det_chartMat hw))⁻¹, ?_⟩
    rw [rhoMap_eq_conj hw]
    rfl

theorem rhoMap_image_subset (N : Matrix (Fin n) (Fin n) K) :
    rhoMap N '' frameChart N ⊆ nilOrbit N := by
  rintro _ ⟨w, hw, rfl⟩
  exact rhoMap_mem_nilOrbit hw

/-- The frame of a point of the fibre of `ρ` over `x` intertwines `N` and `x`: it lies in
the intertwiner space `{g : N g = g x}`. -/
theorem chartMat_mem_interSpace {N : Matrix (Fin n) (Fin n) K} {x : Fin n × Fin n → K}
    {w : (Fin n × Fin n) ⊕ Unit → K} (hw : w ∈ frameChart N ∩ rhoMap N ⁻¹' {x}) :
    matCoords (chartMat w) ∈ interSpace N (matCoords.symm x) := by
  obtain ⟨hwc, hwx⟩ := hw
  have hxw : matCoords.symm x = (chartMat w)⁻¹ * N * chartMat w := by
    rw [← rhoMap_eq_conj hwc]
    congr 1
    exact (Set.mem_singleton_iff.mp hwx).symm
  rw [mem_interSpace, matCoords.symm_apply_apply]
  have hgX : chartMat w * matCoords.symm x = N * chartMat w := by
    rw [hxw, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ (isUnit_det_chartMat hwc), Matrix.one_mul]
  exact hgX.symm

/-- The fibre of `ρ` over `x` is a Zariski closed set of the chart. -/
theorem zclosure_frameChart_fibre (N : Matrix (Fin n) (Fin n) K) (x : Fin n × Fin n → K) :
    zclosure (frameChart N ∩ rhoMap N ⁻¹' {x}) = frameChart N ∩ rhoMap N ⁻¹' {x} :=
  zclosure_inter (zclosure_frameChart N)
    (zclosure_preimage (isPolyMap_rhoMap N) (zclosure_singleton x))

-- The geometry API ties the index universe of `𝔸(ι)` to that of `K`, so the three
-- theorems below live at `K : Type` (the chain runs at `Kbar p r : Type`).

/-- **The fibre bound**: every fibre of `ρ` has dimension at most `c(λ)`.  The frame block
of the chart is injective on a fibre (the last coordinate is `1/det`), so the API's
finite-fibre count (`Height.Geometry.affineDim_image_eq_of_finite_fibres_pts`) carries the
fibre isomorphically into the intertwiner space, whose dimension is `c(λ)`. -/
theorem affineDim_frameChart_fibre_le {K : Type} [Field K] [IsAlgClosed K] {n : ℕ}
    {N : Matrix (Fin n) (Fin n) K}
    (hN : IsNilpotent N) (x : Fin n × Fin n → K) :
    affineDim (frameChart N ∩ rhoMap N ⁻¹' {x}) ≤ ((cOf N : ℕ∞) : WithBot ℕ∞) := by
  rcases Set.eq_empty_or_nonempty (frameChart N ∩ rhoMap N ⁻¹' {x}) with hemp | ⟨w₀, hw₀⟩
  · rw [hemp, affineDim_empty]
    exact bot_le
  have hx0 : rhoMap N w₀ = x := hw₀.2
  have hxmem : x ∈ nilOrbit N := hx0 ▸ rhoMap_mem_nilOrbit hw₀.1
  obtain ⟨M, hM, hMx⟩ := hxmem
  have hMX : M = matCoords.symm x := by rw [← hMx, matCoords.symm_apply_apply]
  have hXorb : matCoords.symm x ∈ conjOrbit N := hMX ▸ hM.2
  obtain ⟨Z, hZ, hZpts⟩ := exists_isConstructible_pts_eq
    (IsLocClosed.of_zclosure (zclosure_frameChart_fibre N x)).isConstructible
  have heq := affineDim_image_eq_of_finite_fibres_pts (chartProjPoly K n) hZ ?_
  · rw [aeval_chartProjPoly, hZpts] at heq
    rw [← heq]
    calc affineDim ((fun w => matCoords (chartMat w)) '' (frameChart N ∩ rhoMap N ⁻¹' {x}))
        ≤ affineDim ((interSpace N (matCoords.symm x) : Submodule K (Fin n × Fin n → K)) :
            Set (Fin n × Fin n → K)) :=
          affineDim_mono (by rintro _ ⟨w, hw, rfl⟩; exact chartMat_mem_interSpace hw)
      _ = ((Module.finrank K (interSpace N (matCoords.symm x)) : ℕ∞) : WithBot ℕ∞) :=
          affineDim_submodule _
      _ = ((cOf N : ℕ∞) : WithBot ℕ∞) := by rw [finrank_interSpace hN hXorb]
  -- the frame block determines the point of the chart: the last coordinate is `1/det`
  · intro y
    refine Set.Finite.subset (Set.finite_singleton
      (Sum.elim y (fun _ : Unit => ((matCoords.symm y).det)⁻¹))) ?_
    rintro w ⟨hwZ, hwy⟩
    have hw : w ∈ frameChart N ∩ rhoMap N ⁻¹' {x} := (Set.ext_iff.1 hZpts w).1 hwZ
    have hmat : matCoords (chartMat w) = y :=
      (congrFun (aeval_chartProjPoly (K := K) (n := n)) w).symm.trans hwy
    have hcm : chartMat w = matCoords.symm y := by rw [← hmat, matCoords.symm_apply_apply]
    refine Set.mem_singleton_iff.mpr (funext fun j => ?_)
    cases j with
    | inl ij =>
        show w (Sum.inl ij) = y ij
        exact congrFun ((matCoords_chartMat w).symm.trans hmat) ij
    | inr u =>
        have hu : u = () := rfl
        subst hu
        show chartInv w = ((matCoords.symm y).det)⁻¹
        rw [chartInv_eq_inv_det hw.1, hcm]

/-- **The frame-chart fibration**: the adapted frames of `N` have dimension
at most `dim (𝔫 ∩ O_N) + c(λ)`.  This is the fibre-dimension inequality on `K`-points
(`Height.Geometry.affineDim_le_image_add_fibre_pts`) for `ρ = polyMapEquiv (rhoPoly N)`,
with the locus of `𝔸` produced by `exists_isConstructible_pts_eq`. -/
theorem affineDim_frameChart_le {K : Type} [Field K] [IsAlgClosed K] {n : ℕ}
    {N : Matrix (Fin n) (Fin n) K}
    (hN : IsNilpotent N) :
    affineDim (frameChart N) ≤ affineDim (nilOrbit N) + ((cOf N : ℕ∞) : WithBot ℕ∞) := by
  obtain ⟨Z, hZ, hZpts⟩ := exists_isConstructible_pts_eq
    (IsLocClosed.of_zclosure (zclosure_frameChart N)).isConstructible
  have hmain := affineDim_le_image_add_fibre_pts (rhoPoly N) hZ
    ((cOf N : ℕ∞) : WithBot ℕ∞) ?_
  · rw [aeval_rhoPoly, hZpts] at hmain
    exact le_trans hmain (add_le_add (affineDim_mono (rhoMap_image_subset N)) le_rfl)
  · intro w
    rw [aeval_rhoPoly, hZpts]
    exact affineDim_frameChart_fibre_le hN w

/-! ### The Borel chart -/

/-- The inverse of an invertible upper triangular matrix is upper triangular:
`b` maps each member of the standard flag into itself, injectively, hence onto
itself. -/
theorem inv_mem_standardBorel {b : Matrix (Fin n) (Fin n) K}
    (hb : b ∈ standardBorel K n) (hu : IsUnit b.det) :
    b⁻¹ ∈ standardBorel K n := by
  rw [mem_standardBorel_iff_preservesStandardFlag]
  intro k v hv
  have hpres := (mem_standardBorel_iff_preservesStandardFlag K n b).mp hb
  -- `b` restricts to an endomorphism of the `k`th flag member
  have hmaps : ∀ u ∈ standardFlag K n k, b.mulVecLin u ∈ standardFlag K n k := fun u hu' =>
    hpres k u hu'
  set L : standardFlag K n k →ₗ[K] standardFlag K n k :=
    b.mulVecLin.restrict hmaps with hL
  have hLinj : Function.Injective L := by
    intro u u' huu
    have h1 : b.mulVec (u : Fin n → K) = b.mulVec (u' : Fin n → K) :=
      congrArg Subtype.val huu
    have h2 : (u : Fin n → K) = (u' : Fin n → K) := by
      have h3 := congrArg (fun z => b⁻¹.mulVec z) h1
      simp only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec] at h3
      exact h3
    exact Subtype.ext h2
  have hLsurj : Function.Surjective L := LinearMap.injective_iff_surjective.mp hLinj
  obtain ⟨u, hu'⟩ := hLsurj ⟨v, hv⟩
  have hbu : b.mulVec (u : Fin n → K) = v := congrArg Subtype.val hu'
  have hinvv : b⁻¹.mulVec v = (u : Fin n → K) := by
    rw [← hbu, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
  rw [hinvv]
  exact u.2

/-- The upper triangular matrices, in coordinates. -/
def borelSpace (K : Type u) [Field K] (n : ℕ) : Submodule K (Fin n × Fin n → K) :=
  ((standardBorel K n).toSubmodule).map (matCoords (K := K) (μ := Fin n)).toLinearMap

theorem mem_borelSpace {x : Fin n × Fin n → K} :
    x ∈ borelSpace K n ↔ matCoords.symm x ∈ standardBorel K n := by
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact hb
  · intro hx
    exact ⟨matCoords.symm x, hx, rfl⟩

theorem finrank_borelSpace : Module.finrank K (borelSpace K n) = n.choose 2 + n := by
  rw [borelSpace, LinearEquiv.finrank_map_eq]
  exact finrank_standardBorel K n

/-- The Borel chart: invertible upper triangular matrices with their inverse
determinant. -/
def borelChart (K : Type u) [Field K] (n : ℕ) : Set ((Fin n × Fin n) ⊕ Unit → K) :=
  graphSet ((borelSpace K n : Submodule K (Fin n × Fin n → K)) : Set (Fin n × Fin n → K))
    (detPoly (K := K) (Fin n))

theorem mem_borelChart_iff {c : (Fin n × Fin n) ⊕ Unit → K} :
    c ∈ borelChart K n ↔
      chartMat c ∈ standardBorel K n ∧ chartInv c * (chartMat c).det = 1 := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨mem_borelSpace.mp h1, ?_⟩
    rwa [aeval_detPoly_chart] at h2
  · rintro ⟨h1, h2⟩
    exact ⟨mem_borelSpace.mpr h1, by rwa [aeval_detPoly_chart]⟩

theorem det_chartMat_ne_zero_of_borel {c : (Fin n × Fin n) ⊕ Unit → K}
    (hc : c ∈ borelChart K n) : (chartMat c).det ≠ 0 := by
  intro h0
  have h := (mem_borelChart_iff.mp hc).2
  rw [h0, mul_zero] at h
  exact zero_ne_one h

theorem isUnit_det_chartMat_of_borel {c : (Fin n × Fin n) ⊕ Unit → K}
    (hc : c ∈ borelChart K n) : IsUnit (chartMat c).det :=
  isUnit_iff_ne_zero.mpr (det_chartMat_ne_zero_of_borel hc)

theorem chartInv_eq_of_borel {c : (Fin n × Fin n) ⊕ Unit → K} (hc : c ∈ borelChart K n) :
    chartInv c = ((chartMat c).det)⁻¹ := by
  have hmul := (mem_borelChart_iff.mp hc).2
  have hdet := det_chartMat_ne_zero_of_borel hc
  calc chartInv c = chartInv c * ((chartMat c).det * ((chartMat c).det)⁻¹) := by
        rw [mul_inv_cancel₀ hdet, mul_one]
    _ = (chartInv c * (chartMat c).det) * ((chartMat c).det)⁻¹ := by ring
    _ = ((chartMat c).det)⁻¹ := by rw [hmul, one_mul]

/-- The adjugate of an invertible upper triangular matrix is upper
triangular. -/
theorem adjugate_mem_standardBorel {b : Matrix (Fin n) (Fin n) K}
    (hb : b ∈ standardBorel K n) (hu : IsUnit b.det) :
    Matrix.adjugate b ∈ standardBorel K n := by
  have hdet : b.det ≠ 0 := isUnit_iff_ne_zero.mp hu
  have hadj : Matrix.adjugate b = b.det • b⁻¹ := by
    rw [Matrix.inv_def, Ring.inverse_eq_inv, smul_smul, mul_inv_cancel₀ hdet, one_smul]
  rw [hadj]
  exact Subalgebra.smul_mem _ (inv_mem_standardBorel hb hu) _

theorem detPoly_notMem_vanishingIdeal_borelSpace [Infinite K] :
    detPoly (K := K) (Fin n) ∉ MvPolynomial.vanishingIdeal K
      ((borelSpace K n : Submodule K (Fin n × Fin n → K)) : Set (Fin n × Fin n → K)) := by
  intro hmem
  have h1 : matCoords (1 : Matrix (Fin n) (Fin n) K) ∈
      ((borelSpace K n : Submodule K (Fin n × Fin n → K)) : Set (Fin n × Fin n → K)) :=
    mem_borelSpace.mpr (by simp [matCoords.symm_apply_apply])
  have := hmem _ h1
  rw [aeval_detPoly, matCoords.symm_apply_apply, Matrix.det_one] at this
  exact one_ne_zero this

theorem isPrime_vanishingIdeal_borelChart [Infinite K] :
    (MvPolynomial.vanishingIdeal K (borelChart K n)).IsPrime :=
  isPrime_vanishingIdeal_graphSet (isPrime_vanishingIdeal_submodule _)
    detPoly_notMem_vanishingIdeal_borelSpace

/-! ### The partner incidence and the Borel action -/

/-- The frame block of a point of the partner incidence. -/
def incFrame (v : ((Fin n × Fin n) ⊕ Unit) ⊕ (Fin n × Fin n) → K) :
    (Fin n × Fin n) ⊕ Unit → K := fun i => v (Sum.inl i)

/-- The partner block of a point of the partner incidence. -/
def incMat (v : ((Fin n × Fin n) ⊕ Unit) ⊕ (Fin n × Fin n) → K) :
    Matrix (Fin n) (Fin n) K := matCoords.symm (fun ij => v (Sum.inr ij))

/-- `Y_N`: frames adapted to `N` together with a partner `M` in the orbit of `N`
which the same frame triangularises. -/
def partnerIncidence (N : Matrix (Fin n) (Fin n) K) :
    Set (((Fin n × Fin n) ⊕ Unit) ⊕ (Fin n × Fin n) → K) :=
  {v | incFrame v ∈ frameChart N ∧ incMat v ∈ conjOrbit N ∧
    Matrix.adjugate (chartMat (incFrame v)) * incMat v * chartMat (incFrame v) ∈
      standardNilradical K n}

/-- A point of the incidence space is determined by its three blocks. -/
theorem inc_ext {v v' : ((Fin n × Fin n) ⊕ Unit) ⊕ (Fin n × Fin n) → K}
    (h1 : incFrame v = incFrame v') (h2 : incMat v = incMat v') : v = v' := by
  funext i
  cases i with
  | inl j => exact congrFun h1 j
  | inr ij =>
      have := congrArg (fun A : Matrix (Fin n) (Fin n) K => A ij.1 ij.2) h2
      simpa [incMat] using this

/-! ### Stability, the partner map, and its image -/

/-- Conjugating a strictly upper triangular matrix by an element of the Borel
chart, in the `adjugate` form used by the incidence. -/
theorem adjugate_sandwich_mem {b Q : Matrix (Fin n) (Fin n) K} {g : Matrix (Fin n) (Fin n) K}
    (hb : b ∈ standardBorel K n) (hbu : IsUnit b.det)
    (hQ : Matrix.adjugate g * Q * g ∈ standardNilradical K n) :
    Matrix.adjugate (g * b) * Q * (g * b) ∈ standardNilradical K n := by
  have hrw : Matrix.adjugate (g * b) * Q * (g * b) =
      Matrix.adjugate b * (Matrix.adjugate g * Q * g) * b := by
    rw [Matrix.adjugate_mul_distrib]
    simp only [Matrix.mul_assoc]
  rw [hrw]
  exact standardBorel_mul_nilradical_mul_standardBorel K n
    (adjugate_mem_standardBorel hb hbu) hQ hb

/-- The partner map: read off the partner `M`. -/
def partnerMap : (((Fin n × Fin n) ⊕ Unit) ⊕ (Fin n × Fin n) → K) → (Fin n × Fin n → K) :=
  fun v => fun ij => v (Sum.inr ij)

theorem isPolyMap_partnerMap : IsPolyMap (partnerMap (K := K) (n := n)) :=
  isPolyMap_restrict_inr

/-! ### The Borel acting on the incidence space

The group is `GLPair.borel`, the Borel subgroup of the pair model of `GL_n`
(`Geometry/GroupExamples.lean`): pairs `(g, h)` of mutually inverse upper triangular
matrices.  It acts on the incidence space by right translation of the frame,

    a ⋆ (G, t, M) = (G h_a, t det g_a, M),

which is polynomial because the pair model carries the inverse as a coordinate: the frame
chart's `t = 1 / det G` is multiplied by `det g_a = 1 / det h_a`.  Since `h_a = g_a⁻¹`, this
is a *left* action, the convention of `ActionPresentation`. -/

section BorelIncidence

variable {K : Type} [Field K] {n : ℕ}

variable (K n) in
/-- The frame block of the translated point, as a polynomial matrix: `G h`. -/
noncomputable def borelIncFrameMat :
    Matrix (Fin n) (Fin n)
      (MvPolynomial (GLIdx n ⊕ (((Fin n × Fin n) ⊕ Unit) ⊕ (Fin n × Fin n))) K) :=
  coordMat (fun ab => Sum.inr (Sum.inl (Sum.inl ab))) * coordMat (fun ab => Sum.inl (Sum.inr ab))

variable (K n) in
/-- The action of the Borel on the incidence space, as polynomials in the group and space
coordinates. -/
noncomputable def borelIncPoly :
    ((Fin n × Fin n) ⊕ Unit) ⊕ (Fin n × Fin n) →
      MvPolynomial (GLIdx n ⊕ (((Fin n × Fin n) ⊕ Unit) ⊕ (Fin n × Fin n))) K :=
  Sum.elim
    (Sum.elim (fun ij => borelIncFrameMat K n ij.1 ij.2)
      (fun _ => MvPolynomial.X (Sum.inr (Sum.inl (Sum.inr ())))
          * (coordMat (fun ab => Sum.inl (Sum.inl ab))).det))
    (fun ij => MvPolynomial.X (Sum.inr (Sum.inr ij)))

variable (K n) in
/-- The action data of the Borel on the incidence space: the whole affine space
(`J = ⊥`). -/
noncomputable def borelIncData :
    ActionData (GLPair.borel K n).toGroupData
      (((Fin n × Fin n) ⊕ Unit) ⊕ (Fin n × Fin n)) where
  J := ⊥
  act := borelIncPoly K n
  act_mem := fun f hf => by rw [Ideal.mem_bot.mp hf, map_zero, map_zero, map_zero]

/-- The frame matrix is right translated by the `h` block. -/
@[simp] theorem chartMat_borelIncActPt (a : GLIdx n → K)
    (v : ((Fin n × Fin n) ⊕ Unit) ⊕ (Fin n × Fin n) → K) :
    chartMat (incFrame ((borelIncData K n).actPt a v))
      = chartMat (incFrame v) * GLPair.hPt K n a := by
  have h : (borelIncFrameMat K n).map (MvPolynomial.aeval (Sum.elim a v))
      = chartMat (incFrame v) * GLPair.hPt K n a := by
    rw [borelIncFrameMat, map_mul_polyMat, map_genMat, map_genMat]
    rfl
  exact Matrix.ext fun i j => congrFun (congrFun h i) j

/-- The inverse-determinant coordinate is multiplied by `det g`. -/
@[simp] theorem chartInv_borelIncActPt (a : GLIdx n → K)
    (v : ((Fin n × Fin n) ⊕ Unit) ⊕ (Fin n × Fin n) → K) :
    chartInv (incFrame ((borelIncData K n).actPt a v))
      = chartInv (incFrame v) * (GLPair.gPt K n a).det :=
  aeval_mul_det_coordMat _ _ (Sum.elim a v)

/-- The partner block is untouched. -/
@[simp] theorem incMat_borelIncActPt (a : GLIdx n → K)
    (v : ((Fin n × Fin n) ⊕ Unit) ⊕ (Fin n × Fin n) → K) :
    incMat ((borelIncData K n).actPt a v) = incMat v :=
  Matrix.ext fun i j => MvPolynomial.aeval_X (Sum.elim a v) (Sum.inr (Sum.inr (i, j)))

@[simp] theorem partnerMap_borelIncActPt (a : GLIdx n → K)
    (v : ((Fin n × Fin n) ⊕ Unit) ⊕ (Fin n × Fin n) → K) :
    partnerMap ((borelIncData K n).actPt a v) = partnerMap v :=
  funext fun ij => MvPolynomial.aeval_X (Sum.elim a v) (Sum.inr (Sum.inr ij))

variable (K n) in
/-- **The Borel acting on the incidence space**, as an `ActionPresentation`.  Both comodule
axioms are action laws that hold on the nose: `1 ⋆ v = v` because `h_1 = 1` and `det g_1 = 1`,
and `b ⋆ (a ⋆ v) = (b a) ⋆ v` because `(G h_a) h_b = G (h_a h_b) = G h_{ba}` and
`(t det g_a) det g_b = t det (g_b g_a) = t det g_{ba}`. -/
noncomputable def borelIncAction :
    ActionPresentation (GLPair.borel K n)
      (((Fin n × Fin n) ⊕ Unit) ⊕ (Fin n × Fin n)) :=
  ActionPresentation.ofLaws (borelIncData K n)
    (by
      -- `1 ⋆ v = v`: both group blocks of the unit are the identity matrix
      set σ : GLIdx n ⊕ (((Fin n × Fin n) ⊕ Unit) ⊕ (Fin n × Fin n)) →
          MvPolynomial (((Fin n × Fin n) ⊕ Unit) ⊕ (Fin n × Fin n)) K :=
        Sum.elim (fun j => MvPolynomial.C (GLPair.glOne K n j)) MvPolynomial.X with hσ
      have hone : ∀ ab : Fin n × Fin n, σ (Sum.inl (Sum.inr ab))
          = (1 : Matrix (Fin n) (Fin n)
              (MvPolynomial (((Fin n × Fin n) ⊕ Unit) ⊕ (Fin n × Fin n)) K)) ab.1 ab.2 := by
        intro ab
        simp [hσ, GLPair.glOne, Matrix.one_apply, apply_ite]
      have hone' : ∀ ab : Fin n × Fin n, σ (Sum.inl (Sum.inl ab))
          = (1 : Matrix (Fin n) (Fin n)
              (MvPolynomial (((Fin n × Fin n) ⊕ Unit) ⊕ (Fin n × Fin n)) K)) ab.1 ab.2 := by
        intro ab
        simp [hσ, GLPair.glOne, Matrix.one_apply, apply_ite]
      have hframe : (borelIncFrameMat K n).map (MvPolynomial.aeval σ)
          = coordMat fun ab : Fin n × Fin n => Sum.inl (Sum.inl ab) := by
        rw [borelIncFrameMat, Matrix.map_mul, map_coordMat_aeval, map_coordMat_aeval,
          show (Matrix.of fun i j => σ (Sum.inl (Sum.inr (i, j)))) = 1 from
            Matrix.ext fun i j => hone (i, j), mul_one]
        exact Matrix.ext fun i j => rfl
      have hg : (Matrix.of fun i j => σ (Sum.inl (Sum.inl (i, j)))) = 1 :=
        Matrix.ext fun i j => hone' (i, j)
      rintro ((ij | u) | ij)
      · exact sub_mem_of_eq (congrFun (congrFun hframe ij.1) ij.2)
      · refine sub_mem_of_eq ?_
        show MvPolynomial.aeval σ (MvPolynomial.X (Sum.inr (Sum.inl (Sum.inr ())))
          * (coordMat fun ab : Fin n × Fin n => Sum.inl (Sum.inl ab)).det) = _
        rw [aeval_mul_det_coordMat, hg, Matrix.det_one, mul_one]
        rfl
      · exact sub_mem_of_eq (MvPolynomial.aeval_X σ (Sum.inr (Sum.inr ij))))
    (by
      -- `b ⋆ (a ⋆ v) = (b a) ⋆ v`: associativity on the frame, `det_mul` on the chart
      rintro ((ij | u) | ij)
      · exact sub_mem_of_eq (by
          simp [ActionData.actAct, ActionData.mulAct, ActionData.act1, GroupData.mulFlip,
            borelIncData, borelIncPoly, borelIncFrameMat, GLPair.glMul, GLPair.inlHom,
            GLPair.inrHom, coordMat, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul,
            mul_assoc]
          exact Finset.sum_comm)
      · refine sub_mem_of_eq ?_
        -- the two group blocks' `g`, in the triple space
        set Ga : Matrix (Fin n) (Fin n)
            (MvPolynomial (GLIdx n ⊕ GLIdx n ⊕ (((Fin n × Fin n) ⊕ Unit) ⊕ (Fin n × Fin n))) K)
            := Matrix.of fun i j => MvPolynomial.X (Sum.inl (Sum.inl (i, j))) with hGa
        set Gb : Matrix (Fin n) (Fin n)
            (MvPolynomial (GLIdx n ⊕ GLIdx n ⊕ (((Fin n × Fin n) ⊕ Unit) ⊕ (Fin n × Fin n))) K)
            := Matrix.of fun i j => MvPolynomial.X (Sum.inr (Sum.inl (Sum.inl (i, j)))) with hGb
        have hA : (Matrix.of fun i j => Sum.elim
              (fun j : GLIdx n => MvPolynomial.X (Sum.inr (Sum.inl j)))
              (borelIncData K n).act1 (Sum.inl (Sum.inl (i, j)))) = Gb := rfl
        have hB : (Matrix.of fun i j => Sum.elim
              ((GLPair.borel K n).mulFlip (((Fin n × Fin n) ⊕ Unit) ⊕ (Fin n × Fin n)))
              (fun k => MvPolynomial.X (Sum.inr (Sum.inr k))) (Sum.inl (Sum.inl (i, j))))
            = Gb * Ga := by
          refine Matrix.ext fun i j => ?_
          simp [hGa, hGb, GroupData.mulFlip, GLPair.glMul, GLPair.inlHom, GLPair.inrHom,
            Matrix.mul_apply]
        have hT : Sum.elim (fun j : GLIdx n => MvPolynomial.X (Sum.inr (Sum.inl j)))
              (borelIncData K n).act1 (Sum.inr (Sum.inl (Sum.inr ())))
            = MvPolynomial.X (Sum.inr (Sum.inr (Sum.inl (Sum.inr ())))) * Ga.det := by
          show MvPolynomial.aeval (Sum.elim (fun j : GLIdx n => MvPolynomial.X (Sum.inl j))
              fun k => MvPolynomial.X (Sum.inr (Sum.inr k)))
              (MvPolynomial.X (Sum.inr (Sum.inl (Sum.inr ())))
                * (coordMat fun ab : Fin n × Fin n => Sum.inl (Sum.inl ab)).det) = _
          rw [aeval_mul_det_coordMat]
          rfl
        show MvPolynomial.aeval (Sum.elim
            (fun j : GLIdx n => MvPolynomial.X (Sum.inr (Sum.inl j))) (borelIncData K n).act1)
              (MvPolynomial.X (Sum.inr (Sum.inl (Sum.inr ())))
                * (coordMat fun ab : Fin n × Fin n => Sum.inl (Sum.inl ab)).det)
          = MvPolynomial.aeval (Sum.elim
            ((GLPair.borel K n).mulFlip (((Fin n × Fin n) ⊕ Unit) ⊕ (Fin n × Fin n)))
              fun k => MvPolynomial.X (Sum.inr (Sum.inr k)))
              (MvPolynomial.X (Sum.inr (Sum.inl (Sum.inr ())))
                * (coordMat fun ab : Fin n × Fin n => Sum.inl (Sum.inl ab)).det)
        rw [aeval_mul_det_coordMat, aeval_mul_det_coordMat, hA, hB, hT, Matrix.det_mul]
        show _ = MvPolynomial.X (Sum.inr (Sum.inr (Sum.inl (Sum.inr ())))) * _
        ring
      · exact sub_mem_of_eq (by
          show MvPolynomial.aeval (Sum.elim
              (fun j : GLIdx n => MvPolynomial.X (Sum.inr (Sum.inl j)))
              (borelIncData K n).act1) (MvPolynomial.X (Sum.inr (Sum.inr ij)))
            = MvPolynomial.aeval (Sum.elim
              ((GLPair.borel K n).mulFlip (((Fin n × Fin n) ⊕ Unit) ⊕ (Fin n × Fin n)))
              fun k => MvPolynomial.X (Sum.inr (Sum.inr k)))
              (MvPolynomial.X (Sum.inr (Sum.inr ij)))
          rw [MvPolynomial.aeval_X, MvPolynomial.aeval_X]
          show (borelIncData K n).act1 (Sum.inr ij) = _
          exact MvPolynomial.aeval_X _ (Sum.inr (Sum.inr ij))))

theorem borelIncAction_J : (borelIncAction K n).J = ⊥ := rfl

theorem borelIncAction_actPt (a : GLIdx n → K)
    (v : ((Fin n × Fin n) ⊕ Unit) ⊕ (Fin n × Fin n) → K) :
    (borelIncAction K n).actPt a v = (borelIncData K n).actPt a v := rfl

/-- The two blocks of a `K`-point of the Borel have reciprocal determinants. -/
theorem det_mul_det_of_mem_borel_pts {a : GLIdx n → K} (ha : a ∈ (GLPair.borel K n).pts) :
    (GLPair.gPt K n a).det * (GLPair.hPt K n a).det = 1 :=
  (Matrix.det_mul _ _).symm.trans
    (by rw [((GLPair.mem_borel_pts_iff a).mp ha).1, Matrix.det_one])

theorem isUnit_det_hPt_of_mem_borel_pts {a : GLIdx n → K} (ha : a ∈ (GLPair.borel K n).pts) :
    IsUnit (GLPair.hPt K n a).det := by
  refine isUnit_iff_ne_zero.mpr fun h0 => ?_
  have h := det_mul_det_of_mem_borel_pts ha
  rw [h0, mul_zero] at h
  exact zero_ne_one h

/-- **The incidence is stable under the Borel.** -/
theorem actPt_mem_partnerIncidence {N : Matrix (Fin n) (Fin n) K}
    {a : GLIdx n → K} (ha : a ∈ (GLPair.borel K n).pts)
    {v : ((Fin n × Fin n) ⊕ Unit) ⊕ (Fin n × Fin n) → K} (hv : v ∈ partnerIncidence N) :
    (borelIncAction K n).actPt a v ∈ partnerIncidence N := by
  obtain ⟨hframe, horb, hpart⟩ := hv
  obtain ⟨-, -, -, hb⟩ := (GLPair.mem_borel_pts_iff a).mp ha
  have hdet := det_mul_det_of_mem_borel_pts ha
  have hbu : IsUnit (GLPair.hPt K n a).det := isUnit_det_hPt_of_mem_borel_pts ha
  rw [borelIncAction_actPt]
  refine ⟨?_, ?_, ?_⟩
  · refine mem_frameChart_iff.mpr ⟨?_, ?_⟩
    · rw [chartMat_borelIncActPt]
      exact adjugate_sandwich_mem hb hbu (mem_frameChart_iff.mp hframe).1
    · rw [chartMat_borelIncActPt, chartInv_borelIncActPt, Matrix.det_mul]
      calc chartInv (incFrame v) * (GLPair.gPt K n a).det *
            ((chartMat (incFrame v)).det * (GLPair.hPt K n a).det)
          = (chartInv (incFrame v) * (chartMat (incFrame v)).det) *
              ((GLPair.gPt K n a).det * (GLPair.hPt K n a).det) := by ring
        _ = 1 := by rw [hdet, (mem_frameChart_iff.mp hframe).2, mul_one]
  · rw [incMat_borelIncActPt]
    exact horb
  · rw [incMat_borelIncActPt, chartMat_borelIncActPt]
    exact adjugate_sandwich_mem hb hbu hpart

/-! ### The Borel is irreducible

`Chain/Springer`'s Borel chart `borelChart` — the invertible upper triangular matrices with
their inverse determinant — is irreducible (`isPrime_vanishingIdeal_borelChart`), and the
`K`-points of the presented Borel are its image under the polynomial map
`c ↦ (t · adj g, g)`, so they are irreducible too (`irreducible_image`). -/

variable (K n) in
/-- The polynomial matrix of `c ↦ t · adj g`, the first block of the pair. -/
noncomputable def chartToPairPolyMat :
    Matrix (Fin n) (Fin n) (MvPolynomial ((Fin n × Fin n) ⊕ Unit) K) :=
  (MvPolynomial.X (Sum.inr ()) : MvPolynomial ((Fin n × Fin n) ⊕ Unit) K) •
    (coordMat (K := K) Sum.inl).adjugate

/-- The pair-model coordinates of a point of the Borel chart: `(g⁻¹, g)`, with `g⁻¹` in the
`adjugate` form which is polynomial on the chart. -/
def chartToPair (c : (Fin n × Fin n) ⊕ Unit → K) : GLIdx n → K :=
  Sum.elim (fun ij => (chartInv c • Matrix.adjugate (chartMat c)) ij.1 ij.2)
    (fun ij => chartMat c ij.1 ij.2)

theorem isPolyMap_chartToPair : IsPolyMap (chartToPair (K := K) (n := n)) :=
  ⟨Sum.elim (fun ij => chartToPairPolyMat K n ij.1 ij.2)
      (fun ij => MvPolynomial.X (Sum.inl ij)),
    fun c i => by
      have hmap : (chartToPairPolyMat K n).map (MvPolynomial.aeval c)
          = chartInv c • Matrix.adjugate (chartMat c) := by
        rw [chartToPairPolyMat, map_smul_polyMat, map_adjugate_polyMat, map_genMat,
          MvPolynomial.aeval_X]
        rfl
      cases i with
      | inl ij =>
          calc chartToPair c (Sum.inl ij)
              = (chartInv c • Matrix.adjugate (chartMat c)) ij.1 ij.2 := rfl
            _ = _ := by rw [← hmap]; rfl
      | inr ij => simp [chartToPair, chartMat]⟩

/-- **The `K`-points of the presented Borel are the image of the Borel chart.** -/
theorem borel_pts_eq_image : (GLPair.borel K n).pts = chartToPair '' borelChart K n := by
  ext a
  constructor
  · intro ha
    obtain ⟨h1, -, -, h4⟩ := (GLPair.mem_borel_pts_iff a).mp ha
    have hbu : IsUnit (GLPair.hPt K n a).det := isUnit_det_hPt_of_mem_borel_pts ha
    refine ⟨Sum.elim (matCoords (GLPair.hPt K n a)) (fun _ => ((GLPair.hPt K n a).det)⁻¹),
      mem_borelChart_iff.mpr ⟨h4, inv_mul_cancel₀ (isUnit_iff_ne_zero.mp hbu)⟩, ?_⟩
    have hg : GLPair.gPt K n a = (GLPair.hPt K n a)⁻¹ := (Matrix.inv_eq_left_inv h1).symm
    have hinv : ((GLPair.hPt K n a).det)⁻¹ • Matrix.adjugate (GLPair.hPt K n a)
        = (GLPair.hPt K n a)⁻¹ := by
      rw [Matrix.inv_def, Ring.inverse_eq_inv]
    refine funext fun i => ?_
    cases i with
    | inl ij =>
        show (((GLPair.hPt K n a).det)⁻¹ • Matrix.adjugate (GLPair.hPt K n a)) ij.1 ij.2
          = a (Sum.inl ij)
        rw [hinv, ← hg]
        rfl
    | inr ij => rfl
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨hb, -⟩ := mem_borelChart_iff.mp hc
    have hbu : IsUnit (chartMat c).det := isUnit_det_chartMat_of_borel hc
    have hgc : GLPair.gPt K n (chartToPair c) = (chartMat c)⁻¹ := by
      refine Matrix.ext fun i j => ?_
      show (chartInv c • Matrix.adjugate (chartMat c)) i j = _
      rw [Matrix.inv_def, Ring.inverse_eq_inv, chartInv_eq_of_borel hc]
    have hhc : GLPair.hPt K n (chartToPair c) = chartMat c := rfl
    refine (GLPair.mem_borel_pts_iff _).mpr ⟨?_, ?_, ?_, ?_⟩
    · rw [hgc, hhc, Matrix.nonsing_inv_mul _ hbu]
    · rw [hgc, hhc, Matrix.mul_nonsing_inv _ hbu]
    · rw [hgc]; exact inv_mem_standardBorel hb hbu
    · rw [hhc]; exact hb

/-- **The presented Borel is irreducible.** -/
theorem isPrime_vanishingIdeal_borel_pts [Infinite K] :
    (MvPolynomial.vanishingIdeal K (GLPair.borel K n).pts).IsPrime := by
  rw [borel_pts_eq_image]
  exact irreducible_image isPolyMap_chartToPair isPrime_vanishingIdeal_borelChart

end BorelIncidence

/-- For a unit of the matrix ring the ring inverse and the nonsingular inverse
agree. -/
theorem coe_units_inv (u : (Matrix (Fin n) (Fin n) K)ˣ) :
    ((u : Matrix (Fin n) (Fin n) K))⁻¹ = ((↑u⁻¹ : Matrix (Fin n) (Fin n) K)) := by
  rw [Matrix.nonsing_inv_eq_ringInverse, Ring.inverse_unit]

/-- `adj g * Q * g ∈ 𝔫` and `g⁻¹ Q g ∈ 𝔫` say the same thing for invertible
`g`. -/
theorem adjugate_sandwich_iff {g Q : Matrix (Fin n) (Fin n) K} (hg : IsUnit g.det) :
    Matrix.adjugate g * Q * g ∈ standardNilradical K n ↔
      g⁻¹ * Q * g ∈ standardNilradical K n := by
  have hdet : g.det ≠ 0 := isUnit_iff_ne_zero.mp hg
  have hinv : g⁻¹ * Q * g = (g.det)⁻¹ • (Matrix.adjugate g * Q * g) := by
    rw [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_mul, Matrix.smul_mul]
  have hadj : Matrix.adjugate g * Q * g = g.det • (g⁻¹ * Q * g) := by
    rw [hinv, smul_smul, mul_inv_cancel₀ hdet, one_smul]
  constructor
  · intro h
    rw [hinv]
    exact Submodule.smul_mem _ _ h
  · intro h
    rw [hadj]
    exact Submodule.smul_mem _ _ h

/-- **The image of the partner map** is the triangularizable partner locus
inside the orbit. -/
theorem partnerMap_image (N : Matrix (Fin n) (Fin n) K) :
    partnerMap '' partnerIncidence N =
      matCoords '' (triangularizablePartnerLocus n N ∩ conjOrbit N) := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨v, ⟨hframe, horb, hpart⟩, rfl⟩
    have hgu : IsUnit (chartMat (incFrame v)).det := isUnit_det_chartMat hframe
    have hgunit : IsUnit (chartMat (incFrame v)) :=
      (Matrix.isUnit_iff_isUnit_det _).mpr hgu
    refine ⟨incMat v, ⟨?_, horb⟩, rfl⟩
    refine (mem_triangularizablePartnerLocus_iff_exists_conjugateNilradical n N _).mpr
      ⟨hgunit.unit, ?_, ?_⟩
    · rw [mem_conjugateNilradical_iff, ← coe_units_inv, hgunit.unit_spec]
      exact (adjugate_sandwich_iff hgu).mp (mem_frameChart_iff.mp hframe).1
    · rw [mem_conjugateNilradical_iff, ← coe_units_inv, hgunit.unit_spec]
      exact (adjugate_sandwich_iff hgu).mp hpart
  · rintro _ ⟨M, ⟨htri, horb⟩, rfl⟩
    obtain ⟨u, hN, hM⟩ :=
      (mem_triangularizablePartnerLocus_iff_exists_conjugateNilradical n N M).mp htri
    rw [mem_conjugateNilradical_iff, ← coe_units_inv] at hN hM
    have hgu : IsUnit ((u : Matrix (Fin n) (Fin n) K)).det :=
      (Matrix.isUnit_iff_isUnit_det _).mp u.isUnit
    have hdet : ((u : Matrix (Fin n) (Fin n) K)).det ≠ 0 := isUnit_iff_ne_zero.mp hgu
    refine ⟨Sum.elim (Sum.elim (matCoords (u : Matrix (Fin n) (Fin n) K))
      (fun _ => (((u : Matrix (Fin n) (Fin n) K)).det)⁻¹)) (matCoords M), ⟨?_, ?_, ?_⟩, rfl⟩
    · refine mem_frameChart_iff.mpr ⟨?_, ?_⟩
      · exact (adjugate_sandwich_iff hgu).mpr hN
      · exact inv_mul_cancel₀ hdet
    · exact horb
    · exact (adjugate_sandwich_iff hgu).mpr hM

/-! ### The dimension of a Borel orbit -/

/-- The invertible upper triangular matrices. -/
def borelUnits (K : Type u) [Field K] (n : ℕ) : Set (Matrix (Fin n) (Fin n) K) :=
  {b | b ∈ standardBorel K n ∧ IsUnit b.det}

theorem matCoords_image_borelUnits :
    matCoords '' borelUnits K n =
      ((borelSpace K n : Submodule K (Fin n × Fin n → K)) : Set (Fin n × Fin n → K)) ∩
        {z | MvPolynomial.aeval z (detPoly (K := K) (Fin n)) ≠ 0} := by
  ext z
  constructor
  · rintro ⟨b, ⟨hb, hbu⟩, rfl⟩
    refine ⟨mem_borelSpace.mpr (by rwa [matCoords.symm_apply_apply]), ?_⟩
    show MvPolynomial.aeval (matCoords b) (detPoly (K := K) (Fin n)) ≠ 0
    rw [aeval_detPoly, matCoords.symm_apply_apply]
    exact isUnit_iff_ne_zero.mp hbu
  · rintro ⟨hz, hzd⟩
    replace hzd : MvPolynomial.aeval z (detPoly (K := K) (Fin n)) ≠ 0 := hzd
    refine ⟨matCoords.symm z, ⟨mem_borelSpace.mp hz, ?_⟩, matCoords.apply_symm_apply z⟩
    rw [aeval_detPoly] at hzd
    exact isUnit_iff_ne_zero.mpr hzd

theorem affineDim_matCoords_borelUnits [IsAlgClosed K] :
    affineDim (matCoords '' borelUnits K n) = ((((n.choose 2 + n : ℕ)) : ℕ∞) : WithBot ℕ∞) := by
  rw [matCoords_image_borelUnits,
    affineDim_inter_dense (isPrime_vanishingIdeal_submodule _)
      detPoly_notMem_vanishingIdeal_borelSpace,
    affineDim_submodule, finrank_borelSpace]

/-- The frame-matrix block of the incidence space. -/
def frameMatMap : (((Fin n × Fin n) ⊕ Unit) ⊕ (Fin n × Fin n) → K) → (Fin n × Fin n → K) :=
  fun v => fun ij => v (Sum.inl (Sum.inl ij))

theorem isPolyMap_frameMatMap : IsPolyMap (frameMatMap (K := K) (n := n)) :=
  ⟨fun ij => MvPolynomial.X (Sum.inl (Sum.inl ij)), fun v ij => by
    show v (Sum.inl (Sum.inl ij)) = _
    simp⟩

section BorelOrbit

variable {K : Type} [Field K] {n : ℕ}

/-- The `h` block of a `K`-point of the Borel is an invertible upper triangular matrix. -/
theorem hPt_mem_borelUnits {a : GLIdx n → K} (ha : a ∈ (GLPair.borel K n).pts) :
    GLPair.hPt K n a ∈ borelUnits K n :=
  ⟨((GLPair.mem_borel_pts_iff a).mp ha).2.2.2, isUnit_det_hPt_of_mem_borel_pts ha⟩

/-- Conversely, every invertible upper triangular matrix is the `h` block of a `K`-point of
the Borel — the pair `(b⁻¹, b)`. -/
theorem mem_borel_pts_pair {b : Matrix (Fin n) (Fin n) K} (hb : b ∈ borelUnits K n) :
    Sum.elim (fun ij => b⁻¹ ij.1 ij.2) (fun ij => b ij.1 ij.2) ∈ (GLPair.borel K n).pts :=
  (GLPair.mem_borel_pts_iff _).mpr
    ⟨Matrix.nonsing_inv_mul b hb.2, Matrix.mul_nonsing_inv b hb.2,
      inv_mem_standardBorel hb.1 hb.2, hb.1⟩

/-- The Borel orbits of the incidence space are the right translates of the frame by the
invertible upper triangular matrices. -/
theorem frameMatMap_image_orbit (v : ((Fin n × Fin n) ⊕ Unit) ⊕ (Fin n × Fin n) → K) :
    frameMatMap '' {z | ∃ a ∈ (GLPair.borel K n).pts, (borelIncAction K n).actPt a v = z} =
      matCoords '' ((fun h => chartMat (incFrame v) * h) '' borelUnits K n) := by
  have hfm : ∀ w : ((Fin n × Fin n) ⊕ Unit) ⊕ (Fin n × Fin n) → K,
      frameMatMap w = matCoords (chartMat (incFrame w)) := fun _ => rfl
  ext z
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    refine ⟨chartMat (incFrame v) * GLPair.hPt K n a,
      ⟨GLPair.hPt K n a, hPt_mem_borelUnits ha, rfl⟩, ?_⟩
    rw [hfm, borelIncAction_actPt, chartMat_borelIncActPt]
  · rintro ⟨_, ⟨b, hb, rfl⟩, rfl⟩
    refine ⟨(borelIncAction K n).actPt
      (Sum.elim (fun ij => b⁻¹ ij.1 ij.2) (fun ij => b ij.1 ij.2)) v,
      ⟨_, mem_borel_pts_pair hb, rfl⟩, ?_⟩
    rw [hfm, borelIncAction_actPt, chartMat_borelIncActPt]
    rfl

/-- **Every Borel orbit through an adapted frame has dimension at least
`n(n+1)/2`.** -/
theorem affineDim_orbit_ge [IsAlgClosed K] {N : Matrix (Fin n) (Fin n) K}
    {v : ((Fin n × Fin n) ⊕ Unit) ⊕ (Fin n × Fin n) → K} (hv : incFrame v ∈ frameChart N) :
    ((((n.choose 2 + n : ℕ)) : ℕ∞) : WithBot ℕ∞) ≤
      affineDim {z | ∃ a ∈ (GLPair.borel K n).pts, (borelIncAction K n).actPt a v = z} := by
  have hgu : IsUnit (chartMat (incFrame v)).det := isUnit_det_chartMat hv
  calc ((((n.choose 2 + n : ℕ)) : ℕ∞) : WithBot ℕ∞)
      = affineDim (matCoords '' borelUnits K n) := affineDim_matCoords_borelUnits.symm
    _ = affineDim (matCoords '' ((fun h => chartMat (incFrame v) * h) '' borelUnits K n)) :=
        (affineDim_leftCoset hgu _).symm
    _ = affineDim (frameMatMap ''
          {z | ∃ a ∈ (GLPair.borel K n).pts, (borelIncAction K n).actPt a v = z}) := by
        rw [frameMatMap_image_orbit]
    _ ≤ affineDim {z | ∃ a ∈ (GLPair.borel K n).pts, (borelIncAction K n).actPt a v = z} :=
        affineDim_image_le isPolyMap_frameMatMap _

end BorelOrbit

/-! ### The incidence and the product have the same dimension -/

/-- The polynomial matrix of `σ : (g,t,M) ↦ g⁻¹ M g`. -/
noncomputable def incToProdPoly (K : Type u) [Field K] (n : ℕ) :
    Matrix (Fin n) (Fin n)
      (MvPolynomial (((Fin n × Fin n) ⊕ Unit) ⊕ (Fin n × Fin n)) K) :=
  (MvPolynomial.X (Sum.inl (Sum.inr ())) :
      MvPolynomial (((Fin n × Fin n) ⊕ Unit) ⊕ (Fin n × Fin n)) K) •
    ((coordMat (fun ab => Sum.inl (Sum.inl ab))).adjugate * coordMat (fun ab => Sum.inr ab) *
      coordMat (fun ab => Sum.inl (Sum.inl ab)))

/-- The polynomial matrix of `τ : (g,t,m) ↦ g m g⁻¹`. -/
noncomputable def prodToIncPoly (K : Type u) [Field K] (n : ℕ) :
    Matrix (Fin n) (Fin n)
      (MvPolynomial (((Fin n × Fin n) ⊕ Unit) ⊕ (Fin n × Fin n)) K) :=
  (MvPolynomial.X (Sum.inl (Sum.inr ())) :
      MvPolynomial (((Fin n × Fin n) ⊕ Unit) ⊕ (Fin n × Fin n)) K) •
    (coordMat (fun ab => Sum.inl (Sum.inl ab)) * coordMat (fun ab => Sum.inr ab) *
      (coordMat (fun ab => Sum.inl (Sum.inl ab))).adjugate)

/-- `σ (g,t,M) = (g,t, g⁻¹ M g)`. -/
noncomputable def incToProd (v : ((Fin n × Fin n) ⊕ Unit) ⊕ (Fin n × Fin n) → K) :
    ((Fin n × Fin n) ⊕ Unit) ⊕ (Fin n × Fin n) → K :=
  Sum.elim (incFrame v)
    (matCoords (chartInv (incFrame v) •
      (Matrix.adjugate (chartMat (incFrame v)) * incMat v * chartMat (incFrame v))))

/-- `τ (g,t,m) = (g,t, g m g⁻¹)`. -/
noncomputable def prodToInc (v : ((Fin n × Fin n) ⊕ Unit) ⊕ (Fin n × Fin n) → K) :
    ((Fin n × Fin n) ⊕ Unit) ⊕ (Fin n × Fin n) → K :=
  Sum.elim (incFrame v)
    (matCoords (chartInv (incFrame v) •
      (chartMat (incFrame v) * incMat v * Matrix.adjugate (chartMat (incFrame v)))))

@[simp] theorem incFrame_incToProd (v : ((Fin n × Fin n) ⊕ Unit) ⊕ (Fin n × Fin n) → K) :
    incFrame (incToProd v) = incFrame v := rfl
@[simp] theorem incMat_incToProd (v : ((Fin n × Fin n) ⊕ Unit) ⊕ (Fin n × Fin n) → K) :
    incMat (incToProd v) = chartInv (incFrame v) •
      (Matrix.adjugate (chartMat (incFrame v)) * incMat v * chartMat (incFrame v)) := rfl
@[simp] theorem incMat_prodToInc (v : ((Fin n × Fin n) ⊕ Unit) ⊕ (Fin n × Fin n) → K) :
    incMat (prodToInc v) = chartInv (incFrame v) •
      (chartMat (incFrame v) * incMat v * Matrix.adjugate (chartMat (incFrame v))) := rfl

/-- `σ` and `τ` have one shape: the frame coordinates are copied and the matrix block is a
polynomial matrix `F` in all the coordinates.  Stated once, so the two differ only in which
`F` they supply and not in the substitution bookkeeping. -/
theorem isPolyMap_sumElim_incFrame
    (F : Matrix (Fin n) (Fin n)
      (MvPolynomial (((Fin n × Fin n) ⊕ Unit) ⊕ (Fin n × Fin n)) K))
    (f : (((Fin n × Fin n) ⊕ Unit) ⊕ (Fin n × Fin n) → K) → Matrix (Fin n) (Fin n) K)
    (hF : ∀ v, F.map (MvPolynomial.aeval v) = f v) :
    IsPolyMap (fun v => Sum.elim (incFrame v) (matCoords (f v))) := by
  refine ⟨fun i => Sum.elim
    (Sum.elim (fun ij => MvPolynomial.X (Sum.inl (Sum.inl ij)))
      (fun _ => MvPolynomial.X (Sum.inl (Sum.inr ()))))
    (fun ij => F ij.1 ij.2) i, ?_⟩
  intro v i
  cases i with
  | inl j =>
      cases j with
      | inl ij => show v (Sum.inl (Sum.inl ij)) = _; simp
      | inr u =>
          have hu : u = () := rfl
          subst hu
          show v (Sum.inl (Sum.inr ())) = _
          simp
  | inr ij =>
      show (f v) ij.1 ij.2 = _
      rw [← hF v]
      rfl

theorem isPolyMap_incToProd : IsPolyMap (incToProd (K := K) (n := n)) :=
  isPolyMap_sumElim_incFrame (incToProdPoly K n)
    (fun v => chartInv (incFrame v) •
      (Matrix.adjugate (chartMat (incFrame v)) * incMat v * chartMat (incFrame v)))
    fun v => by
      rw [incToProdPoly, map_smul_polyMat, map_mul_polyMat, map_mul_polyMat,
        map_adjugate_polyMat, map_genMat, map_genMat, MvPolynomial.aeval_X]
      rfl

theorem isPolyMap_prodToInc : IsPolyMap (prodToInc (K := K) (n := n)) :=
  isPolyMap_sumElim_incFrame (prodToIncPoly K n)
    (fun v => chartInv (incFrame v) •
      (chartMat (incFrame v) * incMat v * Matrix.adjugate (chartMat (incFrame v))))
    fun v => by
      rw [prodToIncPoly, map_smul_polyMat, map_mul_polyMat, map_mul_polyMat,
        map_adjugate_polyMat, map_genMat, map_genMat, MvPolynomial.aeval_X]
      rfl

theorem prodToInc_incToProd {N : Matrix (Fin n) (Fin n) K}
    {v : ((Fin n × Fin n) ⊕ Unit) ⊕ (Fin n × Fin n) → K} (hv : v ∈ partnerIncidence N) :
    prodToInc (incToProd v) = v := by
  obtain ⟨hframe, -, -⟩ := hv
  set g := chartMat (incFrame v) with hg
  set t := chartInv (incFrame v) with ht
  have htg : t * g.det = 1 := (mem_frameChart_iff.mp hframe).2
  refine inc_ext rfl ?_
  rw [incMat_prodToInc, incFrame_incToProd, incMat_incToProd, ← hg, ← ht]
  have hga : g * Matrix.adjugate g = g.det • (1 : Matrix (Fin n) (Fin n) K) :=
    Matrix.mul_adjugate g
  calc t • (g * (t • (Matrix.adjugate g * incMat v * g)) * Matrix.adjugate g)
      = (t * t) • ((g * Matrix.adjugate g) * incMat v * (g * Matrix.adjugate g)) := by
        rw [Matrix.mul_smul, Matrix.smul_mul, smul_smul]
        congr 1
        simp only [Matrix.mul_assoc]
    _ = (t * t) • ((g.det • (1 : Matrix (Fin n) (Fin n) K)) * incMat v *
          (g.det • (1 : Matrix (Fin n) (Fin n) K))) := by rw [hga]
    _ = ((t * g.det) * (t * g.det)) • incMat v := by
        rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul, smul_smul]
        congr 1
        ring
    _ = incMat v := by rw [htg, mul_one, one_smul]

theorem incToProd_image_subset {N : Matrix (Fin n) (Fin n) K} :
    incToProd '' partnerIncidence N ⊆ sumProd (frameChart N) (nilOrbit N) := by
  rintro _ ⟨v, ⟨hframe, horb, hpart⟩, rfl⟩
  have hgu : IsUnit (chartMat (incFrame v)).det := isUnit_det_chartMat hframe
  have hgunit : IsUnit (chartMat (incFrame v)) := (Matrix.isUnit_iff_isUnit_det _).mpr hgu
  have hconj : chartInv (incFrame v) •
      (Matrix.adjugate (chartMat (incFrame v)) * incMat v * chartMat (incFrame v)) =
      (chartMat (incFrame v))⁻¹ * incMat v * chartMat (incFrame v) := by
    rw [inv_chartMat hframe, Matrix.smul_mul, Matrix.smul_mul]
  refine ⟨hframe, ?_⟩
  refine ⟨incMat (incToProd v), ⟨?_, ?_⟩, rfl⟩
  · rw [incMat_incToProd, hconj]
    exact (adjugate_sandwich_iff hgu).mp hpart
  · rw [incMat_incToProd, hconj]
    obtain ⟨k, hk⟩ := horb
    have hval : ((Matrix.nonsingInvUnit (chartMat (incFrame v)) hgu :
        (Matrix (Fin n) (Fin n) K)ˣ) : Matrix (Fin n) (Fin n) K) = chartMat (incFrame v) := rfl
    refine ⟨(Matrix.nonsingInvUnit (chartMat (incFrame v)) hgu)⁻¹ * k, ?_⟩
    rw [hk]
    show (chartMat (incFrame v))⁻¹ * ((k : Matrix (Fin n) (Fin n) K) * N * (↑k⁻¹ :
      Matrix (Fin n) (Fin n) K)) * chartMat (incFrame v) = _
    simp [Matrix.mul_assoc, hval]

theorem affineDim_partnerIncidence_le {K : Type} [Field K] [IsAlgClosed K] {n : ℕ}
    {N : Matrix (Fin n) (Fin n) K} :
    affineDim (partnerIncidence N) ≤ affineDim (frameChart N) + affineDim (nilOrbit N) := by
  have h1 : affineDim (incToProd '' partnerIncidence N) = affineDim (partnerIncidence N) :=
    affineDim_image_eq isPolyMap_incToProd isPolyMap_prodToInc
      (fun y hy => prodToInc_incToProd hy)
  rw [← h1]
  exact le_trans (affineDim_mono incToProd_image_subset) (affineDim_sumProd_le _ _)

/-- Points of the closure of the incidence still carry an adapted frame. -/
theorem zclosure_partnerIncidence_frame [IsAlgClosed K] {N : Matrix (Fin n) (Fin n) K}
    {v : ((Fin n × Fin n) ⊕ Unit) ⊕ (Fin n × Fin n) → K}
    (hv : v ∈ zclosure (partnerIncidence N)) : incFrame v ∈ frameChart N := by
  have hcl := zclosure_preimage (K := K)
    (f := fun w : ((Fin n × Fin n) ⊕ Unit) ⊕ (Fin n × Fin n) → K => fun i => w (Sum.inl i))
    isPolyMap_restrict_inl (zclosure_frameChart N)
  have hsub : partnerIncidence N ⊆
      (fun w : ((Fin n × Fin n) ⊕ Unit) ⊕ (Fin n × Fin n) → K => fun i => w (Sum.inl i)) ⁻¹'
        frameChart N := by
    rintro w ⟨hf, -, -⟩
    exact hf
  have hmem : v ∈ (fun w : ((Fin n × Fin n) ⊕ Unit) ⊕ (Fin n × Fin n) → K =>
      fun i => w (Sum.inl i)) ⁻¹' frameChart N := by
    rw [← hcl]
    exact zclosure_mono hsub hv
  exact hmem

/-! ### The Springer bound -/

theorem cOf_le_sq {N : Matrix (Fin n) (Fin n) K} (hN : IsNilpotent N) : cOf N ≤ n * n := by
  have h := centralizerCount_le_diagramSize_sq (jordanColumns (Matrix.toLinAlgEquiv' N) n)
  rw [diagramSize_jordanColumns _ n (pow_card_eq_zero_of_isNilpotent hN),
    Module.finrank_fin_fun] at h
  rw [cOf_eq_centralizerCount]
  calc centralizerCount (jordanColumns (Matrix.toLinAlgEquiv' N) n) ≤ n ^ 2 := h
    _ = n * n := sq n

theorem nOf_le_choose_two {N : Matrix (Fin n) (Fin n) K} (hN : IsNilpotent N) :
    nOf N ≤ n.choose 2 := by
  have hc := cOf_eq_add_two_mul_nOf hN
  have hcle := cOf_le_sq hN
  have h2 := two_mul_choose_two_add n
  omega

/-- **`prop:springer-bound`, affine form.**  Assuming the strata bound
`dim (𝔫 ∩ O_N) ≤ C(n,2) − n(λ)`
(`lem:springer-dim`, first half), the triangularizable partners of `N` inside
its own orbit have dimension at most `C(n,2)`. -/
theorem affineDim_triangularizablePartner_le {K : Type} [Field K] [IsAlgClosed K] {n : ℕ}
    {N : Matrix (Fin n) (Fin n) K} (hN : IsNilpotent N)
    (hstrata : affineDim (nilOrbit N) ≤ (((n.choose 2 - nOf N : ℕ) : ℕ∞) : WithBot ℕ∞)) :
    affineDim (matCoords '' (triangularizablePartnerLocus n N ∩ conjOrbit N)) ≤
      (((n.choose 2 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
  have hc := cOf_eq_add_two_mul_nOf hN
  have hnOf := nOf_le_choose_two hN
  have h2 := two_mul_choose_two_add n
  have hkey : (n.choose 2 - nOf N) + cOf N + (n.choose 2 - nOf N) =
      n.choose 2 + (n.choose 2 + n) := by omega
  -- the Borel fibration, on the closure of the incidence
  have hP : (MvPolynomial.vanishingIdeal K (GLPair.borel K n).pts).IsPrime :=
    isPrime_vanishingIdeal_borel_pts
  have hstab : ∀ a ∈ (GLPair.borel K n).pts, ∀ y ∈ zclosure (partnerIncidence N),
      (borelIncAction K n).actPt a y ∈ zclosure (partnerIncidence N) := fun a ha y hy =>
    ((borelIncAction K n).toPolyAction hP).act_zclosure_subset
      (fun a' ha' v hv => actPt_mem_partnerIncidence ha' hv) ha ⟨y, hy, rfl⟩
  have horb : ∀ y ∈ zclosure (partnerIncidence N),
      ((((n.choose 2 + n : ℕ)) : ℕ∞) : WithBot ℕ∞) ≤
        affineDim {z | ∃ a ∈ (GLPair.borel K n).pts, (borelIncAction K n).actPt a y = z} :=
    fun y hy => affineDim_orbit_ge (zclosure_partnerIncidence_frame hy)
  have hlow := (GLPair.borel K n).affineDim_image_add_le_of_orbit_le hP (borelIncAction K n)
    borelIncAction_J isPolyMap_partnerMap
    (Y := zclosure (partnerIncidence N))
    (IsLocClosed.of_zclosure (zclosure_zclosure _)).isConstructible
    hstab (fun a _ y _ => partnerMap_borelIncActPt a y) horb
  have h1 : affineDim (matCoords '' (triangularizablePartnerLocus n N ∩ conjOrbit N)) +
      ((((n.choose 2 + n : ℕ)) : ℕ∞) : WithBot ℕ∞) ≤ affineDim (partnerIncidence N) := by
    rw [← partnerMap_image N, ← affineDim_zclosure (partnerIncidence N)]
    exact le_trans (add_le_add (affineDim_mono (Set.image_mono (subset_zclosure _))) le_rfl) hlow
  have hfc : affineDim (frameChart N) ≤
      affineDim (nilOrbit N) + ((cOf N : ℕ∞) : WithBot ℕ∞) := affineDim_frameChart_le hN
  have harith : (((n.choose 2 - nOf N : ℕ) : ℕ∞) : WithBot ℕ∞) + ((cOf N : ℕ∞) : WithBot ℕ∞) +
      (((n.choose 2 - nOf N : ℕ) : ℕ∞) : WithBot ℕ∞) =
      (((n.choose 2 : ℕ) : ℕ∞) : WithBot ℕ∞) + (((n.choose 2 + n : ℕ) : ℕ∞) : WithBot ℕ∞) := by
    have e1 : (((n.choose 2 - nOf N : ℕ) : ℕ∞) : WithBot ℕ∞) + ((cOf N : ℕ∞) : WithBot ℕ∞) +
        (((n.choose 2 - nOf N : ℕ) : ℕ∞) : WithBot ℕ∞) =
        (((((n.choose 2 - nOf N) + cOf N + (n.choose 2 - nOf N) : ℕ)) : ℕ∞) : WithBot ℕ∞) := by
      push_cast
      ring
    have e2 : (((n.choose 2 : ℕ) : ℕ∞) : WithBot ℕ∞) +
        (((n.choose 2 + n : ℕ) : ℕ∞) : WithBot ℕ∞) =
        (((((n.choose 2) + (n.choose 2 + n) : ℕ)) : ℕ∞) : WithBot ℕ∞) := by
      push_cast
      ring
    rw [e1, e2, hkey]
  have h3 : affineDim (matCoords '' (triangularizablePartnerLocus n N ∩ conjOrbit N)) +
      (((n.choose 2 + n : ℕ) : ℕ∞) : WithBot ℕ∞) ≤
      (((n.choose 2 : ℕ) : ℕ∞) : WithBot ℕ∞) +
        (((n.choose 2 + n : ℕ) : ℕ∞) : WithBot ℕ∞) := by
    refine le_trans h1 (le_trans affineDim_partnerIncidence_le ?_)
    refine le_trans (add_le_add (le_trans hfc (add_le_add hstrata le_rfl)) hstrata) ?_
    exact le_of_eq harith
  exact (ENat.WithBot.add_le_add_natCast_right_iff (c := n.choose 2 + n)).mp (by exact_mod_cast h3)

end Springer

/-! ## Extension of scalars to `Kbar` -/

section Statement

variable (p r n : ℕ) [Fact p.Prime]

end Statement

end Height.Chain
