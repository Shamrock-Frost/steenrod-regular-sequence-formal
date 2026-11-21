import Height.Geometry.Coordinates
import Height.Geometry.Dimension.Components
import Height.Geometry.Dimension.FibreUpper
import Height.Geometry.Dimension.FibreGeneric
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Homogeneous fibrations: dimension is additive

Everything is in the affine language of
`Height/Geometry` over an algebraically closed field `K`: `affineDim`
is the Krull dimension of the coordinate ring of the Zariski closure.

## The packaging of a "polynomial action of an irreducible group"

`Height.Geometry.PolyAction K γ ι` is a structure whose fields are, verbatim:
```
G : Set (γ → K)
S : Set (ι → K)
act : (γ → K) → (ι → K) → (ι → K)
act_poly : ∃ F : ι → MvPolynomial (γ ⊕ ι) K,
  ∀ g y i, act g y i = MvPolynomial.aeval (Sum.elim g y) (F i)
irreducible : (MvPolynomial.vanishingIdeal K G).IsPrime
one : γ → K
one_mem : one ∈ G
act_mem : ∀ g ∈ G, ∀ y ∈ S, act g y ∈ S
act_one : ∀ y ∈ S, act one y = y
mul : (γ → K) → (γ → K) → (γ → K)
mul_mem : ∀ g ∈ G, ∀ h ∈ G, mul g h ∈ G
act_mul : ∀ g ∈ G, ∀ h ∈ G, ∀ y ∈ S, act (mul g h) y = act g (act h y)
inv : (γ → K) → (γ → K)
inv_mem : ∀ g ∈ G, inv g ∈ G
act_inv_left : ∀ g ∈ G, ∀ y ∈ S, act (inv g) (act g y) = y
act_inv_right : ∀ g ∈ G, ∀ y ∈ S, act g (act (inv g) y) = y
```

`S` is the space actually acted on: the action of an affine group scheme on a closed
subscheme is polynomial only modulo the ideal of the subscheme, so the laws hold at the
points of the subscheme and nowhere else (`AffineChart.toPolyAction` in
`Geometry/Interface.lean` takes `S := cX.pts`).  The consumers in `Chain/` take
`S := Set.univ`.  Every statement below that uses a law therefore carries `y ∈ S`,
`C ⊆ S` or `Y ⊆ S`.

The group sits inside the affine space `(γ → K)`; for a matrix group take
`γ := Fin n × Fin n` and coordinates `fun M ij => M ij.1 ij.2`, so that `mul`,
`inv` and the action are polynomial in the entries (`inv` through the adjugate,
which is polynomial once the determinant is invertible — the fields only ask for
the inverse laws on `G`).  "Irreducible" is spelled out as
`(MvPolynomial.vanishingIdeal K G).IsPrime`.

## Where the fibration counts are

The orbit and transitive fibration counts are stated once, for a constructible
source, in `LocClosed.lean`; `IsLocClosed.of_zclosure` and
`IsLocClosed.isConstructible` specialise them to a Zariski closed or locally
closed source.  The generic fibre bound they use is
`exists_generic_fibre_dense`, also in `LocClosed.lean`.

This file has the packaging (`PolyAction`, orbits, stability) that the
constructible forms take; the `K`-point face of the counts for a presented
group is `Geometry/Group.lean`'s
`GroupPresentation.affineDim_of_orbit_fibration`, which is what `Chain/Untwist`
and `Chain/Hyps` call.
-/

universe u v

open MvPolynomial

namespace Height.Geometry

variable {K : Type u} [Field K] {γ ι κ : Type v}

/-! ### Polynomial actions of irreducible groups -/

/-- A polynomial action of an irreducible group `G ⊆ (γ → K)` on the affine
space `(ι → K)`.  See the module docstring for the intended matrix instance. -/
structure PolyAction (K : Type u) [Field K] (γ ι : Type v) where
  /-- The group, as a subset of the affine space of its coordinates. -/
  G : Set (γ → K)
  /-- The space acted on.  The laws below hold at its points only. -/
  S : Set (ι → K)
  /-- The action. -/
  act : (γ → K) → (ι → K) → (ι → K)
  /-- The action is polynomial in the group and space coordinates jointly. -/
  act_poly : ∃ F : ι → MvPolynomial (γ ⊕ ι) K,
    ∀ g y i, act g y i = MvPolynomial.aeval (Sum.elim g y) (F i)
  /-- The group is irreducible. -/
  irreducible : (MvPolynomial.vanishingIdeal K G).IsPrime
  /-- The identity element. -/
  one : γ → K
  one_mem : one ∈ G
  act_mem : ∀ g ∈ G, ∀ y ∈ S, act g y ∈ S
  act_one : ∀ y ∈ S, act one y = y
  /-- The group law. -/
  mul : (γ → K) → (γ → K) → (γ → K)
  mul_mem : ∀ g ∈ G, ∀ h ∈ G, mul g h ∈ G
  act_mul : ∀ g ∈ G, ∀ h ∈ G, ∀ y ∈ S, act (mul g h) y = act g (act h y)
  /-- Inversion. -/
  inv : (γ → K) → (γ → K)
  inv_mem : ∀ g ∈ G, inv g ∈ G
  act_inv_left : ∀ g ∈ G, ∀ y ∈ S, act (inv g) (act g y) = y
  act_inv_right : ∀ g ∈ G, ∀ y ∈ S, act g (act (inv g) y) = y

namespace PolyAction

variable (A : PolyAction K γ ι)

/-- The orbit of a point. -/
def orbit (y : ι → K) : Set (ι → K) := {z | ∃ g ∈ A.G, A.act g y = z}

theorem mem_orbit_self {y : ι → K} (hy : y ∈ A.S) : y ∈ A.orbit y :=
  ⟨A.one, A.one_mem, A.act_one y hy⟩

theorem act_mem_orbit {g : γ → K} (hg : g ∈ A.G) (y : ι → K) : A.act g y ∈ A.orbit y :=
  ⟨g, hg, rfl⟩

/-- Orbits of points in the same orbit agree. -/
theorem orbit_eq_of_mem {y z : ι → K} (hy : y ∈ A.S) (h : z ∈ A.orbit y) :
    A.orbit z = A.orbit y := by
  obtain ⟨g, hg, rfl⟩ := h
  refine le_antisymm ?_ ?_
  · rintro _ ⟨h, hh, rfl⟩
    exact ⟨A.mul h g, A.mul_mem h hh g hg, A.act_mul h hh g hg y hy⟩
  · rintro _ ⟨h, hh, rfl⟩
    refine ⟨A.mul h (A.inv g), A.mul_mem h hh _ (A.inv_mem g hg), ?_⟩
    rw [A.act_mul h hh _ (A.inv_mem g hg) _ (A.act_mem g hg y hy), A.act_inv_left g hg y hy]

/-- Each `act g` is a polynomial map. -/
theorem act_isPolyMap (g : γ → K) : IsPolyMap (A.act g) := by
  obtain ⟨F, hF⟩ := A.act_poly
  exact ⟨fun i => subLeft g (F i), fun y i => by rw [aeval_subLeft]; exact hF g y i⟩

/-- The map `(g, y) ↦ act g y` on the product affine space. -/
def sweepMap (z : γ ⊕ ι → K) : ι → K :=
  A.act (fun a => z (Sum.inl a)) (fun i => z (Sum.inr i))

theorem sweepMap_isPolyMap : IsPolyMap A.sweepMap := by
  obtain ⟨F, hF⟩ := A.act_poly
  refine ⟨F, fun z i => ?_⟩
  rw [sweepMap, hF, elim_comp_inl_inr]

/-- The sweep `G · C` of a subset by the group. -/
def sweep (C : Set (ι → K)) : Set (ι → K) := {z | ∃ g ∈ A.G, ∃ y ∈ C, A.act g y = z}

theorem sweep_eq_image (C : Set (ι → K)) : A.sweep C = A.sweepMap '' sumProd A.G C := by
  ext z
  constructor
  · rintro ⟨g, hg, y, hy, rfl⟩
    exact ⟨Sum.elim g y, elim_mem_sumProd hg hy, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨_, hw.1, _, hw.2, rfl⟩

theorem subset_sweep {C : Set (ι → K)} (hC : C ⊆ A.S) : C ⊆ A.sweep C :=
  fun y hy => ⟨A.one, A.one_mem, y, hy, A.act_one y (hC hy)⟩

/-- The sweep of an irreducible set is irreducible. -/
theorem irreducible_sweep {C : Set (ι → K)}
    (hC : (MvPolynomial.vanishingIdeal K C).IsPrime) :
    (MvPolynomial.vanishingIdeal K (A.sweep C)).IsPrime := by
  rw [A.sweep_eq_image]
  exact irreducible_image A.sweepMap_isPolyMap (irreducible_prod A.irreducible hC)

/-- If `Y` is stable then so is its Zariski closure. -/
theorem act_zclosure_subset {Y : Set (ι → K)} (hY : ∀ g ∈ A.G, ∀ y ∈ Y, A.act g y ∈ Y)
    {g : γ → K} (hg : g ∈ A.G) : A.act g '' zclosure Y ⊆ zclosure Y := by
  refine (image_zclosure_subset (A.act_isPolyMap g) Y).trans ?_
  have : A.act g '' Y ⊆ Y := by rintro _ ⟨y, hy, rfl⟩; exact hY g hg y hy
  simpa using zclosure_mono this

end PolyAction

/-! ### Zero loci and preimages -/

/-! ### The scheme-theoretic fibre of a polynomial map -/

/-- The zero locus of a sum of ideals is the intersection of the zero loci. -/
theorem zeroLocus_sup (I J : Ideal (MvPolynomial ι K)) :
    MvPolynomial.zeroLocus K (I ⊔ J) =
      MvPolynomial.zeroLocus K I ∩ MvPolynomial.zeroLocus K J := by
  refine le_antisymm (fun x hx => ⟨MvPolynomial.zeroLocus_anti_mono le_sup_left hx,
    MvPolynomial.zeroLocus_anti_mono le_sup_right hx⟩) ?_
  rintro x ⟨hxI, hxJ⟩ p hp
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hp
  rw [map_add, hxI a ha, hxJ b hb, add_zero]

/-- The zero locus of the extension of an ideal along a polynomial map is the
preimage of its zero locus. -/
theorem zeroLocus_map_aeval {f : (ι → K) → (κ → K)} {F : κ → MvPolynomial ι K}
    (hF : ∀ y j, f y j = aeval y (F j)) (J : Ideal (MvPolynomial κ K)) :
    MvPolynomial.zeroLocus K
        (J.map (aeval F : MvPolynomial κ K →ₐ[K] MvPolynomial ι K).toRingHom) =
      f ⁻¹' MvPolynomial.zeroLocus K J := by
  ext y
  constructor
  · intro hy g hg
    rw [aeval_polyMap hF]
    exact hy _ (Ideal.mem_map_of_mem _ hg)
  · intro hy p hp
    have hle : J.map (aeval F : MvPolynomial κ K →ₐ[K] MvPolynomial ι K).toRingHom ≤
        Ideal.comap (aeval y : MvPolynomial ι K →ₐ[K] K) ⊥ := by
      rw [Ideal.map_le_iff_le_comap]
      intro g hg
      simp only [Ideal.mem_comap, Submodule.mem_bot]
      show aeval y (aeval F g) = 0
      rw [← aeval_polyMap hF]
      exact hy g hg
    simpa using hle hp

/-- The Krull dimension of the scheme-theoretic fibre is the dimension of the
set-theoretic fibre. -/
theorem ringKrullDim_fibre [IsAlgClosed K] [Finite ι] [Finite κ]
    {f : (ι → K) → (κ → K)} {F : κ → MvPolynomial ι K} (hF : ∀ y j, f y j = aeval y (F j))
    (Jy : Ideal (MvPolynomial ι K)) (x : κ → K) :
    ringKrullDim (MvPolynomial ι K ⧸
        (Jy ⊔ (MvPolynomial.vanishingIdeal K ({x} : Set (κ → K))).map
          (aeval F : MvPolynomial κ K →ₐ[K] MvPolynomial ι K).toRingHom))
      = affineDim (MvPolynomial.zeroLocus K Jy ∩ f ⁻¹' {x}) := by
  rw [← affineDim_zeroLocus, zeroLocus_sup, zeroLocus_map_aeval hF,
    show MvPolynomial.zeroLocus K (MvPolynomial.vanishingIdeal K ({x} : Set (κ → K))) = {x} from
      zclosure_singleton x]

/-! ### The fibre-dimension upper bound, in the affine language -/

/-- **The fibre-dimension upper bound in affine form.**  If every fibre of a
polynomial map on a Zariski closed set `Y` has dimension at most `c`, then
`dim Y ≤ dim (f '' Y) + c`. -/
theorem affineDim_le_add_fibre [IsAlgClosed K] [Finite ι] [Finite κ]
    {f : (ι → K) → (κ → K)} (hf : IsPolyMap f) (Y : Set (ι → K)) (hYcl : zclosure Y = Y)
    (c : WithBot ℕ∞) (hc : ∀ x : κ → K, affineDim (Y ∩ f ⁻¹' {x}) ≤ c) :
    affineDim Y ≤ affineDim (f '' Y) + c := by
  obtain ⟨F, hF⟩ := hf
  set IY : Ideal (MvPolynomial ι K) := MvPolynomial.vanishingIdeal K Y with hIY
  set φ : MvPolynomial κ K →ₐ[K] (MvPolynomial ι K ⧸ IY) :=
    (Ideal.Quotient.mkₐ K IY).comp (aeval F) with hφ
  have hker : RingHom.ker φ = MvPolynomial.vanishingIdeal K (f '' Y) := by
    ext g
    rw [RingHom.mem_ker, vanishingIdeal_image hF]
    show Ideal.Quotient.mk IY (aeval F g) = 0 ↔ _
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Iff.rfl
  have hd2 := ringKrullDim_le_of_finiteType K (MvPolynomial κ K) (MvPolynomial ι K ⧸ IY) φ
  have hsup : (⨆ m : {m : Ideal (MvPolynomial κ K) // m.IsMaximal},
      ringKrullDim ((MvPolynomial ι K ⧸ IY) ⧸ (m.1.map φ.toRingHom))) ≤ c := by
    refine iSup_le fun m => ?_
    obtain ⟨x, hx⟩ := MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton.1 m.2
    have hcomp : φ.toRingHom =
        (Ideal.Quotient.mk IY).comp
          (aeval F : MvPolynomial κ K →ₐ[K] MvPolynomial ι K).toRingHom := by
      exact RingHom.ext fun g => rfl
    have hmap : m.1.map φ.toRingHom =
        ((MvPolynomial.vanishingIdeal K ({x} : Set (κ → K))).map
          (aeval F : MvPolynomial κ K →ₐ[K] MvPolynomial ι K).toRingHom).map
          (Ideal.Quotient.mk IY) := by
      rw [hx, hcomp, Ideal.map_map]
    rw [hmap, ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotSup _ _),
      ringKrullDim_fibre hF]
    show affineDim (zclosure Y ∩ f ⁻¹' {x}) ≤ c
    rw [hYcl]
    exact hc x
  calc affineDim Y = ringKrullDim (MvPolynomial ι K ⧸ IY) := rfl
    _ ≤ ringKrullDim (MvPolynomial κ K ⧸ RingHom.ker φ) +
          ⨆ m : {m : Ideal (MvPolynomial κ K) // m.IsMaximal},
            ringKrullDim ((MvPolynomial ι K ⧸ IY) ⧸ (m.1.map φ.toRingHom)) := hd2
    _ ≤ affineDim (f '' Y) + c := add_le_add (le_of_eq (by rw [hker]; rfl)) hsup

/-- A finite affine set has dimension at most `0`. -/
theorem affineDim_le_zero_of_finite {S : Set (ι → K)} (hS : S.Finite) :
    affineDim S ≤ 0 := by
  have _ : Finite S := hS
  have hcov : S = ⋃ z : S, ({(z : ι → K)} : Set (ι → K)) := by
    ext y; simp
  rw [hcov, affineDim_iUnion]
  refine iSup_le fun z => ?_
  have _ : (MvPolynomial.vanishingIdeal K ({(z : ι → K)} : Set (ι → K))).IsMaximal :=
    inferInstance
  have hfield : IsField (MvPolynomial ι K ⧸
      MvPolynomial.vanishingIdeal K ({(z : ι → K)} : Set (ι → K))) :=
    @Field.toIsField _ (Ideal.Quotient.field _)
  have h0 : affineDim ({(z : ι → K)} : Set (ι → K)) = 0 := by
    show ringKrullDim (MvPolynomial ι K ⧸
      MvPolynomial.vanishingIdeal K ({(z : ι → K)} : Set (ι → K))) = 0
    exact ringKrullDim_eq_zero_of_isField hfield
  exact le_of_eq h0

/-- A polynomial map with finite fibres does not change the
dimension. -/
theorem affineDim_of_finite_fibres [IsAlgClosed K] [Finite ι] [Finite κ]
    {f : (ι → K) → (κ → K)} (hf : IsPolyMap f) (Y : Set (ι → K)) (X : Set (κ → K))
    (hYcl : zclosure Y = Y) (hXY : f '' Y = X)
    (hfin : ∀ x ∈ X, (Y ∩ f ⁻¹' {x}).Finite) :
    affineDim Y = affineDim X := by
  refine le_antisymm ?_ ?_
  · have h := affineDim_le_add_fibre hf Y hYcl 0 ?_
    · rwa [hXY, add_zero] at h
    · intro x
      by_cases hx : x ∈ X
      · exact affineDim_le_zero_of_finite (hfin x hx)
      · have hempty : Y ∩ f ⁻¹' {x} = ∅ := by
          refine Set.eq_empty_iff_forall_notMem.2 fun y hy => ?_
          exact hx (hXY ▸ ⟨y, hy.1, hy.2⟩)
        rw [hempty, affineDim_empty]
        exact bot_le
  · rw [← hXY]
    exact affineDim_image_le hf Y

/-! ### Matrices: cosets and the general linear group

The corollaries the consumers cite.  Matrices become points of affine space
through `matCoords`. -/

section Matrices

variable {μ : Type v}

variable [Fintype μ]

/-- Left multiplication by a fixed matrix, in entry coordinates. -/
def leftMul (g : Matrix μ μ K) (x : μ × μ → K) : μ × μ → K :=
  matCoords (g * matCoords.symm x)

theorem leftMul_matCoords (g M : Matrix μ μ K) :
    leftMul g (matCoords M) = matCoords (g * M) := rfl

theorem isPolyMap_leftMul (g : Matrix μ μ K) : IsPolyMap (leftMul g) := by
  refine ⟨fun ij => ∑ k, C (g ij.1 k) * X (k, ij.2), fun x ij => ?_⟩
  show (g * matCoords.symm x) ij.1 ij.2 = _
  rw [Matrix.mul_apply, map_sum]
  simp

/-- Left multiplication by an invertible matrix preserves dimension. -/
theorem affineDim_leftMul_image [IsAlgClosed K] [DecidableEq μ]
    {g : Matrix μ μ K} (hg : IsUnit g.det) (S : Set (μ × μ → K)) :
    affineDim (leftMul g '' S) = affineDim S := by
  refine affineDim_image_eq (isPolyMap_leftMul g) (isPolyMap_leftMul g⁻¹) (fun x _ => ?_)
  show matCoords (g⁻¹ * matCoords.symm (matCoords (g * matCoords.symm x))) = x
  rw [matCoords.symm_apply_apply, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul g hg, Matrix.one_mul,
    matCoords.apply_symm_apply]

/-- **Corollary: cosets.**  A left translate of a set of matrices by an
invertible matrix has the same dimension. -/
theorem affineDim_leftCoset [IsAlgClosed K] [DecidableEq μ]
    {g : Matrix μ μ K} (hg : IsUnit g.det) (H : Set (Matrix μ μ K)) :
    affineDim (matCoords '' ((fun h => g * h) '' H)) =
      affineDim (matCoords '' H) := by
  have hfun : (fun h : Matrix μ μ K => matCoords (g * h)) =
      fun h : Matrix μ μ K => leftMul g (matCoords h) :=
    _root_.funext fun h => (leftMul_matCoords g h).symm
  have himg : matCoords '' ((fun h => g * h) '' H) = leftMul g '' (matCoords '' H) := by
    rw [Set.image_image, Set.image_image, hfun]
  rw [himg, affineDim_leftMul_image hg]

/-- The determinant, as a polynomial in the matrix entries. -/
noncomputable def detPoly (μ : Type v) [Fintype μ] [DecidableEq μ] : MvPolynomial (μ × μ) K :=
  (Matrix.of fun i j => (X (i, j) : MvPolynomial (μ × μ) K)).det

theorem aeval_detPoly [DecidableEq μ] (x : μ × μ → K) :
    aeval x (detPoly (K := K) μ) = (matCoords.symm x).det := by
  show (aeval x : MvPolynomial (μ × μ) K →ₐ[K] K).toRingHom
      (Matrix.det (Matrix.of fun i j => (X (i, j) : MvPolynomial (μ × μ) K))) = _
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp

theorem detPoly_ne_zero [DecidableEq μ] [Nonempty μ] : detPoly (K := K) μ ≠ 0 := by
  intro h
  have h1 : aeval (matCoords (1 : Matrix μ μ K)) (detPoly (K := K) μ) = 1 := by
    rw [aeval_detPoly, matCoords.symm_apply_apply, Matrix.det_one]
  rw [h, map_zero] at h1
  exact zero_ne_one h1

/-- **Corollary: the general linear group is dense in matrix space.** -/
theorem vanishingIdeal_generalLinear [IsAlgClosed K] [DecidableEq μ] :
    MvPolynomial.vanishingIdeal K (matCoords '' {M : Matrix μ μ K | IsUnit M.det}) = ⊥ := by
  refine le_antisymm (fun p hp => ?_) bot_le
  rcases isEmpty_or_nonempty μ with hμ | hμ
  · -- With no indices there is only one point, and it is invertible.
    have hone : matCoords (1 : Matrix μ μ K) ∈
        matCoords '' {M : Matrix μ μ K | IsUnit M.det} := ⟨1, by simp, rfl⟩
    refine Ideal.mem_bot.2 (MvPolynomial.funext fun x => ?_)
    show aeval x p = aeval x (0 : MvPolynomial (μ × μ) K)
    have hx : x = matCoords (1 : Matrix μ μ K) :=
      _root_.funext fun ij => (hμ.false ij.1).elim
    rw [map_zero, hx]
    exact hp _ hone
  have hmul : p * detPoly (K := K) μ = 0 := by
    refine MvPolynomial.funext fun x => ?_
    show aeval x (p * detPoly (K := K) μ) = aeval x (0 : MvPolynomial (μ × μ) K)
    rw [map_zero, map_mul]
    by_cases hx : IsUnit (matCoords.symm x).det
    · have hmem : x ∈ matCoords '' {M : Matrix μ μ K | IsUnit M.det} :=
        ⟨matCoords.symm x, hx, matCoords.apply_symm_apply x⟩
      rw [hp x hmem, zero_mul]
    · have hdet : (matCoords.symm x).det = 0 := by
        rcases eq_or_ne (matCoords.symm x).det 0 with h | h
        · exact h
        · exact absurd (isUnit_iff_ne_zero.2 h) hx
      rw [aeval_detPoly, hdet, mul_zero]
  rcases mul_eq_zero.1 hmul with h | h
  · exact Ideal.mem_bot.2 h
  · exact absurd h detPoly_ne_zero

/-- **Corollary: `dim GL_μ = |μ|²`.** -/
theorem affineDim_generalLinear [IsAlgClosed K] [DecidableEq μ] :
    affineDim (matCoords '' {M : Matrix μ μ K | IsUnit M.det}) =
      ((Fintype.card μ * Fintype.card μ : ℕ) : WithBot ℕ∞) := by
  show ringKrullDim (MvPolynomial (μ × μ) K ⧸
    MvPolynomial.vanishingIdeal K (matCoords '' {M : Matrix μ μ K | IsUnit M.det})) = _
  rw [vanishingIdeal_generalLinear,
    ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot (R := MvPolynomial (μ × μ) K)),
    MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field K]
  simp [Nat.card_eq_fintype_card]

end Matrices

end Height.Geometry
