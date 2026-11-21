import Height.Chain.Counts
import Height.Steenrod.Lang.Counting
import Height.Geometry.Dimension.Homogeneous
import Height.Toolbox.CentralizerDim
import Height.Toolbox.KrullArith
import Height.Geometry.GroupExamples
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# The set-theoretic half of `prop:untwist`

`prop:untwist` compares `dim (V(J) ∩ O_N)` with `dim (𝒞_N ∩ O_N)` through the
set

```
T = { g ∈ GL_n(Kbar) : Lang(g) N Lang(g)⁻¹ ∈ 𝒞_N },
```

which surjects onto both: by `π(g) = g N g⁻¹` onto `V(J) ∩ O_N`, and by
`σ(g) = Lang(g) N Lang(g)⁻¹` onto `𝒞_N ∩ O_N`.  Those two surjections are the
content of this file (`image_conjMap_pairTransporter`,
`image_conjMap_pairPartner`);
they are exactly `eq:transport` plus Lang's theorem, and they need no geometry.

The dimension comparison — both `π` and `σ` drop the dimension by exactly
`dim Z(N)`, whence

```
dim (V(J) ∩ O_N) = dim T − dim Z(N) = dim (𝒞_N ∩ O_N),
```

is proved in the second half of this file
(`Height.Chain.untwist`).  It does not use the sets above: the fibration lemmas
of `Geometry/Dimension/Homogeneous.lean` need a Zariski **closed** source, and
`T ⊆ GL_n` is only locally closed in matrix space, so `T` is replaced by its
copy in the closed *pair* model `glPair = {(g, h) : g h = h g = 1}` of `GL_n`,
where `g⁻¹` is a coordinate and conjugation, the Lang map and the right action
of `Z(N)` are all polynomial.  The two surjections above reappear there as
`image_conjMap_pairTransporter` and (through `transport_pair` and
`matrixLang_surjective`) the image half of `affineDim_pairTransporter`.
-/

namespace Height.Chain

open QSteenrod Height.Steenrod

variable (p r n : ℕ) [Fact p.Prime] [NeZero r]

end Height.Chain

/-!
## The dimension comparison

`prop:untwist` compares two dimensions through the transporter `T`.  The
fibration lemmas of `Geometry/Dimension/Homogeneous.lean` need a Zariski
**closed** source, and `T ⊆ GL_n` is only locally closed inside matrix space.
The fix used here is to replace `GL_n` by its graph

```
glPair = { (g, h) : g * h = h * g = 1 } ⊆ Mat_n × Mat_n,
```

which *is* Zariski closed (it is cut out by polynomial equations) and on which
both `g` and `g⁻¹` are coordinates, so that conjugation, the Lang map and the
right action of the centraliser group are all polynomial.  All three sets that
carry a dimension below — the transporter, the partner transporter and the
centraliser group — are closed subsets of this pair space, and the fibres of
the two projections are exactly the cosets they are in `GL_n`.
-/

namespace Height.Chain.Untwisting

open MvPolynomial Height.Geometry Height.Steenrod

universe u

/-! ### Zariski closed subsets of affine space -/

end Height.Chain.Untwisting

namespace Height.Chain.Untwisting

open MvPolynomial Height.Geometry Height.Steenrod

universe u

/-! ### The invertible pairs -/

section GlPair

variable {K : Type u} [Field K] {n : ℕ}

/-- The graph of inversion: pairs `(g, h)` with `g h = h g = 1`.  This is the
Zariski **closed** model of `GL_n` used throughout. -/
def glPair (K : Type u) [Field K] (n : ℕ) : Set (PairIndex (Fin n) → K) :=
  {x | fstMat x * sndMat x = 1 ∧ sndMat x * fstMat x = 1}

theorem mem_glPair {x : PairIndex (Fin n) → K} :
    x ∈ glPair K n ↔ fstMat x * sndMat x = 1 ∧ sndMat x * fstMat x = 1 := Iff.rfl

/-- The unit of the matrix ring attached to an invertible pair. -/
def pairUnit {x : PairIndex (Fin n) → K} (hx : x ∈ glPair K n) : (Matrix (Fin n) (Fin n) K)ˣ :=
  ⟨fstMat x, sndMat x, hx.1, hx.2⟩

/-- The pair attached to a unit lies in `glPair`. -/
theorem pairCoords_unit_mem (g : (Matrix (Fin n) (Fin n) K)ˣ) :
    pairCoords ((g : Matrix (Fin n) (Fin n) K), ((g⁻¹ : (Matrix (Fin n) (Fin n) K)ˣ) :
      Matrix (Fin n) (Fin n) K)) ∈ glPair K n := by
  exact ⟨g.mul_inv, g.inv_mul⟩

/-- Conjugation of a fixed matrix by an invertible pair. -/
def conjMap (A : Matrix (Fin n) (Fin n) K) (x : PairIndex (Fin n) → K) : Fin n × Fin n → K :=
  matCoords (fstMat x * A * sndMat x)

/-- The reversed conjugation, used only to cut out `glPair`. -/
def conjMapRev (A : Matrix (Fin n) (Fin n) K) (x : PairIndex (Fin n) → K) : Fin n × Fin n → K :=
  matCoords (sndMat x * A * fstMat x)

/-- The commutator of the first block with a fixed matrix. -/
def commMap (A : Matrix (Fin n) (Fin n) K) (x : PairIndex (Fin n) → K) : Fin n × Fin n → K :=
  matCoords (fstMat x * A - A * fstMat x)

theorem isPolyMap_conjMap (A : Matrix (Fin n) (Fin n) K) : IsPolyMap (conjMap A) :=
  isPolyMap_matMul (isPolyMap_matMul isPolyMap_fstMat (isPolyMap_matConst A)) isPolyMap_sndMat

theorem isPolyMap_conjMapRev (A : Matrix (Fin n) (Fin n) K) : IsPolyMap (conjMapRev A) :=
  isPolyMap_matMul (isPolyMap_matMul isPolyMap_sndMat (isPolyMap_matConst A)) isPolyMap_fstMat

theorem isPolyMap_commMap (A : Matrix (Fin n) (Fin n) K) : IsPolyMap (commMap A) :=
  isPolyMap_matSub (isPolyMap_matMul isPolyMap_fstMat (isPolyMap_matConst A))
    (isPolyMap_matMul (isPolyMap_matConst A) isPolyMap_fstMat)

/-- `glPair` is Zariski closed. -/
theorem zclosure_glPair : zclosure (glPair K n) = glPair K n := by
  have hset : glPair K n =
      (conjMap (1 : Matrix (Fin n) (Fin n) K) ⁻¹' {matCoords (1 : Matrix (Fin n) (Fin n) K)}) ∩
        (conjMapRev (1 : Matrix (Fin n) (Fin n) K) ⁻¹'
          {matCoords (1 : Matrix (Fin n) (Fin n) K)}) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, conjMap, conjMapRev, matCoords.injective.eq_iff, mem_glPair, Matrix.mul_one]
  rw [hset]
  exact zclosure_inter (zclosure_preimage (isPolyMap_conjMap _) (zclosure_singleton _))
    (zclosure_preimage (isPolyMap_conjMapRev _) (zclosure_singleton _))

end GlPair

end Height.Chain.Untwisting

namespace Height.Chain.Untwisting

open MvPolynomial Height.Geometry Height.Steenrod

universe u

/-! ### The pair model in the geometry API

The invertible pairs are the `K`-points of the closed subscheme of `𝔸(PairIndex (Fin n))`
cut out by `GLPair.glIdeal` (the pair model of `GL_n`, `Geometry/GroupExamples.lean`), and
the conjugation map is the polynomial map `conjPoly N`.  The group API ties the index
universe to that of `K`, so this section is at `K : Type` (where the chain runs). -/

section API

open AlgebraicGeometry Height.Geometry.GLPair

variable {K : Type} [Field K] {n : ℕ}

/-- The conjugation map `x ↦ g N h` as polynomials on the pair space. -/
noncomputable def conjPoly (N : Matrix (Fin n) (Fin n) K) :
    Fin n × Fin n → MvPolynomial (PairIndex (Fin n)) K :=
  fun ij => (gVar K n * N.map (C : K →+* MvPolynomial (PairIndex (Fin n)) K) * hVar K n) ij.1 ij.2

theorem aeval_conjPoly (N : Matrix (Fin n) (Fin n) K) (x : PairIndex (Fin n) → K) :
    (fun ij => aeval x (conjPoly N ij)) = conjMap N x := by
  funext ij
  simp only [conjPoly, conjMap, gVar, hVar, Matrix.mul_apply, Matrix.of_apply, Matrix.map_apply,
    map_sum, map_mul, aeval_X, aeval_C, matCoords_apply, fstMat_apply, sndMat_apply,
    Algebra.algebraMap_self, RingHom.id_apply]

end API

/-! ### The centraliser group in the pair model -/

section Cgroup

variable {K : Type u} [Field K] {n : ℕ}

/-- The centraliser group `Z(N)`, in the pair model of `GL_n`. -/
def cgroup (N : Matrix (Fin n) (Fin n) K) : Set (PairIndex (Fin n) → K) :=
  {x | x ∈ glPair K n ∧ fstMat x * N = N * fstMat x}

theorem mem_cgroup {N : Matrix (Fin n) (Fin n) K} {x : PairIndex (Fin n) → K} :
    x ∈ cgroup N ↔ x ∈ glPair K n ∧ fstMat x * N = N * fstMat x := Iff.rfl

theorem zclosure_cgroup (N : Matrix (Fin n) (Fin n) K) : zclosure (cgroup N) = cgroup N := by
  have hset : cgroup N =
      glPair K n ∩ (commMap N ⁻¹' {matCoords (0 : Matrix (Fin n) (Fin n) K)}) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, commMap, matCoords.injective.eq_iff, mem_cgroup, sub_eq_zero]
  rw [hset]
  exact zclosure_inter zclosure_glPair
    (zclosure_preimage (isPolyMap_commMap _) (zclosure_singleton _))

/-! ### The action -/

/-! ### The action is polynomial -/

end Cgroup

end Height.Chain.Untwisting

namespace Height.Chain.Untwisting

open MvPolynomial Height.Geometry Height.Steenrod

universe u

/-! ### The centraliser group is irreducible

`Z(N)` is the unit group of the centraliser *algebra* `L`, a linear subspace of
matrix space; in the pair model it is the "Rabinowitsch" set
`{(z, z⁻¹) : z ∈ L, det z ≠ 0}`.  Its vanishing ideal is computed as the kernel
of the evaluation of the pair coordinates at the generic point of `L` with the
determinant inverted, i.e. in the localisation `K[L][1/det]`, which is a domain.
-/

section Irreducible

variable {K : Type u} [Field K] {n : ℕ}

/-- The dimension of the centraliser algebra of `N`. -/
noncomputable def cdim (N : Matrix (Fin n) (Fin n) K) : ℕ :=
  Module.finrank K (Height.Toolbox.centralizer N)

/-- A basis of the centraliser algebra. -/
noncomputable def cbasis (N : Matrix (Fin n) (Fin n) K) :
    Module.Basis (Fin (cdim N)) K (Height.Toolbox.centralizer N) :=
  Module.finBasis K (Height.Toolbox.centralizer N)

/-- The generic centraliser element, at a point of `K^{c(N)}`. -/
noncomputable def cgen (N : Matrix (Fin n) (Fin n) K) (x : Fin (cdim N) → K) :
    Matrix (Fin n) (Fin n) K :=
  (((cbasis N).equivFun.symm x : Height.Toolbox.centralizer N) : Matrix (Fin n) (Fin n) K)

theorem cgen_mem (N : Matrix (Fin n) (Fin n) K) (x : Fin (cdim N) → K) :
    cgen N x ∈ Height.Toolbox.centralizer N := ((cbasis N).equivFun.symm x).2

theorem cgen_apply (N : Matrix (Fin n) (Fin n) K) (x : Fin (cdim N) → K) (i j : Fin n) :
    cgen N x i j = ∑ k, x k * ((cbasis N k : Height.Toolbox.centralizer N) :
      Matrix (Fin n) (Fin n) K) i j := by
  have h : ((cbasis N).equivFun.symm x : Height.Toolbox.centralizer N)
      = ∑ k, x k • cbasis N k := (cbasis N).equivFun_symm_apply x
  have h' : cgen N x = ∑ k, x k • ((cbasis N k : Height.Toolbox.centralizer N) :
      Matrix (Fin n) (Fin n) K) := by
    rw [cgen, h]
    push_cast
    rfl
  rw [h']
  simp [Matrix.sum_apply]

theorem cgen_injective (N : Matrix (Fin n) (Fin n) K) : Function.Injective (cgen N) := by
  intro x y hxy
  have h : ((cbasis N).equivFun.symm x : Height.Toolbox.centralizer N)
      = (cbasis N).equivFun.symm y := Subtype.ext hxy
  have h2 := congrArg (cbasis N).equivFun h
  rwa [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h2

theorem cgen_of_mem (N : Matrix (Fin n) (Fin n) K) {z : Matrix (Fin n) (Fin n) K}
    (hz : z ∈ Height.Toolbox.centralizer N) :
    cgen N ((cbasis N).equivFun ⟨z, hz⟩) = z := by
  show (((cbasis N).equivFun.symm ((cbasis N).equivFun ⟨z, hz⟩) :
    Height.Toolbox.centralizer N) : Matrix (Fin n) (Fin n) K) = z
  rw [LinearEquiv.symm_apply_apply]

theorem isPolyMap_cgen (N : Matrix (Fin n) (Fin n) K) :
    IsPolyMap fun x => matCoords (cgen N x) := by
  refine ⟨fun ij => ∑ k, MvPolynomial.C (((cbasis N k : Height.Toolbox.centralizer N) :
    Matrix (Fin n) (Fin n) K) ij.1 ij.2) * X k, fun x ij => ?_⟩
  show cgen N x ij.1 ij.2 = _
  rw [cgen_apply]
  simp [mul_comm]

/-- The generic centraliser element as a matrix over the coordinate ring. -/
noncomputable def cgenPoly (N : Matrix (Fin n) (Fin n) K) :
    Matrix (Fin n) (Fin n) (MvPolynomial (Fin (cdim N)) K) :=
  Matrix.of fun i j => ∑ k, MvPolynomial.C (((cbasis N k : Height.Toolbox.centralizer N) :
    Matrix (Fin n) (Fin n) K) i j) * X k

theorem aeval_cgenPoly (N : Matrix (Fin n) (Fin n) K) (x : Fin (cdim N) → K) (i j : Fin n) :
    MvPolynomial.aeval x (cgenPoly N i j) = cgen N x i j := by
  rw [cgen_apply]
  simp [cgenPoly, mul_comm]

theorem mapMatrix_cgenPoly (N : Matrix (Fin n) (Fin n) K) (x : Fin (cdim N) → K) :
    ((MvPolynomial.aeval x : MvPolynomial (Fin (cdim N)) K →ₐ[K] K).toRingHom).mapMatrix
        (cgenPoly N) = cgen N x := by
  ext i j
  exact aeval_cgenPoly N x i j

/-- The determinant of the generic centraliser element. -/
noncomputable def dpoly (N : Matrix (Fin n) (Fin n) K) : MvPolynomial (Fin (cdim N)) K :=
  (cgenPoly N).det

theorem aeval_dpoly (N : Matrix (Fin n) (Fin n) K) (x : Fin (cdim N) → K) :
    MvPolynomial.aeval x (dpoly N) = (cgen N x).det := by
  rw [dpoly, ← mapMatrix_cgenPoly N x]
  exact RingHom.map_det _ _

theorem aeval_adjugate_cgenPoly (N : Matrix (Fin n) (Fin n) K) (x : Fin (cdim N) → K)
    (i j : Fin n) :
    MvPolynomial.aeval x ((cgenPoly N).adjugate i j) = (cgen N x).adjugate i j := by
  have h := RingHom.map_adjugate
    ((MvPolynomial.aeval x : MvPolynomial (Fin (cdim N)) K →ₐ[K] K).toRingHom) (cgenPoly N)
  rw [mapMatrix_cgenPoly] at h
  exact congrFun (congrFun (congrArg (fun M : Matrix (Fin n) (Fin n) K => M) h) i) j

theorem one_mem_centralizer (N : Matrix (Fin n) (Fin n) K) :
    (1 : Matrix (Fin n) (Fin n) K) ∈ Height.Toolbox.centralizer N := by
  show (1 : Matrix (Fin n) (Fin n) K) * N = N * 1
  rw [one_mul, mul_one]

theorem dpoly_ne_zero (N : Matrix (Fin n) (Fin n) K) : dpoly N ≠ 0 := by
  intro h
  have hx := aeval_dpoly N ((cbasis N).equivFun ⟨1, one_mem_centralizer N⟩)
  rw [h, map_zero, cgen_of_mem N (one_mem_centralizer N), Matrix.det_one] at hx
  exact zero_ne_one hx

/-- The localisation of the coordinate ring of the centraliser at the
determinant. -/
noncomputable abbrev CLoc (N : Matrix (Fin n) (Fin n) K) : Type u :=
  Localization.Away (dpoly N)

/-- Evaluation of the pair coordinates at the generic invertible centraliser
element `(z, z⁻¹)`. -/
noncomputable def evLoc (N : Matrix (Fin n) (Fin n) K) :
    MvPolynomial (PairIndex (Fin n)) K →+* CLoc N :=
  MvPolynomial.eval₂Hom
    ((algebraMap (MvPolynomial (Fin (cdim N)) K) (CLoc N)).comp (MvPolynomial.C : K →+* _))
    (Sum.elim
      (fun ij => algebraMap (MvPolynomial (Fin (cdim N)) K) (CLoc N) (cgenPoly N ij.1 ij.2))
      (fun ij => algebraMap (MvPolynomial (Fin (cdim N)) K) (CLoc N)
        ((cgenPoly N).adjugate ij.1 ij.2) * IsLocalization.Away.invSelf (dpoly N)))

/-- Evaluation of the localisation at a point where the determinant is nonzero. -/
noncomputable def evPt (N : Matrix (Fin n) (Fin n) K) {x : Fin (cdim N) → K}
    (hx : (cgen N x).det ≠ 0) : CLoc N →+* K :=
  IsLocalization.Away.lift (S := CLoc N) (dpoly N)
    (g := (MvPolynomial.aeval x : MvPolynomial (Fin (cdim N)) K →ₐ[K] K).toRingHom)
    (by
      show IsUnit (MvPolynomial.aeval x (dpoly N))
      rw [aeval_dpoly]
      exact isUnit_iff_ne_zero.2 hx)

theorem evPt_algebraMap (N : Matrix (Fin n) (Fin n) K) {x : Fin (cdim N) → K}
    (hx : (cgen N x).det ≠ 0) (q : MvPolynomial (Fin (cdim N)) K) :
    evPt N hx (algebraMap (MvPolynomial (Fin (cdim N)) K) (CLoc N) q) =
      MvPolynomial.aeval x q :=
  IsLocalization.Away.lift_eq _ _ _

theorem evPt_invSelf (N : Matrix (Fin n) (Fin n) K) {x : Fin (cdim N) → K}
    (hx : (cgen N x).det ≠ 0) :
    evPt N hx (IsLocalization.Away.invSelf (dpoly N)) = ((cgen N x).det)⁻¹ := by
  have h : algebraMap (MvPolynomial (Fin (cdim N)) K) (CLoc N) (dpoly N) *
      IsLocalization.Away.invSelf (dpoly N) = 1 :=
    IsLocalization.Away.mul_invSelf (S := CLoc N) (dpoly N)
  have h2 := congrArg (evPt N hx) h
  rw [map_mul, map_one, evPt_algebraMap, aeval_dpoly] at h2
  exact (inv_eq_of_mul_eq_one_right h2).symm

theorem evPt_comp_evLoc (N : Matrix (Fin n) (Fin n) K) {x : Fin (cdim N) → K}
    (hx : (cgen N x).det ≠ 0) :
    (evPt N hx).comp (evLoc N) =
      (MvPolynomial.aeval (pairCoords ((cgen N x), (cgen N x)⁻¹)) :
        MvPolynomial (PairIndex (Fin n)) K →ₐ[K] K).toRingHom := by
  refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
  · show evPt N hx (evLoc N (MvPolynomial.C a)) = MvPolynomial.aeval _ (MvPolynomial.C a)
    rw [evLoc, MvPolynomial.eval₂Hom_C]
    show evPt N hx (algebraMap (MvPolynomial (Fin (cdim N)) K) (CLoc N) (MvPolynomial.C a)) = _
    rw [evPt_algebraMap]
    simp
  · show evPt N hx (evLoc N (X i)) = MvPolynomial.aeval _ (X i)
    rw [evLoc, MvPolynomial.eval₂Hom_X']
    cases i with
    | inl ij =>
        show evPt N hx (algebraMap (MvPolynomial (Fin (cdim N)) K) (CLoc N)
          (cgenPoly N ij.1 ij.2)) = _
        rw [evPt_algebraMap, aeval_cgenPoly, MvPolynomial.aeval_X]
        rfl
    | inr ij =>
        show evPt N hx (algebraMap (MvPolynomial (Fin (cdim N)) K) (CLoc N)
          ((cgenPoly N).adjugate ij.1 ij.2) * IsLocalization.Away.invSelf (dpoly N)) = _
        rw [map_mul, evPt_algebraMap, evPt_invSelf, aeval_adjugate_cgenPoly,
          MvPolynomial.aeval_X]
        show _ = ((cgen N x)⁻¹) ij.1 ij.2
        rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
        exact mul_comm _ _

theorem evPt_evLoc_apply (N : Matrix (Fin n) (Fin n) K) {x : Fin (cdim N) → K}
    (hx : (cgen N x).det ≠ 0) (f : MvPolynomial (PairIndex (Fin n)) K) :
    evPt N hx (evLoc N f) = MvPolynomial.aeval (pairCoords ((cgen N x), (cgen N x)⁻¹)) f :=
  RingHom.congr_fun (evPt_comp_evLoc N hx) f

/-- The generic invertible centraliser element gives a point of `Z(N)`. -/
theorem pairCoords_mem_cgroup (N : Matrix (Fin n) (Fin n) K) {z : Matrix (Fin n) (Fin n) K}
    (hz : z ∈ Height.Toolbox.centralizer N) (hd : IsUnit z.det) : pairCoords (z, z⁻¹) ∈ cgroup N :=
  ⟨⟨Matrix.mul_nonsing_inv z hd, Matrix.nonsing_inv_mul z hd⟩, hz⟩

/-- **The vanishing ideal of `Z(N)` is the kernel of the generic evaluation.** -/
theorem vanishingIdeal_cgroup_eq_ker [Infinite K] (N : Matrix (Fin n) (Fin n) K) :
    MvPolynomial.vanishingIdeal K (cgroup N) = RingHom.ker (evLoc N) := by
  refine le_antisymm (fun f hf => ?_) (fun f hf y hy => ?_)
  · -- A polynomial vanishing on `Z(N)` is killed by the generic evaluation.
    obtain ⟨m, a, ha⟩ := IsLocalization.Away.surj (S := CLoc N) (dpoly N) (evLoc N f)
    have hazero : a = 0 := by
      have hprod : a * dpoly N = 0 := by
        refine MvPolynomial.funext fun x => ?_
        show MvPolynomial.aeval x (a * dpoly N) = MvPolynomial.aeval x 0
        rw [map_zero, map_mul, aeval_dpoly]
        by_cases hx : (cgen N x).det = 0
        · rw [hx, mul_zero]
        · have hev := congrArg (evPt N hx) ha
          rw [map_mul, map_pow, evPt_algebraMap, evPt_algebraMap, aeval_dpoly,
            evPt_evLoc_apply] at hev
          rw [hf _ (pairCoords_mem_cgroup N (cgen_mem N x) (isUnit_iff_ne_zero.2 hx)),
            zero_mul] at hev
          rw [← hev, zero_mul]
      exact (mul_eq_zero.1 hprod).resolve_right (dpoly_ne_zero N)
    rw [hazero, map_zero] at ha
    have hunit : IsUnit ((algebraMap (MvPolynomial (Fin (cdim N)) K) (CLoc N) (dpoly N)) ^ m) :=
      IsLocalization.Away.algebraMap_pow_isUnit (S := CLoc N) (dpoly N) m
    exact (IsUnit.mul_left_eq_zero hunit).1 ha
  · -- Conversely, an element of the kernel vanishes at every point of `Z(N)`.
    have hz : fstMat y ∈ Height.Toolbox.centralizer N := hy.2
    have hd : IsUnit (fstMat y).det := Matrix.isUnit_det_of_right_inverse hy.1.1
    have hinv : (fstMat y)⁻¹ = sndMat y := Matrix.inv_eq_right_inv hy.1.1
    have hx : (cgen N ((cbasis N).equivFun ⟨fstMat y, hz⟩)).det ≠ 0 := by
      rw [cgen_of_mem N hz]
      exact isUnit_iff_ne_zero.1 hd
    have h := evPt_evLoc_apply N hx f
    rw [cgen_of_mem N hz, hinv, pairCoords_fstMat_sndMat] at h
    rw [← h, RingHom.mem_ker.mp hf, map_zero]

/-- **`Z(N)` is irreducible.** -/
theorem irreducible_cgroup [Infinite K] (N : Matrix (Fin n) (Fin n) K) :
    (MvPolynomial.vanishingIdeal K (cgroup N)).IsPrime := by
  have : IsDomain (CLoc N) := Localization.Away.isDomain (dpoly_ne_zero N)
  rw [vanishingIdeal_cgroup_eq_ker]
  exact RingHom.ker_isPrime _

end Irreducible

end Height.Chain.Untwisting

namespace Height.Chain.Untwisting

open MvPolynomial Height.Geometry Height.Steenrod

universe u

/-! ### The dimension of the centraliser group -/

section Cdim

open AlgebraicGeometry Topology

variable {K : Type} [Field K] [IsAlgClosed K] [Infinite K] {n : ℕ}

/-- The centraliser algebra in entry coordinates. -/
def cspace (N : Matrix (Fin n) (Fin n) K) : Set (Fin n × Fin n → K) :=
  (fun x => matCoords (cgen N x)) '' Set.univ

/-- The invertible elements of the centraliser algebra, in entry coordinates. -/
def cunits (N : Matrix (Fin n) (Fin n) K) : Set (Fin n × Fin n → K) :=
  matCoords '' {A : Matrix (Fin n) (Fin n) K | A ∈ Height.Toolbox.centralizer N ∧ IsUnit A.det}

omit [IsAlgClosed K] [Infinite K] in
theorem cspace_eq (N : Matrix (Fin n) (Fin n) K) :
    cspace N = matCoords '' {A : Matrix (Fin n) (Fin n) K | A ∈ Height.Toolbox.centralizer N} := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨x, -, rfl⟩
    exact ⟨cgen N x, cgen_mem N x, rfl⟩
  · rintro _ ⟨A, hA, rfl⟩
    refine ⟨(cbasis N).equivFun ⟨A, hA⟩, Set.mem_univ _, ?_⟩
    show matCoords (cgen N ((cbasis N).equivFun ⟨A, hA⟩)) = matCoords A
    rw [cgen_of_mem N hA]

/-- The centraliser algebra has the dimension of its parametrising space.

The count is the geometry API's `K`-point corollary of the
scheme-level finite-fibre theorem (`Geometry/Spec.lean`), not the coordinate
calculus of `Dimension/*` — which is that theorem's *prover*, one layer down. -/
theorem affineDim_cspace (N : Matrix (Fin n) (Fin n) K) :
    affineDim (cspace N) = (cdim N : WithBot ℕ∞) := by
  classical
  have hinj : Function.Injective fun x => matCoords (cgen N x) :=
    matCoords.injective.comp (cgen_injective N)
  have hpts : {x : Fin (cdim N) → K |
      (ptEquiv K x : 𝔸(Fin (cdim N); Spec (.of K))) ∈
        (Set.univ : Set 𝔸(Fin (cdim N); Spec (.of K)))} = Set.univ := by
    ext x; simp
  have hfun : (fun (x : Fin (cdim N) → K) (ij : Fin n × Fin n) =>
      MvPolynomial.aeval x (cgenPoly N ij.1 ij.2)) = fun x => matCoords (cgen N x) := by
    funext x ij
    rw [aeval_cgenPoly]
    simp
  have hfin : ∀ w : Fin n × Fin n → K,
      {x : Fin (cdim N) → K |
        (ptEquiv K x : 𝔸(Fin (cdim N); Spec (.of K))) ∈
          (Set.univ : Set 𝔸(Fin (cdim N); Spec (.of K))) ∧
        (fun ij => MvPolynomial.aeval x (cgenPoly N ij.1 ij.2)) = w}.Finite := by
    intro w
    refine Set.Subsingleton.finite fun a ha b hb => hinj ?_
    have h := ha.2.trans hb.2.symm
    rw [show (fun ij => MvPolynomial.aeval a (cgenPoly N ij.1 ij.2)) =
      (fun (x : Fin (cdim N) → K) (ij : Fin n × Fin n) =>
        MvPolynomial.aeval x (cgenPoly N ij.1 ij.2)) a from rfl, hfun] at h
    rw [show (fun ij => MvPolynomial.aeval b (cgenPoly N ij.1 ij.2)) =
      (fun (x : Fin (cdim N) → K) (ij : Fin n × Fin n) =>
        MvPolynomial.aeval x (cgenPoly N ij.1 ij.2)) b from rfl, hfun] at h
    exact h
  have h := affineDim_image_eq_of_finite_fibres_pts
    (fun ij : Fin n × Fin n => cgenPoly N ij.1 ij.2) IsConstructible.univ hfin
  rw [hpts, hfun] at h
  rw [cspace, h, affineDim_univ]
  simp

omit [IsAlgClosed K] in
theorem isPrime_vanishingIdeal_cspace (N : Matrix (Fin n) (Fin n) K) :
    (MvPolynomial.vanishingIdeal K (cspace N)).IsPrime := by
  refine irreducible_image (isPolyMap_cgen N) ?_
  have hv : MvPolynomial.vanishingIdeal K (Set.univ : Set (Fin (cdim N) → K)) = ⊥ := by
    refine le_antisymm (fun p hp => ?_) bot_le
    refine Ideal.mem_bot.2 (MvPolynomial.funext fun x => ?_)
    show MvPolynomial.aeval x p = MvPolynomial.aeval x (0 : MvPolynomial (Fin (cdim N)) K)
    rw [map_zero]
    exact hp x (Set.mem_univ x)
  rw [hv]
  exact Ideal.isPrime_bot

omit [IsAlgClosed K] in
theorem vanishingIdeal_cunits (N : Matrix (Fin n) (Fin n) K) :
    MvPolynomial.vanishingIdeal K (cunits N) = MvPolynomial.vanishingIdeal K (cspace N) := by
  have hsub : cunits N ⊆ cspace N := by
    rw [cspace_eq]
    rintro _ ⟨A, hA, rfl⟩
    exact ⟨A, hA.1, rfl⟩
  refine le_antisymm (fun f hf => ?_) (MvPolynomial.vanishingIdeal_anti_mono hsub)
  have hmul : f * detPoly (K := K) (Fin n) ∈ MvPolynomial.vanishingIdeal K (cspace N) := by
    rw [cspace_eq]
    rintro _ ⟨A, hA, rfl⟩
    rw [map_mul]
    by_cases hd : IsUnit A.det
    · rw [hf _ ⟨A, ⟨hA, hd⟩, rfl⟩, zero_mul]
    · have hdet : A.det = 0 := by
        rcases eq_or_ne A.det 0 with h | h
        · exact h
        · exact absurd (isUnit_iff_ne_zero.2 h) hd
      rw [aeval_detPoly, matCoords.symm_apply_apply, hdet, mul_zero]
  have hdetnot : detPoly (K := K) (Fin n) ∉ MvPolynomial.vanishingIdeal K (cspace N) := by
    intro hcon
    have hone : matCoords (1 : Matrix (Fin n) (Fin n) K) ∈ cspace N := by
      rw [cspace_eq]
      exact ⟨1, one_mem_centralizer N, rfl⟩
    have := hcon _ hone
    rw [aeval_detPoly, matCoords.symm_apply_apply, Matrix.det_one] at this
    exact one_ne_zero this
  exact ((isPrime_vanishingIdeal_cspace N).mem_or_mem hmul).resolve_right hdetnot

/-- **The centraliser group has the dimension of the centraliser algebra.** -/
theorem affineDim_cgroup (N : Matrix (Fin n) (Fin n) K) :
    affineDim (cgroup N) = (cdim N : WithBot ℕ∞) := by
  have himg : (fun x : PairIndex (Fin n) → K => matCoords (fstMat x)) '' cgroup N = cunits N := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨fstMat x, ⟨hx.2, Matrix.isUnit_det_of_right_inverse hx.1.1⟩, rfl⟩
    · rintro _ ⟨A, ⟨hA, hd⟩, rfl⟩
      exact ⟨pairCoords (A, A⁻¹), pairCoords_mem_cgroup N hA hd, rfl⟩
  have h := affineDim_of_finite_fibres (isPolyMap_fstMat (K := K) (μ := Fin n)) (cgroup N)
    (cunits N) (zclosure_cgroup N) himg ?_
  · rw [h]
    show affineDim (cunits N) = _
    unfold affineDim
    rw [vanishingIdeal_cunits N]
    exact affineDim_cspace N
  · intro y _
    refine Set.Subsingleton.finite fun a ha b hb => ?_
    have hfst : fstMat a = fstMat b :=
      matCoords.injective (ha.2.trans hb.2.symm)
    have hsnd : sndMat a = sndMat b := by
      have h1 : (fstMat a)⁻¹ = sndMat a := Matrix.inv_eq_right_inv ha.1.1.1
      have h2 : (fstMat b)⁻¹ = sndMat b := Matrix.inv_eq_right_inv hb.1.1.1
      rw [← h1, ← h2, hfst]
    have : pairCoords ((fstMat a), (sndMat a)) = pairCoords ((fstMat b), (sndMat b)) := by rw [hfst, hsnd]
    rwa [pairCoords_fstMat_sndMat, pairCoords_fstMat_sndMat] at this

/-! ### The polynomial action -/

end Cdim

end Height.Chain.Untwisting

namespace Height.Chain.Untwisting

open MvPolynomial Height.Geometry Height.Steenrod

universe u

/-! ### The conjugation fibration

For any Zariski closed `W` of matrix space, the set of invertible pairs whose
conjugate of `N` lies in `W` fibres over its image with all fibres a single
`Z(N)`-orbit, so dimension is additive.  This is `prop:untwist`'s "`π` is onto
with fibres the cosets `g Z(N)`", applied twice below: to `W = V(J)` and to
`W = 𝒞_N`.
-/

/-! ### The conjugation fibration, on the API

The centraliser `GLPair.centralizer K n N` (a closed subgroup of the pair model of `GL_n`,
`Geometry/GroupExamples.lean`) acts on the pair space by `x ↦ x · a⁻¹`
(`GLPair.centRegularAction`), the conjugation map is `conjMap N`, and the count is
`GroupPresentation.affineDim_of_orbit_fibration`, the classical form of `Geometry/Group.lean`
§ Corollaries.  The classical facts of the previous section discharge its hypotheses;
`actPt a x = (GLPair.glPresentation K n).mulPt x ((GLPair.glPresentation K n).invPt a)`. -/

section FibrationAPI

open AlgebraicGeometry Topology

variable {K : Type} [Field K] {n : ℕ}

theorem centralizer_pts (N : Matrix (Fin n) (Fin n) K) :
    (GLPair.centralizer K n N).pts = cgroup N := by
  ext x
  rw [GLPair.mem_centralizer_pts_iff, mem_cgroup, mem_glPair]
  exact and_assoc.symm

/-- **The pair model is the presented group.**  `glPair` is the `K`-points of
`GLPair.glPresentation`; the geometry API leaves this identification to the
consumer because `Geometry` does not import `Chain`. -/
theorem glPair_eq_pts : glPair K n = (GLPair.glPresentation K n).pts := by
  ext x
  rw [show (GLPair.glPresentation K n).pts = (GLPair.glData K n).pts from rfl,
    GLPair.mem_glData_pts_iff, mem_glPair,
    show GLPair.gPt K n x = fstMat x from rfl, show GLPair.hPt K n x = sndMat x from rfl]

/-- The group law of the pair model, in matrix coordinates. -/
theorem glPresentation_mulPt (x a : PairIndex (Fin n) → K) :
    (GLPair.glPresentation K n).mulPt x a =
      pairCoords ((fstMat x * fstMat a), (sndMat a * sndMat x)) := by
  funext c
  rcases c with c | c <;>
    simp [Height.Geometry.GroupData.mulPt, GLPair.glMul, fstMat, sndMat, GLPair.gVar,
      GLPair.hVar, GLPair.inlHom, GLPair.inrHom, Matrix.mul_apply]

/-- Inversion of the pair model, in matrix coordinates: the swap. -/
theorem glPresentation_invPt (a : PairIndex (Fin n) → K) :
    (GLPair.glPresentation K n).invPt a = pairCoords ((sndMat a), (fstMat a)) := by
  funext c
  rcases c with c | c <;>
    simp [Height.Geometry.GroupData.invPt, GLPair.glInv, fstMat, sndMat]

/-- The unit of the pair model, in matrix coordinates. -/
theorem glPresentation_one : (GLPair.glPresentation K n).one = pairCoords (1, 1) := by
  funext c
  rcases c with c | c <;> simp [GLPair.glOne]

/-- The centraliser's regular action on `K`-points, in pair coordinates. -/
theorem centRegularAction_actPt (N : Matrix (Fin n) (Fin n) K)
    (a x : PairIndex (Fin n) → K) :
    (GLPair.centRegularAction K n N).actPt a x =
      pairCoords ((fstMat x * sndMat a), (fstMat a * sndMat x)) := by
  funext ij
  rcases ij with ⟨i, j⟩ | ⟨i, j⟩
  · show GLPair.gPt K n ((GLPair.glRegData K n).actPt a x) i j = _
    rw [GLPair.gPt_glRegData_actPt]
    simp [GLPair.gPt, GLPair.hPt, fstMat, sndMat]
  · show GLPair.hPt K n ((GLPair.glRegData K n).actPt a x) i j = _
    rw [GLPair.hPt_glRegData_actPt]
    simp [GLPair.gPt, GLPair.hPt, fstMat, sndMat]

/-- The regular action is free on invertible pairs: this is what makes the orbit
count work. -/
theorem actPt_right_injective {N : Matrix (Fin n) (Fin n) K} {y : PairIndex (Fin n) → K}
    (hy : y ∈ glPair K n) {a b : PairIndex (Fin n) → K}
    (h : (GLPair.centRegularAction K n N).actPt a y
      = (GLPair.centRegularAction K n N).actPt b y) : a = b := by
  rw [centRegularAction_actPt, centRegularAction_actPt] at h
  have h1 : fstMat y * sndMat a = fstMat y * sndMat b := by
    have h' := congrArg fstMat h
    simpa using h'
  have h2 : fstMat a * sndMat y = fstMat b * sndMat y := by
    have h' := congrArg sndMat h
    simpa using h'
  have ha : sndMat a = sndMat b := by
    have h' := congrArg (fun M => sndMat y * M) h1
    simpa [← mul_assoc, hy.2] using h'
  have hb : fstMat a = fstMat b := by
    have h' := congrArg (fun M => M * fstMat y) h2
    simpa [mul_assoc, hy.2] using h'
  have h' : pairCoords ((fstMat a), (sndMat a)) = pairCoords ((fstMat b), (sndMat b)) := by
    rw [ha, hb]
  rwa [pairCoords_fstMat_sndMat, pairCoords_fstMat_sndMat] at h'

variable [IsAlgClosed K] [Infinite K]

/-- The regular action preserves invertibility. -/
theorem actPt_mem_glPair {N : Matrix (Fin n) (Fin n) K} {a : PairIndex (Fin n) → K}
    (ha : a ∈ cgroup N) {x : PairIndex (Fin n) → K} (hx : x ∈ glPair K n) :
    (GLPair.centRegularAction K n N).actPt a x ∈ glPair K n := by
  rw [centRegularAction_actPt]
  refine ⟨?_, ?_⟩
  · show (fstMat x * sndMat a) * (fstMat a * sndMat x) = 1
    calc (fstMat x * sndMat a) * (fstMat a * sndMat x)
        = fstMat x * ((sndMat a * fstMat a) * sndMat x) := by simp only [mul_assoc]
      _ = 1 := by rw [ha.1.2, one_mul, hx.1]
  · show (fstMat a * sndMat x) * (fstMat x * sndMat a) = 1
    calc (fstMat a * sndMat x) * (fstMat x * sndMat a)
        = fstMat a * ((sndMat x * fstMat x) * sndMat a) := by simp only [mul_assoc]
      _ = 1 := by rw [hx.2, one_mul, ha.1.1]

/-- The regular action does not move the conjugate of `N`: it is the invariant
map of the orbit fibration. -/
theorem conjMap_actPt {N : Matrix (Fin n) (Fin n) K} {a : PairIndex (Fin n) → K}
    (ha : a ∈ cgroup N) (x : PairIndex (Fin n) → K) :
    conjMap N ((GLPair.centRegularAction K n N).actPt a x) = conjMap N x := by
  rw [centRegularAction_actPt]
  show matCoords ((fstMat x * sndMat a) * N * (fstMat a * sndMat x))
      = matCoords (fstMat x * N * sndMat x)
  have key : sndMat a * N * fstMat a = N := by
    rw [mul_assoc, ← ha.2, ← mul_assoc, ha.1.2, one_mul]
  congr 1
  calc (fstMat x * sndMat a) * N * (fstMat a * sndMat x)
      = fstMat x * ((sndMat a * N * fstMat a) * sndMat x) := by simp only [mul_assoc]
    _ = fstMat x * (N * sndMat x) := by rw [key]
    _ = fstMat x * N * sndMat x := by rw [mul_assoc]

/-- Two invertible pairs with the same conjugate of `N` differ by an element of
the centraliser group. -/
theorem exists_actPt_of_conjMap_eq {N : Matrix (Fin n) (Fin n) K} {y z : PairIndex (Fin n) → K}
    (hy : y ∈ glPair K n) (hz : z ∈ glPair K n) (h : conjMap N z = conjMap N y) :
    ∃ a ∈ cgroup N, (GLPair.centRegularAction K n N).actPt a y = z := by
  set g := fstMat y with hg
  set hh := sndMat y with hhh
  set u := fstMat z with hu
  set v := sndMat z with hv
  have h1 : (hh * u) * (v * g) = 1 := by
    calc (hh * u) * (v * g) = hh * ((u * v) * g) := by simp only [mul_assoc]
      _ = hh * g := by rw [hz.1, one_mul]
      _ = 1 := hy.2
  have h2 : (v * g) * (hh * u) = 1 := by
    calc (v * g) * (hh * u) = v * ((g * hh) * u) := by simp only [mul_assoc]
      _ = v * u := by rw [hy.1, one_mul]
      _ = 1 := hz.2
  have huv : u * N * v = g * N * hh := matCoords.injective h
  have key : (hh * u) * N * (v * g) = N := by
    calc (hh * u) * N * (v * g) = hh * ((u * N * v) * g) := by simp only [mul_assoc]
      _ = hh * ((g * N * hh) * g) := by rw [huv]
      _ = (hh * g) * N * (hh * g) := by simp only [mul_assoc]
      _ = N := by rw [hy.2, one_mul, mul_one]
  have hcomm : (hh * u) * N = N * (hh * u) := by
    calc (hh * u) * N = (hh * u) * N * ((v * g) * (hh * u)) := by rw [h2, mul_one]
      _ = ((hh * u) * N * (v * g)) * (hh * u) := by simp only [mul_assoc]
      _ = N * (hh * u) := by rw [key]
  -- the API's action is `x ↦ x · a⁻¹`, so the witness is the inverse pair
  have key' : (v * g) * N * (hh * u) = N := by
    have h3 : (v * g) * ((hh * u) * N * (v * g)) * (hh * u) = (v * g) * N * (hh * u) :=
      congrArg (fun M => (v * g) * M * (hh * u)) key
    calc (v * g) * N * (hh * u)
        = (v * g) * ((hh * u) * N * (v * g)) * (hh * u) := h3.symm
      _ = ((v * g) * (hh * u)) * N * ((v * g) * (hh * u)) := by simp only [mul_assoc]
      _ = N := by rw [h2, one_mul, mul_one]
  have hcomm' : (v * g) * N = N * (v * g) := by
    calc (v * g) * N = (v * g) * N * ((hh * u) * (v * g)) := by rw [h1, mul_one]
      _ = ((v * g) * N * (hh * u)) * (v * g) := by simp only [mul_assoc]
      _ = N * (v * g) := by rw [key']
  refine ⟨pairCoords ((v * g), (hh * u)), ⟨⟨h2, h1⟩, hcomm'⟩, ?_⟩
  rw [centRegularAction_actPt]
  show pairCoords ((g * (hh * u)), ((v * g) * hh)) = z
  have e1 : g * (hh * u) = u := by rw [← mul_assoc, hy.1, one_mul]
  have e2 : (v * g) * hh = v := by rw [mul_assoc, hy.1, mul_one]
  rw [e1, e2, hu, hv, pairCoords_fstMat_sndMat]

/-- The centraliser group's points form an irreducible set: the input the API's
counts ask for, supplied once. -/
theorem centralizer_pts_isPrime (N : Matrix (Fin n) (Fin n) K) :
    (MvPolynomial.vanishingIdeal K (GLPair.centralizer K n N).pts).IsPrime := by
  rw [centralizer_pts]; exact irreducible_cgroup N

/-- **The centraliser acting on the pair space**, as the coordinate action the
dimension calculus consumes.  This is the geometry API's `centRegularAction` read
on `K`-points -- the group laws, the polynomiality and the orbit API are all the
API's. -/
noncomputable def cAction (N : Matrix (Fin n) (Fin n) K) :
    PolyAction K (PairIndex (Fin n)) (PairIndex (Fin n)) :=
  (GLPair.centRegularAction K n N).toPolyAction (centralizer_pts_isPrime N)

@[simp] theorem cAction_G (N : Matrix (Fin n) (Fin n) K) : (cAction N).G = cgroup N := by
  rw [cAction, Height.Geometry.ActionPresentation.toPolyAction_G, centralizer_pts]

@[simp] theorem cAction_act (N : Matrix (Fin n) (Fin n) K) (a x : PairIndex (Fin n) → K) :
    (cAction N).act a x = pairCoords ((fstMat x * sndMat a), (fstMat a * sndMat x)) :=
  centRegularAction_actPt N a x

theorem cAction_S (N : Matrix (Fin n) (Fin n) K) :
    (cAction N).S = (GLPair.centRegularAction K n N).pts := rfl

/-- The regular action acts on the whole pair space (`J = ⊥`). -/
@[simp] theorem cAction_S_eq_univ (N : Matrix (Fin n) (Fin n) K) :
    (cAction N).S = (Set.univ : Set (PairIndex (Fin n) → K)) := by
  rw [cAction_S]
  exact (GLPair.centRegularAction K n N).toActionData.pts_eq_univ
    (GLPair.centRegularAction_J N)

/-- Acting on the unit gives the inverse: the regular action is right
multiplication by the inverse. -/
@[simp] theorem cAction_act_one (N : Matrix (Fin n) (Fin n) K) (a : PairIndex (Fin n) → K) :
    (cAction N).act a (GLPair.glPresentation K n).one
      = (GLPair.glPresentation K n).invPt a := by
  rw [cAction_act, glPresentation_one, glPresentation_invPt, fstMat_pairCoords,
    sndMat_pairCoords, one_mul, mul_one]

/-- Inversion of the pair model is an involution. -/
@[simp] theorem glPresentation_invPt_invPt (a : PairIndex (Fin n) → K) :
    (GLPair.glPresentation K n).invPt ((GLPair.glPresentation K n).invPt a) = a := by
  rw [glPresentation_invPt, glPresentation_invPt, fstMat_pairCoords, sndMat_pairCoords,
    pairCoords_fstMat_sndMat]

/-! ### The orbit count -/

/-- **Every orbit has the dimension of the centraliser.**  The orbit is the image
of the group under `a ↦ a · y`, whose fibres are singletons
(`actPt_right_injective`), so `affineDim_of_finite_fibres` preserves the
dimension.  The action, its polynomiality and its group laws are the geometry
API's (`GLPair.centRegularAction`); only the freeness is domain input. -/
theorem affineDim_orbit (N : Matrix (Fin n) (Fin n) K)
    {y : PairIndex (Fin n) → K} (hy : y ∈ glPair K n) :
    affineDim ((cAction N).orbit y) = (cdim N : WithBot ℕ∞) := by
  classical
  set A := cAction N with hAdef
  have hpoly : IsPolyMap fun a : PairIndex (Fin n) → K => A.act a y := by
    obtain ⟨F, hF⟩ := A.act_poly
    exact ⟨fun i => subRight y (F i), fun a i => by rw [aeval_subRight]; exact hF a y i⟩
  have hG : A.G = cgroup N := by rw [hAdef, cAction_G]
  have himg : (fun a : PairIndex (Fin n) → K => A.act a y) '' A.G = A.orbit y := by
    ext z; constructor
    · rintro ⟨a, ha, rfl⟩; exact ⟨a, ha, rfl⟩
    · rintro ⟨a, ha, rfl⟩; exact ⟨a, ha, rfl⟩
  have h := affineDim_of_finite_fibres hpoly A.G _ (by rw [hG]; exact zclosure_cgroup N) rfl
    (fun w _ => Set.Subsingleton.finite fun a ha b hb =>
      actPt_right_injective hy (ha.2.trans hb.2.symm))
  rw [← himg, ← h, hG, affineDim_cgroup]

/-- **The conjugation fibration.**  `dim (image) + dim Z(N) = dim (source)`, for any
source cut out of `GL_n` by a constructible condition `S` on the conjugate. -/
theorem affineDim_conj_fibration (N : Matrix (Fin n) (Fin n) K)
    (W : Set (Fin n × Fin n → K)) (hcon : IsAffineConstructible (glPair K n ∩ conjMap N ⁻¹' W)) :
    affineDim (conjMap N '' (glPair K n ∩ conjMap N ⁻¹' W)) +
        (cdim N : WithBot ℕ∞) =
      affineDim (glPair K n ∩ conjMap N ⁻¹' W) := by
  classical
  have hP : (MvPolynomial.vanishingIdeal K (GLPair.centralizer K n N).pts).IsPrime := by
    rw [centralizer_pts]; exact irreducible_cgroup N
  have hmemP : ∀ a, a ∈ (GLPair.centralizer K n N).pts ↔ a ∈ cgroup N := fun a => by
    rw [centralizer_pts]
  refine (GLPair.centralizer K n N).affineDim_of_orbit_fibration hP
    (GLPair.centRegularAction K n N) rfl (isPolyMap_conjMap N) hcon ?_ ?_ ?_ ?_
  · intro a ha x hx
    exact ⟨actPt_mem_glPair ((hmemP a).1 ha) hx.1,
      by rw [Set.mem_preimage, conjMap_actPt ((hmemP a).1 ha)]; exact hx.2⟩
  · intro a ha x _
    exact conjMap_actPt ((hmemP a).1 ha) x
  · rintro w ⟨x, hx, rfl⟩
    refine ⟨x, hx, ?_⟩
    ext z
    constructor
    · rintro ⟨hz, hzw⟩
      rw [Set.mem_preimage, Set.mem_singleton_iff] at hzw
      obtain ⟨a, ha, rfl⟩ := exists_actPt_of_conjMap_eq hx.1 hz.1 hzw
      exact ⟨a, (hmemP a).2 ha, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      have ha' := (hmemP a).1 ha
      exact ⟨⟨actPt_mem_glPair ha' hx.1,
          by rw [Set.mem_preimage, conjMap_actPt ha']; exact hx.2⟩,
        by rw [Set.mem_preimage, Set.mem_singleton_iff, conjMap_actPt ha']⟩
  · intro x hx
    exact affineDim_orbit N hx.1

/-- The conjugation fibration over a Zariski closed `W`. -/
theorem affineDim_conj_fibration_of_zclosure (N : Matrix (Fin n) (Fin n) K)
    (W : Set (Fin n × Fin n → K)) (hW : zclosure W = W) :
    affineDim (conjMap N '' (glPair K n ∩ conjMap N ⁻¹' W)) +
        (cdim N : WithBot ℕ∞) =
      affineDim (glPair K n ∩ conjMap N ⁻¹' W) :=
  affineDim_conj_fibration N W
    (IsLocClosed.of_zclosure
      (zclosure_inter zclosure_glPair (zclosure_preimage (isPolyMap_conjMap N) hW))).isConstructible

end FibrationAPI

end Height.Chain.Untwisting

namespace Height.Chain.Untwisting

open MvPolynomial Height.Geometry Height.Steenrod

universe u

/-! ### The Lang map in the pair model -/

section Lang

variable (p r : ℕ) {K : Type u} [Field K] [ExpChar K p] {n : ℕ}

/-- Lang's map `g ↦ g⁻¹ Fr(g)` in the pair model. -/
def langPair (x : PairIndex (Fin n) → K) : PairIndex (Fin n) → K :=
  pairCoords ((sndMat x * frobeniusMatrix p r (fstMat x)), (frobeniusMatrix p r (sndMat x) * fstMat x))

theorem isPolyMap_frob_fstMat :
    IsPolyMap fun x : PairIndex (Fin n) → K => matCoords (frobeniusMatrix p r (fstMat x)) :=
  ⟨fun ij => X (Sum.inl ij) ^ p ^ r, fun x ij => by
    show (fstMat x ij.1 ij.2) ^ p ^ r = _
    simp⟩

theorem isPolyMap_frob_sndMat :
    IsPolyMap fun x : PairIndex (Fin n) → K => matCoords (frobeniusMatrix p r (sndMat x)) :=
  ⟨fun ij => X (Sum.inr ij) ^ p ^ r, fun x ij => by
    show (sndMat x ij.1 ij.2) ^ p ^ r = _
    simp⟩

theorem isPolyMap_langPair : IsPolyMap (langPair p r : (PairIndex (Fin n) → K) → _) :=
  isPolyMap_pairCoords (isPolyMap_matMul isPolyMap_sndMat (isPolyMap_frob_fstMat p r))
    (isPolyMap_matMul (isPolyMap_frob_sndMat p r) isPolyMap_fstMat)

/-- On invertible pairs the pair Lang map is the matrix Lang map. -/
theorem langPair_eq_matrixLang {x : PairIndex (Fin n) → K} (hx : x ∈ glPair K n) :
    langPair p r x =
      pairCoords (((matrixLang p r (pairUnit hx) : Matrix (Fin n) (Fin n) K)), (((matrixLang p r (pairUnit hx))⁻¹ : (Matrix (Fin n) (Fin n) K)ˣ) :
          Matrix (Fin n) (Fin n) K)) := by
  rw [langPair, coe_matrixLang, coe_matrixLang_inv]
  rfl

theorem fstMat_langPair {x : PairIndex (Fin n) → K} (hx : x ∈ glPair K n) :
    fstMat (langPair p r x) = (matrixLang p r (pairUnit hx) : Matrix (Fin n) (Fin n) K) := by
  rw [langPair_eq_matrixLang p r hx, fstMat_pairCoords]

theorem langPair_mem_glPair {x : PairIndex (Fin n) → K} (hx : x ∈ glPair K n) :
    langPair p r x ∈ glPair K n := by
  rw [langPair_eq_matrixLang p r hx]
  exact pairCoords_unit_mem _

/-- The pair attached to a unit, as a point of `glPair`. -/
theorem langPair_toPair (g : (Matrix (Fin n) (Fin n) K)ˣ) :
    langPair p r (pairCoords ((g : Matrix (Fin n) (Fin n) K), ((g⁻¹ : (Matrix (Fin n) (Fin n) K)ˣ) : Matrix (Fin n) (Fin n) K))) =
      pairCoords (((matrixLang p r g : Matrix (Fin n) (Fin n) K)), (((matrixLang p r g)⁻¹ : (Matrix (Fin n) (Fin n) K)ˣ) : Matrix (Fin n) (Fin n) K)) := by
  rw [langPair, coe_matrixLang, coe_matrixLang_inv]
  rfl

end Lang

end Height.Chain.Untwisting

namespace Height.Chain.Untwisting

open MvPolynomial Height.Geometry Height.Steenrod

universe u

/-- The zero locus of an ideal defined over a subfield is Zariski closed. -/
theorem zclosure_zeroLocus_algebra {k : Type*} {K : Type u} [Field k] [Field K] [Algebra k K]
    {σ : Type} (J : Ideal (MvPolynomial σ k)) :
    zclosure (MvPolynomial.zeroLocus K J) = MvPolynomial.zeroLocus K J := by
  have hset : MvPolynomial.zeroLocus K J =
      {x : σ → K | ∀ j : J, MvPolynomial.aeval x
        (MvPolynomial.map (algebraMap k K) (j : MvPolynomial σ k)) = 0} := by
    ext x
    constructor
    · intro hx j
      rw [Height.Chain.aeval_map_algebraMap]
      exact hx _ j.2
    · intro hx f hf
      have h := hx ⟨f, hf⟩
      rwa [Height.Chain.aeval_map_algebraMap] at h
  rw [hset]
  exact zclosure_eq_self_of_eqZeroLocus
    (T := Set.range fun j : J => MvPolynomial.map (algebraMap k K) (j : MvPolynomial σ k))
    fun z => ⟨fun hz p ⟨j, hj⟩ => hj ▸ hz j, fun hz j => hz _ ⟨j, rfl⟩⟩

end Height.Chain.Untwisting

namespace Height.Chain

open QSteenrod Height.Steenrod Height.Geometry Height.Chain.Untwisting

variable (p r n : ℕ) [Fact p.Prime] [NeZero r]

/-! ## `prop:untwist`: the two fibrations through the Lang map

`T` and its partner analogue are realised inside the closed pair model of
`GL_n`; the conjugation map fibres both over their images with fibres a single
`Z(N)`-orbit, and the Lang map identifies the two sources up to finite fibres.
-/

/-- `T` of `prop:untwist`, in the closed pair model of `GL_n`: the invertible
pairs `(g, g⁻¹)` with `g N g⁻¹ ∈ V(J)`. -/
noncomputable def pairTransporter (N : Matrix (Fin n) (Fin n) (GaloisField p r)) :
    Set (PairIndex (Fin n) → Kbar p r) :=
  Untwisting.glPair (Kbar p r) n ∩
    Untwisting.conjMap (ext p r n N) ⁻¹' MvPolynomial.zeroLocus (Kbar p r) (steenrodIdeal p r n)

/-- The partner transporter: the invertible pairs `(B, B⁻¹)` with
`B N B⁻¹ ∈ 𝒞_N`. -/
noncomputable def pairPartner (N : Matrix (Fin n) (Fin n) (GaloisField p r)) :
    Set (PairIndex (Fin n) → Kbar p r) :=
  Untwisting.glPair (Kbar p r) n ∩
    Untwisting.conjMap (ext p r n N) ⁻¹'
      MvPolynomial.zeroLocus (Kbar p r) (partnerUniversalIdeal p r n (ext p r n N))

omit [NeZero r] in
theorem isNilpotent_ext {N : Matrix (Fin n) (Fin n) (GaloisField p r)} (hN : IsNilpotent N) :
    IsNilpotent (ext p r n N) :=
  hN.map ((algebraMap (GaloisField p r) (Kbar p r)).mapMatrix)

omit [NeZero r] in
/-- Membership in the partner zero locus is membership in the partner locus. -/
theorem mem_partnerZeroLocus_iff {N : Matrix (Fin n) (Fin n) (GaloisField p r)} (hN : IsNilpotent N)
    (A : Matrix (Fin n) (Fin n) (Kbar p r)) :
    matCoords A ∈
        MvPolynomial.zeroLocus (Kbar p r) (partnerUniversalIdeal p r n (ext p r n N)) ↔
      A ∈ nilpotentPartnerLocus n (ext p r n N) :=
  partnerUniversalIdealVanishAt_iff_partner p r n (ext p r n N) A (isNilpotent_ext p r n hN)

omit [NeZero r] in
/-- The conjugation map carries `T` onto `V(J) ∩ O_N`, in coordinates. -/
theorem image_conjMap_pairTransporter (N : Matrix (Fin n) (Fin n) (GaloisField p r)) :
    Untwisting.conjMap (ext p r n N) '' pairTransporter p r n N =
      matCoords '' (Vlocus p r n ∩ conjOrbit (ext p r n N)) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨fstMat x * ext p r n N * sndMat x,
      ⟨hx.2, ⟨Untwisting.pairUnit hx.1, rfl⟩⟩, rfl⟩
  · rintro ⟨A, ⟨hV, g, rfl⟩, rfl⟩
    exact ⟨pairCoords ((g : Matrix (Fin n) (Fin n) (Kbar p r)), ((g⁻¹ : (Matrix (Fin n) (Fin n) (Kbar p r))ˣ) : Matrix (Fin n) (Fin n) (Kbar p r))),
      ⟨Untwisting.pairCoords_unit_mem g, hV⟩, rfl⟩

omit [NeZero r] in
/-- The conjugation map carries the partner transporter onto `𝒞_N ∩ O_N`. -/
theorem image_conjMap_pairPartner {N : Matrix (Fin n) (Fin n) (GaloisField p r)} (hN : IsNilpotent N) :
    Untwisting.conjMap (ext p r n N) '' pairPartner p r n N =
      matCoords '' (nilpotentPartnerLocus n (ext p r n N) ∩ conjOrbit (ext p r n N)) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨fstMat x * ext p r n N * sndMat x,
      ⟨(mem_partnerZeroLocus_iff p r n hN _).1 hx.2, ⟨Untwisting.pairUnit hx.1, rfl⟩⟩, rfl⟩
  · rintro ⟨A, ⟨hC, g, rfl⟩, rfl⟩
    exact ⟨pairCoords ((g : Matrix (Fin n) (Fin n) (Kbar p r)), ((g⁻¹ : (Matrix (Fin n) (Fin n) (Kbar p r))ˣ) : Matrix (Fin n) (Fin n) (Kbar p r))),
      ⟨Untwisting.pairCoords_unit_mem g, (mem_partnerZeroLocus_iff p r n hN _).2 hC⟩, rfl⟩

/-- `eq:transport` in the pair model: the Steenrod equations hold at `g N g⁻¹`
exactly when `Lang(g) N Lang(g)⁻¹` is a nilpotent partner of `N`. -/
theorem transport_pair {N : Matrix (Fin n) (Fin n) (GaloisField p r)} (hN : IsNilpotent N)
    {x : PairIndex (Fin n) → Kbar p r} (hx : x ∈ Untwisting.glPair (Kbar p r) n) :
    (Untwisting.conjMap (ext p r n N) x ∈
        MvPolynomial.zeroLocus (Kbar p r) (steenrodIdeal p r n)) ↔
      (Untwisting.conjMap (ext p r n N) (Untwisting.langPair p r x) ∈
        MvPolynomial.zeroLocus (Kbar p r) (partnerUniversalIdeal p r n (ext p r n N))) := by
  have hlang := Untwisting.langPair_eq_matrixLang p r hx
  have hc : Untwisting.conjMap (ext p r n N) (Untwisting.langPair p r x)
      = matCoords ((matrixLang p r (Untwisting.pairUnit hx) :
            Matrix (Fin n) (Fin n) (Kbar p r)) * ext p r n N *
          (((matrixLang p r (Untwisting.pairUnit hx))⁻¹ :
            (Matrix (Fin n) (Fin n) (Kbar p r))ˣ) : Matrix (Fin n) (Fin n) (Kbar p r))) := by
    show matCoords (fstMat (Untwisting.langPair p r x) * ext p r n N *
      sndMat (Untwisting.langPair p r x)) = _
    rw [hlang]
    rfl
  rw [hc, mem_partnerZeroLocus_iff p r n hN]
  show steenrodIdealVanishAt p r n
      (((Untwisting.pairUnit hx : (Matrix (Fin n) (Fin n) (Kbar p r))ˣ) :
          Matrix (Fin n) (Fin n) (Kbar p r)) * ext p r n N *
        (((Untwisting.pairUnit hx)⁻¹ : (Matrix (Fin n) (Fin n) (Kbar p r))ˣ) :
          Matrix (Fin n) (Fin n) (Kbar p r))) ↔ _
  rw [steenrodIdealVanishAt_iff_generators,
    rationalOrbit_steenrodVanish_iff_langPartner p r n (Untwisting.pairUnit hx) N]
  exact Iff.rfl

/-- **The Lang map identifies the two transporters up to finite fibres.** -/
theorem affineDim_pairTransporter {N : Matrix (Fin n) (Fin n) (GaloisField p r)} (hN : IsNilpotent N) :
    affineDim (pairTransporter p r n N) = affineDim (pairPartner p r n N) := by
  refine Height.Geometry.affineDim_of_finite_fibres (Untwisting.isPolyMap_langPair p r)
    (pairTransporter p r n N) (pairPartner p r n N) ?_ ?_ ?_
  · exact zclosure_inter Untwisting.zclosure_glPair
      (zclosure_preimage (Untwisting.isPolyMap_conjMap _)
        (Untwisting.zclosure_zeroLocus_algebra _))
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨Untwisting.langPair_mem_glPair p r hx.1, (transport_pair p r n hN hx.1).1 hx.2⟩
    · intro hy
      obtain ⟨g, hg⟩ :=
        Height.Steenrod.matrixLang_surjective p r n (K := Kbar p r) (Untwisting.pairUnit hy.1)
      have hgl : pairCoords ((g : Matrix (Fin n) (Fin n) (Kbar p r)), ((g⁻¹ : (Matrix (Fin n) (Fin n) (Kbar p r))ˣ) : Matrix (Fin n) (Fin n) (Kbar p r)))
          ∈ Untwisting.glPair (Kbar p r) n := Untwisting.pairCoords_unit_mem g
      have hy' : Untwisting.langPair p r
          (pairCoords ((g : Matrix (Fin n) (Fin n) (Kbar p r)), ((g⁻¹ : (Matrix (Fin n) (Fin n) (Kbar p r))ˣ) :
              Matrix (Fin n) (Fin n) (Kbar p r)))) = y := by
        rw [Untwisting.langPair_toPair p r g, hg]
        exact pairCoords_fstMat_sndMat y
      refine ⟨_, ⟨hgl, ?_⟩, hy'⟩
      rw [Set.mem_preimage, transport_pair p r n hN hgl, hy']
      exact hy.2
  · intro y _
    rcases Set.eq_empty_or_nonempty
        (pairTransporter p r n N ∩ Untwisting.langPair p r ⁻¹' {y}) with h | ⟨x₀, hx₀⟩
    · rw [h]
      exact Set.finite_empty
    · refine Set.Finite.subset
        ((matrixLang_fiber_finite p r (K := Kbar p r) (ι := Fin n)
          (Untwisting.pairUnit hx₀.1.1)).image
          (fun g : (Matrix (Fin n) (Fin n) (Kbar p r))ˣ =>
            pairCoords ((g : Matrix (Fin n) (Fin n) (Kbar p r)), ((g⁻¹ : (Matrix (Fin n) (Fin n) (Kbar p r))ˣ) :
                Matrix (Fin n) (Fin n) (Kbar p r))))) ?_
      rintro x hx
      refine ⟨Untwisting.pairUnit hx.1.1, ?_, pairCoords_fstMat_sndMat x⟩
      show matrixLang p r (Untwisting.pairUnit hx.1.1)
        = matrixLang p r (Untwisting.pairUnit hx₀.1.1)
      refine Units.ext ?_
      rw [← Untwisting.fstMat_langPair p r hx.1.1, ← Untwisting.fstMat_langPair p r hx₀.1.1,
        hx.2, hx₀.2]

omit [NeZero r] in
/-- The conjugation fibration for `T`. -/
theorem affineDim_conj_pairTransporter (N : Matrix (Fin n) (Fin n) (GaloisField p r)) :
    affineDim (matCoords '' (Vlocus p r n ∩ conjOrbit (ext p r n N))) +
        ((Untwisting.cdim (ext p r n N) : ℕ) : WithBot ℕ∞) =
      affineDim (pairTransporter p r n N) := by
  rw [← image_conjMap_pairTransporter]
  exact Untwisting.affineDim_conj_fibration_of_zclosure _ _ (Untwisting.zclosure_zeroLocus_algebra _)

omit [NeZero r] in
/-- The conjugation fibration for the partner transporter. -/
theorem affineDim_conj_pairPartner {N : Matrix (Fin n) (Fin n) (GaloisField p r)} (hN : IsNilpotent N) :
    affineDim (matCoords '' (nilpotentPartnerLocus n (ext p r n N) ∩
          conjOrbit (ext p r n N))) +
        ((Untwisting.cdim (ext p r n N) : ℕ) : WithBot ℕ∞) =
      affineDim (pairPartner p r n N) := by
  rw [← image_conjMap_pairPartner p r n hN]
  exact Untwisting.affineDim_conj_fibration_of_zclosure _ _ (Untwisting.zclosure_zeroLocus_algebra _)

/-- **`prop:untwist`.**  Inside the orbit of a rational nilpotent `N`, the
Steenrod locus and the partner variety of `N` have the same dimension.

Both sides are the image of a transporter in the closed pair model of `GL_n`
under the conjugation map, whose fibres are single `Z(N)`-orbits
(`affineDim_conj_pairTransporter`, `affineDim_conj_pairPartner`), and the two
transporters have the same dimension because Lang's map is a surjection with
finite fibres between them (`affineDim_pairTransporter`).  Cancelling
`dim Z(N)` gives the statement. -/
theorem untwist :
    ∀ N : Matrix (Fin n) (Fin n) (GaloisField p r), IsNilpotent N →
      affineDim (Height.Geometry.matCoords ''
          (Vlocus p r n ∩ conjOrbit (ext p r n N)))
        = affineDim (Height.Geometry.matCoords ''
            (nilpotentPartnerLocus n (ext p r n N) ∩ conjOrbit (ext p r n N))) := by
  intro N hN
  have h1 := affineDim_conj_pairTransporter p r n N
  have h2 := affineDim_conj_pairPartner p r n hN
  have h3 := affineDim_pairTransporter p r n hN
  exact Toolbox.add_natCast_right_cancel (h1.trans (h3.trans h2.symm))

end Height.Chain
