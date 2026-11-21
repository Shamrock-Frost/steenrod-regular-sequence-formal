import Height.Chain.PsiBlock
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# The map `ψ` of `thm:reduction` in affine coordinates

`Chain/Reduction.lean` reduces the node
`shiftedIsotropy` to a `PsiMap`, the geometry of the map

```
ψ(z') := c(z')⁻¹ · (member of the pencil at the moving point) · c(z')
```

where `c(z')` is a frame carrying a fixed coordinate flag onto the fibre flag
`V_•(z')` of the marked point.  This file builds everything about `ψ` that is
*affine algebra* and isolates the one analytic input — the frame itself — as
the structure `AdaptedFrame`.

## What is proved

`AdaptedFrame.toPsiMap : AdaptedFrame I → PsiMap I`.  Given the frame,
the irreducible `Z ⊆ 𝔫` is produced not as a Zariski closure of an image but as
the kernel of a ring map into a domain: with `A₀ := K[V]/I` the coordinate ring
of the irreducible source, `A₁ := A₀[x_{ij}]` the coordinate ring of the
*generic element `G` of the parabolic* of the fixed flag and
`B := (A₁)_{det G}`,

```
Θ : K[gl_n] → B ,     X_{ij} ↦ (G⁻¹ · ψ_gen · G)_{ij} ,     P := ker Θ .
```

`P` is prime because `B` is a domain, and `V(P) ⊆ 𝔫` because `G⁻¹ ψ_gen G`
lies in the nilradical of the parabolic (`Chain/PsiBlock.lean`).  Every
`K`-point and every arc of `Z` needed by `PsiMap` is then produced by *one*
mechanism, `mem_zeroLocus_psi_conj` for points and `arcInLocus_psi_conj` for arcs: a ring map `φ` out of `A₀` together with an
invertible element `E` of the parabolic over the target specialises `Θ`, since
`E` inverts `det G`.  Taking `φ = ` evaluation at `z` and `E = Ā` gives the
point `Ā⁻¹ ψ(z) Ā`, a conjugate of the member; taking `φ = ` evaluation along an
arc of `V(I)` and `E = (1 + s D) Ā` gives an arc of `Z` whose velocity is the
fibre motion conjugated, the term `[ψ(z), D]` absorbing the ambiguity of the
fibre motion (`lem:flag-velocity`: two decompositions differ by the parabolic).

The parabolic factor `G` is what makes the construction work at all: the fibre
motions of a marked velocity form a coset of `[N₀, 𝔭]` (`lem:local-model`(3) is
unique only modulo `𝔭`), so `Z` must be stable under conjugation by the
parabolic; and it must consist of *conjugates* of the member, since `PsiImage`
asks for `matCoords.symm w = c N₀ c⁻¹`, which is why the parabolic enters as a group
(hence the localisation at `det G`) and not as a linear space.

The node `Chain.shiftedIsotropy` (`Chain/Edges.lean`) then runs
`Chain.siPairing_eq_zero_of_psiMap` on the frame chain
`GeometricFrame → AlgebraicFrame → AdaptedFrame → PsiMap`, whose first link is
`Chain.nonempty_geometricFrame` (`Chain/Frame.lean`), proved there.

## What the frame is

The existence of the frame — proved in `Chain/Frame.lean` — is a tuple of
polynomials
`Ψ` and, at each point of a dense open of `V(I)`, an invertible `c(z)` with

* `Ψ(z) = c(z)⁻¹ (N + tM)(z) c(z)` lying in the nilradical of a *fixed*
  coordinate flag (so that `Ψ(z)` is strictly upper triangular), and
* `c(z)⁻¹ Y c(z) = ∂_s(Ψ ∘ a) + [Ψ(z), D]` for every fibre motion `Y` of the
  velocity of an arc `a`, with `D` in the parabolic.

This is `lem:local-model`(1),(3) made *algebraic in the point*: the fibre flag
`fibFlag (Pat N M t₀)` is the special fibre of `ker P^k` over `K⟦u⟧`, i.e. a
limit of kernels, so a polynomial frame for it exists only after inverting the
leading coefficients that compute that limit — the "transversality open".
`Pencil/LocalModel.lean` provides the frame at a *single* point
(`exists_adapted_trivialisation`); making it polynomial in the point is the
work of `Chain/Frame.lean`.
-/

namespace Height.Chain

open Matrix Height.Orbital Height.Steenrod Height.Pencil
open Height.Geometry (SIIndex SIPoint siCoords PairIndex pairCoords fstMat sndMat matCoords
  MarkedIndex markedCoords)

universe u

/-! ### Generalities: reduction of a conjugate along an arc -/

section MatCD

variable {K : Type u} [Field K] {n : ℕ}

/-- A ring map commutes with matrix inversion when the determinant is a unit. -/
theorem map_nonsing_inv {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    {A : Matrix (Fin n) (Fin n) R} (h : IsUnit A.det) :
    (A⁻¹).map f = (A.map f)⁻¹ := by
  have hu : IsUnit (A.map f).det := by
    rw [show (A.map f).det = f A.det from (RingHom.map_det f A).symm]
    exact h.map f
  refine (Matrix.inv_eq_right_inv ?_).symm
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ h, Matrix.map_one f (map_zero f) (map_one f)]

/-- The determinant commutes with a ring map, in the `Matrix.map` form. -/
theorem det_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (A : Matrix (Fin n) (Fin n) R) : (A.map f).det = f A.det :=
  (RingHom.map_det f A).symm

/-- Reduction at `s = 0` of `E⁻¹ Φ E`. -/
theorem matC_conj {Φ E : Matrix (Fin n) (Fin n) (PowerSeries K)} (hE : IsUnit E.det) :
    matC (E⁻¹ * Φ * E) = (matC E)⁻¹ * matC Φ * matC E := by
  have hC : matC E⁻¹ = (matC E)⁻¹ := by
    show (E⁻¹).map (PowerSeries.constantCoeff (R := K)) = _
    rw [map_nonsing_inv _ hE]
    rfl
  rw [matC_mul, matC_mul, hC]

/-- The velocity of `E⁻¹ Φ E` along an arc, in terms of the reductions. -/
theorem matD_conj {Φ E : Matrix (Fin n) (Fin n) (PowerSeries K)} (hE : IsUnit E.det) :
    matD (E⁻¹ * Φ * E) =
      (matC E)⁻¹ * (matD Φ + matC Φ * (matD E * (matC E)⁻¹)
        - matD E * (matC E)⁻¹ * matC Φ) * matC E := by
  have hdet : IsUnit (matC E).det := by
    have h : (matC E).det = PowerSeries.constantCoeff E.det :=
      (RingHom.map_det (PowerSeries.constantCoeff (R := K)) E).symm
    rw [h]
    exact hE.map _
  have hCinv : matC E⁻¹ = (matC E)⁻¹ := by
    show (E⁻¹).map (PowerSeries.constantCoeff (R := K)) = _
    rw [map_nonsing_inv _ hE]
    rfl
  have hCX : matC E * (matC E)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hXC : (matC E)⁻¹ * matC E = 1 := Matrix.nonsing_inv_mul _ hdet
  have hD1 : matD (E⁻¹ * E) = 0 := by
    rw [Matrix.nonsing_inv_mul _ hE]
    ext i j
    show PowerSeries.coeff 1 ((1 : Matrix (Fin n) (Fin n) (PowerSeries K)) i j) = 0
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  have hDinv : matD E⁻¹ = -((matC E)⁻¹ * matD E * (matC E)⁻¹) := by
    have h := matD_mul E⁻¹ E
    rw [hD1, hCinv] at h
    have h2 : matD E⁻¹ * matC E = -((matC E)⁻¹ * matD E) :=
      eq_neg_of_add_eq_zero_left h.symm
    have h3 : matD E⁻¹ * matC E * (matC E)⁻¹
        = -((matC E)⁻¹ * matD E) * (matC E)⁻¹ := by rw [h2]
    rw [Matrix.mul_assoc, hCX, Matrix.mul_one] at h3
    rw [h3]
    noncomm_ring
  rw [matD_mul, matD_mul, matC_mul, hCinv, hDinv]
  have h1 : (matC E)⁻¹ * (matD Φ + matC Φ * (matD E * (matC E)⁻¹)
        - matD E * (matC E)⁻¹ * matC Φ) * matC E
      = (matC E)⁻¹ * matD Φ * matC E
        + (matC E)⁻¹ * matC Φ * (matD E * ((matC E)⁻¹ * matC E))
        - (matC E)⁻¹ * (matD E * ((matC E)⁻¹ * (matC Φ * matC E))) := by
    noncomm_ring
  rw [h1, hXC, Matrix.mul_one]
  noncomm_ring

end MatCD

/-! ### The coordinates of a point of the incidence -/

section Coords

variable {K : Type u} [Field K] {n : ℕ}

/-- A tuple of polynomials, read as a matrix at a point. -/
noncomputable def polyMat (Ψ : Fin n × Fin n → MvPolynomial (SIIndex (Fin n)) K)
    (z : SIIndex (Fin n) → K) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j => MvPolynomial.eval z (Ψ (i, j))

/-- The same tuple, read as a matrix along an arc. -/
noncomputable def polyMatArc (Ψ : Fin n × Fin n → MvPolynomial (SIIndex (Fin n)) K)
    (a : SIArc n K) : Matrix (Fin n) (Fin n) (PowerSeries K) :=
  Matrix.of fun i j => MvPolynomial.aeval a.coords (Ψ (i, j))

end Coords

/-! ### The generic element of the parabolic -/

section GenPar

variable {n : ℕ}

/-- The coordinates of the parabolic of a coordinate flag: the entries that are
not forced to vanish. -/
abbrev parIdx (lvl : Fin n → ℕ) : Type := {ij : Fin n × Fin n // lvl ij.1 ≤ lvl ij.2}

/-- The generic element of the parabolic of `lvl` over a base ring. -/
noncomputable def genPar (lvl : Fin n → ℕ) (A : Type*) [CommRing A] :
    Matrix (Fin n) (Fin n) (MvPolynomial (parIdx lvl) A) :=
  Matrix.of fun i j => if h : lvl i ≤ lvl j then MvPolynomial.X ⟨(i, j), h⟩ else 0

/-- The element of the parabolic with the given coordinates. -/
def genParVal (lvl : Fin n → ℕ) {A : Type*} [Zero A] (v : parIdx lvl → A) :
    Matrix (Fin n) (Fin n) A :=
  Matrix.of fun i j => if h : lvl i ≤ lvl j then v ⟨(i, j), h⟩ else 0

theorem isBlockUpper_genPar (lvl : Fin n → ℕ) (A : Type*) [CommRing A] :
    IsBlockUpper lvl (genPar lvl A) := by
  intro i j hij
  show (if h : lvl i ≤ lvl j then _ else (0 : MvPolynomial (parIdx lvl) A)) = 0
  rw [dite_eq_right (not_le.mpr hij)]

theorem isBlockUpper_genParVal (lvl : Fin n → ℕ) {A : Type*} [Zero A] (v : parIdx lvl → A) :
    IsBlockUpper lvl (genParVal lvl v) := by
  intro i j hij
  show (if h : lvl i ≤ lvl j then _ else (0 : A)) = 0
  rw [dite_eq_right (not_le.mpr hij)]

theorem genParVal_apply (lvl : Fin n → ℕ) {A : Type*} [Zero A] (v : parIdx lvl → A)
    (ij : parIdx lvl) : genParVal lvl v ij.1.1 ij.1.2 = v ij := by
  show (if h : lvl ij.1.1 ≤ lvl ij.1.2 then v ⟨(ij.1.1, ij.1.2), h⟩ else 0) = v ij
  rw [dite_eq_left ij.2]

/-- Specialising the generic parabolic element. -/
theorem genPar_map_eval₂ {A S : Type*} [CommRing A] [CommRing S] (lvl : Fin n → ℕ)
    (φ : A →+* S) (E : Matrix (Fin n) (Fin n) S) (hE : IsBlockUpper lvl E) :
    (genPar lvl A).map (MvPolynomial.eval₂Hom φ (fun ij : parIdx lvl => E ij.1.1 ij.1.2))
      = E := by
  ext i j
  show MvPolynomial.eval₂Hom φ _
      (if h : lvl i ≤ lvl j then MvPolynomial.X (⟨(i, j), h⟩ : parIdx lvl) else 0) = E i j
  by_cases h : lvl i ≤ lvl j
  · rw [dite_eq_left h]
    simp
  · rw [dite_eq_right h, map_zero, hE i j (lt_of_not_ge h)]

end GenPar

/-! ### The prime `P` cutting out `Z` -/

section Construction

variable {K : Type u} [Field K] {n : ℕ}

/-- The coordinate ring of the irreducible source `V(I)`. -/
abbrev srcRing (I : Ideal (MvPolynomial (SIIndex (Fin n)) K)) : Type u :=
  MvPolynomial (SIIndex (Fin n)) K ⧸ I

/-- The structure map of the coordinate ring of the source. -/
noncomputable def quotC (I : Ideal (MvPolynomial (SIIndex (Fin n)) K)) : K →+* srcRing I :=
  (Ideal.Quotient.mk I).comp MvPolynomial.C

/-- `ψ` read in an arbitrary `srcRing I`-algebra. -/
noncomputable def psiQuot (I : Ideal (MvPolynomial (SIIndex (Fin n)) K))
    (Ψ : Fin n × Fin n → MvPolynomial (SIIndex (Fin n)) K) {S : Type*} [CommRing S]
    (φ : srcRing I →+* S) : Matrix (Fin n) (Fin n) S :=
  Matrix.of fun i j => φ (Ideal.Quotient.mk I (Ψ (i, j)))

variable (lvl : Fin n → ℕ) (I : Ideal (MvPolynomial (SIIndex (Fin n)) K))
  (Ψ : Fin n × Fin n → MvPolynomial (SIIndex (Fin n)) K)

/-- The coordinate ring of the source times the parabolic. -/
abbrev parRing : Type u := MvPolynomial (parIdx lvl) (srcRing I)

/-- The generic element of the parabolic over the source. -/
noncomputable def genParSrc : Matrix (Fin n) (Fin n) (parRing lvl I) := genPar lvl (srcRing I)

/-- Its determinant: the element inverted in the localisation. -/
noncomputable def parDet : parRing lvl I := (genParSrc lvl I).det

/-- The coordinate ring of the source times the parabolic *group*. -/
abbrev locRing : Type u := Localization.Away (parDet lvl I)

/-- The generic element of the parabolic, over the localisation. -/
noncomputable def genParLoc : Matrix (Fin n) (Fin n) (locRing lvl I) :=
  (genParSrc lvl I).map (algebraMap (parRing lvl I) (locRing lvl I))

theorem genParLoc_def : genParLoc lvl I
    = (genParSrc lvl I).map (algebraMap (parRing lvl I) (locRing lvl I)) := rfl

theorem isUnit_det_genParLoc : IsUnit (genParLoc lvl I).det := by
  have h : (genParLoc lvl I).det
      = algebraMap (parRing lvl I) (locRing lvl I) (parDet lvl I) := by
    rw [genParLoc_def]
    exact det_map (algebraMap (parRing lvl I) (locRing lvl I)) (genParSrc lvl I)
  rw [h]
  exact IsLocalization.Away.algebraMap_isUnit (parDet lvl I)

/-- `ψ` over the localisation. -/
noncomputable def psiLoc : Matrix (Fin n) (Fin n) (locRing lvl I) :=
  psiQuot I Ψ ((algebraMap (parRing lvl I) (locRing lvl I)).comp
    (MvPolynomial.C : srcRing I →+* parRing lvl I))

/-- The generic conjugate `G⁻¹ ψ G`: the generic point of `Z`. -/
noncomputable def psiGen : Matrix (Fin n) (Fin n) (locRing lvl I) :=
  (genParLoc lvl I)⁻¹ * psiLoc lvl I Ψ * genParLoc lvl I

/-- The ring map whose kernel is the prime of `Z`. -/
noncomputable def psiHom : MvPolynomial (Fin n × Fin n) K →+* locRing lvl I :=
  MvPolynomial.eval₂Hom
    (((algebraMap (parRing lvl I) (locRing lvl I)).comp
      (MvPolynomial.C : srcRing I →+* parRing lvl I)).comp (quotC I))
    (fun ij => psiGen lvl I Ψ ij.1 ij.2)

/-- **The prime of `Z`.** -/
noncomputable def psiPrime : Ideal (MvPolynomial (Fin n × Fin n) K) :=
  RingHom.ker (psiHom lvl I Ψ)

/-- **Specialisation.**  A ring map out of the coordinate ring of the source
together with an invertible element `E` of the parabolic over the target
specialises the generic point of `Z` to `E⁻¹ ψ E`.  This is the single
mechanism producing both the `K`-points and the arcs of `Z`. -/
theorem exists_psi_specialisation {S : Type u} [CommRing S] (φ : srcRing I →+* S)
    (E : Matrix (Fin n) (Fin n) S) (hE : IsBlockUpper lvl E) (hEu : IsUnit E.det) :
    ∃ ev : locRing lvl I →+* S,
      (∀ x : parRing lvl I, ev (algebraMap (parRing lvl I) (locRing lvl I) x)
          = MvPolynomial.eval₂Hom φ (fun ij : parIdx lvl => E ij.1.1 ij.1.2) x) ∧
        ev.comp (psiHom lvl I Ψ)
          = MvPolynomial.eval₂Hom (φ.comp (quotC I))
              (fun ij : Fin n × Fin n => (E⁻¹ * psiQuot I Ψ φ * E) ij.1 ij.2) := by
  classical
  set evA : parRing lvl I →+* S :=
    MvPolynomial.eval₂Hom φ (fun ij : parIdx lvl => E ij.1.1 ij.1.2) with hevA
  have hmapG : (genParSrc lvl I).map evA = E := genPar_map_eval₂ lvl φ E hE
  have hdet : evA (parDet lvl I) = E.det := by
    rw [parDet, ← det_map evA (genParSrc lvl I), hmapG]
  have hunits : ∀ y : Submonoid.powers (parDet lvl I), IsUnit (evA (y : parRing lvl I)) := by
    rintro ⟨y, k, hk⟩
    have : evA y = E.det ^ k := by rw [← hk, map_pow, hdet]
    rw [this]
    exact hEu.pow k
  refine ⟨IsLocalization.lift hunits, fun x => IsLocalization.lift_eq hunits x, ?_⟩
  have hcomp : ∀ x, (IsLocalization.lift hunits)
      (algebraMap (parRing lvl I) (locRing lvl I) x) = evA x :=
    fun x => IsLocalization.lift_eq hunits x
  have hGev : (genParLoc lvl I).map (IsLocalization.lift hunits) = E := by
    rw [genParLoc_def, Matrix.map_map]
    rw [show ((IsLocalization.lift hunits) ∘ (algebraMap (parRing lvl I) (locRing lvl I)))
        = ⇑evA from funext hcomp]
    exact hmapG
  have hΨev : (psiLoc lvl I Ψ).map (IsLocalization.lift hunits) = psiQuot I Ψ φ := by
    ext i j
    show (IsLocalization.lift hunits)
      (algebraMap (parRing lvl I) (locRing lvl I)
        (MvPolynomial.C (Ideal.Quotient.mk I (Ψ (i, j))))) = φ (Ideal.Quotient.mk I (Ψ (i, j)))
    rw [hcomp, hevA]
    simp
  have hWev : (psiGen lvl I Ψ).map (IsLocalization.lift hunits)
      = E⁻¹ * psiQuot I Ψ φ * E := by
    rw [psiGen, Matrix.map_mul, Matrix.map_mul, hΨev, hGev,
      map_nonsing_inv _ (isUnit_det_genParLoc lvl I), hGev]
  refine MvPolynomial.ringHom_ext (fun a => ?_) (fun ij => ?_)
  · simp only [RingHom.comp_apply, psiHom, MvPolynomial.eval₂Hom_C]
    rw [hcomp, hevA]
    simp
  · simp only [RingHom.comp_apply, psiHom, MvPolynomial.eval₂Hom_X']
    exact congrFun (congrFun hWev ij.1) ij.2

/-! #### `P` is prime and `Z ⊆ 𝔫` -/

theorem genParSrc_def : genParSrc lvl I = genPar lvl (srcRing I) := rfl

theorem parDet_ne_zero (hI : I.IsPrime) : parDet lvl I ≠ 0 := by
  have := hI
  have : IsDomain (srcRing I) := Ideal.Quotient.isDomain I
  intro h
  have hmap : (genParSrc lvl I).map (MvPolynomial.eval₂Hom (RingHom.id (srcRing I))
      (fun ij : parIdx lvl => (1 : Matrix (Fin n) (Fin n) (srcRing I)) ij.1.1 ij.1.2))
      = 1 := by
    rw [genParSrc_def]
    exact genPar_map_eval₂ lvl (RingHom.id (srcRing I)) 1 isBlockUpper_one
  have hev : (MvPolynomial.eval₂Hom (RingHom.id (srcRing I))
      (fun ij : parIdx lvl => (1 : Matrix (Fin n) (Fin n) (srcRing I)) ij.1.1 ij.1.2))
      (parDet lvl I) = 1 := by
    rw [parDet, ← det_map (MvPolynomial.eval₂Hom (RingHom.id (srcRing I))
      (fun ij : parIdx lvl => (1 : Matrix (Fin n) (Fin n) (srcRing I)) ij.1.1 ij.1.2))
      (genParSrc lvl I), hmap, Matrix.det_one]
  rw [h, map_zero] at hev
  exact zero_ne_one hev

theorem isDomain_locRing (hI : I.IsPrime) : IsDomain (locRing lvl I) := by
  have := hI
  have : IsDomain (srcRing I) := Ideal.Quotient.isDomain I
  exact IsLocalization.Away.isDomain (S := locRing lvl I) (parDet_ne_zero lvl I hI)

theorem psiPrime_isPrime (hI : I.IsPrime) : (psiPrime lvl I Ψ).IsPrime := by
  have := isDomain_locRing lvl I hI
  exact RingHom.ker_isPrime (psiHom lvl I Ψ)

theorem isBlockUpper_genParLoc : IsBlockUpper lvl (genParLoc lvl I) := by
  rw [genParLoc_def]
  exact (isBlockUpper_genPar lvl (srcRing I)).map _

theorem isBlockUpper_genParLoc_inv (hI : I.IsPrime) :
    IsBlockUpper lvl ((genParLoc lvl I)⁻¹) := by
  have := isDomain_locRing lvl I hI
  intro i j hij
  have hinj : Function.Injective
      (algebraMap (locRing lvl I) (FractionRing (locRing lvl I))) :=
    IsFractionRing.injective _ _
  apply hinj
  rw [map_zero]
  have h1 : ((genParLoc lvl I)⁻¹).map
        (algebraMap (locRing lvl I) (FractionRing (locRing lvl I)))
      = ((genParLoc lvl I).map
        (algebraMap (locRing lvl I) (FractionRing (locRing lvl I))))⁻¹ :=
    map_nonsing_inv _ (isUnit_det_genParLoc lvl I)
  have h2 : IsBlockUpper lvl ((genParLoc lvl I).map
      (algebraMap (locRing lvl I) (FractionRing (locRing lvl I)))) :=
    (isBlockUpper_genParLoc lvl I).map _
  have h3 : IsUnit ((genParLoc lvl I).map
      (algebraMap (locRing lvl I) (FractionRing (locRing lvl I)))).det := by
    rw [det_map (algebraMap (locRing lvl I) (FractionRing (locRing lvl I))) (genParLoc lvl I)]
    exact (isUnit_det_genParLoc lvl I).map _
  show ((genParLoc lvl I)⁻¹).map
      (algebraMap (locRing lvl I) (FractionRing (locRing lvl I))) i j = 0
  rw [h1]
  exact (h2.inv h3) i j hij

theorem isBlockStrict_psiLoc (hΨ : ∀ i j : Fin n, lvl j ≤ lvl i → Ψ (i, j) ∈ I) :
    IsBlockStrict lvl (psiLoc lvl I Ψ) := by
  intro i j hij
  show ((algebraMap (parRing lvl I) (locRing lvl I)).comp
    (MvPolynomial.C : srcRing I →+* parRing lvl I)) (Ideal.Quotient.mk I (Ψ (i, j))) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr (hΨ i j hij), map_zero]

theorem isBlockStrict_psiGen (hI : I.IsPrime)
    (hΨ : ∀ i j : Fin n, lvl j ≤ lvl i → Ψ (i, j) ∈ I) :
    IsBlockStrict lvl (psiGen lvl I Ψ) :=
  ((isBlockStrict_psiLoc lvl I Ψ hΨ).mul_left
    (isBlockUpper_genParLoc_inv lvl I hI)).mul_right (isBlockUpper_genParLoc lvl I)

/-- `Z ⊆ 𝔫`: every point of the zero locus of `P` is strictly upper
triangular. -/
theorem isStrictlyUpper_of_mem_zeroLocus (hmono : Monotone lvl) (hI : I.IsPrime)
    (hΨ : ∀ i j : Fin n, lvl j ≤ lvl i → Ψ (i, j) ∈ I) :
    ∀ x ∈ MvPolynomial.zeroLocus K (psiPrime lvl I Ψ),
      Height.Orbital.IsStrictlyUpper (matCoords.symm x) := by
  intro x hx i j hij
  have hmem : (MvPolynomial.X (i, j) : MvPolynomial (Fin n × Fin n) K) ∈ psiPrime lvl I Ψ := by
    show psiHom lvl I Ψ (MvPolynomial.X (i, j)) = 0
    rw [psiHom, MvPolynomial.eval₂Hom_X']
    exact (isBlockStrict_psiGen lvl I Ψ hI hΨ).isStrictlyUpper hmono i j hij
  have := hx _ hmem
  simpa using this

/-! #### Genericity: a function not vanishing on `Z` at a conjugate of the member -/

/-- **The genericity transfer.**  A polynomial
`g` not vanishing on `Z` does not vanish at some conjugate `Ā⁻¹ ψ(z) Ā` of the
member, at every point `z` of a dense open of `V(I)`.  The dense open is cut
out by a coefficient of the numerator of `Θ g`, and the conjugator is found by
a nonvanishing point of that coefficient's specialisation. -/
theorem exists_generic_conjugate [Infinite K] (hI : I.IsPrime)
    {g : MvPolynomial (Fin n × Fin n) K} (hg : g ∉ psiPrime lvl I Ψ) :
    ∃ h₁ ∉ I, ∀ z ∈ MvPolynomial.zeroLocus K I, MvPolynomial.eval z h₁ ≠ 0 →
      ∃ Ā : Matrix (Fin n) (Fin n) K, IsBlockUpper lvl Ā ∧ IsUnit Ā.det ∧
        MvPolynomial.eval
          (fun ij : Fin n × Fin n => (Ā⁻¹ * polyMat Ψ z * Ā) ij.1 ij.2) g ≠ 0 := by
  classical
  have := hI
  have : IsDomain (srcRing I) := Ideal.Quotient.isDomain I
  have := isDomain_locRing lvl I hI
  have hΘg : psiHom lvl I Ψ g ≠ 0 := hg
  obtain ⟨⟨q, y⟩, hq⟩ := IsLocalization.surj (M := Submonoid.powers (parDet lvl I))
    (S := locRing lvl I) (psiHom lvl I Ψ g)
  have hyunit : IsUnit (algebraMap (parRing lvl I) (locRing lvl I) (y : parRing lvl I)) := by
    obtain ⟨k, hk⟩ := y.2
    rw [← hk, map_pow]
    exact (IsLocalization.Away.algebraMap_isUnit (parDet lvl I)).pow k
  have hqne : q ≠ 0 := by
    intro h
    apply hΘg
    rw [h, map_zero] at hq
    have := congrArg (fun t => t * (↑hyunit.unit⁻¹ : locRing lvl I)) hq
    simpa [mul_assoc, IsUnit.mul_val_inv] using this
  obtain ⟨β, hβ⟩ : ∃ β, q.coeff β ≠ 0 := by
    by_contra hc
    push Not at hc
    refine hqne (MvPolynomial.ext q 0 fun β => ?_)
    rw [hc β]
    simp
  obtain ⟨h₁, hh₁⟩ := Ideal.Quotient.mk_surjective (I := I) (q.coeff β)
  refine ⟨h₁, ?_, ?_⟩
  · intro hmem
    exact hβ (by rw [← hh₁, Ideal.Quotient.eq_zero_iff_mem.mpr hmem])
  intro z hz hz1
  -- the coordinate ring of the source, evaluated at `z`
  have hzI : ∀ f ∈ I, MvPolynomial.eval z f = 0 := by
    intro f hf
    have := hz f hf
    rwa [MvPolynomial.aeval_eq_eval] at this
  set evz : srcRing I →+* K :=
    Ideal.Quotient.lift I (MvPolynomial.eval z : MvPolynomial (SIIndex (Fin n)) K →+* K) hzI with hevz
  -- the numerator and the determinant, specialised at `z`
  set qz : MvPolynomial (parIdx lvl) K := MvPolynomial.map evz q with hqz
  set δz : MvPolynomial (parIdx lvl) K := MvPolynomial.map evz (parDet lvl I) with hδz
  have hcoeff : qz.coeff β = MvPolynomial.eval z h₁ := by
    rw [hqz, MvPolynomial.coeff_map, ← hh₁]
    rfl
  have hqzne : qz ≠ 0 := by
    intro h
    rw [h] at hcoeff
    simp only [AddMonoidAlgebra.coeff_zero] at hcoeff
    exact hz1 hcoeff.symm
  have hdetspec : ∀ E : Matrix (Fin n) (Fin n) K, IsBlockUpper lvl E →
      MvPolynomial.eval₂ evz (fun ij : parIdx lvl => E ij.1.1 ij.1.2) (parDet lvl I)
        = E.det := by
    intro E hE
    show MvPolynomial.eval₂Hom evz (fun ij : parIdx lvl => E ij.1.1 ij.1.2) (parDet lvl I) = _
    rw [parDet, ← det_map (MvPolynomial.eval₂Hom evz
      (fun ij : parIdx lvl => E ij.1.1 ij.1.2)) (genParSrc lvl I), genParSrc_def,
      genPar_map_eval₂ lvl evz E hE]
  have hδzne : δz ≠ 0 := by
    intro h
    have h1 : MvPolynomial.eval
        (fun ij : parIdx lvl => (1 : Matrix (Fin n) (Fin n) K) ij.1.1 ij.1.2) δz = 1 := by
      rw [hδz, MvPolynomial.eval_map, hdetspec 1 isBlockUpper_one, Matrix.det_one]
    rw [h, map_zero] at h1
    exact zero_ne_one h1
  obtain ⟨v, hv⟩ : ∃ v : parIdx lvl → K, MvPolynomial.eval v (qz * δz) ≠ 0 := by
    by_contra hc
    push Not at hc
    exact (mul_ne_zero hqzne hδzne)
      (MvPolynomial.funext fun x => by rw [hc x, map_zero])
  have hvq : MvPolynomial.eval v qz ≠ 0 := fun h => hv (by rw [map_mul, h, zero_mul])
  have hvδ : MvPolynomial.eval v δz ≠ 0 := fun h => hv (by rw [map_mul, h, mul_zero])
  -- the conjugator
  refine ⟨genParVal lvl v, isBlockUpper_genParVal lvl v, ?_, ?_⟩
  · have hval : (fun ij : parIdx lvl => genParVal lvl v ij.1.1 ij.1.2) = v :=
      funext (genParVal_apply lvl v)
    have hdet : (genParVal lvl v).det = MvPolynomial.eval v δz := by
      rw [hδz, MvPolynomial.eval_map, ← hval,
        hdetspec _ (isBlockUpper_genParVal lvl v), hval]
    rw [hdet]
    exact isUnit_iff_ne_zero.mpr hvδ
  · have hval : (fun ij : parIdx lvl => genParVal lvl v ij.1.1 ij.1.2) = v :=
      funext (genParVal_apply lvl v)
    have hĀunit : IsUnit (genParVal lvl v).det := by
      have hdet : (genParVal lvl v).det = MvPolynomial.eval v δz := by
        rw [hδz, MvPolynomial.eval_map, ← hval,
          hdetspec _ (isBlockUpper_genParVal lvl v), hval]
      rw [hdet]
      exact isUnit_iff_ne_zero.mpr hvδ
    obtain ⟨ev, hevA, hev⟩ := exists_psi_specialisation lvl I Ψ evz (genParVal lvl v)
      (isBlockUpper_genParVal lvl v) hĀunit
    have hpsi : psiQuot I Ψ evz = polyMat Ψ z := rfl
    have hid : evz.comp (quotC I) = RingHom.id K := by
      refine RingHom.ext fun a => ?_
      show evz (Ideal.Quotient.mk I (MvPolynomial.C a)) = a
      show MvPolynomial.eval z (MvPolynomial.C a) = a
      simp
    have hgval : MvPolynomial.eval
        (fun ij : Fin n × Fin n =>
          ((genParVal lvl v)⁻¹ * polyMat Ψ z * genParVal lvl v) ij.1 ij.2) g
        = ev (psiHom lvl I Ψ g) := by
      rw [← RingHom.comp_apply, hev, hpsi, hid]
      rfl
    rw [hgval]
    intro hzero
    apply hvq
    have h1 : ev (psiHom lvl I Ψ g) * ev (algebraMap (parRing lvl I) (locRing lvl I)
        (y : parRing lvl I)) = ev (algebraMap (parRing lvl I) (locRing lvl I) q) := by
      rw [← map_mul, hq]
    rw [hzero, zero_mul, hevA] at h1
    rw [hqz, MvPolynomial.eval_map, ← hval]
    exact h1.symm

end Construction



/-! ### Points and arcs of `Z` -/

section Specialise

variable {K : Type u} [Field K] {n : ℕ} (lvl : Fin n → ℕ)
  (I : Ideal (MvPolynomial (SIIndex (Fin n)) K))
  (Ψ : Fin n × Fin n → MvPolynomial (SIIndex (Fin n)) K)

/-- Evaluation of the coordinate ring of the source at a point of `V(I)`. -/
noncomputable def evPt {z : SIIndex (Fin n) → K} (hz : z ∈ MvPolynomial.zeroLocus K I) :
    srcRing I →+* K :=
  Ideal.Quotient.lift I (MvPolynomial.eval z : MvPolynomial (SIIndex (Fin n)) K →+* K)
    (fun f hf => by
      have := hz f hf
      rwa [MvPolynomial.aeval_eq_eval] at this)

/-- Evaluation of the coordinate ring of the source along an arc of `V(I)`. -/
noncomputable def evArc {a : SIArc n K} (ha : a.InLocus I) :
    srcRing I →+* PowerSeries K :=
  Ideal.Quotient.lift I
    ((MvPolynomial.aeval a.coords : MvPolynomial (SIIndex (Fin n)) K →ₐ[K] PowerSeries K) :
      MvPolynomial (SIIndex (Fin n)) K →+* PowerSeries K) (fun f hf => ha f hf)

/-- A conjugate of `ψ(z)` by an invertible element of the parabolic is a point
of `Z`. -/
theorem mem_zeroLocus_psi_conj (_ : I.IsPrime) {z : SIIndex (Fin n) → K}
    (hz : z ∈ MvPolynomial.zeroLocus K I) {A : Matrix (Fin n) (Fin n) K}
    (hA : IsBlockUpper lvl A) (hu : IsUnit A.det) :
    (fun ij : Fin n × Fin n => (A⁻¹ * polyMat Ψ z * A) ij.1 ij.2)
      ∈ MvPolynomial.zeroLocus K (psiPrime lvl I Ψ) := by
  obtain ⟨ev, -, hev⟩ := exists_psi_specialisation lvl I Ψ (evPt I hz) A hA hu
  have hid : (evPt I hz).comp (quotC I) = RingHom.id K := by
    refine RingHom.ext fun x => ?_
    show MvPolynomial.eval z (MvPolynomial.C x) = x
    simp
  have hpsi : psiQuot I Ψ (evPt I hz) = polyMat Ψ z := rfl
  intro f hf
  rw [MvPolynomial.aeval_eq_eval]
  have : MvPolynomial.eval (fun ij : Fin n × Fin n => (A⁻¹ * polyMat Ψ z * A) ij.1 ij.2) f
      = ev (psiHom lvl I Ψ f) := by
    rw [← RingHom.comp_apply, hev, hpsi, hid]
    rfl
  rw [this, show psiHom lvl I Ψ f = 0 from hf, map_zero]

/-- A conjugate of `ψ ∘ a` by an invertible element of the parabolic over
`K⟦s⟧` is an arc of `Z`. -/
theorem arcInLocus_psi_conj (_ : I.IsPrime) {a : SIArc n K} (ha : a.InLocus I)
    {E : Matrix (Fin n) (Fin n) (PowerSeries K)} (hE : IsBlockUpper lvl E)
    (hu : IsUnit E.det) :
    ArcInLocus (psiPrime lvl I Ψ) (E⁻¹ * polyMatArc Ψ a * E) := by
  obtain ⟨ev, -, hev⟩ := exists_psi_specialisation lvl I Ψ (evArc I ha) E hE hu
  have hid : (evArc I ha).comp (quotC I) = algebraMap K (PowerSeries K) := by
    refine RingHom.ext fun x => ?_
    show (MvPolynomial.aeval a.coords) (MvPolynomial.C x) = _
    simp
  have hpsi : psiQuot I Ψ (evArc I ha) = polyMatArc Ψ a := rfl
  intro f hf
  have : MvPolynomial.aeval
      (fun ij : Fin n × Fin n => (E⁻¹ * polyMatArc Ψ a * E) ij.1 ij.2) f
      = ev (psiHom lvl I Ψ f) := by
    rw [← RingHom.comp_apply, hev, hpsi, hid]
    rfl
  rw [this, show psiHom lvl I Ψ f = 0 from hf, map_zero]

/-- The reduction of `ψ ∘ a` at the base point of the arc. -/
theorem matC_polyMatArc {a : SIArc n K} {z : SIIndex (Fin n) → K} (hb : a.base = siCoords.symm z) :
    matC (polyMatArc Ψ a) = polyMat Ψ z := by
  have hcomp : (PowerSeries.constantCoeff (R := K)).comp
      ((MvPolynomial.aeval a.coords : MvPolynomial (SIIndex (Fin n)) K →ₐ[K] PowerSeries K) :
        MvPolynomial (SIIndex (Fin n)) K →+* PowerSeries K) = MvPolynomial.eval z := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun i => ?_)
    · simp only [RingHom.comp_apply]
      show PowerSeries.constantCoeff ((MvPolynomial.aeval a.coords) (MvPolynomial.C c))
        = MvPolynomial.eval z (MvPolynomial.C c)
      simp
    · simp only [RingHom.comp_apply]
      show PowerSeries.constantCoeff ((MvPolynomial.aeval a.coords) (MvPolynomial.X i))
        = MvPolynomial.eval z (MvPolynomial.X i)
      rw [MvPolynomial.aeval_X, MvPolynomial.eval_X]
      have h1 := SIArc.siCoords_base a
      rw [hb, siCoords.apply_symm_apply] at h1
      exact (congrFun h1 i).symm
  ext i j
  show PowerSeries.constantCoeff ((MvPolynomial.aeval a.coords) (Ψ (i, j)))
    = MvPolynomial.eval z (Ψ (i, j))
  exact congrFun (congrArg (fun f : MvPolynomial (SIIndex (Fin n)) K →+* K => ⇑f) hcomp) (Ψ (i, j))

end Specialise

/-! ### The frame of an arc -/

section ArcFrame

variable {K : Type u} [Field K] {n : ℕ}

/-- The frame along an arc: the fixed conjugator `A` moved by the one-parameter
subgroup `1 + s D` of the parabolic. -/
noncomputable def arcFrame (D A : Matrix (Fin n) (Fin n) K) :
    Matrix (Fin n) (Fin n) (PowerSeries K) :=
  (1 + (PowerSeries.X : PowerSeries K) • D.map (PowerSeries.C : K →+* PowerSeries K))
    * A.map (PowerSeries.C : K →+* PowerSeries K)

theorem matC_arcFrame (D A : Matrix (Fin n) (Fin n) K) : matC (arcFrame D A) = A := by
  rw [arcFrame, matC_mul, matC_map_C]
  have h : matC (1 + (PowerSeries.X : PowerSeries K)
      • D.map (PowerSeries.C : K →+* PowerSeries K)) = 1 := by
    ext i j
    show PowerSeries.constantCoeff
      ((1 : Matrix (Fin n) (Fin n) (PowerSeries K)) i j
        + PowerSeries.X * (PowerSeries.C (D i j))) = _
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  rw [h, Matrix.one_mul]

theorem matD_arcFrame (D A : Matrix (Fin n) (Fin n) K) : matD (arcFrame D A) = D * A := by
  rw [arcFrame, matD_mul, matC_map_C, matD_map_C, Matrix.mul_zero, add_zero]
  have h : matD (1 + (PowerSeries.X : PowerSeries K)
      • D.map (PowerSeries.C : K →+* PowerSeries K)) = D := by
    ext i j
    show PowerSeries.coeff 1
      ((1 : Matrix (Fin n) (Fin n) (PowerSeries K)) i j
        + PowerSeries.X * (PowerSeries.C (D i j))) = _
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  rw [h]

theorem isBlockUpper_arcFrame {lvl : Fin n → ℕ} {D A : Matrix (Fin n) (Fin n) K}
    (hD : IsBlockUpper lvl D) (hA : IsBlockUpper lvl A) :
    IsBlockUpper lvl (arcFrame D A) :=
  ((isBlockUpper_one).add (hD.map (PowerSeries.C : K →+* PowerSeries K)).smul).mul
    (hA.map (PowerSeries.C : K →+* PowerSeries K))

theorem isUnit_det_arcFrame {D A : Matrix (Fin n) (Fin n) K} (hu : IsUnit A.det) :
    IsUnit (arcFrame D A).det := by
  rw [PowerSeries.isUnit_iff_constantCoeff]
  have h : PowerSeries.constantCoeff (arcFrame D A).det = A.det := by
    rw [← det_map (PowerSeries.constantCoeff (R := K)) (arcFrame D A)]
    show ((arcFrame D A).map (PowerSeries.constantCoeff (R := K))).det = A.det
    rw [show (arcFrame D A).map (PowerSeries.constantCoeff (R := K)) = matC (arcFrame D A) from rfl,
      matC_arcFrame]
  rw [h]
  exact hu

end ArcFrame

/-! ### The frame statement -/

section Adapted

variable {K : Type u} [Field K] {n : ℕ}

/-- **The adapted frame** of `thm:reduction` on a component `V(I)`, the one
input of `PsiMap` this file does not build (see the module docstring).

A coordinate flag (a monotone level function `lvl`), a tuple `Ψ` of
polynomials and, on a dense open `V(I) ∖ V(h₀)`, an invertible frame `cfr z`
such that

* `Ψ` takes values in the nilradical of the flag (`Ψ (i,j) ∈ I` when
  `lvl j ≤ lvl i`), so `ψ(z) := polyMat Ψ z` is strictly upper triangular;
* `ψ(z)` is the member at the marked point conjugated by the frame;
* the frame carries every fibre motion of the velocity of an arc `a` of `V` to
  the velocity of `ψ ∘ a`, up to a commutator with the parabolic — which is the
  exact ambiguity of `lem:local-model`(3). -/
structure AdaptedFrame (I : Ideal (MvPolynomial (SIIndex (Fin n)) K)) where
  /-- the level function of the coordinate flag -/
  lvl : Fin n → ℕ
  /-- the conjugate of the member, as a tuple of polynomials -/
  Ψ : Fin n × Fin n → MvPolynomial (SIIndex (Fin n)) K
  /-- the hypersurface off which the frame is defined -/
  h₀ : MvPolynomial (SIIndex (Fin n)) K
  /-- the frame -/
  cfr : (SIIndex (Fin n) → K) → (Matrix (Fin n) (Fin n) K)ˣ
  mono : Monotone lvl
  h₀_notMem : h₀ ∉ I
  /-- `Ψ` lies in the nilradical of the coordinate flag on `V(I)` -/
  strict : ∀ i j : Fin n, lvl j ≤ lvl i → Ψ (i, j) ∈ I
  /-- `ψ(z)` is the conjugate of the member at the marked point -/
  conj : ∀ z ∈ MvPolynomial.zeroLocus K I, MvPolynomial.eval z h₀ ≠ 0 →
    polyMat Ψ z
      = (↑(cfr z)⁻¹ : Matrix (Fin n) (Fin n) K) * siMember (siCoords.symm z)
          * (↑(cfr z) : Matrix (Fin n) (Fin n) K)
  /-- fibre motions are derivatives of `ψ` along arcs, up to the parabolic -/
  arcs : ∀ z ∈ MvPolynomial.zeroLocus K I, MvPolynomial.eval z h₀ ≠ 0 →
    ∀ (m : MarkedArc I z) (Y : Matrix (Fin n) (Fin n) K),
      SIFibreMotion (siCoords.symm z) m.a.vel m.Z Y →
      ∃ D : Matrix (Fin n) (Fin n) K, IsBlockUpper lvl D ∧
        (↑(cfr z)⁻¹ : Matrix (Fin n) (Fin n) K) * Y * (↑(cfr z) : Matrix (Fin n) (Fin n) K)
          = matD (polyMatArc Ψ m.a) + (polyMat Ψ z * D - D * polyMat Ψ z)

end Adapted

/-! ### The map `ψ` from the frame -/

section Assembly

variable {K : Type u} [Field K] {n : ℕ}

/-- **The `ψ`-images**, granted the adapted
frame: on a dense open of `V(I)` every point has a `ψ`-image in `Z ∖ V(g)`,
`Z = V(psiPrime)`.  The point of `Z` is the conjugate `A⁻¹ ψ(z) A` of the
member at the marked point by a generic element `A` of the parabolic, and the
arc of `Z` realising a fibre motion is the same conjugation applied to `ψ ∘ a`
with the conjugator moved by the one-parameter subgroup `1 + s D` of the
parabolic, `D` being the parabolic ambiguity of the fibre motion. -/
theorem exists_psiImage [Infinite K] {I : Ideal (MvPolynomial (SIIndex (Fin n)) K)}
    (hI : I.IsPrime) (F : AdaptedFrame I) {g : MvPolynomial (Fin n × Fin n) K}
    (hg : g ∉ psiPrime F.lvl I F.Ψ) :
    ∃ h ∉ I, ∀ z ∈ MvPolynomial.zeroLocus K I, MvPolynomial.eval z h ≠ 0 →
      Nonempty (PsiImage I (psiPrime F.lvl I F.Ψ) g z) := by
  classical
  obtain ⟨lvl, Ψ, h₀, cfr, hmono, hh₀, hΨI, hconj, harc⟩ := F
  obtain ⟨h₁, hh₁, hgen⟩ := exists_generic_conjugate lvl I Ψ hI hg
  refine ⟨h₁ * h₀, ?_, ?_⟩
  · intro hmem
    rcases hI.mem_or_mem hmem with h | h
    · exact hh₁ h
    · exact hh₀ h
  intro z hz hne
  rw [map_mul] at hne
  have hne₁ : MvPolynomial.eval z h₁ ≠ 0 := fun h => hne (by rw [h, zero_mul])
  have hne₀ : MvPolynomial.eval z h₀ ≠ 0 := fun h => hne (by rw [h, mul_zero])
  obtain ⟨A, hAb, hAu, hgne⟩ := hgen z hz hne₁
  have hpsi := hconj z hz hne₀
  -- the conjugator `c = (cfr z · A)⁻¹`
  have hAunit : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).mpr hAu
  have hAuval : (hAunit.unit : Matrix (Fin n) (Fin n) K) = A := hAunit.unit_spec
  have hAuinv : ((hAunit.unit⁻¹ : (Matrix (Fin n) (Fin n) K)ˣ) :
      Matrix (Fin n) (Fin n) K) = A⁻¹ := by
    rw [Matrix.coe_units_inv, hAuval]
  set c : (Matrix (Fin n) (Fin n) K)ˣ := (cfr z * hAunit.unit)⁻¹ with hcdef
  have hcval : (c : Matrix (Fin n) (Fin n) K)
      = A⁻¹ * (↑(cfr z)⁻¹ : Matrix (Fin n) (Fin n) K) := by
    rw [hcdef, _root_.mul_inv_rev, Units.val_mul, hAuinv]
  have hcinvval : ((c⁻¹ : (Matrix (Fin n) (Fin n) K)ˣ) : Matrix (Fin n) (Fin n) K)
      = (↑(cfr z) : Matrix (Fin n) (Fin n) K) * A := by
    rw [hcdef, inv_inv, Units.val_mul, hAuval]
  -- the point of `Z`
  have hmatCoords : matCoords.symm (fun ij : Fin n × Fin n => (A⁻¹ * polyMat Ψ z * A) ij.1 ij.2)
      = A⁻¹ * polyMat Ψ z * A := by
    ext i j
    rfl
  -- the arcs of `Z`
  have key : ∀ (a : SIArc n K), a.InLocus I → a.base = siCoords.symm z →
      ∀ D Y : Matrix (Fin n) (Fin n) K, IsBlockUpper lvl D →
      (↑(cfr z)⁻¹ : Matrix (Fin n) (Fin n) K) * Y * (↑(cfr z) : Matrix (Fin n) (Fin n) K)
          = matD (polyMatArc Ψ a) + (polyMat Ψ z * D - D * polyMat Ψ z) →
      NilArc (psiPrime lvl I Ψ)
        (fun ij : Fin n × Fin n => (A⁻¹ * polyMat Ψ z * A) ij.1 ij.2)
        (Height.Toolbox.matrixConjugationLinearEquiv K n c Y) := by
    intro a ha hb D Y hDb hD
    refine ⟨(arcFrame D A)⁻¹ * polyMatArc Ψ a * arcFrame D A,
      arcInLocus_psi_conj lvl I Ψ hI ha (isBlockUpper_arcFrame hDb hAb)
        (isUnit_det_arcFrame hAu), ?_, ?_⟩
    · rw [matC_conj (isUnit_det_arcFrame hAu), matC_arcFrame, matC_polyMatArc Ψ hb, hmatCoords]
    · rw [Height.Toolbox.matrixConjugationLinearEquiv_apply,
        matD_conj (isUnit_det_arcFrame hAu), matC_arcFrame, matD_arcFrame,
        matC_polyMatArc Ψ hb, Matrix.mul_assoc D A A⁻¹, Matrix.mul_nonsing_inv A hAu,
        Matrix.mul_one, hcval, hcinvval]
      rw [show matD (polyMatArc Ψ a) + polyMat Ψ z * D - D * polyMat Ψ z
          = matD (polyMatArc Ψ a) + (polyMat Ψ z * D - D * polyMat Ψ z) by abel, ← hD]
      noncomm_ring
  refine ⟨⟨fun ij : Fin n × Fin n => (A⁻¹ * polyMat Ψ z * A) ij.1 ij.2, c,
    mem_zeroLocus_psi_conj lvl I Ψ hI hz hAb hAu, hgne, ?_, ?_⟩⟩
  · rw [hmatCoords, Height.Toolbox.matrixConjugationLinearEquiv_apply, hcval, hcinvval, hpsi]
    noncomm_ring
  · intro m Y hY
    obtain ⟨D, hDb, hD⟩ := harc z hz hne₀ m Y hY
    exact ⟨key m.a m.inLocus m.base D Y hDb hD⟩

/-- **The map `ψ` from the adapted frame**: `Z = V(psiPrime)`, with the
`ψ`-images of `exists_psiImage`. -/
noncomputable def AdaptedFrame.toPsiMap [Infinite K] {I : Ideal (MvPolynomial (SIIndex (Fin n)) K)}
    (hI : I.IsPrime) (F : AdaptedFrame I) : PsiMap I where
  P := psiPrime F.lvl I F.Ψ
  prime := psiPrime_isPrime F.lvl I F.Ψ hI
  upper := isStrictlyUpper_of_mem_zeroLocus F.lvl I F.Ψ F.mono hI F.strict
  image := fun _ hg => exists_psiImage hI F hg

end Assembly

end Height.Chain
