import Height.Chain.Multidegree
import Height.Graded.Cech
import Height.Chain.Reduction
import Height.Pencil.Arcs

/-!
# Polynomiality of the pencil conditions

The loci of `Chain/Incidence.lean` are cut out by conditions on the *ranks* of
matrices whose entries are polynomial functions of the entries of `(N, M)`.
This file builds the dictionary:

* **Rank loci** (`isConstructible_rank_eq`).  For a matrix `E` over
  `MvPolynomial ι K`, the locus `{x | rank (E(x)) = r}` is constructible:
  `rank ≤ r` is the vanishing of all `(r+1)`-minors (closed) and `r ≤ rank` is
  the nonvanishing of some `r`-minor (a finite union of principal opens).
* **The universal pencil** (`univA`, `univB`, `univPencil`).  Over
  `R = MvPolynomial (PairIndex (Fin n)) K` the pair of matrices with independent
  indeterminate entries; specialising at `x` recovers `pairCoords.symm x`.  Every
  polynomial built from the universal pencil therefore *is* a polynomial
  function of the entries.
-/

namespace Height.Chain

open Height.Pencil

open Matrix MvPolynomial Height.Geometry

universe u

/-! ### Closed, locally closed and constructible loci from polynomial families -/

section Loci

variable {K : Type u} [Field K] {ι : Type}

/-- A principal open is locally closed. -/
theorem isLocClosed_principalOpen (g : MvPolynomial ι K) :
    IsLocClosed {x : ι → K | aeval x g ≠ 0} := by
  refine ⟨Set.univ, g, Set.eq_univ_of_univ_subset (subset_zclosure _), ?_⟩
  rw [Set.univ_inter]

/-- The common zero set of a family of polynomials is locally closed. -/
theorem isLocClosed_zeros (S : Set (MvPolynomial ι K)) :
    IsLocClosed {x : ι → K | ∀ q ∈ S, aeval x q = 0} :=
  IsLocClosed.of_zclosure (zclosure_zeros S)

/-- The same, for a family indexed by a type. -/
theorem isLocClosed_zeros_family {J : Type*} (Q : J → MvPolynomial ι K) :
    IsLocClosed {x : ι → K | ∀ j, aeval x (Q j) = 0} := by
  have hset : {x : ι → K | ∀ j, aeval x (Q j) = 0}
      = {x : ι → K | ∀ q ∈ Set.range Q, aeval x q = 0} := by
    refine Set.Subset.antisymm (fun x hx => ?_) (fun x hx => ?_)
    · rintro _ ⟨j, rfl⟩
      exact hx j
    · exact fun j => hx _ ⟨j, rfl⟩
  rw [hset]
  exact isLocClosed_zeros _

end Loci

/-! ### Rank loci of a matrix of polynomials -/

section RankLoci

variable {K : Type u} [Field K] {ι : Type} {a b : ℕ}

/-- The specialisation of a matrix of polynomials at a point. -/
noncomputable def specMat (E : Matrix (Fin a) (Fin b) (MvPolynomial ι K)) (x : ι → K) :
    Matrix (Fin a) (Fin b) K :=
  E.map (MvPolynomial.aeval x)

/-- Minors commute with the entrywise application of a ring homomorphism. -/
theorem det_submatrix_map_rect {R S : Type*} [CommRing R] [CommRing S] {s : ℕ}
    (φ : R →+* S) (A : Matrix (Fin a) (Fin b) R) (f : Fin s → Fin a) (g : Fin s → Fin b) :
    ((A.map φ).submatrix f g).det = φ ((A.submatrix f g).det) := by
  rw [Matrix.submatrix_map]
  exact (RingHom.map_det φ (A.submatrix f g)).symm

theorem det_submatrix_specMat {s : ℕ} (E : Matrix (Fin a) (Fin b) (MvPolynomial ι K))
    (x : ι → K) (f : Fin s → Fin a) (g : Fin s → Fin b) :
    ((specMat E x).submatrix f g).det = aeval x ((E.submatrix f g).det) :=
  det_submatrix_map_rect ((MvPolynomial.aeval x : MvPolynomial ι K →ₐ[K] K).toRingHom) E f g

/-- `rank M ≤ r` is the vanishing of every `(r+1)`-minor. -/
theorem rank_le_iff_minors {F : Type*} [Field F] (M : Matrix (Fin a) (Fin b) F) (r : ℕ) :
    M.rank ≤ r ↔ ∀ (f : Fin (r + 1) → Fin a) (g : Fin (r + 1) → Fin b),
      (M.submatrix f g).det = 0 := by
  constructor
  · intro h f g
    by_contra hdet
    have := Height.Toolbox.le_rank_of_submatrix_det_ne_zero M f g hdet
    omega
  · intro h
    by_contra hcon
    obtain ⟨f, g, hfg⟩ :=
      Height.Toolbox.exists_submatrix_det_ne_zero (k := r + 1) M (by omega)
    exact hfg (h f g)

/-- The locus where the rank drops is Zariski closed. -/
theorem isLocClosed_rank_le (E : Matrix (Fin a) (Fin b) (MvPolynomial ι K)) (r : ℕ) :
    IsLocClosed {x : ι → K | (specMat E x).rank ≤ r} := by
  have hset : {x : ι → K | (specMat E x).rank ≤ r}
      = {x : ι → K | ∀ fg : (Fin (r + 1) → Fin a) × (Fin (r + 1) → Fin b),
          aeval x ((E.submatrix fg.1 fg.2).det) = 0} := by
    refine Set.Subset.antisymm (fun x hx => ?_) (fun x hx => ?_)
    · intro fg
      rw [← det_submatrix_specMat]
      exact (rank_le_iff_minors _ r).1 hx fg.1 fg.2
    · refine (rank_le_iff_minors _ r).2 fun f g => ?_
      rw [det_submatrix_specMat]
      exact hx (f, g)
  rw [hset]
  exact isLocClosed_zeros_family _

/-- **The rank locus of a polynomial matrix is constructible.** -/
theorem isConstructible_rank_eq (E : Matrix (Fin a) (Fin b) (MvPolynomial ι K)) (r : ℕ) :
    IsAffineConstructible {x : ι → K | (specMat E x).rank = r} := by
  classical
  refine ⟨(Fin r → Fin a) × (Fin r → Fin b), inferInstance,
    fun fg => {x : ι → K | (specMat E x).rank ≤ r} ∩
      {x : ι → K | aeval x ((E.submatrix fg.1 fg.2).det) ≠ 0}, fun fg => ?_, ?_⟩
  · exact (isLocClosed_rank_le E r).inter (isLocClosed_principalOpen _)
  · refine Set.Subset.antisymm (fun x hx => ?_) (fun x hx => ?_)
    · have hr : (specMat E x).rank = r := hx
      obtain ⟨f, g, hfg⟩ :=
        Height.Toolbox.exists_submatrix_det_ne_zero (k := r) (specMat E x) (le_of_eq hr.symm)
      refine Set.mem_iUnion.2 ⟨(f, g), le_of_eq hr, ?_⟩
      show aeval x ((E.submatrix f g).det) ≠ 0
      rw [← det_submatrix_specMat]
      exact hfg
    · obtain ⟨fg, hle, hne⟩ := Set.mem_iUnion.1 hx
      have hge : r ≤ (specMat E x).rank := by
        refine Height.Toolbox.le_rank_of_submatrix_det_ne_zero _ fg.1 fg.2 ?_
        rw [det_submatrix_specMat]
        exact hne
      exact le_antisymm hle hge

end RankLoci

/-! ### The universal pair of matrices -/

section Universal

variable {K : Type u} [Field K] {n : ℕ}

end Universal

/-! ### The universal pencil in the parameter -/

section UnivPencil

variable {K : Type u} [Field K] {n : ℕ}

/-- Specialisation of a polynomial ring at a point, as a ring map. -/
noncomputable def specRing {ι : Type*} (x : ι → K) : MvPolynomial ι K →+* K :=
  (MvPolynomial.aeval x : MvPolynomial ι K →ₐ[K] K).toRingHom

@[simp] theorem specRing_apply {ι : Type*} (x : ι → K) (q : MvPolynomial ι K) :
    specRing x q = MvPolynomial.aeval x q := rfl

@[simp] theorem pairOf_specRing (x : PairIndex (Fin n) → K) :
    pairCoords.symm (fun i => specRing x (MvPolynomial.X i : MvPolynomial (PairIndex (Fin n)) K))
      = pairCoords.symm x := by
  simp

/-- The pencil `A + t B` of a family `c` of coordinates in a commutative ring. -/
noncomputable def cPencilPoly {R : Type*} [CommRing R] (c : PairIndex (Fin n) → R) :
    Matrix (Fin n) (Fin n) (Polynomial R) :=
  (pairCoords.symm c).1.map Polynomial.C +
    (Polynomial.X : Polynomial R) • (pairCoords.symm c).2.map Polynomial.C

theorem cPencilPoly_map {R S : Type*} [CommRing R] [Field S] (θ : R →+* S)
    (c : PairIndex (Fin n) → R) :
    (cPencilPoly c).map (Polynomial.map θ)
      = pencilPoly (pairCoords.symm fun i => θ (c i)).1 (pairCoords.symm fun i => θ (c i)).2 := by
  ext i j
  simp [cPencilPoly, pencilPoly, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]

theorem cPencilPoly_pow_map {R S : Type*} [CommRing R] [Field S] (θ : R →+* S)
    (c : PairIndex (Fin n) → R) (k : ℕ) :
    ((cPencilPoly c) ^ k).map (Polynomial.map θ)
      = pencilPoly (pairCoords.symm fun i => θ (c i)).1 (pairCoords.symm fun i => θ (c i)).2 ^ k := by
  have h := map_pow ((Polynomial.mapRingHom θ).mapMatrix (m := Fin n)) (cPencilPoly c) k
  rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply] at h
  rw [show ((Polynomial.mapRingHom θ : Polynomial R →+* Polynomial S) : _ → _)
    = Polynomial.map θ from rfl] at h
  rw [h, cPencilPoly_map]

/-- The `r × r` minor of the `k`-th power of the pencil of `c`. -/
noncomputable def cMinor {R : Type*} [CommRing R] (c : PairIndex (Fin n) → R) {r : ℕ}
    (f g : Fin r → Fin n) (k : ℕ) : Polynomial R :=
  (((cPencilPoly c) ^ k).submatrix f g).det

/-- The universal `r × r` minor of the `k`-th power of the pencil. -/
noncomputable abbrev univMinor (K : Type u) [Field K] (n : ℕ) {r : ℕ}
    (f g : Fin r → Fin n) (k : ℕ) : Polynomial (MvPolynomial (PairIndex (Fin n)) K) :=
  cMinor (MvPolynomial.X : PairIndex (Fin n) → MvPolynomial (PairIndex (Fin n)) K) f g k

theorem cMinor_map {R S : Type*} [CommRing R] [Field S] (θ : R →+* S)
    (c : PairIndex (Fin n) → R) {r : ℕ} (f g : Fin r → Fin n) (k : ℕ) :
    Polynomial.map θ (cMinor c f g k)
      = ((pencilPoly (pairCoords.symm fun i => θ (c i)).1 (pairCoords.symm fun i => θ (c i)).2 ^ k).submatrix
          f g).det := by
  have h := det_submatrix_map_rect (Polynomial.mapRingHom θ) ((cPencilPoly c) ^ k) f g
  rw [show ((Polynomial.mapRingHom θ : Polynomial R →+* Polynomial S) : _ → _)
    = Polynomial.map θ from rfl, cPencilPoly_pow_map] at h
  exact h.symm

/-- A specialised polynomial is nonzero exactly when one of its finitely many
coefficients survives. -/
theorem map_ne_zero_iff_coeff {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (q : Polynomial R) :
    Polynomial.map φ q ≠ 0 ↔ ∃ i ≤ q.natDegree, φ (q.coeff i) ≠ 0 := by
  constructor
  · intro h
    by_contra hcon
    refine h ((Polynomial.ext_iff_natDegree_le (n := q.natDegree)
      Polynomial.natDegree_map_le (by simp)).2 fun i hi => ?_)
    rw [Polynomial.coeff_map, Polynomial.coeff_zero]
    by_contra hne
    exact hcon ⟨i, hi, hne⟩
  · rintro ⟨i, -, hi⟩ h
    exact hi (by rw [← Polynomial.coeff_map, h, Polynomial.coeff_zero])

/-- A polynomial specialises to zero exactly when every coefficient does. -/
theorem map_eq_zero_iff_coeff {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (q : Polynomial R) :
    Polynomial.map φ q = 0 ↔ ∀ i, φ (q.coeff i) = 0 := by
  rw [Polynomial.ext_iff]
  simp [Polynomial.coeff_map]

/-- **`PencilRankGe` is a finite disjunction of inequations** in the
coordinates, along any specialisation. -/
theorem pencilRankGe_map_iff_coeff {R S : Type*} [CommRing R] [Field S] (θ : R →+* S)
    (c : PairIndex (Fin n) → R) (k r : ℕ) :
    PencilRankGe (pairCoords.symm fun i => θ (c i)).1 (pairCoords.symm fun i => θ (c i)).2 k r ↔
      ∃ (f g : Fin r → Fin n) (i : ℕ), i ≤ (cMinor c f g k).natDegree ∧
        θ ((cMinor c f g k).coeff i) ≠ 0 := by
  constructor
  · rintro ⟨f, g, hfg⟩
    rw [← cMinor_map θ c f g k] at hfg
    obtain ⟨i, hi, hne⟩ := (map_ne_zero_iff_coeff θ _).1 hfg
    exact ⟨f, g, i, hi, hne⟩
  · rintro ⟨f, g, i, hi, hne⟩
    refine ⟨f, g, ?_⟩
    rw [← cMinor_map θ c f g k]
    exact (map_ne_zero_iff_coeff θ _).2 ⟨i, hi, hne⟩

/-- Failure of `PencilRankGe` is the vanishing of every coefficient of every
minor, along any specialisation. -/
theorem not_pencilRankGe_map_iff_coeff {R S : Type*} [CommRing R] [Field S] (θ : R →+* S)
    (c : PairIndex (Fin n) → R) (k r : ℕ) :
    ¬ PencilRankGe (pairCoords.symm fun i => θ (c i)).1 (pairCoords.symm fun i => θ (c i)).2 k r ↔
      ∀ (f g : Fin r → Fin n) (i : ℕ), θ ((cMinor c f g k).coeff i) = 0 := by
  constructor
  · intro hx f g i
    have h0 : Polynomial.map θ (cMinor c f g k) = 0 := by
      by_contra hne
      refine hx ⟨f, g, ?_⟩
      rw [← cMinor_map θ c f g k]
      exact hne
    exact (map_eq_zero_iff_coeff θ _).1 h0 i
  · rintro hx ⟨f, g, hfg⟩
    rw [← cMinor_map θ c f g k] at hfg
    exact hfg ((map_eq_zero_iff_coeff θ _).2 (fun i => hx f g i))

/-- The point form of `pencilRankGe_map_iff_coeff`. -/
theorem pencilRankGe_iff_coeff (x : PairIndex (Fin n) → K) (k r : ℕ) :
    PencilRankGe (pairCoords.symm x).1 (pairCoords.symm x).2 k r ↔
      ∃ (f g : Fin r → Fin n) (i : ℕ), i ≤ (univMinor K n f g k).natDegree ∧
        MvPolynomial.aeval x ((univMinor K n f g k).coeff i) ≠ 0 := by
  have h := pencilRankGe_map_iff_coeff (specRing x)
    (MvPolynomial.X : PairIndex (Fin n) → MvPolynomial (PairIndex (Fin n)) K) k r
  rw [pairOf_specRing] at h
  exact h

/-- The point form of `not_pencilRankGe_map_iff_coeff`. -/
theorem not_pencilRankGe_iff_coeff (x : PairIndex (Fin n) → K) (k r : ℕ) :
    ¬ PencilRankGe (pairCoords.symm x).1 (pairCoords.symm x).2 k r ↔
      ∀ (f g : Fin r → Fin n) (i : ℕ),
        MvPolynomial.aeval x ((univMinor K n f g k).coeff i) = 0 := by
  have h := not_pencilRankGe_map_iff_coeff (specRing x)
    (MvPolynomial.X : PairIndex (Fin n) → MvPolynomial (PairIndex (Fin n)) K) k r
  rw [pairOf_specRing] at h
  exact h

/-- **The locus where the generic rank is at least `r` is constructible.** -/
theorem isConstructible_pencilRankGe (k r : ℕ) :
    IsAffineConstructible {x : PairIndex (Fin n) → K | PencilRankGe (pairCoords.symm x).1 (pairCoords.symm x).2 k r} := by
  classical
  refine ⟨(fg : (Fin r → Fin n) × (Fin r → Fin n)) ×
      Fin ((univMinor K n fg.1 fg.2 k).natDegree + 1), inferInstance,
    fun a => {x : PairIndex (Fin n) → K |
      MvPolynomial.aeval x ((univMinor K n a.1.1 a.1.2 k).coeff (a.2 : ℕ)) ≠ 0},
    fun a => isLocClosed_principalOpen _, ?_⟩
  refine Set.Subset.antisymm (fun x hx => ?_) (fun x hx => ?_)
  · obtain ⟨f, g, i, hi, hne⟩ := (pencilRankGe_iff_coeff x k r).1 hx
    exact Set.mem_iUnion.2 ⟨⟨(f, g), ⟨i, Nat.lt_succ_of_le hi⟩⟩, hne⟩
  · obtain ⟨⟨⟨f, g⟩, ⟨i, hi⟩⟩, hne⟩ := Set.mem_iUnion.1 hx
    exact (pencilRankGe_iff_coeff x k r).2 ⟨f, g, i, Nat.lt_succ_iff.1 hi, hne⟩

/-- **The locus where the generic rank is less than `r` is Zariski closed.** -/
theorem isLocClosed_not_pencilRankGe (k r : ℕ) :
    IsLocClosed {x : PairIndex (Fin n) → K | ¬ PencilRankGe (pairCoords.symm x).1 (pairCoords.symm x).2 k r} := by
  classical
  have hset : {x : PairIndex (Fin n) → K | ¬ PencilRankGe (pairCoords.symm x).1 (pairCoords.symm x).2 k r}
      = {x : PairIndex (Fin n) → K | ∀ a : ((Fin r → Fin n) × (Fin r → Fin n)) × ℕ,
          MvPolynomial.aeval x ((univMinor K n a.1.1 a.1.2 k).coeff a.2) = 0} := by
    refine Set.Subset.antisymm (fun x hx a => ?_) (fun x hx => ?_)
    · exact (not_pencilRankGe_iff_coeff x k r).1 hx a.1.1 a.1.2 a.2
    · exact (not_pencilRankGe_iff_coeff x k r).2 fun f g i => hx ((f, g), i)
  rw [hset]
  exact isLocClosed_zeros_family _

/-- **The generic-type locus is constructible** (`genericType_iff`). -/
theorem isConstructible_genericType [Infinite K] (τ : Nat.Partition n) :
    IsAffineConstructible {x : PairIndex (Fin n) → K | GenericType (pairCoords.symm x).1 (pairCoords.symm x).2 τ} := by
  classical
  have hset : {x : PairIndex (Fin n) → K | GenericType (pairCoords.symm x).1 (pairCoords.symm x).2 τ}
      = ⋂ j : Fin n, ({x : PairIndex (Fin n) → K |
            PencilRankGe (pairCoords.symm x).1 (pairCoords.symm x).2 ((j : ℕ) + 1)
              (n - mk τ ((j : ℕ) + 1))} ∩
          {x : PairIndex (Fin n) → K |
            ¬ PencilRankGe (pairCoords.symm x).1 (pairCoords.symm x).2 ((j : ℕ) + 1)
              (n - mk τ ((j : ℕ) + 1) + 1)}) := by
    refine Set.Subset.antisymm (fun x hx => Set.mem_iInter.2 fun j => ?_) (fun x hx => ?_)
    · exact genericType_iff.1 hx ((j : ℕ) + 1) (by omega) (by omega)
    · refine genericType_iff.2 fun k hk1 hkn => ?_
      have h := Set.mem_iInter.1 hx ⟨k - 1, by omega⟩
      simpa [Nat.sub_add_cancel hk1] using h
  rw [hset]
  exact IsAffineConstructible.iInter fun j =>
    IsAffineConstructible.inter (isConstructible_pencilRankGe _ _)
      (isLocClosed_not_pencilRankGe _ _).isConstructible

end UnivPencil

/-! ### The Sylvester matrix of a graded matrix -/

section Sylvester

open Height.Graded

/-- The matrix of "multiply by `E`", from degree `e` to degree `e + k`, in
monomial coordinates. -/
noncomputable def sylMat {R : Type*} [CommRing R] {n : ℕ}
    (E : Matrix (Fin n) (Fin n) (MvPolynomial (Fin 2) R)) (k e : ℕ) :
    Matrix (Fin n × Fin (e + k + 1)) (Fin n × Fin (e + 1)) R :=
  Matrix.of fun ib ja =>
    if (ja.2 : ℕ) ≤ (ib.2 : ℕ) ∧ (ib.2 : ℕ) ≤ (ja.2 : ℕ) + k then
      (E ib.1 ja.1).coeff
        (monExp (k - ((ib.2 : ℕ) - (ja.2 : ℕ))) ((ib.2 : ℕ) - (ja.2 : ℕ)))
    else 0

/-- Reordering a triple sum. -/
theorem sum_swap₃ {α : Type*} [AddCommMonoid α] {p q r : ℕ}
    (T : Fin p → Fin q → Fin r → α) :
    ∑ j, ∑ a, ∑ b, T j a b = ∑ b, ∑ j, ∑ a, T j a b := by
  rw [Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => Finset.sum_comm]
  exact Finset.sum_comm

variable {K : Type u} [Field K] {n : ℕ}

/-- **The Sylvester matrix computes the pencil action in monomial
coordinates.** -/
theorem mulVec_ofCoordVec (N M : Matrix (Fin n) (Fin n) K) (k e : ℕ)
    (v : Fin n × Fin (e + 1) → K) :
    (pencil N M ^ k) *ᵥ (ofCoordVec K (Fin n) e v)
      = ofCoordVec K (Fin n) (e + k) (sylMat (pencil N M ^ k) k e *ᵥ v) := by
  classical
  funext i
  rw [Matrix.mulVec_apply_eq_sum, ofCoordVec_apply]
  have hexp : ∀ j : Fin n, (pencil N M ^ k) i j * ofCoordVec K (Fin n) e v j
      = ∑ a : Fin (e + 1), ∑ b : Fin (e + k + 1),
          (sylMat (pencil N M ^ k) k e (i, b) (j, a) * v (j, a))
            • gmon K (e + k) (b : ℕ) := by
    intro j
    rw [ofCoordVec_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [mul_smul_comm, mul_gmon (Nat.lt_succ_iff.1 a.2) (Height.Pencil.pencil_pow_mem_Bpiece N M k i j),
      Finset.smul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [smul_smul, mul_comm]
    rfl
  rw [Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => hexp j, sum_swap₃]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Matrix.mulVec_apply_eq_sum, Fintype.sum_prod_type, Finset.sum_smul]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_smul.symm

/-- The kernel piece is the image of the Sylvester kernel. -/
theorem map_ofCoordVec_ker (N M : Matrix (Fin n) (Fin n) K) (k e : ℕ) :
    Submodule.map (ofCoordVec K (Fin n) e)
        (LinearMap.ker (sylMat (pencil N M ^ k) k e).mulVecLin)
      = kerPiece N M k e := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨v, hv, rfl⟩
    refine ⟨?_, ofCoordVec_mem v⟩
    show (pencil N M ^ k) *ᵥ (ofCoordVec K (Fin n) e v) = 0
    rw [mulVec_ofCoordVec N M k e v, show (sylMat (pencil N M ^ k) k e *ᵥ v) = 0 from hv,
      map_zero]
  · rintro F ⟨hker, hpiece⟩
    refine ⟨coordVec K (Fin n) e F, ?_, ofCoordVec_coordVec hpiece⟩
    show (sylMat (pencil N M ^ k) k e) *ᵥ (coordVec K (Fin n) e F) = 0
    refine ofCoordVec_injective (K := K) (Fin n) (e + k) ?_
    rw [← mulVec_ofCoordVec N M k e (coordVec K (Fin n) e F), ofCoordVec_coordVec hpiece, map_zero]
    exact hker

/-- **Rank–nullity for the kernel piece.** -/
theorem finrank_kerPiece_add_rank (N M : Matrix (Fin n) (Fin n) K) (k e : ℕ) :
    Module.finrank K (kerPiece N M k e)
        + Matrix.rank (sylMat (pencil N M ^ k) k e)
      = n * (e + 1) := by
  classical
  set S := sylMat (pencil N M ^ k) k e with hS
  have hrn := LinearMap.finrank_range_add_finrank_ker S.mulVecLin
  have hdim : Module.finrank K (Fin n × Fin (e + 1) → K) = n * (e + 1) := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
  rw [hdim] at hrn
  have hker : Module.finrank K (LinearMap.ker S.mulVecLin)
      = Module.finrank K (kerPiece N M k e) := by
    rw [← map_ofCoordVec_ker N M k e]
    exact LinearEquiv.finrank_eq
      (Submodule.equivMapOfInjective (ofCoordVec K (Fin n) e) (ofCoordVec_injective (Fin n) e) _)
  have hrank : Matrix.rank S = Module.finrank K (LinearMap.range S.mulVecLin) := rfl
  rw [hrank, ← hker]
  omega

end Sylvester

/-! ### The universal graded pencil -/

section UnivGraded

variable {K : Type u} [Field K] {n : ℕ}

/-- A matrix specialises to zero exactly when every coefficient of every entry
does. -/
theorem mvMap_eq_zero_iff_coeff {R S : Type*} [CommRing R] [CommRing S] {σ : Type*}
    (φ : R →+* S) (q : MvPolynomial σ R) :
    MvPolynomial.map φ q = 0 ↔ ∀ m, φ (q.coeff m) = 0 := by
  constructor
  · intro h m
    rw [← MvPolynomial.coeff_map, h]
    simp
  · intro h
    ext m
    rw [MvPolynomial.coeff_map, h m]
    simp

/-- The graded pencil `μ A + ν B` of a family `c` of coordinates. -/
noncomputable def cGrPencil {R : Type*} [CommRing R] (c : PairIndex (Fin n) → R) :
    Matrix (Fin n) (Fin n) (MvPolynomial (Fin 2) R) :=
  Matrix.of fun i j =>
    MvPolynomial.C ((pairCoords.symm c).1 i j) * MvPolynomial.X 0
      + MvPolynomial.C ((pairCoords.symm c).2 i j) * MvPolynomial.X 1

/-- The universal pencil `μ A + ν B` over the coordinate ring of pairs. -/
noncomputable abbrev univGrPencil (K : Type u) [Field K] (n : ℕ) :
    Matrix (Fin n) (Fin n) (MvPolynomial (Fin 2) (MvPolynomial (PairIndex (Fin n)) K)) :=
  cGrPencil (MvPolynomial.X : PairIndex (Fin n) → MvPolynomial (PairIndex (Fin n)) K)

theorem cGrPencil_map {R S : Type*} [CommRing R] [Field S] (θ : R →+* S)
    (c : PairIndex (Fin n) → R) :
    (cGrPencil c).map (MvPolynomial.map θ)
      = pencil (pairCoords.symm fun i => θ (c i)).1 (pairCoords.symm fun i => θ (c i)).2 := by
  ext i j
  simp [cGrPencil, pencil, Height.Graded.mu, Height.Graded.nu]

theorem cGrPencil_pow_map {R S : Type*} [CommRing R] [Field S] (θ : R →+* S)
    (c : PairIndex (Fin n) → R) (k : ℕ) :
    ((cGrPencil c) ^ k).map (MvPolynomial.map θ)
      = pencil (pairCoords.symm fun i => θ (c i)).1 (pairCoords.symm fun i => θ (c i)).2 ^ k := by
  have h := map_pow ((MvPolynomial.map θ :
      MvPolynomial (Fin 2) R →+* MvPolynomial (Fin 2) S).mapMatrix
      (m := Fin n)) (cGrPencil c) k
  rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply] at h
  rw [h, cGrPencil_map]

theorem sylMat_map {R S : Type*} [CommRing R] [Field S] (θ : R →+* S)
    (c : PairIndex (Fin n) → R) (k e : ℕ) :
    (sylMat (cGrPencil c ^ k) k e).map θ
      = sylMat (pencil (pairCoords.symm fun i => θ (c i)).1 (pairCoords.symm fun i => θ (c i)).2 ^ k) k e := by
  ext ib ja
  rw [Matrix.map_apply, sylMat, sylMat, Matrix.of_apply, Matrix.of_apply]
  by_cases h : (ja.2 : ℕ) ≤ (ib.2 : ℕ) ∧ (ib.2 : ℕ) ≤ (ja.2 : ℕ) + k
  · rw [ite_eq_left h, ite_eq_left h, ← cGrPencil_pow_map θ c k, Matrix.map_apply,
      MvPolynomial.coeff_map]
  · rw [ite_eq_right h, ite_eq_right h, map_zero]

/-- The point form of `cGrPencil_pow_map`. -/
theorem pencil_pow_specRing (x : PairIndex (Fin n) → K) (k : ℕ) :
    ((univGrPencil K n) ^ k).map (MvPolynomial.map (specRing x))
      = pencil (pairCoords.symm x).1 (pairCoords.symm x).2 ^ k := by
  have h := cGrPencil_pow_map (specRing x)
    (MvPolynomial.X : PairIndex (Fin n) → MvPolynomial (PairIndex (Fin n)) K) k
  rw [pairOf_specRing] at h
  exact h

/-- The point form of `sylMat_map`. -/
theorem sylMat_specRing (x : PairIndex (Fin n) → K) (k e : ℕ) :
    (sylMat (univGrPencil K n ^ k) k e).map (MvPolynomial.aeval x)
      = sylMat (pencil (pairCoords.symm x).1 (pairCoords.symm x).2 ^ k) k e := by
  have h := sylMat_map (specRing x)
    (MvPolynomial.X : PairIndex (Fin n) → MvPolynomial (PairIndex (Fin n)) K) k e
  rw [pairOf_specRing] at h
  exact h

end UnivGraded

/-! ### Rank loci for matrices indexed by arbitrary finite types -/

section RankAny

variable {K : Type u} [Field K] {ι : Type}

theorem isConstructible_rank_eq_any {ρ σ : Type} [Fintype ρ] [Fintype σ]
    (E : Matrix ρ σ (MvPolynomial ι K)) (r : ℕ) :
    IsAffineConstructible {x : ι → K | (E.map (MvPolynomial.aeval x)).rank = r} := by
  classical
  have hrk : ∀ x : ι → K,
      (specMat (E.submatrix (Fintype.equivFin ρ).symm (Fintype.equivFin σ).symm) x).rank
        = (E.map (MvPolynomial.aeval x)).rank := by
    intro x
    show (((E.submatrix (Fintype.equivFin ρ).symm (Fintype.equivFin σ).symm)).map
      (MvPolynomial.aeval x)).rank = _
    rw [← Matrix.submatrix_map]
    exact Matrix.rank_submatrix _ _ _
  have hset : {x : ι → K | (E.map (MvPolynomial.aeval x)).rank = r}
      = {x : ι → K |
          (specMat (E.submatrix (Fintype.equivFin ρ).symm (Fintype.equivFin σ).symm) x).rank
            = r} := by
    refine Set.Subset.antisymm (fun x hx => ?_) (fun x hx => ?_)
    · exact (hrk x).trans hx
    · exact (hrk x).symm.trans hx
  rw [hset]
  exact isConstructible_rank_eq _ r

end RankAny

/-! ### The kernel-piece dimension is a constructible condition -/

section KerPieceLocus

variable {K : Type u} [Field K] {n : ℕ}

/-- **The Hilbert value of the kernel flag cuts out a constructible set.** -/
theorem isConstructible_finrank_kerPiece (k e c t : ℕ) :
    IsAffineConstructible {x : PairIndex (Fin n) → K |
      Module.finrank K (kerPiece (pairCoords.symm x).1 (pairCoords.symm x).2 k e) + c = t} := by
  classical
  by_cases hct : c ≤ t ∧ t ≤ n * (e + 1) + c
  · have hset : {x : PairIndex (Fin n) → K |
        Module.finrank K (kerPiece (pairCoords.symm x).1 (pairCoords.symm x).2 k e) + c = t}
        = {x : PairIndex (Fin n) → K |
            ((sylMat (univGrPencil K n ^ k) k e).map (MvPolynomial.aeval x)).rank
              = n * (e + 1) - (t - c) } := by
      refine Set.Subset.antisymm (fun x hx => ?_) (fun x hx => ?_) <;>
        · have hrn := finrank_kerPiece_add_rank (pairCoords.symm x).1 (pairCoords.symm x).2 k e
          rw [Set.mem_ofPred_eq] at hx ⊢
          rw [sylMat_specRing] at *
          omega
    rw [hset]
    exact isConstructible_rank_eq_any _ _
  · have hset : {x : PairIndex (Fin n) → K |
        Module.finrank K (kerPiece (pairCoords.symm x).1 (pairCoords.symm x).2 k e) + c = t} = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.2 fun x hx => ?_
      have hrn := finrank_kerPiece_add_rank (pairCoords.symm x).1 (pairCoords.symm x).2 k e
      rw [Set.mem_ofPred_eq] at hx
      omega
    rw [hset]
    exact IsAffineConstructible.empty

end KerPieceLocus

/-! ### The pencil stratum is constructible -/

section PencilLocus

open Height.Steenrod

variable {K : Type u} [Field K] {n : ℕ}

/-- Over an infinite field a pencil is nilpotent exactly when its `n`-th power
vanishes over `K[μ, ν]`. -/
theorem nilpotentPencil_iff_pow [Infinite K] (A B : Matrix (Fin n) (Fin n) K) :
    NilpotentPencil A B ↔ pencil A B ^ n = 0 := by
  refine ⟨pencil_pow_eq_zero_of_nilpotentPencil, fun h s t => ⟨n, ?_⟩⟩
  have h1 : (pencil A B ^ n).map (MvPolynomial.eval ![s, t])
      = ((pencil A B).map (MvPolynomial.eval ![s, t])) ^ n := by
    show ((MvPolynomial.eval ![s, t]).mapMatrix (pencil A B ^ n)) = _
    rw [map_pow]
    rfl
  have h2 : (pencil A B).map (MvPolynomial.eval ![s, t]) = s • A + t • B := by
    ext a b
    show MvPolynomial.eval ![s, t]
        (MvPolynomial.C (A a b) * Height.Graded.mu
          + MvPolynomial.C (B a b) * Height.Graded.nu) = _
    simp [Height.Graded.mu, Height.Graded.nu, Matrix.add_apply, mul_comm]
  rw [← h2, ← h1, h, Matrix.map_zero _ (map_zero _)]

theorem pencil_pow_eq_zero_iff_coeff (x : PairIndex (Fin n) → K) (k : ℕ) :
    pencil (pairCoords.symm x).1 (pairCoords.symm x).2 ^ k = 0 ↔
      ∀ (i j : Fin n) (m : Fin 2 →₀ ℕ),
        MvPolynomial.aeval x (((univGrPencil K n ^ k) i j).coeff m) = 0 := by
  rw [← pencil_pow_specRing x k]
  have key : ∀ i j : Fin n,
      (((univGrPencil K n ^ k).map (MvPolynomial.map (specRing x))) i j = 0)
        ↔ ∀ m, MvPolynomial.aeval x (((univGrPencil K n ^ k) i j).coeff m) = 0 := by
    intro i j
    rw [Matrix.map_apply, mvMap_eq_zero_iff_coeff]
    simp only [specRing_apply]
  constructor
  · intro h i j m
    refine (key i j).1 ?_ m
    rw [h]
    simp
  · intro h
    refine Matrix.ext fun i j => ?_
    rw [Matrix.zero_apply]
    exact (key i j).2 (h i j)

/-- **The nilpotent pencils form a Zariski closed set.** -/
theorem isLocClosed_nilpotentPencil [Infinite K] :
    IsLocClosed {x : PairIndex (Fin n) → K | NilpotentPencil (pairCoords.symm x).1 (pairCoords.symm x).2} := by
  have hset : {x : PairIndex (Fin n) → K | NilpotentPencil (pairCoords.symm x).1 (pairCoords.symm x).2}
      = {x : PairIndex (Fin n) → K | ∀ a : (Fin n × Fin n) × (Fin 2 →₀ ℕ),
          MvPolynomial.aeval x (((univGrPencil K n ^ n) a.1.1 a.1.2).coeff a.2) = 0} := by
    refine Set.Subset.antisymm (fun x hx a => ?_) (fun x hx => ?_)
    · exact (pencil_pow_eq_zero_iff_coeff x n).1
        ((nilpotentPencil_iff_pow _ _).1 hx) a.1.1 a.1.2 a.2
    · exact (nilpotentPencil_iff_pow _ _).2
        ((pencil_pow_eq_zero_iff_coeff x n).2 fun i j m => hx ((i, j), m))
  rw [hset]
  exact isLocClosed_zeros_family _

/-- The multidegree condition depends on the type only through `m_k`. -/
theorem hasMultidegree_congr_mk {N M : Matrix (Fin n) (Fin n) K} {τ τ' : Nat.Partition n}
    (h : ∀ k, mk τ k = mk τ' k) {d : ℕ → ℕ} :
    HasMultidegree N M τ d ↔ HasMultidegree N M τ' d := by
  unfold HasMultidegree
  simp only [h]

/-- The multidegree of a *nonempty* pencil stratum obeys the bound of
`lem:kernel-flag`(3). -/
theorem admissible_of_mem_pencilLocus [Infinite K] {τ : Nat.Partition n} {d : ℕ → ℕ}
    {p : Matrix (Fin n) (Fin n) K × Matrix (Fin n) (Fin n) K} (h : p ∈ pencilLocus τ d) :
    ∀ k, 1 ≤ k → d k ≤ k * (n - mk τ k) := by
  obtain ⟨hnil, hgen, hmul⟩ := h
  obtain ⟨τ₀, d₀, hgen₀, hmul₀, hadm₀⟩ := exists_multidegree hnil
  have hmkeq : ∀ k, mk τ k = mk τ₀ k := by
    intro k
    have h1 := mk_add_pencilGenRank_of_genericType hgen k
    have h2 := mk_add_pencilGenRank_of_genericType hgen₀ k
    omega
  have hmul₀' : HasMultidegree p.1 p.2 τ d₀ :=
    (hasMultidegree_congr_mk (fun k => (hmkeq k).symm)).1 hmul₀
  intro k hk
  rw [hasMultidegree_unique hmul hmul₀' k hk, hmkeq k]
  exact hadm₀ k

/-- Extend a multidegree by `d 0 = 0`.  `hasMultidegree_iff_at` wants the admissibility
bound at every `k`, while a point of `pencilLocus` only carries it above `0`; this is the
repair, and both the constructibility proof and the specialisation proof need exactly it. -/
theorem exists_zeroExtend_admissible {τ : Nat.Partition n} {d : ℕ → ℕ}
    (hadm : ∀ k, 1 ≤ k → d k ≤ k * (n - mk τ k)) :
    ∃ d' : ℕ → ℕ, (∀ k, 1 ≤ k → d k = d' k) ∧ ∀ k, d' k ≤ k * (n - mk τ k) := by
  set d' : ℕ → ℕ := fun k => if k = 0 then 0 else d k with hd'def
  have hagree : ∀ k, 1 ≤ k → d k = d' k := by
    intro k hk
    rw [hd'def]
    simp only
    rw [ite_eq_right (by omega)]
  refine ⟨d', hagree, fun k => ?_⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [hd'def]
  · rw [← hagree k hk]
    exact hadm k hk

/-- **`Î_{τ,d}` is constructible.** -/
theorem isConstructible_pencilLocus [Infinite K] (τ : Nat.Partition n) (d : ℕ → ℕ) :
    IsAffineConstructible (pairCoords '' (pencilLocus (K := K) τ d)) := by
  classical
  rw [pairCoords.image_eq_preimage_symm]
  by_cases hadm : ∀ k, 1 ≤ k → d k ≤ k * (n - mk τ k)
  · obtain ⟨d', hagree, hd'adm⟩ := exists_zeroExtend_admissible hadm
    have hset : (pairCoords.symm ⁻¹' pencilLocus (K := K) τ d)
        = {x : PairIndex (Fin n) → K | NilpotentPencil (pairCoords.symm x).1 (pairCoords.symm x).2}
            ∩ ({x : PairIndex (Fin n) → K | GenericType (pairCoords.symm x).1 (pairCoords.symm x).2 τ}
              ∩ ⋂ j : Fin n, {x : PairIndex (Fin n) → K |
                  Module.finrank K
                      (kerPiece (pairCoords.symm x).1 (pairCoords.symm x).2 ((j : ℕ) + 1) (n * n))
                    + d ((j : ℕ) + 1) = mk τ ((j : ℕ) + 1) * (n * n + 1)}) := by
      refine Set.Subset.antisymm (fun x hx => ?_) (fun x hx => ?_)
      · obtain ⟨hnil, hgen, hmul⟩ := hx
        refine ⟨hnil, hgen, Set.mem_iInter.2 fun j => ?_⟩
        have hmul' : HasMultidegree (pairCoords.symm x).1 (pairCoords.symm x).2 τ d' :=
          hasMultidegree_of_agree hmul fun k hk => (hagree k hk).symm
        have h := (hasMultidegree_iff_at hgen hd'adm).1 hmul'
          ((j : ℕ) + 1) (by omega) (by omega)
        rw [Set.mem_ofPred_eq, hagree ((j : ℕ) + 1) (by omega)]
        exact h
      · obtain ⟨hnil, hgen, hfin⟩ := hx
        refine ⟨hnil, hgen, ?_⟩
        refine hasMultidegree_of_agree (d' := d')
          ((hasMultidegree_iff_at hgen hd'adm).2 fun k hk1 hkn => ?_) hagree
        have h := Set.mem_iInter.1 hfin ⟨k - 1, by omega⟩
        rw [Set.mem_ofPred_eq] at h
        rw [show k = (k - 1) + 1 by omega, hagree ((k - 1) + 1) (by omega)] at *
        exact h
    rw [hset]
    refine IsAffineConstructible.inter isLocClosed_nilpotentPencil.isConstructible ?_
    refine IsAffineConstructible.inter (isConstructible_genericType τ) ?_
    exact IsAffineConstructible.iInter fun j => isConstructible_finrank_kerPiece _ _ _ _
  · have hset : (pairCoords.symm ⁻¹' pencilLocus (K := K) τ d) = ∅ :=
      Set.eq_empty_iff_forall_notMem.2 fun _ hx => hadm (admissible_of_mem_pencilLocus hx)
    rw [hset]
    exact IsAffineConstructible.empty

end PencilLocus

/-! ### Transfer of the pencil stratum to a specialisation -/

section Transfer

variable {K : Type u} [Field K] {ι : Type} {n : ℕ}

/-- A polynomial vanishing on the dense open `V(P) ∖ V(q)` of an irreducible
`V(P)` lies in `P`: the Nullstellensatz, plus primality. -/
theorem mem_of_vanishing_on_open [IsAlgClosed K] [Finite ι]
    {P : Ideal (MvPolynomial ι K)} (hP : P.IsPrime) {q f : MvPolynomial ι K} (hq : q ∉ P)
    (h : ∀ z ∈ MvPolynomial.zeroLocus K P, MvPolynomial.aeval z q ≠ 0 →
      MvPolynomial.aeval z f = 0) : f ∈ P := by
  have : P.IsPrime := hP
  have hfq : f * q ∈ MvPolynomial.vanishingIdeal K (MvPolynomial.zeroLocus K P) :=
    MvPolynomial.mem_vanishingIdeal_iff.2 fun z hz => by
      rw [map_mul]
      by_cases hqz : MvPolynomial.aeval z q = 0
      · rw [hqz, mul_zero]
      · rw [h z hz hqz, zero_mul]
  rw [MvPolynomial.IsPrime.vanishingIdeal_zeroLocus (K := K) P] at hfq
  exact (hP.mem_or_mem hfq).resolve_right hq

/-- **Rank transfer.**  A matrix of polynomials of constant rank `r` on the dense
open `V(P) ∖ V(q)` of an irreducible `V(P)` has rank `r` at every specialisation
that kills `P` and kills nothing that survives at a chosen point `z₀` of that
dense open. -/
theorem rank_map_eq_of_dense [IsAlgClosed K] [Finite ι] {L : Type*} [Field L]
    {ρ σ : Type} [Fintype ρ] [Fintype σ]
    {P : Ideal (MvPolynomial ι K)} (hP : P.IsPrime) {q : MvPolynomial ι K} (hq : q ∉ P)
    (E : Matrix ρ σ (MvPolynomial ι K)) (r : ℕ)
    (hpt : ∀ z ∈ MvPolynomial.zeroLocus K P, MvPolynomial.aeval z q ≠ 0 →
      (E.map (specRing z)).rank = r)
    {z₀ : ι → K} (hz₀ : z₀ ∈ MvPolynomial.zeroLocus K P)
    (hq₀ : MvPolynomial.aeval z₀ q ≠ 0)
    (ψ : MvPolynomial ι K →+* L) (hψP : ∀ f ∈ P, ψ f = 0)
    (hψ0 : ∀ f : MvPolynomial ι K, MvPolynomial.aeval z₀ f ≠ 0 → ψ f ≠ 0) :
    (E.map ψ).rank = r := by
  classical
  have hrkL : ∀ θ : MvPolynomial ι K →+* L,
      ((E.submatrix (Fintype.equivFin ρ).symm (Fintype.equivFin σ).symm).map θ).rank
        = (E.map θ).rank := by
    intro θ
    rw [← Matrix.submatrix_map]
    exact Matrix.rank_submatrix _ _ _
  have hrkK : ∀ θ : MvPolynomial ι K →+* K,
      ((E.submatrix (Fintype.equivFin ρ).symm (Fintype.equivFin σ).symm).map θ).rank
        = (E.map θ).rank := by
    intro θ
    rw [← Matrix.submatrix_map]
    exact Matrix.rank_submatrix _ _ _
  rw [← hrkL ψ]
  refine le_antisymm ?_ ?_
  · refine (rank_le_iff_minors _ r).2 fun f g => ?_
    rw [det_submatrix_map_rect ψ _ f g]
    refine hψP _ (mem_of_vanishing_on_open hP hq fun z hz hqz => ?_)
    have h1 : (((E.submatrix (Fintype.equivFin ρ).symm (Fintype.equivFin σ).symm).map
        (specRing z)).submatrix f g).det = 0 := by
      refine (rank_le_iff_minors _ r).1 ?_ f g
      rw [hrkK (specRing z)]
      exact le_of_eq (hpt z hz hqz)
    rw [det_submatrix_map_rect (specRing z) _ f g] at h1
    exact h1
  · obtain ⟨f, g, hfg⟩ := Height.Toolbox.exists_submatrix_det_ne_zero (k := r)
      ((E.submatrix (Fintype.equivFin ρ).symm (Fintype.equivFin σ).symm).map (specRing z₀))
      (by rw [hrkK (specRing z₀)]; exact le_of_eq (hpt z₀ hz₀ hq₀).symm)
    refine Height.Toolbox.le_rank_of_submatrix_det_ne_zero _ f g ?_
    rw [det_submatrix_map_rect ψ _ f g]
    refine hψ0 _ ?_
    rw [det_submatrix_map_rect (specRing z₀) _ f g] at hfg
    exact hfg

/-- **The pencil stratum transfers to a specialisation.**  If `V(P)` is
irreducible, `c` is a family of coordinate functions and the pair `pairCoords.symm c`
lies in `Î_{τ,d}` at every point of the dense open `V(P) ∖ V(q)`, then the pair
has multidegree `d` at every specialisation `ψ` killing `P` and killing nothing
that survives at a chosen point `z₀` of that dense open. -/
theorem hasMultidegree_of_hom [IsAlgClosed K] [Infinite K] [Finite ι]
    {L : Type*} [Field L] [Infinite L]
    {τ : Nat.Partition n} {d : ℕ → ℕ}
    {P : Ideal (MvPolynomial ι K)} (hP : P.IsPrime) {q : MvPolynomial ι K} (hq : q ∉ P)
    (c : PairIndex (Fin n) → MvPolynomial ι K)
    (hlocus : ∀ z ∈ MvPolynomial.zeroLocus K P, MvPolynomial.aeval z q ≠ 0 →
      pairCoords.symm (fun i => specRing z (c i)) ∈ pencilLocus τ d)
    {z₀ : ι → K} (hz₀ : z₀ ∈ MvPolynomial.zeroLocus K P)
    (hq₀ : MvPolynomial.aeval z₀ q ≠ 0)
    (ψ : MvPolynomial ι K →+* L) (hψP : ∀ f ∈ P, ψ f = 0)
    (hψ0 : ∀ f : MvPolynomial ι K, MvPolynomial.aeval z₀ f ≠ 0 → ψ f ≠ 0) :
    HasMultidegree (pairCoords.symm fun i => ψ (c i)).1 (pairCoords.symm fun i => ψ (c i)).2 τ d := by
  classical
  obtain ⟨hbnil, hbgen, hbmul⟩ := hlocus z₀ hz₀ hq₀
  have hadm : ∀ k, 1 ≤ k → d k ≤ k * (n - mk τ k) :=
    admissible_of_mem_pencilLocus ⟨hbnil, hbgen, hbmul⟩
  obtain ⟨d', hagree, hd'adm⟩ := exists_zeroExtend_admissible hadm
  -- the Hilbert value at every point of the dense open
  have hbase : ∀ z ∈ MvPolynomial.zeroLocus K P, MvPolynomial.aeval z q ≠ 0 →
      ∀ k, 1 ≤ k → k ≤ n →
        Module.finrank K (kerPiece (pairCoords.symm fun i => specRing z (c i)).1
            (pairCoords.symm fun i => specRing z (c i)).2 k (n * n)) + d' k
          = mk τ k * (n * n + 1) := by
    intro z hz hqz
    obtain ⟨-, hgen, hmul⟩ := hlocus z hz hqz
    exact (hasMultidegree_iff_at hgen hd'adm).1
      (hasMultidegree_of_agree hmul fun k hk => (hagree k hk).symm)
  -- the generic type transfers
  have hgenA : GenericType (pairCoords.symm fun i => ψ (c i)).1 (pairCoords.symm fun i => ψ (c i)).2 τ := by
    refine genericType_iff.2 fun k hk1 hkn => ⟨?_, ?_⟩
    · obtain ⟨f, g, i, hi, hne⟩ :=
        (pencilRankGe_map_iff_coeff (specRing z₀) c k (n - mk τ k)).1
          (genericType_iff.1 hbgen k hk1 hkn).1
      exact (pencilRankGe_map_iff_coeff ψ c k (n - mk τ k)).2 ⟨f, g, i, hi, hψ0 _ hne⟩
    · refine (not_pencilRankGe_map_iff_coeff ψ c k (n - mk τ k + 1)).2 fun f g i => ?_
      refine hψP _ (mem_of_vanishing_on_open hP hq fun z hz hqz => ?_)
      exact (not_pencilRankGe_map_iff_coeff (specRing z) c k (n - mk τ k + 1)).1
        (genericType_iff.1 (hlocus z hz hqz).2.1 k hk1 hkn).2 f g i
  refine hasMultidegree_of_agree
    ((hasMultidegree_iff_at hgenA hd'adm).2 fun k hk1 hkn => ?_) hagree
  -- the Sylvester rank transfers
  have key : ∀ z ∈ MvPolynomial.zeroLocus K P, MvPolynomial.aeval z q ≠ 0 →
      ((sylMat (cGrPencil c ^ k) k (n * n)).map (specRing z)).rank
        = ((sylMat (cGrPencil c ^ k) k (n * n)).map (specRing z₀)).rank := by
    intro z hz hqz
    have h1 := hbase z hz hqz k hk1 hkn
    have h2 := hbase z₀ hz₀ hq₀ k hk1 hkn
    have h3 := finrank_kerPiece_add_rank (pairCoords.symm fun i => specRing z (c i)).1
      (pairCoords.symm fun i => specRing z (c i)).2 k (n * n)
    have h4 := finrank_kerPiece_add_rank (pairCoords.symm fun i => specRing z₀ (c i)).1
      (pairCoords.symm fun i => specRing z₀ (c i)).2 k (n * n)
    rw [sylMat_map (specRing z) c k (n * n), sylMat_map (specRing z₀) c k (n * n)]
    omega
  have hRA : (sylMat (pencil (pairCoords.symm fun i => ψ (c i)).1
        (pairCoords.symm fun i => ψ (c i)).2 ^ k) k (n * n)).rank
      = (sylMat (pencil (pairCoords.symm fun i => specRing z₀ (c i)).1
          (pairCoords.symm fun i => specRing z₀ (c i)).2 ^ k) k (n * n)).rank := by
    rw [← sylMat_map ψ c k (n * n), ← sylMat_map (specRing z₀) c k (n * n)]
    exact rank_map_eq_of_dense hP hq _ _ key hz₀ hq₀ ψ hψP hψ0
  have h5 := finrank_kerPiece_add_rank (pairCoords.symm fun i => ψ (c i)).1
    (pairCoords.symm fun i => ψ (c i)).2 k (n * n)
  have h6 := hbase z₀ hz₀ hq₀ k hk1 hkn
  have h7 := finrank_kerPiece_add_rank (pairCoords.symm fun i => specRing z₀ (c i)).1
    (pairCoords.symm fun i => specRing z₀ (c i)).2 k (n * n)
  omega

end Transfer

/-! ### The marked locus -/

section MarkedLocus

variable {K : Type u} [Field K] {n : ℕ}

/-- The universal member (`Pencil.genMember`) specialised at a point is the
member of the marked pencil there. -/
theorem aeval_genMember (x : MarkedIndex (Fin n) → K) (j : Fin 2) :
    (Height.Pencil.genMember K n j).map (MvPolynomial.aeval x)
      = (markedCoords.symm x).1 + x (Sum.inr j) • (markedCoords.symm x).2.1 := by
  ext a b
  simp [Height.Pencil.genMember, Matrix.add_apply]

theorem specMat_genMember_pow (x : MarkedIndex (Fin n) → K) (j : Fin 2) (k : ℕ) :
    specMat ((Height.Pencil.genMember K n j) ^ k) x
      = ((markedCoords.symm x).1 + x (Sum.inr j) • (markedCoords.symm x).2.1) ^ k := by
  show (RingHom.mapMatrix (specRing x)) ((Height.Pencil.genMember K n j) ^ k) = _
  rw [map_pow]
  congr 1
  exact aeval_genMember x j

/-- The locus where the member of the pencil at the marked parameter `j` lies in
the orbit closure of `N₀` is Zariski closed. -/
theorem isLocClosed_member_orbitClosure (N₀ : Matrix (Fin n) (Fin n) K) (j : Fin 2) :
    IsLocClosed {x : MarkedIndex (Fin n) → K |
      (markedCoords.symm x).1 + x (Sum.inr j) • (markedCoords.symm x).2.1 ∈ orbitClosure N₀} := by
  have hset : {x : MarkedIndex (Fin n) → K |
        (markedCoords.symm x).1 + x (Sum.inr j) • (markedCoords.symm x).2.1 ∈ orbitClosure N₀}
      = {x : MarkedIndex (Fin n) → K | ∀ a : (k : ℕ) ×
            ((Fin (Matrix.rank (N₀ ^ k) + 1) → Fin n)
              × (Fin (Matrix.rank (N₀ ^ k) + 1) → Fin n)),
          MvPolynomial.aeval x
            ((((Height.Pencil.genMember K n j) ^ a.1).submatrix a.2.1 a.2.2).det) = 0} := by
    refine Set.Subset.antisymm (fun x hx a => ?_) (fun x hx k => ?_)
    · rw [← det_submatrix_specMat, specMat_genMember_pow]
      exact (rank_le_iff_minors _ _).1 (hx a.1) a.2.1 a.2.2
    · rw [← specMat_genMember_pow]
      refine (rank_le_iff_minors _ _).2 fun f g => ?_
      rw [det_submatrix_specMat]
      exact hx ⟨k, (f, g)⟩
  rw [hset]
  exact isLocClosed_zeros_family _

/-- **`Ŷ` is constructible.** -/
theorem isConstructible_markedLocus [Infinite K] (τ : Nat.Partition n) (d : ℕ → ℕ)
    (N₀ : Matrix (Fin n) (Fin n) K) :
    IsAffineConstructible (markedCoords '' (markedLocus (K := K) τ d N₀)) := by
  classical
  rw [markedCoords.image_eq_preimage_symm]
  have hpar : ∀ x : MarkedIndex (Fin n) → K,
      (MvPolynomial.aeval x ((MvPolynomial.X (Sum.inr 0) : MvPolynomial (MarkedIndex (Fin n)) K)
          - MvPolynomial.X (Sum.inr 1)) ≠ 0) ↔ x (Sum.inr 0) ≠ x (Sum.inr 1) := by
    intro x
    rw [map_sub, MvPolynomial.aeval_X, MvPolynomial.aeval_X, sub_ne_zero]
  have hset : markedCoords.symm ⁻¹' (markedLocus (K := K) τ d N₀)
      = ((fun x : MarkedIndex (Fin n) → K => fun i : PairIndex (Fin n) => x (Sum.inl i)) ⁻¹'
            (pairCoords.symm ⁻¹' pencilLocus (K := K) τ d))
        ∩ ({x : MarkedIndex (Fin n) → K | MvPolynomial.aeval x
              ((MvPolynomial.X (Sum.inr 0) : MvPolynomial (MarkedIndex (Fin n)) K)
                - MvPolynomial.X (Sum.inr 1)) ≠ 0}
          ∩ ({x : MarkedIndex (Fin n) → K |
                (markedCoords.symm x).1 + x (Sum.inr 0) • (markedCoords.symm x).2.1 ∈ orbitClosure N₀}
            ∩ {x : MarkedIndex (Fin n) → K |
                (markedCoords.symm x).1 + x (Sum.inr 1) • (markedCoords.symm x).2.1 ∈ orbitClosure N₀})) := by
    ext x
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨h1, (hpar x).2 h2, h3, h4⟩
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨h1, (hpar x).1 h2, h3, h4⟩
  rw [hset]
  refine IsAffineConstructible.inter ?_ (IsAffineConstructible.inter
    (isLocClosed_principalOpen _).isConstructible ?_)
  · refine IsAffineConstructible.preimage isPolyMap_restrict_inl ?_
    rw [← pairCoords.image_eq_preimage_symm]
    exact isConstructible_pencilLocus τ d
  · exact IsAffineConstructible.inter (isLocClosed_member_orbitClosure N₀ 0).isConstructible
      (isLocClosed_member_orbitClosure N₀ 1).isConstructible

end MarkedLocus

end Height.Chain
