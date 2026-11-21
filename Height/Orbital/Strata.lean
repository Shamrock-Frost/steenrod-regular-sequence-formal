import Height.Orbital.TangentSweepIntrinsic
import Height.Orbital.TangentSweep
import Height.Geometry.Coordinates

/-!
# Chain strata, indexed by column sequences

This file fixes the model of the chain strata `A_T` of `subsec:chain-strata`
used by the arc layer.  A point of `𝔫_n` is
strictly upper triangular; the chain tableau of `lem:box-column` is recorded
by the *column sequence* `chainCol x : Fin n → ℕ`, whose value at `i` is the
column in which the Jordan type of `x|_{F_{i+1}}` gains its new box over the
Jordan type of `x|_{F_i}`.  A stratum is a level set of `chainCol`.

No standardness condition is imposed on the column sequence `T`: a
non-standard `T` simply gives an empty stratum.  Nilpotency of the
restrictions `x|_{F_i}`, which `boxColumn` requires, is *derived* from strict
upper triangularity here, so that it never appears as a hypothesis in the
arc-layer API.

The main output: `finrank_ker_pow_of_inStratum` and its corollary
`conj_of_inStratum` say that the whole conjugate Jordan type of a point of
`A_T` is an explicit function of `T`.  This is what makes the ranks appearing
in the saturation lemma constant along an arc, with no semicontinuity
argument.
-/

namespace Height.Orbital

open Matrix
open Height.Toolbox

universe u

section Plain

variable {R : Type*} {n : ℕ}

/-- The restriction of a matrix to the first `n` coordinates, i.e. `x|_{F_n}`
for the standard flag. -/
def restrict (x : Matrix (Fin (n + 1)) (Fin (n + 1)) R) : Matrix (Fin n) (Fin n) R :=
  x.submatrix Fin.castSucc Fin.castSucc

@[simp] theorem restrict_apply (x : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (i j : Fin n) :
    restrict x i j = x i.castSucc j.castSucc := rfl

/-- The last column of a matrix, truncated to the first `n` coordinates. -/
def lastCol (x : Matrix (Fin (n + 1)) (Fin (n + 1)) R) : Fin n → R :=
  fun i => x i.castSucc (Fin.last n)

@[simp] theorem lastCol_apply (x : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (i : Fin n) :
    lastCol x i = x i.castSucc (Fin.last n) := rfl

/-- The top-left `i × i` block of `x`, i.e. the restriction `x|_{F_i}`. -/
def flagBlock (x : Matrix (Fin n) (Fin n) R) (i : Fin n) : Matrix (Fin i) (Fin i) R :=
  x.submatrix (Fin.castLE i.isLt.le) (Fin.castLE i.isLt.le)

/-- The `i`-th column of `x`, truncated to the first `i` coordinates. -/
def flagVec (x : Matrix (Fin n) (Fin n) R) (i : Fin n) : Fin i → R :=
  fun j => x (Fin.castLE i.isLt.le j) i

theorem flagBlock_last (x : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    flagBlock x (Fin.last n) = restrict x := rfl

end Plain

section Zero

variable {R : Type*} [Zero R] {n : ℕ}

/-- Strictly upper triangular matrices: the entrywise description of the
nilradical `𝔫` of the standard Borel (`Height.Toolbox.standardNilradical`). -/
def IsStrictlyUpper (x : Matrix (Fin n) (Fin n) R) : Prop :=
  ∀ i j : Fin n, j ≤ i → x i j = 0

theorem isStrictlyUpper_restrict {x : Matrix (Fin (n + 1)) (Fin (n + 1)) R}
    (hx : IsStrictlyUpper x) : IsStrictlyUpper (restrict x) := fun i j hij =>
  hx i.castSucc j.castSucc hij

theorem isStrictlyUpper_flagBlock {x : Matrix (Fin n) (Fin n) R}
    (hx : IsStrictlyUpper x) (i : Fin n) : IsStrictlyUpper (flagBlock x i) := fun a b hab =>
  hx (Fin.castLE i.isLt.le a) (Fin.castLE i.isLt.le b) hab

end Zero

/-! ### The nilradical as an ideal of the entry polynomial ring -/

section Ideal

open Height.Geometry (matCoords)

variable (K : Type*) [Field K]

/-- The ideal of `𝔫`: the entry coordinates on and below the diagonal.  Its zero
locus is the strictly upper triangular matrices (`mem_zeroLocus_strictUpperIdeal_iff`),
and `strictUpperIdeal n ≤ I` is the algebraic form of "`V(I) ⊆ 𝔫`". -/
noncomputable def strictUpperIdeal (n : ℕ) : Ideal (MvPolynomial (Fin n × Fin n) K) :=
  Ideal.span {f | ∃ i j : Fin n, j ≤ i ∧ f = MvPolynomial.X (i, j)}

variable {K}

/-- A point of entry space is a zero of `strictUpperIdeal` exactly when the matrix
it names is strictly upper triangular. -/
theorem mem_zeroLocus_strictUpperIdeal_iff {n : ℕ} (x : Fin n × Fin n → K) :
    x ∈ MvPolynomial.zeroLocus K (strictUpperIdeal K n) ↔ IsStrictlyUpper (matCoords.symm x) := by
  constructor
  · intro hx i j hij
    have : MvPolynomial.X (R := K) (i, j) ∈ strictUpperIdeal K n :=
      Ideal.subset_span ⟨i, j, hij, rfl⟩
    simpa using hx _ this
  · intro hx f hf
    induction hf using Submodule.span_induction with
    | mem g hg =>
        obtain ⟨i, j, hij, rfl⟩ := hg
        simpa using hx i j hij
    | zero => simp
    | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
    | smul a b _ hb => rw [smul_eq_mul, map_mul, hb, mul_zero]

/-- Over an algebraically closed field, "`V(I) ⊆ 𝔫`" for a prime `I` *is* the
containment `strictUpperIdeal K n ≤ I`: the converse of `isStrictlyUpper_of_le`,
by the Nullstellensatz. -/
theorem strictUpperIdeal_le_of_forall_isStrictlyUpper [IsAlgClosed K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n × Fin n) K)) [I.IsPrime]
    (h : ∀ x ∈ MvPolynomial.zeroLocus K I, IsStrictlyUpper (matCoords.symm x)) :
    strictUpperIdeal K n ≤ I := by
  rw [strictUpperIdeal, Ideal.span_le]
  rintro f ⟨i, j, hij, rfl⟩
  rw [SetLike.mem_coe, ← MvPolynomial.IsPrime.vanishingIdeal_zeroLocus (K := K) I]
  intro x hx
  simpa [Height.Geometry.matCoords_symm_apply] using h x hx i j hij

/-- Every zero of an ideal containing `strictUpperIdeal` is strictly upper
triangular: "`V(I) ⊆ 𝔫`", with no Nullstellensatz. -/
theorem isStrictlyUpper_of_le {n : ℕ} {I : Ideal (MvPolynomial (Fin n × Fin n) K)}
    (h : strictUpperIdeal K n ≤ I) {x : Fin n × Fin n → K}
    (hx : x ∈ MvPolynomial.zeroLocus K I) : IsStrictlyUpper (matCoords.symm x) :=
  (mem_zeroLocus_strictUpperIdeal_iff x).1 fun f hf => hx f (h hf)

end Ideal

section Ring

variable {R : Type*} [CommRing R] {n : ℕ}

theorem isStrictlyUpper_of_map {S : Type*} [CommRing S] (f : R →+* S)
    (hf : Function.Injective f) {x : Matrix (Fin n) (Fin n) R}
    (hx : IsStrictlyUpper (x.map f)) : IsStrictlyUpper x := fun i j hij => by
  apply hf
  rw [map_zero]
  exact hx i j hij

theorem strictlyUpper_pow_apply {x : Matrix (Fin n) (Fin n) R} (hx : IsStrictlyUpper x) :
    ∀ (k : ℕ) (i j : Fin n), (j : ℕ) < (i : ℕ) + k → (x ^ k) i j = 0 := by
  intro k
  induction k with
  | zero =>
      intro i j h
      have hij : i ≠ j := by
        intro hh
        rw [hh] at h
        omega
      simp [hij]
  | succ k ih =>
      intro i j h
      rw [pow_succ, Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro l _
      by_cases hl : (l : ℕ) < (i : ℕ) + k
      · rw [ih i l hl, zero_mul]
      · have hjl : j ≤ l := by
          rw [Fin.le_def]
          omega
        rw [hx l j hjl, mul_zero]

theorem strictlyUpper_pow_eq_zero {x : Matrix (Fin n) (Fin n) R} (hx : IsStrictlyUpper x) :
    x ^ n = 0 := by
  ext i j
  have hj := j.isLt
  exact strictlyUpper_pow_apply hx n i j (by omega)

end Ring

section Field

variable {K : Type u} [Field K] {n : ℕ}

theorem strictlyUpper_isNilpotent {x : Matrix (Fin n) (Fin n) K} (hx : IsStrictlyUpper x) :
    IsNilpotent (Matrix.toLinAlgEquiv' x) :=
  ⟨n, by rw [← map_pow, strictlyUpper_pow_eq_zero hx, map_zero]⟩

/-- The column of the chain tableau in which the `i`-th step adds its box:
`boxColumn` of the restriction `x|_{F_i}` together with the truncated `i`-th
column of `x` (`lem:box-column`). -/
noncomputable def chainCol (x : Matrix (Fin n) (Fin n) K) (hx : IsStrictlyUpper x)
    (i : Fin n) : ℕ :=
  boxColumn (Matrix.toLinAlgEquiv' (flagBlock x i)) (flagVec x i)
    (strictlyUpper_isNilpotent (isStrictlyUpper_flagBlock hx i))

/-- The chain stratum `A_T`: the strictly upper triangular matrices whose
column sequence is `T`. -/
def inStratum (T : Fin n → ℕ) (x : Matrix (Fin n) (Fin n) K) : Prop :=
  ∃ hx : IsStrictlyUpper x, ∀ i, chainCol x hx i = T i

theorem inStratum.upper {T : Fin n → ℕ} {x : Matrix (Fin n) (Fin n) K}
    (h : inStratum T x) : IsStrictlyUpper x := by
  obtain ⟨hx, -⟩ := h
  exact hx

theorem inStratum.chainCol_eq {T : Fin n → ℕ} {x : Matrix (Fin n) (Fin n) K}
    (h : inStratum T x) (hx : IsStrictlyUpper x) (i : Fin n) : chainCol x hx i = T i := by
  obtain ⟨hx', hc⟩ := h
  exact hc i

/-- Every entry of a column sequence is at least one. -/
theorem one_le_chainCol (x : Matrix (Fin n) (Fin n) K) (hx : IsStrictlyUpper x) (i : Fin n) :
    1 ≤ chainCol x hx i :=
  (boxColumn_spec _ _ _).1

theorem one_le_of_inStratum {T : Fin n → ℕ} {x : Matrix (Fin n) (Fin n) K}
    (h : inStratum T x) (i : Fin n) : 1 ≤ T i := by
  rw [← h.chainCol_eq h.upper i]
  exact one_le_chainCol x h.upper i

/-- Restriction to `F_n` maps `A_T` into `A_{T ∘ castSucc}`. -/
theorem inStratum_restrict {T : Fin (n + 1) → ℕ} {x : Matrix (Fin (n + 1)) (Fin (n + 1)) K}
    (h : inStratum T x) : inStratum (T ∘ Fin.castSucc) (restrict x) :=
  ⟨isStrictlyUpper_restrict h.upper, fun i => h.chainCol_eq h.upper i.castSucc⟩

/-- The column of the last box, read off the restriction and the last column. -/
theorem chainCol_last {T : Fin (n + 1) → ℕ} {x : Matrix (Fin (n + 1)) (Fin (n + 1)) K}
    (h : inStratum T x) (hy : IsNilpotent (Matrix.toLinAlgEquiv' (restrict x))) :
    T (Fin.last n) = boxColumn (Matrix.toLinAlgEquiv' (restrict x)) (lastCol x) hy :=
  (h.chainCol_eq h.upper (Fin.last n)).symm

end Field

section Bridge

variable {K : Type u} [Field K] {n : ℕ}

@[simp] theorem blockIndexEquiv_inl (i : Fin n) :
    blockIndexEquiv n (Sum.inl i) = i.castSucc := rfl

@[simp] theorem blockIndexEquiv_inr (u : Unit) :
    blockIndexEquiv n (Sum.inr u) = Fin.last n := by
  ext
  simp [blockIndexEquiv]

@[simp] theorem blockIndexEquiv_symm_castSucc (i : Fin n) :
    (blockIndexEquiv n).symm i.castSucc = Sum.inl i :=
  (blockIndexEquiv n).symm_apply_eq.mpr (blockIndexEquiv_inl i).symm

@[simp] theorem blockIndexEquiv_symm_last :
    (blockIndexEquiv n).symm (Fin.last n) = Sum.inr () :=
  (blockIndexEquiv n).symm_apply_eq.mpr (blockIndexEquiv_inr ()).symm

theorem standardBlockMatrix_apply (A : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) K)
    (i j : Fin (n + 1)) :
    standardBlockMatrix A i j =
      A ((blockIndexEquiv n).symm i) ((blockIndexEquiv n).symm j) := rfl

/-- The bridge to the block algebra of `Transporter.lean`: a strictly upper
triangular
matrix is the standard block extension of its restriction by its last
column, because its last row vanishes. -/
theorem eq_standardBlockMatrix {x : Matrix (Fin (n + 1)) (Fin (n + 1)) K}
    (hx : IsStrictlyUpper x) :
    x = standardBlockMatrix (blockExtension (restrict x) (lastCol x)) := by
  ext i j
  rw [standardBlockMatrix_apply]
  induction i using Fin.lastCases with
  | cast i =>
      induction j using Fin.lastCases with
      | cast j => simp [blockExtension, restrict_apply, blockIndexEquiv_symm_castSucc]
      | last => simp [blockExtension, lastColumn, lastCol_apply,
          blockIndexEquiv_symm_castSucc, blockIndexEquiv_symm_last]
  | last =>
      induction j using Fin.lastCases with
      | cast j =>
          rw [hx (Fin.last n) j.castSucc (Fin.le_last _)]
          simp [blockExtension, blockIndexEquiv_symm_castSucc, blockIndexEquiv_symm_last]
      | last =>
          rw [hx (Fin.last n) (Fin.last n) le_rfl]
          simp [blockExtension, blockIndexEquiv_symm_last]

end Bridge

section Conj

variable {K : Type u} [Field K] {n : ℕ}

/-- Splitting off the last coordinate of `K^{n+1}`. -/
def splitLast (K : Type u) [Field K] (n : ℕ) :
    (Fin (n + 1) → K) ≃ₗ[K] ((Fin n → K) × K) where
  toFun w := (fun i => w i.castSucc, w (Fin.last n))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun p := Fin.snoc p.1 p.2
  left_inv w := Fin.snoc_init_self w
  right_inv p := by
    apply Prod.ext
    · funext i
      simp
    · simp

/-- Under `splitLast`, a strictly upper triangular matrix on `K^{n+1}` becomes
the one-vector extension of its restriction (`Height.Toolbox.extendByVector`). -/
theorem splitLast_comm {x : Matrix (Fin (n + 1)) (Fin (n + 1)) K} (hx : IsStrictlyUpper x)
    (w : Fin (n + 1) → K) :
    splitLast K n (Matrix.toLinAlgEquiv' x w) =
      extendByVector (Matrix.toLinAlgEquiv' (restrict x)) (lastCol x) (splitLast K n w) := by
  apply Prod.ext
  · funext i
    show (x *ᵥ w) i.castSucc =
      ((restrict x) *ᵥ (fun a => w a.castSucc)) i + w (Fin.last n) • lastCol x i
    rw [Matrix.mulVec, Matrix.mulVec, dotProduct, dotProduct, Fin.sum_univ_castSucc]
    simp [restrict_apply, lastCol_apply, smul_eq_mul, mul_comm]
  · show (x *ᵥ w) (Fin.last n) = 0
    rw [Matrix.mulVec, dotProduct]
    apply Finset.sum_eq_zero
    intro j _
    rw [hx (Fin.last n) j (Fin.le_last j), zero_mul]

private theorem finrank_ker_pow_eq_of_semiconj {W W' : Type*} [AddCommGroup W] [Module K W]
    [AddCommGroup W'] [Module K W'] [FiniteDimensional K W]
    (e : W ≃ₗ[K] W') (f : Module.End K W) (g : Module.End K W')
    (h : ∀ w, e (f w) = g (e w)) (m : ℕ) :
    Module.finrank K (LinearMap.ker (g ^ m)) = Module.finrank K (LinearMap.ker (f ^ m)) := by
  have hpow : ∀ (r : ℕ) (w : W), e ((f ^ r) w) = (g ^ r) (e w) := by
    intro r
    induction r with
    | zero => intro w; simp
    | succ r ih =>
        intro w
        rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, h]
  have hmap : Submodule.map (e : W →ₗ[K] W') (LinearMap.ker (f ^ m)) = LinearMap.ker (g ^ m) := by
    apply le_antisymm
    · intro z hz
      rw [Submodule.mem_map] at hz
      obtain ⟨w, hw, rfl⟩ := hz
      rw [LinearMap.mem_ker]
      show (g ^ m) (e w) = 0
      rw [← hpow, LinearMap.mem_ker.mp hw, map_zero]
    · intro z hz
      rw [Submodule.mem_map]
      refine ⟨e.symm z, ?_, e.apply_symm_apply z⟩
      rw [LinearMap.mem_ker]
      apply e.injective
      rw [hpow, e.apply_symm_apply, map_zero]
      exact LinearMap.mem_ker.mp hz
  rw [← hmap, LinearEquiv.finrank_map_eq]

private theorem boxDelta_eq_ite {W : Type*} [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (y : Module.End K W) (v : W) (hy : IsNilpotent y) (m : ℕ) :
    boxDelta y v m = if boxColumn y v hy ≤ m then 1 else 0 := by
  split_ifs with hcm
  · exact (boxDelta_eq_one_iff_boxColumn_le y v hy m).2 hcm
  · by_contra hne
    have hone : boxDelta y v m = 1 := by
      have := boxDelta_le_one y v m
      omega
    exact hcm ((boxDelta_eq_one_iff_boxColumn_le y v hy m).1 hone)

/-- The kernel dimensions of all powers of a
point of `A_T` are the counting function of `T`. -/
theorem finrank_ker_pow_of_inStratum {T : Fin n → ℕ} {x : Matrix (Fin n) (Fin n) K}
    (h : inStratum T x) (m : ℕ) :
    Module.finrank K (LinearMap.ker ((Matrix.toLinAlgEquiv' x) ^ m)) =
      (Finset.univ.filter fun i => T i ≤ m).card := by
  induction n with
  | zero =>
      have hle : Module.finrank K (LinearMap.ker ((Matrix.toLinAlgEquiv' x) ^ m)) ≤
          Module.finrank K (Fin 0 → K) := Submodule.finrank_le _
      rw [Module.finrank_fin_fun] at hle
      have hcard : (Finset.univ.filter fun i : Fin 0 => T i ≤ m).card = 0 := by
        simp [Finset.univ_eq_empty]
      rw [hcard]
      omega
  | succ n ih =>
      have hyn : IsNilpotent (Matrix.toLinAlgEquiv' (restrict x)) :=
        strictlyUpper_isNilpotent (isStrictlyUpper_restrict h.upper)
      have hrestr : inStratum (T ∘ Fin.castSucc) (restrict x) := inStratum_restrict h
      have hstep := finrank_ker_pow_eq_of_semiconj (splitLast K n)
        (Matrix.toLinAlgEquiv' x)
        (extendByVector (Matrix.toLinAlgEquiv' (restrict x)) (lastCol x))
        (splitLast_comm h.upper) m
      rw [hstep.symm.trans
        (finrank_ker_extendByVector_pow (Matrix.toLinAlgEquiv' (restrict x)) (lastCol x) m)]
      rw [ih (T := T ∘ Fin.castSucc) (x := restrict x) hrestr, boxDelta_eq_ite _ _ hyn m,
        ← chainCol_last h hyn]
      rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_castSucc]
      rfl

/-- The conjugate Jordan type of a point of `A_T` is the column-count
function of `T`.  In particular two points of the same stratum, over any two
fields, have the same kernel dimensions in every power. -/
theorem conj_of_inStratum {T : Fin n → ℕ} {x : Matrix (Fin n) (Fin n) K}
    (h : inStratum T x) (m : ℕ) :
    conj (Matrix.toLinAlgEquiv' x) m = (Finset.univ.filter fun i => T i = m).card := by
  cases m with
  | zero =>
      have hzero : (Finset.univ.filter fun i => T i = 0) = (∅ : Finset (Fin n)) := by
        apply Finset.filter_false_of_mem
        intro i _
        have := one_le_of_inStratum h i
        omega
      rw [conj, hzero, Finset.card_empty]
      exact Nat.sub_self _
  | succ m =>
      have hsplit :
          (Finset.univ.filter fun i => T i ≤ m + 1).card =
            (Finset.univ.filter fun i => T i ≤ m).card +
              (Finset.univ.filter fun i => T i = m + 1).card := by
        rw [Finset.card_filter, Finset.card_filter, Finset.card_filter,
          ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        by_cases h1 : T i ≤ m
        · have h2 : T i ≤ m + 1 := by omega
          have h3 : T i ≠ m + 1 := by omega
          simp [h1, h2, h3]
        · by_cases h2 : T i = m + 1
          · simp [h2]
          · have h3 : ¬ T i ≤ m + 1 := by omega
            simp [h1, h2, h3]
      have hm := finrank_ker_pow_of_inStratum h (m + 1)
      have hm' := finrank_ker_pow_of_inStratum h m
      have hpred : m + 1 - 1 = m := by omega
      rw [conj, hpred, hm, hm', hsplit]
      omega

end Conj

end Height.Orbital
