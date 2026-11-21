import Height.Chain.Reduction

/-!
# Coordinate flags: the standard parabolic and its nilradical

The map `ψ` of `thm:reduction` conjugates the fibre
flag `V_•` of a marked point onto a *fixed coordinate flag*, and the target of
`ψ` is the nilradical of the parabolic of that flag.  This file is the
elementary linear algebra of such a flag, in the entrywise form the affine
constructions of `Chain/Psi.lean` need.

A coordinate flag is given by a *level function* `lvl : Fin n → ℕ`: the flag is
`F_k = ⟨e_i : lvl i ≤ k⟩`, so its jumps are the level sets of `lvl`.  Then

* `IsBlockUpper lvl A` (`A i j = 0` whenever `lvl j < lvl i`) says `A F_k ⊆ F_k`
  — the parabolic `𝔭`;
* `IsBlockStrict lvl A` (`A i j = 0` whenever `lvl j ≤ lvl i`) says
  `A F_{k+1} ⊆ F_k` — the nilradical `𝔫_{F_•}`.

For a *monotone* `lvl` the nilradical consists of strictly upper triangular
matrices (`IsBlockStrict.isStrictlyUpper`), which is what `Chain/Star.lean`'s
`star_general` requires of the ambient of the irreducible `Z`.

The one non-formal statement is `IsBlockUpper.inv`: over a field an invertible
element of the parabolic has its inverse in the parabolic.  It is proved from
the flag description (`isBlockUpper_iff_mapsTo`) and the fact that an injective
endomorphism of a finite-dimensional space is surjective, so it needs no
determinant identity for block matrices.
-/

namespace Height.Chain

open Height.Pencil

open Matrix

universe u

variable {n : ℕ}

/-! ### The two entrywise conditions -/

/-- `A` preserves the coordinate flag of `lvl`: the parabolic `𝔭`. -/
def IsBlockUpper {R : Type*} [Zero R] (lvl : Fin n → ℕ) (A : Matrix (Fin n) (Fin n) R) : Prop :=
  ∀ i j, lvl j < lvl i → A i j = 0

/-- `A` lowers the coordinate flag of `lvl`: the nilradical `𝔫_{F_•}`. -/
def IsBlockStrict {R : Type*} [Zero R] (lvl : Fin n → ℕ) (A : Matrix (Fin n) (Fin n) R) : Prop :=
  ∀ i j, lvl j ≤ lvl i → A i j = 0

variable {lvl : Fin n → ℕ}

/-- The nilradical of a monotone coordinate flag consists of strictly upper
triangular matrices: this is what puts the image of `ψ` inside `𝔫`. -/
theorem IsBlockStrict.isStrictlyUpper {R : Type*} [Zero R] {A : Matrix (Fin n) (Fin n) R}
    (hmono : Monotone lvl) (h : IsBlockStrict lvl A) : Height.Orbital.IsStrictlyUpper A :=
  fun i j hij => h i j (hmono hij)

theorem isBlockUpper_one {R : Type*} [Zero R] [One R] [DecidableEq (Fin n)] :
    IsBlockUpper lvl (1 : Matrix (Fin n) (Fin n) R) := by
  intro i j hij
  have hne : i ≠ j := fun h => absurd (h ▸ hij) (lt_irrefl _)
  exact Matrix.one_apply_ne hne

theorem IsBlockUpper.add {R : Type*} [AddZeroClass R] {A B : Matrix (Fin n) (Fin n) R}
    (hA : IsBlockUpper lvl A) (hB : IsBlockUpper lvl B) : IsBlockUpper lvl (A + B) :=
  fun i j hij => by rw [Matrix.add_apply, hA i j hij, hB i j hij, add_zero]

theorem IsBlockUpper.neg {R : Type*} [SubtractionMonoid R] {A : Matrix (Fin n) (Fin n) R}
    (hA : IsBlockUpper lvl A) : IsBlockUpper lvl (-A) :=
  fun i j hij => by rw [Matrix.neg_apply, hA i j hij, neg_zero]

theorem IsBlockUpper.smul {R : Type*} [MonoidWithZero R] {c : R}
    {A : Matrix (Fin n) (Fin n) R} (hA : IsBlockUpper lvl A) : IsBlockUpper lvl (c • A) :=
  fun i j hij => by
    show c * A i j = 0
    rw [hA i j hij, mul_zero]

theorem IsBlockUpper.map {R S : Type*} [Zero R] [Zero S] {F : Type*} [FunLike F R S]
    [ZeroHomClass F R S] (f : F) {A : Matrix (Fin n) (Fin n) R} (hA : IsBlockUpper lvl A) :
    IsBlockUpper lvl (A.map f) :=
  fun i j hij => by
    show f (A i j) = 0
    rw [hA i j hij, map_zero]

/-! ### The multiplicative structure -/

theorem IsBlockUpper.mul {R : Type*} [NonUnitalNonAssocSemiring R]
    {A B : Matrix (Fin n) (Fin n) R} (hA : IsBlockUpper lvl A) (hB : IsBlockUpper lvl B) :
    IsBlockUpper lvl (A * B) := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rcases lt_or_ge (lvl k) (lvl i) with h | h
  · rw [hA i k h, zero_mul]
  · rw [hB k j (lt_of_lt_of_le hij h), mul_zero]

/-- The nilradical is a left ideal of the parabolic. -/
theorem IsBlockStrict.mul_left {R : Type*} [NonUnitalNonAssocSemiring R]
    {A B : Matrix (Fin n) (Fin n) R} (hA : IsBlockUpper lvl A) (hB : IsBlockStrict lvl B) :
    IsBlockStrict lvl (A * B) := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rcases lt_or_ge (lvl k) (lvl i) with h | h
  · rw [hA i k h, zero_mul]
  · rw [hB k j (le_trans hij h), mul_zero]

/-- The nilradical is a right ideal of the parabolic. -/
theorem IsBlockStrict.mul_right {R : Type*} [NonUnitalNonAssocSemiring R]
    {A B : Matrix (Fin n) (Fin n) R} (hA : IsBlockStrict lvl A) (hB : IsBlockUpper lvl B) :
    IsBlockStrict lvl (A * B) := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rcases le_or_gt (lvl k) (lvl i) with h | h
  · rw [hA i k h, zero_mul]
  · rw [hB k j (lt_of_le_of_lt hij h), mul_zero]

/-! ### The flag description and the inverse -/

section Flag

variable {K : Type u} [Field K]

/-- `F_k = ⟨e_i : lvl i ≤ k⟩`, the `k`-th step of the coordinate flag. -/
def levelSpace (lvl : Fin n → ℕ) (k : ℕ) : Submodule K (Fin n → K) where
  carrier := {v | ∀ i, k < lvl i → v i = 0}
  zero_mem' _ _ := rfl
  add_mem' {v w} hv hw i hi := by
    show v i + w i = 0
    rw [hv i hi, hw i hi, add_zero]
  smul_mem' c v hv i hi := by
    show c * v i = 0
    rw [hv i hi, mul_zero]

/-- The parabolic is exactly the stabiliser of the coordinate flag. -/
theorem isBlockUpper_iff_mapsTo {A : Matrix (Fin n) (Fin n) K} :
    IsBlockUpper lvl A ↔ ∀ k, ∀ v ∈ levelSpace (K := K) lvl k, A *ᵥ v ∈ levelSpace lvl k := by
  constructor
  · intro hA k v hv i hi
    show ∑ j, A i j * v j = 0
    refine Finset.sum_eq_zero fun j _ => ?_
    rcases le_or_gt (lvl j) k with h | h
    · rw [hA i j (lt_of_le_of_lt h hi), zero_mul]
    · rw [hv j h, mul_zero]
  · intro h i j hij
    have hj : (Pi.single j 1 : Fin n → K) ∈ levelSpace lvl (lvl j) := by
      intro l hl
      have : l ≠ j := fun hlj => absurd (hlj ▸ hl) (lt_irrefl _)
      simp [this]
    have := h (lvl j) _ hj i hij
    have hval : (A *ᵥ (Pi.single j 1 : Fin n → K)) i = A i j := by
      show ∑ l, A i l * (Pi.single j 1 : Fin n → K) l = A i j
      rw [Finset.sum_eq_single j] <;> simp +contextual
    rwa [hval] at this

/-- **The inverse lemma.**  Over a field the inverse of an invertible element of
the parabolic again preserves the flag: the restriction of `A` to each `F_k` is
an injective endomorphism of a finite-dimensional space, hence surjective. -/
theorem IsBlockUpper.inv {A : Matrix (Fin n) (Fin n) K} (hA : IsBlockUpper lvl A)
    (hu : IsUnit A.det) : IsBlockUpper lvl A⁻¹ := by
  classical
  rw [isBlockUpper_iff_mapsTo] at hA ⊢
  intro k v hv
  -- the restriction of `A` to `F_k`
  set S := levelSpace (K := K) lvl k with hS
  set f : S →ₗ[K] S := LinearMap.restrict A.mulVecLin (fun x hx => hA k x hx) with hf
  have hinj : Function.Injective f := by
    intro x y hxy
    have hx : A *ᵥ (x : Fin n → K) = A *ᵥ (y : Fin n → K) := congrArg Subtype.val hxy
    have : A⁻¹ *ᵥ (A *ᵥ (x : Fin n → K)) = A⁻¹ *ᵥ (A *ᵥ (y : Fin n → K)) := by rw [hx]
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec,
      Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec] at this
    exact Subtype.ext this
  have hsurj : Function.Surjective f := (LinearMap.injective_iff_surjective).mp hinj
  obtain ⟨w, hw⟩ := hsurj ⟨v, hv⟩
  have hwv : A *ᵥ (w : Fin n → K) = v := congrArg Subtype.val hw
  have : A⁻¹ *ᵥ v = (w : Fin n → K) := by
    rw [← hwv, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
  rw [this]
  exact w.2

end Flag

end Height.Chain
