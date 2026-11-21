import Height.Toolbox.Flags
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Basis

/-!
# Frames adapted to a flag (`lem:local-model`(1) as linear algebra)

`Chain/Frame.lean`'s `GeometricFrame` asks for a matrix `C` and a monotone level
function `lvl` such that `C⁻¹ (N + tM) C` lies in the nilradical of the
coordinate flag of `lvl`.  That is one statement of pure linear algebra plus one
of algebraic geometry, and this file is the linear algebra: *a matrix that
lowers a flag is block strict in a frame adapted to that flag*.

* `levelFlag lvl k` — the span of the `e i` with `lvl i ≤ k`, the coordinate
  flag the parabolic `IsBlockUpper lvl` belongs to;
* `exists_flagFrame` — every monotone chain of subspaces of `Lⁿ` from `⊥` to
  `⊤` is the image of `levelFlag lvl •` under an invertible matrix, for a
  monotone `lvl`.  Extend a basis of `V k` to one of `V (k+1)` at every step
  (`exists_linearIndepOn_id_extension`), then sort the resulting basis by the
  level at which each vector entered (`Tuple.sort`), which is what makes `lvl`
  monotone;
* `exists_blockStrict_of_flag` — the two together: if `M` lowers `V`, then in
  the adapted frame `A = P⁻¹ M P` has `A i j = 0` whenever `lvl j ≤ lvl i`.

The flag `Chain/Frame.lean` applies this to is the *fibre* flag
`Pencil.fibFlag` of the generic pencil, not the kernel flag `ker (N + tM)^•` of
the member: the two differ at a marked point, where the type drops, and only the
fibre flag makes the second clause of the frame (`Chain.FrameNorm`) true.
-/

namespace Height.Toolbox

open Matrix Module

universe u

section LevelFlag

variable {L : Type u} [Field L] {n : ℕ}

/-- The coordinate flag of a level function: the span of the `e i` with
`lvl i ≤ k`.  For `lvl` monotone this is `standardFlag L n #{i | lvl i ≤ k}`;
the level form is the one the parabolic `IsBlockUpper lvl` is stated in. -/
def levelFlag (lvl : Fin n → ℕ) (k : ℕ) : Submodule L (Fin n → L) where
  carrier := {v | ∀ i, k < lvl i → v i = 0}
  zero_mem' := by simp
  add_mem' := by
    intro v w hv hw i hi
    simp [hv i hi, hw i hi]
  smul_mem' := by
    intro a v hv i hi
    simp [hv i hi]

@[simp] theorem mem_levelFlag_iff (lvl : Fin n → ℕ) (k : ℕ) (v : Fin n → L) :
    v ∈ levelFlag (L := L) lvl k ↔ ∀ i, k < lvl i → v i = 0 := Iff.rfl

theorem single_mem_levelFlag {lvl : Fin n → ℕ} {k : ℕ} {j : Fin n} (h : lvl j ≤ k) :
    (Pi.single j 1 : Fin n → L) ∈ levelFlag (L := L) lvl k := by
  intro i hi
  have hij : i ≠ j := by
    rintro rfl
    omega
  simp [hij]

theorem levelFlag_eq_span (lvl : Fin n → ℕ) (k : ℕ) :
    levelFlag (L := L) lvl k
      = Submodule.span L ((fun j : Fin n => (Pi.single j 1 : Fin n → L)) '' {j | lvl j ≤ k}) := by
  classical
  refine le_antisymm ?_ ?_
  · intro v hv
    have hveq : v = ∑ j : Fin n, v j • (Pi.single j 1 : Fin n → L) := by
      funext i
      rw [Finset.sum_apply]
      rw [Finset.sum_eq_single i]
      · simp
      · intro l _ hl
        simp [Pi.single_apply, Ne.symm hl]
      · intro h
        exact absurd (Finset.mem_univ i) h
    rw [hveq]
    refine Submodule.sum_mem _ fun j _ => ?_
    by_cases hj : lvl j ≤ k
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)
    · rw [hv j (by omega), zero_smul]
      exact Submodule.zero_mem _
  · rw [Submodule.span_le]
    rintro _ ⟨j, hj, rfl⟩
    exact single_mem_levelFlag hj
theorem finrank_levelFlag (lvl : Fin n → ℕ) (k : ℕ) :
    Module.finrank L (levelFlag (L := L) lvl k)
      = (Finset.univ.filter fun i => lvl i ≤ k).card := by
  classical
  have hli : LinearIndependent L
      (fun i : {i : Fin n // lvl i ≤ k} => (Pi.single (i : Fin n) 1 : Fin n → L)) := by
    have h := Pi.basisFun L (Fin n) |>.linearIndependent
    have h2 := h.comp (fun i : {i : Fin n // lvl i ≤ k} => (i : Fin n)) Subtype.val_injective
    convert h2 using 1
    funext i
    simp [Pi.basisFun_apply]
  have hspan : Submodule.span L (Set.range
      (fun i : {i : Fin n // lvl i ≤ k} => (Pi.single (i : Fin n) 1 : Fin n → L)))
      = levelFlag (L := L) lvl k := by
    rw [levelFlag_eq_span]
    congr 1
    ext v
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨(i : Fin n), i.2, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
  rw [← hspan, finrank_span_eq_card hli]
  simp [Fintype.card_subtype]


end LevelFlag

section FlagFrame

variable {L : Type u} [Field L] {n : ℕ}

/-- **A frame adapted to a flag.**  A monotone chain of subspaces of `Lⁿ` from
`⊥` to `⊤` is the image of the coordinate flag of a monotone level function
under an invertible matrix: extend a basis of `V k` to one of `V (k+1)` at every
step, then sort the resulting basis by the level at which each vector entered.

This is `lem:local-model`(1) as pure linear algebra; the flag it is applied to
is the *fibre* flag of the pencil. -/
theorem exists_flagFrame (V : ℕ → Submodule L (Fin n → L)) (hmono : Monotone V)
    (hbot : V 0 = ⊥) (htop : V n = ⊤) :
    ∃ (lvl : Fin n → ℕ) (P : Matrix (Fin n) (Fin n) L),
      Monotone lvl ∧ IsUnit P.det ∧
      ∀ k, Submodule.map P.mulVecLin (levelFlag lvl k) = V k := by
  classical
  -- an increasing family of independent sets, `{v ∈ B | ℓ v ≤ j}` a basis of `V j`
  have main : ∀ k : ℕ, ∃ (B : Set (Fin n → L)) (ℓ : (Fin n → L) → ℕ),
      LinearIndepOn L id B ∧ (∀ v ∈ B, ℓ v ≤ k) ∧
      ∀ j ≤ k, Submodule.span L {v | v ∈ B ∧ ℓ v ≤ j} = V j := by
    intro k
    induction k with
    | zero =>
        refine ⟨∅, fun _ => 0, linearIndepOn_empty L id, by simp, ?_⟩
        intro j hj
        obtain rfl : j = 0 := Nat.le_zero.mp hj
        rw [hbot]
        have hset : {v : Fin n → L | v ∈ (∅ : Set (Fin n → L)) ∧ (0 : ℕ) ≤ 0} = ∅ := by
          ext v; simp
        rw [hset, Submodule.span_empty]
    | succ k ih =>
        obtain ⟨B, ℓ, hli, hle, hsp⟩ := ih
        have hBsub : B ⊆ (V (k + 1) : Set (Fin n → L)) := by
          intro v hv
          have hmem : v ∈ Submodule.span L {w | w ∈ B ∧ ℓ w ≤ k} :=
            Submodule.subset_span ⟨hv, hle v hv⟩
          rw [hsp k le_rfl] at hmem
          exact hmono (Nat.le_succ k) hmem
        obtain ⟨B', hB'sub, hBB', hspan', hli'⟩ := exists_linearIndepOn_id_extension hli hBsub
        refine ⟨B', fun v => if v ∈ B then ℓ v else k + 1, hli', ?_, ?_⟩
        · intro v _
          show (if v ∈ B then ℓ v else k + 1) ≤ k + 1
          by_cases h : v ∈ B
          · rw [if_pos h]
            exact le_trans (hle v h) (Nat.le_succ k)
          · rw [if_neg h]
        · intro j hj
          rcases Nat.lt_or_ge j (k + 1) with hjk | hjk
          · have hjk' : j ≤ k := by omega
            have hset : {v : Fin n → L | v ∈ B' ∧ (if v ∈ B then ℓ v else k + 1) ≤ j}
                = {v | v ∈ B ∧ ℓ v ≤ j} := by
              ext v
              constructor
              · rintro ⟨hvB', hvl⟩
                by_cases h : v ∈ B
                · rw [if_pos h] at hvl
                  exact ⟨h, hvl⟩
                · rw [if_neg h] at hvl
                  omega
              · rintro ⟨hvB, hvl⟩
                refine ⟨hBB' hvB, ?_⟩
                rw [if_pos hvB]
                exact hvl
            rw [hset]
            exact hsp j hjk'
          · obtain rfl : j = k + 1 := by omega
            have hset : {v : Fin n → L | v ∈ B' ∧ (if v ∈ B then ℓ v else k + 1) ≤ k + 1}
                = B' := by
              ext v
              refine ⟨fun h => h.1, fun hv => ⟨hv, ?_⟩⟩
              by_cases h : v ∈ B
              · rw [if_pos h]
                exact le_trans (hle v h) (Nat.le_succ k)
              · rw [if_neg h]
            rw [hset]
            refine le_antisymm ?_ ?_
            · rw [Submodule.span_le]
              exact hB'sub
            · intro v hv
              exact hspan' hv
  obtain ⟨B, ℓ, hli, hle, hsp⟩ := main n
  have hsetB : {v : Fin n → L | v ∈ B ∧ ℓ v ≤ n} = B := by
    ext v
    exact ⟨fun h => h.1, fun hv => ⟨hv, hle v hv⟩⟩
  have hspanB : Submodule.span L B = ⊤ := by
    have h := hsp n le_rfl
    rw [hsetB, htop] at h
    exact h
  have hrange : Set.range ((↑) : B → (Fin n → L)) = B := Subtype.range_coe
  have hlic : LinearIndependent L (fun x : ↥B => (x : Fin n → L)) := hli
  have hspc : ⊤ ≤ Submodule.span L (Set.range (fun x : ↥B => (x : Fin n → L))) := by
    rw [hrange, hspanB]
  set b0 : Basis ↥B L (Fin n → L) := Basis.mk hlic hspc with hb0
  have hb0apply : ∀ x : ↥B, b0 x = (x : Fin n → L) := by
    intro x
    rw [hb0]
    exact Basis.mk_apply hlic hspc x
  set e0 : ↥B ≃ Fin n := b0.indexEquiv (Pi.basisFun L (Fin n)) with he0
  set g : Fin n → ℕ := fun t => ℓ ((e0.symm t : Fin n → L)) with hgdef
  set s : Equiv.Perm (Fin n) := Tuple.sort g with hsdef
  set σ : Fin n ≃ ↥B := s.trans e0.symm with hσdef
  set lvl : Fin n → ℕ := fun t => ℓ ((σ t : Fin n → L)) with hlvl
  have hlvlmono : Monotone lvl := by
    have hm := Tuple.monotone_sort g
    intro a c hac
    exact hm hac
  set b : Basis (Fin n) L (Fin n → L) := b0.reindex σ.symm with hbdef
  have hbapply : ∀ t, b t = ((σ t : Fin n → L)) := by
    intro t
    rw [hbdef, Basis.reindex_apply, Equiv.symm_symm, hb0apply]
  set P : Matrix (Fin n) (Fin n) L := (Pi.basisFun L (Fin n)).toMatrix b with hP
  have hPcol : ∀ j : Fin n, P.mulVecLin (Pi.single j 1) = b j := by
    intro j
    funext i
    show (P *ᵥ (Pi.single j 1 : Fin n → L)) i = b j i
    rw [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single j]
    · simp [hP, Basis.toMatrix_apply]
    · intro l _ hl
      simp [Pi.single_apply, Ne.symm hl]
    · intro h
      exact absurd (Finset.mem_univ j) h
  refine ⟨lvl, P, hlvlmono, ?_, ?_⟩
  · have hinv := (Pi.basisFun L (Fin n)).invertibleToMatrix b
    exact (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_of_invertible _)
  · intro k
    have himg : (⇑b) '' {j | lvl j ≤ k}
        = {v : Fin n → L | v ∈ B ∧ ℓ v ≤ k} := by
      ext v
      constructor
      · rintro ⟨j, hj, rfl⟩
        rw [hbapply j]
        exact ⟨(σ j).2, hj⟩
      · rintro ⟨hvB, hvl⟩
        refine ⟨σ.symm ⟨v, hvB⟩, ?_, ?_⟩
        · show ℓ ((σ (σ.symm ⟨v, hvB⟩) : Fin n → L)) ≤ k
          rw [Equiv.apply_symm_apply]
          exact hvl
        · rw [hbapply, Equiv.apply_symm_apply]
    rw [levelFlag_eq_span, Submodule.map_span]
    have himg2 : (P.mulVecLin ''
          ((fun j : Fin n => (Pi.single j 1 : Fin n → L)) '' {j | lvl j ≤ k}))
        = (⇑b) '' {j | lvl j ≤ k} := by
      rw [Set.image_image]
      exact Set.image_congr fun j _ => hPcol j
    rw [himg2, himg]
    rcases Nat.lt_or_ge k n with hk | hk
    · exact hsp k (le_of_lt hk)
    · have hset : {v : Fin n → L | v ∈ B ∧ ℓ v ≤ k} = B := by
        ext v
        exact ⟨fun h => h.1, fun hv => ⟨hv, le_trans (hle v hv) hk⟩⟩
      rw [hset, hspanB]
      exact (top_le_iff.mp (htop ▸ hmono hk)).symm


/-- Reading a column off a matrix as the value on a standard basis vector. -/
theorem mulVec_single_one (A : Matrix (Fin n) (Fin n) L) (j : Fin n) :
    A *ᵥ (Pi.single j 1 : Fin n → L) = fun i => A i j := by
  classical
  funext i
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single j]
  · simp
  · intro l _ hl
    simp [Pi.single_apply, Ne.symm hl]
  · intro h
    exact absurd (Finset.mem_univ j) h


/-- Scaling a frame by a nonzero scalar does not change the flag it carries. -/
theorem map_smul_mulVecLin {c : L} (hc : c ≠ 0) (P : Matrix (Fin n) (Fin n) L)
    (S : Submodule L (Fin n → L)) :
    Submodule.map (c • P).mulVecLin S = Submodule.map P.mulVecLin S := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨v, hv, rfl⟩
    refine ⟨c • v, S.smul_mem c hv, ?_⟩
    show P *ᵥ (c • v) = (c • P) *ᵥ v
    rw [Matrix.mulVec_smul, Matrix.smul_mulVec]
  · rintro _ ⟨v, hv, rfl⟩
    refine ⟨c⁻¹ • v, S.smul_mem _ hv, ?_⟩
    show (c • P) *ᵥ (c⁻¹ • v) = P *ᵥ v
    rw [Matrix.mulVec_smul, Matrix.smul_mulVec, smul_smul, inv_mul_cancel₀ hc, one_smul]

/-- **`lem:local-model`(1) as linear algebra.**  A matrix that lowers a flag of
`Lⁿ` is block strict for the level function of any frame adapted to that flag:
the `j`-th column of the frame lies in `V (lvl j)`, so the member carries it
into `V (lvl j − 1)`, whose preimage under the frame is the coordinate flag at
level `lvl j − 1`. -/
theorem blockStrict_of_adapted {V : ℕ → Submodule L (Fin n → L)} {lvl : Fin n → ℕ}
    {P M : Matrix (Fin n) (Fin n) L} (hPdet : IsUnit P.det) (hbot : V 0 = ⊥)
    (hadapt : ∀ k, Submodule.map P.mulVecLin (levelFlag lvl k) = V k)
    (hlow : ∀ k, ∀ v ∈ V (k + 1), M *ᵥ v ∈ V k) :
    ∀ i j : Fin n, lvl j ≤ lvl i → (P⁻¹ * M * P) i j = 0 := by
  classical
  have hPP : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hPdet
  intro i j hle
  -- the `j`-th column of `P` lies in `V (lvl j)`
  have hcolj : P *ᵥ (Pi.single j 1 : Fin n → L) ∈ V (lvl j) := by
    rw [← hadapt (lvl j)]
    exact ⟨Pi.single j 1, single_mem_levelFlag le_rfl, rfl⟩
  -- and it is not zero, so `lvl j ≥ 1`
  have hne : P *ᵥ (Pi.single j 1 : Fin n → L) ≠ 0 := by
    intro h0
    have h1 : P⁻¹ *ᵥ (P *ᵥ (Pi.single j 1 : Fin n → L)) = 0 := by
      rw [h0, Matrix.mulVec_zero]
    rw [Matrix.mulVec_mulVec, hPP, Matrix.one_mulVec] at h1
    have h2 := congrFun h1 j
    simp at h2
  have hpos : 1 ≤ lvl j := by
    by_contra hcon
    have h0 : lvl j = 0 := by omega
    rw [h0, hbot] at hcolj
    exact hne (Submodule.mem_bot L |>.mp hcolj)
  -- so the member carries it into `V (lvl j - 1)`
  have hstep : M *ᵥ (P *ᵥ (Pi.single j 1 : Fin n → L)) ∈ V (lvl j - 1) := by
    refine hlow (lvl j - 1) _ ?_
    rw [show lvl j - 1 + 1 = lvl j by omega]
    exact hcolj
  rw [← hadapt (lvl j - 1)] at hstep
  obtain ⟨w, hw, hwP⟩ := hstep
  have hcol : (P⁻¹ * M * P) *ᵥ (Pi.single j 1 : Fin n → L) = w := by
    have h1 : (P⁻¹ * M * P) *ᵥ (Pi.single j 1 : Fin n → L)
        = P⁻¹ *ᵥ (M *ᵥ (P *ᵥ (Pi.single j 1 : Fin n → L))) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
    rw [h1, ← hwP, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hPP, Matrix.one_mulVec]
  have hij : (P⁻¹ * M * P) i j = w i := by
    have h2 : ((P⁻¹ * M * P) *ᵥ (Pi.single j 1 : Fin n → L)) i = w i := congrFun hcol i
    rw [mulVec_single_one] at h2
    exact h2
  rw [hij]
  exact hw i (by omega)

/-- Clause (1) in one statement: a frame adapted to the flag, its monotone level
function, and the block-strict conjugate. -/
theorem exists_blockStrict_of_flag (V : ℕ → Submodule L (Fin n → L)) (hmono : Monotone V)
    (hbot : V 0 = ⊥) (htop : V n = ⊤) (M : Matrix (Fin n) (Fin n) L)
    (hlow : ∀ k, ∀ v ∈ V (k + 1), M *ᵥ v ∈ V k) :
    ∃ (lvl : Fin n → ℕ) (A P : Matrix (Fin n) (Fin n) L),
      Monotone lvl ∧ IsUnit P.det ∧ (∀ i j : Fin n, lvl j ≤ lvl i → A i j = 0) ∧
      M * P = P * A ∧ ∀ k, Submodule.map P.mulVecLin (levelFlag lvl k) = V k := by
  obtain ⟨lvl, P, hlvlmono, hPdet, hadapt⟩ := exists_flagFrame V hmono hbot htop
  have hPP' : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hPdet
  refine ⟨lvl, P⁻¹ * M * P, P, hlvlmono, hPdet,
    blockStrict_of_adapted hPdet hbot hadapt hlow, ?_, hadapt⟩
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hPP', Matrix.one_mul]

end FlagFrame

end Height.Toolbox
