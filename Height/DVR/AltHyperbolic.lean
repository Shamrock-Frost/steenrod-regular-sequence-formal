import Height.DVR.AltNormalForm

/-!
# `lem:local-pairing`: the hyperbolic normal form

An alternating matrix over a valuation ring (in particular over `K⟦u⟧`, or any
discrete valuation ring) is congruent to `hypNF`, a direct sum of hyperbolic
blocks `[[0, dᵢ], [-dᵢ, 0]]` and zeros.
-/

namespace Height.DVR

open Matrix Finset

universe u

variable {R : Type u} [CommRing R]

section Pivot

/-- In a valuation ring, some member of a nonempty finite family divides all of
its members: this is the "entry of minimal valuation" of `lem:local-pairing`. -/
theorem exists_dvd_all [IsDomain R] [ValuationRing R] {α : Type*} (f : α → R)
    (s : Finset α) : s.Nonempty → ∃ a ∈ s, ∀ b ∈ s, f a ∣ f b := by
  classical
  induction s using Finset.induction with
  | empty => intro hs; simp at hs
  | insert x t hx ih =>
      intro _
      rcases t.eq_empty_or_nonempty with rfl | ht
      · refine ⟨x, Finset.mem_insert_self _ _, fun z hz => ?_⟩
        simp only [Finset.mem_insert, Finset.notMem_empty, or_false] at hz
        subst hz
        exact dvd_rfl
      · obtain ⟨y, hy, hyall⟩ := ih ht
        rcases ValuationRing.dvd_total (f x) (f y) with h | h
        · refine ⟨x, Finset.mem_insert_self _ _, fun z hz => ?_⟩
          rcases Finset.mem_insert.mp hz with rfl | hz
          · exact dvd_rfl
          · exact h.trans (hyall z hz)
        · refine ⟨y, Finset.mem_insert_of_mem hy, fun z hz => ?_⟩
          rcases Finset.mem_insert.mp hz with rfl | hz
          · exact h
          · exact hyall z hz

/-- A nonzero matrix over a valuation ring has an entry dividing every entry. -/
theorem exists_pivot [IsDomain R] [ValuationRing R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) (hM : M ≠ 0) :
    ∃ p q : Fin n, M p q ≠ 0 ∧ ∀ i j, M p q ∣ M i j := by
  classical
  have hne : (Finset.univ.filter fun r : Fin n × Fin n => M r.1 r.2 ≠ 0).Nonempty := by
    rw [Finset.filter_nonempty_iff]
    by_contra hcon
    apply hM
    ext i j
    simp only [Matrix.zero_apply]
    by_contra hij
    exact hcon ⟨(i, j), Finset.mem_univ _, hij⟩
  obtain ⟨r, hr, hall⟩ :=
    exists_dvd_all (fun r : Fin n × Fin n => M r.1 r.2) _ hne
  refine ⟨r.1, r.2, (Finset.mem_filter.mp hr).2, fun i j => ?_⟩
  by_cases hij : M i j = 0
  · rw [hij]; exact dvd_zero _
  · exact hall (i, j) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩)

end Pivot

section PermCongr

/-- Reindexing by a permutation is a congruence by an invertible matrix. -/
theorem exists_perm_congr {n : ℕ} (M : Matrix (Fin n) (Fin n) R)
    (τ : Equiv.Perm (Fin n)) :
    ∃ U : Matrix (Fin n) (Fin n) R, IsUnit U.det ∧
      Uᵀ * M * U = M.submatrix τ τ := by
  classical
  refine ⟨Equiv.Perm.permMatrix R τ⁻¹, ?_, ?_⟩
  · rw [Matrix.det_permutation]
    simpa using Units.isUnit
      (Units.map (Int.castRingHom R).toMonoidHom (Equiv.Perm.sign τ⁻¹))
  · have hcol : ∀ l : Fin n,
        (fun i => Equiv.Perm.permMatrix R τ⁻¹ i l) = Pi.single (τ l) 1 := by
      intro l
      funext i
      by_cases h : i = τ l
      · subst h
        simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
          Equiv.toPEquiv_apply]
      · have h2 : τ.symm i ≠ l := by
          intro hc
          exact h (by rw [← hc]; simp)
        simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
          Equiv.toPEquiv_apply, h, h2]
    ext k l
    rw [transpose_mul_mul_apply, hcol, hcol, gramPair_single_single]
    rfl

end PermCongr

section Clearing

/-- The clearing step of `lem:local-pairing`: if the entry `a = N e₀ e₁` of an
alternating matrix divides every entry, a unipotent congruence makes the two
coordinates `e₀, e₁` an orthogonal hyperbolic summand. -/
theorem exists_clearing {m : ℕ} (N : Matrix (Fin (m + 2)) (Fin (m + 2)) R)
    (hN : IsAltMatrix N) (a : R) (e₀ e₁ : Fin (m + 2))
    (he₀ : (e₀ : ℕ) = m) (he₁ : (e₁ : ℕ) = m + 1)
    (hpiv : N e₀ e₁ = a) (hdvd : ∀ i j, a ∣ N i j) :
    ∃ T : Matrix (Fin (m + 2)) (Fin (m + 2)) R, IsUnit T.det ∧
      (∀ k : Fin (m + 2), (k : ℕ) < m →
        (Tᵀ * N * T) k e₀ = 0 ∧ (Tᵀ * N * T) e₀ k = 0 ∧
          (Tᵀ * N * T) k e₁ = 0 ∧ (Tᵀ * N * T) e₁ k = 0) ∧
      (Tᵀ * N * T) e₀ e₁ = a ∧ (Tᵀ * N * T) e₁ e₀ = -a := by
  classical
  choose c hc using fun k : Fin (m + 2) => hdvd e₀ k
  choose b hb using fun k : Fin (m + 2) => hdvd e₁ k
  -- `hc k : N e₀ k = a * c k`, `hb k : N e₁ k = a * b k`
  set b' : Fin (m + 2) → R := fun k => if (k : ℕ) < m then b k else 0 with hb'
  set c' : Fin (m + 2) → R := fun k => if (k : ℕ) < m then c k else 0 with hc'
  set w : Fin (m + 2) → (Fin (m + 2) → R) := fun k =>
    Pi.single k 1 + b' k • Pi.single e₀ 1 - c' k • Pi.single e₁ 1 with hw
  set T : Matrix (Fin (m + 2)) (Fin (m + 2)) R := Matrix.of fun i k => w k i
    with hT
  -- elementary facts
  have hne01 : e₀ ≠ e₁ := by
    intro h; rw [h, he₁] at he₀; omega
  have hb'0 : b' e₀ = 0 := by simp [hb', he₀]
  have hc'0 : c' e₀ = 0 := by simp [hc', he₀]
  have hb'1 : b' e₁ = 0 := by simp [hb', he₁]
  have hc'1 : c' e₁ = 0 := by simp [hc', he₁]
  have hb'lt : ∀ k : Fin (m + 2), (k : ℕ) < m → b' k = b k := by
    intro k hk; simp [hb', hk]
  have hc'lt : ∀ k : Fin (m + 2), (k : ℕ) < m → c' k = c k := by
    intro k hk; simp [hc', hk]
  have hN00 : N e₀ e₀ = 0 := hN.diag e₀
  have hN11 : N e₁ e₁ = 0 := hN.diag e₁
  have hN10 : N e₁ e₀ = -a := by rw [hN.skew e₀ e₁, hpiv]
  have hNk0 : ∀ k, N k e₀ = -(a * c k) := by
    intro k; rw [hN.skew e₀ k, hc k]
  have hNk1 : ∀ k, N k e₁ = -(a * b k) := by
    intro k; rw [hN.skew e₁ k, hb k]
  -- the congruence in terms of the pairing
  have hpair : ∀ k l, (Tᵀ * N * T) k l = gramPair N (w k) (w l) := by
    intro k l
    rw [transpose_mul_mul_apply]
    rfl
  have hexp : ∀ k l, gramPair N (w k) (w l) =
      (N k l + b' l * N k e₀ - c' l * N k e₁)
      + b' k * (N e₀ l + b' l * N e₀ e₀ - c' l * N e₀ e₁)
      - c' k * (N e₁ l + b' l * N e₁ e₀ - c' l * N e₁ e₁) := by
    intro k l
    simp only [hw, gramPair_sub_left, gramPair_add_left, gramPair_smul_left,
      gramPair_sub_right, gramPair_add_right, gramPair_smul_right,
      gramPair_single_single]
    ring
  refine ⟨T, ?_, ?_, ?_, ?_⟩
  · -- `T` is unipotent lower triangular
    have hdiag : ∀ k, T k k = 1 := by
      intro k
      have h1 : b' k * ((Pi.single e₀ 1 : Fin (m + 2) → R) k) = 0 := by
        by_cases hk : k = e₀
        · rw [hk, hb'0, zero_mul]
        · rw [Pi.single_apply, ite_eq_right hk, mul_zero]
      have h2 : c' k * ((Pi.single e₁ 1 : Fin (m + 2) → R) k) = 0 := by
        by_cases hk : k = e₁
        · rw [hk, hc'1, zero_mul]
        · rw [Pi.single_apply, ite_eq_right hk, mul_zero]
      show w k k = 1
      rw [hw]
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Pi.single_eq_same]
      rw [h1, h2]
      ring
    have hlow : T.IsLowerTriangular := by
      intro i j hij
      have hij' : (i : ℕ) < (j : ℕ) := hij
      have hjlt := j.isLt
      have h0 : (Pi.single j 1 : Fin (m + 2) → R) i = 0 := by
        rw [Pi.single_apply, ite_eq_right]
        intro h; rw [h] at hij'; omega
      have h1 : b' j * ((Pi.single e₀ 1 : Fin (m + 2) → R) i) = 0 := by
        by_cases hi : i = e₀
        · have hjm : ¬((j : ℕ) < m) := by rw [hi, he₀] at hij'; omega
          have hbj : b' j = 0 := by rw [hb']; exact ite_eq_right hjm
          rw [hbj, zero_mul]
        · rw [Pi.single_apply, ite_eq_right hi, mul_zero]
      have h2 : c' j * ((Pi.single e₁ 1 : Fin (m + 2) → R) i) = 0 := by
        by_cases hi : i = e₁
        · exact absurd hij' (by rw [hi, he₁]; omega)
        · rw [Pi.single_apply, ite_eq_right hi, mul_zero]
      show w j i = 0
      rw [hw]
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [h0, h1, h2]
      ring
    rw [Matrix.det_of_isLowerTriangular T hlow]
    simp [hdiag]
  · intro k hk
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hpair, hexp, hb'0, hc'0, hb'lt k hk, hc'lt k hk, hNk0, hN00, hN10]
      ring
    · rw [hpair, hexp, hb'0, hc'0, hb'lt k hk, hc'lt k hk, hc k, hN00, hpiv]
      ring
    · rw [hpair, hexp, hb'1, hc'1, hb'lt k hk, hc'lt k hk, hNk1, hpiv, hN11]
      ring
    · rw [hpair, hexp, hb'1, hc'1, hb'lt k hk, hc'lt k hk, hb k, hN10, hN11]
      ring
  · rw [hpair, hexp, hb'0, hc'0, hb'1, hc'1, hpiv]
    ring
  · rw [hpair, hexp, hb'0, hc'0, hb'1, hc'1, hN10]
    ring

end Clearing

section Assembly

/-- A congruence by a reindexed block matrix is the reindexed block
congruence. -/
theorem transpose_reindex_mul_mul {m : ℕ}
    (C : Matrix (Fin (m + 2)) (Fin (m + 2)) R)
    (A : Matrix (Fin m ⊕ Fin 2) (Fin m ⊕ Fin 2) R) :
    (Matrix.reindex finSumFinEquiv finSumFinEquiv A)ᵀ * C *
        (Matrix.reindex finSumFinEquiv finSumFinEquiv A)
      = Matrix.reindex finSumFinEquiv finSumFinEquiv
          (Aᵀ * C.submatrix finSumFinEquiv finSumFinEquiv * A) := by
  have hC : C = (C.submatrix finSumFinEquiv finSumFinEquiv).submatrix
      finSumFinEquiv.symm finSumFinEquiv.symm := by
    rw [Matrix.submatrix_submatrix]
    simp
  rw [Matrix.reindex_apply, Matrix.transpose_submatrix]
  conv_lhs => rw [hC]
  rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv,
    Matrix.reindex_apply]

end Assembly

section Main

/-- `lem:local-pairing`.  An alternating matrix over a valuation ring — for
instance over `PowerSeries K`, or any discrete valuation ring — is congruent by
an invertible matrix to a direct sum of hyperbolic blocks
`[[0, dᵢ], [-dᵢ, 0]]` and zeros. -/
theorem alt_hyperbolic [IsDomain R] [ValuationRing R] :
    ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) R), IsAltMatrix M →
      ∃ (U : Matrix (Fin n) (Fin n) R) (d : ℕ → R),
        IsUnit U.det ∧ Uᵀ * M * U = hypNF R n d := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro M hM
  classical
  by_cases hzero : M = 0
  · refine ⟨1, fun _ => 0, by simp, ?_⟩
    rw [hzero, hypNF_zero]
    simp
  obtain ⟨p, q, hpq0, hpqdvd⟩ := exists_pivot M hzero
  have hpq : p ≠ q := by
    intro h
    rw [h, hM.diag] at hpq0
    exact hpq0 rfl
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := by
    have h1 := p.isLt
    have h2 := q.isLt
    have h3 : (p : ℕ) ≠ (q : ℕ) := fun h => hpq (Fin.ext h)
    exact ⟨n - 2, by omega⟩
  obtain ⟨e₀, he₀⟩ : ∃ e : Fin (m + 2), (e : ℕ) = m := ⟨⟨m, by omega⟩, rfl⟩
  obtain ⟨e₁, he₁⟩ : ∃ e : Fin (m + 2), (e : ℕ) = m + 1 := ⟨⟨m + 1, by omega⟩, rfl⟩
  have hne01 : e₀ ≠ e₁ := by
    intro h; rw [h, he₁] at he₀; omega
  -- a permutation carrying the last two coordinates to the pivot
  obtain ⟨τ, hτ0, hτ1⟩ : ∃ τ : Equiv.Perm (Fin (m + 2)), τ e₀ = p ∧ τ e₁ = q := by
    have hq' : Equiv.swap e₀ p q ≠ e₀ := by
      intro h
      apply hpq
      have h2 := congrArg (Equiv.swap e₀ p) h
      rw [Equiv.swap_apply_self, Equiv.swap_apply_left] at h2
      exact h2.symm
    refine ⟨Equiv.swap e₀ p * Equiv.swap e₁ (Equiv.swap e₀ p q), ?_, ?_⟩
    · show Equiv.swap e₀ p (Equiv.swap e₁ (Equiv.swap e₀ p q) e₀) = p
      rw [Equiv.swap_apply_of_ne_of_ne hne01 (Ne.symm hq'), Equiv.swap_apply_left]
    · show Equiv.swap e₀ p (Equiv.swap e₁ (Equiv.swap e₀ p q) e₁) = q
      rw [Equiv.swap_apply_left, Equiv.swap_apply_self]
  obtain ⟨U₁, hU₁det, hU₁⟩ := exists_perm_congr M τ
  obtain ⟨N, hNdef⟩ : ∃ N : Matrix (Fin (m + 2)) (Fin (m + 2)) R,
      N = M.submatrix τ τ := ⟨_, rfl⟩
  have hNalt : IsAltMatrix N := hNdef ▸ hM.submatrix τ
  have hNpiv : N e₀ e₁ = M p q := by
    rw [hNdef, Matrix.submatrix_apply, hτ0, hτ1]
  have hNdvd : ∀ i j, M p q ∣ N i j := by
    intro i j; rw [hNdef]; exact hpqdvd _ _
  obtain ⟨T, hTdet, hTcross, hTa, hTa'⟩ :=
    exists_clearing N hNalt (M p q) e₀ e₁ he₀ he₁ hNpiv hNdvd
  obtain ⟨C, hCdef⟩ : ∃ C : Matrix (Fin (m + 2)) (Fin (m + 2)) R,
      C = Tᵀ * N * T := ⟨_, rfl⟩
  have hCalt : IsAltMatrix C := hCdef ▸ hNalt.congr T
  obtain ⟨N', hN'def⟩ : ∃ N' : Matrix (Fin m) (Fin m) R,
      N' = C.submatrix (Fin.castAdd 2) (Fin.castAdd 2) := ⟨_, rfl⟩
  obtain ⟨U', d', hU'det, hU'⟩ :=
    ih m (by omega) N' (hN'def ▸ hCalt.submatrix (Fin.castAdd 2))
  -- assemble
  obtain ⟨A, hAdef⟩ : ∃ A : Matrix (Fin m ⊕ Fin 2) (Fin m ⊕ Fin 2) R,
      A = Matrix.fromBlocks U' 0 0 1 := ⟨_, rfl⟩
  obtain ⟨U₂, hU₂def⟩ : ∃ U₂ : Matrix (Fin (m + 2)) (Fin (m + 2)) R,
      U₂ = Matrix.reindex finSumFinEquiv finSumFinEquiv A := ⟨_, rfl⟩
  have hnat0 : ∀ j : Fin 2, (j : ℕ) = 0 → Fin.natAdd m j = e₀ := by
    intro j hj
    apply Fin.ext
    rw [Fin.val_natAdd, hj, he₀]
    omega
  have hnat1 : ∀ j : Fin 2, (j : ℕ) = 1 → Fin.natAdd m j = e₁ := by
    intro j hj
    apply Fin.ext
    rw [Fin.val_natAdd, hj, he₁]
  have hCblocks : C.submatrix finSumFinEquiv finSumFinEquiv
      = Matrix.fromBlocks N' 0 0 (hyp2 (M p q)) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · rw [Matrix.submatrix_apply, finSumFinEquiv_apply_left,
        finSumFinEquiv_apply_left, Matrix.fromBlocks_apply₁₁, hN'def,
        Matrix.submatrix_apply]
    · rw [Matrix.submatrix_apply, finSumFinEquiv_apply_left,
        finSumFinEquiv_apply_right, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]
      have hi : ((Fin.castAdd 2 i : Fin (m + 2)) : ℕ) < m := by
        simp
      have hj2 := j.isLt
      rw [hCdef]
      rcases (by omega : (j : ℕ) = 0 ∨ (j : ℕ) = 1) with hj | hj
      · rw [hnat0 j hj]; exact (hTcross _ hi).1
      · rw [hnat1 j hj]; exact (hTcross _ hi).2.2.1
    · rw [Matrix.submatrix_apply, finSumFinEquiv_apply_right,
        finSumFinEquiv_apply_left, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
      have hj : ((Fin.castAdd 2 j : Fin (m + 2)) : ℕ) < m := by
        simp
      have hi2 := i.isLt
      rw [hCdef]
      rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1) with hi | hi
      · rw [hnat0 i hi]; exact (hTcross _ hj).2.1
      · rw [hnat1 i hi]; exact (hTcross _ hj).2.2.2
    · rw [Matrix.submatrix_apply, finSumFinEquiv_apply_right,
        finSumFinEquiv_apply_right, Matrix.fromBlocks_apply₂₂, hyp2_apply]
      have hi2 := i.isLt
      have hj2 := j.isLt
      rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1) with hi | hi <;>
        rcases (by omega : (j : ℕ) = 0 ∨ (j : ℕ) = 1) with hj | hj
      · rw [hi, hj, ite_eq_right (by rintro ⟨-, h⟩; omega),
          ite_eq_right (by rintro ⟨h, -⟩; omega), hnat0 i hi, hnat0 j hj]
        exact hCalt.diag e₀
      · rw [hi, hj, ite_eq_left (⟨rfl, rfl⟩ : (0 : ℕ) = 0 ∧ (1 : ℕ) = 1),
          hnat0 i hi, hnat1 j hj, hCdef]
        exact hTa
      · rw [hi, hj, ite_eq_right (by rintro ⟨h, -⟩; omega),
          ite_eq_left (⟨rfl, rfl⟩ : (1 : ℕ) = 1 ∧ (0 : ℕ) = 0),
          hnat1 i hi, hnat0 j hj, hCdef]
        exact hTa'
      · rw [hi, hj, ite_eq_right (by rintro ⟨h, -⟩; omega),
          ite_eq_right (by rintro ⟨-, h⟩; omega), hnat1 i hi, hnat1 j hj]
        exact hCalt.diag e₁
  have hd : Function.update d' m (M p q) m = M p q := Function.update_self _ _ _
  have hdlt : hypNF R m (Function.update d' m (M p q)) = hypNF R m d' := by
    refine hypNF_congr m fun k hk => ?_
    exact Function.update_of_ne (by omega) _ _
  refine ⟨U₁ * T * U₂, Function.update d' m (M p q), ?_, ?_⟩
  · rw [Matrix.det_mul, Matrix.det_mul]
    refine (hU₁det.mul hTdet).mul ?_
    rw [hU₂def, Matrix.det_reindex_self, hAdef, Matrix.det_fromBlocks_zero₁₂,
      Matrix.det_one, mul_one]
    exact hU'det
  · have hassoc : (U₁ * T * U₂)ᵀ * M * (U₁ * T * U₂)
        = U₂ᵀ * (Tᵀ * (U₁ᵀ * M * U₁) * T) * U₂ := by
      simp only [Matrix.transpose_mul]
      noncomm_ring
    have hblock : Aᵀ * C.submatrix finSumFinEquiv finSumFinEquiv * A
        = Matrix.fromBlocks (hypNF R m d') 0 0 (hyp2 (M p q)) := by
      rw [hCblocks, hAdef, Matrix.fromBlocks_transpose, Matrix.transpose_zero,
        Matrix.transpose_one, Matrix.fromBlocks_multiply,
        Matrix.fromBlocks_multiply]
      simp [hU']
    have hdd : Matrix.fromBlocks (hypNF R m d') 0 0 (hyp2 (M p q))
        = Matrix.fromBlocks (hypNF R m (Function.update d' m (M p q))) 0 0
            (hyp2 (Function.update d' m (M p q) m)) := by
      rw [hdlt, hd]
    rw [hassoc, hU₁, ← hNdef, ← hCdef, hU₂def, transpose_reindex_mul_mul,
      hblock, hdd, ← hypNF_submatrix_finSumFinEquiv,
      Matrix.reindex_apply, Matrix.submatrix_submatrix]
    simp

end Main

end Height.DVR
