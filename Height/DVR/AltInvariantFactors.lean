import Height.DVR.AltHyperbolic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.ZMod.Basic

/-!
# `lem:local-pairing`, second half: the block involution of the normal form

The hyperbolic normal form `hypNF n d` is a *monomial* matrix: each row has at
most one nonzero entry.  This file proves that decomposition and the two
properties of the involution `blockInvol` pairing the coordinates of each
hyperbolic block:

* `hypNF_eq_diagonal_mul_permMatrix` —
  `hypNF R n d = diagonal (hypRow d) * permMatrix blockInvol`;
* `hypRow_blockInvol` — the entries pair up, `hypRow d (ι i) = -hypRow d i`;
* `blockInvol_ne_of_hypRow_ne_zero` — the involution has no fixed point where
  the entry is nonzero.

The consequences of these are **not** in this file; they are
statements about a Smith presentation and live in
`DVR/AlternatingPresentation.lean`: the paired diagonalisation of an
alternating matrix is `exists_alternatingPresentation`, the rank of a
specialisation is `AlternatingPresentation.rank_map`, and the difference of
coranks over the residue field and over the fraction field is
`AlternatingPresentation.two_card_blocks_add_rank` (`D_x = c(τ(x)) − c(τ)` in
the notation of the paper, and even by construction).
-/

namespace Height.DVR

open Matrix Finset

universe u

section Involution

variable {n : ℕ}

/-- The involution pairing the two coordinates of each hyperbolic block of
`hypNF n d`; the leftover coordinate (present when `n` is odd) is fixed. -/
def blockInvolFun (i : Fin n) : Fin n :=
  if h : Even ((i : ℕ) + n) then
    ⟨(i : ℕ) + 1, by
      have hi := i.isLt
      obtain ⟨t, ht⟩ := h
      omega⟩
  else if (i : ℕ) = 0 then i
  else ⟨(i : ℕ) - 1, by have := i.isLt; omega⟩

theorem blockInvolFun_of_even {i : Fin n} (h : Even ((i : ℕ) + n)) :
    ((blockInvolFun i : Fin n) : ℕ) = (i : ℕ) + 1 := by
  rw [blockInvolFun, dite_eq_left h]

theorem blockInvolFun_of_odd_pos {i : Fin n} (h : ¬Even ((i : ℕ) + n))
    (h0 : (i : ℕ) ≠ 0) : ((blockInvolFun i : Fin n) : ℕ) = (i : ℕ) - 1 := by
  rw [blockInvolFun, dite_eq_right h, ite_eq_right h0]

theorem blockInvolFun_of_odd_zero {i : Fin n} (h : ¬Even ((i : ℕ) + n))
    (h0 : (i : ℕ) = 0) : blockInvolFun i = i := by
  rw [blockInvolFun, dite_eq_right h, ite_eq_left h0]

theorem blockInvolFun_involutive : Function.Involutive (blockInvolFun (n := n)) := by
  intro i
  have hi := i.isLt
  by_cases h : Even ((i : ℕ) + n)
  · have h1 : ((blockInvolFun i : Fin n) : ℕ) = (i : ℕ) + 1 := blockInvolFun_of_even h
    have h2 : ¬Even (((blockInvolFun i : Fin n) : ℕ) + n) := by
      rw [h1]
      rw [Nat.even_iff] at h ⊢
      omega
    have h3 : ((blockInvolFun i : Fin n) : ℕ) ≠ 0 := by omega
    apply Fin.ext
    rw [blockInvolFun_of_odd_pos h2 h3, h1]
    omega
  · by_cases h0 : (i : ℕ) = 0
    · rw [blockInvolFun_of_odd_zero h h0, blockInvolFun_of_odd_zero h h0]
    · have h1 : ((blockInvolFun i : Fin n) : ℕ) = (i : ℕ) - 1 :=
        blockInvolFun_of_odd_pos h h0
      have h2 : Even (((blockInvolFun i : Fin n) : ℕ) + n) := by
        rw [h1]
        rw [Nat.even_iff] at h ⊢
        omega
      apply Fin.ext
      rw [blockInvolFun_of_even h2, h1]
      omega

/-- The block involution as a permutation. -/
def blockInvol : Equiv.Perm (Fin n) :=
  Function.Involutive.toPerm _ blockInvolFun_involutive

@[simp] theorem blockInvol_apply (i : Fin n) : blockInvol i = blockInvolFun i := rfl

theorem blockInvol_involutive (i : Fin n) :
    blockInvol (blockInvol i) = i := blockInvolFun_involutive i

end Involution

section Monomial

variable {R : Type u} [CommRing R] {n : ℕ}

/-- The unique nonzero entry of row `i` of `hypNF n d`, at column
`blockInvol i`. -/
def hypRow (d : ℕ → R) (i : Fin n) : R :=
  if Even ((i : ℕ) + n) then d (i : ℕ)
  else if (i : ℕ) = 0 then 0 else -d ((i : ℕ) - 1)

/-- The normal form is a monomial matrix: `diagonal (hypRow d)` times the
permutation matrix of the block involution. -/
theorem hypNF_eq_diagonal_mul_permMatrix (d : ℕ → R) :
    hypNF R n d
      = Matrix.diagonal (hypRow (n := n) d) * Equiv.Perm.permMatrix R blockInvol := by
  classical
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  have hperm : (Equiv.Perm.permMatrix R (blockInvol (n := n))) i j
      = if blockInvol i = j then (1 : R) else 0 := by
    simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, eq_comm]
  rw [Matrix.diagonal_mul, hperm, hypNF_apply, hypRow]
  by_cases h : Even ((i : ℕ) + n)
  · have hb : ((blockInvol (n := n) i : Fin n) : ℕ) = (i : ℕ) + 1 :=
      blockInvolFun_of_even h
    rw [ite_eq_left h]
    by_cases hji : (j : ℕ) = (i : ℕ) + 1
    · have : blockInvol (n := n) i = j := Fin.ext (by rw [hb, hji])
      rw [ite_eq_left ⟨hji, h⟩, ite_eq_left this, mul_one]
    · have hne : ¬(blockInvol (n := n) i = j) := by
        intro hc; exact hji (by rw [← hc, hb])
      have h2 : ¬((i : ℕ) = (j : ℕ) + 1 ∧ Even ((j : ℕ) + n)) := by
        rintro ⟨he, hev⟩
        rw [Nat.even_iff] at h hev
        omega
      rw [ite_eq_right (by rintro ⟨hc, -⟩; exact hji hc), ite_eq_right h2,
        ite_eq_right hne, mul_zero]
  · by_cases h0 : (i : ℕ) = 0
    · have hb : blockInvol (n := n) i = i := blockInvolFun_of_odd_zero h h0
      have h1 : ¬((j : ℕ) = (i : ℕ) + 1 ∧ Even ((i : ℕ) + n)) := by
        rintro ⟨-, hev⟩; exact h hev
      have h2 : ¬((i : ℕ) = (j : ℕ) + 1 ∧ Even ((j : ℕ) + n)) := by
        rintro ⟨he, -⟩; omega
      rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h, ite_eq_left h0, zero_mul]
    · have hb : ((blockInvol (n := n) i : Fin n) : ℕ) = (i : ℕ) - 1 :=
        blockInvolFun_of_odd_pos h h0
      rw [ite_eq_right h, ite_eq_right h0,
        ite_eq_right (by rintro ⟨-, hev⟩; exact h hev)]
      by_cases hji : (i : ℕ) = (j : ℕ) + 1
      · have hjv : (j : ℕ) = (i : ℕ) - 1 := by omega
        have hev : Even ((j : ℕ) + n) := by
          rw [Nat.even_iff] at h ⊢; omega
        have : blockInvol (n := n) i = j := Fin.ext (by rw [hb, hjv])
        rw [ite_eq_left ⟨hji, hev⟩, ite_eq_left this, mul_one, hjv]
      · have hne : ¬(blockInvol (n := n) i = j) := by
          intro hc
          apply hji
          have : (j : ℕ) = (i : ℕ) - 1 := by rw [← hc, hb]
          omega
        rw [ite_eq_right (by rintro ⟨hc, -⟩; exact hji hc), ite_eq_right hne,
          mul_zero]

/-- The diagonal entries pair up: the two coordinates of a hyperbolic block
carry the negatives of one another. -/
theorem hypRow_blockInvol (d : ℕ → R) (i : Fin n) :
    hypRow d (blockInvol i) = -hypRow (n := n) d i := by
  have hi := i.isLt
  by_cases h : Even ((i : ℕ) + n)
  · have hb : ((blockInvol (n := n) i : Fin n) : ℕ) = (i : ℕ) + 1 :=
      blockInvolFun_of_even h
    have h2 : ¬Even (((blockInvol (n := n) i : Fin n) : ℕ) + n) := by
      rw [hb]; rw [Nat.even_iff] at h ⊢; omega
    have h3 : ((blockInvol (n := n) i : Fin n) : ℕ) ≠ 0 := by omega
    rw [hypRow, hypRow, ite_eq_right h2, ite_eq_right h3, ite_eq_left h, hb]
    simp
  · by_cases h0 : (i : ℕ) = 0
    · have hb : blockInvol (n := n) i = i := blockInvolFun_of_odd_zero h h0
      rw [hb, hypRow, ite_eq_right h, ite_eq_left h0, neg_zero]
    · have hb : ((blockInvol (n := n) i : Fin n) : ℕ) = (i : ℕ) - 1 :=
        blockInvolFun_of_odd_pos h h0
      have h2 : Even (((blockInvol (n := n) i : Fin n) : ℕ) + n) := by
        rw [hb]; rw [Nat.even_iff] at h ⊢; omega
      rw [hypRow, hypRow, ite_eq_left h2, ite_eq_right h, ite_eq_right h0, hb,
        neg_neg]

/-- The involution has no fixed point where the diagonal entry is nonzero. -/
theorem blockInvol_ne_of_hypRow_ne_zero (d : ℕ → R) (i : Fin n)
    (h : hypRow d i ≠ 0) : blockInvol i ≠ i := by
  have hi := i.isLt
  intro hfix
  have hval : ((blockInvol (n := n) i : Fin n) : ℕ) = (i : ℕ) := congrArg Fin.val hfix
  apply h
  by_cases hev : Even ((i : ℕ) + n)
  · have hb : ((blockInvol (n := n) i : Fin n) : ℕ) = (i : ℕ) + 1 :=
      blockInvolFun_of_even hev
    exact absurd hval (by omega)
  · by_cases h0 : (i : ℕ) = 0
    · rw [hypRow, ite_eq_right hev, ite_eq_left h0]
    · have hb : ((blockInvol (n := n) i : Fin n) : ℕ) = (i : ℕ) - 1 :=
        blockInvolFun_of_odd_pos hev h0
      exact absurd hval (by omega)

end Monomial

end Height.DVR
