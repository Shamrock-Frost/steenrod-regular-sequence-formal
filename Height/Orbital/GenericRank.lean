import Height.Toolbox.MinorRank
import Mathlib.RingTheory.Ideal.Operations

/-!
# The generic rank of a matrix over a domain

An input to `thm:star`.  Let `P` be a prime ideal of a
commutative ring `R` and `M` a matrix over `R`.  There is a largest `r` for
which some `r × r` minor of `M` avoids `P`; call that minor `δ`.  Then for
*every* homomorphism `φ : R → S` into a field which kills `P` and does not
kill `δ`, the rank of `M` over `S` is exactly `r`: the lower bound because
`φ δ ≠ 0`, the upper bound because all `(r+1) × (r+1)` minors lie in `P`
(`MinorRank.rank_eq_of_minors`).

This is the only form in which genericity is used in the proof of `(∗)`: the
two homomorphisms that matter are evaluation at a point `z` of the variety
and evaluation at the generic point of an arc through `z`, and the second
does not kill `δ` because `δ` composed with the arc is a power series with
constant term `δ(z) ≠ 0`.
-/

namespace Height.Orbital

open Matrix Height.Toolbox

universe u

variable {R : Type u} [CommRing R]

/-- `δ` certifies that the rank of `M` is `r` after any field-valued
homomorphism that kills `P` and not `δ`. -/
def GenericRank (P : Ideal R) {a b : ℕ} (M : Matrix (Fin a) (Fin b) R) (r : ℕ) (δ : R) : Prop :=
  δ ∉ P ∧
    ∀ (S : Type u) [Field S] (φ : R →+* S),
      (∀ f ∈ P, φ f = 0) → φ δ ≠ 0 → (M.map φ).rank = r

section Witness

variable {a b : ℕ}

/-- A minor of size exceeding the number of rows has a repeated row, hence
vanishes. -/
theorem det_submatrix_eq_zero_of_card_lt {k : ℕ} (M : Matrix (Fin a) (Fin b) R)
    (f : Fin k → Fin a) (g : Fin k → Fin b) (hk : a < k) :
    (M.submatrix f g).det = 0 := by
  have hnotinj : ¬ Function.Injective f := by
    intro hf
    have := Fintype.card_le_of_injective f hf
    simp only [Fintype.card_fin] at this
    omega
  rw [Function.not_injective_iff] at hnotinj
  obtain ⟨i, j, hij, hne⟩ := hnotinj
  exact Matrix.det_zero_of_row_eq hne (by funext c; simp [hij])

/-- The upper bound on the rank supplied by the vanishing of all
`(r+1)`-minors, and the lower bound supplied by one nonvanishing
`r`-minor. -/
theorem rank_map_eq_of_minor_witness {S : Type*} [Field S] {r : ℕ}
    (M : Matrix (Fin a) (Fin b) R) (P : Ideal R) (φ : R →+* S)
    (hφ : ∀ f ∈ P, φ f = 0)
    (f₀ : Fin r → Fin a) (g₀ : Fin r → Fin b) (hne : φ ((M.submatrix f₀ g₀).det) ≠ 0)
    (hvan : ∀ (f : Fin (r + 1) → Fin a) (g : Fin (r + 1) → Fin b),
      (M.submatrix f g).det ∈ P) :
    (M.map φ).rank = r := by
  have hdet : ∀ {k : ℕ} (f : Fin k → Fin a) (g : Fin k → Fin b),
      ((M.map φ).submatrix f g).det = φ ((M.submatrix f g).det) := by
    intro k f g
    rw [Matrix.submatrix_map, RingHom.map_det]
    rfl
  refine rank_eq_of_minors (M.map φ) (fun f g => ?_) f₀ g₀ ?_
  · rw [hdet f g, hφ _ (hvan f g)]
  · rw [hdet f₀ g₀]
    exact hne

/-- Existence of the generic rank and its witnessing minor. -/
theorem exists_genericRank (P : Ideal R) [hP : P.IsPrime] (M : Matrix (Fin a) (Fin b) R) :
    ∃ (r : ℕ) (δ : R), GenericRank P M r δ := by
  classical
  set Q : ℕ → Prop := fun k =>
    ∃ (f : Fin k → Fin a) (g : Fin k → Fin b), (M.submatrix f g).det ∉ P with hQ
  have hone : (1 : R) ∉ P := fun h => hP.ne_top (Ideal.eq_top_of_isUnit_mem P h isUnit_one)
  have hQ0 : Q 0 := by
    refine ⟨fun i => i.elim0, fun i => i.elim0, ?_⟩
    rw [Matrix.det_fin_zero]
    exact hone
  have hbound : ∀ k : ℕ, a < k → ¬ Q k := by
    intro k hk hQk
    obtain ⟨f, g, hfg⟩ := hQk
    exact hfg (det_submatrix_eq_zero_of_card_lt M f g hk ▸ P.zero_mem)
  set r : ℕ := Nat.findGreatest Q a with hr
  have hQr : Q r := Nat.findGreatest_spec (Nat.zero_le a) hQ0
  have hnotQ : ¬ Q (r + 1) := by
    rcases le_or_gt (r + 1) a with hle | hgt
    · exact Nat.findGreatest_is_greatest (by omega) hle
    · exact hbound (r + 1) (by omega)
  obtain ⟨f₀, g₀, hf₀⟩ := hQr
  refine ⟨r, (M.submatrix f₀ g₀).det, hf₀, ?_⟩
  intro S _ φ hφ hδ
  refine rank_map_eq_of_minor_witness M P φ hφ f₀ g₀ hδ (fun f g => ?_)
  by_contra hcon
  exact hnotQ ⟨f, g, hcon⟩

end Witness

end Height.Orbital
