import Mathlib.Order.KrullDimension
import Mathlib.Data.ENat.Basic

/-!
# Arithmetic in `WithBot ℕ∞`

Krull dimensions live in `WithBot ℕ∞`; the cancellation and comparison facts the
dimension counts need and mathlib states only for `WithTop` are collected here.
-/

namespace Height.Toolbox

/-- Adding a natural number is injective on `WithBot ℕ∞`. -/
theorem add_natCast_right_cancel {a b : WithBot ℕ∞} {c : ℕ}
    (h : a + (c : WithBot ℕ∞) = b + (c : WithBot ℕ∞)) : a = b := by
  have hc : ((c : ℕ) : WithBot ℕ∞) = ((c : ℕ∞) : WithBot ℕ∞) := rfl
  rw [hc] at h
  induction a using WithBot.recBotCoe with
  | bot =>
      induction b using WithBot.recBotCoe with
      | bot => rfl
      | coe b =>
          rw [WithBot.bot_add] at h
          rw [← WithBot.coe_add] at h
          exact absurd h.symm (by simp)
  | coe a =>
      induction b using WithBot.recBotCoe with
      | bot =>
          rw [WithBot.bot_add] at h
          rw [← WithBot.coe_add] at h
          exact absurd h (by simp)
      | coe b =>
          rw [← WithBot.coe_add, ← WithBot.coe_add] at h
          exact congrArg _
            (WithTop.add_right_cancel (ENat.natCast_ne_top c) (WithBot.coe_injective h))

/-- **A sum of two elements of `WithBot ℕ∞` equal to a natural number has both
summands natural.**  `⊥ + x = ⊥` and `⊤ + x = ⊤` unless `x = ⊥`, and neither is
a `↑c`; this is how a dimension formula `height + dim = n²` yields the two
finite numbers the count works with. -/
theorem exists_eq_natCast_of_add_eq_natCast {a b : WithBot ℕ∞} {c : ℕ}
    (h : a + b = (c : WithBot ℕ∞)) :
    ∃ x y : ℕ, a = (x : WithBot ℕ∞) ∧ b = (y : WithBot ℕ∞) ∧ x + y = c := by
  have hc : ((c : ℕ) : WithBot ℕ∞) = ((c : ℕ∞) : WithBot ℕ∞) := rfl
  rw [hc] at h
  induction a using WithBot.recBotCoe with
  | bot => rw [WithBot.bot_add] at h; exact absurd h (by simp)
  | coe a =>
      induction b using WithBot.recBotCoe with
      | bot => rw [WithBot.add_bot] at h; exact absurd h (by simp)
      | coe b =>
          rw [← WithBot.coe_add, WithBot.coe_inj] at h
          have hane : a ≠ ⊤ := by
            intro htop
            rw [htop, top_add] at h
            exact ENat.natCast_ne_top c h.symm
          have hbne : b ≠ ⊤ := by
            intro htop
            rw [htop, add_top] at h
            exact ENat.natCast_ne_top c h.symm
          obtain ⟨x, rfl⟩ := ENat.ne_top_iff_exists.mp hane
          obtain ⟨y, rfl⟩ := ENat.ne_top_iff_exists.mp hbne
          exact ⟨x, y, rfl, rfl, by exact_mod_cast h⟩

end Height.Toolbox
