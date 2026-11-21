import Mathlib.Algebra.Group.Hom.End
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Group

/-!
# The group-theoretic part of Lang's map (`thm:lang`)

The point-counting part of `lem:semilinear` supplies a fixed basis.  Everything
after that is the elementary group calculation isolated here.
-/

namespace Height.Toolbox

universe u

variable {G : Type u} [Group G]

/-- Lang's map for a group endomorphism `F`. -/
def langMap (F : G →* G) (g : G) : G := g⁻¹ * F g

/-- Two points have the same Lang value precisely when their quotient is
fixed by `F`. -/
theorem langMap_eq_iff (F : G →* G) (g' g : G) :
    langMap F g' = langMap F g ↔ F (g' * g⁻¹) = g' * g⁻¹ := by
  constructor
  · intro h
    change g'⁻¹ * F g' = g⁻¹ * F g at h
    have hFg : F g' = g' * g⁻¹ * F g := by
      calc
        F g' = g' * (g'⁻¹ * F g') := by group
        _ = g' * (g⁻¹ * F g) := by rw [h]
        _ = g' * g⁻¹ * F g := by group
    rw [map_mul, map_inv, hFg]
    group
  · intro h
    have hprod : F g' * (F g)⁻¹ = g' * g⁻¹ := by
      simpa only [map_mul, map_inv] using h
    calc
      langMap F g' = g'⁻¹ * F g' := rfl
      _ = g'⁻¹ * (F g' * (F g)⁻¹) * F g := by group
      _ = g'⁻¹ * (g' * g⁻¹) * F g := by rw [hprod]
      _ = g⁻¹ * F g := by group
      _ = langMap F g := rfl

/-- Fiber-coset form of the preceding calculation. -/
theorem lang_fiber (F : G →* G) (g' g : G) :
    langMap F g' = langMap F g ↔
      ∃ γ : G, F γ = γ ∧ g' = γ * g := by
  constructor
  · intro h
    refine ⟨g' * g⁻¹, (langMap_eq_iff F g' g).mp h, ?_⟩
    group
  · rintro ⟨γ, hγ, rfl⟩
    rw [langMap_eq_iff]
    simp [hγ]

end Height.Toolbox
