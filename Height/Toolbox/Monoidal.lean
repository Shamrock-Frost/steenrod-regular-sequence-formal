import Mathlib.CategoryTheory.Monoidal.Mod
import Mathlib.CategoryTheory.Monoidal.Mon

/-!
# Module objects along a lax monoidal functor

A lax monoidal functor `F : C ⥤ D` takes monoid objects to monoid objects
(mathlib's `Functor.monObjObj` and `Functor.mapMon`).  It also takes module objects to
module objects, but mathlib does not say so — that is the TODO
"`mapMod F A : Mod A ⥤ Mod (F.mapMon A)`" at `CategoryTheory/Monoidal/Mon.lean`.
`modObjObj` is the object-level statement, and a mathlib candidate.

The monoid structure on `F.obj M` is taken as a hypothesis rather than fixed to
`Functor.monObjObj`, with `hone`/`hmul` saying that it *is* that structure.  This is what
lets the lemma be applied to a monoid object built elsewhere: for `F = algSpec R` the
monoid object on `Spec A` is mathlib's `instMonObjSpecAsOverSpec`, and the two hypotheses
are `rfl` (`Height/Geometry/Group.lean`).

Nothing in this file knows about schemes.
-/

open CategoryTheory MonoidalCategory

namespace Height.Toolbox

variable {C : Type*} [Category C] [MonoidalCategory C]
  {D : Type*} [Category D] [MonoidalCategory D]

open Functor.LaxMonoidal MonObj in
/-- **The image of a module object under a lax monoidal functor.**  The action is
`μ F M X ≫ F.map smul`; unitality and associativity are the lax monoidal coherences
`left_unitality` and `associativity` together with the naturality of the tensorator. -/
@[instance_reducible]
noncomputable def modObjObj (F : C ⥤ D) [F.LaxMonoidal] {M : C} [MonObj M] (X : C) [ModObj M X]
    [MonObj (F.obj M)]
    (hone : (η : 𝟙_ D ⟶ F.obj M) = ε F ≫ F.map η)
    (hmul : (μ : F.obj M ⊗ F.obj M ⟶ F.obj M) = Functor.LaxMonoidal.μ F M M ≫ F.map μ) :
    ModObj (F.obj M) (F.obj X) where
  smul := Functor.LaxMonoidal.μ F M X ≫ F.map (ModObj.smul (M := M) (X := X))
  one_smul := by
    show (η : 𝟙_ D ⟶ F.obj M) ▷ F.obj X ≫
      Functor.LaxMonoidal.μ F M X ≫ F.map (ModObj.smul (M := M) (X := X)) = (λ_ (F.obj X)).hom
    rw [hone, comp_whiskerRight, Category.assoc, μ_natural_left_assoc, ← F.map_comp,
      ModObj.one_smul_self, ← left_unitality]
  mul_smul := by
    show (μ : F.obj M ⊗ F.obj M ⟶ F.obj M) ▷ F.obj X ≫
        Functor.LaxMonoidal.μ F M X ≫ F.map (ModObj.smul (M := M) (X := X)) =
      (α_ (F.obj M) (F.obj M) (F.obj X)).hom ≫
        F.obj M ◁ (Functor.LaxMonoidal.μ F M X ≫ F.map (ModObj.smul (M := M) (X := X))) ≫
          Functor.LaxMonoidal.μ F M X ≫ F.map (ModObj.smul (M := M) (X := X))
    rw [hmul, comp_whiskerRight, Category.assoc, μ_natural_left_assoc, ← F.map_comp,
      ModObj.mul_smul_self, F.map_comp, F.map_comp, associativity_assoc,
      MonoidalCategory.whiskerLeft_comp, Category.assoc, μ_natural_right_assoc]

end Height.Toolbox
