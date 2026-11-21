import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.Algebraic.Integral

/-!
# Krull dimension of an affine domain is its transcendence degree

For a finitely generated algebra `A` over a field `K` which is a domain, the
Krull dimension of `A` and the transcendence degree of `A` over `K` are the
same natural number.

The proof is Noether normalisation in the form supplied by the pinned mathlib
(`exists_integral_inj_algHom_of_fg`, Stacks 00OW), which already carries the
identification of the number of variables with `ringKrullDim A`: there is an
injective integral `K`-algebra map `g : K[X₀,…,X_{s-1}] → A` with
`s = ringKrullDim A`.  Viewing `A` as an algebra over `P := K[X₀,…,X_{s-1}]`
through `g`, the tower formula `trdeg_add_eq` (Stacks 030H) gives

```
trdeg K A = trdeg K P + trdeg P A = s + 0 = s,
```

because `A` is integral, hence algebraic, over `P` (`trdeg_eq_zero`), and
`trdeg K P = s` (`MvPolynomial.trdeg_of_isDomain`).

Note on the shape of the statement: `Algebra.trdeg` takes values in `Cardinal`
and `ringKrullDim` in `WithBot ℕ∞`, so the two equalities are stated against
the coercions of one and the same natural number `d`; this is the form the
dimension counts use.  `IsAlgClosed K` is not needed.
-/

universe u v

namespace Height.Geometry

open Cardinal

/-- For a finitely generated domain `A` over a field `K`, the Krull
dimension of `A` and the transcendence degree of `A` over `K` are equal, and
finite.  No hypothesis on `K` beyond being a field. -/
theorem ringKrullDim_eq_trdeg (K : Type u) (A : Type v) [Field K] [CommRing A] [IsDomain A]
    [Algebra K A] [Algebra.FiniteType K A] :
    ∃ d : ℕ, ringKrullDim A = d ∧ Algebra.trdeg K A = d := by
  obtain ⟨s, hs, g, hginj, hgint⟩ := exists_integral_inj_algHom_of_fg K A
  refine ⟨s, hs.symm, ?_⟩
  -- View `A` as an algebra over the polynomial ring `MvPolynomial (Fin s) K` through `g`.
  let _inst : Algebra (MvPolynomial (Fin s) K) A := g.toRingHom.toAlgebra
  have : IsScalarTower K (MvPolynomial (Fin s) K) A := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    show algebraMap K A x = g (algebraMap K (MvPolynomial (Fin s) K) x)
    rw [AlgHom.commutes]
  have : FaithfulSMul K (MvPolynomial (Fin s) K) :=
    (faithfulSMul_iff_algebraMap_injective K (MvPolynomial (Fin s) K)).mpr
      (MvPolynomial.C_injective (Fin s) K)
  have : FaithfulSMul (MvPolynomial (Fin s) K) A :=
    (faithfulSMul_iff_algebraMap_injective (MvPolynomial (Fin s) K) A).mpr hginj
  have : Algebra.IsIntegral (MvPolynomial (Fin s) K) A := Algebra.isIntegral_def.mpr hgint
  have : Algebra.IsAlgebraic (MvPolynomial (Fin s) K) A := inferInstance
  -- The tower formula, in the universe-polymorphic `lift` form: `K` lives in `Type u`,
  -- `A` in `Type v`.
  have htower : lift.{v} (Algebra.trdeg K (MvPolynomial (Fin s) K))
      + lift.{u} (Algebra.trdeg (MvPolynomial (Fin s) K) A)
      = lift.{u} (Algebra.trdeg K A) := lift_trdeg_add_eq K (MvPolynomial (Fin s) K) A
  have hPtr : Algebra.trdeg K (MvPolynomial (Fin s) K) = (s : Cardinal.{u}) := by
    rw [MvPolynomial.trdeg_of_isDomain]; simp
  rw [hPtr, trdeg_eq_zero (R := MvPolynomial (Fin s) K) (A := A)] at htower
  simp only [Cardinal.lift_zero, add_zero, Cardinal.lift_natCast] at htower
  refine Cardinal.lift_inj.{v, u}.mp ?_
  rw [Cardinal.lift_natCast]
  exact htower.symm

end Height.Geometry
