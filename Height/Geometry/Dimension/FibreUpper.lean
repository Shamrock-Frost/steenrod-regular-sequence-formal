import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The fibre-dimension upper bound, in ring form

For a morphism `φ : A →ₐ[K] B` of finitely generated algebras over a field `K`,

```
ringKrullDim B ≤ ringKrullDim (A ⧸ ker φ) + ⨆ m maximal, ringKrullDim (B ⧸ m.map φ),
```

the ring-theoretic form of `dim Y ≤ dim (closure of the image) + sup of the fibre
dimensions`.

The proof: fix a maximal
ideal `q` of `B`; by `ringKrullDim_le_iff_isMaximal_height_le` it is enough to bound
`q.height`.

* `p := q.comap φ` is **maximal**: `B ⧸ q` is a field, `A → B ⧸ q` is of finite type
  and `A` is a Jacobson ring (finite type over a field), so `B ⧸ q` is a finite
  `A`-module (`finite_of_finite_type_of_isJacobsonRing`), hence integral, and the
  contraction of the maximal ideal `⊥` of `B ⧸ q` is maximal
  (`Ideal.isMaximal_comap_of_isIntegral_of_isMaximal`).  That contraction is `p`.
* Stacks 00OM (`Ideal.height_le_height_add_of_liesOver`), applied to the *injective*
  factor `A ⧸ ker φ → B` of `φ`, bounds `q.height` by the height of the contraction
  `p'` of `q` to `A ⧸ ker φ` plus the height of the image of `q` in `B ⧸ p' B`.
  Passing to `A ⧸ ker φ` rather than to `A` is essential: over `A` the first summand
  would be `p.height`, which is in general strictly larger than
  `ringKrullDim (A ⧸ ker φ)` (take `A = K[x] → K = B`, where `p.height = 1` while
  `ringKrullDim (A ⧸ ker φ) = 0`).
* Both heights are then bounded by Krull dimensions
  (`Ideal.height_le_ringKrullDim_of_isPrime`), and `p' B = p.map φ` because
  `A → A ⧸ ker φ` is surjective.

`IsAlgClosed K` is **not** assumed.  It plays no role — all
that is used about `K` is that it is a Noetherian Jacobson ring, which every field is.
-/

universe u v w

namespace Height.Geometry

/-- **The fibre-dimension upper bound**: for a morphism `φ : A →ₐ[K] B` of finitely
generated algebras over a field `K`, the Krull dimension of `B` is at most the
Krull dimension of the
image `A ⧸ ker φ` plus the supremum of the Krull dimensions of the scheme-theoretic
fibres `B ⧸ m.map φ` over the maximal ideals `m` of `A`.

`K` is an arbitrary field; algebraic closedness is not needed. -/
theorem ringKrullDim_le_of_finiteType (K : Type u) (A : Type v) (B : Type w) [Field K]
    [CommRing A] [CommRing B] [Algebra K A] [Algebra K B] [Algebra.FiniteType K A]
    [Algebra.FiniteType K B] (φ : A →ₐ[K] B) :
    ringKrullDim B ≤ ringKrullDim (A ⧸ RingHom.ker φ) +
      ⨆ m : {m : Ideal A // m.IsMaximal}, ringKrullDim (B ⧸ (m.1.map φ)) := by
  -- Work throughout with the underlying ring homomorphism, so that `RingHom.ker` and
  -- `Ideal.map` have a single normal form.  This `show` is a definitional change.
  show ringKrullDim B ≤ ringKrullDim (A ⧸ RingHom.ker (φ : A →+* B)) +
      ⨆ m : {m : Ideal A // m.IsMaximal}, ringKrullDim (B ⧸ (m.1.map (φ : A →+* B)))
  have hNB : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing K B
  have hNA : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
  have hNA' : IsNoetherianRing (A ⧸ RingHom.ker (φ : A →+* B)) := inferInstance
  have hJA : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := K) (B := A)
  -- `A ⧸ ker φ` acts on `B` through the injection induced by `φ`.
  let _instA' : Algebra (A ⧸ RingHom.ker (φ : A →+* B)) B :=
    (RingHom.kerLift (φ : A →+* B)).toAlgebra
  have halg : (algebraMap (A ⧸ RingHom.ker (φ : A →+* B)) B)
      = RingHom.kerLift (φ : A →+* B) := rfl
  rw [ringKrullDim_le_iff_isMaximal_height_le]
  intro q hq
  have _ : q.IsMaximal := hq
  -- Step 1: the contraction `p := q.comap φ` is a maximal ideal of `A`.
  let p : Ideal A := q.comap (φ : A →+* B)
  have hpmax : p.IsMaximal := by
    let _instF : Field (B ⧸ q) := Ideal.Quotient.field q
    let _instQ : Algebra A (B ⧸ q) := ((Ideal.Quotient.mkₐ K q).comp φ).toRingHom.toAlgebra
    have _ : IsScalarTower K A (B ⧸ q) :=
      IsScalarTower.of_algebraMap_eq fun x =>
        (((Ideal.Quotient.mkₐ K q).comp φ).commutes x).symm
    have _ : Algebra.FiniteType K (B ⧸ q) :=
      Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ K q)
        (Ideal.Quotient.mkₐ_surjective K q)
    have _ : Algebra.FiniteType A (B ⧸ q) :=
      Algebra.FiniteType.of_restrictScalars_finiteType K A (B ⧸ q)
    have _ : Module.Finite A (B ⧸ q) := finite_of_finite_type_of_isJacobsonRing A (B ⧸ q)
    have hmax := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := A) (S := B ⧸ q)
      (⊥ : Ideal (B ⧸ q))
    have hker : (⊥ : Ideal (B ⧸ q)).comap (algebraMap A (B ⧸ q)) = p := by
      ext x
      show Ideal.Quotient.mk q (φ x) ∈ (⊥ : Ideal (B ⧸ q)) ↔ φ x ∈ q
      rw [Submodule.mem_bot, Ideal.Quotient.eq_zero_iff_mem]
    exact hker ▸ hmax
  -- Step 2: Stacks 00OM for the injective factor `A ⧸ ker φ → B`.
  have h00OM := Ideal.height_le_height_add_of_liesOver
    (R := A ⧸ RingHom.ker (φ : A →+* B)) (S := B)
    (q.under (A ⧸ RingHom.ker (φ : A →+* B))) q
  -- Step 3: the fibre ideal computed over `A ⧸ ker φ` is `p.map φ`.
  have hfib : (q.under (A ⧸ RingHom.ker (φ : A →+* B))).map
        (algebraMap (A ⧸ RingHom.ker (φ : A →+* B)) B) = p.map (φ : A →+* B) := by
    have hsurj : Function.Surjective
        ⇑(Ideal.Quotient.mk (RingHom.ker (φ : A →+* B))) := Ideal.Quotient.mk_surjective
    have hcomap : p = (q.under (A ⧸ RingHom.ker (φ : A →+* B))).comap
        (Ideal.Quotient.mk (RingHom.ker (φ : A →+* B))) := by
      ext x; exact Iff.rfl
    have hcomp : ((RingHom.kerLift (φ : A →+* B)).comp
        (Ideal.Quotient.mk (RingHom.ker (φ : A →+* B)))) = (φ : A →+* B) := by
      ext x; rfl
    have h1 : ((q.under (A ⧸ RingHom.ker (φ : A →+* B))).comap
          (Ideal.Quotient.mk (RingHom.ker (φ : A →+* B)))).map
          ((RingHom.kerLift (φ : A →+* B)).comp
            (Ideal.Quotient.mk (RingHom.ker (φ : A →+* B))))
        = p.map (φ : A →+* B) := by rw [hcomp, ← hcomap]
    rw [← h1, ← Ideal.map_map,
      Ideal.map_comap_of_surjective _ hsurj (q.under (A ⧸ RingHom.ker (φ : A →+* B))), halg]
  -- Step 4: bound the two heights by Krull dimensions.
  have hle1 : ((q.under (A ⧸ RingHom.ker (φ : A →+* B))).height : WithBot ℕ∞)
      ≤ ringKrullDim (A ⧸ RingHom.ker (φ : A →+* B)) :=
    Ideal.height_le_ringKrullDim_of_isPrime
  have hsub : p.map (φ : A →+* B) ≤ q := Ideal.map_le_iff_le_comap.mpr le_rfl
  have hle2 : ((q.map (Ideal.Quotient.mk (p.map (φ : A →+* B)))).height : WithBot ℕ∞)
      ≤ ringKrullDim (B ⧸ p.map (φ : A →+* B)) := by
    have hmm : (q.map (Ideal.Quotient.mk (p.map (φ : A →+* B)))).IsMaximal := by
      refine Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective ?_
      rw [Ideal.mk_ker]
      exact hsub
    have _ : (q.map (Ideal.Quotient.mk (p.map (φ : A →+* B)))).IsPrime := hmm.isPrime
    exact Ideal.height_le_ringKrullDim_of_isPrime
  -- Step 5: assemble.
  calc (q.height : WithBot ℕ∞)
      ≤ ((q.under (A ⧸ RingHom.ker (φ : A →+* B))).height : WithBot ℕ∞)
        + ((q.map (Ideal.Quotient.mk (p.map (φ : A →+* B)))).height : WithBot ℕ∞) := by
        rw [← WithBot.coe_add, WithBot.coe_le_coe]
        rw [hfib] at h00OM
        exact h00OM
    _ ≤ ringKrullDim (A ⧸ RingHom.ker (φ : A →+* B))
        + ringKrullDim (B ⧸ p.map (φ : A →+* B)) := add_le_add hle1 hle2
    _ ≤ ringKrullDim (A ⧸ RingHom.ker (φ : A →+* B)) +
          ⨆ m : {m : Ideal A // m.IsMaximal},
            ringKrullDim (B ⧸ (m.1.map (φ : A →+* B))) :=
        add_le_add le_rfl
          (le_iSup (fun m : {m : Ideal A // m.IsMaximal} =>
            ringKrullDim (B ⧸ (m.1.map (φ : A →+* B)))) ⟨p, hpmax⟩)

end Height.Geometry
