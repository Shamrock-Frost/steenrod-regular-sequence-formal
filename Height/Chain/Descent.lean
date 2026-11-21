import Height.Chain.Statements
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.RingTheory.KrullDimension.Integral

/-!
# Descent of the dimension from `Kbar` to `F_q`

`Chain/Counts.lean` measures loci of matrices over `Kbar` (`affineDim` in the
chart `matCoords`), but `rem:krull` is about the coordinate ring over `F_q`.  The bridge is
elementary: for an *algebraic* field extension `k ⊆ L` the coefficientwise map
`k[x_σ] → L[x_σ]` is integral (`MvPolynomial.isIntegral_iff_isIntegral_coeff`),
and for a set `S` of `L`-points the contraction of `I_L(S)` along it is `I_k(S)`;
so `RingHom.IsIntegral.ringKrullDim_quotient_ker_eq` gives

```
ringKrullDim (k[x] ⧸ I_k(S)) = ringKrullDim (L[x] ⧸ I_L(S)).
```

Also here: every point of `V(J)` is nilpotent, which needs no hypothesis on `r`
because the Steenrod ideal contains `P^0(c_j) = c_j` for all `1 ≤ j ≤ n`.
-/

namespace Height.Chain

open QSteenrod Height.Steenrod

attribute [local instance] MvPolynomial.algebraMvPolynomial

section Descent

variable {k L : Type*} [Field k] [Field L] [Algebra k L] {σ : Type*}

/-- Evaluating at an `L`-point does not see the extension of scalars. -/
theorem aeval_map_algebraMap (x : σ → L) (f : MvPolynomial σ k) :
    MvPolynomial.aeval x (MvPolynomial.map (algebraMap k L) f) = MvPolynomial.aeval x f := by
  simp [MvPolynomial.aeval_def, MvPolynomial.eval₂_map]

variable [Algebra.IsAlgebraic k L]

/-- Coefficientwise extension of scalars along an algebraic field extension is an
integral ring map: a polynomial over `L` is integral over `k[x]` as soon as each
of its coefficients is integral over `k`. -/
theorem isIntegral_mvPolynomial_map :
    (MvPolynomial.map (algebraMap k L) : MvPolynomial σ k →+* MvPolynomial σ L).IsIntegral :=
  fun _ =>
    MvPolynomial.isIntegral_iff_isIntegral_coeff.mpr fun _ => Algebra.IsIntegral.isIntegral _

/-- **Descent of the dimension.**  For a set `S` of `L`-points, the coordinate
ring of `S` over `k` and over `L` have the same Krull dimension, `L/k` algebraic. -/
theorem ringKrullDim_quotient_vanishingIdeal_eq (S : Set (σ → L)) :
    ringKrullDim (MvPolynomial σ k ⧸ MvPolynomial.vanishingIdeal k S) =
      ringKrullDim (MvPolynomial σ L ⧸ MvPolynomial.vanishingIdeal L S) := by
  set φ : MvPolynomial σ k →+* MvPolynomial σ L := MvPolynomial.map (algebraMap k L) with hφ
  set ψ : MvPolynomial σ k →+* (MvPolynomial σ L ⧸ MvPolynomial.vanishingIdeal L S) :=
    (Ideal.Quotient.mk (MvPolynomial.vanishingIdeal L S)).comp φ with hψ
  have hint : ψ.IsIntegral :=
    RingHom.IsIntegral.trans _ _ (isIntegral_mvPolynomial_map (k := k) (L := L) (σ := σ))
      (RingHom.isIntegral_of_surjective _ Ideal.Quotient.mk_surjective)
  have hker : RingHom.ker ψ = MvPolynomial.vanishingIdeal k S := by
    ext f
    simp only [hψ, RingHom.mem_ker, RingHom.coe_comp, Function.comp_apply,
      Ideal.Quotient.eq_zero_iff_mem, MvPolynomial.mem_vanishingIdeal_iff, hφ]
    constructor
    · intro h x hx
      have hx' := h x hx
      rwa [aeval_map_algebraMap] at hx'
    · intro h x hx
      rw [aeval_map_algebraMap]
      exact h x hx
  rw [← hker]
  exact hint.ringKrullDim_quotient_ker_eq

end Descent

variable (p r n : ℕ) [Fact p.Prime]

/-- Every point of `V(J)` is nilpotent: the ideal contains `P^0(c_j) = c_j` for
all `1 ≤ j ≤ n`, so the characteristic polynomial of a point is `X^n`.  No
hypothesis on `r`. -/
theorem isNilpotent_of_mem_steenrodMatrixZeroLocus {K : Type*} [Field K]
    [Algebra (GaloisField p r) K] {M : Matrix (Fin n) (Fin n) K}
    (hM : M ∈ steenrodMatrixZeroLocus p r n) : IsNilpotent M := by
  rw [← characteristicCoefficientsVanish_iff p r n]
  intro j hj1 hjn
  refine hM (QSteenrod.c p r n j) ?_
  have hmem := P_c_mem_steenrodIdeal p r n 0 j hj1 hjn (by omega)
  rwa [P_zero] at hmem

end Height.Chain
