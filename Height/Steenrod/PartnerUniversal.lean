import Height.Steenrod.PartnerEquations

/-!
# Universal polynomial equations for partner varieties (`defn:partner`)

For a fixed endpoint `N`, the coefficients of the characteristic
polynomials of `M + T N` are themselves multivariate polynomials in the
entries of `M`.  This file constructs those universal equations and proves
that evaluation recovers the concrete triangular coefficient list.

These are the coefficients in `(μ, ν)` of `c_j(μ N + ν M')` by which
`defn:partner` cuts out `𝒞_N`.
-/

namespace Height.Steenrod

open Polynomial

universe u

variable (p r n : ℕ) [Fact p.Prime]
variable {K : Type u} [Field K] [Algebra (GaloisField p r) K]

/-- The `j`th signed characteristic coefficient of `X + T N`, with `X`
the generic matrix over `K`. -/
noncomputable def partnerUniversalCharacteristicCoefficient
    (N : Matrix (Fin n) (Fin n) K) (j : ℕ) :
    Polynomial (MvPolynomial (Fin n × Fin n) K) :=
  MvPolynomial.aeval
    (fun ij : Fin n × Fin n =>
      Polynomial.C (MvPolynomial.X ij) +
        Polynomial.monomial 1 (MvPolynomial.C (N ij.1 ij.2)))
    (QSteenrod.c p r n j)

/-- Evaluating the generic matrix entries maps the universal partner
polynomial to the concrete one. -/
theorem map_partnerUniversalCharacteristicCoefficient
    (N M : Matrix (Fin n) (Fin n) K) (j : ℕ) :
    (partnerUniversalCharacteristicCoefficient p r n N j).map
        (MvPolynomial.eval₂Hom (RingHom.id K)
          fun ij : Fin n × Fin n => M ij.1 ij.2) =
      partnerCharacteristicCoefficient p r n N M j := by
  let ev : MvPolynomial (Fin n × Fin n) K →ₐ[K] K :=
    MvPolynomial.aeval fun ij => M ij.1 ij.2
  let evq : MvPolynomial (Fin n × Fin n) K →ₐ[GaloisField p r] K :=
    ev.restrictScalars (GaloisField p r)
  let lhs : QSteenrod.GenericMatrixRing p r n →ₐ[GaloisField p r]
      Polynomial K :=
    (Polynomial.mapAlgHom evq).comp
      (MvPolynomial.aeval fun ij : Fin n × Fin n =>
        Polynomial.C (MvPolynomial.X ij) +
          Polynomial.monomial 1 (MvPolynomial.C (N ij.1 ij.2)))
  let rhs : QSteenrod.GenericMatrixRing p r n →ₐ[GaloisField p r]
      Polynomial K :=
    MvPolynomial.aeval fun ij : Fin n × Fin n =>
      Polynomial.C (M ij.1 ij.2) +
        Polynomial.monomial 1 (N ij.1 ij.2)
  have hhom : lhs = rhs := MvPolynomial.algHom_ext fun ij => by
    simp [lhs, rhs, evq, ev]
  change lhs (QSteenrod.c p r n j) = rhs (QSteenrod.c p r n j)
  exact DFunLike.congr_fun hhom (QSteenrod.c p r n j)

/-- Evaluation of an individual universal coefficient gives the matching
concrete partner coefficient. -/
theorem eval_partnerUniversalCharacteristicCoefficient_coeff
    (N M : Matrix (Fin n) (Fin n) K) (i j : ℕ) :
    MvPolynomial.aeval (fun ij : Fin n × Fin n => M ij.1 ij.2)
        ((partnerUniversalCharacteristicCoefficient p r n N j).coeff i) =
      (partnerCharacteristicCoefficient p r n N M j).coeff i := by
  have h := congrArg (fun f : Polynomial K => f.coeff i)
    (map_partnerUniversalCharacteristicCoefficient p r n N M j)
  simpa [MvPolynomial.aeval_def] using h

/-- The universal ordered triangular equation list for the partner variety
of `N`. -/
noncomputable def partnerUniversalEquationList
    (N : Matrix (Fin n) (Fin n) K) :
    List (MvPolynomial (Fin n × Fin n) K) :=
  (QSteenrod.strictLowerTriangleIndices n).map fun ij =>
    (partnerUniversalCharacteristicCoefficient p r n N ij.2).coeff ij.1

/-- Entrywise evaluation sends the universal equation list to the concrete
coefficient list. -/
theorem map_partnerUniversalEquationList
    (N M : Matrix (Fin n) (Fin n) K) :
    (partnerUniversalEquationList p r n N).map
        (MvPolynomial.aeval fun ij : Fin n × Fin n => M ij.1 ij.2) =
      partnerCoefficientList p r n N M := by
  simp only [partnerUniversalEquationList, partnerCoefficientList,
    List.map_map]
  apply List.map_congr_left
  intro ij hij
  exact eval_partnerUniversalCharacteristicCoefficient_coeff
    p r n N M ij.1 ij.2

/-- Vanishing at `M` of every polynomial in the universal triangular
equation list attached to `N`. -/
def PartnerUniversalEquationsVanishAt
    (N M : Matrix (Fin n) (Fin n) K) : Prop :=
  ∀ f ∈ partnerUniversalEquationList p r n N,
    MvPolynomial.aeval (fun ij : Fin n × Fin n => M ij.1 ij.2) f = 0

/-- Universal equation vanishing is precisely concrete triangular
coefficient vanishing. -/
theorem partnerUniversalEquationsVanishAt_iff_triangle
    (N M : Matrix (Fin n) (Fin n) K) :
    PartnerUniversalEquationsVanishAt p r n N M ↔
      PartnerTriangleVanish p r n N M := by
  rw [partnerTriangleVanish_iff_list]
  let ev : MvPolynomial (Fin n × Fin n) K → K :=
    MvPolynomial.aeval fun ij : Fin n × Fin n => M ij.1 ij.2
  have hmap :
      (partnerUniversalEquationList p r n N).map ev =
        partnerCoefficientList p r n N M := by
    exact map_partnerUniversalEquationList p r n N M
  constructor
  · intro h a ha
    rw [← hmap] at ha
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp ha
    exact h f hf
  · intro h f hf
    apply h (ev f)
    rw [← hmap]
    exact List.mem_map.mpr ⟨f, hf, rfl⟩

/-- Over an infinite field and for a nilpotent endpoint, the universal
triangular equations cut out exactly the nilpotent partners. -/
theorem partnerUniversalEquationsVanishAt_iff_partner [Infinite K]
    (N M : Matrix (Fin n) (Fin n) K) (hN : IsNilpotent N) :
    PartnerUniversalEquationsVanishAt p r n N M ↔
      NilpotentPencil N M := by
  rw [partnerUniversalEquationsVanishAt_iff_triangle,
    partnerTriangleVanish_iff_partner p r n N M hN]

end Height.Steenrod
