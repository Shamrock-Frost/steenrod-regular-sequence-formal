import Height.Steenrod.Partner
import Height.Steenrod.Ideal

/-!
# Equations cutting out the partner condition (`defn:partner`)

For a fixed nilpotent matrix `N`, this proves the algebraic part of
`defn:partner`: the partners of `N` are exactly the matrices for which every
coefficient of every non-leading characteristic coefficient of `M + T N`
vanishes.
-/

namespace Height.Steenrod

open Polynomial

universe u

variable {K : Type u} [Field K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- If the second endpoint is nilpotent, testing the affine line through the
first endpoint is equivalent to testing its entire linear span. -/
theorem nilpotentPencil_iff_line_of_right (A B : Matrix ι ι K)
    (hB : IsNilpotent B) :
    NilpotentPencil A B ↔ ∀ t : K, IsNilpotent (A + t • B) := by
  constructor
  · intro h t
    simpa using h 1 t
  · intro h s t
    by_cases hs : s = 0
    · simpa [hs] using hB.smul t
    · have hst : s * (t / s) = t := by field_simp
      simpa [smul_add, smul_smul, hst] using (h (t / s)).smul s

variable (p r n : ℕ) [Fact p.Prime]
variable [Algebra (GaloisField p r) K]

/-- The `j`th signed characteristic coefficient of the affine pencil
`M + T N`, as a polynomial in `T`. -/
noncomputable def partnerCharacteristicCoefficient
    (N M : Matrix (Fin n) (Fin n) K) (j : ℕ) : Polynomial K :=
  MvPolynomial.aeval
    (fun ij : Fin n × Fin n =>
      C (M ij.1 ij.2) + monomial 1 (N ij.1 ij.2))
    (QSteenrod.c p r n j)

/-- Evaluating the partner equation at `t` gives the corresponding signed
characteristic coefficient of `M + t N`. -/
theorem eval_partnerCharacteristicCoefficient
    (N M : Matrix (Fin n) (Fin n) K) (j : ℕ) (t : K) :
    (partnerCharacteristicCoefficient p r n N M j).eval t =
      (-1 : K) ^ j * (M + t • N).charpoly.coeff (n - j) := by
  let ev : Polynomial K →ₐ[GaloisField p r] K :=
    { Polynomial.evalRingHom t with
      commutes' := fun x => by simp }
  let lhs : QSteenrod.GenericMatrixRing p r n →ₐ[GaloisField p r] K :=
    ev.comp (MvPolynomial.aeval fun ij : Fin n × Fin n =>
      C (M ij.1 ij.2) + monomial 1 (N ij.1 ij.2))
  let rhs : QSteenrod.GenericMatrixRing p r n →ₐ[GaloisField p r] K :=
    MvPolynomial.aeval fun ij => (M + t • N) ij.1 ij.2
  have heval : lhs = rhs := MvPolynomial.algHom_ext fun ij => by
    simp [lhs, rhs, ev, mul_comm]
  calc
    (partnerCharacteristicCoefficient p r n N M j).eval t =
        lhs (QSteenrod.c p r n j) := by rfl
    _ = rhs (QSteenrod.c p r n j) := by rw [heval]
    _ = (-1 : K) ^ j * (M + t • N).charpoly.coeff (n - j) :=
      eval_characteristicCoefficient p r n (M + t • N) j

/-- The `j`th partner polynomial has degree at most `j`. -/
theorem natDegree_partnerCharacteristicCoefficient_le
    (N M : Matrix (Fin n) (Fin n) K) (j : ℕ) (hj : j ≤ n) :
    (partnerCharacteristicCoefficient p r n N M j).natDegree ≤ j := by
  apply natDegree_aeval_le_of_isHomogeneous
    (characteristicCoefficient_isHomogeneous p r n j hj)
  intro ij
  simpa using Polynomial.natDegree_monomial_le (N ij.1 ij.2) (m := 1)

/-- Its top possible coefficient is the signed `j`th characteristic
coefficient of the fixed endpoint `N`. -/
theorem coeff_top_partnerCharacteristicCoefficient
    (N M : Matrix (Fin n) (Fin n) K) (j : ℕ) (hj : j ≤ n) :
    (partnerCharacteristicCoefficient p r n N M j).coeff j =
      (-1 : K) ^ j * N.charpoly.coeff (n - j) := by
  rw [partnerCharacteristicCoefficient,
    coeff_aeval_eq_aeval_coeff_one_of_isHomogeneous
      (characteristicCoefficient_isHomogeneous p r n j hj)]
  · simpa using eval_characteristicCoefficient p r n N j
  · intro ij
    simpa using Polynomial.natDegree_monomial_le (N ij.1 ij.2) (m := 1)

/-- When the fixed endpoint is nilpotent, the top possible partner
coefficient vanishes. -/
theorem coeff_top_partnerCharacteristicCoefficient_eq_zero
    (N M : Matrix (Fin n) (Fin n) K) (j : ℕ)
    (hj1 : 1 ≤ j) (hjn : j ≤ n) (hN : IsNilpotent N) :
    (partnerCharacteristicCoefficient p r n N M j).coeff j = 0 := by
  rw [coeff_top_partnerCharacteristicCoefficient p r n N M j hjn]
  have hcoeff :=
    (characteristicCoefficientsVanish_iff p r n N).mpr hN j hj1 hjn
  rw [eval_characteristicCoefficient] at hcoeff
  exact hcoeff

/-- All polynomial equations in `defn:partner` vanish. -/
def PartnerEquationsVanish
    (N M : Matrix (Fin n) (Fin n) K) : Prop :=
  ∀ j, 1 ≤ j → j ≤ n →
    partnerCharacteristicCoefficient p r n N M j = 0

/-- Vanishing of the finite strict-triangle family of partner
coefficients. -/
def PartnerTriangleVanish
    (N M : Matrix (Fin n) (Fin n) K) : Prop :=
  ∀ j, 1 ≤ j → j ≤ n → ∀ i, i < j →
    (partnerCharacteristicCoefficient p r n N M j).coeff i = 0

/-- The finite ordered list of partner coefficients, using the same strict
lower-triangle enumeration as the Steenrod list. -/
noncomputable def partnerCoefficientList
    (N M : Matrix (Fin n) (Fin n) K) : List K :=
  (QSteenrod.strictLowerTriangleIndices n).map fun ij =>
    (partnerCharacteristicCoefficient p r n N M ij.2).coeff ij.1

/-- Predicate form and ordered-list form of triangular vanishing agree. -/
theorem partnerTriangleVanish_iff_list
    (N M : Matrix (Fin n) (Fin n) K) :
    PartnerTriangleVanish p r n N M ↔
      ∀ a ∈ partnerCoefficientList p r n N M, a = 0 := by
  constructor
  · intro h a ha
    rw [partnerCoefficientList] at ha
    obtain ⟨ij, hij, rfl⟩ := List.mem_map.mp ha
    obtain ⟨hj1, hjn, hij'⟩ :=
      (QSteenrod.mem_strictLowerTriangleIndices_iff n ij.1 ij.2).mp hij
    exact h ij.2 hj1 hjn ij.1 hij'
  · intro h j hj1 hjn i hij
    apply h
    rw [partnerCoefficientList]
    apply List.mem_map.mpr
    exact ⟨(i, j),
      (QSteenrod.mem_strictLowerTriangleIndices_iff n i j).mpr
        ⟨hj1, hjn, hij⟩, rfl⟩

/-- For a nilpotent fixed endpoint, the strict-triangle coefficients are
equivalent to the full partner polynomial identities. -/
theorem partnerTriangleVanish_iff_partnerEquationsVanish
    (N M : Matrix (Fin n) (Fin n) K) (hN : IsNilpotent N) :
    PartnerTriangleVanish p r n N M ↔
      PartnerEquationsVanish p r n N M := by
  constructor
  · intro htriangle j hj1 hjn
    apply Polynomial.ext
    intro i
    simp only [Polynomial.coeff_zero]
    rcases lt_trichotomy i j with hij | hij | hji
    · exact htriangle j hj1 hjn i hij
    · subst i
      exact coeff_top_partnerCharacteristicCoefficient_eq_zero
        p r n N M j hj1 hjn hN
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt
        ((natDegree_partnerCharacteristicCoefficient_le
          p r n N M j hjn).trans_lt hji)
  · intro hfull j hj1 hjn i hij
    rw [hfull j hj1 hjn]
    exact Polynomial.coeff_zero i

/-- For a fixed nilpotent endpoint over an infinite field, the coefficient
equations cut out exactly its nilpotent partners. -/
theorem partnerEquationsVanish_iff_partner [Infinite K]
    (N M : Matrix (Fin n) (Fin n) K) (hN : IsNilpotent N) :
    PartnerEquationsVanish p r n N M ↔ NilpotentPencil N M := by
  rw [nilpotentPencil_comm,
    nilpotentPencil_iff_line_of_right M N hN]
  constructor
  · intro h t
    rw [← characteristicCoefficientsVanish_iff p r n]
    intro j hj1 hjn
    have hj := congrArg (fun f : Polynomial K => f.eval t) (h j hj1 hjn)
    rw [eval_partnerCharacteristicCoefficient p r n N M j t] at hj
    rw [eval_characteristicCoefficient p r n (M + t • N) j]
    simpa using hj
  · intro h j hj1 hjn
    apply Polynomial.zero_of_eval_zero
    intro t
    rw [eval_partnerCharacteristicCoefficient]
    have hc :=
      (characteristicCoefficientsVanish_iff p r n (M + t • N)).mpr (h t)
        j hj1 hjn
    rwa [eval_characteristicCoefficient] at hc

/-- Finite strict-triangle form of the partner equations. -/
theorem partnerTriangleVanish_iff_partner [Infinite K]
    (N M : Matrix (Fin n) (Fin n) K) (hN : IsNilpotent N) :
    PartnerTriangleVanish p r n N M ↔ NilpotentPencil N M := by
  rw [partnerTriangleVanish_iff_partnerEquationsVanish p r n N M hN,
    partnerEquationsVanish_iff_partner p r n N M hN]

end Height.Steenrod
