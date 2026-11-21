import Height.Steenrod.Partner
import Height.Toolbox.Flags
import Height.Toolbox.Lang
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Lang's map on matrix units (`thm:lang`, `prop:untwist`)

This specializes the abstract group-theoretic Lang map to invertible matrices
and packages the algebraic content of `prop:untwist`.  Lang surjectivity and
the geometric fiber-dimension comparison remain separate.
-/

namespace Height.Steenrod

open Height.Toolbox

universe u v

variable (p r : ℕ)
variable {K : Type u} [Field K] [ExpChar K p]
variable {ι : Type v} [Fintype ι] [DecidableEq ι]

/-- Entrywise Frobenius on invertible matrices. -/
def frobeniusMatrixUnitsHom :
    (Matrix ι ι K)ˣ →* (Matrix ι ι K)ˣ :=
  Units.map (iterateFrobenius K p r).mapMatrix.toMonoidHom

@[simp] theorem coe_frobeniusMatrixUnitsHom
    (g : (Matrix ι ι K)ˣ) :
    (frobeniusMatrixUnitsHom p r g : Matrix ι ι K) =
      frobeniusMatrix p r (g : Matrix ι ι K) := by
  rfl

@[simp] theorem coe_frobeniusMatrixUnitsHom_inv
    (g : (Matrix ι ι K)ˣ) :
    (↑((frobeniusMatrixUnitsHom p r g)⁻¹) : Matrix ι ι K) =
      frobeniusMatrix p r (↑(g⁻¹) : Matrix ι ι K) := by
  rw [← map_inv]
  rfl

/-- Lang's map `g ↦ g⁻¹ Fr(g)` on invertible matrices. -/
def matrixLang (g : (Matrix ι ι K)ˣ) : (Matrix ι ι K)ˣ :=
  Height.Toolbox.langMap (frobeniusMatrixUnitsHom p r) g

@[simp] theorem coe_matrixLang (g : (Matrix ι ι K)ˣ) :
    (matrixLang p r g : Matrix ι ι K) =
      (↑(g⁻¹) : Matrix ι ι K) *
        frobeniusMatrix p r (g : Matrix ι ι K) := by
  rfl

@[simp] theorem coe_matrixLang_inv (g : (Matrix ι ι K)ˣ) :
    (↑((matrixLang p r g)⁻¹) : Matrix ι ι K) =
      frobeniusMatrix p r (↑(g⁻¹) : Matrix ι ι K) *
        (g : Matrix ι ι K) := by
  rw [matrixLang, Height.Toolbox.langMap, mul_inv_rev, ← map_inv]
  rfl

/-- Two invertible matrices have the same matrix Lang value exactly when
their left quotient is fixed by entrywise Frobenius. -/
theorem matrixLang_eq_iff (g' g : (Matrix ι ι K)ˣ) :
    matrixLang p r g' = matrixLang p r g ↔
      frobeniusMatrixUnitsHom p r (g' * g⁻¹) = g' * g⁻¹ :=
  Height.Toolbox.langMap_eq_iff (frobeniusMatrixUnitsHom p r) g' g

/-- Fiber-coset form of `matrixLang_eq_iff`. -/
theorem matrixLang_fiber (g' g : (Matrix ι ι K)ˣ) :
    matrixLang p r g' = matrixLang p r g ↔
      ∃ γ : (Matrix ι ι K)ˣ,
        frobeniusMatrixUnitsHom p r γ = γ ∧ g' = γ * g :=
  Height.Toolbox.lang_fiber (frobeniusMatrixUnitsHom p r) g' g

omit [ExpChar K p] in
private theorem frobeniusFixedScalars_finite [Fact p.Prime] [NeZero r] :
    Set.Finite {x : K | x ^ (p ^ r) = x} := by
  have hpoly :
      (Polynomial.X ^ (p ^ r) - Polynomial.X : Polynomial K) ≠ 0 :=
    FiniteField.X_pow_card_pow_sub_X_ne_zero K (NeZero.ne r)
      (Fact.out : Nat.Prime p).one_lt
  simpa [Polynomial.IsRoot.def, sub_eq_zero] using
    (Polynomial.finite_setOfPred_isRoot hpoly)

omit [DecidableEq ι] in
private theorem frobeniusFixedMatrices_finite [Fact p.Prime] [NeZero r] :
    Set.Finite {M : Matrix ι ι K | frobeniusMatrix p r M = M} := by
  have hscalar := frobeniusFixedScalars_finite (K := K) p r
  have hpi : Set.Finite
      {M : Matrix ι ι K | ∀ i j, M i j ∈ {x : K | x ^ (p ^ r) = x}} :=
    Set.Finite.pi' fun _ => Set.Finite.pi' fun _ => hscalar
  apply hpi.subset
  intro M hM i j
  have hij := congrFun (congrFun hM i) j
  change M i j ^ (p ^ r) = M i j
  simpa only [frobeniusMatrix_apply] using hij

/-- The Frobenius-fixed subgroup of `GL` is finite.  This needs only that
`q = p^r > 1`; it does not require identifying the fixed field with the
chosen concrete copy of `F_q`. -/
theorem frobeniusFixedMatrixUnits_finite [Fact p.Prime] [NeZero r] :
    Set.Finite
      {g : (Matrix ι ι K)ˣ | frobeniusMatrixUnitsHom p r g = g} := by
  refine Set.Finite.of_finite_image
    (f := fun g : (Matrix ι ι K)ˣ => (g : Matrix ι ι K)) ?_
    Units.val_injective.injOn
  apply (frobeniusFixedMatrices_finite (K := K) (ι := ι) p r).subset
  rintro M ⟨g, hg, rfl⟩
  exact congrArg Units.val hg

/-- Every fiber of the matrix Lang map is finite, independently of its
surjectivity. -/
theorem matrixLang_fiber_finite [Fact p.Prime] [NeZero r]
    (g : (Matrix ι ι K)ˣ) :
    Set.Finite {g' : (Matrix ι ι K)ˣ |
      matrixLang p r g' = matrixLang p r g} := by
  have hset :
      {g' : (Matrix ι ι K)ˣ | matrixLang p r g' = matrixLang p r g} =
        (fun γ => γ * g) ''
          {γ : (Matrix ι ι K)ˣ | frobeniusMatrixUnitsHom p r γ = γ} := by
    ext g'
    constructor
    · intro hg'
      obtain ⟨γ, hγ, hprod⟩ := (matrixLang_fiber p r g' g).mp hg'
      exact ⟨γ, hγ, hprod.symm⟩
    · rintro ⟨γ, hγ, rfl⟩
      exact (matrixLang_fiber p r (γ * g) g).mpr ⟨γ, hγ, rfl⟩
  rw [hset]
  exact (frobeniusFixedMatrixUnits_finite (K := K) (ι := ι) p r).image _

/-- The transport calculation from `prop:untwist`, with all inverses bundled
as units: the Frobenius pencil through `gNg⁻¹` is nilpotent exactly when the
ordinary pencil through `N` and its Lang conjugate is nilpotent. -/
theorem frobeniusPencil_iff_langPartner [Fact p.Prime]
    (g : (Matrix ι ι K)ˣ) (N : Matrix ι ι K)
    (hN : frobeniusMatrix p r N = N) :
    NilpotentPencil
        ((g : Matrix ι ι K) * N * (↑(g⁻¹) : Matrix ι ι K))
        (frobeniusMatrix p r
          ((g : Matrix ι ι K) * N * (↑(g⁻¹) : Matrix ι ι K))) ↔
      NilpotentPencil N
        ((matrixLang p r g : Matrix ι ι K) * N *
          (↑((matrixLang p r g)⁻¹) : Matrix ι ι K)) := by
  simpa only [NilpotentPencil, coe_matrixLang,
    coe_matrixLang_inv] using
    (frobenius_pencil_untwist p r
      (g : Matrix ι ι K) (↑(g⁻¹) : Matrix ι ι K) N
      (by simp) (by simp) hN)

/-- The linear-algebraic last step in Lang surjectivity: a basis of row
vectors satisfying `Fr(row) = row · b` assembles into a preimage of `b`
under the matrix Lang map. -/
theorem exists_matrixLang_eq_of_fixed_row_basis [Fact p.Prime]
    (b : (Matrix ι ι K)ˣ) (v : ι → ι → K)
    (hv : LinearIndependent K v)
    (hfixed : ∀ i j,
      (v i j) ^ (p ^ r) = ∑ k, v i k * (b : Matrix ι ι K) k j) :
    ∃ g : (Matrix ι ι K)ˣ, matrixLang p r g = b := by
  let M : Matrix ι ι K := fun i j => v i j
  have hM : IsUnit M := Matrix.linearIndependent_rows_iff_isUnit.mp (by
    simpa [Matrix.row, M] using hv)
  obtain ⟨g, hg⟩ := hM
  refine ⟨g, Units.ext ?_⟩
  rw [coe_matrixLang]
  have hF : frobeniusMatrix p r (g : Matrix ι ι K) =
      (g : Matrix ι ι K) * (b : Matrix ι ι K) := by
    rw [hg]
    ext i j
    rw [frobeniusMatrix_apply, Matrix.mul_apply]
    exact hfixed i j
  rw [hF, ← Matrix.mul_assoc]
  simp

omit [ExpChar K p] in
/-- The affine Frobenius equation used to construct triangular fixed rows
one coordinate at a time.  Algebraic closedness supplies a root of
`X^q - a X - c`, whose degree is `q = p^r > 1`. -/
theorem exists_frobenius_pow_sub_mul_eq [Fact p.Prime] [NeZero r]
    [IsAlgClosed K] (a c : K) :
    ∃ x : K, x ^ (p ^ r) - a * x = c := by
  let q := p ^ r
  let P : Polynomial K :=
    Polynomial.X ^ q -
      (Polynomial.C a * Polynomial.X + Polynomial.C c)
  have hq : 1 < q :=
    Nat.one_lt_pow (NeZero.ne r) (Fact.out : Nat.Prime p).one_lt
  have hlower :
      Polynomial.degree
          (Polynomial.C a * Polynomial.X + Polynomial.C c) ≤ 1 := by
    calc
      Polynomial.degree
          (Polynomial.C a * Polynomial.X + Polynomial.C c) ≤
          max (Polynomial.degree (Polynomial.C a * Polynomial.X))
            (Polynomial.degree (Polynomial.C c)) :=
        Polynomial.degree_add_le _ _
      _ ≤ 1 := max_le (Polynomial.degree_C_mul_X_le a)
        (Polynomial.degree_C_le.trans (by simp))
  have hdegree : P.degree = q := by
    dsimp [P]
    rw [Polynomial.degree_sub_eq_left_of_degree_lt]
    · exact Polynomial.degree_X_pow q
    · rw [Polynomial.degree_X_pow]
      exact hlower.trans_lt (by exact_mod_cast hq)
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root P (by
    rw [hdegree]
    exact_mod_cast (show q ≠ 0 by omega))
  refine ⟨x, ?_⟩
  have hx' : x ^ q = a * x + c := by
    apply sub_eq_zero.mp
    simpa [P, Polynomial.IsRoot.def] using hx
  rw [show p ^ r = q by rfl, hx']
  abel

section RationalOrbit

/-! ### Pointwise untwisting on a rational orbit (`prop:untwist`) -/

variable (p r n : ℕ) [Fact p.Prime] [NeZero r]
variable {K : Type u} [Field K] [ExpChar K p]
variable [Algebra (GaloisField p r) K] [Infinite K]

/-- The pointwise algebraic heart of untwisting for the orbit of an
`F_q`-rational matrix. -/
theorem rationalOrbit_steenrodVanish_iff_langPartner
    (g : (Matrix (Fin n) (Fin n) K)ˣ)
    (N₀ : Matrix (Fin n) (Fin n) (GaloisField p r)) :
    powerCharacteristicCoefficientsVanishAt p r
        ((g : Matrix (Fin n) (Fin n) K) *
          N₀.map (algebraMap (GaloisField p r) K) *
          (↑(g⁻¹) : Matrix (Fin n) (Fin n) K)) ↔
      NilpotentPencil
        (N₀.map (algebraMap (GaloisField p r) K))
        ((matrixLang p r g : Matrix (Fin n) (Fin n) K) *
          N₀.map (algebraMap (GaloisField p r) K) *
          (↑((matrixLang p r g)⁻¹) : Matrix (Fin n) (Fin n) K)) := by
  let N : Matrix (Fin n) (Fin n) K :=
    N₀.map (algebraMap (GaloisField p r) K)
  let M : Matrix (Fin n) (Fin n) K :=
    (g : Matrix (Fin n) (Fin n) K) * N *
      (↑(g⁻¹) : Matrix (Fin n) (Fin n) K)
  calc
    powerCharacteristicCoefficientsVanishAt p r M ↔
        NilpotentPencil M (frobeniusMatrix p r M) :=
      powerCharacteristicCoefficientsVanishAt_iff_partner p r M
    _ ↔ NilpotentPencil N
        ((matrixLang p r g : Matrix (Fin n) (Fin n) K) * N *
          (↑((matrixLang p r g)⁻¹) : Matrix (Fin n) (Fin n) K)) :=
      frobeniusPencil_iff_langPartner p r g N
        (frobeniusMatrix_map_algebraMap p r N₀)

end RationalOrbit

end Height.Steenrod
