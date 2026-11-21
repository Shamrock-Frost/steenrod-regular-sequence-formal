import Mathlib.Algebra.Module.PID
import Mathlib.Algebra.Polynomial.Module.AEval
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.LinearAlgebra.DirectSum.Basis
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Rationality of the Jordan form for nilpotent matrices

`cor:qfree` needs one geometric input the development did not have: over an
algebraically closed field every nilpotent matrix is conjugate to a matrix with
entries in the prime field (indeed in any subfield).  Mathlib has no Jordan
normal form, so this file builds it for nilpotent endomorphisms out of the
structure theorem for finitely generated torsion modules over a PID
(`Module.torsion_by_prime_power_decomposition`, `Algebra/Module/PID.lean`).

The route:

* `Module.AEval' f` is `V` with the `L[X]`-module structure in which `X` acts by
  `f`; `f` nilpotent makes it `X`-power torsion (`isTorsion'_aeval`), so the
  structure theorem gives `AEval' f ≃ₗ[L[X]] ⨁_i L[X] ⧸ (X^{k i})`.
* `quoBasis` is the `L`-basis `1, X, …, X^{e-1}` of `L[X] ⧸ (X^e)`, on which
  multiplication by `X` is the shift (`X_smul_quoBasis`); `DFinsupp.basis`
  assembles these into `dsBasis`, a basis of the direct sum indexed by
  `Σ i, Fin (k i)` on which `X` is again a shift.
* Transporting along the equivalence gives `exists_shift_basis`: a basis of `V`
  on which `f` sends every basis vector to a basis vector or to `0`.
* In such a basis the matrix of `f` has entries `0` and `1` only
  (`exists_zeroOne_conj`), and `0`, `1` lie in every subfield
  (`exists_conj_rational`).

No `Fin n` indexing is assumed inside; the reindexing to `Fin n` is
`Basis.indexEquiv` against `Pi.basisFun`.
-/

open Polynomial Module

namespace Height.Toolbox.JordanBasis

variable {L : Type*} [Field L]

/-- The polynomial `∑_{j < e} g j X^j`. -/
noncomputable def polyOf {e : ℕ} (g : Fin e → L) : L[X] :=
  ∑ j : Fin e, C (g j) * X ^ (j : ℕ)

theorem coeff_polyOf {e : ℕ} (g : Fin e → L) (d : ℕ) (hd : d < e) :
    (polyOf g).coeff d = g ⟨d, hd⟩ := by
  classical
  rw [polyOf, Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single (⟨d, hd⟩ : Fin e)]
  · simp
  · intro j _ hj
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, ite_eq_right, mul_zero]
    intro h
    exact absurd (Fin.ext h.symm) hj
  · intro h; exact absurd (Finset.mem_univ _) h

variable (L) in
/-- `L[X] ⧸ (X^e)` as an `L[X]`-module. -/
abbrev Quo (e : ℕ) := L[X] ⧸ (Submodule.span L[X] {(X : L[X]) ^ e})

/-- The image of `a` in `L[X] ⧸ (X^e)`. -/
noncomputable def quoMk (e : ℕ) (a : L[X]) : Quo L e := Submodule.Quotient.mk a

theorem quoMk_smul (e : ℕ) (c : L) (a : L[X]) :
    c • quoMk (L := L) e a = quoMk e (C c * a) := by
  rw [quoMk, quoMk, ← Submodule.Quotient.mk_smul]
  congr 1
  rw [Polynomial.smul_eq_C_mul]

theorem quoMk_X_smul (e : ℕ) (a : L[X]) :
    (X : L[X]) • quoMk (L := L) e a = quoMk e (X * a) := rfl

theorem quoMk_eq_zero_iff (e : ℕ) (a : L[X]) :
    quoMk (L := L) e a = 0 ↔ ∀ d < e, a.coeff d = 0 := by
  rw [quoMk, Submodule.Quotient.mk_eq_zero, Submodule.mem_span_singleton,
    ← Polynomial.X_pow_dvd_iff]
  constructor
  · rintro ⟨b, rfl⟩; exact ⟨b, by rw [smul_eq_mul]; ring⟩
  · rintro ⟨b, rfl⟩; exact ⟨b, by rw [smul_eq_mul]; ring⟩

theorem quoMk_surjective (e : ℕ) : Function.Surjective (quoMk (L := L) e) :=
  Submodule.Quotient.mk_surjective _

theorem quoMk_sum {ι : Type*} (e : ℕ) (s : Finset ι) (f : ι → L[X]) :
    quoMk (L := L) e (∑ i ∈ s, f i) = ∑ i ∈ s, quoMk e (f i) :=
  map_sum (Submodule.span L[X] {(X : L[X]) ^ e}).mkQ f s

theorem quoMk_sub (e : ℕ) (a b : L[X]) :
    quoMk (L := L) e (a - b) = quoMk e a - quoMk e b :=
  map_sub (Submodule.span L[X] {(X : L[X]) ^ e}).mkQ a b

theorem sum_smul_quoMk {e : ℕ} (g : Fin e → L) :
    ∑ j : Fin e, g j • quoMk (L := L) e (X ^ (j : ℕ)) = quoMk e (polyOf g) := by
  rw [polyOf, quoMk_sum]
  exact Finset.sum_congr rfl fun j _ => quoMk_smul e (g j) _

/-- The `L`-basis `1, X, …, X^{e-1}` of `L[X] ⧸ (X^e)`. -/
noncomputable def quoBasis (e : ℕ) : Basis (Fin e) L (Quo L e) := by
  refine Basis.mk (v := fun j : Fin e => quoMk (L := L) e (X ^ (j : ℕ))) ?_ ?_
  · rw [Fintype.linearIndependent_iff]
    intro g hg j
    rw [sum_smul_quoMk, quoMk_eq_zero_iff] at hg
    have hj := hg (j : ℕ) j.2
    rwa [coeff_polyOf g (j : ℕ) j.2, Fin.eta] at hj
  · rintro z -
    obtain ⟨a, rfl⟩ := quoMk_surjective (L := L) e z
    have key : quoMk (L := L) e a =
        ∑ j : Fin e, a.coeff (j : ℕ) • quoMk (L := L) e (X ^ (j : ℕ)) := by
      rw [sum_smul_quoMk, ← sub_eq_zero, ← quoMk_sub, quoMk_eq_zero_iff]
      intro d hd
      rw [Polynomial.coeff_sub, coeff_polyOf _ d hd, sub_self]
    rw [key]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

@[simp] theorem quoBasis_apply (e : ℕ) (j : Fin e) :
    quoBasis (L := L) e j = quoMk e (X ^ (j : ℕ)) := by
  rw [quoBasis, Basis.mk_apply]

theorem X_smul_quoBasis (e : ℕ) (j : Fin e) :
    (X : L[X]) • quoBasis (L := L) e j =
      if h : (j : ℕ) + 1 < e then quoBasis (L := L) e ⟨(j : ℕ) + 1, h⟩ else 0 := by
  rw [quoBasis_apply, quoMk_X_smul, ← pow_succ']
  split
  · rw [quoBasis_apply]
  · rename_i h
    have he : (j : ℕ) + 1 = e := by omega
    rw [he, quoMk_eq_zero_iff]
    intro d hd
    simp [Polynomial.coeff_X_pow, Nat.ne_of_lt hd]


/-! ## The direct sum -/

/-- The `L`-basis of `⨁ i, L[X] ⧸ (X^{k i})` given by the monomials in each summand. -/
noncomputable def dsBasis {d : ℕ} (k : Fin d → ℕ) :
    Basis (Σ i : Fin d, Fin (k i)) L (DirectSum (Fin d) fun i => Quo L (k i)) :=
  DFinsupp.basis fun i => quoBasis (k i)

theorem dsBasis_apply {d : ℕ} (k : Fin d → ℕ) (s : Σ i : Fin d, Fin (k i)) :
    dsBasis (L := L) k s = DFinsupp.single s.1 (quoBasis (k s.1) s.2) := by
  classical
  simp only [dsBasis, DFinsupp.basis, Basis.coe_ofRepr, LinearEquiv.symm_trans_apply,
    LinearEquiv.symm_symm, sigmaFinsuppLequivDFinsupp_apply,
    DFinsupp.mapRange.linearEquiv_symm, DFinsupp.mapRange.linearEquiv_apply]
  rw [show sigmaFinsuppAddEquivDFinsupp.toFun (Finsupp.single s (1 : L))
      = DFinsupp.single s.1 (Finsupp.single s.2 (1 : L)) from
    sigmaFinsuppEquivDFinsupp_single s 1, DFinsupp.mapRange_single]
  simp


theorem X_smul_dsBasis {d : ℕ} (k : Fin d → ℕ) (i : Fin d) (j : Fin (k i)) :
    (X : L[X]) • dsBasis (L := L) k ⟨i, j⟩ =
      if h : (j : ℕ) + 1 < k i then dsBasis (L := L) k ⟨i, ⟨(j : ℕ) + 1, h⟩⟩ else 0 := by
  classical
  rw [dsBasis_apply, ← DFinsupp.single_smul, X_smul_quoBasis]
  split
  · rw [dsBasis_apply]
  · rw [DFinsupp.single_zero]


/-! ## Nilpotent endomorphisms -/

section Endo

variable {V : Type*} [AddCommGroup V] [Module L V] [FiniteDimensional L V]

omit [FiniteDimensional L V] in
/-- A nilpotent endomorphism makes `V` an `X`-power torsion `L[X]`-module. -/
theorem isTorsion'_aeval (f : Module.End L V) (hf : IsNilpotent f) :
    Module.IsTorsion' (Module.AEval' f) (Submonoid.powers (X : L[X])) := by
  intro m
  obtain ⟨N, hN⟩ := hf
  obtain ⟨v, hv⟩ : ∃ v, m = Module.AEval'.of f v := ⟨(Module.AEval'.of f).symm m, by simp⟩
  refine ⟨⟨(X : L[X]) ^ N, N, rfl⟩, ?_⟩
  show ((X : L[X]) ^ N) • m = 0
  rw [hv, Module.AEval'.X_pow_smul_of, hN]
  simp

/-- **Jordan basis for a nilpotent endomorphism.**  There is a basis on which `f`
acts by sending each basis vector to another basis vector or to zero. -/
theorem exists_shift_basis (f : Module.End L V) (hf : IsNilpotent f) :
    ∃ (ι : Type) (_ : Fintype ι) (b : Basis ι L V) (nx : ι → Option ι),
      ∀ i, f (b i) = (nx i).elim 0 b := by
  obtain ⟨d, k, ⟨φ⟩⟩ := Module.torsion_by_prime_power_decomposition
    (R := L[X]) (M := Module.AEval' f) Polynomial.irreducible_X (isTorsion'_aeval f hf)
  set ψ : V ≃ₗ[L] DirectSum (Fin d) (fun i => Quo L (k i)) :=
    (Module.AEval'.of f).trans (φ.restrictScalars L) with hψdef
  have hψ : ∀ v : V, ψ (f v) = (X : L[X]) • ψ v := by
    intro v
    show φ (Module.AEval'.of f (f v)) = (X : L[X]) • φ (Module.AEval'.of f v)
    rw [← Module.AEval'.X_smul_of, map_smul]
  have key : ∀ w, f (ψ.symm w) = ψ.symm ((X : L[X]) • w) := by
    intro w
    apply ψ.injective
    rw [hψ, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  refine ⟨Σ i : Fin d, Fin (k i), inferInstance, (dsBasis k).map ψ.symm,
    fun s => if h : (s.2 : ℕ) + 1 < k s.1 then some ⟨s.1, ⟨(s.2 : ℕ) + 1, h⟩⟩ else none, ?_⟩
  rintro ⟨i, j⟩
  rw [Basis.map_apply, key, X_smul_dsBasis]
  by_cases h : (j : ℕ) + 1 < k i <;> simp [h, Basis.map_apply]

end Endo

/-! ## Matrices -/

section Matrices

open Matrix

variable {n : ℕ}

/-- A nilpotent matrix over any field is conjugate to a matrix all of whose
entries are `0` or `1`. -/
theorem exists_zeroOne_conj (M : Matrix (Fin n) (Fin n) L) (hM : IsNilpotent M) :
    ∃ A : Matrix (Fin n) (Fin n) L, (∀ i j, A i j = 0 ∨ A i j = 1) ∧
      ∃ P : Matrix (Fin n) (Fin n) L, IsUnit P ∧ M * P = P * A := by
  classical
  have hf : IsNilpotent (Matrix.toLin' M) := by
    have := hM.map (Matrix.toLinAlgEquiv' (R := L) (n := Fin n))
    exact this
  obtain ⟨ι, _, b0, nx0, hb0⟩ := exists_shift_basis (Matrix.toLin' M) hf
  set e : ι ≃ Fin n := b0.indexEquiv (Pi.basisFun L (Fin n)) with he
  set b : Basis (Fin n) L (Fin n → L) := b0.reindex e with hb
  set nx : Fin n → Option (Fin n) := fun t => (nx0 (e.symm t)).map e with hnx
  have hstep : ∀ t, M *ᵥ (b t) = (nx t).elim 0 b := by
    intro t
    have h0 := hb0 (e.symm t)
    have hbt : b t = b0 (e.symm t) := by rw [hb, Basis.reindex_apply]
    have hnxt : nx t = (nx0 (e.symm t)).map e := rfl
    rw [hbt, hnxt, show M *ᵥ b0 (e.symm t) = Matrix.toLin' M (b0 (e.symm t)) from rfl, h0]
    cases nx0 (e.symm t) with
    | none => simp
    | some s => simp [hb]
  refine ⟨Matrix.of fun i t => if nx t = some i then (1 : L) else 0, ?_,
    (Pi.basisFun L (Fin n)).toMatrix b, ?_, ?_⟩
  · intro i j
    by_cases h : nx j = some i <;> simp [h]
  · have hinv := (Pi.basisFun L (Fin n)).invertibleToMatrix b
    exact isUnit_of_invertible _
  · ext i t
    have hP : ∀ l s : Fin n, (Pi.basisFun L (Fin n)).toMatrix b l s = b s l := by
      intro l s; simp [Basis.toMatrix_apply]
    rw [Matrix.mul_apply, Matrix.mul_apply]
    have hlhs : ∑ l, M i l * (Pi.basisFun L (Fin n)).toMatrix b l t = (M *ᵥ (b t)) i := by
      rw [Matrix.mulVec_apply_eq_sum]
      exact Finset.sum_congr rfl fun l _ => by rw [hP]
    rw [hlhs, hstep]
    cases hcase : nx t with
    | none =>
        simp only [Option.elim_none, Pi.zero_apply]
        refine (Finset.sum_eq_zero fun l _ => ?_).symm
        simp [hcase]
    | some l0 =>
        simp only [Option.elim_some]
        rw [Finset.sum_eq_single l0]
        · simp [hP, hcase]
        · intro l _ hl
          simp [hcase, Ne.symm hl]
        · intro h; exact absurd (Finset.mem_univ _) h


theorem isNilpotent_conj {R : Type*} [Ring R] (u : Rˣ) {a : R} (ha : IsNilpotent a) :
    IsNilpotent ((u : R) * a * (↑u⁻¹ : R)) := by
  obtain ⟨m, hm⟩ := ha
  exact ⟨m, by rw [u.conj_pow, hm, mul_zero, zero_mul]⟩

/-- **Rationality of the Jordan form.**  A nilpotent matrix over `L` is conjugate
to the image of a nilpotent matrix over any subfield `k` of `L`. -/
theorem exists_conj_rational {k : Type*} [Field k] [Algebra k L]
    (M : Matrix (Fin n) (Fin n) L) (hM : IsNilpotent M) :
    ∃ N : Matrix (Fin n) (Fin n) k, IsNilpotent N ∧
      ∃ g : (Matrix (Fin n) (Fin n) L)ˣ,
        M = (g : Matrix (Fin n) (Fin n) L) * N.map (algebraMap k L) *
          (↑g⁻¹ : Matrix (Fin n) (Fin n) L) := by
  classical
  obtain ⟨A, hA01, P, hPu, hMP⟩ := exists_zeroOne_conj M hM
  obtain ⟨u, hu⟩ := hPu
  set N : Matrix (Fin n) (Fin n) k := Matrix.of fun i j => if A i j = 1 then (1 : k) else 0 with hN
  have hNmap : N.map (algebraMap k L) = A := by
    ext i j
    rw [Matrix.map_apply, hN]
    by_cases h : A i j = 1
    · simp [h]
    · rcases hA01 i j with h0 | h1
      · simp [h0]
      · exact absurd h1 h
  have hcomm : M * (u : Matrix (Fin n) (Fin n) L) = (u : Matrix (Fin n) (Fin n) L) * A := by
    rw [hu]; exact hMP
  have hMeq : M = (u : Matrix (Fin n) (Fin n) L) * A * (↑u⁻¹ : Matrix (Fin n) (Fin n) L) := by
    rw [← hcomm, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
  have hAeq : A = (↑u⁻¹ : Matrix (Fin n) (Fin n) L) * M *
      (↑(u⁻¹)⁻¹ : Matrix (Fin n) (Fin n) L) := by
    rw [inv_inv, mul_assoc, hcomm, ← mul_assoc, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, one_mul]
  refine ⟨N, ?_, u, by rw [hNmap]; exact hMeq⟩
  have hAnil : IsNilpotent A := hAeq ▸ isNilpotent_conj u⁻¹ hM
  rw [← IsNilpotent.map_iff
    (f := (algebraMap k L).mapMatrix (m := Fin n))
    (Matrix.map_injective (algebraMap k L).injective)]
  rw [show ((algebraMap k L).mapMatrix (m := Fin n)) N = N.map (algebraMap k L) from rfl, hNmap]
  exact hAnil

end Matrices

end Height.Toolbox.JordanBasis
