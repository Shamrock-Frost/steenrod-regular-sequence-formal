import Height.Pencil.Basic
import Height.Graded.LocalLength
import Height.Orbital.Arcs

/-!
# The local charts of `ℙ¹`

There is no homogeneous localisation `R_x`.  A point of `ℙ¹` is either a
scalar `t₀ : K` or the point at infinity, and the local algebra is a ring
homomorphism `B = K[μ,ν] →+* K⟦u⟧`.

**The parameter convention.**  One could take the finite chart to be
`μ ↦ t₀ + u, ν ↦ 1`, i.e. `t = μ/ν`.  That is *not* the parameter convention of
`Chain/Incidence.lean`, where the members of the pencil are `N + t M`, i.e.
`t = ν/μ`.  Since the whole chain (`GenericType`, `markedLocus`, (H2′)) uses
`N + t M`, the charts here are

```
atPoint t₀ : μ ↦ 1,  ν ↦ t₀ + u        (finite points, `matC (Pat N M t₀) = N + t₀ • M`)
atInf      : μ ↦ u,  ν ↦ 1             (the point at infinity, `matC (Pat∞ N M) = M`)
```

which is that chart composed with the swap `μ ↔ ν`; `Pat N M t₀` is then
the affine-linear family `N + (t₀ + u) M` and `∂_u Pat = M`.  This is the
`dPat` of the file: the constant matrix `M` over `K⟦u⟧`.

`constantCoeff ∘ atPoint t₀` is the evaluation `(μ,ν) ↦ (1, t₀)`; the paper
states this for homogeneous `f` (where it is the value of `f/μ^e` at `t₀`), but
as a statement about ring homomorphisms it needs no homogeneity, so
`constantCoeff_atPoint` is unconditional.
-/

namespace Height.Pencil

open Matrix Height.Graded Height.Orbital

variable {K : Type*} [Field K] {n : ℕ}

/-! ### The pencil in a chart -/

/-- The pencil `μN + νM` in the chart at the finite point `t₀`: the family
`N + (t₀ + u) M` over `K⟦u⟧`. -/
noncomputable def Pat (N M : Matrix (Fin n) (Fin n) K) (t₀ : K) :
    Matrix (Fin n) (Fin n) (PowerSeries K) :=
  (pencil N M).map (atPoint t₀)

/-- The pencil in the chart at infinity: the family `u N + M`. -/
noncomputable def PatInf (N M : Matrix (Fin n) (Fin n) K) :
    Matrix (Fin n) (Fin n) (PowerSeries K) :=
  (pencil N M).map atInf

/-- A pencil direction in the chart at `t₀`. -/
noncomputable def Qat (Q : Matrix (Fin n) (Fin n) (Graded.Poly K)) (t₀ : K) :
    Matrix (Fin n) (Fin n) (PowerSeries K) :=
  Q.map (atPoint t₀)

/-- `∂_u` of the pencil in the finite chart: the constant matrix `M`.  (The
family `Pat N M t₀ = N + (t₀ + u) M` is affine in `u`, so this is literally its
derivative; see `Pat_eq_add_smul`.) -/
noncomputable def dPat (M : Matrix (Fin n) (Fin n) K) :
    Matrix (Fin n) (Fin n) (PowerSeries K) :=
  M.map PowerSeries.C

@[simp] theorem dPat_apply (M : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    dPat M i j = PowerSeries.C (M i j) := rfl

@[simp] theorem Pat_apply (N M : Matrix (Fin n) (Fin n) K) (t₀ : K) (i j : Fin n) :
    Pat N M t₀ i j = atPoint t₀ (pencil N M i j) := rfl

/-- The value of the pencil at `t₀` is the member `N + t₀ M`. -/
@[simp] theorem matC_Pat (N M : Matrix (Fin n) (Fin n) K) (t₀ : K) :
    matC (Pat N M t₀) = N + t₀ • M := by
  ext i j
  show PowerSeries.constantCoeff (atPoint t₀ (pencil N M i j)) = _
  rw [constantCoeff_atPoint]
  simp [pencil, mu, nu, Matrix.add_apply, mul_comm]

/-- The chart at infinity of the pencil `(N, M)` is the chart at `0` of the
swapped pencil `(M, N)`: both are the family `M + uN`.  This is the only
relation between the two charts that is needed, and it lets the local theory at
infinity be read off from the finite theory at `t₀ = 0`. -/
theorem PatInf_eq_Pat_zero (N M : Matrix (Fin n) (Fin n) K) :
    PatInf N M = Pat M N 0 := by
  refine Matrix.ext fun i j => ?_
  show atInf (pencil N M i j) = atPoint 0 (pencil M N i j)
  simp only [pencil, Matrix.of_apply, map_add, map_mul, atInf_mu, atInf_nu, atInf_C,
    atPoint_mu, atPoint_nu, atPoint_C, map_zero, zero_add, mul_one]
  ring

/-- `∂_u P = M`. -/
@[simp] theorem matD_Pat (N M : Matrix (Fin n) (Fin n) K) (t₀ : K) :
    matD (Pat N M t₀) = M := by
  ext i j
  show PowerSeries.coeff 1 (atPoint t₀ (pencil N M i j)) = _
  simp [pencil, mu, nu, atPoint]

/-- `Pat` is affine in the uniformizer: `P = (N + t₀M) + u · M`.  This is why
`dPat M` deserves the name `∂_u P`. -/
theorem Pat_eq_add_smul (N M : Matrix (Fin n) (Fin n) K) (t₀ : K) :
    Pat N M t₀ = (N + t₀ • M).map (PowerSeries.C : K →+* PowerSeries K) + (PowerSeries.X : PowerSeries K) • dPat M := by
  refine Matrix.ext fun i j => ?_
  show atPoint t₀ (pencil N M i j) = _
  simp only [Matrix.add_apply, Matrix.map_apply, Matrix.smul_apply, dPat_apply,
    smul_eq_mul, pencil, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  rw [map_add, map_mul, map_mul, atPoint_mu, atPoint_nu, atPoint_C, atPoint_C, map_add,
    map_mul]
  ring

/-- The value of a pencil direction `Q = μ Ṅ + ν Ṁ` at `t₀` is `Ṅ + t₀ Ṁ`. -/
@[simp] theorem matC_Qat_pencil (Nd Md : Matrix (Fin n) (Fin n) K) (t₀ : K) :
    matC (Qat (pencil Nd Md) t₀) = Nd + t₀ • Md :=
  matC_Pat Nd Md t₀

/-! ### Nilpotence transports to the chart -/

theorem Pat_pow (N M : Matrix (Fin n) (Fin n) K) (t₀ : K) (k : ℕ) :
    Pat N M t₀ ^ k = (pencil N M ^ k).map (atPoint t₀) := by
  induction k with
  | zero => ext i j; by_cases h : i = j <;> simp [Pat, h]
  | succ k ih => rw [pow_succ, ih, pow_succ, Matrix.map_mul]; rfl

theorem Pat_pow_eq_zero (N M : Matrix (Fin n) (Fin n) K) (t₀ : K) (k : ℕ)
    (h : pencil N M ^ k = 0) : Pat N M t₀ ^ k = 0 := by
  rw [Pat_pow, h]
  ext i j
  simp

end Height.Pencil
