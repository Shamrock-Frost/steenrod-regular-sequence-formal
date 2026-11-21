
import Height.Orbital.Saturation
import Height.Orbital.TangentSweep

/-!
# `prop:transporter` in arc form

Assembling the results of `Strata.lean`, `Arcs.lean` and `Saturation.lean`
with the algebraic transporter step
(`tangent_pair_isotropic_at_boxColumn`, in its representative form) gives
`prop:transporter` of the paper in the following form:

> for every `n`, every column sequence `T`, every `x ∈ A_T` and every arc `x_s`
> in `A_T` through `x`, the velocity `ẋ` lies in `[gl_n, x]`; and for two such
> velocities `ẋ₁ = [α₁, x]`, `ẋ₂ = [α₂, x]` one has `ω_x(α₁, α₂) = 0`.

The induction is on `n`.  At the inductive step the restricted arcs supply
`γ₁, γ₂` with `restrict ẋᵢ = [γᵢ, y]` and `ω_y(γ₁, γ₂) = 0`;
`exists_lift_of_arc` supplies the lifts `u_s`;
`tangent_equation_arc` turns the lifting equation into the constant and
linear coefficient equations; and the centralizer-sweep step corrects
`γᵢ` to a full block transporter without changing the pairing.
-/

namespace Height.Orbital

open Matrix
open Height.Toolbox

universe u

section Transporter

variable {K : Type u} [Field K]

/-- The base-point and derivative equations of `prop:transporter` (b), read
off an arc in `A_T` on `Fin (n+1)`: the lift `u_s` of `exists_lift_of_arc`
and the two coefficient equations of `tangent_equation_arc`, in the exact form
consumed by
`tangent_pair_isotropic_at_boxColumn`. -/
private theorem exists_tangent_data {n : ℕ} {T : Fin (n + 1) → ℕ}
    {x : Matrix (Fin (n + 1)) (Fin (n + 1)) K} (a : ArcIn T x) :
    ∃ u du : Fin n → K,
      ((restrict x) ^ T (Fin.last n)) *ᵥ u =
          ((restrict x) ^ (T (Fin.last n) - 1)) *ᵥ lastCol x ∧
        Isotropy.dpow (restrict x) (restrict a.vel) (T (Fin.last n) - 1) *ᵥ lastCol x +
              ((restrict x) ^ (T (Fin.last n) - 1)) *ᵥ lastCol a.vel =
            Isotropy.dpow (restrict x) (restrict a.vel) (T (Fin.last n)) *ᵥ u +
              ((restrict x) ^ T (Fin.last n)) *ᵥ du := by
  have hY : matC (restrict a.mat) = restrict x :=
    congrArg (fun M : Matrix (Fin (n + 1)) (Fin (n + 1)) K => restrict M) a.base_eq
  have hv : vecC (lastCol a.mat) = lastCol x :=
    congrArg (fun M : Matrix (Fin (n + 1)) (Fin (n + 1)) K => lastCol M) a.base_eq
  have hcpos : 1 ≤ T (Fin.last n) := one_le_of_inStratum a.base_mem (Fin.last n)
  have hnil : IsNilpotent (Matrix.toLinAlgEquiv' (restrict a.gen)) :=
    strictlyUpper_isNilpotent (isStrictlyUpper_restrict a.gen_mem.upper)
  have hmem : lastCol a.gen ∈
      kernelRange (Matrix.toLinAlgEquiv' (restrict a.gen)) (T (Fin.last n)) := by
    rw [chainCol_last a.gen_mem hnil]
    exact (boxColumn_spec _ _ hnil).2
  obtain ⟨u, hu⟩ := exists_lift_of_arc (restrict a.mat) (lastCol a.mat)
    (T ∘ Fin.castSucc) (T (Fin.last n)) hcpos
    (by rw [hY]; exact inStratum_restrict a.base_mem)
    (inStratum_restrict a.gen_mem) hmem
  obtain ⟨h1, h2⟩ := tangent_equation_arc (restrict a.mat) u (lastCol a.mat)
    (T (Fin.last n)) hu
  rw [hY, hv] at h1 h2
  exact ⟨vecC u, vecD u, h1, h2⟩

/-- The two statements of `prop:transporter` proved together, by induction on
`n`: two arcs in the same chain stratum through the same point have velocities
represented by commutators whose Kostant--Kirillov pairing vanishes. -/
private theorem transporter_arc_aux (K : Type u) [Field K] :
    ∀ (n : ℕ) (T : Fin n → ℕ) (x : Matrix (Fin n) (Fin n) K) (a₁ a₂ : ArcIn T x),
      ∃ α₁ α₂ : Matrix (Fin n) (Fin n) K,
        a₁.vel = α₁ * x - x * α₁ ∧ a₂.vel = α₂ * x - x * α₂ ∧ kkForm x α₁ α₂ = 0 := by
  intro n
  induction n with
  | zero =>
      intro T x a₁ a₂
      refine ⟨0, 0, Subsingleton.elim _ _, Subsingleton.elim _ _, ?_⟩
      exact kk_alt x 0
  | succ n ih =>
      intro T x a₁ a₂
      have hx : IsStrictlyUpper x := a₁.base_mem.upper
      have hyn : IsNilpotent (Matrix.toLinAlgEquiv' (restrict x)) :=
        strictlyUpper_isNilpotent (isStrictlyUpper_restrict hx)
      have hc : T (Fin.last n) =
          boxColumn (Matrix.toLinAlgEquiv' (restrict x)) (lastCol x) hyn :=
        chainCol_last a₁.base_mem hyn
      obtain ⟨γ₁, γ₂, hγ₁, hγ₂, hlower⟩ :=
        ih (T ∘ Fin.castSucc) (restrict x) a₁.restrict a₂.restrict
      obtain ⟨u₁, du₁, hbase₁, htangent₁⟩ := exists_tangent_data a₁
      obtain ⟨u₂, du₂, hbase₂, htangent₂⟩ := exists_tangent_data a₂
      obtain ⟨ζ₁, ζ₂, z₁, z₂, -, -, hfull₁, hfull₂, hiso⟩ :=
        tangent_pair_isotropic_at_boxColumn (restrict x)
          (restrict a₁.vel) (restrict a₂.vel) γ₁ γ₂
          u₁ du₁ u₂ du₂ (lastCol x) (lastCol a₁.vel) (lastCol a₂.vel)
          (T (Fin.last n)) hyn hc hγ₁ hγ₂ hbase₁ hbase₂ htangent₁ htangent₂ hlower
      have hxeq : x = standardBlockMatrix (blockExtension (restrict x) (lastCol x)) :=
        eq_standardBlockMatrix hx
      have key₁ : standardBlockMatrix (blockTransporter (γ₁ + ζ₁) z₁) *
            standardBlockMatrix (blockExtension (restrict x) (lastCol x)) -
          standardBlockMatrix (blockExtension (restrict x) (lastCol x)) *
            standardBlockMatrix (blockTransporter (γ₁ + ζ₁) z₁) =
          standardBlockMatrix (Matrix.fromBlocks (restrict a₁.vel)
            (lastColumn (lastCol a₁.vel)) 0 0) := by
        simpa only [standardBlockMatrix, map_mul, map_sub] using
          congrArg (Matrix.reindexAlgEquiv K K (blockIndexEquiv n)) hfull₁
      have key₂ : standardBlockMatrix (blockTransporter (γ₂ + ζ₂) z₂) *
            standardBlockMatrix (blockExtension (restrict x) (lastCol x)) -
          standardBlockMatrix (blockExtension (restrict x) (lastCol x)) *
            standardBlockMatrix (blockTransporter (γ₂ + ζ₂) z₂) =
          standardBlockMatrix (Matrix.fromBlocks (restrict a₂.vel)
            (lastColumn (lastCol a₂.vel)) 0 0) := by
        simpa only [standardBlockMatrix, map_mul, map_sub] using
          congrArg (Matrix.reindexAlgEquiv K K (blockIndexEquiv n)) hfull₂
      have hkk : kkForm (standardBlockMatrix (blockExtension (restrict x) (lastCol x)))
          (standardBlockMatrix (blockTransporter (γ₁ + ζ₁) z₁))
          (standardBlockMatrix (blockTransporter (γ₂ + ζ₂) z₂)) = 0 :=
        (kkForm_reindexAlgEquiv (blockIndexEquiv n) (blockExtension (restrict x) (lastCol x))
          (blockTransporter (γ₁ + ζ₁) z₁) (blockTransporter (γ₂ + ζ₂) z₂)).trans hiso
      refine ⟨standardBlockMatrix (blockTransporter (γ₁ + ζ₁) z₁),
        standardBlockMatrix (blockTransporter (γ₂ + ζ₂) z₂), ?_, ?_, ?_⟩
      · calc a₁.vel
            = standardBlockMatrix (blockExtension (restrict a₁.vel) (lastCol a₁.vel)) :=
              eq_standardBlockMatrix a₁.isStrictlyUpper_vel
          _ = standardBlockMatrix (blockTransporter (γ₁ + ζ₁) z₁) *
                standardBlockMatrix (blockExtension (restrict x) (lastCol x)) -
              standardBlockMatrix (blockExtension (restrict x) (lastCol x)) *
                standardBlockMatrix (blockTransporter (γ₁ + ζ₁) z₁) := key₁.symm
          _ = standardBlockMatrix (blockTransporter (γ₁ + ζ₁) z₁) * x -
              x * standardBlockMatrix (blockTransporter (γ₁ + ζ₁) z₁) := by rw [← hxeq]
      · calc a₂.vel
            = standardBlockMatrix (blockExtension (restrict a₂.vel) (lastCol a₂.vel)) :=
              eq_standardBlockMatrix a₂.isStrictlyUpper_vel
          _ = standardBlockMatrix (blockTransporter (γ₂ + ζ₂) z₂) *
                standardBlockMatrix (blockExtension (restrict x) (lastCol x)) -
              standardBlockMatrix (blockExtension (restrict x) (lastCol x)) *
                standardBlockMatrix (blockTransporter (γ₂ + ζ₂) z₂) := key₂.symm
          _ = standardBlockMatrix (blockTransporter (γ₂ + ζ₂) z₂) * x -
              x * standardBlockMatrix (blockTransporter (γ₂ + ζ₂) z₂) := by rw [← hxeq]
      · rw [hxeq]
        exact hkk

/-- `prop:transporter` (a) and (b) in arc form: the velocity of an arc in a
chain stratum is a commutator. -/
theorem transporter_arc {n : ℕ} (T : Fin n → ℕ) (x : Matrix (Fin n) (Fin n) K)
    (a : ArcIn T x) : ∃ α : Matrix (Fin n) (Fin n) K, a.vel = α * x - x * α := by
  obtain ⟨α, -, hα, -, -⟩ := transporter_arc_aux K n T x a a
  exact ⟨α, hα⟩

/-- `prop:transporter` (c) in arc form: the Kostant--Kirillov form vanishes on
the velocities of arcs in a chain stratum.  The statement is well posed
because `kkForm x α β` depends only on the two commutators
(`Height.Orbital.kk_wellDefined`). -/
theorem transporter_arc_isotropic {n : ℕ} (T : Fin n → ℕ) (x : Matrix (Fin n) (Fin n) K)
    (a₁ a₂ : ArcIn T x) (α₁ α₂ : Matrix (Fin n) (Fin n) K)
    (h₁ : a₁.vel = α₁ * x - x * α₁) (h₂ : a₂.vel = α₂ * x - x * α₂) :
    kkForm x α₁ α₂ = 0 := by
  obtain ⟨β₁, β₂, hβ₁, hβ₂, hiso⟩ := transporter_arc_aux K n T x a₁ a₂
  rw [kk_wellDefined (x := x) (α := α₁) (α' := β₁) (β := α₂) (β' := β₂)
    (by rw [← h₁, ← hβ₁]) (by rw [← h₂, ← hβ₂])]
  exact hiso

end Transporter

end Height.Orbital
