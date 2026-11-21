import Height.Pencil.Commutator
import Height.Toolbox.Parabolic

/-!
# `lem:parabolic-field`: the parabolic attached to a nilpotent kernel flag

The paper, `lem:parabolic-field`.  Let `L` be a
field, `P ∈ gl_n(L)` with `P ^ n = 0`, and `V k := ker (P ^ k)` the kernel
flag.  Put

* `parab P  := { φ | φ (V k) ⊆ V k       for all k }` — the parabolic;
* `nilrad P := { φ | φ (V (k+1)) ⊆ V k   for all k }` — its nilradical.

Then

* (i)   `[P, A] ∈ nilrad P ↔ A ∈ parab P`   (`commutator_mem_nilrad_iff`);
* (ii)  `ad_P (parab P) = nilrad P` (`nilrad_eq_image`).  The paper's
        other half of (ii), `Z(P) ⊆ parab P`, is not needed downstream and is
        not stated here; it follows from (i) with `A ∈ Z(P)`;
* (iii) `trace (parab P · nilrad P) = 0`    (`trace_parab_nilrad`).

(ii b) is obtained **without the dimension count** of the paper: for
`U ∈ nilrad P` the derivative `Dk P U k` annihilates `V k` outright
(`Dk_mulVec_eq_zero_of_mem_nilrad`), so `Commutator.isCommutator_of_kernelFlat`
(`lem:field-commutator`) produces `A` with `U = [P, A]` and (i) puts `A` in
`parab P`.

The set-level content is `Height.Toolbox.parabolic_field`; this
file bundles `parab` and `nilrad` as `Submodule`s and states the items above
on them.
-/

namespace Height.Pencil

open Matrix

variable {L : Type*} [Field L] {n : ℕ}

/-- `Toolbox.flagHom S T` is a submodule: closure under `0`, `+` and `•` is a property of
the target flag `T` alone, so the parabolic and its nilradical share it.

Bundled here rather than in `Toolbox`: the set-level predicate is general, this
`Submodule` is what the four items below are stated on, and there is no third
consumer to justify a layer between them. -/
def flagHomSubmodule (S T : ℕ → Submodule L (Fin n → L)) :
    Submodule L (Matrix (Fin n) (Fin n) L) where
  carrier := Height.Toolbox.flagHom S T
  zero_mem' := by
    intro k v hv
    simp
  add_mem' := by
    intro A B hA hB k v hv
    rw [add_mulVec]
    exact (T k).add_mem (hA k v hv) (hB k v hv)
  smul_mem' := by
    intro a A hA k v hv
    rw [smul_mulVec]
    exact (T k).smul_mem a (hA k v hv)

/-- The parabolic of the kernel flag of `P`: the matrices preserving every
`V k = ker (P ^ k)`. -/
def parab (P : Matrix (Fin n) (Fin n) L) : Submodule L (Matrix (Fin n) (Fin n) L) :=
  flagHomSubmodule (Isotropy.kerFlag P) (Isotropy.kerFlag P)

/-- The nilradical of the kernel flag of `P`: the matrices carrying
`V (k+1) = ker (P ^ (k+1))` into `V k = ker (P ^ k)`. -/
def nilrad (P : Matrix (Fin n) (Fin n) L) : Submodule L (Matrix (Fin n) (Fin n) L) :=
  flagHomSubmodule (fun k => Isotropy.kerFlag P (k + 1)) (Isotropy.kerFlag P)

/-- `lem:parabolic-field`(i): `[P, A]` lowers the kernel flag exactly when
`A` preserves it. -/
theorem commutator_mem_nilrad_iff (P A : Matrix (Fin n) (Fin n) L) :
    (P * A - A * P) ∈ nilrad P ↔ A ∈ parab P :=
  ⟨Height.Toolbox.mem_parabolic_of_adMatrix_mem_nilradical P A,
    Height.Toolbox.adMatrix_mem_nilradical_of_mem_parabolic P A⟩

/-- For `U` in the nilradical, every term `P^j U P^(k-1-j)` of `Dk P U k`
already annihilates `V k = ker (P ^ k)`: `P^(k-1-j) v ∈ V (j+1)`, `U` lowers
it into `V j`, and `P ^ j` kills `V j`.  This is the kernel-flatness input
that turns `lem:field-commutator` into `lem:parabolic-field`(ii b), with no
dimension count. -/
theorem Dk_mulVec_eq_zero_of_mem_nilrad {P U : Matrix (Fin n) (Fin n) L}
    (hU : U ∈ nilrad P) (k : ℕ) (v : Fin n → L)
    (hv : v ∈ LinearMap.ker ((P ^ k).mulVecLin)) :
    (Dk P U k).mulVec v = 0 := by
  rw [Dk, Matrix.sum_mulVec]
  refine Finset.sum_eq_zero fun j hj => ?_
  have hjk : j < k := Finset.mem_range.mp hj
  -- `P ^ (k - 1 - j) v ∈ V (j + 1)`
  have hstep : (P ^ (k - 1 - j)).mulVec v ∈ Isotropy.kerFlag P (j + 1) := by
    rw [Isotropy.mem_kerFlag, Matrix.mulVec_mulVec, ← pow_add,
      show j + 1 + (k - 1 - j) = k by omega]
    exact hv
  -- `U` lowers it into `V j`, and `P ^ j` kills `V j`
  have hU' : U.mulVec ((P ^ (k - 1 - j)).mulVec v) ∈ Isotropy.kerFlag P j :=
    hU j _ hstep
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  exact Isotropy.mem_kerFlag.mp hU'

/-- `lem:parabolic-field`(ii b): every matrix lowering the kernel flag is
`[P, A]` for some `A` in the parabolic. -/
theorem nilrad_eq_image (P : Matrix (Fin n) (Fin n) L) (hP : P ^ n = 0) :
    ∀ U ∈ nilrad P, ∃ A ∈ parab P, U = P * A - A * P := by
  intro U hU
  obtain ⟨A, hA⟩ := isCommutator_of_kernelFlat P hP U fun k v hv => by
    rw [Dk_mulVec_eq_zero_of_mem_nilrad hU k v hv]
    exact Submodule.zero_mem _
  exact ⟨A, (commutator_mem_nilrad_iff P A).mp (hA ▸ hU), hA⟩

/-- `lem:parabolic-field`(iii): the parabolic and its nilradical are
trace-orthogonal, since `φ ψ` lowers an exhaustive flag and is therefore
nilpotent. -/
theorem trace_parab_nilrad (P : Matrix (Fin n) (Fin n) L) (hP : P ^ n = 0) :
    ∀ φ ∈ parab P, ∀ ψ ∈ nilrad P, trace (φ * ψ) = 0 :=
  fun φ hφ ψ hψ => (Height.Toolbox.parabolic_field P hP).2.2.2 φ hφ ψ hψ

end Height.Pencil
