import Height.Orbital.KK
import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Reindexing the Kostant--Kirillov form

Simultaneously reindexing rows and columns preserves the trace and hence the
representative Kostant--Kirillov form.  The block transporter uses the index
type `Fin n ⊕ Unit`; `blockIndexEquiv` gives its standard identification with
`Fin (n+1)` for the intrinsic tangent-space API.
-/

namespace Height.Orbital

open Matrix

universe u v w

variable {K : Type u} [Field K]
variable {m : Type v} {n : Type w}
variable [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- Matrix trace is unchanged by simultaneous row and column reindexing. -/
theorem trace_reindexAlgEquiv (e : m ≃ n) (A : Matrix m m K) :
    Matrix.trace (Matrix.reindexAlgEquiv K K e A) = Matrix.trace A := by
  simp only [Matrix.trace, Matrix.reindex_apply, Matrix.coe_reindexAlgEquiv]
  exact e.symm.sum_comp fun i => A i i

/-- Simultaneous reindexing preserves the Kostant--Kirillov representative
pairing. -/
theorem kkForm_reindexAlgEquiv (e : m ≃ n)
    (x A B : Matrix m m K) :
    kkForm (Matrix.reindexAlgEquiv K K e x)
        (Matrix.reindexAlgEquiv K K e A)
        (Matrix.reindexAlgEquiv K K e B) =
      kkForm x A B := by
  simp only [kkForm, ← map_mul, ← map_sub]
  exact trace_reindexAlgEquiv e (x * (A * B - B * A))

/-- Standardly identify the index type of an upper-left block plus one final
coordinate with `Fin (n+1)`. -/
def blockIndexEquiv (n : ℕ) : (Fin n ⊕ Unit) ≃ Fin (n + 1) :=
  (Equiv.sumCongr (Equiv.refl (Fin n)) finOneEquiv.symm).trans
    finSumFinEquiv

end Height.Orbital
