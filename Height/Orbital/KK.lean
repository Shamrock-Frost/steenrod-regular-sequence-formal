import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# The Kostant--Kirillov trace form

The results here are the purely algebraic identities `kk_wellDefined` and
`kk_alt`.  They hold over every commutative ring.
-/

namespace Height.Orbital

open Matrix

variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]

/-- The representative-level formula for the Kostant--Kirillov form. -/
def kkForm (x α β : Matrix n n R) : R :=
  trace (x * (α * β - β * α))

omit [DecidableEq n] in
/-- The trace identity used to see dependence on the first commutator. -/
theorem kk_eq_neg_trace (x α β : Matrix n n R) :
    kkForm x α β = -trace ((α * x - x * α) * β) := by
  rw [kkForm, mul_sub, trace_sub, sub_mul, trace_sub, neg_sub]
  simp only [mul_assoc]
  congr 1
  rw [← mul_assoc, trace_mul_comm]

omit [DecidableEq n] in
/-- The symmetric companion identity, exposing dependence on the second
commutator. -/
theorem kk_eq_trace (x α β : Matrix n n R) :
    kkForm x α β = trace ((β * x - x * β) * α) := by
  rw [kkForm, mul_sub, trace_sub, sub_mul, trace_sub]
  simp only [mul_assoc]
  congr 1
  rw [← mul_assoc, trace_mul_comm]

omit [DecidableEq n] in
/-- `subsec:kk`: the representative formula depends only on the two tangent
commutators `[α,x]` and `[β,x]`. -/
theorem kk_wellDefined {x α α' β β' : Matrix n n R}
    (hα : α * x - x * α = α' * x - x * α')
    (hβ : β * x - x * β = β' * x - x * β') :
    kkForm x α β = kkForm x α' β' := by
  calc
    kkForm x α β = -trace ((α * x - x * α) * β) := kk_eq_neg_trace _ _ _
    _ = -trace ((α' * x - x * α') * β) := by rw [hα]
    _ = kkForm x α' β := (kk_eq_neg_trace _ _ _).symm
    _ = trace ((β * x - x * β) * α') := kk_eq_trace _ _ _
    _ = trace ((β' * x - x * β') * α') := by rw [hβ]
    _ = kkForm x α' β' := (kk_eq_trace _ _ _).symm

/-- `subsec:kk`: the Kostant--Kirillov form is alternating. -/
theorem kk_alt (x α : Matrix n n R) : kkForm x α α = 0 := by
  simp [kkForm]

end Height.Orbital
