import Mathlib.Tactic.NoncommRing
import Height.Toolbox.Parabolic
import Height.Orbital.KK

/-!
# Algebraic core of the flag-velocity calculation

The local-model lemma supplies decompositions and the shifted-evaluation lemma
supplies the residue value.  The remaining field-level trace calculation from
`lem:flag-velocity` is isolated here.
-/

namespace Height.Pencil

open Height.Toolbox

open Matrix

variable {K : Type*} [Field K] {n : ℕ}

/-- The trace expression obtained by evaluating a flag-velocity decomposition at
the drop point *is* the Kostant--Kirillov representative formula. -/
theorem trace_adMatrix_mul_eq_kkForm (N W₁ W₂ : Matrix (Fin n) (Fin n) K) :
    trace (adMatrix N W₁ * W₂) = Height.Orbital.kkForm N W₁ W₂ := by
  rw [Height.Orbital.kk_eq_neg_trace, adMatrix]
  rw [show N * W₁ - W₁ * N = -(W₁ * N - N * W₁) by noncomm_ring,
    neg_mul, trace_neg]

end Height.Pencil
