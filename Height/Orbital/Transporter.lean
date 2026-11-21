import Height.Orbital.KK
import Mathlib.Data.Matrix.Block

/-!
# The block transporter calculation

This file isolates the matrix algebra in parts (b) and (c) of
`prop:transporter`.  The arc-lifting and centralizer-sweep inputs live outside
this calculation.
-/

namespace Height.Orbital

open Matrix

universe u

variable {R : Type*} [CommRing R]
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- Regard a vector as the single last column of a block matrix. -/
def lastColumn (v : ι → R) : Matrix ι Unit R := fun i _ => v i

/-- The matrix `(y,v)` on `R^ι ⊕ R e`. -/
def blockExtension (y : Matrix ι ι R) (v : ι → R) :
    Matrix (ι ⊕ Unit) (ι ⊕ Unit) R :=
  fromBlocks y (lastColumn v) 0 0

/-- The block-upper-triangular transporter representative `(γ,w;0,0)`. -/
def blockTransporter (γ : Matrix ι ι R) (w : ι → R) :
    Matrix (ι ⊕ Unit) (ι ⊕ Unit) R :=
  fromBlocks γ (lastColumn w) 0 0

omit [DecidableEq ι] in
private theorem mul_lastColumn (A : Matrix ι ι R) (v : ι → R) :
    A * lastColumn v = lastColumn (A.mulVec v) := by
  ext i j
  rfl

omit [DecidableEq ι] in
/-- The equality displayed in part (b) of `prop:transporter`. -/
theorem transporter_commutator (y γ : Matrix ι ι R) (v w : ι → R) :
    blockTransporter γ w * blockExtension y v -
        blockExtension y v * blockTransporter γ w =
      fromBlocks (γ * y - y * γ)
        (lastColumn (γ.mulVec v - y.mulVec w)) 0 0 := by
  rw [blockTransporter, blockExtension, fromBlocks_multiply,
    fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero,
    mul_lastColumn]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.sub_apply, lastColumn]

omit [DecidableEq ι] in
private theorem trace_fromBlocks (A : Matrix ι ι R) (B : Matrix ι Unit R)
    (C : Matrix Unit ι R) (D : Matrix Unit Unit R) :
    trace (fromBlocks A B C D) = trace A + trace D := by
  simp [trace, Fintype.sum_sum_type]

omit [DecidableEq ι] in
/-- The last column does not contribute to the trace pairing in the induction
step of `prop:transporter`. -/
theorem transporter_trace (y γ γ' : Matrix ι ι R) (v w w' : ι → R) :
    trace
        ((blockTransporter γ w * blockExtension y v -
            blockExtension y v * blockTransporter γ w) *
          blockTransporter γ' w') =
      trace ((γ * y - y * γ) * γ') := by
  rw [transporter_commutator, blockTransporter, fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero]
  rw [trace_fromBlocks]
  simp

omit [DecidableEq ι] in
/-- The Kostant--Kirillov pairing of two block-transporter directions is
exactly the pairing of their upper-left representatives one dimension
lower. -/
theorem kkForm_blockExtension_transporters
    (y γ γ' : Matrix ι ι R) (v w w' : ι → R) :
    kkForm (blockExtension y v) (blockTransporter γ w)
        (blockTransporter γ' w') =
      kkForm y γ γ' := by
  rw [kk_eq_neg_trace, kk_eq_neg_trace, transporter_trace]

end Height.Orbital
