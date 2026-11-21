import Height.Pencil.Dk
import Isotropy.FieldLemma

/-!
# `lem:field-commutator`: kernel flatness characterizes commutators over a field

The paper, `lem:field-commutator`.  Let `L` be a
field, `P ∈ gl_n(L)` with `P ^ n = 0`, and `S k := ker (P ^ k) ⊆ L ^ n` the
kernel flag.  For `Q ∈ gl_n(L)`:

> `Q = [P, A]` for some `A` **iff** `Dk P Q k (S k) ⊆ P ^ k · L ^ n` for
> every `k`.

The mathematics is `Isotropy.commutator_iff_dcond` of
`Isotropy/FieldLemma.lean` (regular part, lowering, trace duality); the
kernel-flatness predicate there is `Isotropy.DCond`.  This file is the
pencil layer's statement of the hard direction in its own notation
(`Dk`, `LinearMap.ker`/`LinearMap.range` of `mulVecLin`, and the sign
convention `Q = P * A - A * P`).
-/

namespace Height.Pencil

open Matrix

variable {L : Type*} [Field L] {n : ℕ}

/-- The hard direction of `lem:field-commutator`: kernel flatness at every
level makes `Q` a commutator with `P`.  Proof: `Isotropy.commutator_iff_dcond`
(regular part, lowering, trace duality). -/
theorem isCommutator_of_kernelFlat (P : Matrix (Fin n) (Fin n) L) (hP : P ^ n = 0)
    (Q : Matrix (Fin n) (Fin n) L)
    (hQ : ∀ k, ∀ v ∈ LinearMap.ker ((P ^ k).mulVecLin),
      (Dk P Q k).mulVec v ∈ LinearMap.range ((P ^ k).mulVecLin)) :
    ∃ A, Q = P * A - A * P := by
  obtain ⟨A, hA⟩ := (Isotropy.commutator_iff_dcond P hP Q).mpr
    (fun k v hv => (hQ k v hv).imp fun _ hw => hw)
  exact ⟨A, hA.symm⟩

end Height.Pencil
