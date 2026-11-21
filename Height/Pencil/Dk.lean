
import Isotropy.DPow

/-!
# `D_k`, the derivative of `P ^ k`

Over any commutative ring,
`Dk P Q k = ∑_{j < k} P ^ j * Q * P ^ (k - 1 - j)`,
the derivative of `P ^ k` in the direction `Q`.  This is the pencil layer's
name for `Isotropy.dpow` of `Isotropy/DPow.lean`, with the same body, so the two
are definitionally equal; `Dk_sub` is proved by `Isotropy.dpow_sub`.  The
duplicate buys no isolation -- `Pencil/ArcsLocal.lean` and
`Pencil/FlagVelocityArc.lean` use `Isotropy.dpow` directly, beside `Dk` -- and is
kept only for the notation of the paper.

The identities are the chain rules of the display before
`lem:field-commutator` in the paper: `Dk` is
`Q`-linear, satisfies `D_{k+1} = P D_k + Q P^k` and its mirror
`D_{k+1} = D_k P + P^k Q`, and telescopes on commutators,
`D_k([P, A]) = P^k A - A P^k`.
-/

namespace Height.Pencil

open Matrix

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The derivative of `P ^ k` in the direction `Q`:
`D_k(Q) = ∑_{j < k} P^j Q P^{k-1-j}`. -/
def Dk (P Q : Matrix (Fin n) (Fin n) R) (k : ℕ) : Matrix (Fin n) (Fin n) R :=
  ∑ j ∈ Finset.range k, P ^ j * Q * P ^ (k - 1 - j)

/-- `Dk` is additive in the direction. -/
theorem Dk_add (P Q₁ Q₂ : Matrix (Fin n) (Fin n) R) (k : ℕ) :
    Dk P (Q₁ + Q₂) k = Dk P Q₁ k + Dk P Q₂ k := by
  simp only [Dk, ← Finset.sum_add_distrib, mul_add, add_mul]

/-- `Dk` is homogeneous in the direction. -/
theorem Dk_smul (P Q : Matrix (Fin n) (Fin n) R) (c : R) (k : ℕ) :
    Dk P (c • Q) k = c • Dk P Q k := by
  simp only [Dk, Finset.smul_sum, mul_smul_comm, smul_mul_assoc]

theorem Dk_sub (P Q₁ Q₂ : Matrix (Fin n) (Fin n) R) (k : ℕ) :
    Dk P (Q₁ - Q₂) k = Dk P Q₁ k - Dk P Q₂ k :=
  Isotropy.dpow_sub P Q₁ Q₂ k

end Height.Pencil
