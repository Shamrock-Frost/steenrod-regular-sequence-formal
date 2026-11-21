import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Steenrod powers on a polynomial algebra over a finite field

For a prime `p`, a positive integer `n`, and `q = p ^ n`, the coefficient field is
mathlib's `GaloisField p n`.  If `ι` is a finite type, the polynomial algebra is
`MvPolynomial ι (GaloisField p n)`.

The total `q`-Steenrod power is the algebra homomorphism

`𝒫(T) : f(x) ↦ f(x + x^q T)`.

The operation `P i` is the coefficient of `T^i` in `𝒫(T)`.  In particular,
`P 0 x = x`, `P 1 x = x^q`, and `P i x = 0` for `i ≥ 2` on every polynomial
generator `x`.
-/

open Polynomial

namespace QSteenrod

universe u

variable (p n : ℕ) [Fact p.Prime]

/-- The cardinality parameter `q = p ^ n`. -/
abbrev q : ℕ := p ^ n

/-- The coefficient field has the advertised prime-power cardinality.

`NeZero n` is needed only here: the operations below make sense without carrying
that proof, which is why it is a hypothesis of this theorem rather than of the
definitions. -/
theorem card_galoisField [NeZero n] : Nat.card (GaloisField p n) = q p n :=
  GaloisField.card p n (NeZero.ne n)

section

variable {ι : Type u}

/-- The polynomial algebra over `GaloisField p n` on the variables `ι`.

For the requested finite set of indeterminates, instantiate this with a type
`ι` carrying a `Fintype ι` instance.  The construction itself does not need
finiteness, so it is stated in the more general form.
-/
abbrev PolynomialAlgebra := MvPolynomial ι (GaloisField p n)

/-- The image of a polynomial generator under the total `q`-Steenrod power. -/
noncomputable def totalGenerator (x : ι) : Polynomial (PolynomialAlgebra p n (ι := ι)) :=
  C (MvPolynomial.X x) + monomial 1 (MvPolynomial.X x ^ q p n)

/-- The total `q`-Steenrod power, characterized by
`x ↦ x + x^q T` on polynomial generators. -/
noncomputable def total :
    PolynomialAlgebra p n (ι := ι) →ₐ[GaloisField p n] Polynomial (PolynomialAlgebra p n (ι := ι)) :=
  MvPolynomial.aeval (totalGenerator (ι := ι) p n)

/-- The `i`th `q`-Steenrod power: the coefficient of `T^i` in `total f`.

Each operation is packaged as an `GaloisField p n`-linear map.  The individual
operations are not ring homomorphisms; multiplication is governed by the
Cartan formula.
-/
noncomputable def P (i : ℕ) :
    PolynomialAlgebra p n (ι := ι) →ₗ[GaloisField p n] PolynomialAlgebra p n (ι := ι) :=
  (Polynomial.lcoeff (PolynomialAlgebra p n (ι := ι)) i).restrictScalars (GaloisField p n) ∘ₗ
    (total (ι := ι) p n).toLinearMap

@[simp]
theorem total_X (x : ι) :
    total (ι := ι) p n (MvPolynomial.X x) = totalGenerator p n x := by
  simp [total]

@[simp]
theorem P_apply (i : ℕ) (f : PolynomialAlgebra p n (ι := ι)) :
    P (ι := ι) p n i f = (total (ι := ι) p n f).coeff i := by
  rfl

end

end QSteenrod
