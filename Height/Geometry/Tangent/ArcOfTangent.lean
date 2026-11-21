import Height.Geometry.Tangent.Newton
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Arcs in an irreducible zero locus at a tangent-generic point

Let `P` be a prime ideal of `K[x_ι]`, `Z` its zero locus, and `z ∈ Z` a point at
which some `f₁, …, f_c ∈ P` have an invertible `c × c` Jacobian minor.  Newton lifting
(`Height.Geometry.Tangent.exists_arc_of_jacobian_unit`) produces, for every
tangent vector `v` of `Z` at `z`, an arc through `z` with velocity `v` lying in
the *larger* variety `W = V(f₁, …, f_c)`.  The arc lies in `Z` as soon as
`W = Z` near `z`; the theorems here package that last implication.

The kernel of `aeval a : K[x_ι] → K⟦t⟧` is a prime ideal `Q` containing
`(f₁, …, f_c)` and contained in the maximal ideal of `z` (the arc passes through
`z`).  So the arc lies in `Z` iff `P ≤ Q`, and:

* `exists_arc_of_tangent_of_forall_prime` assumes exactly that every prime
  between `(f)` and the maximal ideal of `z` contains `P`;
* `exists_arc_of_tangent_of_locally_zero` assumes the concrete form of
  "`W = Z` near `z`": every `g ∈ P` is killed by `(f)` after inverting one
  function not vanishing at `z`, i.e. `P` maps to `0` in the local ring of `W`
  at `z`;
* `forall_prime_of_unique_minimal` derives the first hypothesis from `P` being
  the unique minimal prime of `(f)` at `z`.

## The hypothesis this file does not discharge

The three theorems above *assume* "`W = Z` near `z`", in three interchangeable
elementary forms; none of them proves it.  The two inputs of the usual argument
(the local ring of `W` at `z` is regular, hence a domain, hence `z` lies on a
single component of `W`, which must be `Z`) are supplied elsewhere in this
development:

* "a regular local ring is an integral domain" is
  `Height.Toolbox.isDomain_of_isRegularLocalRing`
  (`Toolbox/RegularLocalRing.lean`, with the induction at
  `isDomain_of_isRegularLocalRing_of_spanFinrank`).  It is proved there because
  the pinned mathlib does not have it: `Mathlib/RingTheory/RegularLocalRing/`
  contains only `Defs.lean` and `Polynomial.lean`, whose sole implication runs
  the other way (`[IsDomain R] [IsPrincipalIdealRing R] → IsRegularLocalRing R`).
* the dimension theory making that local ring regular of the right dimension is
  `Geometry/Dimension/` and `Geometry/Tangent/Generic.lean`.
-/

universe u v

open MvPolynomial

namespace Height.Geometry.Tangent

variable {K : Type u} [CommRing K] [IsDomain K] {ι : Type v} [Fintype ι]

/-! ### From an arc in `W` to an arc in `Z` -/

/-- **Prime form.**  If every prime ideal between `(f₁, …, f_c)` and the
maximal ideal of `z` contains `P`, then every tangent vector of the zero locus
of `P` at `z` is the velocity of an arc in that zero locus.

The hypothesis `hP` is the algebraic content of "`W = Z` near `z`". -/
theorem exists_arc_of_tangent_of_forall_prime {c : ℕ} (P : Ideal (MvPolynomial ι K))
    (f : Fin c → MvPolynomial ι K) (hfP : ∀ j, f j ∈ P) (z : ι → K)
    (S : Fin c ↪ ι)
    (hJ : IsUnit (Matrix.of fun j k =>
      MvPolynomial.eval z (MvPolynomial.pderiv (S k) (f j))).det)
    (hz : ∀ g ∈ P, MvPolynomial.eval z g = 0)
    (hP : ∀ Q : Ideal (MvPolynomial ι K), Q.IsPrime → Ideal.span (Set.range f) ≤ Q →
      (∀ s ∈ Q, MvPolynomial.eval z s = 0) → P ≤ Q)
    (v : ι → K)
    (hv : ∀ g ∈ P, ∑ i, MvPolynomial.eval z (MvPolynomial.pderiv i g) * v i = 0) :
    ∃ a : ι → PowerSeries K, (∀ i, PowerSeries.constantCoeff (a i) = z i) ∧
      (∀ i, PowerSeries.coeff 1 (a i) = v i) ∧ ∀ g ∈ P, MvPolynomial.aeval a g = 0 := by
  obtain ⟨a, ha0, ha1, haf⟩ :=
    exists_arc_of_jacobian_unit f z (fun j => hz _ (hfP j)) S hJ v (fun j => hv _ (hfP j))
  refine ⟨a, ha0, ha1, fun g hg => ?_⟩
  set Q : Ideal (MvPolynomial ι K) :=
    RingHom.ker (aeval a : MvPolynomial ι K →ₐ[K] PowerSeries K) with hQdef
  have hQ : Q.IsPrime := RingHom.ker_isPrime _
  have hfQ : Ideal.span (Set.range f) ≤ Q := by
    rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    exact RingHom.mem_ker.2 (haf j)
  have hzQ : ∀ s ∈ Q, MvPolynomial.eval z s = 0 := by
    intro s hs
    have hs0 : aeval a s = 0 := RingHom.mem_ker.1 hs
    have hc := congrArg (PowerSeries.constantCoeff (R := K)) hs0
    rw [constantCoeff_aeval, map_zero] at hc
    rwa [funext ha0] at hc
  exact RingHom.mem_ker.1 (hP Q hQ hfQ hzQ hg)

/-- **Local form.**  "`W = Z` near `z`" in its concrete shape: every element
of `P` is annihilated by `(f₁, …, f_c)` after inverting a single function not
vanishing at `z`.  Equivalently `P` maps to `0` in the local ring of `W` at
`z`. -/
theorem exists_arc_of_tangent_of_locally_zero {c : ℕ} (P : Ideal (MvPolynomial ι K))
    (f : Fin c → MvPolynomial ι K) (hfP : ∀ j, f j ∈ P) (z : ι → K)
    (S : Fin c ↪ ι)
    (hJ : IsUnit (Matrix.of fun j k =>
      MvPolynomial.eval z (MvPolynomial.pderiv (S k) (f j))).det)
    (hz : ∀ g ∈ P, MvPolynomial.eval z g = 0)
    (hloc : ∀ g ∈ P, ∃ s : MvPolynomial ι K, MvPolynomial.eval z s ≠ 0 ∧
      s * g ∈ Ideal.span (Set.range f))
    (v : ι → K)
    (hv : ∀ g ∈ P, ∑ i, MvPolynomial.eval z (MvPolynomial.pderiv i g) * v i = 0) :
    ∃ a : ι → PowerSeries K, (∀ i, PowerSeries.constantCoeff (a i) = z i) ∧
      (∀ i, PowerSeries.coeff 1 (a i) = v i) ∧ ∀ g ∈ P, MvPolynomial.aeval a g = 0 :=
  exists_arc_of_tangent_of_forall_prime P f hfP z S hJ hz
    (fun Q hQ hfQ hzQ g hg => by
      obtain ⟨s, hs, hsg⟩ := hloc g hg
      have hsQ : s ∉ Q := fun h => hs (hzQ s h)
      exact (hQ.mem_or_mem (hfQ hsg)).resolve_left hsQ)
    v hv

/-! ### The minimal-prime form of the hypothesis -/

variable {R : Type*} [CommRing R]

/-- If `P` is the *only* minimal prime over `I` contained in `m`, then every
prime between `I` and `m` contains `P`.  This is the hypothesis `hP` of
`exists_arc_of_tangent_of_forall_prime` in the shape "`z` lies on a single
irreducible component of `W`, namely `Z`"; minimality of `P` itself is not
needed as a separate hypothesis, since `huniq` forces it. -/
theorem forall_prime_of_unique_minimal (I m P : Ideal R)
    (huniq : ∀ Q ∈ I.minimalPrimes, Q ≤ m → Q = P) (Q : Ideal R) (hQ : Q.IsPrime)
    (hIQ : I ≤ Q) (hQm : Q ≤ m) : P ≤ Q := by
  have := hQ
  obtain ⟨Q₀, hQ₀min, hQ₀le⟩ := Ideal.exists_minimalPrimes_le hIQ
  rw [← huniq Q₀ hQ₀min (hQ₀le.trans hQm)]
  exact hQ₀le

end Height.Geometry.Tangent
