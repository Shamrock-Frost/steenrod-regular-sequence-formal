import Mathlib.RingTheory.CohenMacaulay.Unmixed
import Mathlib.RingTheory.Regular.IsSMulRegular
import Height.Geometry.DimensionFormula

/-!
# The prefix-height criterion for a regular sequence

In a Noetherian Cohen-Macaulay ring, a list `rs` whose every prefix generates an
ideal of height exactly the length of that prefix is a regular sequence
(`isRegular_of_height_take`).  The proof is the unmixedness characterisation of
Cohen-Macaulay rings (`isCohenMacaulayRing_iff_unmixed`): the zero divisors on
`R ⧸ J_i` are the union of the associated primes of `J_i`, all of height `i` by
unmixedness; if `rs[i]` were one of them it would lie in a prime `p ⊇ J_i` of
height `i`, whence `ht J_{i+1} ≤ i`, contradicting `ht J_{i+1} = i + 1`.

The prefix hypothesis is strictly stronger than "the span of `rs` has height
`rs.length`", and the weaker form does not suffice.  For the *homogeneous*
generators this development actually uses, the prefix heights follow from the
height of the whole ideal, by localising at the irrelevant maximal ideal:
`isRegular_of_height_eq_length_of_isHomogeneous` in
`Geometry/HomogeneousHeight.lean`, which is what `Chain/Boxes.lean` consumes.
-/

universe u v

namespace Height.Geometry

open RingTheory.Sequence MvPolynomial

/-- In a Noetherian Cohen–Macaulay ring, a list whose every prefix generates an
ideal of height exactly the length of that prefix is a regular sequence.

The hypothesis for the full list alone does *not* suffice. -/
theorem isRegular_of_height_take {R : Type u} [CommRing R] [IsNoetherianRing R]
    [IsCohenMacaulayRing R] (rs : List R)
    (h : ∀ i ≤ rs.length, (Ideal.ofList (rs.take i)).height = (i : ℕ∞)) :
    IsRegular R rs := by
  have unmix := isCohenMacaulayRing_iff_unmixed.mp ‹IsCohenMacaulayRing R›
  have hne : Ideal.ofList rs ≠ ⊤ := by
    intro htop
    have h1 := h rs.length le_rfl
    rw [List.take_of_length_le le_rfl, htop, Ideal.height_top] at h1
    exact (ENat.natCast_ne_top rs.length) h1.symm
  refine ⟨⟨fun i hi => ?_⟩, ?_⟩
  · rw [Ideal.smul_eq_mul, Ideal.mul_top]
    by_contra hreg
    have hmem : rs[i] ∈ ⋃ p ∈ associatedPrimes R (R ⧸ Ideal.ofList (rs.take i)), (p : Set R) := by
      rw [biUnion_associatedPrimes_eq_compl_regular R (R ⧸ Ideal.ofList (rs.take i))]
      exact hreg
    obtain ⟨p, hp, hrp⟩ := Set.mem_iUnion₂.mp hmem
    have hlen : (rs.take i).length = i := by
      simp [List.length_take, le_of_lt hi]
    have hti : (Ideal.ofList (rs.take i)).height = ((rs.take i).length : ℕ∞) := by
      rw [hlen]; exact h i (le_of_lt hi)
    have hph : p.height = (Ideal.ofList (rs.take i)).height := unmix (rs.take i) hti hp
    have hle : Ideal.ofList (rs.take i) ≤ p := by
      have hann := hp.annihilator_le
      rwa [Submodule.annihilator_top, Ideal.annihilator_quotient] at hann
    have hle2 : Ideal.ofList (rs.take (i + 1)) ≤ p := by
      rw [Ideal.span_le]
      intro x hx
      simp only [Set.mem_ofPred_eq] at hx
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hx
      rw [List.length_take] at hj
      rw [List.getElem_take]
      rcases Nat.lt_succ_iff_lt_or_eq.mp (lt_of_lt_of_le hj (min_le_left _ _)) with hlt | rfl
      · exact hle (Ideal.subset_span (by
          simp only [Set.mem_ofPred_eq]
          exact List.mem_iff_getElem.mpr ⟨j, by simpa [List.length_take, hlen] using hlt,
            by rw [List.getElem_take]⟩))
      · exact hrp
    have hmono := Ideal.height_mono hle2
    rw [h (i + 1) hi, hph, hti, hlen] at hmono
    exact absurd hmono (by exact_mod_cast Nat.not_succ_le_self i)
  · rw [Ideal.smul_eq_mul, Ideal.mul_top]
    exact fun e => hne e.symm

end Height.Geometry
