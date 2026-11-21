import Height.Steenrod.PartnerUniversalIdeal
import Height.Steenrod.FlagPencils

/-!
# Triangularizable and flagless partner loci (`defn:flagless`, `cor:flagless`)

This is the set-theoretic part of the flagless reduction.  The partner locus
splits disjointly according to whether its pencil admits a common complete
flag.  The triangularizable part is exactly the union of conjugate standard
nilradicals which contain the fixed endpoint.

The split `𝒞_N = 𝒞_N^Δ ⊔ (flagless part)` is what `cor:flagless` reduces
the theorem to.
-/

namespace Height.Steenrod

open Height.Toolbox

universe u

variable {K : Type u} [Field K] (n : ℕ)

/-- All nilpotent partners of a fixed matrix. -/
def nilpotentPartnerLocus (N : Matrix (Fin n) (Fin n) K) :
    Set (Matrix (Fin n) (Fin n) K) :=
  {M | NilpotentPencil N M}

/-- Partners which lie with the fixed endpoint in one flag nilradical. -/
def triangularizablePartnerLocus (N : Matrix (Fin n) (Fin n) K) :
    Set (Matrix (Fin n) (Fin n) K) :=
  {M | TriangularizablePencil K n N M}

/-- Partners whose pencil admits no common complete flag. -/
def flaglessPartnerLocus (N : Matrix (Fin n) (Fin n) K) :
    Set (Matrix (Fin n) (Fin n) K) :=
  {M | FlaglessPencil K n N M}

/-- The partner locus is the union of its triangularizable and flagless
parts. -/
theorem nilpotentPartnerLocus_eq_union (N : Matrix (Fin n) (Fin n) K) :
    nilpotentPartnerLocus n N =
      triangularizablePartnerLocus n N ∪ flaglessPartnerLocus n N := by
  ext M
  simp only [nilpotentPartnerLocus, triangularizablePartnerLocus,
    flaglessPartnerLocus, Set.mem_ofPred_eq, Set.mem_union, FlaglessPencil]
  constructor
  · intro h
    by_cases ht : TriangularizablePencil K n N M
    · exact Or.inl ht
    · exact Or.inr ⟨h, ht⟩
  · rintro (ht | hf)
    · exact ht.nilpotentPencil
    · exact hf.1

/-- A point lies in the triangularizable partner locus exactly when both
endpoints lie in one conjugate of the standard nilradical. -/
theorem mem_triangularizablePartnerLocus_iff_exists_conjugateNilradical
    (N M : Matrix (Fin n) (Fin n) K) :
    M ∈ triangularizablePartnerLocus n N ↔
      ∃ g : (Matrix (Fin n) (Fin n) K)ˣ,
        N ∈ conjugateNilradical K n g ∧
          M ∈ conjugateNilradical K n g := by
  exact triangularizablePencil_iff_mem_conjugateNilradical K n N M

variable (p r : ℕ) [Fact p.Prime]
variable [Algebra (GaloisField p r) K]

end Height.Steenrod
