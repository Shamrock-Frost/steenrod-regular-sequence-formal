import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Rank–nullity on a subspace

One lemma of finite-dimensional linear algebra over a field: for a
linear map `f` and a finite-dimensional subspace `p` of its source,

  `dim (f '' p) + dim (p ∩ ker f) = dim p`.

Mathlib has `LinearMap.finrank_range_add_finrank_ker` for the whole source and
`Submodule.finrank_quotient_add_finrank` for a quotient, but not this form; it
is that theorem applied to `f.domRestrict p`.

Its users are the Hilbert-function splits of
`Height/Graded` and the length counts of `Height/Pencil`.
-/

namespace Height.Toolbox

variable {K : Type*} [Field K]

/-- **Rank–nullity on a subspace.**  `dim (f '' p) + dim (p ∩ ker f) = dim p`. -/
theorem finrank_map_add_finrank_inf_ker {M N : Type*} [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (f : M →ₗ[K] N) (p : Submodule K M) [Module.Finite K p] :
    Module.finrank K (p.map f) + Module.finrank K ((p ⊓ LinearMap.ker f : Submodule K M))
      = Module.finrank K p := by
  have h := LinearMap.finrank_range_add_finrank_ker (f.domRestrict p)
  have hk : LinearMap.ker (f.domRestrict p)
      = Submodule.comap p.subtype (p ⊓ LinearMap.ker f) := by
    ext x
    exact ⟨fun hx => ⟨x.2, hx⟩, fun hx => hx.2⟩
  rw [LinearMap.range_domRestrict, hk,
    (Submodule.comapSubtypeEquivOfLe (inf_le_left : p ⊓ LinearMap.ker f ≤ p)).finrank_eq] at h
  exact h

end Height.Toolbox
