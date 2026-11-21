import Height.Geometry.Dimension.Affine

/-!
# Irreducibility of products and images of affine sets

Everything is stated in the affine language of
`Height/Geometry`: a "set" is a subset `S ⊆ (ι → K)` of affine space, its
coordinate ring is `MvPolynomial ι K ⧸ MvPolynomial.vanishingIdeal K S`, and its
dimension is `Height.Geometry.affineDim S`, the Krull dimension of that ring.
Here **`S` is irreducible** means

```
(MvPolynomial.vanishingIdeal K S).IsPrime
```

which is spelled out in every statement rather than hidden behind an
abbreviation, so that consumers need not guess a name.  Note that primality
already forces `S ≠ ∅` (the vanishing ideal of `∅` is `⊤`).

Contents:

* `sumProd S T ⊆ (ι ⊕ κ → K)` — the product of two affine sets;
* `Height.Geometry.irreducible_prod` — a product of irreducibles is irreducible;
* `Height.Geometry.irreducible_image` — a polynomial image of an irreducible is
  irreducible.

Polynomial maps, Zariski closure, and the elementary dimension calculus are in
`Geometry/Dimension/Affine.lean`.

`irreducible_prod` and `irreducible_image` need
**no** hypothesis on `K` beyond being a field (the classical proof uses the
Nullstellensatz only through the Galois connection, which is unconditional).
`IsAlgClosed K` and `Finite ι` enter only in `affineDim_zeroLocus`.
-/

universe u v

open MvPolynomial

namespace Height.Geometry

variable {K : Type u} [Field K] {ι κ : Type v}

/-! ### Products of affine sets -/

/-- Substituting the values `s` for the left-hand variables. -/
noncomputable def subLeft (s : ι → K) (f : MvPolynomial (ι ⊕ κ) K) : MvPolynomial κ K :=
  aeval (Sum.elim (fun i => C (s i)) X) f

/-- Substituting the values `t` for the right-hand variables. -/
noncomputable def subRight (t : κ → K) (f : MvPolynomial (ι ⊕ κ) K) : MvPolynomial ι K :=
  aeval (Sum.elim X fun j => C (t j)) f

theorem aeval_subLeft (s : ι → K) (t : κ → K) (f : MvPolynomial (ι ⊕ κ) K) :
    aeval t (subLeft s f) = aeval (Sum.elim s t) f := by
  have h : (aeval t : MvPolynomial κ K →ₐ[K] K).comp
      (aeval (Sum.elim (fun i => C (s i)) X) : MvPolynomial (ι ⊕ κ) K →ₐ[K] MvPolynomial κ K) =
      (aeval (Sum.elim s t) : MvPolynomial (ι ⊕ κ) K →ₐ[K] K) := by
    refine MvPolynomial.algHom_ext fun w => ?_
    cases w <;> simp
  exact AlgHom.congr_fun h f

theorem aeval_subRight (s : ι → K) (t : κ → K) (f : MvPolynomial (ι ⊕ κ) K) :
    aeval s (subRight t f) = aeval (Sum.elim s t) f := by
  have h : (aeval s : MvPolynomial ι K →ₐ[K] K).comp
      (aeval (Sum.elim X fun j => C (t j)) :
        MvPolynomial (ι ⊕ κ) K →ₐ[K] MvPolynomial ι K) =
      (aeval (Sum.elim s t) : MvPolynomial (ι ⊕ κ) K →ₐ[K] K) := by
    refine MvPolynomial.algHom_ext fun w => ?_
    cases w <;> simp
  exact AlgHom.congr_fun h f

/-- The product `S × T`, as a subset of the affine space on `ι ⊕ κ`. -/
def sumProd (S : Set (ι → K)) (T : Set (κ → K)) : Set (ι ⊕ κ → K) :=
  {z | (fun i => z (Sum.inl i)) ∈ S ∧ (fun j => z (Sum.inr j)) ∈ T}

omit [Field K] in
theorem elim_mem_sumProd {S : Set (ι → K)} {T : Set (κ → K)} {s : ι → K} {t : κ → K}
    (hs : s ∈ S) (ht : t ∈ T) : Sum.elim s t ∈ sumProd S T := ⟨hs, ht⟩

omit [Field K] in
theorem elim_comp_inl_inr (z : ι ⊕ κ → K) :
    Sum.elim (fun i => z (Sum.inl i)) (fun j => z (Sum.inr j)) = z :=
  funext fun w => by cases w <;> rfl

theorem mem_vanishingIdeal_sumProd {S : Set (ι → K)} {T : Set (κ → K)}
    {f : MvPolynomial (ι ⊕ κ) K} :
    f ∈ MvPolynomial.vanishingIdeal K (sumProd S T) ↔
      ∀ s ∈ S, ∀ t ∈ T, aeval (Sum.elim s t) f = 0 := by
  constructor
  · intro h s hs t ht
    exact h _ (elim_mem_sumProd hs ht)
  · intro h z hz
    have key := h _ hz.1 _ hz.2
    rwa [elim_comp_inl_inr] at key

/-- A product of irreducible affine sets is
irreducible.  No hypothesis on `K` beyond being a field. -/
theorem irreducible_prod {S : Set (ι → K)} {T : Set (κ → K)}
    (hS : (MvPolynomial.vanishingIdeal K S).IsPrime)
    (hT : (MvPolynomial.vanishingIdeal K T).IsPrime) :
    (MvPolynomial.vanishingIdeal K (sumProd S T)).IsPrime := by
  -- Both factors are nonempty, since the vanishing ideal of `∅` is `⊤`.
  obtain ⟨s₀, hs₀⟩ : S.Nonempty := by
    rcases Set.eq_empty_or_nonempty S with h | h
    · exact absurd ((vanishingIdeal_eq_top_iff S).2 h) hS.ne_top
    · exact h
  obtain ⟨t₀, ht₀⟩ : T.Nonempty := by
    rcases Set.eq_empty_or_nonempty T with h | h
    · exact absurd ((vanishingIdeal_eq_top_iff T).2 h) hT.ne_top
    · exact h
  constructor
  · rw [ne_eq, vanishingIdeal_eq_top_iff]
    exact Set.Nonempty.ne_empty ⟨Sum.elim s₀ t₀, elim_mem_sumProd hs₀ ht₀⟩
  · intro f g hfg
    -- The two closed pieces of `S` on which the slice of `f` (resp. `g`) vanishes.
    set Sf : Set (ι → K) := {s | s ∈ S ∧ ∀ t ∈ T, aeval (Sum.elim s t) f = 0} with hSf
    set Sg : Set (ι → K) := {s | s ∈ S ∧ ∀ t ∈ T, aeval (Sum.elim s t) g = 0} with hSg
    -- Every point of `S` lies in one of them, by primality of `I(T)`.
    have hcover : ∀ s ∈ S, s ∈ Sf ∨ s ∈ Sg := by
      intro s hs
      have hmul : subLeft s f * subLeft s g ∈ MvPolynomial.vanishingIdeal K T := by
        intro t ht
        rw [map_mul, aeval_subLeft, aeval_subLeft, ← map_mul]
        exact mem_vanishingIdeal_sumProd.1 hfg s hs t ht
      rcases hT.mem_or_mem hmul with h | h
      · exact Or.inl ⟨hs, fun t ht => by rw [← aeval_subLeft]; exact h t ht⟩
      · exact Or.inr ⟨hs, fun t ht => by rw [← aeval_subLeft]; exact h t ht⟩
    -- Hence `I(Sf) · I(Sg) ⊆ I(S)`, and `I(S)` is prime.
    have hprod : MvPolynomial.vanishingIdeal K Sf * MvPolynomial.vanishingIdeal K Sg ≤
        MvPolynomial.vanishingIdeal K S := by
      refine Ideal.mul_le.2 fun a ha b hb s hs => ?_
      rw [map_mul]
      rcases hcover s hs with h | h
      · rw [ha s h, zero_mul]
      · rw [hb s h, mul_zero]
    -- One of the two ideals is contained in `I(S)`; that side of the product vanishes.
    have key : ∀ (h : MvPolynomial (ι ⊕ κ) K),
        MvPolynomial.vanishingIdeal K {s | s ∈ S ∧ ∀ t ∈ T, aeval (Sum.elim s t) h = 0} ≤
          MvPolynomial.vanishingIdeal K S →
        h ∈ MvPolynomial.vanishingIdeal K (sumProd S T) := by
      intro h hle
      refine mem_vanishingIdeal_sumProd.2 fun s hs t ht => ?_
      have hmem : subRight t h ∈
          MvPolynomial.vanishingIdeal K {s | s ∈ S ∧ ∀ t ∈ T, aeval (Sum.elim s t) h = 0} := by
        intro s' hs'
        rw [aeval_subRight]
        exact hs'.2 t ht
      have := hle hmem s hs
      rwa [aeval_subRight] at this
    rcases hS.mul_le.1 hprod with h | h
    · exact Or.inl (key f h)
    · exact Or.inr (key g h)

/-! ### Images of affine sets -/

/-- The vanishing ideal of the image of `S` under a polynomial map is the
contraction of the vanishing ideal of `S`. -/
theorem vanishingIdeal_image {f : (ι → K) → (κ → K)} {F : κ → MvPolynomial ι K}
    (hF : ∀ y j, f y j = aeval y (F j)) (S : Set (ι → K)) :
    MvPolynomial.vanishingIdeal K (f '' S) =
      (MvPolynomial.vanishingIdeal K S).comap
        (aeval F : MvPolynomial κ K →ₐ[K] MvPolynomial ι K) := by
  ext g
  simp only [MvPolynomial.mem_vanishingIdeal_iff, Ideal.mem_comap, Set.mem_image]
  constructor
  · intro h y hy
    rw [← aeval_polyMap hF]
    exact h (f y) ⟨y, hy, rfl⟩
  · rintro h _ ⟨y, hy, rfl⟩
    rw [aeval_polyMap hF]
    exact h y hy

/-- The image of an irreducible affine set under a
polynomial map is irreducible.  No hypothesis on `K` beyond being a field. -/
theorem irreducible_image {f : (ι → K) → (κ → K)} (hf : IsPolyMap f) {S : Set (ι → K)}
    (hS : (MvPolynomial.vanishingIdeal K S).IsPrime) :
    (MvPolynomial.vanishingIdeal K (f '' S)).IsPrime := by
  obtain ⟨F, hF⟩ := hf
  have : (MvPolynomial.vanishingIdeal K S).IsPrime := hS
  rw [vanishingIdeal_image hF]
  exact Ideal.IsPrime.comap _

end Height.Geometry
