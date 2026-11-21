import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.Ideal.Height
import Mathlib.LinearAlgebra.Dimension.Basic
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.Ideal.UFD
import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
# Dimension theory of affine algebras

Commutative algebra that mathlib lacks and the geometry API needs: for a
finitely generated domain `R` over a field, every prime `p` satisfies
`height p + dim (R ⧸ p) = dim R` (Eisenbud, *Commutative Algebra*, Cor. 13.4;
Stacks, "Dimension of finite type algebras over fields").  In particular every
maximal ideal has height `dim R`, so the local ring at every closed point of an
irreducible affine variety has the dimension of the variety, and a nonempty
principal open has the dimension of the variety.  Inputs mathlib has: Noether
normalization `exists_integral_inj_algHom_of_fg` (with `s = ringKrullDim R`),
`IsIntegral.ringKrullDim_eq_of_injective`, going-down for integral extensions of
normal domains (`Mathlib/RingTheory/IntegralClosure/GoingDown.lean`),
`IsLocalization.AtPrime.ringKrullDim_eq_height`,
`Ideal.height_le_ringKrullDim_of_isPrime`, `ringKrullDim_of_isNoetherianRing`
(`dim R[X] = dim R + 1`).  Mathlib candidates, all of them.

## The route to the dimension formula

Eisenbud's proof of Theorem A(b), not the Cohen–Macaulay route of Stacks 00OS
(mathlib has neither regular sequences at this generality nor Cohen–Macaulay
rings).  Write `K` for the base field and `d = dim R`.

1. `dim K[X₁, …, Xₙ] = n` is `MvPolynomial.ringKrullDim_of_isNoetherianRing`
   over a field (`ringKrullDim_mvPolynomial_fintype`).
2. Every maximal ideal of `A = K[X₁, …, Xₙ]` has height `n`
   (`height_eq_of_isMaximal_mvPolynomial`).  Induction on `n` through
   `MvPolynomial.finSuccEquiv : K[X₀, …, Xₙ] ≃ₐ[K] (K[X₁, …, Xₙ])[X]`:
   `A` is a Jacobson ring, so the contraction of a maximal ideal of `S[X]` along
   `C` is maximal (`Polynomial.isMaximal_comap_C_of_isJacobsonRing`), and then
   `Polynomial.height_eq_height_add_one` adds exactly one.  This is the only
   place the Nullstellensatz enters.
3. `dim (A ⧸ (f)) = n - 1` for a prime element `f` of `A`
   (`ringKrullDim_quotient_span_singleton_mvPolynomial`).  `≤` is
   `ringKrullDim_quotient_le_of_ne_bot`: a chain of primes over a nonzero ideal
   of a domain is one shorter than a chain of primes, because the zero ideal can
   be prefixed.  `≥` is Krull's principal ideal theorem in the form
   `Ideal.height_le_ringKrullDim_quotient_add_one`, applied to a maximal ideal
   containing `f`, whose height is `n` by step 2.  This is the only place where
   dimension is *created*, and it is why step 2 is needed.
4. `dim (R ⧸ P) + 1 = dim R` for a height-one prime `P` of a finitely generated
   domain `R` over `K` (`ringKrullDim_quotient_of_height_one`).  Noether
   normalization gives `A = K[X₁, …, X_d] ↪ R` integral with `d = dim R`; put
   `q = P ∩ A`.  Going-down for the integral extension of the normal domain `A`
   gives `height q ≤ height P = 1` (`height_under_le_of_hasGoingDown`), and
   `q ≠ 0` because the extension is integral, so `height q = 1`; `A` is a UFD,
   so `q = (f)` with `f` prime; `A ⧸ q ↪ R ⧸ P` is injective and integral, so
   the two quotients have the same dimension; conclude by step 3.
5. The dimension formula `height p + dim (R ⧸ p) = dim R`
   (`height_add_ringKrullDim_quotient`), by induction on `height p`.  For
   `height p = h + 1` take a chain of length `h + 1` below `p` and let `p'` be
   its penultimate term: `height p' = h`, and no prime lies strictly between
   `p'` and `p` (a longer chain would contradict `height p = h + 1`), so the
   image of `p` in `R ⧸ p'` has height one.  Step 4 in `R ⧸ p'` and the
   induction hypothesis at `p'` give the formula, using
   `(R ⧸ p') ⧸ (p ⧸ p') ≃+* R ⧸ p`.

The remaining statements are corollaries: `dim (R ⧸ m) = 0` for `m` maximal
gives `height m = dim R`, hence the dimension of the local ring at a closed
point; and a nonzero `f` avoids some maximal ideal because a finitely generated
algebra over a field is Jacobson, which gives the principal open.

The cotangent statement is independent of all of this: `m ⧸ m²` is already local
at `m`, because `m` and `m ^ 2` are saturated at `m` (if `s ∉ m` and `s * x ∈ m ^ 2`
then `x ∈ m ^ 2`), so both the residue field and the cotangent space are unchanged
by the localisation, and `rank_eq_of_equiv_equiv` transports the dimension across
the two isomorphisms.
-/

open Ideal

namespace Height.Toolbox

/-! ### Two general lemmas on chains of primes -/

/-- **A nonzero ideal of a domain drops the Krull dimension.**  A chain of primes of `R ⧸ I`
is a chain of primes of `R` all containing `I`, hence all nonzero, so the zero ideal can be
prefixed to it.  The bound is stated as `dim (R ⧸ I) ≤ d` under `dim R ≤ d + 1` rather than as
`dim (R ⧸ I) + 1 ≤ dim R`, to keep the `⊥`/`⊤` arithmetic of `WithBot ℕ∞` out of the way. -/
theorem ringKrullDim_quotient_le_of_ne_bot {R : Type*} [CommRing R] [IsDomain R]
    {I : Ideal R} (hI : I ≠ ⊥) {d : ℕ} (hd : ringKrullDim R ≤ ((d + 1 : ℕ) : WithBot ℕ∞)) :
    ringKrullDim (R ⧸ I) ≤ (d : WithBot ℕ∞) := by
  rw [ringKrullDim_le_iff_height_le]
  intro P hP
  have hmono : StrictMono (PrimeSpectrum.comap (Ideal.Quotient.mk I)) :=
    RingHom.strictMono_comap_of_surjective Ideal.Quotient.mk_surjective
  have key : Order.height (⟨P, hP⟩ : PrimeSpectrum (R ⧸ I)) ≤ (d : ℕ∞) := by
    refine Order.height_le ?_
    intro l _
    have hhead : (⟨⊥, inferInstance⟩ : PrimeSpectrum R) < (l.map _ hmono).head := by
      rw [← PrimeSpectrum.asIdeal_lt_asIdeal, LTSeries.head_map]
      refine lt_of_le_of_ne bot_le fun hbot ↦ hI (le_bot_iff.mp ?_)
      intro x hx
      have hmem : x ∈ (PrimeSpectrum.comap (Ideal.Quotient.mk I) l.head).asIdeal := by
        simpa [PrimeSpectrum.comap, Ideal.mem_comap] using
          (Ideal.Quotient.eq_zero_iff_mem.mpr hx) ▸ Ideal.zero_mem _
      rwa [← hbot] at hmem
    have hlen := le_trans (Order.LTSeries.length_le_krullDim ((l.map _ hmono).cons _ hhead)) hd
    rw [RelSeries.cons_length, LTSeries.map_length] at hlen
    have hnat : l.length + 1 ≤ d + 1 := by exact_mod_cast hlen
    exact_mod_cast Nat.succ_le_succ_iff.mp hnat
  have h2 : P.height ≤ (d : ℕ∞) := by
    rw [show P.height = Order.height (⟨P, hP⟩ : PrimeSpectrum (R ⧸ I)) from
      PrimeSpectrum.height_eq_orderHeight ⟨P, hP⟩]
    exact key
  exact_mod_cast h2

/-- **Going down does not raise height on contraction**: a chain of primes below `P ∩ A`
lifts to a chain of primes below `P`. -/
theorem height_under_le_of_hasGoingDown {A S : Type*} [CommRing A] [CommRing S] [Algebra A S]
    [Algebra.HasGoingDown A S] (P : Ideal S) [hP : P.IsPrime] :
    (P.under A).height ≤ P.height := by
  have hp : (P.under A).IsPrime := inferInstance
  rw [PrimeSpectrum.height_eq_orderHeight (⟨P.under A, hp⟩ : PrimeSpectrum A)]
  refine Order.height_le ?_
  intro l hl
  have hlo : P.LiesOver l.last.asIdeal := by rw [hl]; exact Ideal.over_under P
  obtain ⟨L, hlen, hlast, -⟩ := Ideal.exists_ltSeries_of_hasGoingDown l P
  rw [← hlen, PrimeSpectrum.height_eq_orderHeight (⟨P, hP⟩ : PrimeSpectrum S), ← hlast]
  exact Order.length_le_height_last

/-! ### Polynomial rings -/

/-- `dim K[X₁, …, Xₙ] = n`. -/
theorem ringKrullDim_mvPolynomial_fintype (K : Type*) [Field K] (σ : Type*) [Fintype σ] :
    ringKrullDim (MvPolynomial σ K) = Fintype.card σ := by
  simp [MvPolynomial.ringKrullDim_of_isNoetherianRing, Nat.card_eq_fintype_card]

/-- **Every maximal ideal of `K[X₁, …, Xₙ]` has height `n`.**  Induction on `n` through
`MvPolynomial.finSuccEquiv`: a polynomial ring over a field is a Jacobson ring, so the
contraction of a maximal ideal of `S[X]` along `C` is a maximal ideal of `S`
(`Polynomial.isMaximal_comap_C_of_isJacobsonRing`), and `Polynomial.height_eq_height_add_one`
adds exactly one. -/
theorem height_eq_of_isMaximal_mvPolynomial (K : Type*) [Field K] (n : ℕ)
    (m : Ideal (MvPolynomial (Fin n) K)) (hm : m.IsMaximal) : m.height = n := by
  induction n with
  | zero =>
    have h0 : ringKrullDim (MvPolynomial (Fin 0) K) = 0 := by
      simp [ringKrullDim_mvPolynomial_fintype K (Fin 0)]
    have _ := hm.isPrime
    have hle := Ideal.height_le_ringKrullDim_of_isPrime (I := m)
    rw [h0] at hle
    simpa using hle
  | succ n ih =>
    have _ := hm
    set e := (MvPolynomial.finSuccEquiv K n).toRingEquiv with he
    have hM : (m.map e).IsMaximal := Ideal.map_isMaximal_of_equiv e
    have hp : ((m.map e).comap Polynomial.C).IsMaximal :=
      Polynomial.isMaximal_comap_C_of_isJacobsonRing (m.map e)
    have hlo : (m.map e).LiesOver ((m.map e).comap Polynomial.C) := by
      refine ⟨?_⟩
      rw [Ideal.under_def, Polynomial.algebraMap_eq]
    have key := Polynomial.height_eq_height_add_one ((m.map e).comap Polynomial.C) (m.map e)
    rw [ih _ hp, RingEquiv.height_map e m] at key
    rw [key]
    norm_cast

/-- **The dimension of a hypersurface.**  For a prime element `f` of `A = K[X₁, …, Xₙ]`,
`dim (A ⧸ (f)) + 1 = n`.  The inequality `≤` prefixes the zero ideal to a chain
(`ringKrullDim_quotient_le_of_ne_bot`); the inequality `≥` is Krull's principal ideal theorem in
the form `Ideal.height_le_ringKrullDim_quotient_add_one`, applied to a maximal ideal containing
`f`, whose height is `n` by `height_eq_of_isMaximal_mvPolynomial`. -/
theorem ringKrullDim_quotient_span_singleton_mvPolynomial (K : Type*) [Field K] (n : ℕ)
    {f : MvPolynomial (Fin n) K} (hf : Prime f) :
    ringKrullDim (MvPolynomial (Fin n) K ⧸ Ideal.span {f}) + 1 = (n : WithBot ℕ∞) := by
  have hdimA : ringKrullDim (MvPolynomial (Fin n) K) = (n : WithBot ℕ∞) := by
    simp [ringKrullDim_mvPolynomial_fintype K (Fin n)]
  have hspan : (Ideal.span {f}).IsPrime := (Ideal.span_singleton_prime hf.ne_zero).mpr hf
  have hne : Ideal.span ({f} : Set (MvPolynomial (Fin n) K)) ≠ ⊥ := by
    simp [hf.ne_zero]
  have h1n : 1 ≤ n := by
    have h1 : (1 : ℕ∞) ≤ (Ideal.span {f}).height := by
      simpa [Order.one_le_iff_ne_zero, Ideal.height_eq_zero_iff_eq_bot] using hne
    have h2 := Ideal.height_le_ringKrullDim_of_isPrime
      (I := Ideal.span ({f} : Set (MvPolynomial (Fin n) K)))
    rw [hdimA] at h2
    have h3 : ((1 : ℕ∞) : WithBot ℕ∞) ≤ (n : WithBot ℕ∞) := le_trans (by exact_mod_cast h1) h2
    exact_mod_cast h3
  obtain ⟨d, rfl⟩ : ∃ d, n = d + 1 := ⟨n - 1, by omega⟩
  refine le_antisymm ?_ ?_
  · have hle := ringKrullDim_quotient_le_of_ne_bot hne (d := d) (by rw [hdimA])
    calc ringKrullDim (MvPolynomial (Fin (d + 1)) K ⧸ Ideal.span {f}) + 1
        ≤ (d : WithBot ℕ∞) + 1 := by gcongr
      _ = ((d + 1 : ℕ) : WithBot ℕ∞) := by push_cast; ring
  · obtain ⟨m, hm, hle⟩ := (Ideal.span ({f} : Set (MvPolynomial (Fin (d + 1)) K))).exists_le_maximal
      hspan.ne_top
    have _ := hm.isPrime
    have hh := Ideal.height_le_ringKrullDim_quotient_add_one
      (r := f) (p := m) (hle (Ideal.mem_span_singleton_self f))
    rw [height_eq_of_isMaximal_mvPolynomial K _ m hm] at hh
    exact hh

/-! ### Finitely generated domains over a field -/

section Affine

variable {K : Type*} [Field K] (R : Type*) [CommRing R] [IsDomain R] [Algebra K R]
  [Algebra.FiniteType K R]

-- `K` is not mentioned by the statements, so its instances would otherwise be dropped
-- (the signatures elaborated to false claims about arbitrary domains before this line).
include K

/-- **A height-one prime cuts the dimension by exactly one.**  Noether normalization gives an
integral extension `A = K[X₁, …, X_d] ↪ R` with `d = dim R`; the contraction `q = P ∩ A` has
height one (going down for the normal domain `A`, and `q ≠ 0` because the extension is
integral), so `q = (f)` with `f` prime because `A` is a UFD; and `A ⧸ q ↪ R ⧸ P` is injective
and integral, so the two quotients have the same dimension.

Note the `include K in`: without it Lean drops the unmentioned variable `K`, hence also the
instances `[Algebra K R]` and `[Algebra.FiniteType K R]`, and the statement would be about an
arbitrary domain, where it is false. -/
theorem ringKrullDim_quotient_of_height_one (P : Ideal R) [P.IsPrime] (hP : P.height = 1) :
    ringKrullDim (R ⧸ P) + 1 = ringKrullDim R := by
  obtain ⟨s, hs, g, hginj, hgint⟩ := exists_integral_inj_algHom_of_fg K R
  let _ : Algebra (MvPolynomial (Fin s) K) R := g.toRingHom.toAlgebra
  have : Algebra.IsIntegral (MvPolynomial (Fin s) K) R := ⟨hgint⟩
  have : FaithfulSMul (MvPolynomial (Fin s) K) R :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hginj
  have hqp : (P.under (MvPolynomial (Fin s) K)).IsPrime := inferInstance
  have hqne : P.under (MvPolynomial (Fin s) K) ≠ ⊥ :=
    Ideal.IsIntegral.comap_ne_bot _ (Ideal.ne_bot_of_height_eq_one hP)
  have hq1 : (P.under (MvPolynomial (Fin s) K)).height = 1 := by
    refine le_antisymm (hP ▸ height_under_le_of_hasGoingDown P) ?_
    simpa [Order.one_le_iff_ne_zero, Ideal.height_eq_zero_iff_eq_bot] using hqne
  have hprinc := UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hq1
  set f := Submodule.IsPrincipal.generator (P.under (MvPolynomial (Fin s) K)) with hfdef
  have hfp : Prime f := Submodule.IsPrincipal.prime_generator_of_isPrime _ hqne
  have hspan : Ideal.span {f} = P.under (MvPolynomial (Fin s) K) := by
    rw [← Ideal.submodule_span_eq]
    exact Submodule.IsPrincipal.span_singleton_generator _
  have hdimeq : ringKrullDim (MvPolynomial (Fin s) K ⧸ P.under (MvPolynomial (Fin s) K))
      = ringKrullDim (R ⧸ P) := by
    refine RingHom.IsIntegral.ringKrullDim_eq_of_injective
      (f := algebraMap (MvPolynomial (Fin s) K ⧸ P.under (MvPolynomial (Fin s) K)) (R ⧸ P))
      ?_ (FaithfulSMul.algebraMap_injective _ _)
    exact Algebra.isIntegral_def.mp inferInstance
  rw [← hdimeq, ← hspan, ringKrullDim_quotient_span_singleton_mvPolynomial K s hfp, hs]

/-- The induction scaffold for `height_add_ringKrullDim_quotient`, with the height of `p` named
as a natural number so the induction can run on it.  The step from `h` to `h + 1` takes a chain
of primes of length `h + 1` below `p` and its penultimate term `P'`: `P'` has height `h`
(`Order.index_le_height` and `Ideal.height_add_one_le_of_lt_of_isPrime`), no prime lies strictly
between `P'` and `p` (a prime in between would give a chain of length `h + 2` below `p`), so the
image of `p` in `R ⧸ P'` has height one and `ringKrullDim_quotient_of_height_one` applies. -/
theorem height_add_ringKrullDim_quotient_of_height_eq (h : ℕ) :
    ∀ (p : Ideal R) (_ : p.IsPrime), p.height = h →
      ((h : ℕ∞) : WithBot ℕ∞) + ringKrullDim (R ⧸ p) = ringKrullDim R := by
  have _ : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing K R
  induction h with
  | zero =>
    intro p hp hph
    obtain rfl : p = ⊥ := Ideal.height_eq_zero_iff_eq_bot.mp (by simpa using hph)
    rw [ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot R)]
    simp
  | succ h ih =>
    intro p hp hph
    obtain ⟨l, hlast, hlen⟩ := Ideal.exists_ltSeries_length_eq_height p
    have hlen' : l.length = h + 1 := by
      have hc : ((l.length : ℕ) : ℕ∞) = ((h + 1 : ℕ) : ℕ∞) := by rw [hlen, hph]
      exact_mod_cast hc
    have hP'lt : l.toFun ⟨h, by omega⟩ < (⟨p, hp⟩ : PrimeSpectrum R) := by
      rw [← hlast]
      refine l.strictMono ?_
      simp only [Fin.lt_def, Fin.val_last]
      omega
    set P' : Ideal R := (l.toFun ⟨h, by omega⟩).asIdeal with hP'def
    have hP'prime : P'.IsPrime := (l.toFun ⟨h, by omega⟩).isPrime
    have hlt : P' < p := hP'lt
    have hP'h : P'.height = (h : ℕ∞) := by
      obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp (Ideal.height_ne_top_of_isPrime (I := P'))
      have hge : (h : ℕ∞) ≤ P'.height := by
        rw [hP'def, PrimeSpectrum.height_eq_orderHeight]
        simpa using Order.index_le_height l ⟨h, by omega⟩
      have h1 : h ≤ k := by rw [← hk] at hge; exact_mod_cast hge
      have h2 : k + 1 ≤ h + 1 := by
        have hstep := Ideal.height_add_one_le_of_lt_of_isPrime hlt
        rw [hph, ← hk] at hstep
        exact_mod_cast hstep
      rw [← hk]
      congr 1
      omega
    have hbetween : ∀ q : Ideal R, q.IsPrime → P' < q → q < p → False := by
      intro q hq h1 h2
      obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp (Ideal.height_ne_top_of_isPrime (I := q))
      have e1 : h + 1 ≤ k := by
        have hstep := Ideal.height_add_one_le_of_lt_of_isPrime h1
        rw [hP'h, ← hk] at hstep
        exact_mod_cast hstep
      have e2 : k + 1 ≤ h + 1 := by
        have hstep := Ideal.height_add_one_le_of_lt_of_isPrime h2
        rw [hph, ← hk] at hstep
        exact_mod_cast hstep
      omega
    have hpbarprime : (p.map (Ideal.Quotient.mk P')).IsPrime :=
      Ideal.isPrime_map_quotientMk_of_isPrime hlt.le
    have hcomap : (p.map (Ideal.Quotient.mk P')).comap (Ideal.Quotient.mk P') = p := by
      rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective]
      simpa [← RingHom.ker_eq_comap_bot, Ideal.mk_ker] using hlt.le
    have hpbarne : p.map (Ideal.Quotient.mk P') ≠ ⊥ := by
      intro hb
      rw [hb, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker] at hcomap
      exact absurd hcomap hlt.ne
    have hpbar1 : (p.map (Ideal.Quotient.mk P')).height = 1 := by
      refine le_antisymm ?_ ?_
      · rw [PrimeSpectrum.height_eq_orderHeight
          (⟨p.map (Ideal.Quotient.mk P'), hpbarprime⟩ : PrimeSpectrum (R ⧸ P')),
          show (1 : ℕ∞) = ((1 : ℕ) : ℕ∞) by norm_cast]
        refine Order.height_le_coe_iff.mpr ?_
        intro y hy
        have hmono : StrictMono (PrimeSpectrum.comap (Ideal.Quotient.mk P')) :=
          RingHom.strictMono_comap_of_surjective Ideal.Quotient.mk_surjective
        have hlt2 : y.asIdeal.comap (Ideal.Quotient.mk P') < p := by
          have hh := hmono hy
          rw [← PrimeSpectrum.asIdeal_lt_asIdeal] at hh
          simpa [hcomap] using hh
        have hge2 : P' ≤ y.asIdeal.comap (Ideal.Quotient.mk P') := by
          intro x hx
          simp [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
        have heq : y.asIdeal.comap (Ideal.Quotient.mk P') = P' := by
          rcases eq_or_lt_of_le hge2 with e | e
          · exact e.symm
          · exact absurd (hbetween _ inferInstance e hlt2) not_false
        have hybot : y.asIdeal = ⊥ := by
          rw [← Ideal.map_comap_of_surjective (Ideal.Quotient.mk P')
            Ideal.Quotient.mk_surjective y.asIdeal, heq, Ideal.map_quotient_self]
        have hy0 : Order.height y = 0 := by
          rw [← PrimeSpectrum.height_eq_orderHeight y, hybot]
          simp
        simp [hy0]
      · simpa [Order.one_le_iff_ne_zero, Ideal.height_eq_zero_iff_eq_bot] using hpbarne
    have hstep := ringKrullDim_quotient_of_height_one (K := K) (R ⧸ P')
      (p.map (Ideal.Quotient.mk P')) hpbar1
    rw [ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hlt.le)] at hstep
    rw [← ih P' hP'prime hP'h, ← hstep]
    push_cast
    ring

/-- **The dimension formula** for a finitely generated domain over a field:
`height p + dim (R ⧸ p) = dim R` for every prime `p` (Eisenbud Cor. 13.4). -/
theorem height_add_ringKrullDim_quotient (p : Ideal R) [p.IsPrime] :
    ((p.height : ℕ∞) : WithBot ℕ∞) + ringKrullDim (R ⧸ p) = ringKrullDim R := by
  have _ : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing K R
  obtain ⟨h, hh⟩ := ENat.ne_top_iff_exists.mp (Ideal.height_ne_top_of_isPrime (I := p))
  rw [← hh]
  exact height_add_ringKrullDim_quotient_of_height_eq (K := K) R h p inferInstance hh.symm

/-- Every maximal ideal of a finitely generated domain over a field has height `dim R`. -/
theorem height_eq_ringKrullDim_of_isMaximal (m : Ideal R) [m.IsMaximal] :
    ((m.height : ℕ∞) : WithBot ℕ∞) = ringKrullDim R := by
  have h0 : ringKrullDim (R ⧸ m) = 0 :=
    ringKrullDim_eq_zero_of_isField
      ((Ideal.Quotient.maximal_ideal_iff_isField_quotient m).mp ‹m.IsMaximal›)
  have hkey := height_add_ringKrullDim_quotient (K := K) R m
  rwa [h0, add_zero] at hkey

/-- Localizing a finitely generated domain over a field away from a nonzero element keeps
the dimension (a nonempty principal open of an irreducible variety has its dimension). -/
theorem ringKrullDim_localization_away {f : R} (hf : f ≠ 0) :
    ringKrullDim (Localization.Away f) = ringKrullDim R := by
  refine le_antisymm ?_ ?_
  · rw [ringKrullDim_le_iff_height_le]
    intro P hP
    rw [← IsLocalization.height_under (Submonoid.powers f) P]
    exact Ideal.height_le_ringKrullDim_of_isPrime
  · obtain ⟨m, hm, hfm⟩ : ∃ m : Ideal R, m.IsMaximal ∧ f ∉ m := by
      by_contra hcon
      push Not at hcon
      have _ : IsJacobsonRing R := isJacobsonRing_of_finiteType (A := K)
      have hJ : f ∈ Ideal.jacobson (⊥ : Ideal R) :=
        Submodule.mem_sInf.mpr fun J hJ ↦ hcon J hJ.2
      rw [← Ideal.radical_eq_jacobson] at hJ
      have hnil : f ∈ nilradical R := hJ
      rw [nilradical_eq_zero R] at hnil
      exact hf (by simpa using hnil)
    have _ := hm.isPrime
    have hd : Disjoint (Submonoid.powers f : Set R) (m : Set R) :=
      (Ideal.disjoint_powers_iff_notMem_of_isPrime f).mpr hfm
    have _ := IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers f)
      (Localization.Away f) m hm.isPrime hd
    rw [← height_eq_ringKrullDim_of_isMaximal (K := K) R m,
      ← IsLocalization.height_map_of_disjoint (S := Localization.Away f) (Submonoid.powers f) m hd]
    exact Ideal.height_le_ringKrullDim_of_isPrime
end Affine

/-! ### Cotangent spaces and localisation -/

section Cotangent

variable {R : Type*} [CommRing R]

/-- `m ^ 2` is `m`-primary, elementarily: if `s ∉ m` and `s * x ∈ m ^ 2` then `x ∈ m ^ 2`.
Write `1 = y * s + w` with `w ∈ m` and expand `x = y * (s * x) + w * x`. -/
theorem mem_sq_of_notMem_of_mul_mem_sq {m : Ideal R} (hm : m.IsMaximal) {s x : R}
    (hs : s ∉ m) (h : s * x ∈ m ^ 2) : x ∈ m ^ 2 := by
  have _ := hm.isPrime
  have hx : x ∈ m :=
    (Ideal.IsPrime.mem_or_mem ‹m.IsPrime› (Ideal.pow_le_self two_ne_zero h)).resolve_left hs
  obtain ⟨y, w, hw, hyw⟩ := hm.exists_inv hs
  have hx' : x = y * (s * x) + w * x := by
    conv_lhs => rw [← one_mul x, ← hyw]
    ring
  have h2 : s * x ∈ m * m := by rwa [← pow_two]
  rw [hx', pow_two]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h2) (Ideal.mul_mem_mul hw hx)

/-- An ideal `I` that is saturated at a prime `m` (multiplying by an element outside `m` does not
create membership) is its own contraction from `R_m`. -/
theorem mem_of_algebraMap_mem_map_atPrime (m : Ideal R) [m.IsPrime] {I : Ideal R}
    (hI : ∀ s x : R, s ∉ m → s * x ∈ I → x ∈ I) {x : R}
    (h : algebraMap R (Localization.AtPrime m) x ∈
      I.map (algebraMap R (Localization.AtPrime m))) : x ∈ I := by
  rw [IsLocalization.mem_map_algebraMap_iff m.primeCompl] at h
  obtain ⟨⟨⟨y, hy⟩, ⟨s, hs⟩⟩, hxy⟩ := h
  simp only [← map_mul] at hxy
  rw [IsLocalization.eq_iff_exists m.primeCompl] at hxy
  obtain ⟨⟨c, hc⟩, hcx⟩ := hxy
  simp only at hcx hs hc hy
  refine hI (c * s) x (fun hmem ↦ ?_) ?_
  · rcases ‹m.IsPrime›.mem_or_mem hmem with h | h
    · exact hc h
    · exact hs h
  · have heq : c * s * x = c * y := by rw [← hcx]; ring
    rw [heq]
    exact Ideal.mul_mem_left _ _ hy

/-- The residue field of `R` at a maximal ideal `m` is the residue field of `R_m`: the map
`R ⧸ m → κ(R_m)` is bijective.  It is injective because `R ⧸ m` is a field, and surjective
because the image is a subfield containing `a / s` for every `a` and every `s ∉ m`. -/
theorem bijective_residueLift_localization_atPrime (m : Ideal R) [m.IsMaximal]
    (hker : ∀ a ∈ m, ((IsLocalRing.residue (Localization.AtPrime m)).comp
      (algebraMap R (Localization.AtPrime m))) a = 0) :
    Function.Bijective (Ideal.Quotient.lift m
      ((IsLocalRing.residue (Localization.AtPrime m)).comp
        (algebraMap R (Localization.AtPrime m))) hker) := by
  have hm : m.IsMaximal := ‹_›
  have _ := hm.isPrime
  let _ : Field (R ⧸ m) := Ideal.Quotient.field m
  set i := Ideal.Quotient.lift m ((IsLocalRing.residue (Localization.AtPrime m)).comp
    (algebraMap R (Localization.AtPrime m))) hker with hi
  have hinj : Function.Injective i := i.injective
  refine ⟨hinj, ?_⟩
  intro w
  obtain ⟨z, rfl⟩ := IsLocalRing.residue_surjective w
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective m.primeCompl z
  have hsne : Ideal.Quotient.mk m (s : R) ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact s.2
  have hne : i (Ideal.Quotient.mk m (s : R)) ≠ 0 := fun h ↦ hsne (hinj (by simpa using h))
  refine ⟨Ideal.Quotient.mk m a / Ideal.Quotient.mk m (s : R), ?_⟩
  rw [map_div₀, div_eq_iff hne, hi]
  simp only [Ideal.Quotient.lift_mk, RingHom.coe_comp, Function.comp_apply]
  rw [← map_mul, IsLocalization.mk'_spec]

/-- **The cotangent space is already local**: `m ⧸ m²` maps isomorphically onto `𝔪 ⧸ 𝔪²` for
`𝔪` the maximal ideal of `R_m`.  Injectivity is `mem_sq_of_notMem_of_mul_mem_sq`; surjectivity
replaces `y / s ∈ 𝔪` by `y * t` with `t * s ≡ 1 mod m`, the error `y * (1 - t * s)` lying
in `m ^ 2`. -/
theorem bijective_mapCotangent_localization_atPrime (m : Ideal R) [m.IsMaximal]
    (hle : m ≤ (IsLocalRing.maximalIdeal (Localization.AtPrime m)).comap
      (Algebra.ofId R (Localization.AtPrime m))) :
    Function.Bijective (Ideal.mapCotangent m
      (IsLocalRing.maximalIdeal (Localization.AtPrime m))
      (Algebra.ofId R (Localization.AtPrime m)) hle) := by
  have hm : m.IsMaximal := ‹_›
  have _ := hm.isPrime
  have hmax : Ideal.map (algebraMap R (Localization.AtPrime m)) m =
      IsLocalRing.maximalIdeal (Localization.AtPrime m) := Localization.AtPrime.map_eq_maximalIdeal
  have hsq : IsLocalRing.maximalIdeal (Localization.AtPrime m) ^ 2 =
      Ideal.map (algebraMap R (Localization.AtPrime m)) (m ^ 2) := by
    rw [Ideal.map_pow, hmax]
  constructor
  · rw [injective_iff_map_eq_zero]
    intro v hv
    obtain ⟨⟨x, hx⟩, rfl⟩ := m.toCotangent_surjective v
    rw [Ideal.mapCotangent_toCotangent, Ideal.toCotangent_eq_zero, hsq] at hv
    rw [Ideal.toCotangent_eq_zero]
    exact mem_of_algebraMap_mem_map_atPrime m
      (fun s y hs hsy ↦ mem_sq_of_notMem_of_mul_mem_sq hm hs hsy) hv
  · intro w
    obtain ⟨⟨z, hz⟩, rfl⟩ :=
      (IsLocalRing.maximalIdeal (Localization.AtPrime m)).toCotangent_surjective w
    rw [← hmax, IsLocalization.mem_map_algebraMap_iff m.primeCompl] at hz
    obtain ⟨⟨⟨y, hy⟩, ⟨s, hs⟩⟩, hzy⟩ := hz
    simp only at hzy hy hs
    obtain ⟨t, u, hu, htu⟩ := hm.exists_inv hs
    refine ⟨m.toCotangent ⟨y * t, Ideal.mul_mem_right _ _ hy⟩, ?_⟩
    rw [Ideal.mapCotangent_toCotangent, Ideal.toCotangent_eq, hsq]
    have hunit : IsUnit (algebraMap R (Localization.AtPrime m) s) :=
      IsLocalization.map_units _ ⟨s, hs⟩
    rw [← Ideal.unit_mul_mem_iff_mem _ hunit]
    have key : algebraMap R (Localization.AtPrime m) s *
        ((Algebra.ofId R (Localization.AtPrime m)) (y * t) - z) =
        algebraMap R (Localization.AtPrime m) (-(y * u)) := by
      simp only [Algebra.ofId_apply, map_mul, map_neg]
      rw [mul_sub]
      rw [show algebraMap R (Localization.AtPrime m) s * (algebraMap R (Localization.AtPrime m) y *
        algebraMap R (Localization.AtPrime m) t) =
        algebraMap R (Localization.AtPrime m) y * algebraMap R (Localization.AtPrime m) (t * s)
        by rw [map_mul]; ring]
      rw [show t * s = 1 - u from eq_sub_of_add_eq htu]
      rw [mul_comm (algebraMap R (Localization.AtPrime m) s) z, hzy]
      simp [map_sub, mul_sub]
    rw [key]
    exact Ideal.mem_map_of_mem _ (neg_mem (pow_two m ▸ Ideal.mul_mem_mul hy hu))

/-- The Zariski cotangent space of the local ring at a maximal ideal `m` is `m ⧸ m²` over
`R ⧸ m`: its dimension can be computed in `R`.  No Noetherian hypothesis is needed. -/
theorem finrank_cotangentSpace_localization_atPrime (m : Ideal R) [m.IsMaximal] :
    Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime m))
        (IsLocalRing.CotangentSpace (Localization.AtPrime m)) =
      Module.finrank (R ⧸ m) m.Cotangent := by
  have hm : m.IsMaximal := ‹_›
  have _ := hm.isPrime
  have hmax : Ideal.map (algebraMap R (Localization.AtPrime m)) m =
      IsLocalRing.maximalIdeal (Localization.AtPrime m) := Localization.AtPrime.map_eq_maximalIdeal
  have hle : m ≤ (IsLocalRing.maximalIdeal (Localization.AtPrime m)).comap
      (Algebra.ofId R (Localization.AtPrime m)) := by
    intro a ha
    rw [Ideal.mem_comap, Algebra.ofId_apply, ← hmax]
    exact Ideal.mem_map_of_mem _ ha
  have hker : ∀ a ∈ m, ((IsLocalRing.residue (Localization.AtPrime m)).comp
      (algebraMap R (Localization.AtPrime m))) a = 0 := by
    intro a ha
    have hmem := hle ha
    rw [Ideal.mem_comap, Algebra.ofId_apply] at hmem
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  have hibij := bijective_residueLift_localization_atPrime m hker
  have hφbij := bijective_mapCotangent_localization_atPrime m hle
  have key : Module.rank (R ⧸ m) m.Cotangent
      = Module.rank (IsLocalRing.ResidueField (Localization.AtPrime m))
        (IsLocalRing.CotangentSpace (Localization.AtPrime m)) := by
    refine rank_eq_of_equiv_equiv
      (i := ⇑(Ideal.Quotient.lift m ((IsLocalRing.residue (Localization.AtPrime m)).comp
        (algebraMap R (Localization.AtPrime m))) hker))
      (j := AddEquiv.ofBijective _ hφbij) hibij ?_
    intro r v
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
    have hsmul : Ideal.Quotient.mk m a • v = a • v :=
      IsScalarTower.algebraMap_smul (R ⧸ m) a v
    simp only [AddEquiv.ofBijective_apply, Ideal.Quotient.lift_mk, RingHom.coe_comp,
      Function.comp_apply, hsmul, map_smul]
    symm
    calc IsLocalRing.residue (Localization.AtPrime m) (algebraMap R (Localization.AtPrime m) a) •
          (Ideal.mapCotangent m (IsLocalRing.maximalIdeal (Localization.AtPrime m))
            (Algebra.ofId R (Localization.AtPrime m)) hle) v
        = algebraMap R (Localization.AtPrime m) a •
          (Ideal.mapCotangent m (IsLocalRing.maximalIdeal (Localization.AtPrime m))
            (Algebra.ofId R (Localization.AtPrime m)) hle) v :=
          IsScalarTower.algebraMap_smul _ _ _
      _ = a • (Ideal.mapCotangent m (IsLocalRing.maximalIdeal (Localization.AtPrime m))
            (Algebra.ofId R (Localization.AtPrime m)) hle) v :=
          IsScalarTower.algebraMap_smul _ _ _
  exact congrArg Cardinal.toNat key.symm

/-! ### Changing the scalars on `m ⧸ m²` -/

section Scalars

variable {S : Type*} [Field S] [Algebra S R] (m : Ideal R)

/-- The action of the residue field on `m ⧸ m²` restricts along `S → R ⧸ m` to the action of
the base field. -/
theorem algebraMap_smul_cotangent (c : S) (y : Ideal.Cotangent m) :
    (algebraMap S (R ⧸ m)) c • y = c • y := by
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ y
  show (algebraMap S (R ⧸ m)) c • Ideal.toCotangent m z = c • Ideal.toCotangent m z
  rw [IsScalarTower.algebraMap_apply S R (R ⧸ m) c, IsScalarTower.algebraMap_smul,
    ← map_smul (Ideal.toCotangent m), ← algebra_compatible_smul R c z]
  rfl

/-- If the residue field `R ⧸ m` is generated by the base field `S` — as at a rational point —
then the dimension of `m ⧸ m²` may be computed over `S`. -/
theorem finrank_cotangent_eq_of_surjective
    (h : Function.Surjective (algebraMap S (R ⧸ m))) [Nontrivial (R ⧸ m)] :
    Module.finrank (R ⧸ m) (Ideal.Cotangent m) = Module.finrank S (Ideal.Cotangent m) :=
  congrArg Cardinal.toNat (rank_eq_of_equiv_equiv (algebraMap S (R ⧸ m))
    (AddEquiv.refl (Ideal.Cotangent m)) ⟨(algebraMap S (R ⧸ m)).injective, h⟩
    fun c y => (algebraMap_smul_cotangent m c y).symm).symm

end Scalars

end Cotangent

end Height.Toolbox
