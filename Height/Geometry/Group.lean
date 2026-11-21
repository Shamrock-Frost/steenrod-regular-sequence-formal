import Height.Toolbox.Monoidal
import Height.Geometry.Spec
import Mathlib.RingTheory.HopfAlgebra.Quotient
import Mathlib.RingTheory.HopfAlgebra.Convolution
import Mathlib.AlgebraicGeometry.Group.Affine

/-!
# Affine group schemes and their actions, from coordinates

Mathlib makes `Spec A` over `Spec K` a group object
for every `K`-Hopf algebra `A` (`AlgebraicGeometry/Group/Affine.lean`,
`instGrpObjSpecAsOverSpec`) and
gives `Bialgebra.ofAlgHom`, `Ideal.IsHopfIdeal` and the quotient Hopf algebra.  This file
is the classical interface to that: a group cut out by an ideal `I` of a polynomial ring
with polynomial multiplication, inverse and unit is presented by `GroupPresentation`; its
fields are the Hopf axioms as identities of algebra maps out of `K[γ] ⧸ I`, which consumers
check on generators (`MvPolynomial.algHom_ext`, `Ideal.Quotient.algHom_ext`), never on
`K`-points — so no geometric reducedness is needed.  An action is an `ActionPresentation`,
a coaction of the Hopf algebra on the coordinate ring of the space; from it the module
object of `Spec.lean` §4 is built through full faithfulness of `Spec`.  The pair model of
`GL_n` (`(g, h)` with `gh = hg = 1`) and its closed subgroups (centralisers, Borels) are
the instances the consumers supply.

**Convention of `ActionPresentation.coassoc_coact`.**  `ModObj` is a *left*
action, and mathlib's product on `Spec A` is the convolution `(g * h)(x) = Σ g(x₁) h(x₂)`;
so the coaction of a left action is a comodule over the **co-opposite** bialgebra, i.e.
`coassoc_coact` carries `Algebra.TensorProduct.comm ∘ P.comul` on its right-hand side.  The
plain right-comodule law (no flip) presents a *right* action, and no `ModObj` follows from
it without the missing lemma below.  With the flip, `actPt` is a left action of `pts`:
`actPt (mulPt a b) x = actPt a (actPt b x)` (`mulPt_assoc`, `sec_actPt`).

**A missing mathlib lemma, and a mathlib candidate.**  The antipode of a commutative Hopf
algebra is a *coalgebra anti-morphism*:
```
theorem HopfAlgebra.comul_comp_antipode {R A} [CommSemiring R] [CommSemiring A]
    [HopfAlgebra R A] :
    Coalgebra.comul ∘ₗ HopfAlgebra.antipode R
      = LinearMap.map (antipode R) (antipode R) ∘ₗ TensorProduct.comm R A A ∘ₗ Coalgebra.comul
```
`RingTheory/HopfAlgebra/Convolution.lean` sets this up — its `local notation` fixes
`𝑭 := δ ∘ₗ 𝑺` and `𝑮 := (𝑺 ⊗ₘ 𝑺) ∘ₗ comm ∘ₗ δ` — and proves only the half
`LinearMap.comul_right_inv : toConv δ * toConv 𝑭 = 1`; the companion
`toConv 𝑮 * toConv δ = 1` and the conclusion `𝑭 = 𝑮` (uniqueness of convolution inverses in
`Hom(C, C ⊗ C)`) are absent, and `𝑮` is declared and never used.  With it, an
`ActionPresentation` in the plain right-comodule convention would also give a `ModObj`, by
the inverse-twisted action `(g, x) ↦ x · g⁻¹`.

The module-object transport itself (`Height.Toolbox.modObjObj`, the object-level `mapMod`
that `CategoryTheory/Monoidal/Mon.lean` lists as a TODO) is in `Toolbox/Monoidal.lean`.
-/

open MvPolynomial TensorProduct AlgebraicGeometry CategoryTheory MonoidalCategory Opposite
open Topology (IsConstructible)
open Height.Toolbox (modObjObj)

-- `A.CoordRing ⊗[K] (P.CoordRing ⊗[K] P.CoordRing)` needs one more level of pending synthesis
-- than the default.
set_option maxSynthPendingDepth 4

namespace Height.Geometry

universe u

variable {K : Type u} [Field K] {γ ι : Type u}

/-- `Spec` on `(CommAlgCat K)ᵒᵖ` as a braided monoidal functor.  Instance search does not
find mathlib's `braidedAlgSpec` through the reducible `algSpec`, so it is named. -/
noncomputable instance instBraidedAlgSpec :
    (algSpec (CommRingCat.of K)).Braided := AlgebraicGeometry.braidedAlgSpec

/-! ### Sections of an affine scheme over `Spec K`

A section of `(Spec R).asOver (Spec K)` over `Spec K` is `Spec` of a `K`-algebra map
`R →ₐ[K] K`; a pair of sections is `Spec` of `Algebra.TensorProduct.lift` of the two, read
through `pullbackSpecIso`.  This is the bridge from the `K`-point dictionary of `pts` to
the sections `Spec.lean` §4 quantifies over. -/

/-- The section of `(Spec R).asOver (Spec K)` at an algebra map `R →ₐ[K] K`. -/
noncomputable def secOfAlgHom {R : Type u} [CommRing R] [Algebra K R] (f : R →ₐ[K] K) :
    𝟙_ (Over (Spec (.of K))) ⟶ (Spec (.of R)).asOver (Spec (.of K)) :=
  Over.homMk (Spec.map (CommRingCat.ofHom f.toRingHom)) (by
    show Spec.map (CommRingCat.ofHom f.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K R)) = 𝟙 _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id (CommRingCat.of K)]
    congr 1
    exact CommRingCat.hom_ext (RingHom.ext fun r => f.commutes r))

@[simp] theorem secOfAlgHom_left {R : Type u} [CommRing R] [Algebra K R] (f : R →ₐ[K] K) :
    (secOfAlgHom f).left = Spec.map (CommRingCat.ofHom f.toRingHom) := rfl

/-- **The pair of two sections, read on the tensor product**: the section of
`Spec R ×_{Spec K} Spec S` given by `f` and `g` is `Spec` of `Algebra.TensorProduct.lift f g`
(`pullbackSpecIso_inv_fst`, `pullbackSpecIso_inv_snd`). -/
theorem lift_secOfAlgHom {R S : Type u} [CommRing R] [Algebra K R] [CommRing S] [Algebra K S]
    (f : R →ₐ[K] K) (g : S →ₐ[K] K) :
    (CartesianMonoidalCategory.lift (secOfAlgHom f) (secOfAlgHom g)).left ≫
        (pullbackSpecIso K R S).hom
      = Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)).toRingHom) := by
  refine (Iso.eq_comp_inv _).mp (Limits.pullback.hom_ext ?_ ?_)
  · have h : (CartesianMonoidalCategory.lift (secOfAlgHom f) (secOfAlgHom g)).left ≫
        Limits.pullback.fst _ _ = (secOfAlgHom f).left :=
      congrArg Over.Hom.left (CartesianMonoidalCategory.lift_fst _ _)
    have hfst : (pullbackSpecIso K R S).inv ≫ Limits.pullback.fst
        ((Spec (.of R)).asOver (Spec (.of K))).hom ((Spec (.of S)).asOver (Spec (.of K))).hom
        = Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeftRingHom (A := R) (B := S) (R := K))) :=
      pullbackSpecIso_inv_fst K R S
    rw [h, Category.assoc]
    refine Eq.trans ?_ (congrArg (fun t => Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)).toRingHom) ≫ t) hfst.symm)
    refine Eq.trans ?_ (Spec.map_comp _ _)
    rw [← CommRingCat.ofHom_comp, secOfAlgHom_left]
    congr 2
    exact RingHom.ext fun x => by simp
  · have h : (CartesianMonoidalCategory.lift (secOfAlgHom f) (secOfAlgHom g)).left ≫
        Limits.pullback.snd _ _ = (secOfAlgHom g).left :=
      congrArg Over.Hom.left (CartesianMonoidalCategory.lift_snd _ _)
    have hsnd : (pullbackSpecIso K R S).inv ≫ Limits.pullback.snd
        ((Spec (.of R)).asOver (Spec (.of K))).hom ((Spec (.of S)).asOver (Spec (.of K))).hom
        = Spec.map (CommRingCat.ofHom (R := CommRingCat.of S) (S := CommRingCat.of (R ⊗[K] S))
          (RingHomClass.toRingHom (Algebra.TensorProduct.includeRight (A := R) (B := S)))) :=
      pullbackSpecIso_inv_snd K R S
    rw [h, Category.assoc]
    refine Eq.trans ?_ (congrArg (fun t => Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)).toRingHom) ≫ t) hsnd.symm)
    refine Eq.trans ?_ (Spec.map_comp _ _)
    rw [← CommRingCat.ofHom_comp, secOfAlgHom_left]
    congr 2
    exact RingHom.ext fun x => by simp

/-- **The algebra map of a section**: `Spec` is fully faithful, so a section of
`(Spec R).asOver (Spec K)` is `Spec` of a ring map `R → K`, and being a morphism over
`Spec K` makes that map a `K`-algebra map. -/
private noncomputable def algHomOfSecAux {R : Type u} [CommRing R] [Algebra K R]
    (m : Spec (.of K) ⟶ Spec (.of R))
    (hm : m ≫ Spec.map (CommRingCat.ofHom (algebraMap K R)) = 𝟙 (Spec (CommRingCat.of K))) :
    R →ₐ[K] K :=
  { (Spec.preimage m).hom with
    commutes' := by
      intro r
      have h2 : CommRingCat.ofHom (algebraMap K R) ≫ Spec.preimage m =
          𝟙 (CommRingCat.of K) := by
        rw [← Spec.preimage_map (CommRingCat.ofHom (algebraMap K R)), ← Spec.preimage_comp, hm,
          Spec.preimage_id]
      exact congrArg (fun φ : CommRingCat.of K ⟶ CommRingCat.of K => φ r) h2 }

noncomputable def algHomOfSec {R : Type u} [CommRing R] [Algebra K R]
    (s : 𝟙_ (Over (Spec (.of K))) ⟶ (Spec (.of R)).asOver (Spec (.of K))) : R →ₐ[K] K :=
  algHomOfSecAux s.left (Over.w s)

/-- **Sections are algebra maps** (`secOfAlgHom` and `algHomOfSec` are inverse). -/
@[simp] theorem secOfAlgHom_algHomOfSec {R : Type u} [CommRing R] [Algebra K R]
    (s : 𝟙_ (Over (Spec (.of K))) ⟶ (Spec (.of R)).asOver (Spec (.of K))) :
    secOfAlgHom (algHomOfSec s) = s :=
  Over.OverMorphism.ext (Spec.map_preimage _)

@[simp] theorem algHomOfSec_secOfAlgHom {R : Type u} [CommRing R] [Algebra K R]
    (f : R →ₐ[K] K) : algHomOfSec (secOfAlgHom f) = f := by
  refine AlgHom.ext fun r => ?_
  show (Spec.preimage (Spec.map (CommRingCat.ofHom f.toRingHom))).hom r = f r
  rw [Spec.preimage_map]
  rfl

/-! ### Commutative Hopf data as algebra maps -/

/-- A commutative Hopf algebra structure on a `K`-algebra `A`, given by algebra maps: the
hypotheses of `Bialgebra.ofAlgHom` and the two antipode laws.  (Mathlib states the Hopf
axioms for linear maps; for commutative `A` the antipode is an algebra map.) -/
structure CommHopfData (K : Type u) [Field K] (A : Type u) [CommRing A] [Algebra K A] where
  comul : A →ₐ[K] A ⊗[K] A
  counit : A →ₐ[K] K
  antipode : A →ₐ[K] A
  coassoc : (Algebra.TensorProduct.assoc K K K A A A).toAlgHom.comp
      ((Algebra.TensorProduct.map comul (.id K A)).comp comul)
    = (Algebra.TensorProduct.map (.id K A) comul).comp comul
  rTensor_counit : (Algebra.TensorProduct.map counit (.id K A)).comp comul
    = (Algebra.TensorProduct.lid K A).symm
  lTensor_counit : (Algebra.TensorProduct.map (.id K A) counit).comp comul
    = (Algebra.TensorProduct.rid K K A).symm
  mul_antipode_rTensor : (Algebra.TensorProduct.lmul' K).comp
      ((Algebra.TensorProduct.map antipode (.id K A)).comp comul)
    = (Algebra.ofId K A).comp counit
  mul_antipode_lTensor : (Algebra.TensorProduct.lmul' K).comp
      ((Algebra.TensorProduct.map (.id K A) antipode).comp comul)
    = (Algebra.ofId K A).comp counit

/-- The bialgebra of Hopf data (mathlib's constructor). -/
noncomputable abbrev CommHopfData.toBialgebra {A : Type u} [CommRing A] [Algebra K A]
    (H : CommHopfData K A) : Bialgebra K A :=
  Bialgebra.ofAlgHom H.comul H.counit H.coassoc H.rTensor_counit H.lTensor_counit

/-- **The Hopf algebra of Hopf data.**  The bialgebra is `toBialgebra`
(`Bialgebra.ofAlgHom`) and the antipode is `H.antipode`; mathlib's
`HopfAlgebra.ofAlgHom` asks for the two antipode laws with
`Algebra.TensorProduct.lift antipode (.id K A)` where the fields use
`(Algebra.TensorProduct.lmul' K).comp (Algebra.TensorProduct.map antipode (.id K A))`, and the
two agree by `Algebra.TensorProduct.lmul'_comp_map`. -/
@[instance_reducible]
noncomputable def CommHopfData.toHopfAlgebra {A : Type u} [CommRing A] [Algebra K A]
    (H : CommHopfData K A) : HopfAlgebra K A :=
  letI : Bialgebra K A := H.toBialgebra
  HopfAlgebra.ofAlgHom H.antipode
    (by rw [← Algebra.TensorProduct.lmul'_comp_map]; exact H.mul_antipode_rTensor)
    (by rw [← Algebra.TensorProduct.lmul'_comp_map]; exact H.mul_antipode_lTensor)

/-- **A polynomial identity is a congruence modulo any ideal.**  The laws of
`GroupPresentation.ofLaws` and `ActionPresentation.ofLaws` are congruences; this is the shape
in which a law that holds on the nose is supplied. -/
theorem sub_mem_of_eq {R : Type*} [CommRing R] {J : Ideal R} {f g : R} (h : f = g) :
    f - g ∈ J := by
  rw [h, sub_self]
  exact J.zero_mem

/-- **Transport of ideal membership along a polynomial identity**: the shape in which a law
that holds only modulo a relation is supplied to `ofLaws`. -/
theorem mem_ideal_of_eq {R : Type*} [CommRing R] {J : Ideal R} {f g : R} (h : f = g)
    (hg : g ∈ J) : f ∈ J := by
  rw [h]
  exact hg

/-- **An identity of algebra maps out of `K[σ] ⧸ I` may be checked on the generators `X i`**
(`Ideal.Quotient.algHom_ext` after `MvPolynomial.algHom_ext`).  This is how a consumer
discharges the Hopf axioms of a `GroupPresentation` and the comodule laws of an
`ActionPresentation`: never on `K`-points, so no geometric reducedness is needed. -/
theorem quotAlgHom_ext {σ : Type u} {I : Ideal (MvPolynomial σ K)} {B : Type u} [CommRing B]
    [Algebra K B] {f g : (MvPolynomial σ K ⧸ I) →ₐ[K] B}
    (h : ∀ i, f (Ideal.Quotient.mk I (X i)) = g (Ideal.Quotient.mk I (X i))) : f = g :=
  Ideal.Quotient.algHom_ext K (MvPolynomial.algHom_ext h)

/-! ### Coordinates in two blocks

An ideal of `K[γ ⊕ δ]` generated by one ideal in each block of coordinates.  This is the
coordinate ring of a product of groups (`GroupData.prod`) and of a product of spaces
(`ActionData.prod`, `ActionData.prodLeft`); nothing here mentions group laws.  The two
block maps `sumMkL`, `sumMkR` jointly detect identities of algebra maps out of the quotient
(`sumAlgHom_ext`) — the input of `CommHopfData.ofPair` and of the comodule laws of a
product action. -/

section SumIdeal

variable {δ : Type u}

variable (I : Ideal (MvPolynomial γ K)) (J : Ideal (MvPolynomial δ K))

/-- The ideal of `K[γ ⊕ δ]` generated by an ideal in each block of coordinates. -/
noncomputable def sumIdeal : Ideal (MvPolynomial (γ ⊕ δ) K) :=
  I.map (rename Sum.inl) ⊔ J.map (rename Sum.inr)

/-- A map killing both blocks kills the whole ideal. -/
theorem sumIdeal_apply_eq_zero {R : Type u} [CommRing R] [Algebra K R]
    (φ : MvPolynomial (γ ⊕ δ) K →ₐ[K] R)
    (hI : ∀ g ∈ I, φ (rename Sum.inl g) = 0)
    (hJ : ∀ g ∈ J, φ (rename Sum.inr g) = 0) {f : MvPolynomial (γ ⊕ δ) K}
    (hf : f ∈ sumIdeal I J) : φ f = 0 := by
  have h : sumIdeal I J ≤ RingHom.ker (φ : MvPolynomial (γ ⊕ δ) K →+* R) :=
    sup_le
      (Ideal.map_le_iff_le_comap.2 fun g hg =>
        Ideal.mem_comap.2 (RingHom.mem_ker.2 (hI g hg)))
      (Ideal.map_le_iff_le_comap.2 fun g hg =>
        Ideal.mem_comap.2 (RingHom.mem_ker.2 (hJ g hg)))
  exact RingHom.mem_ker.1 (h hf)

variable {I J}

theorem renameL_mem_sumIdeal {g : MvPolynomial γ K} (hg : g ∈ I) :
    rename Sum.inl g ∈ sumIdeal I J :=
  Submodule.mem_sup_left (Ideal.mem_map_of_mem _ hg)

theorem renameR_mem_sumIdeal {g : MvPolynomial δ K} (hg : g ∈ J) :
    rename Sum.inr g ∈ sumIdeal I J :=
  Submodule.mem_sup_right (Ideal.mem_map_of_mem _ hg)

variable (I J)

/-- The first block of coordinates, as a map of quotients. -/
noncomputable def sumMkL :
    (MvPolynomial γ K ⧸ I) →ₐ[K] MvPolynomial (γ ⊕ δ) K ⧸ sumIdeal I J :=
  Ideal.Quotient.liftₐ I ((Ideal.Quotient.mkₐ K (sumIdeal I J)).comp (rename Sum.inl))
    (fun _ hg => Ideal.Quotient.eq_zero_iff_mem.2 (renameL_mem_sumIdeal hg))

/-- The second block of coordinates, as a map of quotients. -/
noncomputable def sumMkR :
    (MvPolynomial δ K ⧸ J) →ₐ[K] MvPolynomial (γ ⊕ δ) K ⧸ sumIdeal I J :=
  Ideal.Quotient.liftₐ J ((Ideal.Quotient.mkₐ K (sumIdeal I J)).comp (rename Sum.inr))
    (fun _ hg => Ideal.Quotient.eq_zero_iff_mem.2 (renameR_mem_sumIdeal hg))

@[simp] theorem sumMkL_mk (g : MvPolynomial γ K) :
    sumMkL I J (Ideal.Quotient.mk I g)
      = Ideal.Quotient.mk (sumIdeal I J) (rename Sum.inl g) := rfl

@[simp] theorem sumMkR_mk (g : MvPolynomial δ K) :
    sumMkR I J (Ideal.Quotient.mk J g)
      = Ideal.Quotient.mk (sumIdeal I J) (rename Sum.inr g) := rfl

/-- **An identity of algebra maps out of `K[γ ⊕ δ] ⧸ sumIdeal I J` is detected on the two
blocks of coordinates** (`quotAlgHom_ext`: the generators `X (inl i)` and `X (inr j)` are the
images of the generators of the two quotients). -/
theorem sumAlgHom_ext {B : Type u} [CommRing B] [Algebra K B]
    {φ ψ : (MvPolynomial (γ ⊕ δ) K ⧸ sumIdeal I J) →ₐ[K] B}
    (hL : φ.comp (sumMkL I J) = ψ.comp (sumMkL I J))
    (hR : φ.comp (sumMkR I J) = ψ.comp (sumMkR I J)) : φ = ψ := by
  refine quotAlgHom_ext fun k => ?_
  cases k with
  | inl i =>
      have h := AlgHom.congr_fun hL (Ideal.Quotient.mk I (X i))
      rwa [AlgHom.comp_apply, AlgHom.comp_apply, sumMkL_mk, rename_X] at h
  | inr j =>
      have h := AlgHom.congr_fun hR (Ideal.Quotient.mk J (X j))
      rwa [AlgHom.comp_apply, AlgHom.comp_apply, sumMkR_mk, rename_X] at h

@[simp] theorem sumIdeal_bot_bot :
    sumIdeal (⊥ : Ideal (MvPolynomial γ K)) (⊥ : Ideal (MvPolynomial δ K)) = ⊥ := by
  rw [sumIdeal, Ideal.map_bot, Ideal.map_bot, bot_sup_eq]

/-- **The zero locus of a two-block ideal is the product of the two zero loci.** -/
theorem zeroLocus_sumIdeal :
    MvPolynomial.zeroLocus K (sumIdeal I J)
      = {x : γ ⊕ δ → K | x ∘ Sum.inl ∈ MvPolynomial.zeroLocus K I
          ∧ x ∘ Sum.inr ∈ MvPolynomial.zeroLocus K J} := by
  ext x
  constructor
  · intro hx
    refine ⟨fun g hg => ?_, fun g hg => ?_⟩
    · have h := hx (rename Sum.inl g) (renameL_mem_sumIdeal hg)
      rwa [aeval_rename] at h
    · have h := hx (rename Sum.inr g) (renameR_mem_sumIdeal hg)
      rwa [aeval_rename] at h
  · rintro ⟨h1, h2⟩ f hf
    refine sumIdeal_apply_eq_zero I J (aeval x) (fun g hg => ?_) (fun g hg => ?_) hf
    · rw [aeval_rename]; exact h1 g hg
    · rw [aeval_rename]; exact h2 g hg

end SumIdeal

/-! ### Naturality of the monoidal structure of `⊗[K]` on algebras

Mathlib's `Algebra.TensorProduct.{assoc, comm, lid, rid, lmul'}` are the structure maps of the
monoidal category of commutative `K`-algebras, but their naturality squares are not stated as
lemmas for `AlgHom`s.  They are one-liners, and they are what makes a Hopf structure transfer
along an algebra map (`CommHopfData.ofSurjective`).  Mathlib candidates. -/

section Naturality

variable {B C D B' C' D' : Type u} [CommRing B] [Algebra K B] [CommRing C] [Algebra K C]
  [CommRing D] [Algebra K D] [CommRing B'] [Algebra K B'] [CommRing C'] [Algebra K C']
  [CommRing D'] [Algebra K D']

/-- Naturality of the associator of the tensor product of algebras. -/
theorem assoc_naturality (f : B →ₐ[K] B') (g : C →ₐ[K] C') (h : D →ₐ[K] D') :
    (Algebra.TensorProduct.assoc K K K B' C' D').toAlgHom.comp
        (Algebra.TensorProduct.map (Algebra.TensorProduct.map f g) h)
      = (Algebra.TensorProduct.map f (Algebra.TensorProduct.map g h)).comp
        (Algebra.TensorProduct.assoc K K K B C D).toAlgHom := by
  refine Algebra.TensorProduct.ext' fun w d => ?_
  induction w with
  | zero => simp
  | tmul a b => rfl
  | add p q hp hq => simp only [add_tmul, map_add, hp, hq]

/-- Naturality of the braiding of the tensor product of algebras. -/
theorem comm_naturality (f : B →ₐ[K] B') (g : C →ₐ[K] C') :
    (Algebra.TensorProduct.comm K B' C').toAlgHom.comp (Algebra.TensorProduct.map f g)
      = (Algebra.TensorProduct.map g f).comp (Algebra.TensorProduct.comm K B C).toAlgHom :=
  Algebra.TensorProduct.ext' fun _ _ => rfl

/-- Naturality of the left unitor. -/
theorem lid_symm_naturality (f : B →ₐ[K] B') :
    ((Algebra.TensorProduct.lid K B').symm : B' →ₐ[K] K ⊗[K] B').comp f
      = (Algebra.TensorProduct.map (AlgHom.id K K) f).comp
        ((Algebra.TensorProduct.lid K B).symm : B →ₐ[K] K ⊗[K] B) :=
  AlgHom.ext fun _ => rfl

/-- Naturality of the right unitor. -/
theorem rid_symm_naturality (f : B →ₐ[K] B') :
    ((Algebra.TensorProduct.rid K K B').symm : B' →ₐ[K] B' ⊗[K] K).comp f
      = (Algebra.TensorProduct.map f (AlgHom.id K K)).comp
        ((Algebra.TensorProduct.rid K K B).symm : B →ₐ[K] B ⊗[K] K) :=
  AlgHom.ext fun _ => rfl

/-- Naturality of the multiplication `A ⊗ A → A`. -/
theorem lmul'_naturality (f : B →ₐ[K] B') :
    f.comp (Algebra.TensorProduct.lmul' K) =
      (Algebra.TensorProduct.lmul' K).comp (Algebra.TensorProduct.map f f) :=
  Algebra.TensorProduct.ext' fun _ _ => by simp

/-- An algebra map is the identity on the base (`AlgHom.commutes`, as a composite). -/
theorem comp_ofId (f : B →ₐ[K] B') : f.comp (Algebra.ofId K B) = Algebra.ofId K B' :=
  AlgHom.ext fun r => f.commutes r

/-- **An identity of algebra maps may be tested after a surjection.** -/
theorem algHom_ext_of_surjective (π : B →ₐ[K] C) (hπ : Function.Surjective π)
    {φ ψ : C →ₐ[K] D} (h : φ.comp π = ψ.comp π) : φ = ψ :=
  AlgHom.ext fun z => by
    obtain ⟨u, rfl⟩ := hπ z
    exact congrArg (fun t : B →ₐ[K] D => t u) h

end Naturality

section OfSurjective

variable {A B : Type u} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
  {comul : B →ₐ[K] B ⊗[K] B} {counit : B →ₐ[K] K} {antipode : B →ₐ[K] B}

/-! Each Hopf axiom for `comul`, `counit`, `antipode` on `B`, *tested after* an algebra map
`π : A →ₐ B` along which they intertwine the Hopf data of `A`, is that data's axiom carried
by `π` through the naturality of `assoc`, `lid`, `rid` and `lmul'`.  Hopf data on `B`
follows as soon as enough such `π` are present to detect identities of algebra maps out of
`B`: one surjective `π` (`CommHopfData.ofSurjective`, the coordinate ring of a closed
subgroup) or a pair of them with jointly generating images (`CommHopfData.ofPair`, the
coordinate ring of a product of groups). -/

private theorem coassoc_comp_of (H : CommHopfData K A) (π : A →ₐ[K] B)
    (hcomul : comul.comp π = (Algebra.TensorProduct.map π π).comp H.comul) :
    ((Algebra.TensorProduct.assoc K K K B B B).toAlgHom.comp
        ((Algebra.TensorProduct.map comul (AlgHom.id K B)).comp comul)).comp π
      = ((Algebra.TensorProduct.map (AlgHom.id K B) comul).comp comul).comp π := by
  have hc : ∀ x : A, comul (π x) = Algebra.TensorProduct.map π π (H.comul x) :=
    fun x => AlgHom.congr_fun hcomul x
  have h1 : ∀ t : A ⊗[K] A,
      Algebra.TensorProduct.map comul (AlgHom.id K B) (Algebra.TensorProduct.map π π t)
        = Algebra.TensorProduct.map (Algebra.TensorProduct.map π π) π
          (Algebra.TensorProduct.map H.comul (AlgHom.id K A) t) := by
    have e : (Algebra.TensorProduct.map comul (AlgHom.id K B)).comp
          (Algebra.TensorProduct.map π π)
        = (Algebra.TensorProduct.map (Algebra.TensorProduct.map π π) π).comp
          (Algebra.TensorProduct.map H.comul (AlgHom.id K A)) := by
      rw [← Algebra.TensorProduct.map_comp, ← Algebra.TensorProduct.map_comp, hcomul]
      rfl
    exact fun t => AlgHom.congr_fun e t
  have h2 : ∀ t : A ⊗[K] A,
      Algebra.TensorProduct.map (AlgHom.id K B) comul (Algebra.TensorProduct.map π π t)
        = Algebra.TensorProduct.map π (Algebra.TensorProduct.map π π)
          (Algebra.TensorProduct.map (AlgHom.id K A) H.comul t) := by
    have e : (Algebra.TensorProduct.map (AlgHom.id K B) comul).comp
          (Algebra.TensorProduct.map π π)
        = (Algebra.TensorProduct.map π (Algebra.TensorProduct.map π π)).comp
          (Algebra.TensorProduct.map (AlgHom.id K A) H.comul) := by
      rw [← Algebra.TensorProduct.map_comp, ← Algebra.TensorProduct.map_comp, hcomul]
      rfl
    exact fun t => AlgHom.congr_fun e t
  have hasn : ∀ s : (A ⊗[K] A) ⊗[K] A,
      (Algebra.TensorProduct.assoc K K K B B B).toAlgHom
          (Algebra.TensorProduct.map (Algebra.TensorProduct.map π π) π s)
        = Algebra.TensorProduct.map π (Algebra.TensorProduct.map π π)
          ((Algebra.TensorProduct.assoc K K K A A A).toAlgHom s) :=
    fun s => AlgHom.congr_fun (assoc_naturality π π π) s
  have hco : ∀ x : A,
      (Algebra.TensorProduct.assoc K K K A A A).toAlgHom
          (Algebra.TensorProduct.map H.comul (AlgHom.id K A) (H.comul x))
        = Algebra.TensorProduct.map (AlgHom.id K A) H.comul (H.comul x) :=
    fun x => AlgHom.congr_fun H.coassoc x
  refine AlgHom.ext fun a => ?_
  show (Algebra.TensorProduct.assoc K K K B B B).toAlgHom
      (Algebra.TensorProduct.map comul (AlgHom.id K B) (comul (π a)))
    = Algebra.TensorProduct.map (AlgHom.id K B) comul (comul (π a))
  rw [hc a, h1 (H.comul a), hasn _, hco a, ← h2 (H.comul a)]

private theorem rTensor_counit_comp_of (H : CommHopfData K A) (π : A →ₐ[K] B)
    (hcomul : comul.comp π = (Algebra.TensorProduct.map π π).comp H.comul)
    (hcounit : counit.comp π = H.counit) :
    ((Algebra.TensorProduct.map counit (AlgHom.id K B)).comp comul).comp π
      = ((Algebra.TensorProduct.lid K B).symm : B →ₐ[K] K ⊗[K] B).comp π := by
  have hc : ∀ x : A, comul (π x) = Algebra.TensorProduct.map π π (H.comul x) :=
    fun x => AlgHom.congr_fun hcomul x
  have h4 : ∀ t : A ⊗[K] A,
      Algebra.TensorProduct.map counit (AlgHom.id K B) (Algebra.TensorProduct.map π π t)
        = Algebra.TensorProduct.map (AlgHom.id K K) π
          (Algebra.TensorProduct.map H.counit (AlgHom.id K A) t) := by
    have e : (Algebra.TensorProduct.map counit (AlgHom.id K B)).comp
          (Algebra.TensorProduct.map π π)
        = (Algebra.TensorProduct.map (AlgHom.id K K) π).comp
          (Algebra.TensorProduct.map H.counit (AlgHom.id K A)) := by
      rw [← Algebra.TensorProduct.map_comp, ← Algebra.TensorProduct.map_comp, hcounit]
      rfl
    exact fun t => AlgHom.congr_fun e t
  have hrt : ∀ x : A, Algebra.TensorProduct.map H.counit (AlgHom.id K A) (H.comul x)
      = ((Algebra.TensorProduct.lid K A).symm : A →ₐ[K] K ⊗[K] A) x :=
    fun x => AlgHom.congr_fun H.rTensor_counit x
  have hlid : ∀ x : A, ((Algebra.TensorProduct.lid K B).symm : B →ₐ[K] K ⊗[K] B) (π x)
      = Algebra.TensorProduct.map (AlgHom.id K K) π
        (((Algebra.TensorProduct.lid K A).symm : A →ₐ[K] K ⊗[K] A) x) :=
    fun x => AlgHom.congr_fun (lid_symm_naturality π) x
  refine AlgHom.ext fun a => ?_
  show Algebra.TensorProduct.map counit (AlgHom.id K B) (comul (π a))
    = ((Algebra.TensorProduct.lid K B).symm : B →ₐ[K] K ⊗[K] B) (π a)
  rw [hc a, h4 (H.comul a), hrt a, hlid a]

private theorem lTensor_counit_comp_of (H : CommHopfData K A) (π : A →ₐ[K] B)
    (hcomul : comul.comp π = (Algebra.TensorProduct.map π π).comp H.comul)
    (hcounit : counit.comp π = H.counit) :
    ((Algebra.TensorProduct.map (AlgHom.id K B) counit).comp comul).comp π
      = ((Algebra.TensorProduct.rid K K B).symm : B →ₐ[K] B ⊗[K] K).comp π := by
  have hc : ∀ x : A, comul (π x) = Algebra.TensorProduct.map π π (H.comul x) :=
    fun x => AlgHom.congr_fun hcomul x
  have h4 : ∀ t : A ⊗[K] A,
      Algebra.TensorProduct.map (AlgHom.id K B) counit (Algebra.TensorProduct.map π π t)
        = Algebra.TensorProduct.map π (AlgHom.id K K)
          (Algebra.TensorProduct.map (AlgHom.id K A) H.counit t) := by
    have e : (Algebra.TensorProduct.map (AlgHom.id K B) counit).comp
          (Algebra.TensorProduct.map π π)
        = (Algebra.TensorProduct.map π (AlgHom.id K K)).comp
          (Algebra.TensorProduct.map (AlgHom.id K A) H.counit) := by
      rw [← Algebra.TensorProduct.map_comp, ← Algebra.TensorProduct.map_comp, hcounit]
      rfl
    exact fun t => AlgHom.congr_fun e t
  have hlt : ∀ x : A, Algebra.TensorProduct.map (AlgHom.id K A) H.counit (H.comul x)
      = ((Algebra.TensorProduct.rid K K A).symm : A →ₐ[K] A ⊗[K] K) x :=
    fun x => AlgHom.congr_fun H.lTensor_counit x
  have hrid : ∀ x : A, ((Algebra.TensorProduct.rid K K B).symm : B →ₐ[K] B ⊗[K] K) (π x)
      = Algebra.TensorProduct.map π (AlgHom.id K K)
        (((Algebra.TensorProduct.rid K K A).symm : A →ₐ[K] A ⊗[K] K) x) :=
    fun x => AlgHom.congr_fun (rid_symm_naturality π) x
  refine AlgHom.ext fun a => ?_
  show Algebra.TensorProduct.map (AlgHom.id K B) counit (comul (π a))
    = ((Algebra.TensorProduct.rid K K B).symm : B →ₐ[K] B ⊗[K] K) (π a)
  rw [hc a, h4 (H.comul a), hlt a, hrid a]

private theorem mul_antipode_rTensor_comp_of (H : CommHopfData K A) (π : A →ₐ[K] B)
    (hcomul : comul.comp π = (Algebra.TensorProduct.map π π).comp H.comul)
    (hcounit : counit.comp π = H.counit)
    (hantipode : antipode.comp π = π.comp H.antipode) :
    ((Algebra.TensorProduct.lmul' K).comp
        ((Algebra.TensorProduct.map antipode (AlgHom.id K B)).comp comul)).comp π
      = ((Algebra.ofId K B).comp counit).comp π := by
  have hc : ∀ x : A, comul (π x) = Algebra.TensorProduct.map π π (H.comul x) :=
    fun x => AlgHom.congr_fun hcomul x
  have hcnt : ∀ x : A, counit (π x) = H.counit x := fun x => AlgHom.congr_fun hcounit x
  have h5 : ∀ t : A ⊗[K] A,
      Algebra.TensorProduct.map antipode (AlgHom.id K B) (Algebra.TensorProduct.map π π t)
        = Algebra.TensorProduct.map π π
          (Algebra.TensorProduct.map H.antipode (AlgHom.id K A) t) := by
    have e : (Algebra.TensorProduct.map antipode (AlgHom.id K B)).comp
          (Algebra.TensorProduct.map π π)
        = (Algebra.TensorProduct.map π π).comp
          (Algebra.TensorProduct.map H.antipode (AlgHom.id K A)) := by
      rw [← Algebra.TensorProduct.map_comp, ← Algebra.TensorProduct.map_comp, hantipode]
      rfl
    exact fun t => AlgHom.congr_fun e t
  have hlm : ∀ t : A ⊗[K] A, π (Algebra.TensorProduct.lmul' K t)
      = Algebra.TensorProduct.lmul' K (Algebra.TensorProduct.map π π t) :=
    fun t => AlgHom.congr_fun (lmul'_naturality π) t
  have hma : ∀ x : A, Algebra.TensorProduct.lmul' K
      (Algebra.TensorProduct.map H.antipode (AlgHom.id K A) (H.comul x))
      = Algebra.ofId K A (H.counit x) :=
    fun x => AlgHom.congr_fun H.mul_antipode_rTensor x
  have hoi : ∀ r : K, π (Algebra.ofId K A r) = Algebra.ofId K B r :=
    fun r => AlgHom.congr_fun (comp_ofId π) r
  refine AlgHom.ext fun a => ?_
  show Algebra.TensorProduct.lmul' K
      (Algebra.TensorProduct.map antipode (AlgHom.id K B) (comul (π a)))
    = Algebra.ofId K B (counit (π a))
  rw [hc a, h5 (H.comul a), ← hlm _, hma a, hoi, hcnt a]

private theorem mul_antipode_lTensor_comp_of (H : CommHopfData K A) (π : A →ₐ[K] B)
    (hcomul : comul.comp π = (Algebra.TensorProduct.map π π).comp H.comul)
    (hcounit : counit.comp π = H.counit)
    (hantipode : antipode.comp π = π.comp H.antipode) :
    ((Algebra.TensorProduct.lmul' K).comp
        ((Algebra.TensorProduct.map (AlgHom.id K B) antipode).comp comul)).comp π
      = ((Algebra.ofId K B).comp counit).comp π := by
  have hc : ∀ x : A, comul (π x) = Algebra.TensorProduct.map π π (H.comul x) :=
    fun x => AlgHom.congr_fun hcomul x
  have hcnt : ∀ x : A, counit (π x) = H.counit x := fun x => AlgHom.congr_fun hcounit x
  have h5 : ∀ t : A ⊗[K] A,
      Algebra.TensorProduct.map (AlgHom.id K B) antipode (Algebra.TensorProduct.map π π t)
        = Algebra.TensorProduct.map π π
          (Algebra.TensorProduct.map (AlgHom.id K A) H.antipode t) := by
    have e : (Algebra.TensorProduct.map (AlgHom.id K B) antipode).comp
          (Algebra.TensorProduct.map π π)
        = (Algebra.TensorProduct.map π π).comp
          (Algebra.TensorProduct.map (AlgHom.id K A) H.antipode) := by
      rw [← Algebra.TensorProduct.map_comp, ← Algebra.TensorProduct.map_comp, hantipode]
      rfl
    exact fun t => AlgHom.congr_fun e t
  have hlm : ∀ t : A ⊗[K] A, π (Algebra.TensorProduct.lmul' K t)
      = Algebra.TensorProduct.lmul' K (Algebra.TensorProduct.map π π t) :=
    fun t => AlgHom.congr_fun (lmul'_naturality π) t
  have hma : ∀ x : A, Algebra.TensorProduct.lmul' K
      (Algebra.TensorProduct.map (AlgHom.id K A) H.antipode (H.comul x))
      = Algebra.ofId K A (H.counit x) :=
    fun x => AlgHom.congr_fun H.mul_antipode_lTensor x
  have hoi : ∀ r : K, π (Algebra.ofId K A r) = Algebra.ofId K B r :=
    fun r => AlgHom.congr_fun (comp_ofId π) r
  refine AlgHom.ext fun a => ?_
  show Algebra.TensorProduct.lmul' K
      (Algebra.TensorProduct.map (AlgHom.id K B) antipode (comul (π a)))
    = Algebra.ofId K B (counit (π a))
  rw [hc a, h5 (H.comul a), ← hlm _, hma a, hoi, hcnt a]

/-- **Hopf data transfers along a pair of algebra maps whose images jointly detect
identities.**  If `π : A →ₐ B` and `π' : A' →ₐ B` intertwine Hopf data of `A` and of `A'`
with `comul`, `counit`, `antipode` on `B`, and two algebra maps out of `B` that agree after
`π` and after `π'` are equal, then those three maps satisfy the Hopf axioms.  Each axiom is
an identity of algebra maps out of `B`, so `hext` reduces it to the two transferred axioms
(`coassoc_comp_of` and friends).

This is the mechanism behind products of presented groups (`GroupPresentation.prod`): the
coordinate ring of `G × H` is generated by the two blocks of coordinates. -/
noncomputable def CommHopfData.ofPair {A' : Type u} [CommRing A'] [Algebra K A']
    (H : CommHopfData K A) (H' : CommHopfData K A') (π : A →ₐ[K] B) (π' : A' →ₐ[K] B)
    (hext : ∀ {D : Type u} [CommRing D] [Algebra K D] {φ ψ : B →ₐ[K] D},
      φ.comp π = ψ.comp π → φ.comp π' = ψ.comp π' → φ = ψ)
    (comul : B →ₐ[K] B ⊗[K] B) (counit : B →ₐ[K] K) (antipode : B →ₐ[K] B)
    (hcomul : comul.comp π = (Algebra.TensorProduct.map π π).comp H.comul)
    (hcounit : counit.comp π = H.counit)
    (hantipode : antipode.comp π = π.comp H.antipode)
    (hcomul' : comul.comp π' = (Algebra.TensorProduct.map π' π').comp H'.comul)
    (hcounit' : counit.comp π' = H'.counit)
    (hantipode' : antipode.comp π' = π'.comp H'.antipode) :
    CommHopfData K B where
  comul := comul
  counit := counit
  antipode := antipode
  coassoc := hext (coassoc_comp_of H π hcomul) (coassoc_comp_of H' π' hcomul')
  rTensor_counit :=
    hext (rTensor_counit_comp_of H π hcomul hcounit)
      (rTensor_counit_comp_of H' π' hcomul' hcounit')
  lTensor_counit :=
    hext (lTensor_counit_comp_of H π hcomul hcounit)
      (lTensor_counit_comp_of H' π' hcomul' hcounit')
  mul_antipode_rTensor :=
    hext (mul_antipode_rTensor_comp_of H π hcomul hcounit hantipode)
      (mul_antipode_rTensor_comp_of H' π' hcomul' hcounit' hantipode')
  mul_antipode_lTensor :=
    hext (mul_antipode_lTensor_comp_of H π hcomul hcounit hantipode)
      (mul_antipode_lTensor_comp_of H' π' hcomul' hcounit' hantipode')

/-- **Hopf data transfers along a surjection of algebras.**  If `π : A →ₐ B` is onto and
`comul`, `counit`, `antipode` on `B` intertwine `H`'s along `π`, then they satisfy the Hopf
axioms: each axiom is an identity of algebra maps out of `B`, hence may be tested after `π`
(`algHom_ext_of_surjective`), where it becomes `H`'s axiom carried by `π` through the
naturality of `assoc`, `lid`, `rid` and `lmul'` — the case `π' = π` of
`CommHopfData.ofPair`.

This is the mechanism behind closed subgroups (`GroupPresentation.restrict`): the coordinate
ring of a closed subgroup is a quotient of the coordinate ring of the group.  Mathlib's
`HopfAlgebra.ofSurjective` is the linear-map analogue, but it presupposes a `Bialgebra`
structure on `B` — i.e. three of the five axioms. -/
noncomputable def CommHopfData.ofSurjective (H : CommHopfData K A) (π : A →ₐ[K] B)
    (hπ : Function.Surjective π) (comul : B →ₐ[K] B ⊗[K] B) (counit : B →ₐ[K] K)
    (antipode : B →ₐ[K] B)
    (hcomul : comul.comp π = (Algebra.TensorProduct.map π π).comp H.comul)
    (hcounit : counit.comp π = H.counit)
    (hantipode : antipode.comp π = π.comp H.antipode) :
    CommHopfData K B :=
  H.ofPair H π π
    (by intro D _ _ φ ψ h _; exact algHom_ext_of_surjective π hπ h)
    comul counit antipode hcomul hcounit hantipode hcomul hcounit hantipode

end OfSurjective

/-! ### A group presented by polynomials -/

/-- The algebra map `K[γ ⊕ γ] → K[γ] ⊗ K[γ]`, `X (inl i) ↦ X i ⊗ 1`, `X (inr i) ↦ 1 ⊗ X i`. -/
noncomputable def tensorOfSum (K : Type u) [Field K] (γ : Type u) :
    MvPolynomial (γ ⊕ γ) K →ₐ[K] MvPolynomial γ K ⊗[K] MvPolynomial γ K :=
  aeval (Sum.elim (fun i => X i ⊗ₜ 1) (fun i => 1 ⊗ₜ X i))

/-- **The data of a group presented by polynomials**: an ideal `I ⊆ K[γ]` and the
coordinates of the product, the inverse and the unit, with the three descent conditions
(the maps kill `I`, so they induce maps on `K[γ] ⧸ I`).  A consumer proves `mul_mem` from
`tensorOfSum (aeval mul f) ∈ I ⊗ A + A ⊗ I` (`GroupData.mul_mem_of_mem_sup`, below). -/
structure GroupData (K : Type u) [Field K] (γ : Type u) where
  I : Ideal (MvPolynomial γ K)
  mul : γ → MvPolynomial (γ ⊕ γ) K
  inv : γ → MvPolynomial γ K
  one : γ → K
  mul_mem : ∀ f ∈ I, Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K I) (Ideal.Quotient.mkₐ K I)
    (tensorOfSum K γ (aeval mul f)) = 0
  inv_mem : ∀ f ∈ I, Ideal.Quotient.mk I (aeval inv f) = 0
  one_mem : ∀ f ∈ I, aeval one f = 0

namespace GroupData

variable (P : GroupData K γ)

/-- The coordinate ring of the group. -/
abbrev CoordRing : Type u := MvPolynomial γ K ⧸ P.I

/-- The comultiplication `A → A ⊗ A` induced by the product. -/
noncomputable def comul : P.CoordRing →ₐ[K] P.CoordRing ⊗[K] P.CoordRing :=
  Ideal.Quotient.liftₐ P.I
    ((Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K P.I) (Ideal.Quotient.mkₐ K P.I)).comp
      ((tensorOfSum K γ).comp (aeval P.mul)))
    (fun f hf => P.mul_mem f hf)

/-- The counit `A → K` induced by the unit. -/
noncomputable def counit : P.CoordRing →ₐ[K] K :=
  Ideal.Quotient.liftₐ P.I (aeval P.one) (fun f hf => P.one_mem f hf)

/-- The antipode `A → A` induced by the inverse. -/
noncomputable def antipode : P.CoordRing →ₐ[K] P.CoordRing :=
  Ideal.Quotient.liftₐ P.I ((Ideal.Quotient.mkₐ K P.I).comp (aeval P.inv))
    (fun f hf => P.inv_mem f hf)

/-! The three induced maps, read on the generators: each is `Ideal.Quotient.liftₐ_comp`. -/

theorem comul_comp_mkₐ :
    P.comul.comp (Ideal.Quotient.mkₐ K P.I)
      = (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K P.I) (Ideal.Quotient.mkₐ K P.I)).comp
        ((tensorOfSum K γ).comp (aeval P.mul)) :=
  Ideal.Quotient.liftₐ_comp _ _ _

theorem counit_comp_mkₐ : P.counit.comp (Ideal.Quotient.mkₐ K P.I) = aeval P.one :=
  Ideal.Quotient.liftₐ_comp _ _ _

theorem antipode_comp_mkₐ :
    P.antipode.comp (Ideal.Quotient.mkₐ K P.I)
      = (Ideal.Quotient.mkₐ K P.I).comp (aeval P.inv) :=
  Ideal.Quotient.liftₐ_comp _ _ _

/-- The coordinates of a pair of group elements, in the coordinate ring of the group:
`X (inl i) ↦ xᵢ ⊗ 1`, `X (inr i) ↦ 1 ⊗ xᵢ`. -/
noncomputable def coordPair : MvPolynomial (γ ⊕ γ) K →ₐ[K] P.CoordRing ⊗[K] P.CoordRing :=
  (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K P.I) (Ideal.Quotient.mkₐ K P.I)).comp
    (tensorOfSum K γ)

@[simp] theorem coordPair_X_inl (i : γ) :
    P.coordPair (X (Sum.inl i)) = Ideal.Quotient.mk P.I (X i) ⊗ₜ[K] 1 := by
  simp [coordPair, tensorOfSum]

@[simp] theorem coordPair_X_inr (i : γ) :
    P.coordPair (X (Sum.inr i)) = 1 ⊗ₜ[K] Ideal.Quotient.mk P.I (X i) := by
  simp [coordPair, tensorOfSum]

theorem mk_eq_zero {g : MvPolynomial γ K} (hg : g ∈ P.I) :
    Ideal.Quotient.mk P.I g = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hg

theorem mk_C (r : K) : Ideal.Quotient.mk P.I (C r) = algebraMap K P.CoordRing r := rfl

theorem comul_mk_X (i : γ) :
    P.comul (Ideal.Quotient.mk P.I (X i)) = P.coordPair (P.mul i) := by
  have h := AlgHom.congr_fun P.comul_comp_mkₐ (X i)
  simpa [coordPair] using h

theorem counit_mk_X (i : γ) : P.counit (Ideal.Quotient.mk P.I (X i)) = P.one i := by
  have h := AlgHom.congr_fun P.counit_comp_mkₐ (X i)
  simpa using h

theorem antipode_mk_X (i : γ) :
    P.antipode (Ideal.Quotient.mk P.I (X i)) = Ideal.Quotient.mk P.I (P.inv i) := by
  have h := AlgHom.congr_fun P.antipode_comp_mkₐ (X i)
  simpa using h

/-- **The transfer of a group law to a Hopf axiom on a generator.**  If `Φ`, read on the
coordinates of a pair, is the substitution `σ` read in `B` through a map `Ψ` that kills `J`,
then `Φ` applied to the comultiplication of a generator is `Ψ` of any polynomial congruent
to `aeval σ (mul i)` modulo `J`. -/
theorem law_of_comp {B δ : Type u} [CommRing B] [Algebra K B] {J : Ideal (MvPolynomial δ K)}
    (Φ : (P.CoordRing ⊗[K] P.CoordRing) →ₐ[K] B) (Ψ : MvPolynomial δ K →ₐ[K] B)
    (σ : γ ⊕ γ → MvPolynomial δ K) (hΦ : Φ.comp P.coordPair = Ψ.comp (aeval σ))
    (hΨ : ∀ g ∈ J, Ψ g = 0) (i : γ) {r : MvPolynomial δ K}
    (hlaw : aeval σ (P.mul i) - r ∈ J) :
    Φ (P.comul (Ideal.Quotient.mk P.I (X i))) = Ψ r := by
  have h := hΨ _ hlaw
  rw [map_sub, sub_eq_zero] at h
  rw [P.comul_mk_X, ← AlgHom.comp_apply, hΦ, AlgHom.comp_apply]
  exact h

/-! #### The group laws as polynomial identities -/

/-- The coordinates of `1 · x`. -/
noncomputable def oneMul : γ → MvPolynomial γ K := fun i => aeval (Sum.elim (fun j => C (P.one j)) X) (P.mul i)

/-- The coordinates of `x · 1`. -/
noncomputable def mulOne : γ → MvPolynomial γ K := fun i => aeval (Sum.elim X fun j => C (P.one j)) (P.mul i)

/-- The coordinates of `x⁻¹ · x`. -/
noncomputable def invMul : γ → MvPolynomial γ K := fun i => aeval (Sum.elim P.inv X) (P.mul i)

/-- The coordinates of `x · x⁻¹`. -/
noncomputable def mulInv : γ → MvPolynomial γ K := fun i => aeval (Sum.elim X P.inv) (P.mul i)

theorem rTensor_counit_of (h : ∀ i, P.oneMul i - X i ∈ P.I) :
    (Algebra.TensorProduct.map P.counit (AlgHom.id K P.CoordRing)).comp P.comul
      = ((Algebra.TensorProduct.lid K P.CoordRing).symm :
          P.CoordRing →ₐ[K] K ⊗[K] P.CoordRing) := by
  refine quotAlgHom_ext (B := K ⊗[K] P.CoordRing) fun i => ?_
  have hΦ : (Algebra.TensorProduct.map P.counit (AlgHom.id K P.CoordRing)).comp P.coordPair
      = (((Algebra.TensorProduct.lid K P.CoordRing).symm :
            P.CoordRing →ₐ[K] K ⊗[K] P.CoordRing).comp (Ideal.Quotient.mkₐ K P.I)).comp
        (aeval (Sum.elim (fun j => C (P.one j)) X)) := by
    refine MvPolynomial.algHom_ext fun c => ?_
    cases c with
    | inl j =>
        simp only [AlgHom.comp_apply, coordPair_X_inl, Algebra.TensorProduct.map_tmul,
          P.counit_mk_X, map_one, aeval_X, Sum.elim_inl, Ideal.Quotient.mkₐ_eq_mk,
          AlgEquiv.coe_toAlgHom, Algebra.TensorProduct.lid_symm_apply, P.mk_C]
        rw [Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul, smul_eq_mul, mul_one]
    | inr j => simp
  simpa using P.law_of_comp (B := K ⊗[K] P.CoordRing) (J := P.I) _ _ _ hΦ
    (fun _ hg => by simp [P.mk_eq_zero hg]) i (h i)

theorem lTensor_counit_of (h : ∀ i, P.mulOne i - X i ∈ P.I) :
    (Algebra.TensorProduct.map (AlgHom.id K P.CoordRing) P.counit).comp P.comul
      = ((Algebra.TensorProduct.rid K K P.CoordRing).symm :
          P.CoordRing →ₐ[K] P.CoordRing ⊗[K] K) := by
  refine quotAlgHom_ext (B := P.CoordRing ⊗[K] K) fun i => ?_
  have hΦ : (Algebra.TensorProduct.map (AlgHom.id K P.CoordRing) P.counit).comp P.coordPair
      = (((Algebra.TensorProduct.rid K K P.CoordRing).symm :
            P.CoordRing →ₐ[K] P.CoordRing ⊗[K] K).comp (Ideal.Quotient.mkₐ K P.I)).comp
        (aeval (Sum.elim X fun j => C (P.one j))) := by
    refine MvPolynomial.algHom_ext fun c => ?_
    cases c with
    | inl j => simp
    | inr j =>
        simp only [AlgHom.comp_apply, coordPair_X_inr, Algebra.TensorProduct.map_tmul,
          P.counit_mk_X, map_one, aeval_X, Sum.elim_inr, Ideal.Quotient.mkₐ_eq_mk,
          AlgEquiv.coe_toAlgHom, Algebra.TensorProduct.rid_symm_apply, P.mk_C]
        rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, smul_eq_mul, mul_one]
  simpa using P.law_of_comp (B := P.CoordRing ⊗[K] K) (J := P.I) _ _ _ hΦ
    (fun _ hg => by simp [P.mk_eq_zero hg]) i (h i)

theorem mul_antipode_rTensor_of (h : ∀ i, P.invMul i - C (P.one i) ∈ P.I) :
    (Algebra.TensorProduct.lmul' K).comp
        ((Algebra.TensorProduct.map P.antipode (AlgHom.id K P.CoordRing)).comp P.comul)
      = (Algebra.ofId K P.CoordRing).comp P.counit := by
  refine quotAlgHom_ext (B := P.CoordRing) fun i => ?_
  have hΦ : ((Algebra.TensorProduct.lmul' K).comp
        (Algebra.TensorProduct.map P.antipode (AlgHom.id K P.CoordRing))).comp P.coordPair
      = (Ideal.Quotient.mkₐ K P.I).comp (aeval (Sum.elim P.inv X)) := by
    refine MvPolynomial.algHom_ext fun c => ?_
    cases c with
    | inl j => simp [P.antipode_mk_X]
    | inr j => simp
  have hmain := P.law_of_comp (B := P.CoordRing) (J := P.I) _ _ _ hΦ
    (fun _ hg => by simp [P.mk_eq_zero hg]) i (h i)
  simpa [P.counit_mk_X, Algebra.ofId_apply, P.mk_C] using hmain

theorem mul_antipode_lTensor_of (h : ∀ i, P.mulInv i - C (P.one i) ∈ P.I) :
    (Algebra.TensorProduct.lmul' K).comp
        ((Algebra.TensorProduct.map (AlgHom.id K P.CoordRing) P.antipode).comp P.comul)
      = (Algebra.ofId K P.CoordRing).comp P.counit := by
  refine quotAlgHom_ext (B := P.CoordRing) fun i => ?_
  have hΦ : ((Algebra.TensorProduct.lmul' K).comp
        (Algebra.TensorProduct.map (AlgHom.id K P.CoordRing) P.antipode)).comp P.coordPair
      = (Ideal.Quotient.mkₐ K P.I).comp (aeval (Sum.elim X P.inv)) := by
    refine MvPolynomial.algHom_ext fun c => ?_
    cases c with
    | inl j => simp
    | inr j => simp [P.antipode_mk_X]
  have hmain := P.law_of_comp (B := P.CoordRing) (J := P.I) _ _ _ hΦ
    (fun _ hg => by simp [P.mk_eq_zero hg]) i (h i)
  simpa [P.counit_mk_X, Algebra.ofId_apply, P.mk_C] using hmain

/-! #### Associativity -/

/-- The ideal of `K[γ ⊕ γ ⊕ γ]` generated by `I` in each of the three blocks. -/
noncomputable def tripleIdeal : Ideal (MvPolynomial (γ ⊕ γ ⊕ γ) K) := sumIdeal P.I (sumIdeal P.I P.I)

/-- The coordinates of a triple of group elements, in the coordinate ring of the group. -/
noncomputable def coordTriple :
    MvPolynomial (γ ⊕ γ ⊕ γ) K →ₐ[K] P.CoordRing ⊗[K] (P.CoordRing ⊗[K] P.CoordRing) :=
  aeval (Sum.elim
    (fun i => Ideal.Quotient.mk P.I (X i) ⊗ₜ[K] (1 : P.CoordRing ⊗[K] P.CoordRing))
    (Sum.elim
      (fun i => (1 : P.CoordRing) ⊗ₜ[K] (Ideal.Quotient.mk P.I (X i) ⊗ₜ[K] (1 : P.CoordRing)))
      (fun i => (1 : P.CoordRing) ⊗ₜ[K] ((1 : P.CoordRing) ⊗ₜ[K] Ideal.Quotient.mk P.I (X i)))))

private theorem apply_rename_eq_zero {δ B : Type u} [CommRing B] [Algebra K B]
    (φ : MvPolynomial δ K →ₐ[K] B) (ρ : γ → δ) (v : P.CoordRing →ₐ[K] B)
    (hv : ∀ j, φ (X (ρ j)) = v (Ideal.Quotient.mk P.I (X j))) {g : MvPolynomial γ K}
    (hg : g ∈ P.I) : φ (rename ρ g) = 0 := by
  have e : φ.comp (rename ρ) = v.comp (Ideal.Quotient.mkₐ K P.I) :=
    MvPolynomial.algHom_ext fun j => by simpa using hv j
  have hgg := AlgHom.congr_fun e g
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at hgg
  rw [hgg, P.mk_eq_zero hg, map_zero]

theorem coordTriple_eq_zero {f : MvPolynomial (γ ⊕ γ ⊕ γ) K} (hf : f ∈ P.tripleIdeal) :
    P.coordTriple f = 0 := by
  refine sumIdeal_apply_eq_zero _ _ P.coordTriple (fun g hg => ?_) (fun g hg => ?_) hf
  · exact P.apply_rename_eq_zero P.coordTriple Sum.inl
      (Algebra.TensorProduct.includeLeft) (fun j => by simp [coordTriple]) hg
  · refine sumIdeal_apply_eq_zero _ _ (P.coordTriple.comp (rename Sum.inr))
      (fun t ht => ?_) (fun t ht => ?_) hg
    · exact P.apply_rename_eq_zero _ Sum.inl
        (Algebra.TensorProduct.includeRight.comp Algebra.TensorProduct.includeLeft)
        (fun j => by simp [coordTriple]) ht
    · exact P.apply_rename_eq_zero _ Sum.inr
        (Algebra.TensorProduct.includeRight.comp Algebra.TensorProduct.includeRight)
        (fun j => by simp [coordTriple]) ht

/-- `mul` read in the first two blocks of `γ ⊕ γ ⊕ γ`. -/
noncomputable def mul12 : γ → MvPolynomial (γ ⊕ γ ⊕ γ) K := fun i =>
  aeval (Sum.elim (fun j => X (Sum.inl j)) fun j => X (Sum.inr (Sum.inl j))) (P.mul i)

/-- `mul` read in the last two blocks of `γ ⊕ γ ⊕ γ`. -/
noncomputable def mul23 : γ → MvPolynomial (γ ⊕ γ ⊕ γ) K := fun i =>
  aeval (Sum.elim (fun j => X (Sum.inr (Sum.inl j))) fun j => X (Sum.inr (Sum.inr j))) (P.mul i)

/-- The coordinates of `(x y) z`. -/
noncomputable def mulAssocL : γ → MvPolynomial (γ ⊕ γ ⊕ γ) K := fun i =>
  aeval (Sum.elim P.mul12 fun j => X (Sum.inr (Sum.inr j))) (P.mul i)

/-- The coordinates of `x (y z)`. -/
noncomputable def mulAssocR : γ → MvPolynomial (γ ⊕ γ ⊕ γ) K := fun i =>
  aeval (Sum.elim (fun j => X (Sum.inl j)) P.mul23) (P.mul i)

/-- The product `y x` in the first two of three blocks `γ ⊕ γ ⊕ ν`, the factors in the
order the co-opposite comodule law of a left action wants them. -/
noncomputable def mulFlip (P : GroupData K γ) (ν : Type u) : γ → MvPolynomial (γ ⊕ γ ⊕ ν) K := fun j =>
  aeval (Sum.elim (fun k => X (Sum.inr (Sum.inl k))) fun k => X (Sum.inl k)) (P.mul j)

theorem assoc_includeLeft_coordPair :
    ((Algebra.TensorProduct.assoc K K K P.CoordRing P.CoordRing P.CoordRing).toAlgHom.comp
        (Algebra.TensorProduct.includeLeft :
          (P.CoordRing ⊗[K] P.CoordRing) →ₐ[K]
            (P.CoordRing ⊗[K] P.CoordRing) ⊗[K] P.CoordRing)).comp P.coordPair
      = P.coordTriple.comp
        (aeval (Sum.elim (fun j => X (Sum.inl j)) fun j => X (Sum.inr (Sum.inl j)))) := by
  refine MvPolynomial.algHom_ext fun c => ?_
  cases c with
  | inl j => simp [coordTriple, Algebra.TensorProduct.one_def]
  | inr j => simp [coordTriple, Algebra.TensorProduct.one_def]

theorem includeRight_coordPair :
    (Algebra.TensorProduct.includeRight :
        (P.CoordRing ⊗[K] P.CoordRing) →ₐ[K]
          P.CoordRing ⊗[K] (P.CoordRing ⊗[K] P.CoordRing)).comp P.coordPair
      = P.coordTriple.comp
        (aeval (Sum.elim (fun j => X (Sum.inr (Sum.inl j)))
          fun j => X (Sum.inr (Sum.inr j)))) := by
  refine MvPolynomial.algHom_ext fun c => ?_
  cases c with
  | inl j => simp [coordTriple]
  | inr j => simp [coordTriple]

theorem coassoc_of (h : ∀ i, P.mulAssocL i - P.mulAssocR i ∈ P.tripleIdeal) :
    (Algebra.TensorProduct.assoc K K K P.CoordRing P.CoordRing P.CoordRing).toAlgHom.comp
        ((Algebra.TensorProduct.map P.comul (AlgHom.id K P.CoordRing)).comp P.comul)
      = (Algebra.TensorProduct.map (AlgHom.id K P.CoordRing) P.comul).comp P.comul := by
  refine quotAlgHom_ext (B := P.CoordRing ⊗[K] (P.CoordRing ⊗[K] P.CoordRing)) fun i => ?_
  have hL : ((Algebra.TensorProduct.assoc K K K P.CoordRing P.CoordRing P.CoordRing).toAlgHom.comp
        (Algebra.TensorProduct.map P.comul (AlgHom.id K P.CoordRing))).comp P.coordPair
      = P.coordTriple.comp
        (aeval (Sum.elim P.mul12 fun j => X (Sum.inr (Sum.inr j)))) := by
    refine MvPolynomial.algHom_ext fun c => ?_
    cases c with
    | inl j =>
        have hj := AlgHom.congr_fun P.assoc_includeLeft_coordPair (P.mul j)
        simp only [AlgHom.comp_apply, Algebra.TensorProduct.includeLeft_apply] at hj
        simpa [P.comul_mk_X, mul12] using hj
    | inr j => simp [coordTriple, Algebra.TensorProduct.one_def]
  have hR : (Algebra.TensorProduct.map (AlgHom.id K P.CoordRing) P.comul).comp P.coordPair
      = P.coordTriple.comp (aeval (Sum.elim (fun j => X (Sum.inl j)) P.mul23)) := by
    refine MvPolynomial.algHom_ext fun c => ?_
    cases c with
    | inl j => simp [coordTriple, Algebra.TensorProduct.one_def]
    | inr j =>
        have hj := AlgHom.congr_fun P.includeRight_coordPair (P.mul j)
        simp only [AlgHom.comp_apply, Algebra.TensorProduct.includeRight_apply] at hj
        simpa [P.comul_mk_X, mul23] using hj
  have hRlaw : aeval (Sum.elim (fun j => X (Sum.inl j)) P.mul23) (P.mul i) - P.mulAssocR i
      ∈ P.tripleIdeal := by
    rw [show aeval (Sum.elim (fun j => X (Sum.inl j)) P.mul23) (P.mul i) = P.mulAssocR i from rfl,
      sub_self]
    exact Ideal.zero_mem _
  have e1 := P.law_of_comp (B := P.CoordRing ⊗[K] (P.CoordRing ⊗[K] P.CoordRing))
    (J := P.tripleIdeal) _ _ _ hL (fun _ hg => P.coordTriple_eq_zero hg) i (h i)
  have e2 := P.law_of_comp (B := P.CoordRing ⊗[K] (P.CoordRing ⊗[K] P.CoordRing))
    (J := P.tripleIdeal) _ _ _ hR (fun _ hg => P.coordTriple_eq_zero hg) i hRlaw
  simpa using e1.trans e2.symm

/-- The `K`-points of the group: the zeros of `I`. -/
def pts : Set (γ → K) := MvPolynomial.zeroLocus K P.I

/-- The product on `K`-points. -/
noncomputable def mulPt (a b : γ → K) : γ → K := fun i => aeval (Sum.elim a b) (P.mul i)

/-- The inverse on `K`-points. -/
noncomputable def invPt (a : γ → K) : γ → K := fun i => aeval a (P.inv i)

/-- The group scheme: `Spec` of the coordinate ring, over `Spec K`. -/
noncomputable abbrev scheme : Over (Spec (.of K)) :=
  (Spec (.of P.CoordRing)).asOver (Spec (.of K))

instance isAffine_scheme_left : IsAffine P.scheme.left :=
  inferInstanceAs (IsAffine (Spec (.of P.CoordRing)))

instance finiteType_coordRing [Finite γ] : Algebra.FiniteType K P.CoordRing :=
  inferInstance

/-- The group scheme is of finite type over `K` when there are finitely many coordinates
(`locallyOfFiniteType_specOverSpec`). -/
instance locallyOfFiniteType_scheme_hom [Finite γ] : LocallyOfFiniteType P.scheme.hom :=
  letI : Algebra.FiniteType (CommRingCat.of K) (CommRingCat.of P.CoordRing) :=
    inferInstanceAs (Algebra.FiniteType K P.CoordRing)
  locallyOfFiniteType_specOverSpec (R := CommRingCat.of K) (A := CommRingCat.of P.CoordRing)

/-- The descent condition for the product follows from `I ↦ I ⊗ A + A ⊗ I`. -/
theorem mul_mem_of_mem_sup {I : Ideal (MvPolynomial γ K)} {mul : γ → MvPolynomial (γ ⊕ γ) K}
    (h : ∀ f ∈ I, tensorOfSum K γ (aeval mul f) ∈
      (I.map (Algebra.TensorProduct.includeLeft :
        MvPolynomial γ K →ₐ[K] MvPolynomial γ K ⊗[K] MvPolynomial γ K)).restrictScalars K ⊔
      (I.map (Algebra.TensorProduct.includeRight :
        MvPolynomial γ K →ₐ[K] MvPolynomial γ K ⊗[K] MvPolynomial γ K)).restrictScalars K) :
    ∀ f ∈ I, Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K I) (Ideal.Quotient.mkₐ K I)
      (tensorOfSum K γ (aeval mul f)) = 0 := by
  set φ := Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K I) (Ideal.Quotient.mkₐ K I) with hφ
  have hleft : ∀ x ∈ (I.map (Algebra.TensorProduct.includeLeft :
      MvPolynomial γ K →ₐ[K] MvPolynomial γ K ⊗[K] MvPolynomial γ K)).restrictScalars K,
      φ x = 0 := by
    intro x hx
    have hle : I.map (Algebra.TensorProduct.includeLeft :
        MvPolynomial γ K →ₐ[K] MvPolynomial γ K ⊗[K] MvPolynomial γ K) ≤
        RingHom.ker (φ : _ →ₐ[K] _).toRingHom := by
      rw [Ideal.map_le_iff_le_comap]
      intro f hf
      simp only [Ideal.mem_comap, RingHom.mem_ker]
      show φ (f ⊗ₜ 1) = 0
      simp [hφ, Ideal.Quotient.eq_zero_iff_mem.mpr hf]
    exact RingHom.mem_ker.mp (hle hx)
  have hright : ∀ x ∈ (I.map (Algebra.TensorProduct.includeRight :
      MvPolynomial γ K →ₐ[K] MvPolynomial γ K ⊗[K] MvPolynomial γ K)).restrictScalars K,
      φ x = 0 := by
    intro x hx
    have hle : I.map (Algebra.TensorProduct.includeRight :
        MvPolynomial γ K →ₐ[K] MvPolynomial γ K ⊗[K] MvPolynomial γ K) ≤
        RingHom.ker (φ : _ →ₐ[K] _).toRingHom := by
      rw [Ideal.map_le_iff_le_comap]
      intro f hf
      simp only [Ideal.mem_comap, RingHom.mem_ker]
      show φ (1 ⊗ₜ f) = 0
      simp [hφ, Ideal.Quotient.eq_zero_iff_mem.mpr hf]
    exact RingHom.mem_ker.mp (hle hx)
  intro f hf
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp (h f hf)
  rw [← hyz, map_add, hleft y hy, hright z hz, add_zero]

/-! #### The `K`-point dictionary of a presented group

`pts` is closed under the product, the inverse and the unit; the evaluation map `ptHom`
of a `K`-point turns those into the convolution product, the antipode and the counit, so
that the group laws on `pts` are the group laws of `WithConv (A →ₐ[K] K)`
(`AlgHom.convGroup`, below in `GroupPresentation`). -/

/-- Evaluation at a `K`-point of the group, as an algebra map on the coordinate ring. -/
noncomputable def ptHom {a : γ → K} (ha : a ∈ P.pts) : P.CoordRing →ₐ[K] K :=
  Ideal.Quotient.liftₐ P.I (aeval a) (fun f hf => ha f hf)

@[simp] theorem ptHom_mk {a : γ → K} (ha : a ∈ P.pts) (f : MvPolynomial γ K) :
    P.ptHom ha (Ideal.Quotient.mk P.I f) = aeval a f := rfl

/-- A `K`-point is determined by its evaluation map. -/
theorem pt_eq_of_ptHom_eq {a b : γ → K} (ha : a ∈ P.pts) (hb : b ∈ P.pts)
    (h : P.ptHom ha = P.ptHom hb) : a = b := by
  funext i
  have := congrArg (fun φ : P.CoordRing →ₐ[K] K => φ (Ideal.Quotient.mk P.I (X i))) h
  simpa using this

/-- Evaluating a pair of `K`-points on `K[γ] ⊗ K[γ]` through `tensorOfSum` is evaluation at
the concatenated tuple. -/
private theorem lift_comp_tensorOfSum {a b : γ → K} (ha : a ∈ P.pts) (hb : b ∈ P.pts) :
    (Algebra.TensorProduct.lift (P.ptHom ha) (P.ptHom hb) (fun _ _ => Commute.all _ _)).comp
      ((Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K P.I) (Ideal.Quotient.mkₐ K P.I)).comp
        (tensorOfSum K γ))
      = aeval (Sum.elim a b) := by
  refine MvPolynomial.algHom_ext fun i => ?_
  cases i <;> simp [tensorOfSum]

/-- The coordinates of the product of two `K`-points are the comultiplication evaluated at
the pair. -/
private theorem eval_mulPt {a b : γ → K} (ha : a ∈ P.pts) (hb : b ∈ P.pts) :
    (Algebra.TensorProduct.lift (P.ptHom ha) (P.ptHom hb) (fun _ _ => Commute.all _ _)).comp
      ((Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K P.I) (Ideal.Quotient.mkₐ K P.I)).comp
        ((tensorOfSum K γ).comp (aeval P.mul)))
      = aeval (P.mulPt a b) := by
  have h : ((Algebra.TensorProduct.lift (P.ptHom ha) (P.ptHom hb)
      (fun _ _ => Commute.all _ _)).comp
      ((Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K P.I) (Ideal.Quotient.mkₐ K P.I)).comp
        (tensorOfSum K γ))).comp (aeval P.mul)
      = (aeval (Sum.elim a b)).comp (aeval P.mul) := by
    rw [P.lift_comp_tensorOfSum ha hb]
  refine (AlgHom.comp_assoc _ _ _).symm.trans (h.trans ?_)
  exact MvPolynomial.algHom_ext fun i => by simp [mulPt]

/-- **`pts` is closed under the product.** -/
theorem mulPt_mem {a b : γ → K} (ha : a ∈ P.pts) (hb : b ∈ P.pts) : P.mulPt a b ∈ P.pts := by
  intro f hf
  rw [← P.eval_mulPt ha hb]
  show (Algebra.TensorProduct.lift (P.ptHom ha) (P.ptHom hb) (fun _ _ => Commute.all _ _))
    ((Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K P.I) (Ideal.Quotient.mkₐ K P.I))
      (tensorOfSum K γ (aeval P.mul f))) = 0
  rw [P.mul_mem f hf, map_zero]

/-- **`pts` is closed under the inverse.** -/
theorem invPt_mem {a : γ → K} (ha : a ∈ P.pts) : P.invPt a ∈ P.pts := by
  intro f hf
  have h : (aeval (R := K) a).comp (aeval P.inv) = aeval (P.invPt a) :=
    MvPolynomial.algHom_ext fun i => by simp [invPt]
  have hmem : aeval P.inv f ∈ P.I := Ideal.Quotient.eq_zero_iff_mem.mp (P.inv_mem f hf)
  have hf' : aeval (P.invPt a) f = aeval a (aeval P.inv f) :=
    (congrArg (fun φ : MvPolynomial γ K →ₐ[K] K => φ f) h).symm
  rw [hf', ha _ hmem]

/-- **The unit is a `K`-point.** -/
theorem one_mem_pts : P.one ∈ P.pts := fun f hf => P.one_mem f hf

/-- The evaluation map of the unit is the counit. -/
theorem ptHom_one : P.ptHom P.one_mem_pts = P.counit := rfl

/-- The evaluation map of a product is the convolution of the two evaluation maps. -/
theorem ptHom_mulPt {a b : γ → K} (ha : a ∈ P.pts) (hb : b ∈ P.pts) :
    P.ptHom (P.mulPt_mem ha hb) =
      (Algebra.TensorProduct.lift (P.ptHom ha) (P.ptHom hb)
        (fun _ _ => Commute.all _ _)).comp P.comul := by
  refine Ideal.Quotient.algHom_ext K ?_
  simp only [ptHom, comul, AlgHom.comp_assoc, Ideal.Quotient.liftₐ_comp]
  exact (P.eval_mulPt ha hb).symm

/-- The evaluation map of an inverse is the evaluation map after the antipode. -/
theorem ptHom_invPt {a : γ → K} (ha : a ∈ P.pts) :
    P.ptHom (P.invPt_mem ha) = (P.ptHom ha).comp P.antipode := by
  refine Ideal.Quotient.algHom_ext K (MvPolynomial.algHom_ext fun i => ?_)
  show aeval (P.invPt a) (X i) = P.ptHom ha (P.antipode (Ideal.Quotient.mk P.I (X i)))
  have hS : P.antipode (Ideal.Quotient.mk P.I (X i)) =
      Ideal.Quotient.mk P.I (aeval P.inv (X i)) := rfl
  rw [hS, ptHom_mk]
  simp [invPt]

/-- The section of `P.scheme` over `Spec K` at a `K`-point. -/
noncomputable def sec {a : γ → K} (ha : a ∈ P.pts) :
    𝟙_ (Over (Spec (.of K))) ⟶ P.scheme :=
  secOfAlgHom (P.ptHom ha)

@[simp] theorem sec_left {a : γ → K} (ha : a ∈ P.pts) :
    (P.sec ha).left = Spec.map (CommRingCat.ofHom (P.ptHom ha).toRingHom) := rfl

/-- The `K`-point of a section of `P.scheme`: its algebra map read on the generators. -/
noncomputable def ptOfSec (s : 𝟙_ (Over (Spec (.of K))) ⟶ P.scheme) : γ → K :=
  fun i => algHomOfSec s (Ideal.Quotient.mk P.I (X i))

theorem ptOfSec_mem (s : 𝟙_ (Over (Spec (.of K))) ⟶ P.scheme) : P.ptOfSec s ∈ P.pts := by
  intro f hf
  have h : (algHomOfSec s).comp (Ideal.Quotient.mkₐ K P.I) = aeval (P.ptOfSec s) :=
    MvPolynomial.algHom_ext fun i => by simp [ptOfSec, Ideal.Quotient.mkₐ_eq_mk]
  have h' := congrArg (fun φ : MvPolynomial γ K →ₐ[K] K => φ f) h
  rw [← h']
  show algHomOfSec s (Ideal.Quotient.mk P.I f) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hf, map_zero]

theorem ptHom_ptOfSec (s : 𝟙_ (Over (Spec (.of K))) ⟶ P.scheme) :
    P.ptHom (P.ptOfSec_mem s) = algHomOfSec s :=
  Ideal.Quotient.algHom_ext K (MvPolynomial.algHom_ext fun i => by
    simp [ptOfSec, ptHom, Ideal.Quotient.mkₐ_eq_mk])

/-- **Sections of `P.scheme` are `K`-points** (`sec` and `ptOfSec` are inverse). -/
@[simp] theorem sec_ptOfSec (s : 𝟙_ (Over (Spec (.of K))) ⟶ P.scheme) :
    P.sec (P.ptOfSec_mem s) = s := by
  rw [sec, ptHom_ptOfSec, secOfAlgHom_algHomOfSec]

@[simp] theorem ptOfSec_sec {a : γ → K} (ha : a ∈ P.pts) : P.ptOfSec (P.sec ha) = a := by
  funext i
  show algHomOfSec (secOfAlgHom (P.ptHom ha)) (Ideal.Quotient.mk P.I (X i)) = a i
  rw [algHomOfSec_secOfAlgHom, ptHom_mk]
  simp

/-! #### Irreducibility -/

/-- The `K`-point companion: over an algebraically closed field the vanishing ideal of
`pts` is `I` itself when `I` is prime (Nullstellensatz), so `pts` is irreducible in the
coordinate sense of `PolyAction`. -/
theorem isPrime_vanishingIdeal_pts [IsAlgClosed K] [Finite γ] (h : P.I.IsPrime) :
    (MvPolynomial.vanishingIdeal K P.pts).IsPrime := by
  rw [pts, MvPolynomial.vanishingIdeal_zeroLocus_eq_radical, h.radical]
  exact h

/-! #### Closed subgroups

A closed subgroup of a presented group is the *same* product, inverse and unit cut out by a
larger ideal `J ⊇ I` for which the three descent conditions still hold — centralisers
`(gN − Ng)` and Borels are of this form.  Its coordinate ring is the further quotient
`K[γ] ⧸ J` of `K[γ] ⧸ I`, and the surjection between them is mathlib's
`Ideal.Quotient.factorₐ`; the three lemmas below say that it intertwines the comultiplication,
the counit and the antipode, which is exactly the input of `CommHopfData.ofSurjective`
(`GroupPresentation.restrict`). -/

/-- **A closed subgroup**: the same product, inverse and unit, cut out by a larger ideal `J`
for which the three descent conditions still hold.  (`J ⊇ P.I` is not needed to build the
group data — only to compare it with `P`, so it is a hypothesis of `restrict_pts` and of
`GroupPresentation.restrict` rather than of `restrict` itself.) -/
def restrict (J : Ideal (MvPolynomial γ K))
    (hmul : ∀ f ∈ J, Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K J)
      (Ideal.Quotient.mkₐ K J) (tensorOfSum K γ (aeval P.mul f)) = 0)
    (hinv : ∀ f ∈ J, Ideal.Quotient.mk J (aeval P.inv f) = 0)
    (hone : ∀ f ∈ J, aeval P.one f = 0) : GroupData K γ where
  I := J
  mul := P.mul
  inv := P.inv
  one := P.one
  mul_mem := hmul
  inv_mem := hinv
  one_mem := hone

section Restrict

variable {J : Ideal (MvPolynomial γ K)}
  (hmul : ∀ f ∈ J, Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K J)
    (Ideal.Quotient.mkₐ K J) (tensorOfSum K γ (aeval P.mul f)) = 0)
  (hinv : ∀ f ∈ J, Ideal.Quotient.mk J (aeval P.inv f) = 0)
  (hone : ∀ f ∈ J, aeval P.one f = 0)

@[simp] theorem restrict_I : (P.restrict J hmul hinv hone).I = J := rfl
@[simp] theorem restrict_mul : (P.restrict J hmul hinv hone).mul = P.mul := rfl
@[simp] theorem restrict_inv : (P.restrict J hmul hinv hone).inv = P.inv := rfl
@[simp] theorem restrict_one : (P.restrict J hmul hinv hone).one = P.one := rfl
@[simp] theorem restrict_mulPt : (P.restrict J hmul hinv hone).mulPt = P.mulPt := rfl
@[simp] theorem restrict_invPt : (P.restrict J hmul hinv hone).invPt = P.invPt := rfl

/-- **The `K`-points of a closed subgroup** are the points of `P` satisfying the extra
equations. -/
theorem restrict_pts (hIJ : P.I ≤ J) :
    (P.restrict J hmul hinv hone).pts = P.pts ∩ MvPolynomial.zeroLocus K J :=
  Set.Subset.antisymm (fun _ hx => ⟨fun p hp => hx p (hIJ hp), hx⟩) fun _ hx => hx.2

/-- The surjection `K[γ] ⧸ I → K[γ] ⧸ J` intertwines the two comultiplications. -/
theorem restrict_comul_comp (hIJ : P.I ≤ J) :
    (P.restrict J hmul hinv hone).comul.comp (Ideal.Quotient.factorₐ K hIJ)
      = (Algebra.TensorProduct.map (Ideal.Quotient.factorₐ K hIJ)
          (Ideal.Quotient.factorₐ K hIJ)).comp P.comul := by
  have hmm : (Algebra.TensorProduct.map (Ideal.Quotient.factorₐ K hIJ)
        (Ideal.Quotient.factorₐ K hIJ)).comp
      (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K P.I) (Ideal.Quotient.mkₐ K P.I))
      = Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K J) (Ideal.Quotient.mkₐ K J) := by
    rw [← Algebra.TensorProduct.map_comp]
    rfl
  refine quotAlgHom_ext fun i => ?_
  exact (AlgHom.congr_fun hmm (tensorOfSum K γ (aeval P.mul (X i)))).symm

/-- The surjection `K[γ] ⧸ I → K[γ] ⧸ J` intertwines the two counits. -/
theorem restrict_counit_comp (hIJ : P.I ≤ J) :
    (P.restrict J hmul hinv hone).counit.comp (Ideal.Quotient.factorₐ K hIJ) = P.counit :=
  quotAlgHom_ext fun _ => rfl

/-- The surjection `K[γ] ⧸ I → K[γ] ⧸ J` intertwines the two antipodes. -/
theorem restrict_antipode_comp (hIJ : P.I ≤ J) :
    (P.restrict J hmul hinv hone).antipode.comp (Ideal.Quotient.factorₐ K hIJ)
      = (Ideal.Quotient.factorₐ K hIJ).comp P.antipode :=
  quotAlgHom_ext fun _ => rfl

end Restrict

/-! #### Products

The product of two presented groups carries the coordinates of both factors side by side,
the ideal generated by both, and the two laws applied blockwise.  Everything transports
along the two block maps of coordinate rings `prodMkL`, `prodMkR`, and an identity of
algebra maps out of the product coordinate ring is detected by the pair of them
(`sumAlgHom_ext`) — exactly the input of `CommHopfData.ofPair`. -/

section Prod

variable {δ : Type u} (Q : GroupData K δ)

/-- The ideal of a product: the two factors' ideals, pushed into `K[γ ⊕ δ]`. -/
noncomputable abbrev prodIdeal : Ideal (MvPolynomial (γ ⊕ δ) K) := sumIdeal P.I Q.I

/-- The product law of a product group, blockwise. -/
noncomputable def prodMul : γ ⊕ δ → MvPolynomial ((γ ⊕ δ) ⊕ (γ ⊕ δ)) K :=
  Sum.elim (fun i => rename (Sum.map Sum.inl Sum.inl) (P.mul i))
    (fun j => rename (Sum.map Sum.inr Sum.inr) (Q.mul j))

/-- The inverse of a product group, blockwise. -/
noncomputable def prodInv : γ ⊕ δ → MvPolynomial (γ ⊕ δ) K :=
  Sum.elim (fun i => rename Sum.inl (P.inv i)) (fun j => rename Sum.inr (Q.inv j))

/-- The first block of coordinates, as a map of coordinate rings. -/
noncomputable abbrev prodMkL : P.CoordRing →ₐ[K] MvPolynomial (γ ⊕ δ) K ⧸ P.prodIdeal Q :=
  sumMkL P.I Q.I

/-- The second block of coordinates, as a map of coordinate rings. -/
noncomputable abbrev prodMkR : Q.CoordRing →ₐ[K] MvPolynomial (γ ⊕ δ) K ⧸ P.prodIdeal Q :=
  sumMkR P.I Q.I

/-! The three transport identities: the block maps carry the product's comultiplication,
counit and antipode to the factor's.  `prodMul`, `prodInv` and `Sum.elim P.one Q.one` are
renamings of the factors' laws, so each is `aeval_rename` followed by `comp_aeval_apply` and
one computation on the generators of `K[γ ⊕ γ]` (for the comultiplication). -/

private theorem prod_tensorOfSum_renameL_comp :
    (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K (P.prodIdeal Q))
        (Ideal.Quotient.mkₐ K (P.prodIdeal Q))).comp
      ((tensorOfSum K (γ ⊕ δ)).comp (rename (Sum.map Sum.inl Sum.inl)))
      = ((Algebra.TensorProduct.map (P.prodMkL Q) (P.prodMkL Q)).comp
        (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K P.I)
          (Ideal.Quotient.mkₐ K P.I))).comp (tensorOfSum K γ) := by
  refine MvPolynomial.algHom_ext fun k => ?_
  cases k with
  | inl a => simp [tensorOfSum]
  | inr a => simp [tensorOfSum]

private theorem prod_tensorOfSum_renameR_comp :
    (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K (P.prodIdeal Q))
        (Ideal.Quotient.mkₐ K (P.prodIdeal Q))).comp
      ((tensorOfSum K (γ ⊕ δ)).comp (rename (Sum.map Sum.inr Sum.inr)))
      = ((Algebra.TensorProduct.map (P.prodMkR Q) (P.prodMkR Q)).comp
        (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K Q.I)
          (Ideal.Quotient.mkₐ K Q.I))).comp (tensorOfSum K δ) := by
  refine MvPolynomial.algHom_ext fun k => ?_
  cases k with
  | inl a => simp [tensorOfSum]
  | inr a => simp [tensorOfSum]

/-- The comultiplication of a product, on the first block. -/
theorem prod_comulHom_renameL (g : MvPolynomial γ K) :
    Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K (P.prodIdeal Q))
        (Ideal.Quotient.mkₐ K (P.prodIdeal Q))
        (tensorOfSum K (γ ⊕ δ) (aeval (P.prodMul Q) (rename Sum.inl g)))
      = Algebra.TensorProduct.map (P.prodMkL Q) (P.prodMkL Q)
        (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K P.I) (Ideal.Quotient.mkₐ K P.I)
          (tensorOfSum K γ (aeval P.mul g))) := by
  rw [aeval_rename]
  have hcomp : P.prodMul Q ∘ Sum.inl
      = fun i => rename (Sum.map Sum.inl Sum.inl) (P.mul i) := rfl
  rw [hcomp, ← MvPolynomial.comp_aeval_apply]
  exact AlgHom.congr_fun (P.prod_tensorOfSum_renameL_comp Q) (aeval P.mul g)

/-- The comultiplication of a product, on the second block. -/
theorem prod_comulHom_renameR (g : MvPolynomial δ K) :
    Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K (P.prodIdeal Q))
        (Ideal.Quotient.mkₐ K (P.prodIdeal Q))
        (tensorOfSum K (γ ⊕ δ) (aeval (P.prodMul Q) (rename Sum.inr g)))
      = Algebra.TensorProduct.map (P.prodMkR Q) (P.prodMkR Q)
        (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K Q.I) (Ideal.Quotient.mkₐ K Q.I)
          (tensorOfSum K δ (aeval Q.mul g))) := by
  rw [aeval_rename]
  have hcomp : P.prodMul Q ∘ Sum.inr
      = fun j => rename (Sum.map Sum.inr Sum.inr) (Q.mul j) := rfl
  rw [hcomp, ← MvPolynomial.comp_aeval_apply]
  exact AlgHom.congr_fun (P.prod_tensorOfSum_renameR_comp Q) (aeval Q.mul g)

/-- The inverse of a product, on the first block. -/
theorem prod_invHom_renameL (g : MvPolynomial γ K) :
    Ideal.Quotient.mk (P.prodIdeal Q) (aeval (P.prodInv Q) (rename Sum.inl g))
      = P.prodMkL Q (Ideal.Quotient.mk P.I (aeval P.inv g)) := by
  rw [aeval_rename]
  have hcomp : P.prodInv Q ∘ Sum.inl = fun i => rename Sum.inl (P.inv i) := rfl
  rw [hcomp, ← MvPolynomial.comp_aeval_apply, sumMkL_mk]

/-- The inverse of a product, on the second block. -/
theorem prod_invHom_renameR (g : MvPolynomial δ K) :
    Ideal.Quotient.mk (P.prodIdeal Q) (aeval (P.prodInv Q) (rename Sum.inr g))
      = P.prodMkR Q (Ideal.Quotient.mk Q.I (aeval Q.inv g)) := by
  rw [aeval_rename]
  have hcomp : P.prodInv Q ∘ Sum.inr = fun j => rename Sum.inr (Q.inv j) := rfl
  rw [hcomp, ← MvPolynomial.comp_aeval_apply, sumMkR_mk]

/-- The unit of a product, on the first block. -/
theorem prod_oneHom_renameL (g : MvPolynomial γ K) :
    aeval (Sum.elim P.one Q.one) (rename Sum.inl g) = aeval P.one g := by
  rw [aeval_rename, Sum.elim_comp_inl]

/-- The unit of a product, on the second block. -/
theorem prod_oneHom_renameR (g : MvPolynomial δ K) :
    aeval (Sum.elim P.one Q.one) (rename Sum.inr g) = aeval Q.one g := by
  rw [aeval_rename, Sum.elim_comp_inr]

/-- **The product of two presented groups**: the coordinates of both factors, the ideal
generated by both, and the product, inverse and unit applied blockwise. -/
noncomputable def prod : GroupData K (γ ⊕ δ) where
  I := P.prodIdeal Q
  mul := P.prodMul Q
  inv := P.prodInv Q
  one := Sum.elim P.one Q.one
  mul_mem := by
    intro f hf
    refine sumIdeal_apply_eq_zero P.I Q.I
      ((Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K (P.prodIdeal Q))
          (Ideal.Quotient.mkₐ K (P.prodIdeal Q))).comp
        ((tensorOfSum K (γ ⊕ δ)).comp (aeval (P.prodMul Q)))) ?_ ?_ hf
    · intro g hg
      show Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K (P.prodIdeal Q))
          (Ideal.Quotient.mkₐ K (P.prodIdeal Q))
          (tensorOfSum K (γ ⊕ δ) (aeval (P.prodMul Q) (rename Sum.inl g))) = 0
      rw [P.prod_comulHom_renameL Q, P.mul_mem g hg, map_zero]
    · intro g hg
      show Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K (P.prodIdeal Q))
          (Ideal.Quotient.mkₐ K (P.prodIdeal Q))
          (tensorOfSum K (γ ⊕ δ) (aeval (P.prodMul Q) (rename Sum.inr g))) = 0
      rw [P.prod_comulHom_renameR Q, Q.mul_mem g hg, map_zero]
  inv_mem := by
    intro f hf
    refine sumIdeal_apply_eq_zero P.I Q.I
      ((Ideal.Quotient.mkₐ K (P.prodIdeal Q)).comp (aeval (P.prodInv Q))) ?_ ?_ hf
    · intro g hg
      show Ideal.Quotient.mk (P.prodIdeal Q) (aeval (P.prodInv Q) (rename Sum.inl g)) = 0
      rw [P.prod_invHom_renameL Q, P.inv_mem g hg, map_zero]
    · intro g hg
      show Ideal.Quotient.mk (P.prodIdeal Q) (aeval (P.prodInv Q) (rename Sum.inr g)) = 0
      rw [P.prod_invHom_renameR Q, Q.inv_mem g hg, map_zero]
  one_mem := by
    intro f hf
    refine sumIdeal_apply_eq_zero P.I Q.I (aeval (Sum.elim P.one Q.one)) ?_ ?_ hf
    · intro g hg
      rw [P.prod_oneHom_renameL Q]
      exact P.one_mem g hg
    · intro g hg
      rw [P.prod_oneHom_renameR Q]
      exact Q.one_mem g hg

@[simp] theorem prod_I : (P.prod Q).I = P.prodIdeal Q := rfl

@[simp] theorem prod_mul : (P.prod Q).mul = P.prodMul Q := rfl

@[simp] theorem prod_inv : (P.prod Q).inv = P.prodInv Q := rfl

@[simp] theorem prod_one : (P.prod Q).one = Sum.elim P.one Q.one := rfl

/-- **The `K`-points of a product are the pairs of `K`-points.** -/
theorem prod_pts :
    (P.prod Q).pts = {x : γ ⊕ δ → K | x ∘ Sum.inl ∈ P.pts ∧ x ∘ Sum.inr ∈ Q.pts} :=
  zeroLocus_sumIdeal P.I Q.I

theorem prod_comul_comp_prodMkL :
    (P.prod Q).comul.comp (P.prodMkL Q)
      = (Algebra.TensorProduct.map (P.prodMkL Q) (P.prodMkL Q)).comp P.comul := by
  refine quotAlgHom_ext fun i => ?_
  show Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K (P.prodIdeal Q))
      (Ideal.Quotient.mkₐ K (P.prodIdeal Q))
      (tensorOfSum K (γ ⊕ δ) (aeval (P.prodMul Q) (rename Sum.inl (X i))))
    = Algebra.TensorProduct.map (P.prodMkL Q) (P.prodMkL Q)
      (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K P.I) (Ideal.Quotient.mkₐ K P.I)
        (tensorOfSum K γ (aeval P.mul (X i))))
  exact P.prod_comulHom_renameL Q (X i)

theorem prod_comul_comp_prodMkR :
    (P.prod Q).comul.comp (P.prodMkR Q)
      = (Algebra.TensorProduct.map (P.prodMkR Q) (P.prodMkR Q)).comp Q.comul := by
  refine quotAlgHom_ext fun j => ?_
  show Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K (P.prodIdeal Q))
      (Ideal.Quotient.mkₐ K (P.prodIdeal Q))
      (tensorOfSum K (γ ⊕ δ) (aeval (P.prodMul Q) (rename Sum.inr (X j))))
    = Algebra.TensorProduct.map (P.prodMkR Q) (P.prodMkR Q)
      (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K Q.I) (Ideal.Quotient.mkₐ K Q.I)
        (tensorOfSum K δ (aeval Q.mul (X j))))
  exact P.prod_comulHom_renameR Q (X j)

theorem prod_counit_comp_prodMkL : (P.prod Q).counit.comp (P.prodMkL Q) = P.counit := by
  refine quotAlgHom_ext fun i => ?_
  show aeval (Sum.elim P.one Q.one) (rename Sum.inl (X i)) = aeval P.one (X i)
  exact P.prod_oneHom_renameL Q (X i)

theorem prod_counit_comp_prodMkR : (P.prod Q).counit.comp (P.prodMkR Q) = Q.counit := by
  refine quotAlgHom_ext fun j => ?_
  show aeval (Sum.elim P.one Q.one) (rename Sum.inr (X j)) = aeval Q.one (X j)
  exact P.prod_oneHom_renameR Q (X j)

theorem prod_antipode_comp_prodMkL :
    (P.prod Q).antipode.comp (P.prodMkL Q) = (P.prodMkL Q).comp P.antipode := by
  refine quotAlgHom_ext fun i => ?_
  show Ideal.Quotient.mk (P.prodIdeal Q) (aeval (P.prodInv Q) (rename Sum.inl (X i)))
    = P.prodMkL Q (Ideal.Quotient.mk P.I (aeval P.inv (X i)))
  exact P.prod_invHom_renameL Q (X i)

theorem prod_antipode_comp_prodMkR :
    (P.prod Q).antipode.comp (P.prodMkR Q) = (P.prodMkR Q).comp Q.antipode := by
  refine quotAlgHom_ext fun j => ?_
  show Ideal.Quotient.mk (P.prodIdeal Q) (aeval (P.prodInv Q) (rename Sum.inr (X j)))
    = P.prodMkR Q (Ideal.Quotient.mk Q.I (aeval Q.inv (X j)))
  exact P.prod_invHom_renameR Q (X j)

end Prod

end GroupData

/-- **A group presented by polynomials**: group data whose induced maps satisfy the Hopf
axioms (the hypotheses of `Bialgebra.ofAlgHom` and the antipode laws), as identities of
algebra maps out of `K[γ] ⧸ I` — checked on the generators `X i`, never on `K`-points.
The consumers' groups (the pair model of `GL_n` with `I = (gh − 1, hg − 1)`, its
centralisers `(gN − Ng)`, Borels) are of this form. -/
structure GroupPresentation (K : Type u) [Field K] (γ : Type u) extends GroupData K γ where
  coassoc : (Algebra.TensorProduct.assoc K K K toGroupData.CoordRing toGroupData.CoordRing
      toGroupData.CoordRing).toAlgHom.comp
      ((Algebra.TensorProduct.map toGroupData.comul (.id K _)).comp toGroupData.comul)
    = (Algebra.TensorProduct.map (.id K _) toGroupData.comul).comp toGroupData.comul
  rTensor_counit : (Algebra.TensorProduct.map toGroupData.counit (.id K _)).comp toGroupData.comul
    = (Algebra.TensorProduct.lid K toGroupData.CoordRing).symm
  lTensor_counit : (Algebra.TensorProduct.map (.id K _) toGroupData.counit).comp toGroupData.comul
    = (Algebra.TensorProduct.rid K K toGroupData.CoordRing).symm
  mul_antipode_rTensor : (Algebra.TensorProduct.lmul' K).comp
      ((Algebra.TensorProduct.map toGroupData.antipode (.id K _)).comp toGroupData.comul)
    = (Algebra.ofId K toGroupData.CoordRing).comp toGroupData.counit
  mul_antipode_lTensor : (Algebra.TensorProduct.lmul' K).comp
      ((Algebra.TensorProduct.map (.id K _) toGroupData.antipode).comp toGroupData.comul)
    = (Algebra.ofId K toGroupData.CoordRing).comp toGroupData.counit

namespace GroupPresentation

variable (P : GroupPresentation K γ)

/-- The Hopf data of a presentation. -/
noncomputable def hopfData : CommHopfData K P.CoordRing :=
  ⟨P.comul, P.counit, P.antipode, P.coassoc, P.rTensor_counit, P.lTensor_counit,
    P.mul_antipode_rTensor, P.mul_antipode_lTensor⟩

/-- **A presented group from the group laws as polynomial identities.**  The five Hopf
axioms of a `GroupData` are exactly associativity of `mul` modulo the ideal of a triple of
group elements, the two unit laws and the two inverse laws modulo `I`; each is checked on
the generators `X i`, where both sides of the axiom are the images of the corresponding
polynomials under a fixed algebra map killing the ideal (`GroupData.law_of_comp`). -/
noncomputable def ofLaws (P : GroupData K γ)
    (hassoc : ∀ i, P.mulAssocL i - P.mulAssocR i ∈ P.tripleIdeal)
    (hone_mul : ∀ i, P.oneMul i - X i ∈ P.I) (hmul_one : ∀ i, P.mulOne i - X i ∈ P.I)
    (hinv_mul : ∀ i, P.invMul i - C (P.one i) ∈ P.I)
    (hmul_inv : ∀ i, P.mulInv i - C (P.one i) ∈ P.I) :
    GroupPresentation K γ where
  toGroupData := P
  coassoc := P.coassoc_of hassoc
  rTensor_counit := P.rTensor_counit_of hone_mul
  lTensor_counit := P.lTensor_counit_of hmul_one
  mul_antipode_rTensor := P.mul_antipode_rTensor_of hinv_mul
  mul_antipode_lTensor := P.mul_antipode_lTensor_of hmul_inv

@[simp] theorem ofLaws_toGroupData (P : GroupData K γ)
    (hassoc : ∀ i, P.mulAssocL i - P.mulAssocR i ∈ P.tripleIdeal)
    (hone_mul : ∀ i, P.oneMul i - X i ∈ P.I) (hmul_one : ∀ i, P.mulOne i - X i ∈ P.I)
    (hinv_mul : ∀ i, P.invMul i - C (P.one i) ∈ P.I)
    (hmul_inv : ∀ i, P.mulInv i - C (P.one i) ∈ P.I) :
    (ofLaws P hassoc hone_mul hmul_one hinv_mul hmul_inv).toGroupData = P :=
  rfl

/-! #### Closed subgroups -/

section Restrict

variable {J : Ideal (MvPolynomial γ K)} (hIJ : P.I ≤ J)
  (hmul : ∀ f ∈ J, Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K J)
    (Ideal.Quotient.mkₐ K J) (tensorOfSum K γ (aeval P.mul f)) = 0)
  (hinv : ∀ f ∈ J, Ideal.Quotient.mk J (aeval P.inv f) = 0)
  (hone : ∀ f ∈ J, aeval P.one f = 0)

/-- The Hopf data of a closed subgroup: `P`'s, pushed forward along the surjection
`K[γ] ⧸ I → K[γ] ⧸ J` (`GroupData.restrict_comul_comp` and friends). -/
noncomputable def restrictHopfData :
    CommHopfData K (P.toGroupData.restrict J hmul hinv hone).CoordRing :=
  P.hopfData.ofSurjective (Ideal.Quotient.factorₐ K hIJ)
    (Ideal.Quotient.factor_surjective hIJ)
    (P.toGroupData.restrict J hmul hinv hone).comul
    (P.toGroupData.restrict J hmul hinv hone).counit
    (P.toGroupData.restrict J hmul hinv hone).antipode
    (P.toGroupData.restrict_comul_comp hmul hinv hone hIJ)
    (P.toGroupData.restrict_counit_comp hmul hinv hone hIJ)
    (P.toGroupData.restrict_antipode_comp hmul hinv hone hIJ)

/-- **A closed subgroup of a presented group is a presented group**: the same polynomials,
the larger ideal `J`.  The five Hopf axioms are `P`'s, pushed forward along the surjection
`K[γ] ⧸ I → K[γ] ⧸ J` (`CommHopfData.ofSurjective`); no `K`-point computation is involved,
so no geometric reducedness is needed. -/
noncomputable def restrict : GroupPresentation K γ where
  toGroupData := P.toGroupData.restrict J hmul hinv hone
  coassoc := (P.restrictHopfData hIJ hmul hinv hone).coassoc
  rTensor_counit := (P.restrictHopfData hIJ hmul hinv hone).rTensor_counit
  lTensor_counit := (P.restrictHopfData hIJ hmul hinv hone).lTensor_counit
  mul_antipode_rTensor := (P.restrictHopfData hIJ hmul hinv hone).mul_antipode_rTensor
  mul_antipode_lTensor := (P.restrictHopfData hIJ hmul hinv hone).mul_antipode_lTensor

@[simp] theorem restrict_toGroupData :
    (P.restrict hIJ hmul hinv hone).toGroupData
      = P.toGroupData.restrict J hmul hinv hone := rfl

end Restrict

/-! #### Products -/

section Prod

variable {δ : Type u} (Q : GroupPresentation K δ)

/-- The Hopf data of a product of presented groups: `CommHopfData.ofPair` along the two
blocks of coordinates, whose three transport identities are
`GroupData.prod_comul_comp_prodMkL` and friends. -/
noncomputable def prodHopfData :
    CommHopfData K (P.toGroupData.prod Q.toGroupData).CoordRing :=
  P.hopfData.ofPair Q.hopfData (P.toGroupData.prodMkL Q.toGroupData)
    (P.toGroupData.prodMkR Q.toGroupData)
    (by
      intro D _ _ φ ψ hL hR
      exact sumAlgHom_ext P.I Q.I hL hR)
    (P.toGroupData.prod Q.toGroupData).comul
    (P.toGroupData.prod Q.toGroupData).counit
    (P.toGroupData.prod Q.toGroupData).antipode
    (P.toGroupData.prod_comul_comp_prodMkL Q.toGroupData)
    (P.toGroupData.prod_counit_comp_prodMkL Q.toGroupData)
    (P.toGroupData.prod_antipode_comp_prodMkL Q.toGroupData)
    (P.toGroupData.prod_comul_comp_prodMkR Q.toGroupData)
    (P.toGroupData.prod_counit_comp_prodMkR Q.toGroupData)
    (P.toGroupData.prod_antipode_comp_prodMkR Q.toGroupData)

/-- **The product of two presented groups is a presented group.**  The five Hopf axioms
are those of the two factors, carried along the two block maps of coordinate rings; no
`K`-point computation is involved. -/
noncomputable def prod : GroupPresentation K (γ ⊕ δ) where
  toGroupData := P.toGroupData.prod Q.toGroupData
  coassoc := (P.prodHopfData Q).coassoc
  rTensor_counit := (P.prodHopfData Q).rTensor_counit
  lTensor_counit := (P.prodHopfData Q).lTensor_counit
  mul_antipode_rTensor := (P.prodHopfData Q).mul_antipode_rTensor
  mul_antipode_lTensor := (P.prodHopfData Q).mul_antipode_lTensor

@[simp] theorem prod_toGroupData :
    (P.prod Q).toGroupData = P.toGroupData.prod Q.toGroupData := rfl

/-- **The `K`-points of a product of presented groups are the pairs of `K`-points.** -/
theorem prod_pts :
    (P.prod Q).pts = {x : γ ⊕ δ → K | x ∘ Sum.inl ∈ P.pts ∧ x ∘ Sum.inr ∈ Q.pts} :=
  P.toGroupData.prod_pts Q.toGroupData

end Prod

end GroupPresentation

/-- **The coordinate ring of a presented group is a Hopf algebra.**  This is the instance that
makes `P.scheme` a group object: mathlib's `instGrpObjSpecAsOverSpec` reads
`GrpObj ((Spec A).asOver (Spec K))` off `HopfAlgebra K A`. -/
noncomputable instance instHopfAlgebraCoordRing (P : GroupPresentation K γ) :
    HopfAlgebra K P.CoordRing :=
  P.hopfData.toHopfAlgebra

/-- Sanity check: the group scheme of a presentation is a group object over `Spec K`. -/
noncomputable example (P : GroupPresentation K γ) : GrpObj P.scheme := inferInstance

namespace GroupPresentation

variable (P : GroupPresentation K γ)

/-! #### The group laws on `K`-points

The Hopf structure of `P.CoordRing` makes `WithConv (P.CoordRing →ₐ[K] K)` a group
(`AlgHom.convGroup`), and `GroupData.ptHom` carries the product, the inverse and the unit
of `pts` to the convolution product, the convolution inverse and the convolution unit.  The
group laws on `pts` are therefore the group laws of that convolution group; no `K`-point
computation with the polynomials is needed. -/

theorem comulAlgHom_eq : Bialgebra.comulAlgHom K P.CoordRing = P.comul := rfl

theorem counitAlgHom_eq : Bialgebra.counitAlgHom K P.CoordRing = P.counit := rfl

theorem antipodeAlgHom_eq : HopfAlgebra.antipodeAlgHom K P.CoordRing = P.antipode := rfl

/-- The evaluation maps of `K`-points multiply by convolution. -/
theorem toConv_ptHom_mulPt {a b : γ → K} (ha : a ∈ P.pts) (hb : b ∈ P.pts) :
    WithConv.toConv (P.ptHom (P.mulPt_mem ha hb)) =
      WithConv.toConv (P.ptHom ha) * WithConv.toConv (P.ptHom hb) := by
  rw [P.ptHom_mulPt ha hb, AlgHom.convMul_def, ← AlgHom.comp_assoc,
    Algebra.TensorProduct.lmul'_comp_map, P.comulAlgHom_eq]

/-- The evaluation map of the unit is the unit of the convolution group. -/
theorem toConv_ptHom_one : WithConv.toConv (P.ptHom P.one_mem_pts) = 1 := by
  rw [AlgHom.convOne_def, P.ptHom_one, ← P.counitAlgHom_eq]
  rfl

/-- The evaluation map of an inverse is the convolution inverse. -/
theorem toConv_ptHom_invPt {a : γ → K} (ha : a ∈ P.pts) :
    WithConv.toConv (P.ptHom (P.invPt_mem ha)) = (WithConv.toConv (P.ptHom ha))⁻¹ := by
  rw [P.ptHom_invPt ha, ← P.antipodeAlgHom_eq]
  rfl

theorem mulPt_assoc {a b c : γ → K} (ha : a ∈ P.pts) (hb : b ∈ P.pts) (hc : c ∈ P.pts) :
    P.mulPt (P.mulPt a b) c = P.mulPt a (P.mulPt b c) := by
  refine P.pt_eq_of_ptHom_eq (P.mulPt_mem (P.mulPt_mem ha hb) hc)
    (P.mulPt_mem ha (P.mulPt_mem hb hc)) (WithConv.toConv_injective ?_)
  rw [P.toConv_ptHom_mulPt (P.mulPt_mem ha hb) hc, P.toConv_ptHom_mulPt ha hb,
    P.toConv_ptHom_mulPt ha (P.mulPt_mem hb hc), P.toConv_ptHom_mulPt hb hc, mul_assoc]

theorem mulPt_invPt {a : γ → K} (ha : a ∈ P.pts) : P.mulPt a (P.invPt a) = P.one := by
  refine P.pt_eq_of_ptHom_eq (P.mulPt_mem ha (P.invPt_mem ha)) P.one_mem_pts
    (WithConv.toConv_injective ?_)
  rw [P.toConv_ptHom_mulPt ha (P.invPt_mem ha), P.toConv_ptHom_invPt ha, P.toConv_ptHom_one]
  exact mul_inv_cancel (WithConv.toConv (P.ptHom ha))

theorem invPt_mulPt {a : γ → K} (ha : a ∈ P.pts) : P.mulPt (P.invPt a) a = P.one := by
  refine P.pt_eq_of_ptHom_eq (P.mulPt_mem (P.invPt_mem ha) ha) P.one_mem_pts
    (WithConv.toConv_injective ?_)
  rw [P.toConv_ptHom_mulPt (P.invPt_mem ha) ha, P.toConv_ptHom_invPt ha, P.toConv_ptHom_one]
  exact inv_mul_cancel (WithConv.toConv (P.ptHom ha))

-- `CategoryTheory.Hom.monoid` (the group law on sections) is a scoped instance of `MonObj`,
-- and that scope's `γ` notation for `ModObj.smul` shadows the index type `γ`.
attribute [local instance] CategoryTheory.Hom.monoid

/-- **The unit `K`-point is the unit section.** -/
theorem sec_one : P.sec P.one_mem_pts = 1 :=
  Over.OverMorphism.ext (by
    show Spec.map (CommRingCat.ofHom P.counit.toRingHom) =
      (CartesianMonoidalCategory.toUnit (𝟙_ (Over (Spec (.of K)))) ≫
        (MonObj.one : _ ⟶ P.scheme)).left
    rw [Over.comp_left, AlgebraicGeometry.one_spec_asOver_spec_left]
    show _ = 𝟙 _ ≫ _
    rw [Category.id_comp]
    rfl)

set_option maxHeartbeats 1000000 in
/-- **The product of `K`-points is the product of the sections** (`Hom.mul_def`,
`mul_spec_asOver_spec_left`, `ptHom_mulPt`). -/
theorem sec_mulPt {a b : γ → K} (ha : a ∈ P.pts) (hb : b ∈ P.pts) :
    P.sec (P.mulPt_mem ha hb) = P.sec ha * P.sec hb := by
  refine Over.OverMorphism.ext ?_
  have hmul : (P.sec ha * P.sec hb).left =
      (CartesianMonoidalCategory.lift (secOfAlgHom (P.ptHom ha))
        (secOfAlgHom (P.ptHom hb))).left ≫
      ((pullbackSpecIso K P.CoordRing P.CoordRing).hom ≫
        Spec.map (CommRingCat.ofHom P.comul.toRingHom)) := rfl
  rw [hmul]
  refine Eq.trans ?_ (Category.assoc _ _ _)
  rw [lift_secOfAlgHom (P.ptHom ha) (P.ptHom hb)]
  refine Eq.trans ?_ (Spec.map_comp _ _)
  rw [← CommRingCat.ofHom_comp, GroupData.sec_left]
  congr 2
  exact congrArg AlgHom.toRingHom (P.ptHom_mulPt ha hb)

/-! #### The group as a monoid object of `(CommAlgCat K)ᵒᵖ`

Mathlib's monoid object `instMonObjSpecAsOverSpec` on `P.scheme` is by construction the
image of a monoid object of `(CommAlgCat K)ᵒᵖ` under `algSpec` (`bialgSpec` is
`… ⋙ (algSpec R).mapMon`).  `opMonObj` is that monoid object read off the presentation, and
`one_scheme`/`mul_scheme` say the two agree — the input `modObjObj` needs. -/

open scoped MonObj in
set_option maxHeartbeats 1000000 in
/-- The coordinate ring of a presented group as a monoid object of `(CommAlgCat K)ᵒᵖ`: the
comultiplication and the counit, with the bialgebra axioms read in the opposite category. -/
@[instance_reducible]
noncomputable def opMonObj : MonObj (op (CommAlgCat.of K P.CoordRing)) where
  one := (CommAlgCat.ofHom P.counit).op
  mul := (CommAlgCat.ofHom P.comul).op
  one_mul := by
    refine Quiver.Hom.unop_inj (CommAlgCat.hom_ext ?_)
    simp only [unop_comp, unop_whiskerRight, Quiver.Hom.unop_op, CommAlgCat.hom_comp,
      CommAlgCat.whiskerRight_hom, CommAlgCat.hom_ofHom]
    exact P.rTensor_counit
  mul_one := by
    refine Quiver.Hom.unop_inj (CommAlgCat.hom_ext ?_)
    simp only [unop_comp, unop_whiskerLeft, Quiver.Hom.unop_op, CommAlgCat.hom_comp,
      CommAlgCat.whiskerLeft_hom, CommAlgCat.hom_ofHom]
    exact P.lTensor_counit
  mul_assoc := by
    refine Quiver.Hom.unop_inj (CommAlgCat.hom_ext ?_)
    simp only [unop_comp, unop_whiskerRight, unop_whiskerLeft, Quiver.Hom.unop_op,
      CommAlgCat.hom_comp, CommAlgCat.whiskerRight_hom, CommAlgCat.whiskerLeft_hom,
      CommAlgCat.hom_ofHom]
    have hα : (CommAlgCat.Hom.hom (α_ (op (CommAlgCat.of K P.CoordRing))
          (op (CommAlgCat.of K P.CoordRing)) (op (CommAlgCat.of K P.CoordRing))).hom.unop) =
        (Algebra.TensorProduct.assoc K K K P.CoordRing P.CoordRing P.CoordRing).symm.toAlgHom :=
      rfl
    rw [hα, ← P.coassoc, ← AlgHom.comp_assoc]
    have hid : ((Algebra.TensorProduct.assoc K K K P.CoordRing P.CoordRing
        P.CoordRing).symm.toAlgHom).comp
        (Algebra.TensorProduct.assoc K K K P.CoordRing P.CoordRing P.CoordRing).toAlgHom
        = AlgHom.id K _ := by
      ext x <;> simp
    rw [hid, AlgHom.id_comp]

open scoped MonObj in
set_option maxHeartbeats 1000000 in
/-- The unit of the group object `P.scheme` is `Spec` of the counit. -/
theorem one_scheme :
    letI := P.opMonObj
    (η : 𝟙_ (Over (Spec (.of K))) ⟶ P.scheme) =
      Functor.LaxMonoidal.ε (algSpec (CommRingCat.of K)) ≫
        (algSpec (CommRingCat.of K)).map (η : _ ⟶ op (CommAlgCat.of K P.CoordRing)) := rfl

open scoped MonObj in
set_option maxHeartbeats 1000000 in
/-- The product of the group object `P.scheme` is `Spec` of the comultiplication. -/
theorem mul_scheme :
    letI := P.opMonObj
    (μ : P.scheme ⊗ P.scheme ⟶ P.scheme) =
      Functor.LaxMonoidal.μ (algSpec (CommRingCat.of K)) (op (CommAlgCat.of K P.CoordRing))
          (op (CommAlgCat.of K P.CoordRing)) ≫
        (algSpec (CommRingCat.of K)).map (μ : _ ⟶ op (CommAlgCat.of K P.CoordRing)) := rfl

end GroupPresentation

/-! ### An action presented by polynomials -/

/-- The algebra map `K[γ ⊕ ι] → K[ι] ⊗ K[γ]` of a right coaction:
`X (inl j) ↦ 1 ⊗ X j`, `X (inr i) ↦ X i ⊗ 1`. -/
noncomputable def tensorOfSum' (K : Type u) [Field K] (γ ι : Type u) :
    MvPolynomial (γ ⊕ ι) K →ₐ[K] MvPolynomial ι K ⊗[K] MvPolynomial γ K :=
  aeval (Sum.elim (fun j => 1 ⊗ₜ X j) (fun i => X i ⊗ₜ 1))

/-- **The data of an action presented by polynomials**: an ideal `J ⊆ K[ι]` cutting out the
space and the coordinates `act : ι → K[γ ⊕ ι]` of the action, descending to a coaction
`K[ι] ⧸ J → (K[ι] ⧸ J) ⊗ (K[γ] ⧸ I)`. -/
structure ActionData (P : GroupData K γ) (ι : Type u) where
  J : Ideal (MvPolynomial ι K)
  act : ι → MvPolynomial (γ ⊕ ι) K
  act_mem : ∀ f ∈ J, Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K J) (Ideal.Quotient.mkₐ K P.I)
    (tensorOfSum' K γ ι (aeval act f)) = 0

namespace ActionData

variable {P : GroupData K γ} (A : ActionData P ι)

/-- The coordinate ring of the space. -/
abbrev CoordRing : Type u := MvPolynomial ι K ⧸ A.J

/-- The coaction `B → B ⊗ A`. -/
noncomputable def coact : A.CoordRing →ₐ[K] A.CoordRing ⊗[K] P.CoordRing :=
  Ideal.Quotient.liftₐ A.J
    ((Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K A.J) (Ideal.Quotient.mkₐ K P.I)).comp
      ((tensorOfSum' K γ ι).comp (aeval A.act)))
    (fun f hf => A.act_mem f hf)

/-- The coaction, read on the generators (`Ideal.Quotient.liftₐ_comp`). -/
theorem coact_comp_mkₐ :
    A.coact.comp (Ideal.Quotient.mkₐ K A.J)
      = (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K A.J) (Ideal.Quotient.mkₐ K P.I)).comp
        ((tensorOfSum' K γ ι).comp (aeval A.act)) :=
  Ideal.Quotient.liftₐ_comp _ _ _

/-- The `K`-points of the space. -/
def pts : Set (ι → K) := MvPolynomial.zeroLocus K A.J

/-- The action on `K`-points. -/
noncomputable def actPt (a : γ → K) (x : ι → K) : ι → K :=
  fun i => aeval (Sum.elim a x) (A.act i)

/-- The space, as a scheme over `Spec K`. -/
noncomputable abbrev scheme : Over (Spec (.of K)) :=
  (Spec (.of A.CoordRing)).asOver (Spec (.of K))

instance isAffine_scheme_left : IsAffine A.scheme.left :=
  inferInstanceAs (IsAffine (Spec (.of A.CoordRing)))

instance finiteType_coordRing [Finite ι] : Algebra.FiniteType K A.CoordRing :=
  inferInstance

instance locallyOfFiniteType_scheme_hom [Finite ι] : LocallyOfFiniteType A.scheme.hom :=
  letI : Algebra.FiniteType (CommRingCat.of K) (CommRingCat.of A.CoordRing) :=
    inferInstanceAs (Algebra.FiniteType K A.CoordRing)
  locallyOfFiniteType_specOverSpec (R := CommRingCat.of K) (A := CommRingCat.of A.CoordRing)

/-- Evaluation at a `K`-point of the space, as an algebra map on the coordinate ring. -/
noncomputable def ptHom {x : ι → K} (hx : x ∈ A.pts) : A.CoordRing →ₐ[K] K :=
  Ideal.Quotient.liftₐ A.J (aeval x) (fun f hf => hx f hf)

@[simp] theorem ptHom_mk {x : ι → K} (hx : x ∈ A.pts) (f : MvPolynomial ι K) :
    A.ptHom hx (Ideal.Quotient.mk A.J f) = aeval x f := rfl

/-- A `K`-point of the space is determined by its evaluation map. -/
theorem pt_eq_of_ptHom_eq {x y : ι → K} (hx : x ∈ A.pts) (hy : y ∈ A.pts)
    (h : A.ptHom hx = A.ptHom hy) : x = y := by
  funext i
  have := congrArg (fun φ : A.CoordRing →ₐ[K] K => φ (Ideal.Quotient.mk A.J (X i))) h
  simpa using this

/-- Evaluating a point of the space and a point of the group on `K[ι] ⊗ K[γ]` through
`tensorOfSum'` is evaluation at the concatenated tuple. -/
private theorem lift_comp_tensorOfSum' {a : γ → K} (ha : a ∈ P.pts) {x : ι → K}
    (hx : x ∈ A.pts) :
    (Algebra.TensorProduct.lift (A.ptHom hx) (P.ptHom ha) (fun _ _ => Commute.all _ _)).comp
      ((Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K A.J) (Ideal.Quotient.mkₐ K P.I)).comp
        (tensorOfSum' K γ ι))
      = aeval (Sum.elim a x) := by
  refine MvPolynomial.algHom_ext fun i => ?_
  cases i <;> simp [tensorOfSum']

/-- The coordinates of an acted-on `K`-point are the coaction evaluated at the pair. -/
private theorem eval_actPt {a : γ → K} (ha : a ∈ P.pts) {x : ι → K} (hx : x ∈ A.pts) :
    (Algebra.TensorProduct.lift (A.ptHom hx) (P.ptHom ha) (fun _ _ => Commute.all _ _)).comp
      ((Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K A.J) (Ideal.Quotient.mkₐ K P.I)).comp
        ((tensorOfSum' K γ ι).comp (aeval A.act)))
      = aeval (A.actPt a x) := by
  have h : ((Algebra.TensorProduct.lift (A.ptHom hx) (P.ptHom ha)
      (fun _ _ => Commute.all _ _)).comp
      ((Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K A.J) (Ideal.Quotient.mkₐ K P.I)).comp
        (tensorOfSum' K γ ι))).comp (aeval A.act)
      = (aeval (Sum.elim a x)).comp (aeval A.act) := by
    rw [A.lift_comp_tensorOfSum' ha hx]
  refine (AlgHom.comp_assoc _ _ _).symm.trans (h.trans ?_)
  exact MvPolynomial.algHom_ext fun i => by simp [actPt]

/-- **`pts` is stable under the action.** -/
theorem actPt_mem {a : γ → K} (ha : a ∈ P.pts) {x : ι → K} (hx : x ∈ A.pts) :
    A.actPt a x ∈ A.pts := by
  intro f hf
  rw [← A.eval_actPt ha hx]
  show (Algebra.TensorProduct.lift (A.ptHom hx) (P.ptHom ha) (fun _ _ => Commute.all _ _))
    ((Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K A.J) (Ideal.Quotient.mkₐ K P.I))
      (tensorOfSum' K γ ι (aeval A.act f))) = 0
  rw [A.act_mem f hf, map_zero]

/-- The evaluation map of an acted-on `K`-point factors through the coaction. -/
theorem ptHom_actPt {a : γ → K} (ha : a ∈ P.pts) {x : ι → K} (hx : x ∈ A.pts) :
    A.ptHom (A.actPt_mem ha hx) =
      (Algebra.TensorProduct.lift (A.ptHom hx) (P.ptHom ha)
        (fun _ _ => Commute.all _ _)).comp A.coact := by
  refine Ideal.Quotient.algHom_ext K ?_
  simp only [ptHom, coact, AlgHom.comp_assoc, Ideal.Quotient.liftₐ_comp]
  exact (A.eval_actPt ha hx).symm

/-- The section of `A.scheme` over `Spec K` at a `K`-point. -/
noncomputable def sec {x : ι → K} (hx : x ∈ A.pts) :
    𝟙_ (Over (Spec (.of K))) ⟶ A.scheme :=
  secOfAlgHom (A.ptHom hx)

@[simp] theorem sec_left {x : ι → K} (hx : x ∈ A.pts) :
    (A.sec hx).left = Spec.map (CommRingCat.ofHom (A.ptHom hx).toRingHom) := rfl

/-- The `K`-point of a section of `A.scheme`. -/
noncomputable def ptOfSec (s : 𝟙_ (Over (Spec (.of K))) ⟶ A.scheme) : ι → K :=
  fun i => algHomOfSec s (Ideal.Quotient.mk A.J (X i))

theorem ptOfSec_mem (s : 𝟙_ (Over (Spec (.of K))) ⟶ A.scheme) : A.ptOfSec s ∈ A.pts := by
  intro f hf
  have h : (algHomOfSec s).comp (Ideal.Quotient.mkₐ K A.J) = aeval (A.ptOfSec s) :=
    MvPolynomial.algHom_ext fun i => by simp [ptOfSec, Ideal.Quotient.mkₐ_eq_mk]
  have h' := congrArg (fun φ : MvPolynomial ι K →ₐ[K] K => φ f) h
  rw [← h']
  show algHomOfSec s (Ideal.Quotient.mk A.J f) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hf, map_zero]

theorem ptHom_ptOfSec (s : 𝟙_ (Over (Spec (.of K))) ⟶ A.scheme) :
    A.ptHom (A.ptOfSec_mem s) = algHomOfSec s :=
  Ideal.Quotient.algHom_ext K (MvPolynomial.algHom_ext fun i => by
    simp [ptOfSec, ptHom, Ideal.Quotient.mkₐ_eq_mk])

/-- **Sections of `A.scheme` are `K`-points** (`sec` and `ptOfSec` are inverse). -/
@[simp] theorem sec_ptOfSec (s : 𝟙_ (Over (Spec (.of K))) ⟶ A.scheme) :
    A.sec (A.ptOfSec_mem s) = s := by
  rw [sec, ptHom_ptOfSec, secOfAlgHom_algHomOfSec]

@[simp] theorem ptOfSec_sec {x : ι → K} (hx : x ∈ A.pts) : A.ptOfSec (A.sec hx) = x := by
  funext i
  show algHomOfSec (secOfAlgHom (A.ptHom hx)) (Ideal.Quotient.mk A.J (X i)) = x i
  rw [algHomOfSec_secOfAlgHom, ptHom_mk]
  simp

/-- The space is the closed subscheme `V(J)` of `𝔸(ι; Spec K)`; its `K`-points are `A.pts`
(the analogue of `GroupData.pt_scheme_iff`). -/
theorem pt_scheme_iff (x : ι → K) :
    (∃ g : Spec (.of K) ⟶ Spec (.of A.CoordRing),
      g ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk A.J)) ≫ (specIso K ι).inv =
        (ptEquiv K x).1) ↔ x ∈ A.pts := by
  have hpt : (ptEquiv K x).1 =
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := K) x).toRingHom) ≫
        (specIso K ι).inv := by
    rw [← ptEquiv_comp_specIso, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  constructor
  · rintro ⟨g, hg⟩
    rw [hpt, ← Category.assoc] at hg
    replace hg := (cancel_mono (specIso K ι).inv).mp hg
    have hg' : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk A.J) ≫ Spec.preimage g) =
        Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := K) x).toRingHom) := by
      rw [Spec.map_comp, Spec.map_preimage]
      exact hg
    have hcomp := Spec.map_injective hg'
    intro f hf
    have := congrArg
      (fun ψ : CommRingCat.of (MvPolynomial ι K) ⟶ CommRingCat.of K => ψ f) hcomp
    simpa [Ideal.Quotient.eq_zero_iff_mem.mpr hf] using this.symm
  · intro hx
    refine ⟨Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.liftₐ A.J (MvPolynomial.aeval (R := K) x) (fun f hf => hx f hf)).toRingHom),
      ?_⟩
    rw [hpt, ← Category.assoc, ← Spec.map_comp]
    congr 2

/-- The coordinates of a group element and a point of the space, in the two coordinate
rings: `X (inl j) ↦ 1 ⊗ aⱼ`, `X (inr i) ↦ xᵢ ⊗ 1`. -/
noncomputable def coordAct : MvPolynomial (γ ⊕ ι) K →ₐ[K] A.CoordRing ⊗[K] P.CoordRing :=
  (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K A.J) (Ideal.Quotient.mkₐ K P.I)).comp
    (tensorOfSum' K γ ι)

@[simp] theorem coordAct_X_inl (j : γ) :
    A.coordAct (X (Sum.inl j)) = 1 ⊗ₜ[K] Ideal.Quotient.mk P.I (X j) := by
  simp [coordAct, tensorOfSum']

@[simp] theorem coordAct_X_inr (i : ι) :
    A.coordAct (X (Sum.inr i)) = Ideal.Quotient.mk A.J (X i) ⊗ₜ[K] 1 := by
  simp [coordAct, tensorOfSum']

theorem mkJ_eq_zero {g : MvPolynomial ι K} (hg : g ∈ A.J) :
    Ideal.Quotient.mk A.J g = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hg

theorem mkJ_C (r : K) : Ideal.Quotient.mk A.J (C r) = algebraMap K A.CoordRing r := rfl

theorem coact_mk_X (i : ι) :
    A.coact (Ideal.Quotient.mk A.J (X i)) = A.coordAct (A.act i) := by
  have h := AlgHom.congr_fun A.coact_comp_mkₐ (X i)
  simpa [coordAct] using h

/-- **The transfer of an action law to a comodule axiom on a generator.** -/
theorem act_law_of_comp {B δ : Type u} [CommRing B] [Algebra K B]
    {J' : Ideal (MvPolynomial δ K)}
    (Φ : (A.CoordRing ⊗[K] P.CoordRing) →ₐ[K] B) (Ψ : MvPolynomial δ K →ₐ[K] B)
    (σ : γ ⊕ ι → MvPolynomial δ K) (hΦ : Φ.comp A.coordAct = Ψ.comp (aeval σ))
    (hΨ : ∀ g ∈ J', Ψ g = 0) (i : ι) {r : MvPolynomial δ K}
    (hlaw : aeval σ (A.act i) - r ∈ J') :
    Φ (A.coact (Ideal.Quotient.mk A.J (X i))) = Ψ r := by
  have h := hΨ _ hlaw
  rw [map_sub, sub_eq_zero] at h
  rw [A.coact_mk_X, ← AlgHom.comp_apply, hΦ, AlgHom.comp_apply]
  exact h

/-! #### The action laws as polynomial identities -/

/-- The coordinates of `1 · x`. -/
noncomputable def oneAct : ι → MvPolynomial ι K := fun i => aeval (Sum.elim (fun j => C (P.one j)) X) (A.act i)

/-- The ideal of `K[γ ⊕ γ ⊕ ι]` generated by `I` in the two group blocks and by `J` in the
space block. -/
noncomputable def actTripleIdeal : Ideal (MvPolynomial (γ ⊕ γ ⊕ ι) K) := sumIdeal P.I (sumIdeal P.I A.J)

/-- The coordinates of a pair of group elements and a point. -/
noncomputable def coordActPair :
    MvPolynomial (γ ⊕ γ ⊕ ι) K →ₐ[K] A.CoordRing ⊗[K] (P.CoordRing ⊗[K] P.CoordRing) :=
  aeval (Sum.elim
    (fun j => (1 : A.CoordRing) ⊗ₜ[K] (Ideal.Quotient.mk P.I (X j) ⊗ₜ[K] (1 : P.CoordRing)))
    (Sum.elim
      (fun j => (1 : A.CoordRing) ⊗ₜ[K] ((1 : P.CoordRing) ⊗ₜ[K] Ideal.Quotient.mk P.I (X j)))
      (fun i => Ideal.Quotient.mk A.J (X i) ⊗ₜ[K] (1 : P.CoordRing ⊗[K] P.CoordRing))))

private theorem apply_rename_eq_zero_J {δ B : Type u} [CommRing B] [Algebra K B]
    (φ : MvPolynomial δ K →ₐ[K] B) (ρ : ι → δ) (v : A.CoordRing →ₐ[K] B)
    (hv : ∀ i, φ (X (ρ i)) = v (Ideal.Quotient.mk A.J (X i))) {g : MvPolynomial ι K}
    (hg : g ∈ A.J) : φ (rename ρ g) = 0 := by
  have e : φ.comp (rename ρ) = v.comp (Ideal.Quotient.mkₐ K A.J) :=
    MvPolynomial.algHom_ext fun i => by simpa using hv i
  have hgg := AlgHom.congr_fun e g
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at hgg
  rw [hgg, A.mkJ_eq_zero hg, map_zero]

theorem coordActPair_eq_zero {f : MvPolynomial (γ ⊕ γ ⊕ ι) K} (hf : f ∈ A.actTripleIdeal) :
    A.coordActPair f = 0 := by
  refine sumIdeal_apply_eq_zero _ _ A.coordActPair (fun g hg => ?_) (fun g hg => ?_) hf
  · exact GroupData.apply_rename_eq_zero P A.coordActPair Sum.inl
      (Algebra.TensorProduct.includeRight.comp Algebra.TensorProduct.includeLeft)
      (fun j => by simp [coordActPair]) hg
  · refine sumIdeal_apply_eq_zero _ _ (A.coordActPair.comp (rename Sum.inr))
      (fun t ht => ?_) (fun t ht => ?_) hg
    · exact GroupData.apply_rename_eq_zero P _ Sum.inl
        (Algebra.TensorProduct.includeRight.comp Algebra.TensorProduct.includeRight)
        (fun j => by simp [coordActPair]) ht
    · exact A.apply_rename_eq_zero_J _ Sum.inr Algebra.TensorProduct.includeLeft
        (fun i => by simp [coordActPair]) ht

/-- The action of the first group block on the point. -/
noncomputable def act1 : ι → MvPolynomial (γ ⊕ γ ⊕ ι) K := fun i =>
  aeval (Sum.elim (fun j => X (Sum.inl j)) fun k => X (Sum.inr (Sum.inr k))) (A.act i)

/-- The coordinates of `b · (a · x)`. -/
noncomputable def actAct : ι → MvPolynomial (γ ⊕ γ ⊕ ι) K := fun i =>
  aeval (Sum.elim (fun j => X (Sum.inr (Sum.inl j))) A.act1) (A.act i)

/-- The coordinates of `(b a) · x`. -/
noncomputable def mulAct : ι → MvPolynomial (γ ⊕ γ ⊕ ι) K := fun i =>
  aeval (Sum.elim (P.mulFlip ι) fun k => X (Sum.inr (Sum.inr k))) (A.act i)

theorem counit_coact_of (h : ∀ i, A.oneAct i - X i ∈ A.J) :
    (Algebra.TensorProduct.map (AlgHom.id K A.CoordRing) P.counit).comp A.coact
      = ((Algebra.TensorProduct.rid K K A.CoordRing).symm :
          A.CoordRing →ₐ[K] A.CoordRing ⊗[K] K) := by
  refine quotAlgHom_ext (B := A.CoordRing ⊗[K] K) fun i => ?_
  have hΦ : (Algebra.TensorProduct.map (AlgHom.id K A.CoordRing) P.counit).comp A.coordAct
      = (((Algebra.TensorProduct.rid K K A.CoordRing).symm :
            A.CoordRing →ₐ[K] A.CoordRing ⊗[K] K).comp (Ideal.Quotient.mkₐ K A.J)).comp
        (aeval (Sum.elim (fun j => C (P.one j)) X)) := by
    refine MvPolynomial.algHom_ext fun c => ?_
    cases c with
    | inl j =>
        simp only [AlgHom.comp_apply, coordAct_X_inl, Algebra.TensorProduct.map_tmul,
          GroupData.counit_mk_X, map_one, aeval_X, Sum.elim_inl, Ideal.Quotient.mkₐ_eq_mk,
          AlgEquiv.coe_toAlgHom, Algebra.TensorProduct.rid_symm_apply, A.mkJ_C]
        rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, smul_eq_mul, mul_one]
    | inr i => simp
  simpa using A.act_law_of_comp (B := A.CoordRing ⊗[K] K) (J' := A.J) _ _ _ hΦ
    (fun _ hg => by simp [A.mkJ_eq_zero hg]) i (h i)

theorem assoc_includeLeft_coordAct :
    ((Algebra.TensorProduct.assoc K K K A.CoordRing P.CoordRing P.CoordRing).toAlgHom.comp
        (Algebra.TensorProduct.includeLeft :
          (A.CoordRing ⊗[K] P.CoordRing) →ₐ[K]
            (A.CoordRing ⊗[K] P.CoordRing) ⊗[K] P.CoordRing)).comp A.coordAct
      = A.coordActPair.comp
        (aeval (Sum.elim (fun j => X (Sum.inl j)) fun i => X (Sum.inr (Sum.inr i)))) := by
  refine MvPolynomial.algHom_ext fun c => ?_
  cases c with
  | inl j => simp [coordActPair, Algebra.TensorProduct.one_def]
  | inr i => simp [coordActPair, Algebra.TensorProduct.one_def]

theorem includeRight_comm_coordPair :
    ((Algebra.TensorProduct.includeRight :
        (P.CoordRing ⊗[K] P.CoordRing) →ₐ[K]
          A.CoordRing ⊗[K] (P.CoordRing ⊗[K] P.CoordRing)).comp
      ((Algebra.TensorProduct.comm K P.CoordRing P.CoordRing).toAlgHom.comp
        P.coordPair))
      = A.coordActPair.comp
        (aeval (Sum.elim (fun k => X (Sum.inr (Sum.inl k))) fun k => X (Sum.inl k))) := by
  refine MvPolynomial.algHom_ext fun c => ?_
  cases c with
  | inl k => simp [coordActPair]
  | inr k => simp [coordActPair]

theorem coassoc_coact_of (h : ∀ i, A.actAct i - A.mulAct i ∈ A.actTripleIdeal) :
    (Algebra.TensorProduct.assoc K K K A.CoordRing P.CoordRing P.CoordRing).toAlgHom.comp
        ((Algebra.TensorProduct.map A.coact (AlgHom.id K P.CoordRing)).comp A.coact)
      = (Algebra.TensorProduct.map (AlgHom.id K A.CoordRing)
          ((Algebra.TensorProduct.comm K P.CoordRing P.CoordRing).toAlgHom.comp P.comul)).comp
        A.coact := by
  refine quotAlgHom_ext (B := A.CoordRing ⊗[K] (P.CoordRing ⊗[K] P.CoordRing)) fun i => ?_
  have hL : ((Algebra.TensorProduct.assoc K K K A.CoordRing P.CoordRing P.CoordRing).toAlgHom.comp
        (Algebra.TensorProduct.map A.coact (AlgHom.id K P.CoordRing))).comp A.coordAct
      = A.coordActPair.comp
        (aeval (Sum.elim (fun j => X (Sum.inr (Sum.inl j))) A.act1)) := by
    refine MvPolynomial.algHom_ext fun c => ?_
    cases c with
    | inl j => simp [coordActPair, Algebra.TensorProduct.one_def]
    | inr i =>
        have hi := AlgHom.congr_fun A.assoc_includeLeft_coordAct (A.act i)
        simp only [AlgHom.comp_apply, Algebra.TensorProduct.includeLeft_apply] at hi
        simpa [A.coact_mk_X, act1] using hi
  have hR : (Algebra.TensorProduct.map (AlgHom.id K A.CoordRing)
        ((Algebra.TensorProduct.comm K P.CoordRing P.CoordRing).toAlgHom.comp P.comul)).comp
        A.coordAct
      = A.coordActPair.comp
        (aeval (Sum.elim (P.mulFlip ι) fun k => X (Sum.inr (Sum.inr k)))) := by
    refine MvPolynomial.algHom_ext fun c => ?_
    cases c with
    | inl j =>
        have hj := AlgHom.congr_fun A.includeRight_comm_coordPair (P.mul j)
        simp only [AlgHom.comp_apply, Algebra.TensorProduct.includeRight_apply] at hj
        simpa [P.comul_mk_X, GroupData.mulFlip] using hj
    | inr i => simp [coordActPair, Algebra.TensorProduct.one_def]
  have hRlaw : aeval (Sum.elim (P.mulFlip ι) fun k => X (Sum.inr (Sum.inr k))) (A.act i)
      - A.mulAct i ∈ A.actTripleIdeal := by
    rw [show aeval (Sum.elim (P.mulFlip ι) fun k => X (Sum.inr (Sum.inr k))) (A.act i)
      = A.mulAct i from rfl, sub_self]
    exact Ideal.zero_mem _
  have e1 := A.act_law_of_comp (B := A.CoordRing ⊗[K] (P.CoordRing ⊗[K] P.CoordRing))
    (J' := A.actTripleIdeal) _ _ _ hL (fun _ hg => A.coordActPair_eq_zero hg) i (h i)
  have e2 := A.act_law_of_comp (B := A.CoordRing ⊗[K] (P.CoordRing ⊗[K] P.CoordRing))
    (J' := A.actTripleIdeal) _ _ _ hR (fun _ hg => A.coordActPair_eq_zero hg) i hRlaw
  simpa using e1.trans e2.symm

/-! #### Products of spaces

Two actions on `ι ⊕ κ`: `prodLeft`, where `P` acts through `A` on the first block and leaves
the second alone, and `prod`, where `P × Q` acts through `A` on the first block and through
`B` on the second.  Both ideals are two-block ideals (`sumIdeal`), and both coactions are
the factors' coactions carried by `sumMkL`, `sumMkR`. -/

section Prod

variable {δ κ : Type u} {Q : GroupData K δ}

/-- **The trivial action of a group on affine `κ`-space.** -/
noncomputable def trivialActionData (P : GroupData K γ) (κ : Type u) : ActionData P κ where
  J := ⊥
  act := fun k => X (Sum.inr k)
  act_mem := by
    intro f hf
    rw [Ideal.mem_bot] at hf
    subst hf
    simp

@[simp] theorem trivialActionData_J (P : GroupData K γ) (κ : Type u) :
    (trivialActionData P κ).J = ⊥ := rfl

@[simp] theorem trivialActionData_act (P : GroupData K γ) (κ : Type u) :
    (trivialActionData P κ).act = fun k => (X (Sum.inr k) : MvPolynomial (γ ⊕ κ) K) := rfl

/-- The coordinates of `A`'s action, extended by `κ` coordinates the group does not move. -/
noncomputable def prodLeftAct (A : ActionData P ι) (κ : Type u) :
    ι ⊕ κ → MvPolynomial (γ ⊕ (ι ⊕ κ)) K :=
  Sum.elim (fun i => rename (Sum.map id Sum.inl) (A.act i))
    (fun k => X (Sum.inr (Sum.inr k)))

private theorem prodLeft_tensorOfSum'_comp (A : ActionData P ι) (κ : Type u) :
    (Algebra.TensorProduct.map
        (Ideal.Quotient.mkₐ K (sumIdeal A.J (⊥ : Ideal (MvPolynomial κ K))))
        (Ideal.Quotient.mkₐ K P.I)).comp
      ((tensorOfSum' K γ (ι ⊕ κ)).comp (rename (Sum.map id Sum.inl)))
      = ((Algebra.TensorProduct.map (sumMkL A.J (⊥ : Ideal (MvPolynomial κ K)))
          (AlgHom.id K P.CoordRing)).comp
        (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K A.J) (Ideal.Quotient.mkₐ K P.I))).comp
        (tensorOfSum' K γ ι) := by
  refine MvPolynomial.algHom_ext fun m => ?_
  cases m with
  | inl a => simp [tensorOfSum']
  | inr i => simp [tensorOfSum']

/-- The coaction of `prodLeft`, read on the first block of coordinates. -/
theorem prodLeft_coactHom_renameL (A : ActionData P ι) (κ : Type u) (g : MvPolynomial ι K) :
    Algebra.TensorProduct.map
        (Ideal.Quotient.mkₐ K (sumIdeal A.J (⊥ : Ideal (MvPolynomial κ K))))
        (Ideal.Quotient.mkₐ K P.I)
        (tensorOfSum' K γ (ι ⊕ κ) (aeval (A.prodLeftAct κ) (rename Sum.inl g)))
      = Algebra.TensorProduct.map (sumMkL A.J (⊥ : Ideal (MvPolynomial κ K)))
          (AlgHom.id K P.CoordRing)
        (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K A.J) (Ideal.Quotient.mkₐ K P.I)
          (tensorOfSum' K γ ι (aeval A.act g))) := by
  rw [aeval_rename]
  have hcomp : A.prodLeftAct κ ∘ Sum.inl
      = fun i => rename (Sum.map id Sum.inl) (A.act i) := rfl
  rw [hcomp, ← MvPolynomial.comp_aeval_apply]
  exact AlgHom.congr_fun (A.prodLeft_tensorOfSum'_comp κ) (aeval A.act g)

/-- **`A` acting on the first of two blocks of coordinates**, trivially on the second. -/
noncomputable def prodLeft (A : ActionData P ι) (κ : Type u) : ActionData P (ι ⊕ κ) where
  J := sumIdeal A.J (⊥ : Ideal (MvPolynomial κ K))
  act := A.prodLeftAct κ
  act_mem := by
    intro f hf
    refine sumIdeal_apply_eq_zero A.J (⊥ : Ideal (MvPolynomial κ K))
      ((Algebra.TensorProduct.map
          (Ideal.Quotient.mkₐ K (sumIdeal A.J (⊥ : Ideal (MvPolynomial κ K))))
          (Ideal.Quotient.mkₐ K P.I)).comp
        ((tensorOfSum' K γ (ι ⊕ κ)).comp (aeval (A.prodLeftAct κ)))) ?_ ?_ hf
    · intro g hg
      simp only [AlgHom.comp_apply]
      rw [A.prodLeft_coactHom_renameL κ, A.act_mem g hg, map_zero]
    · intro g hg
      rw [Ideal.mem_bot] at hg
      subst hg
      simp

@[simp] theorem prodLeft_J (A : ActionData P ι) (κ : Type u) :
    (A.prodLeft κ).J = sumIdeal A.J (⊥ : Ideal (MvPolynomial κ K)) := rfl

@[simp] theorem prodLeft_act (A : ActionData P ι) (κ : Type u) :
    (A.prodLeft κ).act = A.prodLeftAct κ := rfl

theorem prodLeft_J_eq_bot (A : ActionData P ι) (κ : Type u) (hJ : A.J = ⊥) :
    (A.prodLeft κ).J = ⊥ := by
  rw [prodLeft_J, hJ, sumIdeal_bot_bot]

theorem prodLeft_actPt (A : ActionData P ι) (κ : Type u) (a : γ → K) (z : ι ⊕ κ → K) :
    (A.prodLeft κ).actPt a z = Sum.elim (A.actPt a (z ∘ Sum.inl)) (z ∘ Sum.inr) := by
  have hL : Sum.elim a z ∘ Sum.map id Sum.inl = Sum.elim a (z ∘ Sum.inl) := by
    funext m; cases m <;> rfl
  funext m
  cases m with
  | inl i =>
      show aeval (Sum.elim a z) (rename (Sum.map id Sum.inl) (A.act i)) = _
      rw [aeval_rename, hL]
      rfl
  | inr k =>
      show aeval (Sum.elim a z) (X (Sum.inr (Sum.inr k))) = _
      rw [aeval_X]
      rfl

/-- The coordinates of the action of `P × Q` on `ι ⊕ κ`, blockwise. -/
noncomputable def prodAct (A : ActionData P ι) (B : ActionData Q κ) :
    ι ⊕ κ → MvPolynomial ((γ ⊕ δ) ⊕ (ι ⊕ κ)) K :=
  Sum.elim (fun i => rename (Sum.map Sum.inl Sum.inl) (A.act i))
    (fun k => rename (Sum.map Sum.inr Sum.inr) (B.act k))

private theorem prod_tensorOfSum'_renameL_comp (A : ActionData P ι) (B : ActionData Q κ) :
    (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K (sumIdeal A.J B.J))
        (Ideal.Quotient.mkₐ K (sumIdeal P.I Q.I))).comp
      ((tensorOfSum' K (γ ⊕ δ) (ι ⊕ κ)).comp (rename (Sum.map Sum.inl Sum.inl)))
      = ((Algebra.TensorProduct.map (sumMkL A.J B.J) (sumMkL P.I Q.I)).comp
        (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K A.J)
          (Ideal.Quotient.mkₐ K P.I))).comp (tensorOfSum' K γ ι) := by
  refine MvPolynomial.algHom_ext fun m => ?_
  cases m with
  | inl a => simp [tensorOfSum']
  | inr i => simp [tensorOfSum']

private theorem prod_tensorOfSum'_renameR_comp (A : ActionData P ι) (B : ActionData Q κ) :
    (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K (sumIdeal A.J B.J))
        (Ideal.Quotient.mkₐ K (sumIdeal P.I Q.I))).comp
      ((tensorOfSum' K (γ ⊕ δ) (ι ⊕ κ)).comp (rename (Sum.map Sum.inr Sum.inr)))
      = ((Algebra.TensorProduct.map (sumMkR A.J B.J) (sumMkR P.I Q.I)).comp
        (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K B.J)
          (Ideal.Quotient.mkₐ K Q.I))).comp (tensorOfSum' K δ κ) := by
  refine MvPolynomial.algHom_ext fun m => ?_
  cases m with
  | inl b => simp [tensorOfSum']
  | inr k => simp [tensorOfSum']

/-- The coaction of a product of actions, on the first block. -/
theorem prod_coactHom_renameL (A : ActionData P ι) (B : ActionData Q κ)
    (g : MvPolynomial ι K) :
    Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K (sumIdeal A.J B.J))
        (Ideal.Quotient.mkₐ K (sumIdeal P.I Q.I))
        (tensorOfSum' K (γ ⊕ δ) (ι ⊕ κ) (aeval (A.prodAct B) (rename Sum.inl g)))
      = Algebra.TensorProduct.map (sumMkL A.J B.J) (sumMkL P.I Q.I)
        (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K A.J) (Ideal.Quotient.mkₐ K P.I)
          (tensorOfSum' K γ ι (aeval A.act g))) := by
  rw [aeval_rename]
  have hcomp : A.prodAct B ∘ Sum.inl
      = fun i => rename (Sum.map Sum.inl Sum.inl) (A.act i) := rfl
  rw [hcomp, ← MvPolynomial.comp_aeval_apply]
  exact AlgHom.congr_fun (A.prod_tensorOfSum'_renameL_comp B) (aeval A.act g)

/-- The coaction of a product of actions, on the second block. -/
theorem prod_coactHom_renameR (A : ActionData P ι) (B : ActionData Q κ)
    (g : MvPolynomial κ K) :
    Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K (sumIdeal A.J B.J))
        (Ideal.Quotient.mkₐ K (sumIdeal P.I Q.I))
        (tensorOfSum' K (γ ⊕ δ) (ι ⊕ κ) (aeval (A.prodAct B) (rename Sum.inr g)))
      = Algebra.TensorProduct.map (sumMkR A.J B.J) (sumMkR P.I Q.I)
        (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K B.J) (Ideal.Quotient.mkₐ K Q.I)
          (tensorOfSum' K δ κ (aeval B.act g))) := by
  rw [aeval_rename]
  have hcomp : A.prodAct B ∘ Sum.inr
      = fun k => rename (Sum.map Sum.inr Sum.inr) (B.act k) := rfl
  rw [hcomp, ← MvPolynomial.comp_aeval_apply]
  exact AlgHom.congr_fun (A.prod_tensorOfSum'_renameR_comp B) (aeval B.act g)

/-- **The product of two actions**, of `P × Q` on `ι ⊕ κ`. -/
noncomputable def prod (A : ActionData P ι) (B : ActionData Q κ) :
    ActionData (P.prod Q) (ι ⊕ κ) where
  J := sumIdeal A.J B.J
  act := A.prodAct B
  act_mem := by
    intro f hf
    refine sumIdeal_apply_eq_zero A.J B.J
      ((Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K (sumIdeal A.J B.J))
          (Ideal.Quotient.mkₐ K (sumIdeal P.I Q.I))).comp
        ((tensorOfSum' K (γ ⊕ δ) (ι ⊕ κ)).comp (aeval (A.prodAct B)))) ?_ ?_ hf
    · intro g hg
      simp only [AlgHom.comp_apply]
      rw [A.prod_coactHom_renameL B, A.act_mem g hg, map_zero]
    · intro g hg
      simp only [AlgHom.comp_apply]
      rw [A.prod_coactHom_renameR B, B.act_mem g hg, map_zero]

@[simp] theorem prod_J (A : ActionData P ι) (B : ActionData Q κ) :
    (A.prod B).J = sumIdeal A.J B.J := rfl

@[simp] theorem prod_act (A : ActionData P ι) (B : ActionData Q κ) :
    (A.prod B).act = A.prodAct B := rfl

theorem prod_J_eq_bot (A : ActionData P ι) (B : ActionData Q κ) (hA : A.J = ⊥)
    (hB : B.J = ⊥) : (A.prod B).J = ⊥ := by
  rw [prod_J, hA, hB, sumIdeal_bot_bot]

theorem prod_actPt (A : ActionData P ι) (B : ActionData Q κ) (c : γ ⊕ δ → K)
    (z : ι ⊕ κ → K) :
    (A.prod B).actPt c z
      = Sum.elim (A.actPt (c ∘ Sum.inl) (z ∘ Sum.inl))
        (B.actPt (c ∘ Sum.inr) (z ∘ Sum.inr)) := by
  have hL : Sum.elim c z ∘ Sum.map Sum.inl Sum.inl
      = Sum.elim (c ∘ Sum.inl) (z ∘ Sum.inl) := by
    funext m; cases m <;> rfl
  have hR : Sum.elim c z ∘ Sum.map Sum.inr Sum.inr
      = Sum.elim (c ∘ Sum.inr) (z ∘ Sum.inr) := by
    funext m; cases m <;> rfl
  funext m
  cases m with
  | inl i =>
      show aeval (Sum.elim c z) (rename (Sum.map Sum.inl Sum.inl) (A.act i)) = _
      rw [aeval_rename, hL]
      rfl
  | inr k =>
      show aeval (Sum.elim c z) (rename (Sum.map Sum.inr Sum.inr) (B.act k)) = _
      rw [aeval_rename, hR]
      rfl

end Prod

end ActionData

/-- **An action presented by polynomials**: action data whose coaction satisfies the
comodule laws — counit and coassociativity — as identities of algebra maps.

**Convention (see the module docstring).**  `coassoc_coact` carries
`P.comul` composed with the flip `Algebra.TensorProduct.comm`, i.e. `coact` is a comodule
over the *co-opposite* bialgebra.  This is what makes `Spec` of `coact` a **left** action
`G × X ⟶ X` — mathlib's `ModObj` — and hence `actPt` a left action of `pts`:
`actPt (mulPt a b) x = actPt a (actPt b x)`.  Without the flip the field is the ordinary
right-comodule law, whose `Spec` is a right action, and no `ModObj` follows from it
without the antipode. -/
structure ActionPresentation (P : GroupPresentation K γ) (ι : Type u)
    extends ActionData P.toGroupData ι where
  counit_coact : (Algebra.TensorProduct.map (.id K _) P.counit).comp toActionData.coact
    = (Algebra.TensorProduct.rid K K toActionData.CoordRing).symm
  coassoc_coact : (Algebra.TensorProduct.assoc K K K toActionData.CoordRing P.CoordRing
      P.CoordRing).toAlgHom.comp
      ((Algebra.TensorProduct.map toActionData.coact (.id K _)).comp toActionData.coact)
    = (Algebra.TensorProduct.map (.id K _)
        ((Algebra.TensorProduct.comm K P.CoordRing P.CoordRing).toAlgHom.comp P.comul)).comp
      toActionData.coact

namespace ActionPresentation

variable {P : GroupPresentation K γ} (A : ActionPresentation P ι)

/-- **A presented action from the action laws as polynomial identities.**  The two comodule
axioms of an `ActionData` are exactly the unit law `1 · x = x` modulo `J` and the
associativity law `b · (a · x) = (b a) · x` modulo the ideal of a pair of group elements and
a point; each is checked on the generators `X i` (`ActionData.act_law_of_comp`). -/
noncomputable def ofLaws {P : GroupPresentation K γ} (A : ActionData P.toGroupData ι)
    (hone : ∀ i, A.oneAct i - X i ∈ A.J)
    (hmul : ∀ i, A.actAct i - A.mulAct i ∈ A.actTripleIdeal) :
    ActionPresentation P ι where
  toActionData := A
  counit_coact := A.counit_coact_of hone
  coassoc_coact := A.coassoc_coact_of hmul

@[simp] theorem ofLaws_toActionData {P : GroupPresentation K γ} (A : ActionData P.toGroupData ι)
    (hone : ∀ i, A.oneAct i - X i ∈ A.J)
    (hmul : ∀ i, A.actAct i - A.mulAct i ∈ A.actTripleIdeal) :
    (ofLaws A hone hmul).toActionData = A := rfl

/-! #### Restriction to a closed subgroup

An action of `P` is an action of every closed subgroup `P.restrict …` with the *same*
coaction — the coaction of the subgroup is the coaction of `P` followed by
`K[γ] ⧸ I → K[γ] ⧸ J` in the group factor (`restrictGroupData_coact`), and the two comodule
laws are `A`'s pushed forward along that surjection. -/

section RestrictGroup

variable {J : Ideal (MvPolynomial γ K)} (hIJ : P.I ≤ J)
  (hmul : ∀ f ∈ J, Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K J)
    (Ideal.Quotient.mkₐ K J) (tensorOfSum K γ (aeval P.mul f)) = 0)
  (hinv : ∀ f ∈ J, Ideal.Quotient.mk J (aeval P.inv f) = 0)
  (hone : ∀ f ∈ J, aeval P.one f = 0)

private theorem map_id_factorₐ_comp :
    (Algebra.TensorProduct.map (AlgHom.id K A.CoordRing)
        (Ideal.Quotient.factorₐ K hIJ)).comp
      (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K A.J) (Ideal.Quotient.mkₐ K P.I))
      = Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K A.J) (Ideal.Quotient.mkₐ K J) := by
  rw [← Algebra.TensorProduct.map_comp]
  rfl

/-- The action data of `A`, read as action data of a closed subgroup: the same space and the
same polynomials, the coaction composed with `K[γ] ⧸ I → K[γ] ⧸ J`. -/
def restrictGroupData : ActionData (P.toGroupData.restrict J hmul hinv hone) ι where
  J := A.J
  act := A.act
  act_mem := fun f hf => by
    have h0 := congrArg (Algebra.TensorProduct.map (AlgHom.id K A.CoordRing)
      (Ideal.Quotient.factorₐ K hIJ)) (A.act_mem f hf)
    rw [map_zero] at h0
    exact (AlgHom.congr_fun (A.map_id_factorₐ_comp hIJ)
      (tensorOfSum' K γ ι (aeval A.act f))).symm.trans h0

@[simp] theorem restrictGroupData_J :
    (A.restrictGroupData hIJ hmul hinv hone).J = A.J := rfl

@[simp] theorem restrictGroupData_act :
    (A.restrictGroupData hIJ hmul hinv hone).act = A.act := rfl

@[simp] theorem restrictGroupData_actPt (a : γ → K) (x : ι → K) :
    (A.restrictGroupData hIJ hmul hinv hone).actPt a x = A.actPt a x := rfl

theorem restrictGroupData_coact :
    (A.restrictGroupData hIJ hmul hinv hone).coact
      = (Algebra.TensorProduct.map (AlgHom.id K A.CoordRing)
          (Ideal.Quotient.factorₐ K hIJ)).comp A.coact :=
  quotAlgHom_ext fun i =>
    (AlgHom.congr_fun (A.map_id_factorₐ_comp hIJ)
      (tensorOfSum' K γ ι (aeval A.act (X i)))).symm

/-- **An action of a presented group is an action of every closed subgroup**, with the same
coaction.  The counit law is `A`'s after `GroupData.restrict_counit_comp`; the
coassociativity law is `A`'s carried along `K[γ] ⧸ I → K[γ] ⧸ J` by the naturality of the
associator and of the braiding, using `GroupData.restrict_comul_comp`. -/
def restrictGroup : ActionPresentation (P.restrict hIJ hmul hinv hone) ι where
  toActionData := A.restrictGroupData hIJ hmul hinv hone
  counit_coact := by
    have hρ : ∀ b : A.CoordRing, (A.restrictGroupData hIJ hmul hinv hone).coact b
        = Algebra.TensorProduct.map (AlgHom.id K A.CoordRing) (Ideal.Quotient.factorₐ K hIJ)
          (A.coact b) :=
      fun b => AlgHom.congr_fun (A.restrictGroupData_coact hIJ hmul hinv hone) b
    have e2 : (Algebra.TensorProduct.map (AlgHom.id K A.CoordRing)
          (P.toGroupData.restrict J hmul hinv hone).counit).comp
        (Algebra.TensorProduct.map (AlgHom.id K A.CoordRing) (Ideal.Quotient.factorₐ K hIJ))
        = Algebra.TensorProduct.map (AlgHom.id K A.CoordRing) P.counit := by
      rw [← Algebra.TensorProduct.map_comp,
        P.toGroupData.restrict_counit_comp hmul hinv hone hIJ]
      rfl
    refine AlgHom.ext fun b => Eq.trans ?_ (AlgHom.congr_fun A.counit_coact b)
    show Algebra.TensorProduct.map (AlgHom.id K A.CoordRing)
        (P.toGroupData.restrict J hmul hinv hone).counit
        ((A.restrictGroupData hIJ hmul hinv hone).coact b)
      = Algebra.TensorProduct.map (AlgHom.id K A.CoordRing) P.counit (A.coact b)
    rw [hρ b]
    exact AlgHom.congr_fun e2 (A.coact b)
  coassoc_coact := by
    have hρ : ∀ b : A.CoordRing, (A.restrictGroupData hIJ hmul hinv hone).coact b
        = Algebra.TensorProduct.map (AlgHom.id K A.CoordRing) (Ideal.Quotient.factorₐ K hIJ)
          (A.coact b) :=
      fun b => AlgHom.congr_fun (A.restrictGroupData_coact hIJ hmul hinv hone) b
    have hk : ∀ t : A.CoordRing ⊗[K] P.CoordRing,
        Algebra.TensorProduct.map (A.restrictGroupData hIJ hmul hinv hone).coact
            (AlgHom.id K (P.toGroupData.restrict J hmul hinv hone).CoordRing)
            (Algebra.TensorProduct.map (AlgHom.id K A.CoordRing)
              (Ideal.Quotient.factorₐ K hIJ) t)
          = Algebra.TensorProduct.map (Algebra.TensorProduct.map (AlgHom.id K A.CoordRing)
              (Ideal.Quotient.factorₐ K hIJ)) (Ideal.Quotient.factorₐ K hIJ)
            (Algebra.TensorProduct.map A.coact (AlgHom.id K P.CoordRing) t) := by
      have e : (Algebra.TensorProduct.map (A.restrictGroupData hIJ hmul hinv hone).coact
            (AlgHom.id K (P.toGroupData.restrict J hmul hinv hone).CoordRing)).comp
          (Algebra.TensorProduct.map (AlgHom.id K A.CoordRing)
            (Ideal.Quotient.factorₐ K hIJ))
          = (Algebra.TensorProduct.map (Algebra.TensorProduct.map (AlgHom.id K A.CoordRing)
              (Ideal.Quotient.factorₐ K hIJ)) (Ideal.Quotient.factorₐ K hIJ)).comp
            (Algebra.TensorProduct.map A.coact (AlgHom.id K P.CoordRing)) :=
        Algebra.TensorProduct.ext' fun b u =>
          congrArg (fun w => w ⊗ₜ[K] Ideal.Quotient.factorₐ K hIJ u) (hρ b)
      exact fun t => AlgHom.congr_fun e t
    have hasn : ∀ s : (A.CoordRing ⊗[K] P.CoordRing) ⊗[K] P.CoordRing,
        (Algebra.TensorProduct.assoc K K K A.CoordRing
            (P.toGroupData.restrict J hmul hinv hone).CoordRing
            (P.toGroupData.restrict J hmul hinv hone).CoordRing).toAlgHom
          (Algebra.TensorProduct.map (Algebra.TensorProduct.map (AlgHom.id K A.CoordRing)
            (Ideal.Quotient.factorₐ K hIJ)) (Ideal.Quotient.factorₐ K hIJ) s)
        = Algebra.TensorProduct.map (AlgHom.id K A.CoordRing)
            (Algebra.TensorProduct.map (Ideal.Quotient.factorₐ K hIJ)
              (Ideal.Quotient.factorₐ K hIJ))
            ((Algebra.TensorProduct.assoc K K K A.CoordRing P.CoordRing P.CoordRing).toAlgHom s) :=
      fun s => AlgHom.congr_fun (assoc_naturality (AlgHom.id K A.CoordRing)
        (Ideal.Quotient.factorₐ K hIJ) (Ideal.Quotient.factorₐ K hIJ)) s
    have hcoa : ∀ b : A.CoordRing,
        (Algebra.TensorProduct.assoc K K K A.CoordRing P.CoordRing P.CoordRing).toAlgHom
          (Algebra.TensorProduct.map A.coact (AlgHom.id K P.CoordRing) (A.coact b))
        = Algebra.TensorProduct.map (AlgHom.id K A.CoordRing)
            ((Algebra.TensorProduct.comm K P.CoordRing P.CoordRing).toAlgHom.comp P.comul)
            (A.coact b) :=
      fun b => AlgHom.congr_fun A.coassoc_coact b
    have hcm : ∀ v : P.CoordRing,
        Algebra.TensorProduct.map (Ideal.Quotient.factorₐ K hIJ) (Ideal.Quotient.factorₐ K hIJ)
            ((Algebra.TensorProduct.comm K P.CoordRing P.CoordRing).toAlgHom (P.comul v))
          = (Algebra.TensorProduct.comm K (P.toGroupData.restrict J hmul hinv hone).CoordRing
              (P.toGroupData.restrict J hmul hinv hone).CoordRing).toAlgHom
            ((P.toGroupData.restrict J hmul hinv hone).comul
              (Ideal.Quotient.factorₐ K hIJ v)) := by
      intro v
      have h1 : (P.toGroupData.restrict J hmul hinv hone).comul
            (Ideal.Quotient.factorₐ K hIJ v)
          = Algebra.TensorProduct.map (Ideal.Quotient.factorₐ K hIJ)
            (Ideal.Quotient.factorₐ K hIJ) (P.comul v) :=
        AlgHom.congr_fun (P.toGroupData.restrict_comul_comp hmul hinv hone hIJ) v
      rw [h1]
      exact (AlgHom.congr_fun (comm_naturality (Ideal.Quotient.factorₐ K hIJ)
        (Ideal.Quotient.factorₐ K hIJ)) (P.comul v)).symm
    have hlast : ∀ t : A.CoordRing ⊗[K] P.CoordRing,
        Algebra.TensorProduct.map (AlgHom.id K A.CoordRing)
            (Algebra.TensorProduct.map (Ideal.Quotient.factorₐ K hIJ)
              (Ideal.Quotient.factorₐ K hIJ))
            (Algebra.TensorProduct.map (AlgHom.id K A.CoordRing)
              ((Algebra.TensorProduct.comm K P.CoordRing P.CoordRing).toAlgHom.comp P.comul) t)
          = Algebra.TensorProduct.map (AlgHom.id K A.CoordRing)
              ((Algebra.TensorProduct.comm K (P.toGroupData.restrict J hmul hinv hone).CoordRing
                (P.toGroupData.restrict J hmul hinv hone).CoordRing).toAlgHom.comp
                (P.toGroupData.restrict J hmul hinv hone).comul)
              (Algebra.TensorProduct.map (AlgHom.id K A.CoordRing)
                (Ideal.Quotient.factorₐ K hIJ) t) := by
      have e : (Algebra.TensorProduct.map (AlgHom.id K A.CoordRing)
            (Algebra.TensorProduct.map (Ideal.Quotient.factorₐ K hIJ)
              (Ideal.Quotient.factorₐ K hIJ))).comp
          (Algebra.TensorProduct.map (AlgHom.id K A.CoordRing)
            ((Algebra.TensorProduct.comm K P.CoordRing P.CoordRing).toAlgHom.comp P.comul))
          = (Algebra.TensorProduct.map (AlgHom.id K A.CoordRing)
              ((Algebra.TensorProduct.comm K
                (P.toGroupData.restrict J hmul hinv hone).CoordRing
                (P.toGroupData.restrict J hmul hinv hone).CoordRing).toAlgHom.comp
              (P.toGroupData.restrict J hmul hinv hone).comul)).comp
            (Algebra.TensorProduct.map (AlgHom.id K A.CoordRing)
              (Ideal.Quotient.factorₐ K hIJ)) :=
        Algebra.TensorProduct.ext' fun b u => congrArg (fun w => b ⊗ₜ[K] w) (hcm u)
      exact fun t => AlgHom.congr_fun e t
    refine AlgHom.ext fun b => ?_
    show (Algebra.TensorProduct.assoc K K K A.CoordRing
        (P.toGroupData.restrict J hmul hinv hone).CoordRing
        (P.toGroupData.restrict J hmul hinv hone).CoordRing).toAlgHom
        (Algebra.TensorProduct.map (A.restrictGroupData hIJ hmul hinv hone).coact
          (AlgHom.id K (P.toGroupData.restrict J hmul hinv hone).CoordRing)
          ((A.restrictGroupData hIJ hmul hinv hone).coact b))
      = Algebra.TensorProduct.map (AlgHom.id K A.CoordRing)
          ((Algebra.TensorProduct.comm K (P.toGroupData.restrict J hmul hinv hone).CoordRing
            (P.toGroupData.restrict J hmul hinv hone).CoordRing).toAlgHom.comp
            (P.toGroupData.restrict J hmul hinv hone).comul)
          ((A.restrictGroupData hIJ hmul hinv hone).coact b)
    rw [hρ b, hk (A.coact b), hasn _, hcoa b]
    exact hlast (A.coact b)

@[simp] theorem restrictGroup_toActionData :
    (A.restrictGroup hIJ hmul hinv hone).toActionData
      = A.restrictGroupData hIJ hmul hinv hone := rfl

end RestrictGroup

/-- The **left** coaction `B →ₐ A ⊗ B` of the action: `coact` followed by the flip.  Its
`Spec` is the action morphism `G × X ⟶ X`, so this is the algebra map behind `modObj`. -/
noncomputable def leftCoact : A.CoordRing →ₐ[K] P.CoordRing ⊗[K] A.CoordRing :=
  (Algebra.TensorProduct.comm K A.CoordRing P.CoordRing).toAlgHom.comp A.coact

/-- The counit law for the left coaction; `Spec` of it is `ModObj.one_smul`. -/
theorem map_counit_comp_leftCoact :
    (Algebra.TensorProduct.map P.counit (AlgHom.id K A.CoordRing)).comp A.leftCoact
      = (Algebra.TensorProduct.lid K A.CoordRing).symm := by
  have hcomm : (Algebra.TensorProduct.map P.counit (AlgHom.id K A.CoordRing)).comp
      (Algebra.TensorProduct.comm K A.CoordRing P.CoordRing).toAlgHom
      = (Algebra.TensorProduct.comm K A.CoordRing K).toAlgHom.comp
        (Algebra.TensorProduct.map (AlgHom.id K A.CoordRing) P.counit) :=
    Algebra.TensorProduct.ext' fun b a => rfl
  rw [leftCoact, ← AlgHom.comp_assoc, hcomm, AlgHom.comp_assoc, A.counit_coact]
  exact AlgHom.ext fun b => rfl

/-- The flip `b ⊗ (u ⊗ v) ↦ (v ⊗ u) ⊗ b` that turns the coassociativity of `coact` into that
of `leftCoact`. -/
private noncomputable def flipTriple :
    A.CoordRing ⊗[K] (P.CoordRing ⊗[K] P.CoordRing) →ₐ[K]
      (P.CoordRing ⊗[K] P.CoordRing) ⊗[K] A.CoordRing :=
  (Algebra.TensorProduct.map (Algebra.TensorProduct.comm K P.CoordRing P.CoordRing).toAlgHom
      (AlgHom.id K A.CoordRing)).comp
    (Algebra.TensorProduct.comm K A.CoordRing (P.CoordRing ⊗[K] P.CoordRing)).toAlgHom

/-- The coassociativity law for the left coaction; `Spec` of it is `ModObj.mul_smul`.  Both
sides are `_ ∘ coact`, and the two prefixes are matched by the flip `flipTriple` from
`coassoc_coact`. -/
theorem map_comul_comp_leftCoact :
    (Algebra.TensorProduct.map P.comul (AlgHom.id K A.CoordRing)).comp A.leftCoact
      = (Algebra.TensorProduct.assoc K K K P.CoordRing P.CoordRing
            A.CoordRing).symm.toAlgHom.comp
        ((Algebra.TensorProduct.map (AlgHom.id K P.CoordRing) A.leftCoact).comp A.leftCoact) := by
  have hcc : ∀ x : P.CoordRing ⊗[K] P.CoordRing,
      Algebra.TensorProduct.comm K P.CoordRing P.CoordRing
        (Algebra.TensorProduct.comm K P.CoordRing P.CoordRing x) = x := fun x =>
    x.induction_on (by simp) (fun _ _ => rfl) (fun p q hp hq => by simp [hp, hq])
  -- the left-hand side, over `coact`
  have hL : (Algebra.TensorProduct.map P.comul (AlgHom.id K A.CoordRing)).comp A.leftCoact
      = A.flipTriple.comp ((Algebra.TensorProduct.map (AlgHom.id K A.CoordRing)
          ((Algebra.TensorProduct.comm K P.CoordRing P.CoordRing).toAlgHom.comp P.comul)).comp
            A.coact) := by
    rw [leftCoact, ← AlgHom.comp_assoc, ← AlgHom.comp_assoc]
    congr 1
    refine Algebra.TensorProduct.ext' fun b a => ?_
    show P.comul a ⊗ₜ b = Algebra.TensorProduct.comm K P.CoordRing P.CoordRing
      (Algebra.TensorProduct.comm K P.CoordRing P.CoordRing (P.comul a)) ⊗ₜ b
    rw [hcc]
  -- the coaction commutes past the flip
  have hpre : (Algebra.TensorProduct.map (AlgHom.id K P.CoordRing) A.leftCoact).comp
      (Algebra.TensorProduct.comm K A.CoordRing P.CoordRing).toAlgHom
      = ((Algebra.TensorProduct.map (AlgHom.id K P.CoordRing)
            (Algebra.TensorProduct.comm K A.CoordRing P.CoordRing).toAlgHom).comp
          (Algebra.TensorProduct.comm K (A.CoordRing ⊗[K] P.CoordRing)
            P.CoordRing).toAlgHom).comp
        (Algebra.TensorProduct.map A.coact (AlgHom.id K P.CoordRing)) :=
    Algebra.TensorProduct.ext' fun b a => rfl
  -- the right-hand side, over `coact`
  have hR : (Algebra.TensorProduct.map (AlgHom.id K P.CoordRing) A.leftCoact).comp A.leftCoact
      = (((Algebra.TensorProduct.map (AlgHom.id K P.CoordRing)
            (Algebra.TensorProduct.comm K A.CoordRing P.CoordRing).toAlgHom).comp
          (Algebra.TensorProduct.comm K (A.CoordRing ⊗[K] P.CoordRing)
            P.CoordRing).toAlgHom).comp
        (Algebra.TensorProduct.map A.coact (AlgHom.id K P.CoordRing))).comp A.coact := by
    rw [← hpre, AlgHom.comp_assoc]
    rfl
  -- the two flips agree
  have hflip : ((Algebra.TensorProduct.assoc K K K P.CoordRing P.CoordRing
        A.CoordRing).symm.toAlgHom.comp
        (Algebra.TensorProduct.map (AlgHom.id K P.CoordRing)
          (Algebra.TensorProduct.comm K A.CoordRing P.CoordRing).toAlgHom)).comp
        (Algebra.TensorProduct.comm K (A.CoordRing ⊗[K] P.CoordRing) P.CoordRing).toAlgHom
      = A.flipTriple.comp
        (Algebra.TensorProduct.assoc K K K A.CoordRing P.CoordRing P.CoordRing).toAlgHom := by
    refine Algebra.TensorProduct.ext' fun w a' => ?_
    induction w with
    | zero => simp
    | tmul b a => rfl
    | add p q hp hq => simp only [add_tmul, map_add, hp, hq]
  rw [hL, hR, ← A.coassoc_coact]
  simp only [← AlgHom.comp_assoc]
  rw [hflip]

open scoped MonObj in
set_option maxHeartbeats 1000000 in
/-- The coordinate ring of the space as a module object over the coordinate ring of the
group, in `(CommAlgCat K)ᵒᵖ`: the two laws are `map_counit_comp_leftCoact` and
`map_comul_comp_leftCoact`. -/
@[instance_reducible]
noncomputable def opModObj :
    letI := P.opMonObj
    ModObj (op (CommAlgCat.of K P.CoordRing)) (op (CommAlgCat.of K A.CoordRing)) :=
  letI := P.opMonObj
  { smul := (CommAlgCat.ofHom A.leftCoact).op
    one_smul := by
      refine Quiver.Hom.unop_inj (CommAlgCat.hom_ext ?_)
      simp only [unop_comp, Quiver.Hom.unop_op, CommAlgCat.hom_comp, CommAlgCat.hom_ofHom]
      exact A.map_counit_comp_leftCoact
    mul_smul := by
      refine Quiver.Hom.unop_inj (CommAlgCat.hom_ext ?_)
      simp only [unop_comp, Quiver.Hom.unop_op, CommAlgCat.hom_comp, CommAlgCat.hom_ofHom]
      exact A.map_comul_comp_leftCoact }

set_option maxHeartbeats 1000000 in
/-- **The module object of an action presented by polynomials.**  `Spec.lean` §4's group
actions are `GrpObj`/`ModObj` in `Over (Spec K)`; this is the `ModObj` an
`ActionPresentation` supplies, obtained from the comodule structure of the coordinate rings
(`opMonObj`, `opModObj`) by transport along the monoidal functor `algSpec`
(`modObjObj`), whose monoid object on the `Spec` side is mathlib's
`instMonObjSpecAsOverSpec` (`one_scheme`, `mul_scheme`). -/
@[instance_reducible]
noncomputable def modObj : ModObj P.scheme A.scheme :=
  letI := P.opMonObj
  letI := A.opModObj
  letI : MonObj ((algSpec (CommRingCat.of K)).obj (op (CommAlgCat.of K P.CoordRing))) :=
    inferInstanceAs (MonObj P.scheme)
  modObjObj (algSpec (CommRingCat.of K)) (M := op (CommAlgCat.of K P.CoordRing))
    (op (CommAlgCat.of K A.CoordRing)) P.one_scheme P.mul_scheme

set_option maxHeartbeats 1000000 in
/-- **The action on `K`-points is the action of `modObj` on sections**: `actPt` computes
`P.sec ha • A.sec hx`.  With `sec_mulPt` this is the `K`-point dictionary `Spec.lean` §4
consumes. -/
theorem sec_actPt {a : γ → K} (ha : a ∈ P.pts) {x : ι → K} (hx : x ∈ A.pts) :
    letI := A.modObj
    A.sec (A.actPt_mem ha hx) = P.sec ha • A.sec hx := by
  let _inst := A.modObj
  refine Over.OverMorphism.ext ?_
  have hsmul : (P.sec ha • A.sec hx).left =
      (CartesianMonoidalCategory.lift (secOfAlgHom (P.ptHom ha))
        (secOfAlgHom (A.ptHom hx))).left ≫
      ((pullbackSpecIso K P.CoordRing A.CoordRing).hom ≫
        Spec.map (CommRingCat.ofHom A.leftCoact.toRingHom)) := rfl
  rw [hsmul]
  refine Eq.trans ?_ (Category.assoc _ _ _)
  rw [lift_secOfAlgHom (P.ptHom ha) (A.ptHom hx)]
  refine Eq.trans ?_ (Spec.map_comp _ _)
  rw [← CommRingCat.ofHom_comp, ActionData.sec_left]
  congr 2
  have hcomm : (Algebra.TensorProduct.lift (P.ptHom ha) (A.ptHom hx)
        (fun _ _ => Commute.all _ _)).comp
      (Algebra.TensorProduct.comm K A.CoordRing P.CoordRing).toAlgHom
      = Algebra.TensorProduct.lift (A.ptHom hx) (P.ptHom ha) (fun _ _ => Commute.all _ _) :=
    Algebra.TensorProduct.ext' fun b a => by simp [mul_comm]
  have key : A.ptHom (A.actPt_mem ha hx)
      = (Algebra.TensorProduct.lift (P.ptHom ha) (A.ptHom hx)
          (fun _ _ => Commute.all _ _)).comp A.leftCoact := by
    rw [A.ptHom_actPt ha hx, leftCoact, ← AlgHom.comp_assoc, hcomm]
  exact congrArg AlgHom.toRingHom key

/-! #### The action laws on `K`-points, and the polynomial action

`pts` is a group acting on `A.pts` (`mulPt_assoc` and friends, `actPt_mulPt`), so it is a
`PolyAction` in the sense of `Dimension/Homogeneous.lean` — the input of every classical
fibration count.  The laws are read off the `ModObj` action on sections through the
dictionary `sec`/`ptOfSec`, so nothing is recomputed from the comodule axioms. -/

-- The group law on sections (`CategoryTheory.Hom.monoid`) is a scoped instance of `MonObj`,
-- whose `γ` notation for `ModObj.smul` would shadow the index type `γ`.
attribute [local instance] CategoryTheory.Hom.monoid

theorem one_actPt {x : ι → K} (hx : x ∈ A.pts) : A.actPt P.one x = x := by
  let _inst := A.modObj
  have h : A.sec (A.actPt_mem P.one_mem_pts hx) = A.sec hx := by
    rw [A.sec_actPt P.one_mem_pts hx, P.sec_one, one_smul]
  have hpt := congrArg A.ptOfSec h
  rwa [A.ptOfSec_sec, A.ptOfSec_sec] at hpt

/-- **`actPt` is a left action of `pts`.** -/
theorem actPt_mulPt {a b : γ → K} (ha : a ∈ P.pts) (hb : b ∈ P.pts) {x : ι → K}
    (hx : x ∈ A.pts) : A.actPt (P.mulPt a b) x = A.actPt a (A.actPt b x) := by
  let _inst := A.modObj
  have h : A.sec (A.actPt_mem (P.mulPt_mem ha hb) hx)
      = A.sec (A.actPt_mem ha (A.actPt_mem hb hx)) := by
    rw [A.sec_actPt (P.mulPt_mem ha hb) hx, P.sec_mulPt ha hb,
      A.sec_actPt ha (A.actPt_mem hb hx), A.sec_actPt hb hx]
    exact mul_smul (P.sec ha) (P.sec hb) (A.sec hx)
  have hpt := congrArg A.ptOfSec h
  rwa [A.ptOfSec_sec, A.ptOfSec_sec] at hpt

theorem invPt_actPt {a : γ → K} (ha : a ∈ P.pts) {x : ι → K} (hx : x ∈ A.pts) :
    A.actPt (P.invPt a) (A.actPt a x) = x := by
  rw [← A.actPt_mulPt (P.invPt_mem ha) ha hx, P.invPt_mulPt ha, A.one_actPt hx]

theorem actPt_invPt {a : γ → K} (ha : a ∈ P.pts) {x : ι → K} (hx : x ∈ A.pts) :
    A.actPt a (A.actPt (P.invPt a) x) = x := by
  rw [← A.actPt_mulPt ha (P.invPt_mem ha) hx, P.mulPt_invPt ha, A.one_actPt hx]

/-- **The polynomial action of a presented group on a presented space.**  This is the
`PolyAction` every classical fibration count of `Dimension/` takes as input. -/
noncomputable def toPolyAction [IsAlgClosed K] [Finite γ] (hP : (MvPolynomial.vanishingIdeal K P.pts).IsPrime) :
    PolyAction K γ ι where
  G := P.pts
  S := A.pts
  act := A.actPt
  act_poly := ⟨A.act, fun _ _ _ => rfl⟩
  irreducible := hP
  one := P.one
  one_mem := P.one_mem_pts
  act_mem := fun _ hg _ hy => A.actPt_mem hg hy
  act_one := fun _ hy => A.one_actPt hy
  mul := P.mulPt
  mul_mem := fun _ hg _ hh => P.mulPt_mem hg hh
  act_mul := fun _ hg _ hh _ hy => A.actPt_mulPt hg hh hy
  inv := P.invPt
  inv_mem := fun _ hg => P.invPt_mem hg
  act_inv_left := fun _ hg _ hy => A.invPt_actPt hg hy
  act_inv_right := fun _ hg _ hy => A.actPt_invPt hg hy

@[simp] theorem toPolyAction_G [IsAlgClosed K] [Finite γ] (hP : (MvPolynomial.vanishingIdeal K P.pts).IsPrime) :
    (A.toPolyAction hP).G = P.pts := rfl

@[simp] theorem toPolyAction_S [IsAlgClosed K] [Finite γ] (hP : (MvPolynomial.vanishingIdeal K P.pts).IsPrime) :
    (A.toPolyAction hP).S = A.pts := rfl

@[simp] theorem toPolyAction_act [IsAlgClosed K] [Finite γ] (hP : (MvPolynomial.vanishingIdeal K P.pts).IsPrime) :
    (A.toPolyAction hP).act = A.actPt := rfl

@[simp] theorem toPolyAction_orbit [IsAlgClosed K] [Finite γ] (hP : (MvPolynomial.vanishingIdeal K P.pts).IsPrime)
    (x : ι → K) : (A.toPolyAction hP).orbit x = {z | ∃ a ∈ P.pts, A.actPt a x = z} := rfl
/-! #### Products of actions

Both comodule laws of an action assembled from two blocks of coordinates are the laws of the
two factors, carried by a map `Φ` of coordinate rings of spaces over a map `π` of coordinate
rings of groups (`counit_coact_comp_of`, `coassoc_coact_comp_of`), provided the two `Φ`
jointly detect identities of algebra maps out of the assembled coordinate ring — the same
mechanism as `CommHopfData.ofPair`.  `ActionPresentation.prodLeft` (with the trivial action
on the second block) and `ActionPresentation.prod` are the two instances. -/

section Prod

variable {δ ν σ κ : Type u}

private theorem counit_coact_comp_of {R : GroupPresentation K ν}
    {C : ActionData R.toGroupData σ} (A : ActionPresentation P ι)
    (Φ : A.CoordRing →ₐ[K] C.CoordRing) (π : P.CoordRing →ₐ[K] R.CoordRing)
    (hcoact : C.coact.comp Φ = (Algebra.TensorProduct.map Φ π).comp A.coact)
    (hcounit : R.counit.comp π = P.counit) :
    ((Algebra.TensorProduct.map (AlgHom.id K C.CoordRing) R.counit).comp C.coact).comp Φ
      = ((Algebra.TensorProduct.rid K K C.CoordRing).symm :
          C.CoordRing →ₐ[K] C.CoordRing ⊗[K] K).comp Φ := by
  have hc : ∀ b : A.CoordRing, C.coact (Φ b)
      = Algebra.TensorProduct.map Φ π (A.coact b) := fun b => AlgHom.congr_fun hcoact b
  have h1 : ∀ t : A.CoordRing ⊗[K] P.CoordRing,
      Algebra.TensorProduct.map (AlgHom.id K C.CoordRing) R.counit
          (Algebra.TensorProduct.map Φ π t)
        = Algebra.TensorProduct.map Φ (AlgHom.id K K)
          (Algebra.TensorProduct.map (AlgHom.id K A.CoordRing) P.counit t) := by
    have e : (Algebra.TensorProduct.map (AlgHom.id K C.CoordRing) R.counit).comp
          (Algebra.TensorProduct.map Φ π)
        = (Algebra.TensorProduct.map Φ (AlgHom.id K K)).comp
          (Algebra.TensorProduct.map (AlgHom.id K A.CoordRing) P.counit) := by
      rw [← Algebra.TensorProduct.map_comp, ← Algebra.TensorProduct.map_comp]
      simp only [AlgHom.id_comp, AlgHom.comp_id, hcounit]
    exact fun t => AlgHom.congr_fun e t
  have hA : ∀ b : A.CoordRing,
      Algebra.TensorProduct.map (AlgHom.id K A.CoordRing) P.counit (A.coact b)
        = ((Algebra.TensorProduct.rid K K A.CoordRing).symm :
            A.CoordRing →ₐ[K] A.CoordRing ⊗[K] K) b :=
    fun b => AlgHom.congr_fun A.counit_coact b
  have hrid : ∀ b : A.CoordRing,
      ((Algebra.TensorProduct.rid K K C.CoordRing).symm :
          C.CoordRing →ₐ[K] C.CoordRing ⊗[K] K) (Φ b)
        = Algebra.TensorProduct.map Φ (AlgHom.id K K)
          (((Algebra.TensorProduct.rid K K A.CoordRing).symm :
            A.CoordRing →ₐ[K] A.CoordRing ⊗[K] K) b) :=
    fun b => AlgHom.congr_fun (rid_symm_naturality Φ) b
  refine AlgHom.ext fun b => ?_
  show Algebra.TensorProduct.map (AlgHom.id K C.CoordRing) R.counit (C.coact (Φ b))
    = ((Algebra.TensorProduct.rid K K C.CoordRing).symm :
        C.CoordRing →ₐ[K] C.CoordRing ⊗[K] K) (Φ b)
  rw [hc b, h1 (A.coact b), hA b, hrid b]

private theorem coassoc_coact_comp_of {R : GroupPresentation K ν}
    {C : ActionData R.toGroupData σ} (A : ActionPresentation P ι)
    (Φ : A.CoordRing →ₐ[K] C.CoordRing) (π : P.CoordRing →ₐ[K] R.CoordRing)
    (hcoact : C.coact.comp Φ = (Algebra.TensorProduct.map Φ π).comp A.coact)
    (hcomul : R.comul.comp π = (Algebra.TensorProduct.map π π).comp P.comul) :
    ((Algebra.TensorProduct.assoc K K K C.CoordRing R.CoordRing R.CoordRing).toAlgHom.comp
        ((Algebra.TensorProduct.map C.coact (AlgHom.id K R.CoordRing)).comp C.coact)).comp Φ
      = ((Algebra.TensorProduct.map (AlgHom.id K C.CoordRing)
          ((Algebra.TensorProduct.comm K R.CoordRing R.CoordRing).toAlgHom.comp R.comul)).comp
        C.coact).comp Φ := by
  have hc : ∀ b : A.CoordRing, C.coact (Φ b)
      = Algebra.TensorProduct.map Φ π (A.coact b) := fun b => AlgHom.congr_fun hcoact b
  have h1 : ∀ t : A.CoordRing ⊗[K] P.CoordRing,
      Algebra.TensorProduct.map C.coact (AlgHom.id K R.CoordRing)
          (Algebra.TensorProduct.map Φ π t)
        = Algebra.TensorProduct.map (Algebra.TensorProduct.map Φ π) π
          (Algebra.TensorProduct.map A.coact (AlgHom.id K P.CoordRing) t) := by
    have e : (Algebra.TensorProduct.map C.coact (AlgHom.id K R.CoordRing)).comp
          (Algebra.TensorProduct.map Φ π)
        = (Algebra.TensorProduct.map (Algebra.TensorProduct.map Φ π) π).comp
          (Algebra.TensorProduct.map A.coact (AlgHom.id K P.CoordRing)) := by
      rw [← Algebra.TensorProduct.map_comp, ← Algebra.TensorProduct.map_comp, hcoact]
      rfl
    exact fun t => AlgHom.congr_fun e t
  have hasn : ∀ s : (A.CoordRing ⊗[K] P.CoordRing) ⊗[K] P.CoordRing,
      (Algebra.TensorProduct.assoc K K K C.CoordRing R.CoordRing R.CoordRing).toAlgHom
          (Algebra.TensorProduct.map (Algebra.TensorProduct.map Φ π) π s)
        = Algebra.TensorProduct.map Φ (Algebra.TensorProduct.map π π)
          ((Algebra.TensorProduct.assoc K K K A.CoordRing P.CoordRing P.CoordRing).toAlgHom s) :=
    fun s => AlgHom.congr_fun (assoc_naturality Φ π π) s
  have hA : ∀ b : A.CoordRing,
      (Algebra.TensorProduct.assoc K K K A.CoordRing P.CoordRing P.CoordRing).toAlgHom
          (Algebra.TensorProduct.map A.coact (AlgHom.id K P.CoordRing) (A.coact b))
        = Algebra.TensorProduct.map (AlgHom.id K A.CoordRing)
            ((Algebra.TensorProduct.comm K P.CoordRing P.CoordRing).toAlgHom.comp P.comul)
            (A.coact b) :=
    fun b => AlgHom.congr_fun A.coassoc_coact b
  have e3 : (Algebra.TensorProduct.map π π).comp
        ((Algebra.TensorProduct.comm K P.CoordRing P.CoordRing).toAlgHom.comp P.comul)
      = ((Algebra.TensorProduct.comm K R.CoordRing R.CoordRing).toAlgHom.comp R.comul).comp π := by
    rw [← AlgHom.comp_assoc, ← comm_naturality π π, AlgHom.comp_assoc, ← hcomul,
      ← AlgHom.comp_assoc]
  have h2 : ∀ t : A.CoordRing ⊗[K] P.CoordRing,
      Algebra.TensorProduct.map Φ (Algebra.TensorProduct.map π π)
          (Algebra.TensorProduct.map (AlgHom.id K A.CoordRing)
            ((Algebra.TensorProduct.comm K P.CoordRing P.CoordRing).toAlgHom.comp P.comul) t)
        = Algebra.TensorProduct.map (AlgHom.id K C.CoordRing)
            ((Algebra.TensorProduct.comm K R.CoordRing R.CoordRing).toAlgHom.comp R.comul)
            (Algebra.TensorProduct.map Φ π t) := by
    have e : (Algebra.TensorProduct.map Φ (Algebra.TensorProduct.map π π)).comp
          (Algebra.TensorProduct.map (AlgHom.id K A.CoordRing)
            ((Algebra.TensorProduct.comm K P.CoordRing P.CoordRing).toAlgHom.comp P.comul))
        = (Algebra.TensorProduct.map (AlgHom.id K C.CoordRing)
            ((Algebra.TensorProduct.comm K R.CoordRing R.CoordRing).toAlgHom.comp R.comul)).comp
          (Algebra.TensorProduct.map Φ π) := by
      rw [← Algebra.TensorProduct.map_comp, ← Algebra.TensorProduct.map_comp,
        AlgHom.comp_id, AlgHom.id_comp, e3]
    exact fun t => AlgHom.congr_fun e t
  refine AlgHom.ext fun b => ?_
  show (Algebra.TensorProduct.assoc K K K C.CoordRing R.CoordRing R.CoordRing).toAlgHom
      (Algebra.TensorProduct.map C.coact (AlgHom.id K R.CoordRing) (C.coact (Φ b)))
    = Algebra.TensorProduct.map (AlgHom.id K C.CoordRing)
        ((Algebra.TensorProduct.comm K R.CoordRing R.CoordRing).toAlgHom.comp R.comul)
        (C.coact (Φ b))
  rw [hc b, h1 (A.coact b), hasn _, hA b, h2 (A.coact b)]

/-- **An action assembled from two blocks of coordinates.**  `C` is action data for `R` on
`σ`; two presented actions `A` of `P` on `ι` and `B` of `Q` on `κ` are carried into it by
maps `ΦL`, `ΦR` of coordinate rings over maps `πL`, `πR` of the groups' coordinate rings.
If `ΦL` and `ΦR` jointly detect identities of algebra maps out of `C.CoordRing`, the two
comodule laws of `C` follow from those of `A` and of `B`. -/
noncomputable def ofPair {R : GroupPresentation K ν} (C : ActionData R.toGroupData σ)
    {Q : GroupPresentation K δ} (A : ActionPresentation P ι) (B : ActionPresentation Q κ)
    (ΦL : A.CoordRing →ₐ[K] C.CoordRing) (ΦR : B.CoordRing →ₐ[K] C.CoordRing)
    (πL : P.CoordRing →ₐ[K] R.CoordRing) (πR : Q.CoordRing →ₐ[K] R.CoordRing)
    (hext : ∀ {D : Type u} [CommRing D] [Algebra K D] {φ ψ : C.CoordRing →ₐ[K] D},
      φ.comp ΦL = ψ.comp ΦL → φ.comp ΦR = ψ.comp ΦR → φ = ψ)
    (hcoactL : C.coact.comp ΦL = (Algebra.TensorProduct.map ΦL πL).comp A.coact)
    (hcoactR : C.coact.comp ΦR = (Algebra.TensorProduct.map ΦR πR).comp B.coact)
    (hcounitL : R.counit.comp πL = P.counit) (hcounitR : R.counit.comp πR = Q.counit)
    (hcomulL : R.comul.comp πL = (Algebra.TensorProduct.map πL πL).comp P.comul)
    (hcomulR : R.comul.comp πR = (Algebra.TensorProduct.map πR πR).comp Q.comul) :
    ActionPresentation R σ where
  toActionData := C
  counit_coact :=
    hext (counit_coact_comp_of A ΦL πL hcoactL hcounitL)
      (counit_coact_comp_of B ΦR πR hcoactR hcounitR)
  coassoc_coact :=
    hext (coassoc_coact_comp_of A ΦL πL hcoactL hcomulL)
      (coassoc_coact_comp_of B ΦR πR hcoactR hcomulR)

variable (P) in
/-- **The trivial action of a presented group on affine `κ`-space**: the coaction is
`b ↦ b ⊗ 1`. -/
noncomputable def trivialAction (κ : Type u) : ActionPresentation P κ :=
  ActionPresentation.ofLaws (ActionData.trivialActionData P.toGroupData κ)
    (fun _ => sub_mem_of_eq (by simp [ActionData.oneAct, ActionData.trivialActionData]))
    (fun _ => sub_mem_of_eq (by
      simp [ActionData.actAct, ActionData.mulAct, ActionData.act1,
        ActionData.trivialActionData]))

@[simp] theorem trivialAction_toActionData (κ : Type u) :
    (trivialAction P κ).toActionData = ActionData.trivialActionData P.toGroupData κ := rfl

/-- **`A` acting on the first of two blocks of coordinates**, the group not moving the
second (`ActionData.prodLeft`, with the trivial action on the second block). -/
noncomputable def prodLeft (κ : Type u) : ActionPresentation P (ι ⊕ κ) :=
  ofPair (A.toActionData.prodLeft κ) A (trivialAction P κ)
    (sumMkL A.J (⊥ : Ideal (MvPolynomial κ K)))
    (sumMkR A.J (⊥ : Ideal (MvPolynomial κ K)))
    (AlgHom.id K P.CoordRing) (AlgHom.id K P.CoordRing)
    (by
      intro D _ _ φ ψ hL hR
      exact sumAlgHom_ext A.J (⊥ : Ideal (MvPolynomial κ K)) hL hR)
    (by
      refine quotAlgHom_ext fun i => ?_
      show Algebra.TensorProduct.map
          (Ideal.Quotient.mkₐ K (sumIdeal A.J (⊥ : Ideal (MvPolynomial κ K))))
          (Ideal.Quotient.mkₐ K P.I)
          (tensorOfSum' K γ (ι ⊕ κ)
            (aeval (A.toActionData.prodLeftAct κ) (rename Sum.inl (X i))))
        = Algebra.TensorProduct.map (sumMkL A.J (⊥ : Ideal (MvPolynomial κ K)))
            (AlgHom.id K P.CoordRing)
          (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K A.J) (Ideal.Quotient.mkₐ K P.I)
            (tensorOfSum' K γ ι (aeval A.act (X i))))
      exact A.toActionData.prodLeft_coactHom_renameL κ (X i))
    (by
      refine quotAlgHom_ext fun k => ?_
      show Algebra.TensorProduct.map
          (Ideal.Quotient.mkₐ K (sumIdeal A.J (⊥ : Ideal (MvPolynomial κ K))))
          (Ideal.Quotient.mkₐ K P.I)
          (tensorOfSum' K γ (ι ⊕ κ)
            (aeval (A.toActionData.prodLeftAct κ) (rename Sum.inr (X k))))
        = Algebra.TensorProduct.map (sumMkR A.J (⊥ : Ideal (MvPolynomial κ K)))
            (AlgHom.id K P.CoordRing)
          (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K (⊥ : Ideal (MvPolynomial κ K)))
            (Ideal.Quotient.mkₐ K P.I)
            (tensorOfSum' K γ κ
              (aeval (ActionData.trivialActionData P.toGroupData κ).act (X k))))
      simp [ActionData.prodLeftAct, ActionData.trivialActionData, tensorOfSum'])
    (AlgHom.comp_id _) (AlgHom.comp_id _)
    (by rw [AlgHom.comp_id, Algebra.TensorProduct.map_id, AlgHom.id_comp])
    (by rw [AlgHom.comp_id, Algebra.TensorProduct.map_id, AlgHom.id_comp])

@[simp] theorem prodLeft_toActionData (κ : Type u) :
    (A.prodLeft κ).toActionData = A.toActionData.prodLeft κ := rfl

/-- **The product of two presented actions**: `P × Q` acting on `ι ⊕ κ` through `A` on the
first block and through `B` on the second. -/
noncomputable def prod {Q : GroupPresentation K δ} (B : ActionPresentation Q κ) :
    ActionPresentation (P.prod Q) (ι ⊕ κ) :=
  ofPair (A.toActionData.prod B.toActionData) A B (sumMkL A.J B.J) (sumMkR A.J B.J)
    (P.toGroupData.prodMkL Q.toGroupData) (P.toGroupData.prodMkR Q.toGroupData)
    (by
      intro D _ _ φ ψ hL hR
      exact sumAlgHom_ext A.J B.J hL hR)
    (by
      refine quotAlgHom_ext fun i => ?_
      show Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K (sumIdeal A.J B.J))
          (Ideal.Quotient.mkₐ K (sumIdeal P.I Q.I))
          (tensorOfSum' K (γ ⊕ δ) (ι ⊕ κ)
            (aeval (A.toActionData.prodAct B.toActionData) (rename Sum.inl (X i))))
        = Algebra.TensorProduct.map (sumMkL A.J B.J) (sumMkL P.I Q.I)
          (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K A.J) (Ideal.Quotient.mkₐ K P.I)
            (tensorOfSum' K γ ι (aeval A.act (X i))))
      exact A.toActionData.prod_coactHom_renameL B.toActionData (X i))
    (by
      refine quotAlgHom_ext fun k => ?_
      show Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K (sumIdeal A.J B.J))
          (Ideal.Quotient.mkₐ K (sumIdeal P.I Q.I))
          (tensorOfSum' K (γ ⊕ δ) (ι ⊕ κ)
            (aeval (A.toActionData.prodAct B.toActionData) (rename Sum.inr (X k))))
        = Algebra.TensorProduct.map (sumMkR A.J B.J) (sumMkR P.I Q.I)
          (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K B.J) (Ideal.Quotient.mkₐ K Q.I)
            (tensorOfSum' K δ κ (aeval B.act (X k))))
      exact A.toActionData.prod_coactHom_renameR B.toActionData (X k))
    (P.toGroupData.prod_counit_comp_prodMkL Q.toGroupData)
    (P.toGroupData.prod_counit_comp_prodMkR Q.toGroupData)
    (P.toGroupData.prod_comul_comp_prodMkL Q.toGroupData)
    (P.toGroupData.prod_comul_comp_prodMkR Q.toGroupData)

@[simp] theorem prod_toActionData {Q : GroupPresentation K δ} (B : ActionPresentation Q κ) :
    (A.prod B).toActionData = A.toActionData.prod B.toActionData := rfl

end Prod

end ActionPresentation

/-! ### The classical corollaries of `Spec.lean` §4

`Spec.lean` §4 counts the dimension of a locus in a scheme `X` carrying a `ModObj` action,
with hypotheses about *sections*.  Consumers work with a constructible subset of
`𝔸(ι; Spec K)`, a `HomOver` map and `K`-points; these are the counts in that form.  They
cannot live in `Spec.lean`: they mention `GroupPresentation`, and `Geometry/Group.lean`
imports `Geometry/Spec.lean`, not the other way round.

The route is the coordinate one — an `ActionPresentation` with `A.J = ⊥` is a `PolyAction`
on all of `ι → K` (`toPolyAction`), and the counts of `Dimension/LocClosed.lean` apply to
`K`-points directly, `topologicalKrullDim_eq_affineDim` matching the two sides.  This is why
every hypothesis is about `K`-points, and it avoids transporting `Z`, the map and the orbits
along an isomorphism `A.scheme ≅ 𝔸(ι; Spec K)`. -/

theorem ActionData.pts_eq_univ {P : GroupData K γ} (A : ActionData P ι) (hJ : A.J = ⊥) :
    A.pts = Set.univ := by
  refine Set.eq_univ_of_forall fun x p hp => ?_
  rw [hJ, Ideal.mem_bot] at hp
  simp [hp]

section Corollaries

variable [IsAlgClosed K] [Finite γ] [Finite ι] {κ : Type u} [Finite κ]
  (P : GroupPresentation K γ)

/-! #### The classical forms

These are the counts consumers call: every set is a set of `K`-points, every map is an
`IsPolyMap`, and the group is a `GroupPresentation` acting through an `ActionPresentation`
on all of `ι → K`.  Each is one application of the corresponding theorem of
`Dimension/LocClosed.lean` to `ActionPresentation.toPolyAction`; the `𝔸`-shaped `_pts`
corollaries below are the same statements read through `ptEquiv`, and no consumer needs
them.

The other two counts of the family need no group and are already classical:
`Dimension/LocClosed.affineDim_of_finite_fibres_constructible` (a polynomial map with finite
fibres over `K`-points preserves the `affineDim` of a constructible set) and
`Dimension/Components.affineDim_image_le` (`affineDim (f '' Y) ≤ affineDim Y`, any `Y`). -/

/-- **The orbit fibration count, classical form.**  For a presented group `P` acting on
`ι → K` (an `ActionPresentation` with `A.J = ⊥`), a polynomial map `f` invariant along the
action on a `P`-stable constructible `Y` whose fibres over the image are single orbits, all
of dimension `e`: `dim (f '' Y) + e = dim Y`.

This is `Dimension/LocClosed.affineDim_of_orbit_fibration_constructible` with the group a
presentation; `Chain/Untwist`'s conjugation fibration and `Chain/Hyps`'s marked fibration
are the consumers. -/
theorem GroupPresentation.affineDim_of_orbit_fibration
    (hP : (MvPolynomial.vanishingIdeal K P.pts).IsPrime)
    (A : ActionPresentation P ι) (hJ : A.J = ⊥)
    {f : (ι → K) → (κ → K)} (hf : IsPolyMap f)
    {Y : Set (ι → K)} (hY : IsAffineConstructible Y) {e : ℕ}
    (hstable : ∀ a ∈ P.pts, ∀ y ∈ Y, A.actPt a y ∈ Y)
    (hinv : ∀ a ∈ P.pts, ∀ y ∈ Y, f (A.actPt a y) = f y)
    (hfib : ∀ x ∈ f '' Y, ∃ y ∈ Y, Y ∩ f ⁻¹' {x} = {z | ∃ a ∈ P.pts, A.actPt a y = z})
    (horb : ∀ y ∈ Y, affineDim {z | ∃ a ∈ P.pts, A.actPt a y = z} = (e : WithBot ℕ∞)) :
    affineDim (f '' Y) + (e : WithBot ℕ∞) = affineDim Y :=
  affineDim_of_orbit_fibration_constructible (A.toPolyAction hP) hf Y _ e hY
    (by rw [ActionPresentation.toPolyAction_S, A.pts_eq_univ hJ]; exact Set.subset_univ _)
    rfl hstable hinv hfib horb

/-- **The lower half of the orbit fibration count, classical form.**  For a presented group
`P` acting on `ι → K` (an `ActionPresentation` with `A.J = ⊥`), a polynomial map `f` constant
along the action on a `P`-stable constructible `Y` all of whose orbits have dimension at least
`e`: `dim (f '' Y) + e ≤ dim Y`.

The fibres are not assumed to be single orbits — in `Chain/Springer` they are unions of
orbits — so only this half of `affineDim_of_orbit_fibration` is available.  This is
`Dimension/LocClosed.affineDim_image_add_le_of_orbit_le_constructible` with the group a
presentation; `Chain/Springer`'s Borel fibration of the partner incidence is the consumer. -/
theorem GroupPresentation.affineDim_image_add_le_of_orbit_le
    (hP : (MvPolynomial.vanishingIdeal K P.pts).IsPrime)
    (A : ActionPresentation P ι) (hJ : A.J = ⊥)
    {f : (ι → K) → (κ → K)} (hf : IsPolyMap f)
    {Y : Set (ι → K)} (hY : IsAffineConstructible Y) {e : WithBot ℕ∞}
    (hstable : ∀ a ∈ P.pts, ∀ y ∈ Y, A.actPt a y ∈ Y)
    (hinv : ∀ a ∈ P.pts, ∀ y ∈ Y, f (A.actPt a y) = f y)
    (horb : ∀ y ∈ Y, e ≤ affineDim {z | ∃ a ∈ P.pts, A.actPt a y = z}) :
    affineDim (f '' Y) + e ≤ affineDim Y :=
  affineDim_image_add_le_of_orbit_le_constructible (A.toPolyAction hP) hf Y _ e hY
    (by rw [ActionPresentation.toPolyAction_S, A.pts_eq_univ hJ]; exact Set.subset_univ _)
    rfl hstable hinv horb

/-- **The transitive fibration count, classical form.**  For a presented group `P` acting on
`ι → K` and on `κ → K`, a polynomial map `f` equivariant on a `P`-stable constructible `Y`
whose image is one orbit of `y₀`, and one fibre of dimension `d`:
`dim Y = dim (f '' Y) + d`.

This is `Dimension/LocClosed.affineDim_of_transitive_fibration_constructible` with the group
a presentation. -/
theorem GroupPresentation.affineDim_of_transitive_fibration
    (hP : (MvPolynomial.vanishingIdeal K P.pts).IsPrime)
    (A : ActionPresentation P ι) (hJ : A.J = ⊥)
    (B : ActionPresentation P κ) (hJ' : B.J = ⊥)
    {f : (ι → K) → (κ → K)} (hf : IsPolyMap f)
    {Y : Set (ι → K)} (hY : IsAffineConstructible Y) (y₀ : κ → K) {d : ℕ}
    (hstable : ∀ a ∈ P.pts, ∀ y ∈ Y, A.actPt a y ∈ Y)
    (hequiv : ∀ a ∈ P.pts, ∀ y ∈ Y, f (A.actPt a y) = B.actPt a (f y))
    (hy₀ : y₀ ∈ f '' Y) (htrans : ∀ x ∈ f '' Y, ∃ a ∈ P.pts, B.actPt a y₀ = x)
    (hd : affineDim (Y ∩ f ⁻¹' {y₀}) = (d : WithBot ℕ∞)) :
    affineDim Y = affineDim (f '' Y) + (d : WithBot ℕ∞) :=
  affineDim_of_transitive_fibration_constructible (A.toPolyAction hP) B.actPt hf Y _ y₀ d hY
    (by rw [ActionPresentation.toPolyAction_S, A.pts_eq_univ hJ]; exact Set.subset_univ _)
    rfl hstable hequiv
    (fun a ha x _ => B.invPt_actPt ha (by rw [B.pts_eq_univ hJ']; exact Set.mem_univ x))
    hy₀ htrans hd

end Corollaries
end Height.Geometry
