module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFibreAndEqOfSpecializesOfIsFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteFromSpecResidueFieldCompOfIsClosedOfClosStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleSpaceFibreSemiAbelianFieldPoint
import Mathlib.Tactic.Linter.Style
import Mathlib.Order.CompletePartialOrder

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfSpecializesSemiAbelianSquareSameProjections

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem eq_of_specializes_of_fst_eq_of_snd_eq :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G →
      ∀ x : G.left, G.hom x = closedPoint R → IsClosed ({x} : Set G.left) →
      ∀ p q : (G ⊗ G).left, (fst G G).left p = x → (fst G G).left q = x →
        (snd G G).left p = (snd G G).left q → p ⤳ q → p = q := by
  intro R _ _ G _ hG x hx hxc p q hp hq hpq hs
  haveI : Smooth G.hom := hG.smooth
  have hfin : IsFinite (G.left.fromSpecResidueField x ≫ G.hom) := GlobalTheory.T.isFinite_fromSpecResidueField_comp_of_closed R G inferInstance x hx hxc

  let j : pullback (pullback.fst G.hom G.hom) (G.left.fromSpecResidueField x) ⟶ pullback G.hom G.hom :=
    pullback.fst _ _
  let e := pullbackSymmetry (pullback.fst G.hom G.hom) (G.left.fromSpecResidueField x) ≪≫
    pullbackRightPullbackFstIso G.hom G.hom (G.left.fromSpecResidueField x)
  have hk : j ≫ pullback.snd G.hom G.hom = e.hom ≫ pullback.snd _ _ := by
    simp [e, j, pullbackRightPullbackFstIso_hom_snd]
  have hkf : IsFinite (j ≫ pullback.snd G.hom G.hom) := by rw [hk]; infer_instance
  have hr : Set.range j = (pullback.fst G.hom G.hom) ⁻¹' {x} := by
    simp only [j, Scheme.Pullback.range_fst, Scheme.range_fromSpecResidueField]
  obtain ⟨p', rfl⟩ : p ∈ Set.range j := by rw [hr]; exact hp
  obtain ⟨q', rfl⟩ : q ∈ Set.range j := by rw [hr]; exact hq
  have hs' : p' ⤳ q' := (j.isEmbedding.toIsInducing.specializes_iff).mp hs
  have := (GlobalTheory.finite_fibre_and_eq_of_specializes_of_isFinite _ _ _ hkf
    ((j ≫ pullback.snd G.hom G.hom) q')).2 p' q' (by simpa using hpq) rfl hs'
  rw [this]

end GlobalTheory.Mum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfSpecializesSemiAbelianSquareSameProjectionsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.eq_of_specializes_semiAbelian_square_same_projections : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → ∀ x : G.left, G.hom x = closedPoint R → IsClosed ({x} : Set G.left) → ∀ p q : (G ⊗ G).left, (fst G G).left p = x → (fst G G).left q = x → (snd G G).left p = (snd G G).left q → p ⤳ q → p = q := by
  first | exact @GlobalTheory.Mum.eq_of_specializes_of_fst_eq_of_snd_eq | exact GlobalTheory.Mum.eq_of_specializes_of_fst_eq_of_snd_eq | (intros; apply GlobalTheory.Mum.eq_of_specializes_of_fst_eq_of_snd_eq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedImageSndOfSubsetSemiAbelianFibre

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.Mum.isClosed_image_snd_of_subset_fibre_closedPoint :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G →
      ∀ x : G.left, G.hom x = closedPoint R → IsClosed ({x} : Set G.left) →
      ∀ N : Set (G ⊗ G).left, IsClosed N → N ⊆ (fst G G).left ⁻¹' {x} →
      IsClosed ((snd G G).left '' N) := by
  intro R _ _ G _ hG x hx hxc N hN hNZ
  have hlft : LocallyOfFiniteType G.hom := by
    haveI := hG.smooth; infer_instance
  have hfin : IsFinite (G.left.fromSpecResidueField x ≫ G.hom) :=
    GlobalTheory.T.isFinite_fromSpecResidueField_comp_of_closed R G hlft x hx hxc
  set k := G.left.fromSpecResidueField x
  set f := G.hom
  let i := pullback.snd k (pullback.fst f f)
  have hrange : Set.range i = (pullback.fst f f) ⁻¹' {x} := by
    simp only [i, Scheme.Pullback.range_snd, k, Scheme.range_fromSpecResidueField]
  have hcomp : i ≫ pullback.snd f f =
      (pullbackRightPullbackFstIso f f k).hom ≫ pullback.snd (k ≫ f) f :=
    (pullbackRightPullbackFstIso_hom_snd f f k).symm
  have hcl : IsClosedMap (i ≫ pullback.snd f f) := by
    rw [hcomp]
    haveI := hfin
    haveI : IsFinite (pullback.snd (k ≫ f) f) := inferInstance
    exact ((pullbackRightPullbackFstIso f f k).hom ≫ pullback.snd (k ≫ f) f).isClosedMap
  have hNi : (snd G G).left '' N = (i ≫ pullback.snd f f) '' (i ⁻¹' N) := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.image_comp, Set.image_preimage_eq_of_subset]
    · rfl
    · rw [hrange]; exact hNZ
  rw [hNi]
  exact hcl _ (hN.preimage i.continuous)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedImageSndOfSubsetSemiAbelianFibreStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.isClosed_image_snd_of_subset_semiAbelian_fibre : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → ∀ x : G.left, G.hom x = closedPoint R → IsClosed ({x} : Set G.left) → ∀ N : Set (G ⊗ G).left, IsClosed N → N ⊆ (fst G G).left ⁻¹' {x} → IsClosed ((snd G G).left '' N) := by
  first | exact @GlobalTheory.Mum.isClosed_image_snd_of_subset_fibre_closedPoint | exact GlobalTheory.Mum.isClosed_image_snd_of_subset_fibre_closedPoint | (intros; apply GlobalTheory.Mum.isClosed_image_snd_of_subset_fibre_closedPoint <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIrreducibleFibreFst

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MoverFibre

theorem isIrreducible_fibre_fst : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → ∀ x : G.left, IsIrreducible ((fst G G).left ⁻¹' {x}) := by
  intro R _ G _ hG x
  let j := G.left.fromSpecResidueField x
  let p₁ : pullback G.hom G.hom ⟶ G.left := pullback.fst G.hom G.hom
  have hp : (fst G G).left = p₁ := rfl
  have hirr0 := GlobalTheory.SemiAbFibre.irreducibleSpace_fibre _ G hG _ (j ≫ G.hom)
  haveI hirr : IrreducibleSpace (pullback G.hom (j ≫ G.hom) : Scheme.{0}) := hirr0
  let e : pullback G.hom (j ≫ G.hom) ≅ p₁.fiber x :=
    pullbackSymmetry _ _ ≪≫ (pullbackRightPullbackFstIso G.hom G.hom j).symm ≪≫ pullbackSymmetry _ _
  have hr := (IrreducibleSpace.isIrreducible_univ (pullback G.hom (j ≫ G.hom) : Scheme.{0})).image _
      ((e.hom ≫ Scheme.Hom.fiberι p₁ x).continuous.continuousOn)
  rw [Set.image_univ] at hr
  have hrange : Set.range (e.hom ≫ Scheme.Hom.fiberι p₁ x) = Set.range (Scheme.Hom.fiberι p₁ x) := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨e.hom z, by rw [Scheme.Hom.comp_apply]⟩
    · rintro ⟨z, rfl⟩
      exact ⟨e.inv z, by rw [Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply e.inv e.hom, e.inv_hom_id]; rfl⟩
  show IsIrreducible (p₁ ⁻¹' {x})
  rw [← Scheme.Hom.range_fiberι p₁ x, ← hrange]
  exact hr

end GlobalTheory.MoverFibre
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIrreducibleFibreFstStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.isIrreducible_preimage_fst_of_isSemiAbelian : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → ∀ x : G.left, IsIrreducible ((fst G G).left ⁻¹' {x}) := by
  first | exact @GlobalTheory.MoverFibre.isIrreducible_fibre_fst | exact GlobalTheory.MoverFibre.isIrreducible_fibre_fst | (intros; apply GlobalTheory.MoverFibre.isIrreducible_fibre_fst <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenTranslationsMovingClosedPointsIntoOpen

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem exists_open_mul_mem : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (V : G.left.Opens), (∃ v ∈ V, G.hom v = closedPoint R) → ∀ s : Finset G.left, (∀ x ∈ s, G.hom x = closedPoint R ∧ IsClosed ({x} : Set G.left)) → ∃ O : G.left.Opens, (∃ u ∈ O, G.hom u = closedPoint R) ∧ ∀ (Ω : Type) [Field Ω] (t : Sp Ω ⟶ Sp R) (x a : Over.mk t ⟶ G), (∀ z, x.left z ∈ s) → (∀ z, a.left z ∈ O) → ∀ z, (x * a).left z ∈ V := by
  intro R _ _ _ G _ _ hG V hV s hs
  obtain ⟨v, hvV, hvc⟩ := hV
  set F : Set G.left := G.hom ⁻¹' {closedPoint R} with hFdef
  have hFc : IsClosed F := (isClosed_singleton_closedPoint R).preimage G.hom.continuous
  have hcond : ∀ p : (G ⊗ G).left, G.hom ((snd G G).left p) = G.hom ((fst G G).left p) := fun p => by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply]
    exact congrArg (fun h : (G ⊗ G).left ⟶ Sp R => h p) pullback.condition.symm
  have hsurj : ∀ x : G.left, G.hom x = closedPoint R → (snd G G).left '' ((fst G G).left ⁻¹' {x}) = F := by
    intro x hx
    ext w
    constructor
    · rintro ⟨p, hp, rfl⟩
      show G.hom _ = closedPoint R
      rw [hcond p, show (fst G G).left p = x from hp, hx]
    · intro hw
      obtain ⟨p, h1, h2⟩ := Scheme.Pullback.exists_preimage_pullback (f := G.hom) (g := G.hom) x w (hx.trans hw.symm)
      exact ⟨p, h1, h2⟩
  have hmu : ∀ p : (G ⊗ G).left, G.hom (μ[G].left p) = G.hom ((fst G G).left p) := fun p => by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Over.w μ[G]]
    rfl
  let Ψ : G ⊗ G ⟶ G ⊗ G := lift (fst G G) ((fst G G)⁻¹ * snd G G)
  have hΨ1 : Ψ ≫ fst G G = fst G G := lift_fst _ _
  have hΨ2 : Ψ ≫ μ[G] = snd G G := by
    show fst G G * ((fst G G)⁻¹ * snd G G) = snd G G
    exact mul_inv_cancel_left _ _
  have hmsurj : ∀ x : G.left, G.hom x = closedPoint R → μ[G].left '' ((fst G G).left ⁻¹' {x}) = F := by
    intro x hx
    ext w
    constructor
    · rintro ⟨p, hp, rfl⟩
      show G.hom _ = closedPoint R
      rw [hmu p, show (fst G G).left p = x from hp, hx]
    · intro hw
      obtain ⟨q, hq, rfl⟩ := (hsurj x hx).symm ▸ hw
      refine ⟨Ψ.left q, ?_, ?_⟩
      · show (fst G G).left (Ψ.left q) = x
        rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hΨ1]; exact hq
      · rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hΨ2]
  have hFirr : IsIrreducible F := by
    rw [← hsurj v hvc]
    exact (GlobalTheory.T.isIrreducible_preimage_fst_of_isSemiAbelian R G hG v).image _ (snd G G).left.continuous.continuousOn
  set gpt := hFirr.genericPoint
  have hgp : IsGenericPoint gpt F := by
    have := hFirr.isGenericPoint_genericPoint_closure
    rwa [hFc.closure_eq] at this

  have gen_of : ∀ (f : (G ⊗ G).left → G.left), Continuous f → ∀ (Z : Set (G ⊗ G).left) (ξ : (G ⊗ G).left),
      IsGenericPoint ξ Z → f '' Z = F → f ξ = gpt := by
    intro f hf Z ξ hξ hZ
    refine IsGenericPoint.eq ?_ hgp
    show closure {f ξ} = F
    apply le_antisymm
    · exact hFc.closure_subset_iff.2 (Set.singleton_subset_iff.2 (hZ ▸ ⟨ξ, hξ.mem, rfl⟩))
    · rw [← hZ, ← hξ.def, ← Set.image_singleton]
      exact image_closure_subset_closure_image hf
  let T : G.left → Set G.left := fun x =>
    (snd G G).left '' ((fst G G).left ⁻¹' {x} ∩ μ[G].left ⁻¹' (V : Set G.left)ᶜ)
  have hTc : ∀ x ∈ s, IsClosed (T x) := by
    intro x hx
    refine GlobalTheory.T.isClosed_image_snd_of_subset_semiAbelian_fibre R G hG x (hs x hx).1 (hs x hx).2 _ ?_ Set.inter_subset_left
    exact ((hs x hx).2.preimage (fst G G).left.continuous).inter
      (V.isOpen.isClosed_compl.preimage μ[G].left.continuous)
  have hgpV : gpt ∈ (V : Set G.left) := (hgp.specializes (show v ∈ F from hvc)).mem_open V.isOpen hvV
  have hgpT : ∀ x ∈ s, gpt ∉ T x := by
    intro x hx ⟨n, ⟨hn1, hn2⟩, hn3⟩
    have hZc : IsClosed ((fst G G).left ⁻¹' {x}) := (hs x hx).2.preimage (fst G G).left.continuous
    have hZi := GlobalTheory.T.isIrreducible_preimage_fst_of_isSemiAbelian R G hG x
    have hξ : IsGenericPoint hZi.genericPoint ((fst G G).left ⁻¹' {x}) := by
      have := hZi.isGenericPoint_genericPoint_closure
      rwa [hZc.closure_eq] at this
    have e2 := gen_of _ (snd G G).left.continuous _ _ hξ (hsurj x (hs x hx).1)
    have em := gen_of _ μ[G].left.continuous _ _ hξ (hmsurj x (hs x hx).1)
    have hnξ : hZi.genericPoint = n :=
      GlobalTheory.T.eq_of_specializes_semiAbelian_square_same_projections R G hG x (hs x hx).1 (hs x hx).2 _ _ hξ.mem hn1 (e2.trans hn3.symm) (hξ.specializes hn1)
    exact hn2 (hnξ ▸ em ▸ hgpV)
  refine ⟨⟨(⋃ x ∈ (s : Set G.left), T x)ᶜ,
    isOpen_compl_iff.2 (s.finite_toSet.isClosed_biUnion hTc)⟩, ⟨gpt, ?_, hgp.mem⟩, ?_⟩
  · show gpt ∉ ⋃ x ∈ (s : Set G.left), T x
    simp only [Set.mem_iUnion, not_exists]
    exact fun x hx => hgpT x hx
  · intro Ω _ t x a hx ha z
    by_contra hz
    let q : Over.mk t ⟶ G ⊗ G := lift x a
    have h1 : (fst G G).left (q.left z) = x.left z := by
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, lift_fst]
    have h2 : (snd G G).left (q.left z) = a.left z := by
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, lift_snd]
    have h3 : μ[G].left (q.left z) = (x * a).left z := by
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left]; rfl
    have hO := ha z
    simp only [TopologicalSpace.Opens.mem_mk, Set.mem_compl_iff, Set.mem_iUnion, not_exists] at hO
    exact hO (x.left z) (hx z) ⟨q.left z, ⟨h1, by simp only [Set.mem_preimage, Set.mem_compl_iff, h3]; exact hz⟩, h2⟩

end GlobalTheory.Mum
end
end
end
