module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldMapCompConstFn
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvrExtensionOfEssentiallyEtaleLocalStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NadelVanishingCanonicalAddBoundary
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsBasisKaehlerOfAlgebraicIndependent
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkMapFlatFormallyEtaleEssFiniteTypeOfEtaleRes
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Tactic.Basify
import Mathlib.Tactic.TypeStar

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrdFracFunctionFieldMapOfEssentiallyEtale

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
open IsLocalRing

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.EtaleKlt

theorem ord_functionFieldMap_of_formallyEtale : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (p : W ⟶ Sp ℂ) (f : M ⟶ W) [IsDominant f] (E : DivOver p) (E' : DivOver (f ≫ p)) (h : ∀ x ∈ E.ring, functionFieldMap f x ∈ E'.ring), (∀ x, functionFieldMap f x ∈ E'.ring → x ∈ E.ring) → ((functionFieldMap f).restrict E.ring E'.ring h).FormallyEtale → ((functionFieldMap f).restrict E.ring E'.ring h).EssFiniteType → ∀ g : W.functionFieldˣ, E'.ord (Units.map (functionFieldMap f).toMonoidHom g) = E.ord g := by
  intro M W _ _ p f _ E E' h htr het hft g
  set φ := functionFieldMap f
  set ρ := φ.restrict E.ring E'.ring h
  letI := ρ.toAlgebra
  haveI : Algebra.FormallyEtale E.ring E'.ring := het
  haveI : Algebra.EssFiniteType E.ring E'.ring := hft
  haveI : IsLocalHom (algebraMap E.ring E'.ring) := by
    refine ⟨fun x hx => ?_⟩
    obtain ⟨y, hy⟩ := hx.exists_right_inv
    have e : φ (x : W.functionField) * (y : M.functionField) = 1 := congrArg Subtype.val hy
    have hx0 : (x : W.functionField) ≠ 0 := by
      rintro h0
      rw [h0, map_zero, zero_mul] at e
      exact zero_ne_one e
    have hinv : φ ((x : W.functionField)⁻¹) = y := by
      rw [map_inv₀]
      exact inv_eq_of_mul_eq_one_right e
    have hmem : (x : W.functionField)⁻¹ ∈ E.ring := htr _ (hinv ▸ y.2)
    exact IsUnit.of_mul_eq_one (b := (⟨_, hmem⟩ : E.ring)) (Subtype.ext (mul_inv_cancel₀ hx0))
  have hm := Algebra.FormallyUnramified.map_maximalIdeal (R := E.ring) (S := E'.ring)
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible E.ring
  have ht' : Irreducible (ρ t) := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer, ← hm, (IsDiscreteValuationRing.irreducible_iff_uniformizer t).1 ht, Ideal.map_span,
      Set.image_singleton]
    rfl
  obtain ⟨m, u, e⟩ := exists_eq_unit_mul_zpow (F := W.functionField) ht g.ne_zero
  have h1 := ordTop_vw_unit_mul_zpow (F := W.functionField) ht u m
  have h2 := ordTop_vw_unit_mul_zpow (F := M.functionField) ht' (Units.map ρ.toMonoidHom u) m
  rw [← e, ordTop_vw_of_ne_zero _ g.ne_zero, WithTop.coe_inj] at h1
  have e2 : ((Units.map φ.toMonoidHom g : M.functionFieldˣ) : M.functionField) =
      algebraMap E'.ring M.functionField (Units.map ρ.toMonoidHom u) *
        algebraMap E'.ring M.functionField (ρ t) ^ m := by
    rw [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, e, map_mul, map_zpow₀]
    rfl
  rw [← e2, ordTop_vw_of_ne_zero _ (Units.ne_zero _), WithTop.coe_inj] at h2
  exact h2.trans h1.symm

end GlobalTheory.EtaleKlt
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrdFracFunctionFieldMapOfEssentiallyEtaleStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy

theorem _root_.GlobalTheory.T.ordFrac_functionFieldMap_of_essentiallyEtale : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (p : W ⟶ Sp ℂ) (f : M ⟶ W) [IsDominant f] (E : DivOver p) (E' : DivOver (f ≫ p)) (h : ∀ x ∈ E.ring, functionFieldMap f x ∈ E'.ring), (∀ x, functionFieldMap f x ∈ E'.ring → x ∈ E.ring) → ((functionFieldMap f).restrict E.ring E'.ring h).FormallyEtale → ((functionFieldMap f).restrict E.ring E'.ring h).EssFiniteType → ∀ g : W.functionFieldˣ, E'.ord (Units.map (functionFieldMap f).toMonoidHom g) = E.ord g := by
  first | exact @GlobalTheory.EtaleKlt.ord_functionFieldMap_of_formallyEtale | exact GlobalTheory.EtaleKlt.ord_functionFieldMap_of_formallyEtale | (intros; apply GlobalTheory.EtaleKlt.ord_functionFieldMap_of_formallyEtale <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkMapFlatFormallyEtaleEssFiniteTypeOfEtaleResStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry

theorem _root_.GlobalTheory.T.stalkMap_flat_formallyEtale_essFiniteType_of_etale_open : ∀ (M W : Scheme.{0}) (f : M ⟶ W) (U : M.Opens), Etale (U.ι ≫ f) → ∀ y ∈ U, (f.stalkMap y).hom.Flat ∧ (f.stalkMap y).hom.FormallyEtale ∧ (f.stalkMap y).hom.EssFiniteType := by
  first | exact @GlobalTheory.stalkMap_flat_formallyEtale_essFiniteType_of_etale_restrict | exact GlobalTheory.stalkMap_flat_formallyEtale_essFiniteType_of_etale_restrict | (intros; apply GlobalTheory.stalkMap_flat_formallyEtale_essFiniteType_of_etale_restrict <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopFormOrderRationalPullbackOfEssentiallyEtale

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.EtaleKlt

theorem isFreeGen_formMap_of_formallyEtale {k A B : Type*} [CommRing k] [CommRing A] [CommRing B]
    {α : k →+* A} {β : k →+* B} {D : ℕ} {ρ : A →+* B} (hρ : ρ.FormallyEtale) (h : ρ.comp α = β)
    {ω : Forms α D} (hω : IsFreeGen A ω) : IsFreeGen B (TopForm.formMap D ρ h ω) := by
  letI := α.toAlgebra
  letI := β.toAlgebra
  letI := ρ.toAlgebra
  haveI : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq' h.symm
  haveI : Algebra.FormallyEtale A B := hρ
  exact hω.of_isBaseChange (isBaseChange_exteriorPower
    (KaehlerDifferential.isBaseChange_of_formallyEtale k A B) D)

theorem formOrd_ratPull (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (p : W ⟶ Sp ℂ)
    (f : M ⟶ W) [IsDominant f] (n : ℕ) [LocallyOfFiniteType p]
    (hn : topologicalKrullDim W = n) (E : DivOver p) (E' : DivOver (f ≫ p))
    (h : ∀ x ∈ E.ring, functionFieldMap f x ∈ E'.ring)
    (hρ : ((functionFieldMap f).restrict E.ring E'.ring h).FormallyEtale)
    (hord : ∀ g : W.functionFieldˣ,
      E'.ord (Units.map (functionFieldMap f).toMonoidHom g) = E.ord g)
    (η : RatForms p n) (hη : η ≠ 0) :
    (fun ω => @dite ℤ (∃ a, E'.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (GlobalTheory.EtaleKlt.ratPull p f n η) = (fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) η := by
  set φ := functionFieldMap f with hφ
  set ρ := φ.restrict E.ring E'.ring h with hρdef
  obtain ⟨ω, hω, g, hη', hg⟩ := E.isFormOrd_formOrd hn hη
  have hc : ρ.comp E.const = E'.const := by
    ext a
    exact RingHom.congr_fun (functionFieldMap_comp_constFn p f) a
  have hω' : IsFreeGen E'.ring (TopForm.formMap n ρ hc ω) := isFreeGen_formMap_of_formallyEtale hρ hc hω
  have e : φ.comp E.ring.subtype = E'.ring.subtype.comp ρ := by
    ext x
    rfl
  have hτ : (E'.ring.subtype.comp ρ).comp E.const = Cartier.constFn (f ≫ p) := by
    rw [RingHom.comp_assoc, hc]
    rfl
  have key : ratPull p f n (E.toRat n ω) = E'.toRat n (TopForm.formMap n ρ hc ω) := by
    have k1 := TopForm.formMap_formMap (D := n) E.ring.subtype φ _ e rfl
      (functionFieldMap_comp_constFn p f) hτ ω
    have k2 := TopForm.formMap_formMap (D := n) ρ E'.ring.subtype _ rfl hc rfl hτ ω
    exact k1.trans k2.symm
  have hpull : ratPull p f n η = φ (g : W.functionField) • E'.toRat n (TopForm.formMap n ρ hc ω) := by
    rw [hη', map_smulₛₗ, key]
  have hne : ratPull p f n η ≠ 0 := by
    rw [hpull]
    intro h0
    have hinj := (E'.isFreeGen_toRat hω').1
    have : φ (g : W.functionField) = 0 := hinj (by simpa using h0)
    exact (g.map φ.toMonoidHom).ne_zero this
  change E'.formOrd (ratPull p f n η) = E.formOrd η
  rw [← hg]
  refine DivOver.IsFormOrd.formOrd_eq hne ⟨_, hω', Units.map φ.toMonoidHom g, hpull, hord g⟩

end GlobalTheory.EtaleKlt
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopFormOrderRationalPullbackOfEssentiallyEtaleStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy

theorem _root_.GlobalTheory.T.topFormOrder_rationalPullback_of_essentiallyEtale : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (p : W ⟶ Sp ℂ) (f : M ⟶ W) [IsDominant f] (n : ℕ) [LocallyOfFiniteType p], topologicalKrullDim W = n → ∀ (E : DivOver p) (E' : DivOver (f ≫ p)) (h : ∀ x ∈ E.ring, functionFieldMap f x ∈ E'.ring), ((functionFieldMap f).restrict E.ring E'.ring h).FormallyEtale → (∀ g : W.functionFieldˣ, E'.ord (Units.map (functionFieldMap f).toMonoidHom g) = E.ord g) → ∀ η : RatForms p n, η ≠ 0 → (fun ω => @dite ℤ (∃ a, E'.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (GlobalTheory.EtaleKlt.ratPull p f n η) = (fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) η := by
  first | exact @GlobalTheory.EtaleKlt.formOrd_ratPull | exact GlobalTheory.EtaleKlt.formOrd_ratPull | (intros; apply GlobalTheory.EtaleKlt.formOrd_ratPull <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeDivisorLiftAlongEtaleMap

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.EtaleKlt

theorem divOver_lift : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] [IsLocallyNoetherian M] [IsLocallyNoetherian W] (p : W ⟶ Sp ℂ) (f : M ⟶ W) [IsDominant f] (n : ℕ) [SmoothOfRelativeDimension n p] [SmoothOfRelativeDimension n (f ≫ p)] (U : M.Opens), Etale (U.ι ≫ f) → ∀ y ∈ U, ∀ E : DivOver p, E.Through (f y) → ∃ E' : DivOver (f ≫ p), E'.Through y ∧ (∀ g : W.functionFieldˣ, E'.ord (Units.map (functionFieldMap f).toMonoidHom g) = E.ord g) ∧ ∀ η : RatForms p n, η ≠ 0 → (fun ω => @dite ℤ (∃ a, E'.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (GlobalTheory.EtaleKlt.ratPull p f n η) = (fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) η := by
  intro M W _ _ _ _ p f _ n _ _ U hU y hy E hE
  obtain ⟨hfl, hfe, hft⟩ := GlobalTheory.T.stalkMap_flat_formallyEtale_essFiniteType_of_etale_open M W f U hU y hy
  obtain ⟨V', h, hdvr, hS, hcomap, het, hess⟩ := GlobalTheory.T.exists_dvr_extension_of_essentially_etale_local (K := W.functionField)
    (K' := M.functionField) (R := W.presheaf.stalk (f y)) (S := M.presheaf.stalk y)
    (functionFieldMap f) (f.stalkMap y).hom hfl hfe hft
    (RingHom.ext fun a => functionFieldMap_algebraMap f y a) E.ring E.dvr (fun a => hE _ ⟨a, rfl⟩)
  have hc : ∀ a, Cartier.constFn (f ≫ p) a ∈ V' := fun a => by
    rw [← functionFieldMap_comp_constFn p f]
    exact h _ (E.const_mem a)
  have hess' : ((Cartier.constFn (f ≫ p)).codRestrict V' hc).EssFiniteType := by
    have e : (Cartier.constFn (f ≫ p)).codRestrict V' hc =
        ((functionFieldMap f).restrict E.ring V' h).comp E.const := by
      ext a
      simp [DivOver.const, ← functionFieldMap_comp_constFn p f]
    rw [e]
    exact E.essFiniteType.comp hess
  let E' : DivOver (f ≫ p) := ⟨V', hc, hdvr, hess'⟩
  haveI := SmoothOfRelativeDimension.smooth n p
  have hdim := GlobalTheory.NadelApp.topologicalKrullDim_eq_of_smooth W p n
  have hord := GlobalTheory.T.ordFrac_functionFieldMap_of_essentiallyEtale M W p f E E' h hcomap het hess
  refine ⟨E', fun g hg => ?_, hord, fun η hη => GlobalTheory.T.topFormOrder_rationalPullback_of_essentiallyEtale M W p f n hdim E E' h het hord η hη⟩
  obtain ⟨a, rfl⟩ := hg
  exact hS a

end GlobalTheory.EtaleKlt
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeDivisorLiftAlongEtaleMapStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy

theorem _root_.GlobalTheory.T.primeDivisor_lift_along_etale_map : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] [IsLocallyNoetherian M] [IsLocallyNoetherian W] (p : W ⟶ Sp ℂ) (f : M ⟶ W) [IsDominant f] (n : ℕ) [SmoothOfRelativeDimension n p] [SmoothOfRelativeDimension n (f ≫ p)] (U : M.Opens), Etale (U.ι ≫ f) → ∀ y ∈ U, ∀ E : DivOver p, E.Through (f y) → ∃ E' : DivOver (f ≫ p), E'.Through y ∧ (∀ g : W.functionFieldˣ, E'.ord (Units.map (functionFieldMap f).toMonoidHom g) = E.ord g) ∧ ∀ η : RatForms p n, η ≠ 0 → (fun ω => @dite ℤ (∃ a, E'.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (GlobalTheory.EtaleKlt.ratPull p f n η) = (fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) η := by
  first | exact @GlobalTheory.EtaleKlt.divOver_lift | exact GlobalTheory.EtaleKlt.divOver_lift | (intros; apply GlobalTheory.EtaleKlt.divOver_lift <;> assumption)
end
end
