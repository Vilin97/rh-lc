module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldMapCompConstFn
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrComapFiniteIndexEssFiniteTypeComplexStatement
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpecializesDominatesStalkOfRegular
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
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalFunctionFieldOfEtaleOnOpenStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogOrdFracComapFormallyUnramifiedDvrStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NadelVanishingCanonicalAddBoundary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceDvrFormallyUnramifiedOfEtaleStatement
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpecializesDominatesStalkOfRegularStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy

theorem _root_.GlobalTheory.T.exists_specializes_dominatesStalk_of_regular : ∀ (X : Scheme.{0}) [IsIntegral X] (V : ValuationSubring X.functionField) (y : X), (∀ g, RegAt y g → g ∈ V) → ∃ z, z ⤳ y ∧ DominatesStalk V z := by
  first | exact @GlobalTheory.exists_specializes_dominatesStalk_of_regAt | exact GlobalTheory.exists_specializes_dominatesStalk_of_regAt | (intros; apply GlobalTheory.exists_specializes_dominatesStalk_of_regAt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFreeGeneratorTopFormsOfFormallyUnramified

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy

namespace GlobalTheory.TopForm

theorem isFreeGen_formMap_of_formallyUnramified :
    ∀ {k A B : Type} [CommRing k] [CommRing A] [CommRing B] (α : k →+* A) (β : k →+* B) (ψ : A →+* B) (h : ψ.comp α = β) (n : ℕ), (letI := ψ.toAlgebra; Algebra.FormallyUnramified A B) → ∀ ω : Forms α n, IsFreeGen A ω → (∃ ω' : Forms β n, IsFreeGen B ω') → IsFreeGen B (TopForm.formMap n ψ h ω) := by
  intro k A B _ _ _ α β ψ h n hU ω hω hex
  obtain ⟨ω', hω'⟩ := hex
  letI := α.toAlgebra
  letI := β.toAlgebra
  letI := ψ.toAlgebra
  haveI : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq' h.symm
  haveI : Algebra.FormallyUnramified A B := hU
  have hspan : Submodule.span B (Set.range fun a : A => KaehlerDifferential.D k B (ψ a)) = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    obtain ⟨y, rfl⟩ :=
      (KaehlerDifferential.exact_mapBaseChange_map k A B x).mp (Subsingleton.elim _ _)
    induction y with
    | add _ _ h1 h2 => simpa only [map_add] using add_mem h1 h2
    | tmul b m =>
      rw [KaehlerDifferential.mapBaseChange_tmul]
      refine Submodule.smul_mem _ b ?_
      have hm : m ∈ Submodule.span A (Set.range (KaehlerDifferential.D k A)) := by
        rw [KaehlerDifferential.span_range_derivation]; trivial
      induction hm using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨a, rfl⟩ := hx
        rw [KaehlerDifferential.map_D]
        exact Submodule.subset_span ⟨a, rfl⟩
      | zero => simp
      | add _ _ _ _ h1 h2 => simpa only [map_add] using add_mem h1 h2
      | smul a x _ hx =>
        rw [map_smul, ← algebraMap_smul B a]
        exact Submodule.smul_mem _ _ hx
  have hgen : Submodule.span B {formMap n ψ h ω} = ⊤ := by
    rw [eq_top_iff, ← exteriorPower.ιMulti_span_of_span B n (Omega β) hspan, Submodule.span_le]
    rintro _ ⟨w, hw, rfl⟩
    choose v hv using fun i => hw (Set.mem_range_self i)
    have e : exteriorPower.ιMulti B n w = formMap n ψ h (dForm α v) := by
      rw [formMap_dForm, dForm_eq]
      congr 1
      funext i
      exact (hv i).symm
    rw [SetLike.mem_coe, e, ← hω.repr_smul (dForm α v), map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  have hmem : ω' ∈ Submodule.span B {formMap n ψ h ω} := hgen ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  have hb := hω'.repr_smul (formMap n ψ h ω)
  rw [← hb] at hc ⊢
  refine hω'.smul_iff.mpr (IsUnit.of_mul_eq_one c ?_)
  refine hω'.1 ?_
  simp only [mul_comm _ c, mul_smul, one_smul]
  exact hc

end GlobalTheory.TopForm
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFreeGeneratorTopFormsOfFormallyUnramifiedStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy

theorem _root_.GlobalTheory.T.isFreeGenerator_topForms_of_formallyUnramified : ∀ {k A B : Type} [CommRing k] [CommRing A] [CommRing B] (α : k →+* A) (β : k →+* B) (ψ : A →+* B) (h : ψ.comp α = β) (n : ℕ), (letI := ψ.toAlgebra; Algebra.FormallyUnramified A B) → ∀ ω : Forms α n, IsFreeGen A ω → (∃ ω' : Forms β n, IsFreeGen B ω') → IsFreeGen B (TopForm.formMap n ψ h ω) := by
  first | exact @GlobalTheory.TopForm.isFreeGen_formMap_of_formallyUnramified | exact GlobalTheory.TopForm.isFreeGen_formMap_of_formallyUnramified | (intros; apply GlobalTheory.TopForm.isFreeGen_formMap_of_formallyUnramified <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeDivisorOverRestrictEtale

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.EtaleKlt

theorem divOver_restrict : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] [IsLocallyNoetherian M] [IsLocallyNoetherian W] (p : W ⟶ Sp ℂ) (f : M ⟶ W) [IsDominant f] (n : ℕ) [SmoothOfRelativeDimension n p] [SmoothOfRelativeDimension n (f ≫ p)] (U : M.Opens), Etale (U.ι ≫ f) → ∀ y ∈ U, ∀ E' : DivOver (f ≫ p), E'.Through y → ∃ E : DivOver p, E.Through (f y) ∧ (∀ g : W.functionFieldˣ, E'.ord (Units.map (functionFieldMap f).toMonoidHom g) = E.ord g) ∧ ∀ η : RatForms p n, η ≠ 0 → (fun ω => @dite ℤ (∃ a, E'.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (GlobalTheory.EtaleKlt.ratPull p f n η) = (fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) η := by
  intro M W _ _ _ _ p f _ n _ _ U hf y hy E' hE'
  have e := functionFieldMap_comp_constFn p f
  have hc : ∀ a, functionFieldMap f (Cartier.constFn p a) ∈ E'.ring := fun a => by
    rw [← RingHom.comp_apply, e]; exact E'.const_mem a
  obtain ⟨z, hzy, hz⟩ := GlobalTheory.T.exists_specializes_dominatesStalk_of_regular M E'.ring y hE'
  have hzU : z ∈ U := hzy.mem_open U.isOpen hy
  have hfin := GlobalTheory.T.finiteDimensional_functionField_of_etale_on_open' M W f U hf ⟨y, hy⟩
  have hess' : ((functionFieldMap f).comp (Cartier.constFn p)).codRestrict E'.ring hc =
      (Cartier.constFn (f ≫ p)).codRestrict E'.ring E'.const_mem :=
    RingHom.ext fun a => Subtype.ext (RingHom.congr_fun e a)
  obtain ⟨hdvr, hess⟩ := GlobalTheory.T.dvr_comap_finiteIndex_essFiniteType_complex W.functionField M.functionField (functionFieldMap f)
    (Cartier.constFn p) hfin E'.ring hc (hess' ▸ E'.essFiniteType)
  let E : DivOver p := ⟨E'.ring.comap (functionFieldMap f), hc, hdvr, hess⟩
  haveI : IsDiscreteValuationRing (E'.ring.comap (functionFieldMap f)) := hdvr
  have hun := GlobalTheory.T.etale_restrict_dvr_comap_dominatesStalk M W f U hf z hzU E'.ring hz
  let ψ : E.ring →+* E'.ring := (functionFieldMap f).restrict E.ring E'.ring fun _ hx => hx
  letI := ψ.toAlgebra
  have hψ : ψ.comp E.const = E'.const := RingHom.ext fun a => Subtype.ext (RingHom.congr_fun e a)
  have hft : Algebra.EssFiniteType E.ring E'.ring := by
    have h1 : (ψ.comp E.const).EssFiniteType := hψ ▸ E'.essFiniteType
    exact RingHom.EssFiniteType.of_comp E.const h1
  have hord : ∀ g : W.functionFieldˣ,
      E'.ord (Units.map (functionFieldMap f).toMonoidHom g) = E.ord g := fun g =>
    GlobalTheory.T.log_ordFrac_comap_formallyUnramified_dvr W.functionField M.functionField (functionFieldMap f) E'.ring ⟨hun, hft⟩ g g.ne_zero
  refine ⟨E, fun g ⟨a, ha⟩ => ?_, hord, fun η hη => ?_⟩
  · show functionFieldMap f g ∈ E'.ring
    exact hE' _ ⟨f.stalkMap y a, by rw [← functionFieldMap_algebraMap, ha]⟩
  · haveI := SmoothOfRelativeDimension.smooth n p
    haveI := SmoothOfRelativeDimension.smooth n (f ≫ p)
    have hnW : topologicalKrullDim W = n := NadelApp.topologicalKrullDim_eq_of_smooth W p n
    have hnM : topologicalKrullDim M = n := NadelApp.topologicalKrullDim_eq_of_smooth M (f ≫ p) n
    obtain ⟨ω, hω, g, rfl, hg⟩ := E.isFormOrd_formOrd hnW hη
    have hω' := GlobalTheory.T.isFreeGenerator_topForms_of_formallyUnramified E.const E'.const ψ hψ n hun ω hω (E'.exists_isFreeGen hnM)
    have key : ratPull p f n (E.toRat n ω) = E'.toRat n (TopForm.formMap n ψ hψ ω) := by
      have h1 := formMap_formMap (D := n) E.ring.subtype (functionFieldMap f)
        ((functionFieldMap f).comp E.ring.subtype) rfl rfl e
        (by rw [RingHom.comp_assoc]; exact e) ω
      have h2 := formMap_formMap (D := n) ψ E'.ring.subtype
        ((functionFieldMap f).comp E.ring.subtype) rfl hψ rfl
        (by rw [RingHom.comp_assoc]; exact e) ω
      exact h1.trans h2.symm
    have hpull : ratPull p f n ((g : W.functionField) • E.toRat n ω) =
        ((Units.map (functionFieldMap f).toMonoidHom g : M.functionFieldˣ) : M.functionField) •
          E'.toRat n (TopForm.formMap n ψ hψ ω) := by
      rw [map_smulₛₗ, key]; rfl
    have hne : ratPull p f n ((g : W.functionField) • E.toRat n ω) ≠ 0 := by
      rw [hpull]
      refine smul_ne_zero (Units.ne_zero _) fun h0 => ?_
      have := (E'.isFreeGen_toRat hω').1 (a₁ := 0) (a₂ := 1) (by simp [h0])
      exact zero_ne_one this
    change E'.formOrd (ratPull p f n ((g : W.functionField) • E.toRat n ω)) =
      E.formOrd ((g : W.functionField) • E.toRat n ω)
    rw [← hg, ← hord g]
    exact DivOver.IsFormOrd.formOrd_eq hne ⟨_, hω', _, hpull, rfl⟩

end GlobalTheory.EtaleKlt
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeDivisorOverRestrictEtaleStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy

theorem _root_.GlobalTheory.T.primeDivisorOver_restrict_etale : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] [IsLocallyNoetherian M] [IsLocallyNoetherian W] (p : W ⟶ Sp ℂ) (f : M ⟶ W) [IsDominant f] (n : ℕ) [SmoothOfRelativeDimension n p] [SmoothOfRelativeDimension n (f ≫ p)] (U : M.Opens), Etale (U.ι ≫ f) → ∀ y ∈ U, ∀ E' : DivOver (f ≫ p), E'.Through y → ∃ E : DivOver p, E.Through (f y) ∧ (∀ g : W.functionFieldˣ, E'.ord (Units.map (functionFieldMap f).toMonoidHom g) = E.ord g) ∧ ∀ η : RatForms p n, η ≠ 0 → (fun ω => @dite ℤ (∃ a, E'.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (GlobalTheory.EtaleKlt.ratPull p f n η) = (fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) η := by
  first | exact @GlobalTheory.EtaleKlt.divOver_restrict | exact GlobalTheory.EtaleKlt.divOver_restrict | (intros; apply GlobalTheory.EtaleKlt.divOver_restrict <;> assumption)
end
end
