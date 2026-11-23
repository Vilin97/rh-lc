module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaTranslateRangeGap
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodFormReadingEqGoodModelVectorEvaluationStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComplexFormsBaseLevelLeSpanIntegral
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProjectedLiftUnipotentTypeBaseLevelFormStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProjectedThetaLiftExtremalVectorEqClassSum
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemBlockTriangularTwoBlockSizesOfLe

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComplexFormsBaseLevelLeSpanIntegralStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.complex_forms_base_level_le_span_integral : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool),
    ∀ F ∈ (Y.Z.ρ.B i j b).formsC (Y.Z.ρ.tw i b 0 ∅ 1),
      F ∈ Submodule.span ℂ (Y.Z.ρ.mt i j b 0 ∅ 1 : Set (Bridge.Gf (Vc D j) → PolF D (Wc D j).rank (Vc D j).rank)) := by
  first | exact @GlobalTheory.BaseSpan.formsC_le_span_mt | exact GlobalTheory.BaseSpan.formsC_le_span_mt | (intros; apply GlobalTheory.BaseSpan.formsC_le_span_mt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProjectedThetaLiftExtremalVectorEqClassSumStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.projectedThetaLift_extremalVector_eq_classSum : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (t : X.T),
    X.R.xi t = (Y.Z.ρ.B i j b).de.chi → X.R.Q t = (Y.Z.ρ.B i j b).de.Q → ∀ y : (X.R.HV j t).H,
    (∀ (h : Bridge.Gf (Vc D j)) (k : (Y.Z.ρ.B i j b).levJ (Y.Z.ρ.tw i b 0 ∅ 1)),
        (X.R.HV j t).e y (h * (k : Bridge.Gf (Vc D j))) = (((Y.Z.ρ.B i j b).levLam (Y.Z.ρ.tw i b 0 ∅ 1) k : ℂˣ) : ℂ) • (X.R.HV j t).e y h) →
    ∃ F ∈ (Y.Z.ρ.B i j b).formsC (Y.Z.ρ.tw i b 0 ∅ 1),
      (X.R.HW j (sg0 D X.A3.A)).e (X.R.thG j t y) (X.geo.v₀ j _) = Y.Z.ρ.sum i j b 0 ∅ 1 F := by
  first | exact @GlobalTheory.LiftClassSum.exists_projected_thetaLift_eq_sum | exact GlobalTheory.LiftClassSum.exists_projected_thetaLift_eq_sum | (intros; apply GlobalTheory.LiftClassSum.exists_projected_thetaLift_eq_sum <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodModelVectorEqClassSumBaseLevel

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TypeClassSum



theorem goodModel_eq_classSum : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), (∀ j t, GlobalTheory.IndefiniteRowSideFullHecke.ThetaTranslateSize.GoodRangeAt X.R.toRealDat j t) →
    ∀ i, BaseTup Y i → ∀ (j : Fin D.R.m) (b : Bool), ∀ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaTranslateSize.goodModel X.R.toRealDat j,
      (∀ (u : G0g D.nd) (hu : u ∈ D.nexp.U) (κ : GA D (Wc D j)),
        Lev.IsLevelLift (Wc D j) (Y.Z.ρ.B i j b).F.βT (Y.Z.ρ.B i j b).G.levT (Y.Z.ρ.eG i j b u) κ → ∀ g,
        (X.R.HW j (sg0 D X.A3.A)).e w (X.geo.v₀ j _) (g * κ) =
          Y.Z.ρ.e i b ((D.nexp.psiU i b ⟨u, hu⟩ : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) *
          (X.R.HW j (sg0 D X.A3.A)).e w (X.geo.v₀ j _) g) →
      ∃ F ∈ Submodule.span ℂ (Y.Z.ρ.mt i j b 0 ∅ 1 : Set (Bridge.Gf (Vc D j) → PolF D (Wc D j).rank (Vc D j).rank)),
        (X.R.HW j (sg0 D X.A3.A)).e w (X.geo.v₀ j _) = Y.Z.ρ.sum i j b 0 ∅ 1 F := by
  intro D X E Y hG i hB j b w hw hty
  obtain ⟨t, hxi, hQ⟩ : ∃ t : X.T, X.R.xi t = (Y.Z.ρ.B i j b).de.chi ∧
      X.R.Q t = (Y.Z.ρ.B i j b).de.Q := hB j b
  obtain ⟨y0, rfl⟩ : w ∈ LinearMap.range (X.R.thG j t) := by
    rw [hG j t]; exact hw
  obtain ⟨y, hlaw, heq⟩ := GlobalTheory.T.projectedLift_unipotentType_baseLevelForm D X E Y i j b t hxi hQ y0 hty
  obtain ⟨F, hF, hsum⟩ := GlobalTheory.T.projectedThetaLift_extremalVector_eq_classSum D X E Y i j b t hxi hQ y hlaw
  exact ⟨F, GlobalTheory.T.complex_forms_base_level_le_span_integral D X E Y i j b F hF, heq.symm.trans hsum⟩

end GlobalTheory.TypeClassSum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodModelVectorEqClassSumBaseLevelStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.goodModelVector_eq_classSum_baseLevel : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), (∀ j t, GlobalTheory.IndefiniteRowSideFullHecke.ThetaTranslateSize.GoodRangeAt X.R.toRealDat j t) →
    ∀ i, BaseTup Y i → ∀ (j : Fin D.R.m) (b : Bool), ∀ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaTranslateSize.goodModel X.R.toRealDat j,
      (∀ (u : G0g D.nd) (hu : u ∈ D.nexp.U) (κ : GA D (Wc D j)),
        Lev.IsLevelLift (Wc D j) (Y.Z.ρ.B i j b).F.βT (Y.Z.ρ.B i j b).G.levT (Y.Z.ρ.eG i j b u) κ → ∀ g,
        (X.R.HW j (sg0 D X.A3.A)).e w (X.geo.v₀ j _) (g * κ) =
          Y.Z.ρ.e i b ((D.nexp.psiU i b ⟨u, hu⟩ : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) *
          (X.R.HW j (sg0 D X.A3.A)).e w (X.geo.v₀ j _) g) →
      ∃ F ∈ Submodule.span ℂ (Y.Z.ρ.mt i j b 0 ∅ 1 : Set (Bridge.Gf (Vc D j) → PolF D (Wc D j).rank (Vc D j).rank)),
        (X.R.HW j (sg0 D X.A3.A)).e w (X.geo.v₀ j _) = Y.Z.ρ.sum i j b 0 ∅ 1 F := by
  first | exact @GlobalTheory.TypeClassSum.goodModel_eq_classSum | exact GlobalTheory.TypeClassSum.goodModel_eq_classSum | (intros; apply GlobalTheory.TypeClassSum.goodModel_eq_classSum <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodTypeFormReadingRightTranslateLift

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar




namespace GlobalTheory.TypeRead

theorem actG_eG (D : D7) (i : D.ntw.Tw) (j : ℕ) (b : Bool) (u : G0g D.nd) (y : D.nexp.Fm i j b) :
    D.nexp.actG i j b u (Formalism.MainNotions.IntegralHeckeForms.eG D.nexp i j b y) = Formalism.MainNotions.IntegralHeckeForms.eG D.nexp i j b (D.nexp.actG i j b u y) := by
  have h := congrArg (fun z => MonoidAlgebra.lift (FractionRing (D.ntw.O i)) (Module.End (FractionRing (D.ntw.O i)) (D.nexp.Fm i j b)) (G0g D.nd)
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (D.nexp.actG i j b)) z y)
    (D.nexp.eAlg_central i b (MonoidAlgebra.single u 1))
  simp only [map_mul, MonoidAlgebra.lift_single, one_smul, Module.End.mul_apply] at h
  exact h.symm

theorem finite_group_acts_on_good_type_form_by_character (D : D7) (i : D.ntw.Tw) (j : ℕ) (b : Bool) (x : D.nexp.Fm i j b) (hx : x ∈ V0 D.nexp i j b)
    (u : G0g D.nd) (hu : u ∈ D.nexp.U) :
    D.nexp.actG i j b u x = ((D.nexp.psiU i b ⟨u, hu⟩ : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) • x := by
  obtain ⟨f, hf, rfl⟩ := hx
  have hf' := (Submodule.mem_iInf _).1 hf ⟨u, hu⟩
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at hf'
  rw [actG_eG]
  change Formalism.MainNotions.IntegralHeckeForms.eG D.nexp i j b ((D.nexp.actG i j b (⟨u, hu⟩ : D.nexp.U) : _ ≃ₗ[_] _) f) = _
  erw [hf']
  simp

end GlobalTheory.TypeRead


open GlobalTheory.TypeRead in
theorem GlobalTheory.TypeRead.rd_mul_lift : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool),
    ∀ x ∈ V0 D.nexp i ((j : ℕ) + 1) b, ∀ (u : G0g D.nd) (hu : u ∈ D.nexp.U) (κ : GA D (Wc D j)),
      Lev.IsLevelLift (Wc D j) (Y.Z.ρ.B i j b).F.βT (Y.Z.ρ.B i j b).G.levT (Y.Z.ρ.eG i j b u) κ → ∀ g,
      Y.Z.rd i j b x (g * κ) = Y.Z.ρ.e i b ((D.nexp.psiU i b ⟨u, hu⟩ : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) *
        Y.Z.rd i j b x g := by
  intro D X E Y i j b x hx u hu κ hκ g
  have hA : ActRead (Y.Z.rd i j b) :=
    actRead_realRd D X.Γ X.Pl0 X.I0 X.T X.A3 X.core.Q.c.F X.R X.cG Y.S Y.YS X.geo.v₀ Y.Z.ρ Y.Z.good i j b _ Y.Z.pin X.unif
      X.char.models.HW
  rw [← hA u κ hκ x g, finite_group_acts_on_good_type_form_by_character D i _ b x hx u hu, map_smulₛₗ]
  rfl
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodTypeFormReadingRightTranslateLiftStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.good_type_form_reading_right_translate_lift : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool),
    ∀ x ∈ V0 D.nexp i ((j : ℕ) + 1) b, ∀ (u : G0g D.nd) (hu : u ∈ D.nexp.U) (κ : GA D (Wc D j)),
      Lev.IsLevelLift (Wc D j) (Y.Z.ρ.B i j b).F.βT (Y.Z.ρ.B i j b).G.levT (Y.Z.ρ.eG i j b u) κ → ∀ g,
      Y.Z.rd i j b x (g * κ) = Y.Z.ρ.e i b ((D.nexp.psiU i b ⟨u, hu⟩ : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) *
        Y.Z.rd i j b x g := by
  first | exact @GlobalTheory.TypeRead.rd_mul_lift | exact GlobalTheory.TypeRead.rd_mul_lift | (intros; apply GlobalTheory.TypeRead.rd_mul_lift <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodFormsClassSumsOfProjectedLiftRange

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section




namespace GlobalTheory.RankOnto

theorem sumOnto_of_goodRange : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), (∀ j t, GlobalTheory.IndefiniteRowSideFullHecke.ThetaTranslateSize.GoodRangeAt X.R.toRealDat j t) → ∀ i, BaseTup Y i → SumOnto Y.Z.rd i := by
  intro D X E Y hG i hB j b x hx
  obtain ⟨w, hw, hrd⟩ := GlobalTheory.T.good_form_reading_eq_good_model_vector_evaluation D X E Y i j b x hx
  have hν : Y.Z.ν i j b ≠ 0 := (Y.Z.scalar i j b).ne
  have hT := GlobalTheory.T.good_type_form_reading_right_translate_lift D X E Y i j b x hx
  have hφ : (X.R.HW j (Formalism.IndefR.Links.sg0 D X.A3.A)).e w (X.geo.v₀ j _) = Y.Z.ν i j b • Y.Z.rd i j b x := by
    rw [hrd, smul_smul, mul_inv_cancel₀ hν, one_smul]
  obtain ⟨F, hF, hsum⟩ := GlobalTheory.T.goodModelVector_eq_classSum_baseLevel D X E Y hG i hB j b w hw (fun u hu κ hκ g => by
    rw [hφ, Pi.smul_apply, Pi.smul_apply, hT u hu κ hκ g, smul_eq_mul, smul_eq_mul]; ring)
  refine ⟨(Y.Z.ν i j b)⁻¹ • F, Submodule.smul_mem _ _ hF, ?_⟩
  rw [map_smul, ← hsum, hrd]

end GlobalTheory.RankOnto
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodFormsClassSumsOfProjectedLiftRangeStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.goodForms_classSums_of_projectedLift_range : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), (∀ j t, GlobalTheory.IndefiniteRowSideFullHecke.ThetaTranslateSize.GoodRangeAt X.R.toRealDat j t) → ∀ i, BaseTup Y i → SumOnto Y.Z.rd i := by
  first | exact @GlobalTheory.RankOnto.sumOnto_of_goodRange | exact GlobalTheory.RankOnto.sumOnto_of_goodRange | (intros; apply GlobalTheory.RankOnto.sumOnto_of_goodRange <;> assumption)
end
end
