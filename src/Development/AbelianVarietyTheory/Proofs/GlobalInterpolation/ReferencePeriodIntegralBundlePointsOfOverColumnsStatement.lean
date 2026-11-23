module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AndLeft
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ReferenceChainEvaluationAtBundlePoints
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LowerTieTwAt
public import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
public import Formalism.SharpRestriction.Divisibility.StatementFT.PeriodPointConditions
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdmissiblePeriodZeroOfClassPeriodDecompositionAl
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ClassPairingIntegralFormRowIsIntegralStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsClassSumPairingOfIsFormsOf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStandardColumnComparisonsTrueColumnsStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PropertyAtConstructedPointsOfTrueColumnsViewStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdmissiblePeriodZeroOfClassPeriodDecompositionAlStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Forms

theorem _root_.GlobalTheory.T.admissiblePeriodZero_of_classPeriodDecomposition_all : ∀ D : D7, (∀ u, Formalism.MainNotions.RT.PeriodPointConditions.PerDec0 D u) → Formalism.MainNotions.WeightDegreeSizes.PeriodClassSumWeyl D := by
  first | exact @GlobalTheory.PerRed.periodClassSumWeyl_of_forall_perDec0 | exact GlobalTheory.PerRed.periodClassSumWeyl_of_forall_perDec0 | (intros; apply GlobalTheory.PerRed.periodClassSumWeyl_of_forall_perDec0 <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.VAddNonnegOfInt

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PerDecAtRef


open Formalism.BasicNotions in
theorem vAdd_nonneg_of_int {K : Type} [Field K] [NumberField K] (la : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (a : NumberField.RingOfIntegers K) : 0 ≤ vAdd la (a : K) := by
  have h : la.valuation K (a : K) ≤ 1 := la.valuation_le_one a
  unfold vAdd
  rcases eq_or_ne (la.valuation K (a : K)) 0 with h0 | h0
  · rw [h0, WithZero.log_zero]; simp
  · have h1 : WithZero.log (la.valuation K (a : K)) ≤ 0 := by
      rw [WithZero.log_le_iff_le_exp h0]
      simpa using h
    exact neg_nonneg.mpr h1

end GlobalTheory.PerDecAtRef



theorem GlobalTheory.PerDecAtRef.perDec0At_std : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), GlobalTheory.PerQ.RowInt I l Z → ∀ (u : B.Word) (Ch : ℕ → Type) (chOf : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch i) (F : FormsTiedSym (I.rec7 l Z) u Ch chOf), I.StdF l Z u F → Formalism.MainNotions.RT.PeriodPointConditions.PerDec0At F := by
  intro B X I hI l Z hZ u Ch chOf F hF
  intro x hx G hG c
  classical
  obtain ⟨y0, hy0, hrd⟩ := hZ.ref u G hG c
  have hpr : ∀ w, ((I.perIn u I.mu0).per B.fields.emb B.embLL (l.ch u I.mu0) (l.per u I.mu0) (B.hcW u)).period w
      (((I.rec7 l Z).eMt u).symm G) = (I.perIn u I.mu0).ipP B.fields.emb B.embLL (l.per u I.mu0)
      (F.jM (((I.rec7 l Z).eMt u).symm G)) w := by
    intro w
    have hper := F.per
    unfold Formalism.L2.Forms.PerTie at hper
    exact hper.2.2 w _
  have key := GlobalTheory.T.classPairing_integral_form_row_isIntegral B.fields.emb B.embLL (I.perIn u I.mu0) (l.ch u I.mu0) (l.per u I.mu0) (B.hcW u)
    (l.fmL u I.mu0).famP (((I.rec7 l Z).eMt u).symm G) (F.jM (((I.rec7 l Z).eMt u).symm G)) hpr c y0 ?ha ?hb
  case ha =>
    clear hpr hZ hI hx hG hrd hF
    have hL : (I.perIn u I.mu0).S'.Lsh c.fst ((I.perIn u I.mu0).S'.rep c) = (((I.stX I.mu0).rep c).1.1.deco).1.N :=
      GlobalTheory.PeriodOnStep.Lsh_eq_N _
    rw [hL]
    exact hy0
  case hb =>
    clear hpr hZ hI hx hG hy0 hF
    convert hrd using 2
  obtain ⟨a, ha⟩ := key x hx
  refine ⟨(a : B.fields.K), ?_, ?_⟩
  · have hw := hF.eW
    have hsingle : ∀ (dec : ∀ c' : ((I.rec7 l Z).fm u).clsP, Decidable (c' = c)) (v : ((I.rec7 l Z).mem u).P.Wrow),
        F.valP.eW.symm (fun c' => @ite _ (c' = c) (dec c') (F.valP.eW v c') 0) =
          fun (c' : (I.perIn u I.mu0).S'.Cl) => if c' = c then v c' else 0 := by
      intro dec v
      apply F.valP.eW.injective
      rw [LinearEquiv.apply_symm_apply]
      funext c' s
      erw [hw _ c' s ⟨s.1, s.2⟩ rfl]
      by_cases h : c' = c
      · rw [if_pos h, if_pos (show @Eq (I.perIn u I.mu0).S'.Cl c' c from h)]
        erw [hw v c' s ⟨s.1, s.2⟩ rfl]
      · rw [if_neg h, if_neg (show ¬ @Eq (I.perIn u I.mu0).S'.Cl c' c from h)]
        rfl
    unfold Formalism.MainNotions.RT.PeriodPointConditions.pcL Formalism.MainNotions.RT.PeriodPointConditions.resC
    rw [hsingle, hsingle]
    clear key hpr hrd hy0 hG hZ hI hx hsingle hw hF
    refine ha.trans ?_
    congr! 4
    exact congrArg (fun f => ⇑((I.perIn u I.mu0).ipP B.fields.emb B.embLL (l.per u I.mu0) f))
      (funext fun c' => by by_cases h : c' = c <;> simp [h])
  · intro w
    right
    exact GlobalTheory.PerDecAtRef.vAdd_nonneg_of_int _ a
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PeriodAdmissibleOfIntegralPeriodRows

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.PerAdm0.periodAdmissible_of_integralPeriodRows : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), GlobalTheory.PerQ.RowInt I l Z → Formalism.MainNotions.WeightDegreeSizes.PeriodClassSumWeyl (I.rec7 l Z) := by
  intro B X I hI hP l Z hR
  obtain ⟨C, hC, _⟩ := GlobalTheory.T.exists_standardColumnComparisons_trueColumns I hI hP l Z
  exact GlobalTheory.T.admissiblePeriodZero_of_classPeriodDecomposition_all _ (Formalism.MainNotions.RT.PeriodPointConditions.perDec0_of_cols C
    (fun u => GlobalTheory.PerDecAtRef.perDec0At_std I hI l Z hR u _ _ (C.forms u) (hC u)))
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PeriodAdmissibleOfIntegralPeriodRowsStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.periodClassSumWeyl_of_rowInt : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), GlobalTheory.PerQ.RowInt I l Z → Formalism.MainNotions.WeightDegreeSizes.PeriodClassSumWeyl (I.rec7 l Z) := by
  first | exact @GlobalTheory.PerAdm0.periodAdmissible_of_integralPeriodRows | exact GlobalTheory.PerAdm0.periodAdmissible_of_integralPeriodRows | (intros; apply GlobalTheory.PerAdm0.periodAdmissible_of_integralPeriodRows <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ReferencePeriodIntegralBundlePointsOfOverColumns

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Fc.Cv NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.Fc.PeriodEntriesOverColumns.row_aPer0_of_overCols :
    ∀ (Q : V4.Slot), OverCols Q → ∀ (Bd : BdT) (Lk : LkT Bd), PeriodEntriesOverColumns.PeriodAtZeroAtBundlePoints Q Lk := by
  intro Q hQ Bd Lk
  have h : Row0 Q (EvC fun D _ => Formalism.MainNotions.WeightDegreeSizes.PeriodClassSumWeyl D) :=
    validForConstructedPointClasses_eventuallyWorkingClass (EvP.of_all fun _ K _ β hq =>
      GlobalTheory.T.property_at_constructedPoints_of_trueColumnsView (fun D _ => Formalism.MainNotions.WeightDegreeSizes.PeriodClassSumWeyl D)
        (fun _ _ _ w Z _ _ hv _ _ => GlobalTheory.T.periodClassSumWeyl_of_rowInt w.I w.ok w.pins w.l Z hv.rowInt) K β (hQ _ _ _ _ _ hq))
  exact h.row Lk
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ReferencePeriodIntegralBundlePointsOfOverColumnsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Fc.Cv NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.referencePeriodIntegral_bundlePoints_of_overColumns : ∀ (Q : V4.Slot), OverCols Q → ∀ (Bd : BdT) (Lk : LkT Bd), PeriodEntriesOverColumns.PeriodAtZeroAtBundlePoints Q Lk := by
  first | exact @GlobalTheory.Fc.PeriodEntriesOverColumns.row_aPer0_of_overCols | exact GlobalTheory.Fc.PeriodEntriesOverColumns.row_aPer0_of_overCols | (intros; apply GlobalTheory.Fc.PeriodEntriesOverColumns.row_aPer0_of_overCols <;> assumption)
end
end
