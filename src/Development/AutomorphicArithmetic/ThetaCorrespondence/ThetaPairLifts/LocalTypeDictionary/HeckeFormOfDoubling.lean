module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingEulerProductFarRightStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingSphericalFactorizationOfWeilDualPairStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeFormOfDoubling
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.FlatZetaIntegral
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledLatticeHeightFunPropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatFamilyZetaConvergenceHolomorphyStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HolomorphicContinuationValueEqDivMulStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PartialNormalizingFactorProductAnalyticNeZeroStatement
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
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SphericalParameterBoundNonsplitPlacesStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SphericalParameterBoundSplitPlaceStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedDoublingIntegralInertAdelicStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedDoublingIntegralSplitPlaceAdelicStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnramifiedDoublingIntegralInertPlaceStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GlobalDoublingZetaFormSelfDualLatticeTransfer
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GlobalFormOfSiegelWeil
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SiegelWeilFock
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelWeilFockDoubledPairOfWeilAndIchino
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.GlobalFormFrameLattice

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeInnerProductFormulaOfDoublingEuler

section

@[expose] public section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.IP

theorem heckeForm_of_global_euler : ∀ D : D7, GlobalForm D → EulerRight D → HeckeForm D := by
  intro D hG hE ψ θ A B χA χB sA sB t cA a om ν 𝓕 hP hw LA LB Sf Φ₁ Φ₂ hF₁ hF₂ hU m mH hm hmH u₁ hu₁ u₂ hu₂ par hpar
    hsph hs
  obtain ⟨s₁, hs₁, hint⟩ := hs
  obtain ⟨hUp₁, hUp₂, hZint, z, hz, hpet⟩ :=
    hG A LA hU.sdA ψ θ B χA χB sA sB t cA a om ν 𝓕 hP hw m mH hm hmH Φ₁ Φ₂ hF₁ hF₂ u₁ hu₁ u₂ hu₂
  obtain ⟨hA1, ht1, hB, -⟩ := hP.setting
  have hs0 : sZero A B = (t : ℂ) / 2 := by
    simp only [sZero, hB]; push_cast; ring
  have hs0re : (sZero A B).re = (t : ℝ) / 2 := by rw [hs0]; simp
  obtain ⟨hcont, hbd, -⟩ := GlobalTheory.T.doubledLatticeHeightFun_properties D A LA a hU.sdA hP.maj
  have hflat : ∀ s, integrand om m ν 𝓕 LA a Φ₁ Φ₂ u₁ u₂ s =
      GlobalTheory.IndefiniteRowSideFullHecke.FlatZetaIntegral.flatIntegrand (fun g => wcoef om ν 𝓕 Φ₁ Φ₂ g * rcoef m u₁ u₂ g)
        (fun g => (hgtL A LA a g : ℝ)) (sZero A B) s := by
    intro s; funext g
    simp only [integrand, GlobalTheory.IndefiniteRowSideFullHecke.FlatZetaIntegral.flatIntegrand, npow]; ring
  have hmeas : Measurable (fun g => (hgtL A LA a g : ℝ)) := (NNReal.continuous_coe.comp hcont).measurable
  have hfz := GlobalTheory.T.flatFamilyZeta_convergence_holomorphy (GA D A) (m.restrict (openOff A LA Sf)) (fun g => wcoef om ν 𝓕 Φ₁ Φ₂ g * rcoef m u₁ u₂ g)
    (fun g => (hgtL A LA a g : ℝ)) (sZero A B) (s₁ : ℂ) hmeas (fun g => by exact_mod_cast (hbd g).1)
    (fun g => by exact_mod_cast (hbd g).2) (by rw [← hflat]; exact hint)
  have hint0 : IntegrableOn (fun g => wcoef om ν 𝓕 Φ₁ Φ₂ g * rcoef m u₁ u₂ g) (openOff A LA Sf) m := by
    have := hfz.1.1 (sZero A B) (by simp only [Set.mem_setOf_eq, Complex.ofReal_re, hs0re]; linarith)
    rwa [GlobalTheory.IndefiniteRowSideFullHecke.FlatZetaIntegral.flatIntegrand_self] at this
  refine ⟨hUp₁, hUp₂, hint0, fun l hl => ?_⟩
  have hd := GlobalTheory.T.partialNormalizingFactorProduct_analytic_ne_zero D (Sf : Set (FinPl D)) A.rank B.rank
  have hER : EqRight (fun s => ∫ g, integrand om m ν 𝓕 LA a Φ₁ Φ₂ u₁ u₂ s g ∂m)
      (fun s => LFun.LSD D Sf par χB (s + 1 / 2) / LFun.dSfun D.host.E (Sf : Set (FinPl D)) A.rank B.rank s *
        ∫ g in openOff A LA Sf, integrand om m ν 𝓕 LA a Φ₁ Φ₂ u₁ u₂ s g ∂m) := by
    refine ⟨(A.rank : ℝ) + 1, fun s hs => ?_⟩
    have hs' : (A.rank : ℝ) + 1 < s.re := hs
    refine hE ψ θ A B χA χB sA sB t cA a om ν 𝓕 hP LA LB Sf Φ₁ Φ₂ hF₁.1 hF₂.1 hU m hm u₁ hu₁ u₂ hu₂ par hpar hsph s hs'
      (hZint s ?_)
    have : (0 : ℝ) ≤ A.rank := Nat.cast_nonneg _
    linarith
  have hY : DifferentiableOn ℂ (fun s => ∫ g in openOff A LA Sf, integrand om m ν 𝓕 LA a Φ₁ Φ₂ u₁ u₂ s g ∂m)
      (rightOf s₁) := by
    have h2 := hfz.2.1
    simp only [Complex.ofReal_re] at h2
    refine h2.congr fun s _ => ?_
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.FlatZetaIntegral.flatZeta, hflat]
  have hL : HolValueAt (fun s => LFun.LSD D Sf par χB (s + 1 / 2)) (sZero A B) l := by rw [hs0]; exact hl
  have hmain := GlobalTheory.T.holomorphicContinuationValue_eq_div_mul _ _ _ _ (sZero A B) z l s₁ (by rw [hs0re]; positivity) (by rw [hs0re]; exact hs₁)
    hd.1 (fun s hs => (hd.2 s hs).1) hY hER hz hL
  rw [hpet, hmain, ← hs0]
  simp only [integrand_sZero]
  ring

end GlobalTheory.Core.Rk.IP
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeInnerProductFormulaOfDoublingEulerStatement

section

@[expose] public section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP


theorem _root_.GlobalTheory.T.heckeInnerProductFormula_of_doublingEuler : ∀ D : D7, GlobalForm D → EulerRight D → HeckeForm D := by
  first | exact @GlobalTheory.Core.Rk.IP.heckeForm_of_global_euler | exact GlobalTheory.Core.Rk.IP.heckeForm_of_global_euler | (intros; apply GlobalTheory.Core.Rk.IP.heckeForm_of_global_euler <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GlobalDoublingZetaFormSelfDualLatticeTransferStatement

section

@[expose] public section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP


theorem _root_.GlobalTheory.T.global_doubling_zeta_form_selfDual_lattice_transfer : ∀ (D : D7) (A : HSp D) (L L' : Lat A), IsSelfDualC A L → IsSelfDualC A L' → GlobalFormAt A L → GlobalFormAt A L' := by
  first | exact @GlobalTheory.Core.Rk.GlobMove.globalFormAt_move | exact GlobalTheory.Core.Rk.GlobMove.globalFormAt_move | (intros; apply GlobalTheory.Core.Rk.GlobMove.globalFormAt_move <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelWeilFockDoubledPairOfWeilAndIchinoStatement

section

@[expose] public section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP


theorem _root_.GlobalTheory.T.siegelWeil_fockDoubledPair_of_weil_and_ichino : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent → ∀ D : D7, SiegelWeilFock D := by
  first | exact @GlobalTheory.Core.Rk.IP.siegelWeilAll_of_hypotheses | exact GlobalTheory.Core.Rk.IP.siegelWeilAll_of_hypotheses | (intros; apply GlobalTheory.Core.Rk.IP.siegelWeilAll_of_hypotheses <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.GlobalFormOfSiegelWeil

section

@[expose] public section

section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP
namespace GlobalTheory.Core.Rk.IP
theorem globalForm_of_siegelWeil' : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.CuspRapidDecay →
    GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals →
    ∀ D : D7, GlobalForm D := by
  intro hW hC hWS hSW hDM D A L hL
  have hsw := GlobalTheory.T.siegelWeil_fockDoubledPair_of_weil_and_ichino hW hWS hSW D
  have h0 := _root_.GlobalTheory.T.globalFormAt_frameLat_of_siegelWeil hW hC hDM D hsw A
  exact GlobalTheory.T.global_doubling_zeta_form_selfDual_lattice_transfer D A (frameLat A) L (frameLat_isSelfDualC A) hL h0
end GlobalTheory.Core.Rk.IP
end

section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

theorem _root_.GlobalTheory.T.globalForm_of_siegel_weil : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → ∀ D : D7, GlobalForm D := by
  first | exact @_root_.GlobalTheory.Core.Rk.IP.globalForm_of_siegelWeil' | exact _root_.GlobalTheory.Core.Rk.IP.globalForm_of_siegelWeil' | (intros; apply _root_.GlobalTheory.Core.Rk.IP.globalForm_of_siegelWeil' <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.HeckeFormOfDoubling

section

@[expose] public section

section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP
namespace GlobalTheory.Core.Rk.IP
theorem heckeForm_of_doubling' : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.CuspRapidDecay →
    GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals →
    GlobalTheory.Published.UnramifiedDoublingGL → ∀ D : D7, HeckeForm D := by
  intro p1 p2 p3 p4 p5 p6 D
  have hU := GlobalTheory.T.unramifiedDoublingIntegral_inert_place
  have hG : GlobalForm D := _root_.GlobalTheory.T.globalForm_of_siegel_weil p1 p2 p3 p4 p5 D
  have hPB := paramBoundOn_all_of_split_inert D (GlobalTheory.T.sphericalParameterBound_split_place D) (GlobalTheory.T.sphericalParameterBound_nonsplit_places hU D)
  have hLZ := localZetaOn_all_of_split_inert D (GlobalTheory.T.unramifiedDoublingIntegral_splitPlace_adelic p6 D) (GlobalTheory.T.unramified_doubling_integral_inert_adelic hU D (GlobalTheory.T.sphericalParameterBound_nonsplit_places hU D))
  have hE : EulerRight D := GlobalTheory.T.doubling_eulerProduct_farRight p2 D (GlobalTheory.T.doublingSphericalFactorization_of_weilDualPair p1 D) hLZ hPB
  exact GlobalTheory.T.heckeInnerProductFormula_of_doublingEuler D hG hE
end GlobalTheory.Core.Rk.IP
end

section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

theorem _root_.GlobalTheory.T.heckeForm_of_doubling : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → GlobalTheory.Published.UnramifiedDoublingGL → ∀ D : D7, HeckeForm D := by
  first | exact @_root_.GlobalTheory.Core.Rk.IP.heckeForm_of_doubling' | exact _root_.GlobalTheory.Core.Rk.IP.heckeForm_of_doubling' | (intros; apply _root_.GlobalTheory.Core.Rk.IP.heckeForm_of_doubling' <;> assumption)
end
end
end
