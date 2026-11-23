module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter
public import Formalism.SharpRestriction.Divisibility.AbsolutelyIrreducibleSpan
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AuxiliaryPrimeNeTypePrime
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlacesOkOfModEqOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
public import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JointCondOfDefinite
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyCoeffFieldContainsRootOfUnityGroupOrdeStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyHundredLeHermitianRankColumnChoicesStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfOpenCompact
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyDefiniteSpacesStandardAndLarge
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyTwoMulRankLeLevelPrimeStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyAuxiliaryPlacesSplitDistinct

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

namespace GlobalTheory.TwInputs.PlacesAt

theorem evLgG_placesOk : EvLgG fun K B f _ => KPx B f → ∀ (T : TwDat B) (w : ColW B f T) (Z : w.Lt),
    ∃ w0, GlobalTheory.LamTie.PlacesOk (w.D Z).host (AbsolutelyIrreducibleSpan.q0 (w.D Z)) w0 := by
  refine evG_good.imp fun K C5 c6 Cb hG _ => ?_
  refine (GlobalTheory.TwInputs.SmallField.lg_lam K).imp fun B f _ hO _ _ T w Z => ?_
  have hq := GlobalTheory.TwInputs.SmallField.auxiliary_prime_ne_type_prime K C5 c6 Cb hG B.toPre hO
  have hqp := (GlobalTheory.EX.DC.globalTwisting_spec_fact B.toPre.host).1
  obtain ⟨w0, hw0⟩ := GlobalTheory.TwInputs.SmallField.exists_over B.toPre.host.E hqp
  have hmod : ∀ p ∈ [B.toPre.host.g 0, B.toPre.host.g 1, B.toPre.host.pde, B.toPre.host.pde', GlobalTheory.EX.DC.q0H B.toPre.host],
      p ≡ 1 [MOD B.toPre.host.QS * B.toPre.host.q * B.toPre.host.d] := by
    intro p hp
    rw [Nat.ModEq, Nat.mod_eq_of_lt (GlobalTheory.TwInputs.SmallField.one_lt_cond B.toPre)]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    exacts [B.toPre.g_cond 0, B.toPre.g_cond 1, B.toPre.pde_cond.1, B.toPre.pde_cond.2, GlobalTheory.EX.DC.mod_cond _]
  exact ⟨w0, (GlobalTheory.LamTie.placesOk_of_modEq_one B.toPre.R B.toPre.host _ w0 hqp hmod hq
    (GlobalTheory.EX.DC.q0H_ne_pde_and_ne_pde' _).1 (GlobalTheory.EX.DC.q0H_ne_pde_and_ne_pde' _).2 hw0).1⟩

end GlobalTheory.TwInputs.PlacesAt
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyAuxiliaryPlacesSplitDistinctStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

theorem _root_.GlobalTheory.T.eventually_auxiliary_places_split_distinct : EvLgG fun K B f _ => KPx B f → ∀ (T : TwDat B) (w : ColW B f T) (Z : w.Lt), ∃ w0, GlobalTheory.LamTie.PlacesOk (w.D Z).host (AbsolutelyIrreducibleSpan.q0 (w.D Z)) w0 := by
  first | exact @GlobalTheory.TwInputs.PlacesAt.evLgG_placesOk | exact GlobalTheory.TwInputs.PlacesAt.evLgG_placesOk | (intros; apply GlobalTheory.TwInputs.PlacesAt.evLgG_placesOk <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyBaseChangeHypothesesColumnChoices

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

namespace GlobalTheory.Mem.HypCMRec

theorem hypCM_all (D : D7) : SphericalInertData.HypCM D := by
  refine ⟨?_, GlobalTheory.DesignBC.two_le_finrank D, fun w hw h2 => hw (GlobalTheory.DesignBC.isSplitPl_of_two_mem D w h2)⟩
  letI := D.host.cmStar
  exact D.sp.cm.cmUnram

theorem hypCM_at_record : EvLgG fun K B f _ => KPx B f → ∀ (T : TwDat B) (w : ColW B f T) (Z : w.Lt), SphericalInertData.HypCM (w.D Z) :=
  evG_all fun K => lg_all K fun _ _ _ _ _ _ _ _ => hypCM_all _

end GlobalTheory.Mem.HypCMRec

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyBaseChangeHypothesesColumnChoicesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

theorem _root_.GlobalTheory.T.eventually_baseChangeHypotheses_columnChoices : EvLgG fun K B f _ => KPx B f → ∀ (T : TwDat B) (w : ColW B f T) (Z : w.Lt), SphericalInertData.HypCM (w.D Z) := by
  first | exact @GlobalTheory.Mem.HypCMRec.hypCM_at_record | exact GlobalTheory.Mem.HypCMRec.hypCM_at_record | (intros; apply GlobalTheory.Mem.HypCMRec.hypCM_at_record <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyHostEqCompositumTotallyRealImagQuadrat

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

namespace GlobalTheory.Mem.HostEFK

theorem hypEFK_ev : EvLgG fun K B f _ => KPx B f → ∀ (T : TwDat B) (w : ColW B f T) (Z : w.Lt), SphericalInertData.HypEFK (w.D Z) :=
  evG_all fun K => lg_all K fun B f T _ _ T' w Z => GlobalTheory.DesignBC.hypEFK (w.D Z)

end GlobalTheory.Mem.HostEFK
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyHostEqCompositumTotallyRealImagQuadratStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

theorem _root_.GlobalTheory.T.eventually_host_eq_compositum_totallyReal_imagQuadratic : EvLgG fun K B f _ => KPx B f → ∀ (T : TwDat B) (w : ColW B f T) (Z : w.Lt), SphericalInertData.HypEFK (w.D Z) := by
  first | exact @GlobalTheory.Mem.HostEFK.hypEFK_ev | exact GlobalTheory.Mem.HostEFK.hypEFK_ev | (intros; apply GlobalTheory.Mem.HostEFK.hypEFK_ev <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallySpacesVDefiniteColumnChoices

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

namespace GlobalTheory.Mem.DefSpaces

theorem v_isDefinite : EvLgG fun K B f _ => KPx B f → ∀ (T : TwDat B) (w : ColW B f T) (Z : w.Lt), ∀ j, 1 ≤ j → j ≤ (w.D Z).R.m → ((w.D Z).sp.V j).IsDefinite := by
  refine (GlobalTheory.Mem.Top.evG_of_ev GlobalTheory.Mem.StdSize.vstd_size_ev).imp fun K _ _ _ _ hK =>
    GlobalTheory.Mem.Top.GroupRetwisting.lg_all K fun B f _ hO _ T w Z j hj1 hj2 => ?_
  obtain ⟨hV, -⟩ := hK (w.st Z) hO
  have hm : (w.st Z).toD7.R.m = (w.D Z).R.m := rfl
  have hp := GlobalTheory.RepsObj.isPosDef_of_vStd (D := (w.st Z).toD7) ⟨j - 1, by omega⟩ (hV ⟨j - 1, by omega⟩)
  change ((w.st Z).toD7.sp.V j).IsDefinite
  intro τ
  left
  have e : j - 1 + 1 = j := by omega
  have := hp τ
  simp only [Formalism.IndefR.Links.Vc, e] at this
  exact this

end GlobalTheory.Mem.DefSpaces
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallySpacesVDefiniteColumnChoicesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

theorem _root_.GlobalTheory.T.eventually_spacesV_definite_columnChoices : EvLgG fun K B f _ => KPx B f → ∀ (T : TwDat B) (w : ColW B f T) (Z : w.Lt), ∀ j, 1 ≤ j → j ≤ (w.D Z).R.m → ((w.D Z).sp.V j).IsDefinite := by
  first | exact @GlobalTheory.Mem.DefSpaces.v_isDefinite | exact GlobalTheory.Mem.DefSpaces.v_isDefinite | (intros; apply GlobalTheory.Mem.DefSpaces.v_isDefinite <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallySizesCongruencesHostFactsColumnChoices

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

namespace GlobalTheory.HeightCounting.Up

theorem sizes_host_at_record : EvLgG fun K B f _ => KPx B f → ∀ (T : TwDat B) (w : ColW B f T) (Z : w.Lt), 100 ≤ (w.D Z).R.r ∧ (∀ k, 2 * (w.D Z).R.r ≤ (w.D Z).host.g k) ∧ RootsLL (w.D Z) ∧ SphericalInertData.HypEFK (w.D Z) ∧ SphericalInertData.HypCM (w.D Z) ∧ (∀ j, 1 ≤ j → j ≤ (w.D Z).R.m → ((w.D Z).sp.V j).IsDefinite) ∧ ∃ w0, GlobalTheory.LamTie.PlacesOk (w.D Z).host (AbsolutelyIrreducibleSpan.q0 (w.D Z)) w0 := by
  refine EvG.imp (GlobalTheory.T.eventually_hundred_le_hermitianRank_columnChoices.inter (GlobalTheory.T.eventually_two_mul_rank_le_levelPrime.inter (GlobalTheory.T.eventually_coeffField_contains_rootOfUnity_groupOrder.inter (GlobalTheory.T.eventually_host_eq_compositum_totallyReal_imagQuadratic.inter (GlobalTheory.T.eventually_baseChangeHypotheses_columnChoices.inter (GlobalTheory.T.eventually_spacesV_definite_columnChoices.inter GlobalTheory.T.eventually_auxiliary_places_split_distinct)))))) fun K _ _ _ _ H => ?_
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := H
  exact (h1.inter (h2.inter (h3.inter (h4.inter (h5.inter (h6.inter h7)))))).imp fun B f T _ G hk T' w Z =>
    ⟨G.1 hk T' w Z, G.2.1 hk T' w Z, G.2.2.1 hk T' w Z, G.2.2.2.1 hk T' w Z, G.2.2.2.2.1 hk T' w Z, G.2.2.2.2.2.1 hk T' w Z,
      G.2.2.2.2.2.2 hk T' w Z⟩

end GlobalTheory.HeightCounting.Up
end
end
