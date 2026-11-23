module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AtPtsImp
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExportSt
public import Formalism.PieriBlockIdeals.LatticeInclusionRealSettingAlt
public import Formalism.SharpRestriction.Divisibility.JumpSets
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftWeightCombinatorialDataULeUZero
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.SumExpSt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftWeightRhoEntriesLeFloorHeightStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftWeightRhoEntryValuesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftWeightRhoLowsDistanceBoundsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftWeightRhoNonThickPlaceCentreWidthStatement
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AtPtsImp
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AtPtsStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ParOfFurtherStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftWeightRhoBlockConstantCentred

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.ExpTie GlobalTheory.ExpTie.Lift

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ExpTie.Lift

theorem block_centre : ∀ {D : Formalism.BasicNotions.D7} (L : Formalism.BasicNotions.SizeData₂ D) (j : Fin D.R.m) (τ : D.what₂.Tau), GlobalTheory.ExpTie.Lift.ValsAt L j τ → (∀ a, Formalism.CohomologicalDescent.ShortWeightBounds.kc (GlobalTheory.ExpTie.parOf L j) + (GlobalTheory.ExpTie.Lift.wts L j).j τ ≤ a → a < Formalism.CohomologicalDescent.ShortWeightBounds.kc (GlobalTheory.ExpTie.parOf L j) + (GlobalTheory.ExpTie.Lift.wts L j).j τ + (GlobalTheory.ExpTie.parOf L j).t → (GlobalTheory.ExpTie.Lift.wts L j).lam τ a = (GlobalTheory.ExpTie.Lift.wts L j).lam τ (Formalism.CohomologicalDescent.ShortWeightBounds.kc (GlobalTheory.ExpTie.parOf L j) + (GlobalTheory.ExpTie.Lift.wts L j).j τ)) ∧ (((GlobalTheory.ExpTie.Lift.wts L j).bot (GlobalTheory.ExpTie.parOf L j) τ : ℝ) + (((GlobalTheory.ExpTie.parOf L j).t : ℝ) - 1) / 2 - (GlobalTheory.ExpTie.Lift.wts L j).c τ = -(GlobalTheory.ExpTie.Lift.wts L j).e τ) := by
  intro D L j τ hv
  have hk := D.R.m_add_three_le_k
  have ht0 := D.R.t_odd.pos
  have hkc : Formalism.CohomologicalDescent.ShortWeightBounds.kc (parOf L j) + (wts L j).j τ = D.R.k + (j : ℕ) := by
    simp only [Formalism.CohomologicalDescent.ShortWeightBounds.kc, parOf, wts]; omega
  have htt : (parOf L j).t = D.R.t := rfl
  have he : (wts L j).e τ = wj D ((j : ℕ) + 1) τ := rfl
  constructor
  · intro a ha1 ha2
    rw [hkc] at ha1 ⊢
    rw [hkc, htt] at ha2
    obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le ha1
    have h1 := hv.2.2.1 s (by omega)
    have h0 := hv.2.2.1 0 ht0
    simp only [add_zero, Nat.cast_zero, sub_zero] at h0
    have hU : ((wts L j).U (parOf L j) τ (D.R.k + j + s) : ℝ) = (((wts L j).U (parOf L j) τ (D.R.k + j) - s : ℤ) : ℝ) := by
      push_cast; linarith
    have hU' := Int.cast_injective (α := ℝ) hU
    change Formalism.CohomologicalDescent.UnitNormBounds.UN _ _ _ = Formalism.CohomologicalDescent.UnitNormBounds.UN _ _ _ - _ at hU'
    unfold Formalism.CohomologicalDescent.UnitNormBounds.UN at hU'
    push_cast at hU'
    omega
  · have hrow : Formalism.CohomologicalDescent.ShortWeightBounds.kc (parOf L j) + (wts L j).j τ + (parOf L j).t - 1 = D.R.k + (j : ℕ) + (D.R.t - 1) := by
      rw [hkc, htt]; omega
    have h := hv.2.2.1 (D.R.t - 1) (by omega)
    have hts : ((D.R.t - 1 : ℕ) : ℝ) = (D.R.t : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    rw [hts] at h
    rw [Formalism.CohomologicalDescent.ShortWeightBounds.Wts.bot, hrow, htt, he]
    linarith

end GlobalTheory.ExpTie.Lift

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftWeightRhoBlockConstantCentredStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.ExpTie GlobalTheory.ExpTie.Lift

theorem _root_.GlobalTheory.T.liftWeightRho_block_constant_centred : ∀ {D : Formalism.BasicNotions.D7} (L : Formalism.BasicNotions.SizeData₂ D) (j : Fin D.R.m) (τ : D.what₂.Tau), GlobalTheory.ExpTie.Lift.ValsAt L j τ → (∀ a, Formalism.CohomologicalDescent.ShortWeightBounds.kc (GlobalTheory.ExpTie.parOf L j) + (GlobalTheory.ExpTie.Lift.wts L j).j τ ≤ a → a < Formalism.CohomologicalDescent.ShortWeightBounds.kc (GlobalTheory.ExpTie.parOf L j) + (GlobalTheory.ExpTie.Lift.wts L j).j τ + (GlobalTheory.ExpTie.parOf L j).t → (GlobalTheory.ExpTie.Lift.wts L j).lam τ a = (GlobalTheory.ExpTie.Lift.wts L j).lam τ (Formalism.CohomologicalDescent.ShortWeightBounds.kc (GlobalTheory.ExpTie.parOf L j) + (GlobalTheory.ExpTie.Lift.wts L j).j τ)) ∧ (((GlobalTheory.ExpTie.Lift.wts L j).bot (GlobalTheory.ExpTie.parOf L j) τ : ℝ) + (((GlobalTheory.ExpTie.parOf L j).t : ℝ) - 1) / 2 - (GlobalTheory.ExpTie.Lift.wts L j).c τ = -(GlobalTheory.ExpTie.Lift.wts L j).e τ) := by
  first | exact @GlobalTheory.ExpTie.Lift.block_centre | exact GlobalTheory.ExpTie.Lift.block_centre | (intros; apply GlobalTheory.ExpTie.Lift.block_centre <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftWeightRhoThickPlaceCentreWindow

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.ExpTie GlobalTheory.ExpTie.Lift

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ExpTie.Lift

variable {D : D7}

theorem thick_of_mem (L : Formalism.BasicNotions.SizeData₂ D) (j : Fin D.R.m) (τ : D.what₂.Tau) (hv : ValsAt L j τ)
    (hτ : τ ∈ (wts L j).T2) :
    (parOf L j).Thick ((wts L j).e τ) ∧ ((wts L j).xp τ : ℝ) ≤ (parOf L j).h := by
  have hmem : (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces := by
    simpa [wts] using hτ
  have hm2 := D.R.two_le_m
  have hj := j.2
  have h1 := L.win_thick ((j : ℕ) + 1) (by omega) (by omega) τ hmem
  have h2 := L.win_thick D.R.m (by omega) le_rfl τ hmem
  have hc := c_le L j τ hv
  have hb : (parOf L j).b = L.sc.b := rfl
  refine ⟨?_, ?_⟩
  · show (parOf L j).b ≤ wj D ((j : ℕ) + 1) τ ∧ wj D ((j : ℕ) + 1) τ ≤ (parOf L j).b + L.etaSz + 1
    rw [hb]; exact h1
  · have hfl : ((wts L j).xp τ : ℝ) ≤ cT j τ + L.Sc := by
      show ((⌊cT j τ + L.Sc⌋ : ℤ) : ℝ) ≤ cT j τ + L.Sc
      exact Int.floor_le _
    have hc' : cT j τ ≤ wj D D.R.m τ + ((D.R.t : ℝ) - 1) / 2 := hc
    have ht : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
    show ((wts L j).xp τ : ℝ) ≤ (parOf L j).b + L.Sc + L.etaSz + (D.R.t : ℝ) + 1
    rw [hb]
    linarith [h2.2]

end GlobalTheory.ExpTie.Lift

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftWeightRhoThickPlaceCentreWindowStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.ExpTie GlobalTheory.ExpTie.Lift

theorem _root_.GlobalTheory.T.liftWeightRho_thickPlace_centre_window : ∀ {D : Formalism.BasicNotions.D7} (L : Formalism.BasicNotions.SizeData₂ D) (j : Fin D.R.m) (τ : D.what₂.Tau), GlobalTheory.ExpTie.Lift.ValsAt L j τ → τ ∈ (GlobalTheory.ExpTie.Lift.wts L j).T2 → (GlobalTheory.ExpTie.parOf L j).Thick ((GlobalTheory.ExpTie.Lift.wts L j).e τ) ∧ ((GlobalTheory.ExpTie.Lift.wts L j).xp τ : ℝ) ≤ (GlobalTheory.ExpTie.parOf L j).h := by
  first | exact @GlobalTheory.ExpTie.Lift.thick_of_mem | exact GlobalTheory.ExpTie.Lift.thick_of_mem | (intros; apply GlobalTheory.ExpTie.Lift.thick_of_mem <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftWeightRhoWindowContainsCloud

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.ExpTie GlobalTheory.ExpTie.Lift

theorem GlobalTheory.ExpTie.Lift.window_cloud : ∀ {D : Formalism.BasicNotions.D7} (L : Formalism.BasicNotions.SizeData₂ D) (j : Fin D.R.m) (τ : D.what₂.Tau), GlobalTheory.ExpTie.Lift.ValsAt L j τ → ((GlobalTheory.ExpTie.Lift.wts L j).c τ ≤ ((GlobalTheory.ExpTie.Lift.wts L j).xm τ : ℝ) ∧ (GlobalTheory.ExpTie.Lift.wts L j).xm τ ≤ (GlobalTheory.ExpTie.Lift.wts L j).xp τ ∧ ((GlobalTheory.ExpTie.Lift.wts L j).xp τ : ℝ) ≤ (GlobalTheory.ExpTie.Lift.wts L j).c τ + (GlobalTheory.ExpTie.parOf L j).S) ∧ ∀ a, a < Formalism.CohomologicalDescent.ShortWeightBounds.kc (GlobalTheory.ExpTie.parOf L j) → (GlobalTheory.ExpTie.Lift.wts L j).xm τ ≤ (GlobalTheory.ExpTie.Lift.wts L j).U (GlobalTheory.ExpTie.parOf L j) τ a ∧ (GlobalTheory.ExpTie.Lift.wts L j).U (GlobalTheory.ExpTie.parOf L j) τ a ≤ (GlobalTheory.ExpTie.Lift.wts L j).xp τ := by
  intro D L j τ hv
  have hS : (GlobalTheory.ExpTie.parOf L j).S = L.Sc := rfl
  have hkc : Formalism.CohomologicalDescent.ShortWeightBounds.kc (GlobalTheory.ExpTie.parOf L j) = D.R.k - 1 := rfl
  have hxm : (GlobalTheory.ExpTie.Lift.wts L j).xm τ = ⌈(GlobalTheory.ExpTie.Lift.wts L j).c τ⌉ := rfl
  have hxp : (GlobalTheory.ExpTie.Lift.wts L j).xp τ = ⌊(GlobalTheory.ExpTie.Lift.wts L j).c τ + L.Sc⌋ := rfl

  have hrow : ∀ a, a < D.R.k - 1 →
      (GlobalTheory.ExpTie.Lift.wts L j).xm τ ≤ (GlobalTheory.ExpTie.Lift.wts L j).U (GlobalTheory.ExpTie.parOf L j) τ a ∧
        (GlobalTheory.ExpTie.Lift.wts L j).U (GlobalTheory.ExpTie.parOf L j) τ a ≤ (GlobalTheory.ExpTie.Lift.wts L j).xp τ := by
    intro a ha
    have h1 := hv.1 a ha
    have h2 := L.cloud_v τ ⟨a, ha⟩
    have hlo : (GlobalTheory.ExpTie.Lift.wts L j).c τ ≤ ((GlobalTheory.ExpTie.Lift.wts L j).U (GlobalTheory.ExpTie.parOf L j) τ a : ℝ) := by
      have : (0 : ℝ) ≤ (((D.hc τ).v ⟨a, ha⟩ : ℚ) : ℝ) := by exact_mod_cast h2.1
      linarith
    have hhi : ((GlobalTheory.ExpTie.Lift.wts L j).U (GlobalTheory.ExpTie.parOf L j) τ a : ℝ) ≤ (GlobalTheory.ExpTie.Lift.wts L j).c τ + L.Sc := by
      have : (((D.hc τ).v ⟨a, ha⟩ : ℚ) : ℝ) ≤ L.Sc := by exact_mod_cast h2.2
      linarith
    rw [hxm, hxp]
    exact ⟨Int.ceil_le.2 hlo, Int.le_floor.2 hhi⟩
  have hk := D.R.m_add_three_le_k
  have hm2 := D.R.two_le_m
  have h0 := hrow 0 (by omega)
  refine ⟨⟨?_, le_trans h0.1 h0.2, ?_⟩, ?_⟩
  · rw [hxm]; exact Int.le_ceil _
  · rw [hxp, hS]; exact Int.floor_le _
  · intro a ha
    rw [hkc] at ha
    exact hrow a ha
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftWeightRhoWindowContainsCloudStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.ExpTie GlobalTheory.ExpTie.Lift

theorem _root_.GlobalTheory.T.liftWeightRho_window_contains_cloud : ∀ {D : Formalism.BasicNotions.D7} (L : Formalism.BasicNotions.SizeData₂ D) (j : Fin D.R.m) (τ : D.what₂.Tau), GlobalTheory.ExpTie.Lift.ValsAt L j τ → ((GlobalTheory.ExpTie.Lift.wts L j).c τ ≤ ((GlobalTheory.ExpTie.Lift.wts L j).xm τ : ℝ) ∧ (GlobalTheory.ExpTie.Lift.wts L j).xm τ ≤ (GlobalTheory.ExpTie.Lift.wts L j).xp τ ∧ ((GlobalTheory.ExpTie.Lift.wts L j).xp τ : ℝ) ≤ (GlobalTheory.ExpTie.Lift.wts L j).c τ + (GlobalTheory.ExpTie.parOf L j).S) ∧ ∀ a, a < Formalism.CohomologicalDescent.ShortWeightBounds.kc (GlobalTheory.ExpTie.parOf L j) → (GlobalTheory.ExpTie.Lift.wts L j).xm τ ≤ (GlobalTheory.ExpTie.Lift.wts L j).U (GlobalTheory.ExpTie.parOf L j) τ a ∧ (GlobalTheory.ExpTie.Lift.wts L j).U (GlobalTheory.ExpTie.parOf L j) τ a ≤ (GlobalTheory.ExpTie.Lift.wts L j).xp τ := by
  first | exact @GlobalTheory.ExpTie.Lift.window_cloud | exact GlobalTheory.ExpTie.Lift.window_cloud | (intros; apply GlobalTheory.ExpTie.Lift.window_cloud <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WtsOk

section

@[expose] public section



section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie
namespace GlobalTheory.ExpTie.Lift
open Formalism.IndefR.Bridge
theorem wts_ok_alt : _root_.GlobalTheory.BigOn.AtPtsAlt fun Fm x _ i _ => ∀ j : Fin (Fm.D x i).R.m, ∃ W : Formalism.CohomologicalDescent.ShortWeightBounds.Wts (Fm.D x i).what₂.Tau, W.Ok (GlobalTheory.ExpTie.parOf (Fm.L x i) j) ∧
    (∀ τ, ∃ c : ℤ, ∀ a : Fin (Formalism.IndefR.Links.Vc (Fm.D x i) j).rank,
      (W.lam τ a : ℤ) = (Formalism.IndefR.Bridge.lamLdef (D := Fm.D x i) (Formalism.IndefR.Links.Vc (Fm.D x i) j).rank ((j : ℕ) + 1) τ).w a + c) ∧
    (∀ τ a, a < (GlobalTheory.ExpTie.parOf (Fm.L x i) j).Nr → 0 ≤ W.U (GlobalTheory.ExpTie.parOf (Fm.L x i) j) τ a ∧ W.U (GlobalTheory.ExpTie.parOf (Fm.L x i) j) τ a ≤ (Formalism.CohomologicalDescent.ShortWeightBounds.h0 (GlobalTheory.ExpTie.parOf (Fm.L x i) j) : ℤ)) ∧
    W.T2.card ≤ (Fm.D x i).host.T2.card ∧ W.Sp = Formalism.MainNotions.JumpSetsAlt.excSet (Fm.D x i) := by
  refine _root_.GlobalTheory.ExpTie.atPts_mono (_root_.GlobalTheory.ExpTie.atPts_and_alt _root_.GlobalTheory.T.isLamPrime_at_all_points _root_.GlobalTheory.T.parameter_large_at_all_points) ?_
  intro eps Fm x hx i p hp j
  obtain ⟨hF, hLg⟩ := hp
  have hv : ∀ τ, ValsAt (Fm.L x i) j τ := fun τ => GlobalTheory.T.liftWeightRho_entryValues (Fm.L x i) j τ (hF j τ)
  refine ⟨wts (Fm.L x i) j, ⟨anti _ j, what₂ _ j, fun τ => (GlobalTheory.T.liftWeightRho_block_constant_centred (Fm.L x i) j τ (hv τ)).1, fun τ => (GlobalTheory.T.liftWeightRho_block_constant_centred (Fm.L x i) j τ (hv τ)).2,
    fun τ => (GlobalTheory.T.liftWeightRho_window_contains_cloud (Fm.L x i) j τ (hv τ)).1, fun τ => (GlobalTheory.T.liftWeightRho_window_contains_cloud (Fm.L x i) j τ (hv τ)).2,
    fun τ => GlobalTheory.T.liftWeightRho_lows_distance_bounds (Fm.L x i) (Fm.params x hx i) j τ (hv τ), fun τ h => GlobalTheory.T.liftWeightRho_thickPlace_centre_window (Fm.L x i) j τ (hv τ) h,
    fun τ h => GlobalTheory.T.liftWeightRho_nonThickPlace_centre_width (Fm.L x i) (Fm.params x hx i) j τ (hv τ) h⟩, fun τ => ⟨-(lamL j τ).detShift, fun a => ?_⟩,
    fun τ a ha => ⟨U_nonneg _ j τ a ha, GlobalTheory.T.liftWeightRho_entries_le_floor_height (Fm.L x i) (Fm.params x hx i) j τ (hLg j) (hv τ) a ha⟩, T2_card _ j, rfl⟩
  have := lamT_of_lt j τ a a.2
  show (lamT j τ a : ℤ) = _
  rw [this]
  ring
end GlobalTheory.ExpTie.Lift
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WtsOkStatement

section

@[expose] public section



section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie

theorem _root_.GlobalTheory.T.weight_lambda_shift_nonneg' : _root_.GlobalTheory.BigOn.AtPtsAlt fun Fm x _ i _ => ∀ j : Fin (Fm.D x i).R.m, ∃ W : Formalism.CohomologicalDescent.ShortWeightBounds.Wts (Fm.D x i).what₂.Tau, W.Ok (GlobalTheory.ExpTie.parOf (Fm.L x i) j) ∧
    (∀ τ, ∃ c : ℤ, ∀ a : Fin (Formalism.IndefR.Links.Vc (Fm.D x i) j).rank,
      (W.lam τ a : ℤ) = (Formalism.IndefR.Bridge.lamLdef (D := Fm.D x i) (Formalism.IndefR.Links.Vc (Fm.D x i) j).rank ((j : ℕ) + 1) τ).w a + c) ∧
    (∀ τ a, a < (GlobalTheory.ExpTie.parOf (Fm.L x i) j).Nr → 0 ≤ W.U (GlobalTheory.ExpTie.parOf (Fm.L x i) j) τ a ∧ W.U (GlobalTheory.ExpTie.parOf (Fm.L x i) j) τ a ≤ (Formalism.CohomologicalDescent.ShortWeightBounds.h0 (GlobalTheory.ExpTie.parOf (Fm.L x i) j) : ℤ)) ∧
    W.T2.card ≤ (Fm.D x i).host.T2.card ∧ W.Sp = Formalism.MainNotions.JumpSetsAlt.excSet (Fm.D x i) := by
  first | exact @_root_.GlobalTheory.ExpTie.Lift.wts_ok_alt | exact _root_.GlobalTheory.ExpTie.Lift.wts_ok_alt | (intros; apply _root_.GlobalTheory.ExpTie.Lift.wts_ok_alt <;> assumption)
end
end
end
