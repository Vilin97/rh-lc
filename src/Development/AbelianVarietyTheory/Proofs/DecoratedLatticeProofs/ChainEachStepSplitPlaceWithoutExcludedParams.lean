module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UpNeNSOfUpNe
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IteratedLiftChains
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsStdIsVacVec
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Formalism.LocalToGlobal.UnitaryNorms.CharTied
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NotIsOfFinOrderHeckeCharacterValueCompletelySpli
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeCharacterOfUnitaryTensorIdeles
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasInfExpIffHasInfQ
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CharacterEquivalenceLocalData
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainCharQuotientLFunctionEntireNeZero
import Mathlib.Algebra.Order.Star.Rat
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftChainHeckeParameterTwistNextTargetChar
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSplitPrimeAvoiding
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPrimePlacesSplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NotIsOfFinOrderHeckeCharacterValueCompletelySpliStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions


theorem _root_.GlobalTheory.T.not_isOfFinOrder_heckeCharacter_value_completelySplitPrime : ∀ (D : D7) (χ : Formalism.L2.Host.HChar D.host.E) (a : D.what₂.Tau → ℚ) (p : ℕ), χ.HasInfQ (Formalism.L2.Host.embTau D) a → (∀ τ, a τ ≠ 0) → GlobalTheory.IndefiniteRowSideFullHecke.IteratedLiftChains.SplitsCompletely D p → ∀ w : HeightOneSpectrum (𝓞 D.host.E), (p : 𝓞 D.host.E) ∈ w.asIdeal → ¬ IsOfFinOrder (χ.val w) := by
  first | exact @GlobalTheory.SplitValuePow.not_isOfFinOrder_val | exact GlobalTheory.SplitValuePow.not_isOfFinOrder_val | (intros; apply GlobalTheory.SplitValuePow.not_isOfFinOrder_val <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeCharValueSplitPrimeNotRootOfUnity

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitValueAdelic

theorem not_isOfFinOrder_val : ∀ (D : D7) (χ : (AE D)ˣ →* Circle), IsHeckeChar D χ → (∀ τ : D.what₂.Tau, ∃ a : ℚ, a ≠ 0 ∧ HasInfExp D χ τ a) → ∀ p : ℕ, GlobalTheory.IndefiniteRowSideFullHecke.IteratedLiftChains.SplitsCompletely D p → ∀ w : HeightOneSpectrum (𝓞 D.host.E), (p : 𝓞 D.host.E) ∈ w.asIdeal → GlobalTheory.LFun.UnrAt χ w → ¬ IsOfFinOrder (GlobalTheory.LFun.val (F := D.host.F) χ w) := by
  intro D χ hχ ha p hp w hw _
  obtain ⟨H, hH⟩ := GlobalTheory.HeckeTensorRead.exists_hchar_chrEq D χ hχ
  choose a ha0 ha using ha
  have h1 := (GlobalTheory.HeckeInfExp.hasInfExp_iff_hasInfQ D χ H a hH).1 ha
  rw [(GlobalTheory.ChrTie.unrAt_iff_and_val_eq D χ H hH w).2]
  exact GlobalTheory.T.not_isOfFinOrder_heckeCharacter_value_completelySplitPrime D H a p h1 ha0 hp w hw

end GlobalTheory.SplitValueAdelic
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeCharValueSplitPrimeNotRootOfUnityStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.heckeChar_value_split_prime_not_root_of_unity : ∀ (D : D7) (χ : (AE D)ˣ →* Circle), IsHeckeChar D χ → (∀ τ : D.what₂.Tau, ∃ a : ℚ, a ≠ 0 ∧ HasInfExp D χ τ a) → ∀ p : ℕ, GlobalTheory.IndefiniteRowSideFullHecke.IteratedLiftChains.SplitsCompletely D p → ∀ w : HeightOneSpectrum (𝓞 D.host.E), (p : 𝓞 D.host.E) ∈ w.asIdeal → GlobalTheory.LFun.UnrAt χ w → ¬ IsOfFinOrder (GlobalTheory.LFun.val (F := D.host.F) χ w) := by
  first | exact @GlobalTheory.SplitValueAdelic.not_isOfFinOrder_val | exact GlobalTheory.SplitValueAdelic.not_isOfFinOrder_val | (intros; apply GlobalTheory.SplitValueAdelic.not_isOfFinOrder_val <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeCharQuotientNeOneCompletelySplitPrime

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto.QuotVal

theorem val_quot_ne_one : ∀ (D : D7) (c : Com D), c.Is → ∀ i j : ℕ, 1 ≤ i → i < j → j ≤ D.R.m → ∀ p : ℕ,
    GlobalTheory.IndefiniteRowSideFullHecke.IteratedLiftChains.SplitsCompletely D p → ∀ w : HeightOneSpectrum (𝓞 D.host.E), (p : 𝓞 D.host.E) ∈ w.asIdeal →
    w.under (𝓞 D.host.F) ∉ c.S → GlobalTheory.LFun.val (F := D.host.F) (c.μ i * (c.μ j)⁻¹) w ≠ 1 := by
  intro D c hc i j hi hij hj p hp w hw hS h1
  obtain ⟨i', rfl⟩ : ∃ i' : ℕ, i = i' + 1 := ⟨i - 1, by omega⟩
  obtain ⟨j', rfl⟩ : ∃ j' : ℕ, j = j' + 1 := ⟨j - 1, by omega⟩
  have hoff : w ∉ GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))) := hS
  refine GlobalTheory.T.heckeChar_value_split_prime_not_root_of_unity D (c.μ (i' + 1) * (c.μ (j' + 1))⁻¹)
    (GlobalTheory.Chain.isHeckeChar_div (QuotL.isHecke hc (by omega) (by omega)) (QuotL.isHecke hc (by omega) hj))
    (fun τ => ⟨_, ?_, GlobalTheory.Chain.hasInfExp_div (hc.exp ⟨i', by omega⟩ τ) (hc.exp ⟨j', by omega⟩ τ)⟩) p hp w hw
    ((hc.unr ⟨i', by omega⟩ w hoff).mul (hc.unr ⟨j', by omega⟩ w hoff).inv) ?_
  · have := QuotL.e_strictMono (D.hc τ) (show (⟨i', by omega⟩ : Fin D.R.m) < ⟨j', by omega⟩ from
      Fin.mk_lt_mk.2 (by omega))
    intro h0
    linarith
  · rw [h1]
    exact IsOfFinOrder.one

end GlobalTheory.ChainOnto.QuotVal

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeCharQuotientNeOneCompletelySplitPrimeStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.heckeCharQuotient_ne_one_completelySplitPrime : ∀ (D : D7) (c : Com D), c.Is → ∀ i j : ℕ, 1 ≤ i → i < j → j ≤ D.R.m → ∀ p : ℕ, GlobalTheory.IndefiniteRowSideFullHecke.IteratedLiftChains.SplitsCompletely D p → ∀ w : HeightOneSpectrum (𝓞 D.host.E), (p : 𝓞 D.host.E) ∈ w.asIdeal → w.under (𝓞 D.host.F) ∉ c.S → GlobalTheory.LFun.val (F := D.host.F) (c.μ i * (c.μ j)⁻¹) w ≠ 1 := by
  first | exact @GlobalTheory.ChainOnto.QuotVal.val_quot_ne_one | exact GlobalTheory.ChainOnto.QuotVal.val_quot_ne_one | (intros; apply GlobalTheory.ChainOnto.QuotVal.val_quot_ne_one <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SmallEntriesAndStringsAvoidExcludedNormPowers

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RkNs

theorem small_entries_and_strings_avoid_excluded : ∀ (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (r t : ℕ), r + 2 ≤ t → ∀ k ∈ ({(t : ℤ) - 1, 1 - (t : ℤ), (t : ℤ) + 1, -((t : ℤ) + 1)} : Set ℤ), (∀ β : ℂ, β ≠ 0 → ‖β‖ ≤ ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ ((r : ℝ) / 2) → ‖β⁻¹‖ ≤ ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ ((r : ℝ) / 2) → β ≠ GlobalTheory.LFun.npow w ((k : ℂ) / 2)) ∧ ∀ x : ℂˣ, ‖(x : ℂ)‖ = 1 → x ≠ 1 → ∀ β ∈ GlobalTheory.LFun.seg w x t, (β : ℂ) ≠ GlobalTheory.LFun.npow w ((k : ℂ) / 2) := by
  intro K _ _ w r t hrt k hk
  have hN : (1 : ℝ) < ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) := by
    exact_mod_cast GlobalTheory.LFun.one_lt_absNorm w
  have hN0 : (0 : ℝ) < ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) := by linarith
  have hkabs : (r : ℤ) < k ∨ k < -(r : ℤ) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk
    rcases hk with h | h | h | h <;> subst h <;> omega
  refine ⟨?_, ?_⟩
  · intro β hβ0 h1 h2 heq
    have hn : ‖β‖ = ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ ((k : ℝ) / 2) := by
      rw [heq, GlobalTheory.LFun.norm_npow]
      congr 1
      simp
    rcases hkabs with hk' | hk'
    · have : ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ ((r : ℝ) / 2) <
          ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ ((k : ℝ) / 2) := by
        apply Real.rpow_lt_rpow_of_exponent_lt hN
        have : (r : ℝ) < (k : ℝ) := by exact_mod_cast hk'
        linarith
      linarith
    · have hinv : ‖β⁻¹‖ = ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ (-((k : ℝ) / 2)) := by
        rw [norm_inv, hn, Real.rpow_neg hN0.le]
      have : ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ ((r : ℝ) / 2) <
          ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ (-((k : ℝ) / 2)) := by
        apply Real.rpow_lt_rpow_of_exponent_lt hN
        have : (k : ℝ) < -(r : ℝ) := by exact_mod_cast hk'
        linarith
      linarith
  · intro x hx1 hxne β hβ heq
    simp only [GlobalTheory.LFun.seg, Multiset.mem_map, Finset.mem_range] at hβ
    obtain ⟨i, -, rfl⟩ := hβ
    set c : ℂ := (k : ℂ) / 2 - (((t : ℂ) - 1) / 2 - (i : ℂ)) with hc
    have hsplit : GlobalTheory.LFun.npow w ((k : ℂ) / 2) =
        GlobalTheory.LFun.npow w (((t : ℂ) - 1) / 2 - (i : ℂ)) * GlobalTheory.LFun.npow w c := by
      rw [← GlobalTheory.LFun.npow_add]
      congr 1
      rw [hc]; ring
    rw [Units.val_mul, GlobalTheory.LFun.coe_npowU, hsplit, mul_comm] at heq
    have hx : (x : ℂ) = GlobalTheory.LFun.npow w c :=
      mul_left_cancel₀ (GlobalTheory.LFun.npow_ne_zero w _) heq
    have him : c.im = 0 := by
      rw [hc]; simp
    have hre : c.re = 0 := by
      have h1 : ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ c.re = 1 := by
        rw [← GlobalTheory.LFun.norm_npow, ← hx, hx1]
      rcases lt_trichotomy c.re 0 with h | h | h
      · have := Real.rpow_lt_one_of_one_lt_of_neg hN h
        linarith
      · exact h
      · have := Real.one_lt_rpow hN h
        linarith
    have hc0 : c = 0 := Complex.ext hre him
    apply hxne
    ext
    rw [hx, hc0, GlobalTheory.LFun.npow, Complex.cpow_zero, Units.val_one]

end GlobalTheory.RkNs
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SmallEntriesAndStringsAvoidExcludedNormPowersStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.small_entries_and_strings_avoid_excluded_norm_powers : ∀ (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (r t : ℕ), r + 2 ≤ t → ∀ k ∈ ({(t : ℤ) - 1, 1 - (t : ℤ), (t : ℤ) + 1, -((t : ℤ) + 1)} : Set ℤ), (∀ β : ℂ, β ≠ 0 → ‖β‖ ≤ ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ ((r : ℝ) / 2) → ‖β⁻¹‖ ≤ ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ ((r : ℝ) / 2) → β ≠ GlobalTheory.LFun.npow w ((k : ℂ) / 2)) ∧ ∀ x : ℂˣ, ‖(x : ℂ)‖ = 1 → x ≠ 1 → ∀ β ∈ GlobalTheory.LFun.seg w x t, (β : ℂ) ≠ GlobalTheory.LFun.npow w ((k : ℂ) / 2) := by
  first | exact @GlobalTheory.RkNs.small_entries_and_strings_avoid_excluded | exact GlobalTheory.RkNs.small_entries_and_strings_avoid_excluded | (intros; apply GlobalTheory.RkNs.small_entries_and_strings_avoid_excluded <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainEachStepSplitPlaceWithoutExcludedParams

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainNS
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainNS

theorem chainNS_holds : ∀ D : D7, ChainNS D := by
  intro D c hc S' hS' B hB hBi k hk
  obtain ⟨p, hp, -, hpS, v, hv⟩ :=
    GlobalTheory.SplitChoice.exists_split_prime D (S' : Set (HeightOneSpectrum (𝓞 D.host.F))) 1 (Finset.finite_toSet _) one_ne_zero
  have hvS : v ∉ S' := fun h => hpS v (Finset.mem_coe.2 h) hv
  refine ⟨v, hvS, GlobalTheory.SplitPlace.isSplit_of_splitsCompletely D p hp v hv, ?_⟩
  intro w hw β hβ k' hk'
  have hrt5 : D.R.r + 5 ≤ D.R.t := D.R.rank_add_five_le
  have hrt : D.R.r + 2 ≤ D.R.t := by omega
  have hwS : w ∉ GlobalTheory.LFun.above D.host.E (S' : Set (HeightOneSpectrum (𝓞 D.host.F))) := by
    simp [GlobalTheory.LFun.above, hw, hvS]
  have hpw : ((p : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal := by
    have h := hv
    rw [← hw, HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap, map_natCast] at h
    exact h
  have hwc : w.under (𝓞 D.host.F) ∉ c.S := fun h => hvS (hw ▸ hS' h)
  set x := GlobalTheory.LFun.val (F := D.host.F) (c.chT (k + 1)) w with hx
  have hmem : x⁻¹ * β ∈ GlobalTheory.LFun.twist (chainPar c B k) (GlobalTheory.LFun.val (F := D.host.F) (c.chT (k + 1)))⁻¹ w := by
    simp only [GlobalTheory.LFun.twist, Pi.inv_apply]
    exact Multiset.mem_map_of_mem _ hβ
  rw [chainPar_twist_chT] at hmem
  have key : ((x⁻¹ * β : ℂˣ) : ℂ) ≠ GlobalTheory.LFun.npow w ((k' : ℂ) / 2) := by
    have hN := GlobalTheory.T.small_entries_and_strings_avoid_excluded_norm_powers D.host.E w D.R.r D.R.t hrt k' hk'
    simp only [Pi.add_apply, Finset.sum_apply, Multiset.mem_add, Multiset.mem_sum] at hmem
    rcases hmem with h | ⟨i, hi, h⟩
    · simp only [GlobalTheory.LFun.twist, Pi.inv_apply] at h
      obtain ⟨b, hb, hb'⟩ := Multiset.mem_map.1 h
      rw [← hb']
      have hb1 := (hB w hwS).2 b hb
      have hb2 := (hBi w hwS).2 b⁻¹ (Multiset.mem_map_of_mem _ hb)
      have hu : ‖((GlobalTheory.LFun.val (F := D.host.F) (c.μ (k + 1)) w : ℂˣ) : ℂ)‖ = 1 := GlobalTheory.LFun.norm_val _ _
      refine hN.1 _ (Units.ne_zero _) ?_ ?_
      · rw [Units.val_mul, norm_mul, Units.val_inv_eq_inv_val, norm_inv, hu, inv_one, one_mul]
        exact hb1
      · rw [Units.val_mul, mul_inv, norm_mul, Units.val_inv_eq_inv_val, inv_inv, hu, one_mul]
        rw [Units.val_inv_eq_inv_val] at hb2
        exact hb2
    · have hi' := Finset.mem_Icc.1 hi
      exact hN.2 _ (GlobalTheory.LFun.norm_val _ _)
        (GlobalTheory.T.heckeCharQuotient_ne_one_completelySplitPrime D c hc i (k + 1) hi'.1 (by omega) (by omega) p hp w hpw hwc) _ h
  intro he
  apply key
  rw [Units.val_mul, Units.val_inv_eq_inv_val, mul_comm]
  exact he

end GlobalTheory.ChainNS
end
end
