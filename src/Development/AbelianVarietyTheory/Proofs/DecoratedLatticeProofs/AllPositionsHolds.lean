module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.AllPositions
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricLevelChainClassAtEveryPositionStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralCompBlocks
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OpEOmTargetUnipotent
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalBasic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricLevelChainPatternIteratedStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricLevelChainSupportAtOfPatternStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricLevelChainUnfoldedPositionExchange

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricLevelChainOneIndexAtOfClassSupport

section

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

namespace GlobalTheory.SymChain

theorem oneIndexAt_of_classAt_supportAt : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], S.ClassAt t ν → S.SupportAt t → S.OneIndexAt t ν := by
  intro k _ _ _ _ _ _ ν hν s κ S t _ _ hC hS j c H p hp1 hpc h hE
  haveI : ν.IsAddHaarMeasure := hν.1
  obtain ⟨r, hr, u, hu, rfl⟩ := hC j c H p hp1 hpc h hE
  obtain ⟨γ, g, hg, rfl⟩ := Radical.exists_of_mem_R hr
  have hmul : ∀ (a b : GL (XIx (Fin κ) t (j + 1) ⊕ Fin c) k) (Ψ : type_of% ((S.T t).Phi j c H)),
      om (S.μ (j + 1)) 1 (a * b) Ψ = om (S.μ (j + 1)) 1 a (om (S.μ (j + 1)) 1 b Ψ) :=
    fun a b Ψ => by rw [← om_mul, one_mul]
  have hne : opE S.ψ ν p (om (S.μ (j + 1)) 1 u ((S.T t).Phi j c H)) ≠ 0 := by
    intro h0
    apply hE
    rw [mul_assoc, hmul, (opE_om_embX k _ _ c p hp1 hpc S.ψ ν _ _).1, hmul,
      opE_om_target_unipotent k _ _ c p hp1 hpc S.ψ ν _ _ g hg, h0]
    funext y
    simp [om]
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, opE S.ψ ν p (om (S.μ (j + 1)) 1 u ((S.T t).Phi j c H)) x₀ ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hne (funext hc)
  classical
  obtain ⟨e, he⟩ : ∃ e, om (S.μ (j + 1)) 1 u ((S.T t).Phi j c H) (affPt p x₀ e) ≠ 0 := by
    by_contra hc
    push_neg at hc
    apply hx₀
    simp [opE, hc]
  have hΦ : (S.T t).Phi j c H ((u⁻¹).val * affPt p x₀ e) ≠ 0 := by
    intro h0
    apply he
    simp only [om, Units.val_one, Matrix.mul_one, h0, mul_zero]
  obtain ⟨r', hr', u', hu', rfl⟩ := hS j c H p hp1 hpc u hu x₀ e hΦ
  exact ⟨embX c γ * g * r', mul_mem hr hr', u', hu', by group⟩

end GlobalTheory.SymChain
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricLevelChainOneIndexAtOfClassSupportStatement

section

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

theorem _root_.GlobalTheory.T.symmetricLevelChain_oneIndexAt_of_class_support : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], S.ClassAt t ν → S.SupportAt t → S.OneIndexAt t ν := by
  first | exact @GlobalTheory.SymChain.oneIndexAt_of_classAt_supportAt | exact GlobalTheory.SymChain.oneIndexAt_of_classAt_supportAt | (intros; apply GlobalTheory.SymChain.oneIndexAt_of_classAt_supportAt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricLevelChainUnfoldedPositionExchangeStatement

section

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

theorem _root_.GlobalTheory.T.symmetricLevelChain_unfolded_position_exchange : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], S.Pattern t → S.ExchangeAt t ν := by
  first | exact @GlobalTheory.SymChain.ExchangeProof.exchangeAt | exact GlobalTheory.SymChain.ExchangeProof.exchangeAt | (intros; apply GlobalTheory.SymChain.ExchangeProof.exchangeAt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AllPositionsHolds

section

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

namespace GlobalTheory.SymChain

theorem allPositions_holds : AllPositions := by
  intro k _ _ _ _ _ _ ν hν s κ S t _ _
  have hpat : S.Pattern t := GlobalTheory.T.symmetricLevelChain_pattern_iterated k s κ S t
  have hsupp : S.SupportAt t := GlobalTheory.T.symmetricLevelChain_supportAt_of_pattern k s κ S t hpat
  have hclass : S.ClassAt t ν := GlobalTheory.T.symmetricLevelChain_classAt_every_position k ν hν s κ S t
  exact ⟨GlobalTheory.T.symmetricLevelChain_oneIndexAt_of_class_support k ν hν s κ S t hclass hsupp, GlobalTheory.T.symmetricLevelChain_unfolded_position_exchange k ν hν s κ S t hpat⟩

end GlobalTheory.SymChain
end
end
