module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ContinuousBdGen
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EqOfThetaHeisenbergTranslates
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HalfMulTwoAF
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PoissonSummationAdelicTuples

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EqOfThetaHeisenbergTranslatesStatement

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.eq_of_theta_heisenbergTranslates : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) (ψ : AddChar (AF F) ℂ) (lam : InfinitePlace F → ℝ) (ν : Measure (AF F)) (a : Fin N → F), Ctx ψ lam ν a → ∀ G G' : (Fin N → AF F) → ℂ, Decay G → Decay G' → (∀ x y, th (rho ψ a x y G) = th (rho ψ a x y G')) → G = G' := by
  first | exact @GlobalTheory.SWQ.eq_of_theta_rho | exact GlobalTheory.SWQ.eq_of_theta_rho | (intros; apply GlobalTheory.SWQ.eq_of_theta_rho <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PoissonSummationAdelicTuplesStatement

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.poisson_summation_adelic_tuples : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) (ψ : AddChar (AF F) ℂ) (lam : InfinitePlace F → ℝ) (ν : Measure (AF F)) (a : Fin N → F), Ctx ψ lam ν a → ∀ Φ : (Fin N → AF F) → ℂ, Decay Φ → Decay (Fo ψ ν a Φ) → th (Fo ψ ν a Φ) = th Φ := by
  first | exact @GlobalTheory.SWQ.poisson_summation | exact GlobalTheory.SWQ.poisson_summation | (intros; apply GlobalTheory.SWQ.poisson_summation <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FourierInversion

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.SWQ

theorem fourier_inversion : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) (ψ : AddChar (AF F) ℂ)
    (lam : InfinitePlace F → ℝ) (ν : Measure (AF F)) (a : Fin N → F), Ctx ψ lam ν a →
    ∀ Φ : (Fin N → AF F) → ℂ, Decay Φ → Decay (Fo ψ ν a Φ) → Decay (Fo ψ ν a (Fo ψ ν a Φ)) →
      Fo ψ ν a (Fo ψ ν a Φ) = Da (-1) Φ := by
  intro F _ _ N ψ lam ν a hC Φ hΦ hFΦ hFFΦ
  have hD1 : Decay (Da (-1) Φ) :=
    (GlobalTheory.SWQ.decay_ops F N ψ lam ν a hC Φ hΦ).2.2.1 (-1) isUnit_one.neg
  apply GlobalTheory.T.eq_of_theta_heisenbergTranslates F N ψ lam ν a hC _ _ hFFΦ hD1
  intro x y

  have iΦ := GlobalTheory.SWQ.weil_intertwine F N ψ lam ν a hC Φ
  have iFΦ := GlobalTheory.SWQ.weil_intertwine F N ψ lam ν a hC (Fo ψ ν a Φ)
  have e1 : rho ψ a (-y) x (Fo ψ ν a Φ) = Fo ψ ν a (rho ψ a (-x) (-y) Φ) := by
    have := iΦ.2.2.1 (-y) x
    simpa using this
  have e2 : rho ψ a x y (Fo ψ ν a (Fo ψ ν a Φ)) = Fo ψ ν a (Fo ψ ν a (rho ψ a (-x) (-y) Φ)) := by
    rw [iFΦ.2.2.1 x y, e1]
  have dΨ : Decay (rho ψ a (-x) (-y) Φ) := (GlobalTheory.SWQ.decay_ops F N ψ lam ν a hC Φ hΦ).2.1 _ _
  have dFΨ : Decay (Fo ψ ν a (rho ψ a (-x) (-y) Φ)) := by
    rw [← e1]; exact (GlobalTheory.SWQ.decay_ops F N ψ lam ν a hC _ hFΦ).2.1 _ _
  have dFFΨ : Decay (Fo ψ ν a (Fo ψ ν a (rho ψ a (-x) (-y) Φ))) := by
    rw [← e2]; exact (GlobalTheory.SWQ.decay_ops F N ψ lam ν a hC _ hFFΦ).2.1 _ _
  rw [e2, GlobalTheory.T.poisson_summation_adelic_tuples F N ψ lam ν a hC _ dFΨ dFFΨ, GlobalTheory.T.poisson_summation_adelic_tuples F N ψ lam ν a hC _ dΨ dFΨ]

  have e3 : rho ψ a x y (Da (-1) Φ) = Da (-1) (rho ψ a (-x) (-y) Φ) := by
    have := iΦ.2.1 (-1) (-1) x y (by norm_num)
    simpa using this
  rw [e3]
  have e4 : (Da (-1 : AF F) (rho ψ a (-x) (-y) Φ) : (Fin N → AF F) → ℂ) =
      Da (algebraMap F (AF F) (-1)) (rho ψ a (-x) (-y) Φ) := by simp
  rw [e4, (GlobalTheory.SWQ.weil_intertwine F N ψ lam ν a hC (rho ψ a (-x) (-y) Φ)).2.2.2.2 (-1) (by norm_num)]

end GlobalTheory.SWQ
end
end
