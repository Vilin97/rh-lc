module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemTranslate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerOperatorHeisenbergPreservesSchwartzB
public import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
public import Mathlib.Analysis.Normed.Ring.Basic
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupClosedEmbeddingIntegralStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenNormalisedSubgroupSubset
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EqOneOfNormPowTwoPowSubOneLt

section

@[expose] public section

namespace GlobalTheory.NormPowerTwoUnity

lemma norm_sq_sub_one_ge (w : ℂ) (h : ‖w - 1‖ < (1 / 2 : ℝ)) :
    (3 / 2 : ℝ) * ‖w - 1‖ ≤ ‖w ^ 2 - 1‖ := by
  have e : w ^ 2 - 1 = (w + 1) * (w - 1) := by ring
  have h2 : ‖(2 : ℂ)‖ ≤ ‖w + 1‖ + ‖w - 1‖ := by
    have : (2 : ℂ) = (w + 1) - (w - 1) := by ring
    rw [this]
    exact norm_sub_le _ _
  have h3 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [e, norm_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  linarith

theorem eq_one_of_norm_pow_two_pow_sub_one_lt (z : ℂ)
    (h : ∀ (m : ℕ), ‖z ^ (2 : ℕ) ^ m - (1 : ℂ)‖ < (1 / 2 : ℝ)) : z = (1 : ℂ) := by
  apply SchrodingerSchwartzBruhat.GlobalTheory.CompanionTheory.SchrSB.eq_one_of_pow_two_pow_near <;> assumption

end GlobalTheory.NormPowerTwoUnity
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSpaceOfTypedAutomorphic

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TriStepMem

theorem eq_one_of_pow_two_pow (z : ℂ) (h : ∀ m : ℕ, ‖z ^ (2 ^ m) - 1‖ < 1 / 2) : z = 1 := by
  first
  | exact @_root_.GlobalTheory.NormPowerTwoUnity.eq_one_of_norm_pow_two_pow_sub_one_lt
  | exact _root_.GlobalTheory.NormPowerTwoUnity.eq_one_of_norm_pow_two_pow_sub_one_lt
  | (apply _root_.GlobalTheory.NormPowerTwoUnity.eq_one_of_norm_pow_two_pow_sub_one_lt <;> assumption)
  | (intros; apply _root_.GlobalTheory.NormPowerTwoUnity.eq_one_of_norm_pow_two_pow_sub_one_lt <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NormPowerTwoUnity.eq_one_of_norm_pow_two_pow_sub_one_lt <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NormPowerTwoUnity.eq_one_of_norm_pow_two_pow_sub_one_lt ..)

end GlobalTheory.TriStepMem

namespace GlobalTheory.TriStep

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {S : Dbl2 ψ σ}

theorem mem_space_of_typed : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (S : Dbl2 ψ σ) (Q : QStep S)
    (f : GA D S.B'.V → ℂ), IsContAut S.B'.V f → Q.Typed f → f ∈ GlobalTheory.TriStep.space Q := by
  intro D ψ σ S Q f hf hT
  have hgl : Continuous Q.gl₂ := (GlobalTheory.T.splitPlace_local_group_closedEmbedding_integral D Q.k Q.q S.B'.V _ Q.F.G₂ Q.gl₂ Q.loc₂).1.continuous
  refine ⟨fun y => ⟨fun γ hγ x => ?_, ?_⟩, ?_⟩
  · simp only [rTrans]
    rw [mul_assoc, hf.1 γ hγ]
  · exact hf.2.comp (continuous_id.mul continuous_const)
  · by_cases h0 : ∃ x, f x ≠ 0
    · obtain ⟨x, hx⟩ := h0
      have hval : ∀ j : Q.L₂.J, f (x * Q.gl₂ j.1) = (Q.L₂.lam j : ℂ) * f x := fun j => by
        have := congrFun (hT j) x
        simpa [rTrans] using this
      let φ : GL (Q.n₂ ⊕ Fin (Q.c + 1)) Q.k → ℂ := fun g => f (x * Q.gl₂ g) / f x
      have hφc : Continuous φ := (hf.2.comp (continuous_const.mul hgl)).div_const _
      have hφ : ∀ j : Q.L₂.J, φ j.1 = (Q.L₂.lam j : ℂ) := fun j => by
        simp only [φ, hval j]; field_simp
      let U : Set (GL (Q.n₂ ⊕ Fin (Q.c + 1)) Q.k) := (Q.L₂.J : Set _) ∩ φ ⁻¹' Metric.ball 1 (1 / 2)
      have hU : U ∈ nhds (1 : GL (Q.n₂ ⊕ Fin (Q.c + 1)) Q.k) := by
        refine (Q.co₂.1.inter (Metric.isOpen_ball.preimage hφc)).mem_nhds ⟨Q.L₂.J.one_mem, ?_⟩
        have := hφ 1
        simp only [OneMemClass.coe_one, map_one, Units.val_one] at this
        simp [this]
      obtain ⟨K, hKo, hKU, -, -⟩ := GlobalTheory.SmGL.exists_open_normalised_subgroup_subset Q.k (Q.n₂ ⊕ Fin (Q.c + 1)) U hU
      refine ⟨K, hKo, fun u hu => ?_⟩
      have huJ : u ∈ Q.L₂.J := (hKU hu).1
      have hlam : (Q.L₂.lam ⟨u, huJ⟩ : ℂ) = 1 := by
        apply GlobalTheory.TriStepMem.eq_one_of_pow_two_pow
        intro m
        have hm : u ^ (2 ^ m) ∈ K := K.pow_mem hu _
        have hmU := hKU hm
        have hmJ : u ^ (2 ^ m) ∈ Q.L₂.J := hmU.1
        have e : (⟨u ^ (2 ^ m), hmJ⟩ : Q.L₂.J) = (⟨u, huJ⟩ : Q.L₂.J) ^ (2 ^ m) := rfl
        have h2 : φ (u ^ (2 ^ m)) ∈ Metric.ball (1 : ℂ) (1 / 2) := hmU.2
        rw [show u ^ (2 ^ m) = ((⟨u ^ (2 ^ m), hmJ⟩ : Q.L₂.J) : GL _ _) from rfl, hφ, e, map_pow,
          Units.val_pow_eq_pow_val, Metric.mem_ball, dist_eq_norm] at h2
        exact h2
      have := hT ⟨u, huJ⟩
      rw [hlam, one_smul] at this
      exact this
    · push_neg at h0
      refine ⟨⊤, isOpen_univ, fun u _ => ?_⟩
      funext g
      simp [rTrans, h0]

end GlobalTheory.TriStep
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSpaceOfTypedAutomorphicStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.mem_space_of_typed_automorphic : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (S : Dbl2 ψ σ) (Q : QStep S) (f : GA D S.B'.V → ℂ), IsContAut S.B'.V f → Q.Typed f → f ∈ GlobalTheory.TriStep.space Q := by
  first | exact @GlobalTheory.TriStep.mem_space_of_typed | exact GlobalTheory.TriStep.mem_space_of_typed | (intros; apply GlobalTheory.TriStep.mem_space_of_typed <;> assumption)
end
end
