module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BiThetaOfVac
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsJointlySmoothBiThetaTwoVarCombination
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FramePositiveSum
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOneComb
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ToOneSucc
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
public import Mathlib.Algebra.Group.End
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.NumberTheory.LocalField.Basic
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsJointlySmoothBiThetaTwoVarCombination
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealLineOfPeriodsOnLine

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsReindexIff

section

@[expose] public section

open MeasureTheory ValuativeRel Matrix

noncomputable section
namespace GlobalTheory.SymCompare
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

section Plain
variable {k : Type*} [Field k] {n m n' m' : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
  [Fintype n'] [DecidableEq n'] [Fintype m'] [DecidableEq m'] {c : ℕ}

abbrev sE {n m : Type*} (e : n ≃ m) (c : ℕ) : n ⊕ Fin c ≃ m ⊕ Fin c := e.sumCongr (Equiv.refl _)

end Plain

section Local
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n m n' m' : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
  [Fintype n'] [DecidableEq n'] [Fintype m'] [DecidableEq m'] {c : ℕ}




end Local

section Iter
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {r t t' : Type*} [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t] [Fintype t'] [DecidableEq t']

variable {κ : Type*} [Fintype κ] [DecidableEq κ] {s : ℕ}

end Iter

end GlobalTheory.SymCompare
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsTer

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open GlobalTheory.FinPl (SplitPt grpAt grpOff)
open GlobalTheory.SymCompare (sE)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CombThetaAny

theorem main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (C : WO S T →₀ ℂ)
    (f : WO S T → ℂ), IsThetaFunO ψ S T f → IsThetaFunO ψ S T (comb ψ S T C f) := by
  intro D ψ hψ S T C f hf
  have e : comb ψ S T C f = fun u => ∑ x ∈ C.support, C x * (ψ (symplOH S T u x) * f (u + x)) := by
    funext u; exact GlobalTheory.FrComb.comb_apply C f u
  refine ⟨fun γ u => ?_, ?_, ?_, ?_⟩
  · simp only [GlobalTheory.FrComb.comb_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [add_assoc, hf.quasi, GlobalTheory.FinTranslate.symplOH_add_left, GlobalTheory.FinTranslate.symplOH_add_right]
    have key : ψ (symplOH S T (ratW T S γ) x + symplOH S T u x) * ψ (-(symplOH S T (ratW T S γ) u + symplOH S T (ratW T S γ) x)) =
        ψ (-(symplOH S T (ratW T S γ) u)) * ψ (symplOH S T u x) := by
      rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]; congr 1; ring
    linear_combination (C x * f (u + x)) * key
  · obtain ⟨U, hU, hUf⟩ := hf.level
    obtain ⟨V, hV, hVf⟩ := GlobalTheory.FrCombAny.exists_orth_any hψ C.support
    refine ⟨U ⊓ V, hU.inter hV, fun a ha ha' => ?_⟩
    exact GlobalTheory.FrComb.heisO_comb (hVf a ha.2 ha') (hUf a ha.1 ha')
  · rw [e]
    exact continuous_finsetSum _ fun x _ => continuous_const.mul
      ((hψ.1.1.comp (GlobalTheory.FinTranslate.continuous_symplOH S T x)).mul
        (hf.cont.comp (continuous_id.add continuous_const)))
  · intro n L hL hLf w
    rw [e]
    have e2 : (fun t => ∑ x ∈ C.support, C x * (ψ (symplOH S T (w + L t) x) * f (w + L t + x))) =
        fun t => ∑ x ∈ C.support, C x * (ψ (symplOH S T w x) * (ψ (symplOH S T (L t) x) * f (w + x + L t))) := by
      funext t
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [GlobalTheory.FinTranslate.symplOH_add_left, AddChar.map_add_eq_mul, add_right_comm, mul_assoc]
    simp only []
    rw [e2]
    exact ContDiff.sum fun x _ => contDiff_const.mul (contDiff_const.mul
      ((GlobalTheory.FrCombAny.contDiff_psi hψ hL hLf x).mul (hf.smooth n L hL hLf (w + x))))

end GlobalTheory.CombThetaAny

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestHeisenbergCombinationsJointRowGood

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowCombGood

theorem comb_good : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ C, IsRealFam ch.W C → ∀ c : Combs ch.G, (∀ j, j < D.R.m → IsFinComb (c.1 j)) →
    Good ch.W (combC ch.W c C) (combR ch.rm c) := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch _ _ => ?_⟩⟩
  intro C hC c _
  have hψ : IsStdChar D ch.W.ψ (-1) := ch.W.ψ_std
  have hL := s.core.lev
  refine ⟨fun j hje hj => ?_, fun i => ?_⟩
  · obtain ⟨k, hk⟩ := D.R.m_even
    obtain ⟨l, hl⟩ := hje
    obtain ⟨hv, hs⟩ := hC j ⟨l, hl⟩ hj
    have h1 : IsBiTheta ch.W.ψ _ _ _ (C j) :=
      GlobalTheory.FrComb.biTheta_of_vac (node_isV ch.G hL (X := .top j) (show j ≤ D.R.m by omega)).sd
        (node_isV ch.G hL (X := .top (j + 1)) (show j + 1 ≤ D.R.m by omega)).sd
        (node_isV ch.G hL (X := .top (j + 1 + 1)) (show j + 1 + 1 ≤ D.R.m by omega)).sd hv hs
    exact GlobalTheory.FrCombAny.biTheta_biComb D _ hψ _ _ _ _ h1 _ _
  · exact GlobalTheory.CombThetaAny.main D _ hψ _ _ _ _ (ch.rm.vX_is i D.R.m i.2 le_rfl).2.theta

end GlobalTheory.RowCombGood
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestHeisenbergCombinationsJointRowGoodStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.rowTest_heisenberg_combinations_joint_row_good : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ C, IsRealFam ch.W C → ∀ c : Combs ch.G, (∀ j, j < D.R.m → IsFinComb (c.1 j)) →
    Good ch.W (combC ch.W c C) (combR ch.rm c) := by
  first | exact @GlobalTheory.RowCombGood.comb_good | exact GlobalTheory.RowCombGood.comb_good | (intros; apply GlobalTheory.RowCombGood.comb_good <;> assumption)
end
end
