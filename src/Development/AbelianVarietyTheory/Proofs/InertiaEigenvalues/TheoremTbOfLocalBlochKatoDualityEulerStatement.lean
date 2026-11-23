module

public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoLocalAllOfTateDualityEulerCharStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiesAndInputsOfDualityEuler
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineExtensionClassBoundStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeightGoodReductionAtPrime
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeightGoodReductionAtPrimeStatement

section

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

theorem _root_.GlobalTheory.T.weight_good_reduction_at_prime : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), admitted D HW F → Conclusion5 D → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := sit D.loc HW l (D.locA l) K s LL h; let E : S.Comparison₂ := ((F l).E K s LL h).tie; TBeAt S := by
  first | exact @GlobalTheory.TwistTors.twist_torsion_facts | exact GlobalTheory.TwistTors.twist_torsion_facts | (intros; apply GlobalTheory.TwistTors.twist_torsion_facts <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedTorsionClassTheoremGoodCase

section

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

namespace GlobalTheory.TheoremTB

theorem tb_assembled : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW),
    admitted D HW F → Conclusion5 D → Conclusion4 D HW F := by
  intro D HW F hA h5 l _ K s LL h
  exact ⟨GlobalTheory.T.crystalline_extension_class_bound D HW F hA l K s LL h, GlobalTheory.T.weight_good_reduction_at_prime D HW F hA h5 l K s LL h⟩

end GlobalTheory.TheoremTB
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedTorsionClassTheoremGoodCaseStatement

section

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

theorem _root_.GlobalTheory.T.twistedTorsionClassTheorem_goodCase : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), admitted D HW F → Conclusion5 D → Conclusion4 D HW F := by
  first | exact @GlobalTheory.TheoremTB.tb_assembled | exact GlobalTheory.TheoremTB.tb_assembled | (intros; apply GlobalTheory.TheoremTB.tb_assembled <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TheoremTbOfLocalBlochKatoDualityEuler

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.TheoremTBRecords

theorem aux_of_blochKato_tateDuality_eulerChar :
    GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK →
      ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
        LocalSituation.Conclusion4 D HW F := by
  intro hBK hTD hEC D HW F _Cm
  obtain ⟨_J, hA⟩ := GlobalTheory.LocInputs.ties_and_inputs_of_duality_euler hTD hEC D HW F
  exact GlobalTheory.T.twistedTorsionClassTheorem_goodCase D HW F hA (GlobalTheory.T.blochKatoLocal_all_of_tateDuality_eulerChar hBK hTD hEC D)

end GlobalTheory.TheoremTBRecords
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TheoremTbOfLocalBlochKatoDualityEulerStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

theorem _root_.GlobalTheory.T.theorem_tb_of_local_blochKato_duality_euler : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), LocalSituation.Conclusion4 D HW F := by
  first | exact @GlobalTheory.TheoremTBRecords.aux_of_blochKato_tateDuality_eulerChar | exact GlobalTheory.TheoremTBRecords.aux_of_blochKato_tateDuality_eulerChar | (intros; apply GlobalTheory.TheoremTBRecords.aux_of_blochKato_tateDuality_eulerChar <;> assumption)
end
end
