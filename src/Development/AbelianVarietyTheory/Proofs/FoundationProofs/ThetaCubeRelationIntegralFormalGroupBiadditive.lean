module

public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.AdditionIdentityOfSigmaFormulaUnit
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FrobeniusStickelbergerPadicDeterminantFormula
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
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SigmaStarAdditionFormulaPadicModelParameterStatement
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.FormalGroupLawFirstHalfHolds
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.CubicExponentialFactor
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FglChordFactor
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FglTriFactor
public import Formalism.PeriodIntegrals.PhiCubeOfFactor
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalGroupCommon.ExpLog
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalGroupCommon.CoeffSingleLg
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.LevelRestrictionOfGroupLawHolds

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.FrobeniusStickelbergerPadicDeterminantFormulaStatement

section

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.pAdicFrobeniusStickelberger_of_d7_datum : ∀ D : D7, Formalism.MainNotions.Ext.CutA.PAdicFrobeniusStickelberger D := by
  first | exact @GlobalTheory.FrobStick.frobenius_stickelberger_padic_determinant_formula | exact GlobalTheory.FrobStick.frobenius_stickelberger_padic_determinant_formula | (intros; apply GlobalTheory.FrobStick.frobenius_stickelberger_padic_determinant_formula <;> assumption)
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialFactorIdentity.ExpMvEq

section

@[expose] public section

noncomputable section

namespace PI.PhiCubeOfFactor.Wk

open PI.PhiCubeOfFactor MvPowerSeries PI.FglShared

variable {p : ℕ} [Fact p.Prime]

theorem logMv_eq {σ : Type} (F : MvPowerSeries σ ℂ_[p]) : logMv F = logS F := rfl

theorem expMv_eq {σ : Type} (F : MvPowerSeries σ ℂ_[p]) : expMv F = PI.FglPhSplit.expMv F := rfl

theorem main : Lemma := by
  intro p _ l ex E Q hex0 hinv hE1 hfun hQ
  obtain ⟨n, hnI, hn0, rfl⟩ := hQ
  have hl0 := l_constantCoeff hex0 hinv
  have hcX : ∀ i : Fin 2, constantCoeff (Xv i : MvPowerSeries (Fin 2) ℂ_[p]) = 0 :=
    fun i => constantCoeff_X i
  have hlg : ∀ i : Fin 2, constantCoeff (lg l (Xv i : MvPowerSeries (Fin 2) ℂ_[p])) = 0 := by
    intro i
    unfold lg
    rw [constantCoeff_subst_of_zero (hcX i)]
    exact hl0
  have hs0 : constantCoeff (lg l (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) + lg l (Xv 1)) = 0 := by
    rw [map_add (f := _), hlg, hlg, add_zero]
  have hd0 : constantCoeff (lg l (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) - lg l (Xv 1)) = 0 := by
    rw [map_sub, hlg, hlg, sub_zero]
  have hA0 : constantCoeff (add l ex (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := by
    unfold add pt
    rw [constantCoeff_subst_of_zero hs0]
    exact hex0
  have hB0 : constantCoeff (sub l ex (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := by
    unfold sub pt
    rw [constantCoeff_subst_of_zero hd0]
    exact hex0
  obtain ⟨k, hk, hlk⟩ := exists_coeff_ne hex0 hinv
  have hc0 : ∀ i : Fin 2, coeff (Finsupp.single (0 : Fin 2) k) (lg l (Xv i : MvPowerSeries (Fin 2) ℂ_[p])) =
      if i = 0 then PowerSeries.coeff k l else 0 := fun i => coeff_single_lg l 0 i hk
  have hAne : (add l ex (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) ≠ 0 := by
    unfold add pt
    refine subst_ne_zero hex0 hinv hs0 ?_
    intro h
    have h2 := congrArg (coeff (Finsupp.single (0 : Fin 2) k)) h
    rw [map_add (f := _), map_zero, hc0, hc0] at h2
    simp at h2
    exact hlk h2
  have hBne : (sub l ex (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) ≠ 0 := by
    unfold sub pt
    refine subst_ne_zero hex0 hinv hd0 ?_
    intro h
    have h2 := congrArg (coeff (Finsupp.single (0 : Fin 2) k)) h
    rw [map_sub, map_zero, hc0, hc0] at h2
    simp at h2
    exact hlk h2
  have hcanc : eAt E (add l ex (Xv 0) (Xv 1)) * eAt E (sub l ex (Xv 0) (Xv 1)) =
      n * eAt E (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) ^ 2 * eAt E (Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) ^ 2 := by
    apply mul_left_cancel₀ (mul_ne_zero hAne hBne)
    linear_combination hfun
  have hexp0 : PI.FglPhSplit.expMv (0 : PowerSeries ℂ_[p]) = 1 := by
    refine MvPowerSeries.ext fun α => ?_
    change (∑ m ∈ Finset.range ((α.sum fun _ k => k) + 1),
      MvPowerSeries.coeff α ((0 : PowerSeries ℂ_[p]) ^ m) / (m.factorial : ℂ_[p])) = MvPowerSeries.coeff α 1
    rw [Finset.sum_eq_single 0 (fun m _ hm => by rw [zero_pow hm, map_zero, zero_div])
      (fun h => absurd (Finset.mem_range.mpr (Nat.succ_pos _)) h)]
    simp
  have hL0 : constantCoeff (logS E) = 0 := constantCoeff_logS E
  have hnL0 : constantCoeff (-logS E) = 0 := by rw [map_neg, hL0, neg_zero]
  have hUE : PI.FglPhSplit.expMv (-logS E) * E = 1 := by
    have h := expMv_add' hnL0 hL0
    rw [neg_add_cancel, hexp0, expMv_logS hE1] at h
    exact h.symm
  have hsub : ∀ a : MvPowerSeries (Fin 2) ℂ_[p], constantCoeff a = 0 →
      PI.FglPhSplit.expMv (phAt E a) * eAt E a = 1 := by
    intro a ha
    have hS : PowerSeries.HasSubst a := PowerSeries.HasSubst.of_constantCoeff_zero ha
    unfold phAt eAt
    rw [logMv_eq, expMv_subst' ha hnL0, ← PowerSeries.subst_mul hS, hUE, ← PowerSeries.coe_substAlgHom hS,
      map_one]
  have hneg : ∀ a : MvPowerSeries (Fin 2) ℂ_[p], constantCoeff a = 0 →
      PI.FglPhSplit.expMv (-phAt E a) = eAt E a := by
    intro a ha
    have hS : PowerSeries.HasSubst a := PowerSeries.HasSubst.of_constantCoeff_zero ha
    unfold phAt eAt
    rw [logMv_eq, ← PowerSeries.coe_substAlgHom hS, ← map_neg, neg_neg, PowerSeries.coe_substAlgHom hS,
      expMv_subst' ha hL0, expMv_logS hE1]
  have hph0 : ∀ a : MvPowerSeries (Fin 2) ℂ_[p], constantCoeff a = 0 → constantCoeff (phAt E a) = 0 := by
    intro a ha
    unfold phAt
    rw [constantCoeff_subst_of_zero ha, logMv_eq]
    exact hnL0
  have hnph0 : ∀ a : MvPowerSeries (Fin 2) ℂ_[p], constantCoeff a = 0 → constantCoeff (-phAt E a) = 0 := by
    intro a ha
    rw [map_neg, hph0 a ha, neg_zero]
  have hf : phAt E (add l ex (Xv 0) (Xv 1)) + phAt E (sub l ex (Xv 0) (Xv 1)) -
      (2 * phAt E (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) + 2 * phAt E (Xv 1 : MvPowerSeries (Fin 2) ℂ_[p])) =
      phAt E (add l ex (Xv 0) (Xv 1)) + phAt E (sub l ex (Xv 0) (Xv 1)) + -phAt E (Xv 0) + -phAt E (Xv 0) +
        -phAt E (Xv 1) + -phAt E (Xv 1) := by ring
  refine ⟨?_, ?_⟩
  · rw [hf, map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), hph0 _ hA0, hph0 _ hB0, hnph0 _ (hcX 0),
      hnph0 _ (hcX 1)]
    ring
  · rw [expMv_eq, hf]
    have c1 := hph0 _ hA0
    have c2 := hph0 _ hB0
    have c3 := hnph0 _ (hcX 0)
    have c4 := hnph0 _ (hcX 1)
    rw [expMv_add' (by simp only [map_add (f := _), c1, c2, c3, c4, add_zero]) c4,
      expMv_add' (by simp only [map_add (f := _), c1, c2, c3, add_zero]) c4,
      expMv_add' (by simp only [map_add (f := _), c1, c2, c3, add_zero]) c3,
      expMv_add' (by simp only [map_add (f := _), c1, c2, add_zero]) c3,
      expMv_add' c1 c2, hneg _ (hcX 0), hneg _ (hcX 1)]
    refine int_of_mul_eq_one hnI hn0 ?_
    have e1 := hsub _ hA0
    have e2 := hsub _ hB0
    linear_combination (PI.FglPhSplit.expMv (phAt E (add l ex (Xv 0) (Xv 1))) *
      PI.FglPhSplit.expMv (phAt E (sub l ex (Xv 0) (Xv 1)))) * hcanc.symm +
      PI.FglPhSplit.expMv (phAt E (sub l ex (Xv 0) (Xv 1))) * eAt E (sub l ex (Xv 0) (Xv 1)) * e1 + e2

end PI.PhiCubeOfFactor.Wk

end
end
end

-- Source module: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PhiCubeOfFactor

section

@[expose] public section

theorem phiCubeOfFactor : PI.PhiCubeOfFactor.Lemma := PI.PhiCubeOfFactor.Wk.main
end
end

-- Source module: Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.TheoremOfCubeOfAdditionFormulas

section

@[expose] public section

namespace Formalism.MainNotions.Ext.CutA

open Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3r7

theorem lemma_three_one_third_holds : LemmaThreeOneThird := by
  intro p hp g hOk hI
  obtain ⟨⟨h1, h2, h3, h4, h6, hΔ⟩, hW, he0, hel⟩ := hOk
  exact formal_group_tri_factor p g.W g.wq g.ex h1 h2 h3 h4 h6 hΔ hW he0 hel hI

theorem lemma_three_one_second_holds : UnitTraceSumSecondBound := by
  intro p hp g hOk hI
  obtain ⟨⟨h1, h2, h3, h4, h6, hΔ⟩, hW, he0, hel⟩ := hOk
  exact fglChordFactor p g.W g.wq g.ex h1 h2 h3 h4 h6 hΔ hW he0 hel hI

theorem cube3OfDet_holds : Cube3OfDet := by
  intro p hp g hOk hE hQ hn
  obtain ⟨⟨h1, h2, h3, h4, h6, hΔ⟩, hW, he0, hel⟩ := hOk
  exact thetaCube_triple_relation p g.W g.wq g.l g.ex (ePhi1 g.lam g.abelian₂ g.C g.wq) _ h1 h2 h3 h4 h6 hW he0 hel hE hQ hn

theorem cube_second_of_determinant_formula (D : Formalism.BasicNotions.D7) (hQ : PAdicFrobeniusStickelberger D) : cube3 D :=
  cube_second_identity_of_determinant lemma_three_one_third_holds cube3OfDet_holds D hQ (addInt_holds D)

theorem cube_first_of_addition_holds : CubeIdentityFromAdditionFormula := by
  intro p hp g hOk hE hId hn
  obtain ⟨_, hW, he0, hel⟩ := hOk
  exact phiCubeOfFactor p _ g.ex _ _ he0 hel hE hId hn

theorem cube_first_of_addition_formula (D : Formalism.BasicNotions.D7) (hQ : PAdicSigmaAdditionFormula D) : cube2 D :=
  addition_identity_of_sigma_formula lemma_three_one_second_holds cube_first_of_addition_holds D hQ (ePhiOne_holds D) (addInt_holds D)

theorem theorem_of_cube_of_addition_formulas (D : Formalism.BasicNotions.D7) (hQ : PAdicSigmaAdditionFormula D) (hQd : PAdicFrobeniusStickelberger D) : cube D :=
  cube_of cube_of_two_identities_holds D (cube_first_of_addition_formula D hQ) (cube_second_of_determinant_formula D hQd)

end Formalism.MainNotions.Ext.CutA
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaCubeRelationIntegralFormalGroupBiadditive

section

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.ThetaCube

theorem cube_addInt_beBiadd : ∀ D : D7, GL3Theta.cube D ∧ GL3Theta.addInt D ∧ GL3Theta.beBiadd D := by
  intro D
  have hc : GL3Theta.cube D := Formalism.MainNotions.Ext.CutA.theorem_of_cube_of_addition_formulas D (GlobalTheory.T.sigmaStar_addition_formula_padic_modelParameter D) (GlobalTheory.T.pAdicFrobeniusStickelberger_of_d7_datum D)
  exact ⟨hc, Formalism.MainNotions.Ext.addInt_holds D, Formalism.MainNotions.Ext.beBiadd_of_cube D hc⟩

end GlobalTheory.ThetaCube
end
end
