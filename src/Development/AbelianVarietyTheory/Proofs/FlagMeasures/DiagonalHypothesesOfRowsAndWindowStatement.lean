module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ToGlob0
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.SzHypFD
public import Formalism.SharpRestriction.CuspSpanNormBounds.AdmissibleBoundsFromSource
public import Formalism.SharpRestriction.CuspSpanNormBounds.LocalBesselAndTopKernel
public import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalRankNumberBoundsSizeComparisonsStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalRankNumberBoundsRankClausesFirstHalfStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HypothesesOfGlobalRowsAndNodesStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LevelPrimesSizeBoundsColumnDimensionStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PgFrameAtRecord
public import Formalism.LocalToGlobal.GlobalTheory.GL2.ModEqOfNormOneMod
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ResidEvFree
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.RamificationTwoAndConjugationAtQAndD
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.DataConditionsOfGlobalAndRealRows

section

@[expose] public section

noncomputable section

namespace GlobalTheory.Diag.PG

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

theorem data_of_rows (eps CD : ℝ) (he : 0 < eps) (he' : eps < 1 / 52) (hCD : 3 ≤ CD) :
    ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (D : D7) (Cg C0 : ℝ), Glob0 D x eps CD Cg → Nodes D x eps → ArithmeticConditionsOfDatum D →
      DuWin D C0 → StandingNumericalData D C0 := by
  obtain ⟨x1, hx1⟩ := GlobalTheory.T.globalRankNumberBounds_size_comparisons eps CD he he' hCD 1 one_pos
  refine ⟨max x1 1, fun x hx D Cg C0 hG hN hA hW => ?_⟩
  have hxx1 : x1 ≤ x := le_trans (le_max_left _ _) hx
  have hxone : 1 ≤ x := le_trans (le_max_right _ _) hx
  obtain ⟨-, -, -, h12, -⟩ := hx1 x hxx1 _ _ _ _ _ hG.nums
  have hk : 5 ≤ D.R.k := by
    have := D.R.two_le_m
    have := D.R.m_add_three_le_k
    omega
  have hm2 := D.R.two_le_m
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl

  have hF : ∀ {n : ℕ} (g : Fin n → ℚ) (a b : ℕ) (ha : a < n) (hb : b < n), a = b →
      g ⟨a, ha⟩ = g ⟨b, hb⟩ := by
    intro n g a b ha hb h
    subst h
    rfl

  have huO : ∀ u τ (i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ D.R.k),
      Formalism.MainNotions.S.uOne D u τ i = (((D.hcW u τ).u ⟨i - 1, by omega⟩ : ℚ) : ℝ) := by
    intro u τ i h1 h2
    unfold Formalism.MainNotions.S.uOne Formalism.MainNotions.S.uS
    rw [dite_eq_left ⟨h1, h2⟩]
  have hvO : ∀ τ (l : ℕ) (h1 : 1 ≤ l) (h2 : l ≤ D.R.k - 1),
      Formalism.MainNotions.S.vOne D τ l = (((D.hc τ).v ⟨l - 1, by omega⟩ : ℚ) : ℝ) := by
    intro τ l h1 h2
    unfold Formalism.MainNotions.S.vOne
    rw [dite_eq_left ⟨h1, h2⟩]
  have hbO : ∀ τ, Formalism.MainNotions.S.bOne D τ 1 = bFirst D τ := by
    intro τ
    unfold Formalism.MainNotions.S.bOne bFirst
    rw [dite_eq_left ⟨le_rfl, by have := D.R.two_le_m; omega⟩]
  have hu1 : ∀ u τ, Formalism.MainNotions.S.uOne D u τ 1 = uFirst D τ := by
    intro u τ
    rw [huO u τ 1 le_rfl (by omega)]
    unfold uFirst
    exact congrArg (fun q : ℚ => (q : ℝ))
      ((hF _ (1 - 1) 0 _ (by omega) (by norm_num)).trans (D.hcW_first u τ (by omega)))
  have huk : ∀ u τ, Formalism.MainNotions.S.uOne D u τ D.R.k = uLast D τ := by
    intro u τ
    rw [huO u τ D.R.k (by omega) le_rfl]
    unfold uLast
    exact congrArg (fun q : ℚ => (q : ℝ)) (D.hcW_last u τ (by omega))
  have hv1 : ∀ τ, Formalism.MainNotions.S.vOne D τ 1 = vFirst D τ := by
    intro τ
    rw [hvO τ 1 le_rfl (by omega)]
    unfold vFirst
    exact congrArg (fun q : ℚ => (q : ℝ)) (hF _ _ _ _ _ (by norm_num))
  have hvk : ∀ τ, Formalism.MainNotions.S.vOne D τ (D.R.k - 1) = vLast D τ := by
    intro τ
    rw [hvO τ (D.R.k - 1) (by omega) le_rfl]
    unfold vLast
    exact congrArg (fun q : ℚ => (q : ℝ)) (hF _ _ _ _ _ (by omega))
  have hDel : (0 : ℝ) < D.s.Del := by exact_mod_cast D.s.Del_pos
  have hkDel : (0 : ℝ) ≤ (D.R.k : ℝ) * D.s.Del := mul_nonneg (Nat.cast_nonneg _) hDel.le

  have hbx : 1 ≤ bx x eps := by
    unfold bx
    exact Real.one_le_exp (Real.rpow_nonneg (by linarith) _)
  have hg : ∀ i, 2 ≤ D.host.g i := by
    intro i
    have h := (hG.g_win i).1
    have hk' : (5 : ℝ) ≤ D.R.k := by exact_mod_cast hk
    have h5 : (5 : ℝ) ≤ (D.R.k : ℝ) * bx x eps := by nlinarith
    have h2 : (2 : ℝ) ≤ ((D.R.k : ℝ) * bx x eps) ^ 8 :=
      calc (2 : ℝ) ≤ 5 := by norm_num
        _ ≤ (D.R.k : ℝ) * bx x eps := h5
        _ ≤ ((D.R.k : ℝ) * bx x eps) ^ 8 := le_self_pow₀ (by linarith) (by norm_num)
    exact_mod_cast h2.trans h
  unfold Formalism.MainNotions.S.StandingNumericalData
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hW, hA.2.1, hA.2.2.1, hA.2.2.2, ?_⟩
  ·
    intro τ l h1 h2
    rw [hvO τ l h1 h2]
    exact hG.cloud τ ⟨l - 1, by omega⟩
  ·
    intro u l h1 h2
    have key : ∀ τ, Formalism.MainNotions.S.uOne D u τ (l + 1) = Formalism.MainNotions.S.vOne D τ l - 1 / 2 -
        (if D.s.letter u ⟨l - 1, by omega⟩ then (D.s.Del : ℝ) else 0) := by
      intro τ
      rw [huO u τ (l + 1) (by omega) (by omega), hvO τ l h1 (by omega)]
      have e := D.s.u_letter u τ (l - 1) (by omega)
      rw [D.hcW_v u τ] at e
      have e' : (D.hcW u τ).u ⟨l + 1 - 1, by omega⟩ = (D.hcW u τ).u ⟨l - 1 + 1, by omega⟩ :=
        hF _ _ _ _ _ (by omega)
      rw [e', e]
      split_ifs <;> push_cast <;> ring
    by_cases hL : D.s.letter u ⟨l - 1, by omega⟩ = true
    · right
      intro τ
      rw [key τ, if_pos hL]
    · left
      intro τ
      rw [key τ, if_neg hL]
      ring
  ·
    intro u τ
    rw [hu1 u τ, hv1 τ]
    by_cases ht : Top D τ
    · have h1 := (hN.top τ ht).1
      have h2 := (hG.cloud τ ⟨0, by omega⟩).2
      have hvF : vFirst D τ = (((D.hc τ).v ⟨0, by omega⟩ : ℚ) : ℝ) := by
        unfold vFirst
        rfl
      rw [hvF]
      nlinarith
    · exact (hG.off τ ht).1
  ·
    intro u τ ht
    rw [hu1 u τ, hv1 τ]
    exact (hG.off τ ht).2.1
  ·
    intro u τ ht
    rw [huk u τ, hvk τ]
    exact (hG.off τ ht).2.2
  ·
    intro τ ht
    unfold Formalism.MainNotions.S.bTop
    rw [huk D.u₀ τ, hbO τ]
    obtain ⟨-, -, h3, h4⟩ := hN.top τ ht
    constructor <;> linarith
  ·
    intro u τ
    constructor
    · intro i hi
      have hl : Formalism.MainNotions.S.lamS D.R (D.hc τ) ⟨i, by omega⟩ = (((D.hcW u τ).v ⟨i, by omega⟩ : ℚ) : ℝ) := by
        unfold Formalism.MainNotions.S.lamS
        rw [dite_eq_left (show i < D.R.k - 1 by omega), D.hcW_v u τ]
      rw [hl]
      unfold Formalism.MainNotions.S.uS
      exact ⟨by exact_mod_cast (D.hcW u τ).u_gt_v ⟨i, by omega⟩,
        by exact_mod_cast (D.hcW u τ).v_gt_u ⟨i, by omega⟩⟩
    · intro h
      have hm : 0 < D.R.m := by
        have := D.R.two_le_m
        omega
      have hl : Formalism.MainNotions.S.lamS D.R (D.hc τ) ⟨D.R.k - 1, by omega⟩ =
          -(((D.hcW u τ).b ⟨0, hm⟩ : ℚ) : ℝ) := by
        unfold Formalism.MainNotions.S.lamS
        rw [dite_eq_right (show ¬ (D.R.k - 1 < D.R.k - 1) by omega),
          dite_eq_left (show D.R.k - 1 - (D.R.k - 1) < D.R.m by omega), D.hcW_b u τ]
        exact congrArg (fun q : ℚ => -(q : ℝ)) (hF _ _ _ _ _ (by simp))
      rw [hl]
      unfold Formalism.MainNotions.S.uS
      exact_mod_cast (D.hcW u τ).u_last_gt h hm
  ·
    intro u u' hne τ heq
    have hl : D.s.letter u ≠ D.s.letter u' := fun h => hne (D.s.letter_inj h)
    obtain ⟨⟨j, hj⟩, hjl⟩ := Function.ne_iff.mp hl
    have e := congrFun heq ⟨j + 1, by omega⟩
    simp only [Formalism.MainNotions.S.uS] at e
    have e' : (D.hcW u τ).u ⟨j + 1, by omega⟩ = (D.hcW u' τ).u ⟨j + 1, by omega⟩ := by
      exact_mod_cast e
    rw [D.s.u_letter u τ j hj, D.s.u_letter u' τ j hj, D.hcW_v, D.hcW_v] at e'
    have hQ := D.s.Del_pos
    cases h1 : D.s.letter u ⟨j, hj⟩ <;> cases h2 : D.s.letter u' ⟨j, hj⟩ <;>
      simp only [h1, h2] at e' hjl <;> simp at e' hjl <;> linarith
  ·
    intro u
    exact ⟨hA.1 u, Formalism.MainNotions.S.T_mod D u⟩
  ·
    intro u
    exact Formalism.MainNotions.S.ne_of_mod (hg 0) (hg 1) (Formalism.MainNotions.S.T_mod D u)

end GlobalTheory.Diag.PG

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.DataConditionsOfGlobalAndRealRowsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S GlobalTheory.Diag.PG

theorem _root_.GlobalTheory.T.dataConditions_of_global_and_real_rows : ∀ eps CD : ℝ, 0 < eps → eps < 1 / 52 → 3 ≤ CD → ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (D : D7) (Cg C0 : ℝ), Glob0 D x eps CD Cg → Nodes D x eps → ArithmeticConditionsOfDatum D → DuWin D C0 → StandingNumericalData D C0 := by
  first | exact @GlobalTheory.Diag.PG.data_of_rows | exact GlobalTheory.Diag.PG.data_of_rows | (intros; apply GlobalTheory.Diag.PG.data_of_rows <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.TwoLeRootDiscriminantAndSplitArithmeticCondition

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

namespace GlobalTheory

theorem two_le_rdE_and_arithmeticConditionsS0 : ∀ D : D7, 2 ≤ D.host.rdE ∧ ArithmeticConditionsOfDatum D := fun D =>
  ⟨S.root_discriminant_ge_two _ (UnusedSlot33.ramification_two_and_conjugation_at_q_and_d _),
    fun u => S.splitsCompl_of_ncard _ _ (D.mem u).A.T_prime
      (Formalism.L2.GlobalTheoryTheory.FiltrationCocycleLiftCriterion.split_clause _ Formalism.L2.SG.ResidEvFree.cycSplit_holds _ (D.mem u).A.T_prime (S.level_norm_one_mod_conductor _ u)).2,
    Formalism.L2.SG.ResidEvFree.splitsE_g _ 0, Formalism.L2.SG.ResidEvFree.splitsE_g _ 1, S.discriminant_eq_base_sq _ (UnusedSlot33.ramification_two_and_conjugation_at_q_and_d _)⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.TwoLeRootDiscriminantAndSplitArithmeticConditionStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

theorem _root_.GlobalTheory.T.two_le_rootDiscriminant_and_split_arithmetic_conditions : ∀ D : D7, 2 ≤ D.host.rdE ∧ ArithmeticConditionsOfDatum D := by
  first | exact @GlobalTheory.two_le_rdE_and_arithmeticConditionsS0 | exact GlobalTheory.two_le_rdE_and_arithmeticConditionsS0 | (intros; apply GlobalTheory.two_le_rdE_and_arithmeticConditionsS0 <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiagonalHypothesesOfRowsAndWindow

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S GlobalTheory.Diag.PG

namespace GlobalTheory.Diag.PG

theorem lemmaPG_record : Formalism.HermitianLatticesTheory.SiegelMassRatio → Formalism.L2.SG.Pf.SzHypFD.DsigHC → ∀ eps CD : ℝ, 0 < eps → eps < 1 / 52 → 3 ≤ CD → ∀ C' Cl Cg C : ℝ, 40 ≤ Cl → Cl ≤ CD → ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (D : D7) (large₂ : SizeData₂ D), large₂.sc.L = x ^ eps → 8 * large₂.CGam ≤ C' → Ties D → LocalBesselAndTopKernel.FamilyMidVolume D → Glob0 D x eps CD Cg → Nodes D x eps → DuWin D 3 → AdmissibleBoundsFromSource.hyp D large₂ 3 C' Cl Cg (1 / 4) 3 (1 / 2) (4 * Cg + 13) ∧ Formalism.L2.SG.RowsConc.TFrameAt D ∧ C * large₂.sc.L ≤ (D.R.m : ℝ) - 1 ∧ C ≤ (D.R.k : ℝ) := by
  intro hSM hDs eps CD heps0 heps1 hCD C' Cl Cg C hCl40 hClCD
  have hCl0 : (0 : ℝ) < Cl := by linarith
  obtain ⟨x1, hx1⟩ := GlobalTheory.T.dataConditions_of_global_and_real_rows eps CD heps0 heps1 hCD
  obtain ⟨x2, hx2⟩ := GlobalTheory.T.hypotheses_of_global_rows_and_nodes eps CD heps0 heps1 hCD C' Cl Cg hCl0 hClCD
  obtain ⟨x3, hx3⟩ := GlobalTheory.T.eventually_rankNums_imp_parameter_lower_bounds eps CD heps0 heps1 hCD (max C (3 * Real.exp 8))
  refine ⟨max x1 (max x2 x3), ?_⟩
  intro x hx D large₂ hL hC' hTies hAdm hG hN hW
  have hx1' : x1 ≤ x := le_trans (le_max_left _ _) hx
  have hx2' : x2 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx3' : x3 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx

  obtain ⟨-, hAr⟩ := GlobalTheory.T.two_le_rootDiscriminant_and_split_arithmetic_conditions D
  have hData : StandingNumericalData D 3 := hx1 x hx1' D Cg 3 hG hN hAr hW

  obtain ⟨-, -, -, -, -, hm1, hk, hxe⟩ := hx3 x hx3' _ _ _ _ _ hG.nums
  have hxe0 : (0 : ℝ) ≤ x ^ eps := le_of_lt (lt_trans zero_lt_one hxe)
  have h3 : (3 : ℝ) ≤ max C (3 * Real.exp 8) :=
    le_trans (by have := Real.add_one_le_exp (8 : ℝ); linarith) (le_max_right _ _)
  have hCm : C * large₂.sc.L ≤ (D.R.m : ℝ) - 1 := by
    rw [hL]; exact le_trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hxe0) hm1
  have h3m : 3 * large₂.sc.L ≤ (D.R.m : ℝ) - 1 := by
    rw [hL]; exact le_trans (mul_le_mul_of_nonneg_right h3 hxe0) hm1
  have h3k : 3 * Real.exp 8 ≤ (D.R.k : ℝ) := le_trans (le_max_right _ _) hk
  have hCk : C ≤ (D.R.k : ℝ) := le_trans (le_max_left _ _) hk

  have hLpos : 0 < large₂.sc.L := by rw [hL]; linarith
  have hb1 : 1 < large₂.sc.b := by
    show 1 < Real.exp large₂.sc.L
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr hLpos
  have hb0 : 0 < large₂.sc.b := lt_trans zero_lt_one hb1
  have hm0 : (0 : ℝ) < (D.R.m : ℝ) := by
    have := D.R.two_le_m
    exact_mod_cast (show 0 < D.R.m by omega)
  have hT1 : ∀ u, (1 : ℝ) ≤ Tr D u := fun u => by
    show (1 : ℝ) ≤ ((D.mem u).A.T : ℝ)
    exact_mod_cast (D.mem u).A.T_prime.one_lt.le
  have hmb : (D.R.m : ℝ) * Real.log large₂.sc.b ≠ 0 := (mul_pos hm0 (Real.log_pos hb1)).ne'
  obtain ⟨CT0, hCT0⟩ : ∃ c : ℝ, c * ((D.R.m : ℝ) * Real.log large₂.sc.b) = ∑ v, Real.log (Tr D v) :=
    ⟨(∑ v, Real.log (Tr D v)) / ((D.R.m : ℝ) * Real.log large₂.sc.b), div_mul_cancel₀ _ hmb⟩
  have hwin0 : ∀ u, large₂.sc.b ^ ((0 : ℝ) * (D.R.m : ℝ)) ≤ Tr D u ∧
      Tr D u ≤ large₂.sc.b ^ (CT0 * (D.R.m : ℝ)) := by
    intro u
    refine ⟨by rw [zero_mul, Real.rpow_zero]; exact hT1 u, ?_⟩
    rw [Real.rpow_def_of_pos hb0,
      show Real.log large₂.sc.b * (CT0 * (D.R.m : ℝ)) = CT0 * ((D.R.m : ℝ) * Real.log large₂.sc.b) by ring, hCT0]
    calc Tr D u = Real.exp (Real.log (Tr D u)) :=
          (Real.exp_log (lt_of_lt_of_le zero_lt_one (hT1 u))).symm
      _ ≤ Real.exp (∑ v, Real.log (Tr D v)) :=
          Real.exp_le_exp.mpr (Finset.single_le_sum (fun v _ => Real.log_nonneg (hT1 v))
            (Finset.mem_univ u))

  have hHyp0 : StandingHypotheses D large₂ C' Cl Cg (1 / 4) 3 0 CT0 := hx2 x hx2' D large₂ 0 CT0 hL hC' hG hN hwin0
  have hCnt : Cnt.Hyp0 D large₂ C' Cl Cg (1 / 4) 3 0 CT0 3 :=
    (⟨hHyp0, hData, by norm_num⟩ : StandingHypotheses D large₂ C' Cl Cg (1 / 4) 3 0 CT0 ∧ StandingNumericalData D 3 ∧ (1 : ℝ) ≤ 3)

  have hFr := (GlobalTheory.pgFrame_at_record hSM hDs D large₂ C' Cl Cg (1 / 4) 3 0 CT0 3 hTies hCnt hCl40 h3m h3k hAdm).1
  have hwin := GlobalTheory.T.levelPrimes_size_bounds_columnDimension hSM hDs D large₂ C' Cl Cg (1 / 4) 3 0 CT0 3 hTies hCnt hCl40 h3m h3k hAdm

  have hHyp : StandingHypotheses D large₂ C' Cl Cg (1 / 4) 3 (1 / 2) (4 * Cg + 13) :=
    hx2 x hx2' D large₂ (1 / 2) (4 * Cg + 13) hL hC' hG hN hwin
  exact ⟨(⟨hData, hHyp, by norm_num⟩ :
      StandingNumericalData D 3 ∧ StandingHypotheses D large₂ C' Cl Cg (1 / 4) 3 (1 / 2) (4 * Cg + 13) ∧ (1 : ℝ) ≤ 3), hFr, hCm, hCk⟩

end GlobalTheory.Diag.PG
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiagonalHypothesesOfRowsAndWindowStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S GlobalTheory.Diag.PG

theorem _root_.GlobalTheory.T.diagonal_hypotheses_of_rows_and_window : Formalism.HermitianLatticesTheory.SiegelMassRatio → Formalism.L2.SG.Pf.SzHypFD.DsigHC → ∀ eps CD : ℝ, 0 < eps → eps < 1 / 52 → 3 ≤ CD → ∀ C' Cl Cg C : ℝ, 40 ≤ Cl → Cl ≤ CD → ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (D : D7) (large₂ : SizeData₂ D), large₂.sc.L = x ^ eps → 8 * large₂.CGam ≤ C' → Ties D → LocalBesselAndTopKernel.FamilyMidVolume D → Glob0 D x eps CD Cg → Nodes D x eps → DuWin D 3 → AdmissibleBoundsFromSource.hyp D large₂ 3 C' Cl Cg (1 / 4) 3 (1 / 2) (4 * Cg + 13) ∧ Formalism.L2.SG.RowsConc.TFrameAt D ∧ C * large₂.sc.L ≤ (D.R.m : ℝ) - 1 ∧ C ≤ (D.R.k : ℝ) := by
  first | exact @GlobalTheory.Diag.PG.lemmaPG_record | exact GlobalTheory.Diag.PG.lemmaPG_record | (intros; apply GlobalTheory.Diag.PG.lemmaPG_record <;> assumption)
end
end
