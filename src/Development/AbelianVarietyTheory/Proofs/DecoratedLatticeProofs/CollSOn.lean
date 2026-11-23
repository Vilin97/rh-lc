module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RowsPtAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CollSBound
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CollisionAbsSumBoundOfTwoRowBoundsStatement
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.MinkowskiDividesFactorialOfBound
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsDegF
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsKB
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsNDF
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsNDn
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
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TermTieOf
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsNDF
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsNDn
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsLab
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsND
import Formalism.SharpRestriction.CuspSpanNormBounds.ThresholdCubicInequalitySignPattern

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DegenerateCollisionRowBoundAtParams

section

@[expose] public section

open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.Deg

theorem rowsDeg_at_record : ∀ CT cH cV Ca C2 Ch c C : ℝ, 1 ≤ c → CT ≤ c → |cH| + 2 ≤ c → |cV| + 2 ≤ c → 0 ≤ Ch → c ≤ C → 4 + (c ^ 2 + 2 * max (Ch - c) 0) * (6 * c + 2) ≤ C → 2 * C2 ≤ C → |Ca| ≤ C → ∀ (D : D7) (large₂ : SizeData₂ D) (u : D.what₂.Word) (T : TermTie D) (Z : LoopTie D large₂ T u u 1) (C' Cl Cg cb Cu cT C0 : ℝ), 3 * |C2| ≤ C' → Cnt.Hyp D large₂ u u C' Cl Cg cb Cu cT CT C0 1 → UnitaryVolumeMass.MeanFlagPairCount D large₂ u u C' Cl Cg cb Cu cT CT C0 1 3 c → UnitaryVolumeMass.stHH D large₂ u u C' Cl Cg cb Cu cT CT C0 1 cH → UnitaryVolumeMass.stVol D large₂ T u u 1 Z C' Cl Cg cb Cu cT CT C0 1 cV → AmpAt D large₂ C' Cl Cg cb Cu cT CT C0 (9 * c + 3) Ca C2 Ch 1 → SmallAt D large₂ C' Cl Cg cb Cu cT CT C0 1 → BridgeLemma.TermPtsTie T Z → @BridgeLemma.LatticeDeterminantFactorization D T u u → BridgeLemma₂.wordPairEntriesInLattice T u u → BridgeLemma.RowsDeg T Z C := by
  intro CT cH cV Ca C2 Ch c C k2 hCT k3 k4 hCh hcC hCsq1 hC2 hCa D large₂ u T Z C' Cl Cg cb Cu cT C0 h3C hH hC3 hHH hV hA hS hTP hG0 hE
  have hc0 : 0 ≤ c := by linarith
  have hC1 : 1 ≤ C := k2.trans hcC
  have hCsq : 4 + (c ^ 2 + 2 * max (Ch - c) 0) * (6 * c + 2) ≤ C ^ 2 := by nlinarith
  have hHHc : UnitaryVolumeMass.stHH D large₂ u u C' Cl Cg cb Cu cT CT C0 1 c :=
    BridgeLemma₂.rows_stHH_mono (by linarith [le_abs_self cH]) (by linarith [neg_abs_le cH]) hHH
  have hK := BridgeLemma₂.rows_KBound_of Z hH hHHc k2 hCT
  have hr0 : (0 : ℝ) ≤ D.R.rS := by positivity
  have hm2 : (2 : ℝ) ≤ D.R.m := by rw [BridgeLemma₂.rows_m_cast]; linarith
  have hf1 : (1 : ℝ) ≤ D.R.f := by exact_mod_cast BridgeLemma₂.rows_f_pos D
  have hL1 : 1 ≤ large₂.sc.L := BridgeLemma.d_one_le_L D large₂
  have hkm : (D.R.m : ℝ) + 3 ≤ D.R.k := by exact_mod_cast D.R.m_add_three_le_k
  have hk5 : C' * (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L ≤ D.R.k := hH.1.1.2.1
  have ha2 : |C2| * (D.R.m : ℝ) ^ 2 + |C2| * (D.R.m : ℝ) ^ 4 * 2 ≤ D.R.k := by
    refine le_trans ?_ hk5
    have e1 : (D.R.m : ℝ) ^ 2 ≤ (D.R.m : ℝ) ^ 5 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have e4 : (D.R.m : ℝ) ^ 4 ≤ (D.R.m : ℝ) ^ 5 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have h5 : 0 ≤ (D.R.m : ℝ) ^ 5 := by positivity
    have e2 : (D.R.m : ℝ) ^ 5 ≤ (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L := by
      nlinarith [mul_nonneg h5 (by linarith : 0 ≤ (D.R.f : ℝ) - 1),
        mul_nonneg (mul_nonneg h5 (by linarith : 0 ≤ (D.R.f : ℝ))) (by linarith : 0 ≤ large₂.sc.L - 1)]
    have hab := abs_nonneg C2
    have hP : 0 ≤ (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L := by linarith
    calc |C2| * (D.R.m : ℝ) ^ 2 + |C2| * (D.R.m : ℝ) ^ 4 * 2
        = |C2| * ((D.R.m : ℝ) ^ 2 + 2 * (D.R.m : ℝ) ^ 4) := by ring
      _ ≤ |C2| * (3 * ((D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L)) :=
          mul_le_mul_of_nonneg_left (by linarith) hab
      _ = (3 * |C2|) * ((D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L) := by ring
      _ ≤ C' * ((D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L) := mul_le_mul_of_nonneg_right h3C hP
      _ = C' * (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L := by ring
  obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = 4 * (c * D.R.k) + 4 * BridgeLemma₂.pairCountExponent D c D.R.k +
    4 * (c * (D.R.rS : ℝ) ^ 2) + (|C2| * (D.R.m : ℝ) ^ 2 + |C2| * (D.R.m : ℝ) ^ 4 * 2) / 2 +
    12 * ((D.R.rS : ℝ) + 1) ^ 2 := ⟨_, rfl⟩
  have ha0 : 0 ≤ a := by
    rw [hadef]
    have := BridgeLemma₂.pairCountExponent_nonneg D hc0 D.R.k
    positivity
  have hqb := BridgeLemma₂.rows_q_bound (m := D.R.m) (k := D.R.k) (r := D.R.rS) (c := c)
    (cf := Cnt.cF D.R.f) (a2 := |C2| * (D.R.m : ℝ) ^ 2 + |C2| * (D.R.m : ℝ) ^ 4 * 2)
    (BridgeLemma₂.rows_m_cast _) hr0 hkm hc0 (BridgeLemma₂.rows_cF_le hH) ha2
  have hqb' : ((D.R.rS : ℝ) + 1) * a + 1 ≤ (9 * c + 3) * D.R.k * (D.R.m : ℝ) ^ 2 := by
    rw [hadef]; unfold BridgeLemma₂.pairCountExponent; exact hqb
  have hra0 : 0 ≤ ((D.R.rS : ℝ) + 1) * a := by positivity
  have hyp : BridgeLemma₂.rows_Hyps Z C' Cl Cg cb Cu cT CT C0 1 c (9 * c + 3) Ca C2 Ch 1 1
      ⌈((D.R.rS : ℝ) + 1) * a⌉₊ :=
    { hH := hH
      hC3 := hC3
      hHH := hHHc
      hV := BridgeLemma₂.rows_stVol_mono _ (by linarith [le_abs_self cV]) (by linarith [neg_abs_le cV]) hV
      hDEC := hA.2.2
      ha := hS.1
      hb := hS.2.1
      hp := hA.1
      hpp := hA.2.1
      h6 := hS.2.2.1
      hδ := zero_le_one
      hThA := BridgeLemma.word_theorem_a_admissible D u u
      hT := hTP
      hG0 := hG0
      hE := hE
      hc := hc0
      hCh := hCh
      hdim := BridgeLemma₂.rows_dim_pos Z hH.1 (hS.2.2.2.2 hH.1 u)
      hq := by linarith [(Nat.ceil_lt_add_one hra0).le] }
  refine BridgeLemma₂.rows_RowsDeg_record _ hyp hK k2 hcC hC1 hCsq hC2 hCa ?_
  rw [le_div_iff₀ (by positivity)]
  have h1 := Nat.le_ceil (((D.R.rS : ℝ) + 1) * a)
  have h2 : (C2 * (D.R.m : ℝ) ^ 2 + C2 * (D.R.m : ℝ) ^ 4 * 2) / 2 ≤
      (|C2| * (D.R.m : ℝ) ^ 2 + |C2| * (D.R.m : ℝ) ^ 4 * 2) / 2 := by
    have := le_abs_self C2
    gcongr
  calc _ ≤ a * ((D.R.rS : ℝ) + 1) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        rw [hadef]; linarith
    _ = ((D.R.rS : ℝ) + 1) * a := by ring
    _ ≤ _ := h1

end GlobalTheory.Core.Deg
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DegenerateCollisionRowBoundAtParametersStatement

section

@[expose] public section

open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.degenerateCollision_rowBound_at_sizeData : ∀ CT cH cV Ca C2 Ch c C : ℝ, 1 ≤ c → CT ≤ c → |cH| + 2 ≤ c → |cV| + 2 ≤ c → 0 ≤ Ch → c ≤ C → 4 + (c ^ 2 + 2 * max (Ch - c) 0) * (6 * c + 2) ≤ C → 2 * C2 ≤ C → |Ca| ≤ C → ∀ (D : D7) (large₂ : SizeData₂ D) (u : D.what₂.Word) (T : TermTie D) (Z : LoopTie D large₂ T u u 1) (C' Cl Cg cb Cu cT C0 : ℝ), 3 * |C2| ≤ C' → Cnt.Hyp D large₂ u u C' Cl Cg cb Cu cT CT C0 1 → UnitaryVolumeMass.MeanFlagPairCount D large₂ u u C' Cl Cg cb Cu cT CT C0 1 3 c → UnitaryVolumeMass.stHH D large₂ u u C' Cl Cg cb Cu cT CT C0 1 cH → UnitaryVolumeMass.stVol D large₂ T u u 1 Z C' Cl Cg cb Cu cT CT C0 1 cV → AmpAt D large₂ C' Cl Cg cb Cu cT CT C0 (9 * c + 3) Ca C2 Ch 1 → SmallAt D large₂ C' Cl Cg cb Cu cT CT C0 1 → BridgeLemma.TermPtsTie T Z → @BridgeLemma.LatticeDeterminantFactorization D T u u → BridgeLemma₂.wordPairEntriesInLattice T u u → BridgeLemma.RowsDeg T Z C := by
  first | exact @GlobalTheory.Core.Deg.rowsDeg_at_record | exact GlobalTheory.Core.Deg.rowsDeg_at_record | (intros; apply GlobalTheory.Core.Deg.rowsDeg_at_record <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NondegenerateCollisionRowBoundAtParameters

section

@[expose] public section

open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.Deg

section SlopeTestRemainingChoices
open Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticeCounting Formalism.MainNotions.BridgeLemma Formalism.MainNotions.BridgeLemma₂

theorem rowsND_one_record : ∀ CT cH cV Ca C2 Ch c C : ℝ, 1 ≤ c → |cH| + 2 ≤ c → |cV| + 2 ≤ c → 0 ≤ Ch → c ≤ C → 4 + (c ^ 2 + 2 * max (Ch - c) 0) * (6 * c + 2) ≤ C → ∀ (D : D7) (large₂ : SizeData₂ D) (u : D.what₂.Word) (T : TermTie D) (Z : LoopTie D large₂ T u u 1) (C' Cl Cg cb Cu cT C0 : ℝ), |C2| ≤ C' → Cnt.Hyp D large₂ u u C' Cl Cg cb Cu cT CT C0 1 → UnitaryVolumeMass.MeanFlagPairCount D large₂ u u C' Cl Cg cb Cu cT CT C0 1 3 c → UnitaryVolumeMass.stHH D large₂ u u C' Cl Cg cb Cu cT CT C0 1 cH → UnitaryVolumeMass.stVol D large₂ T u u 1 Z C' Cl Cg cb Cu cT CT C0 1 cV → AmpAt D large₂ C' Cl Cg cb Cu cT CT C0 (9 * c + 3) Ca C2 Ch 1 → SmallAt D large₂ C' Cl Cg cb Cu cT CT C0 1 → BridgeLemma.TermPtsTie T Z → @BridgeLemma.LatticeDeterminantFactorization D T u u → BridgeLemma₂.wordPairEntriesInLattice T u u → BridgeLemma.RowsND T Z C := by
  intro CT cH cV Ca C2 Ch c C hc1 hcH hcV hCh hcC hCC D large₂ u T Z C' Cl Cg cb Cu cT C0 hC2 hH hC3 hHH hVol hAmp hSm
    hTP hG0 hE
  have hc0 : 0 ≤ c := by linarith
  have hC1 : 1 ≤ C := hc1.trans hcC
  have hCsq : 4 + (c ^ 2 + 2 * max (Ch - c) 0) * (6 * c + 2) ≤ C ^ 2 := by nlinarith
  have hr0 : (0 : ℝ) ≤ D.R.rS := by positivity
  have hm2 : (2 : ℝ) ≤ D.R.m := by rw [rows_m_cast]; linarith
  have hf1 : (1 : ℝ) ≤ D.R.f := by exact_mod_cast rows_f_pos D
  have hL1 := d_one_le_L D large₂
  have hkm : (D.R.m : ℝ) + 3 ≤ D.R.k := by exact_mod_cast D.R.m_add_three_le_k
  have hk5 : C' * (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L ≤ D.R.k := hH.1.1.2.1
  have ha2 : |C2| * (D.R.m : ℝ) ^ 2 ≤ D.R.k := by
    refine le_trans ?_ hk5
    have hC'0 : 0 ≤ C' := (abs_nonneg C2).trans hC2
    have e1 : (D.R.m : ℝ) ^ 2 ≤ (D.R.m : ℝ) ^ 5 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have e2 : (D.R.m : ℝ) ^ 5 ≤ (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L := by
      have h5 : 0 ≤ (D.R.m : ℝ) ^ 5 := by positivity
      nlinarith [mul_nonneg h5 (by linarith : 0 ≤ (D.R.f : ℝ) - 1),
        mul_nonneg (mul_nonneg h5 (by linarith : 0 ≤ (D.R.f : ℝ))) (by linarith : 0 ≤ large₂.sc.L - 1)]
    have e3 : 0 ≤ (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L := by positivity
    calc |C2| * (D.R.m : ℝ) ^ 2 ≤ C' * ((D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L) :=
          mul_le_mul hC2 (e1.trans e2) (by positivity) hC'0
      _ = C' * (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L := by ring
  obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = 4 * (c * D.R.k) + 4 * pairCountExponent D c D.R.k +
    4 * (c * (D.R.rS : ℝ) ^ 2) + |C2| * (D.R.m : ℝ) ^ 2 / 2 + 12 * ((D.R.rS : ℝ) + 1) ^ 2 := ⟨_, rfl⟩
  have ha0 : 0 ≤ a := by
    rw [hadef]
    have := pairCountExponent_nonneg D hc0 D.R.k
    positivity
  have hqb := rows_q_bound (m := D.R.m) (k := D.R.k) (r := D.R.rS) (c := c)
    (cf := cF D.R.f) (a2 := |C2| * (D.R.m : ℝ) ^ 2) (rows_m_cast _) hr0 hkm hc0 (rows_cF_le hH) ha2
  have hqb' : ((D.R.rS : ℝ) + 1) * a + 1 ≤ (9 * c + 3) * D.R.k * (D.R.m : ℝ) ^ 2 := by
    rw [hadef]; unfold pairCountExponent; exact hqb
  have hra0 : 0 ≤ ((D.R.rS : ℝ) + 1) * a := by positivity
  have hyp : rows_Hyps Z C' Cl Cg cb Cu cT CT C0 1 c (9 * c + 3) Ca C2 Ch 1 1
      ⌈((D.R.rS : ℝ) + 1) * a⌉₊ :=
    { hH := hH
      hC3 := hC3
      hHH := rows_stHH_mono (by linarith [le_abs_self cH]) (by linarith [neg_abs_le cH]) hHH
      hV := rows_stVol_mono _ (by linarith [le_abs_self cV]) (by linarith [neg_abs_le cV]) hVol
      hDEC := hAmp.2.2
      ha := hSm.1
      hb := hSm.2.1
      hp := hAmp.1
      hpp := hAmp.2.1
      h6 := hSm.2.2.1
      hδ := zero_le_one
      hThA := word_theorem_a_admissible D u u
      hT := hTP
      hG0 := hG0
      hE := hE
      hc := hc0
      hCh := hCh
      hdim := rows_dim_pos Z hH.1 (hSm.2.2.2.2 hH.1 u)
      hq := by linarith [(Nat.ceil_lt_add_one hra0).le] }
  refine rows_RowsND_record _ hyp le_rfl hcC hC1 hCsq ?_
  rw [le_div_iff₀ (by positivity)]
  have h1 := Nat.le_ceil (((D.R.rS : ℝ) + 1) * a)
  have h2 : C2 * (D.R.m : ℝ) ^ 2 / 2 ≤ |C2| * (D.R.m : ℝ) ^ 2 / 2 := by
    have := le_abs_self C2
    gcongr
  calc _ ≤ a * ((D.R.rS : ℝ) + 1) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        rw [hadef]; linarith
    _ = ((D.R.rS : ℝ) + 1) * a := by ring
    _ ≤ _ := h1

end SlopeTestRemainingChoices

end GlobalTheory.Core.Deg
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NondegenerateCollisionRowBoundAtParametersStatement

section

@[expose] public section

open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.nondegenerateCollision_rowBound_at_parameters : ∀ CT cH cV Ca C2 Ch c C : ℝ, 1 ≤ c → |cH| + 2 ≤ c → |cV| + 2 ≤ c → 0 ≤ Ch → c ≤ C → 4 + (c ^ 2 + 2 * max (Ch - c) 0) * (6 * c + 2) ≤ C → ∀ (D : D7) (large₂ : SizeData₂ D) (u : D.what₂.Word) (T : TermTie D) (Z : LoopTie D large₂ T u u 1) (C' Cl Cg cb Cu cT C0 : ℝ), |C2| ≤ C' → Cnt.Hyp D large₂ u u C' Cl Cg cb Cu cT CT C0 1 → UnitaryVolumeMass.MeanFlagPairCount D large₂ u u C' Cl Cg cb Cu cT CT C0 1 3 c → UnitaryVolumeMass.stHH D large₂ u u C' Cl Cg cb Cu cT CT C0 1 cH → UnitaryVolumeMass.stVol D large₂ T u u 1 Z C' Cl Cg cb Cu cT CT C0 1 cV → AmpAt D large₂ C' Cl Cg cb Cu cT CT C0 (9 * c + 3) Ca C2 Ch 1 → SmallAt D large₂ C' Cl Cg cb Cu cT CT C0 1 → BridgeLemma.TermPtsTie T Z → @BridgeLemma.LatticeDeterminantFactorization D T u u → BridgeLemma₂.wordPairEntriesInLattice T u u → BridgeLemma.RowsND T Z C := by
  first | exact @GlobalTheory.Core.Deg.rowsND_one_record | exact GlobalTheory.Core.Deg.rowsND_one_record | (intros; apply GlobalTheory.Core.Deg.rowsND_one_record <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CollSOn

section

@[expose] public section

open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Deg

theorem collS_on : Formalism.HermitianLatticesTheory.SiegelMassRatio → ∀ S : Set ℝ, AmpOn S → CountBoundOn S → SmallOn S → TieOn S → On S CollS := by
  intro hSMR S hAmp hCnt hSmall hTie
  intro Cg cb Cu cT CT hcb hcT
  obtain ⟨c3, cH, thr1, hC⟩ := hCnt Cg cb Cu cT CT
  obtain ⟨cV, thr2, hT⟩ := hTie Cg cb Cu cT CT
  obtain ⟨Ca, C2, Ch, -, hCh, hA⟩ := hAmp Cg cb Cu cT CT hcb hcT
  set c : ℝ := max (max (max (max c3 1) CT) (|cH| + 2)) (|cV| + 2) with hc
  have hc3 : c3 ≤ c := le_trans (le_trans (le_max_left _ _) (le_max_left _ _))
    (le_trans (le_max_left _ _) (le_max_left _ _))
  have hc1 : 1 ≤ c := le_trans (le_trans (le_max_right _ _) (le_max_left _ _))
    (le_trans (le_max_left _ _) (le_max_left _ _))
  have hcT' : CT ≤ c := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hcH : |cH| + 2 ≤ c := le_trans (le_max_right _ _) (le_max_left _ _)
  have hcV : |cV| + 2 ≤ c := le_max_right _ _
  set C : ℝ := max (max (max (max (max c (4 + (c ^ 2 + 2 * max (Ch - c) 0) * (6 * c + 2))) (2 * C2)) |Ca|)
    (408 * (Real.exp 1 * Real.pi))) CT with hCdef
  have hCc : c ≤ C := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_trans (le_max_left _ _)
    (le_trans (le_max_left _ _) (le_max_left _ _))))
  have hC4 : 4 + (c ^ 2 + 2 * max (Ch - c) 0) * (6 * c + 2) ≤ C := le_trans (le_max_right _ _)
    (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _))))
  have hC2 : 2 * C2 ≤ C := le_trans (le_max_right _ _) (le_trans (le_max_left _ _)
    (le_trans (le_max_left _ _) (le_max_left _ _)))
  have hCa : |Ca| ≤ C := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hC408 : 408 * (Real.exp 1 * Real.pi) ≤ C := le_trans (le_max_right _ _) (le_max_left _ _)
  have hCT : CT ≤ C := le_max_right _ _
  obtain ⟨thr3, hA3⟩ := hA (9 * c + 3) 1 one_pos
  obtain ⟨thr4, hS⟩ := hSmall Cg cb Cu cT CT 1 hcb hcT one_pos
  obtain ⟨thr5, hsum⟩ := GlobalTheory.T.collisionAbsSum_bound_of_two_rowBounds hSMR CT C hC408 hCT
  refine ⟨max (max (max (max (max thr1 thr2) thr3) thr4) thr5) (max (3 * |C2|) 4), ?_⟩
  intro C0 hC0 C' Cl hC' hCl D large₂ X Y hF hI u hCG hTies hadm hH0 hConc hAbs
  have hle : ∀ {x : ℝ}, max (max (max (max (max thr1 thr2) thr3) thr4) thr5) (max (3 * |C2|) 4) ≤ x →
      thr1 ≤ x ∧ thr2 ≤ x ∧ thr3 ≤ x ∧ thr4 ≤ x ∧ thr5 ≤ x ∧ 3 * |C2| ≤ x ∧ 4 ≤ x := by
    intro x hx
    simp only [max_le_iff] at hx
    exact ⟨hx.1.1.1.1.1, hx.1.1.1.1.2, hx.1.1.1.2, hx.1.1.2, hx.1.2, hx.2.1, hx.2.2⟩
  obtain ⟨h1', h2', h3', h4', h5', h6', h7'⟩ := hle hC'
  obtain ⟨h1l, h2l, h3l, h4l, h5l, -, h7l⟩ := hle hCl
  have hCnt' := hC C0 hC0 C' Cl h1' h1l D large₂ u
  have hc3' := hCnt'.1 c hc3
  obtain ⟨T, Z, hTA, hVol⟩ := hT C0 hC0 C' Cl h2' h2l D large₂ X Y hF hI u hTies hH0 hConc
  have hAmpAt := hA3 C0 hC0 C' Cl h3' h3l D large₂ hCG hTies hadm hConc.2.2.2.2.2.2.2
  have hSm := hS C0 hC0 C' Cl h4' h4l D large₂ hTies hadm
  have hHyp : Cnt.Hyp D large₂ u u C' Cl Cg cb Cu cT CT C0 1 :=
    Formalism.MainNotions.count_hypotheses_diagonal_words D large₂ C' Cl Cg cb Cu cT CT C0 1 hH0.2.1 hH0.1 hH0.2.2 (by linarith) (by linarith) le_rfl u
  have hC2' : |C2| ≤ C' := by have := abs_nonneg C2; linarith
  have hDeg := GlobalTheory.T.degenerateCollision_rowBound_at_sizeData CT cH cV Ca C2 Ch c C hc1 hcT' hcH hcV hCh hCc hC4 hC2 hCa D large₂ u T Z C' Cl Cg cb Cu cT C0
    h6' hHyp hc3' hCnt'.2 hVol hAmpAt hSm hTA.2.2.2.1 hTA.2.2.2.2.1 hTA.2.2.2.2.2.1
  have hND := GlobalTheory.T.nondegenerateCollision_rowBound_at_parameters CT cH cV Ca C2 Ch c C hc1 hcH hcV hCh hCc hC4 D large₂ u T Z C' Cl Cg cb Cu cT C0
    hC2' hHyp hc3' hCnt'.2 hVol hAmpAt hSm hTA.2.2.2.1 hTA.2.2.2.2.1 hTA.2.2.2.2.2.1
  exact hsum D large₂ X Y hF hI u T Z C' Cl Cg cb Cu cT C0 h5' h5l hH0 hConc hAbs hTA (hSm.2.2.2.2 hH0 u) hND hDeg

end GlobalTheory.Core.Deg
end
end
