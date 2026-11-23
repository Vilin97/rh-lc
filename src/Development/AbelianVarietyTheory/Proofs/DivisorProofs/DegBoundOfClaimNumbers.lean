module

public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LevelCarrying
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCoprimeOfNatCast
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRightActFunPull
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Definitions.Divisors.Multiplier
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertSamuelDegreeRatioLowerBoundRearranged

section

@[expose] public section

namespace GlobalTheory.CovNum

open Formalism.NormVectorIdentities.Items

theorem hsLogRho_bounds (D : ℕ) (n Λ δ h l₀ : ℝ) (hD : 1 ≤ D) (hn : 1 ≤ n) (hΛ : 1 ≤ Λ)
    (hδ : 1 ≤ δ)
    (hl : Real.log Λ + 26 * Real.log (n * D * δ * (1 + Real.log Λ)) ≤ l₀) :
    0 ≤ hsLogRho 26 n D 1 Λ δ h ∧
      hsLogRho 26 n D 1 Λ δ h ≤ l₀ + 26 * Real.log (2 + |h|) := by
  have hD' : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hL : 0 ≤ Real.log Λ := Real.log_nonneg hΛ
  have hh : 0 ≤ |h| := abs_nonneg h
  have h1 : 1 ≤ n * D * δ :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hn hD') hδ
  have h2 : 1 ≤ n * D * δ * (2 + |h| + Real.log Λ) :=
    one_le_mul_of_one_le_of_one_le h1 (by linarith)
  have h3 : n * D * δ * (2 + |h| + Real.log Λ)
      ≤ (n * D * δ * (1 + Real.log Λ)) * (2 + |h|) := by
    rw [mul_assoc (n * D * δ)]
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    nlinarith [mul_nonneg hL hh]
  have h4 : Real.log (n * D * δ * (2 + |h| + Real.log Λ))
      ≤ Real.log (n * D * δ * (1 + Real.log Λ)) + Real.log (2 + |h|) := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    exact Real.log_le_log (by linarith) h3
  have h5 := Real.log_nonneg h2
  unfold hsLogRho
  rw [mul_one]
  constructor <;> linarith

theorem deg_lower_of_claim : ∀ (T D : ℕ) (n Λ β ΛD ΛT J δ h d deg z l₀ : ℝ), 1 ≤ T → 1 ≤ D → 1 ≤ n → 1 ≤ Λ → 1 ≤ β → 1 ≤ ΛD → 1 ≤ ΛT → 1 ≤ δ → 0 < d → 0 ≤ z → z ≤ 1 / 2 → (1 - z) * d ≤ ((T - 1).choose D : ℕ) * δ → Real.log Λ + 26 * Real.log (n * D * δ * (1 + Real.log Λ)) ≤ l₀ → Formalism.NormVectorIdentities.Items.HSClaimS 26 T D n 1 Λ β ΛD ΛT J δ h d deg → ((T - 1).choose D : ℕ) * δ * (T * h - 3 * (D + 1) * |h| - 26 * (26 * D ^ 2 + 2 * z * T) * Real.log (2 + |h|) - (J + 26 * D ^ 2 * (l₀ + Real.log T) + (T + D + 1) * Real.log β + (T + D ^ 2) * (Formalism.NormVectorIdentities.Items.hsG D n + 2) + 2 * z * (T * (Real.log 2 + l₀ + Real.log β / 2) + Real.log ΛD + Real.log ΛT))) ≤ deg := by
  intro T D n Λ β ΛD ΛT J δ h d deg z l₀ hT hD hn hΛ hβ hΛD hΛT hδ hd hz hz2 hP hl hc
  obtain ⟨hρ0, hρ⟩ := hsLogRho_bounds D n Λ δ h l₀ hD hn hΛ hδ hl
  obtain ⟨-, -, hc⟩ := hc
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hβ0 : 0 < β := by linarith
  have e1 : Real.log (Real.exp (hsLogRho 26 n D 1 Λ δ h) * T)
      = hsLogRho 26 n D 1 Λ δ h + Real.log T := by
    rw [Real.log_mul (Real.exp_pos _).ne' (by positivity), Real.log_exp]
  have e2 : Real.log (2 * Real.exp (hsLogRho 26 n D 1 Λ δ h) * Real.sqrt β)
      = Real.log 2 + hsLogRho 26 n D 1 Λ δ h + Real.log β / 2 := by
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp, Real.log_sqrt hβ0.le]
  rw [e1, e2, le_div_iff₀ hd] at hc
  unfold hsZ hsR at hc
  generalize hsLogRho 26 n D 1 Λ δ h = ρ at hρ0 hρ hc
  generalize ((Nat.choose (T - 1) D : ℕ) : ℝ) * δ = P at hP hc ⊢
  generalize hsG D n = g at hc ⊢
  have hb := Real.log_nonneg hβ
  have hLD := Real.log_nonneg hΛD
  have hLT := Real.log_nonneg hΛT
  have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  generalize Real.log (2 + |h|) = L at hρ ⊢
  have hdP : d ≤ 2 * P := by nlinarith
  have hP0 : 0 ≤ P := by linarith
  have hdef : d - P ≤ 2 * z * P := by nlinarith
  set A := (T : ℝ) * h - 3 * ((D : ℝ) + 1) * |h| - J - 26 * (D : ℝ) ^ 2 * (ρ + Real.log T)
    - ((T : ℝ) + D + 1) * Real.log β - ((T : ℝ) + (D : ℝ) ^ 2) * (g + 2) with hA
  set B := (T : ℝ) * (Real.log 2 + ρ + Real.log β / 2) + Real.log ΛD + Real.log ΛT with hB
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have e3 : ((1 - (1 - P / d)) * A - (1 - P / d) * B) * d = P * A - (d - P) * B := by
    field_simp
    ring
  rw [e3] at hc
  have h6 : (d - P) * B ≤ 2 * z * P * B := mul_le_mul_of_nonneg_right hdef hB0
  have h7 : 0 ≤ (26 * (D : ℝ) ^ 2 + 2 * z * T) * (l₀ + 26 * L - ρ) :=
    mul_nonneg (by positivity) (by linarith)
  have h8 : P * (A - 2 * z * B - (26 * (D : ℝ) ^ 2 + 2 * z * T) * (l₀ + 26 * L - ρ))
      ≤ P * (A - 2 * z * B) := mul_le_mul_of_nonneg_left (by linarith) hP0
  refine le_trans (le_of_eq ?_) (h8.trans (by linarith))
  rw [hA, hB]
  ring

end GlobalTheory.CovNum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertSamuelDegreeRatioLowerBoundRearrangedStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

theorem _root_.GlobalTheory.T.hilbertSamuel_degree_ratio_lower_bound_rearranged : ∀ (T D : ℕ) (n Λ β ΛD ΛT J δ h d deg z l₀ : ℝ), 1 ≤ T → 1 ≤ D → 1 ≤ n → 1 ≤ Λ → 1 ≤ β → 1 ≤ ΛD → 1 ≤ ΛT → 1 ≤ δ → 0 < d → 0 ≤ z → z ≤ 1 / 2 → (1 - z) * d ≤ ((T - 1).choose D : ℕ) * δ → Real.log Λ + 26 * Real.log (n * D * δ * (1 + Real.log Λ)) ≤ l₀ → Formalism.NormVectorIdentities.Items.HSClaimS 26 T D n 1 Λ β ΛD ΛT J δ h d deg → ((T - 1).choose D : ℕ) * δ * (T * h - 3 * (D + 1) * |h| - 26 * (26 * D ^ 2 + 2 * z * T) * Real.log (2 + |h|) - (J + 26 * D ^ 2 * (l₀ + Real.log T) + (T + D + 1) * Real.log β + (T + D ^ 2) * (Formalism.NormVectorIdentities.Items.hsG D n + 2) + 2 * z * (T * (Real.log 2 + l₀ + Real.log β / 2) + Real.log ΛD + Real.log ΛT))) ≤ deg := by
  first | exact @GlobalTheory.CovNum.deg_lower_of_claim | exact GlobalTheory.CovNum.deg_lower_of_claim | (intros; apply GlobalTheory.CovNum.deg_lower_of_claim <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegBoundOfClaimNumbers

section

@[expose] public section

namespace GlobalTheory.CovHSNum



theorem deg_bound_of_claim_numbers : ∀ (T D : ℕ) (PP kap b z ρ n Λ β ΛD ΛT J δ h d deg degM c : ℝ), 1 ≤ D → 3 * D + 5 ≤ T → 1 ≤ PP → 1 ≤ b → Real.log b ≤ PP → (T : ℝ) * PP ≤ Real.sqrt b → z = 7 * ((D : ℝ) ^ 2 / T + D * ρ) → 0 ≤ ρ → z ≤ 1 / 2 → z * (PP * kap) ≤ b → 0 ≤ kap → 1 ≤ n → 1 ≤ Λ → 1 ≤ β → 1 ≤ ΛD → 1 ≤ ΛT → 1 ≤ δ → 0 < d → Real.log n ≤ PP → Real.log β ≤ PP → Real.log δ ≤ PP → Real.log Λ ≤ PP * (kap / T + 1) → Real.log ΛD ≤ PP * kap → Real.log ΛT ≤ PP * kap → J ≤ 4 * (D * PP * (kap / T + 1) + T * PP) + 2 * PP * (kap / T) * D → (1 - z) * d ≤ ((T - 1).choose D : ℕ) * δ → Formalism.NormVectorIdentities.Items.HSClaimS 26 T D n 1 Λ β ΛD ΛT J δ h d deg → 0 ≤ c → deg - d * c ≤ degM → ((T - 1).choose D : ℕ) * δ * ((T : ℝ) * h - 3 * ((D : ℝ) + 1) * |h| - 26 * (26 * (D : ℝ) ^ 2 + 2 * z * T) * Real.log (2 + |h|) - (4000 * b + 2 * c)) ≤ degM := by
  intro T D PP kap b z ρ n Λ β ΛD ΛT J δ h d deg degM c hD1 hDT hPP hb hlogb hTPP hz hρ hz2 hzk hkap hn hΛ hβ hΛD hΛT hδ hd hlogn hlogβ hlogδ hlogΛ hlogΛD hlogΛT hJ hcmp hclaim hc hdeg
  have hT8 : (8:ℝ) ≤ T := by exact_mod_cast (by omega : 8 ≤ T)
  have hD1r : (1:ℝ) ≤ D := by exact_mod_cast hD1
  have hDTr : (D:ℝ) + 1 ≤ T := by exact_mod_cast (by omega : D + 1 ≤ T)
  have hTpos : (0:ℝ) < T := by linarith
  have hT0 : (T:ℝ) ≠ 0 := hTpos.ne'

  have hs0 : 0 ≤ Real.sqrt b := Real.sqrt_nonneg b
  have hs2 : Real.sqrt b ^ 2 = b := Real.sq_sqrt (by linarith)
  have hs1 : 1 ≤ Real.sqrt b := by
    have := Real.sqrt_le_sqrt (show (1:ℝ) ≤ b from hb)
    rwa [Real.sqrt_one] at this
  have hsb : Real.sqrt b ≤ b := by nlinarith [mul_le_mul_of_nonneg_left hs1 hs0]
  have hTPPb : (T:ℝ) * PP ≤ b := le_trans hTPP hsb
  have hTPP0 : 0 ≤ (T:ℝ) * PP := by positivity
  have hTPP2 : ((T:ℝ) * PP) ^ 2 ≤ b := by
    calc ((T:ℝ) * PP) ^ 2 ≤ (Real.sqrt b) ^ 2 := pow_le_pow_left₀ hTPP0 hTPP 2
      _ = b := hs2
  have hTs : (T:ℝ) ≤ Real.sqrt b := le_trans (by nlinarith) hTPP
  have hlogT : Real.log T ≤ PP / 2 := by
    have := Real.log_le_log hTpos hTs
    rw [Real.log_sqrt (by linarith)] at this
    linarith
  have hlogD : Real.log D ≤ Real.log T := Real.log_le_log (by linarith) (by linarith)
  have hlogΛ0 : 0 ≤ Real.log Λ := Real.log_nonneg hΛ
  have hlogβ0 : 0 ≤ Real.log β := Real.log_nonneg hβ
  have hlogn0 : 0 ≤ Real.log n := Real.log_nonneg hn
  have hlog1 : Real.log (1 + Real.log Λ) ≤ Real.log Λ := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + Real.log Λ by linarith)
    linarith
  have hprod : Real.log (n * D * δ * (1 + Real.log Λ)) =
      Real.log n + Real.log D + Real.log δ + Real.log (1 + Real.log Λ) := by
    have h1 : (0:ℝ) < n := by linarith
    have h2 : (0:ℝ) < D := by linarith
    have h3 : (0:ℝ) < δ := by linarith
    have h4 : (0:ℝ) < 1 + Real.log Λ := by linarith
    rw [Real.log_mul (mul_pos (mul_pos h1 h2) h3).ne' h4.ne',
      Real.log_mul (mul_pos h1 h2).ne' h3.ne', Real.log_mul h1.ne' h2.ne']

  have hD2T0 : 0 ≤ (D:ℝ) ^ 2 / T := by positivity
  have hDρ : 0 ≤ (D:ℝ) * ρ := mul_nonneg (by positivity) hρ
  have hz0 : 0 ≤ z := by rw [hz]; linarith
  have hD2z : (D:ℝ) ^ 2 ≤ z * T / 7 := by
    have e : z * T / 7 = (D:ℝ) ^ 2 + D * ρ * T := by rw [hz]; field_simp
    rw [e]; have := mul_nonneg hDρ hTpos.le; linarith
  have hD2T : (D:ℝ) ^ 2 ≤ T / 14 := by nlinarith [mul_le_mul_of_nonneg_right hz2 hTpos.le]

  have hq0 : 0 ≤ kap / T := div_nonneg hkap hTpos.le
  obtain ⟨q, hq⟩ : ∃ q : ℝ, kap / T = q := ⟨_, rfl⟩
  have hkq : kap = q * T := by rw [← hq]; field_simp
  rw [hq] at hlogΛ hJ hq0
  rw [hkq] at hzk hlogΛD hlogΛT
  clear hq hkq hkap
  have hl0 : Real.log Λ + 26 * Real.log (n * D * δ * (1 + Real.log Λ)) ≤
      27 * (PP * (q + 1)) + 65 * PP := by
    rw [hprod]; linarith
  have key := GlobalTheory.T.hilbertSamuel_degree_ratio_lower_bound_rearranged T D n Λ β ΛD ΛT J δ h d deg z (27 * (PP * (q + 1)) + 65 * PP)
    (by omega) hD1 hn hΛ hβ hΛD hΛT hδ hd hz0 hz2 hcmp hl0 hclaim

  have hPPq : 0 ≤ PP * q := mul_nonneg (by linarith) hq0
  have F1 : (D:ℝ) ^ 2 * (PP * q) ≤ b / 7 := by
    linarith [mul_le_mul_of_nonneg_right hD2z hPPq]
  have F2 : (D:ℝ) ^ 2 * PP ≤ b / 14 := by
    linarith [mul_le_mul_of_nonneg_right hD2T (show (0:ℝ) ≤ PP by linarith)]
  have hDD2 : (D:ℝ) ≤ (D:ℝ) ^ 2 := by nlinarith
  have hDPPq : (D:ℝ) * (PP * q) ≤ b / 7 := by
    linarith [mul_le_mul_of_nonneg_right hDD2 hPPq]
  have hDPP : (D:ℝ) * PP ≤ b := by
    linarith [mul_le_mul_of_nonneg_right (show (D:ℝ) ≤ T by linarith) (show (0:ℝ) ≤ PP by linarith)]
  have t1 : J ≤ 9 * b := by linarith
  have hDlogT : (D:ℝ) ^ 2 * Real.log T ≤ (D:ℝ) ^ 2 * (PP / 2) :=
    mul_le_mul_of_nonneg_left hlogT (sq_nonneg _)
  have t2 : 26 * (D:ℝ) ^ 2 * ((27 * (PP * (q + 1)) + 65 * PP) + Real.log T) ≤ 300 * b := by
    linarith
  have t3 : ((T:ℝ) + D + 1) * Real.log β ≤ 2 * b := by
    have := mul_le_mul (show (T:ℝ) + D + 1 ≤ 2 * T by linarith) hlogβ hlogβ0 (by linarith)
    linarith
  have hG : Formalism.NormVectorIdentities.Items.hsG D n + 2 ≤ 5 * D * PP := by
    unfold Formalism.NormVectorIdentities.Items.hsG
    have a1 := mul_le_mul_of_nonneg_left hlogn (show (0:ℝ) ≤ D + 1 by linarith)
    have a2 := mul_le_mul_of_nonneg_left hPP (show (0:ℝ) ≤ D by linarith)
    have a3 := mul_le_mul_of_nonneg_right hD1r (show (0:ℝ) ≤ PP by linarith)
    nlinarith
  have hG0 : 0 ≤ Formalism.NormVectorIdentities.Items.hsG D n + 2 := by
    unfold Formalism.NormVectorIdentities.Items.hsG; positivity
  have hTDPP : (T:ℝ) * D * PP ≤ b := by
    have e1 : (T:ℝ) * D * PP ≤ T * T * PP := by
      have := mul_le_mul_of_nonneg_left (show (D:ℝ) ≤ T by linarith) hTPP0
      linarith
    have e2 : (T:ℝ) * T * PP ≤ T * T * PP * PP := by
      have := mul_le_mul_of_nonneg_left hPP (mul_nonneg hTPP0 hTpos.le)
      linarith
    linarith only [e1, e2, hTPP2]
  have t4 : ((T:ℝ) + D ^ 2) * (Formalism.NormVectorIdentities.Items.hsG D n + 2) ≤ 10 * b := by
    have := mul_le_mul (show (T:ℝ) + D ^ 2 ≤ 2 * T by linarith) hG hG0 (by linarith)
    linarith
  have hl2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  have hl20 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have p1 := mul_le_mul_of_nonneg_left hlogΛD hz0
  have p2 := mul_le_mul_of_nonneg_left hlogΛT hz0
  have p3 : z * ((T:ℝ) * Real.log β) ≤ (1/2) * ((T:ℝ) * PP) :=
    mul_le_mul hz2 (mul_le_mul_of_nonneg_left hlogβ hTpos.le) (mul_nonneg hTpos.le hlogβ0) (by norm_num)
  have p4 : z * ((T:ℝ) * Real.log 2) ≤ (1/2) * ((T:ℝ) * 1) :=
    mul_le_mul hz2 (mul_le_mul_of_nonneg_left hl2.le hTpos.le) (mul_nonneg hTpos.le hl20) (by norm_num)
  have p5 : z * ((T:ℝ) * PP) ≤ (1/2) * ((T:ℝ) * PP) :=
    mul_le_mul_of_nonneg_right hz2 hTPP0
  have t5 : 2 * z * ((T:ℝ) * (Real.log 2 + (27 * (PP * (q + 1)) + 65 * PP) + Real.log β / 2) +
      Real.log ΛD + Real.log ΛT) ≤ 200 * b := by
    linarith

  set B : ℝ := (((T - 1).choose D : ℕ) : ℝ) * δ with hB
  have hB0 : 0 ≤ B := by positivity
  have hR : J + 26 * (D:ℝ) ^ 2 * ((27 * (PP * (q + 1)) + 65 * PP) + Real.log T) + ((T:ℝ) + D + 1) * Real.log β +
      ((T:ℝ) + D ^ 2) * (Formalism.NormVectorIdentities.Items.hsG D n + 2) + 2 * z * ((T:ℝ) * (Real.log 2 + (27 * (PP * (q + 1)) + 65 * PP) + Real.log β / 2) +
      Real.log ΛD + Real.log ΛT) ≤ 4000 * b := by linarith
  have hd2 : d ≤ 2 * B := by linarith [mul_le_mul_of_nonneg_right hz2 hd.le]
  have hdc := mul_le_mul_of_nonneg_right hd2 hc
  have hBR := mul_le_mul_of_nonneg_left hR hB0
  linarith

end GlobalTheory.CovHSNum
end
end
