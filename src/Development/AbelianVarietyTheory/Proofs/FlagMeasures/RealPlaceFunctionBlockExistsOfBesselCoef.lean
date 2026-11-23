module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.BesselLevi
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SettingBlocks
public import Formalism.PeriodIntegrals.ScGapBig
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.ScWlocExists
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HCReprodM
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.TensInt
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.WFLStepsLocHNProps
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.WFromLoc
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.NUnimodLoc
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QuotProdK

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SpectralGapLarge.ScGapBigMain

section

@[expose] public section

namespace PI.UnitaryGroupMassFormula.ScGapBig

open PI.ScGapBig

theorem nat_bound (n m t : ℕ) (hn : 1801 ≤ n) (hm : m ≤ n + 1) (ht : t ≤ n + 6) :
    2 * (n + m * t) ^ 3 + t + 3 < 16 * n ^ 19 := by
  have hmt : m * t ≤ (n + 1) * (n + 6) := Nat.mul_le_mul hm ht
  have hsq : 1801 * n ≤ n * n := Nat.mul_le_mul_right n hn
  have h1 : n + m * t ≤ 2 * n ^ 2 := by nlinarith
  have h2 : (n + m * t) ^ 3 ≤ (2 * n ^ 2) ^ 3 := Nat.pow_le_pow_left h1 3
  have h3 : (2 * n ^ 2) ^ 3 = 8 * n ^ 6 := by ring
  have h4 : 2 ≤ n ^ 13 :=
    le_trans (by norm_num) (Nat.pow_le_pow_left (show 2 ≤ n by omega) 13)
  have h5 : n ^ 19 = n ^ 6 * n ^ 13 := by ring
  have h6 : n ^ 6 * 2 ≤ n ^ 6 * n ^ 13 := Nat.mul_le_mul_left _ h4
  have h7 : n ≤ n ^ 6 := Nat.le_self_pow (by norm_num) n
  omega

theorem scGapBig_main : ScGapBig := by
  intro k r b hn hgap
  have hrk : rk48 k r = 2 * r + k + 1 := rfl
  obtain ⟨t, hodd, ht1, ht2⟩ : ∃ t : ℕ, Odd t ∧ rk48 k r + 5 ≤ t ∧ t ≤ rk48 k r + 6 := by
    rcases Nat.even_or_odd (rk48 k r) with ⟨a, ha⟩ | ⟨a, ha⟩
    · exact ⟨rk48 k r + 5, ⟨a + 2, by omega⟩, le_refl _, by omega⟩
    · exact ⟨rk48 k r + 6, ⟨a + 3, by omega⟩, by omega, le_refl _⟩
  refine ⟨t, hodd, ht1, by omega, ?_⟩
  intro j hj
  have hm : 2 * r + 2 ≤ rk48 k r + 1 := by omega
  have hb := nat_bound (rk48 k r) (2 * r + 2) t hn hm ht2
  have hcast : 2 * ((rk48 k r + (2 * r + 2) * t : ℕ) : ℝ) ^ 3 + (t : ℝ) + 3 <
      16 * (rk48 k r : ℝ) ^ 19 := by
    exact_mod_cast hb
  linarith [hgap j hj]

end PI.UnitaryGroupMassFormula.ScGapBig
end
end

-- Source module: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ScGapBig

section

@[expose] public section

theorem scGapBig : PI.ScGapBig.ScGapBig := PI.UnitaryGroupMassFormula.ScGapBig.scGapBig_main
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.GapBigOfComparison

section

@[expose] public section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.SplitPrimeNormLemmas

namespace GlobalTheory.GapAtRealPlaces

theorem gapBig_of_comparison (h : PI.ScGapBig.ScGapBig) (D : Formalism.BasicNotions.D7) :
    Formalism.L2.SG.SplitPrimeNormLemmas.GapBigOfGapHyp D := by
  intro hm hG τ

  have hr : PI.ScGapBig.rk48 D.R.k D.R.rS = D.R.r := by
    simp only [PI.ScGapBig.rk48, Formalism.BasicNotions.Ranks.r]
    omega

  have hgaps : ∀ (j : Fin (2 * D.R.rS + 2)) (hj : j.val + 1 < 2 * D.R.rS + 2),
      16 * (PI.ScGapBig.rk48 D.R.k D.R.rS : ℝ) ^ 19 ≤
        ((D.hc τ).b (Fin.cast hm.symm ⟨j.val + 1, hj⟩) : ℝ) - ((D.hc τ).b (Fin.cast hm.symm j) : ℝ) := by
    intro j hj
    have hlt : (Fin.cast hm.symm j).val + 1 < D.R.m := by
      rw [Fin.val_cast]
      omega
    have key := hG.2 τ (Fin.cast hm.symm j) hlt
    have hidx : (⟨(Fin.cast hm.symm j).val + 1, hlt⟩ : Fin D.R.m) = Fin.cast hm.symm ⟨j.val + 1, hj⟩ :=
      Fin.ext rfl
    rw [hidx] at key
    rw [hr]
    exact_mod_cast key
  obtain ⟨t, hto, ht5, ht1801, hgap⟩ :=
    h D.R.k D.R.rS (fun j => ((D.hc τ).b (Fin.cast hm.symm j) : ℝ)) (hr ▸ hG.1) hgaps
  exact ⟨t, hto, ht5, ht1801, hgap⟩

theorem gapBigOfGapHyp : ∀ D : D7, GapBigOfGapHyp D := by
  intro D
  exact gapBig_of_comparison scGapBig D

end GlobalTheory.GapAtRealPlaces
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.WlocExistsReal

section

@[expose] public section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.SplitPrimeNormLemmas

namespace GlobalTheory

theorem wlocExists_real : WlocExists :=
  scWlocExists Formalism.L2.SG.HCReprodM.hcReprodDSm

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealPlaceFunctionBlockExistsOfBesselCoef

section

@[expose] public section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.SplitPrimeNormLemmas

namespace GlobalTheory.WBlockExists

theorem nUnimodLoc : Formalism.L2.SG.Pf.WFL.NUnimodLoc := by
  intro k r ε e f wf z0 z c hF hc hz
  exact n_unimodular_local k r ε e f wf z0 z c
    ⟨hF.ee, hF.ff, hF.ef, hF.ez, hF.fz, hF.zz, hF.ww, hF.ew, hF.fw, hF.zw⟩ hc hz

theorem realPlaceFunctionBlockExists_of_bessel_coef : BesselNVGap → CoefWeightedLoc → ∀ D : D7, GlobalTheory.St.WBlkExists D :=
  by
    intro hB hCW D hG A L Ps Rf Bu Pi Mu
    obtain ⟨I, ιE, ιE_conj, ιE_F, bas, J_eq, L_eq, pl, φ_eq, n_eq, eps_eq⟩ := A
    exact Formalism.L2.SG.Pf.WFL.wblk_core quotient_product_compact
      Formalism.L2.SG.Pf.WFL.locHNProps_holds nUnimodLoc
      Formalism.L2.SG.Pf.WuDec.integrable_and_integral_pi_apply hB hCW
      GlobalTheory.wlocExists_real (GlobalTheory.GapAtRealPlaces.gapBigOfGapHyp D)
      hG I ιE ιE_conj ιE_F bas J_eq L_eq pl φ_eq n_eq eps_eq L Ps Rf Bu Pi Mu

end GlobalTheory.WBlockExists
end
end
