module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousBlkM
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetWBlockMatrixFormulaStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableHermC
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousBlkM
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianHaarBlockDecompositionStatement
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Topology.Separation.CompletelyRegular
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableHermC
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.TotallySplit
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.RingTheory.Norm.Transitivity
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralPowerLineScalingStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneLeDetWStatement
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetWEqNormSqDetOneAddI

section

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt

open MeasureTheory Matrix

theorem detW_eq_normSq_det_one_add_I_smul :
    ∀ (n : ℕ) (b : Matrix (Fin n) (Fin n) ℂ), b.IsHermitian →
      detW b = Complex.normSq (Matrix.det (1 + Complex.I • b)) := by
  intro n b hb
  unfold detW
  have h1 : (1 + b * b : Matrix (Fin n) (Fin n) ℂ) = (1 + Complex.I • b) * (1 + Complex.I • b)ᴴ := by
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one, Matrix.conjTranspose_smul, hb.eq,
      Complex.star_def, Complex.conj_I]
    simp only [add_mul, mul_add, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_neg,
      Complex.I_mul_I, one_smul, neg_smul]
    abel
  rw [h1, Matrix.det_mul, Matrix.det_conjTranspose, Complex.star_def, Complex.mul_conj, Complex.ofReal_re]

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetWEqNormSqDetOneAddIStatement

section

@[expose] public section

open MeasureTheory Matrix
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt

theorem _root_.GlobalTheory.T.detW_eq_normSq_det_one_add_I : ∀ (n : ℕ) (b : Matrix (Fin n) (Fin n) ℂ), b.IsHermitian →
    detW b = Complex.normSq (Matrix.det (1 + Complex.I • b)) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.detW_eq_normSq_det_one_add_I_smul | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.detW_eq_normSq_det_one_add_I_smul | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.detW_eq_normSq_det_one_add_I_smul <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralComplexPowerFinite

section

@[expose] public section

open MeasureTheory Matrix
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt

theorem lintegral_one_add_normSq_rpow_ne_top :
    ∀ (n : ℕ) (t : ℝ), (n : ℝ) < t →
    ∫⁻ v : Fin n → ℂ, ENNReal.ofReal ((1 + ∑ i, Complex.normSq (v i)) ^ (-t)) ≠ ⊤ := by
  intro n t ht
  have ht0 : 0 < t := lt_of_le_of_lt n.cast_nonneg ht
  have hdim : (Module.finrank ℝ (Fin n → ℂ) : ℝ) < 2 * t := by
    simp [Module.finrank_pi_fintype, Complex.finrank_real_complex]
    linarith
  have hint := integrable_rpow_neg_one_add_norm_sq (E := Fin n → ℂ) (μ := volume) hdim
  refine ne_of_lt (lt_of_le_of_lt (lintegral_mono fun v => ?_) hint.lintegral_lt_top)
  apply ENNReal.ofReal_le_ofReal

  have hS0 : 0 ≤ ∑ i, Complex.normSq (v i) := Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  have hnorm : ‖v‖ ≤ Real.sqrt (∑ i, Complex.normSq (v i)) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun i => ?_
    have h1 : ‖v i‖ ^ 2 ≤ ∑ j, Complex.normSq (v j) := by
      rw [← Complex.normSq_eq_norm_sq]
      exact Finset.single_le_sum (fun j _ => Complex.normSq_nonneg (v j)) (Finset.mem_univ i)
    simpa [abs_of_nonneg (norm_nonneg _)] using Real.abs_le_sqrt h1
  have hab : 1 + ‖v‖ ^ 2 ≤ 1 + ∑ i, Complex.normSq (v i) := by
    have h2 := pow_le_pow_left₀ (norm_nonneg v) hnorm 2
    rw [Real.sq_sqrt hS0] at h2
    linarith
  have ha : 0 < 1 + ‖v‖ ^ 2 := by positivity
  rw [show -(2 * t) / 2 = -t by ring, Real.rpow_neg (by linarith), Real.rpow_neg ha.le]
  exact inv_anti₀ (Real.rpow_pos_of_pos ha t) (Real.rpow_le_rpow ha.le hab ht0.le)

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralComplexPowerFiniteStatement

section

@[expose] public section

open MeasureTheory Matrix
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt

theorem _root_.GlobalTheory.T.lintegral_complex_power_finite : ∀ (n : ℕ) (t : ℝ), (n : ℝ) < t →
    ∫⁻ v : Fin n → ℂ, ENNReal.ofReal ((1 + ∑ i, Complex.normSq (v i)) ^ (-t)) ≠ ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.lintegral_one_add_normSq_rpow_ne_top | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.lintegral_one_add_normSq_rpow_ne_top | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.lintegral_one_add_normSq_rpow_ne_top <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralLinearChangeVariablesComplex

section

@[expose] public section

open MeasureTheory Matrix
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt

theorem det_restrictScalars_toLin' {n : ℕ} (D : Matrix (Fin n) (Fin n) ℂ) :
    LinearMap.det ((Matrix.toLin' D).restrictScalars ℝ) = Complex.normSq (Matrix.det D) := by
  rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply]

theorem lintegral_eq_normSq_det_mul_lintegral_mulVec (n : ℕ) (D : Matrix (Fin n) (Fin n) ℂ)
    (hD : Matrix.det D ≠ 0) (g : (Fin n → ℂ) → ENNReal) (hg : Measurable g) :
    ∫⁻ u, g u = ENNReal.ofReal (Complex.normSq (Matrix.det D)) * ∫⁻ v, g (D *ᵥ v) := by
  set f : (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ) := (Matrix.toLin' D).restrictScalars ℝ with hf
  have hdet : LinearMap.det f = Complex.normSq (Matrix.det D) := det_restrictScalars_toLin' D
  have hpos : 0 < Complex.normSq (Matrix.det D) := Complex.normSq_pos.mpr hD
  have hne : LinearMap.det f ≠ 0 := by
    rw [hdet]
    exact hpos.ne'
  have hmap := MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar
    (volume : Measure (Fin n → ℂ)) hne
  have hfm : Measurable f := f.continuous_of_finiteDimensional.measurable
  have key : ∫⁻ v, g (D *ᵥ v) = ENNReal.ofReal (Complex.normSq (Matrix.det D))⁻¹ * ∫⁻ u, g u := by
    have e : ∀ v, D *ᵥ v = f v := fun v => by simp [hf, Matrix.toLin'_apply]
    simp_rw [e]
    rw [← lintegral_map hg hfm, hmap, lintegral_smul_measure, hdet, abs_of_pos (inv_pos.mpr hpos), smul_eq_mul]
  rw [key, ← mul_assoc, ← ENNReal.ofReal_mul hpos.le, mul_inv_cancel₀ hpos.ne', ENNReal.ofReal_one,
    one_mul]

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralLinearChangeVariablesComplexStatement

section

@[expose] public section

open MeasureTheory Matrix
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt

theorem _root_.GlobalTheory.T.lintegral_linear_change_variables_complex : ∀ (n : ℕ) (D : Matrix (Fin n) (Fin n) ℂ), Matrix.det D ≠ 0 →
    ∀ g : (Fin n → ℂ) → ENNReal, Measurable g →
    ∫⁻ u, g u = ENNReal.ofReal (Complex.normSq (Matrix.det D)) * ∫⁻ v, g (D *ᵥ v) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.lintegral_eq_normSq_det_mul_lintegral_mulVec | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.lintegral_eq_normSq_det_mul_lintegral_mulVec | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.lintegral_eq_normSq_det_mul_lintegral_mulVec <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HuaDeterminantIntegrableOfLt

section

@[expose] public section

noncomputable section
namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
open MeasureTheory Matrix
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch

theorem continuous_detW (n : ℕ) : Continuous (fun b : Matrix (Fin n) (Fin n) ℂ => detW b) := by
  unfold detW
  exact Complex.continuous_re.comp (Continuous.matrix_det (by fun_prop))

theorem measurable_term (n : ℕ) (s : ℝ) :
    Measurable (fun b : hermC n => ENNReal.ofReal (detW (b : Matrix (Fin n) (Fin n) ℂ) ^ (-s))) := by
  have h : Continuous (fun b : hermC n => detW (b : Matrix (Fin n) (Fin n) ℂ)) :=
    (continuous_detW n).comp continuous_subtype_val
  exact (h.measurable.pow_const _).ennreal_ofReal

theorem inner_eq (n : ℕ) (s : ℝ) (hs : (n : ℝ) + 1 / 2 < s) : ∃ K : ENNReal, K ≠ ⊤ ∧
    ∀ b' : hermC n, ∫⁻ u : Fin n → ℂ, ∫⁻ d : ℝ,
      ENNReal.ofReal (detW (blk b' u d : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) ^ (-s)) =
      K * ENNReal.ofReal (detW (b' : Matrix (Fin n) (Fin n) ℂ) ^ (-(s - 1))) := by
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
  obtain ⟨C, hC, hD⟩ := GlobalTheory.T.lintegral_power_line_scaling s (by linarith)
  have hL := GlobalTheory.T.lintegral_complex_power_finite n (2 * s - 1) (by linarith)
  set L := ∫⁻ v : Fin n → ℂ, ENNReal.ofReal ((1 + ∑ i, Complex.normSq (v i)) ^ (-(2 * s - 1))) with hLdef
  refine ⟨C * L, ENNReal.mul_ne_top hC hL, fun b' => ?_⟩
  have hB : (b' : Matrix (Fin n) (Fin n) ℂ).IsHermitian := mem_hermC.1 b'.2
  have hw1 := GlobalTheory.T.one_le_detW_of_isHermitian n _ hB
  have hwA := GlobalTheory.T.detW_eq_normSq_det_one_add_I n _ hB
  have hdet : Matrix.det (1 + Complex.I • (b' : Matrix (Fin n) (Fin n) ℂ)) ≠ 0 := by
    intro h0
    rw [h0] at hwA
    simp at hwA
    linarith
  have hgm : Measurable (fun u : Fin n → ℂ => ∫⁻ d : ℝ,
      ENNReal.ofReal (detW (blk b' u d : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) ^ (-s))) := by
    apply Measurable.lintegral_prod_right'
      (f := fun p : (Fin n → ℂ) × ℝ => ENNReal.ofReal (detW (blk b' p.1 p.2 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) ^ (-s)))
    have hc : Continuous (fun p : (Fin n → ℂ) × ℝ => detW (blk b' p.1 p.2 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)) :=
      (continuous_detW _).comp (continuous_blkM.comp
        (by fun_prop : Continuous fun p : (Fin n → ℂ) × ℝ => ((b' : Matrix (Fin n) (Fin n) ℂ), p.1, p.2)))
    exact (hc.measurable.pow_const _).ennreal_ofReal
  rw [GlobalTheory.T.lintegral_linear_change_variables_complex n _ hdet _ hgm, ← hwA]
  have hv : ∀ v : Fin n → ℂ, ∫⁻ d : ℝ, ENNReal.ofReal (detW (blk b' ((1 + Complex.I • (b' : Matrix (Fin n) (Fin n) ℂ)) *ᵥ v) d : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) ^ (-s))
      = ENNReal.ofReal (detW (b' : Matrix (Fin n) (Fin n) ℂ) ^ (-s)) *
        (C * ENNReal.ofReal ((1 + ∑ i, Complex.normSq (v i)) ^ (-(2 * s - 1)))) := by
    intro v
    have hr : 0 ≤ ∑ i, Complex.normSq (v i) := Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
    have hterm : ∀ d : ℝ, ENNReal.ofReal (detW (blk b' ((1 + Complex.I • (b' : Matrix (Fin n) (Fin n) ℂ)) *ᵥ v) d : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) ^ (-s))
        = ENNReal.ofReal (detW (b' : Matrix (Fin n) (Fin n) ℂ) ^ (-s)) *
          ENNReal.ofReal (((1 + ∑ i, Complex.normSq (v i)) ^ 2 +
            (d - (star v ⬝ᵥ ((b' : Matrix (Fin n) (Fin n) ℂ) *ᵥ v)).re) ^ 2) ^ (-s)) := by
      intro d
      have hh := mem_hermC.1 (blk b' ((1 + Complex.I • (b' : Matrix (Fin n) (Fin n) ℂ)) *ᵥ v) d).2
      rw [GlobalTheory.T.detW_eq_normSq_det_one_add_I _ _ hh]
      have e : ((blk b' ((1 + Complex.I • (b' : Matrix (Fin n) (Fin n) ℂ)) *ᵥ v) d : hermC (n+1)) : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
          = blkM (b' : Matrix (Fin n) (Fin n) ℂ) ((1 + Complex.I • (b' : Matrix (Fin n) (Fin n) ℂ)) *ᵥ v) d := rfl
      rw [e, GlobalTheory.T.detW_block_matrix_formula n _ hB hdet v d, ← hwA, Real.mul_rpow (by linarith) (by positivity),
        ENNReal.ofReal_mul (Real.rpow_nonneg (by linarith) _)]
    simp only [hterm]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hD (1 + ∑ i, Complex.normSq (v i)) (by linarith)]
    congr 3
    ring_nf
  simp only [hv]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul' _ _ hC]
  have e2 : ENNReal.ofReal (detW (b' : Matrix (Fin n) (Fin n) ℂ) ^ (-(s - 1)))
      = ENNReal.ofReal (detW (b' : Matrix (Fin n) (Fin n) ℂ)) *
        ENNReal.ofReal (detW (b' : Matrix (Fin n) (Fin n) ℂ) ^ (-s)) := by
    rw [← ENNReal.ofReal_mul (by linarith)]
    congr 1
    rw [show -(s - 1) = 1 + -s by ring, Real.rpow_add (by linarith), Real.rpow_one]
  rw [e2]
  ring

theorem hua_integrable : ∀ (n : ℕ) (s : ℝ), (n : ℝ) - 1 / 2 < s → ∀ ν : Measure (hermC n), ν.IsAddHaarMeasure →
    Integrable (fun b : hermC n => detW (b : Matrix (Fin n) (Fin n) ℂ) ^ (-s)) ν := by
  intro n
  induction n with
  | zero =>
    intro s _ ν hν
    have : IsFiniteMeasure ν := by
      haveI : Finite (hermC 0) := by
        haveI : Subsingleton (Matrix (Fin 0) (Fin 0) ℂ) := inferInstance
        exact Finite.of_subsingleton
      haveI : CompactSpace (hermC 0) := Finite.compactSpace
      exact ⟨isCompact_univ.measure_lt_top⟩
    have h1 : ∀ b : hermC 0, detW (b : Matrix (Fin 0) (Fin 0) ℂ) ^ (-s) = 1 := by
      intro b
      simp [detW]
    simp only [h1]
    exact integrable_const _
  | succ n ih =>
    intro s hs ν hν
    have hs' : (n : ℝ) + 1 / 2 < s := by push_cast at hs; linarith
    have hpos : ∀ b : hermC (n + 1), 0 ≤ detW (b : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) ^ (-s) := fun b =>
      Real.rpow_nonneg (by linarith [GlobalTheory.T.one_le_detW_of_isHermitian _ _ (mem_hermC.1 b.2)]) _
    have hmeas := measurable_term (n + 1) s
    have hm2 : Measurable (fun b : hermC (n + 1) => detW (b : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) ^ (-s)) :=
      (((continuous_detW (n + 1)).comp continuous_subtype_val).measurable.pow_const _)
    refine ⟨hm2.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hpos)]
    obtain ⟨c, hc, hF⟩ := GlobalTheory.T.hermitian_haar_block_decomposition n ν (Measure.addHaar) hν inferInstance
    obtain ⟨K, hK, hI⟩ := inner_eq n s hs'
    rw [hF _ hmeas]
    simp only [hI]
    rw [lintegral_const_mul _ (measurable_term n (s - 1))]
    have h3 := ih (s - 1) (by linarith) Measure.addHaar inferInstance
    have hp3 : ∀ b : hermC n, 0 ≤ detW (b : Matrix (Fin n) (Fin n) ℂ) ^ (-(s - 1)) := fun b =>
      Real.rpow_nonneg (by linarith [GlobalTheory.T.one_le_detW_of_isHermitian _ _ (mem_hermC.1 b.2)]) _
    have h4 := (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hp3)).1 h3.2
    exact ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hc)
      (ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hK) h4)

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
end
end
end
