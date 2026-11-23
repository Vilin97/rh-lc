module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DilationDecomposition.Imports
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.GoodAwayEx
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussLaw
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobData
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierInjectiveMatrixSpaceStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HolomorphicParameterIntegralGaussianBoundStatement
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IteratedDerivGaussianExponentialAtZeroStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IteratedDerivIntegralGaussianExponentialStatement
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BruhatCellParabolicUnipotentFactorization

section

@[expose] public section

open scoped Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.DCell

open Matrix PositivityTheory.Rg.Sw

variable {n : ℕ}

theorem JJ_mul_self : JJ n * JJ n = -1 := by
  rw [JJ, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_neg]
  simp

theorem rows_rel (g : M2 n) (h : InG g) : g * JJ n * gᴴ = JJ n := by
  have hinv : (-(JJ n) * gᴴ * JJ n) * g = 1 := by
    have h' : gᴴ * JJ n * g = JJ n := h
    calc (-(JJ n) * gᴴ * JJ n) * g = -(JJ n * (gᴴ * JJ n * g)) := by
          simp only [Matrix.mul_assoc, Matrix.neg_mul]
      _ = 1 := by rw [h', JJ_mul_self, neg_neg]
  have h2 : g * (-(JJ n) * gᴴ * JJ n) = 1 := mul_eq_one_comm.mp hinv
  calc g * JJ n * gᴴ = g * JJ n * gᴴ * (-(JJ n * JJ n)) := by
        rw [JJ_mul_self, neg_neg, Matrix.mul_one]
    _ = -((g * (-(JJ n) * gᴴ * JJ n)) * JJ n) * (-1) * (-1) * (-1) := by
        simp only [Matrix.mul_assoc, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_one, neg_neg]
    _ = JJ n := by
        rw [h2]; simp

theorem block_rel (g : M2 n) (h : InG g) :
    g.toBlocks₂₁ * g.toBlocks₂₂ᴴ = g.toBlocks₂₂ * g.toBlocks₂₁ᴴ := by
  have h1 := rows_rel g h
  have h3 : (g * JJ n * gᴴ).toBlocks₂₂ = (JJ n).toBlocks₂₂ := by rw [h1]
  rw [← fromBlocks_toBlocks g] at h3
  simp only [JJ, fromBlocks_conjTranspose, fromBlocks_multiply, toBlocks_fromBlocks₂₂] at h3
  simp at h3
  have h4 := sub_eq_zero.mp (by
    rw [← h3]; abel : g.toBlocks₂₁ * g.toBlocks₂₂ᴴ - g.toBlocks₂₂ * g.toBlocks₂₁ᴴ = 0)
  exact h4

theorem inG_lower (c : Matrix (Fin n) (Fin n) ℂ) (hc : cᴴ = c) :
    InG (fromBlocks 1 0 c 1 : M2 n) := by
  unfold InG
  rw [JJ, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]
  simp [hc]

def lowerU (c : Matrix (Fin n) (Fin n) ℂ) : GL (Fin n ⊕ Fin n) ℂ where
  val := fromBlocks 1 0 c 1
  inv := fromBlocks 1 0 (-c) 1
  val_inv := by rw [fromBlocks_multiply, ← fromBlocks_one]; simp
  inv_val := by rw [fromBlocks_multiply, ← fromBlocks_one]; simp

theorem main : ∀ (n : ℕ) (y : PositivityTheory.Rg.Sw.GR n), ((PositivityTheory.Rg.Sw.mR y).toBlocks₂₂).det ≠ 0 → ∃ (p nbb : PositivityTheory.Rg.Sw.GR n) (c : Matrix (Fin n) (Fin n) ℂ), (PositivityTheory.Rg.Sw.mR p).toBlocks₂₁ = 0 ∧ cᴴ = c ∧ PositivityTheory.Rg.Sw.mR nbb = Matrix.fromBlocks 1 0 c 1 ∧ y = p * nbb := by
  intro n y hD
  set g : M2 n := mR y with hg
  have hy : InG g := y.2
  set C := g.toBlocks₂₁ with hC
  set D := g.toBlocks₂₂ with hDd
  have hrel : C * Dᴴ = D * Cᴴ := block_rel g hy
  have hu : IsUnit D.det := isUnit_iff_ne_zero.mpr hD
  have hDi : D * D⁻¹ = 1 := Matrix.mul_nonsing_inv D hu
  have hiD : D⁻¹ * D = 1 := Matrix.nonsing_inv_mul D hu
  have hiDH : (D⁻¹)ᴴ * Dᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hDi, Matrix.conjTranspose_one]
  have hc : (D⁻¹ * C)ᴴ = D⁻¹ * C := by
    rw [Matrix.conjTranspose_mul]
    have hDH : Dᴴ * (D⁻¹)ᴴ = 1 := mul_eq_one_comm.mp hiDH
    calc Cᴴ * (D⁻¹)ᴴ = (D⁻¹ * D) * Cᴴ * (D⁻¹)ᴴ := by rw [hiD, Matrix.one_mul]
      _ = D⁻¹ * (D * Cᴴ) * (D⁻¹)ᴴ := by simp only [Matrix.mul_assoc]
      _ = D⁻¹ * (C * Dᴴ) * (D⁻¹)ᴴ := by rw [hrel]
      _ = D⁻¹ * C * (Dᴴ * (D⁻¹)ᴴ) := by simp only [Matrix.mul_assoc]
      _ = D⁻¹ * C := by rw [hDH, Matrix.mul_one]
  set c := D⁻¹ * C with hcdef
  have hmem : lowerU c ∈ GR n := inG_lower c hc
  refine ⟨y * (⟨lowerU c, hmem⟩ : GR n)⁻¹, ⟨lowerU c, hmem⟩, c, ?_, hc, rfl, by simp⟩
  have hval : mR (y * (⟨lowerU c, hmem⟩ : GR n)⁻¹) = g * fromBlocks 1 0 (-c) 1 := rfl
  rw [hval]
  conv_lhs => rw [← fromBlocks_toBlocks g]
  rw [fromBlocks_multiply, toBlocks_fromBlocks₂₁]
  have : D * c = C := by rw [hcdef, ← Matrix.mul_assoc, hDi, Matrix.one_mul]
  simp [← hC, ← hDd, this]

end GlobalTheory.CompanionTheory.DCell
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BruhatCellParabolicUnipotentFactorizationStatement

section

@[expose] public section

open scoped Matrix

theorem _root_.GlobalTheory.T.bruhat_cell_parabolic_unipotent_factorization : ∀ (n : ℕ) (y : PositivityTheory.Rg.Sw.GR n), ((PositivityTheory.Rg.Sw.mR y).toBlocks₂₂).det ≠ 0 → ∃ (p nbb : PositivityTheory.Rg.Sw.GR n) (c : Matrix (Fin n) (Fin n) ℂ), (PositivityTheory.Rg.Sw.mR p).toBlocks₂₁ = 0 ∧ cᴴ = c ∧ PositivityTheory.Rg.Sw.mR nbb = Matrix.fromBlocks 1 0 c 1 ∧ y = p * nbb := by
  first | exact @GlobalTheory.CompanionTheory.DCell.main | exact GlobalTheory.CompanionTheory.DCell.main | (intros; apply GlobalTheory.CompanionTheory.DCell.main <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IteratedDerivEqOfEqOnRealSegment

section

@[expose] public section

open Filter Topology

namespace GlobalTheory.CompanionTheory.ComplexAnalysis

theorem iteratedDeriv_zero_eq_of_eq_on_real_points (f g : ℂ → ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hf : DifferentiableOn ℂ f (Metric.ball 0 ρ)) (hg : DifferentiableOn ℂ g (Metric.ball 0 ρ))
    (h : ∀ s : ℝ, |s| < ρ → f s = g s) (r : ℕ) :
    iteratedDeriv r f 0 = iteratedDeriv r g 0 := by

  have hU : IsOpen (Metric.ball (0 : ℂ) ρ) := Metric.isOpen_ball
  have h0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) ρ := Metric.mem_ball_self hρ
  have hreal : ∀ᶠ s : ℝ in 𝓝[≠] 0, f s = g s := by
    have hs : {s : ℝ | |s| < ρ} ∈ 𝓝 (0 : ℝ) :=
      (isOpen_lt continuous_abs continuous_const).mem_nhds (by simpa using hρ)
    exact Filter.mem_of_superset (nhdsWithin_le_nhds hs) fun s hs' => h s hs'
  have htend : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[≠] 0) (𝓝[≠] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hc := Complex.continuous_ofReal.tendsto (0 : ℝ)
      simpa using hc.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      simpa using hs
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), f z = g z := htend.frequently hreal.frequently
  have heq : Set.EqOn f g (Metric.ball 0 ρ) :=
    (hf.analyticOnNhd hU).eqOn_of_preconnected_of_frequently_eq (hg.analyticOnNhd hU)
      (convex_ball (0 : ℂ) ρ).isPreconnected h0 hfreq
  have hev : f =ᶠ[𝓝 0] g := Filter.mem_of_superset (hU.mem_nhds h0) heq
  exact hev.iteratedDeriv_eq r

end GlobalTheory.CompanionTheory.ComplexAnalysis
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IteratedDerivEqOfEqOnRealSegmentStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.iteratedDeriv_eq_of_eq_on_real_segment : ∀ (f g : ℂ → ℂ) (ρ : ℝ), 0 < ρ → DifferentiableOn ℂ f (Metric.ball 0 ρ) → DifferentiableOn ℂ g (Metric.ball 0 ρ) → (∀ s : ℝ, |s| < ρ → f s = g s) → ∀ r : ℕ, iteratedDeriv r f 0 = iteratedDeriv r g 0 := by
  first | exact @GlobalTheory.CompanionTheory.ComplexAnalysis.iteratedDeriv_zero_eq_of_eq_on_real_points | exact GlobalTheory.CompanionTheory.ComplexAnalysis.iteratedDeriv_zero_eq_of_eq_on_real_points | (intros; apply GlobalTheory.CompanionTheory.ComplexAnalysis.iteratedDeriv_zero_eq_of_eq_on_real_points <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicDecompositionUpperHalfSpace

section

@[expose] public section

open scoped Matrix

namespace GlobalTheory.CompanionTheory.SiegelPoint

open Matrix PositivityTheory.Rg.Sw

variable {n : ℕ}

theorem block_relations (A B D : Matrix (Fin n) (Fin n) ℂ)
    (h : InG (fromBlocks A B 0 D : M2 n)) : Aᴴ * D = 1 ∧ Bᴴ * D = Dᴴ * B := by
  unfold InG JJ at h
  rw [fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply] at h
  obtain ⟨-, h12, -, h22⟩ := fromBlocks_inj.mp h
  simp only [conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_neg, Matrix.neg_mul, add_zero, zero_add, neg_zero] at h12 h22
  exact ⟨h12, (neg_add_eq_zero.mp h22).symm⟩

theorem levi_inG (a D : Matrix (Fin n) (Fin n) ℂ) (h : aᴴ * D = 1) :
    InG (fromBlocks a 0 0 D : M2 n) := by
  have h' : Dᴴ * a = 1 := by
    have h2 := congrArg conjTranspose h
    rwa [conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_one] at h2
  unfold InG JJ
  rw [fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]
  simp only [conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_neg, Matrix.neg_mul, add_zero, zero_add, h, h', neg_zero]

theorem siegel_point :
    ∀ (n : ℕ) (p : PositivityTheory.Rg.Sw.GR n), (PositivityTheory.Rg.Sw.mR p).toBlocks₂₁ = 0 →
      ∃ (nb ma : PositivityTheory.Rg.Sw.GR n) (b a : Matrix (Fin n) (Fin n) ℂ), bᴴ = b ∧ IsUnit a.det ∧
        PositivityTheory.Rg.Sw.mR nb = PositivityTheory.Rg.Sw.nU b ∧ PositivityTheory.Rg.Sw.mR ma = Matrix.fromBlocks a 0 0 (aᴴ)⁻¹ ∧
        p = nb * ma ∧
        ((PositivityTheory.Rg.Sw.mR p).toBlocks₁₁ * (Complex.I • 1) + (PositivityTheory.Rg.Sw.mR p).toBlocks₁₂) *
            ((PositivityTheory.Rg.Sw.mR p).toBlocks₂₁ * (Complex.I • 1) + (PositivityTheory.Rg.Sw.mR p).toBlocks₂₂)⁻¹ =
          b + Complex.I • (a * aᴴ) := by
  intro n p hp
  set A := (mR p).toBlocks₁₁ with hA
  set B := (mR p).toBlocks₁₂ with hB
  set D := (mR p).toBlocks₂₂ with hD
  have hpm : mR p = fromBlocks A B 0 D := by
    rw [← hp]
    exact (fromBlocks_toBlocks (mR p)).symm
  have hG : InG (mR p) := p.2
  rw [hpm] at hG
  obtain ⟨h1, h2⟩ := block_relations A B D hG
  have hDA : D * Aᴴ = 1 := mul_eq_one_comm.mp h1
  have hADh : A * Dᴴ = 1 := by
    have h3 := congrArg conjTranspose hDA
    rwa [conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_one] at h3
  have hinv : (Aᴴ)⁻¹ = D := Matrix.inv_eq_right_inv h1
  have hDinv : D⁻¹ = Aᴴ := Matrix.inv_eq_right_inv hDA
  set b := B * Aᴴ with hb
  have hbh : bᴴ = b := by
    rw [hb, conjTranspose_mul, conjTranspose_conjTranspose]
    calc A * Bᴴ = A * Bᴴ * (D * Aᴴ) := by rw [hDA, Matrix.mul_one]
      _ = A * (Bᴴ * D) * Aᴴ := by simp only [Matrix.mul_assoc]
      _ = A * (Dᴴ * B) * Aᴴ := by rw [h2]
      _ = A * Dᴴ * B * Aᴴ := by simp only [Matrix.mul_assoc]
      _ = B * Aᴴ := by rw [hADh, Matrix.one_mul]
  have hnbG : InG (nU b : M2 n) := by
    unfold InG JJ nU
    rw [fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]
    simp only [conjTranspose_zero, conjTranspose_one, Matrix.mul_zero, Matrix.zero_mul,
      Matrix.mul_one, Matrix.one_mul, Matrix.mul_neg, Matrix.neg_mul, add_zero, zero_add, hbh,
      neg_add_cancel, neg_zero]
  have hdet1 : IsUnit (nU b : M2 n).det := by
    unfold nU
    rw [det_fromBlocks_zero₂₁, det_one, mul_one]
    exact isUnit_one
  have hmaG : InG (fromBlocks A 0 0 D : M2 n) := levi_inG A D h1
  have hM : (fromBlocks A 0 0 D : M2 n) * fromBlocks Dᴴ 0 0 Aᴴ = 1 := by
    rw [fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, hADh, hDA, fromBlocks_one]
  have hdet2 : IsUnit (fromBlocks A 0 0 D : M2 n).det := Matrix.isUnit_det_of_right_inverse hM
  refine ⟨⟨Matrix.nonsingInvUnit _ hdet1, hnbG⟩, ⟨Matrix.nonsingInvUnit _ hdet2, hmaG⟩, b, A, hbh,
    Matrix.isUnit_det_of_right_inverse hADh, rfl, ?_, ?_, ?_⟩
  · show (fromBlocks A 0 0 D : M2 n) = fromBlocks A 0 0 (Aᴴ)⁻¹
    rw [hinv]
  · apply Subtype.ext
    apply Units.ext
    show mR p = nU b * fromBlocks A 0 0 D
    rw [hpm]
    unfold nU
    rw [fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul, add_zero, zero_add]
    rw [hb, Matrix.mul_assoc, h1, Matrix.mul_one]
  · rw [hp, Matrix.zero_mul, zero_add, hDinv, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul, hb, add_comm]

end GlobalTheory.CompanionTheory.SiegelPoint
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicDecompositionUpperHalfSpaceStatement

section

@[expose] public section

open scoped Matrix

theorem _root_.GlobalTheory.T.parabolic_decomposition_upper_half_space : ∀ (n : ℕ) (p : PositivityTheory.Rg.Sw.GR n), (PositivityTheory.Rg.Sw.mR p).toBlocks₂₁ = 0 → ∃ (nb ma : PositivityTheory.Rg.Sw.GR n) (b a : Matrix (Fin n) (Fin n) ℂ), bᴴ = b ∧ IsUnit a.det ∧ PositivityTheory.Rg.Sw.mR nb = PositivityTheory.Rg.Sw.nU b ∧ PositivityTheory.Rg.Sw.mR ma = Matrix.fromBlocks a 0 0 (aᴴ)⁻¹ ∧ p = nb * ma ∧ ((PositivityTheory.Rg.Sw.mR p).toBlocks₁₁ * (Complex.I • 1) + (PositivityTheory.Rg.Sw.mR p).toBlocks₁₂) * ((PositivityTheory.Rg.Sw.mR p).toBlocks₂₁ * (Complex.I • 1) + (PositivityTheory.Rg.Sw.mR p).toBlocks₂₂)⁻¹ = b + Complex.I • (a * aᴴ) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelPoint.siegel_point | exact GlobalTheory.CompanionTheory.SiegelPoint.siegel_point | (intros; apply GlobalTheory.CompanionTheory.SiegelPoint.siegel_point <;> assumption)
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DilationDecomposition.LocAlgPf

section

@[expose] public section

noncomputable section

open scoped Matrix
open MeasureTheory PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Kdil

open PositivityTheory.Rg.Sw.Glob (actZ)
open Matrix

variable {n : ℕ}

theorem up_decomp_pf (p : GR n) (hp : (mR p).toBlocks₂₁ = 0) :
    ∃ (nb ma : GR n) (b a : Matrix (Fin n) (Fin n) ℂ), bᴴ = b ∧ IsUnit a.det ∧ mR nb = nU b ∧ mR ma = mLoc a ∧
      p = nb * ma ∧ actZ p (Complex.I • 1) = b + Complex.I • (a * aᴴ) :=
  GlobalTheory.T.parabolic_decomposition_upper_half_space n p hp

theorem fam_deriv_pf (m : ℕ) (X : Fin n → ℝ) (v : Fin m → Fin n → ℂ) (r : ℕ) :
    iteratedDeriv r (fun z => fam m X z v) 0 = fP ((dil (2 * Real.pi) X ^ r) 1) v :=
  (GlobalTheory.T.iteratedDeriv_gaussian_exponential_at_zero m n X v).2 r

theorem fam_int_hol_pf (m : ℕ) (X : Fin n → ℝ) (K : (Fin m → Fin n → ℂ) → ℂ) (hK : Continuous K)
    (hK1 : ∀ v, ‖K v‖ ≤ 1) :
    ∃ ρ : ℝ, 0 < ρ ∧ DifferentiableOn ℂ (fun z => ∫ v, K v * fam m X z v) (Metric.ball 0 ρ) ∧
      ∀ r : ℕ, iteratedDeriv r (fun z => ∫ v, K v * fam m X z v) 0 =
        ∫ v, K v * iteratedDeriv r (fun z => fam m X z v) 0 :=
  GlobalTheory.T.iteratedDeriv_integral_gaussian_exponential m n X K hK hK1

theorem iteratedDeriv_eq_of_real_pf {f g : ℂ → ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hf : DifferentiableOn ℂ f (Metric.ball 0 ρ))
    (hg : DifferentiableOn ℂ g (Metric.ball 0 ρ)) (hfg : ∀ s : ℝ, |s| < ρ → f s = g s) (r : ℕ) :
    iteratedDeriv r f 0 = iteratedDeriv r g 0 :=
  GlobalTheory.T.iteratedDeriv_eq_of_eq_on_real_segment f g ρ hρ hf hg hfg r

theorem dcell_pf (y : GR n) (hy : ((mR y).toBlocks₂₂).det ≠ 0) :
    ∃ (p nbb : GR n) (c : Matrix (Fin n) (Fin n) ℂ), (mR p).toBlocks₂₁ = 0 ∧ cᴴ = c ∧ mR nbb = nbLoc c ∧ y = p * nbb :=
  GlobalTheory.T.bruhat_cell_parabolic_unipotent_factorization n y hy

theorem hol_int_pf {m : ℕ} (Φ : ℂ → (Fin m → Fin n → ℂ) → ℂ) (ρ C δ : ℝ) (hρ : 0 < ρ) (hδ : 0 < δ)
    (hd : ∀ v, DifferentiableOn ℂ (fun z => Φ z v) (Metric.ball 0 ρ))
    (hc : ContinuousOn (fun zv : ℂ × (Fin m → Fin n → ℂ) => Φ zv.1 zv.2) (Metric.ball 0 ρ ×ˢ Set.univ))
    (hb : ∀ z ∈ Metric.ball (0 : ℂ) ρ, ∀ v, ‖Φ z v‖ ≤ C * Real.exp (-δ * sq v))
    (K : (Fin m → Fin n → ℂ) → ℂ) (hK : Continuous K) (hK1 : ∀ v, ‖K v‖ ≤ 1) :
    ∃ ρ' : ℝ, 0 < ρ' ∧ DifferentiableOn ℂ (fun z => ∫ v, K v * Φ z v) (Metric.ball 0 ρ') ∧
      ∀ r : ℕ, iteratedDeriv r (fun z => ∫ v, K v * Φ z v) 0 = ∫ v, K v * iteratedDeriv r (fun z => Φ z v) 0 ∧
        Continuous (fun v => iteratedDeriv r (fun z => Φ z v) 0) ∧
        ∃ C' : ℝ, ∀ v, ‖iteratedDeriv r (fun z => Φ z v) 0‖ ≤ C' * Real.exp (-δ * sq v) :=
  GlobalTheory.T.holomorphic_parameter_integral_gaussian_bound m n Φ ρ C δ hρ hδ hd hc hb K hK hK1

theorem ft_uniq_pf {m : ℕ} (s : ℂ) (hs : s ≠ 0) (g : (Fin m → Fin n → ℂ) → ℂ) (hg : Continuous g) (hgi : Integrable g)
    (h0 : ∀ u : Fin m → Fin n → ℂ, ∫ v, Complex.exp (2 * Real.pi * Complex.I *
      ((s * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v)).re : ℂ)) * g v = 0) : g = 0 :=
  GlobalTheory.T.fourier_injective_matrix_space m n s hs g hg hgi h0

theorem up_decomp_closed : type_of% @up_decomp_pf := @up_decomp_pf

theorem fam_deriv_closed : type_of% @fam_deriv_pf := @fam_deriv_pf

theorem fam_int_hol_closed : type_of% @fam_int_hol_pf := @fam_int_hol_pf

theorem iteratedDeriv_eq_of_real_closed : type_of% @iteratedDeriv_eq_of_real_pf := @iteratedDeriv_eq_of_real_pf

theorem dcell_closed : type_of% @dcell_pf := @dcell_pf

theorem hol_int_closed : type_of% @hol_int_pf := @hol_int_pf

theorem ft_uniq_closed : type_of% @ft_uniq_pf := @ft_uniq_pf

end PositivityTheory.SiegelWeilFormula.Kdil

end
end
end
