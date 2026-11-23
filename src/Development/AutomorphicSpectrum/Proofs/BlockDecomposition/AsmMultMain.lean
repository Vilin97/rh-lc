module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsMultOfFintype
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BumpConvolutionSupport
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
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.IsMultZero
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoshTransformCasimirReal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsMultOfFintype
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoshTransformConvolutionStatement
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.Group.Units
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelMultiplierOnEigenfunctionStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveKernelConvolutionStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveKernelDecomposition
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveTimeAverageIsWave
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZOpSmooth

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BumpConvolutionSupportStatement

section

@[expose] public section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem _root_.GlobalTheory.T.bump_convolution_support : ∀ (g g' : ℝ → ℝ) (T T' : ℝ), IsBump g T → IsBump g' T' → IsBump (gconv g g') (T + T') := by
  first | exact @GlobalTheory.CompanionTheory.WaveMult.isBump_gconv | exact GlobalTheory.CompanionTheory.WaveMult.isBump_gconv | (intros; apply GlobalTheory.CompanionTheory.WaveMult.isBump_gconv <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoshTransformCasimirRealStatement

section

@[expose] public section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem _root_.GlobalTheory.T.cosh_transform_casimir_real : ∀ (n : ℕ) (χ : Inf n) (g : ℝ → ℝ) (T : ℝ), IsHerm χ → IsBump g T → conj (coshT g (cas χ)) = coshT g (cas χ) := by
  first | exact @GlobalTheory.CompanionTheory.WaveMult.conj_coshT_cas | exact GlobalTheory.CompanionTheory.WaveMult.conj_coshT_cas | (intros; apply GlobalTheory.CompanionTheory.WaveMult.conj_coshT_cas <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelMultiplierLinear

section

@[expose] public section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult

theorem conv_eq_sum_of_kernels : LgFacts → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n) {ι ι' : Type} [Fintype ι] [Fintype ι'] (c : ι → ℂ) (c' : ι' → ℂ) (ks : ι → Mat n → (E.V →L[ℂ] E.V)) (ks' : ι' → Mat n → (E.V →L[ℂ] E.V)) (k k' : Mat n → (E.V →L[ℂ] E.V)), (∀ i, KReg (ks i)) → (∀ j, KReg (ks' j)) → (∀ y ∈ GLs n, k y = ∑ i, c i • ks i y) → (∀ y ∈ GLs n, k' y = ∑ j, c' j • ks' j y) → ∀ x ∈ GLs n, conv μ E k k' x = ∑ i, ∑ j, (c i * c' j) • conv μ E (ks i) (ks' j) x := by
  intro hL n _ _ μ _ E ι ι' _ _ c c' ks ks' k k' hks hks' hk hk' x hx
  haveI : CompleteSpace E.V := FiniteDimensional.complete ℂ E.V
  have hval : ∀ y : G n, y.val ∈ GLs n := fun y => by
    have := (Matrix.isUnit_iff_isUnit_det _).1 y.isUnit
    exact this.ne_zero
  have hcv : Continuous (fun y : G n => y.val) := Units.continuous_val
  have hcinv : Continuous (fun y : G n => (y⁻¹ : G n).val) := Units.continuous_val.comp continuous_inv
  have hmem : ∀ y : G n, (y⁻¹ : G n).val * x ∈ GLs n := by
    intro y
    have h1 : ((y⁻¹ : G n).val).det ≠ 0 := hval _
    change ((y⁻¹ : G n).val * x).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero h1 hx
  have hint : ∀ i j, Integrable (fun y : G n => ks i y.val * ks' j ((y⁻¹ : G n).val * x)) μ := by
    intro i j
    obtain ⟨hc, R, hR⟩ := hks i
    have hcont : Continuous (fun y : G n => ks i y.val * ks' j ((y⁻¹ : G n).val * x)) := by
      have h1 : Continuous (fun y : G n => ks i y.val) := hc.comp_continuous hcv hval
      have h2 : Continuous (fun y : G n => ks' j ((y⁻¹ : G n).val * x)) :=
        (hks' j).1.comp_continuous (hcinv.mul continuous_const) hmem
      exact h1.mul h2
    have hsupp : HasCompactSupport (fun y : G n => ks i y.val * ks' j ((y⁻¹ : G n).val * x)) := by
      refine HasCompactSupport.intro ((hL n).2.2.2.2.1 R) ?_
      intro y hy
      have hy' : R < lg y.val := not_le.1 hy
      simp [hR y.val (hval y) hy']
    exact hcont.integrable_of_hasCompactSupport hsupp
  have hpt : (fun y : G n => k y.val * k' ((y⁻¹ : G n).val * x))
      = fun y : G n => ∑ i, ∑ j, (c i * c' j) • (ks i y.val * ks' j ((y⁻¹ : G n).val * x)) := by
    funext y
    rw [hk y.val (hval y), hk' _ (hmem y), Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_mul_smul_comm]
  have hi : ∀ i ∈ (Finset.univ : Finset ι), Integrable
      (fun y : G n => ∑ j, (c i * c' j) • (ks i y.val * ks' j ((y⁻¹ : G n).val * x))) μ :=
    fun i _ => MeasureTheory.integrable_finsetSum _ fun j _ => (hint i j).smul (c i * c' j)
  unfold conv
  rw [hpt, MeasureTheory.integral_finsetSum _ hi]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hj : ∀ j ∈ (Finset.univ : Finset ι'), Integrable
      (fun y : G n => (c i * c' j) • (ks i y.val * ks' j ((y⁻¹ : G n).val * x))) μ :=
    fun j _ => (hint i j).smul (c i * c' j)
  rw [MeasureTheory.integral_finsetSum _ hj]
  exact Finset.sum_congr rfl fun j _ => integral_smul (c i * c' j) _

end GlobalTheory.CompanionTheory.WaveMult
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelMultiplierLinearStatement

section

@[expose] public section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem _root_.GlobalTheory.T.kernel_multiplier_linear : LgFacts → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n) {ι ι' : Type} [Fintype ι] [Fintype ι'] (c : ι → ℂ) (c' : ι' → ℂ) (ks : ι → Mat n → (E.V →L[ℂ] E.V)) (ks' : ι' → Mat n → (E.V →L[ℂ] E.V)) (k k' : Mat n → (E.V →L[ℂ] E.V)), (∀ i, KReg (ks i)) → (∀ j, KReg (ks' j)) → (∀ y ∈ GLs n, k y = ∑ i, c i • ks i y) → (∀ y ∈ GLs n, k' y = ∑ j, c' j • ks' j y) → ∀ x ∈ GLs n, conv μ E k k' x = ∑ i, ∑ j, (c i * c' j) • conv μ E (ks i) (ks' j) x := by
  first | exact @GlobalTheory.CompanionTheory.WaveMult.conv_eq_sum_of_kernels | exact GlobalTheory.CompanionTheory.WaveMult.conv_eq_sum_of_kernels | (intros; apply GlobalTheory.CompanionTheory.WaveMult.conv_eq_sum_of_kernels <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveKernelDecompositionStatement

section

@[expose] public section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem _root_.GlobalTheory.T.wave_kernel_decomposition : LgFacts → Unimod → RCalc → WaveSpeed → WaveEx → KerUniq → KerOne → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n) (w : List (Bool × ℕ)) (g : ℝ → ℝ) (T : ℝ) (k : Mat n → (E.V →L[ℂ] E.V)), IsBump g T → IsKer μ E w g k → ∃ (N : ℕ) (c : Fin N → ℂ) (w₁ : Fin N → List (Bool × ℕ)) (K : Fin N → Mat n → (E.V →L[ℂ] E.V)), (∀ i, IsKer μ E (w₁ i) g (K i)) ∧ (haveI := FiniteDimensional.complete ℂ E.V; ∀ y ∈ GLs n, ContinuousLinearMap.adjoint (k y⁻¹) = ∑ i, c i • K i y) ∧ ∀ χ : Inf n, IsHerm χ → conj (zVal w χ) = ∑ i, c i * zVal (w₁ i) χ := by
  first | exact @GlobalTheory.CompanionTheory.WaveMult.KerAdj.kernel_adjoint | exact GlobalTheory.CompanionTheory.WaveMult.KerAdj.kernel_adjoint | (intros; apply GlobalTheory.CompanionTheory.WaveMult.KerAdj.kernel_adjoint <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveKernelWordOrderSwap

section

@[expose] public section

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult.KerSwap

theorem isKer_swap : WaveSpeed → RCalc → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n) (w w' : List (Bool × ℕ)) (g : ℝ → ℝ) (T : ℝ) (K : Mat n → (E.V →L[ℂ] E.V)), IsBump g T → IsKer μ E (w ++ w') g K → IsKer μ E (w' ++ w) g K := by
  intro hW hR n _ _ μ _ E w w' g T K hg hK
  refine ⟨hK.1, hK.2.1, hK.2.2.1, fun u hu x hx => ?_⟩
  rw [hK.2.2.2 u hu x hx]
  have hs : ContDiffOn ℝ ∞ (fun x' => ∫ t : ℝ, (g t : ℂ) • u t x') (GLs n) := by
    have h1 := ((GlobalTheory.CompanionTheory.WaveMult.WaveAvg.isWave_avg hW n E u g T hu hg).2.1 0).1
    simpa only [zero_add] using h1
  exact GlobalTheory.CompanionTheory.WaveMult.Swap.zOp_swap hR n w w' _ hs x hx

end GlobalTheory.CompanionTheory.WaveMult.KerSwap
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveKernelWordOrderSwapStatement

section

@[expose] public section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem _root_.GlobalTheory.T.wave_kernel_word_order_swap : WaveSpeed → RCalc → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n) (w w' : List (Bool × ℕ)) (g : ℝ → ℝ) (T : ℝ) (K : Mat n → (E.V →L[ℂ] E.V)), IsBump g T → IsKer μ E (w ++ w') g K → IsKer μ E (w' ++ w) g K := by
  first | exact @GlobalTheory.CompanionTheory.WaveMult.KerSwap.isKer_swap | exact GlobalTheory.CompanionTheory.WaveMult.KerSwap.isKer_swap | (intros; apply GlobalTheory.CompanionTheory.WaveMult.KerSwap.isKer_swap <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AsmMultMain

section

@[expose] public section

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult

theorem asmMult_main : AsmMult := by
  intro hL hU hR hS hE hQ h1 n _ _ μ _ E k k' val val' T T' hk hk'
  obtain ⟨m, c, w, g, ks, hb, hs, hv⟩ := hk
  obtain ⟨m', c', w', g', ks', hb', hs', hv'⟩ := hk'
  have hreg : ∀ i, KReg (ks i) := fun i => ⟨(hb i).2.1.continuousOn, (hb i).2.2.1⟩
  have hreg' : ∀ i, KReg (ks' i) := fun i => ⟨(hb' i).2.1.continuousOn, (hb' i).2.2.1⟩
  have hbp : ∀ p : Fin m × Fin m', IsBump (gconv (g p.1) (g' p.2)) (T + T') :=
    fun p => GlobalTheory.T.bump_convolution_support _ _ _ _ (hb p.1).1 (hb' p.2).1
  choose K hK using fun p : Fin m × Fin m' => h1 n μ E (w p.1 ++ w' p.2) (gconv (g p.1) (g' p.2)) (T + T') (hbp p)
  have hconv : ∀ y ∈ GLs n, conv μ E k k' y = ∑ p : Fin m × Fin m', (c p.1 * c' p.2) • K p y := by
    intro y hy
    rw [GlobalTheory.T.kernel_multiplier_linear hL n μ E c c' ks ks' k k' hreg hreg' hs hs' y hy, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [GlobalTheory.T.wave_kernel_convolution hL hU hR hS hE hQ n μ E (w i) (w' j) (g i) (g' j) T T' (ks i) (ks' j) (K (i, j))
      (hb i).1 (hb' j).1 (hb i).2 (hb' j).2 (hK (i, j)) y hy]
  have hconv' : ∀ y ∈ GLs n, conv μ E k' k y = ∑ p : Fin m × Fin m', (c p.1 * c' p.2) • K p y := by
    intro y hy
    rw [GlobalTheory.T.kernel_multiplier_linear hL n μ E c' c ks' ks k' k hreg' hreg hs' hs y hy, Finset.sum_comm, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have hsw := GlobalTheory.T.wave_kernel_word_order_swap hS hR n μ E (w i) (w' j) _ (T + T') (K (i, j)) (hbp (i, j)) (hK (i, j))
    rw [gconv_comm] at hsw
    rw [GlobalTheory.T.wave_kernel_convolution hL hU hR hS hE hQ n μ E (w' j) (w i) (g' j) (g i) T' T (ks' j) (ks i) (K (i, j))
      (hb' j).1 (hb i).1 (hb' j).2 (hb i).2 hsw y hy, mul_comm]
  refine ⟨?_, fun y hy => by rw [hconv y hy, hconv' y hy], ?_,
    GlobalTheory.T.kernel_multiplier_on_eigenfunction hL n μ E k val T ⟨m, c, w, g, ks, hb, hs, hv⟩⟩
  · refine isMult_of_fintype μ E (fun p : Fin m × Fin m' => c p.1 * c' p.2) (fun p => w p.1 ++ w' p.2)
      (fun p => gconv (g p.1) (g' p.2)) K (fun p => ⟨hbp p, hK p⟩) hconv fun χ => ?_
    rw [Pi.mul_apply, hv χ, hv' χ, Finset.sum_mul_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [zVal_append, ← GlobalTheory.T.cosh_transform_convolution _ _ _ _ _ (hb i).1 (hb' j).1]
    ring
  · haveI := FiniteDimensional.complete ℂ E.V
    choose N d w₁ K₁ hK₁ hadj hval using fun i =>
      GlobalTheory.T.wave_kernel_decomposition hL hU hR hS hE hQ h1 n μ E (w i) (g i) T (ks i) (hb i).1 (hb i).2
    refine ⟨fun χ => ∑ q : (Σ i, Fin (N i)), (conj (c q.1) * d q.1 q.2) * zVal (w₁ q.1 q.2) χ * coshT (g q.1) (cas χ), ?_, ?_⟩
    · refine isMult_of_fintype μ E (fun q : (Σ i, Fin (N i)) => conj (c q.1) * d q.1 q.2) (fun q => w₁ q.1 q.2)
        (fun q => g q.1) (fun q => K₁ q.1 q.2) (fun q => ⟨(hb q.1).1, hK₁ q.1 q.2⟩) (fun y hy => ?_) fun χ => rfl

      rw [hs _ (inv_mem_GLs hy), map_sum, Fintype.sum_sigma]
      refine Finset.sum_congr rfl fun i _ => ?_
      have := hadj i y hy
      rw [map_smulₛₗ, this, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [smul_smul]
    · intro χ hχ

      rw [hv χ, map_sum]
      beta_reduce
      rw [Fintype.sum_sigma]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, map_mul, GlobalTheory.T.cosh_transform_casimir_real n χ (g i) T hχ (hb i).1, hval i χ hχ, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring

end GlobalTheory.CompanionTheory.WaveMult
end
end
end
