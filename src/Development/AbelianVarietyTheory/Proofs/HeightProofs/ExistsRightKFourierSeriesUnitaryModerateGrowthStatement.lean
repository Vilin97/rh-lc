module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteDimensionalPolyV
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.CompactUnitaryCoordFunMulEqSum
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
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.CompactUnitaryIntegralConjInvariantStatement
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.CompactUnitaryRightDerivConjInvariantAverageEqStatement
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ContDiffMatrixRightInvariantDerivative
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.HasSumCompactUnitaryFourierValueOne
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.KFourierCoefficientRapidDecayStatement
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ToMKExpKEqMatrixExpRealStatement
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ComplexificationHolds
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.HeightProofs.CompactUnitaryCoordFunMulEqSumStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.compactUnitary_fourierKernel_conj_invariant : ∀ {n : ℕ} (ε : Fin n → Bool) (i : ℕ) (e : KG ε → ℂ), GlobalTheory.KFourier.IsKer ε i e → ∀ a k : KG ε, e (a * k * a⁻¹) = e k := by
  first | exact @GlobalTheory.KFourier.isKer_class | exact GlobalTheory.KFourier.isKer_class | (intros; apply GlobalTheory.KFourier.isKer_class <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.HeightProofs.ContDiffMatrixRightInvariantDerivativeStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.contDiff_matrixRightInvariantDerivative : ∀ {n : ℕ} (ε : Fin n → Bool) (d : ℕ) (φ : KG ε → ℂ), φ ∈ GlobalTheory.KFourier.polyV ε d → ∀ X : Mx n, inK ε X → GlobalTheory.KFourier.rder ε [X] φ ∈ GlobalTheory.KFourier.polyV ε d ∧ ∀ k : KG ε, HasDerivAt (fun t : ℝ => φ (k * expK ε X t)) (GlobalTheory.KFourier.rder ε [X] φ k) 0 := by
  first | exact @GlobalTheory.KFourier.rder_mem_and_hasDerivAt | exact GlobalTheory.KFourier.rder_mem_and_hasDerivAt | (intros; apply GlobalTheory.KFourier.rder_mem_and_hasDerivAt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.HeightProofs.HasDerivAtMatrixExpEntryReal

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KFourier

open MeasureTheory

variable {n : ℕ}

theorem coord_mul_eq_sum (ε : Fin n → Bool) (c : Fin n × Fin n × Bool) (a k : KG ε) :
    coord ε c (a * k) = ∑ l : Fin n, coord ε (c.1, l, c.2.2) a * coord ε (l, c.2.1, c.2.2) k := by
  simp only [coord, toMK_mul, Matrix.mul_apply]
  split_ifs
  · rfl
  · rw [star_sum]; exact Finset.sum_congr rfl fun l _ => by rw [star_mul', mul_comm]

theorem integrable_muK_of_continuous {ε : Fin n → Bool} {F : KG ε → ℂ} (hF : Continuous F) :
    Integrable F (muK ε) :=
  hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace F)

theorem conv_mono_mem (ε : Fin n → Bool) (s : List (Fin n × Fin n × Bool)) :
    ∀ (d : ℕ), s.length ≤ d → ∀ h : KG ε → ℂ, Continuous h →
      (fun k' : KG ε => ∫ k, mono ε s (k'⁻¹ * k) * h k ∂(muK ε)) ∈ polyV ε d := by
  induction s with
  | nil =>
    intro d _ h _
    simpa [mono] using const_mem ε d (∫ k, h k ∂(muK ε))
  | cons c s ih =>
    intro d hd h hh
    have hd' : s.length + 1 ≤ d := by simpa using hd
    have e : (fun k' : KG ε => ∫ k, mono ε (c :: s) (k'⁻¹ * k) * h k ∂(muK ε)) =
        ∑ l : Fin n, (fun k' : KG ε => coord ε (c.1, l, c.2.2) k'⁻¹) *
          (fun k' : KG ε => ∫ k, mono ε s (k'⁻¹ * k) * (coord ε (l, c.2.1, c.2.2) k * h k) ∂(muK ε)) := by
      funext k'
      simp only [Finset.sum_apply, Pi.mul_apply]
      simp only [← integral_const_mul]
      rw [← integral_finsetSum]
      · refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
        have h1 : mono ε (c :: s) (k'⁻¹ * k) = coord ε c (k'⁻¹ * k) * mono ε s (k'⁻¹ * k) := by simp [mono]
        simp only [h1, coord_mul_eq_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun l _ => by ring
      · intro l _
        refine integrable_muK_of_continuous (continuous_const.mul ?_)
        exact ((continuous_mono ε s).comp (continuous_const.mul continuous_id)).mul
          ((continuous_coord ε _).mul hh)
    rw [e]
    refine Submodule.sum_mem _ fun l _ => ?_
    exact polyV_mono ε (show 1 + (d - 1) ≤ d by omega)
      (mul_mem (coord_inv_mem ε _) (ih (d - 1) (by omega) _ ((continuous_coord ε _).mul hh)))

theorem conv_mem {ε : Fin n → Bool} {d : ℕ} {e : KG ε → ℂ} (he : e ∈ polyV ε d) {h : KG ε → ℂ}
    (hh : Continuous h) : (fun k' : KG ε => ∫ k, e (k'⁻¹ * k) * h k ∂(muK ε)) ∈ polyV ε d := by
  induction he using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨s, hs, rfl⟩ := hx
    exact conv_mono_mem ε s d hs h hh
  | zero =>
    simpa using const_mem ε d 0
  | add x y hx hy ihx ihy =>
    convert add_mem ihx ihy using 1
    funext k'
    simp only [Pi.add_apply, add_mul]
    refine integral_add (integrable_muK_of_continuous ?_) (integrable_muK_of_continuous ?_)
    · exact ((continuous_of_mem (d := d) hx).comp (continuous_const.mul continuous_id)).mul hh
    · exact ((continuous_of_mem (d := d) hy).comp (continuous_const.mul continuous_id)).mul hh
  | smul a x _ ih =>
    convert Submodule.smul_mem _ a ih using 1
    funext k'
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]

theorem avgK_mem : ∀ {n : ℕ} (ε : Fin n → Bool) (i : ℕ) (e : KG ε → ℂ), e ∈ GlobalTheory.KFourier.polyV ε i →
    ∀ f : Mx n → ℂ, ContinuousOn f (UJset ε) → ∀ y ∈ UJset ε,
      GlobalTheory.KFourier.avgK ε e f y ∈ GlobalTheory.KFourier.polyV ε i := by
  intro n ε i e he f hf y hy
  have hh : Continuous fun k : KG ε => f (y * toMK k) :=
    hf.comp_continuous (continuous_const.mul (GlobalTheory.TypeSum.continuous_toMK ε))
      fun k => GlobalTheory.TypeSum.mul_mem_UJ hy (GlobalTheory.TypeSum.K_le_UJ (GlobalTheory.TypeSum.toMK_mem_K k))
  convert conv_mem he hh using 1
  funext k'
  rw [← integral_mul_left_eq_self (μ := muK ε) _ k']
  simp only [avgK, inv_mul_cancel_left, toMK_mul, Matrix.mul_assoc]

end GlobalTheory.KFourier

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.HeightProofs.HasDerivAtMatrixExpEntryRealStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.compactUnitaryAverage_mem_polyV : ∀ {n : ℕ} (ε : Fin n → Bool) (i : ℕ) (e : KG ε → ℂ), e ∈ GlobalTheory.KFourier.polyV ε i → ∀ f : Mx n → ℂ, ContinuousOn f (UJset ε) → ∀ y ∈ UJset ε, GlobalTheory.KFourier.avgK ε e f y ∈ GlobalTheory.KFourier.polyV ε i := by
  first | exact @GlobalTheory.KFourier.avgK_mem | exact GlobalTheory.KFourier.avgK_mem | (intros; apply GlobalTheory.KFourier.avgK_mem <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.HeightProofs.HasSumCompactUnitaryFourierValueOneStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.hasSum_compactUnitaryFourier_value_one : ∀ {n : ℕ} (ε : Fin n → Bool) (e : ℕ → KG ε → ℂ), (∀ i, GlobalTheory.KFourier.IsKer ε i (e i)) → ∀ g : KG ε → ℂ, Continuous g → ∀ b : ℕ → ℝ, Summable b → (∀ i (k' : KG ε), ‖∫ k, e i k * g (k' * k) ∂(muK ε)‖ ≤ b i) → HasSum (fun i => ∫ k, e i k * g k ∂(muK ε)) (g 1) := by
  first | exact @GlobalTheory.KFourier.hasSum_kFourier | exact GlobalTheory.KFourier.hasSum_kFourier | (intros; apply GlobalTheory.KFourier.hasSum_kFourier <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsRightKFourierSeriesUnitaryModerateGrowth

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KFourier
open MeasureTheory Matrix Formalism.REAL GlobalTheory.TypeSum

variable {n : ℕ}

theorem rder_mem (ε : Fin n → Bool) (d : ℕ) (φ : KG ε → ℂ) (hφ : φ ∈ polyV ε d) (l : List (Mx n))
    (hl : ∀ X ∈ l, inK ε X) : rder ε l φ ∈ polyV ε d := by
  induction l with
  | nil => exact hφ
  | cons X l ih =>
    have h := (GlobalTheory.T.contDiff_matrixRightInvariantDerivative ε d _ (ih fun Y hY => hl Y (List.mem_cons_of_mem _ hY)) X (hl X List.mem_cons_self)).1
    exact h

theorem hs_mul_toMK (ε : Fin n → Bool) (y : Mx n) (k : KG ε) : hs (y * toMK k) = hs y :=
  ((hermitian_small_ball n ε).2 y _ k.2).1

theorem toMK_expK_mul (ε : Fin n → Bool) (X : Mx n) (hK : inK ε X) (t : ℝ) (x : KG ε) :
    toMK (expK ε X t * x) = NormedSpace.exp (t • X) * toMK x := by
  rw [toMK_mul, toMK_expK hK, Complex.coe_smul]

theorem summable_listSum {ι : Type} (U : List ι) (b : ι → ℕ → ℝ) (hb : ∀ u ∈ U, Summable (b u)) :
    Summable fun i => (U.map fun u => b u i).sum := by
  induction U with
  | nil => simp
  | cons u U ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (hb u List.mem_cons_self).add (ih fun v hv => hb v (List.mem_cons_of_mem _ hv))

theorem exists_rightKFourier : ∀ (n : ℕ) (ε : Fin n → Bool), ∃ e : ℕ → (Formalism.REAL.KG ε → ℂ), (∀ i, Continuous (e i)) ∧
    (∀ i, KFinFun ε (e i)) ∧ ∀ f : Mx n → ℂ, ContinuousOn f (UJset ε) → UMG ε f →
    ∃ (N : ℕ) (Φ : ℕ → List (Mx n) → Mx n → ℂ) (B : ℕ → ℕ → ℝ),
      (∀ i, ∀ y ∈ UJset ε, Φ i [] y = ∫ k, e i k * f (y * Formalism.REAL.toMK k) ∂(Formalism.REAL.muK ε)) ∧
      (∀ i (l : List (Mx n)), (∀ Y ∈ l, Y ∈ lieSet ε ∧ Yᴴ = -Y) → ∀ X : Mx n, X ∈ lieSet ε → Xᴴ = -X →
        ∀ y ∈ UJset ε, HasDerivAt (fun t : ℝ => Φ i l (y * NormedSpace.exp (t • X))) (Φ i (X :: l) y) 0) ∧
      (∀ i k (w : List (Mx n)), w.length ≤ k → (∀ X ∈ w, X ∈ lieSet ε ∧ Xᴴ = -X ∧ hs X ≤ 1) →
        ∀ y ∈ UJset ε, ‖Φ i w y‖ ≤ B i k * (1 + hs y) ^ N) ∧
      (∀ k, Summable fun i => B i k) ∧
      ∀ y ∈ UJset ε, HasSum (fun i => ∫ k, e i k * f (y * Formalism.REAL.toMK k) ∂(Formalism.REAL.muK ε)) (f y) := by
  intro n ε
  have hker : ∀ i, IsKer ε i (kerE ε i) := fun i => isKer_kerE (GlobalTheory.T.exists_compactUnitary_fourierKernel ε i)
  refine ⟨kerE ε, fun i => continuous_of_mem (hker i).1, fun i => kFinFun_of_mem (hker i).1, ?_⟩
  intro f hf hU
  obtain ⟨N, F, hF0, hFd, hFg⟩ := hU
  have hcF : ContinuousOn (F []) (UJset ε) := hf.congr fun g hg => hF0 g hg
  have hdec : ∀ u : List (Mx n), ∃ b : ℕ → ℝ, Summable b ∧ ((∀ X ∈ u, inK ε X) → ∀ i, ∀ y ∈ UJset ε,
      ‖∫ k, kerE ε i k * F u (y * toMK k) ∂(muK ε)‖ ≤ b i * (1 + hs y) ^ N) := by
    intro u
    by_cases hu : ∀ X ∈ u, inK ε X
    · obtain ⟨b, hb, hb'⟩ := GlobalTheory.T.kFourier_coefficient_rapid_decay ε N F hFd hFg hcF (kerE ε) hker u hu
      exact ⟨b, hb, fun _ => hb'⟩
    · exact ⟨0, summable_zero, fun h => absurd h hu⟩
  choose b hbs hbb using hdec
  choose U C hC0 hUK hC using GlobalTheory.T.rightDeriv_norm_le_finite_words_bound ε
  have hQ : ∀ i, ∀ y ∈ UJset ε, avgK ε (kerE ε i) f y ∈ polyV ε i := fun i y hy =>
    GlobalTheory.T.compactUnitaryAverage_mem_polyV ε i _ (hker i).1 f hf y hy
  have hbound : ∀ i m (w : List (Mx n)), w.length ≤ m → (∀ X ∈ w, X ∈ GlobalTheory.SmoothGlob.lieSet ε ∧ Xᴴ = -X ∧ hs X ≤ 1) →
      ∀ y ∈ UJset ε, ‖rder ε w (avgK ε (kerE ε i) f y) 1‖ ≤ C m * ((U m).map fun u => b u i).sum * (1 + hs y) ^ N := by
    intro i m w hw hwX y hy
    have hwK : ∀ X ∈ w, inK ε X ∧ hs X ≤ 1 := fun X hX =>
      ⟨inK_of_skew (hwX X hX).1 (hwX X hX).2.1, (hwX X hX).2.2⟩
    have h1 := hC m i _ (hQ i y hy) w hw hwK
    have h2 : ((U m).map fun u => ‖rder ε u (avgK ε (kerE ε i) f y) 1‖).sum ≤
        ((U m).map fun u => b u i * (1 + hs y) ^ N).sum := by
      refine List.sum_le_sum fun u hu => ?_
      rw [GlobalTheory.T.compactUnitaryRightDeriv_conjInvariantAverage_eq ε N F hFd hFg f hf hF0 _ (continuous_of_mem (hker i).1) (GlobalTheory.T.compactUnitary_fourierKernel_conj_invariant ε i _ (hker i)) u (hUK m u hu) y hy]
      exact hbb u (hUK m u hu) i y hy
    rw [List.sum_map_mul_right] at h2
    calc _ ≤ _ := h1
      _ ≤ C m * (((U m).map fun u => b u i).sum * (1 + hs y) ^ N) := mul_le_mul_of_nonneg_left h2 (hC0 m)
      _ = _ := by ring
  refine ⟨N, fun i l y => rder ε l (avgK ε (kerE ε i) f y) 1,
    fun i m => C m * ((U m).map fun u => b u i).sum, ?_, ?_, hbound, ?_, ?_⟩
  · intro i y hy
    simp [avgK, toMK_one]
  · intro i l hl X hX hXs y hy
    have hK := inK_of_skew hX hXs
    have hlK : ∀ Y ∈ l, inK ε Y := fun Y hY => inK_of_skew (hl Y hY).1 (hl Y hY).2
    have hR := rder_mem ε i _ (hQ i y hy) l hlK
    have e1 : (fun t : ℝ => rder ε l (avgK ε (kerE ε i) f (y * NormedSpace.exp (t • X))) 1) =
        fun t : ℝ => rder ε l (avgK ε (kerE ε i) f y) (1 * expK ε X t) := by
      funext t
      rw [one_mul, ← mul_one (expK ε X t), ← rder_left ε l _ (expK ε X t) 1]
      congr 1
      funext x
      unfold avgK
      rw [toMK_expK_mul ε X hK t x]
      simp only [Matrix.mul_assoc]
    show HasDerivAt (fun t : ℝ => rder ε l (avgK ε (kerE ε i) f (y * NormedSpace.exp (t • X))) 1)
      (rder ε [X] (rder ε l (avgK ε (kerE ε i) f y)) 1) 0
    rw [e1]
    exact (GlobalTheory.T.contDiff_matrixRightInvariantDerivative ε i _ hR X hK).2 1
  · intro m
    exact (summable_listSum (U m) b fun u _ => hbs u).mul_left (C m)
  · intro y hy
    have key := GlobalTheory.T.hasSum_compactUnitaryFourier_value_one ε (kerE ε) hker (fun k => f (y * toMK k)) ?_ (fun i => C 0 * ((U 0).map fun u => b u i).sum * (1 + hs y) ^ N)
      (((summable_listSum (U 0) b fun u _ => hbs u).mul_left (C 0)).mul_right _) ?_
    · simpa [toMK_one] using key
    · exact hf.comp_continuous ((continuous_const.mul (continuous_toMK ε))) fun k => mul_mem_UJ hy (K_le_UJ k.2)
    · intro i k'
      have hyk : y * toMK k' ∈ UJset ε := mul_mem_UJ hy (K_le_UJ k'.2)
      have := hbound i 0 [] le_rfl (by simp) _ hyk
      rw [hs_mul_toMK] at this
      simpa [avgK, toMK_one, toMK_mul, Matrix.mul_assoc] using this

end GlobalTheory.KFourier

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsRightKFourierSeriesUnitaryModerateGrowthStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_rightKFourierSeries_unitary_moderateGrowth : ∀ (n : ℕ) (ε : Fin n → Bool), ∃ e : ℕ → (Formalism.REAL.KG ε → ℂ), (∀ i, Continuous (e i)) ∧
    (∀ i, KFinFun ε (e i)) ∧ ∀ f : Mx n → ℂ, ContinuousOn f (UJset ε) → UMG ε f →
    ∃ (N : ℕ) (Φ : ℕ → List (Mx n) → Mx n → ℂ) (B : ℕ → ℕ → ℝ),
      (∀ i, ∀ y ∈ UJset ε, Φ i [] y = ∫ k, e i k * f (y * Formalism.REAL.toMK k) ∂(Formalism.REAL.muK ε)) ∧
      (∀ i (l : List (Mx n)), (∀ Y ∈ l, Y ∈ lieSet ε ∧ Yᴴ = -Y) → ∀ X : Mx n, X ∈ lieSet ε → Xᴴ = -X →
        ∀ y ∈ UJset ε, HasDerivAt (fun t : ℝ => Φ i l (y * NormedSpace.exp (t • X))) (Φ i (X :: l) y) 0) ∧
      (∀ i k (w : List (Mx n)), w.length ≤ k → (∀ X ∈ w, X ∈ lieSet ε ∧ Xᴴ = -X ∧ hs X ≤ 1) →
        ∀ y ∈ UJset ε, ‖Φ i w y‖ ≤ B i k * (1 + hs y) ^ N) ∧
      (∀ k, Summable fun i => B i k) ∧
      ∀ y ∈ UJset ε, HasSum (fun i => ∫ k, e i k * f (y * Formalism.REAL.toMK k) ∂(Formalism.REAL.muK ε)) (f y) := by
  first | exact @GlobalTheory.KFourier.exists_rightKFourier | exact GlobalTheory.KFourier.exists_rightKFourier | (intros; apply GlobalTheory.KFourier.exists_rightKFourier <;> assumption)
end
end
