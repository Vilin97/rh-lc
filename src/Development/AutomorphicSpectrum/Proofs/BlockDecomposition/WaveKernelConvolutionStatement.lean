module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsMultOfFintype
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ActEqSumOfKernel
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Algebra.Group.Units
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveKernelCompositionStatement
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConvRightEquivariant

section

@[expose] public section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult

theorem conv_right_equivariant : LgFacts → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n) (k k' : Mat n → (E.V →L[ℂ] E.V)), KReg k → KReg k' → (∀ y ∈ GLs n, ∀ k₂ : Matrix.unitaryGroup (Fin n) ℂ, k' (y * k₂.1) = k' y * E.ρ k₂) → ∀ x ∈ GLs n, ∀ k₂ : Matrix.unitaryGroup (Fin n) ℂ, conv μ E k k' (x * k₂.1) = conv μ E k k' x * E.ρ k₂ := by
  intro _ n _ _ μ _ E k k' _ _ hk' x hx k₂
  haveI : CompleteSpace E.V := FiniteDimensional.complete ℂ E.V
  have hinv : E.ρ k₂ * E.ρ k₂⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have hinv' : E.ρ k₂⁻¹ * E.ρ k₂ = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  let L : (E.V →L[ℂ] E.V) ≃L[ℂ] (E.V →L[ℂ] E.V) :=
    ContinuousLinearEquiv.equivOfInverse
      ((ContinuousLinearMap.mul ℂ (E.V →L[ℂ] E.V)).flip (E.ρ k₂))
      ((ContinuousLinearMap.mul ℂ (E.V →L[ℂ] E.V)).flip (E.ρ k₂⁻¹))
      (fun A => by simp [mul_assoc, hinv]) (fun A => by simp [mul_assoc, hinv'])
  have hL : ∀ A, L A = A * E.ρ k₂ := fun A => rfl
  have hmem : ∀ y : G n, (y⁻¹ : G n).val * x ∈ GLs n := by
    intro y
    have h1 : ((y⁻¹ : G n).val).det ≠ 0 := by
      have := (Matrix.isUnit_iff_isUnit_det _).1 (y⁻¹ : G n).isUnit
      exact this.ne_zero
    change ((y⁻¹ : G n).val * x).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero h1 hx
  unfold conv
  rw [← hL, ← L.integral_comp_comm]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  change k y.val * k' ((y⁻¹ : G n).val * (x * k₂.1)) = L (k y.val * k' ((y⁻¹ : G n).val * x))
  rw [hL, ← mul_assoc, hk' _ (hmem y) k₂, mul_assoc]

end GlobalTheory.CompanionTheory.WaveMult
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralConvApplyEq

section

@[expose] public section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult

theorem integral_conv_apply_eq {Γ V : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [T2Space Γ]
    [MeasurableSpace Γ] [BorelSpace Γ] (μ : Measure Γ) [μ.IsHaarMeasure]
    [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    (F F' : Γ → (V →L[ℂ] V)) (φ : Γ → V) (hF : Continuous F) (hF' : Continuous F') (hφ : Continuous φ)
    (cF : HasCompactSupport F) (cF' : HasCompactSupport F') :
    ∫ z, (∫ y, F y * F' (y⁻¹ * z) ∂μ) (φ z) ∂μ = ∫ y, F y (∫ z, F' z (φ (y * z)) ∂μ) ∂μ := by
  have h1 : ∀ z, (∫ y, F y * F' (y⁻¹ * z) ∂μ) (φ z) = ∫ y, F y (F' (y⁻¹ * z) (φ z)) ∂μ := by
    intro z
    have hc : Continuous fun y => F y * F' (y⁻¹ * z) :=
      hF.mul (hF'.comp ((continuous_inv).mul continuous_const))
    have hs : HasCompactSupport fun y => F y * F' (y⁻¹ * z) :=
      HasCompactSupport.intro cF fun y hy => by
        simp [image_eq_zero_of_notMem_tsupport hy]
    have := ContinuousLinearMap.integral_apply (hc.integrable_of_hasCompactSupport (μ := μ) hs) (φ z)
    simpa using this
  simp_rw [h1]
  have hcont : Continuous (Function.uncurry fun (z y : Γ) => F y (F' (y⁻¹ * z) (φ z))) := by
    have a1 : Continuous fun p : Γ × Γ => F p.2 := hF.comp continuous_snd
    have a2 : Continuous fun p : Γ × Γ => F' (p.2⁻¹ * p.1) :=
      hF'.comp (continuous_snd.inv.mul continuous_fst)
    have a3 : Continuous fun p : Γ × Γ => φ p.1 := hφ.comp continuous_fst
    exact a1.clm_apply (a2.clm_apply a3)
  have hsupp : HasCompactSupport (Function.uncurry fun (z y : Γ) => F y (F' (y⁻¹ * z) (φ z))) := by
    have hK : IsCompact ((fun p : Γ × Γ => (p.1 * p.2, p.1)) '' (tsupport F ×ˢ tsupport F')) :=
      (IsCompact.prod cF cF').image ((continuous_fst.mul continuous_snd).prodMk continuous_fst)
    refine HasCompactSupport.intro hK ?_
    rintro ⟨z, y⟩ hzy
    by_cases hy : y ∈ tsupport F
    · by_cases hy' : y⁻¹ * z ∈ tsupport F'
      · exact absurd ⟨(y, y⁻¹ * z), ⟨hy, hy'⟩, by simp⟩ hzy
      · simp [Function.uncurry, image_eq_zero_of_notMem_tsupport hy']
    · simp [Function.uncurry, image_eq_zero_of_notMem_tsupport hy]
  rw [integral_integral_swap_of_hasCompactSupport hcont hsupp]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  change ∫ z, F y (F' (y⁻¹ * z) (φ z)) ∂μ = F y (∫ z, F' z (φ (y * z)) ∂μ)
  rw [← integral_mul_left_eq_self (fun z => F y (F' (y⁻¹ * z) (φ z))) y]
  simp only [inv_mul_cancel_left]
  have hc : Continuous fun z => F' z (φ (y * z)) :=
    hF'.clm_apply (hφ.comp (continuous_const.mul continuous_id))
  have hs : HasCompactSupport fun z => F' z (φ (y * z)) :=
    HasCompactSupport.intro cF' fun z hz => by simp [image_eq_zero_of_notMem_tsupport hz]
  exact (F y).integral_comp_comm (hc.integrable_of_hasCompactSupport (μ := μ) hs)

theorem val_mem_GLs {n : ℕ} (y : G n) : y.val ∈ GLs n :=
  (Matrix.isUnits_det_units y).ne_zero

theorem KReg.continuous_val {n : ℕ} {V : Type} [NormedAddCommGroup V] {k : Mat n → V} (hk : KReg k) :
    Continuous fun y : G n => k y.val :=
  hk.1.comp_continuous Units.continuous_val val_mem_GLs

theorem KReg.hasCompactSupport_val (hL : LgFacts) {n : ℕ} {V : Type} [NormedAddCommGroup V] {k : Mat n → V}
    (hk : KReg k) : HasCompactSupport fun y : G n => k y.val := by
  obtain ⟨R, hR⟩ := hk.2
  refine HasCompactSupport.intro ((hL n).2.2.2.2.1 R) fun y hy => ?_
  exact hR _ (val_mem_GLs y) (not_le.1 hy)

theorem act_conv : LgFacts → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
    (E : KMod n) (k k' : Mat n → (E.V →L[ℂ] E.V)) (f : Mat n → E.V), KReg k → KReg k' →
    ContinuousOn f (GLs n) → ∀ x ∈ GLs n, act μ E (conv μ E k k') f x = act μ E k (act μ E k' f) x := by
  intro hL n _ _ μ _ E k k' f hk hk' hf x hx
  haveI := FiniteDimensional.complete ℂ E.V
  obtain ⟨X, rfl⟩ : ∃ X : G n, X.val = x :=
    (Matrix.isUnit_iff_isUnit_det x).2 (isUnit_iff_ne_zero.2 hx)
  have hφ : Continuous fun z : G n => f (X.val * z.val) :=
    hf.comp_continuous (continuous_const.mul Units.continuous_val) fun z => val_mem_GLs (X * z)
  have key := integral_conv_apply_eq μ (fun y : G n => k y.val) (fun y : G n => k' y.val)
    (fun z : G n => f (X.val * z.val)) hk.continuous_val hk'.continuous_val hφ
    (hk.hasCompactSupport_val hL) (hk'.hasCompactSupport_val hL)
  simp only [Units.val_mul, ← mul_assoc] at key
  exact key

end GlobalTheory.CompanionTheory.WaveMult
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KRegConv

section

@[expose] public section

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult

theorem kReg_conv : LgFacts → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
    (E : KMod n) (k k' : Mat n → (E.V →L[ℂ] E.V)), KReg k → KReg k' → KReg (conv μ E k k') := by
  intro hL n _ _ μ _ E k k' hk hk'
  obtain ⟨hsub, -, -, -, hcG, -, -⟩ := hL n
  obtain ⟨hkc, R, hR⟩ := hk
  obtain ⟨hkc', R', hR'⟩ := hk'
  haveI : CompleteSpace E.V := FiniteDimensional.complete ℂ E.V
  have hval : ∀ y : G n, y.val ∈ GLs n := fun y => by
    have : IsUnit y.val.det := (Matrix.isUnit_iff_isUnit_det _).1 y.isUnit
    exact this.ne_zero
  have hmul : ∀ a ∈ GLs n, ∀ b ∈ GLs n, a * b ∈ GLs n := fun a ha b hb => by
    change (a * b).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero ha hb
  refine ⟨?_, R + R', fun x hx hlt => ?_⟩
  · have hcv : Continuous (fun y : G n => y.val) := Units.continuous_val
    have hci : Continuous (fun y : G n => (y⁻¹ : G n).val) := hcv.comp continuous_inv
    have h1 : ContinuousOn (fun p : Mat n × G n => k p.2.val) (GLs n ×ˢ Set.univ) :=
      hkc.comp (hcv.comp continuous_snd).continuousOn (fun p _ => hval p.2)
    have h2 : ContinuousOn (fun p : Mat n × G n => k' ((p.2⁻¹ : G n).val * p.1)) (GLs n ×ˢ Set.univ) :=
      hkc'.comp ((hci.comp continuous_snd).mul continuous_fst).continuousOn
        (fun p hp => hmul _ (hval _) _ hp.1)
    have h3 : ContinuousOn (Function.uncurry fun (x : Mat n) (y : G n) => k y.val * k' ((y⁻¹ : G n).val * x))
        (GLs n ×ˢ Set.univ) := h1.clm_comp h2
    exact continuousOn_integral_of_compact_support (hcG R) h3 (fun x y _ hy => by
      have : R < lg y.val := not_le.1 hy
      simp [hR _ (hval y) this])
  · have hz : ∀ y : G n, k y.val * k' ((y⁻¹ : G n).val * x) = 0 := fun y => by
      by_cases hy : R < lg y.val
      · simp [hR _ (hval y) hy]
      · have hm : (y⁻¹ : G n).val * x ∈ GLs n := hmul _ (hval _) _ hx
        have hle := hsub _ (hval y) _ hm
        have he : y.val * ((y⁻¹ : G n).val * x) = x := by
          rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
        rw [he] at hle
        have : R' < lg ((y⁻¹ : G n).val * x) := by linarith [not_lt.1 hy]
        rw [hR' _ hm this, mul_zero]
    change ∫ y : G n, k y.val * k' ((y⁻¹ : G n).val * x) ∂μ = 0
    rw [show (fun y : G n => k y.val * k' ((y⁻¹ : G n).val * x)) = fun _ => 0 from funext hz, integral_zero]

end GlobalTheory.CompanionTheory.WaveMult
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveKernelConvolution

section

@[expose] public section

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult

theorem isOpen_GLs_kerconv (n : ℕ) : IsOpen (GLs n) := by
  have hc : Continuous fun g : Mat n => g.det := Continuous.matrix_det continuous_id
  exact isOpen_ne.preimage hc

theorem mul_unitary_mem_GLs_kerconv {n : ℕ} {y : Mat n} (hy : y ∈ GLs n)
    (k₂ : Matrix.unitaryGroup (Fin n) ℂ) : y * k₂.1 ∈ GLs n := by
  have h1 : y.det ≠ 0 := hy
  have h2 : (k₂.1 : Mat n).det ≠ 0 := by
    have h3 : (star k₂.1 * k₂.1 : Mat n) = 1 := Unitary.star_mul_self_of_mem k₂.2
    intro h0
    have h4 := congrArg Matrix.det h3
    rw [Matrix.det_mul, h0, mul_zero, Matrix.det_one] at h4
    exact zero_ne_one h4
  change (y * k₂.1).det ≠ 0
  rw [Matrix.det_mul]
  exact mul_ne_zero h1 h2

theorem act_congr_kerconv {n : ℕ} [MeasurableSpace (G n)] (μ : Measure (G n)) (E : KMod n)
    (k : Mat n → (E.V →L[ℂ] E.V)) {f f' : Mat n → E.V} (h : ∀ x ∈ GLs n, f x = f' x)
    {x : Mat n} (hx : x ∈ GLs n) : act μ E k f x = act μ E k f' x := by
  unfold act
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  have hy : (y.val).det ≠ 0 := by
    have := y.isUnit
    exact ((Matrix.isUnit_iff_isUnit_det _).1 this).ne_zero
  have hxy : x * y.val ∈ GLs n := by
    change (x * y.val).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero hx hy
  simp only [h _ hxy]

theorem one_mem_GLs_kerconv (n : ℕ) : (1 : Mat n) ∈ GLs n := by
  change (1 : Mat n).det ≠ 0
  simp

theorem conv_eq_of_isKer : LgFacts → Unimod → RCalc → WaveSpeed → WaveEx → KerUniq → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n) (w w' : List (Bool × ℕ)) (g g' : ℝ → ℝ) (T T' : ℝ) (k k' K : Mat n → (E.V →L[ℂ] E.V)), IsBump g T → IsBump g' T' → IsKer μ E w g k → IsKer μ E w' g' k' → IsKer μ E (w ++ w') (gconv g g') K → ∀ y ∈ GLs n, conv μ E k k' y = K y := by
  intro hLg _ hRC hWS hWE hKU n _ _ μ _ E w w' g g' T T' k k' K hg hg' hk hk' hK y hy
  have rk : KReg k := ⟨hk.1.continuousOn, hk.2.1⟩
  have rk' : KReg k' := ⟨hk'.1.continuousOn, hk'.2.1⟩
  have rK : KReg K := ⟨hK.1.continuousOn, hK.2.1⟩
  have rc : KReg (conv μ E k k') := kReg_conv hLg n μ E k k' rk rk'
  have hk'eq : ∀ y ∈ GLs n, ∀ k₂ : Matrix.unitaryGroup (Fin n) ℂ, k' (y * k₂.1) = k' y * E.ρ k₂ := by
    intro y hy k₂
    have := hk'.2.2.1 y hy 1 k₂
    simpa using this
  have hKeq : ∀ y ∈ GLs n, ∀ k₂ : Matrix.unitaryGroup (Fin n) ℂ, K (y * k₂.1) = K y * E.ρ k₂ := by
    intro y hy k₂
    have := hK.2.2.1 y hy 1 k₂
    simpa using this
  have hceq := conv_right_equivariant hLg n μ E k k' rk rk' hk'eq
  have key := hKU n μ E (fun y => conv μ E k k' y - K y) (GLs n) (isOpen_GLs_kerconv n) subset_rfl
    (fun y hy k₂ => mul_unitary_mem_GLs_kerconv hy k₂) (rc.1.sub rK.1)
    (fun y hy k₂ => by
      simp only [hceq y hy k₂, hKeq y hy k₂]
      exact (sub_mul _ _ _).symm)
    (fun f hf hc _ => by
      obtain ⟨u, hu, hu0⟩ := hWE n E f hf
      obtain ⟨v, hv, hv0, hvc⟩ := GlobalTheory.T.wave_kernel_composition hRC hWS n E u w w' g g' T T' hu hg hg'
      have h1 := one_mem_GLs_kerconv n
      have hfc : ContinuousOn f (GLs n) := hf.1.continuousOn
      have hlin := act_eq_sum_of_kernel hLg n μ E (ι := Bool) (fun b => if b then 1 else -1)
        (fun b => if b then conv μ E k k' else K) (fun y => conv μ E k k' y - K y) f
        (fun b => by cases b <;> simp [rc, rK])
        (fun y _ => by simp [Fintype.sum_bool, sub_eq_add_neg]) hfc 1 h1
      have hc1 : act μ E (conv μ E k k') f 1 = act μ E k (act μ E k' f) 1 :=
        act_conv hLg n μ E k k' f rk rk' hfc 1 h1
      have hact' : ∀ x ∈ GLs n, act μ E k' f x = v 0 x := by
        intro x hx
        rw [act_congr_kerconv μ E k' (fun z hz => (hu0 z hz).symm) hx, hk'.2.2.2 u hu x hx, hv0 x hx]
      have hc2 : act μ E k (act μ E k' f) 1 = act μ E K f 1 := by
        rw [act_congr_kerconv μ E k hact' h1, hk.2.2.2 v hv 1 h1, hvc 1 h1,
          ← hK.2.2.2 u hu 1 h1]
        exact act_congr_kerconv μ E K hu0 h1
      rw [hlin]
      simp [Fintype.sum_bool, hc1, hc2]) y hy
  exact sub_eq_zero.1 key

end GlobalTheory.CompanionTheory.WaveMult
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveKernelConvolutionStatement

section

@[expose] public section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem _root_.GlobalTheory.T.wave_kernel_convolution : LgFacts → Unimod → RCalc → WaveSpeed → WaveEx → KerUniq → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n) (w w' : List (Bool × ℕ)) (g g' : ℝ → ℝ) (T T' : ℝ) (k k' K : Mat n → (E.V →L[ℂ] E.V)), IsBump g T → IsBump g' T' → IsKer μ E w g k → IsKer μ E w' g' k' → IsKer μ E (w ++ w') (gconv g g') K → ∀ y ∈ GLs n, conv μ E k k' y = K y := by
  first | exact @GlobalTheory.CompanionTheory.WaveMult.conv_eq_of_isKer | exact GlobalTheory.CompanionTheory.WaveMult.conv_eq_of_isKer | (intros; apply GlobalTheory.CompanionTheory.WaveMult.conv_eq_of_isKer <;> assumption)
end
end
