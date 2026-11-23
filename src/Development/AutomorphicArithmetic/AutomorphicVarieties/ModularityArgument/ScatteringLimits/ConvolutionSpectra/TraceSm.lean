module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.Carries
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.AvApprox
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.BandTC
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ConvAdj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.CobLaws
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.SvSpec
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Convolution
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Analysis.Fourier.Notation
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.NAll
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ProjLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.KvSpec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.Planch
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.TailB
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.TraceFar
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.AvSpec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.CarLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ProjLaws
public import GroundTheory.AutomorphicForms.TraceClass
import Mathlib.RingTheory.PiTensorProduct
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.Carries
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.TruncatedCuspIrreducibility.ScatteringLimits
import Mathlib.Tactic.Linter.Style
public import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.CorOne

section

@[expose] public section

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.corOne :
    ∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] (φ : ℝ → ℂ) (e n : V) (c : ℝ), Continuous φ → HasCompactSupport φ →
      Tendsto (fun a => ∫ s in (c - a)..(c + a), ⟪sv V φ e, sh V s (one V n)⟫_ℂ) atTop (𝓝 (conj (∫ x, φ x) * ⟪e, n⟫_ℂ)) := by
  intro V _ _ _ _ φ e n c h1 h2
  have iφ : Integrable φ := h1.integrable_of_hasCompactSupport h2
  have hf : Integrable fun x => conj (φ (-x)) := (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp iφ.comp_neg
  have hg : Integrable ((Ioc (0 : ℝ) 1).indicator fun _ => ⟪e, n⟫_ℂ) := (integrable_indicator_iff measurableSet_Ioc).2 (by simp)
  have e1 : ∀ s, ⟪sv V φ e, sh V s (one V n)⟫_ℂ = convolution (fun x => conj (φ (-x)))
      ((Ioc (0 : ℝ) 1).indicator fun _ => ⟪e, n⟫_ℂ) (ContinuousLinearMap.mul ℂ ℂ) volume s := fun s => by
    rw [convolution_def, L2.inner_def, ← integral_neg_eq_self _ volume]
    rw [← integral_neg_eq_self (fun t => ContinuousLinearMap.mul ℂ ℂ (conj (φ (-t)))
      ((Ioc (0 : ℝ) 1).indicator (fun _ => ⟪e, n⟫_ℂ) (s - t))) volume, integral_neg_eq_self (fun a => ⟪sv V φ e a, sh V s (one V n) a⟫_ℂ) volume]
    refine integral_congr_ae ?_
    filter_upwards [((svSpec (V := V)).1 φ (h1.memLp_of_hasCompactSupport h2) e).1, sh_ae V s (one V n),
      (measurePreserving_add_right volume s).quasiMeasurePreserving.ae ((svSpec (V := V)).2 n).1] with x a1 a2 a3
    rw [a1, a2, a3, sub_neg_eq_add, add_comm s x, inner_smul_left]
    by_cases b : x + s ∈ Ioc (0 : ℝ) 1 <;> simp [b]
  simp only [e1]
  have t := intervalIntegral_tendsto_integral (hf.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hg)
    (a := fun a : ℝ => c - a) (b := fun a : ℝ => c + a) (l := atTop)
    (tendsto_atBot_add_const_left _ c tendsto_neg_atTop_atBot) (tendsto_atTop_add_const_left _ c tendsto_id)
  rw [integral_convolution _ hf hg, integral_indicator measurableSet_Ioc, integral_conj, integral_neg_eq_self] at t
  simpa using t
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.CorLim

section

@[expose] public section

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.corLim :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (M : Sc H V W) (N : W →ₗ[ℂ] V), M.IsN N → ∀ (φ : ℝ → ℂ) (e : V) (p : L W) (c : ℝ), Continuous φ → HasCompactSupport φ → Bdd p →
      Continuous (M.cor φ e p) ∧ Tendsto (fun a => ∫ s in (c - a)..(c + a), M.cor φ e p s) atTop (𝓝 (conj (∫ x, φ x) * ⟪e, N (∫ x, p x)⟫_ℂ)) := by
  intro H _ _ _ V _ _ _ _ W _ _ _ _ M N hN φ e p c h1 h2 hp
  have hc : ∀ a b : H, Continuous fun s => ⟪a, M.F.U s b⟫_ℂ := fun a b => continuous_const.inner (M.F.cont b)
  refine ⟨hc _ _, ?_⟩
  have t1 := (cobLaws M.F).2.2.2.2.2.2.1 (projLaws M).1 _ (M.J (sv V φ e)) c (nAll M N hN p hp)
  have t2 := corOne φ e (N (∫ x, p x)) c h1 h2
  have t3 := t1.add t2
  rw [zero_add] at t3
  refine t3.congr fun a => ?_
  have e1 : ∀ s, ⟪sv V φ e, sh V s (one V (N (∫ x, p x)))⟫_ℂ = ⟪M.J (sv V φ e), M.F.U s (M.J (one V (N (∫ x, p x))))⟫_ℂ :=
    fun s => by rw [M.hJ, M.J.inner_map_map]
  simp only [e1]
  rw [← intervalIntegral.integral_add ((hc _ _).intervalIntegrable _ _) ((hc _ _).intervalIntegrable _ _)]
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp only [Sc.cor, map_sub, inner_sub_right, sub_add_cancel]
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.TwoProj

section

@[expose] public section

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.twoProj :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (Λ E Λ' E' Y : H →L[ℂ] H), Λ + E = Λ' + E' → Λ ∘L Λ = Λ → E ∘L E = E → Λ' ∘L Λ' = Λ' → E' ∘L E' = E' →
      Λ ∘L E = 0 → E ∘L Λ = 0 → Λ' ∘L E' = 0 → E' ∘L Λ' = 0 → IsTraceClass (Λ ∘L Y ∘L Λ) → IsTraceClass (E ∘L Y) →
      IsTraceClass (Y ∘L E) → IsTraceClass (Y ∘L E') →
      IsTraceClass (Λ' ∘L Y ∘L Λ') ∧ trace (Λ ∘L Y ∘L Λ) + trace (E ∘L Y) = trace (Λ' ∘L Y ∘L Λ') + trace (Y ∘L E') := by
  intro H _ _ _ Λ E Λ' E' Y hs h1 h2 h3 h4 h5 h6 h7 h8 t1 t2 t3 t4
  have key : ∀ A B Z : H →L[ℂ] H, A * A = A → B * B = B → A * B = 0 → B * A = 0 → IsTraceClass ((A + B) * Z * (A + B)) →
      IsTraceClass (A * Z * A) ∧ trace ((A + B) * Z * (A + B)) = trace (A * Z * A) + trace (B * Z * B) := by
    intro A B Z a b ab ba h
    have e1 : A * ((A + B) * Z * (A + B)) * A = A * Z * A := by
      rw [← mul_assoc, ← mul_assoc, mul_add A A, a, ab, add_zero, mul_assoc, add_mul, a, ba, add_zero]
    have e2 : B * ((A + B) * Z * (A + B)) * B = B * Z * B := by
      rw [← mul_assoc, ← mul_assoc, mul_add B A, b, ba, zero_add, mul_assoc, add_mul, b, ab, zero_add]
    set Q := (A + B) * Z * (A + B) with hQ
    have e3 : Q = A * Q + B * Q := by
      rw [← add_mul, hQ, ← mul_assoc, ← mul_assoc, add_mul A B (A + B), mul_add A, mul_add B, a, b, ab, ba, add_zero, zero_add]
    have c : ∀ P : H →L[ℂ] H, P * P = P → trace (P * Q) = trace (P * Q * P) := fun P hP => by
      have := trace_comp_comm (h.comp_left P) P
      change trace (P * (P * Q)) = trace (P * Q * P) at this
      rwa [← mul_assoc, hP] at this
    refine ⟨e1 ▸ (h.comp_left A).comp_right A, ?_⟩
    rw [← e1, ← e2, ← c A a, ← c B b]
    conv_lhs => rw [e3]
    exact trace_add (h.comp_left A) (h.comp_left B)
  have hT : IsTraceClass ((Λ + E) * Y * (Λ + E)) := by
    have : (Λ + E) * Y * (Λ + E) = Λ * (Y * Λ) + (Λ * (Y * E) + E * Y * (Λ + E)) := by noncomm_ring
    rw [this]
    exact t1.add ((t3.comp_left Λ).add (t2.comp_right (Λ + E)))
  obtain ⟨-, k1⟩ := key Λ E Y h1 h2 h5 h6 hT
  rw [hs] at hT k1
  obtain ⟨k2, k3⟩ := key Λ' E' Y h3 h4 h7 h8 hT
  have c1 : trace (E * Y * E) = trace (E * Y) := by
    have := trace_comp_comm t2 E
    change trace (E * (E * Y)) = trace (E * Y * E) at this
    rw [← this, ← mul_assoc]; exact congrArg (fun Z => trace (Z * Y)) h2
  have c2 : trace (E' * Y * E') = trace (Y * E') := by
    have := trace_comp_comm t4 E'
    change trace (E' * (Y * E')) = trace (Y * E' * E') at this
    rw [mul_assoc, this, mul_assoc]; exact congrArg (fun Z => trace (Y * Z)) h4
  refine ⟨k2, ?_⟩
  change trace (Λ * (Y * Λ)) + trace (E * Y) = trace (Λ' * (Y * Λ')) + trace (Y * E')
  rw [← mul_assoc, ← mul_assoc, ← c1, ← c2, ← k1, k3]
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.TraceId

section

@[expose] public section

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.traceId :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (M : Sc H V W) (X : H →L[ℂ] H) (κ : ℝ → V →L[ℂ] W), Ker κ → M.Carries X κ → ∀ (ψ : ℝ → ℝ) (δ T a : ℝ), Bump ψ (-δ) 0 → M.T₀ ≤ T → 0 ≤ a →
      IsTraceClass (M.abelian₂ T T ∘L (M.F.av (fun t => (ψ t : ℂ)) ∘L X) ∘L M.abelian₂ T T) →
      trace (M.abelian₂ T T ∘L (M.F.av (fun t => (ψ t : ℂ)) ∘L X) ∘L M.abelian₂ T T) + trace (M.P' (Ioc T (T + a)) ∘L (M.F.av (fun t => (ψ t : ℂ)) ∘L X)) =
        trace (M.abelian₂ T T ∘L M.F.U (-(2 * a)) ∘L (M.F.av (fun t => (ψ t : ℂ)) ∘L X) ∘L M.abelian₂ T T) + trace ((M.F.av (fun t => (ψ t : ℂ)) ∘L X) ∘L M.P (Ioc (T - a) T)) := by
  intro H _ _ _ V _ _ _ _ W _ _ _ _ M X κ hk hX ψ δ T a hψ hT ha htc
  obtain ⟨-, -, -, -, hP, -, -, hL⟩ := projLaws M
  have hP' := (projLaws M.swap).2.2.2.2.1
  obtain ⟨t1, -, -, -, -⟩ := bandTC M X κ hk hX ψ δ (T - a) T hψ (by linarith)
  obtain ⟨-, t2, t3, -, -⟩ := bandTC M X κ hk hX ψ δ T (T + a) hψ (by linarith)
  have hcomm := ((avSpec M.F).2.2.2 _ (avApprox.2.1 ψ _ _ hψ).2.1).2.2.2.2 M.F (M.F.U (-a))
    (fun t h => by rw [← M.F.add, ← M.F.add, add_comm])
  set Ψ := M.F.av (fun t => (ψ t : ℂ)) with hΨ
  set Y := Ψ ∘L X with hY
  have mI : ∀ x : ℝ, MeasurableSet (Ioi x) := fun _ => measurableSet_Ioi
  have mc : ∀ x y : ℝ, MeasurableSet (Ioc x y) := fun _ _ => measurableSet_Ioc
  have s1 : M.P' (Ioi T) = M.P' (Ioc T (T + a)) + M.P' (Ioi (T + a)) := by
    have := (hP' _ _ (mc T (T + a)) (mI (T + a))).2.2.2.1 (Ioc_disjoint_Ioi le_rfl)
    rwa [Ioc_union_Ioi_eq_Ioi (by linarith)] at this
  have s2 : M.P (Ioi (T - a)) = M.P (Ioc (T - a) T) + M.P (Ioi T) := by
    have := (hP _ _ (mc (T - a) T) (mI T)).2.2.2.1 (Ioc_disjoint_Ioi le_rfl)
    rwa [Ioc_union_Ioi_eq_Ioi (by linarith)] at this
  obtain ⟨-, -, l0, -, -, -, -, l3, l4⟩ := hL T T (by linarith)
  obtain ⟨-, -, m0, -, -, m1, m2, -, -⟩ := hL (T - a) (T + a) (by linarith)
  have e0 : M.P' (Ioc T (T + a)) ∘L M.P' (Ioc T (T + a)) = M.P' (Ioc T (T + a)) := by
    have := (hP' _ _ (mc T (T + a)) (mc T (T + a))).1
    rwa [inter_self] at this
  have e1 : M.P' (Ioi T) ∘L M.P' (Ioc T (T + a)) = M.P' (Ioc T (T + a)) := by
    have := (hP' _ _ (mI T) (mc T (T + a))).1
    rwa [inter_eq_right.2 Ioc_subset_Ioi_self] at this
  have e2 : M.P' (Ioc T (T + a)) ∘L M.P' (Ioi T) = M.P' (Ioc T (T + a)) := by
    have := (hP' _ _ (mc T (T + a)) (mI T)).1
    rwa [inter_eq_left.2 Ioc_subset_Ioi_self] at this
  have e3 : M.P (Ioi (T - a)) ∘L M.P (Ioc (T - a) T) = M.P (Ioc (T - a) T) := by
    have := (hP _ _ (mI (T - a)) (mc (T - a) T)).1
    rwa [inter_eq_right.2 Ioc_subset_Ioi_self] at this
  have e4 : M.P (Ioc (T - a) T) ∘L M.P (Ioi (T - a)) = M.P (Ioc (T - a) T) := by
    have := (hP _ _ (mc (T - a) T) (mI (T - a))).1
    rwa [inter_eq_left.2 Ioc_subset_Ioi_self] at this
  obtain ⟨tc, key⟩ := twoProj (M.abelian₂ T T) (M.P' (Ioc T (T + a))) (M.abelian₂ (T - a) (T + a)) (M.P (Ioc (T - a) T)) Y
    (by simp only [Sc.abelian₂, s1, s2]; abel) l0 e0 m0 (by simpa using (hP _ _ (mc (T - a) T) (mc (T - a) T)).1)
    (by rw [← e1, ← ContinuousLinearMap.comp_assoc, l3, ContinuousLinearMap.zero_comp])
    (by rw [← e2, ContinuousLinearMap.comp_assoc, l4, ContinuousLinearMap.comp_zero])
    (by rw [← e3, ← ContinuousLinearMap.comp_assoc, m1, ContinuousLinearMap.zero_comp])
    (by rw [← e4, ContinuousLinearMap.comp_assoc, m2, ContinuousLinearMap.comp_zero]) htc t2 t3 t1
  rw [key]
  congr 1
  have u1 : ∀ h, M.F.U a (M.abelian₂ T T h) = M.abelian₂ (T - a) (T + a) (M.F.U a h) := fun h => by
    obtain ⟨x1, x2⟩ := (hP _ _ (mI T) (mI T)).2.2.2.2 a
    have y1 : (fun x : ℝ => x + a) ⁻¹' Ioi T = Ioi (T - a) := by ext x; simp [sub_lt_iff_lt_add]
    have y2 : (fun x : ℝ => x - a) ⁻¹' Ioi T = Ioi (T + a) := by ext x; simp [lt_sub_iff_add_lt]
    rw [y1] at x1; rw [y2] at x2
    have z1 := DFunLike.congr_fun x1 h
    have z2 := DFunLike.congr_fun x2 h
    simp only [ContinuousLinearMap.comp_apply] at z1 z2
    simp only [Sc.abelian₂, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, map_sub, z1, z2]
  have inv1 : ∀ h, M.F.U (-a) (M.F.U a h) = h := fun h => by rw [← M.F.add, neg_add_cancel, M.F.zero]
  have inv2 : ∀ h, M.F.U a (M.F.U (-a) h) = h := fun h => by rw [← M.F.add, add_neg_cancel, M.F.zero]
  have u2 : ∀ h, M.F.U (-a) (M.abelian₂ (T - a) (T + a) h) = M.abelian₂ T T (M.F.U (-a) h) := fun h => by
    conv_lhs => rw [← inv2 h, ← u1, inv1]
  have hYU : ∀ h, Y (M.F.U a h) = M.F.U (-a) (Y h) := fun h => by
    show Ψ (X (M.F.U a h)) = M.F.U (-a) (Ψ (X h))
    rw [(carLaws M X κ hk hX).1]
    exact (DFunLike.congr_fun hcomm _).symm
  have := trace_comp_comm (tc.comp_left (M.F.U (-a))) (M.F.U a)
  have f1 : M.F.U a ∘L (M.F.U (-a) ∘L (M.abelian₂ (T - a) (T + a) ∘L Y ∘L M.abelian₂ (T - a) (T + a))) =
      M.abelian₂ (T - a) (T + a) ∘L Y ∘L M.abelian₂ (T - a) (T + a) := by
    ext h; simp only [ContinuousLinearMap.comp_apply, inv2]
  have f2 : (M.F.U (-a) ∘L (M.abelian₂ (T - a) (T + a) ∘L Y ∘L M.abelian₂ (T - a) (T + a))) ∘L M.F.U a =
      M.abelian₂ T T ∘L M.F.U (-(2 * a)) ∘L Y ∘L M.abelian₂ T T := by
    ext h
    show M.F.U (-a) (M.abelian₂ (T - a) (T + a) (Y (M.abelian₂ (T - a) (T + a) (M.F.U a h)))) = M.abelian₂ T T (M.F.U (-(2 * a)) (Y (M.abelian₂ T T h)))
    rw [← u1, hYU, u2, ← M.F.add]
    congr 3; ring
  rwa [f1, f2] at this
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.TraceSm

section

@[expose] public section

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.traceSm :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (M : Sc H V W) (N : W ≃ₗᵢ[ℂ] V), M.IsN (N.toLinearEquiv : W →ₗ[ℂ] V) → ∀ (X : H →L[ℂ] H) (κ : ℝ → V →L[ℂ] W), Ker κ → M.Carries X κ → ∀ (ψ : ℝ → ℝ) (δ T K : ℝ), δ ≤ 1 / 2 → Bump ψ (-δ) 0 → M.T₀ ≤ T →
      IsTraceClass (M.abelian₂ T T ∘L X ∘L M.abelian₂ T T) → (∀ z : ℂ, |z.re| ≤ 1 → ‖symb κ z‖ ≤ K / (1 + |z.im|)) →
      ‖trace (M.abelian₂ T T ∘L (M.F.av (fun t => (ψ t : ℂ)) ∘L X) ∘L M.abelian₂ T T) -
          (1 / 2 : ℂ) * LinearMap.trace ℂ V ((N.toLinearEquiv : W →ₗ[ℂ] V) ∘ₗ (symb κ 0 : V →ₗ[ℂ] W))‖ ≤
        Module.finrank ℂ V * Real.exp (2 * M.T₀) * K * Real.exp (-2 * T) := by
  intro H _ _ _ V _ _ _ _ W _ _ _ _ M N hN X κ hk hX ψ δ T K hδ hψ hT htc hb
  obtain ⟨hk', -, hs'⟩ := convAdj κ hk
  obtain ⟨s0, hi, -⟩ := avApprox.2.1 ψ _ _ hψ
  have cc : Continuous fun t => (ψ t : ℂ) := Complex.continuous_ofReal.comp hψ.cont
  have sc : HasCompactSupport fun t => (ψ t : ℂ) := s0.comp_left Complex.ofReal_zero
  have cn : Continuous fun t => (ψ (-t) : ℂ) := cc.comp continuous_neg
  have z : ∀ t, 1 / 2 < |t| → ψ t = 0 := fun t ht => hψ.supp t fun h => by
    have : |t| ≤ 1 / 2 := abs_le.2 ⟨by linarith [h.1], h.2.trans (by norm_num)⟩
    linarith
  have n1 : ∫ x, ‖(ψ x : ℂ)‖ = 1 := by
    simp only [Complex.norm_real, Real.norm_of_nonneg (hψ.nonneg _)]; exact hψ.total
  have n2 : ∫ x, ‖(ψ (-x) : ℂ)‖ = 1 := (integral_neg_eq_self (fun x => ‖(ψ x : ℂ)‖) _).trans n1
  have n3 : ∫ x, (ψ x : ℂ) = 1 := by rw [integral_complex_ofReal, hψ.total]; simp
  have K0 : 0 ≤ K := by simpa using (norm_nonneg _).trans (hb 0 (by simp))
  have Q0 : 0 ≤ K / √3 := by positivity
  have w1 := planch κ K hk fun y => by simpa using hb (1 + y * Complex.I) (by simp)
  have w2 := planch (sharp κ) K hk' fun y => by
    rw [hs', LinearIsometryEquiv.norm_map]
    simpa using hb (-conj (1 + y * Complex.I)) (by simp)
  obtain ⟨f1, f2⟩ := traceFar M X κ hk hX ψ δ T hψ hT htc
  set e := stdOrthonormalBasis ℂ V
  set f := stdOrthonormalBasis ℂ W
  set c : _ → ℝ → ℂ := fun i => M.cor (fun x => (ψ x : ℂ)) (e i) (kv κ (e i)) with hc
  set d : _ → ℝ → ℂ := fun j => M.swap.cor (fun x => (ψ (-x) : ℂ)) (f j) (kv (sharp κ) (f j)) with hd
  have c0 : ∀ i, Continuous (c i) := fun i => continuous_const.inner (M.F.cont _)
  have d0 : ∀ j, Continuous (d j) := fun j => continuous_const.inner (M.swap.F.cont _)
  have sub : ∀ {ι : Type} [Fintype ι] (g : ι → ℝ → ℂ), (∀ i, Continuous (g i)) → ∀ a b : ℝ,
      ∫ y in a..b, ∑ i, g i (2 * y) = (1 / 2 : ℂ) * ∑ i, ∫ s in (2 * a)..(2 * b), g i s := by
    intro ι _ g hg a b
    rw [intervalIntegral.integral_finsetSum fun i _ =>
      (show Continuous fun y => g i (2 * y) from (hg i).comp (continuous_const.mul continuous_id)).intervalIntegrable _ _, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [intervalIntegral.integral_comp_mul_left _ two_ne_zero]
    simp
  set B : ℝ := 6 / 5 * Real.exp (2 * M.T₀) * (K / √3) * Real.exp (-(2 * T)) with hB
  have tc : ∀ i β, 2 * T ≤ β → ‖∫ s in (2 * T)..β, c i s‖ ≤ B := fun i β hβ => by
    have := tailB M _ (e i) _ _ _ β cc (fun x hx => by rw [z x hx]; simp) n1.le (mul_nonneg Q0 (norm_nonneg _)) (w1 (e i)) hβ
    simpa [e.orthonormal.1 i, hB] using this
  have td : ∀ j β, 2 * T ≤ β → ‖∫ s in (2 * T)..β, d j s‖ ≤ B := fun j β hβ => by
    have := tailB M.swap _ (f j) _ _ _ β cn (fun x hx => by rw [z (-x) (by rwa [abs_neg])]; simp) n2.le
      (mul_nonneg Q0 (norm_nonneg _)) (w2 (f j)) hβ
    simp only [f.orthonormal.1 j, mul_one] at this
    exact this
  have lim : ∀ i, Tendsto (fun a : ℝ => ∫ s in (2 * T - 2 * a)..(2 * T + 2 * a), c i s) atTop (𝓝 ⟪e i, N (symb κ 0 (e i))⟫_ℂ) := fun i => by
    obtain ⟨-, k1, k2⟩ := (kvSpec κ hk).1 (e i)
    have := (corLim M _ hN _ (e i) _ (2 * T) cc sc k1).2
    rw [n3, map_one, one_mul, k2] at this
    exact this.comp (tendsto_id.const_mul_atTop two_pos)
  have tot := f2.add ((tendsto_finsetSum Finset.univ fun i _ => lim i).const_mul (1 / 2 : ℂ))
  rw [zero_add] at tot
  rw [LinearMap.trace_eq_sum_inner _ e]
  refine le_of_tendsto ((tendsto_const_nhds.sub tot).norm) ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with a ha
  have id1 := traceId M X κ hk hX ψ δ T a hψ hT ha f1
  rw [(bandTC M X κ hk hX ψ δ T (T + a) hψ (by linarith)).2.2.2.2, (bandTC M X κ hk hX ψ δ (T - a) T hψ (by linarith)).2.2.2.1,
    sub c c0, sub d d0] at id1
  have sp : ∀ i, ∫ s in (2 * T - 2 * a)..(2 * T + 2 * a), c i s =
      (∫ s in (2 * (T - a))..(2 * T), c i s) + ∫ s in (2 * T)..(2 * T + 2 * a), c i s := fun i => by
    rw [intervalIntegral.integral_add_adjacent_intervals ((c0 i).intervalIntegrable _ _) ((c0 i).intervalIntegrable _ _), mul_sub]
  simp only [sp, Finset.sum_add_distrib]
  rw [eq_sub_of_add_eq id1]
  have hd' : Module.finrank ℂ W = Module.finrank ℂ V := N.toLinearEquiv.finrank_eq
  have b1 : ‖∑ i, ∫ s in (2 * T)..(2 * T + 2 * a), c i s‖ ≤ Module.finrank ℂ V * B := by
    refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ B fun i _ => tc i _ (by linarith)).trans_eq ?_)
    simp
  have b2 : ‖∑ j, ∫ s in (2 * T)..(2 * (T + a)), d j s‖ ≤ Module.finrank ℂ V * B := by
    rw [← hd']
    refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ B fun j _ => td j _ (by linarith)).trans_eq ?_)
    simp
  have alg : ∀ R x y w : ℂ, R + 1 / 2 * x - conj (1 / 2 * w) - (R + 1 / 2 * (x + y)) = -(conj (1 / 2 * w) + 1 / 2 * y) := by
    intros; ring
  rw [alg, norm_neg]
  refine (norm_add_le _ _).trans ?_
  rw [Complex.norm_conj, norm_mul, norm_mul]
  have h2 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
  have h3 : 6 / 5 * (K / √3) ≤ K := by
    have : (6 / 5 : ℝ) ≤ √3 := Real.le_sqrt_of_sq_le (by norm_num)
    rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
    nlinarith
  have h4 : B ≤ Real.exp (2 * M.T₀) * K * Real.exp (-2 * T) := by
    rw [hB, neg_mul, show 6 / 5 * Real.exp (2 * M.T₀) * (K / √3) = Real.exp (2 * M.T₀) * (6 / 5 * (K / √3)) by ring]
    gcongr
  have h5 : (Module.finrank ℂ V : ℝ) * B ≤ Module.finrank ℂ V * (Real.exp (2 * M.T₀) * K * Real.exp (-2 * T)) := by gcongr
  rw [h2]
  linarith
end
end
