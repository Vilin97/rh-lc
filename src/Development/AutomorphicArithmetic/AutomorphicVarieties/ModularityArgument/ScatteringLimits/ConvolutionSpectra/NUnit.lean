module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.Carries
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.AvSpec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.CobLaws
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.CobTail
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.CutLaws
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ProjLaws
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ResCob
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.CutLaws
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Analysis.Fourier.Notation
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.SvSpec
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.NIso
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ProjLaws
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ResBelow
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ResTail

section

@[expose] public section

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.resTail :
    ∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] (k : L V) (T : ℝ), cut V (Iic T) k = k → Tail (cut V (Ioi T) ((shF V).av wR k)) := by
  intro V _ _ _ _ k T hk
  obtain ⟨-, w1, w2, w3⟩ := avSpec (shF V)
  obtain ⟨a1, a2, -⟩ := w3 wR w1
  have cl := fun s t hs ht => cutLaws (V := V) s t hs ht
  refine ⟨Real.exp |T| * ‖k‖, fun ρ hρ => ?_⟩
  have e := DFunLike.congr_fun (cl (Icc (-ρ) ρ)ᶜ (Ioi T) measurableSet_Icc.compl measurableSet_Ioi).1 ((shF V).av wR k)
  rw [ContinuousLinearMap.comp_apply] at e
  rw [e]
  by_cases h : |T| ≤ ρ
  · have e2 : (Icc (-ρ) ρ)ᶜ ∩ Ioi T = Ioi ρ := by
      ext x
      have := abs_le.1 h
      simp only [mem_inter_iff, mem_compl_iff, mem_Icc, mem_Ioi, not_and_or, not_le]
      constructor
      · rintro ⟨h1 | h1, h2⟩ <;> linarith
      · exact fun h1 => ⟨Or.inr h1, by linarith⟩
    rw [e2, (a1 k).2]
    erw [← (cut V (Ioi ρ)).integral_comp_comm (a1 k).1]
    have ib : Integrable fun t => (Iic (T - ρ)).indicator Real.exp t * ‖k‖ :=
      ((integrable_indicator_iff measurableSet_Iic).2 (integrableOn_exp_Iic _)).mul_const _
    refine (norm_integral_le_of_norm_le ib (Eventually.of_forall fun t => ?_)).trans ?_
    · rw [map_smul, norm_smul]
      by_cases ht : t ≤ T - ρ
      · rw [indicator_of_mem (mem_Iic.2 ht)]
        refine mul_le_mul ?_ (((cl _ univ measurableSet_Ioi .univ).2.2.2.2.2.1 _).trans_eq ((shF V).norm t k)) (norm_nonneg _)
          (Real.exp_pos _).le
        refine (norm_indicator_le_norm_self _ _).trans_eq ?_
        simp
      · have h1 := DFunLike.congr_fun ((cl (Ioi (ρ + t)) univ measurableSet_Ioi .univ).2.2.2.2.2.2.1 t) k
        simp only [ContinuousLinearMap.comp_apply, preimage_add_const_Ioi, add_sub_cancel_right] at h1
        have h2 := DFunLike.congr_fun (cl (Ioi (ρ + t)) (Iic T) measurableSet_Ioi measurableSet_Iic).1 k
        rw [ContinuousLinearMap.comp_apply, hk, Ioi_inter_Iic, Ioc_eq_empty (by linarith [not_le.1 ht]),
          (cl univ univ .univ .univ).2.2.2.2.1] at h2
        have h3 : cut V (Ioi ρ) ((shF V).U t k) = 0 := by
          show cut V (Ioi ρ) (sh V t k) = 0
          rw [← h1, h2]; simp
        rw [h3, indicator_of_notMem (by simpa using ht)]; simp
    · rw [integral_mul_const, integral_indicator measurableSet_Iic, integral_exp_Iic, mul_right_comm, ← Real.exp_add]
      gcongr
      linarith [le_abs_self T]
  · refine ((cl _ univ (measurableSet_Icc.compl.inter measurableSet_Ioi) .univ).2.2.2.2.2.1 _).trans ?_
    refine (((shF V).av wR).le_of_opNorm_le (a2.trans_eq w2) k).trans ?_
    rw [mul_right_comm, ← Real.exp_add]
    gcongr
    exact Real.one_le_exp (by linarith [not_le.1 h])
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.NEx

section

@[expose] public section

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.nEx :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (M : Sc H V W), Function.Surjective (1 - M.abelian₂ M.T₀ M.T₀ ∘L M.F.av wR ∘L M.abelian₂ M.T₀ M.T₀ : H →L[ℂ] H) → ∃ N : W →ₗ[ℂ] V, M.IsN N := by
  intro H _ _ _ V _ _ _ _ W _ _ _ _ M hs
  obtain ⟨c0, cadd, csmul, -, csh, -, -, -⟩ := cobLaws M.F
  obtain ⟨-, -, -, -, hP, -, -, hL⟩ := projLaws M
  have hP' := (projLaws M.swap).2.2.2.2.1
  obtain ⟨o1, o2, l0, -, -, l1, l2, l3, l4⟩ := hL M.T₀ M.T₀ (by linarith)
  set T := M.T₀ with hT
  set Λ := M.abelian₂ T T with hΛ
  have mI : ∀ x : ℝ, MeasurableSet (Ioi x) := fun _ => measurableSet_Ioi
  have carry : ∀ p : L V, Tail p → M.F.Cob (M.J p - M.J (one V (∫ x, p x))) := fun p hp => by
    have := (cobLaws (shF V)).2.2.2.2.2.2.2 M.F (M.J.toContinuousLinearEquiv : L V →L[ℂ] H) (fun t h => (M.hJ t h).symm) _
      ((cobTail p).2 hp).2
    rwa [map_sub] at this
  have ex : ∀ w, ∃ n, M.F.Cob (M.J' (one W w) - M.J (one V n)) := by
    intro w
    set h := M.F.U (T - 1) (M.J' (one W w)) with hh
    have s0 : M.P' (Ioc 0 1) (M.J' (one W w)) = M.J' (one W w) := by
      show M.J' (cut W _ (M.J'.symm (M.J' _))) = _
      rw [M.J'.symm_apply_apply, ((cutLaws (Ioc 0 1) univ measurableSet_Ioc .univ).2.2.2.2.2.2.2.1 _).2]
      exact ((svSpec (V := W)).2 w).1.mono fun x hx hn => by rw [hx, indicator_of_notMem hn]
    have s1 : M.P' (Ioc (T - 1) T) h = h := by
      have := DFunLike.congr_fun ((hP _ _ (measurableSet_Ioc (a := (0 : ℝ)) (b := 1)) .univ).2.2.2.2 (T - 1)).2 (M.J' (one W w))
      have y : (fun x : ℝ => x - (T - 1)) ⁻¹' Ioc 0 1 = Ioc (T - 1) T := by
        ext x; simp only [mem_preimage, mem_Ioc]; constructor <;> rintro ⟨a, b⟩ <;> constructor <;> linarith
      rw [y] at this
      simp only [ContinuousLinearMap.comp_apply, s0] at this
      exact this.symm
    have s2 : M.P' (Ioi T) h = 0 := by
      have a : M.P' (Ioi T) ∘L M.P' (Ioc (T - 1) T) = M.P' (Ioi T ∩ Ioc (T - 1) T) := (hP' _ _ (mI T) measurableSet_Ioc).1
      have b : Ioi T ∩ Ioc (T - 1) T = ∅ := eq_empty_of_forall_notMem fun x hx => absurd hx.1 (not_lt.2 hx.2.2)
      rw [b, show M.P' ∅ = 0 from (projLaws M.swap).2.2.2.2.2.1] at a
      rw [← s1]; exact DFunLike.congr_fun a h
    have s3 : M.P (Ioi (T + 1)) h = 0 := by
      have a : M.P' (Ioi (T - 1)) ∘L M.P' (Ioc (T - 1) T) = M.P' (Ioi (T - 1) ∩ Ioc (T - 1) T) := (hP' _ _ (mI _) measurableSet_Ioc).1
      rw [inter_eq_right.2 Ioc_subset_Ioi_self] at a
      rw [← s1, ← a]
      exact DFunLike.congr_fun (hL (T + 1) (T - 1) (by linarith)).1 _
    obtain ⟨k, hk⟩ := hs (Λ h)
    set R := M.F.av wR with hR
    have hk' : k - Λ (R (Λ k)) = Λ h := hk
    have ΛΛ : ∀ x, Λ (Λ x) = Λ x := fun x => DFunLike.congr_fun l0 x
    have kΛ : Λ k = k := by
      have := congrArg Λ hk'
      rw [map_sub, ΛΛ, ΛΛ, ← hk'] at this
      exact sub_left_injective this
    rw [kΛ] at hk'
    have k1 : M.P (Ioi T) k = 0 := by rw [← kΛ]; exact DFunLike.congr_fun l2 k
    have k2 : M.P' (Ioi T) k = 0 := by rw [← kΛ]; exact DFunLike.congr_fun l4 k
    have r2 : M.P' (Ioi T) (R k) = 0 := by
      obtain ⟨i, e⟩ := ((avSpec M.F).2.2.2 _ (avSpec M.F).2.1).1 k
      rw [hR, e, ← (M.P' (Ioi T)).integral_comp_comm i]
      refine integral_eq_zero_of_ae (Eventually.of_forall fun r => ?_)
      by_cases hr : r ≤ 0
      · have a := DFunLike.congr_fun ((hP _ _ (mI (T - r)) .univ).2.2.2.2 r).2 k
        have y : (fun x : ℝ => x - r) ⁻¹' Ioi (T - r) = Ioi T := by ext x; simp
        have b : M.P' (Ioi (T - r)) ∘L M.P' (Ioi T) = M.P' (Ioi (T - r) ∩ Ioi T) := (hP' _ _ (mI _) (mI _)).1
        rw [inter_eq_left.2 (Ioi_subset_Ioi (by linarith))] at b
        rw [y, ← b] at a
        simp only [ContinuousLinearMap.comp_apply, k2, map_zero] at a
        simp [← a]
      · simp [wR, hr]
    have dec : h = (k - R k) + M.P (Ioi T) (R k) + M.P (Ioi T) h := by
      have a : Λ h = h - M.P (Ioi T) h - M.P' (Ioi T) h := rfl
      have b : Λ (R k) = R k - M.P (Ioi T) (R k) - M.P' (Ioi T) (R k) := rfl
      rw [a, b, s2, r2, sub_zero, sub_zero] at hk'
      linear_combination (norm := module) -hk'
    have cl := fun s t hs ht => cutLaws (V := V) s t hs ht
    set u := M.J.symm k with hu
    have u1 : cut V (Iic T) u = u := by
      have a := (cl (Iic T) (Ioi T) measurableSet_Iic (mI T)).2.2.1 (Iic_disjoint_Ioi le_rfl)
      rw [Iic_union_Ioi, (cl _ _ .univ .univ).2.2.2.1] at a
      have b : u = cut V (Iic T) u + cut V (Ioi T) u := DFunLike.congr_fun a u
      have c : cut V (Ioi T) u = 0 := M.J.injective (by rw [map_zero]; exact k1)
      rw [c, add_zero] at b
      exact b.symm
    have e1 : M.P (Ioi T) (R k) = M.J (cut V (Ioi T) ((shF V).av wR u)) := by
      have := DFunLike.congr_fun (((avSpec (shF V)).2.2.2 _ (avSpec M.F).2.1).2.2.2.2 M.F
        (M.J.toContinuousLinearEquiv : L V →L[ℂ] H) fun t h => (M.hJ t h).symm) u
      have a : M.J ((shF V).av wR u) = R (M.J u) := this
      rw [hu, M.J.apply_symm_apply] at a
      show M.J (cut V _ (M.J.symm (R k))) = _
      rw [← a, M.J.symm_apply_apply]
    set v := cut V (Ioi T) (M.J.symm h) with hv
    have e2 : M.P (Ioi T) h = M.J v := rfl
    have bv : Bdd v := by
      refine ⟨|T| + 1, ?_⟩
      have a := (cl (Ioc T (T + 1)) (Ioi (T + 1)) measurableSet_Ioc (mI _)).2.2.1 (Ioc_disjoint_Ioi le_rfl)
      rw [Ioc_union_Ioi_eq_Ioi (by linarith)] at a
      have c : cut V (Ioi (T + 1)) (M.J.symm h) = 0 := M.J.injective (by rw [map_zero]; exact s3)
      have b : v = cut V (Ioc T (T + 1)) (M.J.symm h) := by rw [hv, a, ContinuousLinearMap.add_apply, c, add_zero]
      have d := (cl (Icc (-(|T| + 1)) (|T| + 1)) (Ioc T (T + 1)) measurableSet_Icc measurableSet_Ioc).1
      have sub : Ioc T (T + 1) ⊆ Icc (-(|T| + 1)) (|T| + 1) := fun x hx =>
        ⟨by linarith [hx.1, neg_abs_le T], by linarith [hx.2, le_abs_self T]⟩
      rw [inter_eq_right.2 sub] at d
      rw [b]
      exact DFunLike.congr_fun d _
    have f1 := carry _ (resTail u T u1)
    have f2 := carry _ ((cobTail v).1 bv)
    have f3 := (cadd _ _ (cadd _ _ (cadd _ _ (csh (T - 1) (M.J' (one W w))) (resCob M.F k).1).1 f1).1 f2).1
    refine ⟨(∫ x, cut V (Ioi T) ((shF V).av wR u) x) + ∫ x, v x, ?_⟩
    convert f3 using 1
    rw [← e1, ← e2, map_add (f := _), map_add (f := _), ← hh, ← hR]
    linear_combination (norm := module) dec
  choose n hn using ex
  let b := Module.finBasis ℂ W
  refine ⟨b.constr ℂ fun i => n (b i), fun w => ?_⟩
  have e : M.J' (one W w) - M.J (one V (b.constr ℂ (fun i => n (b i)) w)) =
      ∑ i, b.repr w i • (M.J' (one W (b i)) - M.J (one V (n (b i)))) := by
    conv_lhs => rw [← b.sum_repr w]

    simp only [map_sum, map_smul, Module.Basis.constr_basis, smul_sub, Finset.sum_sub_distrib]
  rw [e]
  exact Finset.sum_induction _ _ (fun x y hx hy => (cadd x y hx hy).1) c0 fun i _ => csmul _ _ (hn _)
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ResInv

section

@[expose] public section

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.resInv :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (M : Sc H V W) (B : H →L[ℂ] H) (β : ℝ → V →L[ℂ] V) (β' : ℝ → W →L[ℂ] W), Ker β → Ker β' → IsUnit (symb β 0) → IsUnit (symb β' 0) → M.Acts B β β' → IsCompactOperator (M.abelian₂ M.T₀ M.T₀ ∘L B ∘L M.abelian₂ M.T₀ M.T₀) →
      Function.Surjective (1 - M.abelian₂ M.T₀ M.T₀ ∘L M.F.av wR ∘L M.abelian₂ M.T₀ M.T₀ : H →L[ℂ] H) := by
  intro H _ _ _ V _ _ _ _ W _ _ _ _ M B β β' k1 k2 u1 u2 ha hc
  obtain ⟨-, -, l0, sa, ln, -⟩ := (projLaws M).2.2.2.2.2.2.2 M.T₀ M.T₀ (by linarith)
  set Λ := M.abelian₂ M.T₀ M.T₀ with hΛ
  set R := M.F.av wR with hR
  have hΛΛ : ∀ x, Λ (Λ x) = Λ x := fun x => DFunLike.congr_fun l0 x
  have below : ∀ S : H →L[ℂ] H, (∀ x, (⟪x, S x⟫_ℂ).re = (⟪x, R x⟫_ℂ).re) →
      ∃ c : ℝ, 0 < c ∧ ∀ x, c * ‖x‖ ≤ ‖x - Λ (S (Λ x))‖ := by
    intro S hS
    by_contra hcon
    push Not at hcon
    choose x hx using fun n : ℕ => hcon (1 / ((n : ℝ) + 1)) Nat.one_div_pos_of_nat
    have h0 : ∀ n, x n ≠ 0 := fun n h => by simpa [h] using hx n
    let f : ℕ → H := fun n => (‖x n‖⁻¹ : ℂ) • x n
    have hf : ∀ n, ‖f n‖ = 1 := fun n => norm_smul_inv_norm (h0 n)
    have t0 : Tendsto (fun n => f n - Λ (S (Λ (f n)))) atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun n => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
      have e : f n - Λ (S (Λ (f n))) = (‖x n‖⁻¹ : ℂ) • (x n - Λ (S (Λ (x n)))) := by simp [f, smul_sub]
      rw [e, norm_smul, norm_inv, Complex.norm_real, norm_norm, inv_mul_le_iff₀ (norm_pos_iff.2 (h0 n)), mul_comm]
      exact (hx n).le
    have t1 : Tendsto (fun n => Λ (f n) - f n) atTop (𝓝 0) := by
      have := ((Λ.continuous.tendsto 0).comp t0).sub t0
      simpa [Function.comp_def, hΛΛ] using this
    have t2 : Tendsto (fun n => f n - Λ (S (f n))) atTop (𝓝 0) := by
      have := t0.add (((Λ ∘L S).continuous.tendsto 0).comp t1)
      simpa [Function.comp_def] using this
    have t3 : Tendsto (fun n => ⟪f n, f n - Λ (S (f n))⟫_ℂ + ⟪Λ (f n) - f n, S (f n)⟫_ℂ) atTop (𝓝 0) := by
      have a : Tendsto (fun n => ⟪f n, f n - Λ (S (f n))⟫_ℂ) atTop (𝓝 0) :=
        squeeze_zero_norm (fun n => (norm_inner_le_norm _ _).trans_eq (by rw [hf, one_mul])) (tendsto_zero_iff_norm_tendsto_zero.1 t2)
      have b : Tendsto (fun n => ⟪Λ (f n) - f n, S (f n)⟫_ℂ) atTop (𝓝 0) := by
        refine squeeze_zero_norm (a := fun n => ‖Λ (f n) - f n‖ * ‖S‖) (fun n => (norm_inner_le_norm _ _).trans ?_) ?_
        · gcongr; simpa [hf] using S.le_opNorm (f n)
        · simpa using (tendsto_zero_iff_norm_tendsto_zero.1 t1).mul_const ‖S‖
      simpa using a.add b
    refine resBelow M B β β' k1 k2 u1 u2 ha hc f hf t1 ?_
    have t4 := (tendsto_const_nhds (x := (1 : ℝ))).sub ((Complex.continuous_re.tendsto 0).comp t3)
    simp only [Complex.zero_re, sub_zero] at t4
    refine t4.congr fun n => ?_
    have e1 : ⟪f n, f n⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hf]; simp
    rw [← hS, Function.comp_apply, inner_sub_right, inner_sub_left, sa.isSymmetric.apply_clm, e1]
    simp
  obtain ⟨c, c0, h1⟩ := below R fun _ => rfl
  obtain ⟨c', c0', h2⟩ := below (ContinuousLinearMap.adjoint R) fun x => by
    rw [ContinuousLinearMap.adjoint_inner_right, ← inner_conj_symm, Complex.conj_re]
  set A : H →L[ℂ] H := 1 - Λ ∘L R ∘L Λ with hA
  have anti : AntilipschitzWith ⟨c⁻¹, by positivity⟩ A := A.antilipschitz_of_bound fun x => by
    show ‖x‖ ≤ c⁻¹ * ‖x - Λ (R (Λ x))‖
    rw [le_inv_mul_iff₀ c0]; exact h1 x
  have cl : IsClosed (LinearMap.range (A : H →ₗ[ℂ] H) : Set H) := anti.isClosed_range A.uniformContinuous
  have bot : (LinearMap.range (A : H →ₗ[ℂ] H))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro y hy
    have h3 : y - Λ (ContinuousLinearMap.adjoint R (Λ y)) = 0 := ext_inner_left ℂ fun x => by
      have := hy (A x) ⟨x, rfl⟩
      rw [inner_sub_right, ← sa.isSymmetric.apply_clm, ContinuousLinearMap.adjoint_inner_right, ← sa.isSymmetric.apply_clm,
        ← inner_sub_left, inner_zero_right]
      exact this
    have := h2 y
    rw [h3, norm_zero] at this
    exact norm_le_zero_iff.1 (nonpos_of_mul_nonpos_right this c0')
  haveI := cl.completeSpace_coe
  exact LinearMap.range_eq_top.1 ((Submodule.orthogonal_eq_bot_iff).1 bot)
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.NUnit

section

@[expose] public section

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.nUnit :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (M : Sc H V W) (B : H →L[ℂ] H) (β : ℝ → V →L[ℂ] V) (β' : ℝ → W →L[ℂ] W), Ker β → Ker β' → IsUnit (symb β 0) → IsUnit (symb β' 0) → M.Acts B β β' → IsCompactOperator (M.abelian₂ M.T₀ M.T₀ ∘L B ∘L M.abelian₂ M.T₀ M.T₀) →
      ∃ N : W ≃ₗᵢ[ℂ] V, M.IsN (N.toLinearEquiv : W →ₗ[ℂ] V) := by
  intro H _ _ _ V _ _ _ _ W _ _ _ _ M B β β' k1 k2 u1 u2 ha hc
  obtain ⟨N, hN⟩ := nEx M (resInv M B β β' k1 k2 u1 u2 ha hc)
  have hl : M.swap.abelian₂ M.swap.T₀ M.swap.T₀ = M.abelian₂ M.T₀ M.T₀ := (projLaws M).2.2.2.1 _ _
  obtain ⟨N', hN'⟩ := nEx M.swap (resInv M.swap B β' β k2 k1 u2 u1 ⟨ha.2, ha.1⟩ (hl ▸ hc))
  have i1 := (nIso M).2 N hN
  have i2 := (nIso M.swap).2 N' hN'
  let A : W →ₗᵢ[ℂ] V := ⟨N, i1⟩
  let A' : V →ₗᵢ[ℂ] W := ⟨N', i2⟩
  have hd : Module.finrank ℂ W = Module.finrank ℂ V :=
    le_antisymm (LinearMap.finrank_le_finrank_of_injective A.injective) (LinearMap.finrank_le_finrank_of_injective A'.injective)
  exact ⟨A.toLinearIsometryEquiv hd, hN⟩
end
end
