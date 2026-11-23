module

public import Development.AbelianVarietyTheory.Definitions.Divisors.TCoefMInMMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugationDerivCutoffPolynomialMemUnitarySpan
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
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic.Linter.Style
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledKoszulTestFamilyHasDerivAtScale
import Mathlib.Algebra.Order.Star.Real
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugationDerivCutoffPolynomialMemUnitarySpanStatement

section

@[expose] public section

open MvPolynomial GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc1.A

theorem _root_.GlobalTheory.T.conjugationDerivCutoffPolynomial_mem_unitarySpan : ∀ {n : ℕ} (ε : Fin n → Bool) (Z : GlobalTheory.PsCo.Pc1.Mat n) (H : ℝ → ℝ) (P : GlobalTheory.PsCo.Pc1.Poly n), GlobalTheory.PsCo.Pc1.IsCutFn H → GlobalTheory.PsCo.Pc1.adBas ε Z H P ∈ GlobalTheory.PsCo.Pc1.AdSpanM ε := by
  first | exact @GlobalTheory.PsCo.Pc1.adBas_mem_adSpanM | exact GlobalTheory.PsCo.Pc1.adBas_mem_adSpanM | (intros; apply GlobalTheory.PsCo.Pc1.adBas_mem_adSpanM <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmoothEventuallyZeroCutoffIntervalIntegralDeri

section

@[expose] public section

noncomputable section
open scoped ContDiff
open Set MeasureTheory

namespace GlobalTheory.ParamIntCut

theorem hasDerivAt_snd {F : ℝ → ℝ → ℝ} (hF : ContDiff ℝ 1 (Function.uncurry F)) (s y : ℝ) :
    HasDerivAt (F s) (fderiv ℝ (Function.uncurry F) (s, y) (0, 1)) y := by
  have h1 : HasFDerivAt (Function.uncurry F) (fderiv ℝ (Function.uncurry F) (s, y)) (s, y) :=
    (hF.differentiable one_ne_zero (s, y)).hasFDerivAt
  have h2 : HasDerivAt (fun t : ℝ => ((s, t) : ℝ × ℝ)) ((0, 1) : ℝ × ℝ) y :=
    (hasDerivAt_const y s).prodMk (hasDerivAt_id y)
  exact h1.comp_hasDerivAt y h2

theorem hasDerivAt_intervalIntegral {F : ℝ → ℝ → ℝ} (a b : ℝ)
    (hF : ContDiff ℝ 1 (Function.uncurry F)) (y₀ : ℝ) :
    HasDerivAt (fun y => ∫ s in a..b, F s y)
      (∫ s in a..b, fderiv ℝ (Function.uncurry F) (s, y₀) (0, 1)) y₀ := by
  set P : ℝ → ℝ → ℝ := fun s y => fderiv ℝ (Function.uncurry F) (s, y) (0, 1) with hP
  have hPc : Continuous (Function.uncurry P) :=
    (hF.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hFc : Continuous (Function.uncurry F) := hF.continuous
  have hsec : ∀ (G : ℝ → ℝ → ℝ), Continuous (Function.uncurry G) → ∀ y, Continuous (fun s => G s y) :=
    fun G hG y => hG.comp (continuous_id.prodMk continuous_const)
  obtain ⟨C, hC⟩ : ∃ C, ∀ p ∈ (uIcc a b) ×ˢ (Metric.closedBall y₀ 1), ‖Function.uncurry P p‖ ≤ C :=
    (isCompact_uIcc.prod (isCompact_closedBall y₀ 1)).exists_bound_of_continuousOn hPc.continuousOn
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℝ) (μ := volume)
    (a := a) (b := b) (F := fun y s => F s y) (F' := fun y s => P s y) (x₀ := y₀)
    (bound := fun _ => C) (s := Metric.ball y₀ 1) (Metric.ball_mem_nhds y₀ one_pos)
    (Filter.Eventually.of_forall fun y => (hsec F hFc y).aestronglyMeasurable)
    ((hsec F hFc y₀).intervalIntegrable _ _)
    ((hsec P hPc y₀).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun t ht y hy =>
      hC (t, y) ⟨uIoc_subset_uIcc ht, Metric.ball_subset_closedBall hy⟩)
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun t _ y _ => hasDerivAt_snd hF t y)
  exact key.2

theorem contDiff_nat_intervalIntegral (a b : ℝ) :
    ∀ (n : ℕ) (F : ℝ → ℝ → ℝ), ContDiff ℝ ∞ (Function.uncurry F) →
      ContDiff ℝ n (fun y => ∫ s in a..b, F s y)
  | 0, F, hF => by
    have h1 : ContDiff ℝ 1 (Function.uncurry F) := hF.of_le (by exact_mod_cast le_top)
    rw [Nat.cast_zero, contDiff_zero]
    exact continuous_iff_continuousAt.2 fun y => (hasDerivAt_intervalIntegral a b h1 y).continuousAt
  | n + 1, F, hF => by
    have h1 : ContDiff ℝ 1 (Function.uncurry F) := hF.of_le (by exact_mod_cast le_top)
    set P : ℝ → ℝ → ℝ := fun s y => fderiv ℝ (Function.uncurry F) (s, y) (0, 1) with hP
    have hPs : ContDiff ℝ ∞ (Function.uncurry P) :=
      (hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
    have hc : ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 := by norm_cast
    rw [hc, contDiff_succ_iff_deriv]
    refine ⟨fun y => (hasDerivAt_intervalIntegral a b h1 y).differentiableAt, by simp, ?_⟩
    have hd : deriv (fun y => ∫ s in a..b, F s y) = fun y => ∫ s in a..b, P s y :=
      funext fun y => (hasDerivAt_intervalIntegral a b h1 y).deriv
    rw [hd]
    exact contDiff_nat_intervalIntegral a b n P hPs

end GlobalTheory.ParamIntCut

namespace GlobalTheory.PsCo.Pc1

theorem isCutFn_intervalIntegral_and_deriv :
    ∀ (F : ℝ → ℝ → ℝ) (a b : ℝ), ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry F) →
      (∃ R : ℝ, ∀ s ∈ Set.uIcc a b, ∀ y, R ≤ y → F s y = 0) →
      GlobalTheory.PsCo.Pc1.IsCutFn (fun y => ∫ s in a..b, F s y) ∧
        ∀ y, deriv (fun y => ∫ s in a..b, F s y) y = ∫ s in a..b, deriv (F s) y := by
  intro F a b hF ⟨R, hR⟩
  have h1 : ContDiff ℝ 1 (Function.uncurry F) := hF.of_le (by exact_mod_cast le_top)
  refine ⟨⟨contDiff_infty.2 fun n => GlobalTheory.ParamIntCut.contDiff_nat_intervalIntegral a b n F hF, R, fun y hy => ?_⟩,
    fun y => ?_⟩
  · show ∫ s in a..b, F s y = 0
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (fun s hs => hR s hs y hy)]
    simp
  · rw [(GlobalTheory.ParamIntCut.hasDerivAt_intervalIntegral a b h1 y).deriv]
    refine intervalIntegral.integral_congr fun s _ => ?_
    exact ((GlobalTheory.ParamIntCut.hasDerivAt_snd h1 s y).deriv).symm

end GlobalTheory.PsCo.Pc1
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmoothEventuallyZeroCutoffIntervalIntegralDeriStatement

section

@[expose] public section

open MvPolynomial GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc1.A

theorem _root_.GlobalTheory.T.isSmoothEventuallyZeroCutoff_intervalIntegral_deriv : ∀ (F : ℝ → ℝ → ℝ) (a b : ℝ), ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry F) → (∃ R : ℝ, ∀ s ∈ Set.uIcc a b, ∀ y, R ≤ y → F s y = 0) → GlobalTheory.PsCo.Pc1.IsCutFn (fun y => ∫ s in a..b, F s y) ∧ ∀ y, deriv (fun y => ∫ s in a..b, F s y) y = ∫ s in a..b, deriv (F s) y := by
  first | exact @GlobalTheory.PsCo.Pc1.isCutFn_intervalIntegral_and_deriv | exact GlobalTheory.PsCo.Pc1.isCutFn_intervalIntegral_and_deriv | (intros; apply GlobalTheory.PsCo.Pc1.isCutFn_intervalIntegral_and_deriv <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledKoszulTestFamilyHasDerivAtScaleStatement

section

@[expose] public section

open MvPolynomial GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc1.A

theorem _root_.GlobalTheory.T.scaledKoszulTestFamily_hasDerivAt_scale : ∀ {n : ℕ} (ε : Fin n → Bool) (G : ℝ → ℝ) (p : ℕ → GlobalTheory.PsCo.Pc1.Poly n) (q : GlobalTheory.PsCo.Pc1.Mode ε → ℕ → GlobalTheory.PsCo.Pc1.Poly n), ContDiff ℝ (⊤ : ℕ∞) G → GlobalTheory.PsCo.Pc1.IsKoszul ε p q → ∀ t : ℝ, 0 < t → ∀ g : GlobalTheory.PsCo.Pc1.Mat n, HasDerivAt (fun s : ℝ => GlobalTheory.PsCo.Pc1.famF ε G p s g) (((t⁻¹ : ℝ) : ℂ) * ∑ x : GlobalTheory.PsCo.Pc1.Mode ε, ∑ j ∈ Finset.range (GlobalTheory.PsCo.Pc1.nMode ε + 1), GlobalTheory.PsCo.Pc1.adBas ε (Matrix.single x.1.2 x.1.1 1) (iteratedDeriv (j + 1) (fun y => G (t * y))) (q x j) g) t := by
  first | exact @GlobalTheory.PsCo.HomotDeriv.famF_hasDerivAt | exact GlobalTheory.PsCo.HomotDeriv.famF_hasDerivAt | (intros; apply GlobalTheory.PsCo.HomotDeriv.famF_hasDerivAt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffIter

section

@[expose] public section

open MvPolynomial GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc1.A
open scoped ContDiff

namespace GlobalTheory.PsCo.Pc1.Homot

noncomputable def scF (G : ℝ → ℝ) (j : ℕ) (s y : ℝ) : ℝ := s ^ j * iteratedDeriv (j + 1) G (s * y)

lemma contDiff_iter {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G) (k : ℕ) : ContDiff ℝ ∞ (iteratedDeriv k G) := by
  rw [iteratedDeriv_eq_iterate]
  exact hG.iterate_deriv k

lemma scF_contDiff {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G) (j : ℕ) : ContDiff ℝ ∞ (Function.uncurry (scF G j)) := by
  have h := contDiff_iter hG (j + 1)
  exact (contDiff_fst.pow j).mul (h.comp (contDiff_fst.mul contDiff_snd))

lemma deriv_scF {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G) (j : ℕ) (s y : ℝ) : deriv (scF G j s) y = scF G (j + 1) s y := by
  have h := (contDiff_iter hG (j + 1)).differentiable (by simp)
  have h1 : HasDerivAt (fun y => s * y) s y := by simpa using (hasDerivAt_id y).const_mul s
  have h2 := ((h (s * y)).hasDerivAt.comp y h1).const_mul (s ^ j)
  have h3 : deriv (scF G j s) y = _ := h2.deriv
  rw [h3, scF, iteratedDeriv_succ (n := j + 1)]
  ring

lemma iter_scale {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G) (j : ℕ) (s y : ℝ) :
    iteratedDeriv (j + 1) (fun y => G (s * y)) y = s * scF G j s y := by
  rw [iteratedDeriv_comp_const_mul (hG.of_le (by exact_mod_cast le_top)) s, scF]
  ring

lemma iter_zero {G : ℝ → ℝ} (h0 : ∀ x, 1 ≤ x → G x = 0) (k : ℕ) {x : ℝ} (hx : 1 < x) : iteratedDeriv k G x = 0 := by
  have : G =ᶠ[nhds x] fun _ => (0 : ℝ) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy using h0 y (le_of_lt hy)
  rw [this.iteratedDeriv_eq k]
  simp

lemma scF_cont {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G) (j : ℕ) (y : ℝ) : Continuous fun s => scF G j s y :=
  (scF_contDiff hG j).continuous.comp (continuous_id.prodMk continuous_const)

theorem stHomot : GlobalTheory.PsCo.Pc1.StHomot := by
  intro n ε G p q hP hK t ht
  obtain ⟨hG, h0, -, -⟩ := hP
  have hI : ∀ j, IsCutFn (fun y => ∫ s in (1:ℝ)..t, scF G j s y) ∧
      ∀ y, deriv (fun y => ∫ s in (1:ℝ)..t, scF G j s y) y = ∫ s in (1:ℝ)..t, deriv (scF G j s) y := by
    intro j
    refine GlobalTheory.T.isSmoothEventuallyZeroCutoff_intervalIntegral_deriv (scF G j) 1 t (scF_contDiff hG j) ⟨2, ?_⟩
    intro s hs y hy
    rw [Set.uIcc_of_le ht] at hs
    have : 1 < s * y := by nlinarith [hs.1]
    simp [scF, iter_zero h0 _ this]
  have key : famF ε G p 1 - famF ε G p t = -∑ x : Mode ε, ∑ j ∈ Finset.range (nMode ε + 1),
      adBas ε (Matrix.single x.1.2 x.1.1 1) (fun y => ∫ s in (1:ℝ)..t, scF G j s y) (q x j) := by
    funext g
    set D : ℝ → ℂ := fun s => ∑ x : Mode ε, ∑ j ∈ Finset.range (nMode ε + 1),
      ((scF G (j + 1) s (rM ε g) : ℂ) * ev g (dZ ε (Matrix.single x.1.2 x.1.1 1) (rP ε) * q x j) +
        (scF G j s (rM ε g) : ℂ) * ev g (dZ ε (Matrix.single x.1.2 x.1.1 1) (q x j))) with hD
    have hc : ∀ j, Continuous fun s => (scF G j s (rM ε g) : ℂ) := fun j =>
      Complex.continuous_ofReal.comp (scF_cont hG j _)
    have hder : ∀ s ∈ Set.uIcc (1:ℝ) t, HasDerivAt (fun s : ℝ => famF ε G p s g) (D s) s := by
      intro s hs
      rw [Set.uIcc_of_le ht] at hs
      have hs0 : 0 < s := by linarith [hs.1]
      have h := GlobalTheory.T.scaledKoszulTestFamily_hasDerivAt_scale ε G p q hG hK s hs0 g
      convert h using 1
      rw [hD, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hsc : (s : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
      simp only [adBas, bas]
      rw [← iteratedDeriv_succ, iter_scale hG, iter_scale hG]
      push_cast
      field_simp
    have hDc : Continuous D := by
      rw [hD]
      refine continuous_finsetSum _ fun x _ => continuous_finsetSum _ fun j _ => ?_
      exact ((hc _).mul continuous_const).add ((hc _).mul continuous_const)
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hder (hDc.intervalIntegrable _ _)
    have hint : ∫ s in (1:ℝ)..t, D s = ∑ x : Mode ε, ∑ j ∈ Finset.range (nMode ε + 1),
        adBas ε (Matrix.single x.1.2 x.1.1 1) (fun y => ∫ s in (1:ℝ)..t, scF G j s y) (q x j) g := by
      rw [hD, intervalIntegral.integral_finsetSum]
      · refine Finset.sum_congr rfl fun x _ => ?_
        rw [intervalIntegral.integral_finsetSum]
        · refine Finset.sum_congr rfl fun j _ => ?_
          rw [intervalIntegral.integral_add (((hc _).mul_const _).intervalIntegrable _ _)
            (((hc _).mul_const _).intervalIntegrable _ _),
            intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const,
            intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal]
          simp only [adBas, bas, (hI j).2, deriv_scF hG]
        · intro j _
          exact (((hc _).mul continuous_const).add ((hc _).mul continuous_const)).intervalIntegrable _ _
      · intro x _
        refine (continuous_finsetSum _ fun j _ => ?_).intervalIntegrable _ _
        exact ((hc _).mul continuous_const).add ((hc _).mul continuous_const)
    simp only [Pi.sub_apply, Pi.neg_apply, Finset.sum_apply]
    rw [← hint, hftc]
    ring
  rw [key]
  exact neg_mem (Submodule.sum_mem _ fun x _ => Submodule.sum_mem _ fun j _ => GlobalTheory.T.conjugationDerivCutoffPolynomial_mem_unitarySpan ε _ _ _ (hI j).1)

end GlobalTheory.PsCo.Pc1.Homot
end
end
