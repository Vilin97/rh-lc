module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.Order.CompletePartialOrder
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalCharacterIntegrals.ShellP
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhitGenLowOf
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalCharacterIntegrals.ContinuousLatticeNorm
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalCharacterIntegrals.MeasurePreservingOfAddEquiv

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalCharacterIntegrals.DifferentiableSetIntegralFz

section

@[expose] public section

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.SwLocFin

open MeasureTheory Filter Topology Set

variable {H : Type*} [MeasurableSpace H]

def fz (r : H → ℝ) (u : H → ℂ) (s₀ z : ℂ) (b : H) : ℂ := (r b : ℂ) ^ (-(z - s₀)) * u b

theorem norm_cpow_le {x : ℝ} (hx : 1 ≤ x) {R : ℝ} (hR : x ≤ R) (w : ℂ) :
    ‖(x : ℂ) ^ w‖ ≤ R ^ max w.re 0 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
  calc x ^ w.re ≤ x ^ max w.re 0 := Real.rpow_le_rpow_of_exponent_le hx (le_max_left _ _)
    _ ≤ R ^ max w.re 0 := Real.rpow_le_rpow (by linarith) hR (le_max_right _ _)

theorem integrableOn_fz {ν : Measure H} {r : H → ℝ} {u : H → ℂ} {s₀ : ℂ} (hr1 : ∀ b, 1 ≤ r b) (hrm : Measurable r)
    (hum : AEStronglyMeasurable u ν) {C : ℝ} (hub : ∀ b, ‖u b‖ ≤ C) {S : Set H} (hS : MeasurableSet S)
    (hSf : ν S < ⊤) {Rm : ℝ} (hRm : ∀ b ∈ S, r b ≤ Rm) (z : ℂ) : IntegrableOn (fz r u s₀ z) S ν := by
  have hmeas : Measurable fun b => (r b : ℂ) ^ (-(z - s₀)) :=
    (Complex.measurable_ofReal.comp hrm).pow_const _
  refine Measure.integrableOn_of_bounded (M := Rm ^ max (-(z - s₀)).re 0 * C) hSf.ne
    (hmeas.aestronglyMeasurable.mul hum) ?_
  filter_upwards [ae_restrict_mem hS] with b hb
  show ‖(r b : ℂ) ^ (-(z - s₀)) * u b‖ ≤ Rm ^ max (-(z - s₀)).re 0 * C
  rw [norm_mul]
  exact mul_le_mul (PositivityTheory.SiegelWeilFormula.SwLocFin.norm_cpow_le (hr1 b) (hRm b hb) _) (hub b)
    (norm_nonneg _) (Real.rpow_nonneg (by linarith [hr1 b, hRm b hb]) _)

theorem differentiable_setIntegral_fz {ν : Measure H} {r : H → ℝ} {u : H → ℂ} {s₀ : ℂ} (hr1 : ∀ b, 1 ≤ r b)
    (hrm : Measurable r) (hum : AEStronglyMeasurable u ν) {C : ℝ} (hub : ∀ b, ‖u b‖ ≤ C) {S : Set H}
    (hS : MeasurableSet S) (hSf : ν S < ⊤) {Rm : ℝ} (hRm : ∀ b ∈ S, r b ≤ Rm) :
    Differentiable ℂ (fun z => ∫ b in S, fz r u s₀ z b ∂ν) := by
  intro z₀
  haveI : IsFiniteMeasure (ν.restrict S) := isFiniteMeasure_restrict.mpr hSf.ne
  have hofr : Measurable fun b => (r b : ℂ) := Complex.measurable_ofReal.comp hrm
  have hmeas : ∀ z : ℂ, Measurable fun b => (r b : ℂ) ^ (-(z - s₀)) := fun z => hofr.pow_const _
  set R' := max Rm 1 with hR'
  have hR'1 : 1 ≤ R' := le_max_right _ _
  have hR'0 : 0 ≤ R' := by linarith
  set E := max (s₀.re - z₀.re + 1) 0 with hE
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν.restrict S)
    (F := fun z b => PositivityTheory.SiegelWeilFormula.SwLocFin.fz r u s₀ z b)
    (F' := fun z b => -(Complex.log (r b) * (r b : ℂ) ^ (-(z - s₀)) * u b))
    (bound := fun _ => R' * R' ^ E * C) (x₀ := z₀)
    (Metric.ball_mem_nhds z₀ one_pos)
    (Eventually.of_forall fun z => ((hmeas z).aestronglyMeasurable.mul hum).restrict)
    (PositivityTheory.SiegelWeilFormula.SwLocFin.integrableOn_fz hr1 hrm hum hub hS hSf hRm z₀)
    ((((Complex.measurable_log.comp hofr).mul (hmeas z₀)).aestronglyMeasurable.mul hum).neg.restrict)
    ?_ (integrable_const _) ?_
  · exact key.2.differentiableAt
  · filter_upwards [ae_restrict_mem hS] with b hb z hz
    show ‖-(Complex.log (r b) * (r b : ℂ) ^ (-(z - s₀)) * u b)‖ ≤ R' * R' ^ E * C
    have hb1 := hr1 b
    have hbR : r b ≤ R' := (hRm b hb).trans (le_max_left _ _)
    have hlog : ‖Complex.log (r b)‖ ≤ R' := by
      rw [← Complex.ofReal_log (by linarith), Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.log_nonneg hb1)]
      linarith [Real.log_le_sub_one_of_pos (show 0 < r b by linarith)]
    have hre : (-(z - s₀)).re ≤ s₀.re - z₀.re + 1 := by
      have h1 : dist z z₀ < 1 := Metric.mem_ball.mp hz
      rw [Complex.dist_eq] at h1
      have h2 := Complex.abs_re_le_norm (z - z₀)
      rw [Complex.sub_re, abs_le] at h2
      rw [Complex.neg_re, Complex.sub_re]
      linarith [h2.1]
    have hcp : ‖(r b : ℂ) ^ (-(z - s₀))‖ ≤ R' ^ E :=
      (PositivityTheory.SiegelWeilFormula.SwLocFin.norm_cpow_le hb1 hbR _).trans
        (Real.rpow_le_rpow_of_exponent_le hR'1 (max_le_max hre le_rfl))
    rw [norm_neg, norm_mul, norm_mul]
    exact mul_le_mul (mul_le_mul hlog hcp (norm_nonneg _) hR'0) (hub b) (norm_nonneg _)
      (mul_nonneg hR'0 (Real.rpow_nonneg hR'0 _))
  · refine Eventually.of_forall fun b z _ => ?_
    have hne : (r b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith [hr1 b])
    have h0 := (((hasDerivAt_id' z).sub_const s₀).neg.const_cpow (c := (r b : ℂ)) (Or.inl hne)).mul_const (u b)
    show HasDerivAt (fun x => (r b : ℂ) ^ (-(x - s₀)) * u b)
      (-(Complex.log (r b) * (r b : ℂ) ^ (-(z - s₀)) * u b)) z
    have e : (r b : ℂ) ^ (-(z - s₀)) * Complex.log (r b) * -1 * u b =
        -(Complex.log (r b) * (r b : ℂ) ^ (-(z - s₀)) * u b) := by ring
    exact h0.congr_deriv e

theorem core (ν : Measure H) (r : H → ℝ) (u : H → ℂ) (s₀ w₀ : ℂ) (B : ℕ → Set H)
    (hBm : ∀ j, MeasurableSet (B j)) (hmono : Monotone B) (hcov : ⋃ j, B j = univ)
    (hfin : ∀ j, ν (B j) < ⊤) (hr1 : ∀ b, 1 ≤ r b) (hrm : Measurable r) (hrb : ∀ j, ∃ Rm, ∀ b ∈ B j, r b ≤ Rm)
    (hum : AEStronglyMeasurable u ν) (hub : ∃ C, ∀ b, ‖u b‖ ≤ C)
    (hshell : ∀ z j, ∫ b in B (j + 1) \ B j, fz r u s₀ z b ∂ν = 0)
    (hint : ∃ t : ℝ, ∀ z : ℂ, t < z.re → Integrable (fz r u s₀ z) ν)
    (hval : Tendsto (fun j => ∫ b in B j, u b ∂ν) atTop (𝓝 w₀)) :
    ∃ W : ℂ → ℂ, Differentiable ℂ W ∧ W s₀ = w₀ ∧ ∃ t : ℝ, ∀ z : ℂ, t < z.re →
      Integrable (fz r u s₀ z) ν ∧ W z = ∫ b, fz r u s₀ z b ∂ν := by
  obtain ⟨C, hC⟩ := hub
  have hon : ∀ z j, IntegrableOn (PositivityTheory.SiegelWeilFormula.SwLocFin.fz r u s₀ z) (B j) ν := fun z j => by
    obtain ⟨Rm, hRm⟩ := hrb j
    exact PositivityTheory.SiegelWeilFormula.SwLocFin.integrableOn_fz hr1 hrm hum hC (hBm j) (hfin j) hRm z
  have hG : ∀ z j, ∫ b in B j, PositivityTheory.SiegelWeilFormula.SwLocFin.fz r u s₀ z b ∂ν =
      ∫ b in B 0, PositivityTheory.SiegelWeilFormula.SwLocFin.fz r u s₀ z b ∂ν := by
    intro z j
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [← ih]
      have hsub : B j ⊆ B (j + 1) := hmono (Nat.le_succ j)
      rw [← Set.union_diff_cancel hsub, setIntegral_union Set.disjoint_sdiff_right
        ((hBm _).diff (hBm _)) (hon z j) ((hon z (j + 1)).mono_set diff_subset), hshell, add_zero]
  obtain ⟨R0, hR0⟩ := hrb 0
  refine ⟨fun z => ∫ b in B 0, PositivityTheory.SiegelWeilFormula.SwLocFin.fz r u s₀ z b ∂ν,
    PositivityTheory.SiegelWeilFormula.SwLocFin.differentiable_setIntegral_fz hr1 hrm hum hC (hBm 0) (hfin 0) hR0, ?_, ?_⟩
  · have hfs : ∀ j, ∫ b in B j, PositivityTheory.SiegelWeilFormula.SwLocFin.fz r u s₀ s₀ b ∂ν = ∫ b in B j, u b ∂ν := by
      intro j
      simp only [PositivityTheory.SiegelWeilFormula.SwLocFin.fz, sub_self, neg_zero, Complex.cpow_zero, one_mul]
    have e : (fun j => ∫ b in B j, u b ∂ν) =
        fun _ => ∫ b in B 0, PositivityTheory.SiegelWeilFormula.SwLocFin.fz r u s₀ s₀ b ∂ν := by
      funext j
      rw [← hfs j, hG]
    rw [e] at hval
    exact tendsto_nhds_unique tendsto_const_nhds hval
  · obtain ⟨t, ht⟩ := hint
    refine ⟨t, fun z hz => ⟨ht z hz, ?_⟩⟩
    have hlim := tendsto_setIntegral_of_monotone hBm hmono (ht z hz).integrableOn
    rw [hcov, Measure.restrict_univ] at hlim
    have e : (fun j => ∫ b in B j, PositivityTheory.SiegelWeilFormula.SwLocFin.fz r u s₀ z b ∂ν) =
        fun _ => ∫ b in B 0, PositivityTheory.SiegelWeilFormula.SwLocFin.fz r u s₀ z b ∂ν := funext (hG z)
    rw [e] at hlim
    exact tendsto_nhds_unique tendsto_const_nhds hlim

end PositivityTheory.SiegelWeilFormula.SwLocFin
end
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalCharacterIntegrals.LocFin2OfX

section

@[expose] public section

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.SwLocFin

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory GlobalTheory.Cont PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gen Filter Topology
open scoped TensorProduct Matrix

theorem whI_eq {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {M n : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F))
    (μv : Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (lam : Measure (Fin n → Fv F v ⊗[F] E))
    (L₁ L₂ : AddSubgroup (Fin n → Fv F v ⊗[F] E)) (Φv : (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ)
    (T : HermR (Fv F v) σ n) (z : ℂ) (b : HermR (Fv F v) σ n) :
    whI (Fv F v) σ J (psiV F ψ v) μv Φv (nu2 lam L₁ L₂) T.1 z b =
      fz (fun b : HermR (Fv F v) σ n => nu2 lam L₁ L₂ b.1) (uu σ J ψ v μv Φv T) (((M : ℂ) - n) / 2) z b := by
  simp only [whI, fz, uu, mul_assoc]

theorem locFinX_of (hS : ShellP) (hC : ConvP) (hD : DualP) : LocFinX := by
  intro F E _ _ _ _ _ σ hcm M J hJ n ψ hψ v μv νv lam L₁ L₂ hμ hν hlam h₁ h₂ Φv hΦ g hg T hT
  have h : Hyp σ M J n ψ v μv νv lam L₁ L₂ Φv g T := ⟨hcm, hJ, hψ, hμ, hν, hlam, h₁, h₂, hΦ, hg, hT⟩
  haveI : νv.IsAddHaarMeasure := hν.1
  obtain ⟨R₀, hR₀⟩ := hS F E σ M J n ψ v μv νv lam L₁ L₂ Φv g T h 2 one_lt_two
  set R₁ : ℝ := max R₀ 1 with hR₁
  have hR₁pos : 0 < R₁ := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  set B : ℕ → Set (HermR (Fv F v) σ n) := fun j => {b | nM v b.1 ≤ R₁ * 2 ^ j} with hB
  have hWeq : ∀ z, whI (Fv F v) σ J (psiV F ψ v) μv Φv (nu2 lam L₁ L₂) T.1 z =
      fz (fun b : HermR (Fv F v) σ n => nu2 lam L₁ L₂ b.1) (uu σ J ψ v μv Φv T) (((M : ℂ) - n) / 2) z :=
    fun z => funext fun b => whI_eq σ J ψ v μv lam L₁ L₂ Φv T z b
  obtain ⟨W, hWd, hW0, t, hWt⟩ := core νv (fun b : HermR (Fv F v) σ n => nu2 lam L₁ L₂ b.1) (uu σ J ψ v μv Φv T)
    (((M : ℂ) - n) / 2) (g T) B
    (fun j => measurableSet_ballH _)
    (fun i j hij => by
      intro b hb
      simp only [hB, Set.mem_setOf_eq] at hb ⊢
      exact hb.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ one_le_two hij) hR₁pos.le))
    (by
      refine Set.eq_univ_of_forall fun b => ?_
      obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (nM v b.1 / R₁) one_lt_two
      refine Set.mem_iUnion.2 ⟨j, ?_⟩
      simp only [hB, Set.mem_setOf_eq]
      rw [div_lt_iff₀ hR₁pos] at hj
      linarith)
    (fun j => (isCompact_ballH _).measure_lt_top)
    (lattice_norm_ge_one h)
    (continuous_lattice_norm h).measurable
    (fun j => by
      obtain ⟨C, hC⟩ := (isCompact_ballH (σ := σ) (n := n) (v := v) (R₁ * 2 ^ j)).exists_bound_of_continuousOn
        (continuous_lattice_norm h).continuousOn
      exact ⟨C, fun b hb => (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hC b hb)⟩)
    (continuous_uu h).aestronglyMeasurable
    (uu_bound h)
    (fun z j => by
      have hset : B (j + 1) \ B j = {b : HermR (Fv F v) σ n | R₁ * 2 ^ j < nM v b.1 ∧ nM v b.1 ≤ 2 * (R₁ * 2 ^ j)} := by
        ext b
        simp only [hB, Set.mem_diff, Set.mem_setOf_eq, not_le, pow_succ]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨h2, by linarith⟩
        · rintro ⟨h1, h2⟩; exact ⟨by linarith, h1⟩
      rw [hset, ← hWeq z]
      exact hR₀ _ ((le_max_left _ _).trans (le_mul_of_one_le_right hR₁pos.le (one_le_pow₀ one_le_two))) z)
    (by
      obtain ⟨t, ht⟩ := hC F E σ M J n ψ v μv νv lam L₁ L₂ Φv g T h
      exact ⟨t, fun z hz => by rw [← hWeq z]; exact ht z hz⟩)
    ((hD F E σ M J n ψ v μv νv lam L₁ L₂ Φv g T h).comp
      (Tendsto.const_mul_atTop hR₁pos (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)))
  refine ⟨W, hWd, hW0, t, fun z hz => ?_⟩
  rw [hWeq z]
  exact hWt z hz

theorem locFin2_of_X (h : LocFinX) : LocFin2 := by
  intro F E _ _ _ _ _ σ hcm M J hJ n _ ψ hψ v μv νv lam L₁ L₂ hμ hν hlam h₁ h₂ Φv hΦ g hg T hT
  exact h F E σ hcm M J hJ n ψ hψ v μv νv lam L₁ L₂ hμ hν hlam h₁ h₂ Φv hΦ g hg T hT

end PositivityTheory.SiegelWeilFormula.SwLocFin
end
end
end
