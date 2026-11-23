module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussTubeOfTubeGood
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContourShiftGaussianDecayStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TubeTransformHorizontalInvariance

section

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier

namespace GlobalTheory.CompanionTheory.TubeFourier

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]

theorem shiftFst_bound {Ω : Set (ℝ × ℝ)} {G : ℂ × ℂ → X} (hG : GaussTube G Ω) {a b c : ℝ}
    (hs : ∀ s ∈ Set.Icc a b, (s, c) ∈ Ω) (t : ℝ × ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ l : ℂ × ℂ, l.1.re ∈ Set.Icc a b → l.2.re = c →
      ‖Complex.exp (-dot l t) • G l‖ ≤ M * Real.exp (-(l.1.im ^ 2 + l.2.im ^ 2)) := by
  have hC : IsCompact ((fun s : ℝ => (s, c)) '' Set.Icc a b) :=
    isCompact_Icc.image (Continuous.prodMk continuous_id continuous_const)
  have hCΩ : (fun s : ℝ => (s, c)) '' Set.Icc a b ⊆ Ω := by
    rintro _ ⟨s, hs', rfl⟩
    exact hs s hs'
  obtain ⟨M₀, hM₀⟩ := hG.3 _ hCΩ hC
  refine ⟨Real.exp ((|a| + |b|) * |t.1| + |c| * |t.2|) * |M₀|, by positivity, ?_⟩
  intro l hl hlc
  have hmem : l ∈ PositivityTheory.RgEis.tube ((fun s : ℝ => (s, c)) '' Set.Icc a b) := by
    show (l.1.re, l.2.re) ∈ (fun s : ℝ => (s, c)) '' Set.Icc a b
    exact ⟨l.1.re, hl, Prod.ext rfl hlc.symm⟩
  have hGl := hM₀ l hmem
  have hre : (-GlobalTheory.CompanionTheory.TubeFourier.dot l t).re = -(l.1.re * t.1 + l.2.re * t.2) := by
    simp [GlobalTheory.CompanionTheory.TubeFourier.dot]
  have hx : |l.1.re| ≤ |a| + |b| :=
    abs_le.2 ⟨by linarith [neg_abs_le a, abs_nonneg b, hl.1], by linarith [le_abs_self b, abs_nonneg a, hl.2]⟩
  have hexp : ‖Complex.exp (-GlobalTheory.CompanionTheory.TubeFourier.dot l t)‖ ≤
      Real.exp ((|a| + |b|) * |t.1| + |c| * |t.2|) := by
    rw [Complex.norm_exp, hre, hlc]
    apply Real.exp_le_exp.2
    have e1 : -(l.1.re * t.1) ≤ (|a| + |b|) * |t.1| := by
      calc -(l.1.re * t.1) ≤ |l.1.re * t.1| := neg_le_abs _
        _ = |l.1.re| * |t.1| := abs_mul _ _
        _ ≤ (|a| + |b|) * |t.1| := mul_le_mul_of_nonneg_right hx (abs_nonneg _)
    have e2 : -(c * t.2) ≤ |c| * |t.2| := by
      rw [← abs_mul]
      exact neg_le_abs _
    linarith
  rw [norm_smul]
  calc ‖Complex.exp (-GlobalTheory.CompanionTheory.TubeFourier.dot l t)‖ * ‖G l‖
      ≤ Real.exp ((|a| + |b|) * |t.1| + |c| * |t.2|) *
          (|M₀| * Real.exp (-(l.1.im ^ 2 + l.2.im ^ 2))) :=
        mul_le_mul hexp (hGl.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le))
          (norm_nonneg _) (Real.exp_pos _).le
    _ = Real.exp ((|a| + |b|) * |t.1| + |c| * |t.2|) * |M₀| *
          Real.exp (-(l.1.im ^ 2 + l.2.im ^ 2)) := by ring

theorem integrable_exp_neg_sq_prod :
    Integrable (fun y : ℝ × ℝ => Real.exp (-y.1 ^ 2) * Real.exp (-y.2 ^ 2)) := by
  have h := (integrable_exp_neg_mul_sq one_pos).mul_prod (integrable_exp_neg_mul_sq one_pos)
  rw [← MeasureTheory.Measure.volume_eq_prod] at h
  refine h.congr (Filter.Eventually.of_forall fun y => ?_)
  simp only [neg_mul, one_mul]

theorem shiftFst_integrable {Ω : Set (ℝ × ℝ)} {G : ℂ × ℂ → X} (hG : GaussTube G Ω) {a b c : ℝ}
    (hs : ∀ s ∈ Set.Icc a b, (s, c) ∈ Ω) (t : ℝ × ℝ) {s : ℝ} (hsm : s ∈ Set.Icc a b) :
    Integrable (fun y : ℝ × ℝ => Complex.exp (-dot (pt (s, c) y) t) • G (pt (s, c) y)) := by
  obtain ⟨M, -, hM⟩ := GlobalTheory.CompanionTheory.TubeFourier.shiftFst_bound hG hs t
  have htp : Continuous (GlobalTheory.CompanionTheory.TubeFourier.pt (s, c)) := by
    have h : GlobalTheory.CompanionTheory.TubeFourier.pt (s, c) = fun y : ℝ × ℝ =>
        ((s : ℂ) + (y.1 : ℂ) * Complex.I, (c : ℂ) + (y.2 : ℂ) * Complex.I) := by
      funext y
      simp only [GlobalTheory.CompanionTheory.TubeFourier.pt, Complex.mk_eq_add_mul_I]
    rw [h]
    fun_prop
  have hmem : ∀ y, GlobalTheory.CompanionTheory.TubeFourier.pt (s, c) y ∈ PositivityTheory.RgEis.tube Ω := fun _ => hs s hsm
  have hGc : Continuous (fun y => G (GlobalTheory.CompanionTheory.TubeFourier.pt (s, c) y)) := hG.2.comp_continuous htp hmem
  have hpair : Continuous (fun l : ℂ × ℂ => GlobalTheory.CompanionTheory.TubeFourier.dot l t) := by
    simp only [GlobalTheory.CompanionTheory.TubeFourier.dot]
    fun_prop
  have hE : Continuous (fun y => Complex.exp (-GlobalTheory.CompanionTheory.TubeFourier.dot (GlobalTheory.CompanionTheory.TubeFourier.pt (s, c) y) t)) :=
    (hpair.comp htp).neg.cexp
  refine MeasureTheory.Integrable.mono'
    (GlobalTheory.CompanionTheory.TubeFourier.integrable_exp_neg_sq_prod.const_mul M)
    (hE.smul hGc).aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
  refine (hM (GlobalTheory.CompanionTheory.TubeFourier.pt (s, c) y) hsm rfl).trans (le_of_eq ?_)
  show M * Real.exp (-(y.1 ^ 2 + y.2 ^ 2)) = M * (Real.exp (-y.1 ^ 2) * Real.exp (-y.2 ^ 2))
  rw [← Real.exp_add]
  congr 2
  ring

theorem phi_eq_iterated {Ω : Set (ℝ × ℝ)} {G : ℂ × ℂ → X} (hG : GaussTube G Ω) {a b c : ℝ}
    (hs : ∀ s ∈ Set.Icc a b, (s, c) ∈ Ω) (t : ℝ × ℝ) {s : ℝ} (hsm : s ∈ Set.Icc a b) :
    phi G (s, c) t = ∫ y₂ : ℝ, ∫ y₁ : ℝ,
      Complex.exp (-dot (pt (s, c) (y₁, y₂)) t) • G (pt (s, c) (y₁, y₂)) := by
  have h := shiftFst_integrable hG hs t hsm
  unfold phi
  rw [Measure.volume_eq_prod] at h ⊢
  exact integral_prod_symm _ h

end GlobalTheory.CompanionTheory.TubeFourier

theorem GlobalTheory.CompanionTheory.TubeFourier.phi_shift_fst :
    ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] (Ω : Set (ℝ × ℝ)) (G : ℂ × ℂ → X),
      GaussTube G Ω → ∀ a b c : ℝ, a ≤ b → (∀ s ∈ Set.Icc a b, (s, c) ∈ Ω) →
        ∀ t : ℝ × ℝ, phi G (a, c) t = phi G (b, c) t := by
  intro X _ _ _ Ω G hG a b c hab hs t
  rw [GlobalTheory.CompanionTheory.TubeFourier.phi_eq_iterated hG hs t (Set.left_mem_Icc.2 hab),
    GlobalTheory.CompanionTheory.TubeFourier.phi_eq_iterated hG hs t (Set.right_mem_Icc.2 hab)]
  obtain ⟨M, hM0, hM⟩ := GlobalTheory.CompanionTheory.TubeFourier.shiftFst_bound hG hs t
  refine integral_congr_ae (ae_of_all _ fun y₂ => ?_)
  have hline : DifferentiableOn ℂ (fun z : ℂ => G (z, ⟨c, y₂⟩)) {z : ℂ | z.re ∈ Set.Icc a b} := by
    have h1 := hG.1 ((0 : ℂ), (⟨c, y₂⟩ : ℂ)) ((1 : ℂ), (0 : ℂ))
    have heq : ∀ τ : ℂ, ((0 : ℂ), (⟨c, y₂⟩ : ℂ)) + τ • ((1 : ℂ), (0 : ℂ)) = (τ, ⟨c, y₂⟩) :=
      fun τ => Prod.ext (by simp) (by simp)
    simp only [heq] at h1
    refine h1.mono fun z hz => ?_
    exact hs z.re hz
  have hpair : Differentiable ℂ (fun z : ℂ => Complex.exp (-GlobalTheory.CompanionTheory.TubeFourier.dot (z, ⟨c, y₂⟩) t)) := by
    simp only [GlobalTheory.CompanionTheory.TubeFourier.dot]
    fun_prop
  have hdiff : DifferentiableOn ℂ
      (fun z : ℂ => Complex.exp (-GlobalTheory.CompanionTheory.TubeFourier.dot (z, ⟨c, y₂⟩) t) • G (z, ⟨c, y₂⟩))
      {z : ℂ | z.re ∈ Set.Icc a b} :=
    hpair.differentiableOn.smul hline
  have hbound : ∀ z : ℂ, z.re ∈ Set.Icc a b →
      ‖Complex.exp (-GlobalTheory.CompanionTheory.TubeFourier.dot (z, ⟨c, y₂⟩) t) • G (z, ⟨c, y₂⟩)‖ ≤
        M * Real.exp (-z.im ^ 2) := by
    intro z hz
    refine (hM (z, ⟨c, y₂⟩) hz rfl).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hM0)
    show -(z.im ^ 2 + y₂ ^ 2) ≤ -z.im ^ 2
    linarith [sq_nonneg y₂]
  exact GlobalTheory.T.contour_shift_gaussian_decay X
    (fun z : ℂ => Complex.exp (-GlobalTheory.CompanionTheory.TubeFourier.dot (z, ⟨c, y₂⟩) t) • G (z, ⟨c, y₂⟩))
    a b M hab hdiff hbound
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TubeTransformHorizontalInvarianceStatement

section

@[expose] public section

open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier

theorem _root_.GlobalTheory.T.tube_transform_horizontal_invariance : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] (Ω : Set (ℝ × ℝ)) (G : ℂ × ℂ → X), GaussTube G Ω → ∀ a b c : ℝ, a ≤ b → (∀ s ∈ Set.Icc a b, (s, c) ∈ Ω) → ∀ t : ℝ × ℝ, phi G (a, c) t = phi G (b, c) t := by
  first | exact @GlobalTheory.CompanionTheory.TubeFourier.phi_shift_fst | exact GlobalTheory.CompanionTheory.TubeFourier.phi_shift_fst | (intros; apply GlobalTheory.CompanionTheory.TubeFourier.phi_shift_fst <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TubeTransformVerticalInvariance

section

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier

namespace GlobalTheory.CompanionTheory.TubeFourier

theorem continuous_mk_im_shiftSnd (x : ℝ) : Continuous fun y : ℝ => (⟨x, y⟩ : ℂ) := by
  have h : (fun y : ℝ => (⟨x, y⟩ : ℂ)) = fun y : ℝ => (x : ℂ) + (y : ℂ) * Complex.I := by
    ext y
    apply Complex.ext <;> simp
  rw [h]
  fun_prop

theorem continuous_pt_shiftSnd (x : ℝ × ℝ) : Continuous fun y : ℝ × ℝ => pt x y := by
  unfold pt
  exact ((continuous_mk_im_shiftSnd x.1).comp continuous_fst).prodMk ((continuous_mk_im_shiftSnd x.2).comp continuous_snd)

theorem integrable_gauss_prod_shiftSnd (K : ℝ) :
    Integrable fun y : ℝ × ℝ => K * Real.exp (-(y.1 ^ 2 + y.2 ^ 2)) := by
  have h1 : Integrable fun x : ℝ => Real.exp (-1 * x ^ 2) := integrable_exp_neg_mul_sq one_pos
  have h2 := (h1.mul_prod h1).const_mul K
  rw [Measure.volume_eq_prod]
  refine h2.congr (Eventually.of_forall fun y => ?_)
  simp only
  rw [← Real.exp_add]
  congr 2
  ring

theorem phi_shift_snd (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] (Ω : Set (ℝ × ℝ))
    (G : ℂ × ℂ → X) (hG : GaussTube G Ω) (a b c : ℝ) (hab : a ≤ b) (hs : ∀ s ∈ Set.Icc a b, (c, s) ∈ Ω)
    (t : ℝ × ℝ) : phi G (c, a) t = phi G (c, b) t := by
  set C : Set (ℝ × ℝ) := (fun s : ℝ => (c, s)) '' Set.Icc a b with hC
  have hCc : IsCompact C := isCompact_Icc.image (by fun_prop)
  have hCΩ : C ⊆ Ω := by
    rintro _ ⟨s, hs', rfl⟩
    exact hs s hs'
  obtain ⟨M, hM⟩ := hG.decay C hCΩ hCc
  obtain ⟨B, hB⟩ := (hCc.image (f := fun x : ℝ × ℝ => Real.exp (-(x.1 * t.1 + x.2 * t.2)))
    (by fun_prop)).bddAbove
  let H : ℂ × ℂ → X := fun l => Complex.exp (-dot l t) • G l
  have hexp : Continuous fun l : ℂ × ℂ => Complex.exp (-dot l t) := by
    unfold dot
    fun_prop
  have hbound : ∀ l ∈ tube C, ‖H l‖ ≤ (|B| * |M|) * Real.exp (-(l.1.im ^ 2 + l.2.im ^ 2)) := by
    intro l hl
    have h1 : ‖Complex.exp (-dot l t)‖ ≤ |B| := by
      rw [Complex.norm_exp]
      have h : (-dot l t).re = -(l.1.re * t.1 + l.2.re * t.2) := by simp [dot]
      rw [h]
      exact (hB ⟨(l.1.re, l.2.re), hl, rfl⟩).trans (le_abs_self B)
    have h2 : ‖G l‖ ≤ |M| * Real.exp (-(l.1.im ^ 2 + l.2.im ^ 2)) :=
      (hM l hl).trans (mul_le_mul_of_nonneg_right (le_abs_self M) (Real.exp_pos _).le)
    calc ‖H l‖ = ‖Complex.exp (-dot l t)‖ * ‖G l‖ := norm_smul _ _
      _ ≤ |B| * (|M| * Real.exp (-(l.1.im ^ 2 + l.2.im ^ 2))) := by gcongr
      _ = _ := by ring
  have hcont : ContinuousOn H (tube Ω) := hexp.continuousOn.smul hG.cont
  have hmem : ∀ s ∈ Set.Icc a b, ∀ y : ℝ × ℝ, pt (c, s) y ∈ tube C := fun s hs' y => ⟨s, hs', rfl⟩
  have hint : ∀ s ∈ Set.Icc a b, Integrable fun y : ℝ × ℝ => H (pt (c, s) y) := by
    intro s hs'
    have hc : Continuous fun y : ℝ × ℝ => H (pt (c, s) y) :=
      hcont.comp_continuous (continuous_pt_shiftSnd _) fun y => hs s hs'
    refine (integrable_gauss_prod_shiftSnd (|B| * |M|)).mono' hc.aestronglyMeasurable
      (Eventually.of_forall fun y => ?_)
    exact hbound _ (hmem s hs' y)
  have hphi : ∀ s ∈ Set.Icc a b, phi G (c, s) t = ∫ y₁ : ℝ, ∫ y₂ : ℝ, H (⟨c, y₁⟩, ⟨s, y₂⟩) := by
    intro s hs'
    have h := hint s hs'
    rw [Measure.volume_eq_prod] at h
    have h' := integral_prod _ h
    rw [← Measure.volume_eq_prod] at h'
    exact h'
  rw [hphi a (Set.left_mem_Icc.2 hab), hphi b (Set.right_mem_Icc.2 hab)]
  refine integral_congr_ae (Eventually.of_forall fun y₁ => ?_)
  simp only
  refine GlobalTheory.T.contour_shift_gaussian_decay X (fun z => H (⟨c, y₁⟩, z)) a b (|B| * |M|) hab ?_ ?_
  · let p : ℂ × ℂ := (⟨c, y₁⟩, 0)
    let v : ℂ × ℂ := (0, 1)
    have e : ∀ τ : ℂ, p + τ • v = (⟨c, y₁⟩, τ) := by
      intro τ
      simp [p, v]
    have h1 : DifferentiableOn ℂ (fun τ : ℂ => G (⟨c, y₁⟩, τ)) {z : ℂ | z.re ∈ Set.Icc a b} := by
      have h := hG.hol p v
      simp only [e] at h
      exact h.mono fun z hz => hs _ hz
    have h2 : Differentiable ℂ fun τ : ℂ => Complex.exp (-dot ((⟨c, y₁⟩, τ) : ℂ × ℂ) t) := by
      unfold dot
      fun_prop
    exact h2.differentiableOn.smul h1
  · intro z hz
    have h := hbound (⟨c, y₁⟩, z) ⟨z.re, hz, rfl⟩
    refine h.trans ?_
    have hK : 0 ≤ |B| * |M| := by positivity
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hK
    have : 0 ≤ y₁ ^ 2 := sq_nonneg _
    simp only
    linarith

end GlobalTheory.CompanionTheory.TubeFourier
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TubeTransformVerticalInvarianceStatement

section

@[expose] public section

open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier

theorem _root_.GlobalTheory.T.tube_transform_vertical_invariance : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] (Ω : Set (ℝ × ℝ)) (G : ℂ × ℂ → X), GaussTube G Ω → ∀ a b c : ℝ, a ≤ b → (∀ s ∈ Set.Icc a b, (c, s) ∈ Ω) → ∀ t : ℝ × ℝ, phi G (c, a) t = phi G (c, b) t := by
  first | exact @GlobalTheory.CompanionTheory.TubeFourier.phi_shift_snd | exact GlobalTheory.CompanionTheory.TubeFourier.phi_shift_snd | (intros; apply GlobalTheory.CompanionTheory.TubeFourier.phi_shift_snd <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TubeTransformIndependentOfBase

section

@[expose] public section

open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier

namespace GlobalTheory.CompanionTheory.TubeFourier

theorem phi_eq_of_convex : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    (Ω : Set (ℝ × ℝ)) (G : ℂ × ℂ → X), IsOpen Ω → Convex ℝ Ω → GaussTube G Ω →
    ∀ x ∈ Ω, ∀ x' ∈ Ω, ∀ t : ℝ × ℝ, phi G x t = phi G x' t := by
  intro X _ _ _ Ω G hΩ hconv hG x hx x' hx' t
  have hhor : ∀ a b c : ℝ, (∀ s ∈ Set.uIcc a b, (s, c) ∈ Ω) →
      GlobalTheory.CompanionTheory.TubeFourier.phi G (a, c) t = GlobalTheory.CompanionTheory.TubeFourier.phi G (b, c) t := by
    intro a b c h
    rcases le_total a b with hab | hba
    · exact GlobalTheory.T.tube_transform_horizontal_invariance X Ω G hG a b c hab
        (fun s hs => h s (Set.Icc_subset_uIcc hs)) t
    · exact (GlobalTheory.T.tube_transform_horizontal_invariance X Ω G hG b a c hba
        (fun s hs => h s (Set.Icc_subset_uIcc' hs)) t).symm
  have hver : ∀ a b c : ℝ, (∀ s ∈ Set.uIcc a b, (c, s) ∈ Ω) →
      GlobalTheory.CompanionTheory.TubeFourier.phi G (c, a) t = GlobalTheory.CompanionTheory.TubeFourier.phi G (c, b) t := by
    intro a b c h
    rcases le_total a b with hab | hba
    · exact GlobalTheory.T.tube_transform_vertical_invariance X Ω G hG a b c hab
        (fun s hs => h s (Set.Icc_subset_uIcc hs)) t
    · exact (GlobalTheory.T.tube_transform_vertical_invariance X Ω G hG b a c hba
        (fun s hs => h s (Set.Icc_subset_uIcc' hs)) t).symm
  have hf : IsLocallyConstant (fun p : Ω => GlobalTheory.CompanionTheory.TubeFourier.phi G (p : ℝ × ℝ) t) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    rintro ⟨⟨p₁, p₂⟩, hp⟩
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hΩ (p₁, p₂) hp
    have hmem : {q : Ω | (q : ℝ × ℝ) ∈ Metric.ball (p₁, p₂) ε} ∈ 𝓝 (⟨(p₁, p₂), hp⟩ : Ω) :=
      continuousAt_subtype_val.preimage_mem_nhds (Metric.ball_mem_nhds _ hε)
    filter_upwards [hmem]
    rintro ⟨⟨q₁, q₂⟩, hq⟩ hqball
    have hd : dist q₁ p₁ < ε ∧ dist q₂ p₂ < ε := by
      have h' : dist (q₁, q₂) (p₁, p₂) < ε := hqball
      rwa [Prod.dist_eq, max_lt_iff] at h'
    obtain ⟨h₁, h₂⟩ := hd
    rw [Real.dist_eq] at h₁ h₂
    have hv : GlobalTheory.CompanionTheory.TubeFourier.phi G (q₁, p₂) t = GlobalTheory.CompanionTheory.TubeFourier.phi G (q₁, q₂) t := by
      refine hver p₂ q₂ q₁ (fun s hs => hball ?_)
      rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq]
      exact ⟨h₁, lt_of_le_of_lt (Set.abs_sub_left_of_mem_uIcc hs) h₂⟩
    have hh : GlobalTheory.CompanionTheory.TubeFourier.phi G (p₁, p₂) t = GlobalTheory.CompanionTheory.TubeFourier.phi G (q₁, p₂) t := by
      refine hhor p₁ q₁ p₂ (fun s hs => hball ?_)
      rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff, dist_self, Real.dist_eq]
      exact ⟨lt_of_le_of_lt (Set.abs_sub_left_of_mem_uIcc hs) h₁, hε⟩
    show GlobalTheory.CompanionTheory.TubeFourier.phi G (q₁, q₂) t = GlobalTheory.CompanionTheory.TubeFourier.phi G (p₁, p₂) t
    rw [← hv, ← hh]
  haveI : PreconnectedSpace Ω := Subtype.preconnectedSpace hconv.isPreconnected
  exact hf.apply_eq_of_isPreconnected isPreconnected_univ (Set.mem_univ (⟨x, hx⟩ : Ω))
    (Set.mem_univ (⟨x', hx'⟩ : Ω))

end GlobalTheory.CompanionTheory.TubeFourier
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TubeTransformIndependentOfBaseStatement

section

@[expose] public section

open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier

theorem _root_.GlobalTheory.T.tube_transform_independent_of_base : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] (Ω : Set (ℝ × ℝ)) (G : ℂ × ℂ → X), IsOpen Ω → Convex ℝ Ω → GaussTube G Ω → ∀ x ∈ Ω, ∀ x' ∈ Ω, ∀ t : ℝ × ℝ, phi G x t = phi G x' t := by
  first | exact @GlobalTheory.CompanionTheory.TubeFourier.phi_eq_of_convex | exact GlobalTheory.CompanionTheory.TubeFourier.phi_eq_of_convex | (intros; apply GlobalTheory.CompanionTheory.TubeFourier.phi_eq_of_convex <;> assumption)
end
end
