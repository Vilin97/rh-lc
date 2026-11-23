module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.Smooth
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.RedH
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Iwa
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.RowMaj
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ThMeas
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.ContinuousAdelicGL2OfContinuousEntries
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.ImportsRest
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.UnitsCpt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ThBoundH
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ThMeas
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Vol
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.CuspZero
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.Imports
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.WfBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.HatMaj
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ZpowLeAbs
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.HatSt
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.ImportsMore
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.UnitsCpt
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.RowBoundH

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Ff.rowBoundH :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (π : TR.CuspSub F 2), RowBoundH W π := by
  intro F E _ _ _ _ _ _ _ D W π f hf φ hφ h x
  obtain ⟨y, hy, φ₁, hφ₁, m, e⟩ := redH F E D W h φ hφ
  obtain ⟨c, hc, hred⟩ := UpperTheory.ConvolutionTheory.R2.red F
  obtain ⟨B₁, hB₁⟩ := rowMaj F E D W φ₁ hφ₁ y hy c hc
  have hC : IsCompact ((fun k : G1 F => gl k * ((gl m)⁻¹ * x)) '' KK F) :=
    (iwa F).1.image (M.continuous_gl.mul continuous_const)
  obtain ⟨B₂, hB₂⟩ := (UpperTheory.ConvolutionTheory.R2.decay F π f hf).2 _ hC c hc 1
  have hinv := (thMeas F E D W (W.L (infGL E 2 y) φ₁)).2.2.2.1
  refine ⟨B₂ * B₁, fun g => ?_⟩
  have e1 : W.Om g (W.L h φ) = W.Om (g * m) (W.L (infGL E 2 y) φ₁) := by
    simpa using e g 1
  obtain ⟨γ, b, a, k, hk, ek, ha⟩ := hred (g * m)
  have e2 : ThRow 0 0 (W.Om g (W.L h φ)).1 =
      ThRow 0 0 (W.Om (nU b * mD a * k) (W.L (infGL E 2 y) φ₁)).1 := by
    rw [e1, ← ek]
    exact (hinv γ (g * m)).symm
  have e3 : f.1 (gl g * x) = f.1 (gl (nU b * mD a) * (gl k * ((gl m)⁻¹ * x))) := by
    have e4 : gl (nU b * mD a) * (gl k * ((gl m)⁻¹ * x)) =
        ratGL F 2 (Matrix.SpecialLinearGroup.toGL γ) * (gl g * x) := by
      have e5 : ratGL F 2 (Matrix.SpecialLinearGroup.toGL γ) = gl (ratS F γ) := Units.ext rfl
      rw [← mul_assoc, ← gl_mul, ← mul_assoc, ← ek, gl_mul, gl_mul, e5]
      group
    rw [e4]
    exact ((π.cusp _ hf).1.left _ _).symm
  rw [norm_mul, e2, e3]
  have hp := M.ab_pos a
  have h1 := hB₁ b a k hk ha
  have h2 := hB₂ b a _ ⟨k, hk, rfl⟩ ha
  calc _ ≤ (B₂ * (ab a)⁻¹ ^ 1) * (B₁ * ab a) :=
        mul_le_mul h2 h1 (norm_nonneg _) ((norm_nonneg _).trans h2)
    _ = B₂ * B₁ := by field_simp
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.WeilLiftOneCuspidal

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Ff.weilLift_one_cuspidal :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), UnfoldedThetaIntegralConvergesSimilitudeOne W M π := by
  intro F E _ _ _ _ _ _ _ D W M π f hf φ x
  have hL := (UpperTheory.ConvolutionTheory.R2.Pp.cuspZero F π f hf).1
  have hW := UpperTheory.ConvolutionTheory.R2.Pp.wfBasic F f.1 hL
  have hWc : Continuous fun g : G1 F => Wf f.1 (gl g * x) :=
    hW.1.comp (UpperTheory.ConvolutionTheory.R2.continuous_gl.mul continuous_const)
  have hm : ∀ φ : S4 F, Measurable fun g => Wf f.1 (gl g * x) * hat (W.Om g φ).1 ![0, 1, 1, 0] := fun φ =>
    hWc.measurable.mul ((thMeas F E D W φ).2.2.2.2 _)
  refine ⟨hm φ, ?_, ?_⟩
  · intro b g
    have h1 : Wf f.1 (gl (nU b * g) * x) = ψ (-b) * Wf f.1 (gl g * x) := by
      rw [UpperTheory.ConvolutionTheory.R2.gl_mul, mul_assoc]
      exact hW.2.1 b _
    have h2 : hat (W.Om (nU b * g) φ).1 ![0, 1, 1, 0] = ψ b * hat (W.Om g φ).1 ![0, 1, 1, 0] := by
      rw [map_mul, Module.End.mul_apply, (hatSt F E D W).n b (W.Om g φ) ![0, 1, 1, 0]]
      have e : Function.update ![(0 : A F), 1, 1, 0] 1 (![(0 : A F), 1, 1, 0] 1 + b * ![(0 : A F), 1, 1, 0] 0) = ![0, 1, 1, 0] := by
        ext i; fin_cases i <;> simp
      rw [e]
      simp
    rw [h1, h2]
    have h3 : ψ (-b) * ψ b = 1 := by
      rw [UpperTheory.ConvolutionTheory.R2.ψ_neg]; exact inv_mul_cancel₀ (UpperTheory.ConvolutionTheory.R2.ψ_ne_zero b)
    calc _ = (ψ (-b) * ψ b) * (Wf f.1 (gl g * x) * hat (W.Om g φ).1 ![0, 1, 1, 0]) := by ring
      _ = _ := by rw [h3, one_mul]
  · intro hφ y hy
    obtain ⟨N, hN⟩ := wtId F
    obtain ⟨K, hK, hB'⟩ := hatMaj F E D W φ hφ y hy
    obtain ⟨B', hB'⟩ := hB' N
    obtain ⟨B, hB⟩ := UpperTheory.ConvolutionTheory.R2.Pp.bdd F π f hf {x} isCompact_singleton
    have := M.prob
    have hI := (hN K hK).comp_fst M.κ
    have hmaj : Integrable (fun p : IdeleGroup F × G1 F => (B * B') * ((ab p.1)⁻¹ * wt K N ![0, ((p.1⁻¹ : (A F)ˣ) : A F), (p.1 : A F), 0])) M.ν :=
      hI.const_mul _
    refine hmaj.mono' ?_ ?_
    · have hc : Continuous fun p : IdeleGroup F × G1 F => mD p.1 * p.2 :=
        (UpperTheory.ConvolutionTheory.R2.continuous_mD.comp continuous_fst).mul continuous_snd
      have hab : Continuous fun p : IdeleGroup F × G1 F => ab p.1 :=
        UpperTheory.ConvolutionTheory.R2.continuous_ab.comp continuous_fst
      have hmm : Measurable (iw fun g => Wf f.1 (gl g * x) * hat (W.Om g (W.L (infGL E 2 y) φ)).1 ![0, 1, 1, 0]) :=
        (Complex.continuous_ofReal.comp ((hab.inv₀ fun p => UpperTheory.ConvolutionTheory.R2.ab_ne_zero _).pow 2)).measurable.mul
          ((hm (W.L (infGL E 2 y) φ)).comp hc.measurable)
      exact hmm.aestronglyMeasurable
    · have hk : ∀ᵐ p ∂M.ν, p.2 ∈ KK F := Measure.quasiMeasurePreserving_snd.ae (by
        have := M.supp
        exact measure_eq_zero_iff_ae_notMem.1 (by simpa using this) |>.mono (fun k hk => by simpa using hk))
      filter_upwards [hk] with p hp
      obtain ⟨a, k⟩ := p
      have hk' : k ∈ KK F := hp
      have h1 := (hB (mD a * k) x rfl).2
      have h2 := hB' 0 a k hk' 1 1 0
      rw [UpperTheory.ConvolutionTheory.R2.nU_zero, one_mul, mul_one, mul_one, mul_zero] at h2
      have hpos : 0 < ab a := UpperTheory.ConvolutionTheory.R2.ab_pos a
      have hB0 : 0 ≤ B := (norm_nonneg _).trans h1
      simp only [iw, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_pos (by positivity)]
      calc ((ab a)⁻¹ ^ 2) * (‖Wf f.1 (gl (mD a * k) * x)‖ * ‖hat (W.Om (mD a * k) (W.L (infGL E 2 y) φ)).1 ![0, 1, 1, 0]‖)
          ≤ ((ab a)⁻¹ ^ 2) * (B * (B' * ab a * wt K N ![0, ((a⁻¹ : (A F)ˣ) : A F), (a : A F), 0])) := by
            gcongr
        _ = _ := by field_simp
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.One

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.conv :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), St.Conv W M π := by
  intro F E _ _ _ _ _ _ _ D W M π f hf φ hφ h
  have hc : Continuous fun g : G1 F => f.1 (gl g * dM (nu F h)) :=
    (decay F π f hf).1.comp (Matrix.SpecialLinearGroup.continuous_toGL.mul continuous_const)
  haveI : IsFiniteMeasure (M.μ.restrict M.D) := ⟨by simpa using vol F M⟩
  obtain ⟨m1, -, m2, -, -⟩ := thMeas F E D W (W.L h φ)
  obtain ⟨a1, a2, -⟩ := weilLift_one_cuspidal F E D W M π f hf (W.L h φ) (dM (nu F h))
  refine ⟨?_, ?_, a1, a2, ?_⟩
  · obtain ⟨B, hB⟩ := thBoundH F E D W π f hf φ hφ h {dM (nu F h)} isCompact_singleton {1} isCompact_singleton
      (by rintro _ rfl; simp [Ff.One, nu])
    refine Integrable.of_bound (hc.measurable.mul m1).aestronglyMeasurable B (ae_of_all _ fun g => ?_)
    simpa using hB g _ rfl 1 rfl
  · obtain ⟨B, hB⟩ := rowBoundH F E D W π f hf φ hφ h (dM (nu F h))
    exact Integrable.of_bound (hc.measurable.mul (m2 0 0)).aestronglyMeasurable B (ae_of_all _ hB)
  · obtain ⟨y, hy, φ₁, h₁, m, hm⟩ := redH F E D W h φ hφ
    obtain ⟨b1, b2, -⟩ := weilLift_one_cuspidal F E D W M π f hf (W.L (infGL E 2 y) φ₁) ((gl m)⁻¹ * dM (nu F h))
    have b3 := (weilLift_one_cuspidal F E D W M π f hf φ₁ ((gl m)⁻¹ * dM (nu F h))).2.2 h₁ y hy
    have := ((inv F M _ b1 b2 b3).1 m).1
    have e : w1 W f.1 φ h = fun g => Wf f.1 (gl (g * m) * ((gl m)⁻¹ * dM (nu F h))) *
        hat (W.Om (g * m) (W.L (infGL E 2 y) φ₁)).1 ![0, 1, 1, 0] := by
      funext g
      have h2 := hm g 1
      simp only [map_one, mul_one] at h2
      rw [w1, h2, show gl (g * m) = gl g * gl m from map_mul _ _ _, mul_assoc, mul_inv_cancel_left]
    rw [e]
    exact this
end
end
