module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import GroundTheory.GlobalFields.TateThesis.AdelicChar
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdeleHaarMapEqScaledVolume
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Mathlib.Analysis.Complex.Circle
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Mathlib.Analysis.Fourier.FourierTransform
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SelfdualMeasureTransportEquiv
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LebesgueSelfdualForDotCharacter

section

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.RealFourier

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem fourierChar_smul (t : ℝ) (c : ℂ) :
    (Real.fourierChar t : Circle) • c = c * Complex.exp (2 * Real.pi * Complex.I * (t : ℝ)) := by
  rw [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, mul_comm]
  congr 2
  push_cast
  ring

theorem inversion_neg (ι : Type) [Fintype ι] (Φ : (ι → ℝ) → ℂ) (hc : Continuous Φ)
    (hs : HasCompactSupport Φ)
    (hi : Integrable (fun y : ι → ℝ => ∫ x : ι → ℝ,
      Φ x * Complex.exp (2 * Real.pi * Complex.I * (((-1 : ℝ) * (x ⬝ᵥ y) : ℝ) : ℝ))) volume)
    (z : ι → ℝ) :
    ∫ y : ι → ℝ, (∫ x : ι → ℝ,
        Φ x * Complex.exp (2 * Real.pi * Complex.I * (((-1 : ℝ) * (x ⬝ᵥ y) : ℝ) : ℝ))) *
      Complex.exp (2 * Real.pi * Complex.I * (((-1 : ℝ) * (y ⬝ᵥ z) : ℝ) : ℝ)) = Φ (-z) := by
  have mp := PiLp.volume_preserving_toLp ι
  have emb : MeasurableEmbedding (WithLp.toLp 2 : (ι → ℝ) → EuclideanSpace ℝ ι) :=
    (MeasurableEquiv.toLp 2 (ι → ℝ)).measurableEmbedding
  have hin : ∀ x y : ι → ℝ, inner ℝ (WithLp.toLp 2 x : EuclideanSpace ℝ ι) (WithLp.toLp 2 y)
      = x ⬝ᵥ y := by
    intro x y
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp [dotProduct_comm]
  set Ψ : EuclideanSpace ℝ ι → ℂ := fun u => Φ u.ofLp with hΨ
  have hΨc : Continuous Ψ := hc.comp (PiLp.continuous_ofLp 2 _)
  have hΨi : Integrable Ψ volume :=
    (mp.integrable_comp_emb emb).1 (hc.integrable_of_hasCompactSupport hs)
  have hF : ∀ y : ι → ℝ, FourierTransform.fourier Ψ (WithLp.toLp 2 y) = ∫ x : ι → ℝ,
      Φ x * Complex.exp (2 * Real.pi * Complex.I * (((-1 : ℝ) * (x ⬝ᵥ y) : ℝ) : ℝ)) := by
    intro y
    rw [Real.fourier_eq, ← mp.integral_comp emb]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hin, fourierChar_smul, hΨ]
    simp
  have hFi : Integrable (FourierTransform.fourier Ψ) volume := by
    refine (mp.integrable_comp_emb emb).1 ?_
    refine hi.congr (Filter.Eventually.of_forall fun y => ?_)
    exact (hF y).symm
  have hinv := congrFun (hΨc.fourierInv_fourier_eq hΨi hFi) (WithLp.toLp 2 (-z))
  rw [Real.fourierInv_eq, ← mp.integral_comp emb] at hinv
  have hval : Ψ (WithLp.toLp 2 (-z)) = Φ (-z) := rfl
  rw [← hval, ← hinv]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [hin, fourierChar_smul, hF]
  simp

end GlobalTheory.CompanionTheory.SW.RealFourier

namespace GlobalTheory.CompanionTheory.SW

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem selfDual_real_coord : ∀ (ι : Type) [Fintype ι] (ε : ℝ), ε = 1 ∨ ε = -1 →
    SelfDual (volume : Measure (ι → ℝ))
      (fun x y => Complex.exp (2 * Real.pi * Complex.I * (ε * (x ⬝ᵥ y) : ℝ))) := by
  intro ι _ ε hε
  refine ⟨inferInstance, fun Φ hc hs hi z => ?_⟩
  rcases hε with rfl | rfl
  ·
    have hG : ∀ y : ι → ℝ, (∫ x : ι → ℝ,
        Φ x * Complex.exp (2 * Real.pi * Complex.I * (((1 : ℝ) * (x ⬝ᵥ y) : ℝ) : ℝ))) =
        ∫ x : ι → ℝ, (fun u => Φ (-u)) x *
          Complex.exp (2 * Real.pi * Complex.I * (((-1 : ℝ) * (x ⬝ᵥ y) : ℝ) : ℝ)) := by
      intro y
      rw [← integral_neg_eq_self (fun x : ι → ℝ =>
        Φ x * Complex.exp (2 * Real.pi * Complex.I * (((1 : ℝ) * (x ⬝ᵥ y) : ℝ) : ℝ))) volume]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp
    have hc' : Continuous fun u : ι → ℝ => Φ (-u) := hc.comp continuous_neg
    have hs' : HasCompactSupport fun u : ι → ℝ => Φ (-u) :=
      hs.comp_homeomorph (Homeomorph.neg (ι → ℝ))
    have hi' : Integrable (fun y : ι → ℝ => ∫ x : ι → ℝ, (fun u => Φ (-u)) x *
        Complex.exp (2 * Real.pi * Complex.I * (((-1 : ℝ) * (x ⬝ᵥ y) : ℝ) : ℝ))) volume :=
      hi.congr (Filter.Eventually.of_forall hG)
    have key := RealFourier.inversion_neg ι (fun u => Φ (-u)) hc' hs' hi' (-z)
    simp only [neg_neg] at key
    rw [← key]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [hG y]
    simp
  · exact RealFourier.inversion_neg ι Φ hc hs hi z

end GlobalTheory.CompanionTheory.SW
end
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ArchimedeanSelfdualMeasureDiscriminantScaled

section

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.SW

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem real_coord_eq_re {F : Type} [Field F] [NumberField F]
    (ρ : InfinitePlace F → (F →+* ℝ)) (e : Ainf F ≃+* (InfinitePlace F → ℝ))
    (hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) (hh : IsHomeomorph e)
    (he : ∀ x w, e (algebraMap F (Ainf F) x) w = ρ w x) (x : Ainf F) (w : InfinitePlace F) :
    e x w = (InfinitePlace.Completion.extensionEmbedding w (x w)).re := by
  have hf : Continuous fun y : Ainf F => e y w := (continuous_apply w).comp hh.continuous
  have hg : Continuous fun y : Ainf F =>
      (InfinitePlace.Completion.extensionEmbedding w (y w)).re :=
    Complex.continuous_re.comp
      ((InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp (continuous_apply w))
  have key := (InfiniteAdeleRing.denseRange_algebraMap (K := F)).equalizer hf hg (by
    funext k
    simp only [Function.comp_apply]
    rw [he, GroundTheory.Global.extensionEmbedding_algebraMap_apply, ← hρ, Complex.ofReal_re])
  exact congrFun key x

theorem psiInf_std_mul {F : Type} [Field F] [NumberField F] (hF : IsTotallyReal F)
    (ρ : InfinitePlace F → (F →+* ℝ)) (e : Ainf F ≃+* (InfinitePlace F → ℝ))
    (hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) (hh : IsHomeomorph e)
    (he : ∀ x w, e (algebraMap F (Ainf F) x) w = ρ w x) (s t : Ainf F) :
    psiInf F (Circle.coeHom.compAddChar (GroundTheory.Global.adelicChar F)) (s * t) =
      Complex.exp (2 * Real.pi * Complex.I * (((-1 : ℝ) * (e s ⬝ᵥ e t) : ℝ) : ℂ)) := by
  have htr : GroundTheory.Global.infiniteTrace F (s * t) = e s ⬝ᵥ e t := by
    rw [GroundTheory.Global.infiniteTrace_apply]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [(hF.isReal w).mult_eq_one, Nat.cast_one, one_mul,
      ← real_coord_eq_re ρ e hρ hh he, map_mul, Pi.mul_apply]
  have h1 : GroundTheory.Global.adelicChar F (pairA F (s * t) 0) =
      Real.fourierChar (-GroundTheory.Global.infiniteTrace F (s * t)) :=
    GroundTheory.Global.adelicChar_infinite (K := F) (s * t)
  show ((GroundTheory.Global.adelicChar F (pairA F (s * t) 0) : Circle) : ℂ) = _
  rw [h1, htr, Real.fourierChar_apply]
  congr 1
  push_cast
  ring

theorem selfDual_psiInf_std (F : Type) [Field F] [NumberField F] (hF : IsTotallyReal F)
    (laminf : Measure (Ainf F)) (hl : IsStdInf laminf) :
    SelfDual (Real.toNNReal (Real.sqrt |(discr F : ℝ)|) • laminf)
      (fun s t => psiInf F (Circle.coeHom.compAddChar (GroundTheory.Global.adelicChar F)) (s * t)) := by
  obtain ⟨ρ, e, hρ, hh, he, -, hm⟩ := real_iso F hF
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  let e' : Ainf F ≃ₜ+ (InfinitePlace F → ℝ) :=
    { e.toAddEquiv with
      continuous_toFun := hh.continuous
      continuous_invFun :=
        (e.toEquiv.toHomeomorphOfContinuousOpen hh.continuous hh.isOpenMap).symm.continuous }
  set c : ℝ := Real.sqrt |(discr F : ℝ)| with hc
  have hc0 : 0 < c := by
    have : (discr F : ℝ) ≠ 0 := by exact_mod_cast discr_ne_zero F
    exact Real.sqrt_pos.mpr (abs_pos.mpr this)
  have hmap : (Real.toNNReal c • laminf).map e' = (volume : Measure (InfinitePlace F → ℝ)) := by
    have h1 : laminf.map e' = ENNReal.ofReal c⁻¹ • (volume : Measure (InfinitePlace F → ℝ)) := hm laminf hl
    have h2 : ((Real.toNNReal c : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal c⁻¹ = 1 := by
      rw [ENNReal.coe_nnreal_eq, Real.coe_toNNReal _ hc0.le,
        ← ENNReal.ofReal_mul hc0.le, mul_inv_cancel₀ hc0.ne', ENNReal.ofReal_one]
    rw [Measure.map_smul, h1, ENNReal.smul_def, smul_smul, h2, one_smul]
    exact e'.continuous.measurable.aemeasurable
  have hsd := selfDual_real_coord (InfinitePlace F) (-1) (Or.inr rfl)
  rw [← hmap] at hsd
  have := (selfDual_transport (Ainf F) (InfinitePlace F → ℝ) e' (Real.toNNReal c • laminf)
    (fun x y => Complex.exp (2 * Real.pi * Complex.I * (((-1 : ℝ) * (x ⬝ᵥ y) : ℝ) : ℂ)))).mpr hsd
  convert this using 3 with s t
  exact psiInf_std_mul hF ρ e hρ hh he s t

end GlobalTheory.CompanionTheory.SW
end
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ArchimedeanSelfdualMeasureDiscriminantScaledStatement

section

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.archimedean_selfdual_measure_discriminant_scaled : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ laminf : Measure (Ainf F), IsStdInf laminf → SelfDual (Real.toNNReal (Real.sqrt |(discr F : ℝ)|) • laminf) (fun s t => psiInf F (Circle.coeHom.compAddChar (GroundTheory.Global.adelicChar F)) (s * t)) := by
  first | exact @GlobalTheory.CompanionTheory.SW.selfDual_psiInf_std | exact GlobalTheory.CompanionTheory.SW.selfDual_psiInf_std | (intros; apply GlobalTheory.CompanionTheory.SW.selfDual_psiInf_std <;> assumption)
end
end
