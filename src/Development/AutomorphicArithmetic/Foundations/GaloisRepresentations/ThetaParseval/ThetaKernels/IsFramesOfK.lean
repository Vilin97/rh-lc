module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitDict
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaPlaces.RelReal
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
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
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.WhitKOfSteps
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaPlaces.NormInvMulSelf
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilThetadictRelReal

section

@[expose] public section



section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.ThetaDictR
open PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KWhit
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem isCharAF_of_good_k (B : Base F E) (hB : _root_.UpperTheory.TP.W.GoodK σ B) : HeckeCharacterZeroLocus.SiegelWeilU.IsCharAF F B.ψ :=
  GlobalTheory.StdCharFromIsStd.isCharAF hB.std
theorem frW_det_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) {η : E} (hη : η ≠ 0) (w : InfinitePlace F) :
    IsUnit (cW d.B η w • (R.fr w).1.map star).det := by
  rw [isUnit_iff_ne_zero, Matrix.det_smul]
  refine mul_ne_zero (pow_ne_zero _ (cW_ne d.B hη w)) ?_
  have hu : IsUnit (R.fr w).1.det := (Matrix.isUnit_iff_isUnit_det _).1 (R.fr w).isUnit
  have e : ((R.fr w).1.map star).det = star (R.fr w).1.det := by
    rw [← Matrix.det_conjTranspose, ← Matrix.det_transpose ((R.fr w).1)ᴴ]; rfl
  rw [e, star_ne_zero]
  exact hu.ne_zero
def frW_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (η : E) (hη : η ≠ 0) (w : InfinitePlace F) : GL (Fin d.m) ℂ :=
  Matrix.nonsingInvUnit (cW d.B η w • (R.fr w).1.map star) (_root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.frW_det_k R hη w)
theorem frW_frc_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (η : E) (hη : η ≠ 0) (w : InfinitePlace F) :
    (_root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.frW_k R η hη w).1 = cW d.B η w • (R.fr w).1.map star := rfl
theorem gW_det_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (u : GL (Fin d.n) (AE F E)) {η : E} (hη : η ≠ 0) (w : InfinitePlace F) :
    IsUnit (cW d.B η w • (((d.cw w u.1)ᵀ).map star)⁻¹).det := by
  rw [isUnit_iff_ne_zero, Matrix.det_smul]
  refine mul_ne_zero (pow_ne_zero _ (cW_ne d.B hη w)) ?_
  have hu : IsUnit u.1.det := (Matrix.isUnit_iff_isUnit_det _).1 u.isUnit
  have h1 : (d.cw w u.1).det = piInf (d.B.emb w) u.1.det := by
    unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.cw; rw [RingHom.map_det]; rfl
  have h2 : (((d.cw w u.1)ᵀ).map star).det = star (d.cw w u.1).det := by
    rw [← Matrix.det_conjTranspose]; rfl
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv', h2, h1]
  exact inv_ne_zero (star_ne_zero.2 (hu.map (piInf (d.B.emb w))).ne_zero)
def gW_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (u : GL (Fin d.n) (AE F E)) (η : E) (hη : η ≠ 0) (w : InfinitePlace F) : GL (Fin d.n) ℂ :=
  Matrix.nonsingInvUnit (cW d.B η w • (((d.cw w u.1)ᵀ).map star)⁻¹) (_root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.gW_det_k d u hη w)
theorem gW_gc_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (u : GL (Fin d.n) (AE F E)) (η : E) (hη : η ≠ 0) (w : InfinitePlace F) :
    (_root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.gW_k d u η hη w).1 * ((d.cw w u.1)ᵀ).map star = cW d.B η w • 1 := by
  have hu : IsUnit u.1.det := (Matrix.isUnit_iff_isUnit_det _).1 u.isUnit
  have hN : IsUnit (((d.cw w u.1)ᵀ).map star).det := by
    have h1 : (d.cw w u.1).det = piInf (d.B.emb w) u.1.det := by
      unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.cw; rw [RingHom.map_det]; rfl
    have h2 : (((d.cw w u.1)ᵀ).map star).det = star (d.cw w u.1).det := by
      rw [← Matrix.det_conjTranspose]; rfl
    rw [h2, h1, isUnit_iff_ne_zero, star_ne_zero]
    exact (hu.map (piInf (d.B.emb w))).ne_zero
  change (cW d.B η w • (((d.cw w u.1)ᵀ).map star)⁻¹) * ((d.cw w u.1)ᵀ).map star = cW d.B η w • 1
  rw [Matrix.smul_mul, Matrix.nonsing_inv_mul _ hN]
def εsW_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (η : E) (w : InfinitePlace F) (_ : Fin d.m) : Bool :=
  decide (0 < (((d.B.emb w).1 η / R.ζ) * ((R.sg w : ℤ) : ℂ)).re)
end PositivityTheory.SiegelWeilFormula.ThetaDictR
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.IsFramesOfK

section

@[expose] public section



section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.ThetaDictR
open PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KWhit
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem isFrames_of'_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (η : E) (hη : η ≠ 0) (hcm : HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ)
    (herm : ∀ i j, σ (η * d.A.J j i) = η * d.A.J i j) (hηζ : (σ η = η ∧ R.ζ = 1) ∨ (σ η = -η ∧ R.ζ = Complex.I))
    (θ : InfinitePlace F → (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F ⊗[F] E →+* ℂ))
    (th : ∀ w y, θ w (Algebra.TensorProduct.map (HeckeCharacterZeroLocus.SiegelWeilU.fstA F) (AlgHom.id F E) y) = star (piInf (d.B.emb w) y))
    (fr : InfinitePlace F → GL (Fin d.m) ℂ)
    (frc : ∀ w, (fr w).1 = ((‖(d.B.emb w).1 η‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • (R.fr w).1.map star) :
    Gen.IsFrames (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) θ (_root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.εsW_k R η) fr := by
  intro w
  set τ := (d.B.emb w).1 with hτ
  set a := τ η with ha
  set c := cW d.B η w with hc
  have hθ1 : ∀ x : E, θ w ((1 : HeckeCharacterZeroLocus.SiegelWeilU.Ainf F) ⊗ₜ[F] x) = star (τ x) := fun x => by
    have := th w ((1 : AF F) ⊗ₜ[F] x)
    rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply, piInf_one] at this
    exact this
  have hmat : (HeckeCharacterZeroLocus.SiegelWeilU.JR (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F) (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η)).map (θ w) = a • d.A.J.map τ := by
    ext i j
    simp only [Matrix.map_apply, HeckeCharacterZeroLocus.SiegelWeilU.JR, _root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul,
      HeckeCharacterZeroLocus.SiegelWeilU.inclR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply, hθ1]
    rw [← hcm.2.2.2, herm, map_mul]
  have hcs : star c = c := Complex.conj_ofReal _
  have hfrH : ((fr w).1)ᴴ = c • ((R.fr w).1)ᵀ := by
    rw [frc w, Matrix.conjTranspose_smul]
    change star c • _ = _
    rw [hcs]
    congr 1
    ext i j
    simp [Matrix.conjTranspose_apply]
  have hζ : R.ζ ≠ 0 := by
    rcases hηζ with ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h] <;> simp
  have hfr' : (R.fr w).1ᵀ * d.A.J.map τ * (R.fr w).1.map star = (R.ζ⁻¹ * ((R.sg w : ℤ) : ℂ)) • 1 := by
    have := congrArg (fun M => R.ζ⁻¹ • M) (R.hfr w)
    simp only [smul_smul, inv_mul_cancel₀ hζ, one_smul] at this
    rw [this]
  have ha0 : a ≠ 0 := (map_ne_zero τ).2 hη
  have hapos : 0 < ‖a‖ := norm_pos_iff.2 ha0
  have hcc : c * c = ((‖a‖⁻¹ : ℝ) : ℂ) := by
    rw [hc, cW, ← Complex.ofReal_mul, ← Real.rpow_add hapos]
    norm_num [Real.rpow_neg_one]
  set z := a / R.ζ * ((R.sg w : ℤ) : ℂ) with hz
  have hsg : ‖((R.sg w : ℤ) : ℂ)‖ = 1 := by
    rcases Int.units_eq_one_or (R.sg w) with h | h <;> rw [h] <;> simp
  have hsg0 : ((R.sg w : ℤ) : ℂ) ≠ 0 := by
    intro h; rw [h] at hsg; simp at hsg
  have hsgim : (((R.sg w : ℤ) : ℂ)).im = 0 := by simp
  have hz0 : z ≠ 0 := mul_ne_zero (div_ne_zero ha0 hζ) hsg0
  have hzn : ‖z‖ = ‖a‖ := by
    rw [hz, norm_mul, norm_div, hsg]
    rcases hηζ with ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h] <;> simp
  have hzim : z.im = 0 := by
    have hconj := hcm.2.2.2 τ η
    rcases hηζ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1] at hconj
      have him : a.im = 0 := by
        have := congrArg Complex.im hconj
        change a.im = (star a).im at this
        simp at this; linarith
      rw [hz, h2, div_one, Complex.mul_im, him, hsgim]; ring
    · rw [h1, map_neg] at hconj
      have hre : a.re = 0 := by
        have := congrArg Complex.re hconj
        change (-a).re = (star a).re at this
        simp at this; linarith
      rw [hz, h2, Complex.div_I, Complex.mul_im, hsgim]
      simp [Complex.mul_im, hre]
  have key : (fr w).1ᴴ * (HeckeCharacterZeroLocus.SiegelWeilU.JR (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F) (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η)).map (θ w) * (fr w).1 =
      (((‖z‖⁻¹ : ℝ) : ℂ) * z) • (1 : Matrix (Fin d.m) (Fin d.m) ℂ) := by
    rw [hfrH, hmat, frc w, show ((‖(d.B.emb w).1 η‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) = c from rfl]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [hfr', smul_smul, hzn, ← hcc, hz]
    congr 1
    field_simp
  change (fr w).1ᴴ * (HeckeCharacterZeroLocus.SiegelWeilU.JR (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F) (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η)).map (θ w) * (fr w).1 = _
  rw [key, norm_inv_mul_self hz0 hzim]
  ext i j
  by_cases hij : i = j
  · subst hij; simp [_root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.εsW_k, sgn, hz, ha, hτ]
  · simp [hij]
end PositivityTheory.SiegelWeilFormula.ThetaDictR
end
end
end
end
