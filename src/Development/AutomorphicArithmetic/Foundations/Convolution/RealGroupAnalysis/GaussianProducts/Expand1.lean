module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.AdelicWeightFourNonneg
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.BdInv
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.HatMeas
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ZetaFin
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.CuspZero
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.KkCpt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.HatSt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.TopoAF
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
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.CoordinateEmbedNormZero
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.HatMeas
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.LamRight
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.LCen
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.ContinuousAdelicGL2OfContinuousEntries
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.ContinuousQuaternaryQuadraticForm
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.ImportsAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.CuspZero
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.Kern
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.UnfoldSum
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.One

-- Source module: Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.AbsFin1

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

theorem UpperTheory.ConvolutionTheory.R2.G.absFin1 :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), ∀ f ∈ π.V, ∀ φ ∈ Fock D.δ, ∀ h : GL (Fin 2) (A E), ((nu F h : (A F)ˣ) : A F).1 = 1 → ∑' ξ, abelian₂ M (ux W f.1 φ h ξ) ≠ ⊤ := by
  intro F E _ _ _ _ _ _ _ D W M π f hf φ hφ h hnu
  haveI := M.prob
  haveI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  obtain ⟨N, hN⟩ := UpperTheory.ConvolutionTheory.R2.G.zetaFin F
  obtain ⟨B', L, hB'0, hB'⟩ := UpperTheory.ConvolutionTheory.R2.G.majL F E D W φ hφ h hnu N
  have hC : IsCompact ((fun k : G1 F => gl k * dM (nu F h)) '' KK F) :=
    (UpperTheory.ConvolutionTheory.R2.M.kkCpt F).2.image (UpperTheory.ConvolutionTheory.R2.M.continuous_gl.mul continuous_const)
  obtain ⟨B, hB0, hB⟩ := UpperTheory.ConvolutionTheory.R2.G.bdInv F π f hf _ hC
  have hLf := (UpperTheory.ConvolutionTheory.R2.Pp.cuspZero F π f hf).1
  let w : IdeleGroup F → (Fin 2 → F) → ℝ := fun a ξ =>
    wt4 L N ![0, ((a⁻¹ : (A F)ˣ) : A F), (a : A F) * rt (ξ 0), (a : A F) * rt (ξ 1)]
  have hw : ∀ ξ, Continuous fun a : IdeleGroup F => w a ξ := by
    intro ξ
    have h1 : Continuous (wt4 L N : V4 F → ℝ) :=
      continuous_finsetProd _ fun i _ =>
        (GlobalTheory.CompanionTheory.EpConvB.continuous_adeleWeight L N).comp (continuous_apply i)
    refine h1.comp (continuous_pi fun i => ?_)
    fin_cases i
    · exact continuous_const
    · exact Units.continuous_coe_inv
    · exact Units.continuous_val.mul continuous_const
    · exact Units.continuous_val.mul continuous_const
  have pw : ∀ (a : IdeleGroup F), ∀ k ∈ KK F, ∀ (b : A F) (ξ : Fin 2 → F),
      ‖ux W f.1 φ h ξ (nU b * (mD a * k))‖ ≤ B * B' * w a ξ := by
    intro a k hk b ξ
    rw [(UpperTheory.ConvolutionTheory.R2.G.uxAv F E D W f.1 hLf φ h ξ).2.2 b (mD a * k)]
    have hgl : ∀ x y : G1 F, gl (x * y) = gl x * gl y := fun x y => map_mul _ x y
    have e1 : gl (nU b * (mD a * k)) * dM (nu F h) = gl (nU b * mD a) * (gl k * dM (nu F h)) := by
      rw [← mul_assoc, hgl (nU b * mD a) k, mul_assoc]
    have h1 := (hB b a _ ⟨k, hk, rfl⟩).1
    rw [← e1] at h1
    have e2 : hat (W.Om (mD a * k) (W.L h φ)).1 (pt ξ) = ((W.η.1 a : ℂˣ) : ℂ) * ((ab a : ℝ) : ℂ) *
        hat (W.Om k (W.L h φ)).1 ![0, ((a⁻¹ : (A F)ˣ) : A F), (a : A F) * rt (ξ 0), (a : A F) * rt (ξ 1)] := by
      rw [map_mul, Module.End.mul_apply, (UpperTheory.ConvolutionTheory.R2.hatSt F E D W).m]
      simp [pt]
    have hη : ‖((W.η.1 a : ℂˣ) : ℂ)‖ = 1 := by
      have h2 : ((W.η.1 a : ℂˣ) : ℂ) ^ 2 = 1 := by
        have := congrArg (fun u : ℂˣ => (u : ℂ)) (W.η_sq a)
        simpa using this
      have h3 : ‖((W.η.1 a : ℂˣ) : ℂ)‖ ^ 2 = 1 := by rw [← norm_pow, h2, norm_one]
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h3
    have hab : 0 < ab a := UpperTheory.ConvolutionTheory.R2.M.ab_pos a
    have h4 : ‖hat (W.Om (mD a * k) (W.L h φ)).1 (pt ξ)‖ ≤ ab a * (B' * w a ξ) := by
      rw [e2, norm_mul, norm_mul, hη, one_mul, Complex.norm_real, Real.norm_of_nonneg hab.le]
      exact mul_le_mul_of_nonneg_left (hB' k hk _) hab.le
    calc _ ≤ (B * (ab a)⁻¹) * (ab a * (B' * w a ξ)) :=
          mul_le_mul h1 h4 (norm_nonneg _) (mul_nonneg hB0 (inv_pos.2 hab).le)
      _ = B * B' * w a ξ := by field_simp
  have hae : ∀ᵐ p ∂M.ν, p.2 ∈ KK F := by
    have h0 : ∀ᵐ k ∂M.κ, k ∈ KK F := by
      rw [ae_iff]
      exact M.supp
    exact Measure.quasiMeasurePreserving_snd.ae h0
  let G : (Fin 2 → F) → IdeleGroup F → ℝ≥0∞ := fun ξ a =>
    _root_.UpperTheory.ConvolutionTheory.R2.M.wt a * ENNReal.ofReal (w a ξ)
  have hG : ∀ ξ, Measurable (G ξ) := fun ξ =>
    _root_.UpperTheory.ConvolutionTheory.R2.M.measurable_wt.mul (hw ξ).measurable.ennreal_ofReal
  have key : ∀ ξ, abelian₂ M (ux W f.1 φ h ξ) ≤ ENNReal.ofReal (B * B') * ∫⁻ a, G ξ a ∂(ideleMeasure F) := by
    intro ξ
    have hm : Measurable fun p : IdeleGroup F × G1 F => G ξ p.1 := (hG ξ).comp measurable_fst
    have e : ∫⁻ p, G ξ p.1 ∂M.ν = ∫⁻ a, G ξ a ∂(ideleMeasure F) := by
      rw [Meas.ν, lintegral_prod _ hm.aemeasurable]
      simp
    rw [← e, ← lintegral_const_mul _ hm, abelian₂, _root_.UpperTheory.ConvolutionTheory.R2.M.J0]
    refine lintegral_mono_ae (hae.mono fun p hp => ?_)
    have hb : ∫⁻ b in fundamentalSet F, ‖ux W f.1 φ h ξ (nU b * (mD p.1 * p.2))‖ₑ ∂(adeleMeasure F) ≤
        ENNReal.ofReal (B * B') * ENNReal.ofReal (w p.1 ξ) := by
      have hw0 : 0 ≤ B * B' := mul_nonneg hB0 hB'0
      calc _ ≤ ∫⁻ _ in fundamentalSet F, ENNReal.ofReal (B * B' * w p.1 ξ) ∂(adeleMeasure F) := by
            refine lintegral_mono fun b => ?_
            rw [← ofReal_norm_eq_enorm]
            exact ENNReal.ofReal_le_ofReal (pw p.1 p.2 hp b ξ)
        _ = _ := by
            rw [setLIntegral_const, adeleMeasure_fundamentalSet, mul_one, ENNReal.ofReal_mul hw0]
    calc _ ≤ _root_.UpperTheory.ConvolutionTheory.R2.M.wt p.1 * (ENNReal.ofReal (B * B') * ENNReal.ofReal (w p.1 ξ)) := by
          gcongr
      _ = _ := by
          simp only [G]
          ring
  have hsum : ∑' ξ, ∫⁻ a, G ξ a ∂(ideleMeasure F) ≠ ⊤ := by
    rw [← lintegral_tsum fun ξ => (hG ξ).aemeasurable]
    have e : ∀ a, ∑' ξ, G ξ a = _root_.UpperTheory.ConvolutionTheory.R2.M.wt a * ∑' ξ, ENNReal.ofReal (w a ξ) :=
      fun a => ENNReal.tsum_mul_left
    simp_rw [e]
    exact hN L
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum key)
  rw [ENNReal.tsum_mul_left]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hsum
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.UxCen

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

theorem UpperTheory.ConvolutionTheory.R2.G.uxCen :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (π : TR.CuspSub F 2) (s : (A F)ˣ) (h : GL (Fin 2) (A E)), ∃ (h₁ : GL (Fin 2) (A E)) (c : ℂ), nu F h = s ^ 4 * nu F h₁ ∧
    ∀ f ∈ π.V, ∀ φ ξ g, ux W f.1 φ h ξ g = c * ux W f.1 φ h₁ ξ (g * mD (s ^ 2)⁻¹) := by
  intro F E _ _ _ _ _ _ _ D W π s h
  obtain ⟨ω, -, hω⟩ := UpperTheory.ConvolutionTheory.R2.cen F π
  obtain ⟨z, hz⟩ : ∃ z : (A E)ˣ, ideleNorm F E z = s ^ 2 := ⟨ideleEmbedding F E s, D.ideleNorm_emb s⟩
  obtain ⟨hL, hnu⟩ := UpperTheory.ConvolutionTheory.R2.Ff.lCen F E D W z
  rw [hz] at hL hnu
  obtain ⟨h₁, rfl⟩ : ∃ h₁, h = Matrix.GeneralLinearGroup.scalar (Fin 2) z * h₁ :=
    ⟨_, (mul_inv_cancel_left _ _).symm⟩
  have hnh : nu F (Matrix.GeneralLinearGroup.scalar (Fin 2) z * h₁) = s ^ 4 * nu F h₁ := by
    rw [nu_mul, hnu, ← pow_mul]
  refine ⟨h₁, ((ω (s ^ 2) : ℂˣ) : ℂ), hnh, fun f hf φ ξ g => ?_⟩
  have e0 : dM (s ^ 4) = gl (mD (s ^ 2)⁻¹) * Matrix.GeneralLinearGroup.scalar (Fin 2) (s ^ 2) := by
    rw [← gl_mD_mul_dM_sq (s ^ 2), mD_inv, gl_inv, inv_mul_cancel_left, ← pow_mul]
  have e1 : gl g * dM (s ^ 4 * nu F h₁) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (s ^ 2) * (gl (g * mD (s ^ 2)⁻¹) * dM (nu F h₁)) := by
    rw [dM_mul, e0, mul_assoc (gl _) _ (dM _), UpperTheory.ConvolutionTheory.R2.scalar_comm (s ^ 2) (dM _),
      UpperTheory.ConvolutionTheory.R2.scalar_comm (s ^ 2) (gl _ * dM _), gl_mul]
    simp only [mul_assoc]
  have e2 : W.Om g (W.L (Matrix.GeneralLinearGroup.scalar (Fin 2) z * h₁) φ) =
      W.Om (g * mD (s ^ 2)⁻¹) (W.L h₁ φ) := by
    rw [map_mul, hL, map_mul, Module.End.mul_apply, Module.End.mul_apply]
  rw [ux, ux, hnh, e1, hω f hf, e2, mul_assoc]
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.AbsFin

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

theorem UpperTheory.ConvolutionTheory.R2.G.absFin :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), ∀ f ∈ π.V, ∀ φ ∈ Fock D.δ, ∀ h : GL (Fin 2) (A E), ∑' ξ, abelian₂ M (ux W f.1 φ h ξ) ≠ ⊤ := by
  intro F E _ _ _ _ _ _ _ D W M π f hf φ hφ h
  obtain ⟨s, hs⟩ := UpperTheory.ConvolutionTheory.R2.G.nuPos F E D h
  obtain ⟨h₁, c, hnu, hux⟩ := UpperTheory.ConvolutionTheory.R2.G.uxCen F E D W π s h
  have hnu₁ : ((nu F h₁ : (A F)ˣ) : A F).1 = 1 := by
    have e : nu F h * (s ^ 4)⁻¹ = nu F h₁ := by
      rw [hnu, mul_comm, inv_mul_cancel_left]
    rw [← e]
    exact hs
  have hLf : Pp.Lf f.1 := (Pp.cuspZero F π f hf).1
  have hterm : ∀ ξ, abelian₂ M (ux W f.1 φ h ξ) = ‖c‖ₑ * abelian₂ M (ux W f.1 φ h₁ ξ) := by
    intro ξ
    have e : ux W f.1 φ h ξ = fun g => c * ux W f.1 φ h₁ ξ (g * mD (s ^ 2)⁻¹) :=
      funext fun g => hux f hf φ ξ g
    rw [e]
    exact UpperTheory.ConvolutionTheory.R2.G.lamRight F M _ (UpperTheory.ConvolutionTheory.R2.G.uxAv F E D W f.1 hLf φ h₁ ξ).1 c _
  simp only [hterm]
  rw [ENNReal.tsum_mul_left]
  exact ENNReal.mul_ne_top enorm_ne_top (UpperTheory.ConvolutionTheory.R2.G.absFin1 F E D W M π f hf φ hφ h₁ hnu₁)
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.Expand1

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

theorem UpperTheory.ConvolutionTheory.R2.G.expand1 :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), ∀ f ∈ π.V, ∀ φ ∈ Fock D.δ, ∀ h, Summable (fun ξ => ‖Wx W M f.1 φ h ξ‖) ∧
    lift W M f.1 φ h = T0 W M f.1 φ h + ∑' ξ, Wx W M f.1 φ h ξ := by
  intro F E _ _ _ _ _ _ _ D W M π f hf φ hφ h
  haveI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  have hL := (UpperTheory.ConvolutionTheory.R2.Pp.cuspZero F π f hf).1
  obtain ⟨σ, hσ⟩ := exists_rowSec (F := F)
  have hN := fun ξ => UpperTheory.ConvolutionTheory.R2.G.uxAv F E D W f.1 hL φ h ξ
  obtain ⟨hs, hi, he⟩ := UpperTheory.ConvolutionTheory.R2.G.unfoldSum F M σ hσ (Fin 2 → F) (ux W f.1 φ h)
    (fun ξ => (hN ξ).1) (UpperTheory.ConvolutionTheory.R2.G.absFin F E D W M π f hf φ hφ h)
  have hav : ∀ ξ, M.I0 (av (ux W f.1 φ h ξ)) = Wx W M f.1 φ h ξ := fun ξ => by
    rw [(hN ξ).2.1]; rfl
  simp only [hav] at hs he
  obtain ⟨-, c2, -⟩ := UpperTheory.ConvolutionTheory.R2.conv F E D W M π f hf φ hφ h
  have hk : ∀ g : G1 F, f.1 (gl g * dM (nu F h)) * Th (W.Om g (W.L h φ)).1 =
      f.1 (gl g * dM (nu F h)) * ThRow 0 0 (W.Om g (W.L h φ)).1 +
        ∑' r, ∑' ξ, ux W f.1 φ h ξ (ratS F (σ r) * g) := by
    intro g
    rw [UpperTheory.ConvolutionTheory.R2.G.kern F E D W σ hσ (W.Om g (W.L h φ)), mul_add]
    congr 1
    rw [← tsum_mul_left]
    refine tsum_congr fun r => ?_
    rw [← tsum_mul_left]
    refine tsum_congr fun ξ => ?_
    have e1 : f.1 (gl (ratS F (σ r) * g) * dM (nu F h)) = f.1 (gl g * dM (nu F h)) := by
      rw [gl_mul, gl_ratS, mul_assoc, hL.2]
    have e2 : W.Om (ratS F (σ r) * g) (W.L h φ) = W.Om (ratS F (σ r)) (W.Om g (W.L h φ)) := by
      rw [map_mul]; rfl
    simp only [ux]
    rw [e1, e2]
  refine ⟨hs, ?_⟩
  have hlift : lift W M f.1 φ h = ∫ g in M.D, (f.1 (gl g * dM (nu F h)) * ThRow 0 0 (W.Om g (W.L h φ)).1 +
      ∑' r, ∑' ξ, ux W f.1 φ h ξ (ratS F (σ r) * g)) ∂M.μ :=
    integral_congr_ae (Eventually.of_forall hk)
  rw [hlift, integral_add c2 hi, he]
  rfl
end
end
