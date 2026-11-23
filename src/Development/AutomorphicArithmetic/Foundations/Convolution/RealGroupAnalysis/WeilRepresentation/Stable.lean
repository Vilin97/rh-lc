module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.Smooth
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.OpsEx
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.DLFock
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.FstFinGL
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Transl
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.FockSt
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
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.LieL
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.LieSplit
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.LieZ
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.NormDetKinf

-- Source module: Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.FinLift

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Ff.finLift :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), FinLift W M π := by
  intro F E _ _ _ _ _ _ _ D W M π f hf φ hφ k
  obtain ⟨κ, -, hκ⟩ := finTr F E D
  refine ⟨TR.finRep F 2 (κ k) f, π.stable (.fin (κ k)) f hf, W.L (finGL E 2 k) φ,
    (fockSt F E D W).fin k φ hφ, fun h => ?_⟩
  have e : (fun x => f.1 (x * dM (nu F (finGL E 2 k)))) = (TR.finRep F 2 (κ k) f).1 := by
    funext x
    rw [hκ k]
    rfl
  rw [transl F E D W M f.1 φ h (finGL E 2 k), e]
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.Stable

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.stable :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), St.Stable W M π := by
  intro F E _ _ _ _ _ _ _ D W M π o Φ hΦ
  refine (Submodule.span_le.2 ?_ : span W M π ≤ (span W M π).comap (act o)) hΦ
  rintro Ψ ⟨f, hf, φ, hφ, e⟩
  cases o with
  | fin k =>
    obtain ⟨f', hf', φ', hφ', h⟩ := finLift F E D W M π f hf φ hφ k
    exact Submodule.subset_span ⟨f', hf', φ', hφ', funext fun g => (congrFun e _).trans (h g)⟩
  | cpt k => exact (kFin F E D W M π f hf φ hφ Ψ e).1 k
  | lie X =>
    obtain ⟨O⟩ := UpperTheory.ConvolutionTheory.R2.Fo.opsEx F
    obtain ⟨Y, s, hY, rfl, -⟩ := lieSplit X
    change lie E 2 (Y + zE s) Ψ ∈ span W M π
    rw [map_add (f := _), LinearMap.add_apply]
    exact add_mem (Submodule.subset_span ⟨f, hf, _, dLFock F E D O Y φ hφ, lieL F E D O W M π f hf φ hφ Y hY Ψ e⟩)
      (Submodule.subset_span ⟨_, π.stable (.lie _) f hf, φ, hφ, lieZ F E D W M π f hf φ hφ s Ψ e⟩)
end
end
