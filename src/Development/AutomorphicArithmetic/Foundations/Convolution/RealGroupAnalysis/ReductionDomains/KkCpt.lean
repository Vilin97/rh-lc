module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.EntryMul
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaLiftTrivialOrbitTermsVanish
public import GroundTheory.AutomorphicForms.ReductionHeight
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

-- Source module: Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.KkFin

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.M.kkFin :
    ∀ (F : Type) [Field F] [NumberField F], ∀ (k : G1 F) (v : HeightOneSpectrum (𝓞 F)), IntAt v k ↔ Reduction.finAt v (gl k) ∈ GLnLocal.integralGL (v.adicCompletion F) 2 := by
  intro F _ _ k v
  have hinv : (Reduction.finAt v (gl k))⁻¹ = Reduction.finAt v (gl k⁻¹) := by
    have e : ∀ g : GL (Fin 2) (A F), Reduction.finAt v g = Matrix.GeneralLinearGroup.map (Reduction.finEval v) g := by
      intro g; ext i j; rfl
    rw [e, e, ← map_inv, ← map_inv]
  have hent : ∀ (g : G1 F) i j, (Reduction.finAt v (gl g)) i j = (g i j).2 v := fun _ _ _ => rfl
  rw [GLnLocal.mem_integralGL_iff, hinv]
  simp only [hent, GroundTheory.Global.mem_valuationInteger_iff]
  refine ⟨fun h => ⟨h, ?_⟩, fun h => h.1⟩
  intro i j
  have e : (k⁻¹ : G1 F).1 = !![k.1 1 1, -k.1 0 1; -k.1 1 0, k.1 0 0] := by
    rw [Matrix.SpecialLinearGroup.coe_inv, adjugate_fin_two]
  have hn : ∀ a b, (-(k.1 a b)).2 v ∈ v.adicCompletionIntegers F := fun a b =>
    neg_mem (h a b)
  show ((k⁻¹ : G1 F).1 i j).2 v ∈ _
  rw [e]
  fin_cases i <;> fin_cases j
  · exact h 1 1
  · exact hn 0 1
  · exact hn 1 0
  · exact h 0 0
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.KkCpt

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.M.kkCpt :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], KK F = (M.Ks F : Set (G1 F)) ∧ IsCompact (KK F) := by
  intro F _ _ _
  have h1 : KK F = (M.Ks F : Set (G1 F)) := by
    ext g
    change (InfOrth g ∧ ∀ v, IntAt v g) ↔ gl g ∈ Reduction.maxCompact (K := F) (n := 2)
    rw [Reduction.mem_maxCompact, UpperTheory.ConvolutionTheory.R2.M.kkInf F g]
    exact and_congr_right fun _ => forall_congr' fun v => UpperTheory.ConvolutionTheory.R2.M.kkFin F g v
  refine ⟨h1, ?_⟩
  have hC := Reduction.isCompact_maxCompact (K := F) (n := 2)
  have hD := hC.image (Units.continuous_val)
  have h2 := Matrix.SpecialLinearGroup.isClosedEmbedding_val.isCompact_preimage hD
  have h3 : KK F = (fun g : G1 F => g.1) ⁻¹' (Units.val '' (Reduction.maxCompact (K := F) (n := 2) : Set (GL (Fin 2) (A F)))) := by
    rw [h1]
    ext g
    constructor
    · intro hg
      exact ⟨gl g, hg, rfl⟩
    · rintro ⟨u, hu, huv⟩
      have : u = gl g := Units.ext huv
      subst this
      exact hu
  rw [h3]
  exact h2
end
end
