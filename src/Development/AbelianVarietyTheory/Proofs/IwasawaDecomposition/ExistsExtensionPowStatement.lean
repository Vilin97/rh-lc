module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasNormGroups
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.NotIsGenericDetRepTwo
import Formalism.ConjugateSelfDual.Statement
import ReciprocityTheory.GaloisValuations.GlobalA

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfValuationEqPow

section

@[expose] public section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField Filter Topology
open scoped WithZeroTopology WithZero

namespace GlobalTheory.CompletionHomContinuous

theorem continuous_of_valuation_eq_pow {A B Γ : Type*} [Field A] [Field B]
    [LinearOrderedCommGroupWithZero Γ] [hA : Valued A Γ] [hB : Valued B Γ]
    (hs : Function.Surjective hA.v) (g : A →+* B) {e : ℕ} (he : 0 < e)
    (hg : ∀ x, hB.v (g x) = hA.v x ^ e) : Continuous g := by
  refine continuous_of_continuousAt_zero g ?_
  rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero B Γ).tendsto_right_iff]
  intro γ _
  have hc : Continuous fun x : A => hA.v x ^ e :=
    (Valued.continuous_valuation_of_surjective hs).pow e
  have h0 : Tendsto (fun x : A => hA.v x ^ e) (𝓝 0) (𝓝 0) :=
    hc.tendsto' 0 0 (by simp [he.ne'])
  rw [WithZeroTopology.tendsto_zero] at h0
  have hγ : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 := by simp
  filter_upwards [h0 _ hγ] with x hx
  simp only [Set.mem_ofPred_eq, Valuation.restrict_lt_iff_lt_embedding, hg]
  exact hx

theorem exists_completion_hom (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (v : HeightOneSpectrum (RingOfIntegers K))
    (v' : HeightOneSpectrum (RingOfIntegers L)) (e : ℕ) (he : 0 < e)
    (h : ∀ x : K, v'.valuation L (algebraMap K L x) = v.valuation K x ^ e) :
    ∃ f : adicCompletion K v →+* adicCompletion L v', Continuous f ∧
      (∀ x : K, f (algebraMap K (adicCompletion K v) x) =
        algebraMap L (adicCompletion L v') (algebraMap K L x)) ∧
      ∀ y : adicCompletion K v, (Valued.v (f y) : WithZero (Multiplicative ℤ)) = Valued.v y ^ e := by
  let g : WithVal (v.valuation K) →+* adicCompletion L v' :=
    (algebraMap L (adicCompletion L v')).comp
      ((algebraMap K L).comp (WithVal.equiv (v.valuation K)).toRingHom)
  have hL : ∀ x : L, (Valued.v (algebraMap L (adicCompletion L v') x) : WithZero (Multiplicative ℤ))
      = v'.valuation L x := fun x => valuedAdicCompletion_eq_valuation' v' x
  have hK : ∀ x : K, (Valued.v (algebraMap K (adicCompletion K v) x) : WithZero (Multiplicative ℤ))
      = v.valuation K x := fun x => valuedAdicCompletion_eq_valuation' v x
  have hg : Continuous g := by
    refine continuous_of_valuation_eq_pow (Γ := WithZero (Multiplicative ℤ)) ?_ g he ?_
    · intro c
      obtain ⟨x, hx⟩ := v.valuation_surjective K c
      exact ⟨(WithVal.equiv (v.valuation K)).symm x, hx⟩
    · intro x
      exact (hL _).trans (h _)
  let f : adicCompletion K v →+* adicCompletion L v' :=
    (UniformSpace.Completion.extensionHom g hg).comp (adicCompletion.equiv K v).toRingHom
  have hf : Continuous f :=
    (UniformSpace.Completion.continuous_extension (f := g)).comp
      (adicCompletion.continuous_toCompletion K v)
  have hfx : ∀ x : K, f (algebraMap K (adicCompletion K v) x) =
      algebraMap L (adicCompletion L v') (algebraMap K L x) := fun x =>
    UniformSpace.Completion.extensionHom_coe g hg ((WithVal.equiv (v.valuation K)).symm x)
  refine ⟨f, hf, hfx, fun y => ?_⟩
  refine (denseRange_algebraMap K v).induction_on y ?_ ?_
  · exact isClosed_eq
      ((Valued.continuous_valuation_of_surjective (valuedAdicCompletion_surjective L v')).comp hf)
      ((Valued.continuous_valuation_of_surjective (valuedAdicCompletion_surjective K v)).pow e)
  · intro x
    rw [hfx, hL, hK, h]

end GlobalTheory.CompletionHomContinuous
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExtensionPow

section

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.DenseCompl


open scoped WithZeroTopology in
theorem exists_extension_pow (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (e : ℕ) (he : 0 < e)
    (hv : ∀ x : K, v'.valuation L (algebraMap K L x) = v.valuation K x ^ e) :
    ∃ f : v.adicCompletion K →+* v'.adicCompletion L, Continuous f ∧
      (∀ x : K, f (algebraMap K _ x) = algebraMap L _ (algebraMap K L x)) ∧
      ∀ y, Valued.v (f y) = Valued.v y ^ e := by
  first
  | exact @_root_.GlobalTheory.CompletionHomContinuous.exists_completion_hom
  | exact _root_.GlobalTheory.CompletionHomContinuous.exists_completion_hom
  | (apply _root_.GlobalTheory.CompletionHomContinuous.exists_completion_hom <;> assumption)
  | (intros; apply _root_.GlobalTheory.CompletionHomContinuous.exists_completion_hom <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CompletionHomContinuous.exists_completion_hom <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CompletionHomContinuous.exists_completion_hom ..)

end GlobalTheory.DenseCompl
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExtensionPowStatement

section

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.exists_extension_pow_alt : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (e : ℕ), 0 < e → (∀ x : K, v'.valuation L (algebraMap K L x) = v.valuation K x ^ e) → ∃ f : v.adicCompletion K →+* v'.adicCompletion L, Continuous f ∧ (∀ x : K, f (algebraMap K _ x) = algebraMap L _ (algebraMap K L x)) ∧ ∀ y, Valued.v (f y) = Valued.v y ^ e := by
  first | exact @GlobalTheory.DenseCompl.exists_extension_pow | exact GlobalTheory.DenseCompl.exists_extension_pow | (intros; apply GlobalTheory.DenseCompl.exists_extension_pow <;> assumption)
end
end
