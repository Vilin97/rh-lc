module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.FormsFiniteAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsFiniteDimensionalCompactTranslatesOfLevelT
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AlgModBotOfMemAdjoinCommuting
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CenterUActionMemAdjoinCapOp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsIdempotentDecompositionMixedSpace
public import Development.AutomorphicArithmetic.DivisorFrames.FiniteDimensionalSpanAdjoinApplyOfCommutingAlgeb
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.QdetGeneratesUniversalEnvelopingCentre
public import Development.AutomorphicArithmetic.DivisorFrames.ExistsQdetEqPowAddSumCoeffMemSpan
import Mathlib.Tactic.Linter.Style
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.OrderedCechToCatCochainsOneApplyValueAtSubset
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Gl2LocalToAdelicEmbedding
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Mathlib.RingTheory.Etale.Weakly

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FiniteDimensionalSpanAdjoinOrbitOfCommuting

section

@[expose] public section

open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

theorem UpperTheory.finiteDimensional_span_adjoin_orbit_of_commuting :
    ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (x : M) (s : Set (Module.End ℂ M)), s.Finite → (∀ a ∈ s, ∀ b ∈ s, a * b = b * a) → (∀ T ∈ s, AlgMod (Submodule.span ℂ {x}) ⊥ T) → FiniteDimensional ℂ (Submodule.span ℂ ((fun T : Module.End ℂ M => T x) '' (Algebra.adjoin ℂ s : Set (Module.End ℂ M)))) := by
  intro M _ _ x s hs hc h
  refine UpperTheory.finiteDimensional_span_adjoin_apply_of_commuting_algebraic M s x hc (FiniteDimensional.span_of_finite ℂ hs) fun a ha => ?_
  obtain ⟨p, hp, hx⟩ := h a ha
  exact ⟨p, hp.ne_zero, (Submodule.mem_bot ℂ).1 (hx x (Submodule.mem_span_singleton_self x))⟩
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsZFiniteOfCentreSpan

section

@[expose] public section

open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

theorem UpperTheory.isZFinite_of_centre_span :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (φ : archSmooth K n), Centre (Submodule.span ℂ {φ}) → IsZFinite φ := by
  intro K _ _ n φ hφ
  obtain ⟨ι, hι, ⟨D⟩⟩ := UpperTheory.exists_idempotent_decomposition_mixedSpace K
  have key := fun τ => UpperTheory.exists_qdet_eq_pow_add_sum_coeff_mem_span (Module.End ℂ (archSmooth K n)) n (gen D (lam K n) τ)
  choose c hc hq using key
  let s : Set (Module.End ℂ (archSmooth K n)) := Set.range (fun p : ι × Fin n => c p.1 p.2)
  have hcZ : ∀ τ k, c τ k ∈ Zc K n := by
    intro τ k
    have h1 : Submodule.span ℂ (Set.range (Formalism.REAL.qdet (gen D (lam K n) τ))) ≤
        Subalgebra.toSubmodule (Zc K n) := by
      rw [Submodule.span_le]
      rintro x ⟨u, rfl⟩
      exact UpperTheory.qdet_generates_universalEnveloping_centre K n ι D τ u
    exact h1 (hc τ k)
  have hsZ : ∀ x ∈ s, x ∈ Zc K n := by
    rintro x ⟨⟨τ, k⟩, rfl⟩
    exact hcZ τ k
  have hAlg : ∀ T ∈ Zc K n, AlgMod (Submodule.span ℂ {φ}) ⊥ T := by
    intro T hT
    apply UpperTheory.algMod_bot_of_mem_adjoin_commuting _ _ (uAction '' (isExpLieAlgebra K n).centerU)
    · rintro x ⟨z, hz, rfl⟩ y ⟨w, hw, rfl⟩
      exact Zc_comm (uAction_mem_Zc hz) (uAction_mem_Zc hw)
    · rintro x ⟨z, hz, rfl⟩
      exact hφ z hz
    · exact hT
  have hfd := UpperTheory.finiteDimensional_span_adjoin_orbit_of_commuting _ φ s (Set.finite_range _)
    (fun a ha b hb => Zc_comm (hsZ a ha) (hsZ b hb)) (fun T hT => hAlg T (hsZ T hT))
  have hle : Algebra.adjoin ℂ {x | ∃ τ u, x = capOp D n τ u} ≤ Algebra.adjoin ℂ s := by
    rw [Algebra.adjoin_le_iff]
    rintro x ⟨τ, u, rfl⟩
    show Formalism.REAL.qdet (gen D (lam K n) τ) u ∈ Algebra.adjoin ℂ s
    rw [hq τ u]
    refine Subalgebra.add_mem _ (Subalgebra.algebraMap_mem _ _)
      (Subalgebra.sum_mem _ fun k hk => Subalgebra.smul_mem _ ?_ _)
    exact Algebra.subset_adjoin ⟨(τ, ⟨k, Finset.mem_range.mp hk⟩), rfl⟩
  have hsub : Submodule.span ℂ ((fun z => (uAction z) φ) '' ((isExpLieAlgebra K n).centerU : Set _)) ≤
      Submodule.span ℂ ((fun T : Module.End ℂ (archSmooth K n) => T φ) '' (Algebra.adjoin ℂ s : Set _)) := by
    apply Submodule.span_mono
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨uAction z, hle (UpperTheory.centerU_action_mem_adjoin_capOp K n ι D z hz), rfl⟩
  exact Submodule.finiteDimensional_of_le hsub
end
end

-- Source module: Development.AutomorphicArithmetic.DivisorFrames.FiniteDimensionalSpanRangeOfColumnsMem

section

@[expose] public section

open scoped TensorProduct NNReal Matrix ComplexConjugate ContDiff
open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.GLTwoHecke GlobalTheory.StdPar
open GlobalTheory.Doubling (absE ideleAtInf)
open GlobalTheory.UAut (IsMaxCpt)

theorem UpperTheory.finiteDimensional_span_range_of_columns_mem :
    ∀ (A B : Type) (Φ : A → B → ℂ) (S : Submodule ℂ (A → ℂ)), FiniteDimensional ℂ S → (∀ b, (fun a => Φ a b) ∈ S) →
        FiniteDimensional ℂ (Submodule.span ℂ (Set.range Φ)) := by
  intro A B Φ S hS hcol
  let F : Module.Dual ℂ S →ₗ[ℂ] (B → ℂ) :=
    { toFun := fun f b => f ⟨fun a => Φ a b, hcol b⟩
      map_add' := fun f g => rfl
      map_smul' := fun c f => rfl }
  have hle : Submodule.span ℂ (Set.range Φ) ≤ LinearMap.range F := by
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    refine ⟨(LinearMap.proj (R := ℂ) (φ := fun _ : A => ℂ) a).comp S.subtype, ?_⟩
    rfl
  exact Submodule.finiteDimensional_of_le hle
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsAutomorphicFormOfBddSubmodule

section

@[expose] public section

open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

theorem UpperTheory.isAutomorphicForm_of_bdd_submodule :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (S : Submodule ℂ (archSmooth K n)), Bdd S → ∀ φ ∈ S, IsAutomorphicForm φ.1 := by
  intro K _ _ n S hS φ hφ
  obtain ⟨V, hV, hVφ⟩ := UpperTheory.exists_finiteDimensional_compact_translates_of_level_types K n S hS.level hS.types
  refine ⟨hS.left φ hφ, ⟨φ.2, ?_⟩, ?_, ?_, hS.growth φ hφ⟩
  · intro g
    obtain ⟨L, hL, hLφ⟩ := hS.level
    filter_upwards [hL.mem_nhds L.one_mem] with y hy
    exact hLφ φ hφ y hy g
  · exact UpperTheory.finiteDimensional_span_range_of_columns_mem (Reduction.maxCompact (K := K) (n := n)) _
      (fun k g => (φ : AdelicGLn.AdelicGL K n → ℂ) (g * k)) V hV (fun g => hVφ φ hφ g)
  · exact UpperTheory.isZFinite_of_centre_span K n φ (hS.mono ((Submodule.span_singleton_le_iff_mem _ _).mpr hφ)).centre
end
end
