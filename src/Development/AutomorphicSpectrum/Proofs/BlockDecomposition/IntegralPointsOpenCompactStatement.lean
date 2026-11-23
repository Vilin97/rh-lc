module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.GlobalCharacterOfInputs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsOpenIsCompactUnitaryIntegralPoints
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.GlintPrincRelIndexNeZero
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
public import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalRingCardinality.SpanPowerMembership.HasStrictFDerivAtExpZero
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapFacts

-- Source module: Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapTop

section

@[expose] public section

noncomputable section
namespace Formalism.MainNotions.Gaps.LevGap
open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions
open scoped TensorProduct

section DefCong

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

end DefCong

section Gen

variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable (R : Type) [CommRing R] [Algebra F R]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable [TopologicalSpace R] [IsTopologicalRing R]

variable [FiniteDimensional F E]

end Gen

section GLc

variable {M : Type} [CommRing M] [TopologicalSpace M] [IsTopologicalRing M] [T2Space M]
  {n : Type} [Fintype n] [DecidableEq n]

end GLc

section Dec

variable {F E : Type} [Field F] [Field E] [NumberField E] [Algebra F E]
variable {R : Type} [CommRing R] [Algebra F R] (O : Subring R)

variable [NumberField F]

variable {n : Type} [Fintype n] [DecidableEq n]

end Dec

section Adele

variable {F : Type} [Field F] [NumberField F]

theorem compact_Ov (v : HeightOneSpectrum (𝓞 F)) : CompactSpace (v.adicCompletionIntegers F) := by
  have h1 : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) :=
    Formalism.UG.P.glint_finite_residueField v
  have h2 : IsClosed ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    Valued.isClosed_valuationSubring _
  have h3 : CompleteSpace (v.adicCompletionIntegers F) := h2.completeSpace_coe
  exact Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField.2
    ⟨h3, (inferInstance : IsDiscreteValuationRing (v.adicCompletionIntegers F)), h1⟩

theorem isCompact_intAd : IsCompact (intAd F : Set (FiniteAdeleRing (𝓞 F) F)) := by
  have : ∀ v : HeightOneSpectrum (𝓞 F), CompactSpace (v.adicCompletionIntegers F) := compact_Ov
  have h := isCompact_range (RestrictedProduct.isEmbedding_structureMap
    (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (𝓕 := Filter.cofinite)).continuous
  rw [RestrictedProduct.range_structureMap] at h
  exact h

theorem isOpen_intAd : IsOpen (intAd F : Set (FiniteAdeleRing (𝓞 F) F)) :=
  RestrictedProduct.isOpen_forall_mem (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (fun _ => Valued.isOpen_valuationSubring _)

open scoped RestrictedProduct in
theorem t2Space_adeleRing_numberField : T2Space (FiniteAdeleRing (𝓞 F) F) :=
  inferInstanceAs (T2Space (Πʳ v : HeightOneSpectrum (𝓞 F),
    [v.adicCompletion F, v.adicCompletionIntegers F]))

variable {E : Type} [Field E] [NumberField E] [Algebra F E]

end Adele

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

end Main

section Bridge

open Formalism.MainNotions.Gaps.LG

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

section Loc

variable (v : HeightOneSpectrum (𝓞 F))

end Loc

section ParSec

variable {k : ℕ} (P : Par F E k) (v : HeightOneSpectrum (𝓞 F))

end ParSec

end Bridge

section Facts

open Formalism.MainNotions.Gaps.LG

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {k : ℕ}

end Facts

end Formalism.MainNotions.Gaps.LevGap
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralPointsOpenCompact

section

@[expose] public section

open NumberField IsDedekindDomain Matrix

namespace GlobalTheory.CompanionTheory.IntegralPoints

theorem isOpen_isCompact_intGL {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
    (O : Subring R) (ho : IsOpen (O : Set R)) (hc : IsCompact (O : Set R)) (n : ℕ) :
    IsOpen {g : GL (Fin n) R | (∀ i j, (g : Matrix (Fin n) (Fin n) R) i j ∈ O) ∧
        ∀ i j, ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i j ∈ O} ∧
    IsCompact {g : GL (Fin n) R | (∀ i j, (g : Matrix (Fin n) (Fin n) R) i j ∈ O) ∧
        ∀ i j, ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i j ∈ O} := by
  constructor
  · have e : {g : GL (Fin n) R | (∀ i j, (g : Matrix (Fin n) (Fin n) R) i j ∈ O) ∧
        ∀ i j, ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i j ∈ O} =
        (⋂ i, ⋂ j, (fun g : GL (Fin n) R => (g : Matrix (Fin n) (Fin n) R) i j) ⁻¹' (O : Set R)) ∩
        (⋂ i, ⋂ j, (fun g : GL (Fin n) R => ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i j) ⁻¹' (O : Set R)) := by
      ext g
      simp [Set.mem_iInter]
    rw [e]
    refine IsOpen.inter ?_ ?_
    · exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
        ho.preimage (Units.continuous_val.matrix_elem i j)
    · exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
        ho.preimage (Units.continuous_coe_inv.matrix_elem i j)
  · have hM : IsCompact {A : Matrix (Fin n) (Fin n) R | ∀ i j, A i j ∈ O} := by
      have := isCompact_univ_pi fun _ : Fin n => isCompact_univ_pi fun _ : Fin n => hc
      have e : {A : Matrix (Fin n) (Fin n) R | ∀ i j, A i j ∈ O} =
          Set.univ.pi fun _ : Fin n => Set.univ.pi fun _ : Fin n => (O : Set R) :=
        Set.ext fun A => ⟨fun h i _ j _ => h i j, fun h i j => h i trivial j trivial⟩
      exact e ▸ this
    have := (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin n) (Fin n) R)).isCompact_preimage
      (hM.prod (hM.image MulOpposite.continuous_op))
    convert this using 1
    ext g
    exact ⟨fun h => ⟨h.1, _, h.2, rfl⟩, fun ⟨h1, A, hA, e⟩ => ⟨h1, fun i j => by
      have : A = ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) := MulOpposite.op_injective e
      exact this ▸ hA i j⟩⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem coe_Kf (n : ℕ) : (PositivityTheory.Rg.BcB.G8.Kf E n : Set (GL (Fin n) (FiniteAdeleRing (𝓞 E) E))) =
    {g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E) | (∀ i j, (g : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) i j ∈ Formalism.UG.intAd E) ∧
      ∀ i j, ((g⁻¹ : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) i j ∈
        Formalism.UG.intAd E} := by
  ext g
  simp only [SetLike.mem_coe, PositivityTheory.Rg.BcB.G8.Kf, Subgroup.mem_iInf, Subgroup.mem_comap, Set.mem_setOf_eq]
  constructor
  · intro h
    refine ⟨fun i j w => ?_, fun i j w => ?_⟩
    · have h1 := h w
      rw [← SetLike.mem_coe, GlobalTheory.LFun.KGL, GlobalTheory.LFun.IntPtsUnitary.coe_GLint] at h1
      exact h1.1 i j
    · have h1 := h w
      rw [← SetLike.mem_coe, GlobalTheory.LFun.KGL, GlobalTheory.LFun.IntPtsUnitary.coe_GLint] at h1
      have h2 := h1.2 i j
      rw [← map_inv] at h2
      exact h2
  · rintro ⟨h1, h2⟩ w
    rw [← SetLike.mem_coe, GlobalTheory.LFun.KGL, GlobalTheory.LFun.IntPtsUnitary.coe_GLint]
    refine ⟨fun i j => h1 i j w, fun i j => ?_⟩
    rw [← map_inv]
    exact h2 i j w

theorem kfOC : PositivityTheory.Rg.BcB.G8.KfOC := by
  intro E _ _ _ n
  haveI : T2Space (FiniteAdeleRing (𝓞 E) E) := Formalism.MainNotions.Gaps.LevGap.t2Space_adeleRing_numberField
  rw [coe_Kf]
  exact isOpen_isCompact_intGL (Formalism.UG.intAd E) Formalism.MainNotions.Gaps.LevGap.isOpen_intAd
    Formalism.MainNotions.Gaps.LevGap.isCompact_intAd n

end GlobalTheory.CompanionTheory.IntegralPoints
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralPointsOpenCompactStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.finite_kernel_compact_open : PositivityTheory.Rg.BcB.G8.KfOC := by
  first | exact @GlobalTheory.CompanionTheory.IntegralPoints.kfOC | exact GlobalTheory.CompanionTheory.IntegralPoints.kfOC | (intros; apply GlobalTheory.CompanionTheory.IntegralPoints.kfOC <;> assumption)
end
end
