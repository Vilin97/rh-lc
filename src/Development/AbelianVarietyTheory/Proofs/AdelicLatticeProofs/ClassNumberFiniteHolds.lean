module

public import Formalism.UnipotentAdelicQuotients.ClassNumberFinite
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ClassNumberFiniteIntegralLevelClosedSubgroupGLStatement
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Topology.Algebra.Group.Defs
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.Topology.Instances.Matrix
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsOpenIsCompact
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactAdeleRingModNumberField
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Algebra.Group.Units

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CompactMeetsFinitelyManyLeftCosetsOpen

section

@[expose] public section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem compact_subset_finite_leftCosets (G : Type) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (U : Subgroup G) (K : Set G) (hU : IsOpen (U : Set G))
    (hK : IsCompact K) : ∃ T : Finset G, ∀ k ∈ K, ∃ t ∈ T, ∃ u ∈ U, k = t * u := by
  obtain ⟨T, -, hT⟩ := hK.elim_nhds_subcover (fun t : G => (fun k => t⁻¹ * k) ⁻¹' (U : Set G))
    (fun t _ => (hU.preimage (by fun_prop)).mem_nhds (by simp))
  refine ⟨T, fun k hk => ?_⟩
  have := hT hk
  simp only [Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe] at this
  obtain ⟨t, ht, h⟩ := this
  exact ⟨t, ht, t⁻¹ * k, h, by simp⟩

end GlobalTheory.ClassFin
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CompactMeetsFinitelyManyLeftCosetsOpenStatement

section

@[expose] public section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.compact_meets_finitely_many_leftCosets_open : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (U : Subgroup G) (K : Set G), IsOpen (U : Set G) → IsCompact K → ∃ T : Finset G, ∀ k ∈ K, ∃ t ∈ T, ∃ u ∈ U, k = t * u := by
  first | exact @GlobalTheory.ClassFin.compact_subset_finite_leftCosets | exact GlobalTheory.ClassFin.compact_subset_finite_leftCosets | (intros; apply GlobalTheory.ClassFin.compact_subset_finite_leftCosets <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsCompactIntegralPointsFiniteAdelicAlgebraicGrou

section

@[expose] public section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open NumberField IsDedekindDomain

namespace GlobalTheory.IntegralPointsCompact

theorem continuous_aeval_family {F A X σ : Type} [CommRing F] [CommRing A] [Algebra F A]
    [TopologicalSpace A] [IsTopologicalRing A] [TopologicalSpace X] (f : X → σ → A)
    (hf : ∀ s, Continuous fun x => f x s) (P : MvPolynomial σ F) :
    Continuous fun x => MvPolynomial.aeval (f x) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa using continuous_const
  | add p q hp hq => simp only [map_add (f := _)]; exact hp.add hq
  | mul_X p s hp => simp only [map_mul, MvPolynomial.aeval_X]; exact hp.mul (hf s)

theorem isClosed_of_equations {F A ι : Type} [CommRing F] [CommRing A] [Algebra F A]
    [TopologicalSpace A] [IsTopologicalRing A] [T2Space A] [Fintype ι] [DecidableEq ι]
    (S : Set (MvPolynomial (ι × ι) F)) (H : Subgroup (GL ι A))
    (hH : ∀ g, g ∈ H ↔ ∀ P ∈ S, MvPolynomial.aeval
      (fun ij : ι × ι => ((g : GL ι A) : Matrix ι ι A) ij.1 ij.2) P = 0) :
    IsClosed (H : Set (GL ι A)) := by
  have e : (H : Set (GL ι A)) = ⋂ P ∈ S, {g : GL ι A | MvPolynomial.aeval
      (fun ij : ι × ι => (g : Matrix ι ι A) ij.1 ij.2) P = 0} := by
    ext g
    simp only [Set.mem_iInter, SetLike.mem_coe]
    exact hH g
  rw [e]
  refine isClosed_biInter fun P _ => isClosed_eq ?_ continuous_const
  exact continuous_aeval_family (fun (g : GL ι A) (ij : ι × ι) => (g : Matrix ι ι A) ij.1 ij.2)
    (fun s => Units.continuous_val.matrix_elem s.1 s.2) P

theorem isCompact_integral_points : ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (S : Set (MvPolynomial (Fin n × Fin n) F)) (H : Subgroup (GL (Fin n) (FiniteAdeleRing (𝓞 F) F))), (∀ g, g ∈ H ↔ (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) ij.1 ij.2) P = 0)) → IsCompact {u : H | (∀ i j, (∀ v, (((u : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) i j : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v) ∧ (∀ v, ((((u : GL (Fin n) (FiniteAdeleRing (𝓞 F) F))⁻¹ : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) i j : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v))} := by
  intro F _ _ n S H hH
  have : T2Space (FiniteAdeleRing (𝓞 F) F) :=
    inferInstanceAs (T2Space (RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite))
  have hK := GlobalTheory.GLIntegral.isCompact_glSub (ι := Fin n) (GlobalTheory.GLIntegral.intSubring F)
    (GlobalTheory.AdeleCocompact.isCompact_integral F)
  have hc := isClosed_of_equations S H hH
  have h := hc.isClosedEmbedding_subtypeVal.isCompact_preimage hK
  refine (congrArg IsCompact (Set.ext fun u => ?_)).mpr h
  exact ⟨fun hu => ⟨fun i j => (hu i j).1, fun i j => (hu i j).2⟩,
    fun hu i j => ⟨hu.1 i j, hu.2 i j⟩⟩

end GlobalTheory.IntegralPointsCompact
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsCompactIntegralPointsFiniteAdelicAlgebraicGrouStatement

section

@[expose] public section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.isCompact_integralPoints_finiteAdelic_algebraicGroup : ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (S : Set (MvPolynomial (Fin n × Fin n) F)) (H : Subgroup (GL (Fin n) (FiniteAdeleRing (𝓞 F) F))), (∀ g, g ∈ H ↔ (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) ij.1 ij.2) P = 0)) → IsCompact {u : H | (∀ i j, (∀ v, (((u : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) i j : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v) ∧ (∀ v, ((((u : GL (Fin n) (FiniteAdeleRing (𝓞 F) F))⁻¹ : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) i j : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v))} := by
  first | exact @GlobalTheory.IntegralPointsCompact.isCompact_integral_points | exact GlobalTheory.IntegralPointsCompact.isCompact_integral_points | (intros; apply GlobalTheory.IntegralPointsCompact.isCompact_integral_points <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ClassNumberFiniteHolds

section

@[expose] public section

open NumberField IsDedekindDomain

namespace GlobalTheory

theorem classNumberFinite_holds : HeckeCharacterZeroLocus.ClassNumberFinite := by
  classical
  intro F _ _ n S hS U hUo _
  obtain ⟨T₀, hT₀, hx⟩ := GlobalTheory.T.classNumber_finite_integralLevel_closedSubgroupGL F n S (fun B _ _ =>
    ⟨(hS B).1, fun g h hg hh => (hS B).2.1 g hg h hh, fun g hg => (hS B).2.2 g hg⟩)
  have hK := GlobalTheory.T.isCompact_integralPoints_finiteAdelic_algebraicGroup F n S (HeckeCharacterZeroLocus.locusSubgroup S hS (FiniteAdeleRing (𝓞 F) F))
    (fun g => Iff.rfl)
  obtain ⟨T₁, hT₁⟩ := GlobalTheory.T.compact_meets_finitely_many_leftCosets_open _ U _ hUo hK
  refine ⟨Finset.image₂ (fun (s : T₀) (t : HeckeCharacterZeroLocus.locusSubgroup S hS (FiniteAdeleRing (𝓞 F) F)) =>
    (⟨s.1, hT₀ s.1 s.2⟩ : HeckeCharacterZeroLocus.locusSubgroup S hS (FiniteAdeleRing (𝓞 F) F)) * t) T₀.attach T₁, ?_⟩
  intro x
  obtain ⟨γ, hγ, s, hs, k, hk, hki, hxe⟩ := hx x.1 x.2
  obtain ⟨t, ht, u, hu, hke⟩ := hT₁ ⟨k, hk⟩ hki
  refine ⟨γ, hγ, _, Finset.mem_image₂_of_mem (Finset.mem_attach T₀ ⟨s, hs⟩) ht, u, hu, ?_⟩
  have hke' : k = t.1 * u.1 := congrArg Subtype.val hke
  rw [hxe, hke']
  simp only [Subgroup.coe_mul, mul_assoc]

end GlobalTheory
end
end
