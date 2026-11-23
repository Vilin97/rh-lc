module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrEqLocalizationIntegralClosureComapStatement
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsAddEquivOfSurjectiveOfKerIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDVRValuationSubringComapOfFiniteDimensionalStatement
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZariskiDescentDvrTraceLocalisationStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FractionsUnitDenominatorsReplaceGenerators

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
open Polynomial

namespace GlobalTheory

theorem fractions_unit_denominators_replace_generators : ∀ (L : Type) [Field L] (ψ : ℂ →+* L) (V : ValuationSubring L) (P : L → Prop) (s₀ : Finset L), (∀ x ∈ s₀, ∃ b d : L, P b ∧ P d ∧ d ≠ 0 ∧ d⁻¹ ∈ V ∧ x = b / d) → (∀ s ∈ V, ∃ b ∈ Subring.closure (Set.range ψ ∪ ↑s₀), ∃ d ∈ Subring.closure (Set.range ψ ∪ ↑s₀), d ≠ 0 ∧ d⁻¹ ∈ V ∧ s = b / d) → ∃ t : Finset L, (∀ x ∈ t, P x) ∧ ∀ s ∈ V, ∃ b ∈ Subring.closure (Set.range ψ ∪ ↑t), ∃ d ∈ Subring.closure (Set.range ψ ∪ ↑t), d ≠ 0 ∧ d⁻¹ ∈ V ∧ s = b / d := by
  intro L _ ψ V P s₀ h1 h2
  classical
  choose b d hb hd hd0 hdV hx using h1
  let t : Finset L := (s₀.attach.image (fun x => b x.1 x.2)) ∪ (s₀.attach.image (fun x => d x.1 x.2))
  refine ⟨t, ?_, ?_⟩
  · intro x hx'
    simp only [t, Finset.mem_union, Finset.mem_image] at hx'
    rcases hx' with ⟨⟨y, hy⟩, _, rfl⟩ | ⟨⟨y, hy⟩, _, rfl⟩
    · exact hb y hy
    · exact hd y hy
  · let S : Subring L := Subring.closure (Set.range ψ ∪ (t : Set L))
    have hVone : (1 : L)⁻¹ ∈ V := by simpa using V.one_mem
    let F : Subring L :=
      { carrier := {y | ∃ b ∈ S, ∃ d ∈ S, d ≠ 0 ∧ d⁻¹ ∈ V ∧ y = b / d}
        mul_mem' := by
          rintro _ _ ⟨b₁, hb₁, d₁, hd₁, h₁, i₁, rfl⟩ ⟨b₂, hb₂, d₂, hd₂, h₂, i₂, rfl⟩
          refine ⟨b₁ * b₂, S.mul_mem hb₁ hb₂, d₁ * d₂, S.mul_mem hd₁ hd₂, mul_ne_zero h₁ h₂, ?_, ?_⟩
          · rw [mul_inv]; exact mul_mem i₁ i₂
          · rw [div_mul_div_comm]
        one_mem' := ⟨1, S.one_mem, 1, S.one_mem, one_ne_zero, hVone, by simp⟩
        add_mem' := by
          rintro _ _ ⟨b₁, hb₁, d₁, hd₁, h₁, i₁, rfl⟩ ⟨b₂, hb₂, d₂, hd₂, h₂, i₂, rfl⟩
          refine ⟨b₁ * d₂ + d₁ * b₂, S.add_mem (S.mul_mem hb₁ hd₂) (S.mul_mem hd₁ hb₂),
            d₁ * d₂, S.mul_mem hd₁ hd₂, mul_ne_zero h₁ h₂, ?_, ?_⟩
          · rw [mul_inv]; exact mul_mem i₁ i₂
          · rw [div_add_div _ _ h₁ h₂]
        zero_mem' := ⟨0, S.zero_mem, 1, S.one_mem, one_ne_zero, hVone, by simp⟩
        neg_mem' := by
          rintro _ ⟨b₁, hb₁, d₁, hd₁, h₁, i₁, rfl⟩
          exact ⟨-b₁, S.neg_mem hb₁, d₁, hd₁, h₁, i₁, by rw [neg_div]⟩ }
    have htS : ∀ x ∈ t, x ∈ S := fun x hx' => Subring.subset_closure (Or.inr hx')
    have hle : Subring.closure (Set.range ψ ∪ (s₀ : Set L)) ≤ F := by
      rw [Subring.closure_le]
      rintro x (⟨c, rfl⟩ | hx')
      · exact ⟨ψ c, Subring.subset_closure (Or.inl ⟨c, rfl⟩), 1, S.one_mem, one_ne_zero, hVone, by simp⟩
      · refine ⟨b x hx', htS _ ?_, d x hx', htS _ ?_, hd0 x hx', hdV x hx', hx x hx'⟩
        · exact Finset.mem_union_left _ (Finset.mem_image_of_mem (fun y : s₀ => b y.1 y.2) (Finset.mem_attach _ ⟨x, hx'⟩))
        · exact Finset.mem_union_right _ (Finset.mem_image_of_mem (fun y : s₀ => d y.1 y.2) (Finset.mem_attach _ ⟨x, hx'⟩))
    intro s hs
    obtain ⟨B, hB, D, hD, hD0, hDV, rfl⟩ := h2 s hs
    obtain ⟨b₁, hb₁, b₂, hb₂, hb₂0, hb₂V, rfl⟩ := hle hB
    obtain ⟨d₁, hd₁, d₂, hd₂, hd₂0, hd₂V, rfl⟩ := hle hD
    have hd₁0 : d₁ ≠ 0 := by
      rintro rfl; exact hD0 (by simp)
    have hd₁V : d₁⁻¹ ∈ V := by
      have : d₁⁻¹ = (d₁ / d₂)⁻¹ * d₂⁻¹ := by
        field_simp
      rw [this]; exact mul_mem hDV hd₂V
    refine ⟨b₁ * d₂, S.mul_mem hb₁ hd₂, b₂ * d₁, S.mul_mem hb₂ hd₁, mul_ne_zero hb₂0 hd₁0, ?_, ?_⟩
    · rw [mul_inv]; exact mul_mem hb₂V hd₁V
    · rw [div_div_div_eq]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FractionsUnitDenominatorsReplaceGeneratorsStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
open Polynomial


theorem _root_.GlobalTheory.T.fractions_unitDenominators_replace_generators : ∀ (L : Type) [Field L] (ψ : ℂ →+* L) (V : ValuationSubring L) (P : L → Prop) (s₀ : Finset L), (∀ x ∈ s₀, ∃ b d : L, P b ∧ P d ∧ d ≠ 0 ∧ d⁻¹ ∈ V ∧ x = b / d) → (∀ s ∈ V, ∃ b ∈ Subring.closure (Set.range ψ ∪ ↑s₀), ∃ d ∈ Subring.closure (Set.range ψ ∪ ↑s₀), d ≠ 0 ∧ d⁻¹ ∈ V ∧ s = b / d) → ∃ t : Finset L, (∀ x ∈ t, P x) ∧ ∀ s ∈ V, ∃ b ∈ Subring.closure (Set.range ψ ∪ ↑t), ∃ d ∈ Subring.closure (Set.range ψ ∪ ↑t), d ≠ 0 ∧ d⁻¹ ∈ V ∧ s = b / d := by
  first | exact @GlobalTheory.fractions_unit_denominators_replace_generators | exact GlobalTheory.fractions_unit_denominators_replace_generators | (intros; apply GlobalTheory.fractions_unit_denominators_replace_generators <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationSubringFractionsOfEssFiniteTypeComplex

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
open Polynomial

namespace GlobalTheory

theorem valuationSubring_fractions_of_essFiniteType : ∀ (L : Type) [Field L] (ψ : ℂ →+* L) (V : ValuationSubring L) (hψ : ∀ a, ψ a ∈ V), (ψ.codRestrict V hψ).EssFiniteType → ∃ s₀ : Finset L, (∀ x ∈ s₀, x ∈ V) ∧ ∀ s ∈ V, ∃ b ∈ Subring.closure (Set.range ψ ∪ ↑s₀), ∃ d ∈ Subring.closure (Set.range ψ ∪ ↑s₀), d ≠ 0 ∧ d⁻¹ ∈ V ∧ s = b / d := by
  classical
  intro L _ ψ V hψ h
  letI : Algebra ℂ V := (ψ.codRestrict V hψ).toAlgebra
  have h' : Algebra.EssFiniteType ℂ V := h
  obtain ⟨s, hs⟩ := h'.cond
  refine ⟨s.image (fun x : V => (x : L)), ?_, ?_⟩
  · intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨y, -, rfl⟩ := hx
    exact y.2
  have key : ∀ x ∈ Algebra.adjoin ℂ (s : Set V),
      ((x : V) : L) ∈ Subring.closure (Set.range ψ ∪ ↑(s.image (fun x : V => (x : L)))) := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      apply Subring.subset_closure
      right
      rw [Finset.coe_image]
      exact ⟨x, hx, rfl⟩
    | algebraMap r =>
      apply Subring.subset_closure
      left
      exact ⟨r, rfl⟩
    | add x y _ _ hx hy =>
      simpa using Subring.add_mem _ hx hy
    | mul x y _ _ hx hy =>
      simpa using Subring.mul_mem _ hx hy
  intro v hv
  obtain ⟨⟨a, m⟩, hm⟩ := IsLocalization.surj
    (Submonoid.comap (algebraMap (↥(Algebra.adjoin ℂ (s : Set V))) V) (IsUnit.submonoid V)) (⟨v, hv⟩ : V)
  have hu : IsUnit ((m : Algebra.adjoin ℂ (s : Set V)) : V) := m.2
  obtain ⟨u, hu'⟩ := hu
  have hinv : (((m : Algebra.adjoin ℂ (s : Set V)) : V) : L) * (((u⁻¹ : Vˣ) : V) : L) = 1 := by
    rw [← hu']
    change (((u : V) * ((u⁻¹ : Vˣ) : V) : V) : L) = ((1 : V) : L)
    rw [u.mul_inv]
  have hd0 : (((m : Algebra.adjoin ℂ (s : Set V)) : V) : L) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hinv
    exact zero_ne_one hinv
  have hmL := congrArg (fun z : V => (z : L)) hm
  simp only at hmL
  refine ⟨((a : V) : L), key _ a.2, (((m : Algebra.adjoin ℂ (s : Set V)) : V) : L),
    key _ (m : Algebra.adjoin ℂ (s : Set V)).2, hd0, ?_, ?_⟩
  · rw [inv_eq_of_mul_eq_one_right hinv]
    exact ((u⁻¹ : Vˣ) : V).2
  · rw [eq_div_iff hd0]
    simpa using hmL

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationSubringFractionsOfEssFiniteTypeComplexStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
open Polynomial


theorem _root_.GlobalTheory.T.valuationSubring_fractions_of_essFiniteType_complex : ∀ (L : Type) [Field L] (ψ : ℂ →+* L) (V : ValuationSubring L) (hψ : ∀ a, ψ a ∈ V), (ψ.codRestrict V hψ).EssFiniteType → ∃ s₀ : Finset L, (∀ x ∈ s₀, x ∈ V) ∧ ∀ s ∈ V, ∃ b ∈ Subring.closure (Set.range ψ ∪ ↑s₀), ∃ d ∈ Subring.closure (Set.range ψ ∪ ↑s₀), d ≠ 0 ∧ d⁻¹ ∈ V ∧ s = b / d := by
  first | exact @GlobalTheory.valuationSubring_fractions_of_essFiniteType | exact GlobalTheory.valuationSubring_fractions_of_essFiniteType | (intros; apply GlobalTheory.valuationSubring_fractions_of_essFiniteType <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrComapFiniteIndexEssFiniteTypeComplex

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
open Polynomial

namespace GlobalTheory

theorem restrict_dvr_essFiniteType : ∀ (K L : Type) [Field K] [Field L] (φ : K →+* L) (c : ℂ →+* K), (letI := φ.toAlgebra; FiniteDimensional K L) → ∀ (V : ValuationSubring L) [IsDiscreteValuationRing V] (hc : ∀ a, φ (c a) ∈ V), ((φ.comp c).codRestrict V hc).EssFiniteType → IsDiscreteValuationRing (V.comap φ) ∧ (c.codRestrict (V.comap φ) hc).EssFiniteType := by
  have hL0 := GlobalTheory.T.valuationSubring_fractions_of_essFiniteType_complex
  have hL1 := GlobalTheory.T.isDVR_valuationSubring_comap_of_finiteDimensional
  have hL2 := GlobalTheory.T.dvr_eq_localization_integralClosure_comap
  have hL4 := GlobalTheory.T.fractions_unitDenominators_replace_generators
  have hL3 := GlobalTheory.T.zariski_descent_dvr_trace_localisation
  intro K L _ _ φ c hfin V _ hc hV
  have hE : IsDiscreteValuationRing (V.comap φ) := hL1 K L φ hfin V
  haveI : CharZero K := RingHom.charZero_iff c.injective |>.mp inferInstance
  obtain ⟨s₀, hs₀V, hs₀⟩ := hL0 L (φ.comp c) V hc hV
  obtain ⟨t, ht, htV⟩ := hL4 L (φ.comp c) V
    (fun x => x ∈ V ∧ ∃ p : K[X], p.Monic ∧ (∀ i, p.coeff i ∈ V.comap φ) ∧ p.eval₂ φ x = 0) s₀
    (fun x hx => hL2 K L φ hfin V hE x (hs₀V x hx)) hs₀
  exact ⟨hE, hL3 K L φ c hfin V hc t ht htV⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrComapFiniteIndexEssFiniteTypeComplexStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy

theorem _root_.GlobalTheory.T.dvr_comap_finiteIndex_essFiniteType_complex : ∀ (K L : Type) [Field K] [Field L] (φ : K →+* L) (c : ℂ →+* K), (letI := φ.toAlgebra; FiniteDimensional K L) → ∀ (V : ValuationSubring L) [IsDiscreteValuationRing V] (hc : ∀ a, φ (c a) ∈ V), ((φ.comp c).codRestrict V hc).EssFiniteType → IsDiscreteValuationRing (V.comap φ) ∧ (c.codRestrict (V.comap φ) hc).EssFiniteType := by
  first | exact @GlobalTheory.restrict_dvr_essFiniteType | exact GlobalTheory.restrict_dvr_essFiniteType | (intros; apply GlobalTheory.restrict_dvr_essFiniteType <;> assumption)
end
end
