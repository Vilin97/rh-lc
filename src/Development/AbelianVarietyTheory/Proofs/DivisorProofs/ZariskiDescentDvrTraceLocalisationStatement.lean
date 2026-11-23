module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EssFiniteTypeOfLocalizationFiniteTypeComplex
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsAddEquivOfSurjectiveOfKerIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.HaveILetI
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalFiniteTypeSubringInValuationSubring
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightLeOneOfGoingDownZariskiStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EssFiniteTypeOfLocalizationFiniteTypeComplexStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
open Polynomial


theorem _root_.GlobalTheory.T.essFiniteType_of_localization_finiteType_complex : ∀ (K : Type) [Field K] (c : ℂ →+* K) (R : Subring K) (hcR : ∀ a, c a ∈ R) (E : ValuationSubring K) (hcE : ∀ a, c a ∈ E), R ≤ E.toSubring → (c.codRestrict R hcR).FiniteType → (∀ e ∈ E, ∃ a ∈ R, ∃ s ∈ R, s⁻¹ ∈ E ∧ e = a / s) → (c.codRestrict E hcE).EssFiniteType := by
  first | exact @GlobalTheory.EssFiniteDescent.essFiniteType_of_eq_div | exact GlobalTheory.EssFiniteDescent.essFiniteType_of_eq_div | (intros; apply GlobalTheory.EssFiniteDescent.essFiniteType_of_eq_div <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDivOfCenterHeightLeOne

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
open Polynomial

namespace GlobalTheory


open IsLocalRing in
theorem valuationRing_atPrime_of_minimal {A : Type} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] (q : Ideal A) [q.IsPrime]
    (hmin : ∀ p : Ideal A, p.IsPrime → p ≠ ⊥ → p ≤ q → p = q) :
    ValuationRing (Localization.AtPrime q) := by
  have hT := tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain (Localization.AtPrime q)
  have h1 : IsIntegrallyClosed (Localization.AtPrime q) :=
    isIntegrallyClosed_of_isLocalization _ q.primeCompl q.primeCompl_le_nonZeroDivisors
  have h2 : ∀ Q' : Ideal (Localization.AtPrime q), Q' ≠ ⊥ → Q'.IsPrime →
      Q' = maximalIdeal (Localization.AtPrime q) := by
    intro Q' hQ' hQ'p
    have hc : (Q'.comap (algebraMap A (Localization.AtPrime q))).IsPrime := Ideal.comap_isPrime _ _
    have hle : Q'.comap (algebraMap A (Localization.AtPrime q)) ≤ q := by
      intro x hx
      by_contra hxq
      exact hQ'p.ne_top (Ideal.eq_top_of_isUnit_mem _ hx
        (IsLocalization.map_units (Localization.AtPrime q) (⟨x, hxq⟩ : q.primeCompl)))
    have hne : Q'.comap (algebraMap A (Localization.AtPrime q)) ≠ ⊥ := by
      intro h0
      apply hQ'
      rw [← IsLocalization.map_under q.primeCompl (Localization.AtPrime q) Q']
      rw [Ideal.under, h0, Ideal.map_bot]
    have heq := hmin _ hc hne hle
    rw [← IsLocalization.map_under q.primeCompl (Localization.AtPrime q) Q']
    rw [Ideal.under, heq, Localization.AtPrime.map_eq_maximalIdeal]
  have h12 : IsIntegrallyClosed (Localization.AtPrime q) ∧ ∀ Q' : Ideal (Localization.AtPrime q),
      Q' ≠ ⊥ → Q'.IsPrime → Q' = maximalIdeal (Localization.AtPrime q) := ⟨h1, h2⟩
  exact (hT.out 4 2).mp h12

theorem mul_eq_mul_of_atPrime {A : Type} [CommRing A] [IsDomain A] (q : Ideal A) [q.IsPrime]
    (x y a : A) (s : q.primeCompl)
    (h : algebraMap A (Localization.AtPrime q) x * IsLocalization.mk' _ a s =
      algebraMap A (Localization.AtPrime q) y) : x * a = y * s := by
  rw [IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_eq_iff_eq_mul, ← map_mul] at h
  exact IsLocalization.injective (Localization.AtPrime q) q.primeCompl_le_nonZeroDivisors h

end GlobalTheory

namespace GlobalTheory

theorem exists_div_of_center_height_le_one : ∀ (K : Type) [Field K] (R : Subring K) [IsNoetherianRing R]
    [IsIntegrallyClosed R] [IsFractionRing R K] (E : ValuationSubring K), R ≤ E.toSubring →
    (∀ p : Ideal R, p.IsPrime → p ≠ ⊥ → (∀ r ∈ p, (r : K) ∈ E.nonunits) →
      ∀ r : R, (r : K) ∈ E.nonunits → r ∈ p) →
    ∀ e ∈ E, ∃ a ∈ R, ∃ s ∈ R, s⁻¹ ∈ E ∧ e = a / s := by
  intro K _ R _ _ _ E hRE hyp e he
  classical
  let φ : R →+* E :=
    { toFun := fun r => ⟨r, hRE r.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl,
      map_zero' := rfl, map_add' := fun _ _ => rfl }
  let q : Ideal R := (IsLocalRing.maximalIdeal E).comap φ
  have hqmem : ∀ r : R, r ∈ q ↔ E.valuation (r : K) < 1 := fun r => E.valuation_lt_one_iff (φ r)
  have hRv : ∀ r : R, E.valuation (r : K) ≤ 1 := fun r => (E.valuation_le_one_iff _).2 (hRE r.2)
  have hv1 : ∀ s : R, s ∉ q → E.valuation (s : K) = 1 := fun s hs =>
    le_antisymm (hRv s) (not_lt.1 ((hqmem s).not.1 hs))
  have hinv : ∀ s : R, s ∉ q → (s : K)⁻¹ ∈ E := by
    intro s hs
    rw [← E.valuation_le_one_iff, map_inv₀, hv1 s hs, inv_one]
  have hne0 : ∀ s : R, s ∉ q → (s : K) ≠ 0 := by
    intro s hs h
    have := hv1 s hs
    rw [h, map_zero] at this
    exact zero_ne_one this
  haveI : q.IsPrime := Ideal.comap_isPrime _ _
  obtain ⟨⟨x, y⟩, hxy⟩ := IsLocalization.mk'_surjective (S := K) (nonZeroDivisors R) e
  dsimp only at hxy
  rw [IsFractionRing.mk'_eq_div] at hxy
  have hy0 : (algebraMap R K y) ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors y.2
  change ((x : R) : K) / ((y : R) : K) = e at hxy
  change ((y : R) : K) ≠ 0 at hy0
  by_cases hq : q = ⊥
  · have hyq : (y : R) ∉ q := by
      rw [hq, Ideal.mem_bot]
      intro h; apply hy0; rw [h]; rfl
    exact ⟨x, (x : R).2, y, (y : R).2, hinv _ hyq, hxy.symm⟩
  · have hmin : ∀ p : Ideal R, p.IsPrime → p ≠ ⊥ → p ≤ q → p = q := by
      intro p hp hp0 hpq
      refine le_antisymm hpq ?_
      intro r hr
      refine hyp p hp hp0 (fun t ht => ?_) r ?_
      · exact E.mem_nonunits_iff.2 ((hqmem t).1 (hpq ht))
      · exact E.mem_nonunits_iff.2 ((hqmem r).1 hr)
    haveI : ValuationRing (Localization.AtPrime q) := valuationRing_atPrime_of_minimal q hmin
    obtain ⟨c, hc⟩ := ValuationRing.cond (algebraMap R (Localization.AtPrime q) x)
      (algebraMap R (Localization.AtPrime q) y)
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (S := Localization.AtPrime q) q.primeCompl c
    dsimp only at hc
    have hsq : (s : R) ∉ q := s.2
    rcases hc with hc | hc
    · have h := mul_eq_mul_of_atPrime q _ _ _ _ hc
      have hK : ((x : R) : K) * (a : K) = ((y : R) : K) * ((s : R) : K) := by
        have := congrArg (fun t : R => (t : K)) h
        simpa using this
      by_cases haq : a ∈ q
      · exfalso
        have hea : e * (a : K) = ((s : R) : K) := by
          rw [← hxy]
          field_simp
          linear_combination hK
        have h1 := hv1 _ hsq
        rw [← hea, map_mul] at h1
        have hle : E.valuation e * E.valuation (a : K) ≤ E.valuation (a : K) :=
          mul_le_of_le_one_left' ((E.valuation_le_one_iff e).2 he)
        have := (hqmem a).1 haq
        rw [h1] at hle
        exact absurd (lt_of_le_of_lt hle this) (lt_irrefl 1)
      · refine ⟨((s : R) : K), (s : R).2, (a : K), a.2, hinv a haq, ?_⟩
        rw [← hxy, div_eq_div_iff hy0 (hne0 a haq)]
        linear_combination hK
    · have h := mul_eq_mul_of_atPrime q _ _ _ _ hc
      have hK : ((y : R) : K) * (a : K) = ((x : R) : K) * ((s : R) : K) := by
        have := congrArg (fun t : R => (t : K)) h
        simpa using this
      refine ⟨(a : K), a.2, ((s : R) : K), (s : R).2, hinv _ hsq, ?_⟩
      rw [← hxy, div_eq_div_iff hy0 (hne0 _ hsq)]
      linear_combination -hK

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDivOfCenterHeightLeOneStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
open Polynomial


theorem _root_.GlobalTheory.T.exists_div_of_center_height_le_one' : ∀ (K : Type) [Field K] (R : Subring K) [IsNoetherianRing R] [IsIntegrallyClosed R] [IsFractionRing R K] (E : ValuationSubring K), R ≤ E.toSubring → (∀ p : Ideal R, p.IsPrime → p ≠ ⊥ → (∀ r ∈ p, (r : K) ∈ E.nonunits) → ∀ r : R, (r : K) ∈ E.nonunits → r ∈ p) → ∀ e ∈ E, ∃ a ∈ R, ∃ s ∈ R, s⁻¹ ∈ E ∧ e = a / s := by
  first | exact @GlobalTheory.exists_div_of_center_height_le_one | exact GlobalTheory.exists_div_of_center_height_le_one | (intros; apply GlobalTheory.exists_div_of_center_height_le_one <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalFiniteTypeSubringInValuationSubringStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
open Polynomial


theorem _root_.GlobalTheory.T.exists_normal_finiteType_subring_in_valuationSubring : ∀ (K L : Type) [Field K] [Field L] (φ : K →+* L) (c : ℂ →+* K), (letI := φ.toAlgebra; FiniteDimensional K L) → ∀ (V : ValuationSubring L) (hc : ∀ a, φ (c a) ∈ V) (t : Finset L), (∀ x ∈ t, x ∈ V ∧ ∃ p : K[X], p.Monic ∧ (∀ i, p.coeff i ∈ V.comap φ) ∧ p.eval₂ φ x = 0) → (∀ s ∈ V, ∃ b ∈ Subring.closure (Set.range (φ.comp c) ∪ ↑t), ∃ d ∈ Subring.closure (Set.range (φ.comp c) ∪ ↑t), d ≠ 0 ∧ d⁻¹ ∈ V ∧ s = b / d) → ∃ R : Subring K, ∃ hcR : ∀ a, c a ∈ R, (c.codRestrict R hcR).FiniteType ∧ R ≤ (V.comap φ).toSubring ∧ IsNoetherianRing R ∧ IsIntegrallyClosed R ∧ IsFractionRing R K ∧ (∀ x ∈ t, ∃ p : R[X], p.Monic ∧ p.eval₂ (φ.comp R.subtype) x = 0) := by
  first | exact @GlobalTheory.exists_normal_finiteType_subring_of_valuationSubring | exact GlobalTheory.exists_normal_finiteType_subring_of_valuationSubring | (intros; apply GlobalTheory.exists_normal_finiteType_subring_of_valuationSubring <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZariskiDescentDvrTraceLocalisation

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
open Polynomial

namespace GlobalTheory

theorem zariski_descent_heart : ∀ (K L : Type) [Field K] [Field L] (φ : K →+* L) (c : ℂ →+* K), (letI := φ.toAlgebra; FiniteDimensional K L) → ∀ (V : ValuationSubring L) [IsDiscreteValuationRing V] (hc : ∀ a, φ (c a) ∈ V) (t : Finset L), (∀ x ∈ t, x ∈ V ∧ ∃ p : K[X], p.Monic ∧ (∀ i, p.coeff i ∈ V.comap φ) ∧ p.eval₂ φ x = 0) → (∀ s ∈ V, ∃ b ∈ Subring.closure (Set.range (φ.comp c) ∪ ↑t), ∃ d ∈ Subring.closure (Set.range (φ.comp c) ∪ ↑t), d ≠ 0 ∧ d⁻¹ ∈ V ∧ s = b / d) → (c.codRestrict (V.comap φ) hc).EssFiniteType := by
  have hA : ∀ (K L : Type) [Field K] [Field L] (φ : K →+* L) (c : ℂ →+* K), (letI := φ.toAlgebra; FiniteDimensional K L) → ∀ (V : ValuationSubring L) (hc : ∀ a, φ (c a) ∈ V) (t : Finset L), (∀ x ∈ t, x ∈ V ∧ ∃ p : K[X], p.Monic ∧ (∀ i, p.coeff i ∈ V.comap φ) ∧ p.eval₂ φ x = 0) → (∀ s ∈ V, ∃ b ∈ Subring.closure (Set.range (φ.comp c) ∪ ↑t), ∃ d ∈ Subring.closure (Set.range (φ.comp c) ∪ ↑t), d ≠ 0 ∧ d⁻¹ ∈ V ∧ s = b / d) → ∃ R : Subring K, ∃ hcR : ∀ a, c a ∈ R, (c.codRestrict R hcR).FiniteType ∧ R ≤ (V.comap φ).toSubring ∧ IsNoetherianRing R ∧ IsIntegrallyClosed R ∧ IsFractionRing R K ∧ (∀ x ∈ t, ∃ p : R[X], p.Monic ∧ p.eval₂ (φ.comp R.subtype) x = 0) := GlobalTheory.T.exists_normal_finiteType_subring_in_valuationSubring
  have hB : ∀ (K L : Type) [Field K] [Field L] (φ : K →+* L) (c : ℂ →+* K) (V : ValuationSubring L) [IsDiscreteValuationRing V] (R : Subring K) [IsIntegrallyClosed R], (∀ a, c a ∈ R) → R ≤ (V.comap φ).toSubring → ∀ t : Finset L, (∀ x ∈ t, x ∈ V ∧ ∃ p : R[X], p.Monic ∧ p.eval₂ (φ.comp R.subtype) x = 0) → (∀ s ∈ V, ∃ b ∈ Subring.closure (Set.range (φ.comp c) ∪ ↑t), ∃ d ∈ Subring.closure (Set.range (φ.comp c) ∪ ↑t), d ≠ 0 ∧ d⁻¹ ∈ V ∧ s = b / d) → ∀ p : Ideal R, p.IsPrime → p ≠ ⊥ → (∀ r ∈ p, (r : K) ∈ (V.comap φ).nonunits) → ∀ r : R, (r : K) ∈ (V.comap φ).nonunits → r ∈ p := GlobalTheory.T.height_le_one_of_goingDown_zariski
  have hC : ∀ (K : Type) [Field K] (R : Subring K) [IsNoetherianRing R] [IsIntegrallyClosed R] [IsFractionRing R K] (E : ValuationSubring K), R ≤ E.toSubring → (∀ p : Ideal R, p.IsPrime → p ≠ ⊥ → (∀ r ∈ p, (r : K) ∈ E.nonunits) → ∀ r : R, (r : K) ∈ E.nonunits → r ∈ p) → ∀ e ∈ E, ∃ a ∈ R, ∃ s ∈ R, s⁻¹ ∈ E ∧ e = a / s := GlobalTheory.T.exists_div_of_center_height_le_one'
  have hD : ∀ (K : Type) [Field K] (c : ℂ →+* K) (R : Subring K) (hcR : ∀ a, c a ∈ R) (E : ValuationSubring K) (hcE : ∀ a, c a ∈ E), R ≤ E.toSubring → (c.codRestrict R hcR).FiniteType → (∀ e ∈ E, ∃ a ∈ R, ∃ s ∈ R, s⁻¹ ∈ E ∧ e = a / s) → (c.codRestrict E hcE).EssFiniteType := GlobalTheory.T.essFiniteType_of_localization_finiteType_complex
  intro K L _ _ φ c hfin V _ hc t ht htV
  obtain ⟨R, hcR, hft, hRE, hnoeth, hic, hfr, htR⟩ := hA K L φ c hfin V hc t ht htV
  have hB' := hB K L φ c V R hcR hRE t (fun x hx => ⟨(ht x hx).1, htR x hx⟩) htV
  have hC' := hC K R (V.comap φ) hRE hB'
  exact hD K c R hcR (V.comap φ) hc hRE hft hC'
end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZariskiDescentDvrTraceLocalisationStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
open Polynomial


theorem _root_.GlobalTheory.T.zariski_descent_dvr_trace_localisation : ∀ (K L : Type) [Field K] [Field L] (φ : K →+* L) (c : ℂ →+* K), (letI := φ.toAlgebra; FiniteDimensional K L) → ∀ (V : ValuationSubring L) [IsDiscreteValuationRing V] (hc : ∀ a, φ (c a) ∈ V) (t : Finset L), (∀ x ∈ t, x ∈ V ∧ ∃ p : K[X], p.Monic ∧ (∀ i, p.coeff i ∈ V.comap φ) ∧ p.eval₂ φ x = 0) → (∀ s ∈ V, ∃ b ∈ Subring.closure (Set.range (φ.comp c) ∪ ↑t), ∃ d ∈ Subring.closure (Set.range (φ.comp c) ∪ ↑t), d ≠ 0 ∧ d⁻¹ ∈ V ∧ s = b / d) → (c.codRestrict (V.comap φ) hc).EssFiniteType := by
  first | exact @GlobalTheory.zariski_descent_heart | exact GlobalTheory.zariski_descent_heart | (intros; apply GlobalTheory.zariski_descent_heart <;> assumption)
end
end
