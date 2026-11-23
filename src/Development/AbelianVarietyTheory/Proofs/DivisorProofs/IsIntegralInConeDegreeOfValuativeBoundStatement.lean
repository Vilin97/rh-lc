module

public import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Definitions.Divisors.Multiplier
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.RingTheory.Adjoin.FG
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Definitions.Divisors.Multiplier
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
public import Mathlib.Data.Int.WithZero
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Sheaves.Init
import Mathlib.Algebra.Module.StablyFree.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralOfForallRealValuationLeOne

section

@[expose] public section

open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp GlobalTheory.DegVal GlobalTheory.CovTop ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped ENNReal NNReal

namespace GlobalTheory.DegVal

open IsDedekindDomain IsLocalRing

theorem exists_realValuation_of_discreteValuationSubring {Ω : Type} [Field Ω]
    (V : ValuationSubring Ω) [IsDiscreteValuationRing V] :
    ∃ ν : Valuation Ω ℝ≥0, (∀ x : V, ν (x : Ω) ≤ 1) ∧ ∀ x ∈ maximalIdeal V, ν (x : Ω) < 1 := by
  have hne : maximalIdeal V ≠ ⊥ := IsDiscreteValuationRing.not_a_field V
  let v : HeightOneSpectrum V := ⟨maximalIdeal V, inferInstance, hne⟩
  let hmono := (WithZeroMulInt.toNNReal_strictMono (e := 2) (by norm_num))
  refine ⟨Valuation.map { WithZeroMulInt.toNNReal (e := 2) (by norm_num) with
    monotone' := hmono.monotone } (v.valuation Ω),
    fun x => ?_, fun x hx => ?_⟩
  · have h := v.valuation_le_one (K := Ω) x
    have := hmono.monotone h
    simpa using this
  · have h := (v.valuation_lt_one_iff_mem (K := Ω) x).mpr hx
    have := hmono h
    simpa using this

theorem isIntegral_of_forall_realValuation_le_one : ∀ (K Ω : Type) [Field K] [CharZero K] [Field Ω] [Algebra K Ω], (⊤ : IntermediateField K Ω).FG → ∀ (A : Subalgebra K Ω), A.FG → ∀ t : Ω, (∀ ν : Valuation Ω ℝ≥0, (∀ a ∈ A, ν a ≤ 1) → ν t ≤ 1) → IsIntegral A t := by
  intro K Ω _ _ _ _ hfg A hA t ht
  by_contra hn
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact hn isIntegral_zero
  have : Algebra.EssFiniteType K Ω := IntermediateField.fg_top_iff.mp hfg
  have : Algebra.EssFiniteType A Ω := .of_comp K A Ω
  have : Algebra.FiniteType K A := (Subalgebra.fg_iff_finiteType A).mp hA
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
  have hic : IsIntegrallyClosedIn (integralClosure A Ω).toSubring Ω :=
    inferInstanceAs (IsIntegrallyClosedIn (integralClosure A Ω) Ω)
  obtain ⟨W, hW, htW⟩ := Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn
    (R := (integralClosure A Ω).toSubring) (x := t) hn
  have hinv : t⁻¹ ∈ W.nonunits := W.inv_mem_nonunits_iff.mpr (Or.inr htW)
  obtain ⟨V, h1, h2, -, h3⟩ := GlobalTheory.exists_discreteValuationSubring_of_valuationSubring (R := A) W
    (fun r => hW ((integralClosure A Ω).algebraMap_mem r))
    Set.finite_empty (Set.finite_singleton t⁻¹) (by simp) (by simpa using hinv)
    ⟨_, rfl, inv_ne_zero ht0⟩
  obtain ⟨ν, hν1, hνm⟩ := exists_realValuation_of_discreteValuationSubring V
  have hle : ν t ≤ 1 := ht ν fun a ha => hν1 ⟨a, h2 ⟨a, ha⟩⟩
  have hn3 : t⁻¹ ∈ V.nonunits := h3 _ rfl
  have htV : t⁻¹ ∈ V :=
    (V.valuation_le_one_iff _).mp (le_of_lt ((V.mem_nonunits_iff).mp hn3))
  have hm : (⟨t⁻¹, htV⟩ : V) ∈ maximalIdeal V :=
    (ValuationSubring.coe_mem_nonunits_iff (a := ⟨t⁻¹, htV⟩)).mp hn3
  have hlt : ν t⁻¹ < 1 := hνm _ hm
  have h1' : ν (t * t⁻¹) = 1 := by rw [mul_inv_cancel₀ ht0, map_one]
  rw [map_mul] at h1'
  have : ν t * ν t⁻¹ < 1 := lt_of_le_of_lt (mul_le_of_le_one_left zero_le hle) hlt
  exact absurd h1' this.ne

end GlobalTheory.DegVal
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralOfForallRealValuationLeOneStatement

section

@[expose] public section

open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp GlobalTheory.DegVal GlobalTheory.CovTop ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped ENNReal NNReal

theorem _root_.GlobalTheory.T.isIntegral_of_forall_valuation_le_one_of_fg : ∀ (K Ω : Type) [Field K] [CharZero K] [Field Ω] [Algebra K Ω], (⊤ : IntermediateField K Ω).FG → ∀ (A : Subalgebra K Ω), A.FG → ∀ t : Ω, (∀ ν : Valuation Ω ℝ≥0, (∀ a ∈ A, ν a ≤ 1) → ν t ≤ 1) → IsIntegral A t := by
  first | exact @GlobalTheory.DegVal.isIntegral_of_forall_realValuation_le_one | exact GlobalTheory.DegVal.isIntegral_of_forall_realValuation_le_one | (intros; apply GlobalTheory.DegVal.isIntegral_of_forall_realValuation_le_one <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralInConeDegreeOfValuativeBound

section

@[expose] public section

open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp GlobalTheory.DegVal GlobalTheory.CovTop ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped ENNReal NNReal

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DegVal.ValInt

theorem ratFunc_top_fg {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (h : (⊤ : IntermediateField K Ω).FG) :
    (⊤ : IntermediateField K (RatFunc Ω)).FG := by
  classical
  obtain ⟨S, hS⟩ := h
  refine ⟨insert RatFunc.X (S.image (algebraMap Ω (RatFunc Ω))), ?_⟩
  set F := IntermediateField.adjoin K
    (↑(insert RatFunc.X (S.image (algebraMap Ω (RatFunc Ω)))) : Set (RatFunc Ω)) with hF
  have hX : (RatFunc.X : RatFunc Ω) ∈ F := IntermediateField.subset_adjoin _ _ (by simp)
  have hc : ∀ a : Ω, algebraMap Ω (RatFunc Ω) a ∈ F := by
    intro a
    have ha : a ∈ IntermediateField.adjoin K (S : Set Ω) := hS ▸ IntermediateField.mem_top
    have hm : algebraMap Ω (RatFunc Ω) a ∈
        (IntermediateField.adjoin K (S : Set Ω)).map (IsScalarTower.toAlgHom K Ω (RatFunc Ω)) := ⟨a, ha, rfl⟩
    rw [IntermediateField.adjoin_map] at hm
    refine IntermediateField.adjoin.mono K _ _ ?_ hm
    rintro _ ⟨y, hy, rfl⟩
    exact Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hy))
  have hp : ∀ p : Polynomial Ω, algebraMap (Polynomial Ω) (RatFunc Ω) p ∈ F := by
    intro p
    induction p using Polynomial.induction_on with
    | C a => rw [RatFunc.algebraMap_C, ← RatFunc.algebraMap_eq_C]; exact hc a
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | monomial n a ih => rw [pow_succ, ← mul_assoc, map_mul, RatFunc.algebraMap_X]; exact mul_mem ih hX
  refine eq_top_iff.2 fun x _ => ?_
  rw [← RatFunc.num_div_denom x]
  exact div_mem (hp _) (hp _)

theorem isIntegral_of_map_subalgebra {K R L : Type} [Field K] [CommRing R] [Algebra K R] [CommRing L] [Algebra K L]
    (φ : R →ₐ[K] L) (hφ : Function.Injective φ) (B : Subalgebra K R) (y : R)
    (h : IsIntegral (B.map φ) (φ y)) : IsIntegral B y := by
  let e := B.equivMapOfInjective φ hφ
  obtain ⟨p, hm, hp⟩ := h
  refine ⟨p.map e.symm.toRingHom, hm.map _, hφ ?_⟩
  rw [map_zero, ← hp]
  change φ.toRingHom _ = _
  rw [Polynomial.hom_eval₂, Polynomial.eval₂_map]
  congr 1
  ext x
  exact congrArg Subtype.val (e.apply_symm_apply x)

theorem coneAlg_fg {K V Ω : Type} [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω]
    [FiniteDimensional K V] (ev : V →ₗ[K] Ω) : (coneAlg ev).FG := by
  let b := Module.finBasis K V
  let ψ : V →ₗ[K] Polynomial Ω := (LinearMap.mulLeft K (Polynomial.X : Polynomial Ω)) ∘ₗ
    (IsScalarTower.toAlgHom K Ω (Polynomial Ω)).toLinearMap ∘ₗ ev
  have e : coneAlg ev = Algebra.adjoin K (ψ '' Set.range b) := by
    rw [← Algebra.adjoin_span, ← Submodule.map_span, b.span_eq, Submodule.map_top]
    rfl
  exact Subalgebra.fg_def.2 ⟨_, (Set.finite_range b).image ψ, e.symm⟩

theorem isIntDeg_of_valBound : ∀ (K V Ω : Type) [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω]
    (ev : V →ₗ[K] Ω), CharZero K → FiniteDimensional K V → (⊤ : IntermediateField K Ω).FG →
    ∀ (τ : ℕ) (t : Ω), ValBound ev τ t → IsIntDeg ev τ t := by
  intro K V Ω _ _ _ _ _ ev hK hV hfg τ t hb
  have := hK
  have := hV
  let φ : Polynomial Ω →ₐ[K] RatFunc Ω := IsScalarTower.toAlgHom K (Polynomial Ω) (RatFunc Ω)
  have hφ : Function.Injective φ := RatFunc.algebraMap_injective Ω
  have hφa : ∀ p, φ p = algebraMap (Polynomial Ω) (RatFunc Ω) p := fun _ => rfl
  refine isIntegral_of_map_subalgebra φ hφ _ _ (GlobalTheory.T.isIntegral_of_forall_valuation_le_one_of_fg K (RatFunc Ω) (ratFunc_top_fg hfg)
    ((coneAlg ev).map φ) ((coneAlg_fg ev).map φ) _ fun μ hμ => ?_)
  have hK1 : ∀ a : K, a ≠ 0 → μ (algebraMap K (RatFunc Ω) a) = 1 := by
    intro a ha
    have h1 : μ (algebraMap K (RatFunc Ω) a) ≤ 1 := hμ _ (Subalgebra.algebraMap_mem _ a)
    have h2 : μ (algebraMap K (RatFunc Ω) a⁻¹) ≤ 1 := hμ _ (Subalgebra.algebraMap_mem _ a⁻¹)
    have h3 : μ (algebraMap K (RatFunc Ω) a) * μ (algebraMap K (RatFunc Ω) a⁻¹) = 1 := by
      rw [← map_mul, ← map_mul, mul_inv_cancel₀ ha, map_one, map_one]
    refine le_antisymm h1 ?_
    calc (1 : ℝ≥0) = _ := h3.symm
      _ ≤ μ (algebraMap K (RatFunc Ω) a) := mul_le_of_le_one_right zero_le h2
  obtain ⟨v, hv⟩ := hb (μ.comap (algebraMap Ω (RatFunc Ω))) fun a ha => by
    rw [Valuation.comap_apply, ← IsScalarTower.algebraMap_apply]; exact hK1 a ha
  rw [Valuation.comap_apply, Valuation.comap_apply] at hv
  have hXv : μ (RatFunc.X * algebraMap Ω (RatFunc Ω) (ev v)) ≤ 1 := by
    refine hμ _ (Subalgebra.mem_map.2 ⟨_, Algebra.subset_adjoin ⟨v, rfl⟩, ?_⟩)
    rw [hφa, map_mul, RatFunc.algebraMap_X, RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C]
  rw [hφa, map_mul, map_pow, RatFunc.algebraMap_X, RatFunc.algebraMap_C, ← RatFunc.algebraMap_eq_C, map_mul, map_pow]
  calc μ RatFunc.X ^ τ * μ (algebraMap Ω (RatFunc Ω) t)
      ≤ μ RatFunc.X ^ τ * μ (algebraMap Ω (RatFunc Ω) (ev v)) ^ τ := mul_le_mul_of_nonneg_left hv zero_le
    _ = μ (RatFunc.X * algebraMap Ω (RatFunc Ω) (ev v)) ^ τ := by rw [map_mul, mul_pow]
    _ ≤ 1 := pow_le_one₀ zero_le hXv

end GlobalTheory.DegVal.ValInt
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralInConeDegreeOfValuativeBoundStatement

section

@[expose] public section

open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp GlobalTheory.DegVal GlobalTheory.CovTop ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped ENNReal NNReal

theorem _root_.GlobalTheory.T.isIntegralInConeDegree_of_valuativeBound : ∀ (K V Ω : Type) [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω] (ev : V →ₗ[K] Ω), CharZero K → FiniteDimensional K V → (⊤ : IntermediateField K Ω).FG → ∀ (τ : ℕ) (t : Ω), ValBound ev τ t → IsIntDeg ev τ t := by
  first | exact @GlobalTheory.DegVal.ValInt.isIntDeg_of_valBound | exact GlobalTheory.DegVal.ValInt.isIntDeg_of_valBound | (intros; apply GlobalTheory.DegVal.ValInt.isIntDeg_of_valBound <;> assumption)
end
end
