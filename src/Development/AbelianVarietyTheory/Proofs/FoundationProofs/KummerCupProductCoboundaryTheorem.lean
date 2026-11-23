module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsFirstChernClassOfLineBundle
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.C1FieldNormSurjectiveStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CupKummerCoboundaryOfNormsStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InertFixesRootOfUnitRatio
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCochainCharacterGaloisInvariantClassStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerDivisorDescendsFunctionField
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerExponentOfGaloisElementIsKummerCharacter
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TsenTheoremStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ZetaMemRange
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.InertiaFixesAdjoinKummerRootsAndValuesEq

section

@[expose] public section

open GlobalTheory.NeedB Polynomial

namespace GlobalTheory.InertKummer

theorem valuation_eq_one_of_mem {Ω : Type} [Field Ω] (B : ValuationSubring Ω) {x : Ω} (hx : x ∈ B) (hx' : x⁻¹ ∈ B)
    (h0 : x ≠ 0) : B.valuation x = 1 := by
  have hu : IsUnit (⟨x, hx⟩ : B) :=
    isUnit_iff_exists_inv.mpr ⟨⟨x⁻¹, hx'⟩, Subtype.ext (mul_inv_cancel₀ h0)⟩
  exact (B.valuation_eq_one_iff ⟨x, hx⟩).mp hu

theorem inert_fixes_adjoin_and_kum_eq : ∀ (k K Ω : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k[X] K] [Algebra (RatFunc k) K]
    [IsScalarTower k[X] (RatFunc k) K] [FiniteDimensional (RatFunc k) K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (N : ℕ) (ζ : Ω), 0 < N → IsPrimitiveRoot ζ N →
    ∀ (a b : K) (α β : Ω), a ∈ FunctionField.ringOfIntegers k K → a⁻¹ ∈ FunctionField.ringOfIntegers k K →
      b ∈ FunctionField.ringOfIntegers k K → b⁻¹ ∈ FunctionField.ringOfIntegers k K → a ≠ 0 → b ≠ 0 →
      α ^ N = algebraMap K Ω a → β ^ N = algebraMap K Ω b →
      ∀ θ θ₀ : Ω, θ ≠ 0 → θ₀ ≠ 0 → θ ^ N ∈ IntermediateField.adjoin K {α, β} → θ₀ ^ N ∈ Set.range (algebraMap K Ω) →
      ∀ B : ValuationSubring Ω, GlobalTheory.NeedB.Over (FunctionField.ringOfIntegers k K).toSubring B →
      ∀ g : Ω ≃ₐ[K] Ω, GlobalTheory.NeedB.Inert B g → ∀ c ∈ IntermediateField.adjoin K {α, β}, c ≠ 0 →
        B.valuation (θ ^ N / (θ₀ ^ N * c ^ N)) = 1 →
        g ∈ (IntermediateField.adjoin K {α, β}).fixingSubgroup ∧ GlobalTheory.NeedB.kum (N := N) ζ θ g = GlobalTheory.NeedB.kum ζ θ₀ g := by
  intro k K Ω _ _ _ _ _ _ _ _ _ _ _ N ζ hN hζ a b α β ha ha' hb hb' ha0 hb0 hα hβ θ θ₀ hθ hθ₀ hθE hθ₀K B hB g hg c hcE hc0 hv
  haveI : NeZero N := ⟨hN.ne'⟩

  have hunit : ∀ x : K, x ∈ FunctionField.ringOfIntegers k K → x⁻¹ ∈ FunctionField.ringOfIntegers k K → x ≠ 0 →
      B.valuation (algebraMap K Ω x) = 1 := by
    intro x hx hx' hx0
    refine valuation_eq_one_of_mem B (hB x hx) ?_ ((_root_.map_ne_zero _).mpr hx0)
    rw [← map_inv₀]; exact hB _ hx'

  have hNK0 : (N : K) ≠ 0 := by
    have : ((algebraMap k[X] K).comp Polynomial.C) (N : k) = (N : K) := map_natCast _ _
    rw [← this]; exact (_root_.map_ne_zero _).mpr (by exact_mod_cast hN.ne')
  have hNmem : (N : K) ∈ FunctionField.ringOfIntegers k K := Subalgebra.natCast_mem _ N
  have hNinv : (N : K)⁻¹ ∈ FunctionField.ringOfIntegers k K := by
    have : ((algebraMap k[X] K).comp Polynomial.C) ((N : k)⁻¹) = (N : K)⁻¹ := by
      rw [map_inv₀, map_natCast]
    rw [← this]
    exact Subalgebra.algebraMap_mem _ _
  have hvN : B.valuation (N : Ω) = 1 := by
    have := hunit _ hNmem hNinv hNK0
    rwa [map_natCast] at this

  have hroot : ∀ (γ : Ω) (x : K), x ∈ FunctionField.ringOfIntegers k K → x⁻¹ ∈ FunctionField.ringOfIntegers k K → x ≠ 0 →
      γ ^ N = algebraMap K Ω x → g γ = γ := by
    intro γ x hx hx' hx0 hγ
    refine GlobalTheory.inert_fixes_root_of_unit_ratio K Ω B g N 1 γ hN hvN hg (map_one g) one_ne_zero ?_ ?_
    · rw [hγ]; exact g.commutes x
    · rw [one_pow, div_one, hγ]; exact hunit x hx hx' hx0
  have hgα : g α = α := hroot α a ha ha' ha0 hα
  have hgβ : g β = β := hroot β b hb hb' hb0 hβ
  have hfix : g ∈ (IntermediateField.adjoin K {α, β}).fixingSubgroup := by
    have hz : Subgroup.zpowers g ≤ (IntermediateField.adjoin K {α, β}).fixingSubgroup := by
      rw [← IntermediateField.le_iff_le, IntermediateField.adjoin_le_iff]
      intro x hx
      have hgx : g x = x := by
        rcases hx with rfl | hx
        · exact hgα
        · rw [Set.mem_singleton_iff.mp hx]; exact hgβ
      have hs : g ∈ MulAction.stabilizer (Ω ≃ₐ[K] Ω) x := hgx
      intro f
      have hf : (f : Ω ≃ₐ[K] Ω) ∈ MulAction.stabilizer (Ω ≃ₐ[K] Ω) x := Subgroup.zpowers_le.mpr hs f.2
      exact hf
    exact hz (Subgroup.mem_zpowers g)
  have hfixE : ∀ x ∈ IntermediateField.adjoin K {α, β}, g x = x := fun x hx => hfix ⟨x, hx⟩
  refine ⟨hfix, ?_⟩

  have hgθN : g (θ ^ N) = θ ^ N := hfixE _ hθE
  have hgθ₀N : g (θ₀ ^ N) = θ₀ ^ N := by
    obtain ⟨y, hy⟩ := hθ₀K; rw [← hy]; exact g.commutes y
  have hq : g (θ / θ₀) = θ / θ₀ := by
    refine GlobalTheory.inert_fixes_root_of_unit_ratio K Ω B g N c (θ / θ₀) hN hvN hg (hfixE c hcE) hc0 ?_ ?_
    · rw [div_pow, map_div₀, hgθN, hgθ₀N]
    · rw [div_pow, div_div]; exact hv
  have hq' : g θ₀ = g θ * θ₀ / θ := by
    rw [map_div₀] at hq
    have hgθ₀0 : g θ₀ ≠ 0 := (_root_.map_ne_zero g).mpr hθ₀
    rw [div_eq_div_iff hgθ₀0 hθ₀] at hq
    rw [eq_div_iff hθ, hq, mul_comm]

  have hξ : (g θ / θ) ^ N = 1 := by
    rw [div_pow, ← map_pow, hgθN, div_self (pow_ne_zero _ hθ)]
  obtain ⟨i, hiN, hi⟩ := hζ.eq_pow_of_pow_eq_one hξ
  have hval : ((i : ZMod N)).val = i := ZMod.val_cast_of_lt hiN
  have h1 : g θ = ζ ^ ((i : ZMod N)).val * θ := by
    rw [hval, hi]; field_simp
  have h2 : g θ₀ = ζ ^ ((i : ZMod N)).val * θ₀ := by
    rw [hq', h1]; field_simp
  rw [kum_eq_of hζ hθ _ h1, kum_eq_of hζ hθ₀ _ h2]

end GlobalTheory.InertKummer
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.InertiaFixesAdjoinKummerRootsAndValuesEqStatement

section

@[expose] public section

open GlobalTheory.NeedB Polynomial

theorem _root_.GlobalTheory.T.inertia_fixes_adjoin_kummer_roots_and_values_eq : ∀ (k K Ω : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k[X] K] [Algebra (RatFunc k) K]
    [IsScalarTower k[X] (RatFunc k) K] [FiniteDimensional (RatFunc k) K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (N : ℕ) (ζ : Ω), 0 < N → IsPrimitiveRoot ζ N →
    ∀ (a b : K) (α β : Ω), a ∈ FunctionField.ringOfIntegers k K → a⁻¹ ∈ FunctionField.ringOfIntegers k K →
      b ∈ FunctionField.ringOfIntegers k K → b⁻¹ ∈ FunctionField.ringOfIntegers k K → a ≠ 0 → b ≠ 0 →
      α ^ N = algebraMap K Ω a → β ^ N = algebraMap K Ω b →
      ∀ θ θ₀ : Ω, θ ≠ 0 → θ₀ ≠ 0 → θ ^ N ∈ IntermediateField.adjoin K {α, β} → θ₀ ^ N ∈ Set.range (algebraMap K Ω) →
      ∀ B : ValuationSubring Ω, GlobalTheory.NeedB.Over (FunctionField.ringOfIntegers k K).toSubring B →
      ∀ g : Ω ≃ₐ[K] Ω, GlobalTheory.NeedB.Inert B g → ∀ c ∈ IntermediateField.adjoin K {α, β}, c ≠ 0 →
        B.valuation (θ ^ N / (θ₀ ^ N * c ^ N)) = 1 →
        g ∈ (IntermediateField.adjoin K {α, β}).fixingSubgroup ∧ GlobalTheory.NeedB.kum (N := N) ζ θ g = GlobalTheory.NeedB.kum ζ θ₀ g := by
  first | exact @GlobalTheory.InertKummer.inert_fixes_adjoin_and_kum_eq | exact GlobalTheory.InertKummer.inert_fixes_adjoin_and_kum_eq | (intros; apply GlobalTheory.InertKummer.inert_fixes_adjoin_and_kum_eq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerDivisorDescendsFunctionFieldStatement

section

@[expose] public section

open GlobalTheory.NeedB Polynomial

theorem _root_.GlobalTheory.T.kummer_divisor_descends_functionField : ∀ (k K Ω : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k[X] K] [Algebra (RatFunc k) K]
    [IsScalarTower k[X] (RatFunc k) K] [FiniteDimensional (RatFunc k) K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (N : ℕ) (ζ : Ω), 0 < N → IsPrimitiveRoot ζ N →
    ∀ (a b : K) (α β : Ω), a ∈ FunctionField.ringOfIntegers k K → a⁻¹ ∈ FunctionField.ringOfIntegers k K →
      b ∈ FunctionField.ringOfIntegers k K → b⁻¹ ∈ FunctionField.ringOfIntegers k K → a ≠ 0 → b ≠ 0 →
      α ^ N = algebraMap K Ω a → β ^ N = algebraMap K Ω b →
      ∀ θ : Ω, θ ≠ 0 → θ ^ N ∈ IntermediateField.adjoin K {α, β} →
      (∀ s : Ω ≃ₐ[K] Ω, ∃ u ∈ IntermediateField.adjoin K {α, β}, u ≠ 0 ∧ s (θ ^ N) = θ ^ N * u ^ N) →
      ∃ f : K, f ≠ 0 ∧ ∀ B : ValuationSubring Ω, GlobalTheory.NeedB.Over (FunctionField.ringOfIntegers k K).toSubring B →
        ∃ c ∈ IntermediateField.adjoin K {α, β}, c ≠ 0 ∧ B.valuation (θ ^ N / (algebraMap K Ω f * c ^ N)) = 1 := by
  first | exact @GlobalTheory.KummerCob.divisor_descends | exact GlobalTheory.KummerCob.divisor_descends | (intros; apply GlobalTheory.KummerCob.divisor_descends <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCupProductCoboundaryTheorem

section

@[expose] public section

open GlobalTheory.NeedB Polynomial

namespace GlobalTheory.KummerCob

theorem cup_eq_coboundary_vanishing_on_inertia : ∀ (k K Ω : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k[X] K] [Algebra (RatFunc k) K]
    [IsScalarTower k[X] (RatFunc k) K] [FiniteDimensional (RatFunc k) K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (N : ℕ) (ζ : Ω), 0 < N → IsPrimitiveRoot ζ N →
    ∀ (a b : K) (α β : Ω), a ∈ FunctionField.ringOfIntegers k K → a⁻¹ ∈ FunctionField.ringOfIntegers k K →
      b ∈ FunctionField.ringOfIntegers k K → b⁻¹ ∈ FunctionField.ringOfIntegers k K → a ≠ 0 → b ≠ 0 →
      α ^ N = algebraMap K Ω a → β ^ N = algebraMap K Ω b →
      ∃ η : (Ω ≃ₐ[K] Ω) → ZMod N, IsLocallyConstant η ∧
        (∀ g h, kum ζ α g * kum ζ β h = η h - η (g * h) + η g) ∧
        ∀ B : ValuationSubring Ω, Over (FunctionField.ringOfIntegers k K).toSubring B → ∀ g, Inert B g → η g = 0 := by
  intro k K Ω _ _ _ _ _ _ _ _ _ _ _ N ζ hN hζ a b α β haA hai hbA hbi ha0 hb0 hα hβ
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  haveI : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap (RatFunc k) K).injective
  obtain ⟨z, hz⟩ := zeta_mem_range k K Ω N ζ hN hζ
  have hfix : ∀ g : Ω ≃ₐ[K] Ω, g ζ = ζ := fun g => by rw [← hz]; exact g.commutes z
  have hC1 : IsFirstChernClassOfLineBundle K := GlobalTheory.T.tsen_theorem k K
  have hnorm : ∀ (L : IntermediateField K Ω), FiniteDimensional K L → ∀ c : K, c ≠ 0 →
      ∃ x : L, Algebra.norm K x = c := fun L _ c hc => GlobalTheory.T.exists_algebra_norm_eq_of_isFirstChernClass K L hC1 c hc
  obtain ⟨η₀, hη₀c, hη₀⟩ := GlobalTheory.T.exists_locallyConstant_kum_cup_coboundary_of_norm_surj K Ω N ζ hN hζ hfix hnorm a b α β ha0 hb0 hα hβ
  obtain ⟨θ, hθ0, hθE, hθη, hθs⟩ :=
    GlobalTheory.T.kummer_cochain_character_galoisInvariant_class K Ω N ζ hN hζ hfix a b α β ha0 hb0 hα hβ η₀ hη₀c hη₀
  obtain ⟨f, hf0, hfB⟩ := GlobalTheory.T.kummer_divisor_descends_functionField k K Ω N ζ hN hζ a b α β haA hai hbA hbi ha0 hb0 hα hβ θ hθ0 hθE hθs
  obtain ⟨θ₀, hθ₀⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap K Ω f) hN
  have hθ₀0 : θ₀ ≠ 0 := by
    rintro rfl
    rw [zero_pow hN.ne'] at hθ₀
    exact hf0 ((map_eq_zero_iff _ (algebraMap K Ω).injective).1 hθ₀.symm)
  obtain ⟨hk0c, -, hk0add, -⟩ :=
    GlobalTheory.NeedB.KumLemma.kummer_character_main K Ω N ζ θ₀ hN hζ hfix hθ₀0 ⟨f, hθ₀.symm⟩
  refine ⟨fun g => η₀ g - kum ζ θ₀ g, hη₀c.sub hk0c, ?_, ?_⟩
  · intro g h
    simp only
    rw [hη₀ g h, hk0add g h]
    ring
  · intro B hB g hg
    obtain ⟨c, hcE, hc0, hcv⟩ := hfB B hB
    rw [← hθ₀] at hcv
    obtain ⟨hgE, hk⟩ := GlobalTheory.T.inertia_fixes_adjoin_kummer_roots_and_values_eq k K Ω N ζ hN hζ a b α β haA hai hbA hbi ha0 hb0 hα hβ θ θ₀ hθ0 hθ₀0 hθE
      ⟨f, hθ₀.symm⟩ B hB g hg c hcE hc0 hcv
    show η₀ g - kum ζ θ₀ g = 0
    rw [hθη g hgE, hk, sub_self]

theorem thmA : GlobalTheory.NeedB.ThmA := by
  intro k K Ω _ _ _ _ _ _ _ _ _ _ _ N ζ hN hζ a b α β ha0 hb0 haA hai hbA hbi hα hβ
  haveI : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  obtain ⟨z, hz⟩ := zeta_mem_range k K Ω N ζ hN hζ
  have hfix : ∀ g : Ω ≃ₐ[K] Ω, g ζ = ζ := fun g => by rw [← hz]; exact g.commutes z
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [zero_pow hN.ne'] at hα
    exact ha0 ((map_eq_zero_iff _ (algebraMap K Ω).injective).1 hα.symm)
  have hβ0 : β ≠ 0 := by
    rintro rfl
    rw [zero_pow hN.ne'] at hβ
    exact hb0 ((map_eq_zero_iff _ (algebraMap K Ω).injective).1 hβ.symm)
  obtain ⟨hαc, -, hαadd, -⟩ :=
    GlobalTheory.NeedB.KumLemma.kummer_character_main K Ω N ζ α hN hζ hfix hα0 ⟨a, hα.symm⟩
  obtain ⟨hβc, -, hβadd, -⟩ :=
    GlobalTheory.NeedB.KumLemma.kummer_character_main K Ω N ζ β hN hζ hfix hβ0 ⟨b, hβ.symm⟩
  exact ⟨hαadd, hαc, hβadd, hβc,
    cup_eq_coboundary_vanishing_on_inertia k K Ω N ζ hN hζ a b α β haA hai hbA hbi ha0 hb0 hα hβ⟩

end GlobalTheory.KummerCob
end
end
