module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMapThetaExpansionAllTraitsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralThetaFamilyPrescribedLeadingTermStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaNormalisationConstantOrigin
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeightZeroSectionNonzeroAtOrigin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitExpansionScalarsRescaleStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSectionNormalisedUnitAtTraitsStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaNormalisationConstantOriginStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_thetaNormalisationConstant_origin : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (k : ℕ), 1 ≤ k → ∀ b₀ : D.toPre.SecB k 0, eSec D.toPre.P.A (closedPoint R) ∈ nonzeroLocus b₀ → ∀ F₀ : IntFam (maximalIdeal R) D.toPre k, F₀.Lead 0 b₀ → ∀ s : SecK C.P.L.L C.α k, ∃ c₁ c₂ : R, c₂ ≠ 0 ∧ ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (a b : W), a ≠ 0 → b ≠ 0 → T.Exp a b s F₀ → ∃ u : Wˣ, T.φ c₂ * (u : W) * a = T.φ c₁ * b := by
  first | exact @GlobalTheory.Mum.exists_norm_const | exact GlobalTheory.Mum.exists_norm_const | (intros; apply GlobalTheory.Mum.exists_norm_const <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeightZeroSectionNonzeroAtOriginStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_weightZero_section_nonzero_at_origin : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)), ∃ k₀ : ℕ, ∀ k ≥ k₀, ∃ b : D.toPre.SecB k 0, eSec D.toPre.P.A (closedPoint R) ∈ nonzeroLocus b := by
  first | exact @GlobalTheory.Mum.exists_secB_zero_nonzero_origin | exact GlobalTheory.Mum.exists_secB_zero_nonzero_origin | (intros; apply GlobalTheory.Mum.exists_secB_zero_nonzero_origin <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOriginNormalisationUnitAtTraits

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_unit_normalisation : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D), ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ Φ : IntFam (maximalIdeal R) D.toPre k → SecK C.P.L.L C.α k, (∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ a b : W, a ≠ 0 ∧ b ≠ 0 ∧ ∀ F, T.Exp a b (Φ F) F) → ∃ Φ' : IntFam (maximalIdeal R) D.toPre k → SecK C.P.L.L C.α k, ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ u : Wˣ, ∀ F, T.Exp 1 u (Φ' F) F := by
  intro R _ _ _ hR D C
  obtain ⟨k₁, hk₁⟩ := GlobalTheory.T.exists_weightZero_section_nonzero_at_origin R hR D
  refine ⟨max k₁ 1, fun k hk Φ hΦ => ?_⟩
  obtain ⟨b₀, hb₀⟩ := hk₁ k (le_of_max_le_left hk)
  have hk1 : 1 ≤ k := le_of_max_le_right hk
  obtain ⟨F₀, hF₀⟩ := (GlobalTheory.T.exists_integralThetaFamily_prescribed_leadingTerm R hR D).2 k hk1 b₀
  obtain ⟨c₁, c₂, hc₂, hc⟩ := GlobalTheory.T.exists_thetaNormalisationConstant_origin R hR D C k hk1 b₀ hb₀ F₀ hF₀ (Φ F₀)
  refine ⟨fun F => scal C.A.A.hom (algebraMap R (FractionRing R) c₁ / algebraMap R (FractionRing R) c₂) • Φ F,
    fun W _ _ _ T => ?_⟩
  obtain ⟨a, b, ha, hb, hE⟩ := hΦ W T
  obtain ⟨u, hu⟩ := hc W T a b ha hb (hE F₀)
  exact ⟨u, fun F => GlobalTheory.T.trait_expansionScalars_rescale R hR D C W T k (Φ F) F a b u c₁ c₂ ha hc₂ hu (hE F)⟩

end GlobalTheory.Mum
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOriginNormalisationUnitAtTraitsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_origin_normalisation_unit_at_traits : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D), ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ Φ : IntFam (maximalIdeal R) D.toPre k → SecK C.P.L.L C.α k, (∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ a b : W, a ≠ 0 ∧ b ≠ 0 ∧ ∀ F, T.Exp a b (Φ F) F) → ∃ Φ' : IntFam (maximalIdeal R) D.toPre k → SecK C.P.L.L C.α k, ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ u : Wˣ, ∀ F, T.Exp 1 u (Φ' F) F := by
  first | exact @GlobalTheory.Mum.exists_unit_normalisation | exact GlobalTheory.Mum.exists_unit_normalisation | (intros; apply GlobalTheory.Mum.exists_unit_normalisation <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsTailRest

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.SecsDesc

theorem assemble (hE : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (j : ℕ), ∃ Φ : IntFam (maximalIdeal R) D.toPre (C.n ^ j) → SecK C.P.L.L C.α (C.n ^ j), ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ a b : W, a ≠ 0 ∧ b ≠ 0 ∧ ∀ F, T.Exp a b (Φ F) F) (hN : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D), ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ Φ : IntFam (maximalIdeal R) D.toPre k → SecK C.P.L.L C.α k, (∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ a b : W, a ≠ 0 ∧ b ≠ 0 ∧ ∀ F, T.Exp a b (Φ F) F) → ∃ Φ' : IntFam (maximalIdeal R) D.toPre k → SecK C.P.L.L C.α k, ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ u : Wˣ, ∀ F, T.Exp 1 u (Φ' F) F) (hT : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (m : ℕ), Odd m → ∀ Φ : IntFam (maximalIdeal R) D.toPre (m ^ 2) → SecK C.P.L.L C.α (m ^ 2), (∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ u : Wˣ, ∀ F, T.Exp 1 u (Φ F) F) → ∀ F₁ : IntFam (maximalIdeal R) D.toPre 1, ∃ θ : SecK C.P.L.L C.α 1, ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ u : Wˣ, T.Exp 1 u θ F₁) : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D), (∃ j₀ : ℕ, ∀ j ≥ j₀, ∃ Φ : IntFam (maximalIdeal R) D.toPre (C.n ^ j) → SecK C.P.L.L C.α (C.n ^ j), ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ u : Wˣ, ∀ F, T.Exp 1 u (Φ F) F) ∧ ∀ F₁ : IntFam (maximalIdeal R) D.toPre 1, ∃ θ : SecK C.P.L.L C.α 1, ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ u : Wˣ, T.Exp 1 u θ F₁ := by
  intro R _ _ _ hR D C
  obtain ⟨k₀, hk₀⟩ := hN R hR D C
  have hn : 1 < C.n := C.n_prime.one_lt
  have part1 : ∀ j ≥ k₀, ∃ Φ : IntFam (maximalIdeal R) D.toPre (C.n ^ j) → SecK C.P.L.L C.α (C.n ^ j),
      ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ u : Wˣ, ∀ F, T.Exp 1 u (Φ F) F := by
    intro j hj
    obtain ⟨Φ, hΦ⟩ := hE R hR D C j
    exact hk₀ (C.n ^ j) (hj.trans (Nat.lt_pow_self hn).le) Φ hΦ
  refine ⟨⟨k₀, part1⟩, fun F₁ => ?_⟩
  have key : ∀ k, k = C.n ^ (k₀ * 2) → ∃ Φ : IntFam (maximalIdeal R) D.toPre k → SecK C.P.L.L C.α k,
      ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ u : Wˣ, ∀ F, T.Exp 1 u (Φ F) F := by
    rintro k rfl
    exact part1 _ (Nat.le_mul_of_pos_right _ (by norm_num))
  obtain ⟨Φ, hΦ⟩ := key ((C.n ^ k₀) ^ 2) (pow_mul _ _ _).symm
  exact hT R hR D C (C.n ^ k₀) (C.n_odd.pow) Φ hΦ F₁

end GlobalTheory.Mum.SecsDesc
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSecsOfIntFam

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.Mum.exists_secs_of_intFam : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D), (∃ j₀ : ℕ, ∀ j ≥ j₀, ∃ Φ : IntFam (maximalIdeal R) D.toPre (C.n ^ j) → SecK C.P.L.L C.α (C.n ^ j), ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ u : Wˣ, ∀ F, T.Exp 1 u (Φ F) F) ∧ ∀ F₁ : IntFam (maximalIdeal R) D.toPre 1, ∃ θ : SecK C.P.L.L C.α 1, ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ u : Wˣ, T.Exp 1 u θ F₁ :=
  GlobalTheory.Mum.SecsDesc.assemble GlobalTheory.T.exists_map_thetaExpansion_all_traits GlobalTheory.T.exists_origin_normalisation_unit_at_traits GlobalTheory.T.exists_thetaSection_normalised_unit_at_traits
end
end
