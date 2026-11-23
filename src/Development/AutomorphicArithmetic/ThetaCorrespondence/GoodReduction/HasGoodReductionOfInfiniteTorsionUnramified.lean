module

import Mathlib
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInjectivePointsLargerFieldGalois
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.PullbackDegree.EpsPullbackFst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardAbelianVarietyTorsionSepClosedStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.GoodReduction.HasGoodReductionOfInertiaFixed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRelativeDimensionAbelianVarietyField
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
import Development.AbelianVarietyTheory.Definitions.Divisors.MapSmulOfIsHausdorff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFieldOfValues
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertiaFixedFieldValuationRingStrictlyHenselian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasGoodReductionOfManyRationalTorsionPointsStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRelativeDimensionAbelianVarietyFieldStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_relativeDimension_abelianVariety_field : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∃ g : ℕ, SmoothOfRelativeDimension g A.hom := by
  first | exact @GlobalTheory.AbVarRelDim.exists_relDim | exact GlobalTheory.AbVarRelDim.exists_relDim | (intros; apply GlobalTheory.AbVarRelDim.exists_relDim <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFixedFieldPointOfFixedBySubgroup

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Published.AbVarRed

theorem exists_fixedField_point (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (H : Subgroup (Ω ≃ₐ[K] Ω))
    (A : Over (Sp K)) (_ : LocallyOfFiniteType A.hom) (x : ptOver K Ω ⟶ A)
    (hx : ∀ σ ∈ H, specAut σ ≫ x = x) :
    ∃ y : Sp (IntermediateField.fixedField H) ⟶ A.left,
      spMap (algebraMap (IntermediateField.fixedField H) Ω) ≫ y = x.left := by
  obtain ⟨E, hE1, hE2, -⟩ := GlobalTheory.SS.exists_fieldOfValues A.left Ω x.left
  have hid : spMap (RingHom.id Ω) = 𝟙 (Sp Ω) := by
    rw [← Spec.map_id]
    congr 1
  have hfix : ∀ c ∈ E, ∀ σ ∈ H, σ c = c := by
    intro c hc σ hσ
    have h1 : spMap (σ : Ω →+* Ω) ≫ x.left = spMap (RingHom.id Ω) ≫ x.left := by
      rw [hid, Category.id_comp]
      exact congrArg CommaMorphism.left (hx σ hσ)
    exact (hE1 _ _).1 h1 c hc
  refine (hE2 (IntermediateField.fixedField H) (algebraMap (IntermediateField.fixedField H) Ω)).1 ?_
  intro c hc
  exact ⟨⟨c, fun σ => hfix c hc σ σ.2⟩, rfl⟩

end GlobalTheory.Published.AbVarRed
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFixedFieldPointOfFixedBySubgroupStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_fixedField_point_of_fixed_by_subgroup : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (H : Subgroup (Ω ≃ₐ[K] Ω)) (A : Over (Sp K)), LocallyOfFiniteType A.hom → ∀ x : ptOver K Ω ⟶ A, (∀ σ ∈ H, specAut σ ≫ x = x) → ∃ y : Sp (IntermediateField.fixedField H) ⟶ A.left, spMap (algebraMap (IntermediateField.fixedField H) Ω) ≫ y = x.left := by
  first | exact @GlobalTheory.Published.AbVarRed.exists_fixedField_point | exact GlobalTheory.Published.AbVarRed.exists_fixedField_point | (intros; apply GlobalTheory.Published.AbVarRed.exists_fixedField_point <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertiaFixedFieldValuationRingStrictlyHenselianStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.inertiaFixedField_valuationRing_strictlyHenselian : ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [PerfectField (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring → GlobalTheory.SS.SH (V.comap (algebraMap (IntermediateField.fixedField (inertia K V)) Ω)) (IntermediateField.fixedField (inertia K V)) ∧ ∃ f : R →+* V.comap (algebraMap (IntermediateField.fixedField (inertia K V)) Ω), (∀ r : R, ((f r : IntermediateField.fixedField (inertia K V)) : Ω) = algebraMap K Ω (algebraMap R K r)) ∧ ∀ π : R, Irreducible π → Irreducible (f π) := by
  first | exact @GlobalTheory.InertiaFixedSH.inertiaFixed_strictlyHenselian | exact GlobalTheory.InertiaFixedSH.inertiaFixed_strictlyHenselian | (intros; apply GlobalTheory.InertiaFixedSH.inertiaFixed_strictlyHenselian <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.GoodReduction.HasGoodReductionOfInfiniteTorsionUnramified

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace UpperTheory.Lit.Nos.C6
open GlobalTheory

def basePtEquiv {K L : Type} [Field K] [Field L] [Algebra K L] (A : Over (Sp K)) [GrpObj A] :
    (ptOver K L ⟶ A) ≃* (𝟙_ (Over (Sp L)) ⟶ (Over.pullback (spMap (algebraMap K L))).obj A) :=
  let e : (Over.map (spMap (algebraMap K L))).obj (𝟙_ (Over (Sp L))) ≅ ptOver K L :=
    Over.isoMk (Iso.refl _) (by
      change 𝟙 _ ≫ spMap (algebraMap K L) = 𝟙 _ ≫ spMap (algebraMap K L)
      rfl)
  { toFun := fun x => (Over.mapPullbackAdj (spMap (algebraMap K L))).homEquiv _ A (e.hom ≫ x)
    invFun := fun y => e.inv ≫ ((Over.mapPullbackAdj (spMap (algebraMap K L))).homEquiv _ A).symm y
    left_inv := fun x => by simp
    right_inv := fun y => by simp
    map_mul' := fun x y => by
      rw [MonObj.comp_mul, ReciprocityTheory.ChartRestriction.G.Out.UBC.homEquiv_mul] }

def fixedPtHom {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (H : Subgroup (Ω ≃ₐ[K] Ω))
    (A : Over (Sp K)) [GrpObj A] :
    (ptOver K (IntermediateField.fixedField H) ⟶ A) →* (ptOver K Ω ⟶ A) :=
  MonoidHom.mk' (fun x => ptOverMap (IntermediateField.val _) ≫ x) fun x y => MonObj.comp_mul _ x y

theorem fixedPtHom_injective {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (H : Subgroup (Ω ≃ₐ[K] Ω))
    (A : Over (Sp K)) [GrpObj A] : Function.Injective (fixedPtHom H A) := by
  intro x y e
  have := epi_ptOverMap (IntermediateField.val (IntermediateField.fixedField H))
  exact Over.OverMorphism.ext ((cancel_epi (ptOverMap (IntermediateField.val _)).left).1
    (by simpa using congrArg (fun q => q.left) (show ptOverMap (IntermediateField.val _) ≫ x =
      ptOverMap (IntermediateField.val _) ≫ y from e)))

theorem card_torsion_fixedField {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (H : Subgroup (Ω ≃ₐ[K] Ω))
    (A : Over (Sp K)) [GrpObj A] (hA : LocallyOfFiniteType A.hom) (m : ℕ)
    (hfix : ∀ σ ∈ H, ∀ x : ptOver K Ω ⟶ A, x ^ m = 1 → specAut σ ≫ x = x) :
    Nat.card {x : 𝟙_ (Over (Sp (IntermediateField.fixedField H))) ⟶
        (Over.pullback (spMap (algebraMap K (IntermediateField.fixedField H)))).obj A // x ^ m = 1} =
      Nat.card {x : ptOver K Ω ⟶ A // x ^ m = 1} := by
  have e1 := Equiv.subtypeEquiv (basePtEquiv (K := K) (L := IntermediateField.fixedField H) A).symm.toEquiv
    (p := fun x => x ^ m = 1) (q := fun y => y ^ m = 1) (fun x => by
      change x ^ m = 1 ↔ (basePtEquiv A).symm x ^ m = 1
      rw [← map_pow, MulEquiv.map_eq_one_iff])
  rw [Nat.card_congr e1]
  refine Nat.card_eq_of_bijective (fun y => ⟨fixedPtHom H A y.1, by rw [← map_pow, y.2, map_one]⟩) ⟨?_, ?_⟩
  · intro y y' h
    exact Subtype.ext (fixedPtHom_injective H A (congrArg Subtype.val h))
  · rintro ⟨z, hz⟩
    obtain ⟨y, hy⟩ := GlobalTheory.T.exists_fixedField_point_of_fixed_by_subgroup K Ω H A hA z (fun σ hσ => hfix σ hσ z hz)
    have hep := epi_ptOverMap (IntermediateField.val (IntermediateField.fixedField H))
    have hj : (ptOverMap (IntermediateField.val (IntermediateField.fixedField H))).left =
        spMap (algebraMap (IntermediateField.fixedField H) Ω) := rfl
    rw [hj] at hep
    have hover : y ≫ A.hom = spMap (algebraMap K (IntermediateField.fixedField H)) := by
      refine (cancel_epi (spMap (algebraMap (IntermediateField.fixedField H) Ω))).1 ?_
      rw [← Category.assoc, hy, Over.w z]
      change spMap (algebraMap K Ω) = _
      rw [← Spec.map_comp]
      congr 1
    let y' : ptOver K (IntermediateField.fixedField H) ⟶ A := Over.homMk y hover
    have hy' : fixedPtHom H A y' = z := Over.OverMorphism.ext hy
    refine ⟨⟨y', ?_⟩, Subtype.ext hy'⟩
    apply fixedPtHom_injective H A
    rw [map_pow, hy', hz, map_one]

end UpperTheory.Lit.Nos.C6

namespace UpperTheory.Lit.Nos.C6
open GlobalTheory

theorem hasGoodReduction_of_infinite_torsionUnramified : ∀ (R K Ω : Type) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [PerfectField (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K]
    [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring →
    ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A →
    {m : ℕ | (m : ResidueField R) ≠ 0 ∧ TorsionUnramified A V m}.Infinite → HasGoodReduction R K A := by
  intro R K Ω _ _ _ _ _ _ _ _ _ _ V hV A _ _ hA hinf
  haveI : IsSepClosed Ω := IsSepClosure.sep_closed K
  apply UpperTheory.Lit.Nos.C5.hasGoodReduction_of_inertiaFixed R K Ω V hV A hA
  obtain ⟨hSH, f, -, -⟩ := GlobalTheory.T.inertiaFixedField_valuationRing_strictlyHenselian R K Ω V hV
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_relativeDimension_abelianVariety_field K A hA
  have hA' := isAbelianScheme_pullback_obj (spMap (algebraMap K (IntermediateField.fixedField (inertia K V)))) A hA
  haveI := hA'.comm
  have hloc : LocallyOfFiniteType A.hom := by haveI := hA.smooth; infer_instance
  refine GlobalTheory.T.hasGoodReduction_of_many_rational_torsion_points _ _ hSH _ hA' g ?_ ?_
  · exact (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback (IsPullback.of_hasPullback _ _) hg
  · refine hinf.mono ?_
    rintro m ⟨hm, hu⟩
    have hunit : IsUnit (m : R) := by
      by_contra h
      apply hm
      rw [← map_natCast (residue R), residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff]
      exact h
    have hmK : (m : K) ≠ 0 := by
      rw [← map_natCast (algebraMap R K)]
      exact (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hunit.ne_zero
    refine ⟨?_, ?_⟩
    · have h' := hunit.map f
      rw [map_natCast] at h'
      rw [← map_natCast (residue _), ne_eq, residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff, not_not]
      exact h'
    · rw [card_torsion_fixedField (inertia K V) A hloc m (fun σ hσ x hx => hu σ hσ x hx)]
      exact GlobalTheory.T.card_abelianVariety_torsion_sepClosed K Ω A hA g hg m hmK

end UpperTheory.Lit.Nos.C6
end
end
end
