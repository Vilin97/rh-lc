module

public import Mathlib.AlgebraicGeometry.Normalization
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalisedBlowupCyclotomicAwayProjective
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsOverIff
import Mathlib.Tactic.Linter.HaveILetI
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyQuasiFiniteOfFiniteGeometricFibres

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.GeomFibre

theorem finite_of_finite_sections {K : Type} [Field K] [IsAlgClosed K] {P : Scheme.{0}}
    (g : P ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType g]
    (h : Finite {p : Spec (CommRingCat.of K) ⟶ P // p ≫ g = 𝟙 _}) : Finite P := by
  have := LocallyOfFiniteType.jacobsonSpace g
  have h1 : (closedPoints P).Finite :=
    Set.finite_coe_iff.mp ((pointEquivClosedPoint g).finite_iff.mp h)
  have hc : IsClosed (closedPoints P) := by
    rw [← Set.biUnion_of_singleton (closedPoints P)]
    exact h1.isClosed_biUnion fun x hx ↦ hx
  have h2 := JacobsonSpace.closure_inter_closedPoints (isClosed_univ (X := P))
  rw [Set.univ_inter, hc.closure_eq] at h2
  exact Set.finite_univ_iff.mp (h2 ▸ h1)

theorem locallyQuasiFinite_of_finite_geometric_fibres :
    ∀ (X Y : Scheme.{0}) (f : X ⟶ Y), LocallyOfFiniteType f →
      (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ X),
        Set.Finite {y : Sp K ⟶ X | y ≫ f = x ≫ f}) → LocallyQuasiFinite f := by
  intro X Y f _ H
  refine LocallyQuasiFinite.of_finite_preimage_singleton f fun y ↦ ?_
  rcases (f ⁻¹' {y}).eq_empty_or_nonempty with h | ⟨x₀, hx₀⟩
  · rw [h]; exact Set.finite_empty
  obtain rfl : f x₀ = y := hx₀
  let K := AlgebraicClosure (X.residueField x₀)
  let x : Sp K ⟶ X :=
    Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x₀) K)) ≫ X.fromSpecResidueField x₀
  have hx : ∀ z, x z = x₀ := fun z ↦ by
    simp only [x, Scheme.Hom.comp_apply]
    exact Scheme.fromSpecResidueField_apply _ _
  have hfin : Finite ↥(pullback f (x ≫ f)) := by
    refine finite_of_finite_sections (pullback.snd f (x ≫ f)) ?_
    have := (H K x).to_subtype
    refine Finite.of_injective (β := {y : Sp K ⟶ X | y ≫ f = x ≫ f})
      (fun p ↦ ⟨p.1 ≫ pullback.fst f (x ≫ f), ?_⟩) fun a b hab ↦ ?_
    · change (p.1 ≫ _) ≫ f = x ≫ f
      rw [Category.assoc, pullback.condition, reassoc_of% p.2]
    · exact Subtype.ext (pullback.hom_ext (congrArg Subtype.val hab) (a.2.trans b.2.symm))
  refine (Set.finite_range (pullback.fst f (x ≫ f))).subset fun z hz ↦ ?_
  rw [Scheme.Pullback.range_fst]
  exact ⟨IsLocalRing.closedPoint K,
    ((Scheme.Hom.comp_apply x f _).trans (congrArg f (hx _))).trans hz.symm⟩

end GlobalTheory.GeomFibre
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenImmersionGenericFibre

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section

namespace GlobalTheory.SecCompact

theorem exists_openImmersion_genericFibre (F : Type) [Field F] (o : Type) [CommRing o] [Algebra o F]
    [IsFractionRing o F] [Algebra.FiniteType ℤ o] (m : ℕ) (X : Scheme.{0}) (sX : X ⟶ Sp F) [IsReduced X]
    [IsSeparated sX] [LocallyOfFiniteType sX] [QuasiCompact sX] (f : X ⟶ PSpace o m) [QuasiCompact f]
    [QuasiSeparated f] (hf : f ≫ PSpace.str o m = sX ≫ spMap (algebraMap o F))
    (hfib : ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ X),
      Set.Finite {y : Sp K ⟶ X | y ≫ sX = x ≫ sX ∧ y ≫ f = x ≫ f}) :
    IsFinite f.fromNormalization ∧
      ∃ iF : X ⟶ pullback (f.fromNormalization ≫ PSpace.str o m) (spMap (algebraMap o F)),
        IsOpenImmersion iF ∧ Dense (Set.range iF) ∧ iF ≫ pullback.snd _ _ = sX ∧
          iF ≫ pullback.fst _ _ = f.toNormalization := by
  haveI := isProper_str o m
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  haveI := IsPreimmersion.of_isLocalization (R := o) (S := F) (nonZeroDivisors o)
  haveI : Algebra.FiniteType ℤ (CommRingCat.of o) := ‹Algebra.FiniteType ℤ o›
  refine ⟨GlobalTheory.NormBlowupInt.isFinite_fromNormalization_int_of_isReduced (o := CommRingCat.of o) f
    (PSpace.str o m) fun x _ => ?_, ?_⟩
  · have h1 : ((f ≫ PSpace.str o m).stalkMap x).hom.EssFiniteType := by
      rw [hf, Scheme.Hom.stalkMap_comp]
      exact .comp (RingHom.FiniteType.of_surjective _
        (Scheme.Hom.stalkMap_surjective _ _)).essFiniteType (LocallyOfFiniteType.stalkMap sX x)
    rw [Scheme.Hom.stalkMap_comp] at h1
    have h2 : (f.stalkMap x).hom.EssFiniteType := .of_comp _ h1
    exact h2.residueFieldMap
  have hb := IsPullback.of_hasPullback (PSpace.str o m) (spMap (algebraMap o F))
  let f' : X ⟶ pullback (PSpace.str o m) (spMap (algebraMap o F)) := pullback.lift f sX hf
  have e₁ : f' ≫ pullback.fst _ _ = f := pullback.lift_fst _ _ _
  have e₂ : f' ≫ pullback.snd _ _ = sX := pullback.lift_snd _ _ _
  haveI : LocallyOfFiniteType (f' ≫ pullback.snd _ _) := by rw [e₂]; infer_instance
  haveI : LocallyOfFiniteType f' := locallyOfFiniteType_of_comp f' (pullback.snd _ _)
  haveI : QuasiCompact (f' ≫ pullback.snd _ _) := by rw [e₂]; infer_instance
  haveI : QuasiCompact f' := QuasiCompact.of_comp f' (pullback.snd _ _)
  haveI : IsSeparated (f' ≫ pullback.snd _ _) := by rw [e₂]; infer_instance
  haveI : IsSeparated f' := IsSeparated.of_comp f' (pullback.snd _ _)
  haveI : LocallyQuasiFinite f' := by
    refine GlobalTheory.GeomFibre.locallyQuasiFinite_of_finite_geometric_fibres X _ f' inferInstance fun K _ _ x => ?_
    refine (hfib K x).subset fun y (hy : y ≫ f' = x ≫ f') => ⟨?_, ?_⟩
    · rw [← e₂, ← Category.assoc, hy, Category.assoc]
    · rw [← e₁, ← Category.assoc, hy, Category.assoc]
  obtain ⟨hoi, -, hdom⟩ :=
    GlobalTheory.isOpenImmersion_lift_toNormalization_of_isLocalization (M := nonZeroDivisors o) hb f' f e₁.symm
  refine ⟨pullback.lift f.toNormalization f' (by simp [e₁]) ≫
    (pullbackRightPullbackFstIso (PSpace.str o m) (spMap (algebraMap o F)) f.fromNormalization).hom,
    inferInstance, (Scheme.Hom.denseRange _), ?_, ?_⟩
  · rw [Category.assoc, pullbackRightPullbackFstIso_hom_snd, pullback.lift_snd_assoc, e₂]
  · rw [Category.assoc, pullbackRightPullbackFstIso_hom_fst, pullback.lift_fst]

end GlobalTheory.SecCompact
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionDenseGenericFibreNormalisation

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin

theorem isOpenImmersion_dense_genericFibre_normalization : ∀ (o F : Type) [CommRing o] [IsDomain o] [IsDedekindDomain o] [Algebra.FiniteType ℤ o] [Field F] [CharZero F] (b : o →+* F) (n : ℕ) (X : Scheme.{0}) (s : X ⟶ Sp F) (f : X ⟶ PSpace o n) [QuasiCompact f] [QuasiSeparated f], Function.Injective b → (∀ x : F, ∃ a d : o, b d ≠ 0 ∧ x * b d = b a) → Geo.Tor.IsNormalScheme X → IsSeparated s → LocallyOfFiniteType s → QuasiCompact s → f ≫ PSpace.str o n = s ≫ spMap b → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ X), Set.Finite {y : Sp K ⟶ X | y ≫ s = x ≫ s ∧ y ≫ f = x ≫ f}) → ∀ iF : X ⟶ pullback (f.fromNormalization ≫ PSpace.str o n) (spMap b), iF ≫ pullback.fst _ _ = f.toNormalization → iF ≫ pullback.snd _ _ = s → IsOpenImmersion iF ∧ Dense (Set.range iF) := by
  intro o F _ _ _ _ _ _ b n X s f _ _ hb hfrac hN _ _ _ hfs hfib iF h1 h2
  letI : Algebra o F := b.toAlgebra
  haveI : FaithfulSMul o F := (faithfulSMul_iff_algebraMap_injective _ _).mpr hb
  haveI : IsFractionRing o F := IsFractionRing.of_field o F fun x => by
    obtain ⟨a, d, hd, e⟩ := hfrac x
    exact ⟨a, d, (eq_div_iff hd).mpr e⟩
  haveI : GlobalTheory.IsNormalScheme X := GlobalTheory.IsNormalScheme.of_pred hN
  haveI : IsReduced X := inferInstance
  obtain ⟨-, i₀, hoi, hd, hsnd, hfst⟩ :=
    GlobalTheory.SecCompact.exists_openImmersion_genericFibre F o n X s f hfs hfib
  have e : iF = i₀ := by
    apply pullback.hom_ext
    · rw [h1, hfst]
    · rw [h2, hsnd]
  subst e
  exact ⟨hoi, hd⟩

end GlobalTheory.UMin
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionDenseGenericFibreNormalisationStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isOpenImmersion_dense_genericFibre_normalisation : ∀ (o F : Type) [CommRing o] [IsDomain o] [IsDedekindDomain o] [Algebra.FiniteType ℤ o] [Field F] [CharZero F] (b : o →+* F) (n : ℕ) (X : Scheme.{0}) (s : X ⟶ Sp F) (f : X ⟶ PSpace o n) [QuasiCompact f] [QuasiSeparated f], Function.Injective b → (∀ x : F, ∃ a d : o, b d ≠ 0 ∧ x * b d = b a) → Geo.Tor.IsNormalScheme X → IsSeparated s → LocallyOfFiniteType s → QuasiCompact s → f ≫ PSpace.str o n = s ≫ spMap b → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ X), Set.Finite {y : Sp K ⟶ X | y ≫ s = x ≫ s ∧ y ≫ f = x ≫ f}) → ∀ iF : X ⟶ pullback (f.fromNormalization ≫ PSpace.str o n) (spMap b), iF ≫ pullback.fst _ _ = f.toNormalization → iF ≫ pullback.snd _ _ = s → IsOpenImmersion iF ∧ Dense (Set.range iF) := by
  first | exact @GlobalTheory.UMin.isOpenImmersion_dense_genericFibre_normalization | exact GlobalTheory.UMin.isOpenImmersion_dense_genericFibre_normalization | (intros; apply GlobalTheory.UMin.isOpenImmersion_dense_genericFibre_normalization <;> assumption)
end
end
