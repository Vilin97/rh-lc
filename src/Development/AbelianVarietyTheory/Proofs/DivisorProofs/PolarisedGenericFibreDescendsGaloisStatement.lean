module

public import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FracMapAlgebraMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianOfFieldExtensionPullbackProperStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisConjugateGenericBundleIsoStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleGaloisDescentAbelianVarietyFinitStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixedMemRangeFractionFieldMapGaloisInvariantsStatement
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalPolarisationOfGroupSchemeIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FracMapAlgebraMap
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RigidifiedSymmetricKernelTrivialDescendFieldExt
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ProperRelAmpleKTrivOfFieldExtension
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FractionFieldMapFiniteOfFiniteInjective

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.GenDesc

noncomputable section

namespace GlobalTheory.Mum.GenDesc

theorem fracMap_finite : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R') (hρ : Function.Injective ρ), ρ.Finite → (fracMap ρ hρ).Finite := by
  intro R R' _ _ _ _ ρ hρ hfin
  letI : Algebra R R' := ρ.toAlgebra
  haveI : Module.Finite R R' := hfin
  have hinj : Function.Injective (algebraMap R R') := hρ
  haveI : FaithfulSMul R R' := (faithfulSMul_iff_algebraMap_injective R R').mpr hinj
  letI : Algebra (FractionRing R) (FractionRing R') := FractionRing.liftAlgebra R (FractionRing R')
  haveI : IsScalarTower R (FractionRing R) (FractionRing R') :=
    FractionRing.isScalarTower_liftAlgebra R (FractionRing R')
  haveI : IsLocalization (Algebra.algebraMapSubmonoid R' (nonZeroDivisors R)) (FractionRing R') :=
    inferInstance
  haveI : Module.Finite (FractionRing R) (FractionRing R') :=
    Module.Finite.of_isLocalization R R' (nonZeroDivisors R)
  have heq : fracMap ρ hρ = algebraMap (FractionRing R) (FractionRing R') := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r => ?_)
    simp only [RingHom.comp_apply]
    rw [fracMap_algebraMap, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R R' (FractionRing R')]
    rfl
  rw [heq]
  exact RingHom.finite_algebraMap.mpr inferInstance

end GlobalTheory.Mum.GenDesc
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FractionFieldMapFiniteOfFiniteInjectiveStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.GenDesc

theorem _root_.GlobalTheory.T.fractionFieldMap_finite_of_finite_injective : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R') (hρ : Function.Injective ρ), ρ.Finite → (fracMap ρ hρ).Finite := by
  first | exact @GlobalTheory.Mum.GenDesc.fracMap_finite | exact GlobalTheory.Mum.GenDesc.fracMap_finite | (intros; apply GlobalTheory.Mum.GenDesc.fracMap_finite <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackGenericFibreFractionFieldMap

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.GenDesc

namespace GlobalTheory.Mum.GenDesc

theorem isGrpPullback_genMap : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R') (hρ : Function.Injective ρ) (G' : Over (Sp R')) [GrpObj G'] (G : Over (Sp R)) [GrpObj G] (β : G'.left ⟶ G.left) (h : IsGrpPullback G' G (spMap ρ) β), IsGrpPullback ((Over.pullback (jK R')).obj G') ((Over.pullback (jK R)).obj G) (spMap (fracMap ρ hρ)) (genMap hρ β h.1.w) := by
  intro R R' _ _ _ _ ρ hρ G' _ G _ β h
  have n : IsGrpPullback ((Over.pullback (jK R')).obj G') G (spMap (fracMap ρ hρ) ≫ jK R)
      (genMap hρ β h.1.w ≫ pullback.fst G.hom (jK R)) :=
    ((isGrpPullback_pullback G' (jK R')).comp h).congr (jK_comp_spMap ρ hρ) (genMap_fst hρ β h.1.w).symm
  exact IsGrpPullback.cancel (isGrpPullback_pullback G (jK R)) n (genMap_snd hρ β h.1.w)

end GlobalTheory.Mum.GenDesc
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackGenericFibreFractionFieldMapStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.GenDesc

theorem _root_.GlobalTheory.T.isGrpPullback_genericFibre_fractionFieldMap : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R') (hρ : Function.Injective ρ) (G' : Over (Sp R')) [GrpObj G'] (G : Over (Sp R)) [GrpObj G] (β : G'.left ⟶ G.left) (h : IsGrpPullback G' G (spMap ρ) β), IsGrpPullback ((Over.pullback (jK R')).obj G') ((Over.pullback (jK R)).obj G) (spMap (fracMap ρ hρ)) (genMap hρ β h.1.w) := by
  first | exact @GlobalTheory.Mum.GenDesc.isGrpPullback_genMap | exact GlobalTheory.Mum.GenDesc.isGrpPullback_genMap | (intros; apply GlobalTheory.Mum.GenDesc.isGrpPullback_genMap <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalPolarisationOfGroupSchemeIsoStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.GenDesc

theorem _root_.GlobalTheory.T.principalPolarisation_of_groupScheme_iso : ∀ (S : Scheme.{0}) (P : PolAV S) (B : Over S) [GrpObj B] (e : B ≅ P.A), IsMonHom e.hom → ∀ L : LB B.left, L.IsLB → LBIso L (P.L.pull e.hom.left) → IsProper B.hom ∧ SmoothOfRelativeDimension P.g B.hom ∧ Sym B L ∧ RelAmple B L ∧ KTriv B L := by
  first | exact @GlobalTheory.polarisation_of_iso | exact GlobalTheory.polarisation_of_iso | (intros; apply GlobalTheory.polarisation_of_iso <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedSymmetricOfSymmetricFieldExtensionPull

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.GenDesc

namespace GlobalTheory.Mum.GenDesc

theorem rigidified_and_sym_of_field_extension : ∀ (K K' : Type) [Field K] [Field K'] (i : K →+* K') (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp K')) [GrpObj A'] (φ : A'.left ⟶ A.left), IsAbelianScheme A → IsGrpPullback A' A (spMap i) φ → ∀ (L : LB A.left) (L' : LB A'.left), L.IsLB → L'.IsLB → LBIso L' (L.pull φ) → Sym A' L' → Rigidified A L ∧ Sym A L := by
  intro K K' _ _ i A _ A' _ φ hA h L L' hL hL' hw hS
  refine ⟨?_, (GlobalTheory.PolDescent.rigidified_sym_kTriv_descend K K' i A A' φ L L' hA h hL hL' hw).2.1 hS⟩
  have : Subsingleton (𝟙_ (Over (Sp K))).left := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  exact GlobalTheory.PolDescent.exists_gen_of_unique (default : PrimeSpectrum K) (pull_isLB hL _)

end GlobalTheory.Mum.GenDesc
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedSymmetricOfSymmetricFieldExtensionPullStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.GenDesc

theorem _root_.GlobalTheory.T.rigidified_symmetric_of_symmetric_fieldExtension_pullback : ∀ (K K' : Type) [Field K] [Field K'] (i : K →+* K') (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp K')) [GrpObj A'] (φ : A'.left ⟶ A.left), IsAbelianScheme A → IsGrpPullback A' A (spMap i) φ → ∀ (L : LB A.left) (L' : LB A'.left), L.IsLB → L'.IsLB → LBIso L' (L.pull φ) → Sym A' L' → Rigidified A L ∧ Sym A L := by
  first | exact @GlobalTheory.Mum.GenDesc.rigidified_and_sym_of_field_extension | exact GlobalTheory.Mum.GenDesc.rigidified_and_sym_of_field_extension | (intros; apply GlobalTheory.Mum.GenDesc.rigidified_and_sym_of_field_extension <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedGenericFibreDescendsGalois

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum.GenDesc

open GlobalTheory.Mum

theorem polarisedGeneric : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G'), ∀ (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback G' G (spMap ρ) β → (∀ σ, a.act σ ≫ β = β) → ∃ (A : PolAV (Sp (FractionRing R))) (gen : (Over.pullback (jK R)).obj G ≅ A.A) (κ : pullback G'.hom (jK R') ⟶ pullback G.hom (jK R)), IsMonHom gen.hom ∧ κ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ β ∧ LBIso (U'.LG.L.pull (pullback.fst G'.hom (jK R'))) (A.L.pull (κ ≫ gen.hom.left)) := by
  intro R _ _ _ _ R' _ _ _ ρ hfin hgal D D' hD A' G' _ _ _ U' a G _ _ β hG hpb hinv
  have hρ : Function.Injective ρ := hfin.2.1
  haveI := hgal.1
  have hκ := GlobalTheory.T.isGrpPullback_genericFibre_fractionFieldMap R R' ρ hρ G' G β hpb
  let L' := U'.LG.L.pull (pullback.fst G'.hom (jK R'))
  have hL' : L'.IsLB := pull_isLB U'.LG.isLB _
  have hiso : LBIso L' (A'.L.pull U'.gen.hom.left) := LBIso.symm U'.ext
  have := U'.gen_hom
  obtain ⟨hP', hdim', hsym', hamp', hkt'⟩ := GlobalTheory.T.principalPolarisation_of_groupScheme_iso _ A' _ U'.gen U'.gen_hom L' hL' hiso
  have hsemi : IsSemiAbelian ((Over.pullback (jK R)).obj G) := Geo.Tor.IsSemiAbelian.pullback (jK R) G hG
  obtain ⟨hab, hdim⟩ := GlobalTheory.T.abelian_of_fieldExtension_pullback_proper _ _ (fracMap ρ hρ) ((Over.pullback (jK R)).obj G) _ _ A'.g hsemi hκ hP' hdim'
  obtain ⟨L, hL, hLL⟩ := GlobalTheory.T.exists_lineBundle_galoisDescent_abelianVariety_finite (FractionRing R) (FractionRing R') (fracMap ρ hρ)
    (GlobalTheory.T.fractionFieldMap_finite_of_finite_injective R R' ρ hρ hfin.2.2) (Gal ρ) (fun σ => fracAut σ.1) (fun σ x => fracAut_fracMap hρ σ x)
    (GlobalTheory.T.fixed_mem_range_fractionFieldMap_galoisInvariants R R' ρ hρ hgal) ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R')).obj G') _ hab hκ L' hL'
    (GlobalTheory.T.exists_galoisConjugate_genericBundle_iso R R' ρ hρ D D' hD A' G' U' a G β hpb.1.w hinv)
  obtain ⟨hrig, hsym⟩ := GlobalTheory.T.rigidified_symmetric_of_symmetric_fieldExtension_pullback _ _ (fracMap ρ hρ) _ _ _ hab hκ L L' hL hL' hLL hsym'
  have := hsemi.quasiCompact
  have := hsemi.separated
  have := hsemi.smooth
  obtain ⟨-, hamp, hkt⟩ := GlobalTheory.AmpleDescent.proper_relAmple_kTriv_of_fieldExtension (FractionRing R) (FractionRing R')
    (fracMap ρ hρ) ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R')).obj G') _ hκ L L' hL hL' hLL hP' hamp' hkt'
  let P : PolAV (Sp (FractionRing R)) :=
    { A := (Over.pullback (jK R)).obj G
      isAb := hab
      g := A'.g
      smoothDim := hdim
      L := L
      isLB := hL
      rigid := hrig
      sym := hsym
      ample := hamp
      ktriv := hkt }
  refine ⟨P, Iso.refl _, genMap hρ β hpb.1.w, ?_, genMap_fst _ _ _, ?_⟩
  · show IsMonHom (𝟙 _)
    infer_instance
  · simpa using hLL

end GlobalTheory.Mum.GenDesc
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedGenericFibreDescendsGaloisStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.polarised_generic_fibre_descends_galois : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G'), ∀ (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback G' G (spMap ρ) β → (∀ σ, a.act σ ≫ β = β) → ∃ (A : PolAV (Sp (FractionRing R))) (gen : (Over.pullback (jK R)).obj G ≅ A.A) (κ : pullback G'.hom (jK R') ⟶ pullback G.hom (jK R)), IsMonHom gen.hom ∧ κ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ β ∧ LBIso (U'.LG.L.pull (pullback.fst G'.hom (jK R'))) (A.L.pull (κ ≫ gen.hom.left)) := by
  first | exact @GlobalTheory.Mum.GenDesc.polarisedGeneric | exact GlobalTheory.Mum.GenDesc.polarisedGeneric | (intros; apply GlobalTheory.Mum.GenDesc.polarisedGeneric <;> assumption)
end
end
