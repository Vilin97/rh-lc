module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianTorsionFiniteAndMulNSurjective
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.Divisors.MapSmulOfIsHausdorff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.DimEqZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.MapSmulOfIsHausdorff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateModuleLevelSurjectiveOfDivisible
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietySepClosedPointDivisible

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SepClosedDiv

theorem exists_section_of_etale {Ω : Type} [Field Ω] [IsSepClosed Ω] {X : Scheme.{0}} (f : X ⟶ Sp Ω)
    [Etale f] (x : X) : ∃ s : Sp Ω ⟶ X, s ≫ f = 𝟙 _ := by
  let i := X.affineCover.idx x
  obtain ⟨y, -⟩ := X.affineCover.covers x
  obtain ⟨R, e⟩ : ∃ R : CommRingCat, X.affineCover.X i = Spec R := ⟨_, rfl⟩
  let φ : CommRingCat.of Ω ⟶ R := Spec.preimage (eqToHom e.symm ≫ X.affineCover.f i ≫ f)
  have hφ : Spec.map φ = eqToHom e.symm ≫ X.affineCover.f i ≫ f := Spec.map_preimage _
  have hg : Etale (Spec.map φ) := by rw [hφ]; infer_instance
  have hr : φ.hom.Etale := (HasRingHomProperty.Spec_iff (P := @Etale)).1 hg
  letI := φ.hom.toAlgebra
  have : Algebra.Etale Ω R := hr
  let q : PrimeSpectrum R := (eqToHom e).base y
  obtain ⟨ψ⟩ := GlobalTheory.nonempty_algHom_of_etale_of_isSepClosed (R := Ω) (A := R) (K := Ω) q.asIdeal
    (by
      rw [(Ideal.comap (algebraMap Ω R) q.asIdeal).eq_bot_of_prime]
      exact ((RingHom.injective_iff_ker_eq_bot _).1 (algebraMap Ω Ω).injective).symm)
  refine ⟨Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ eqToHom e.symm ≫ X.affineCover.f i, ?_⟩
  simp only [Category.assoc]
  rw [← hφ, ← Spec.map_comp]
  rw [← Spec.map_id]
  congr 1
  ext a
  exact ψ.commutes a

theorem exists_pow_eq : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosed Ω] (A : Over (Sp K)) [GrpObj A]
    [IsCommMonObj A], IsAbelianScheme A → ∀ n : ℕ, (n : K) ≠ 0 → ∀ x : ptOver K Ω ⟶ A, ∃ y, y ^ n = x := by
  intro K Ω _ _ _ _ A _ _ hA n hn x
  have := hA.smooth
  have hu : IsUnit (n : Γ(Sp K, ⊤)) := by
    simpa using (isUnit_iff_ne_zero.2 hn).map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  have he : Etale (mulN A n).left := GlobalTheory.GrpTangent.etale_mulN A hu
  have hs : Surjective (mulN A n).left := GlobalTheory.surjective_mulN_of_isAbelianScheme K A hA n hn
  let m := (mulN A n).left
  have he' : Etale (pullback.snd m x.left) := inferInstance
  obtain ⟨z, -⟩ := (pullback.snd m x.left).surjective (IsLocalRing.closedPoint Ω)
  obtain ⟨s, hs'⟩ := exists_section_of_etale (pullback.snd m x.left) z
  have h : (s ≫ pullback.fst m x.left) ≫ m = x.left := by
    rw [Category.assoc, pullback.condition, reassoc_of% hs']
  refine ⟨Over.homMk (s ≫ pullback.fst m x.left) ?_, ?_⟩
  · change (s ≫ pullback.fst m x.left) ≫ A.hom = _
    rw [← Over.w (mulN A n), ← Category.assoc, h]
    exact Over.w x
  · rw [← GlobalTheory.GrpTangent.comp_mulN]
    exact Over.OverMorphism.ext h

end GlobalTheory.SepClosedDiv
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietySepClosedPointDivisibleStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.abelianVariety_sepClosed_point_divisible : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosed Ω] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ n : ℕ, (n : K) ≠ 0 → ∀ x : ptOver K Ω ⟶ A, ∃ y, y ^ n = x := by
  first | exact @GlobalTheory.SepClosedDiv.exists_pow_eq | exact GlobalTheory.SepClosedDiv.exists_pow_eq | (intros; apply GlobalTheory.SepClosedDiv.exists_pow_eq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateModuleLevelSurjectiveOfDivisibleStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.tateModule_level_surjective_of_divisible : ∀ (l : ℕ) [Fact l.Prime] (M : Type) [CommGroup M], (∀ x : M, ∃ y, y ^ l = x) → ∀ (n : ℕ) (x : M), x ^ l ^ n = 1 → ∃ t : Tate l M, t.lev n = x := by
  first | exact @GlobalTheory.Published.tate_lev_surj | exact GlobalTheory.Published.tate_lev_surj | (intros; apply GlobalTheory.Published.tate_lev_surj <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfiniteTorsionUnramifiedOfTateModuleUnramified

section

@[expose] public section

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbVarRed

theorem natCast_ne_zero_of_residue {R K : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] {m : ℕ} (h : (m : ResidueField R) ≠ 0) : (m : K) ≠ 0 := by
  intro h0
  apply h
  have h1 : (m : R) = 0 := IsFractionRing.injective R K (by rw [map_natCast, map_zero, h0])
  rw [← map_natCast (residue R), h1, map_zero]

theorem torsionUnramified_pow_of_tateUnramified {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsSepClosed Ω]
    {V : ValuationSubring Ω} {A : Over (Sp K)} [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A)
    {l : ℕ} [Fact l.Prime] (hl : (l : K) ≠ 0) (h : TateUnramified A V l) (n : ℕ) :
    TorsionUnramified A V (l ^ n) := by
  intro σ hσ x hx
  obtain ⟨t, rfl⟩ := GlobalTheory.T.tateModule_level_surjective_of_divisible l (ptOver K Ω ⟶ A) (GlobalTheory.T.abelianVariety_sepClosed_point_divisible K Ω A hA l hl) n x hx
  rw [← lev_galTate, h σ hσ]
  rfl

theorem infinite_torsionUnramified_of_tateUnramified :
    ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [PerfectField (ResidueField R)]
      [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
      (V : ValuationSubring Ω), IsAbove R K V.toSubring →
      ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A →
      ∀ (l : ℕ) [Fact l.Prime], (l : ResidueField R) ≠ 0 → TateUnramified A V l →
        {m : ℕ | (m : ResidueField R) ≠ 0 ∧ TorsionUnramified A V m}.Infinite := by
  intro R K Ω _ _ _ _ _ _ _ _ _ _ V _ A _ _ hA l hp hl h
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ => l ^ n)
    (Nat.pow_right_injective hp.out.two_le) fun n => ⟨?_, ?_⟩
  · rw [Nat.cast_pow]
    exact pow_ne_zero _ hl
  · exact torsionUnramified_pow_of_tateUnramified hA (natCast_ne_zero_of_residue hl) h n

end GlobalTheory.AbVarRed
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfiniteTorsionUnramifiedOfTateModuleUnramifiedStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.infinite_torsionUnramified_of_tateModuleUnramified : ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [PerfectField (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (l : ℕ) [Fact l.Prime], (l : ResidueField R) ≠ 0 → TateUnramified A V l → {m : ℕ | (m : ResidueField R) ≠ 0 ∧ TorsionUnramified A V m}.Infinite := by
  first | exact @GlobalTheory.AbVarRed.infinite_torsionUnramified_of_tateUnramified | exact GlobalTheory.AbVarRed.infinite_torsionUnramified_of_tateUnramified | (intros; apply GlobalTheory.AbVarRed.infinite_torsionUnramified_of_tateUnramified <;> assumption)
end
end
