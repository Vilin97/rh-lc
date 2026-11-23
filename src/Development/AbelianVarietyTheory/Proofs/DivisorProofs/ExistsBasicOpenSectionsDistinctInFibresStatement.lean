module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealSectionsEq

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace GlobalTheory.IdealSectionsFactorization

theorem comp_eq_iff_factors {S X B W : Scheme.{0}} (p : X ⟶ B) (x y : S ⟶ X)
    (h : x ≫ p = y ≫ p) (g : W ⟶ S) :
    g ≫ x = g ≫ y ↔
      ∃ l : W ⟶ pullback (pullback.lift x y h) (pullback.diagonal p),
        l ≫ pullback.fst _ _ = g := by
  constructor
  · intro hg
    refine ⟨pullback.lift g (g ≫ x) ?_, pullback.lift_fst _ _ _⟩
    apply pullback.hom_ext
    · simp [pullback.diagonal_fst, pullback.lift_fst]
    · simp [pullback.diagonal_snd, pullback.lift_snd, hg]
  · rintro ⟨l, rfl⟩
    have hc := pullback.condition (f := pullback.lift x y h) (g := pullback.diagonal p)
    have h1 := congrArg (· ≫ pullback.fst p p) hc
    have h2 := congrArg (· ≫ pullback.snd p p) hc
    simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.diagonal_fst,
      pullback.diagonal_snd, Category.comp_id] at h1 h2
    rw [Category.assoc, Category.assoc, h1, h2]

theorem factors_iff_kills {R T : Type} [CommRing R] [CommRing T] (I : Ideal R) (ψ : R →+* T) :
    (∃ l : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of (R ⧸ I)),
      l ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) = Spec.map (CommRingCat.ofHom ψ)) ↔
      ∀ r ∈ I, ψ r = 0 := by
  constructor
  · rintro ⟨l, hl⟩ r hr
    obtain ⟨φ, rfl⟩ := Spec.map_surjective l
    rw [← Spec.map_comp] at hl
    have h := Spec.map_injective hl
    have h' : φ.hom (Ideal.Quotient.mk I r) = ψ r :=
      congrArg (fun k : CommRingCat.of R ⟶ CommRingCat.of T => k.hom r) h
    rw [← h', Ideal.Quotient.eq_zero_iff_mem.mpr hr, map_zero]
  · intro h
    refine ⟨Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift I ψ h)), ?_⟩
    rw [← Spec.map_comp]
    congr 1

theorem exists_ideal_sections_eq (R : Type) [CommRing R]
    (X : Over (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R)) (hX : IsSeparated X.hom)
    (x y : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R ⟶ X.left)
    (hx : x ≫ X.hom = 𝟙 (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R))
    (hy : y ≫ X.hom = 𝟙 (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R)) :
    ∃ I : Ideal R, ∀ (T : Type) [CommRing T] (ψ : R →+* T),
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap ψ ≫ x = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap ψ ≫ y ↔
        ∀ r ∈ I, ψ r = 0 := by
  have h : x ≫ X.hom = y ≫ X.hom := hx.trans hy.symm
  have hc : IsClosedImmersion
      (pullback.fst (pullback.lift x y h) (pullback.diagonal X.hom)) :=
    IsClosedImmersion.isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback _ _).flip hX.isClosedImmersion_diagonal
  obtain ⟨I, e, he⟩ := IsClosedImmersion.Spec_iff.mp hc
  refine ⟨I, fun T _ ψ => ?_⟩
  rw [comp_eq_iff_factors X.hom x y h, ← factors_iff_kills I ψ, he]
  constructor
  · rintro ⟨l, hl⟩
    exact ⟨l ≫ e.hom, by rw [Category.assoc]; exact hl⟩
  · rintro ⟨l, hl⟩
    exact ⟨l ≫ e.inv, by rw [Category.assoc, e.inv_hom_id_assoc]; exact hl⟩

end GlobalTheory.IdealSectionsFactorization
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqualizerSectionsClosedIdeal

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem sections_eqLocus_ideal : ∀ (R : Type) [CommRing R] (X : Over (Sp R)), IsSeparated X.hom →
    ∀ (x y : Sp R ⟶ X.left), x ≫ X.hom = 𝟙 _ → y ≫ X.hom = 𝟙 _ → ∃ I : Ideal R,
      ∀ (T : Type) [CommRing T] (ψ : R →+* T), (spMap ψ ≫ x = spMap ψ ≫ y ↔ ∀ r ∈ I, ψ r = 0) := by
  first
  | exact @_root_.GlobalTheory.IdealSectionsFactorization.exists_ideal_sections_eq
  | exact _root_.GlobalTheory.IdealSectionsFactorization.exists_ideal_sections_eq
  | (apply _root_.GlobalTheory.IdealSectionsFactorization.exists_ideal_sections_eq <;> assumption)
  | (intros; apply _root_.GlobalTheory.IdealSectionsFactorization.exists_ideal_sections_eq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IdealSectionsFactorization.exists_ideal_sections_eq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IdealSectionsFactorization.exists_ideal_sections_eq ..)

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqualizerSectionsClosedIdealStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.equalizer_sections_closed_ideal : ∀ (R : Type) [CommRing R] (X : Over (Sp R)), IsSeparated X.hom → ∀ (x y : Sp R ⟶ X.left), x ≫ X.hom = 𝟙 _ → y ≫ X.hom = 𝟙 _ → ∃ I : Ideal R, ∀ (T : Type) [CommRing T] (ψ : R →+* T), (spMap ψ ≫ x = spMap ψ ≫ y ↔ ∀ r ∈ I, ψ r = 0) := by
  first | exact @GlobalTheory.sections_eqLocus_ideal | exact GlobalTheory.sections_eqLocus_ideal | (intros; apply GlobalTheory.sections_eqLocus_ideal <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenSectionsDistinctInFibres

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SectionsSpread

theorem sep_elem (R : Type) [CommRing R] (X : Over (Sp R)) (hX : IsSeparated X.hom)
    (K : Type) [Field K] (e : R →+* K) (x y : Sp R ⟶ X.left)
    (hx : x ≫ X.hom = 𝟙 _) (hy : y ≫ X.hom = 𝟙 _) (hne : spMap e ≫ x ≠ spMap e ≫ y) :
    ∃ r : R, e r ≠ 0 ∧ ∀ (F : Type) [Field F] (ψ : R →+* F), ψ r ≠ 0 →
      spMap ψ ≫ x ≠ spMap ψ ≫ y := by
  obtain ⟨I, hI⟩ := GlobalTheory.T.equalizer_sections_closed_ideal R X hX x y hx hy
  have h1 : ¬ ∀ r ∈ I, e r = 0 := fun h => hne ((hI K e).2 h)
  push_neg at h1
  obtain ⟨r, hrI, hr⟩ := h1
  refine ⟨r, hr, fun F _ ψ hψ heq => hψ ((hI F ψ).1 heq r hrI)⟩

theorem pairs : ∀ (R : Type) [CommRing R] (X : Over (Sp R)), IsSeparated X.hom → ∀ (K : Type) [Field K] (e : R →+* K), Function.Injective e → ∀ t : Finset (Sp R ⟶ X.left), (∀ x ∈ t, x ≫ X.hom = 𝟙 _) → (∀ x ∈ t, ∀ y ∈ t, x ≠ y → spMap e ≫ x ≠ spMap e ≫ y) → ∃ f : R, e f ≠ 0 ∧ ∀ (F : Type) [Field F] (ψ : R →+* F), IsUnit (ψ f) → ∀ x ∈ t, ∀ y ∈ t, x ≠ y → spMap ψ ≫ x ≠ spMap ψ ≫ y := by
  intro R _ X hX K _ e _ t ht hsep
  classical
  let g : (Sp R ⟶ X.left) × (Sp R ⟶ X.left) → R := fun p =>
    if h : p.1 ∈ t ∧ p.2 ∈ t ∧ p.1 ≠ p.2 then
      Classical.choose (sep_elem R X hX K e p.1 p.2 (ht _ h.1) (ht _ h.2.1) (hsep _ h.1 _ h.2.1 h.2.2))
    else 1
  have hg : ∀ p : (Sp R ⟶ X.left) × (Sp R ⟶ X.left), e (g p) ≠ 0 ∧
      ∀ (F : Type) [Field F] (ψ : R →+* F), ψ (g p) ≠ 0 → p.1 ∈ t → p.2 ∈ t → p.1 ≠ p.2 →
        spMap ψ ≫ p.1 ≠ spMap ψ ≫ p.2 := by
    intro p
    by_cases h : p.1 ∈ t ∧ p.2 ∈ t ∧ p.1 ≠ p.2
    · have hs := Classical.choose_spec
        (sep_elem R X hX K e p.1 p.2 (ht _ h.1) (ht _ h.2.1) (hsep _ h.1 _ h.2.1 h.2.2))
      simp only [g, dif_pos h]
      exact ⟨hs.1, fun F _ ψ hψ _ _ _ => hs.2 F ψ hψ⟩
    · simp only [g, dif_neg h]
      exact ⟨by simp, fun F _ ψ _ h1 h2 h3 => absurd ⟨h1, h2, h3⟩ h⟩
  refine ⟨∏ p ∈ t ×ˢ t, g p, ?_, ?_⟩
  · rw [map_prod]
    exact Finset.prod_ne_zero_iff.2 fun p _ => (hg p).1
  · intro F _ ψ hu x hx y hy hxy
    have hmem : (x, y) ∈ t ×ˢ t := Finset.mem_product.2 ⟨hx, hy⟩
    have hdvd : g (x, y) ∣ ∏ p ∈ t ×ˢ t, g p := Finset.dvd_prod_of_mem g hmem
    have hu' : IsUnit (ψ (g (x, y))) := isUnit_of_dvd_unit (map_dvd ψ hdvd) hu
    exact (hg (x, y)).2 F ψ hu'.ne_zero hx hy hxy

end GlobalTheory.SectionsSpread
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenSectionsDistinctInFibresStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_basicOpen_sections_distinct_in_fibres : ∀ (R : Type) [CommRing R] (X : Over (Sp R)), IsSeparated X.hom → ∀ (K : Type) [Field K] (e : R →+* K), Function.Injective e → ∀ t : Finset (Sp R ⟶ X.left), (∀ x ∈ t, x ≫ X.hom = 𝟙 _) → (∀ x ∈ t, ∀ y ∈ t, x ≠ y → spMap e ≫ x ≠ spMap e ≫ y) → ∃ f : R, e f ≠ 0 ∧ ∀ (F : Type) [Field F] (ψ : R →+* F), IsUnit (ψ f) → ∀ x ∈ t, ∀ y ∈ t, x ≠ y → spMap ψ ≫ x ≠ spMap ψ ≫ y := by
  first | exact @GlobalTheory.SectionsSpread.pairs | exact GlobalTheory.SectionsSpread.pairs | (intros; apply GlobalTheory.SectionsSpread.pairs <;> assumption)
end
end
