module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodHom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeIsSeparatedOfAffineBase
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicPeriodsNaturalAlongCoveredMorphism
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodCompTranslationGroupHom

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer.Reindex

open GlobalTheory.CatCoh

variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] (F : Fam I g Λ) {Λ' : Type} [AddCommGroup Λ'] (A : Λ' →+ Λ)

abbrev fam : Fam I g Λ' := ⟨F.V, F.τ.comp A, fun l ↦ F.hol (A l)⟩

variable {F A} (K' : Charts (fam F A))

@[reducible] def charts : Charts F where
  K := K'.K
  W := K'.W
  base := K'.base
  le m k' k := ∃ l, A l = m ∧ K'.le l k' k
  le_refl k := ⟨0, map_zero A, K'.le_refl k⟩
  le_trans := by
    rintro _ _ k k' k'' ⟨l, rfl, h⟩ ⟨m, rfl, h'⟩
    exact ⟨l + m, map_add A l m, K'.le_trans h h'⟩
  maps := by
    rintro _ k k' ⟨l, rfl, h⟩
    exact K'.maps h

@[reducible] def obj (T : K'.Obj) : (charts K').Obj where
  k := T.k
  C := T.C
  alg := T.alg
  J := T.J
  nil := T.nil
  ρ := T.ρ
  ρ_cst := T.ρ_cst

def hom {T T' : K'.Obj} (f : T ⟶ T') : obj K' T ⟶ obj K' T' where
  φ := f.φ
  deg := A f.deg
  le := ⟨f.deg, rfl, Charts.Hom.le f⟩
  mem := f.mem
  close := f.close

theorem isPeriod_comp : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {B : Type} [CommRing B] {X : Scheme.{0}} {s : X ⟶ Sp B} {σ : B →+* Hol F.V} (u : Unif F s σ) {Λ' : Type} [AddCommGroup Λ'] (A : Λ' →+ Λ) (u' : Unif (⟨F.V, F.τ.comp A, fun l ↦ F.hol (A l)⟩ : Fam I g Λ') s σ), u'.E = u.E → ∀ (c : FirstDeRham s) (per : Λ →+ Hol F.V), IsPeriod u c per → IsPeriod u' c (per.comp A) := by
  intro I _ g Λ _ F B _ X s σ u Λ' _ A u' hE c per h K' r' hr
  let r : Real (charts K') s σ :=
    { x := r'.x
      w := r'.w
      compat := by
        rintro _ k k' ⟨l, rfl, e⟩
        exact r'.compat e }
  have h1 := h (charts K') r (fun k p hp ↦ (hr k p hp).trans (congrFun hE p))
  obtain ⟨f, rfl⟩ := H1.mk_surjective _ c
  obtain ⟨G, hG⟩ := H1.mk_eq_mk.1 h1
  refine H1.mk_eq_mk.2 ⟨fun T ↦ G (obj K' T), ?_⟩
  funext T T' φ
  exact congrFun (congrFun (congrFun hG (obj K' T)) (obj K' T')) (hom K' φ)

end GlobalTheory.AnPer.Reindex
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodCompTranslationGroupHomStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.period_comp_translationGroup_hom : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {B : Type} [CommRing B] {X : Scheme.{0}} {s : X ⟶ Sp B} {σ : B →+* Hol F.V} (u : Unif F s σ) {Λ' : Type} [AddCommGroup Λ'] (A : Λ' →+ Λ) (u' : Unif (⟨F.V, F.τ.comp A, fun l ↦ F.hol (A l)⟩ : Fam I g Λ') s σ), u'.E = u.E → ∀ (c : FirstDeRham s) (per : Λ →+ Hol F.V), IsPeriod u c per → IsPeriod u' c (per.comp A) := by
  first | exact @GlobalTheory.AnPer.Reindex.isPeriod_comp | exact GlobalTheory.AnPer.Reindex.isPeriod_comp | (intros; apply GlobalTheory.AnPer.Reindex.isPeriod_comp <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibrePeriodEqFamilyPeriodValue

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer

theorem period_fibre_eq_value : PFix := by
  intro I _ g Λ _ F B _ 𝒜 _ h𝒜 σ e z hz y hy A _ hA φ m L u hE τ hτ P hP c per hper l
  let u' : Unif (⟨(fibFam u).V, (fibFam u).τ.comp τ, fun l ↦ (fibFam u).hol (τ l)⟩ : Fam Empty g Λ)
      (A.hom ≫ 𝟙 _) (algebraMap ℂ (Hol (fibFam u).V)) :=
    { E := (fibUnif u).E
      w := (fibUnif u).w
      per := fun l p hp ↦ (fibUnif u).per (τ l) p hp
      hol := (fibUnif u).hol }
  have h1 := GlobalTheory.T.period_comp_translationGroup_hom (fibUnif u) τ u' rfl _ _ (hP (m.pull c))
  have h2 := GlobalTheory.AnPer.isPeriod_pull1_eq_comap u' e (GlobalTheory.abelianScheme_left_isSeparated_of_affine A hA)
    (GlobalTheory.abelianScheme_left_isSeparated_of_affine 𝒜 h𝒜) (fun _ ↦ z) analyticOnNhd_const (fun _ _ ↦ hz)
    LinearMap.id (AddMonoidHom.id Λ) (fun l _ _ ↦ (hτ l).symm) y φ m.isMor
    (fun x ↦ Hol.ext_fn fun p hp ↦ by rw [Hol.fn_algebraMap _ hp, Hol.fn_comap _ _ _ _ hp, hy])
    (fun p _ ↦ (hE p.2).symm) c.1 per _ hper h1 l
  have hp : (0 : Empty → ℂ) ∈ (fibFam u).V := trivial
  have h3 := congrArg (fun f ↦ Hol.fn f 0) h2
  simp only [Hol.fn_comap _ _ _ _ hp] at h3
  exact (Hol.fn_algebraMap _ hp).symm.trans h3

end GlobalTheory.AnPer
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibrePeriodEqFamilyPeriodValueStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.fibrePeriod_eq_familyPeriod_value : PFix := by
  first | exact @GlobalTheory.AnPer.period_fibre_eq_value | exact GlobalTheory.AnPer.period_fibre_eq_value | (intros; apply GlobalTheory.AnPer.period_fibre_eq_value <;> assumption)
end
end
