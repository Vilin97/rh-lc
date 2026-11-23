module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HasBareNormDisc
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsConstMul
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNumberFieldPoint
public import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexUniformisationHolds
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.LocallyQuasiFiniteSpMap
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
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HasBareNormDisc
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatDegreeHoldsStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatFirstFromResolutionAndGagaStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.KroneckerCharacterPeriodFormula

-- Source module: Development.WeilBound.CoreStatements.ComplexPeriods.ComplexPointPeriods.PeriodPos

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br

namespace PositivityTheory.Xj6.PeriodIn

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem exists_complex_point {U : Set (Xo.XF c)} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ y : Sp ℂ ⟶ Xo.XF c, y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) ∧ ∀ z, y z ∈ U := by
  haveI := Xo.smooth
  haveI hs0 : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  let s : Xo.XF c ⟶ Sp c.F := pullback.snd _ _
  haveI hs : Smooth s := inferInstanceAs (Smooth (pullback.snd _ _))
  obtain ⟨L, _, j, g, hj, hg, hZ⟩ := GlobalTheory.FlatLine.exists_finite_point s hU hne
  letI : Algebra c.F L := j.toAlgebra
  haveI : Module.Finite c.F L := hj
  let e : L →ₐ[c.F] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨spMap e.toRingHom ≫ g, ?_, fun z => ?_⟩
  · change (spMap e.toRingHom ≫ g) ≫ s = _
    rw [Category.assoc, hg, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact e.comp_algebraMap
  · rw [Scheme.Hom.comp_apply]; exact hZ _

theorem exists_period {U : Set (Xo.XF c)} (hU : IsClopen U) (hne : U.Nonempty) {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (hty : IsTypeFn H D.p D.q ty) :
    ∃ i : Fin FU.n, ∀ P (y : Sp ℂ ⟶ Xo.XF c), IsPeriod (FU.Di i) ty P → under y = FU.u i P →
      y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) → Set.range y ⊆ U := by
  obtain ⟨y₀, hy₀, hU₀⟩ := exists_complex_point hU.isOpen hne
  have hs : under y₀ ≫ Xo.s = spMap (algebraMap (KA l) ℂ) := by
    rw [under, Category.assoc, pullback.condition, ← Category.assoc, hy₀, ← Spec.map_comp]; rfl
  obtain ⟨i, P₀, hP₀, hu₀⟩ := FU.onto _ hs
  refine ⟨i, fun P y hP hu hy => ?_⟩
  rintro _ ⟨z, rfl⟩
  have h := PositivityTheory.Xgn.GeometricOfPeriods.sameComp_periods FU i hty hP hP₀
  rw [← hu, hu₀] at h
  obtain ⟨hp, hq, h⟩ := PositivityTheory.Xgn.GeometricOfPeriods.sameComp_baseChange _ _ Xo.s y y₀ hy hy₀ h
  let π : pullback (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom))
      (spMap (algebraMap c.F ℂ)) ⟶ Xo.XF c := pullback.fst _ _
  have h1 := π.continuous.image_connectedComponent_subset _ ⟨_, h z, rfl⟩
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.lift_fst, pullback.lift_fst] at h1
  exact hU.connectedComponent_subset (hU₀ z) h1

theorem period_in_pos (hr : 1 ≤ D.p + D.q) {U : Set (Xo.XF c)} (hU : IsClopen U) (hne : U.Nonempty) :
    ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n),
      IsTypeFn H D.p D.q ty ∧ ∀ P (y : Sp ℂ ⟶ Xo.XF c), IsPeriod (FU.Di i) ty P → under y = FU.u i P →
        y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) → Set.range y ⊆ U := by
  obtain ⟨g, ty, hty⟩ := GlobalTheory.AllClasses.exists_isTypeFn H D.p D.q
  obtain ⟨FU⟩ := GlobalTheory.CompanionTheory.Ar.Top.complex_uniformisation_holds E H D l Xo (algebraMap (KA l) ℂ) g ty hr rfl hty
  obtain ⟨i, hi⟩ := exists_period hU hne FU hty
  exact ⟨g, ty, FU, i, hty, hi⟩

end PositivityTheory.Xj6.PeriodIn
end
end

-- Source module: Development.WeilBound.CoreStatements.ComplexPeriods.ComplexPointPeriods.PeriodIn

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br

theorem PositivityTheory.Xj6.period_in : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)), 1 ≤ D.p + D.q → IsClopen U → U.Nonempty → ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n), IsTypeFn H D.p D.q ty ∧ ∀ P (y : Sp ℂ ⟶ Xo.XF c), IsPeriod (FU.Di i) ty P → under y = FU.u i P → y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) → Set.range y ⊆ U :=
  fun _ _ _ _ _ _ _ _ _ _ hr hU hne => PositivityTheory.Xj6.PeriodIn.period_in_pos hr hU hne
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.FamilyUniformizationTypeRelay

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br

theorem _root_.GlobalTheory.CompanionTheory.Relay.family_uniformization_type_relay : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)), 1 ≤ D.p + D.q → IsClopen U → U.Nonempty → ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n), IsTypeFn H D.p D.q ty ∧ ∀ P (y : Sp ℂ ⟶ Xo.XF c), IsPeriod (FU.Di i) ty P → under y = FU.u i P → y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) → Set.range y ⊆ U := by
  first | exact @PositivityTheory.Xj6.period_in | exact PositivityTheory.Xj6.period_in
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.FamilyUniformizationTypeRelayStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br

theorem _root_.GlobalTheory.T.family_uniformization_type_relay : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)), 1 ≤ D.p + D.q → IsClopen U → U.Nonempty → ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n), IsTypeFn H D.p D.q ty ∧ ∀ P (y : Sp ℂ ⟶ Xo.XF c), IsPeriod (FU.Di i) ty P → under y = FU.u i P → y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) → Set.range y ⊆ U := by
  first | exact @GlobalTheory.CompanionTheory.Relay.family_uniformization_type_relay | exact GlobalTheory.CompanionTheory.Relay.family_uniformization_type_relay | (intros; apply GlobalTheory.CompanionTheory.Relay.family_uniformization_type_relay <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.KroneckerCharacterFrameBound

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br

namespace GlobalTheory.CompanionTheory.Ar.Br

theorem degree_of_flatOnModel : Geo.ResK.ResKStatement → GagaSections → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [NumberField c.F] (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (φ : FrameFn Xo c) (N : LogNorms c.F) [NeZero H.d] (χ : DirichletCharacter ℂ H.d), GlobalTheory.IsKroneckerChar χ → FracBase β → 1 ≤ D.p + D.q → τ (H.rt : E) = H.rt0 → IsClopen U → Z.IsGeom → FlatOnModel Z τ φ → (∀ s, HasInfNorm U τ φ s (N.inf s)) → (∀ (p : Nat.Primes) (κ : c.F →+* ℂ_[p]), HasFinNorm U τ φ p κ (N.fin p κ)) → N.IsAdelic ∧ N.deg = ((D.p : ℝ) - D.q) / 2 * (GlobalTheory.CM.logOm E χ).re := by
  intro hres hgaga E _ _ _ H D l Xo c O _ β Y _ U Z τ φ N _ χ hχ hO hpq hτ hcl hZ hflat hinf hfin
  obtain ⟨g, ty, FU, i, hty, hin⟩ := GlobalTheory.T.family_uniformization_type_relay E H D l Xo c U hpq hcl ⟨_, Z.genPt_mem⟩
  have hA := GlobalTheory.T.flat_first_from_resolution_and_gaga hres hgaga E H D l Xo c O β Y U Z τ φ hO hpq hτ hZ hflat.isLineFn hflat
  exact GlobalTheory.CompanionTheory.Ar.Fl.TopLL.degree_frames GlobalTheory.T.FlatDegree_holds E H D l Xo c g ty FU i U τ φ N χ hχ hty hτ
    (hA.2 g ty FU i hty hin) hinf hfin

end GlobalTheory.CompanionTheory.Ar.Br
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.KroneckerCharacterFrameBoundStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br

theorem _root_.GlobalTheory.T.kronecker_character_frame_bound : Geo.ResK.ResKStatement → GagaSections → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [NumberField c.F] (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (φ : FrameFn Xo c) (N : LogNorms c.F) [NeZero H.d] (χ : DirichletCharacter ℂ H.d), GlobalTheory.IsKroneckerChar χ → FracBase β → 1 ≤ D.p + D.q → τ (H.rt : E) = H.rt0 → IsClopen U → Z.IsGeom → FlatOnModel Z τ φ → (∀ s, HasInfNorm U τ φ s (N.inf s)) → (∀ (p : Nat.Primes) (κ : c.F →+* ℂ_[p]), HasFinNorm U τ φ p κ (N.fin p κ)) → N.IsAdelic ∧ N.deg = ((D.p : ℝ) - D.q) / 2 * (GlobalTheory.CM.logOm E χ).re := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Br.degree_of_flatOnModel | exact GlobalTheory.CompanionTheory.Ar.Br.degree_of_flatOnModel | (intros; apply GlobalTheory.CompanionTheory.Ar.Br.degree_of_flatOnModel <;> assumption)
end
end
