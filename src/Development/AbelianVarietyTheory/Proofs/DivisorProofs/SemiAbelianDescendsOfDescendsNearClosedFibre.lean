module

public import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentDatumOfDescendedMultiplicationStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiAbelianDescentAlongProperSurjectiveStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartSome
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescentDatumCarriesTranslateChartStatement
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentOfChartsPulledBackFromFlat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSectionTranslatesCoverSemiAbelianStatement
import Mathlib.RingTheory.Henselian

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartIsOpenImmersionOverBase

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem transl_toTerm_eq {S : Scheme.{0}} {X : Over S} (f g : X ⟶ Over.mk (𝟙 S)) : f = g := by
  ext
  have hf := Over.w f
  have hg := Over.w g
  simp only [Over.mk_hom] at hf hg
  exact (Category.comp_id f.left).symm.trans (hf.trans (hg.symm.trans (Category.comp_id g.left)))

theorem transl_comp {S : Scheme.{0}} {G : Over S} [GrpObj G] (y z : Over.mk (𝟙 S) ⟶ G) :
    transl y ≫ transl z = transl (y * z) := by
  unfold transl
  rw [comp_mul, Category.comp_id, ← Category.assoc,
    transl_toTerm_eq (_ ≫ Over.homMk G.hom (by simp)) (Over.homMk G.hom (by simp)), _root_.mul_assoc, ← comp_mul]

theorem transl_one {S : Scheme.{0}} {G : Over S} [GrpObj G] : transl (1 : Over.mk (𝟙 S) ⟶ G) = 𝟙 G := by
  unfold transl
  rw [comp_one, _root_.mul_one]

instance transl_isIso {S : Scheme.{0}} {G : Over S} [GrpObj G] (y : Over.mk (𝟙 S) ⟶ G) : IsIso (transl y) :=
  ⟨⟨transl y⁻¹, by rw [transl_comp, _root_.mul_inv_cancel, transl_one], by rw [transl_comp, _root_.inv_mul_cancel, transl_one]⟩⟩

instance transl_left_isIso {S : Scheme.{0}} {G : Over S} [GrpObj G] (y : Over.mk (𝟙 S) ⟶ G) : IsIso (transl y).left :=
  inferInstanceAs (IsIso ((Over.forget S).map (transl y)))

theorem Near.chart_isOpenImmersion_over {R : Type} [CommRing R] [IsLocalRing R] (S : Scheme.{0}) (π : S ⟶ Sp R)
    (G' : Over S) [GrpObj G'] (N : Near π G') (n : ℕ) (x : Fin n → (Over.mk (𝟙 S) ⟶ G')) (j : Option (Fin n)) :
    IsOpenImmersion (N.chart x j) ∧ N.chart x j ≫ G'.hom = pullback.snd N.U.hom π := by
  have := N.isOpen
  cases j with
  | none => exact ⟨N.isOpen, N.u_over⟩
  | some k =>
    refine ⟨?_, ?_⟩
    · rw [Near.chart_some]; infer_instance
    · rw [Near.chart_some, Category.assoc, Over.w, N.u_over]

end GlobalTheory.Mum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartIsOpenImmersionOverBaseStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.chart_isOpenImmersion_over_base : ∀ {R : Type} [CommRing R] [IsLocalRing R] (S : Scheme.{0}) (π : S ⟶ Sp R) (G' : Over S) [GrpObj G'] (N : Near π G') (n : ℕ) (x : Fin n → (Over.mk (𝟙 S) ⟶ G')) (j : Option (Fin n)), IsOpenImmersion (N.chart x j) ∧ N.chart x j ≫ G'.hom = pullback.snd N.U.hom π := by
  first | exact @GlobalTheory.Mum.Near.chart_isOpenImmersion_over | exact GlobalTheory.Mum.Near.chart_isOpenImmersion_over | (intros; apply GlobalTheory.Mum.Near.chart_isOpenImmersion_over <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentOfChartsPulledBackFromFlatStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_descent_of_charts_pulled_back_from_flat : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (S X : Scheme.{0}) (π : S ⟶ Sp R) (f : X ⟶ S), IsProper π → Surjective π → IsIntegral S → ∀ (Φ : pullback f (pullback.fst π π) ⟶ pullback f (pullback.snd π π)), Φ ≫ pullback.snd _ _ = pullback.snd _ _ → ∀ (U : Over (Sp R)), Flat U.hom → ∀ (J : Type) (e : J → (pullback U.hom π ⟶ X)), (∀ j, IsOpenImmersion (e j)) → (∀ j, e j ≫ f = pullback.snd _ _) → (∀ x : X, ∃ j, x ∈ Set.range (e j)) → (∀ (j : J) (T : Scheme.{0}) (y₁ y₂ : T ⟶ pullback U.hom π) (s : T ⟶ pullback π π), y₁ ≫ pullback.fst _ _ = y₂ ≫ pullback.fst _ _ → y₁ ≫ pullback.snd _ _ = s ≫ pullback.fst π π → y₂ ≫ pullback.snd _ _ = s ≫ pullback.snd π π → ∀ z : T ⟶ pullback f (pullback.fst π π), z ≫ pullback.fst _ _ = y₁ ≫ e j → z ≫ pullback.snd _ _ = s → z ≫ Φ ≫ pullback.fst _ _ = y₂ ≫ e j) → ∃ (G : Over (Sp R)) (β : X ⟶ G.left) (ψ : J → (U.left ⟶ G.left)), (∀ j, IsOpenImmersion (ψ j) ∧ ψ j ≫ G.hom = U.hom ∧ e j ≫ β = pullback.fst _ _ ≫ ψ j) ∧ (∀ g : G.left, ∃ j, g ∈ Set.range (ψ j)) ∧ IsPullback β f G.hom π ∧ pullback.fst f (pullback.fst π π) ≫ β = Φ ≫ pullback.fst f (pullback.snd π π) ≫ β := by
  first | exact @GlobalTheory.Mum.ChartDescent.exists_descent | exact GlobalTheory.Mum.ChartDescent.exists_descent | (intros; apply GlobalTheory.Mum.ChartDescent.exists_descent <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothNeighbourhoodTranslatesCoverGroup

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem chartCover_toTerm {S : Scheme.{0}} {A : Over S} (f : A ⟶ Over.mk (𝟙 S)) :
    f = Over.homMk A.hom (by simp) := by
  ext1
  simpa using Over.w f

theorem comp_transl {S : Scheme.{0}} {G A : Over S} [GrpObj G] (y : Over.mk (𝟙 S) ⟶ G) (h : A ⟶ G) :
    h ≫ transl y = h * (Over.homMk A.hom (by simp) ≫ y) := by
  unfold transl
  rw [comp_mul, Category.comp_id, ← Category.assoc]
  congr 2
  exact chartCover_toTerm _

theorem chart_cover : ∀ {R : Type} [CommRing R] [IsLocalRing R] (S : Scheme.{0}) (π : S ⟶ Sp R) (G' : Over S) [GrpObj G']
    (N : Near π G') (n : ℕ) (x : Fin n → (Over.mk (𝟙 S) ⟶ G')),
    (∀ (Ω : Type) [Field Ω] (s : Sp Ω ⟶ S) (g : Over.mk s ⟶ G'), Set.range g.left ⊆ Set.range N.u ∨
      ∃ i, Set.range (g * (Over.homMk s (by simp) : Over.mk s ⟶ Over.mk (𝟙 S)) ≫ x i).left ⊆ Set.range N.u) →
    ∀ p : G'.left, ∃ j, p ∈ Set.range (N.chart x j) := by
  intro R _ _ S π G' _ N n x H p
  let t : Sp (G'.left.residueField p) ⟶ G'.left := G'.left.fromSpecResidueField p
  let s : Sp (G'.left.residueField p) ⟶ S := t ≫ G'.hom
  let g : Over.mk s ⟶ G' := Over.homMk t rfl
  have hp : g.left (IsLocalRing.closedPoint _) = p := Scheme.fromSpecResidueField_apply p _
  rcases H (G'.left.residueField p) s g with h1 | ⟨i, h2⟩
  · exact ⟨none, by simpa [Near.chart] using h1 ⟨_, hp⟩⟩
  · let c : Over.mk s ⟶ G' := (Over.homMk s (by simp) : Over.mk s ⟶ Over.mk (𝟙 S)) ≫ x i
    obtain ⟨b, hb⟩ := h2 ⟨IsLocalRing.closedPoint _, rfl⟩
    have key : (g * c) ≫ transl (x i)⁻¹ = g := by
      rw [comp_transl]
      have e : (Over.homMk (Over.mk s).hom (by simp) : Over.mk s ⟶ Over.mk (𝟙 S)) ≫ (x i)⁻¹ = c⁻¹ := by
        rw [GrpObj.comp_inv]; rfl
      rw [e, mul_inv_cancel_right]
    refine ⟨some i, b, ?_⟩
    rw [Near.chart_some, Scheme.Hom.comp_apply, hb]
    have e2 : ((g * c) ≫ transl (x i)⁻¹).left (IsLocalRing.closedPoint _) = p := by rw [key]; exact hp
    rw [Over.comp_left] at e2
    exact (Scheme.Hom.comp_apply _ _ _).symm.trans e2

end GlobalTheory.Mum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothNeighbourhoodTranslatesCoverGroupStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.smoothNeighbourhood_translates_cover_group : ∀ {R : Type} [CommRing R] [IsLocalRing R] (S : Scheme.{0}) (π : S ⟶ Sp R) (G' : Over S) [GrpObj G'] (N : Near π G') (n : ℕ) (x : Fin n → (Over.mk (𝟙 S) ⟶ G')), (∀ (Ω : Type) [Field Ω] (s : Sp Ω ⟶ S) (g : Over.mk s ⟶ G'), Set.range g.left ⊆ Set.range N.u ∨ ∃ i, Set.range (g * (Over.homMk s (by simp) : Over.mk s ⟶ Over.mk (𝟙 S)) ≫ x i).left ⊆ Set.range N.u) → ∀ p : G'.left, ∃ j, p ∈ Set.range (N.chart x j) := by
  first | exact @GlobalTheory.Mum.chart_cover | exact GlobalTheory.Mum.chart_cover | (intros; apply GlobalTheory.Mum.chart_cover <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianDescendsNearClosedFibre

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem smooth_of_charts_cover : ∀ (Y G U : Scheme.{0}) (J : Type) (ψ : J → (U ⟶ G)) (g : G ⟶ Y) (h : U ⟶ Y), (∀ j, IsOpenImmersion (ψ j)) → (∀ x : G, ∃ j, x ∈ Set.range (ψ j)) → (∀ j, ψ j ≫ g = h) → Smooth h → Smooth g := by
  intro Y G U J ψ g h ho hc hw hs
  let 𝒰 : G.OpenCover := Scheme.Cover.mkOfCovers J (fun _ => U) ψ (fun x => by
    obtain ⟨j, hj⟩ := hc x; exact ⟨j, hj⟩) ho
  haveI : IsZariskiLocalAtSource @Smooth.{0} := HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_openCover (P := @Smooth) 𝒰 ?_
  intro j
  have h2 : 𝒰.f j ≫ g = h := hw j
  rw [h2]; exact hs

theorem descends_near_closed_fibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ N : Near π G', N.Law → ∀ φ, N.Datum φ → ∃ (G : Over (Sp R)) (β : G'.left ⟶ G.left) (i : N.U ⟶ G), Smooth G.hom ∧ IsPullback β G'.hom G.hom π ∧ IsOpenImmersion i.left ∧ N.u ≫ β = pullback.fst _ _ ≫ i.left ∧ pullback.fst G'.hom (pullback.fst π π) ≫ β = φ.hom.left ≫ pullback.fst G'.hom (pullback.snd π π) ≫ β := by
  intro R _ _ _ hA S π hp hs hS G' _ _ hG N hL φ hφ
  obtain ⟨n, a, x, hx, hcov⟩ := GlobalTheory.T.finite_section_translates_cover_semiAbelian R hA S π hp hs hS G' hG N hL
  haveI : IsNoetherianRing R := hA.1
  haveI : IsIntegrallyClosed R := hA.2.2.1
  haveI : Smooth N.U.hom := N.smooth
  obtain ⟨G, β, ψ, hψ, hcovG, hpb, hφβ⟩ := GlobalTheory.T.exists_descent_of_charts_pulled_back_from_flat R S G'.left π G'.hom hp hs hS φ.hom.left (Over.w φ.hom)
    N.U inferInstance (Option (Fin n)) (N.chart x) (fun j => (GlobalTheory.T.chart_isOpenImmersion_over_base S π G' N n x j).1)
    (fun j => (GlobalTheory.T.chart_isOpenImmersion_over_base S π G' N n x j).2) (GlobalTheory.T.smoothNeighbourhood_translates_cover_group S π G' N n x hcov)
    (GlobalTheory.T.descentDatum_carries_translateChart S π G' N n a x (fun i => (hx i).2) φ hφ)
  refine ⟨G, β, Over.homMk (ψ none) (hψ none).2.1, ?_, hpb, (hψ none).1, ?_, hφβ⟩
  · exact smooth_of_charts_cover _ _ _ _ ψ G.hom N.U.hom (fun j => (hψ j).1) hcovG (fun j => (hψ j).2.1) N.smooth
  · simpa [Near.chart] using (hψ none).2.2

end GlobalTheory.Mum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianDescendsNearClosedFibreStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.semiAbelian_descends_near_closedFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ N : Near π G', N.Law → ∀ φ, N.Datum φ → ∃ (G : Over (Sp R)) (β : G'.left ⟶ G.left) (i : N.U ⟶ G), Smooth G.hom ∧ IsPullback β G'.hom G.hom π ∧ IsOpenImmersion i.left ∧ N.u ≫ β = pullback.fst _ _ ≫ i.left ∧ pullback.fst G'.hom (pullback.fst π π) ≫ β = φ.hom.left ≫ pullback.fst G'.hom (pullback.snd π π) ≫ β := by
  first | exact @GlobalTheory.Mum.descends_near_closed_fibre | exact GlobalTheory.Mum.descends_near_closed_fibre | (intros; apply GlobalTheory.Mum.descends_near_closed_fibre <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianDescendsOfDescendsNearClosedFibre

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem descend_of_near : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) →
    ∀ (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G']
    [IsCommMonObj G'], IsSemiAbelian G' → ∀ N : Near π G', N.Law → ∃ (G : Over (Sp R)) (_ : GrpObj G)
    (_ : IsCommMonObj G) (β : G'.left ⟶ G.left) (i : N.U ⟶ G), IsSemiAbelian G ∧ IsGrpPullback G' G π β ∧
    IsOpenImmersion i.left ∧ N.u ≫ β = pullback.fst _ _ ≫ i.left := by
  intro R _ _ _ hA S π hP hS hI G' _ _ hG' N hL
  have hNoeth : IsNoetherianRing R := hA.1
  have hIC : IsIntegrallyClosed R := hA.2.2.1
  obtain ⟨φ, hφ⟩ := GlobalTheory.T.exists_descentDatum_of_descendedMultiplication R hA S π hP hS hI G' hG' N hL
  obtain ⟨G, β, i, hsm, hpb, hop, hu, hc⟩ := GlobalTheory.T.semiAbelian_descends_near_closedFibre R hA S π hP hS hI G' hG' N hL φ hφ
  obtain ⟨g, c, hsa, hgp⟩ := GlobalTheory.T.exists_semiAbelian_descent_along_proper_surjective R S π hP hS hI G' hG' G β hsm hpb φ hφ.1 hc
  exact ⟨G, g, c, β, i, hsa, hgp, hop, hu⟩

end GlobalTheory.Mum
end
end
