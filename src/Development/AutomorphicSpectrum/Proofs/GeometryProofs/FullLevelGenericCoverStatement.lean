module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.MemEigSpOfMemHtDual
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFullLevelAt
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsGenOfIsVBOne
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModuliFiniteSurjectiveOverGenericFamily
public import Development.WeilBound.CoreStatements.HodgeTatePoints.MgLevel
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
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TateIsoPullbackEquiv
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.FullLevelStructureProperties

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.XR
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.XR

theorem fullLevel_props : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), ∀ (X : Scheme.{0}) (t : SAB H X) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (N : ℕ), 0 < N → ∀ (z : Ωˣ) (ev : D.La → (Over.mk ξ ⟶ t.G)), IsFullLevelAt D t ξ N z ev → IsPrimitiveRoot z N ∧ (∀ a b, ev (a + b) = ev a * ev b) ∧ (∀ (r : 𝓞 E) a, ev (r • a) = ev a ≫ t.act.act r) ∧ (∀ a, ev a = 1 ↔ ∃ b, a = N • b) ∧ (∀ g : Over.mk ξ ⟶ t.G, g ^ N = 1 ↔ ∃ a, ev a = g) ∧ FullTorsion t.G ξ N ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (i : Ω →+* k) (a b : D.La) (g g' : Over.mk (spMap i ≫ ξ) ⟶ t.G), g.left = spMap i ≫ (ev a).left → g'.left = spMap i ≫ (ev b).left → Out.WeilIs t.G t.PP.L N g g' (unitOn (Units.map i.toMonoidHom z ^ D.EF a b)) :=
  PositivityTheory.HtPt.Mg.level_props

end GlobalTheory.CompanionTheory.Ar.XR
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.FullLevelStructurePropertiesStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.XR
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.full_level_structure_properties : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), ∀ (X : Scheme.{0}) (t : SAB H X) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (N : ℕ), 0 < N → ∀ (z : Ωˣ) (ev : D.La → (Over.mk ξ ⟶ t.G)), IsFullLevelAt D t ξ N z ev → IsPrimitiveRoot z N ∧ (∀ a b, ev (a + b) = ev a * ev b) ∧ (∀ (r : 𝓞 E) a, ev (r • a) = ev a ≫ t.act.act r) ∧ (∀ a, ev a = 1 ↔ ∃ b, a = N • b) ∧ (∀ g : Over.mk ξ ⟶ t.G, g ^ N = 1 ↔ ∃ a, ev a = g) ∧ FullTorsion t.G ξ N ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (i : Ω →+* k) (a b : D.La) (g g' : Over.mk (spMap i ≫ ξ) ⟶ t.G), g.left = spMap i ≫ (ev a).left → g'.left = spMap i ≫ (ev b).left → Out.WeilIs t.G t.PP.L N g g' (unitOn (Units.map i.toMonoidHom z ^ D.EF a b)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.XR.fullLevel_props | exact GlobalTheory.CompanionTheory.Ar.XR.fullLevel_props | (intros; apply GlobalTheory.CompanionTheory.Ar.XR.fullLevel_props <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.FullLevelStructurePullback

section

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.XR
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.XR

theorem isFullLevelAt_move : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), ∀ (X X' : Scheme.{0}) (t : SAB H X) (t' : SAB H X') (f : X' ⟶ X) (m : SABMap t' t f) (Ω Ω' : Type) [Field Ω] [Field Ω'] (i : Ω →+* Ω') (ξ : Sp Ω ⟶ X) (ξ' : Sp Ω' ⟶ X'), ξ' ≫ f = spMap i ≫ ξ → ∀ (N : ℕ) (z : Ωˣ) (ev : D.La → (Over.mk ξ ⟶ t.G)), IsFullLevelAt D t ξ N z ev → ∃ ev' : D.La → (Over.mk ξ' ⟶ t'.G), IsFullLevelAt D t' ξ' N (Units.map i.toMonoidHom z) ev' ∧ ∀ a, (ev' a).left ≫ m.φ = spMap i ≫ (ev a).left := by
  intro E _ _ _ H D X X' t t' f m Ω Ω' _ _ i ξ ξ' hξ N z ev hfull
  have hpb : IsPullback m.φ t'.G.hom t.G.hom f := m.cart.1
  have hsq : ∀ a, (spMap i ≫ (ev a).left) ≫ t.G.hom = ξ' ≫ f := by
    intro a
    rw [Category.assoc, Over.w (ev a)]
    exact hξ.symm
  let ev' : D.La → (Over.mk ξ' ⟶ t'.G) := fun a =>
    Over.homMk (hpb.lift (spMap i ≫ (ev a).left) ξ' (hsq a)) (hpb.lift_snd _ _ _)
  have hfst : ∀ a, (ev' a).left ≫ m.φ = spMap i ≫ (ev a).left := fun a => hpb.lift_fst _ _ _
  have hsnd : ∀ a, (ev' a).left ≫ t'.G.hom = ξ' := fun a => hpb.lift_snd _ _ _
  refine ⟨ev', ?_, hfst⟩
  unfold IsFullLevelAt
  intro k _ _ j
  obtain ⟨I, hIζ, hIev⟩ := hfull k (j.comp i)
  have hx : spMap (j.comp i) ≫ ξ = (spMap j ≫ ξ') ≫ f := by
    rw [spMap_comp, Category.assoc, Category.assoc, hξ]
  obtain ⟨I', hζ, hev⟩ := (tateIsoAt_move E H D X X' t t' f m k (spMap j ≫ ξ') (spMap (j.comp i) ≫ ξ) hx).1 I
  refine ⟨I', ?_, ?_⟩
  · rw [hζ, hIζ]
    simp
  · intro a
    apply hpb.hom_ext
    · rw [hev N a, hIev a, Category.assoc, hfst a, spMap_comp, Category.assoc]
    · rw [Over.w (I'.ev N a), Category.assoc, hsnd a]
      rfl

end GlobalTheory.CompanionTheory.Ar.XR
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.FullLevelStructurePullbackStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.XR
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.full_level_structure_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), ∀ (X X' : Scheme.{0}) (t : SAB H X) (t' : SAB H X') (f : X' ⟶ X) (m : SABMap t' t f) (Ω Ω' : Type) [Field Ω] [Field Ω'] (i : Ω →+* Ω') (ξ : Sp Ω ⟶ X) (ξ' : Sp Ω' ⟶ X'), ξ' ≫ f = spMap i ≫ ξ → ∀ (N : ℕ) (z : Ωˣ) (ev : D.La → (Over.mk ξ ⟶ t.G)), IsFullLevelAt D t ξ N z ev → ∃ ev' : D.La → (Over.mk ξ' ⟶ t'.G), IsFullLevelAt D t' ξ' N (Units.map i.toMonoidHom z) ev' ∧ ∀ a, (ev' a).left ≫ m.φ = spMap i ≫ (ev a).left := by
  first | exact @GlobalTheory.CompanionTheory.Ar.XR.isFullLevelAt_move | exact GlobalTheory.CompanionTheory.Ar.XR.isFullLevelAt_move | (intros; apply GlobalTheory.CompanionTheory.Ar.XR.isFullLevelAt_move <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.FullLevelGenericCover

section

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.XR
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.XR

theorem unitAt_of_pow_eq_one {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} (hN : Flat.NormalCpt ξ)
    {N : ℕ} (hN0 : N ≠ 0) {a : Ω} (ha : a ^ N = 1) (q : Cpt ξ) : unitAt ξ q a :=
  Flat.ZUnit.of_pow_of_normal hN hN0 (by rw [ha]; exact Flat.ZUnit.one)

theorem exists_full_level_over : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), ∀ (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (K Ω : Type) [Field K] [Field Ω] [CharZero Ω] (i : K →+* Ω) (y : Sp K ⟶ Xo.XF c) (N : ℕ) (z : Ωˣ) (ev : D.La → (Over.mk (spMap i ≫ y ≫ Y.j) ⟶ Y.t.G)), 1 ≤ N → IsFullLevelAt D Y.t (spMap i ≫ y ≫ Y.j) N z ev → ∀ (X : Scheme.{0}) (ξ : Sp Ω ⟶ X), IsCptGen ξ → Flat.NormalCpt ξ → ∀ f : X ⟶ Y.X, ξ ≫ f = spMap i ≫ y ≫ Y.j → ∃ (t : SAB H X) (_ : SABMap t Y.t f) (ev' : D.La → (Over.mk ξ ⟶ t.G)), IsFullLevelAt D t ξ N z ev' ∧ FullTorsion t.G ξ N ∧ ∀ q : Cpt ξ, unitAt ξ q (z : Ω) := by
  intro E _ _ _ H D l Xo c Y K Ω _ _ _ i y N z ev hN hlev X ξ _ hnorm f hf
  obtain ⟨t, ⟨m⟩⟩ := GlobalTheory.ModFam.exists_sabPull f Y.t
  have hid : ξ ≫ f = spMap (RingHom.id Ω) ≫ spMap i ≫ y ≫ Y.j := by
    rw [hf]
    have : spMap (RingHom.id Ω) = 𝟙 _ := by simp [spMap]
    rw [this, Category.id_comp]
  obtain ⟨ev', hev', -⟩ := GlobalTheory.T.full_level_structure_pullback E H D Y.X X Y.t t f m Ω Ω (RingHom.id Ω) (spMap i ≫ y ≫ Y.j) ξ hid N z ev hlev
  have hz : Units.map (RingHom.id Ω).toMonoidHom z = z := by ext; rfl
  rw [hz] at hev'
  obtain ⟨hprim, -, -, -, -, hfull, -⟩ := GlobalTheory.T.full_level_structure_properties E H D X t Ω ξ N hN z ev' hev'
  refine ⟨t, m, ev', hev', hfull, fun q => ?_⟩
  have hpow : (z : Ω) ^ N = 1 := by
    have := congrArg Units.val hprim.pow_eq_one
    simpa using this
  exact unitAt_of_pow_eq_one hnorm (by omega) hpow q

end GlobalTheory.CompanionTheory.Ar.XR
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.FullLevelGenericCoverStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.XR
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.full_level_generic_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), ∀ (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (K Ω : Type) [Field K] [Field Ω] [CharZero Ω] (i : K →+* Ω) (y : Sp K ⟶ Xo.XF c) (N : ℕ) (z : Ωˣ) (ev : D.La → (Over.mk (spMap i ≫ y ≫ Y.j) ⟶ Y.t.G)), 1 ≤ N → IsFullLevelAt D Y.t (spMap i ≫ y ≫ Y.j) N z ev → ∀ (X : Scheme.{0}) (ξ : Sp Ω ⟶ X), IsCptGen ξ → Flat.NormalCpt ξ → ∀ f : X ⟶ Y.X, ξ ≫ f = spMap i ≫ y ≫ Y.j → ∃ (t : SAB H X) (_ : SABMap t Y.t f) (ev' : D.La → (Over.mk ξ ⟶ t.G)), IsFullLevelAt D t ξ N z ev' ∧ FullTorsion t.G ξ N ∧ ∀ q : Cpt ξ, unitAt ξ q (z : Ω) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.XR.exists_full_level_over | exact GlobalTheory.CompanionTheory.Ar.XR.exists_full_level_over | (intros; apply GlobalTheory.CompanionTheory.Ar.XR.exists_full_level_over <;> assumption)
end
end
