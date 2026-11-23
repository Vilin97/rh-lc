module

public import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsSandwichOfHodgeTateFreeStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatZeroFromResolutionAndGagaStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TowerIntersectionOfSandwichSplitStatement
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SplitComps
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.WeilBound.CoreStatements.FlagImmersions.EqOfSpecializesGenPt

section

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace RootFieldNumerics

section General

variable {X : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω']

theorem spMap_genMap (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : Cpt ξ) :
    Spec.map (CommRingCat.ofHom (genMap ξ p)) ≫ X.fromSpecStalk p.1 = ξ := by
  have h1 := Spec.map_comp (X.presheaf.stalkSpecializes p.2) (Scheme.stalkClosedPointTo ξ)
  have h2 := Scheme.SpecMap_stalkSpecializes_fromSpecStalk (X := X) p.2
  exact (congrArg (· ≫ X.fromSpecStalk p.1) h1).trans <| (Category.assoc _ _ _).trans <|
    (congrArg (Spec.map (Scheme.stalkClosedPointTo ξ) ≫ ·) h2).trans
      (Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ)

theorem eq_of_specializes_genPt {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    (hb : Function.Bijective (Scheme.stalkClosedPointTo ξ).hom) (x' : X) (h : x' ⤳ genPt ξ) : x' = genPt ξ := by
  have hF : IsField (X.presheaf.stalk (genPt ξ)) :=
    (RingEquiv.ofBijective _ hb).toMulEquiv.isField (Field.toIsField Ω)
  have h1 : x' ∈ Set.range (X.fromSpecStalk (genPt ξ)) := by
    rw [Scheme.range_fromSpecStalk]; exact h
  have h2 : genPt ξ ∈ Set.range (X.fromSpecStalk (genPt ξ)) := by
    rw [Scheme.range_fromSpecStalk]; exact specializes_rfl
  obtain ⟨u, hu⟩ := h1
  obtain ⟨v, hv⟩ := h2
  let _ := hF.toField
  have huv : u = v := Subsingleton.elim (α := PrimeSpectrum (X.presheaf.stalk (genPt ξ))) u v
  rw [← hu, huv, hv]

theorem exists_factor {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    (hb : Function.Bijective (Scheme.stalkClosedPointTo ξ).hom) (ξ' : Spec (CommRingCat.of Ω') ⟶ X)
    (h : genPt ξ' ⤳ genPt ξ) : ∃ φ : Ω →+* Ω', ξ' = spMap φ ≫ ξ := by
  let e := RingEquiv.ofBijective _ hb
  refine ⟨(genMap ξ' ⟨genPt ξ, h⟩).comp e.symm.toRingHom, ?_⟩
  have h1 : Scheme.stalkClosedPointTo ξ ≫
      CommRingCat.ofHom ((genMap ξ' ⟨genPt ξ, h⟩).comp e.symm.toRingHom) =
      CommRingCat.ofHom (genMap ξ' ⟨genPt ξ, h⟩) := by
    ext a
    exact congrArg (genMap ξ' ⟨genPt ξ, h⟩) (e.symm_apply_apply a)
  have h2 := spMap_genMap ξ' ⟨genPt ξ, h⟩
  have h3 := Spec.map_comp (Scheme.stalkClosedPointTo ξ)
    (CommRingCat.ofHom ((genMap ξ' ⟨genPt ξ, h⟩).comp e.symm.toRingHom))
  refine h2.symm.trans ?_
  refine (congrArg (fun u => Spec.map u ≫ X.fromSpecStalk (genPt ξ)) h1.symm).trans ?_
  refine (congrArg (· ≫ X.fromSpecStalk (genPt ξ)) h3).trans <| (Category.assoc _ _ _).trans ?_
  exact congrArg (spMap ((genMap ξ' ⟨genPt ξ, h⟩).comp e.symm.toRingHom) ≫ ·)
    (Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ)

end General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem splitComps_of_origin {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)}
    {T : Top.RootTower (CMType H) (D.p + D.q)} (o : TowerOrigin Y T) : SplitComps Y := by
  intro Ω _ ξ cst hξ hs a ha
  have : NumberField c.F := { to_charZero := inferInstance, to_finiteDimensional := c.fin }
  obtain ⟨b, hb⟩ := o.comp_onto (genPt ξ) (eq_of_specializes_genPt hξ.bij)
  obtain ⟨φ, hφ⟩ := exists_factor hξ.bij (o.Fx b).ξf (hb ▸ specializes_rfl)
  let r := o.Or 0 b
  have h1 : spMap (r.𝔐.cst.comp (algebraMap (𝓞 c.F) c.F)) =
      spMap ((r.g.comp (φ.comp cst)).comp (algebraMap (𝓞 c.F) c.F)) := by
    rw [← r.𝔐.cst_over, ← Category.assoc, r.g_over, hφ, Category.assoc, Category.assoc, hs,
      ← Spec.map_comp, ← Spec.map_comp]
    rfl
  have h2 : r.𝔐.cst.comp (algebraMap (𝓞 c.F) c.F) =
      (r.g.comp (φ.comp cst)).comp (algebraMap (𝓞 c.F) c.F) :=
    congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
  have h3 : r.𝔐.cst = r.g.comp (φ.comp cst) :=
    IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 c.F)) h2
  obtain ⟨x, hx⟩ := r.g_const (φ a) (ha.algHom φ.toIntAlgHom)
  rw [h3] at hx
  exact ⟨x, φ.injective (r.g.injective hx)⟩

end RootFieldNumerics
end
end

-- Source module: Development.WeilBound.CoreStatements.FlagImmersions.GlobalModelTowerFifthCondition

section

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree (ComponentData ComponentSetting degMu ArLimExists slX)

namespace RootFieldNumerics

theorem global_model_tower_fifth_condition : Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : RootTower (CMType H) (D.p + D.q)) (o : GoodOrigin Y T) (II : IntersectionSystem), IsGlobal Xo l c Y → o.Extra → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → T.I5 II ∧ T.I6 II := by
  intro hG E _ _ _ _ H D Xo l c Y _ T o II _ _ hII hp _
  have hG' := hG
  obtain ⟨-, -, -, -, hRes, -, hF, hGaga, -⟩ := hG'
  refine GlobalTheory.T.tower_intersection_of_sandwich_split hG (GlobalTheory.T.flat_zero_from_resolution_and_gaga hRes hGaga) E H D l (Xo l) c Y T o II hII.1
    (splitComps_of_origin o.toTowerOrigin) fun B a p hpS => ?_
  haveI : Fact p.Prime := ⟨(o.Or B a).𝔐.S_prime p hpS⟩
  exact GlobalTheory.T.exists_sandwich_of_hodge_tate_free hF E H D l (Xo l) c _ _ Y (o.S B) _ _ _ _ (o.Or B a).𝔐 p hpS (by omega) (o.omVB B a p hpS)

end RootFieldNumerics
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.GoodTowerI5Statement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree (ComponentData ComponentSetting degMu ArLimExists slX)

theorem _root_.GlobalTheory.T.good_tower_I5 : Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : RootTower (CMType H) (D.p + D.q)) (o : GoodOrigin Y T) (II : IntersectionSystem), IsGlobal Xo l c Y → o.Extra → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → T.I5 II ∧ T.I6 II := by
  exact RootFieldNumerics.global_model_tower_fifth_condition
end
end
