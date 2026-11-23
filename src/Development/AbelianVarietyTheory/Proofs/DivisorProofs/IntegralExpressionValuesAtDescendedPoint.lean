module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueScalar
public import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterValueMemLocalUnitsMulSubfieldStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBaseWith
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValMemOfCorrPull
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
import Mathlib.Tactic.Linter.Style
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueScalar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepAtBIff
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetryGeneratorValueLocalUnitsMulSubfieldStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGeneratorValuesScalarMulLocalUnitStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFrameValueLocalUnitsMulSubfieldStatement
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefOverOfFiniteOrbit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionIsoOfGroupPullbackGeneric
import Mathlib.Tactic.Basify
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValMemOfCorrPull
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValuationThetaRatioEqBilinear

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodGeneratorsValLocalUnitsMulSubfield

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange

noncomputable section

namespace GlobalTheory.USep.EvG.AtPoint

theorem gm_stalkMap {X Y Z : Scheme.{0}} (r : Z ⟶ Y) (f : Y ⟶ X) (z : Z) (U : X.Opens) (a : Γ(X, U)ˣ) :
    Units.map (r.stalkMap z).hom.toMonoidHom (gm f (r z) U a) = gm (r ≫ f) z U a := by
  by_cases h : f (r z) ∈ U
  · apply Units.ext
    rw [Units.coe_map, gm_val f (r z) U h, gm_val (r ≫ f) z U h]
    exact Scheme.Hom.germ_stalkMap_apply r (f ⁻¹ᵁ U) z h _
  · have h' : (r ≫ f) z ∉ U := h
    rw [gm, dite_eq_right h, gm, dite_eq_right h']
    simp

theorem val_stalkMap {X Y Y' Z : Scheme.{0}} {L : LB X} {Ix : Type} [Fintype Ix] {φ : Ix → (Y ⟶ X)} {ε : Ix → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (g : Y' ⟶ Y) (r : Z ⟶ Y') (z : Z) (J : (Z ⟶ X) → L.ι) :
    Units.map (r.stalkMap z).hom.toMonoidHom (val t g (r z) (fun ψ => J (r ≫ ψ))) = val t (r ≫ g) z J := by
  rw [val_of t (r ≫ g) z J (fun k => J (r ≫ g ≫ φ k)) (fun k => by rw [Category.assoc])]
  exact gm_stalkMap r g z _ _

end GlobalTheory.USep.EvG.AtPoint

open GlobalTheory.USep.EvG.AtPoint in
theorem GlobalTheory.USep.EvG.fromBase_tau_val : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) →
    ∀ (D : DegPre V₁) (τ₀ : GlobalTheory.UChart.Gens D) (W₀ : Type) [CommRing W₀] (ib : W₀ →+* V₁) (B₀ : Over (Sp W₀)) [GrpObj B₀]
      (M₀ : LB B₀.left) (c₀ : D.X → (Sp W₀ ⟶ B₀.left))
      (τ₁ : ∀ a b : D.X, LB.Gen (LB.LinComb M₀ (K := Fin 4) ![c₀ (a + b), c₀ a, c₀ b, c₀ 0] ![-1, 1, 1, -1]))
      (β : D.P.A.left ⟶ B₀.left) (w : LB.Iso D.P.L (M₀.pull β)), GlobalTheory.USep.EvG.FromBaseWith D τ₀ ib B₀ M₀ c₀ τ₁ β w →
    ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ a, ev (ib a) ∈ k₀) →
    ∀ (z : Sp K) (J : (Sp K ⟶ D.P.A.left) → D.P.L.ι) (J₀ : (Sp K ⟶ B₀.left) → M₀.ι), Good D.P.L z J → Good M₀ z J₀ →
    ∀ a b : D.X, ∃ c ∈ k₀, (val (τ₀ a b) (spMap ev) z J).val =
      (GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ (D.c (a + b)).left) * (GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ (D.c a).left))⁻¹ *
        (GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ (D.c b).left))⁻¹ * GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ (D.c 0).left)).val * toStk z c := by
  intro V₁ _ _ _ _ _ D τ₀ W₀ _ ib B₀ _ M₀ c₀ τ₁ β w hFB K _ _ ev k₀ _ hk z J J₀ hJ hJ₀ a b
  obtain ⟨-, -, -, -, -, -, hlast⟩ := hFB
  have hJ' : Good D.P.L ((spMap ev) z) (fun ψ => J (spMap ev ≫ ψ)) := fun ψ => hJ (spMap ev ≫ ψ)
  have hJ₀' : Good M₀ ((spMap ev) z) (fun ψ => J₀ (spMap ev ≫ ψ)) := fun ψ => hJ₀ (spMap ev ≫ ψ)
  have E := congrArg (Units.map ((spMap ev).stalkMap z).hom.toMonoidHom) (hlast a b ((spMap ev) z) _ _ hJ' hJ₀')
  simp only [map_mul, map_inv, val_stalkMap, gm_stalkMap, Category.comp_id] at E
  have hg : ∀ x : D.X, gm (spMap ev ≫ UChart.cpt D x) z
      (((M₀.pull β).div D.P.L).U (fun _ => J₀ (spMap ev ≫ UChart.cpt D x ≫ β), J (spMap ev ≫ UChart.cpt D x)))
      (w.s (fun _ => J₀ (spMap ev ≫ UChart.cpt D x ≫ β), J (spMap ev ≫ UChart.cpt D x))) =
      GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ (D.c x).left) := by
    intro x
    show _ = gw w _ z _ _
    rw [Category.assoc]
    rfl
  rw [hg (a + b), hg a, hg b, hg 0, ← ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp] at E
  obtain ⟨c, hc, hv⟩ := GlobalTheory.Poinc.Sep.val_spMap_mem k₀ (τ₁ a b) (ev.comp ib) hk z hJ₀
  refine ⟨c, hc, ?_⟩
  rw [E, Units.val_mul, hv]
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodGeneratorsValLocalUnitsMulSubfieldStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange


theorem _root_.GlobalTheory.T.periodGenerators_val_localUnits_mul_subfield : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) →
    ∀ (D : DegPre V₁) (τ₀ : GlobalTheory.UChart.Gens D) (W₀ : Type) [CommRing W₀] (ib : W₀ →+* V₁) (B₀ : Over (Sp W₀)) [GrpObj B₀]
      (M₀ : LB B₀.left) (c₀ : D.X → (Sp W₀ ⟶ B₀.left))
      (τ₁ : ∀ a b : D.X, LB.Gen (LB.LinComb M₀ (K := Fin 4) ![c₀ (a + b), c₀ a, c₀ b, c₀ 0] ![-1, 1, 1, -1]))
      (β : D.P.A.left ⟶ B₀.left) (w : LB.Iso D.P.L (M₀.pull β)), GlobalTheory.USep.EvG.FromBaseWith D τ₀ ib B₀ M₀ c₀ τ₁ β w →
    ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ a, ev (ib a) ∈ k₀) →
    ∀ (z : Sp K) (J : (Sp K ⟶ D.P.A.left) → D.P.L.ι) (J₀ : (Sp K ⟶ B₀.left) → M₀.ι), Good D.P.L z J → Good M₀ z J₀ →
    ∀ a b : D.X, ∃ c ∈ k₀, (val (τ₀ a b) (spMap ev) z J).val =
      (GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ (D.c (a + b)).left) * (GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ (D.c a).left))⁻¹ *
        (GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ (D.c b).left))⁻¹ * GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ (D.c 0).left)).val * toStk z c := by
  first | exact @GlobalTheory.USep.EvG.fromBase_tau_val | exact GlobalTheory.USep.EvG.fromBase_tau_val | (intros; apply GlobalTheory.USep.EvG.fromBase_tau_val <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointsProjectionsDefinedOverSubfield

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange

namespace GlobalTheory.USep.EvG

theorem points_defOver : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) →
    ∀ (D : DegPre V₁) (τ₀ : GlobalTheory.UChart.Gens D) (W₀ : Type) [CommRing W₀] (ib : W₀ →+* V₁) (B₀ : Over (Sp W₀)) [GrpObj B₀]
      (M₀ : LB B₀.left) (c₀ : D.X → (Sp W₀ ⟶ B₀.left))
      (τ₁ : ∀ a b : D.X, LB.Gen (LB.LinComb M₀ (K := Fin 4) ![c₀ (a + b), c₀ a, c₀ b, c₀ 0] ![-1, 1, 1, -1]))
      (β : D.P.A.left ⟶ B₀.left) (w : LB.Iso D.P.L (M₀.pull β)), GlobalTheory.USep.EvG.FromBaseWith D τ₀ ib B₀ M₀ c₀ τ₁ β w →
    ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ a, ev (ib a) ∈ k₀) →
    ∀ (N : ℕ), 1 ≤ N → ∀ (b : 𝟙_ (Over (Sp V₁)) ⟶ D.P.A), b ^ N = 1 → ∀ a : D.X,
      DefOver k₀ (spMap ev ≫ b.left ≫ β) ∧ DefOver k₀ (spMap ev ≫ (D.c a).left ≫ β) ∧
        DefOver k₀ (spMap ev ≫ (b * D.c a).left ≫ β) ∧ DefOver k₀ (spMap ev ≫ (D.c a * b).left ≫ β) := by
  intro V₁ _ _ _ hV hunit D τ₀ W₀ _ ib B₀ _ M₀ c₀ τ₁ β w hF K _ _ ev k₀ hk₀ hk N hN b hb a
  classical
  obtain ⟨-, -, hβ, -, hc, -, -⟩ := hF
  haveI : IsNoetherianRing V₁ := hV.1
  have hg : spMap ev ≫ spMap ib = spMap (ev.comp ib) := by
    simp only [spMap, ← Spec.map_comp]; rfl
  obtain ⟨Φ, hΦ⟩ :=
    GlobalTheory.GroupBplus.Aff.exists_mulEquiv_points_of_isGrpPullback hβ (spMap ev) (spMap (ev.comp ib)) hg

  have htor : ∀ x : Over.mk (spMap ev) ⟶ D.P.A, x ^ N = 1 → DefOver k₀ (x.left ≫ β) := by
    intro x hx
    have hNK : (N : K) ≠ 0 := by
      have := ((hunit N (by omega)).map ev).ne_zero
      simpa using this
    have hcard := (GlobalTheory.abelianSchemeLaws_all.1.mulN (Sp V₁) D.P N hN).2.2.2.2 K (spMap ev) hNK
    have hfin : Finite {y : Over.mk (spMap ev) ⟶ D.P.A // y ^ N = 1} :=
      Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ (by omega))
    refine defOver_of_finite_orbit K k₀ hk₀ _ _ ((Set.finite_range
      fun y : {y : Over.mk (spMap ev) ⟶ D.P.A // y ^ N = 1} => (Φ y.1).left).subset ?_)
    rintro _ ⟨σ, hσ, rfl⟩
    have hσf : spMap σ.toRingHom ≫ spMap (ev.comp ib) = spMap (ev.comp ib) := by
      have e1 : (σ.toRingHom).comp (ev.comp ib) = ev.comp ib := RingHom.ext fun u => hσ _ (hk u)
      have e0 : spMap σ.toRingHom ≫ spMap (ev.comp ib) = spMap ((σ.toRingHom).comp (ev.comp ib)) := by
        simp only [spMap, ← Spec.map_comp]; rfl
      rw [e0, e1]
    let hh : Over.mk (spMap (ev.comp ib)) ⟶ Over.mk (spMap (ev.comp ib)) := Over.homMk (spMap σ.toRingHom) hσf
    refine ⟨⟨Φ.symm (hh ≫ Φ x), ?_⟩, ?_⟩
    · rw [← map_pow, ← MonObj.comp_pow, ← map_pow, hx, map_one, MonObj.comp_one, map_one]
    · show (Φ (Φ.symm (hh ≫ Φ x))).left = _
      rw [MulEquiv.apply_symm_apply, Over.comp_left, hΦ]
      rfl

  have hsub : spMap k₀.subtype ≫ spMap ((ev.comp ib).codRestrict k₀ hk) = spMap (ev.comp ib) := by
    simp only [spMap, ← Spec.map_comp]; rfl
  let j : Over.mk (spMap (ev.comp ib)) ⟶ Over.mk (spMap ((ev.comp ib).codRestrict k₀ hk)) :=
    Over.homMk (spMap k₀.subtype) hsub
  have hdesc : ∀ p : Over.mk (spMap (ev.comp ib)) ⟶ B₀, DefOver k₀ p.left →
      ∃ p₀ : Over.mk (spMap ((ev.comp ib).codRestrict k₀ hk)) ⟶ B₀, j ≫ p₀ = p := by
    intro p ⟨P₀, hP₀⟩
    have e : P₀ ≫ B₀.hom = spMap ((ev.comp ib).codRestrict k₀ hk) := spMap_subtype_cancel k₀ (by
      rw [← Category.assoc, hP₀, Over.w p, hsub]; rfl)
    exact ⟨Over.homMk P₀ e, Over.OverMorphism.ext hP₀⟩
  have hmul : ∀ p q : Over.mk (spMap (ev.comp ib)) ⟶ B₀, DefOver k₀ p.left → DefOver k₀ q.left →
      DefOver k₀ (p * q).left := by
    intro p q hp hq
    obtain ⟨p₀, rfl⟩ := hdesc p hp
    obtain ⟨q₀, rfl⟩ := hdesc q hq
    rw [← MonObj.comp_mul]
    exact ⟨(p₀ * q₀).left, rfl⟩
  have hprod : ∀ y z : Over.mk (spMap ev) ⟶ D.P.A, DefOver k₀ (y.left ≫ β) → DefOver k₀ (z.left ≫ β) →
      DefOver k₀ ((y * z).left ≫ β) := by
    intro y z hy hz
    rw [← hΦ, map_mul]
    exact hmul _ _ (by rw [hΦ]; exact hy) (by rw [hΦ]; exact hz)

  let h : Over.mk (spMap ev) ⟶ 𝟙_ (Over (Sp V₁)) := Over.homMk (spMap ev) (Category.comp_id _)
  have hl : ∀ y : 𝟙_ (Over (Sp V₁)) ⟶ D.P.A, spMap ev ≫ y.left ≫ β = (h ≫ y).left ≫ β := by
    intro y
    rw [Over.comp_left, Category.assoc]
    rfl
  have h1 : DefOver k₀ (spMap ev ≫ b.left ≫ β) := by
    rw [hl]
    exact htor _ (by rw [← MonObj.comp_pow, hb, MonObj.comp_one])
  have h2 : DefOver k₀ (spMap ev ≫ (D.c a).left ≫ β) := by
    have e : spMap ev ≫ (D.c a).left ≫ β = spMap (ev.comp ib) ≫ c₀ a := by
      rw [show (D.c a).left ≫ β = spMap ib ≫ c₀ a from hc a, ← Category.assoc, hg]
    rw [e]
    exact defOver_comp k₀ (defOver_spMap k₀ _ hk) _
  refine ⟨h1, h2, ?_, ?_⟩
  · rw [hl, MonObj.comp_mul]
    exact hprod _ _ (by rw [← hl]; exact h1) (by rw [← hl]; exact h2)
  · rw [hl, MonObj.comp_mul]
    exact hprod _ _ (by rw [← hl]; exact h2) (by rw [← hl]; exact h1)

end GlobalTheory.USep.EvG
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointsProjectionsDefinedOverSubfieldStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange


theorem _root_.GlobalTheory.T.torsionPoints_projections_defined_over_subfield : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) →
    ∀ (D : DegPre V₁) (τ₀ : GlobalTheory.UChart.Gens D) (W₀ : Type) [CommRing W₀] (ib : W₀ →+* V₁) (B₀ : Over (Sp W₀)) [GrpObj B₀]
      (M₀ : LB B₀.left) (c₀ : D.X → (Sp W₀ ⟶ B₀.left))
      (τ₁ : ∀ a b : D.X, LB.Gen (LB.LinComb M₀ (K := Fin 4) ![c₀ (a + b), c₀ a, c₀ b, c₀ 0] ![-1, 1, 1, -1]))
      (β : D.P.A.left ⟶ B₀.left) (w : LB.Iso D.P.L (M₀.pull β)), GlobalTheory.USep.EvG.FromBaseWith D τ₀ ib B₀ M₀ c₀ τ₁ β w →
    ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ a, ev (ib a) ∈ k₀) →
    ∀ (N : ℕ), 1 ≤ N → ∀ (b : 𝟙_ (Over (Sp V₁)) ⟶ D.P.A), b ^ N = 1 → ∀ a : D.X,
      DefOver k₀ (spMap ev ≫ b.left ≫ β) ∧ DefOver k₀ (spMap ev ≫ (D.c a).left ≫ β) ∧
        DefOver k₀ (spMap ev ≫ (b * D.c a).left ≫ β) ∧ DefOver k₀ (spMap ev ≫ (D.c a * b).left ≫ β) := by
  first | exact @GlobalTheory.USep.EvG.points_defOver | exact GlobalTheory.USep.EvG.points_defOver | (intros; apply GlobalTheory.USep.EvG.points_defOver <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralExpressionValuesAtDescendedPoint

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange

noncomputable section

namespace GlobalTheory.USep.EvG

theorem unit_of_val {K S : Type} [Field K] [CommRing S] [Nontrivial S] (f : K →+* S) {u v : Sˣ} {c : K}
    (h : u.val = v.val * f c) : ∃ m : Kˣ, (m : K) = c ∧ u = v * Units.map f.toMonoidHom m := by
  have hc : c ≠ 0 := by
    rintro rfl
    rw [map_zero, mul_zero] at h
    exact u.ne_zero h
  exact ⟨Units.mk0 c hc, rfl, Units.ext (by rw [h, Units.val_mul]; rfl)⟩

theorem toStk_surj' {K : Type} [Field K] (z : Sp K) : Function.Surjective (toStk z) := fun s => by
  obtain ⟨U, hU, a, rfl⟩ := (Sp K).presheaf.germ_exist s
  exact ⟨_, (toStk_valF_gs (𝟙 _) U z hU a).trans (gs_eq _ _ _ hU _)⟩

theorem units_identity {U : Type} [CommGroup U] (gO gB gP gC gCn R M2 M3 M4 M5 : U) :
    (gO⁻¹ * gB * M2) ^ 2 * (gP * gC⁻¹ * gB⁻¹ * gO * M3) ^ 2 * (gCn⁻¹ * gC * M4) *
        (gO * gC⁻¹ * gCn⁻¹ * gO * M5)⁻¹ * (R ^ 2)⁻¹ =
      gP ^ 2 * (gO⁻¹ ^ 2 * (R ^ 2)⁻¹) * (M2 ^ 2 * M3 ^ 2 * M4 * M5⁻¹) := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_pow]
  abel

theorem sq_cancel {S : Type} [CommRing S] (a b c d f : S) (h : a * c = 1) :
    (a * b) ^ 2 * (c ^ 2 * d * f) = b ^ 2 * (d * f) := by
  linear_combination (a * c + 1) * b ^ 2 * d * f * h

theorem c_zero_eta {V₁ : Type} [CommRing V₁] [IsDomain V₁] (D : DegPre V₁) : D.c 0 = η[D.P.A] := by
  rw [GlobalTheory.Poinc.ThetaOne.c_zero]
  rfl

theorem ev_values : ∀ (N₁ : ℕ), 2 ≤ N₁ → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ →
    (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) → ∀ (D : DegPre V₁) (X C : Type) [AddCommGroup X] (e : X ≃+ D.X)
    (τ₀ : GlobalTheory.UChart.Gens D) (θ : SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))),
    (∀ (R' : Type) [CommRing R'] (f : V₁ →+* R') θ',
      IsPullSecLC D.P.L (D.famφB 0) (DegPre.famε 1) (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left θ θ' →
      GlobalTheory.Poinc.ThetaOne.OneBasisAt D f θ') →
    ∀ (b : C → (𝟙_ (Over (Sp V₁)) ⟶ D.P.A)), (∀ c, b c ^ N₁ = 1) →
    ∀ (t : ∀ c, LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, (b c).left] (DegPre.lineε 1))),
      (∀ c, (t c).IsGen ∧ ∀ κ : LB.Gen (kapLB D (𝟙 D.P.A ^ N₁) (N₁ ^ 2) 1), Normd κ →
        ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp V₁) (z : Z) J, Good D.P.L z J →
          val (t c) r z J ^ (N₁ ^ 2) * val κ (r ≫ (b c).left) z J = 1) →
    ∀ (χt : ∀ (mu : X) (c : C), LB.Gen (LB.LinComb D.P.L
        ![(D.c (e mu) * b c).left, (D.c (e mu)).left, (b c).left, (η[D.P.A]).left] DegPre.gtε)),
      (∀ mu c, (χt mu c).IsGen ∧ ∀ (T : Over (Sp V₁)) (z : T.left) J, Good D.P.L z J →
        ∏ i ∈ Finset.range N₁, cubV D.cub z J (toUnit T ≫ D.c (e mu)) (toUnit T ≫ b c ^ i) (toUnit T ≫ b c) =
          val (χt mu c) T.hom z J ^ N₁) →
    ∀ (G : X → C → V₁),
      (∀ mu c (Z : Scheme.{0}) (r : Z ⟶ Sp V₁) (z : Z) J, Good D.P.L z J →
        gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of V₁)).inv.hom (G mu c)) =
          sval (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) (r ≫ (b c * D.c (e mu)).left) z J ^ 2 *
            (val (t c) r z J ^ 2 * val (χt mu c) r z J ^ 2 * val D.sym (r ≫ (D.c (e mu)).left) z J *
              (val (τ₀ (e mu) (-e mu)) r z J)⁻¹ * (rigV D r z J ^ 2)⁻¹).val) →
    ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ →
    ∀ (W₀ : Type) [CommRing W₀] (ib : W₀ →+* V₁), GlobalTheory.UChart.FromBase D τ₀ ib → (∀ a, ev (ib a) ∈ k₀) →
    ∃ Λ : K, ∀ mu c, ∃ r ∈ k₀, ev (G mu c) = Λ * r := by
  intro N₁ hN V₁ _ _ _ hV hunit D X C _ e τ₀ θ hθ b hb t ht χt hχt G hG K _ _ ev k₀ hk₀ W₀ _ ib hB hib
  obtain ⟨B₀, iG, M₀, c₀, τ₁, β, w, hFB⟩ := (fromBase_iff D τ₀ ib).1 hB
  have hM₀ : M₀.IsLB := hFB.2.1
  let z : Sp K := IsLocalRing.closedPoint K
  choose J hJ using fun ψ : Sp K ⟶ D.P.A.left => exists_chart D.P.isLB (ψ z)
  choose J₀ hJ₀ using fun ψ : Sp K ⟶ B₀.left => exists_chart hM₀ (ψ z)
  have gJ : Good D.P.L z J := hJ
  have gJ₀ : Good M₀ z J₀ := hJ₀
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.thetaGenerator_values_scalar_mul_localUnit V₁ hV hunit D τ₀ W₀ ib B₀ M₀ c₀ τ₁ β w hFB K ev k₀ hk₀ hib z J J₀ gJ gJ₀ θ hθ
  set r : Sp K ⟶ Sp V₁ := spMap ev with hr
  set U0 : ((Sp K).presheaf.stalk z)ˣ := (gwx w z J J₀ (r ≫ (D.c 0).left))⁻¹ ^ 2 * (rigV D r z J ^ 2)⁻¹ with hU0
  have hO : r ≫ (η[D.P.A]).left = r ≫ (D.c 0).left := by rw [c_zero_eta]
  have key : ∀ mu c, ∃ q ∈ k₀, toStk z (ev (G mu c)) = toStk z (κ ^ 2 * q) * U0.val := by
    intro mu c
    obtain ⟨hBd, -, hPd, -⟩ := GlobalTheory.T.torsionPoints_projections_defined_over_subfield V₁ hV hunit D τ₀ W₀ ib B₀ M₀ c₀ τ₁ β w hFB K ev k₀ hk₀ hib N₁ (by omega)
      (b c) (hb c) (e mu)
    obtain ⟨c1, hc1, e1⟩ := hκ (b c * D.c (e mu)) hPd
    obtain ⟨c2, hc2, e2⟩ := GlobalTheory.T.torsionFrame_value_localUnits_mul_subfield V₁ hV hunit D τ₀ W₀ ib B₀ M₀ c₀ τ₁ β w hFB K ev k₀ hk₀ hib z J J₀ gJ gJ₀ N₁ hN
      (b c) (hb c) hBd (t c) (ht c)
    obtain ⟨c3, hc3, e3⟩ := GlobalTheory.T.characterValue_mem_localUnits_mul_subfield V₁ hV hunit D τ₀ W₀ ib B₀ M₀ c₀ τ₁ β w hFB K ev k₀ hk₀ hib z J J₀ gJ gJ₀ N₁ hN
      (e mu) (b c) (hb c) hBd (χt mu c) (hχt mu c)
    obtain ⟨c4, hc4, e4⟩ := GlobalTheory.T.symmetryGenerator_value_localUnits_mul_subfield V₁ hV hunit D τ₀ W₀ ib B₀ M₀ c₀ τ₁ β w hFB K ev k₀ hk₀ hib z J J₀ gJ gJ₀ (e mu)
    obtain ⟨c5, hc5, e5⟩ := GlobalTheory.T.periodGenerators_val_localUnits_mul_subfield V₁ hV hunit D τ₀ W₀ ib B₀ M₀ c₀ τ₁ β w hFB K ev k₀ hk₀ hib z J J₀ gJ gJ₀
      (e mu) (-e mu)
    have hPP : r ≫ (D.c (e mu) * b c).left = r ≫ (b c * D.c (e mu)).left := by rw [mul_comm]
    have h00 : r ≫ (D.c (e mu + -e mu)).left = r ≫ (D.c 0).left := by rw [add_neg_cancel]
    rw [hO] at e2 e3
    rw [hPP] at e3
    rw [h00] at e5
    obtain ⟨m2, rfl, u2⟩ := unit_of_val (toStk z) e2
    obtain ⟨m3, rfl, u3⟩ := unit_of_val (toStk z) e3
    obtain ⟨m4, rfl, u4⟩ := unit_of_val (toStk z) e4
    obtain ⟨m5, rfl, u5⟩ := unit_of_val (toStk z) e5
    have h1 := hG mu c (Sp K) r z J gJ
    rw [u2, u3, u4, u5, e1, units_identity, ← hU0] at h1
    have hL : gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of V₁)).inv.hom (G mu c)) = toStk z (ev (G mu c)) := by
      have := GlobalTheory.RatioVal.gs_specMap ev z ((Scheme.ΓSpecIso (CommRingCat.of V₁)).inv.hom (G mu c))
      rw [Iso.inv_hom_id_apply] at this
      exact this
    refine ⟨c1 ^ 2 * ((m2 : K) ^ 2 * (m3 : K) ^ 2 * (m4 : K) * (m5 : K)⁻¹),
      k₀.mul_mem (k₀.pow_mem hc1 2) (k₀.mul_mem (k₀.mul_mem (k₀.mul_mem (k₀.pow_mem hc2 2) (k₀.pow_mem hc3 2)) hc4)
        (k₀.inv_mem hc5)), ?_⟩
    rw [← hL, h1, Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val,
      sq_cancel _ _ _ _ _ (Units.inv_mul _)]
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, ← map_inv, Units.coe_map, MonoidHom.coe_coe,
      RingHom.toMonoidHom_eq_coe, Units.val_inv_eq_inv_val, map_mul, map_pow]
    ring
  obtain ⟨lam, hlam⟩ := toStk_surj' z U0.val
  refine ⟨κ ^ 2 * lam, fun mu c => ?_⟩
  obtain ⟨q, hq, eq⟩ := key mu c
  refine ⟨q, hq, (toStk z).injective ?_⟩
  rw [eq, ← hlam, ← map_mul]
  congr 1
  ring

end GlobalTheory.USep.EvG
end
end
end
