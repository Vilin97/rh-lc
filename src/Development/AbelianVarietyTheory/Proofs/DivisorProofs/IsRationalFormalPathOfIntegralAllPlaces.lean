module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatPath
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalSectionAtRingPointSpMapCompRestrictStalkStatement
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Basify
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePlacesCentreOutsideOpenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldOneVariableTranscendentalFiniteAndEStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFunctionFieldOfOneVariableOfGenericPointOfCurvStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRatIffExistsRatFunc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRationalPowerSeriesOfAdelicIntegralPositiveRadStatement
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundedDenominatorAlongValuationPath

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

namespace GlobalTheory.Nef

theorem den_along_path : ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (p : Place k E) (u : E) (Y : Scheme.{0}) (ζ : Sp (PowerSeries p.O) ⟶ Y) (U : Y.Opens) (h : ⊤ ≤ (spMap (sc p u) ≫ ζ) ⁻¹ᵁ U) (f : Γ(Y, U)), ∃ e ψ : PowerSeries p.O, PowerSeries.constantCoeff e ≠ 0 ∧ (⊤ ≤ ζ ⁻¹ᵁ U → e = 1) ∧ sc p u e * evAt (spMap (sc p u) ≫ ζ) h f = sc p u ψ := by
  intro k E _ _ _ p u Y ζ U h f
  obtain ⟨hcomp, -, hres, hloc, -⟩ := GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk
  by_cases hU : ⊤ ≤ ζ ⁻¹ᵁ U
  · refine ⟨1, evAt ζ hU f, by simp, fun _ => rfl, ?_⟩
    rw [map_one, _root_.one_mul, hcomp (PowerSeries p.O) (PowerSeries E) Y (sc p u) ζ U hU h f]
  · obtain ⟨_, ⟨U₀, hU₀, rfl⟩, hy0, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (ζ (IsLocalRing.closedPoint (PowerSeries p.O)))) isOpen_univ
    have hζ0 : ⊤ ≤ ζ ⁻¹ᵁ U₀ := (hloc _ _ _ _).2 hy0
    have hη0 : ⊤ ≤ (spMap (sc p u) ≫ ζ) ⁻¹ᵁ U₀ := fun x _ => hζ0 (Set.mem_univ ((spMap (sc p u)) x))
    have hyU := (hloc _ _ _ _).1 h
    have hyU₀ := (hloc _ _ _ _).1 hη0
    obtain ⟨t, htU, hyt⟩ := hU₀.exists_basicOpen_le (V := U) ⟨_, hyU⟩ hyU₀
    have hηt : ⊤ ≤ (spMap (sc p u) ≫ ζ) ⁻¹ᵁ Y.basicOpen t := (hloc _ _ _ _).2 hyt
    haveI := hU₀.isLocalization_basicOpen t
    obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, hmk⟩ := IsLocalization.mk'_surjective (Submonoid.powers t)
      (Y.presheaf.map (homOfLE htU).op f)
    have hspec := IsLocalization.mk'_spec Γ(Y, Y.basicOpen t) a (⟨t ^ n, n, rfl⟩ : Submonoid.powers t)
    simp only at hmk
    rw [hmk] at hspec
    have hle : Y.basicOpen t ≤ U₀ := Y.basicOpen_le t
    have key : evAt (spMap (sc p u) ≫ ζ) hηt (Y.presheaf.map (homOfLE htU).op f) *
        evAt (spMap (sc p u) ≫ ζ) hηt (Y.presheaf.map (homOfLE hle).op (t ^ n)) =
        evAt (spMap (sc p u) ≫ ζ) hηt (Y.presheaf.map (homOfLE hle).op a) := by
      rw [← map_mul]; exact congrArg _ hspec
    have h1 := hres _ _ _ _ _ htU h hηt f
    have h2 := hres _ _ _ _ _ hle hη0 hηt (t ^ n)
    have h3 := hres _ _ _ _ _ hle hη0 hηt a
    have hu : IsUnit (evAt (spMap (sc p u) ≫ ζ) hηt (Y.presheaf.map (homOfLE hle).op t)) :=
      (Y.toRingedSpace.isUnit_res_basicOpen t).map _
    refine ⟨evAt ζ hζ0 (t ^ n), evAt ζ hζ0 a, ?_, fun h' => absurd h' hU, ?_⟩
    · intro h0
      have hu' : IsUnit (sc p u (evAt ζ hζ0 (t ^ n))) := by
        rw [← hcomp (PowerSeries p.O) (PowerSeries E) Y (sc p u) ζ U₀ hζ0 hη0, ← h2, map_pow, map_pow]
        exact hu.pow n
      rw [PowerSeries.isUnit_iff_constantCoeff] at hu'
      apply hu'.ne_zero
      rw [sc, RingHom.comp_apply, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale,
        PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply, h0]
      simp
    · rw [← hcomp (PowerSeries p.O) (PowerSeries E) Y (sc p u) ζ U₀ hζ0 hη0, ← hcomp (PowerSeries p.O) (PowerSeries E) Y (sc p u) ζ U₀ hζ0 hη0, ← h1, ← h2, ← h3, ← key]
      exact mul_comm _ _

end GlobalTheory.Nef
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundedDenominatorAlongValuationPathStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc


theorem _root_.GlobalTheory.T.exists_bounded_denominator_along_valuationPath : ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (p : Place k E) (u : E) (Y : Scheme.{0}) (ζ : Sp (PowerSeries p.O) ⟶ Y) (U : Y.Opens) (h : ⊤ ≤ (spMap (sc p u) ≫ ζ) ⁻¹ᵁ U) (f : Γ(Y, U)), ∃ e ψ : PowerSeries p.O, PowerSeries.constantCoeff e ≠ 0 ∧ (⊤ ≤ ζ ⁻¹ᵁ U → e = 1) ∧ sc p u e * evAt (spMap (sc p u) ≫ ζ) h f = sc p u ψ := by
  first | exact @GlobalTheory.Nef.den_along_path | exact GlobalTheory.Nef.den_along_path | (intros; apply GlobalTheory.Nef.den_along_path <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRationalFormalPathOfRationalExpansions

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

namespace GlobalTheory.Nef

theorem isRatPath_of_isRat : ∀ (F : Type) [Field F] (Y : Scheme.{0}) (ξ : Sp (PowerSeries F) ⟶ Y),
    (∀ (U : Y.Opens), IsAffineOpen U → ∀ (h : ⊤ ≤ ξ ⁻¹ᵁ U) (f : Γ(Y, U)), IsRat (evAt ξ h f)) → IsRatPath ξ := by
  intro F _ Y ξ hrat
  obtain ⟨h1, -, -, h4, h5, h6, -⟩ := GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk
  obtain ⟨U, hUa, hy, -⟩ := (Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens)
    (show ξ (IsLocalRing.closedPoint (PowerSeries F)) ∈ (⊤ : Y.Opens) from trivial)
  have hξ : ⊤ ≤ ξ ⁻¹ᵁ U := (h4 _ Y ξ U).2 hy
  set ψ := evAt ξ hξ
  set ιR := algebraMap (RatFunc F) (LaurentSeries F)
  set ιP := algebraMap (PowerSeries F) (LaurentSeries F)
  have hR : Function.Injective ιR := ιR.injective
  have hmem : ∀ f, (ιP.comp ψ) f ∈ ιR.range := fun f => by
    obtain ⟨ρ, hρ⟩ := (isRat_iff_exists_ratFunc F (ψ f)).1 (hrat U hUa hξ f)
    exact ⟨ρ, hρ⟩
  let e := RingEquiv.ofBijective ιR.rangeRestrict ⟨fun a b hab => hR (congrArg Subtype.val hab), ιR.rangeRestrict_surjective⟩
  let φ : Γ(Y, U) →+* RatFunc F := e.symm.toRingHom.comp ((ιP.comp ψ).codRestrict ιR.range hmem)
  have hφ : ∀ f, ιR (φ f) = ιP (ψ f) := fun f => by
    have := congrArg Subtype.val (e.apply_symm_apply ((ιP.comp ψ).codRestrict ιR.range hmem f))
    exact this
  obtain ⟨β, hβ, hβφ⟩ := h6 (RatFunc F) Y U hUa φ
  refine ⟨β, ?_⟩
  have ha : ⊤ ≤ (spMap ιR ≫ β) ⁻¹ᵁ U := fun x _ => hβ (Set.mem_univ ((spMap ιR) x))
  have hb : ⊤ ≤ (spMap ιP ≫ ξ) ⁻¹ᵁ U := fun x _ => hξ (Set.mem_univ ((spMap ιP) x))
  refine h5 (LaurentSeries F) Y _ _ U hUa ha hb ?_
  refine RingHom.ext fun f => ?_
  rw [h1 _ _ Y ιR β U hβ ha f, h1 _ _ Y ιP ξ U hξ hb f, hβφ]
  exact hφ f

end GlobalTheory.Nef
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRationalFormalPathOfRationalExpansionsStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc


theorem _root_.GlobalTheory.T.isRationalFormalPath_of_rationalExpansions : ∀ (F : Type) [Field F] (Y : Scheme.{0}) (ξ : Sp (PowerSeries F) ⟶ Y), (∀ (U : Y.Opens), IsAffineOpen U → ∀ (h : ⊤ ≤ ξ ⁻¹ᵁ U) (f : Γ(Y, U)), IsRat (evAt ξ h f)) → IsRatPath ξ := by
  first | exact @GlobalTheory.Nef.isRatPath_of_isRat | exact GlobalTheory.Nef.isRatPath_of_isRat | (intros; apply GlobalTheory.Nef.isRatPath_of_isRat <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRationalFormalPathOfIntegralAllPlaces

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option autoImplicit false

namespace GlobalTheory.Nef

private theorem isLocalHom_constantCoeff_ps (O : Type) [CommRing O] [IsLocalRing O] :
    IsLocalHom (PowerSeries.constantCoeff (R := O)) :=
  ⟨fun _ ha => PowerSeries.isUnit_iff_constantCoeff.2 ha⟩

private theorem constantCoeff_comp_sc {k E : Type} [Field k] [Field E] [Algebra k E] (p : Place k E) (u : E) :
    (PowerSeries.constantCoeff (R := E)).comp (sc p u) = p.O.subtype.comp (PowerSeries.constantCoeff (R := p.O)) := by
  refine RingHom.ext fun a => ?_
  show PowerSeries.constantCoeff (PowerSeries.rescale u (PowerSeries.map p.O.subtype a)) = _
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale, pow_zero, _root_.one_mul,
    PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply]
  rfl

private theorem spMap_comp_spMap {A B D : Type} [CommRing A] [CommRing B] [CommRing D] (f : A →+* B) (g : B →+* D) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [spMap, spMap, spMap, CommRingCat.ofHom_comp, Spec.map_comp]

private theorem evAt_eq_of_eq {R : Type} [CommRing R] {X : Scheme.{0}} {a b : Sp R ⟶ X} (e : a = b) {U : X.Opens}
    (h : ⊤ ≤ a ⁻¹ᵁ U) (h' : ⊤ ≤ b ⁻¹ᵁ U) : evAt a h = evAt b h' := by
  subst e; rfl

theorem isRatPath_of_integral_at_places : ∀ (k K E : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k K] [Field E] [Algebra k E] [Algebra K E] [IsScalarTower k K E] [FiniteDimensional K E] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] (x : Sp K ⟶ C), IsGenOver k x →
  ∀ (G : Over C) [GrpObj G] (ξ : Sp (PowerSeries E) ⟶ G.left) (u : Place k E → E), (∀ p, u p ≠ 0) → {p | ord p (u p) ≠ 0}.Finite → 0 < ∑ᶠ p, ord p (u p) → (∀ p : Place k E, ∃ (b : Sp p.O ⟶ C) (ζ : Sp (PowerSeries p.O) ⟶ G.left), spMap p.O.subtype ≫ b = spMap (algebraMap K E) ≫ x ∧ IsPath G 2 b ζ ∧ ξ = spMap (sc p (u p)) ≫ ζ) → IsRatPath ξ := by
  intro k K E _ _ _ _ _ _ _ _ _ _ C _ x hx G _ ξ u hu0 hfin hpos hloc
  choose b ζ hb hpath hξ using hloc
  have hFF : IsFF k E := (GlobalTheory.T.functionFieldOneVariable_transcendental_finite_and_ext k K (GlobalTheory.T.isFunctionFieldOfOneVariable_of_genericPointOfCurve k K C x hx)).2 E
  obtain ⟨p₀, -⟩ : ∃ p, ord p (u p) ≠ 0 := by
    by_contra hc
    push_neg at hc
    rw [finsum_eq_zero_of_forall_eq_zero hc] at hpos
    exact lt_irrefl _ hpos
  apply GlobalTheory.T.isRationalFormalPath_of_rationalExpansions E G.left ξ
  intro U _ h f
  set V : C.Opens := unitSec G ⁻¹ᵁ U with hV
  have hVne : (V : Set C).Nonempty := by
    let q : Sp E := IsLocalRing.closedPoint E
    refine ⟨(spMap p₀.O.subtype ≫ b p₀) q, ?_⟩
    have h2 : spMap (PowerSeries.constantCoeff (R := E)) ≫ ξ = spMap p₀.O.subtype ≫ b p₀ ≫ unitSec G := by
      rw [hξ p₀, ← Category.assoc, spMap_comp_spMap, constantCoeff_comp_sc, ← spMap_comp_spMap, Category.assoc,
        (hpath p₀).zero]
    have h3 : (spMap (PowerSeries.constantCoeff (R := E)) ≫ ξ) q ∈ U := h trivial
    rw [h2] at h3
    exact h3
  have hfinb := GlobalTheory.T.finite_places_centre_outside_open k K E C x hx V hVne
  have hUp : ∀ p, ⊤ ≤ (spMap (sc p (u p)) ≫ ζ p) ⁻¹ᵁ U := fun p => hξ p ▸ h
  choose e ψ he0 he1 heq using fun p => GlobalTheory.T.exists_bounded_denominator_along_valuationPath k E p (u p) G.left (ζ p) U (hUp p) f
  have key : ∀ p, ⊤ ≤ (b p) ⁻¹ᵁ V → ⊤ ≤ (ζ p) ⁻¹ᵁ U := by
    intro p hp
    haveI := isLocalHom_constantCoeff_ps p.O
    rw [GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk.2.2.2.1 (PowerSeries p.O) G.left (ζ p) U]
    rw [← (IsLocalRing.comap_closedPoint (PowerSeries.constantCoeff (R := p.O)) :
      spMap (PowerSeries.constantCoeff (R := p.O)) (IsLocalRing.closedPoint p.O) = _)]
    show (spMap (PowerSeries.constantCoeff (R := p.O)) ≫ ζ p) (IsLocalRing.closedPoint p.O) ∈ U
    rw [(hpath p).zero]
    exact hp trivial
  refine GlobalTheory.T.isRational_powerSeries_of_adelicIntegral_positiveRadius k E hFF (evAt ξ h f) u e ψ hu0 hfin hpos he0 ?_ ?_
  · refine hfinb.subset fun p hp => ⟨b p, hb p, fun hbV => hp ?_⟩
    rw [he1 p (key p hbV), map_one]
    exact isUnit_one
  · intro p
    rw [evAt_eq_of_eq (hξ p) h (hUp p)]
    exact heq p

end GlobalTheory.Nef
end
end
