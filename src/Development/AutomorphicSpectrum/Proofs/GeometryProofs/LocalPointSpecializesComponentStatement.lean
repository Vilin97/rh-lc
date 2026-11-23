module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsGenOfIsVBOne
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointNormalCoords
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GermStalkClosedPointToBaseChange
public import Mathlib.NumberTheory.NumberField.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StableEig

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.NumberFieldMapsLocalRingUnique

section

@[expose] public section

namespace GlobalTheory.CompanionTheory.Ggeo.TwoMaps

open Polynomial

theorem ringHom_eq_of_comp_eq (K : Type) [Field K] [NumberField K] (B : Type) [CommRing B]
    [IsLocalRing B] (Ω : Type) [Field Ω] (π : B →+* Ω) (s t : K →+* B)
    (h : π.comp s = π.comp t) : s = t := by
  refine RingHom.ext fun a => ?_
  have hsep : (minpoly ℚ a).Separable := Algebra.IsSeparable.isSeparable ℚ a
  obtain ⟨p, hp⟩ : ∃ p : K[X], p = (minpoly ℚ a).map (algebraMap ℚ K) := ⟨_, rfl⟩
  have hpa : p.eval a = 0 := by
    rw [hp, eval_map_algebraMap]
    exact minpoly.aeval ℚ a
  have hpd : p.derivative.eval a ≠ 0 := by
    rw [hp, derivative_map, eval_map_algebraMap]
    exact hsep.aeval_derivative_ne_zero (minpoly.aeval ℚ a)
  have hst : p.map s = p.map t := by
    rw [hp, Polynomial.map_map, Polynomial.map_map]
    congr 1
    exact RingHom.ext_rat _ _
  have hx : (p.map s).eval (s a) = 0 := by
    rw [eval_map, eval₂_at_apply, hpa, map_zero]
  have hy : (p.map s).eval (t a) = 0 := by
    rw [hst, eval_map, eval₂_at_apply, hpa, map_zero]
  have hdx : (p.map s).derivative.eval (s a) = s (p.derivative.eval a) := by
    rw [derivative_map, eval_map, eval₂_at_apply]
  have hunit : IsUnit ((p.map s).derivative.eval (s a)) := by
    rw [hdx]
    exact (IsUnit.mk0 _ hpd).map s
  obtain ⟨k, hk⟩ := binomExpansion (p.map s) (s a) (t a - s a)
  have hd : ¬ IsUnit (t a - s a) := by
    intro hu
    have h0 : π (t a - s a) = 0 := by
      have := RingHom.congr_fun h a
      simp only [RingHom.comp_apply] at this
      rw [map_sub, this, sub_self]
    exact (hu.map π).ne_zero h0
  have hkd : ¬ IsUnit (-(k * (t a - s a))) := by
    rw [IsUnit.neg_iff]
    exact fun hu => hd (isUnit_of_mul_isUnit_right hu)
  have hu2 : IsUnit ((p.map s).derivative.eval (s a) + k * (t a - s a)) := by
    by_contra hc
    have hsum := IsLocalRing.nonunits_add (R := B) (a := (p.map s).derivative.eval (s a) + k * (t a - s a))
      (b := -(k * (t a - s a))) hc hkd
    apply hsum
    simpa using hunit
  have hmul : (t a - s a) * ((p.map s).derivative.eval (s a) + k * (t a - s a)) = 0 := by
    have e : s a + (t a - s a) = t a := by ring
    rw [e, hy, hx] at hk
    linear_combination -hk
  have hz : t a - s a = 0 := by
    simpa using (hu2.mul_left_eq_zero).1 hmul
  exact (sub_eq_zero.1 hz).symm

end GlobalTheory.CompanionTheory.Ggeo.TwoMaps
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.NumberFieldMapsLocalRingUniqueStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.number_field_maps_local_ring_unique : ∀ (K : Type) [Field K] [NumberField K] (B : Type) [CommRing B] [IsLocalRing B] (Ω : Type) [Field Ω] (π : B →+* Ω) (s t : K →+* B), π.comp s = π.comp t → s = t := by
  first | exact @GlobalTheory.CompanionTheory.Ggeo.TwoMaps.ringHom_eq_of_comp_eq | exact GlobalTheory.CompanionTheory.Ggeo.TwoMaps.ringHom_eq_of_comp_eq | (intros; apply GlobalTheory.CompanionTheory.Ggeo.TwoMaps.ringHom_eq_of_comp_eq <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalPointSpecializesComponent

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.LocFn

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LocFn.Coef

section General

variable {X : Scheme.{0}} {K R : Type} [CommRing K] [CommRing R] [IsLocalRing R]

def cst (g : X ⟶ Sp K) (x : X) : K →+* X.presheaf.stalk x :=
  ((X.presheaf.germ ⊤ x trivial).hom.comp g.appTop.hom).comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom

theorem stalkClosedPointTo_germ_top (z : Sp R ⟶ X) (t : Γ(X, ⊤)) :
    (Scheme.stalkClosedPointTo z).hom ((X.presheaf.germ ⊤ (centre z) trivial).hom t) =
      (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (z.appTop.hom t) := by
  have h : X.presheaf.germ ⊤ (centre z) trivial ≫ Scheme.stalkClosedPointTo z =
      z.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom := by
    refine (Scheme.germ_stalkClosedPointTo z ⊤ trivial).trans ?_
    simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, Scheme.Hom.appTop]
    congr 1
  exact congrArg (fun q => q.hom t) h

theorem val_cst (z : Sp R ⟶ X) (g : X ⟶ Sp K) (φ : K →+* R) (h : z ≫ g = spMap φ) (k : K) :
    (Scheme.stalkClosedPointTo z).hom (cst g (centre z) k) = φ k := by
  show (Scheme.stalkClosedPointTo z).hom ((X.presheaf.germ ⊤ (centre z) trivial).hom
    (g.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom k))) = φ k
  rw [stalkClosedPointTo_germ_top]
  have h2 : z.appTop.hom (g.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom k)) =
      (Spec.map (CommRingCat.ofHom φ)).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom k) := by
    have h' : z ≫ g = Spec.map (CommRingCat.ofHom φ) := h
    rw [← h']; simp only [Scheme.Hom.comp_appTop]; rfl
  rw [h2]
  have h3 := congrArg (fun q => q.hom k) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  have h3' : (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (φ k) =
      (Spec.map (CommRingCat.ofHom φ)).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom k) := h3
  rw [← h3']
  simp

variable {Ω : Type} [Field Ω]

theorem genMap_cst (ξ : Sp Ω ⟶ X) (g : X ⟶ Sp K) (φ : K →+* Ω) (h : ξ ≫ g = spMap φ) (p : Cpt ξ) (k : K) :
    genMap ξ p (cst g p.1 k) = φ k := by
  have h1 : genMap ξ p (cst g p.1 k) = (Scheme.stalkClosedPointTo ξ).hom (cst g (centre ξ) k) :=
    congrArg (Scheme.stalkClosedPointTo ξ).hom
      (X.presheaf.germ_stalkSpecializes_apply (show p.1 ∈ (⊤ : X.Opens) from trivial) p.2 _)
  rw [h1, val_cst ξ g φ h]

theorem exists_lift {ξ : Sp Ω ⟶ X} {F : Type} [Field F] [NumberField F] (hξ : IsCptGen ξ) (hN : NormalCpt ξ)
    (p : Cpt ξ) (inc : F →+* Ω) (hq : ∀ n : ℕ, 0 < n → IsUnit (n : X.presheaf.stalk p.1)) :
    ∃ κ : F →+* X.presheaf.stalk p.1, (genMap ξ p).comp κ = inc := by
  haveI : CharZero Ω := charZero_of_injective_ringHom inc.injective
  have hinv : ∀ n : ℕ, 0 < n → ((n : Ω))⁻¹ ∈ regAt ξ p := by
    intro n hn
    obtain ⟨u, hu⟩ := hq n hn
    refine ⟨(u⁻¹ : _ˣ), ?_⟩
    have h1 : genMap ξ p u = (n : Ω) := by rw [hu, map_natCast]
    have h2 : genMap ξ p (u⁻¹ : _ˣ) * genMap ξ p u = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    rw [h1] at h2
    exact eq_inv_of_mul_eq_one_left h2
  have hmem : ∀ r : ℚ, Rat.castHom Ω r ∈ regAt ξ p := by
    intro r
    rw [eq_ratCast, Rat.cast_def, div_eq_mul_inv]
    exact mul_mem (intCast_mem _ _) (hinv r.den r.den_pos)
  let ψ : ℚ →+* regAt ξ p := (Rat.castHom Ω).codRestrict _ hmem
  have hint : ∀ a : F, inc a ∈ regAt ξ p := by
    intro a
    refine hN p _ ⟨(minpoly ℚ a).map ψ, (minpoly.monic (Algebra.IsIntegral.isIntegral a)).map ψ, ?_⟩
    rw [Polynomial.eval₂_map]
    have e : (algebraMap (regAt ξ p) Ω).comp ψ = inc.comp (algebraMap ℚ F) := Subsingleton.elim _ _
    rw [e, ← Polynomial.hom_eval₂]
    have := minpoly.aeval ℚ a
    rw [Polynomial.aeval_def] at this
    rw [this, map_zero]
  have hb : Function.Bijective (genMap ξ p).rangeRestrict :=
    ⟨fun a b hab => hξ.inj p (congrArg Subtype.val hab), (genMap ξ p).rangeRestrict_surjective⟩
  refine ⟨(RingEquiv.ofBijective _ hb).symm.toRingHom.comp (inc.codRestrict (genMap ξ p).range hint), ?_⟩
  ext a
  exact congrArg Subtype.val ((RingEquiv.ofBijective _ hb).apply_symm_apply (inc.codRestrict (genMap ξ p).range hint a))

end General

theorem exists_coef : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (Z : CptOver Y U) (T : Type) [CommRing T] [IsLocalRing T] (y : Sp T ⟶ Xo.XF c) (c₀ : c.F →+* T), y ≫ pullback.snd _ _ = spMap c₀ → centre y ∈ U → ∃ (h : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j)) (κ : c.F →+* Y.X.presheaf.stalk (centre (y ≫ Y.j))), (genMap (Z.ξ₀ ≫ Y.j) ⟨_, h⟩).comp κ = Z.inc ∧ (Scheme.stalkClosedPointTo (y ≫ Y.j)).hom.comp κ = c₀ := by
  intro E _ _ _ H D l Xo c U O _ β Y Z T _ _ y c₀ hy hU
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : NumberField c.F := { to_charZero := inferInstance, to_finiteDimensional := c.fin }
  have h0 : genPt Z.ξ₀ ⤳ centre y := (Z.closure _).1 hU
  have h : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j) := h0.map Y.j.continuous
  refine ⟨h, ?_⟩
  have hN : NormalCpt (Z.ξ₀ ≫ Y.j) := XR.normalCpt_of_isCptGen Z.gen Y.normal
  have hq : ∀ n : ℕ, 0 < n → IsUnit (n : Y.X.presheaf.stalk (centre (y ≫ Y.j))) := by
    intro n hn
    haveI : IsLocalHom (Scheme.stalkClosedPointTo (y ≫ Y.j)).hom := Scheme.isLocalHom_stalkClosedPointTo _
    have e : (Scheme.stalkClosedPointTo (y ≫ Y.j)).hom (n : Y.X.presheaf.stalk (centre (y ≫ Y.j))) =
        c₀ (n : c.F) := (map_natCast _ n).trans (map_natCast c₀ n).symm
    exact isUnit_of_map_unit (Scheme.stalkClosedPointTo (y ≫ Y.j)).hom _
      ((congrArg IsUnit e).mpr ((IsUnit.mk0 _ (Nat.cast_ne_zero.2 hn.ne')).map c₀))
  obtain ⟨κ, hκ⟩ := exists_lift Z.gen hN ⟨centre (y ≫ Y.j), h⟩ Z.inc hq
  refine ⟨κ, hκ, ?_⟩
  let π := genMap Z.ξ₀ ⟨centre y, h0⟩
  let s : c.F →+* (Xo.XF c).presheaf.stalk (centre y) := (Y.j.stalkMap (centre y)).hom.comp κ
  let t : c.F →+* (Xo.XF c).presheaf.stalk (centre y) := cst (pullback.snd _ _) (centre y)
  have hD : GlobalTheory.CompanionTheory.Ar.Dominates Z.ξ₀ (Z.ξ₀ ≫ Y.j) Y.j (RingHom.id Z.Ω) := by
    show Z.ξ₀ ≫ Y.j = Spec.map (CommRingCat.ofHom (RingHom.id Z.Ω)) ≫ Z.ξ₀ ≫ Y.j
    have e : CommRingCat.ofHom (RingHom.id Z.Ω) = 𝟙 _ := rfl
    rw [e, Spec.map_id, Category.id_comp]
  have hs : π.comp s = Z.inc := by
    ext a
    exact (PullReg.stalkMap_comp_genMap hD ⟨centre y, h0⟩ h (κ a)).trans (congrArg (fun f => f a) hκ)
  have ht : π.comp t = Z.inc := by
    ext a
    exact genMap_cst Z.ξ₀ (pullback.snd _ _) Z.inc Z.over_inc ⟨centre y, h0⟩ a
  have est : s = t := GlobalTheory.T.number_field_maps_local_ring_unique c.F _ Z.Ω π s t (hs.trans ht.symm)
  have e1 : (Scheme.stalkClosedPointTo (y ≫ Y.j)).hom.comp κ = (Scheme.stalkClosedPointTo y).hom.comp s := by
    rw [Scheme.stalkClosedPointTo_comp]
    rfl
  rw [e1, est]
  ext a
  exact val_cst y (pullback.snd _ _) c₀ hy a

end GlobalTheory.CompanionTheory.Ar.LocFn.Coef
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalPointSpecializesComponentStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.LocFn

theorem _root_.GlobalTheory.T.local_point_specializes_component : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (Z : CptOver Y U) (T : Type) [CommRing T] [IsLocalRing T] (y : Sp T ⟶ Xo.XF c) (c₀ : c.F →+* T), y ≫ pullback.snd _ _ = spMap c₀ → centre y ∈ U → ∃ (h : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j)) (κ : c.F →+* Y.X.presheaf.stalk (centre (y ≫ Y.j))), (genMap (Z.ξ₀ ≫ Y.j) ⟨_, h⟩).comp κ = Z.inc ∧ (Scheme.stalkClosedPointTo (y ≫ Y.j)).hom.comp κ = c₀ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LocFn.Coef.exists_coef | exact GlobalTheory.CompanionTheory.Ar.LocFn.Coef.exists_coef | (intros; apply GlobalTheory.CompanionTheory.Ar.LocFn.Coef.exists_coef <;> assumption)
end
end
