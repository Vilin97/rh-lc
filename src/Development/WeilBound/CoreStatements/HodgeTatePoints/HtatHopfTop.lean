module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderEqOfLeStatement
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
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BaseChangePointsCompatStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsDenominatorRegular
public import Development.WeilBound.CoreStatements.HodgeTatePoints.TwhopfSec
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Development.WeilBound.CoreStatements.HodgeTatePoints.TwhopfFin
import Development.WeilBound.CoreStatements.HodgeTatePoints.TwhopfSec
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsHenselianFlatOverPrimeStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsBaseChangeGroupStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularAtBaseChangeStatement

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsFinOpenSubBaseChange

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.BT.PullSub

variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] (Γ : QFGroup R T)
  {R' : Type} [CommRing R'] [IsDomain R'] (Γ' : QFGroup R' T) (φ : R →+* R')
  (F : Γ'.G.left ⟶ Γ.G.left)

def pushPt (hw : F ≫ Γ.G.hom = Γ'.G.hom ≫ Spec.map (CommRingCat.ofHom φ))
    {S : Over (Spec (CommRingCat.of R'))} (x : S ⟶ Γ'.G) :
    Over.mk (S.hom ≫ Spec.map (CommRingCat.ofHom φ)) ⟶ Γ.G :=
  Over.homMk (x.left ≫ F) (by
    have hx : x.left ≫ Γ'.G.hom = S.hom := Over.w x
    simp only [Over.mk_hom, Category.assoc, hw]
    rw [← Category.assoc, hx])

variable {Γ Γ' φ F}

theorem pushPt_left (hw : F ≫ Γ.G.hom = Γ'.G.hom ≫ Spec.map (CommRingCat.ofHom φ))
    {S : Over (Spec (CommRingCat.of R'))} (x : S ⟶ Γ'.G) :
    (pushPt Γ Γ' φ F hw x).left = x.left ≫ F := rfl

theorem pushPt_mul (h : Γ'.IsBaseChange Γ φ F)
    {S : Over (Spec (CommRingCat.of R'))} (x y : S ⟶ Γ'.G) :
    pushPt Γ Γ' φ F h.cart.w (x * y) = pushPt Γ Γ' φ F h.cart.w x * pushPt Γ Γ' φ F h.cart.w y := by
  apply Over.OverMorphism.ext
  rw [pushPt_left]
  exact (h.mul S x y _ _ (pushPt_left h.cart.w x) (pushPt_left h.cart.w y)).symm

theorem pushPt_one (h : Γ'.IsBaseChange Γ φ F) (S : Over (Spec (CommRingCat.of R'))) :
    pushPt Γ Γ' φ F h.cart.w (1 : S ⟶ Γ'.G) = 1 := by
  have h1 := pushPt_mul h (1 : S ⟶ Γ'.G) 1
  rw [_root_.mul_one] at h1
  exact _root_.mul_left_cancel (h1.symm.trans (_root_.mul_one _).symm)

theorem pushPt_inv (h : Γ'.IsBaseChange Γ φ F)
    {S : Over (Spec (CommRingCat.of R'))} (x : S ⟶ Γ'.G) :
    pushPt Γ Γ' φ F h.cart.w x⁻¹ = (pushPt Γ Γ' φ F h.cart.w x)⁻¹ := by
  have h2 := pushPt_mul h x⁻¹ x
  rw [_root_.inv_mul_cancel, pushPt_one h S] at h2
  exact eq_inv_of_mul_eq_one_left h2.symm

end GlobalTheory.CompanionTheory.Ar.BT.PullSub

open GlobalTheory.CompanionTheory.Ar.BT.PullSub

open GlobalTheory.CompanionTheory.Ar.BT.PullSub in
theorem GlobalTheory.CompanionTheory.Ar.BT.isFinOpenSub_preimage_baseChange :
    ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left), Γ'.IsBaseChange Γ (algebraMap R R') F → ∀ U : Γ.G.left.Opens, Γ.IsFinOpenSub U → Γ'.IsFinOpenSub (F ⁻¹ᵁ U) := by
  intro R _ _ T _ _ Γ R' _ _ _ Γ' F h U hU
  have hpb := (isPullback_morphismRestrict F U).paste_vert h.cart
  refine ⟨MorphismProperty.of_isPullback (P := @IsFinite) hpb hU.finite, ?_, ?_, ?_⟩
  · intro x
    have e1 : (1 : 𝟙_ (Over (Spec (CommRingCat.of R'))) ⟶ Γ'.G) = MonObj.one := by
      change SemiCartesianMonoidalCategory.toUnit _ ≫ MonObj.one = MonObj.one
      rw [SemiCartesianMonoidalCategory.toUnit_unique (SemiCartesianMonoidalCategory.toUnit _) (𝟙 _),
        Category.id_comp]
    have e2 : (1 : 𝟙_ (Over (Spec (CommRingCat.of R'))) ⟶ Γ'.G).left ≫ F =
        (1 : Over.mk ((𝟙_ (Over (Spec (CommRingCat.of R')))).hom ≫
          Spec.map (CommRingCat.ofHom (algebraMap R R'))) ⟶ Γ.G).left := by
      rw [← pushPt_left h.cart.w, pushPt_one h]
    rw [Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply, ← e1, e2]
    change (Over.Hom.left (SemiCartesianMonoidalCategory.toUnit (Over.mk ((𝟙_ (Over (Spec (CommRingCat.of R')))).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap R R')))) ≫ (MonObj.one : 𝟙_ _ ⟶ Γ.G))) x ∈ U
    rw [Over.comp_left, Scheme.Hom.comp_apply]
    exact hU.one _
  · intro S x y hx hy z
    have hx' : ∀ w, (pushPt Γ Γ' (algebraMap R R') F h.cart.w x).left w ∈ U := fun w => by
      rw [pushPt_left, Scheme.Hom.comp_apply]
      exact (Scheme.Hom.mem_preimage F).mp (hx w)
    have hy' : ∀ w, (pushPt Γ Γ' (algebraMap R R') F h.cart.w y).left w ∈ U := fun w => by
      rw [pushPt_left, Scheme.Hom.comp_apply]
      exact (Scheme.Hom.mem_preimage F).mp (hy w)
    have hxy := hU.mul _ _ _ hx' hy' z
    rw [← pushPt_mul h, pushPt_left, Scheme.Hom.comp_apply] at hxy
    exact (Scheme.Hom.mem_preimage F).mpr hxy
  · intro S x hx z
    have hx' : ∀ w, (pushPt Γ Γ' (algebraMap R R') F h.cart.w x).left w ∈ U := fun w => by
      rw [pushPt_left, Scheme.Hom.comp_apply]
      exact (Scheme.Hom.mem_preimage F).mp (hx w)
    have hxi := hU.inv _ _ hx' z
    rw [← pushPt_inv h, pushPt_left, Scheme.Hom.comp_apply] at hxi
    exact (Scheme.Hom.mem_preimage F).mpr hxi
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsFinOpenSubBaseChangeStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

theorem _root_.GlobalTheory.T.isFinOpenSub_base_change : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left), Γ'.IsBaseChange Γ (algebraMap R R') F → ∀ U : Γ.G.left.Opens, Γ.IsFinOpenSub U → Γ'.IsFinOpenSub (F ⁻¹ᵁ U) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.isFinOpenSub_preimage_baseChange | exact GlobalTheory.CompanionTheory.Ar.BT.isFinOpenSub_preimage_baseChange | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.isFinOpenSub_preimage_baseChange <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsDenominatorRegularStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

theorem _root_.GlobalTheory.T.exists_denominator_regular : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (f : T → FractionRing R) (g : Γ.G.left), ∃ d : R, d ≠ 0 ∧ Γ.RegularAt (fun t => algebraMap R _ d * f t) g := by
  exact @GlobalTheory.CompanionTheory.Ar.BT.RegDenom.exists_denom_regularAt
end
end

-- Source module: Development.WeilBound.CoreStatements.HodgeTatePoints.HtatHopfReg

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

noncomputable section

namespace PositivityTheory.HtPt.Htat.StalkDivisibility

def constSec {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of R)) (U : X.Opens) (d : R) : Γ(X, U) :=
  (p.appLE ⊤ U (fun _ _ => trivial)).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom d)

section valAt

variable {B C R : Type} [CommRing B] [CommRing C] [CommRing R] {X Y : Scheme.{0}}

theorem valAt_congr {x y : Spec (CommRingCat.of B) ⟶ X} (e : x = y) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (h' : ⊤ ≤ y ⁻¹ᵁ U) (s : Γ(X, U)) : valAt x U h s = valAt y U h' s := by
  subst e; rfl

theorem valAt_res (x : Spec (CommRingCat.of B) ⟶ X) {U V : X.Opens} (i : V ⟶ U) (hV : ⊤ ≤ x ⁻¹ᵁ V)
    (hU : ⊤ ≤ x ⁻¹ᵁ U) (s : Γ(X, U)) :
    valAt x V hV ((X.presheaf.map i.op).hom s) = valAt x U hU s :=
  congrArg (fun φ => (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom (φ.hom s)) (x.map_appLE hV i.op)

theorem valAt_mul (x : Spec (CommRingCat.of B) ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (a b : Γ(X, U)) :
    valAt x U h (a * b) = valAt x U h a * valAt x U h b := by
  simp [valAt]

theorem valAt_sub (x : Spec (CommRingCat.of B) ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (a b : Γ(X, U)) :
    valAt x U h (a - b) = valAt x U h a - valAt x U h b := by
  simp [valAt]

theorem valAt_comp (x : Spec (CommRingCat.of B) ⟶ Y) (F : Y ⟶ X) (U : X.Opens) (h : ⊤ ≤ (x ≫ F) ⁻¹ᵁ U)
    (s : Γ(X, U)) : valAt (x ≫ F) U h s = valAt x (F ⁻¹ᵁ U) h ((F.app U).hom s) := by
  simp only [valAt, Scheme.Hom.comp_appLE]
  rfl

theorem specMap_appLE_top (φ : B →+* C) (e) (r : Γ(Spec (CommRingCat.of B), ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of C)).hom.hom (((Spec.map (CommRingCat.ofHom φ)).appLE ⊤ ⊤ e).hom r) =
      φ ((Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom r) := by
  have h : (Spec.map (CommRingCat.ofHom φ)).appLE ⊤ ⊤ e = (Spec.map (CommRingCat.ofHom φ)).appTop := by
    exact (Scheme.Hom.app_eq_appLE _).symm
  rw [h]
  exact congrArg (fun ψ => ψ.hom r) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ))

theorem valAt_spec (κ : B →+* C) (x : Spec (CommRingCat.of B) ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (h' : ⊤ ≤ (Spec.map (CommRingCat.ofHom κ) ≫ x) ⁻¹ᵁ U) (s : Γ(X, U)) :
    valAt (Spec.map (CommRingCat.ofHom κ) ≫ x) U h' s = κ (valAt x U h s) := by
  have e := Scheme.Hom.appLE_comp_appLE (Spec.map (CommRingCat.ofHom κ)) x U ⊤ ⊤ h (fun _ _ => trivial)
  simp only [valAt]
  rw [← e]
  exact specMap_appLE_top κ _ _

theorem valAt_const (p : X ⟶ Spec (CommRingCat.of R)) (x : Spec (CommRingCat.of B) ⟶ X) (φ : R →+* B)
    (hx : x ≫ p = Spec.map (CommRingCat.ofHom φ)) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (d : R) :
    valAt x U h (constSec p U d) = φ d := by
  have e := Scheme.Hom.appLE_comp_appLE x p ⊤ U ⊤ (fun _ _ => trivial) h
  have key : ∀ (y : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R)) (_ : y = Spec.map (CommRingCat.ofHom φ)) (e' : ⊤ ≤ y ⁻¹ᵁ ⊤),
      (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom ((y.appLE ⊤ ⊤ e').hom
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom d)) = φ d := by
    intro y hy e'
    subst hy
    rw [specMap_appLE_top]
    simp
  change (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom
    ((p.appLE ⊤ U (fun _ _ => trivial) ≫ x.appLE U ⊤ h).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom d)) = φ d
  rw [e]
  exact key _ hx _

theorem constSec_res (p : X ⟶ Spec (CommRingCat.of R)) {U V : X.Opens} (i : V ⟶ U) (d : R) :
    (X.presheaf.map i.op).hom (constSec p U d) = constSec p V d :=
  congrArg (fun ψ => ψ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom d))
    (p.appLE_map (U := ⊤) (V := U) (V' := V) (fun _ _ => trivial) i.op)

theorem app_constSec {R' : Type} [CommRing R'] (p : X ⟶ Spec (CommRingCat.of R)) (p' : Y ⟶ Spec (CommRingCat.of R'))
    (F : Y ⟶ X) (φ : R →+* R') (hF : F ≫ p = p' ≫ Spec.map (CommRingCat.ofHom φ)) (U : X.Opens) (d : R) :
    (F.app U).hom (constSec p U d) = constSec p' (F ⁻¹ᵁ U) (φ d) := by
  have e₁ := Scheme.Hom.appLE_comp_appLE F p ⊤ U (F ⁻¹ᵁ U) (fun _ _ => trivial) le_rfl
  have e₂ : ∀ (y : Y ⟶ Spec (CommRingCat.of R)) (_ : y = p' ≫ Spec.map (CommRingCat.ofHom φ)) (e' : F ⁻¹ᵁ U ≤ y ⁻¹ᵁ ⊤),
      (y.appLE ⊤ (F ⁻¹ᵁ U) e').hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom d) = constSec p' (F ⁻¹ᵁ U) (φ d) := by
    intro y hy e'
    subst hy
    rw [Scheme.Hom.comp_appLE]
    have n := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ)
    have n' := congrArg (fun ψ => ψ.hom d) n
    simp only [constSec]
    change (p'.appLE _ _ _).hom (((Spec.map (CommRingCat.ofHom φ)).appTop).hom _) = _
    exact congrArg (p'.appLE ⊤ (F ⁻¹ᵁ U) (fun _ _ => trivial)).hom n'.symm
  rw [← e₂ _ hF (fun _ _ => trivial), ← e₁, Scheme.Hom.app_eq_appLE]
  rfl

theorem dvd_of_stalkMap_dvd (r : Y ⟶ X) [Flat r] (z : Y) {a b : X.presheaf.stalk (r z)}
    (h : (r.stalkMap z).hom a ∣ (r.stalkMap z).hom b) : a ∣ b := by
  let _ := (r.stalkMap z).hom.toAlgebra
  have : Module.Flat (X.presheaf.stalk (r z)) (Y.presheaf.stalk z) := Flat.stalkMap r z
  have : IsLocalHom (algebraMap (X.presheaf.stalk (r z)) (Y.presheaf.stalk z)) :=
    inferInstanceAs (IsLocalHom (r.stalkMap z).hom)
  have : Module.FaithfullyFlat (X.presheaf.stalk (r z)) (Y.presheaf.stalk z) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  rw [← Ideal.mem_span_singleton, ← Ideal.comap_map_eq_self_of_faithfullyFlat (B := Y.presheaf.stalk z) (Ideal.span {a}),
    Ideal.mem_comap, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton]
  exact h

theorem top_le_of_spec_comp {K L : Type} [Field K] [Field L] (κ : K →+* L) (x : Spec (CommRingCat.of K) ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ (Spec.map (CommRingCat.ofHom κ) ≫ x) ⁻¹ᵁ U) : ⊤ ≤ x ⁻¹ᵁ U := by
  intro y _
  have : Subsingleton (Spec (CommRingCat.of K)) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  have : Nonempty (Spec (CommRingCat.of L)) := inferInstanceAs (Nonempty (PrimeSpectrum L))
  obtain ⟨w⟩ := this
  have hw := h (show w ∈ (⊤ : (Spec (CommRingCat.of L)).Opens) from trivial)
  rw [Subsingleton.elim y (Spec.map (CommRingCat.ofHom κ) w)]
  simpa using hw

end valAt

theorem regularAt_of_baseChange : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left), Γ'.IsBaseChange Γ (algebraMap R R') F → Module.Flat R R' → ∀ κ : FractionRing R →+* FractionRing R', κ.comp (algebraMap R _) = (algebraMap R' _).comp (algebraMap R R') → ∀ (f : T → FractionRing R) (g' : Γ'.G.left), Γ'.RegularAt (fun t => κ (f t)) g' → Γ.RegularAt f (F g') := by
  intro R _ _ T _ _ Γ R' _ _ _ Γ' F hbc hfl κ hκ f g' hreg
  obtain ⟨U', hgU', s', hs'⟩ := hreg
  obtain ⟨d, hd0, U, hgU, s, hs⟩ := GlobalTheory.T.exists_denominator_regular R T Γ f (F g')
  have hφ : Flat (Spec.map (CommRingCat.ofHom (algebraMap R R'))) :=
    Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr hfl)
  have hF : Flat F := MorphismProperty.of_isPullback (P := @Flat) hbc.cart.flip hφ
  have hsq : F ≫ Γ.G.hom = Γ'.G.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')) := hbc.cart.w
  let W' : Γ'.G.left.Opens := (F ⁻¹ᵁ U) ⊓ U'
  have hgW' : g' ∈ W' := ⟨hgU, hgU'⟩
  let i₁ : W' ⟶ F ⁻¹ᵁ U := homOfLE inf_le_left
  let i₂ : W' ⟶ U' := homOfLE inf_le_right
  have key : (Γ'.G.left.presheaf.map i₁.op).hom ((F.app U).hom s) =
      constSec Γ'.G.hom W' (algebraMap R R' d) * (Γ'.G.left.presheaf.map i₂.op).hom s' := by
    refine sub_eq_zero.mp (PositivityTheory.HtPt.Twhopf.sec_inj R' T Γ' W' _ fun t h => ?_)
    have h₁ : ⊤ ≤ (Γ'.pt t).left ⁻¹ᵁ (F ⁻¹ᵁ U) := fun x hx => (h hx).1
    have h₂ : ⊤ ≤ (Γ'.pt t).left ⁻¹ᵁ U' := fun x hx => (h hx).2
    have hpt := GlobalTheory.T.base_change_points_compat R T Γ R' Γ' F hbc κ hκ t
    have h₃ : ⊤ ≤ (Spec.map (CommRingCat.ofHom κ) ≫ (Γ.pt t).left) ⁻¹ᵁ U := by
      rw [← hpt]; exact h₁
    have h₄ : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U := top_le_of_spec_comp κ _ U h₃
    have hw' : (Γ'.pt t).left ≫ Γ'.G.hom =
        Spec.map (CommRingCat.ofHom (algebraMap R' (FractionRing R'))) := Over.w (Γ'.pt t)
    rw [valAt_sub, valAt_mul, valAt_res _ i₁ h h₁, valAt_res _ i₂ h h₂, hs' t h₂,
      valAt_const _ _ (algebraMap R' (FractionRing R')) hw', ← valAt_comp _ F U h₁,
      valAt_congr hpt U h₁ h₃, valAt_spec κ _ U h₄ h₃, hs t h₄, map_mul]
    have : κ (algebraMap R _ d) = algebraMap R' _ (algebraMap R R' d) := congrArg (fun ψ => ψ d) hκ
    rw [this, sub_self]
  have hdvd : Γ.G.left.presheaf.germ U (F g') hgU (constSec Γ.G.hom U d) ∣
      Γ.G.left.presheaf.germ U (F g') hgU s := by
    apply dvd_of_stalkMap_dvd F g'
    refine ⟨Γ'.G.left.presheaf.germ W' g' hgW' ((Γ'.G.left.presheaf.map i₂.op).hom s'), ?_⟩
    have e₁ := Scheme.Hom.germ_stalkMap_apply F U g' hgU s
    have e₂ := Scheme.Hom.germ_stalkMap_apply F U g' hgU (constSec Γ.G.hom U d)
    rw [app_constSec _ _ F _ hsq] at e₂
    have e₃ := Γ'.G.left.presheaf.germ_res_apply i₁ g' hgW' ((F.app U).hom s)
    have e₄ := Γ'.G.left.presheaf.germ_res_apply i₁ g' hgW' (constSec Γ'.G.hom (F ⁻¹ᵁ U) (algebraMap R R' d))
    rw [constSec_res] at e₄
    rw [key, map_mul] at e₃
    exact e₁.trans (e₃.symm.trans (by rw [e₄, ← e₂]))
  obtain ⟨x, hx⟩ := hdvd
  obtain ⟨W, hgW, s₀, rfl⟩ := Γ.G.left.presheaf.exists_germ_eq x
  let P : Γ.G.left.Opens := U ⊓ W
  have hgP : F g' ∈ P := ⟨hgU, hgW⟩
  let j₁ : P ⟶ U := homOfLE inf_le_left
  let j₂ : P ⟶ W := homOfLE inf_le_right
  have hP : Γ.G.left.presheaf.germ U (F g') hgU s = Γ.G.left.presheaf.germ P (F g') hgP
      (constSec Γ.G.hom P d * (Γ.G.left.presheaf.map j₂.op).hom s₀) := by
    rw [hx, map_mul, TopCat.Presheaf.germ_res_apply, ← constSec_res _ j₁, TopCat.Presheaf.germ_res_apply]
  obtain ⟨V, hV, iU, iP, hres⟩ := TopCat.Presheaf.germ_eq _ _ hgU hgP _ _ hP
  refine ⟨V, hV, (Γ.G.left.presheaf.map (iP ≫ j₂).op).hom s₀, fun t h => ?_⟩
  have hU : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U := fun x hx => iU.le (h hx)
  have hPt : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ P := fun x hx => iP.le (h hx)
  have hWt : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ W := fun x hx => (iP ≫ j₂).le (h hx)
  have hw : (Γ.pt t).left ≫ Γ.G.hom =
      Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) := Over.w (Γ.pt t)
  have hK : algebraMap R (FractionRing R) d ≠ 0 := by
    simpa using hd0
  refine mul_left_cancel₀ hK ?_
  have e₁ := congrArg (valAt (Γ.pt t).left V h) hres
  rw [valAt_res _ iU h hU, hs t hU, valAt_res _ iP h hPt, valAt_mul, valAt_const _ _ _ hw,
    valAt_res _ j₂ hPt hWt] at e₁
  rw [valAt_res _ (iP ≫ j₂) h hWt]
  exact e₁.symm

end PositivityTheory.HtPt.Htat.StalkDivisibility

theorem PositivityTheory.HtPt.Htat.bt_reg_descent : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left), Γ'.IsBaseChange Γ (algebraMap R R') F → Module.Flat R R' → ∀ κ : FractionRing R →+* FractionRing R', κ.comp (algebraMap R _) = (algebraMap R' _).comp (algebraMap R R') → ∀ (f : T → FractionRing R) (g' : Γ'.G.left), Γ'.RegularAt (fun t => κ (f t)) g' → Γ.RegularAt f (F g') :=
  @PositivityTheory.HtPt.Htat.StalkDivisibility.regularAt_of_baseChange
end
end
end

-- Source module: Development.WeilBound.CoreStatements.HodgeTatePoints.HtatHopfTop

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.HtPt.Htat.HopfOrderEqTop

theorem btOrder_eq_top (hHenselian : type_of% @GlobalTheory.T.exists_henselian_flat_over_prime) (hBaseChange : type_of% @GlobalTheory.T.exists_base_change_group) (hRegular : type_of% @GlobalTheory.T.regular_at_base_change) (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T]
    [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens) (hU : Γ.IsFinOpenSub U) :
    Γ.btOrder U = Γ.btOrder ⊤ := by
  ext f
  rw [PositivityTheory.HtPt.Twhopf.mem_order, PositivityTheory.HtPt.Twhopf.mem_order]
  refine ⟨fun hf t g _ => ?_, fun hf t g _ => hf t g trivial⟩
  obtain ⟨R', _, _, _, _, hN, hflat, hP⟩ :=
    @hHenselian R _ _ _ (Γ.G.hom g).asIdeal (Γ.G.hom g).isPrime
  have hinj : Function.Injective (algebraMap R R') := FaithfulSMul.algebraMap_injective R R'
  obtain ⟨Γ', F, hF⟩ := hBaseChange R T Γ R' (algebraMap R R') hinj
  have hinj' : Function.Injective ((algebraMap R' (FractionRing R')).comp (algebraMap R R')) :=
    (IsFractionRing.injective R' (FractionRing R')).comp hinj
  let κ : FractionRing R →+* FractionRing R' := IsFractionRing.lift hinj'
  have hκa : ∀ r, κ (algebraMap R _ r) = algebraMap R' _ (algebraMap R R' r) := fun r =>
    IsFractionRing.lift_algebraMap hinj' r
  have hκ : κ.comp (algebraMap R _) = (algebraMap R' _).comp (algebraMap R R') := RingHom.ext hκa
  obtain ⟨g', hg1, hg2⟩ := Scheme.exists_preimage_of_isPullback hF.cart g (IsLocalRing.closedPoint R') (by
    apply PrimeSpectrum.ext
    exact hP.symm)
  haveI := Γ'.quasiFinite
  haveI := Γ'.finPres
  haveI := Γ'.separated
  haveI := Γ'.quasiCompact
  obtain ⟨U', hU'fin, hU'cl⟩ := PositivityTheory.HtPt.Twhopf.finite_part R' Γ'.G.left Γ'.G.hom
  have hU' := PositivityTheory.HtPt.Twhopf.finite_sub R' T Γ' U' hU'fin hU'cl
  have hFU := GlobalTheory.T.isFinOpenSub_base_change R T Γ R' Γ' F hF U hU
  have hle : F ⁻¹ᵁ U ≤ U' := PositivityTheory.HtPt.Twhopf.finite_le R' _ Γ'.G.hom _ _ hFU.finite hU'cl
  have h1 : (fun h => algebraMap R R' (f h)) ∈ Γ'.btSet (F ⁻¹ᵁ U) := by
    intro s x hx
    have := hRegular R T Γ R' Γ' F hF κ hκ _ x (hf s (F x) hx)
    simpa only [hκa] using this
  rw [← PositivityTheory.HtPt.Twhopf.mem_order, ← GlobalTheory.T.btOrder_eq_of_le_of_isFinOpenSub R' T Γ' U' _ hU' hFU hle, PositivityTheory.HtPt.Twhopf.mem_order] at h1
  rw [← hg1]
  refine PositivityTheory.HtPt.Htat.bt_reg_descent R T Γ R' Γ' F hF hflat κ hκ _ g' ?_
  simpa only [hκa] using h1 t g' (hU'cl g' hg2)

end PositivityTheory.HtPt.Htat.HopfOrderEqTop

theorem PositivityTheory.HtPt.Htat.bt_sub_eq_top_of (hHenselian : type_of% @GlobalTheory.T.exists_henselian_flat_over_prime) (hBaseChange : type_of% @GlobalTheory.T.exists_base_change_group) (hRegular : type_of% @GlobalTheory.T.regular_at_base_change) : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens), Γ.IsFinOpenSub U → Γ.btOrder U = Γ.btOrder ⊤ :=
  @PositivityTheory.HtPt.Htat.HopfOrderEqTop.btOrder_eq_top hHenselian hBaseChange hRegular
end
end
