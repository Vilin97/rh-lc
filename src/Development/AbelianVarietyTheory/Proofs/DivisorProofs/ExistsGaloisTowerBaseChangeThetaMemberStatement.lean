module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleIsoPullbackCommSquareStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisationBaseChangeFiniteInjectiveStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisTowerThetaMemberTermsBaseChangeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackPasteFactorisationStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaRingRegularAtExtensionPointStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeeperThetaValueImageEqImageValue
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
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeeperThetaValueGaloisConjugateExtension

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValExtensionPointEqImageOfVal

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.GSep
open GlobalTheory.Points


open GlobalTheory.ZH.RatModel in
theorem Tower.valF_app_p {I : Type} {X₁ : GSet} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} (𝔗 : Tower X₁ act)
    {U : X₁.M.Z.Opens} (hU : (U : Set X₁.M.Z).Nonempty) (a : Γ(X₁.M.Z, U)) :
    valF 𝔗.X₂.M.pt (𝔗.p ⁻¹ᵁ U) (𝔗.p.app U a) = algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁ (valF X₁.M.pt U a) := by
  refine (valR_comp 𝔗.X₂.M.pt 𝔗.p U a).symm.trans ?_
  rw [𝔗.p_pt]
  exact valR_spMap_comp _ X₁.M.pt U (X₁.M.top_le_preimage_pt hU) a

theorem Tower.stalkHom_stalkMap_p {I : Type} {X₁ : GSet} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} (𝔗 : Tower X₁ act)
    (z₂ : 𝔗.X₂.M.Z) (x : X₁.M.Z.presheaf.stalk (𝔗.p z₂)) :
    𝔗.X₂.M.stalkHom z₂ (𝔗.p.stalkMap z₂ x) = algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁ (X₁.M.stalkHom (𝔗.p z₂) x) := by
  obtain ⟨U, hz, f, rfl⟩ := X₁.M.Z.presheaf.germ_exist x
  rw [Scheme.Hom.germ_stalkMap_apply, RatModel.stalkHom_germ hz f]
  exact (RatModel.stalkHom_germ (M := 𝔗.X₂.M) (U := 𝔗.p ⁻¹ᵁ U) hz _).trans (𝔗.valF_app_p ⟨_, hz⟩ f)

theorem Tower.val_comp_p {I : Type} {X₁ : GSet} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} (𝔗 : Tower X₁ act)
    {K : Type} [Field K] (y : Sp K ⟶ 𝔗.X₂.M.Z) (w : Sp K) {x : X₁.Ω₁} (hx : x ∈ X₁.M.O (𝔗.p (y w))) :
    X₁.M.val (y ≫ 𝔗.p) x = 𝔗.X₂.M.val y (algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁ x) := by
  obtain ⟨U, a, hz, rfl⟩ := hx
  have h1 : Set.range y ⊆ (𝔗.p ⁻¹ᵁ U : 𝔗.X₂.M.Z.Opens) := by
    rw [RatModel.range_eq_singleton y w, Set.singleton_subset_iff]
    exact hz
  rw [← 𝔗.valF_app_p ⟨_, hz⟩ a, RatModel.val_valF h1,
    RatModel.val_valF (U := U) (by rintro _ ⟨w', rfl⟩; exact h1 ⟨w', rfl⟩)]
  exact valR_comp y 𝔗.p U a

theorem Tower.val_om_ext : ∀ {I : Type} {X₁ : GlobalTheory.GSep.GSet} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} (𝔗 : GlobalTheory.GSep.Tower X₁ act) {z₁ : X₁.M.Z} {z₂ : 𝔗.X₂.M.Z}, 𝔗.p z₂ = z₁ → ∀ {V V' : Type} [CommRing V] [IsDomain V] [CommRing V'] [IsDomain V'] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (io : V →+* V') (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V') (f : FractionRing V →+* FractionRing V'), (∀ v, f (algebraMap V (FractionRing V) v) = algebraMap V' (FractionRing V') (io v)) → Function.Injective io → 𝔗.Ext ev io ev₂ → GlobalTheory.GSep.RegAt X₁ z₁ ev → ∀ a : X₁.S.R, 𝔗.X₂.M.val (jK V' ≫ spMap ev₂ ≫ 𝔗.X₂.M.Z.fromSpecStalk z₂) (𝔗.om a) = f (X₁.M.val (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) a) := by
  intro I X₁ act 𝔗 z₁ z₂ hz V V' _ _ _ _ ev io ev₂ f hf hio hext hreg a
  subst hz
  have e1 : ev₂.comp (𝔗.p.stalkMap z₂).hom = io.comp ev :=
    RingHom.ext fun x => hext.2 x _ (𝔗.stalkHom_stalkMap_p z₂ x)
  have e2 : jK V' ≫ spMap io = spMap f ≫ jK V := by
    simp only [jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext v
    exact (hf v).symm
  have h1 : (jK V' ≫ spMap ev₂ ≫ 𝔗.X₂.M.Z.fromSpecStalk z₂) ≫ 𝔗.p =
      spMap f ≫ (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk (𝔗.p z₂)) := by
    have e3 : spMap ev₂ ≫ Spec.map (𝔗.p.stalkMap z₂) = spMap io ≫ spMap ev := by
      show Spec.map (CommRingCat.ofHom ev₂) ≫ Spec.map (CommRingCat.ofHom (𝔗.p.stalkMap z₂).hom) = _
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, e1, CommRingCat.ofHom_comp, Spec.map_comp]
    rw [Category.assoc, Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk, ← Category.assoc (spMap ev₂), e3,
      Category.assoc, ← Category.assoc (jK V'), e2]
    simp only [Category.assoc]
  have hmem := hreg a a.2
  have hp : 𝔗.p ((jK V' ≫ spMap ev₂ ≫ 𝔗.X₂.M.Z.fromSpecStalk z₂) (closedPoint (FractionRing V'))) =
      (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk (𝔗.p z₂)) (closedPoint (FractionRing V)) := by
    have e := congrArg (fun q : Sp (FractionRing V') ⟶ X₁.M.Z => q (closedPoint (FractionRing V'))) h1
    refine e.trans ?_
    show (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk (𝔗.p z₂)) ((spMap f) (closedPoint (FractionRing V'))) = _
    rw [Subsingleton.elim ((spMap f) (closedPoint (FractionRing V'))) (closedPoint (FractionRing V))]
  rw [𝔗.om_eq, ← 𝔗.val_comp_p (K := FractionRing V') _ (closedPoint (FractionRing V')) (hp ▸ hmem), h1,
    RatModel.val_spMap_comp_field (K := FractionRing V) f _ (closedPoint (FractionRing V)) hmem]

end GlobalTheory.GSep
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValExtensionPointEqImageOfValStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.val_extensionPoint_eq_image_of_val : ∀ {I : Type} {X₁ : GlobalTheory.GSep.GSet} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} (𝔗 : GlobalTheory.GSep.Tower X₁ act) {z₁ : X₁.M.Z} {z₂ : 𝔗.X₂.M.Z}, 𝔗.p z₂ = z₁ → ∀ {V V' : Type} [CommRing V] [IsDomain V] [CommRing V'] [IsDomain V'] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (io : V →+* V') (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V') (f : FractionRing V →+* FractionRing V'), (∀ v, f (algebraMap V (FractionRing V) v) = algebraMap V' (FractionRing V') (io v)) → Function.Injective io → 𝔗.Ext ev io ev₂ → GlobalTheory.GSep.RegAt X₁ z₁ ev → ∀ a : X₁.S.R, 𝔗.X₂.M.val (jK V' ≫ spMap ev₂ ≫ 𝔗.X₂.M.Z.fromSpecStalk z₂) (𝔗.om a) = f (X₁.M.val (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) a) := by
  first | exact @GlobalTheory.GSep.Tower.val_om_ext | exact GlobalTheory.GSep.Tower.val_om_ext | (intros; apply GlobalTheory.GSep.Tower.val_om_ext <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValGaloisConjugateExtensionEq

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.GSep
open GlobalTheory.Points GlobalTheory.ZH GlobalTheory.Poinc.Sep.GalVal

theorem val_galois_conj : ∀ {I : Type} {X₁ : GlobalTheory.GSep.GSet} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} (𝔗 : GlobalTheory.GSep.Tower X₁ act) {z₂ : 𝔗.X₂.M.Z} {V' : Type} [CommRing V'] [IsDomain V'] (ev₂ ev₂' : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V') (σ : 𝔗.X₂.Ω₁ ≃ₐ[X₁.Ω₁] 𝔗.X₂.Ω₁), (∀ x x', 𝔗.X₂.M.stalkHom z₂ x' = σ (𝔗.X₂.M.stalkHom z₂ x) → ev₂' x = ev₂ x') → (∀ x, ∃ x', 𝔗.X₂.M.stalkHom z₂ x' = σ (𝔗.X₂.M.stalkHom z₂ x)) → GlobalTheory.GSep.RegAt 𝔗.X₂ z₂ ev₂ → GlobalTheory.GSep.RegAt 𝔗.X₂ z₂ ev₂' → ∀ a : 𝔗.X₂.S.R, 𝔗.X₂.M.val (jK V' ≫ spMap ev₂' ≫ 𝔗.X₂.M.Z.fromSpecStalk z₂) a = 𝔗.X₂.M.val (jK V' ≫ spMap ev₂ ≫ 𝔗.X₂.M.Z.fromSpecStalk z₂) (𝔗.sR σ a) := by

  intro I X₁ act 𝔗 z₂ V' _ _ ev₂ ev₂' σ h1 h2 hr hr' a
  have ha := hr' a a.2
  obtain ⟨x, d, hxd, hd, hu⟩ := exists_mul_eq_stalkHom (specializes_jK ev₂' _) ha
  obtain ⟨x', hx'⟩ := h2 x
  obtain ⟨d', hd'⟩ := h2 d
  have ex := h1 x x' hx'
  have ed := h1 d d' hd'
  have hsp' := RatModel.specializes_of_range_eq
    (RatModel.range_eq_singleton (jK V' ≫ spMap ev₂' ≫ 𝔗.X₂.M.Z.fromSpecStalk z₂) (IsLocalRing.closedPoint _))
  have hsp := RatModel.specializes_of_range_eq
    (RatModel.range_eq_singleton (jK V' ≫ spMap ev₂ ≫ 𝔗.X₂.M.Z.fromSpecStalk z₂) (IsLocalRing.closedPoint _))
  have e1 := RatModel.val_mul hsp' ha hd
  rw [hxd, val_stalkHom, val_stalkHom] at e1
  have hne := (RatModel.val_ne_zero_iff (RatModel.range_eq_singleton _ _) ⟨_, hd⟩).2 hu
  rw [val_stalkHom] at hne
  have hb := hr _ (𝔗.sR σ a).2
  have hd'' := RatModel.O_le_of_specializes (specializes_jK ev₂ (IsLocalRing.closedPoint _))
    (𝔗.X₂.M.stalkEquiv z₂ d').2
  have e2 := RatModel.val_mul hsp hb hd''
  have key : σ (a : 𝔗.X₂.Ω₁) * 𝔗.X₂.M.stalkHom z₂ d' = 𝔗.X₂.M.stalkHom z₂ x' := by
    rw [hd', hx', ← map_mul, hxd]
  rw [RatModel.coe_stalkEquiv, 𝔗.sR_eq, key, val_stalkHom, val_stalkHom, ← ed, ← ex] at e2
  rw [𝔗.sR_eq]
  exact mul_right_cancel₀ hne (e1.symm.trans e2)

end GlobalTheory.GSep
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValGaloisConjugateExtensionEqStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.val_galoisConjugate_extension_eq : ∀ {I : Type} {X₁ : GlobalTheory.GSep.GSet} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} (𝔗 : GlobalTheory.GSep.Tower X₁ act) {z₂ : 𝔗.X₂.M.Z} {V' : Type} [CommRing V'] [IsDomain V'] (ev₂ ev₂' : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V') (σ : 𝔗.X₂.Ω₁ ≃ₐ[X₁.Ω₁] 𝔗.X₂.Ω₁), (∀ x x', 𝔗.X₂.M.stalkHom z₂ x' = σ (𝔗.X₂.M.stalkHom z₂ x) → ev₂' x = ev₂ x') → (∀ x, ∃ x', 𝔗.X₂.M.stalkHom z₂ x' = σ (𝔗.X₂.M.stalkHom z₂ x)) → GlobalTheory.GSep.RegAt 𝔗.X₂ z₂ ev₂ → GlobalTheory.GSep.RegAt 𝔗.X₂ z₂ ev₂' → ∀ a : 𝔗.X₂.S.R, 𝔗.X₂.M.val (jK V' ≫ spMap ev₂' ≫ 𝔗.X₂.M.Z.fromSpecStalk z₂) a = 𝔗.X₂.M.val (jK V' ≫ spMap ev₂ ≫ 𝔗.X₂.M.Z.fromSpecStalk z₂) (𝔗.sR σ a) := by
  exact @GlobalTheory.GSep.val_galois_conj
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisTowerBaseChangeThetaMember

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.GSep

theorem exists_ringHom_val_of_regAt' : ∀ (X₂ : GSet) (z : X₂.M.Z) {V : Type} [CommRing V] [IsDomain V] (ev : X₂.M.Z.presheaf.stalk z →+* V), RegAt X₂ z ev → ∃ yK : X₂.S.R →+* FractionRing V, ∀ a : X₂.S.R, yK a = X₂.M.val (jK V ≫ spMap ev ≫ X₂.M.Z.fromSpecStalk z) a := by
  intro X₂ z V _ _ ev hr
  have hR : X₂.S.R ≤ X₂.M.O ((jK V ≫ spMap ev ≫ X₂.M.Z.fromSpecStalk z) (IsLocalRing.closedPoint (FractionRing V))) :=
    fun a ha => hr a ha
  exact ⟨(RatModel.valHomOf (jK V ≫ spMap ev ≫ X₂.M.Z.fromSpecStalk z) _
    (RatModel.specializes_of_range_eq (RatModel.range_eq_singleton (M := X₂.M) (jK V ≫ spMap ev ≫ X₂.M.Z.fromSpecStalk z) (IsLocalRing.closedPoint (FractionRing V))))).comp
      (Subalgebra.inclusion hR).toRingHom, fun a => rfl⟩

theorem Tower.comp_act₂_of_comp_act' : ∀ {I : Type} {X₁ : GSet} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} (𝔗 : Tower X₁ act) {K : Type} [Field K] (A' : Over (Sp K)) (y₂ : 𝔗.X₂.S.R →+* K) (φ₂ : A'.left ⟶ 𝔗.X₂.ρ.P.A.left), φ₂ ≫ 𝔗.X₂.ρ.P.A.hom = A'.hom ≫ spMap y₂ → ∀ (e : A' ⟶ A') (a : I), e.left ≫ φ₂ ≫ 𝔗.φ = φ₂ ≫ 𝔗.φ ≫ (act a).left → e.left ≫ φ₂ = φ₂ ≫ (𝔗.act₂ a).left := by
  intro I X₁ act 𝔗 K _ A' y₂ φ₂ hφ e a h
  refine 𝔗.cart.1.hom_ext ?_ ?_
  · simp only [Category.assoc, 𝔗.act_eq a]
    simpa only [Category.assoc] using h
  · simp only [Category.assoc, Over.w (𝔗.act₂ a), hφ]
    rw [← Category.assoc, Over.w e]

theorem Tower.pt_iff_pt_gl' : ∀ {I : Type} {X₁ : GSet} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} (𝔗 : Tower X₁ act) {K : Type} [Field K] (A' : Over (Sp K)) [GrpObj A'] (ya yb : 𝔗.X₂.S.R →+* K) (φa φb : A'.left ⟶ 𝔗.X₂.ρ.P.A.left) (σ : 𝔗.X₂.Ω₁ ≃ₐ[X₁.Ω₁] 𝔗.X₂.Ω₁), IsGrpPullback A' 𝔗.X₂.ρ.P.A (spMap ya) φa → IsGrpPullback A' 𝔗.X₂.ρ.P.A (spMap yb) φb → φa ≫ 𝔗.φ = φb ≫ 𝔗.φ → ya = yb.comp (𝔗.sR σ) → ∀ {L : Type} [Field L] (j : K →+* L) (x : Sp L ⟶ A'.left), x ≫ A'.hom = spMap j → ∀ a, (x ≫ φa = spMap (j.comp ya) ≫ (𝔗.X₂.ρ.pt a).left ↔ x ≫ φb = spMap (j.comp yb) ≫ (𝔗.X₂.ρ.pt (𝔗.gl σ a)).left) := by
  intro I X₁ act 𝔗 K _ A' _ ya yb φa φb σ ha hb hab hy L _ j x hx a
  have hc := 𝔗.cart.1
  have hsec : ∀ b, (𝔗.X₂.ρ.pt b).left ≫ 𝔗.X₂.ρ.P.A.hom = 𝟙 _ := fun b => Over.w (𝔗.X₂.ρ.pt b)
  have hsp : ∀ y : 𝔗.X₂.S.R →+* K, spMap j ≫ spMap y = spMap (j.comp y) := fun y => by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hxa : (x ≫ φa) ≫ 𝔗.X₂.ρ.P.A.hom = spMap (j.comp ya) := by
    rw [Category.assoc, ha.1.w, ← Category.assoc, hx, hsp]
  have hxb : (x ≫ φb) ≫ 𝔗.X₂.ρ.P.A.hom = spMap (j.comp yb) := by
    rw [Category.assoc, hb.1.w, ← Category.assoc, hx, hsp]
  have hra : (spMap (j.comp ya) ≫ (𝔗.X₂.ρ.pt a).left) ≫ 𝔗.X₂.ρ.P.A.hom = spMap (j.comp ya) := by
    rw [Category.assoc, hsec]
    exact Category.comp_id _
  have hrb : (spMap (j.comp yb) ≫ (𝔗.X₂.ρ.pt (𝔗.gl σ a)).left) ≫ 𝔗.X₂.ρ.P.A.hom = spMap (j.comp yb) := by
    rw [Category.assoc, hsec]
    exact Category.comp_id _
  have hg : spMap (j.comp yb) ≫ (𝔗.X₂.ρ.pt (𝔗.gl σ a)).left ≫ 𝔗.φ = spMap (j.comp ya) ≫ (𝔗.X₂.ρ.pt a).left ≫ 𝔗.φ := by
    rw [𝔗.gl_pt, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, RingHom.comp_assoc, ← hy]
  constructor
  · intro h1
    refine hc.hom_ext ?_ (hxb.trans hrb.symm)
    rw [Category.assoc, ← hab, ← Category.assoc, h1, Category.assoc, Category.assoc, hg]
  · intro h1
    refine hc.hom_ext ?_ (hxa.trans hra.symm)
    rw [Category.assoc, hab, ← Category.assoc, h1, Category.assoc, Category.assoc, hg]

theorem exists_baseChange_gMem_of_tower : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), GlobalTheory.GSep.IsAct X₁ act → ∀ (𝔗 : GlobalTheory.GSep.Tower X₁ act) (z₂ : 𝔗.X₂.M.Z), 𝔗.p z₂ = z₁ → ∀ x₀ : X₁.S.Gam, X₁.M.Div X₁.S.th x₀ z₁ → ∃ eps : X₁.S.Gam → ℕ, ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (C : Type) (lab : C → X₁.S.Gam) (T : X → C → V), 𝔪.Terms x₀ lab T → ∀ (V' : Type) [CommRing V'] [IsDomain V'] [IsLocalRing V'] (io : V →+* V'), IsCN V' → Function.Injective io → io.Finite → ∃ 𝔪₂ : ∀ ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V', 𝔗.Ext ev io ev₂ → GlobalTheory.GSep.GMem 𝔗.X₂ z₂ 𝔗.act₂ V' ev₂ X (fun k => io (t k)) δ, (∀ ev₂ h (zt : 𝔗.X₂.M.Z.presheaf.stalk z₂), 𝔗.X₂.M.stalkHom z₂ zt = algebraMap 𝔗.X₂.o₁ 𝔗.X₂.Ω₁ 𝔗.X₂.S.ζ → (𝔪₂ ev₂ h).Terms (𝔗.lam x₀) (fun c => 𝔗.lam (lab c)) (fun mu c => ev₂ zt ^ eps (lab c) * io (T mu c))) ∧ ∀ ev₂ h ev₂' h' (σ : 𝔗.X₂.Ω₁ ≃ₐ[X₁.Ω₁] 𝔗.X₂.Ω₁), (∀ x x', 𝔗.X₂.M.stalkHom z₂ x' = σ (𝔗.X₂.M.stalkHom z₂ x) → ev₂' x = ev₂ x') → (∀ x, ∃ x', 𝔗.X₂.M.stalkHom z₂ x' = σ (𝔗.X₂.M.stalkHom z₂ x)) → ∀ a mu, (𝔪₂ ev₂' h').YY a mu ↔ (𝔪₂ ev₂ h).YY (𝔗.gl σ a) mu := by
  intro I X₁ z₁ act hact 𝔗 z₂ hz₂ x₀ hdiv
  obtain ⟨eps, heps⟩ := GlobalTheory.T.galoisTower_thetaMember_terms_baseChange X₁ act 𝔗 z₁ z₂ hz₂ x₀ hdiv
  refine ⟨eps, ?_⟩
  intro V _ _ _ ev X _ t δ 𝔪 C lab T hT V' _ _ _ io hcn hinj hfin
  have hle : nonZeroDivisors V ≤ (nonZeroDivisors V').comap io :=
    nonZeroDivisors_le_comap_nonZeroDivisors_of_injective io hinj
  let f : FractionRing V →+* FractionRing V' := IsLocalization.map (FractionRing V') io hle
  have hf : ∀ v, f (algebraMap V (FractionRing V) v) = algebraMap V' (FractionRing V') (io v) :=
    fun v => IsLocalization.map_eq hle v
  obtain ⟨D', e₈', G', _, _, A', U', ψ, hD, bc, hsemi, hψ, hw, hbc, hPU, hxe, hgen, hE, hpsi⟩ :=
    GlobalTheory.T.exists_uniformisation_baseChange_finite_injective X₁ z₁ act V ev X t δ 𝔪 V' io f hf hcn hinj hfin
  have hreg : ∀ ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V', 𝔗.Ext ev io ev₂ → RegAt 𝔗.X₂ z₂ ev₂ :=
    fun ev₂ h => GlobalTheory.T.thetaRing_regular_at_extension_point 𝔗 hz₂ ev io ev₂ hinj h 𝔪.reg
  choose yK hyK using fun (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V') (h : 𝔗.Ext ev io ev₂) =>
    exists_ringHom_val_of_regAt' 𝔗.X₂ z₂ ev₂ (hreg ev₂ h)
  have hyKc : ∀ ev₂ h, (yK ev₂ h).comp 𝔗.om = f.comp 𝔪.yK := by
    intro ev₂ h
    ext a
    simp only [RingHom.comp_apply]
    rw [hyK, 𝔪.yK_eq]
    exact GlobalTheory.T.val_extensionPoint_eq_image_of_val 𝔗 hz₂ ev io ev₂ f hf hinj h 𝔪.reg a
  have hsq : ∀ ev₂ h, spMap (yK ev₂ h) ≫ spMap 𝔗.om = spMap f ≫ spMap 𝔪.yK := by
    intro ev₂ h
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hyKc ev₂ h]
  choose φ₂ hφ₂ using fun (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V') (h : 𝔗.Ext ev io ev₂) =>
    GlobalTheory.T.isGrpPullback_paste_factorisation X₁.ρ.P.A 𝔗.X₂.ρ.P.A 𝔪.A.A A'.A (spMap 𝔗.om) (spMap 𝔪.yK) (spMap f) (spMap (yK ev₂ h)) 𝔗.φ 𝔪.φ ψ
      𝔗.cart 𝔪.cart hψ (hsq ev₂ h)
  choose wl hwl using fun (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V') (h : 𝔗.Ext ev io ev₂) =>
    GlobalTheory.T.exists_lineBundleIso_pullback_commSquare A'.L 𝔪.A.L X₁.ρ.P.L 𝔗.X₂.ρ.P.L ψ 𝔪.φ (φ₂ ev₂ h) 𝔗.φ A'.isLB 𝔪.A.isLB X₁.ρ.P.isLB 𝔗.X₂.ρ.P.isLB
      (hφ₂ ev₂ h).2.symm hw ⟨𝔪.wl, 𝔪.wl_gen⟩ 𝔗.lb
  let 𝔪₂ : ∀ ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V', 𝔗.Ext ev io ev₂ →
      GMem 𝔗.X₂ z₂ 𝔗.act₂ V' ev₂ X (fun k => io (t k)) δ := fun ev₂ h =>
    { cn := hcn
      loc := h.1
      reg := hreg ev₂ h
      yK := yK ev₂ h
      yK_eq := hyK ev₂ h
      D := D'
      e₈ := e₈'
      G := G'
      semi := hsemi
      A := A'
      U := U'
      φ := φ₂ ev₂ h
      cart := (hφ₂ ev₂ h).1
      wl := wl ev₂ h
      wl_gen := hwl ev₂ h
      equiv := fun a => by
        obtain ⟨E, hE1, hE2⟩ := 𝔪.equiv a
        obtain ⟨E', hE'1, hE'2⟩ := hE E
        refine ⟨E', ?_, fun mu => hD.xe.injective ?_⟩
        · have e2 := (hφ₂ ev₂ h).2
          refine Tower.comp_act₂_of_comp_act' 𝔗 A'.A (yK ev₂ h) (φ₂ ev₂ h) (hφ₂ ev₂ h).1.1.w E'.aA a ?_
          calc E'.aA.left ≫ φ₂ ev₂ h ≫ 𝔗.φ = E'.aA.left ≫ ψ ≫ 𝔪.φ := by rw [e2]
            _ = ψ ≫ E.aA.left ≫ 𝔪.φ := by rw [← Category.assoc, hE'1, Category.assoc]
            _ = ψ ≫ 𝔪.φ ≫ (act a).left := by rw [hE1]
            _ = φ₂ ev₂ h ≫ 𝔗.φ ≫ (act a).left := by rw [← Category.assoc, ← e2, Category.assoc]
        · rw [hE'2, hxe, hE2, hxe]
      psi := hpsi }
  refine ⟨𝔪₂, ?_, ?_⟩
  · intro ev₂ h zt hzt
    exact heps V ev X t δ 𝔪 C lab T hT V' io f hf hinj hfin ev₂ (𝔪₂ ev₂ h) ψ hD bc h (hyKc ev₂ h) hψ hw
      (hφ₂ ev₂ h).2 hbc hPU hxe hgen zt hzt
  · intro ev₂ h ev₂' h' σ h1 h2 a mu
    have hy : yK ev₂' h' = (yK ev₂ h).comp (𝔗.sR σ) := by
      ext b
      simp only [RingHom.comp_apply]
      rw [hyK, hyK]
      exact GlobalTheory.T.val_galoisConjugate_extension_eq 𝔗 ev₂ ev₂' σ h1 h2 (hreg ev₂ h) (hreg ev₂' h') b
    unfold GMem.YY
    refine exists_congr fun p => exists_congr fun x => and_congr_right fun _ => and_congr_right fun _ => ?_
    exact Tower.pt_iff_pt_gl' 𝔗 A'.A (yK ev₂' h') (yK ev₂ h) (φ₂ ev₂' h') (φ₂ ev₂ h) σ (hφ₂ ev₂' h').1 (hφ₂ ev₂ h).1
      ((hφ₂ ev₂' h').2.trans (hφ₂ ev₂ h).2.symm) hy
      (algebraMap (FractionRing V') (AlgebraicClosure (FractionRing V'))) x.left (Over.w x) a

end GlobalTheory.GSep
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisTowerBaseChangeThetaMemberStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.exists_galoisTower_baseChange_thetaMember : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), GlobalTheory.GSep.IsAct X₁ act → ∀ (𝔗 : GlobalTheory.GSep.Tower X₁ act) (z₂ : 𝔗.X₂.M.Z), 𝔗.p z₂ = z₁ → ∀ x₀ : X₁.S.Gam, X₁.M.Div X₁.S.th x₀ z₁ → ∃ eps : X₁.S.Gam → ℕ, ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (C : Type) (lab : C → X₁.S.Gam) (T : X → C → V), 𝔪.Terms x₀ lab T → ∀ (V' : Type) [CommRing V'] [IsDomain V'] [IsLocalRing V'] (io : V →+* V'), IsCN V' → Function.Injective io → io.Finite → ∃ 𝔪₂ : ∀ ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V', 𝔗.Ext ev io ev₂ → GlobalTheory.GSep.GMem 𝔗.X₂ z₂ 𝔗.act₂ V' ev₂ X (fun k => io (t k)) δ, (∀ ev₂ h (zt : 𝔗.X₂.M.Z.presheaf.stalk z₂), 𝔗.X₂.M.stalkHom z₂ zt = algebraMap 𝔗.X₂.o₁ 𝔗.X₂.Ω₁ 𝔗.X₂.S.ζ → (𝔪₂ ev₂ h).Terms (𝔗.lam x₀) (fun c => 𝔗.lam (lab c)) (fun mu c => ev₂ zt ^ eps (lab c) * io (T mu c))) ∧ ∀ ev₂ h ev₂' h' (σ : 𝔗.X₂.Ω₁ ≃ₐ[X₁.Ω₁] 𝔗.X₂.Ω₁), (∀ x x', 𝔗.X₂.M.stalkHom z₂ x' = σ (𝔗.X₂.M.stalkHom z₂ x) → ev₂' x = ev₂ x') → (∀ x, ∃ x', 𝔗.X₂.M.stalkHom z₂ x' = σ (𝔗.X₂.M.stalkHom z₂ x)) → ∀ a mu, (𝔪₂ ev₂' h').YY a mu ↔ (𝔪₂ ev₂ h).YY (𝔗.gl σ a) mu := by
  first | exact @GlobalTheory.GSep.exists_baseChange_gMem_of_tower | exact GlobalTheory.GSep.exists_baseChange_gMem_of_tower | (intros; apply GlobalTheory.GSep.exists_baseChange_gMem_of_tower <;> assumption)
end
end
