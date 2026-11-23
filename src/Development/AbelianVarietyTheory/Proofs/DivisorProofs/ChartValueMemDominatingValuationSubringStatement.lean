module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartValEq
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageGenericBaseChangeModificatio

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartValueMemRangeOfAgreeTraitExtension

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem gs_eq_germ_top {Z X : Scheme.{0}} (f : Z ⟶ X) (z : Z) (U : X.Opens) (h : ⊤ ≤ f ⁻¹ᵁ U) (a : Γ(X, U)) :
    gs f z U a = (Z.presheaf.germ ⊤ z trivial).hom ((f.appLE U ⊤ h).hom a) := by
  rw [gs_eq f z U (h trivial)]
  exact (TopCat.Presheaf.germ_res_apply Z.presheaf (homOfLE h) z trivial _).symm

theorem specMap_appLE_top {R Ω : Type} [CommRing R] [CommRing Ω] (f : R →+* Ω) (V : (Sp R).Opens) (hV : ⊤ ≤ V)
    (h : ⊤ ≤ Spec.map (CommRingCat.ofHom f) ⁻¹ᵁ V) (a : Γ(Sp R, V)) :
    ((Spec.map (CommRingCat.ofHom f)).appLE V ⊤ h).hom a =
      (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (f ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
        (((Sp R).presheaf.map (homOfLE hV).op).hom a))) := by
  have e1 := Scheme.Hom.map_appLE (Spec.map (CommRingCat.ofHom f)) (U := ⊤) (U' := V) (V := ⊤) (fun _ _ => trivial) (homOfLE hV).op
  have e2 := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f)
  rw [← e1]
  have e3 : (Spec.map (CommRingCat.ofHom f)).appLE ⊤ ⊤ (fun _ _ => trivial) = (Spec.map (CommRingCat.ofHom f)).appTop := by
    rw [Scheme.Hom.appTop, ← Scheme.Hom.appLE_eq_app]; rfl
  have e4 : ∀ x, ((Spec.map (CommRingCat.ofHom f)).appTop).hom x =
      (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (f ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom x)) := fun x => by
    have := congrArg (fun t => t.hom x) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
    rw [← this, ← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]
  rw [CommRingCat.hom_comp, RingHom.comp_apply, e3, e4]

theorem fromSpec_appLE_self {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (h : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U) :
    hU.fromSpec.appLE U ⊤ h = (Scheme.ΓSpecIso Γ(X, U)).inv := by
  rw [Scheme.Hom.appLE, hU.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
  convert Category.comp_id _
  exact (Spec Γ(X, U)).presheaf.map_id _

theorem ΓSpecIso_hom_inv_apply (R : CommRingCat.{0}) (a : R) :
    (Scheme.ΓSpecIso R).hom.hom ((Scheme.ΓSpecIso R).inv.hom a) = a := by
  rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]

end GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem gs_specMap_comp {R Ω : Type} [CommRing R] [CommRing Ω] {X : Scheme.{0}} (f : R →+* Ω) (g : Sp R ⟶ X)
    (z : Sp Ω) (U : X.Opens) (hg : ⊤ ≤ g ⁻¹ᵁ U) (a : Γ(X, U)) :
    gs (Spec.map (CommRingCat.ofHom f) ≫ g) z U a = ((Sp Ω).presheaf.germ ⊤ z trivial).hom
      ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (f ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
        ((g.appLE U ⊤ hg).hom a)))) := by
  have h : ⊤ ≤ Spec.map (CommRingCat.ofHom f) ⁻¹ᵁ (g ⁻¹ᵁ U) := fun x _ => hg trivial
  rw [← gs_pull (Spec.map (CommRingCat.ofHom f)) g z U (hg trivial) a, gs_eq_germ_top _ z _ h,
    specMap_appLE_top f _ hg h]
  rfl

end GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem chartVal_mem_range_of_agree : ∀ (X S Y : Scheme.{0}) (gX : X ⟶ S) (L : LB X), L.IsLB → ∀ (α : Y ⟶ X) (k : ℕ) (s : SecK L α k) (j : L.ι) (W : X.Opens) (hW : W ≤ L.U j) (hWa : IsAffineOpen W), IsAffineOpen (α ⁻¹ᵁ W) → ∀ (T : Type) [CommRing T] (lam : Γ(X, W) →+* T) (W' : Type) [CommRing W'] (io : T →+* W') (σ : SecK L (pullback.fst gX (spMap io ≫ Spec.map (CommRingCat.ofHom lam) ≫ hWa.fromSpec ≫ gX)) k), Agree L σ s → ∀ (Ω : Type) [Field Ω] (ψ : Γ(Y, α ⁻¹ᵁ W) →+* Ω) (e : W' →+* Ω), (∀ c, ψ ((α.app W).hom c) = e (io (lam c))) → ∃ w : W', ψ (chartVal L α s j W hW) = e w := by
  intro X S Y gX L hL α k s j W hW hWa hαW T _ lam W' _ io σ hσ Ω _ ψ e hψ
  have hq : (Spec.map (CommRingCat.ofHom (io.comp lam)) ≫ hWa.fromSpec) ≫ gX =
      𝟙 (Sp W') ≫ (spMap io ≫ Spec.map (CommRingCat.ofHom lam) ≫ hWa.fromSpec ≫ gX) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.id_comp]
    simp only [spMap, Category.assoc]
  let q'' := pullback.lift (Spec.map (CommRingCat.ofHom (io.comp lam)) ≫ hWa.fromSpec) (𝟙 (Sp W')) hq
  let P : Sp Ω ⟶ _ := Spec.map (CommRingCat.ofHom e) ≫ q''
  let pY : Sp Ω ⟶ Y := Spec.map (CommRingCat.ofHom ψ) ≫ hαW.fromSpec
  have hring : α.appLE W (α ⁻¹ᵁ W) le_rfl ≫ CommRingCat.ofHom ψ = CommRingCat.ofHom (e.comp (io.comp lam)) := by
    ext c
    rw [Scheme.Hom.appLE_eq_app]
    exact hψ c
  have hA : P ≫ pullback.fst _ _ = pY ≫ α := by
    simp only [P, pY, q'', Category.assoc, pullback.lift_fst]
    rw [← IsAffineOpen.SpecMap_appLE_fromSpec α hWa hαW le_rfl, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc,
      hring, ← CommRingCat.ofHom_comp]
  have hαmem : ∀ x, hαW.fromSpec x ∈ α ⁻¹ᵁ W := fun x => by
    show _ ∈ ((α ⁻¹ᵁ W : Y.Opens) : Set Y)
    rw [← hαW.range_fromSpec]
    exact ⟨x, rfl⟩
  have hWmem : ∀ x, hWa.fromSpec x ∈ W := fun x => by
    show _ ∈ ((W : X.Opens) : Set X)
    rw [← hWa.range_fromSpec]
    exact ⟨x, rfl⟩
  obtain ⟨z⟩ : Nonempty (Sp Ω) := ⟨IsLocalRing.closedPoint Ω⟩
  have hz : (pY ≫ α) z ∈ L.U j := hW (hαmem _)
  obtain ⟨J, hJ, hJj⟩ := exists_good L hL z (K := Unit) (fun _ => pY ≫ α) (fun _ => j) (fun _ _ _ => rfl)
    (fun _ => hz)
  have hag := hσ (Sp Ω) P pY hA z J hJ
  have hl : sval s pY z J = ((Sp Ω).presheaf.germ ⊤ z trivial).hom
      ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (ψ (chartVal L α s j W hW))) := by
    rw [sval_of s pY z J (fun _ => j) (fun _ => hJj ()),
      ← gs_res pY z (locInt_le_chart L α j W hW) (hαmem _) (s.f (fun _ => j))]
    rw [gs_specMap_comp ψ hαW.fromSpec z (α ⁻¹ᵁ W) hαW.fromSpec_preimage_self.ge]
    rw [fromSpec_appLE_self hαW]
    exact congrArg (fun t => ((Sp Ω).presheaf.germ ⊤ z trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (ψ t)))
      (ΓSpecIso_hom_inv_apply _ _)
  have hq'' : ⊤ ≤ q'' ⁻¹ᵁ LB.wchart L (K := Fin 1) (fun _ => pullback.fst _ _) (fun _ => j) := fun x _ =>
    Set.mem_iInter.2 fun _ => hW (by
      show (q'' ≫ pullback.fst _ _) x ∈ W
      rw [pullback.lift_fst]
      exact hWmem _)
  have hr : sval σ P z J = ((Sp Ω).presheaf.germ ⊤ z trivial).hom
      ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (e ((Scheme.ΓSpecIso (CommRingCat.of W')).hom.hom
        ((q''.appLE _ ⊤ hq'').hom (σ.f (fun _ => j)))))) := by
    rw [sval_of σ P z J (fun _ => j) (fun _ => by rw [hA]; exact hJj ())]
    exact gs_specMap_comp e q'' z _ hq'' _
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of W')).hom.hom ((q''.appLE _ ⊤ hq'').hom (σ.f (fun _ => j))),
    ((((Sp Ω).presheaf.germ ⊤ z trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom).injective) ?_⟩
  simp only [RingHom.comp_apply]
  rw [← hl, ← hr, hag]

end GlobalTheory.Mum
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartValueMemRangeOfAgreeTraitExtensionStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.chartValue_mem_range_of_agree_traitExtension : ∀ (X S Y : Scheme.{0}) (gX : X ⟶ S) (L : LB X), L.IsLB → ∀ (α : Y ⟶ X) (k : ℕ) (s : SecK L α k) (j : L.ι) (W : X.Opens) (hW : W ≤ L.U j) (hWa : IsAffineOpen W), IsAffineOpen (α ⁻¹ᵁ W) → ∀ (T : Type) [CommRing T] (lam : Γ(X, W) →+* T) (W' : Type) [CommRing W'] (io : T →+* W') (σ : SecK L (pullback.fst gX (spMap io ≫ Spec.map (CommRingCat.ofHom lam) ≫ hWa.fromSpec ≫ gX)) k), Agree L σ s → ∀ (Ω : Type) [Field Ω] (ψ : Γ(Y, α ⁻¹ᵁ W) →+* Ω) (e : W' →+* Ω), (∀ c, ψ ((α.app W).hom c) = e (io (lam c))) → ∃ w : W', ψ (chartVal L α s j W hW) = e w := by
  first | exact @GlobalTheory.Mum.chartVal_mem_range_of_agree | exact GlobalTheory.Mum.chartVal_mem_range_of_agree | (intros; apply GlobalTheory.Mum.chartVal_mem_range_of_agree <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedDominatingDvrClosedFibrePointIsTrait

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem trait_at_closed_point : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R] (M : Modif R) (G : Over M.S) (Y : Scheme.{0}) (α : Y ⟶ G.left) (t : Y ⟶ Sp (FractionRing R)), α ≫ G.hom = t ≫ M.gp → ∀ (W : G.left.Opens) (hWa : IsAffineOpen W) (x : G.left) (hx : x ∈ W), M.π (G.hom x) = closedPoint R → ∀ (F : Type) [Field F] (β : Γ(Y, α ⁻¹ᵁ W) →+* F) (V : ValuationSubring F), IsDiscreteValuationRing V → ∀ (h1 : ∀ c, β ((α.app W).hom c) ∈ V), (∀ c, (G.left.residue x).hom ((G.left.presheaf.germ W x hx).hom c) = 0 → β ((α.app W).hom c) ∈ V.nonunits) → ∃ (T : Type) (_ : CommRing T) (_ : IsDomain T) (_ : IsLocalRing T) (lam : Γ(G.left, W) →+* T) (g : V →+* T) (φ : R →+* T), GlobalTheory.LN.CDvr T ∧ Function.Injective g ∧ IsLocalHom g ∧ (∀ c, g ⟨β ((α.app W).hom c), h1 c⟩ = lam c) ∧ Function.Injective φ ∧ IsLocalHom φ ∧ (Spec.map (CommRingCat.ofHom lam) ≫ hWa.fromSpec ≫ G.hom) ≫ M.π = spMap φ := by
  intro R _ _ _ _ M G Y α t hαt W hWa x hx hxc F _ β V hV h1 hnu
  haveI := hV
  let T := AdicCompletion (maximalIdeal V) V
  let g : V →+* T := algebraMap V T
  have hg : Function.Injective g := GlobalTheory.algebraMap_adicCompletion_injective_of_dvr V
  let f : G.left ⟶ Sp R := G.hom ≫ M.π
  let ρ : R →+* Γ(G.left, W) := ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ W le_top).hom
  let lam : Γ(G.left, W) →+* T := g.comp ((β.comp (α.app W).hom).codRestrict V h1)
  let φ : R →+* T := lam.comp ρ
  let ψ : FractionRing R →+* F :=
    β.comp ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv ≫ t.appLE ⊤ (α ⁻¹ᵁ W) le_top).hom
  have key : ∀ r, β ((α.app W).hom (ρ r)) = ψ (algebraMap R (FractionRing R) r) := by
    intro r
    have hc : ∀ {a b : Y ⟶ Sp R} (_ : a = b), a.appLE ⊤ (α ⁻¹ᵁ W) le_top = b.appLE ⊤ (α ⁻¹ᵁ W) le_top := by
      rintro _ _ rfl; rfl
    have e1 : f.appLE ⊤ W le_top ≫ α.app W = (α ≫ f).appLE ⊤ (α ⁻¹ᵁ W) le_top := by
      rw [Scheme.Hom.app_eq_appLE]; exact Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
    have e2 : α ≫ f = t ≫ jK R := by
      simp only [f]; rw [reassoc_of% hαt, M.gp_π]
    have e4 : (t ≫ jK R).appLE ⊤ (α ⁻¹ᵁ W) le_top = (jK R).appTop ≫ t.appLE ⊤ (α ⁻¹ᵁ W) le_top :=
      Scheme.Hom.comp_appLE t (jK R) ⊤ (α ⁻¹ᵁ W) le_top
    have e3 : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ W le_top ≫ α.app W =
        CommRingCat.ofHom (algebraMap R (FractionRing R)) ≫ (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv ≫
          t.appLE ⊤ (α ⁻¹ᵁ W) le_top := by
      rw [e1, hc e2, e4, ← Category.assoc, ← Category.assoc, Scheme.ΓSpecIso_inv_naturality]
    change β (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ W le_top ≫ α.app W).hom r) =
      β ((CommRingCat.ofHom (algebraMap R (FractionRing R)) ≫ (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv ≫
          t.appLE ⊤ (α ⁻¹ᵁ W) le_top).hom r)
    rw [e3]
  have hφi : Function.Injective φ := by
    intro a b hab
    have h2 : ((β.comp (α.app W).hom).codRestrict V h1) (ρ a) = ((β.comp (α.app W).hom).codRestrict V h1) (ρ b) := hg hab
    have h3 : β ((α.app W).hom (ρ a)) = β ((α.app W).hom (ρ b)) := congrArg Subtype.val h2
    rw [key, key] at h3
    exact IsFractionRing.injective R (FractionRing R) (ψ.injective h3)
  haveI : CharZero T := charZero_of_injective_ringHom hφi
  refine ⟨T, inferInstance, inferInstance, inferInstance, lam, g, φ,
    ⟨inferInstance, inferInstance, inferInstance⟩, hg, inferInstance, fun c => rfl, hφi, ?_, ?_⟩
  · constructor
    intro r hu
    by_contra hr
    have hrm : r ∈ maximalIdeal R := hr
    have hres : (G.left.residue x).hom ((G.left.presheaf.germ W x hx).hom (ρ r)) = 0 := by
      have hb : x ∉ G.left.basicOpen (ρ r) := by
        intro hxb
        have e := Scheme.basicOpen_appLE f W ⊤ le_top ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)
        rw [basicOpen_eq_of_affine (R := CommRingCat.of R) r] at e
        have h4 := ((show G.left.basicOpen (ρ r) = _ from e).le hxb).2
        have h7 : r ∉ PrimeSpectrum.asIdeal (f x) := h4
        have h6 : f x = closedPoint R := hxc
        rw [h6] at h7
        exact h7 hrm
      rw [Scheme.mem_basicOpen _ _ _ hx] at hb
      exact (IsLocalRing.residue_eq_zero_iff _).2 hb
    have h5 := hnu (ρ r) hres
    have h6 : ((β.comp (α.app W).hom).codRestrict V h1) (ρ r) ∈ maximalIdeal V :=
      (ValuationSubring.coe_mem_nonunits_iff (a := ⟨_, h1 (ρ r)⟩)).mp h5
    exact h6 (isUnit_of_map_unit g _ hu)
  · simp only [Category.assoc]
    rw [← IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top (Sp R)) hWa le_top,
      IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp, ← Spec.map_comp]
    rfl

end GlobalTheory.Mum
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedDominatingDvrClosedFibrePointIsTraitStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.completed_dominating_dvr_closedFibre_point_is_trait : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R] (M : Modif R) (G : Over M.S) (Y : Scheme.{0}) (α : Y ⟶ G.left) (t : Y ⟶ Sp (FractionRing R)), α ≫ G.hom = t ≫ M.gp → ∀ (W : G.left.Opens) (hWa : IsAffineOpen W) (x : G.left) (hx : x ∈ W), M.π (G.hom x) = closedPoint R → ∀ (F : Type) [Field F] (β : Γ(Y, α ⁻¹ᵁ W) →+* F) (V : ValuationSubring F), IsDiscreteValuationRing V → ∀ (h1 : ∀ c, β ((α.app W).hom c) ∈ V), (∀ c, (G.left.residue x).hom ((G.left.presheaf.germ W x hx).hom c) = 0 → β ((α.app W).hom c) ∈ V.nonunits) → ∃ (T : Type) (_ : CommRing T) (_ : IsDomain T) (_ : IsLocalRing T) (lam : Γ(G.left, W) →+* T) (g : V →+* T) (φ : R →+* T), GlobalTheory.LN.CDvr T ∧ Function.Injective g ∧ IsLocalHom g ∧ (∀ c, g ⟨β ((α.app W).hom c), h1 c⟩ = lam c) ∧ Function.Injective φ ∧ IsLocalHom φ ∧ (Spec.map (CommRingCat.ofHom lam) ≫ hWa.fromSpec ≫ G.hom) ≫ M.π = spMap φ := by
  first | exact @GlobalTheory.Mum.trait_at_closed_point | exact GlobalTheory.Mum.trait_at_closed_point | (intros; apply GlobalTheory.Mum.trait_at_closed_point <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartValueMemDominatingValuationSubring

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem mem_valuationSubring_of_image : ∀ (F : Type) [Field F] (V : ValuationSubring F) (T : Type) [CommRing T] [IsLocalRing T] (g : V →+* T), IsLocalHom g → ∀ (W' : Type) [CommRing W'] [IsDomain W'] [IsLocalRing W'] (io : T →+* W'), Function.Injective io → io.Finite → ∀ (Ω : Type) [Field Ω] (iF : F →+* Ω) (e : W' →+* Ω), Function.Injective e → (∀ v : V, iF v = e (io (g v))) → ∀ (y : F) (w : W'), iF y = e w → y ∈ V := by
  intro F _ V T _ _ g hg W' _ _ _ io hioi hiof Ω _ iF e he hi y w hy
  haveI : IsLocalHom io := RingHom.IsIntegral.isLocalHom hiof.to_isIntegral hioi
  by_contra hyV
  have hy0 : y ≠ 0 := fun h => hyV (h ▸ V.zero_mem)
  have hinv : y⁻¹ ∈ V := (V.mem_or_inv_mem y).resolve_left hyV
  let u : V := ⟨y⁻¹, hinv⟩
  have hu : ¬ IsUnit u := by
    intro hu
    obtain ⟨v, hv⟩ := hu.exists_right_inv
    have h' : y⁻¹ * (v : F) = 1 := by simpa [u] using congrArg Subtype.val hv
    have hv' : (v : F) = y := by
      calc (v : F) = y * (y⁻¹ * v) := by rw [← _root_.mul_assoc, mul_inv_cancel₀ hy0, _root_.one_mul]
        _ = y := by rw [h', _root_.mul_one]
    exact hyV (hv' ▸ v.2)
  have hprod : io (g u) * w = 1 := by
    apply he
    rw [map_mul, map_one, ← hi u, ← hy, ← map_mul]
    simp [u, inv_mul_cancel₀ hy0]
  exact hu ((isUnit_map_iff g u).1 ((isUnit_map_iff io (g u)).1 (IsUnit.of_mul_eq_one _ hprod)))

theorem chartVal_mem_of_dominates : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [CharZero R] (M : Modif R) (G : Over M.S), Smooth G.hom → QuasiCompact G.hom → GeometricallyIrreducible G.hom → ∀ (L : LB G.left), L.IsLB → ∀ (Y : Scheme.{0}) (α : Y ⟶ G.left) (t : Y ⟶ Sp (FractionRing R)), IsPullback α t G.hom M.gp → ∀ (k : ℕ) (s : SecK L α k), TraitReg M G L s → ∀ (j : L.ι) (U : M.S.Opens) (W : G.left.Opens) (hW : W ≤ L.U j), W ≤ G.hom ⁻¹ᵁ U → IsAffineOpen W → IsAffineOpen U → ∀ (x : G.left) (hx : x ∈ W), M.π (G.hom x) = closedPoint R → ∀ (F : Type) [Field F] (β : Γ(Y, α ⁻¹ᵁ W) →+* F) (V : ValuationSubring F), IsDiscreteValuationRing V → (∀ c, β ((α.app W).hom c) ∈ V) → (∀ c, (G.left.residue x).hom ((G.left.presheaf.germ W x hx).hom c) = 0 → β ((α.app W).hom c) ∈ V.nonunits) → β (chartVal L α s j W hW) ∈ V := by
  intro R _ _ _ _ _ M G hsm hqc hgi L hL Y α t hpb k s hs j U W hW hWU hWa hUa x hx hcl F _ β V hV h1 h2
  obtain ⟨T, _, _, _, lam, g, φ, hT, hgi', hgl, hgl', hφi, hφl, hξ⟩ :=
    GlobalTheory.T.completed_dominating_dvr_closedFibre_point_is_trait R M G Y α t hpb.w W hWa x hx hcl F β V hV h1 h2
  obtain ⟨W', _, _, _, io, σ, hW', hioi, hiof, hag⟩ := hs T hT φ (Spec.map (CommRingCat.ofHom lam) ≫ hWa.fromSpec ≫ G.hom) hφi hφl hξ
  let e : W' →+* FractionRing W' := algebraMap W' (FractionRing W')
  have he : Function.Injective e := IsFractionRing.injective W' (FractionRing W')
  have hgg : Function.Injective ((e.comp io).comp g) := he.comp (hioi.comp hgi')
  let iF : F →+* FractionRing W' := IsFractionRing.lift hgg
  have hi : ∀ v : V, iF v = e (io (g v)) := fun v => IsFractionRing.lift_algebraMap hgg v
  have hαW := GlobalTheory.Mum.isAffineOpen_preimage_genericBaseChange R M G Y α t hpb W hWa
  obtain ⟨w, hw⟩ := GlobalTheory.T.chartValue_mem_range_of_agree_traitExtension G.left M.S Y G.hom L hL α k s j W hW hWa hαW T lam W' io σ hag (FractionRing W') (iF.comp β) e
    (fun c => (hi ⟨_, h1 c⟩).trans (by rw [hgl' c]))
  have hw' : iF (β (chartVal L α s j W hW)) = e w := hw
  exact mem_valuationSubring_of_image F V T g hgl W' io hioi hiof (FractionRing W') iF e he hi (β (chartVal L α s j W hW)) w hw'

end GlobalTheory.Mum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartValueMemDominatingValuationSubringStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.chartValue_mem_dominating_valuationSubring : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [CharZero R] (M : Modif R) (G : Over M.S), Smooth G.hom → QuasiCompact G.hom → GeometricallyIrreducible G.hom → ∀ (L : LB G.left), L.IsLB → ∀ (Y : Scheme.{0}) (α : Y ⟶ G.left) (t : Y ⟶ Sp (FractionRing R)), IsPullback α t G.hom M.gp → ∀ (k : ℕ) (s : SecK L α k), TraitReg M G L s → ∀ (j : L.ι) (U : M.S.Opens) (W : G.left.Opens) (hW : W ≤ L.U j), W ≤ G.hom ⁻¹ᵁ U → IsAffineOpen W → IsAffineOpen U → ∀ (x : G.left) (hx : x ∈ W), M.π (G.hom x) = closedPoint R → ∀ (F : Type) [Field F] (β : Γ(Y, α ⁻¹ᵁ W) →+* F) (V : ValuationSubring F), IsDiscreteValuationRing V → (∀ c, β ((α.app W).hom c) ∈ V) → (∀ c, (G.left.residue x).hom ((G.left.presheaf.germ W x hx).hom c) = 0 → β ((α.app W).hom c) ∈ V.nonunits) → β (chartVal L α s j W hW) ∈ V := by
  first | exact @GlobalTheory.Mum.chartVal_mem_of_dominates | exact GlobalTheory.Mum.chartVal_mem_of_dominates | (intros; apply GlobalTheory.Mum.chartVal_mem_of_dominates <;> assumption)
end
end
