module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkOfInjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ToStkAInjective
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
import Mathlib.Tactic.Polynomial.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.PullGt
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitAdicSumOriginValuesIntegralFamily
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FibreLawOfTestCartesian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorFieldPointThroughGenericPoint

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CarriesUnitSectionRigidificationUnit

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum

theorem stalkOf_cpt_bijective (W : Type) [CommRing W] [IsLocalRing W] : Function.Bijective (stalkOf (cpt W)) := by
  have e : stalkOf (cpt W) = (stalkClosedPointIso (.of W)).inv.hom := by
    have h := ΓSpecIso_hom_stalkClosedPointIso_inv (CommRingCat.of W)
    have h' : (stalkClosedPointIso (.of W)).inv = (Scheme.ΓSpecIso (CommRingCat.of W)).inv ≫
        (Sp W).presheaf.germ ⊤ (cpt W) trivial := by
      rw [Iso.eq_inv_comp]; exact h
    rw [h']; rfl
  rw [e]
  exact (stalkClosedPointIso (.of W)).symm.commRingCatIsoToRingEquiv.bijective

theorem exists_unit_stalkOf (W : Type) [CommRing W] [IsLocalRing W] (x : ((Sp W).presheaf.stalk (cpt W))ˣ) :
    ∃ ε : Wˣ, stalkOf (cpt W) (ε : W) = x.val := by
  let e := RingEquiv.ofBijective _ (stalkOf_cpt_bijective W)
  exact ⟨Units.map e.symm.toMonoidHom x, e.apply_symm_apply x.val⟩

theorem gs_scal_section {W : Type} [CommRing W] {Y : Scheme.{0}} (p : Y ⟶ Sp W) (e : Sp W ⟶ Y) (he : e ≫ p = 𝟙 _)
    (z : Sp W) (u : W) : gs e z ⊤ (scal p u) = stalkOf z u := by
  have h := gs_pull e p z ⊤ trivial ((Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom u)
  rw [he] at h
  exact h.trans (gs_eq (𝟙 _) z ⊤ trivial _)

theorem gw_val_indep {X X' Y Y' Z : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (w : LB.Iso L' (L.pull F))
    (hw : w.IsGen) {s : Y ⟶ X} {s' : Y' ⟶ X'} (t : LB.Gen (L.pull s)) (ht : t.IsGen) (t' : LB.Gen (L'.pull s'))
    (ht' : t'.IsGen) (r : Z ⟶ Y) (r' : Z ⟶ Y') (e : Z ⟶ X') (he' : r' ≫ s' = e) (he : r ≫ s = e ≫ F) (z : Z)
    {I J : (Z ⟶ X) → L.ι} {I' J' : (Z ⟶ X') → L'.ι} (hI : Good L z I) (hJ : Good L z J) (hI' : Good L' z I')
    (hJ' : Good L' z J') :
    gw w e z (J (e ≫ F)) (J' e) * val t' r' z J' * (val t r z J)⁻¹ =
      gw w e z (I (e ≫ F)) (I' e) * val t' r' z I' * (val t r z I)⁻¹ := by
  have a := (isGen_iff w).1 hw Z e z (J (e ≫ F)) (I (e ≫ F)) (J' e) (I' e) (hJ (e ≫ F)) (hI (e ≫ F)) (hJ' e) (hI' e)
  have b : val t r z J = _ * val t r z I := gen_trans ht r z (hJ.mem _ r) (hI.mem _ r)
  have c : val t' r' z J' = _ * val t' r' z I' := gen_trans ht' r' z (hJ'.mem _ r') (hI'.mem _ r')
  rw [trF, Fintype.prod_unique, zpow_one] at b c
  subst he'
  rw [he] at b
  rw [a, b, c]
  generalize gm ((r' ≫ s') ≫ F) z _ _ = A
  generalize gm (r' ≫ s') z _ _ = B
  rw [mul_inv]
  generalize gw w _ _ _ _ = C
  generalize val t' r' z I' = D
  generalize (val t r z I)⁻¹ = E
  have : A * B⁻¹ * C * (B * D) * (A⁻¹ * E) = (A * A⁻¹) * (B * B⁻¹) * (C * D * E) := by ac_rfl
  rw [this]; simp

theorem Trait.carries_unit : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (k : ℕ) (u : W) (σ' : H0 T.U.LG.L k) (σ : SecK C.P.L.L T.β k), T.Carries u σ' σ → ∃ ε : Wˣ, ∀ J J', Good C.P.L.L (cpt W) J → Good T.U.LG.L (cpt W) J' → sval σ (unitW T.G) (cpt W) J * (val T.U.LG.rig (idW W) (cpt W) J').val ^ k = stalkOf (cpt W) (u * ε) * sval σ' (unitW T.G) (cpt W) J' * (val C.P.L.rig T.ξ (cpt W) J).val ^ k := by
  intro R _ _ _ D C W _ _ _ T k u σ' σ h
  obtain ⟨I, hI, -⟩ := exists_good C.P.L.L C.P.L.isLB (cpt W) (K := PEmpty.{1}) PEmpty.elim PEmpty.elim
    (fun a => a.elim) (fun a => a.elim)
  obtain ⟨I', hI', -⟩ := exists_good T.U.LG.L T.U.LG.isLB (cpt W) (K := PEmpty.{1}) PEmpty.elim PEmpty.elim
    (fun a => a.elim) (fun a => a.elim)
  have he : T.ξ ≫ eSec C.G = unitW T.G ≫ T.β := (PullGtPf.IsGrpPullback.one_left T.cart).symm
  obtain ⟨ε, hε⟩ := exists_unit_stalkOf W ((gw T.ℓ (unitW T.G) (cpt W) (I (unitW T.G ≫ T.β)) (I' (unitW T.G)) *
    val T.U.LG.rig (idW W) (cpt W) I' * (val C.P.L.rig T.ξ (cpt W) I)⁻¹) ^ k)
  refine ⟨ε, fun J J' hJ hJ' => ?_⟩
  have key := gw_val_indep T.ℓ T.ℓ_gen C.P.L.rig C.P.L.rigGen T.U.LG.rig T.U.LG.rigGen T.ξ (idW W) (unitW T.G)
    (Category.id_comp _) he (cpt W) hI hJ hI' hJ'
  rw [← key] at hε
  rw [h _ (unitW T.G) (cpt W) J J' hJ hJ', gs_scal_section T.G.hom (unitW T.G) (Over.w η[T.G]), map_mul, hε]
  generalize gw T.ℓ _ _ _ _ = A
  generalize val T.U.LG.rig _ _ _ = B
  generalize val C.P.L.rig _ _ _ = E
  have : (A * B * E⁻¹) ^ k * E ^ k = A ^ k * B ^ k := by rw [← mul_pow, ← mul_pow, inv_mul_cancel_right]
  have := congrArg Units.val this
  simp only [Units.val_mul, Units.val_pow_eq_pow_val] at this ⊢
  linear_combination (-(stalkOf (cpt W) u * sval σ' (unitW T.G) (cpt W) J')) * this

end GlobalTheory.Mum
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CarriesUnitSectionRigidificationUnitStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.carries_unitSection_rigidification_unit : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (k : ℕ) (u : W) (σ' : H0 T.U.LG.L k) (σ : SecK C.P.L.L T.β k), T.Carries u σ' σ → ∃ ε : Wˣ, ∀ J J', Good C.P.L.L (cpt W) J → Good T.U.LG.L (cpt W) J' → sval σ (unitW T.G) (cpt W) J * (val T.U.LG.rig (idW W) (cpt W) J').val ^ k = stalkOf (cpt W) (u * ε) * sval σ' (unitW T.G) (cpt W) J' * (val C.P.L.rig T.ξ (cpt W) J).val ^ k := by
  first | exact @GlobalTheory.Mum.Trait.carries_unit | exact GlobalTheory.Mum.Trait.carries_unit | (intros; apply GlobalTheory.Mum.Trait.carries_unit <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitAdicSumOriginValuesIntegralFamilyStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.exists_unit_adic_sum_origin_values_integral_family : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (k : ℕ), 1 ≤ k → ∀ b₀ : D.toPre.SecB k 0, eSec D.toPre.P.A (closedPoint R) ∈ nonzeroLocus b₀ → ∀ F₀ : IntFam (maximalIdeal R) D.toPre k, F₀.Lead 0 b₀ → ∃ s₀ : R, IsUnit s₀ ∧ ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (σ' : H0 T.U.LG.L k) (f' : ∀ x, T.D'.toPre.SecB k x), (∀ x, PullB T.hD x (F₀.f (T.hD.xe x)) (f' x)) → (∀ e, T.U.ExpandsAt e k σ' f') → ∀ J', Good T.U.LG.L (cpt W) J' → sval σ' (unitW T.G) (cpt W) J' = stalkOf (cpt W) (T.φ s₀) * (val T.U.LG.rig (idW W) (cpt W) J').val ^ k := by
  first | exact @GlobalTheory.Mum.exists_unit_origin_sum | exact GlobalTheory.Mum.exists_unit_origin_sum | (intros; apply GlobalTheory.Mum.exists_unit_origin_sum <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValueUnitSectionSmulGenericFibreSection

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.UnitGen

def gv {A : Type} [CommRing A] {X : Scheme.{0}} (f : Sp A ⟶ X) (V : X.Opens) (h : ⊤ ≤ f ⁻¹ᵁ V) (c : Γ(X, V)) : A :=
  (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom (((Sp A).presheaf.map (homOfLE h).op).hom ((f.app V).hom c))

theorem gs_gv {A : Type} [CommRing A] {X : Scheme.{0}} (f : Sp A ⟶ X) (V : X.Opens) (h : ⊤ ≤ f ⁻¹ᵁ V) (c : Γ(X, V))
    (z : Sp A) : gs f z V c = stalkOf z (gv f V h c) := by
  rw [gs_eq f z V (h trivial)]
  simp only [stalkOf, gv, RingHom.comp_apply]
  rw [Iso.hom_inv_id_apply]
  exact (TopCat.Presheaf.germ_res_apply _ _ _ _ _).symm

theorem gs_spMap_top {A B : Type} [CommRing A] [CommRing B] (ψ : A →+* B) (e : Γ(Sp A, ⊤)) (z : Sp B) :
    gs (spMap ψ) z ⊤ e = stalkOf z (ψ ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom e)) := by
  rw [gs_eq _ z ⊤ trivial]
  simp only [stalkOf, RingHom.comp_apply]
  have := congrArg (fun q => q.hom e) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ψ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
  rw [← this, Iso.hom_inv_id_apply]
  rfl

theorem gs_comp_gv {A B : Type} [CommRing A] [CommRing B] (ψ : A →+* B) {X : Scheme.{0}} (f : Sp A ⟶ X) (V : X.Opens)
    (h : ⊤ ≤ f ⁻¹ᵁ V) (c : Γ(X, V)) (z : Sp B) : gs (spMap ψ ≫ f) z V c = stalkOf z (ψ (gv f V h c)) := by
  rw [← gs_pull (spMap ψ) f z V (h trivial) c, ← gs_res (spMap ψ) z h trivial, gs_spMap_top]
  rfl

theorem sp_field_eq {F : Type} [Field F] (a b : Sp F) : a = b :=
  PrimeSpectrum.ext (by haveI := a.isPrime; haveI := b.isPrime; rw [Ideal.eq_bot_of_prime a.asIdeal, Ideal.eq_bot_of_prime b.asIdeal])

end GlobalTheory.Mum.UnitGen


open GlobalTheory.Mum.UnitGen in
theorem GlobalTheory.Mum.UnitGen.value_unit_generic : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (k : ℕ) (s : SecK C.P.L.L C.α k), ∃ x y : R, y ≠ 0 ∧ ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (a : W) (σ : SecK C.P.L.L T.β k), (∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left), p ≫ T.β = p' ≫ C.α → ∀ z J, Good C.P.L.L z J → sval σ p z J = gs p z ⊤ (scal T.G.hom a) * sval s p' z J) → ∀ J, Good C.P.L.L (cpt W) J → stalkOf (cpt W) (T.φ y) * sval σ (unitW T.G) (cpt W) J = stalkOf (cpt W) (a * T.φ x) * (val C.P.L.rig T.ξ (cpt W) J).val ^ k := by
  intro R _ _ _ hB D C k s
  have hL : C.P.L.L.IsLB := C.P.L.isLB
  have hrg : C.P.L.rig.IsGen := C.P.L.rigGen
  have hE : eSec C.A.A ≫ C.α = C.gp ≫ eSec C.G := GlobalTheory.ZJ.eSec_comp_of_isGrpPullback C.α_cart
  obtain ⟨i₀, hi₀⟩ := exists_chart hL ((C.gp ≫ eSec C.G) (cpt (FractionRing R)))
  have hs₀ : ⊤ ≤ (eSec C.A.A) ⁻¹ᵁ LB.wchart C.P.L.L (fun _ : Fin 1 => C.α) (fun _ => i₀) :=
    (top_le_iff_cpt _ _).2 (Set.mem_iInter.2 fun _ => by
      rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, hE]; exact hi₀)
  have hr₀ : ⊤ ≤ C.gp ⁻¹ᵁ LB.wchart C.P.L.L (fun _ : PUnit => eSec C.G) (fun _ => i₀) :=
    (top_le_iff_cpt _ _).2 (Set.mem_iInter.2 fun _ => by
      rw [Set.mem_preimage, ← Scheme.Hom.comp_apply]; exact hi₀)
  set cs : FractionRing R := gv (eSec C.A.A) _ hs₀ (s.f (fun _ => i₀)) with hcs
  set cr : FractionRing R := gv C.gp _ hr₀ (C.P.L.rig.s (fun _ => i₀)).val with hcr
  have hcr0 : IsUnit cr := ((((C.P.L.rig.s (fun _ => i₀)).isUnit.map (C.gp.app _).hom).map _).map _)
  obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective (A := R) (cs / cr ^ k)
  refine ⟨x, y, nonZeroDivisors.ne_zero hy, ?_⟩
  intro W _ _ _ T a σ hσ J hJ

  have hinj : Function.Injective ((algebraMap W (FractionRing W)).comp T.φ) :=
    (IsFractionRing.injective W (FractionRing W)).comp T.inj
  obtain ⟨ga, hga, hgp⟩ := Modif.factor_gp R C.toModif (FractionRing W) ((algebraMap W _).comp T.φ) (jK W ≫ T.ξ) hinj (by
    rw [Category.assoc, T.ξ_π]
    exact (Spec.map_comp _ _).symm)
  have hjK : jK W = spMap (algebraMap W (FractionRing W)) := rfl
  have hU : unitW T.G ≫ T.β = T.ξ ≫ eSec C.G := GlobalTheory.ZJ.eSec_comp_of_isGrpPullback T.cart
  set g : Sp (FractionRing W) := cpt (FractionRing W)
  set p : Sp (FractionRing W) ⟶ T.G.left := jK W ≫ unitW T.G with hp
  set p' : Sp (FractionRing W) ⟶ C.A.A.left := spMap ga ≫ eSec C.A.A with hp'
  have hr : jK W ≫ T.ξ ≫ eSec C.G = spMap ga ≫ C.gp ≫ eSec C.G := by rw [← Category.assoc, hgp, Category.assoc]
  have hpp : p ≫ T.β = p' ≫ C.α := by
    rw [hp, hp', Category.assoc, Category.assoc, hU, hE, hr]
  set I := J (T.ξ ≫ eSec C.G) with hIdef
  have hI : (T.ξ ≫ eSec C.G) (cpt W) ∈ C.P.L.L.U I := hJ _
  have hItop : ⊤ ≤ (T.ξ ≫ eSec C.G) ⁻¹ᵁ C.P.L.L.U I := (top_le_iff_cpt _ _).2 hI
  have hpI : (p ≫ T.β) g ∈ C.P.L.L.U I := by
    rw [hp, Category.assoc, hU, Scheme.Hom.comp_apply]; exact hItop trivial
  have hpi₀ : (p ≫ T.β) g ∈ C.P.L.L.U i₀ := by
    rw [hp, Category.assoc, hU, ← Category.assoc, hgp, Category.assoc, Scheme.Hom.comp_apply,
      sp_field_eq ((spMap ga) g) (cpt (FractionRing R))]
    exact hi₀
  obtain ⟨J', hJ', hJ'e⟩ := exists_good C.P.L.L hL g (K := PUnit) (fun _ => p ≫ T.β) (fun _ => I) (fun _ _ _ => rfl)
    (fun _ => hpI)
  have e1 := hσ _ p p' hpp g J' hJ'
  rw [sval_of σ p g J' (fun _ => I) (fun _ => hJ'e ⟨⟩),
    sval_of s p' g J' (fun _ => I) (fun _ => by rw [← hpp]; exact hJ'e ⟨⟩)] at e1

  have hσtop : ⊤ ≤ unitW T.G ⁻¹ᵁ LB.wchart C.P.L.L (fun _ : Fin 1 => T.β) (fun _ => I) :=
    (top_le_iff_cpt _ _).2 (Set.mem_iInter.2 fun _ => by
      rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, hU]; exact hI)
  have hρtop : ⊤ ≤ T.ξ ⁻¹ᵁ LB.wchart C.P.L.L (fun _ : PUnit => eSec C.G) (fun _ => I) :=
    (top_le_iff_cpt _ _).2 (Set.mem_iInter.2 fun _ => by
      rw [Set.mem_preimage, ← Scheme.Hom.comp_apply]; exact hI)
  set σv : W := gv (unitW T.G) _ hσtop (σ.f (fun _ => I)) with hσv
  set ρv : W := gv T.ξ _ hρtop (C.P.L.rig.s (fun _ => I)).val with hρv
  have eσ : gs p g (LB.wchart C.P.L.L (fun _ : Fin 1 => T.β) (fun _ => I)) (σ.f (fun _ => I)) =
      stalkOf g (algebraMap W _ σv) := by
    rw [hp, hjK]; exact gs_comp_gv _ _ _ hσtop _ g
  have hu : unitW T.G ≫ T.G.hom = 𝟙 _ := by simpa [unitW, eSec] using Over.w (η[T.G])
  have ea : gs p g ⊤ (scal T.G.hom a) = stalkOf g (algebraMap W _ a) := by
    have h1 : p ≫ T.G.hom = spMap (algebraMap W (FractionRing W)) := by
      rw [hp, Category.assoc, hu, Category.comp_id]
    have h2 := gs_pull p T.G.hom g ⊤ trivial ((Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom a)
    rw [h1, gs_spMap_top, Iso.inv_hom_id_apply] at h2
    exact h2

  have hrp : (jK W ≫ T.ξ) ≫ eSec C.G = p ≫ T.β := by rw [hp, Category.assoc, Category.assoc, hU]
  have hp'i₀ : p' g ∈ LB.wchart C.P.L.L (fun _ : Fin 1 => C.α) (fun _ => i₀) := Set.mem_iInter.2 fun _ => by
    rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, ← hpp]; exact hpi₀
  have hp'I : p' g ∈ LB.wchart C.P.L.L (fun _ : Fin 1 => C.α) (fun _ => I) := Set.mem_iInter.2 fun _ => by
    rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, ← hpp]; exact hpI
  have hri₀ : (jK W ≫ T.ξ) g ∈ LB.wchart C.P.L.L (fun _ : PUnit => eSec C.G) (fun _ => i₀) := Set.mem_iInter.2 fun _ => by
    rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, hrp]; exact hpi₀
  have hrI : (jK W ≫ T.ξ) g ∈ LB.wchart C.P.L.L (fun _ : PUnit => eSec C.G) (fun _ => I) := Set.mem_iInter.2 fun _ => by
    rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, hrp]; exact hpI
  have e2 := sec_trans s p' g hp'i₀ hp'I
  have orbitMap_conj_smul_zero : gs p' g (LB.wchart C.P.L.L (fun _ : Fin 1 => C.α) (fun _ => i₀)) (s.f (fun _ => i₀)) = stalkOf g (ga cs) := by
    rw [hp']; exact gs_comp_gv ga _ _ hs₀ _ g
  have e3 := gen_trans hrg (jK W ≫ T.ξ) g hri₀ hrI
  have eB0 : (gm (jK W ≫ T.ξ) g (LB.wchart C.P.L.L (fun _ : PUnit => eSec C.G) (fun _ => i₀)) (C.P.L.rig.s (fun _ => i₀))).val = stalkOf g (ga cr) := by
    refine (gs_unit (jK W ≫ T.ξ) g _ hri₀ _).symm.trans ?_
    rw [hgp]; exact gs_comp_gv ga _ _ hr₀ _ g
  have eB : (gm (jK W ≫ T.ξ) g (LB.wchart C.P.L.L (fun _ : PUnit => eSec C.G) (fun _ => I)) (C.P.L.rig.s (fun _ => I))).val = stalkOf g (algebraMap W _ ρv) := by
    refine (gs_unit (jK W ≫ T.ξ) g _ hrI _).symm.trans ?_
    rw [hjK]; exact gs_comp_gv _ _ _ hρtop _ g
  have et : trF (L := C.P.L.L) (fun _ : Fin 1 => C.α) (fun _ => ((k : ℕ) : ℤ)) p' g (fun _ => i₀) (fun _ => I) =
      (trF (L := C.P.L.L) (fun _ : PUnit => eSec C.G) (fun _ => 1) (jK W ≫ T.ξ) g (fun _ => i₀) (fun _ => I)) ^ k := by
    simp only [trF]
    rw [show p' ≫ C.α = (jK W ≫ T.ξ) ≫ eSec C.G from hpp.symm.trans hrp.symm]
    simp

  rw [eσ, ea] at e1
  rw [orbitMap_conj_smul_zero, et] at e2
  have e3v := congrArg Units.val e3
  rw [Units.val_mul, eB0, eB] at e3v
  have hy0 : algebraMap R (FractionRing R) y ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy
  have hxy' : algebraMap R _ x * cr ^ k = cs * algebraMap R _ y := by
    rw [div_eq_div_iff hy0 (pow_ne_zero _ hcr0.ne_zero)] at hxy; exact hxy
  have hXY := congrArg (fun q => stalkOf g (ga q)) hxy'
  simp only [map_mul, map_pow, hga, RingHom.comp_apply] at hXY
  rw [e3v, e2, Units.val_pow_eq_pow_val] at hXY
  have hW : T.φ y * σv = a * T.φ x * ρv ^ k := by
    apply ((stalkOf_injective g).comp (IsFractionRing.injective W (FractionRing W)))
    simp only [Function.comp_apply, map_mul, map_pow]
    refine ((trF (L := C.P.L.L) (fun _ : PUnit => eSec C.G) (fun _ => 1) (jK W ≫ T.ξ) g (fun _ => i₀)
      (fun _ => I)).isUnit.pow k).mul_left_inj.1 ?_
    rw [e1]
    linear_combination (-(stalkOf g (algebraMap W (FractionRing W) a))) * hXY
  have eBc : (gm T.ξ (cpt W) (LB.wchart C.P.L.L (fun _ : PUnit => eSec C.G) (fun _ => I)) (C.P.L.rig.s (fun _ => I))).val = stalkOf (cpt W) ρv :=
    (gs_unit T.ξ (cpt W) _ (hρtop trivial) _).symm.trans (gs_gv _ _ hρtop _ _)
  have eσc : gs (unitW T.G) (cpt W) (LB.wchart C.P.L.L (fun _ : Fin 1 => T.β) (fun _ => I)) (σ.f (fun _ => I)) =
      stalkOf (cpt W) σv := gs_gv _ _ hσtop _ _
  rw [sval_of σ (unitW T.G) (cpt W) J (fun _ => I) (fun _ => by rw [hU])]
  erw [eσc]
  rw [val_of C.P.L.rig T.ξ (cpt W) J (fun _ => I) (fun _ => rfl), eBc, ← map_mul, ← map_pow, ← map_mul, hW]
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValueUnitSectionSmulGenericFibreSectionStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.value_unitSection_smul_genericFibre_section : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (k : ℕ) (s : SecK C.P.L.L C.α k), ∃ x y : R, y ≠ 0 ∧ ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (a : W) (σ : SecK C.P.L.L T.β k), (∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left), p ≫ T.β = p' ≫ C.α → ∀ z J, Good C.P.L.L z J → sval σ p z J = gs p z ⊤ (scal T.G.hom a) * sval s p' z J) → ∀ J, Good C.P.L.L (cpt W) J → stalkOf (cpt W) (T.φ y) * sval σ (unitW T.G) (cpt W) J = stalkOf (cpt W) (a * T.φ x) * (val C.P.L.rig T.ξ (cpt W) J).val ^ k := by
  first | exact @GlobalTheory.Mum.UnitGen.value_unit_generic | exact GlobalTheory.Mum.UnitGen.value_unit_generic | (intros; apply GlobalTheory.Mum.UnitGen.value_unit_generic <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaNormalisationConstantOrigin

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum

theorem exists_unit_value_at_unit : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (k : ℕ), 1 ≤ k → ∀ b₀ : D.toPre.SecB k 0, eSec D.toPre.P.A (closedPoint R) ∈ nonzeroLocus b₀ → ∀ F₀ : IntFam (maximalIdeal R) D.toPre k, F₀.Lead 0 b₀ → ∃ s₀ : R, IsUnit s₀ ∧ ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (b : W) (σ : SecK C.P.L.L T.β k), T.ExpBy b σ F₀ → ∃ ε : Wˣ, ∀ J, Good C.P.L.L (cpt W) J → sval σ (unitW T.G) (cpt W) J = stalkOf (cpt W) (b * ε * T.φ s₀) * (val C.P.L.rig T.ξ (cpt W) J).val ^ k := by
  intro R _ _ _ hR D C k hk b₀ hb₀ F₀ hF₀
  obtain ⟨s₀, hs₀, h⟩ := GlobalTheory.T.exists_unit_adic_sum_origin_values_integral_family R hR D C k hk b₀ hb₀ F₀ hF₀
  refine ⟨s₀, hs₀, fun W _ _ _ T b σ hσ => ?_⟩
  obtain ⟨σ', f', hc, hp, he⟩ := hσ
  obtain ⟨ε, hε⟩ := GlobalTheory.T.carries_unitSection_rigidification_unit R D C W T k b σ' σ hc
  refine ⟨ε, fun J hJ => ?_⟩
  obtain ⟨J', hJ', -⟩ := exists_good T.U.LG.L T.U.LG.isLB (cpt W) (K := Empty) (fun e => e.elim) (fun e => e.elim)
    (fun e => e.elim) (fun e => e.elim)
  have e1 := hε J J' hJ hJ'
  rw [h W T σ' f' hp he J' hJ'] at e1
  refine mul_right_cancel₀ (pow_ne_zero k (Units.ne_zero (val T.U.LG.rig (idW W) (cpt W) J'))) ?_
  rw [e1]
  simp only [map_mul]
  ring

theorem exists_norm_const : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (k : ℕ), 1 ≤ k → ∀ b₀ : D.toPre.SecB k 0, eSec D.toPre.P.A (closedPoint R) ∈ nonzeroLocus b₀ → ∀ F₀ : IntFam (maximalIdeal R) D.toPre k, F₀.Lead 0 b₀ → ∀ s : SecK C.P.L.L C.α k, ∃ c₁ c₂ : R, c₂ ≠ 0 ∧ ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (a b : W), a ≠ 0 → b ≠ 0 → T.Exp a b s F₀ → ∃ u : Wˣ, T.φ c₂ * (u : W) * a = T.φ c₁ * b := by
  intro R _ _ _ hR D C k hk b₀ hb₀ F₀ hF₀ s
  obtain ⟨x, y, hy, h1⟩ := GlobalTheory.T.value_unitSection_smul_genericFibre_section R hR D C k s
  obtain ⟨s₀, hs₀, h2⟩ := exists_unit_value_at_unit R hR D C k hk b₀ hb₀ F₀ hF₀
  have key : ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (a b : W), T.Exp a b s F₀ →
      ∃ ε : Wˣ, T.φ y * (b * ε * T.φ s₀) = a * T.φ x := by
    intro W _ _ _ T a b hE
    obtain ⟨σ, hσ, hgen⟩ := hE
    obtain ⟨ε, hε⟩ := h2 W T b σ hσ
    obtain ⟨J, hJ, -⟩ := exists_good C.P.L.L C.P.L.isLB (cpt W) (K := Empty) (fun e => e.elim) (fun e => e.elim)
      (fun e => e.elim) (fun e => e.elim)
    have e1 := h1 W T a σ hgen J hJ
    rw [hε J hJ, ← _root_.mul_assoc, ← map_mul] at e1
    refine ⟨ε, stalkOf_injective (cpt W) (mul_right_cancel₀ ?_ e1)⟩
    exact pow_ne_zero _ (Units.ne_zero _)
  by_cases hx : x = 0
  · refine ⟨0, 1, one_ne_zero, fun W _ _ _ T a b ha hb hE => ?_⟩
    exfalso
    obtain ⟨ε, e⟩ := key W T a b hE
    rw [hx, map_zero, mul_zero] at e
    have hφy : T.φ y ≠ 0 := fun h => hy (T.inj (h.trans (map_zero _).symm))
    have hφs : T.φ s₀ ≠ 0 := (hs₀.map T.φ).ne_zero
    exact mul_ne_zero hφy (mul_ne_zero (mul_ne_zero hb (Units.ne_zero ε)) hφs) e
  · refine ⟨s₀ * y, x, hx, fun W _ _ _ T a b ha hb hE => ?_⟩
    obtain ⟨ε, e⟩ := key W T a b hE
    refine ⟨ε⁻¹, ?_⟩
    rw [map_mul]
    have hinv : (ε : W) * ((ε⁻¹ : Wˣ) : W) = 1 := Units.mul_inv ε
    linear_combination (-(((ε⁻¹ : Wˣ) : W))) * e + (T.φ y * b * T.φ s₀) * hinv

end GlobalTheory.Mum
end
end
end
