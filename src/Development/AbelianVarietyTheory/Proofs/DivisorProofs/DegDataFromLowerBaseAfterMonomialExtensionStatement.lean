module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodRel
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinesPolarisedDataBaseChangeSymmetric
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMinAt
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValEqOfAppInjective
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.StalkMapInjectiveOfFlat
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValuesNatural

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoCompGroupPullbackIso

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.PrimCocycle
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LamPullComp

section Iso

variable {S S₁ S₂ : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {B' : Over S₁} [GrpObj B']
  {G' : Over S₂} [GrpObj G'] [IsCommMonObj G'] {φ : G'.left ⟶ G.left} {β₂ : (G2 B').left ⟶ (G2 G).left}
  {sq : (G2 G').left ⟶ (G2 B').left} {L : LB G.left} {L' : LB G'.left}

theorem pt_eq (h : ∀ I, sq ≫ β₂ ≫ lamφ G I = lamφ G' I ≫ φ) (I : ULift.{0} (Finset (Fin 2))) (x : (G2 G').left) :
    lamφ G I (β₂ (sq x)) = φ (lamφ G' I x) :=
  congrArg (fun g => g x) (h I)

theorem iso_le (h : ∀ I, sq ≫ β₂ ≫ lamφ G I = lamφ G' I ≫ φ)
    (p : (((abelian₂ G L).pull β₂).pull sq).ι × (abelian₂ G' L').ι) (I : ULift.{0} (Finset (Fin 2))) :
    (((abelian₂ G L).pull β₂).pull sq).U p.1 ⊓ (abelian₂ G' L').U p.2 ≤
      lamφ G' I ⁻¹ᵁ ((L.pull φ).U (fun _ => p.1 PUnit.unit PUnit.unit I) ⊓ L'.U (p.2 I)) := fun x hx =>
  ⟨mem_pull.2 (by
    have := Set.mem_iInter.1 (mem_pull.1 (mem_pull.1 hx.1)) I
    show φ (lamφ G' I x) ∈ _
    rw [← pt_eq h I x]; exact this), Set.mem_iInter.1 hx.2 I⟩

def iso2 (h : ∀ I, sq ≫ β₂ ≫ lamφ G I = lamφ G' I ≫ φ) (v : LB.Iso L' (L.pull φ)) :
    LB.Iso (abelian₂ G' L') (((abelian₂ G L).pull β₂).pull sq) :=
  ⟨fun p => ∏ I, (res (iso_le h p I)
    (pullU (lamφ G' I) _ (v.s (fun _ => p.1 PUnit.unit PUnit.unit I, p.2 I)))) ^ lamε I⟩

theorem mumfordBundle_pullback_composite_germ_iso (h : ∀ I, sq ≫ β₂ ≫ lamφ G I = lamφ G' I ≫ φ) (v : LB.Iso L' (L.pull φ)) {Y : Scheme.{0}}
    (r : Y ⟶ (G2 G').left) (y : Y) (j : PUnit → ULift.{0} (Finset (Fin 2)) → L.ι)
    (k : ULift.{0} (Finset (Fin 2)) → L'.ι)
    (hj : ∀ I, φ (lamφ G' I (r y)) ∈ L.U (j PUnit.unit I)) (hk : ∀ I, lamφ G' I (r y) ∈ L'.U (k I)) :
    gw (iso2 h v) r y j k = ∏ I, gw v (r ≫ lamφ G' I) y (j PUnit.unit I) (k I) ^ lamε I := by
  have hm : r y ∈ (((abelian₂ G L).pull β₂).pull sq).U (fun _ => j) ⊓ (abelian₂ G' L').U k :=
    ⟨mem_pull.2 (mem_pull.2 (Set.mem_iInter.2 fun I => by
      show lamφ G I (β₂ (sq (r y))) ∈ L.U (j PUnit.unit I)
      rw [pt_eq h]; exact hj I)), Set.mem_iInter.2 hk⟩
  unfold gw
  dsimp only [iso2]
  refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun I _ => (map_zpow _ _ _).trans (congrArg (· ^ lamε I) ?_))
  exact (gm_res r y _ hm _).trans (gm_pull r (lamφ G' I) y ((L.pull φ).U (fun _ => j PUnit.unit I) ⊓ L'.U (k I))
    ⟨mem_pull.2 (hj I), hk I⟩ _)

theorem mumfordBundle_pullback_composite_isGen (h : ∀ I, sq ≫ β₂ ≫ lamφ G I = lamφ G' I ≫ φ) (v : LB.Iso L' (L.pull φ)) (hv : PGen v) :
    PGen (iso2 h v) := by
  intro Y r y j j' k k' hj hj' hk hk'
  have bj := mem_pull.1 hj
  have bj' := mem_pull.1 hj'
  have aj : ∀ I, φ (lamφ G' I (r y)) ∈ L.U (j PUnit.unit I) := fun I => by
    rw [← pt_eq h I]; exact Set.mem_iInter.1 bj I
  have aj' : ∀ I, φ (lamφ G' I (r y)) ∈ L.U (j' PUnit.unit I) := fun I => by
    rw [← pt_eq h I]; exact Set.mem_iInter.1 bj' I
  have ak : ∀ I, lamφ G' I (r y) ∈ L'.U (k I) := fun I => Set.mem_iInter.1 hk I
  have ak' : ∀ I, lamφ G' I (r y) ∈ L'.U (k' I) := fun I => Set.mem_iInter.1 hk' I
  rw [mumfordBundle_pullback_composite_germ_iso h v r y j k aj ak, mumfordBundle_pullback_composite_germ_iso h v r y j' k' aj' ak']
  have e₀ := gm_pull_g (abelian₂ G L) β₂ (r ≫ sq) y j j' hj hj'
  have e₁ := gm_linComb L (lamφ G) lamε ((r ≫ sq) ≫ β₂) y (j PUnit.unit) (j' PUnit.unit) bj bj'
  have e₂ := gm_linComb L' (lamφ G') lamε r y k k' hk hk'
  erw [e₀, e₁, e₂]
  rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun I _ => ?_
  rw [hv Y (r ≫ lamφ G' I) y (j PUnit.unit I) (j' PUnit.unit I) (k I) (k' I) (aj I) (aj' I) (ak I) (ak' I),
    Category.assoc, Category.assoc, Category.assoc, h, mul_zpow, mul_zpow, inv_zpow]

end Iso

theorem lamIso_comp_pull : ∀ {S S₁ S₂ S₀ : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] (B' : Over S₁) [GrpObj B'] (G' : Over S₂) [GrpObj G'] [IsCommMonObj G'] (T : Over S₀) [GrpObj T] [IsCommMonObj T] (f₁ : S₁ ⟶ S) (f₂ : S₂ ⟶ S₁) (β' : B'.left ⟶ G.left) (Φ : G'.left ⟶ B'.left) (φ : G'.left ⟶ G.left) (β₂ : (G2 B').left ⟶ (G2 G).left) (β₂' : (G2 B').left ⟶ (G2 T).left) (L : LB G.left) (L' : LB G'.left) (M : LB T.left) (gp' : IsGrpPullback B' G f₁ β') (gΦ : IsGrpPullback G' B' f₂ Φ), IsSquare β' β₂ → Φ ≫ β' = φ → L.IsLB → L'.IsLB → M.IsLB → ∀ (v : LB.Iso L' (L.pull φ)) (w₁ : LB.Iso ((abelian₂ G L).pull β₂) ((abelian₂ T M).pull β₂')), v.IsGen → w₁.IsGen → ∃ w : LB.Iso (abelian₂ G' L') ((abelian₂ T M).pull (GlobalTheory.HalfBC.sqOf gΦ ≫ β₂')), w.IsGen ∧ ∀ (Z : Scheme.{0}) (p : Z ⟶ (G2 G').left) (z : Z) (J : (Z ⟶ T.left) → M.ι) (J₁ : (Z ⟶ G.left) → L.ι) (J' : (Z ⟶ G'.left) → L'.ι), Good M z J → Good L z J₁ → Good L' z J' → lamVal w p z J J' = isoVal w₁ (p ≫ GlobalTheory.HalfBC.sqOf gΦ) z J J₁ * ∏ I, gw v (p ≫ lamφ G' I) z (J₁ ((p ≫ lamφ G' I) ≫ φ)) (J' (p ≫ lamφ G' I)) ^ lamε I := by
  intro S S₁ S₂ S₀ G _ _ B' _ G' _ _ T _ _ f₁ f₂ β' Φ φ β₂ β₂' L L' M gp' gΦ hsq hΦ hL hL' hM v w₁ hv hw₁
  have gp : IsGrpPullback G' G (f₂ ≫ f₁) φ := (IsGrpPullback.comp gΦ gp').congr rfl hΦ
  have e1 : GlobalTheory.HalfBC.sqOf gΦ ≫ β₂ = GlobalTheory.HalfBC.sqOf gp := by
    apply pullback.hom_ext
    · show _ ≫ (fst G G).left = _ ≫ (fst G G).left
      rw [Category.assoc, hsq.1, ← Category.assoc]
      unfold GlobalTheory.HalfBC.sqOf
      rw [← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst]
      show ((fst G' G').left ≫ Φ) ≫ β' = (fst G' G').left ≫ φ
      rw [Category.assoc, hΦ]
    · show _ ≫ (snd G G).left = _ ≫ (snd G G).left
      rw [Category.assoc, hsq.2, ← Category.assoc]
      unfold GlobalTheory.HalfBC.sqOf
      rw [← Over.comp_left, ← Over.comp_left, lift_snd, lift_snd]
      show ((snd G' G').left ≫ Φ) ≫ β' = (snd G' G').left ≫ φ
      rw [Category.assoc, hΦ]
  have h : ∀ I, GlobalTheory.HalfBC.sqOf gΦ ≫ β₂ ≫ lamφ G I = lamφ G' I ≫ φ := fun I => by
    rw [← Category.assoc, e1, GlobalTheory.HalfBC.sqOf_lamφ]
  have hΛT : (abelian₂ T M).IsLB := DVR.linComb_isLB _ hM _ _
  have hΛG : ((abelian₂ G L).pull β₂).IsLB := LB.isLB_pull (DVR.linComb_isLB _ hL _ _) _
  have hΛ' : (abelian₂ G' L').IsLB := DVR.linComb_isLB _ hL' _ _
  obtain ⟨w, Tw⟩ := exists_comp hΛG w₁ (iso2 h v) ((isGen_iff _).1 hw₁) (mumfordBundle_pullback_composite_isGen h v ((isGen_iff v).1 hv)) hΛT hΛ'
  refine ⟨w, (isGen_iff _).2 (Tw.pgen_comp hΛG ((isGen_iff _).1 hw₁) (mumfordBundle_pullback_composite_isGen h v ((isGen_iff v).1 hv))), ?_⟩
  intro Z p z J J₁ J' hJ hJ₁ hJ'
  have t := Tw Z p z (fun I => J (p ≫ (GlobalTheory.HalfBC.sqOf gΦ ≫ β₂') ≫ lamφ T I))
    (fun _ I => J₁ ((p ≫ lamφ G' I) ≫ φ)) (fun I => J' (p ≫ lamφ G' I))
    (Set.mem_iInter.2 fun I => hJ (p ≫ (GlobalTheory.HalfBC.sqOf gΦ ≫ β₂') ≫ lamφ T I))
    (mem_pull.2 (Set.mem_iInter.2 fun I => by
      show lamφ G I (β₂ (GlobalTheory.HalfBC.sqOf gΦ (p z))) ∈ L.U (J₁ ((p ≫ lamφ G' I) ≫ φ))
      rw [pt_eq h]; exact hJ₁ ((p ≫ lamφ G' I) ≫ φ)))
    (Set.mem_iInter.2 fun I => hJ' (p ≫ lamφ G' I))
  refine t.trans (congrArg₂ (· * ·) ?_ ?_)
  · show _ = gw w₁ (p ≫ GlobalTheory.HalfBC.sqOf gΦ) z (fun I => J ((p ≫ GlobalTheory.HalfBC.sqOf gΦ) ≫ β₂' ≫ lamφ T I))
      (fun _ I => J₁ ((p ≫ GlobalTheory.HalfBC.sqOf gΦ) ≫ β₂ ≫ lamφ G I))
    simp only [Category.assoc, h]
  · exact mumfordBundle_pullback_composite_germ_iso h v p z _ _ (fun I => hJ₁ ((p ≫ lamφ G' I) ≫ φ)) (fun I => hJ' (p ≫ lamφ G' I))

end GlobalTheory.LamPullComp

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoCompGroupPullbackIsoStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.PrimCocycle
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.mumfordBundleIso_comp_group_pullback_iso : ∀ {S S₁ S₂ S₀ : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] (B' : Over S₁) [GrpObj B'] (G' : Over S₂) [GrpObj G'] [IsCommMonObj G'] (T : Over S₀) [GrpObj T] [IsCommMonObj T] (f₁ : S₁ ⟶ S) (f₂ : S₂ ⟶ S₁) (β' : B'.left ⟶ G.left) (Φ : G'.left ⟶ B'.left) (φ : G'.left ⟶ G.left) (β₂ : (G2 B').left ⟶ (G2 G).left) (β₂' : (G2 B').left ⟶ (G2 T).left) (L : LB G.left) (L' : LB G'.left) (M : LB T.left) (gp' : IsGrpPullback B' G f₁ β') (gΦ : IsGrpPullback G' B' f₂ Φ), IsSquare β' β₂ → Φ ≫ β' = φ → L.IsLB → L'.IsLB → M.IsLB → ∀ (v : LB.Iso L' (L.pull φ)) (w₁ : LB.Iso ((abelian₂ G L).pull β₂) ((abelian₂ T M).pull β₂')), v.IsGen → w₁.IsGen → ∃ w : LB.Iso (abelian₂ G' L') ((abelian₂ T M).pull (GlobalTheory.HalfBC.sqOf gΦ ≫ β₂')), w.IsGen ∧ ∀ (Z : Scheme.{0}) (p : Z ⟶ (G2 G').left) (z : Z) (J : (Z ⟶ T.left) → M.ι) (J₁ : (Z ⟶ G.left) → L.ι) (J' : (Z ⟶ G'.left) → L'.ι), Good M z J → Good L z J₁ → Good L' z J' → lamVal w p z J J' = isoVal w₁ (p ≫ GlobalTheory.HalfBC.sqOf gΦ) z J J₁ * ∏ I, gw v (p ≫ lamφ G' I) z (J₁ ((p ≫ lamφ G' I) ≫ φ)) (J' (p ≫ lamφ G' I)) ^ lamε I := by
  first | exact @GlobalTheory.LamPullComp.lamIso_comp_pull | exact GlobalTheory.LamPullComp.lamIso_comp_pull | (intros; apply GlobalTheory.LamPullComp.lamIso_comp_pull <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodRelationPullbackMonomialConstants

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.PrimCocycle
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PeriodPull

open GlobalTheory.TChart

theorem gm_unitOn_map {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (u : Rˣ) (z : Sp R') :
    gm (𝟙 (Sp R')) z ⊤ (unitOn (Units.map f.toMonoidHom u)) =
      Units.map ((spMap f).stalkMap z).hom.toMonoidHom (gm (𝟙 (Sp R)) (spMap f z) ⊤ (unitOn u)) := by
  rw [← GlobalTheory.ConstFam.gm_comp_stalkMap (spMap f) (𝟙 _) z ⊤ trivial, Category.comp_id]
  apply Units.ext
  rw [gm_val _ z ⊤ trivial, gm_val _ z ⊤ trivial]
  have e := congrArg (fun g => g.hom (u : R)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
  simp only [unitOn, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
  rw [e]
  simp [Scheme.Hom.appTop]
  rfl

theorem periods_pull : ∀ (n : ℕ) (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (r : ℕ) (e₀ : (Fin r → ℤ) ≃+ D.X) {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) (V₁ : Type) [CommRing V₁] [IsDomain V₁] (f₁ : V →+* V₁) (κ₁ : W →+* V₁) (e : (Fin T.r → ℤ) ≃+ (Fin r → ℤ)) (B' : Over (Sp V₁)) [GrpObj B'] (β₂ : (G2 B').left ⟶ (G2 D.P.A).left) (β₂' : (G2 B').left ⟶ (G2 T.B).left) (x : (Fin T.r → ℤ) → (𝟙_ (Over (Sp V₁)) ⟶ B')) (w₁ : LB.Iso ((abelian₂ D.P.A D.P.L).pull β₂) ((abelian₂ T.B T.M.L).pull β₂')) (q : (Fin T.r → ℤ) → (Fin T.r → ℤ) → (FractionRing V₁)ˣ), Function.Injective f₁ → PeriodRel D T f₁ κ₁ w₁ (e.trans e₀) x n q → ∀ (V₂ : Type) [CommRing V₂] [IsDomain V₂] (f₂ : V₁ →+* V₂) (fK : FractionRing V₁ →+* FractionRing V₂) {I : Type} [Fintype I] (s : I → V₂) (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)), (∀ a, fK (algebraMap V₁ _ a) = algebraMap V₂ _ (f₂ a)) → (∀ a b, fK (q a b : FractionRing V₁) = ∏ k, algebraMap V₂ _ (s k) ^ ((n : ℤ) * ε k a b)) → ∀ (D' : DegPre V₂) (hD : IsPullDeg (f₂.comp f₁) D D') (Φ : D'.P.A.left ⟶ B'.left) (gΦ : IsGrpPullback D'.P.A B' (spMap f₂) Φ), (∀ a, (D'.c a).left ≫ Φ = spMap f₂ ≫ (x (hD.xe.trans (e₀.symm.trans e.symm) a)).left) → ∀ (w : LB.Iso (abelian₂ D'.P.A D'.P.L) ((abelian₂ T.B T.M.L).pull (GlobalTheory.HalfBC.sqOf gΦ ≫ β₂'))), (∀ (Z : Scheme.{0}) (p : Z ⟶ (G2 D'.P.A).left) (z : Z) (J : (Z ⟶ T.B.left) → T.M.L.ι) (J₁ : (Z ⟶ D.P.A.left) → D.P.L.ι) (J' : (Z ⟶ D'.P.A.left) → D'.P.L.ι), Good T.M.L z J → Good D.P.L z J₁ → Good D'.P.L z J' → lamVal w p z J J' = isoVal w₁ (p ≫ GlobalTheory.HalfBC.sqOf gΦ) z J J₁ * ∏ I, gw hD.w (p ≫ lamφ D'.P.A I) z (J₁ ((p ≫ lamφ D'.P.A I) ≫ GlobalTheory.PsiEvenPull.proj hD)) (J' (p ≫ lamφ D'.P.A I)) ^ lamε I) → ∀ a b : D'.X, ∃ k : (FractionRing V₂)ˣ, (k : FractionRing V₂) = ∏ i, algebraMap V₂ (FractionRing V₂) (s i) ^ ((n : ℤ) * ε i (hD.xe.trans (e₀.symm.trans e.symm) a) (hD.xe.trans (e₀.symm.trans e.symm) b)) ∧ ∀ z J J', Good T.M.L z J → Good D'.P.L z J' → val (D'.tau a b) (𝟙 _) z J' = gm (𝟙 (TK V₂).left) z ⊤ (unitOn k) * (lamVal w (lift (toUnit (TK V₂) ≫ D'.c a) (toUnit (TK V₂) ≫ D'.c b)).left z J J' * val (T.τ₀ ((n : ℤ) • hD.xe.trans (e₀.symm.trans e.symm) a) ((n : ℤ) • hD.xe.trans (e₀.symm.trans e.symm) b)) ((TK V₂).hom ≫ spMap (f₂.comp κ₁)) z J) := by
  intro n V _ _ D r e₀ o W _ _ _ T V₁ _ _ f₁ κ₁ e B' _ β₂ β₂' x w₁ q hf₁ hP V₂ _ _ f₂ fK I _ s ε hfK hq D' hD Φ gΦ hc w hw a b
  refine ⟨Units.map fK.toMonoidHom (q (hD.xe.trans (e₀.symm.trans e.symm) a) (hD.xe.trans (e₀.symm.trans e.symm) b)),
    hq _ _, ?_⟩
  intro z J J' hJ hJ'
  set E := hD.xe.trans (e₀.symm.trans e.symm) with hE
  obtain ⟨κK, hκK, -⟩ := GlobalTheory.HalfBC.exists_kappa f₁ f₂ fK hfK hf₁
  let g₀ : (TK V₂).left ⟶ (TK V₁).left := spMap fK
  have sg : g₀ ≫ jK V₁ = jK V₂ ≫ spMap f₂ := GlobalTheory.HalfBC.gam_comm f₂ fK hfK
  choose J₁ hJ₀ using fun χ : (TK V₂).left ⟶ D.P.A.left => exists_chart D.P.isLB (χ z)
  have hJ₁ : Good D.P.L z J₁ := hJ₀
  have cE : ∀ a, (e.trans e₀) (E a) = hD.xe a := fun a => by simp [E]
  have t₁ := hP κK hκK (E a) (E b) (g₀ z) (fun ψ => J (g₀ ≫ ψ)) (fun ψ => J₁ (g₀ ≫ ψ))
    (fun ψ => hJ (g₀ ≫ ψ)) (fun ψ => hJ₁ (g₀ ≫ ψ))
  rw [cE, cE] at t₁
  have t₂ := (congrArg (Units.map (g₀.stalkMap z).hom.toMonoidHom) t₁).trans
    ((map_mul _ _ _).trans (congrArg₂ (· * ·) rfl (map_mul _ _ _)))
  have n₁ : val (D.tau (hD.xe a) (hD.xe b)) (g₀ ≫ κK) z J₁ = Units.map (g₀.stalkMap z).hom.toMonoidHom
      (val (D.tau (hD.xe a) (hD.xe b)) κK (g₀ z) (fun ψ => J₁ (g₀ ≫ ψ))) :=
    Units.ext ((GlobalTheory.values_natural _ _ _ _ _ _ _ _ κK g₀ z J₁ hJ₁).2.2.1 _)
  have h0 : g₀ ≫ (TK V₁).hom ≫ spMap κ₁ = (TK V₂).hom ≫ spMap (f₂.comp κ₁) := by
    show g₀ ≫ jK V₁ ≫ spMap κ₁ = jK V₂ ≫ spMap (f₂.comp κ₁)
    rw [← Category.assoc, sg, Category.assoc, GlobalTheory.HalfBC.spMap_comp_spMap']
  have n₀ : val (T.τ₀ ((n : ℤ) • E a) ((n : ℤ) • E b)) ((TK V₂).hom ≫ spMap (f₂.comp κ₁)) z J =
      Units.map (g₀.stalkMap z).hom.toMonoidHom (val (T.τ₀ ((n : ℤ) • E a) ((n : ℤ) • E b))
        ((TK V₁).hom ≫ spMap κ₁) (g₀ z) (fun ψ => J (g₀ ≫ ψ))) := by
    rw [← h0]; exact Units.ext ((GlobalTheory.values_natural _ _ _ _ _ _ _ _ _ g₀ z J hJ).2.2.1 _)
  have nC : gm (𝟙 (TK V₂).left) z ⊤ (unitOn (Units.map fK.toMonoidHom (q (E a) (E b)))) =
      Units.map (g₀.stalkMap z).hom.toMonoidHom (gm (𝟙 (TK V₁).left) (g₀ z) ⊤ (unitOn (q (E a) (E b)))) :=
    gm_unitOn_map fK _ z
  have ni : isoVal w₁ (g₀ ≫ (lift (toUnit (TK V₁) ≫ x (E a)) (toUnit (TK V₁) ≫ x (E b))).left) z J J₁ =
      Units.map (g₀.stalkMap z).hom.toMonoidHom (isoVal w₁ (lift (toUnit (TK V₁) ≫ x (E a))
        (toUnit (TK V₁) ≫ x (E b))).left (g₀ z) (fun ψ => J (g₀ ≫ ψ)) (fun ψ => J₁ (g₀ ≫ ψ))) := by
    unfold isoVal
    simp only [Category.assoc]
    refine GlobalTheory.ConstFam.gm_comp_stalkMap g₀ _ z _ ?_ _
    exact ⟨mem_pull.2 (Set.mem_iInter.2 fun I => hJ _), mem_pull.2 (Set.mem_iInter.2 fun I => hJ₁ _)⟩
  have hr : 𝟙 _ ≫ jK V₂ ≫ spMap (f₂.comp f₁) = (g₀ ≫ κK) ≫ jK V := by
    rw [Category.id_comp, Category.assoc, hκK, ← Category.assoc, sg, Category.assoc, GlobalTheory.HalfBC.spMap_comp_spMap' f₁ f₂]
  have tv := GlobalTheory.ArcPull.tau_val hD (g₀ ≫ κK) (𝟙 _) hr hJ₁ hJ' a b
  have A : val (D.tau (hD.xe a) (hD.xe b)) (g₀ ≫ κK) z J₁ =
      gm (𝟙 (TK V₂).left) z ⊤ (unitOn (Units.map fK.toMonoidHom (q (E a) (E b)))) *
        (isoVal w₁ (g₀ ≫ (lift (toUnit (TK V₁) ≫ x (E a)) (toUnit (TK V₁) ≫ x (E b))).left) z J J₁ *
          val (T.τ₀ ((n : ℤ) • E a) ((n : ℤ) • E b)) ((TK V₂).hom ≫ spMap (f₂.comp κ₁)) z J) := by
    rw [n₁, t₂, nC, ni, n₀]
  have hx : ∀ χ, (toUnit (TK V₂) ≫ D'.c χ).left ≫ Φ = g₀ ≫ (toUnit (TK V₁) ≫ x (E χ)).left := fun χ => by
    show (jK V₂ ≫ (D'.c χ).left) ≫ Φ = spMap fK ≫ jK V₁ ≫ (x (E χ)).left
    rw [Category.assoc, hc, ← Category.assoc, ← sg, Category.assoc]
  have hPq : (lift (toUnit (TK V₂) ≫ D'.c a) (toUnit (TK V₂) ≫ D'.c b)).left ≫ GlobalTheory.HalfBC.sqOf gΦ =
      g₀ ≫ (lift (toUnit (TK V₁) ≫ x (E a)) (toUnit (TK V₁) ≫ x (E b))).left := by
    have sq1 : GlobalTheory.HalfBC.sqOf gΦ ≫ (fst B' B').left = (fst D'.P.A D'.P.A).left ≫ Φ :=
      congrArg (fun z => z.left) (lift_fst (pushPt gΦ.1.w (fst D'.P.A D'.P.A)) (pushPt gΦ.1.w (snd D'.P.A D'.P.A)))
    have sq2 : GlobalTheory.HalfBC.sqOf gΦ ≫ (snd B' B').left = (snd D'.P.A D'.P.A).left ≫ Φ :=
      congrArg (fun z => z.left) (lift_snd (pushPt gΦ.1.w (fst D'.P.A D'.P.A)) (pushPt gΦ.1.w (snd D'.P.A D'.P.A)))
    apply pullback.hom_ext
    · show _ ≫ (fst B' B').left = _ ≫ (fst B' B').left
      rw [Category.assoc, sq1, ← Category.assoc, ← Over.comp_left, lift_fst,
        Category.assoc, ← Over.comp_left, lift_fst]
      exact hx a
    · show _ ≫ (snd B' B').left = _ ≫ (snd B' B').left
      rw [Category.assoc, sq2, ← Category.assoc, ← Over.comp_left, lift_snd,
        Category.assoc, ← Over.comp_left, lift_snd]
      exact hx b
  let h : ((TK V₂).left ⟶ D'.P.A.left) → ((TK V₂).left.presheaf.stalk z)ˣ :=
    fun q => gw hD.w q z (J₁ (q ≫ GlobalTheory.PsiEvenPull.proj hD)) (J' q)
  have K := (hw _ (lift (toUnit (TK V₂) ≫ D'.c a) (toUnit (TK V₂) ≫ D'.c b)).left z J J₁ J' hJ hJ₁ hJ').trans
    (congrArg₂ (· * ·) (congrArg (fun q => isoVal w₁ q z J J₁) hPq)
      (prod_lam (DVR.cP D' (TK V₂) a) (DVR.cP D' (TK V₂) b) h))
  rw [← DVR.cPoint_add] at K
  have c₀ : ∀ χ, GlobalTheory.ArcPull.om hD.w z J₁ J' (𝟙 _ ≫ D'.xK χ) = h (DVR.cP D' (TK V₂) χ).left := fun χ => by
    rw [Category.id_comp]; rfl
  have c₁ : GlobalTheory.ArcPull.om hD.w z J₁ J' (𝟙 _ ≫ (1 : TK V₂ ⟶ D'.P.A).left) = h (1 : TK V₂ ⟶ D'.P.A).left := by
    rw [Category.id_comp]; rfl
  rw [c₀, c₀, c₀, c₁] at tv
  rw [K]
  have F := tv.symm.trans A
  generalize val (D'.tau a b) (𝟙 _) z J' = X at F ⊢
  generalize h (DVR.cP D' (TK V₂) (a + b)).left = Y₀ at F ⊢
  generalize h (DVR.cP D' (TK V₂) a).left = Y₁ at F ⊢
  generalize h (DVR.cP D' (TK V₂) b).left = Y₂ at F ⊢
  generalize h (1 : TK V₂ ⟶ D'.P.A).left = Y₃ at F ⊢
  have F' := congrArg Additive.ofMul F
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv] at F' ⊢
  linear_combination (norm := abel) F'

end GlobalTheory.PeriodPull
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodRelationPullbackMonomialConstantsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.PrimCocycle
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.period_relation_pullback_monomial_constants : ∀ (n : ℕ) (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (r : ℕ) (e₀ : (Fin r → ℤ) ≃+ D.X) {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) (V₁ : Type) [CommRing V₁] [IsDomain V₁] (f₁ : V →+* V₁) (κ₁ : W →+* V₁) (e : (Fin T.r → ℤ) ≃+ (Fin r → ℤ)) (B' : Over (Sp V₁)) [GrpObj B'] (β₂ : (G2 B').left ⟶ (G2 D.P.A).left) (β₂' : (G2 B').left ⟶ (G2 T.B).left) (x : (Fin T.r → ℤ) → (𝟙_ (Over (Sp V₁)) ⟶ B')) (w₁ : LB.Iso ((abelian₂ D.P.A D.P.L).pull β₂) ((abelian₂ T.B T.M.L).pull β₂')) (q : (Fin T.r → ℤ) → (Fin T.r → ℤ) → (FractionRing V₁)ˣ), Function.Injective f₁ → PeriodRel D T f₁ κ₁ w₁ (e.trans e₀) x n q → ∀ (V₂ : Type) [CommRing V₂] [IsDomain V₂] (f₂ : V₁ →+* V₂) (fK : FractionRing V₁ →+* FractionRing V₂) {I : Type} [Fintype I] (s : I → V₂) (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)), (∀ a, fK (algebraMap V₁ _ a) = algebraMap V₂ _ (f₂ a)) → (∀ a b, fK (q a b : FractionRing V₁) = ∏ k, algebraMap V₂ _ (s k) ^ ((n : ℤ) * ε k a b)) → ∀ (D' : DegPre V₂) (hD : IsPullDeg (f₂.comp f₁) D D') (Φ : D'.P.A.left ⟶ B'.left) (gΦ : IsGrpPullback D'.P.A B' (spMap f₂) Φ), (∀ a, (D'.c a).left ≫ Φ = spMap f₂ ≫ (x (hD.xe.trans (e₀.symm.trans e.symm) a)).left) → ∀ (w : LB.Iso (abelian₂ D'.P.A D'.P.L) ((abelian₂ T.B T.M.L).pull (GlobalTheory.HalfBC.sqOf gΦ ≫ β₂'))), (∀ (Z : Scheme.{0}) (p : Z ⟶ (G2 D'.P.A).left) (z : Z) (J : (Z ⟶ T.B.left) → T.M.L.ι) (J₁ : (Z ⟶ D.P.A.left) → D.P.L.ι) (J' : (Z ⟶ D'.P.A.left) → D'.P.L.ι), Good T.M.L z J → Good D.P.L z J₁ → Good D'.P.L z J' → lamVal w p z J J' = isoVal w₁ (p ≫ GlobalTheory.HalfBC.sqOf gΦ) z J J₁ * ∏ I, gw hD.w (p ≫ lamφ D'.P.A I) z (J₁ ((p ≫ lamφ D'.P.A I) ≫ GlobalTheory.PsiEvenPull.proj hD)) (J' (p ≫ lamφ D'.P.A I)) ^ lamε I) → ∀ a b : D'.X, ∃ k : (FractionRing V₂)ˣ, (k : FractionRing V₂) = ∏ i, algebraMap V₂ (FractionRing V₂) (s i) ^ ((n : ℤ) * ε i (hD.xe.trans (e₀.symm.trans e.symm) a) (hD.xe.trans (e₀.symm.trans e.symm) b)) ∧ ∀ z J J', Good T.M.L z J → Good D'.P.L z J' → val (D'.tau a b) (𝟙 _) z J' = gm (𝟙 (TK V₂).left) z ⊤ (unitOn k) * (lamVal w (lift (toUnit (TK V₂) ≫ D'.c a) (toUnit (TK V₂) ≫ D'.c b)).left z J J' * val (T.τ₀ ((n : ℤ) • hD.xe.trans (e₀.symm.trans e.symm) a) ((n : ℤ) • hD.xe.trans (e₀.symm.trans e.symm) b)) ((TK V₂).hom ≫ spMap (f₂.comp κ₁)) z J) := by
  first | exact @GlobalTheory.PeriodPull.periods_pull | exact GlobalTheory.PeriodPull.periods_pull | (intros; apply GlobalTheory.PeriodPull.periods_pull <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegDataFromLowerBaseAfterMonomialExtension

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.PrimCocycle
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PullFrom

theorem exists_cart_of_pullDeg : ∀ {V V₁ V₂ : Type} [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] [CommRing V₂] [IsDomain V₂] (D : DegPre V) (f₁ : V →+* V₁) (f₂ : V₁ →+* V₂) (B' : Over (Sp V₁)) [GrpObj B'] (β' : B'.left ⟶ D.P.A.left) (D' : DegPre V₂) (hD : IsPullDeg (f₂.comp f₁) D D'), IsGrpPullback B' D.P.A (spMap f₁) β' → ∃ Φ : D'.P.A.left ⟶ B'.left, IsGrpPullback D'.P.A B' (spMap f₂) Φ ∧ Φ ≫ β' = hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf (f₂.comp f₁)) ∧ ∀ (a : D'.X) (y : 𝟙_ (Over (Sp V₁)) ⟶ B'), y.left ≫ β' = spMap f₁ ≫ (D.c (hD.xe a)).left → (D'.c a).left ≫ Φ = spMap f₂ ≫ y.left := by
  intro V V₁ V₂ _ _ _ _ _ _ D f₁ f₂ B' _ β' D' hD gp'
  have gp := pull_grp hD
  have hsp : spMap f₂ ≫ spMap f₁ = spMap (f₂.comp f₁) := GlobalTheory.HalfBC.spMap_comp_spMap' f₁ f₂
  have w₀ : (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf (f₂.comp f₁))) ≫ D.P.A.hom =
      (D'.P.A.hom ≫ spMap f₂) ≫ spMap f₁ := by
    rw [gp.1.w, Category.assoc, hsp]
  refine ⟨gp'.1.lift _ _ w₀, ?_, gp'.1.lift_fst _ _ w₀, fun a y hy => ?_⟩
  · exact IsGrpPullback.cancel gp' (gp.congr hsp.symm (gp'.1.lift_fst _ _ w₀).symm) (gp'.1.lift_snd _ _ w₀)
  · apply gp'.1.hom_ext
    · rw [Category.assoc, gp'.1.lift_fst, Category.assoc, hy, ← Category.assoc (spMap f₂), hsp]
      exact hD.c_pr a
    · rw [Category.assoc, gp'.1.lift_snd, Category.assoc, Over.w y, ← Category.assoc, Over.w (D'.c a)]
      rfl

theorem degFrom_of_periodRel : ∀ (n : ℕ) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D : DegData V (maximalIdeal V)) (r : ℕ) (e₀ : (Fin r → ℤ) ≃+ D.toPre.X) (L : LowBase (zetaAway n) n) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (f₁ : V →+* V₁) (κ₁ : L.W →+* V₁) (e : (Fin L.T.r → ℤ) ≃+ (Fin r → ℤ)) (B' : Over (Sp V₁)) [GrpObj B'] (β' : B'.left ⟶ D.toPre.P.A.left) (β'' : B'.left ⟶ L.T.B.left) (β₂ : (G2 B').left ⟶ (G2 D.toPre.P.A).left) (β₂' : (G2 B').left ⟶ (G2 L.T.B).left), IsCN V → IsDiscreteValuationRing V → IsCN V₁ → IsDiscreteValuationRing V₁ → Function.Injective f₁ → f₁.Finite → IsLocalHom f₁ → IsLocalHom κ₁ → IsGrpPullback B' D.toPre.P.A (spMap f₁) β' → IsGrpPullback B' L.T.B (spMap κ₁) β'' → IsSquare β' β₂ → IsSquare β'' β₂' → ∀ (x : (Fin L.T.r → ℤ) → (𝟙_ (Over (Sp V₁)) ⟶ B')), (∀ a, (x a).left ≫ β' = spMap f₁ ≫ (D.toPre.c (e₀ (e a))).left ∧ (x a).left ≫ β'' = spMap κ₁ ≫ (L.T.c₀ ((n : ℤ) • a)).left) → ∀ (w₁ : LB.Iso ((abelian₂ D.toPre.P.A D.toPre.P.L).pull β₂) ((abelian₂ L.T.B L.T.M.L).pull β₂')) (q : (Fin L.T.r → ℤ) → (Fin L.T.r → ℤ) → (FractionRing V₁)ˣ), w₁.IsGen → PeriodRel D.toPre L.T f₁ κ₁ w₁ (e.trans e₀) x n q → ∀ (V₂ : Type) [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂] (f₂ : V₁ →+* V₂) (fK : FractionRing V₁ →+* FractionRing V₂) {I : Type} [Fintype I] (s : I → V₂) (ε : I → LinearMap.BilinForm ℤ (Fin L.T.r → ℤ)), IsCN V₂ → Function.Injective f₂ → f₂.Finite → IsLocalHom f₂ → (∀ a, fK (algebraMap V₁ _ a) = algebraMap V₂ _ (f₂ a)) → (∀ a b, fK (q a b : FractionRing V₁) = ∏ k, algebraMap V₂ _ (s k) ^ ((n : ℤ) * ε k a b)) → ∀ (D' : DegData V₂ (maximalIdeal V₂)) (hD : IsPullDeg (f₂.comp f₁) D.toPre D'.toPre), DegFrom L.T (f₂.comp κ₁) s ε n D'.toPre (hD.xe.trans (e₀.symm.trans e.symm)) := by
  intro n V _ _ _ D r e₀ L V₁ _ _ _ f₁ κ₁ e B' _ β' β'' β₂ β₂' hV hVd hV₁ hV₁d hf₁i hf₁f hf₁l hκ₁l gp' gp'' sq' sq'' x hx w₁ q hw₁ hPR V₂ _ _ _ f₂ fK I _ s ε hV₂ hf₂i hf₂f hf₂l hfK hq D' hD
  obtain ⟨Φ, gΦ, hΦ, hc₀⟩ := exists_cart_of_pullDeg D.toPre f₁ f₂ B' β' D'.toPre hD gp'
  have hc : ∀ a, (D'.toPre.c a).left ≫ Φ = spMap f₂ ≫ (x (hD.xe.trans (e₀.symm.trans e.symm) a)).left := fun a =>
    hc₀ a _ (by
      have := (hx (hD.xe.trans (e₀.symm.trans e.symm) a)).1
      simpa using this)
  have hΛD : (abelian₂ D.toPre.P.A D.toPre.P.L).IsLB := DVR.linComb_isLB _ D.toPre.P.isLB _ _
  obtain ⟨w, hw, hval⟩ := GlobalTheory.T.mumfordBundleIso_comp_group_pullback_iso D.toPre.P.A B' D'.toPre.P.A L.T.B (spMap f₁) (spMap f₂) β' Φ (GlobalTheory.PsiEvenPull.proj hD) β₂ β₂'
    D.toPre.P.L D'.toPre.P.L L.T.M.L gp' gΦ sq' hΦ D.toPre.P.isLB D'.toPre.P.isLB L.T.M.isLB hD.w w₁ hD.w_gen hw₁
  have hsp : spMap f₂ ≫ spMap κ₁ = spMap (f₂.comp κ₁) := GlobalTheory.HalfBC.spMap_comp_spMap' κ₁ f₂
  refine ⟨Wit.ofDeg D'.toPre D'.tau_bimult, AddEquiv.refl _, Wit.refines_ofDeg _ _, Φ ≫ β'', GlobalTheory.HalfBC.sqOf gΦ ≫ β₂', w,
    (IsGrpPullback.comp gΦ gp'').congr hsp rfl, ⟨?_, ?_⟩, hw, fun a => ?_, fun a b => ?_⟩
  · have e₁ : GlobalTheory.HalfBC.sqOf gΦ ≫ (fst B' B').left = (fst D'.toPre.P.A D'.toPre.P.A).left ≫ Φ :=
      congrArg (fun z => z.left) (lift_fst (pushPt gΦ.1.w (fst D'.toPre.P.A D'.toPre.P.A)) (pushPt gΦ.1.w (snd D'.toPre.P.A D'.toPre.P.A)))
    show (GlobalTheory.HalfBC.sqOf gΦ ≫ β₂') ≫ (fst L.T.B L.T.B).left = (fst D'.toPre.P.A D'.toPre.P.A).left ≫ Φ ≫ β''
    rw [Category.assoc, sq''.1, ← Category.assoc, e₁, Category.assoc]
  · have e₂ : GlobalTheory.HalfBC.sqOf gΦ ≫ (snd B' B').left = (snd D'.toPre.P.A D'.toPre.P.A).left ≫ Φ :=
      congrArg (fun z => z.left) (lift_snd (pushPt gΦ.1.w (fst D'.toPre.P.A D'.toPre.P.A)) (pushPt gΦ.1.w (snd D'.toPre.P.A D'.toPre.P.A)))
    show (GlobalTheory.HalfBC.sqOf gΦ ≫ β₂') ≫ (snd L.T.B L.T.B).left = (snd D'.toPre.P.A D'.toPre.P.A).left ≫ Φ ≫ β''
    rw [Category.assoc, sq''.2, ← Category.assoc, e₂, Category.assoc]
  · refine (congrArg (· ≫ β'') (hc a)).trans ?_
    rw [Category.assoc, (hx _).2, ← Category.assoc, hsp]
    rfl
  · obtain ⟨k, hk, hk'⟩ := GlobalTheory.T.period_relation_pullback_monomial_constants n V D.toPre r e₀ L.T V₁ f₁ κ₁ e B' β₂ β₂' x w₁ q hf₁i hPR V₂ f₂ fK s ε hfK hq D'.toPre hD Φ gΦ hc w hval a b
    refine ⟨k, hk, fun z J J' hJ hJ' => ?_⟩
    refine ((Wit.exists_tau D'.toPre a b).choose_spec.2 _ _ z J' hJ').trans ?_
    exact hk' z J J' hJ hJ'

end GlobalTheory.PullFrom
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegDataFromLowerBaseAfterMonomialExtensionStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.degData_from_lowerBase_after_monomial_extension : ∀ (n : ℕ) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D : DegData V (maximalIdeal V)) (r : ℕ) (e₀ : (Fin r → ℤ) ≃+ D.toPre.X) (L : LowBase (zetaAway n) n) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (f₁ : V →+* V₁) (κ₁ : L.W →+* V₁) (e : (Fin L.T.r → ℤ) ≃+ (Fin r → ℤ)) (B' : Over (Sp V₁)) [GrpObj B'] (β' : B'.left ⟶ D.toPre.P.A.left) (β'' : B'.left ⟶ L.T.B.left) (β₂ : (G2 B').left ⟶ (G2 D.toPre.P.A).left) (β₂' : (G2 B').left ⟶ (G2 L.T.B).left), IsCN V → IsDiscreteValuationRing V → IsCN V₁ → IsDiscreteValuationRing V₁ → Function.Injective f₁ → f₁.Finite → IsLocalHom f₁ → IsLocalHom κ₁ → IsGrpPullback B' D.toPre.P.A (spMap f₁) β' → IsGrpPullback B' L.T.B (spMap κ₁) β'' → IsSquare β' β₂ → IsSquare β'' β₂' → ∀ (x : (Fin L.T.r → ℤ) → (𝟙_ (Over (Sp V₁)) ⟶ B')), (∀ a, (x a).left ≫ β' = spMap f₁ ≫ (D.toPre.c (e₀ (e a))).left ∧ (x a).left ≫ β'' = spMap κ₁ ≫ (L.T.c₀ ((n : ℤ) • a)).left) → ∀ (w₁ : LB.Iso ((abelian₂ D.toPre.P.A D.toPre.P.L).pull β₂) ((abelian₂ L.T.B L.T.M.L).pull β₂')) (q : (Fin L.T.r → ℤ) → (Fin L.T.r → ℤ) → (FractionRing V₁)ˣ), w₁.IsGen → PeriodRel D.toPre L.T f₁ κ₁ w₁ (e.trans e₀) x n q → ∀ (V₂ : Type) [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂] (f₂ : V₁ →+* V₂) (fK : FractionRing V₁ →+* FractionRing V₂) {I : Type} [Fintype I] (s : I → V₂) (ε : I → LinearMap.BilinForm ℤ (Fin L.T.r → ℤ)), IsCN V₂ → Function.Injective f₂ → f₂.Finite → IsLocalHom f₂ → (∀ a, fK (algebraMap V₁ _ a) = algebraMap V₂ _ (f₂ a)) → (∀ a b, fK (q a b : FractionRing V₁) = ∏ k, algebraMap V₂ _ (s k) ^ ((n : ℤ) * ε k a b)) → ∀ (D' : DegData V₂ (maximalIdeal V₂)) (hD : IsPullDeg (f₂.comp f₁) D.toPre D'.toPre), DegFrom L.T (f₂.comp κ₁) s ε n D'.toPre (hD.xe.trans (e₀.symm.trans e.symm)) := by
  first | exact @GlobalTheory.PullFrom.degFrom_of_periodRel | exact GlobalTheory.PullFrom.degFrom_of_periodRel | (intros; apply GlobalTheory.PullFrom.degFrom_of_periodRel <;> assumption)
end
end
