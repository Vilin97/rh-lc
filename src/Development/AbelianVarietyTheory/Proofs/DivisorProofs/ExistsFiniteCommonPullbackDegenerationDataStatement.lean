module

public import Mathlib.RingTheory.SimpleRing.Principal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifBaseChangeSt
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValEqOfAppInjective
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsPullDegOfVal
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullDegCancelTowerOfFields
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsomorphismMonHomDescendsFiniteExtensionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyIsPullDegCompOfInjective
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InvariantFunctionsDescend
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolarisedAVIsoDescendsOfRationalThreeTorsion
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsRigidifiedIso
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsoUniqueOfRig
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyPullDegIdOfCommonFieldExtension

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.ArcPull GlobalTheory.ArcQ

namespace GlobalTheory.FieldDescent

open GlobalTheory.PsiEvenPull (proj)
open GlobalTheory.GenSpread

variable {K Ω : Type} [Field K] [Field Ω] {l : K →+* Ω} {D₁ D₂ : DegPre K} {D : DegPre Ω}

theorem lbIso_of_common_pull (h₁ : IsPullDeg l D₁ D) (h₂ : IsPullDeg l D₂ D) {Φ : D₂.P.A.left ⟶ D₁.P.A.left}
    (hΦ : proj h₂ ≫ Φ = proj h₁) : LBIso D₂.P.L (D₁.P.L.pull Φ) := by
  have e : pullback.fst D₂.P.A.hom (specOf l) = h₂.e.inv.left ≫ proj h₂ := by
    rw [← Category.assoc, ← Over.comp_left, Iso.inv_hom_id, Over.id_left]
    exact (Category.id_comp _).symm
  have e' : pullback.fst D₂.P.A.hom (specOf l) ≫ Φ = h₂.e.inv.left ≫ proj h₁ :=
    (congrArg (· ≫ Φ) e).trans ((Category.assoc _ _ _).trans (congrArg (h₂.e.inv.left ≫ ·) hΦ))
  exact PolIsoDescent.lbIso_descend globalFns_holds (specOf l) D₂.P.A D₂.P.isAb D₂.P.isLB (pull_isLB D₁.P.isLB Φ)
    (LBIso.trans (pull_isLB D₂.P.isLB _) (pull_isLB D.P.isLB _) (pull_isLB (pull_isLB D₁.P.isLB _) _)
      (lbIso_pull_of_lbIso ⟨h₂.w, h₂.w_gen⟩ h₂.e.inv.left e).symm
      (LBIso.trans (pull_isLB D.P.isLB _) (pull_isLB D₁.P.isLB _) (pull_isLB (pull_isLB D₁.P.isLB _) _)
        (lbIso_pull_of_lbIso ⟨h₁.w, h₁.w_gen⟩ h₂.e.inv.left e') (lbIso_pull_pull D₁.P.isLB _ rfl)))

theorem om_eq (h₁ : IsPullDeg l D₁ D) {ψ : D.P.A.left ⟶ D₁.P.A.left} (v : LB.Iso D.P.L (D₁.P.L.pull ψ))
    (hψ : ψ = proj h₁) (gv : PGen v)
    (pv : PMaps v (K := PUnit) (fun _ => eSec D.P.A) (fun _ => eSec D₁.P.A) (fun _ => 1) D.rig D₁.rig (spMap l))
    {Z : Scheme.{0}} (z : Z) (J J') (q : Z ⟶ D.P.A.left) : om v z J J' q = om h₁.w z J J' q := by
  subst hψ
  rw [iso_unique_of_rig globalFns_holds D.P.A D.P.isAb D.P.isLB D₁.P.isLB ((isGen_iff v).2 gv) h₁.w_gen
    ((maps_iff v _ (fun _ => eSec D₁.P.A) _ D.rig D₁.rig (specOf l) _
      (rigPull_le (proj h₁) (specOf l) h₁.he D₁.P.L) (fun _ => rfl)).2 pv) h₁.w_rig]

end GlobalTheory.FieldDescent


open GlobalTheory.PsiEvenPull (proj) in
theorem GlobalTheory.nonempty_isPullDeg_id_of_common_pull : ∀ (K Ω : Type) [Field K] [Field Ω] (l : K →+* Ω) (D₁ D₂ : DegPre K) (D : DegPre Ω) (h₁ : IsPullDeg l D₁ D) (h₂ : IsPullDeg l D₂ D) (φ : D₂.P.A ≅ D₁.P.A), IsMonHom φ.hom → h₂.e.hom.left ≫ pullback.fst D₂.P.A.hom (specOf l) ≫ φ.hom.left = h₁.e.hom.left ≫ pullback.fst D₁.P.A.hom (specOf l) → Nonempty (IsPullDeg (RingHom.id K) D₁ D₂) := by
  intro K Ω _ _ l D₁ D₂ D h₁ h₂ φ hm hφ
  have hΦ : proj h₂ ≫ φ.hom.left = proj h₁ := (Category.assoc _ _ _).trans hφ
  have hs : spMap (RingHom.id K) = 𝟙 (Sp K) := Spec.map_id (CommRingCat.of K)
  have gp : IsGrpPullback D₂.P.A D₁.P.A (spMap (RingHom.id K)) φ.hom.left :=
    (Geo.Tor.isGrpPullback_of_iso φ).congr hs.symm rfl
  have he : eSec D₂.P.A ≫ φ.hom.left = spMap (RingHom.id K) ≫ eSec D₁.P.A := (cubeMapOf gp).e_comm
  obtain ⟨w, gw', rw'⟩ := Unif.RigidifyIso.exists_rigidified_iso _ _ (spMap (RingHom.id K)) D₁.P.A D₂.P.A φ.hom.left he
    ⟨D₁.P.L, D₁.rig, D₁.P.isLB, D₁.rig_gen⟩ ⟨D₂.P.L, D₂.rig, D₂.P.isLB, D₂.rig_gen⟩
    (FieldDescent.lbIso_of_common_pull h₁ h₂ hΦ)
  have pw' := (isGen_iff w).1 gw'
  have p₂ := (isGen_iff h₂.w).1 h₂.w_gen
  have r₀ := (maps_iff w _ (fun _ => eSec D₁.P.A) _ D₂.rig D₁.rig (spMap (RingHom.id K)) _
    (rigPull_le φ.hom.left (spMap (RingHom.id K)) he D₁.P.L) (fun _ => rfl)).1 rw'
  obtain ⟨v, T⟩ := exists_comp D₂.P.isLB w h₂.w pw' p₂ D₁.P.isLB D.P.isLB
  have r₂ := T.pmaps_comp D₂.P.isLB (fun _ => h₂.he) r₀ (FieldPull.pmaps_rig h₂)
  rw [← spMap_comp] at r₂
  have hom := fun {Z : Scheme.{0}} (z : Z) J J' q =>
    FieldDescent.om_eq h₁ v hΦ (T.pgen_comp D₂.P.isLB pw' p₂) r₂ z J J' q
  obtain ⟨f₁, f₂⟩ := PolIsoDescent.flat_surjective (spMap l)
  have : Epi (spMap l) := Flat.epi_of_flat_of_surjective _
  let xe : D₂.X ≃+ D₁.X := h₂.xe.symm.trans h₁.xe
  have hxe : ∀ y, xe (h₂.xe y) = h₁.xe y := fun y => congrArg h₁.xe (h₂.xe.symm_apply_apply y)
  have hc : ∀ x, (D₂.c x).left ≫ φ.hom.left = spMap (RingHom.id K) ≫ (D₁.c (xe x)).left := fun x => by
    obtain ⟨y, rfl⟩ := h₂.xe.surjective x
    rw [hxe, hs]
    refine Eq.trans ?_ (Category.id_comp _).symm
    refine (cancel_epi (spMap l)).1 ((Category.assoc _ _ _).symm.trans ?_)
    exact (congrArg (· ≫ φ.hom.left) (h₂.c_pr y).symm).trans ((Category.assoc _ _ _).trans
      ((congrArg ((D.c y).left ≫ ·) hΦ).trans (h₁.c_pr y)))
  have si : jK K ≫ spMap (RingHom.id K) = genMap (RingHom.id K).injective ≫ jK K :=
    (Category.id_comp _).symm.trans (fracMap_sq (RingHom.id K).injective)
  have si' : genMap (RingHom.id K).injective ≫ jK K = jK K :=
    si.symm.trans ((congrArg (jK K ≫ ·) hs).trans (Category.comp_id _))
  have sl := fracMap_sq l.injective
  obtain ⟨hD, -⟩ := FieldPull.exists_isPullDeg_of_val (RingHom.id K) D₁ D₂ gp w pw' r₀ xe hc
    (fun x z J₁ J₂ hJ₁ hJ₂ => by
      obtain ⟨y, rfl⟩ := h₂.xe.surjective x
      have hx : D₂.xK (h₂.xe y) ≫ φ.hom.left = genMap (RingHom.id K).injective ≫ D₁.xK (xe (h₂.xe y)) := by
        show (jK K ≫ (D₂.c _).left) ≫ _ = _ ≫ jK K ≫ (D₁.c _).left
        rw [Category.assoc, hc, ← Category.assoc, si, Category.assoc]
      obtain ⟨a, ha, va⟩ := exists_down_om gw' D₁.P.isLB D₂.P.isLB (K := PUnit) (φ' := fun _ => D₂.xK (h₂.xe y))
        (genMap (RingHom.id K).injective) (fun _ => hx) (D₁.psi (xe (h₂.xe y))) (D₁.psi_gen _)
      obtain ⟨k₁, k₂⟩ := PolIsoDescent.flat_surjective (F := FractionRing Ω) (C := FractionRing K) (genMap l.injective)
      have ea := PsiEvenPull.val_eq_of_app_injective D₂.P.isLB (fun _ _ _ => rfl) (genMap l.injective)
        (fun U => FunDescent.app_injective (genMap l.injective) U) ha (D₂.psi_gen (h₂.xe y)) (fun u I₂ hI₂ => by
          obtain ⟨I₁, hI₁⟩ := DegPull.exists_good' D₁.P.isLB u
          obtain ⟨I, hI⟩ := DegPull.exists_good' D.P.isLB u
          have v₂ := psi_val h₂ _ _ sl hI₂ hI y
          have v₁ := psi_val h₁ (genMap l.injective ≫ genMap (RingHom.id K).injective) _
            (sl.trans ((congrArg (_ ≫ ·) si'.symm).trans (Category.assoc _ _ _).symm)) hI₁ hI y
          have v₀ := va _ (genMap l.injective) u I₁ I₂ hI₁ hI₂
          have hq : genMap l.injective ≫ D₂.xK (h₂.xe y) = (𝟙 _ ≫ D.xK y) ≫ proj h₂ := by
            show _ ≫ jK K ≫ (D₂.c _).left = (𝟙 _ ≫ jK Ω ≫ (D.c y).left) ≫ _
            rw [← Category.assoc, ← sl]
            simp only [Category.assoc]
            exact congrArg (fun q => 𝟙 _ ≫ jK Ω ≫ q) (h₂.c_pr y).symm
          have t : om v u I₁ I (𝟙 _ ≫ D.xK y) =
              om w u I₁ I₂ ((𝟙 _ ≫ D.xK y) ≫ proj h₂) * om h₂.w u I₂ I (𝟙 _ ≫ D.xK y) := by
            rw [om, om, om, Category.assoc (𝟙 _ ≫ D.xK y)]
            exact T _ _ u _ _ _ (hI₁ ((𝟙 _ ≫ D.xK y) ≫ proj h₂ ≫ φ.hom.left)) (hI₂ ((𝟙 _ ≫ D.xK y) ≫ proj h₂)) (hI _)
          rw [Fintype.prod_unique, zpow_neg_one, hq, hxe, v₁, ← hom, t, mul_inv, _root_.mul_assoc] at v₀
          exact (mul_left_cancel v₀).symm.trans v₂.symm) _ (𝟙 _) z J₂ hJ₂
      have v₀ := va _ (𝟙 _) z J₁ J₂ hJ₁ hJ₂
      rw [Fintype.prod_unique, zpow_neg_one, Category.id_comp, Category.id_comp, ea] at v₀
      exact v₀)
  exact ⟨hD⟩
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyPullDegIdOfCommonFieldExtensionStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.ArcPull GlobalTheory.ArcQ

theorem _root_.GlobalTheory.T.nonempty_pullDeg_id_of_common_fieldExtension : ∀ (K Ω : Type) [Field K] [Field Ω] (l : K →+* Ω) (D₁ D₂ : DegPre K) (D : DegPre Ω) (h₁ : IsPullDeg l D₁ D) (h₂ : IsPullDeg l D₂ D) (φ : D₂.P.A ≅ D₁.P.A), IsMonHom φ.hom → h₂.e.hom.left ≫ pullback.fst D₂.P.A.hom (specOf l) ≫ φ.hom.left = h₁.e.hom.left ≫ pullback.fst D₁.P.A.hom (specOf l) → Nonempty (IsPullDeg (RingHom.id K) D₁ D₂) := by
  first | exact @GlobalTheory.nonempty_isPullDeg_id_of_common_pull | exact GlobalTheory.nonempty_isPullDeg_id_of_common_pull | (intros; apply GlobalTheory.nonempty_isPullDeg_id_of_common_pull <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteCommonPullbackDegenerationData

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.FieldDesc
open GlobalTheory.ArcPull GlobalTheory.ArcQ
open GlobalTheory.PsiEvenPull (proj)

theorem exists_comp_proj {R R' R'' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']
    [CommRing R''] [IsDomain R''] {i : R →+* R'} {j : R' →+* R''} (hj : Function.Injective j)
    {D : DegPre R} {D' : DegPre R'} {D'' : DegPre R''} (p : IsPullDeg i D D') (q : IsPullDeg j D' D'') :
    ∃ r : IsPullDeg (j.comp i) D D'', proj r = proj q ≫ proj p := by
  have sc : spMap j ≫ spMap i = spMap (j.comp i) := (spMap_comp i j).symm
  have gp : IsGrpPullback D''.P.A D.P.A (spMap (j.comp i)) (proj q ≫ proj p) :=
    ((pull_grp q).comp (pull_grp p)).congr sc rfl
  have g₁ := (isGen_iff _).1 p.w_gen
  have g₂ := (isGen_iff _).1 q.w_gen
  obtain ⟨w, T⟩ := Geo.Tor.exists_comp D'.P.isLB p.w q.w g₁ g₂ D.P.isLB D''.P.isLB
  have hr := T.pmaps_comp D'.P.isLB (fun _ => q.he) (FieldPull.pmaps_rig p) (FieldPull.pmaps_rig q)
  rw [sc] at hr
  have hc : ∀ x, (D''.c x).left ≫ proj q ≫ proj p = spMap (j.comp i) ≫ (D.c ((q.xe.trans p.xe) x)).left := fun x =>
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ proj p) (q.c_pr x)).trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (p.c_pr _)).trans ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) sc)))))
  have sj : jK R'' ≫ spMap j = genMap hj ≫ jK R' := (Category.id_comp _).symm.trans (fracMap_sq hj)
  have hg : (genMap hj ≫ p.g) ≫ p.W.ι = jK R'' ≫ specOf (j.comp i) := by
    rw [Category.assoc, p.g_comm, ← Category.assoc, ← sj, Category.assoc]
    exact congrArg (jK R'' ≫ ·) sc
  exact GlobalTheory.PullDegCompGen.exists_isPullDeg_of_valW D D'' p.psiW (genMap hj ≫ p.g) hg gp w
    (T.pgen_comp D'.P.isLB g₁ g₂) hr (q.xe.trans p.xe) hc (fun x z J J'' hJ hJ'' => by
      obtain ⟨J', hJ'⟩ := DegPull.exists_good' D'.P.isLB z
      have v₁ := PsiEvenPull.psi_pull p (q.xe x) (genMap hj) z hJ hJ'
      have v₂ := psi_val q _ _ (fracMap_sq hj) hJ' hJ'' x
      have hx : D''.xK x ≫ proj q = genMap hj ≫ D'.xK (q.xe x) := by
        show (jK R'' ≫ (D''.c x).left) ≫ proj q = genMap hj ≫ jK R' ≫ (D'.c (q.xe x)).left
        rw [Category.assoc, q.c_pr, ← Category.assoc, ← Category.assoc, ← sj]
      have t : om w z J J'' (D''.xK x) = om p.w z J J' (D''.xK x ≫ proj q) * om q.w z J' J'' (D''.xK x) :=
        (congrArg (fun u => Geo.Tor.gw w (D''.xK x) z (J u) (J'' (D''.xK x)))
          (Category.assoc (D''.xK x) (proj q) (proj p)).symm).trans
          (T _ _ z _ _ _ (hJ ((D''.xK x ≫ proj q) ≫ proj p)) (hJ' (D''.xK x ≫ proj q)) (hJ'' _))
      change _ = (om p.w z J J' (genMap hj ≫ D'.xK (q.xe x)))⁻¹ * val (D'.psi (q.xe x)) (genMap hj) z J' at v₁
      rw [v₂, Category.id_comp, ← hx, ← _root_.mul_assoc, ← mul_inv, ← t] at v₁
      exact v₁)

theorem exists_finite_common_pull : ∀ (K L : Type) [Field K] [CharZero K] [Field L] (β : K →+* L) (E₁ E₂ : DegPre K) (E' : DegPre L), IsPullDeg β E₁ E' → IsPullDeg β E₂ E' → ∃ (K' : Type) (_ : Field K') (io : K →+* K') (E₃ : DegPre K'), io.Finite ∧ Nonempty (IsPullDeg io E₁ E₃) ∧ Nonempty (IsPullDeg io E₂ E₃) := by
  intro K L _ _ _ β E₁ E₂ E' h₁ h₂
  haveI := h₁.e_hom
  haveI := h₂.e_hom
  obtain ⟨K', _, io, Ω, _, j, l, φ, hfin, hl, hφ, hcomp⟩ :=
    GlobalTheory.T.isomorphism_mon_hom_descends_finite_extension K L β E₁.P.A E₂.P.A E₁.P.isAb E₂.P.isAb (h₁.e.symm ≪≫ h₂.e) (by dsimp; infer_instance)
  have hP := GlobalTheory.polBaseChange_holds
  obtain ⟨E₃, h₃, -, -⟩ := GlobalTheory.DegPull.exists_isPullDeg hP K K' io E₁ ⊤ (FieldPull.nonempty_psiOn_field E₁) trivial
  obtain ⟨E₄, h₄, -, -⟩ := GlobalTheory.DegPull.exists_isPullDeg hP K K' io E₂ ⊤ (FieldPull.nonempty_psiOn_field E₂) trivial
  obtain ⟨E'', h', -, -⟩ := GlobalTheory.DegPull.exists_isPullDeg hP L Ω j E' ⊤ (FieldPull.nonempty_psiOn_field E') trivial
  obtain ⟨c₁, pc₁⟩ : ∃ c : IsPullDeg (l.comp io) E₁ E'', proj c = proj h' ≫ proj h₁ := by
    rw [hl]; exact exists_comp_proj j.injective h₁ h'
  obtain ⟨c₂, pc₂⟩ : ∃ c : IsPullDeg (l.comp io) E₂ E'', proj c = proj h' ≫ proj h₂ := by
    rw [hl]; exact exists_comp_proj j.injective h₂ h'
  obtain ⟨g₃, pg₃⟩ := FieldPull.exists_isPullDeg_cancel K K' Ω io l E₁ E₃ E'' h₃ c₁
  obtain ⟨g₄, pg₄⟩ := FieldPull.exists_isPullDeg_cancel K K' Ω io l E₂ E₄ E'' h₄ c₂
  have w₁ : proj h' ≫ E'.P.A.hom = E''.P.A.hom ≫ spMap j := (pull_grp h').1.w
  have w₃ : proj g₃ ≫ E₃.P.A.hom = E''.P.A.hom ≫ spMap l := (pull_grp g₃).1.w
  have w₄ : proj g₄ ≫ E₄.P.A.hom = E''.P.A.hom ≫ spMap l := (pull_grp g₄).1.w
  have key : proj g₃ ≫ h₃.e.hom.left ≫ φ.hom.left = proj g₄ ≫ h₄.e.hom.left := by
    apply pullback.hom_ext
    · have := hcomp E''.P.A.left (proj h' ≫ h₁.e.hom.left) (proj g₃ ≫ h₃.e.hom.left) E''.P.A.hom
        (by simp only [Category.assoc]; exact (pc₁.symm.trans pg₃.symm))
        (by rw [Category.assoc]; exact (congrArg (proj h' ≫ ·) (Over.w h₁.e.hom)).trans w₁)
        (by rw [Category.assoc]; exact (congrArg (proj g₃ ≫ ·) (Over.w h₃.e.hom)).trans w₃)
      simp only [Category.assoc] at this ⊢
      rw [← this]
      have e₁ : h₁.e.hom.left ≫ (h₁.e.symm ≪≫ h₂.e).hom.left = h₂.e.hom.left := by
        rw [Iso.trans_hom, Iso.symm_hom, Over.comp_left, ← Category.assoc, ← Over.comp_left, Iso.hom_inv_id,
          Over.id_left, Category.id_comp]
      rw [reassoc_of% e₁]
      exact (pg₄.trans pc₂).symm
    · simp only [Category.assoc]
      have a := Over.w φ.hom
      have b := Over.w h₃.e.hom
      have c := Over.w h₄.e.hom
      erw [a, b, w₃, c, w₄]
  let Ψ : E₃.P.A ≅ E₄.P.A := h₃.e ≪≫ φ ≪≫ h₄.e.symm
  haveI := h₃.e_hom
  haveI := h₄.e_hom
  haveI := hφ
  have hΨ : IsMonHom Ψ.hom := by dsimp [Ψ]; infer_instance
  have cΨ : g₃.e.hom.left ≫ pullback.fst E₃.P.A.hom (specOf l) ≫ Ψ.hom.left =
      g₄.e.hom.left ≫ pullback.fst E₄.P.A.hom (specOf l) := by
    have k2 : (proj g₃ ≫ h₃.e.hom.left ≫ φ.hom.left) ≫ h₄.e.inv.left = proj g₄ := by
      rw [key, Category.assoc, ← Over.comp_left, Iso.hom_inv_id, Over.id_left, Category.comp_id]
    refine Eq.trans ?_ k2
    simp only [Ψ, Iso.trans_hom, Iso.symm_hom, Over.comp_left, Category.assoc]
  obtain ⟨q⟩ := GlobalTheory.T.nonempty_pullDeg_id_of_common_fieldExtension K' Ω l E₄ E₃ E'' g₄ g₃ Ψ hΨ cΨ
  have hh := nonempty_isPullDeg_comp_of_injective K K' K' io (RingHom.id K') E₂ E₄ E₃ (fun _ _ h => h) ⟨h₄⟩ ⟨q⟩
  rw [RingHom.id_comp] at hh
  exact ⟨K', inferInstance, io, E₃, hfin, ⟨h₃⟩, hh⟩

end GlobalTheory.FieldDesc
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteCommonPullbackDegenerationDataStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_finite_common_pullback_degenerationData : ∀ (K L : Type) [Field K] [CharZero K] [Field L] (β : K →+* L) (E₁ E₂ : DegPre K) (E' : DegPre L), IsPullDeg β E₁ E' → IsPullDeg β E₂ E' → ∃ (K' : Type) (_ : Field K') (io : K →+* K') (E₃ : DegPre K'), io.Finite ∧ Nonempty (IsPullDeg io E₁ E₃) ∧ Nonempty (IsPullDeg io E₂ E₃) := by
  first | exact @GlobalTheory.FieldDesc.exists_finite_common_pull | exact GlobalTheory.FieldDesc.exists_finite_common_pull | (intros; apply GlobalTheory.FieldDesc.exists_finite_common_pull <;> assumption)
end
end
