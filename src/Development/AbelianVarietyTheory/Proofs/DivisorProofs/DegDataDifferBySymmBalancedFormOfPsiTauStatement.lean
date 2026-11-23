module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EvenDefect
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRatioDescendsDegenerationPsiFamily
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LiftThreeOverMapComp
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifBaseChangeSt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChartA
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TauBalOfIsPullDeg
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TauBimultOfIsPullDeg
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TraceFormTwistIsoOfPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RescaledDegenerationDataDifferByScalarStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRescaleIsPullDegGeneratingEverywhere

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PreLiftData

open GlobalTheory.ArcPull GlobalTheory.ArcQ

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

theorem exists_rescale_isPullDeg_data {i : R →+* R'} (D : DegPre R) (D' : DegPre R')
    {W : (Sp R).Opens} (ψW : PsiOn D W) (g : (TK R').left ⟶ (TW W).left) (hg : g ≫ W.ι = jK R' ≫ specOf i)
    {Φ : D'.P.A.left ⟶ D.P.A.left} (gp : IsGrpPullback D'.P.A D.P.A (spMap i) Φ)
    (w : LB.Iso D'.P.L (D.P.L.pull Φ)) (hw : PGen w)
    (hr : PMaps w (K := PUnit) (fun _ => eSec D'.P.A) (fun _ => eSec D.P.A) (fun _ => 1) D'.rig D.rig (spMap i))
    (xe : D'.X ≃+ D.X) (hc : ∀ x, (D'.c x).left ≫ Φ = spMap i ≫ (D.c (xe x)).left) :
    ∃ (κ : D'.X → (FractionRing R')ˣ) (hD : IsPullDeg i D (GlobalTheory.PolDeg.rescale D' κ)),
      (∀ y, hD.xe y = xe y) ∧ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) = Φ ∧ hD.W = W := by
  obtain ⟨e, e_hom, he⟩ := grpPullback_iso gp (isGrpPullback_pullback D.P.A (specOf i))
  subst he
  have hE : eSec D'.P.A ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) = specOf i ≫ eSec D.P.A :=
    (cubeMapOf gp).e_comm
  have hx : ∀ x, g ≫ (toUnit (TW W) ≫ D.c (xe x)).left =
      D'.xK x ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) := fun x => by
    show g ≫ W.ι ≫ (D.c (xe x)).left = (jK R' ≫ (D'.c x).left) ≫ _
    rw [Category.assoc, hc, ← Category.assoc, hg, Category.assoc]
  choose b hb vb using fun x => exists_gen D.P.isLB (K' := PUnit)
    (φ' := fun _ => D'.xK x ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf i)) (ε' := fun _ => -1)
    (fun U _ h => Finset.prod_congr rfl fun _ _ => congrArg (fun q => h q ^ (-1 : ℤ)) (hx x))
    (LB.pullGen D.P.L _ _ (ψW.psi (xe x)) g) (DVR.pullGen_isGen _ _ _ _ (ψW.psi_gen _) g)
  choose psi hpsi vpsi using fun x => DegPull.exists_down_val hw D.P.isLB D'.P.isLB (K := PUnit)
    (φ' := fun _ => D'.xK x) (ε := fun _ => -1) (fun _ => rfl) (b x) (hb x)
  choose u hu using GlobalTheory.FieldPull.exists_psi_ratio D' psi hpsi
  refine ⟨fun x => (u x)⁻¹, ?_⟩
  have eψ : ∀ x, psi x = (GlobalTheory.PolDeg.rescale D' fun x => (u x)⁻¹).psi x := fun x =>
    GlobalTheory.TorusExt.gen_ext_val D'.P.isLB (hpsi x) ((GlobalTheory.PolDeg.rescale D' fun x => (u x)⁻¹).psi_gen x)
      fun y J' hJ' => by
        refine Eq.trans ?_ (GlobalTheory.UU.val_scaleGen _ _ _ hJ').symm
        have h1 : unitOn (u x)⁻¹ * unitOn (u x) = 1 := (map_mul _ _ _).symm.trans
          ((congrArg unitOn (inv_mul_cancel (u x))).trans (map_one _))
        rw [hu x y J' hJ', GlobalTheory.TauTwist.unitAt_apply, ← _root_.mul_assoc, ← map_mul]
        erw [h1]
        rw [map_one, _root_.one_mul]
  have key : ∀ x, GeneratorPullback.MapsAt D.P.L D'.P.L (J := PUnit)
      (fun _ => e.hom.left ≫ pullback.fst D.P.A.hom (specOf i)) w (D'.xK x) (-1) (psi x) (b x) := fun x jN jL => by
    refine unit_ext fun y hy => ?_
    have v := vpsi x _ (𝟙 _) y jN (fun _ => jL) (GeneratorPullback.mapsAt_le_b _ _ _ _ jN jL hy) (GeneratorPullback.mapsAt_le_a _ _ _ _ jN jL hy)
    refine (gm_res _ y _ hy _).trans (v.trans (Eq.symm ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_
      (gm_res _ y _ hy _)))))
    rw [pw, Fintype.prod_unique]
    exact (map_zpow _ _ _).trans (congrArg (· ^ (-1 : ℤ)) (gm_pull (𝟙 _) _ y _ hy _))
  refine ⟨⟨e, e_hom, w, (isGen_iff w).2 hw, hE, ?_, xe, hc, W, ψW, g, hg, fun x => ⟨b x, eψ x ▸ key x,
      corr_of_val D.P.isLB fun y J hJ => vb x _ _ y J hJ⟩⟩, fun _ => rfl, rfl, rfl⟩
  exact (maps_iff w _ (fun _ => eSec D.P.A) _ D'.rig D.rig (specOf i) _
    (rigPull_le (G' := D'.P.A) (G := D.P.A) _ (specOf i) hE D.P.L) (fun _ => rfl)).2 hr

theorem exists_rescale_isPullDeg_top : ∀ {W V : Type} [CommRing W] [IsDomain W] [CommRing V] [IsDomain V] (θ₀ : W →+* V) (D₀ : DegPre W) (Q : DegPre V) (e : Q.X ≃+ D₀.X) (β : Q.P.A.left ⟶ D₀.P.A.left), (∀ y, PsiUnitOn D₀ y Set.univ) → IsGrpPullback Q.P.A D₀.P.A (spMap θ₀) β → LBIso Q.P.L (D₀.P.L.pull β) → (∀ y, (Q.c y).left ≫ β = spMap θ₀ ≫ (D₀.c (e y)).left) → ∃ (g : Q.X → (FractionRing V)ˣ) (hD : IsPullDeg θ₀ D₀ (GlobalTheory.PolDeg.rescale Q g)), (∀ y, hD.xe y = e y) ∧ hD.e.hom.left ≫ pullback.fst D₀.P.A.hom (specOf θ₀) = β ∧ hD.W = ⊤ := by
  intro _ _ _ _ _ _ θ₀ D₀ Q e β hU gp hL hc
  obtain ⟨ψW⟩ := GlobalTheory.ArcPull.nonempty_psiOn_top D₀ hU
  let gg : (TK _).left ⟶ (TW (⊤ : (Sp _).Opens)).left := (jK _ ≫ specOf θ₀) ≫ (Sp _).topIso.inv
  have hg : gg ≫ (⊤ : (Sp _).Opens).ι = jK _ ≫ specOf θ₀ := by
    rw [Category.assoc, ← Scheme.topIso_hom, Iso.inv_hom_id, Category.comp_id]
  obtain ⟨w₀, hw₀⟩ := hL
  have he : eSec Q.P.A ≫ β = spMap θ₀ ≫ eSec D₀.P.A := (cubeMapOf gp).e_comm
  have hσ : eSec Q.P.A ≫ Q.P.A.hom = 𝟙 _ := Over.w η[Q.P.A]
  obtain ⟨w, hw, hr⟩ := GlobalTheory.UnifPreCompare.exists_rigidified D₀.P.isLB Q.P.isLB Q.P.A.hom (eSec Q.P.A) hσ w₀ hw₀
    Q.rig Q.rig_gen (φ := eSec D₀.P.A) D₀.rig D₀.rig_gen (spMap θ₀) he
  exact exists_rescale_isPullDeg_data (i := θ₀) D₀ Q ψW gg hg gp w ((isGen_iff w).1 hw) hr e hc

end GlobalTheory.PreLiftData
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRescaleIsPullDegGeneratingEverywhereStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.exists_rescale_isPullDeg_generating_everywhere : ∀ {W V : Type} [CommRing W] [IsDomain W] [CommRing V] [IsDomain V] (θ₀ : W →+* V) (D₀ : DegPre W) (Q : DegPre V) (e : Q.X ≃+ D₀.X) (β : Q.P.A.left ⟶ D₀.P.A.left), (∀ y, PsiUnitOn D₀ y Set.univ) → IsGrpPullback Q.P.A D₀.P.A (spMap θ₀) β → LBIso Q.P.L (D₀.P.L.pull β) → (∀ y, (Q.c y).left ≫ β = spMap θ₀ ≫ (D₀.c (e y)).left) → ∃ (g : Q.X → (FractionRing V)ˣ) (hD : IsPullDeg θ₀ D₀ (GlobalTheory.PolDeg.rescale Q g)), (∀ y, hD.xe y = e y) ∧ hD.e.hom.left ≫ pullback.fst D₀.P.A.hom (specOf θ₀) = β ∧ hD.W = ⊤ := by
  first | exact @GlobalTheory.PreLiftData.exists_rescale_isPullDeg_top | exact GlobalTheory.PreLiftData.exists_rescale_isPullDeg_top | (intros; apply GlobalTheory.PreLiftData.exists_rescale_isPullDeg_top <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiUnitOnUnivOfPullbackReadTop

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PullTopUnit
open GlobalTheory.ArcPull
open GlobalTheory.PsiEvenPull (proj)

theorem psiUnitOn_pull_top {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'}
    {D : DegPre R} {D' : DegPre R'} (hD : IsPullDeg φ D D') (hW : hD.W = ⊤) (x : D'.X) :
    PsiUnitOn D' x Set.univ := by
  have hI : IsIso hD.W.ι := by rw [hW, ← Scheme.topIso_hom]; infer_instance
  let h : Sp R' ⟶ (TW hD.W).left := specOf φ ≫ inv hD.W.ι
  have hh : h ≫ hD.W.ι = specOf φ := by simp [h]
  have hg : hD.g = jK R' ≫ h := by
    rw [← cancel_mono hD.W.ι, hD.g_comm, Category.assoc, hh]
  have sq : (D'.c x).left ≫ proj hD = h ≫ (toUnit (TW hD.W) ≫ D.c (hD.xe x)).left := by
    rw [hD.c_pr x, ← hh, Category.assoc]; rfl
  obtain ⟨a, ha, va⟩ := exists_down_om hD.w_gen D.P.isLB D'.P.isLB (Y' := Sp R') (K := PUnit)
    (φ' := fun _ => (D'.c x).left) h (fun _ => sq) (hD.psiW.psi (hD.xe x)) (hD.psiW.psi_gen _)
  refine (psiUnitOn_univ_iff D' x).2 ⟨a, ha, corr_of_val D'.P.isLB fun y J' hJ' => ?_⟩
  obtain ⟨J, hJ⟩ := DegPull.exists_good' D.P.isLB y
  have e₁ := PsiEvenPull.psi_pull hD x (𝟙 _) y hJ hJ'
  have e₂ := va _ (𝟙 _ ≫ jK R') y J J' hJ hJ'
  rw [Fintype.prod_unique, zpow_neg_one, Category.assoc (𝟙 _) (jK R') h, ← hg] at e₂
  have e := e₁.symm.trans e₂
  exact (val_pull hJ' _ _ _).trans (mul_left_cancel e).symm

end GlobalTheory.PullTopUnit
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiUnitOnUnivOfPullbackReadTopStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.psiUnitOn_univ_of_pullback_read_top : ∀ {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R} {D' : DegPre R'} (hD : IsPullDeg φ D D'), hD.W = ⊤ → ∀ x : D'.X, PsiUnitOn D' x Set.univ := by
  first | exact @GlobalTheory.PullTopUnit.psiUnitOn_pull_top | exact GlobalTheory.PullTopUnit.psiUnitOn_pull_top | (intros; apply GlobalTheory.PullTopUnit.psiUnitOn_pull_top <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullDegKeepsBimultActionPolarisationElement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem tauBimult_and_exists_oAct_of_pullDeg : ∀ {O : Type} [CommRing O] [StarRing O] {W V : Type} [CommRing W] [IsDomain W] [CommRing V] [IsDomain V] {θ₀ : W →+* V} {D₀ : DegPre W} [Module O D₀.X] (o₀ : D₀.OAct O) {D : DegPre V} [Module O D.X] (hD : IsPullDeg θ₀ D₀ D) (ob : D.P.OAct O), (∀ (a : O) y, hD.xe (a • y) = a • hD.xe y) → (∀ (a : O) y, D.c (a • y) = D.c y ≫ ob.act a) → (∀ a : O, (ob.act a).left ≫ hD.e.hom.left ≫ pullback.fst D₀.P.A.hom (specOf θ₀) = (hD.e.hom.left ≫ pullback.fst D₀.P.A.hom (specOf θ₀)) ≫ (o₀.onB.act a).left) → D₀.TauBimult → ∀ w0 : O, TraceFormTwistIso D₀ o₀ w0 → D.TauBimult ∧ ∃ o : D.OAct O, o.onB = ob ∧ TraceFormTwistIso D o w0 := by
  intro O _ _ W V _ _ _ _ θ₀ D₀ _ o₀ D _ hD ob hx hcl hact hB w0 hP
  have hG : GlobalFnsSt := GlobalTheory.allSixLaws.1.globalFns
  have hc : ∀ a : O, ob.act a ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf θ₀)).map (o₀.onB.act a) := by
    intro a
    have a₂ : ((Over.pullback (specOf θ₀)).map (o₀.onB.act a)).left ≫ pullback.fst D₀.P.A.hom (specOf θ₀) =
        pullback.fst _ _ ≫ (o₀.onB.act a).left := pullback.lift_fst _ _ _
    refine Over.OverMorphism.ext (pullback.hom_ext ?_ ?_)
    · have h := hact a
      simp only [Over.comp_left, Category.assoc] at h ⊢
      exact h.trans (congrArg (fun q => hD.e.hom.left ≫ q) a₂.symm)
    · exact (Over.w (ob.act a ≫ hD.e.hom)).trans
        (Over.w (hD.e.hom ≫ (Over.pullback (specOf θ₀)).map (o₀.onB.act a))).symm
  let o : D.OAct O := ⟨ob, hcl, fun a =>
    GlobalTheory.tauBal_of_isPullDeg hG _ _ θ₀ D₀ D hD (o₀.onB.act a) (o₀.onB.act (star a)) (ob.act a) (ob.act (star a))
      (o₀.onB.hom _) (o₀.onB.hom _) (o₀.onB.rosati a) (hc a) (hc (star a)) (fun y => a • y) (fun y => star a • y)
      (fun y => a • y) (fun y => star a • y) (hx a) (hx (star a)) (o₀.c_lin a) (o₀.c_lin (star a)) (o₀.tau_bal a)⟩
  exact ⟨GlobalTheory.TauPull.tauBimult_pull hG hD hB, o, rfl,
    GlobalTheory.traceFormTwistIso_of_overPullback _ _ θ₀ D₀ D hD O o₀ o hx hc w0 hP⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullDegKeepsBimultActionPolarisationElementStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.pullDeg_keeps_bimult_action_polarisationElement : ∀ {O : Type} [CommRing O] [StarRing O] {W V : Type} [CommRing W] [IsDomain W] [CommRing V] [IsDomain V] {θ₀ : W →+* V} {D₀ : DegPre W} [Module O D₀.X] (o₀ : D₀.OAct O) {D : DegPre V} [Module O D.X] (hD : IsPullDeg θ₀ D₀ D) (ob : D.P.OAct O), (∀ (a : O) y, hD.xe (a • y) = a • hD.xe y) → (∀ (a : O) y, D.c (a • y) = D.c y ≫ ob.act a) → (∀ a : O, (ob.act a).left ≫ hD.e.hom.left ≫ pullback.fst D₀.P.A.hom (specOf θ₀) = (hD.e.hom.left ≫ pullback.fst D₀.P.A.hom (specOf θ₀)) ≫ (o₀.onB.act a).left) → D₀.TauBimult → ∀ w0 : O, TraceFormTwistIso D₀ o₀ w0 → D.TauBimult ∧ ∃ o : D.OAct O, o.onB = ob ∧ TraceFormTwistIso D o w0 := by
  first | exact @GlobalTheory.tauBimult_and_exists_oAct_of_pullDeg | exact GlobalTheory.tauBimult_and_exists_oAct_of_pullDeg | (intros; apply GlobalTheory.tauBimult_and_exists_oAct_of_pullDeg <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegDataDifferBySymmBalancedFormOfPsiTau

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.YRatio

theorem main : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {W V : Type} [CommRing W] [IsDomain W] [IsLocalRing W] [CommRing V] [IsDomain V] [IsLocalRing V] (θ₀ : W →+* V) (D₀ : DegPre W) [Module (𝓞 E) D₀.X] (o₀ : letI := H.starRing; D₀.OAct (𝓞 E)) (Q : DegPre V) [Module (𝓞 E) Q.X] (oQ : letI := H.starRing; Q.OAct (𝓞 E)) (e : Q.X ≃ₗ[𝓞 E] D₀.X) (β : Q.P.A.left ⟶ D₀.P.A.left), D₀.TauBimult → (∀ y, PsiUnitOn D₀ y Set.univ) → (letI := H.starRing; TraceFormTwistIso D₀ o₀ H.w0) → Q.TauBimult → (letI := H.starRing; TraceFormTwistIso Q oQ H.w0) → IsGrpPullback Q.P.A D₀.P.A (spMap θ₀) β → (letI := H.starRing; ∀ a : 𝓞 E, (oQ.onB.act a).left ≫ β = β ≫ (o₀.onB.act a).left) → LBIso Q.P.L (D₀.P.L.pull β) → (∀ y, (Q.c y).left ≫ β = spMap θ₀ ≫ (D₀.c (e y)).left) → ∃ (g : Q.X → (FractionRing V)ˣ) (hD : IsPullDeg θ₀ D₀ (GlobalTheory.PolDeg.rescale Q g)) (q : Q.X → Q.X → (FractionRing V)ˣ), (∀ y : Q.X, hD.xe y = e y) ∧ hD.e.hom.left ≫ pullback.fst D₀.P.A.hom (specOf θ₀) = β ∧ (∀ y, PsiUnitOn (GlobalTheory.PolDeg.rescale Q g) y Set.univ) ∧ (∀ a b, q a b = q b a) ∧ (∀ a a' b, q (a + a') b = q a b * q a' b) ∧ (∀ (x : 𝓞 E) a b, q (x • a) b = q a (H.bar x • b)) ∧ ∀ y, (g y)⁻¹ = q y (H.w0 • y) := by
  intro E _ _ _ H W V _ _ _ _ _ _ θ₀ D₀ _ o₀ Q _ oQ e β hB₀ hU hW₀ hBQ hWQ gp hact hL hc
  letI := H.starRing
  obtain ⟨g, hD, hxe, hβ, hWt⟩ := GlobalTheory.T.exists_rescale_isPullDeg_generating_everywhere θ₀ D₀ Q e.toAddEquiv β hU gp hL hc
  letI : Module (𝓞 E) (GlobalTheory.PolDeg.rescale Q g).X := ‹Module (𝓞 E) Q.X›
  obtain ⟨hB', o', ho', hW'⟩ := GlobalTheory.T.pullDeg_keeps_bimult_action_polarisationElement o₀ hD oQ.onB
    (fun a y => by rw [hxe, hxe]; exact e.map_smul a y) oQ.c_lin
    (fun a => by rw [hβ]; exact hact a) hB₀ H.w0 hW₀
  obtain ⟨q, h1, h2, h3, h4⟩ := GlobalTheory.T.rescaled_degenerationData_differ_by_scalar Q oQ g o' ho' hBQ hB' H.w0 hWQ hW'
  exact ⟨g, hD, q, hxe, hβ, GlobalTheory.T.psiUnitOn_univ_of_pullback_read_top hD hWt, h1, h2, h3, h4⟩

end GlobalTheory.YRatio
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegDataDifferBySymmBalancedFormOfPsiTauStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.degData_differ_by_symmBalancedForm_of_psi_tau : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {W V : Type} [CommRing W] [IsDomain W] [IsLocalRing W] [CommRing V] [IsDomain V] [IsLocalRing V] (θ₀ : W →+* V) (D₀ : DegPre W) [Module (𝓞 E) D₀.X] (o₀ : letI := H.starRing; D₀.OAct (𝓞 E)) (Q : DegPre V) [Module (𝓞 E) Q.X] (oQ : letI := H.starRing; Q.OAct (𝓞 E)) (e : Q.X ≃ₗ[𝓞 E] D₀.X) (β : Q.P.A.left ⟶ D₀.P.A.left), D₀.TauBimult → (∀ y, PsiUnitOn D₀ y Set.univ) → (letI := H.starRing; TraceFormTwistIso D₀ o₀ H.w0) → Q.TauBimult → (letI := H.starRing; TraceFormTwistIso Q oQ H.w0) → IsGrpPullback Q.P.A D₀.P.A (spMap θ₀) β → (letI := H.starRing; ∀ a : 𝓞 E, (oQ.onB.act a).left ≫ β = β ≫ (o₀.onB.act a).left) → LBIso Q.P.L (D₀.P.L.pull β) → (∀ y, (Q.c y).left ≫ β = spMap θ₀ ≫ (D₀.c (e y)).left) → ∃ (g : Q.X → (FractionRing V)ˣ) (hD : IsPullDeg θ₀ D₀ (GlobalTheory.PolDeg.rescale Q g)) (q : Q.X → Q.X → (FractionRing V)ˣ), (∀ y : Q.X, hD.xe y = e y) ∧ hD.e.hom.left ≫ pullback.fst D₀.P.A.hom (specOf θ₀) = β ∧ (∀ y, PsiUnitOn (GlobalTheory.PolDeg.rescale Q g) y Set.univ) ∧ (∀ a b, q a b = q b a) ∧ (∀ a a' b, q (a + a') b = q a b * q a' b) ∧ (∀ (x : 𝓞 E) a b, q (x • a) b = q a (H.bar x • b)) ∧ ∀ y, (g y)⁻¹ = q y (H.w0 • y) := by
  first | exact @GlobalTheory.YRatio.main | exact GlobalTheory.YRatio.main | (intros; apply GlobalTheory.YRatio.main <;> assumption)
end
end
