module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AbelianPartEqOfThetaOperatorEqStatement
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsShiftGen
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsThetaActs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegExpF
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
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
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueFamOfReps
import Mathlib.Tactic.Linter.Style
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsFamRep
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtPtBridgeSt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.DegPreAbelianPartIsIntegralAndIsIntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUnitOfStalks
import Mathlib.RingTheory.RegularLocalRing.Defs

-- Source module: Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpansionExtensionFieldTotal

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem expandsF_total : Laws → Laws2 → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k → ∀ (w : LB.Iso (A.L.pull U.gen.hom.left) (U.LG.L.pull (pullback.fst G.hom (jK R)))), w.IsGen → (∀ s : Fam D.toPre F k, ∃ t, U.toUnifPre.ExpandsF F k w t s) ∧ ∀ t, ∃ s : Fam D.toPre F k, U.toUnifPre.ExpandsF F k w t s := by
  intro h₁ _ R _ _ I _ D A G _ _ _ U F _ _ k hk w hw
  have h := FieldBaseChange.expandsF_bijective U.toUnifPre F h₁.globalFns hk (U.expand k hk) hw
  exact ⟨fun s => (h.2 s).exists, fun t => (h.1 t).exists⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpansionExtensionFieldTotalStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.expansion_extensionField_total : Laws → Laws2 → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k → ∀ (w : LB.Iso (A.L.pull U.gen.hom.left) (U.LG.L.pull (pullback.fst G.hom (jK R)))), w.IsGen → (∀ s : Fam D.toPre F k, ∃ t, U.toUnifPre.ExpandsF F k w t s) ∧ ∀ t, ∃ s : Fam D.toPre F k, U.toUnifPre.ExpandsF F k w t s := by
  first | exact @GlobalTheory.expandsF_total | exact GlobalTheory.expandsF_total | (intros; apply GlobalTheory.expandsF_total <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LatticePartCongrOfPhiRel

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PhiLattice

open ReciprocityTheory.ChartRestriction.G.DVR

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem trPt_inv_comp (m : TF (R := R) F ⟶ D.P.A) : DegPre.trPt D F m⁻¹ ≫ DegPre.trPt D F m = 𝟙 _ := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, tr_fst, tr_fst, Category.id_comp]
  · show (DegPre.trPt D F m⁻¹ ≫ DegPre.trPt D F m) ≫ DegPre.prB D F = 𝟙 _ ≫ DegPre.prB D F
    rw [Category.assoc, tr_pr, MonObj.comp_mul, tr_pr, ← Category.assoc, tr_fst, _root_.mul_assoc,
      ← MonObj.comp_mul, inv_mul_cancel, MonObj.comp_one, _root_.mul_one, Category.id_comp]

theorem zero_of_phiVal {n : ℕ} (p p' : QkPt D F n)
    (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε n)))
    (w' : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p'.g.b) (DegPre.lineε n)))
    {s t : Fam D F n} (h : PhiVal p w s.s t.s) (h' : PhiVal p' w' s.s t.s) {α α' : D.X}
    (e : α' + p'.y = α + p.y) (h0 : ∀ j, (s.s α).f j = 0) : ∀ j, (s.s α').f j = 0 := by
  intro j
  refine sec_ext_val (s' := SecOps.secZero) D.P.isLB (fun y J hJ => ?_) j
  have e₁ := h α _ rfl _ (DegPre.trPt D F p'.g.b⁻¹) y J hJ
  have e₂ := h' α' _ e _ (DegPre.trPt D F p'.g.b⁻¹) y J hJ
  rw [UUA.sval_zero_of h0 _ y J (hJ.mem _ _), MulZeroClass.zero_mul] at e₁
  rw [e₁, trPt_inv_comp, Over.id_left] at e₂
  rw [UUA.sval_zero_of (s := SecOps.secZero) (fun _ => rfl) _ y J (hJ.mem _ _)]
  exact (Units.mul_left_eq_zero _).1 e₂.symm

end GlobalTheory.PhiLattice

namespace GlobalTheory

theorem lattice_part_congr_of_phiRel : GlobalFnsSt → SecTwistSt → ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (n : ℕ), 1 ≤ n → ∀ (p p' : QkPt D F n) (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε n))) (w' : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p'.g.b) (DegPre.lineε n))), w.IsGen → w'.IsGen → (∀ s : Fam D F n, ∃ s' : Fam D F n, PhiRel D F n p w s s' ∧ PhiRel D F n p' w' s s') → ∃ z : D.X, p'.y = p.y + n • z := by
  intro hG hT R _ _ D hB F _ _ n hn p p' w w' hw hw' H
  obtain ⟨s, hs⟩ := FamFree.exists_fam_support (D := D) (F := F) hG hT hB hn 0
  obtain ⟨t, h, h'⟩ := H s
  rw [ReciprocityTheory.ChartRestriction.G.DVR.phiRel_iff hG p w hw] at h
  rw [ReciprocityTheory.ChartRestriction.G.DVR.phiRel_iff hG p' w' hw'] at h'
  have h0 : ¬ ∀ j, (s.s 0).f j = 0 := (hs 0).2 ⟨0, by rw [smul_zero, add_zero]⟩
  obtain ⟨z, hz⟩ := (hs (p'.y - p.y)).1 fun h1 =>
    h0 (PhiLattice.zero_of_phiVal p p' w w' h h' (by rw [zero_add, sub_add_cancel]) h1)
  exact ⟨z, by rw [zero_add] at hz; rw [hz, add_sub_cancel]⟩

end GlobalTheory
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorsionPairEqOfThetaOperatorRel

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace OperatorPoint

open ReciprocityTheory.ChartRestriction.G.DVR

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem trPt_inv_comp (b : TF (R := R) F ⟶ D.P.A) : DegPre.trPt D F b⁻¹ ≫ DegPre.trPt D F b = 𝟙 _ := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, tr_fst, tr_fst, Category.id_comp]
  · have e : (DegPre.trPt D F b⁻¹ ≫ DegPre.trPt D F b) ≫ DegPre.prB D F = DegPre.prB D F := by
      rw [Category.assoc, tr_pr, MonObj.comp_mul, tr_pr, ← Category.assoc, tr_fst, _root_.mul_assoc,
        ← MonObj.comp_mul, inv_mul_cancel, MonObj.comp_one, _root_.mul_one]
    exact e.trans (Category.id_comp _).symm

theorem phiVal_inv {n : ℕ} (p : QkPt D F n)
    (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε n)))
    {s t : ∀ α : D.X, LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε n))} (h : PhiVal p w s t)
    (α β : D.X) (hβ : α + p.y = β) (b : TF (R := R) F ⟶ D.P.A) (hb : p.g.b = b) (y : (DegPre.BF D F).left) (J)
    (hJ : Good D.P.L y J) :
    sval (t β) (DegPre.trPt D F b⁻¹).left y J = sval (s α) (𝟙 _) y J *
      (uVal D F n α b (DegPre.trPt D F b⁻¹) y J * (val (p.g.s α) (fst (TF (R := R) F) D.P.A).left y J *
        val w (fst (TF (R := R) F) D.P.A).left y J)).val := by
  subst hb
  have e := h α β hβ _ (DegPre.trPt D F p.g.b⁻¹) y J hJ
  rw [trPt_inv_comp, tr_fst, val_mul hJ] at e
  exact e

end OperatorPoint


open ReciprocityTheory.ChartRestriction.G.DVR OperatorPoint in
theorem qkPt_g_eq_of_phiRel :
    GlobalFnsSt → SecTwistSt → ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (n : ℕ), 1 ≤ n → ∀ (p p' : QkPt D F n) (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε n))) (w' : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p'.g.b) (DegPre.lineε n))), w.IsGen → w'.IsGen → (∀ s : Fam D F n, ∃ s' : Fam D F n, PhiRel D F n p w s s' ∧ PhiRel D F n p' w' s s') → p'.y = p.y → p.g.b = p'.g.b → p.g = p'.g := by
  intro hG hT R _ _ D hB F _ _ n hn p p' w w' hw hw' H hy hb
  have hI := (degPre_abelianPart_isIntegral_and_isIntegrallyClosed_stalk R D F).1
  have key : ∀ (α : D.X) (y : (DegPre.BF D F).left) (J), Good D.P.L y J →
      val (p.g.s α) (fst (TF (R := R) F) D.P.A).left y J * val w (fst (TF (R := R) F) D.P.A).left y J =
        val (p'.g.s α) (fst (TF (R := R) F) D.P.A).left y J * val w' (fst (TF (R := R) F) D.P.A).left y J := by
    intro α y J hJ
    obtain ⟨σ, hσ⟩ := FamFree.exists_sec_ne_zero (D := D) (F := F) hT hn α
    obtain ⟨s, rfl, -⟩ := FamFree.exists_fam_single hG hB hn α σ
    obtain ⟨t, h₁, h₂⟩ := H s
    have e₁ := phiVal_inv p w ((phiRel_iff hG p w hw s t).1 h₁) α (α + p.y) rfl _ rfl y J hJ
    have e₂ := phiVal_inv p' w' ((phiRel_iff hG p' w' hw' s t).1 h₂) α (α + p.y) (by rw [hy]) _ hb.symm y J hJ
    have hne : sval (s.s α) (𝟙 _) y J ≠ 0 :=
      RootUnit.sec_gs_ne_zero (s.s α) (not_forall.1 hσ) y _ (hJ.mem _ (𝟙 _))
    exact mul_left_cancel (Units.ext (mul_left_cancel₀ hne (e₁.symm.trans e₂)))
  have key' : ∀ (α : D.X) (y : (DegPre.BF D F).left) (J), Good D.P.L y J →
      val (p.g.s α) (fst (TF (R := R) F) D.P.A).left y J = val (p'.g.s α) (fst (TF (R := R) F) D.P.A).left y J := by
    intro α y J hJ
    have e₀ := key 0 y J hJ
    rw [val_corr hJ p.g.s_zero, val_corr hJ p'.g.s_zero, val_one, _root_.one_mul, _root_.one_mul] at e₀
    have e := key α y J hJ
    rw [e₀] at e
    exact mul_right_cancel e
  refine TorusExt.gt_ext hb fun χ => corr_of_val D.P.isLB fun y J hJ => ?_
  have hc : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ (p.g.s χ) (fst (TF (R := R) F) D.P.A).left)
      (LB.pullGen D.P.L _ _ (p'.g.s χ) (fst (TF (R := R) F) D.P.A).left) :=
    corr_of_val D.P.isLB fun y J hJ => by
      rw [val_pull hJ, val_pull hJ, Category.id_comp]; exact key' χ y J hJ
  have z₁ : (DegPre.zF D F).left ≫ (fst (TF (R := R) F) D.P.A).left = 𝟙 _ :=
    congrArg (fun q => q.left) (show DegPre.zF D F ≫ fst _ _ = 𝟙 _ from lift_fst _ _)
  have e := val_corr hJ hc (DegPre.zF D F).left
  rwa [val_pull hJ, val_pull hJ, z₁] at e

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorsionPairEqOfThetaOperatorRelStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.torsionPair_eq_of_thetaOperator_rel : GlobalFnsSt → SecTwistSt → ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (n : ℕ), 1 ≤ n → ∀ (p p' : QkPt D F n) (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε n))) (w' : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p'.g.b) (DegPre.lineε n))), w.IsGen → w'.IsGen → (∀ s : Fam D F n, ∃ s' : Fam D F n, PhiRel D F n p w s s' ∧ PhiRel D F n p' w' s s') → p'.y = p.y → p.g.b = p'.g.b → p.g = p'.g := by
  first | exact @GlobalTheory.qkPt_g_eq_of_phiRel | exact GlobalTheory.qkPt_g_eq_of_phiRel | (intros; apply GlobalTheory.qkPt_g_eq_of_phiRel <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkInjective

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsionMapInj

theorem qkToAk_injective : Laws → Laws2 → QkToAkInjSt := by
  intro hL hL₂ R _ _ I hR D A G _ _ hG U F _ _ _ n hn p p' x hp hp'
  obtain ⟨w₀, hw₀⟩ := U.ext
  obtain ⟨hx, H⟩ := hp w₀ hw₀
  obtain ⟨-, H'⟩ := hp' w₀ hw₀
  obtain ⟨θ, hθ, hact⟩ := GlobalTheory.TorsionTheta.exists_theta_acts hL.kerPow _ A F (jFK (R := R) F) n hn x hx
  obtain ⟨w, hw, Hw⟩ := H θ hθ
  obtain ⟨w', hw', Hw'⟩ := H' θ hθ
  obtain ⟨E₁, E₂⟩ := GlobalTheory.T.expansion_extensionField_total hL hL₂ R I hR D A G hG U F n hn w₀ hw₀
  have key : ∀ s : Fam D.toPre F n, ∃ s' : Fam D.toPre F n,
      PhiRel D.toPre F n p w s s' ∧ PhiRel D.toPre F n p' w' s s' := fun s => by
    obtain ⟨t, ht⟩ := E₁ s
    obtain ⟨t', ht'⟩ := hact t
    obtain ⟨s', hs'⟩ := E₂ t'
    exact ⟨s', Hw t t' s s' ht hs' ht', Hw' t t' s s' ht hs' ht'⟩
  have hB := D.tau_bimult
  obtain ⟨z, hz⟩ := GlobalTheory.lattice_part_congr_of_phiRel hL.globalFns hL₂.secTwist R D.toPre hB F n hn p p' w w' hw hw' key
  obtain ⟨w₂, hw₂, Hs⟩ := GlobalTheory.QkShift.qk_shift hL.globalFns R D.toPre hB F n hn p (GlobalTheory.TorusExt.qkShift hB p z) z
    (GlobalTheory.TorusExt.iota hB F z) rfl (GlobalTheory.TorusExt.isIota_iota hB z) ((GlobalTheory.TorusExt.isAdd_iff_eq _ _ _).2 rfl) w hw
  have key₂ : ∀ s : Fam D.toPre F n, ∃ s' : Fam D.toPre F n,
      PhiRel D.toPre F n (GlobalTheory.TorusExt.qkShift hB p z) w₂ s s' ∧ PhiRel D.toPre F n p' w' s s' := fun s => by
    obtain ⟨s', h, h'⟩ := key s
    exact ⟨s', Hs s s' h, h'⟩
  have hb := GlobalTheory.T.abelianPart_eq_of_thetaOperator_eq hL.globalFns hL₂.secTwist R D.toPre hB F n hn _ p' w₂ w' hw₂ hw' key₂ hz
  have hg := GlobalTheory.T.torsionPair_eq_of_thetaOperator_rel hL.globalFns hL₂.secTwist R D.toPre hB F n hn _ p' w₂ w' hw₂ hw' key₂ hz hb
  exact (GlobalTheory.TorusExt.equiv_iff hB p p').2 ⟨z, hz, hg.symm⟩

end GlobalTheory.TorsionMapInj
end
end
