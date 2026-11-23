module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealTwLe
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TupPrimeEmpty
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelLiftIsLiftPrincipalLevelDatumRealisation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatDatumLiftDatumSameHalfTranslateConjugatePlac
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuppAtMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NabBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatVectorEqUnitSmulCentralTranslatePlacePart
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
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatVectorThreeStepsConjugatePlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatTranslateOfPrime
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LiftWeightComplexPointEqTwist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPairCharactersAtLevel
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdjointFrameIntegralIffPartsConjHalf
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIdempotentSumSubsetAndConjugateFlip
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPlaceModelCompRestrictToHalfLatticeIndicator
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReductionAdjointFrameConjHalfTwoParts
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftVectorIsThetaFunctionTwoStepModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GramMapMulInv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaHalfMovesUnderTranslateOtherPlaces
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VStdOfOrthonormalSpan
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Links2OfRowsStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatVectorEqUnitSmulCentralTranslatePlacePartStatement

section

@[expose] public section

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.ExportSeries
open Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.ConjTwist (BaseOf UnitOff)
open GlobalTheory.FlatVecSum (princ)
open scoped TensorProduct


attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
open GlobalTheory.BigOn.Exp.TupLe.Swap


theorem _root_.GlobalTheory.T.flatVector_eq_unit_smul_centralTranslate_placePart : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m) (t : T0), VStd D i → ∀ (Sa : Finset (Pl D.host.E)), Sa ⊆ R.Q t → ∀ (eg ea : AE D) (fg : WO (Vc D i) (Wc D i) → ℂ), IsIdemSum eg R.Pg → IsIdemSum ea Sa → GlobalTheory.BaseCmp.IsTypeVec R i eg fg → ∃ (z : GA D (Vc D i)) (c : ℂ), SuppAt ea (Vc D i) z ∧ SuppAt (idem (R.Q t)) (Vc D i) z ∧ UnitOff (GlobalTheory.TwistField.tupPrime R t) c ∧ ∀ h g, ThAt R i ea fg (GlobalTheory.BaseCmp.flatDat R i Sa (R.xiR t) ea) h → ThAt R i (cA D ea) fg (adjDat R i Sa (R.xiR t) (cA D ea)) g → h = c • R.ωP i t (z⁻¹, 1) g := by
  first | exact @GlobalTheory.PartFlat.flat_eq_unit_smul_om_part | exact GlobalTheory.PartFlat.flat_eq_unit_smul_om_part | (intros; apply GlobalTheory.PartFlat.flat_eq_unit_smul_om_part <;> assumption)
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatVectorThreeStepsConjugatePlacesStatement

section

@[expose] public section

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.ExportSeries
open Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.ConjTwist (BaseOf UnitOff)
open GlobalTheory.FlatVecSum (princ)
open scoped TensorProduct


attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
open GlobalTheory.BigOn.Exp.TupLe.Swap


theorem _root_.GlobalTheory.T.flatVector_three_steps_conjugate_places : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m) (t : T0), VStd D i → ∀ (B : Base (Vc D i) (Wc D i)) (ψ : Twist D Circle), B.Good → BaseOf R i B → ψ.Good → B.admitted ψ.Q → R.xi t = B.de.chi * ψ.chi → idem (R.Q t) + cA D (idem (R.Q t)) = idem (B.de.Q ∪ ψ.Q) + cA D (idem (B.de.Q ∪ ψ.Q)) → ∃ (eg ea et : AE D) (fg hA : WO (Vc D i) (Wc D i) → ℂ), IsIdemSum eg R.Pg ∧ IsIdemSum ea (keepPart (R := R) t (B.de.Q ∪ ψ.Q)) ∧ IsIdemSum et (flipPart (R := R) t (B.de.Q ∪ ψ.Q)) ∧ GlobalTheory.BaseCmp.IsTypeVec R i eg fg ∧ ThAt R i ea fg (GlobalTheory.BaseCmp.flatDat R i (keepPart (R := R) t (B.de.Q ∪ ψ.Q)) (R.xiR t) ea) hA ∧ ThAt R i (cA D et) hA (GlobalTheory.BaseCmp.flatDat R i ((flipPart (R := R) t (B.de.Q ∪ ψ.Q)).image conjPl) (fun PP => B.de.locC PP * ψ.locC PP) (cA D et)) ((princ B).vecFlat ψ) := by
  first | exact @GlobalTheory.FlatThreeSteps.vecFlat_three_steps | exact GlobalTheory.FlatThreeSteps.vecFlat_three_steps | (intros; apply GlobalTheory.FlatThreeSteps.vecFlat_three_steps <;> assumption)
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftVectorThreeStepDecomposition

section

@[expose] public section

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.ExportSeries
open Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.ConjTwist (BaseOf UnitOff)
open GlobalTheory.FlatVecSum (princ)
open scoped TensorProduct


attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
open GlobalTheory.BigOn.Exp.TupLe.Swap

namespace GlobalTheory.LiftThreeStep

theorem omegaQ_union {D : D7} {a b : ℕ} {Sa St : Finset (Pl D.host.E)} (hd : Disjoint Sa St) (r : ℕ)
    (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (k : ℤ) (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)) :
    omegaQ (Sa ∪ St) r ξ k y = omegaQ Sa r ξ k y * omegaQ St r ξ k y := by
  let g : Pl D.host.E → ℂ := fun PP =>
    if h : LowZero r (y PP) ∧ IsUnit (topL r (y PP)).det then ((ξ PP h.2.unit : ℂˣ) : ℂ) ^ k else 0
  have key : ∀ Q : Finset (Pl D.host.E), omegaQ Q r ξ k y = ∏ PP ∈ Q, g PP := by
    intro Q
    unfold omegaQ
    by_cases h : ∀ PP ∈ Q, LowZero r (y PP) ∧ IsUnit (topL r (y PP)).det
    · rw [dite_eq_left h, ← Finset.prod_attach Q g]
      refine Finset.prod_congr rfl fun PP _ => ?_
      simp only [g]
      rw [dite_eq_left (h PP.1 PP.2)]
    · rw [dite_eq_right h]
      obtain ⟨PP, hPP⟩ := not_forall.1 h
      obtain ⟨hQ, hn⟩ := Classical.not_imp.1 hPP
      refine (Finset.prod_eq_zero hQ ?_).symm
      simp only [g]
      rw [dite_eq_right hn]
  rw [key, key, key, Finset.prod_union hd]

section
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)

theorem adjDat_union {Sa St : Finset (Pl D.host.E)} {ea et : AE D} (hg : IsIdemSum ea Sa) (hq : IsIdemSum et St)
    (hd : Disjoint Sa St) (he : IsIdemSum (ea + et) (Sa ∪ St)) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) :
    adjDat R i (Sa ∪ St) ξ (cA D (ea + et)) =
      GlobalTheory.TwoStepModel.tensorHalf (cA D et) (cA D ea) (adjDat R i Sa ξ (cA D ea)) (adjDat R i St ξ (cA D et)) := by
  have hA := GlobalTheory.ConjHalfSplitInt.frMapAdj_int_iff D _ _ (R.βV i) (R.βW i) Sa St ea et hg hq hd he
  have hB := GlobalTheory.TwoStepRed.redM_twoStep D _ _ (R.βV i) (R.βW i) Sa St ea et hg hq hd he
  have heg := GlobalTheory.PlaceVec.idemSum_mul_self hg
  have heQ := GlobalTheory.PlaceVec.idemSum_mul_self hq
  have hcg : ∀ x : WO (Vc D i) (Wc D i), IsHalf (cA D ea) (cA D ea • x) :=
    fun x => GlobalTheory.ExportSeries.RestrictHalfModel.isHalf_smul (by rw [← map_mul, heg]) x
  have hcQ : ∀ x : WO (Vc D i) (Wc D i), IsHalf (cA D et) (cA D et • x) :=
    fun x => GlobalTheory.ExportSeries.RestrictHalfModel.isHalf_smul (by rw [← map_mul, heQ]) x
  funext x
  rw [GlobalTheory.TwoStepModel.tensorHalf_apply]
  unfold adjDat
  have hc : cA D (ea + et) = cA D et + cA D ea := by rw [map_add (f := _), add_comm]
  by_cases hx : IsHalf (cA D (ea + et)) x
  · have hx' : IsHalf (cA D et + cA D ea) x := hc ▸ hx
    rw [if_pos hx', mul_one]
    by_cases hi : IsIntM (frMapAdj _ _ (R.βV i) (R.βW i) x)
    · obtain ⟨i1, i2⟩ := (hA x hx).1 hi
      obtain ⟨r1, r2⟩ := hB x hx hi
      rw [if_pos (And.intro hx hi), if_pos (And.intro (hcQ x) i2), if_pos (And.intro (hcg x) i1), omegaQ_union hd, mul_comm]
      congr 1
      · exact GlobalTheory.PlaceVec.omegaQ_congr St _ ξ _ fun PP hPP => (r2 PP hPP).symm
      · exact GlobalTheory.PlaceVec.omegaQ_congr Sa _ ξ _ fun PP hPP => (r1 PP hPP).symm
    · have c1 : ¬ (IsHalf (cA D (ea + et)) x ∧ IsIntM (frMapAdj _ _ (R.βV i) (R.βW i) x)) := fun h => hi h.2
      rw [if_neg c1]
      have := mt (hA x hx).2 hi
      rcases not_and_or.1 this with h | h
      · have c3 : ¬ (IsHalf (cA D ea) (cA D ea • x) ∧ IsIntM (frMapAdj _ _ (R.βV i) (R.βW i) (cA D ea • x))) :=
          fun h' => h h'.2
        rw [if_neg c3, mul_zero]
      · have c2 : ¬ (IsHalf (cA D et) (cA D et • x) ∧ IsIntM (frMapAdj _ _ (R.βV i) (R.βW i) (cA D et • x))) :=
          fun h' => h h'.2
        rw [if_neg c2, zero_mul]
  · have c1 : ¬ (IsHalf (cA D (ea + et)) x ∧ IsIntM (frMapAdj _ _ (R.βV i) (R.βW i) x)) := fun h => hx h.1
    have hx' : ¬ IsHalf (cA D et + cA D ea) x := hc ▸ hx
    rw [if_neg c1, if_neg hx', mul_zero]

end

theorem thetaVector_three_step_decomposition : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m) (t : T0), VStd D i → ∀ (Sa St : Finset (Pl D.host.E)), Disjoint Sa St → Sa ∪ St = R.Q t → ∀ (eg ea et : AE D) (fg : WO (Vc D i) (Wc D i) → ℂ), IsIdemSum eg R.Pg → IsIdemSum ea Sa → IsIdemSum et St → GlobalTheory.BaseCmp.IsTypeVec R i eg fg → ∃ gA : WO (Vc D i) (Wc D i) → ℂ, ThAt R i (cA D ea) fg (adjDat R i Sa (R.xiR t) (cA D ea)) gA ∧ ThAt R i (cA D et) gA (adjDat R i St (R.xiR t) (cA D et)) (R.vP i t) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC hG i t _ Sa St hd hU eg ea et fg hg ha ht hfg
  obtain ⟨⟨hψ, -⟩, e, he, -⟩ := hC.thP.vP i t
  have hSV := GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hC.lev.βV i))
  have hSW := GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hC.lev.βW i))
  obtain ⟨eQ, hq⟩ := (GlobalTheory.IdemFlip.idemSum_sub_and_flip D e _ (R.Q t) he Finset.subset_union_right).1
  have h2 : ThAt R i (cA D eQ) fg (adjDat R i (R.Q t) (R.xiR t) (cA D eQ)) (R.vP i t) :=
    GlobalTheory.ConjTwist.isThetaAt_vP_twoStep D G Pl0 T0 A Ks R F hC hG i t eg eQ fg hg hq hfg
  rw [← hU] at hq h2
  have hsum : eQ = ea + et := by
    rw [← GlobalTheory.ExportSeries.idem_eq hq, ← GlobalTheory.ExportSeries.idem_eq ha, ← GlobalTheory.ExportSeries.idem_eq ht]
    exact Finset.sum_union hd
  subst hsum
  have hea := GlobalTheory.PlaceVec.idemSum_mul_self ha
  have het := GlobalTheory.PlaceVec.idemSum_mul_self ht
  have hee := GlobalTheory.PlaceVec.idemSum_mul_self hq
  have hat : ea * et = 0 := by
    refine GlobalTheory.PlaceVec.natCast_mul_eq_zero 2 _ two_pos ?_
    push_cast
    linear_combination hee - hea - het
  have hca : cA D ea * cA D ea = cA D ea := by rw [← map_mul, hea]
  have hct : cA D et * cA D et = cA D et := by rw [← map_mul, het]
  have hta : cA D et * cA D ea = 0 := by rw [← map_mul, mul_comm, hat, map_zero]
  have hat' : cA D ea * cA D et = 0 := by rw [mul_comm, hta]
  have hΛ : ∀ a : AE D, a * a = a → ∀ u ∈ (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True),
      a • u ∈ (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) :=
    fun a ha u hu => GlobalTheory.PlaceModelSum.idem_smul_latO ha hu
  have hinfa : infPart D (cA D ea) = 0 := GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart ha)
  have hinft : infPart D (cA D et) = 0 := GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart ht)
  have hSB : ∀ (Q : Finset (Pl D.host.E)) (a : AE D), infPart D a = 0 →
      IsSBHalf a (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) (adjDat R i Q (R.xiR t) a) :=
    fun Q a hinf => GlobalTheory.PlaceVec.isSBHalf_of_red (GlobalTheory.PlaceVec.selfDual_isFullLattice _ _ hSV) (GlobalTheory.PlaceVec.selfDual_isFullLattice _ _ hSW) hinf (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i))
      (GlobalTheory.PlaceVec.frMapAdj_add _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_up _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_down _ _ _ _)
      Q (fun y => omegaQ Q (Wc D i).rank (R.xiR t) (-1) y) fun y y' h => GlobalTheory.PlaceVec.omegaQ_congr _ _ _ _ h
  obtain ⟨⟨Te, hTe1⟩, hTe2⟩ := h2
  have hc : cA D (ea + et) = cA D et + cA D ea := by rw [map_add (f := _), add_comm]
  have hc' : cA D (ea + et) = cA D ea + cA D et := map_add _ _ _
  have hm1 := GlobalTheory.TwoStepModel.isPlaceModel_comp_tensorHalf hct hca hta hΛ (hSB Sa _ hinfa) (hc ▸ hTe1)
  have hm2 := GlobalTheory.ExportSeries.isPlaceModel_comp_restrictHalf hca hct hat' hΛ (hc' ▸ hTe1)
  refine ⟨_, ⟨⟨_, hm2⟩, fun T' hT' => ?_⟩, ⟨_, hm1⟩, fun T' hT' => ?_⟩
  · exact GlobalTheory.PlaceVec.placeModel_unique hψ hSV hSW hca hinfa hm2 hT' (hSB Sa _ hinfa)
  · rw [hTe2 Te hTe1, adjDat_union R i ha ht hd hq (R.xiR t)]
    exact GlobalTheory.PlaceVec.placeModel_unique hψ hSV hSW hct hinft hm1 hT' (hSB St _ hinft)

end GlobalTheory.LiftThreeStep

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftVectorThreeStepDecompositionStatement

section

@[expose] public section

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.ExportSeries
open Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.ConjTwist (BaseOf UnitOff)
open GlobalTheory.FlatVecSum (princ)
open scoped TensorProduct


attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
open GlobalTheory.BigOn.Exp.TupLe.Swap


theorem _root_.GlobalTheory.T.lift_vector_three_step_decomposition : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m) (t : T0), VStd D i → ∀ (Sa St : Finset (Pl D.host.E)), Disjoint Sa St → Sa ∪ St = R.Q t → ∀ (eg ea et : AE D) (fg : WO (Vc D i) (Wc D i) → ℂ), IsIdemSum eg R.Pg → IsIdemSum ea Sa → IsIdemSum et St → GlobalTheory.BaseCmp.IsTypeVec R i eg fg → ∃ gA : WO (Vc D i) (Wc D i) → ℂ, ThAt R i (cA D ea) fg (adjDat R i Sa (R.xiR t) (cA D ea)) gA ∧ ThAt R i (cA D et) gA (adjDat R i St (R.xiR t) (cA D et)) (R.vP i t) := by
  first | exact @GlobalTheory.LiftThreeStep.thetaVector_three_step_decomposition | exact GlobalTheory.LiftThreeStep.thetaVector_three_step_decomposition | (intros; apply GlobalTheory.LiftThreeStep.thetaVector_three_step_decomposition <;> assumption)
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaHalfMovesUnderTranslateOtherPlacesStatement

section

@[expose] public section

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.ExportSeries
open Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.ConjTwist (BaseOf UnitOff)
open GlobalTheory.FlatVecSum (princ)
open scoped TensorProduct


attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
open GlobalTheory.BigOn.Exp.TupLe.Swap


theorem _root_.GlobalTheory.T.theta_half_moves_under_translate_other_places : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m) (t : T0), VStd D i → ∀ (Sa St : Finset (Pl D.host.E)), Sa ⊆ R.Q t → St ⊆ R.Q t → Disjoint Sa St → ∀ (eg ea et : AE D) (fg b Φ f : WO (Vc D i) (Wc D i) → ℂ) (z : GA D (Vc D i)) (c : ℂ), IsIdemSum eg R.Pg → IsIdemSum ea Sa → IsIdemSum et St → GlobalTheory.BaseCmp.IsTypeVec R i eg fg → ThAt R i (cA D ea) fg (adjDat R i Sa (R.xiR t) (cA D ea)) b → SuppAt ea (Vc D i) z → c ≠ 0 → ThAt R i (cA D et) b Φ f → ThAt R i (cA D et) (c • R.ωP i t (z⁻¹, 1) b) Φ (c • R.ωP i t (z⁻¹, 1) f) := by
  first | exact @GlobalTheory.ThetaBaseMove.thAt_move | exact GlobalTheory.ThetaBaseMove.thAt_move | (intros; apply GlobalTheory.ThetaBaseMove.thAt_move <;> assumption)
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceBoundTuple

section

@[expose] public section

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.ExportSeries
open Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.ConjTwist (BaseOf UnitOff)
open GlobalTheory.FlatVecSum (princ)
open scoped TensorProduct


attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

namespace GlobalTheory.BigOn.Exp.TupLe.Swap

theorem flat_gen : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m) (t : T0), VStd D i → ∀ (B : Base (Vc D i) (Wc D i)) (ψ : Twist D Circle), B.Good → BaseOf R i B → ψ.Good → B.admitted ψ.Q → R.xi t = B.de.chi * ψ.chi → idem (R.Q t) + cA D (idem (R.Q t)) = idem (B.de.Q ∪ ψ.Q) + cA D (idem (B.de.Q ∪ ψ.Q)) → ∃ (z : GA D (Vc D i)) (c : ℂ), SuppAt (idem (R.Q t)) (Vc D i) z ∧ UnitOff (GlobalTheory.TwistField.tupPrime R t) c ∧
    (princ B).vecFlat ψ = c • R.ωP i t (z⁻¹, 1) (R.vP i t) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC hQG i t hV B ψ hB hB0 hψ hQ hxi hid
  classical
  obtain ⟨eg, ea, et, fg, hA, heg, hea, het, hfg, hhA, hflat⟩ := GlobalTheory.T.flatVector_three_steps_conjugate_places D G Pl0 T0 A Ks R F hC hQG i t hV B ψ hB hB0 hψ hQ hxi hid
  have hdisj : Disjoint (keepPart (R := R) t (B.de.Q ∪ ψ.Q)) (flipPart (R := R) t (B.de.Q ∪ ψ.Q)) :=
    Finset.disjoint_filter_filter_not _ _ _
  have hun : keepPart (R := R) t (B.de.Q ∪ ψ.Q) ∪ flipPart (R := R) t (B.de.Q ∪ ψ.Q) = R.Q t :=
    Finset.filter_union_filter_not_eq _ _
  obtain ⟨gA, hgA, hvP⟩ := GlobalTheory.T.lift_vector_three_step_decomposition D G Pl0 T0 A Ks R F hC hQG i t hV _ _ hdisj hun eg ea et fg heg hea het hfg
  obtain ⟨zA, cA', hzA, hzA', hcA, hAeq⟩ := GlobalTheory.T.flatVector_eq_unit_smul_centralTranslate_placePart D G Pl0 T0 A Ks R F hC hQG i t hV _ (Finset.filter_subset _ _) eg ea fg heg hea hfg
  obtain ⟨zT, cT, -, hzT', hcT, hT⟩ := GlobalTheory.T.flatDatum_liftDatum_same_half_translate_conjugatePlaces D G Pl0 T0 A Ks R F hC hQG i t hV B ψ hB hB0 hψ hQ hxi hid eg ea et fg hA heg hea het hfg hhA
  have e1 : hA = cA' • R.ωP i t (zA⁻¹, 1) gA := hAeq hA gA hhA hgA
  have hm := GlobalTheory.T.theta_half_moves_under_translate_other_places D G Pl0 T0 A Ks R F hC hQG i t hV _ _ (Finset.filter_subset _ _) (Finset.filter_subset _ _) hdisj eg ea et fg gA _ _ zA cA'
    heg hea het hfg hgA hzA hcA.1 hvP
  rw [← e1] at hm
  have e2 := hT _ _ hflat hm
  refine ⟨zA * zT, cT * cA', suppAt_mul' hzA' hzT', GlobalTheory.BigOn.Exp.TupLe.unitOff_mul hcT hcA, ?_⟩
  rw [e2, map_smul, smul_smul, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one, mul_inv_rev]

end GlobalTheory.BigOn.Exp.TupLe.Swap

namespace GlobalTheory.BigOn.Exp.TupLe


end GlobalTheory.BigOn.Exp.TupLe

end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FlatStHolds

section

@[expose] public section



section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.ExportSeries
open Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.ConjTwist (BaseOf UnitOff)
open GlobalTheory.FlatVecSum (princ)
open scoped TensorProduct


attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
namespace GlobalTheory.BigOn.Exp.TupLe.Swap
end GlobalTheory.BigOn.Exp.TupLe.Swap
namespace GlobalTheory.BigOn.Exp.TupLe
open GlobalTheory.BigOn.Exp.TupLe.Swap in
theorem flatSt_holds_alt : _root_.GlobalTheory.BigOn.Exp.TupLe.FlatCondition := by
  intro D L hT Gi Gl Kc Y cX ex Csz p j hr hm B ψ t hB hB0 hψ hQ hxi hid
  have hL : Links2 p := _root_.GlobalTheory.T.links2_of_single_index_twisted D L hT Gi Gl Kc Y cX ex Csz p hr hm.1
  have hC : GlobalTheory.Hk3.Core (R2 p) (F2 p) := ⟨hL.1.lev, hL.1.grp, hL.1.fam, hL.1.models, hL.1.chain, hL.1.thP⟩
  exact flat_gen _ _ _ _ _ _ (R2 p) (F2 p) hC p.qGuard j t (GlobalTheory.StdFrame.vStd_of_orthonormal_span _ j (p.stdV j))
    B ψ hB hB0 hψ hQ hxi hid
end GlobalTheory.BigOn.Exp.TupLe
end
end
end
end
