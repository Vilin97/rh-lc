module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DatP
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteAdelicMemSelfDualFrameStabilizerOfSplitSupStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameMapAdjointMulFrameMatrixEqIdempotentSplitStatement
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameMapAdjointTranslateInvEqMulFrameMatrix
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DatP
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.PartsOrth
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCharacterEmbeddingCompat
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalFrameChangeMemIntegralGLAtPlaceStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimeIdempotentOfIdempotentSumPlaceSplit
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameMapAdjointTranslateInvEqMulFrameMatrixStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.BadPlace
open Classical

theorem _root_.GlobalTheory.T.frameMapAdjoint_translate_inv_eq_mul_frameMatrix : ∀ (D : D7) (V W : HSp D) (βV : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (βW : GL (Fin W.rank) (Formalism.IndefR.Lev.EAf D)) (k : GA D W) (x : WO V W), frMapAdj V W βV βW (actO V W 1 k⁻¹ x) = (HMul.hMul (frMapAdj V W βV βW x) (HMul.hMul (HMul.hMul ((βW)⁻¹).val ((Formalism.L2.Theta.mt W k).map (toEAf D))) (βW).val : Matrix (Fin (W).rank) (Fin (W).rank) (Formalism.IndefR.Datum.EAf D)) : Matrix (Fin V.rank) (Fin W.rank) (Formalism.IndefR.Datum.EAf D)) := by
  first | exact @GlobalTheory.TranslateAdj.frMapAdj_actO_inv | exact GlobalTheory.TranslateAdj.frMapAdj_actO_inv | (intros; apply GlobalTheory.TranslateAdj.frMapAdj_actO_inv <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameMatrixComponentSubOneEqZeroOffIdempotent

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.BadPlace
open Classical

namespace GlobalTheory.FrameOff

theorem cpt_frame_sub_one_eq_zero_of_suppF : ∀ (D : D7) (W : HSp D) (β : GL (Fin W.rank) (Formalism.IndefR.Lev.EAf D)) (f : AE D) (k : GA D W) (PP : Pl D.host.E), SuppF W f k → GlobalTheory.StdFrames.cpt PP (toEAf D f) = 0 → ∀ a b, GlobalTheory.StdFrames.cpt PP (((HMul.hMul (HMul.hMul ((β)⁻¹).val ((Formalism.L2.Theta.mt W k).map (toEAf D))) (β).val : Matrix (Fin (W).rank) (Fin (W).rank) (Formalism.IndefR.Datum.EAf D)) - 1) a b) = 0 := by
  intro D W β f k PP hS hf a b
  set M := Formalism.L2.Theta.mt W k with hMdef
  have hmap : M.map (toEAf D) - 1 = (M - 1).map (toEAf D) := by
    rw [Matrix.map_sub (toEAf D) (fun x y => (toEAf D).map_sub x y),
      Matrix.map_one _ (toEAf D).map_zero (toEAf D).map_one]
  have hM : ((M - 1).map (toEAf D)).map (GlobalTheory.StdFrames.cpt PP) = 0 := by
    refine Matrix.ext fun i j => ?_
    change GlobalTheory.StdFrames.cpt PP (toEAf D ((M - 1) i j)) = 0
    rw [← hS i j, RingHom.map_mul, RingHom.map_mul, hf, zero_mul]
  have hk : (HMul.hMul (HMul.hMul ((β)⁻¹).val (M.map (toEAf D))) (β).val :
        Matrix (Fin (W).rank) (Fin (W).rank) (Formalism.IndefR.Datum.EAf D)) - 1
      = ((β)⁻¹).val * (M.map (toEAf D) - 1) * (β).val := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Units.inv_mul]
  rw [hk]
  change ((((β)⁻¹).val * (M.map (toEAf D) - 1) * (β).val).map (GlobalTheory.StdFrames.cpt PP)) a b = 0
  rw [Matrix.map_mul, Matrix.map_mul, hmap, hM, Matrix.mul_zero, Matrix.zero_mul]
  rfl

end GlobalTheory.FrameOff
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameMatrixComponentSubOneEqZeroOffIdempotentStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.BadPlace
open Classical

theorem _root_.GlobalTheory.T.frameMatrix_component_sub_one_eq_zero_off_idempotent : ∀ (D : D7) (W : HSp D) (β : GL (Fin W.rank) (Formalism.IndefR.Lev.EAf D)) (f : AE D) (k : GA D W) (PP : Pl D.host.E), SuppF W f k → GlobalTheory.StdFrames.cpt PP (toEAf D f) = 0 → ∀ a b, GlobalTheory.StdFrames.cpt PP (((HMul.hMul (HMul.hMul ((β)⁻¹).val ((Formalism.L2.Theta.mt W k).map (toEAf D))) (β).val : Matrix (Fin (W).rank) (Fin (W).rank) (Formalism.IndefR.Datum.EAf D)) - 1) a b) = 0 := by
  first | exact @GlobalTheory.FrameOff.cpt_frame_sub_one_eq_zero_of_suppF | exact GlobalTheory.FrameOff.cpt_frame_sub_one_eq_zero_of_suppF | (intros; apply GlobalTheory.FrameOff.cpt_frame_sub_one_eq_zero_of_suppF <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameReductionEqOneOfFrameMatrixCongruentOne

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.BadPlace
open Classical

namespace GlobalTheory.RedAt

theorem redFn_finE_eq_one : ∀ (D : D7) (W : HSp D) (β : GL (Fin W.rank) (Formalism.IndefR.Lev.EAf D)) (k : GA D W) (PP : Pl D.host.E), finE W k ∈ St β → (∀ a b, Valued.v (GlobalTheory.StdFrames.cpt PP (((HMul.hMul (HMul.hMul ((β)⁻¹).val ((Formalism.L2.Theta.mt W k).map (toEAf D))) (β).val : Matrix (Fin (W).rank) (Fin (W).rank) (Formalism.IndefR.Datum.EAf D)) - 1) a b)) < 1) → redFn β PP (finE W k) = 1 := by
  intro D W β k PP hk hv
  obtain ⟨y, hy⟩ := hk
  have hyv : (Formalism.L2.DIV.intGL _ _ _ y).val
      = (HMul.hMul (HMul.hMul ((β)⁻¹).val ((Formalism.L2.Theta.mt W k).map (toEAf D))) (β).val :
          Matrix (Fin (W).rank) (Fin (W).rank) (Formalism.IndefR.Datum.EAf D)) := by
    have h2 : Formalism.L2.DIV.intGL _ _ _ y = β⁻¹ * finE W k * β := by
      rw [← hy]; simp [Formalism.L2.DIV.frGL, MulAut.conj_apply, mul_assoc]
    rw [h2]; rfl
  rw [← hy, GlobalTheory.LiftLevel.redFn_eq_one_iff]
  intro i j
  rw [GlobalTheory.AdIsom.resS_eq_zero_iff_cpt]
  have := hv i j
  rw [← hyv] at this
  convert this using 3
  simp [Matrix.sub_apply, Matrix.one_apply, Formalism.L2.DIV.intGL, Formalism.UG.bc]
  split_ifs <;> simp

end GlobalTheory.RedAt
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameReductionEqOneOfFrameMatrixCongruentOneStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.BadPlace
open Classical

theorem _root_.GlobalTheory.T.frameReduction_eq_one_of_frameMatrix_congruent_one : ∀ (D : D7) (W : HSp D) (β : GL (Fin W.rank) (Formalism.IndefR.Lev.EAf D)) (k : GA D W) (PP : Pl D.host.E), finE W k ∈ St β → (∀ a b, Valued.v (GlobalTheory.StdFrames.cpt PP (((HMul.hMul (HMul.hMul ((β)⁻¹).val ((Formalism.L2.Theta.mt W k).map (toEAf D))) (β).val : Matrix (Fin (W).rank) (Fin (W).rank) (Formalism.IndefR.Datum.EAf D)) - 1) a b)) < 1) → redFn β PP (finE W k) = 1 := by
  first | exact @GlobalTheory.RedAt.redFn_finE_eq_one | exact GlobalTheory.RedAt.redFn_finE_eq_one | (intros; apply GlobalTheory.RedAt.redFn_finE_eq_one <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimeIdempotentOfIdempotentSumPlaceSplitStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.BadPlace
open Classical

theorem _root_.GlobalTheory.T.primeIdempotent_of_idempotentSum_place_split : ∀ (D : D7) (P : Pl D.host.E) (e f ea : AE D) (S : Finset (Pl D.host.E)), IsPrimeIdem P e f → IsIdemSum ea S → P ∈ S → Formalism.L2.NTheta.IsIdemAt e P ∧ f = e + cA D e ∧ cA D f = f ∧ infPart D f = 0 ∧ ∀ PP ∈ S, GlobalTheory.IdemSupport.cP PP ≠ P := by
  first | exact @GlobalTheory.IdemSumBranch.branch | exact GlobalTheory.IdemSumBranch.branch | (intros; apply GlobalTheory.IdemSumBranch.branch <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaHalfSpaceDatumTranslateDisjointSupport

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.BadPlace
open Classical

noncomputable section

namespace GlobalTheory.BadPlace

theorem datP_ne_zero_unpack {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (ea : AE D)
    (y : WO (Vc D i) (Wc D i)) (h : datP R i t ea y ≠ 0) :
    IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) y) ∧
    (∀ PP ∈ R.Pg, topL (Wc D i).rank (redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) y)) = 1) ∧
    (∀ PP ∈ R.Q t, IsUnit (topL (Wc D i).rank (redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) y))).det) := by
  unfold datP at h
  split_ifs at h with hc
  · refine ⟨hc.2, fun PP hPP => ?_, fun PP hPP => ?_⟩
    · have hK := left_ne_zero_of_mul h
      unfold omegaK at hK
      split_ifs at hK with hh
      · exact (hh PP hPP).2
      · exact absurd rfl hK
    · have hQ := right_ne_zero_of_mul h
      unfold omegaQ at hQ
      split_ifs at hQ with hh
      · exact (hh PP hPP).2
      · exact absurd rfl hQ
  · exact absurd rfl h

theorem disj_supp : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (ea : AE D), IsIdemSum ea (R.Pg ∪ R.Q t) → ∀ (P : Pl D.host.E), P ∈ R.Pg ∨ P ∈ R.Q t → ∀ e f, IsPrimeIdem P e f → ∀ k, SuppF (Wc D i) f k → k ∉ levW R i → ∀ x x' : WO (Vc D i) (Wc D i), (∀ a b, f * x a b = f * x' a b) → datP R i t ea (actO (Vc D i) (Wc D i) 1 k⁻¹ x) ≠ 0 → datP R i t ea x' ≠ 0 → False := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL hFP i t ea hea P hP e f hpe k hk hkn x x' hxx h1 h2
  apply hkn
  have hPS : P ∈ R.Pg ∪ R.Q t := Finset.mem_union.2 hP
  obtain ⟨heP, hfe, hcf, hinf, hcP⟩ := GlobalTheory.T.primeIdempotent_of_idempotentSum_place_split D P e f ea (R.Pg ∪ R.Q t) hpe hea hPS
  obtain ⟨hI1, hK1, hQ1⟩ := datP_ne_zero_unpack R i t ea _ h1
  obtain ⟨hI2, hK2, hQ2⟩ := datP_ne_zero_unpack R i t ea _ h2
  have hY := GlobalTheory.T.frameMapAdjoint_translate_inv_eq_mul_frameMatrix D (Vc D i) (Wc D i) (R.βV i) (R.βW i) k x
  have hid := GlobalTheory.T.frameMapAdjoint_mul_frameMatrix_eq_idempotent_split D (Vc D i) (Wc D i) (R.βV i) (R.βW i) f hcf k hk x x' hxx
  rw [← hY] at hid

  have he1 := GlobalTheory.StdFrames.cpt_of_isIdemAt heP
  have hcPP : GlobalTheory.IdemSupport.cP P ≠ P := hcP P hPS
  have hfP : GlobalTheory.StdFrames.cpt P (toEAf D f) = 1 := by
    rw [hfe, RingHom.map_add (f := _), GlobalTheory.StdFrames.toEAf_cA, RingHom.map_add (f := _), he1.1,
      GlobalTheory.StdFrames.cpt_sg_eq_zero (he1.2 _ hcPP), add_zero]
  have hfoff : ∀ PP ∈ R.Pg, PP ≠ P → GlobalTheory.StdFrames.cpt PP (toEAf D f) = 0 := by
    intro PP hPP hne
    rw [hfe, RingHom.map_add (f := _), GlobalTheory.StdFrames.toEAf_cA, RingHom.map_add (f := _), he1.2 _ hne,
      GlobalTheory.StdFrames.cpt_sg_eq_zero (he1.2 _ (hcP PP (Finset.mem_union_left _ hPP))), add_zero]
  have hu : ∀ (y : WO (Vc D i) (Wc D i)), (∀ PP ∈ R.Pg, topL (Wc D i).rank (redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) y)) = 1) →
      (∀ PP ∈ R.Q t, IsUnit (topL (Wc D i).rank (redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) y))).det) →
      IsUnit (topL (Wc D i).rank (redM P (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) y))).det := by
    intro y hK hQ
    rcases hP with hP | hP
    · rw [hK P hP, Matrix.det_one]; exact isUnit_one
    · exact hQ P hP
  obtain ⟨hint, hdet, hone⟩ := GlobalTheory.T.localFrameChange_mem_integralGL_at_place D P _ _ _ _ _ _ hfP hid hI2 hI1 (hu _ hK2 hQ2) (hu _ hK1 hQ1)
  have hSt := GlobalTheory.T.finiteAdelic_mem_selfDualFrameStabilizer_of_splitSupport D (Wc D i) (R.βW i) (R.ΛW i) (hL.lev.βW i) e f P heP hfe hcPP k hk hint hdet
  have hred : ∀ PP, PP ∈ (R.datWp i R.triv).Pg ∨ PP ∈ (R.datWp i R.triv).Q → redFn (R.βW i) PP (finE (Wc D i) k) = 1 := by
    rintro PP (hPP | hPP)
    · change PP ∈ R.Pg at hPP
      refine GlobalTheory.T.frameReduction_eq_one_of_frameMatrix_congruent_one D (Wc D i) (R.βW i) k PP hSt ?_
      by_cases hPe : PP = P
      · subst hPe
        exact hone (hK2 PP hPP) (hK1 PP hPP)
      · intro a b
        rw [GlobalTheory.T.frameMatrix_component_sub_one_eq_zero_off_idempotent D (Wc D i) (R.βW i) f k PP hk (hfoff PP hPP hPe) a b, map_zero]
        exact zero_lt_one
    · exact absurd hPP (Finset.notMem_empty _)
  exact ⟨GlobalTheory.IdemSupport.mem_GfC_of_suppF (Wc D i) hinf hk,
    GlobalTheory.LevSplit.mem_lev_of_red D.sp.cm (Wc D i).gram (R.βW i) (R.datWp i R.triv) _ (GlobalTheory.LevSplit.finE_mem_UA _ k) hSt hred⟩

end GlobalTheory.BadPlace

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaHalfSpaceDatumTranslateDisjointSupportStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.BadPlace
open Classical

theorem _root_.GlobalTheory.T.thetaHalfSpaceDatum_translate_disjoint_support : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (ea : AE D), IsIdemSum ea (R.Pg ∪ R.Q t) → ∀ (P : Pl D.host.E), P ∈ R.Pg ∨ P ∈ R.Q t → ∀ e f, IsPrimeIdem P e f → ∀ k, SuppF (Wc D i) f k → k ∉ levW R i → ∀ x x' : WO (Vc D i) (Wc D i), (∀ a b, f * x a b = f * x' a b) → datP R i t ea (actO (Vc D i) (Wc D i) 1 k⁻¹ x) ≠ 0 → datP R i t ea x' ≠ 0 → False := by
  first | exact @GlobalTheory.BadPlace.disj_supp | exact GlobalTheory.BadPlace.disj_supp | (intros; apply GlobalTheory.BadPlace.disj_supp <;> assumption)
end
end
