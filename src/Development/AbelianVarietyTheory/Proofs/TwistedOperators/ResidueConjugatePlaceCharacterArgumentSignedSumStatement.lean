module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CPAsIdeal
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateResidueFlagTermsReindexSymmetricEdgeStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemDeeperLevelIffReductionsSymmetricUnipotentStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairTable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagPairingVectorsIntegralInFrame
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OtherInstanceCharacterEqConjInstancePsiValueInte
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubOneIffEntries
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.IndefiniteReal.AutomorphicEvaluation
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SurjectiveReductionOntoFiniteLevelGroup
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ResidueConjugatePlaceHermitianFormAdjointStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ResidueOtherInstanceFormFlagPairingEqSignedDeltaStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ResidueOtherInstanceFormFrameStabilizerMulVecStatement
import Formalism.LocalToGlobal.Divisibility.TiedLemmas
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.OtherInstanceFormFlagPairingIntegralOnFrameLatti

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.SeeConjRead

noncomputable section
namespace GlobalTheory.SeeConjChar
open Classical

theorem hT_pairAt_int : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (β : GL (Fin (Yc D 0).rank) (EAf D)), IsFrame β (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → ∀ (PP : Pl D.host.E) (a : Fin (Yc D 0).rank) (z : Fin (Yc D 0).rank → EAf D), (∀ i, Matrix.mulVec (β⁻¹).val z i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) → GlobalTheory.SeeConjChar.hT X h (pairAt X h PP a) z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  intro D X h β hβ PP a z hz
  have hLf := GlobalTheory.KgFrame.Lf_eq D
  have hzL : z ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Lf := by
    rw [hLf]
    exact (hβ z).2 hz
  set S : Set (Fin (Yc D 0).rank → EAf D) := {v | v ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Lf} with hS
  have h0 : (0 : Fin (Yc D 0).rank → EAf D) ∈ S := by
    show (0 : Fin (Yc D 0).rank → EAf D) ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Lf
    exact zero_mem _
  obtain ⟨hef, hz0, hbw⟩ := X.vectorsInLattice
  have he : ∀ a, e0T X h a ∈ S := GlobalTheory.SeeConjRead.cast_fun_mem_Lf h X.e0 (fun a => (hef a).1)
  have hf : ∀ a, f0T X h a ∈ S := GlobalTheory.SeeConjRead.cast_fun_mem_Lf h X.f0 (fun a => (hef a).2)
  have hb : ∀ a, bwT X h a ∈ S := GlobalTheory.SeeConjRead.cast_fun_mem_Lf h X.bw (fun a => (hbw a).1)
  have hbd : ∀ a, bwdT X h a ∈ S := GlobalTheory.SeeConjRead.cast_fun_mem_Lf h X.bwd (fun a => (hbw a).2)
  have hzz : z0T X h ∈ S := GlobalTheory.SeeConjRead.cast_mem_Lf h X.z0 hz0
  have hv : pairAt X h PP a ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Lf := by
    show pairAt X h PP a ∈ S
    unfold pairAt
    split_ifs
    · exact GlobalTheory.SeeConjRead.flagV_mem S h0 _ _ _ _ _ _ _ hf he hbd hzz a
    · exact GlobalTheory.SeeConjRead.flagV_mem S h0 _ _ _ _ _ _ _ hf he (fun i => hb _) hzz a
  unfold hT
  exact intAf_cast X h _ (Formalism.L2.SG.Pf.unitaryCongruence.hA_int _ (GlobalTheory.SeeConjRead.cast_mem_Lf h.symm _ hv)
    (GlobalTheory.SeeConjRead.cast_mem_Lf h.symm _ hzL))

end GlobalTheory.SeeConjChar
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.OtherInstanceFormFlagPairingIntegralOnFrameLattiStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead


theorem _root_.GlobalTheory.T.otherInstanceForm_flagPairing_integral_on_frameLattice : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (β : GL (Fin (Yc D 0).rank) (EAf D)), IsFrame β (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → ∀ (PP : Pl D.host.E) (a : Fin (Yc D 0).rank) (z : Fin (Yc D 0).rank → EAf D), (∀ i, Matrix.mulVec (β⁻¹).val z i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) → GlobalTheory.SeeConjChar.hT X h (pairAt X h PP a) z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  first | exact @GlobalTheory.SeeConjChar.hT_pairAt_int | exact GlobalTheory.SeeConjChar.hT_pairAt_int | (intros; apply GlobalTheory.SeeConjChar.hT_pairAt_int <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ResidueConjugatePlaceHermitianDualBasisStabilise

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

namespace GlobalTheory.SeeConjChar

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf

theorem cpt_cP_eq_zero_of_orth {D : D7} {PP : Pl D.host.E} {e : EAf D} (ho : e * GlobalTheory.StdFrames.sg D e = 0)
    (h1 : GlobalTheory.StdFrames.cpt PP e = 1) : GlobalTheory.StdFrames.cpt (GlobalTheory.IdemSupport.cP PP) e = 0 := by
  have h2 := GlobalTheory.StdFrames.cpt_sg_eq_zero (Q := GlobalTheory.IdemSupport.cP PP) (z := 1 - e)
    (by rw [GlobalTheory.StdFrames.cP_cP, RingHom.map_sub, h1, RingHom.map_one, sub_self])
  rw [RingHom.map_sub, RingHom.map_one, RingHom.map_sub, RingHom.map_one, sub_eq_zero] at h2
  have h3 := congrArg (GlobalTheory.StdFrames.cpt (GlobalTheory.IdemSupport.cP PP)) ho
  rwa [RingHom.map_mul, ← h2, mul_one, RingHom.map_zero] at h3

theorem resT_eq_zero_of_fixed {D : D7} {Q : Pl D.host.E} {e x : EAf D} (hx : x ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (he : GlobalTheory.StdFrames.cpt Q e = 0) (hf : x = e * x) : resT Q x = 0 := by
  unfold resT
  rw [dite_eq_left hx]
  refine (GlobalTheory.AdIsom.resS_eq_zero_iff_cpt Q ⟨x, hx⟩).2 ?_
  have h0 : GlobalTheory.StdFrames.cpt Q x = 0 := by rw [hf, RingHom.map_mul, he, zero_mul]
  show Valued.v (GlobalTheory.StdFrames.cpt Q x) < 1
  rw [h0, Valuation.map_zero]
  exact zero_lt_one

theorem resT_cP_hT_bwd_eq_zero : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (β : GL (Fin (Yc D 0).rank) (EAf D)), IsFrame β (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → ∀ PP : Pl D.host.E, GlobalTheory.SeeConjChar.sideAt X h PP = true → ∀ M ∈ St β, ∀ i j : Fin D.R.k, GlobalTheory.SeeConjChar.hT X h (bwdT X h i) (Matrix.mulVec M.val (bwT X h j)) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ GlobalTheory.SeeConjChar.resT (GlobalTheory.IdemSupport.cP PP) (GlobalTheory.SeeConjChar.hT X h (bwdT X h i) (Matrix.mulVec M.val (bwT X h j))) = 0 := by
  intro D X h β hF PP hs M hM i j
  have hb := X.vectorsInLattice.2.2
  have ho := X.ew_orth
  have hw := X.bwd_w i
  have h1 : GlobalTheory.StdFrames.cpt PP (ewT X h) = 1 := by
    unfold sideAt at hs
    simpa only [decide_eq_true_eq] using hs
  have hfix : ∀ v, hA X.B.I (X.bwd i) v = X.ew * hA X.B.I (X.bwd i) v := fun v => by
    conv_lhs => rw [hw, unitaryCongruence.hA_smul_left, unitaryCongruence.sigA_sigA]
  obtain ⟨⟨I⟩⟩ := X
  dsimp only at h hb ho hfix
  subst h
  have hv := (hb j).1
  rw [GlobalTheory.SeeMatchOnto.Lf_eq] at hv
  have hv2 := (GlobalTheory.SeeMatchOnto.mem_hatL_iff_of_St hF hM _).1 hv
  have hv3 := (GlobalTheory.SeeMatchOnto.Lf_eq (D := D)).ge hv2
  have hint := unitaryCongruence.hA_int _ (hb i).2 hv3
  exact ⟨hint, resT_eq_zero_of_fixed hint (cpt_cP_eq_zero_of_orth ho h1) (hfix _)⟩

end GlobalTheory.SeeConjChar
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ResidueConjugatePlaceHermitianDualBasisStabiliseStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead


theorem _root_.GlobalTheory.T.residue_conjugatePlace_hermitian_dualBasis_stabiliser_eq_zero : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (β : GL (Fin (Yc D 0).rank) (EAf D)), IsFrame β (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → ∀ PP : Pl D.host.E, GlobalTheory.SeeConjChar.sideAt X h PP = true → ∀ M ∈ St β, ∀ i j : Fin D.R.k, GlobalTheory.SeeConjChar.hT X h (bwdT X h i) (Matrix.mulVec M.val (bwT X h j)) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ GlobalTheory.SeeConjChar.resT (GlobalTheory.IdemSupport.cP PP) (GlobalTheory.SeeConjChar.hT X h (bwdT X h i) (Matrix.mulVec M.val (bwT X h j))) = 0 := by
  first | exact @GlobalTheory.SeeConjChar.resT_cP_hT_bwd_eq_zero | exact GlobalTheory.SeeConjChar.resT_cP_hT_bwd_eq_zero | (intros; apply GlobalTheory.SeeConjChar.resT_cP_hT_bwd_eq_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ResidueConjugatePlaceCharacterArgumentSignedSum

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

noncomputable section

namespace GlobalTheory.SeeConjChar.AtConj

theorem resT_of_mem {D : D7} (PP : Pl D.host.E) {x : EAf D} (hx : x ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) :
    resT PP x = Formalism.L2.DIV.resS D.host.F PP ⟨x, hx⟩ := by
  unfold resT; rw [dite_eq_left hx]

theorem resT_zero {D : D7} (PP : Pl D.host.E) : resT PP (0 : EAf D) = 0 := by
  rw [resT_of_mem PP (zero_mem _)]
  exact map_zero (Formalism.L2.DIV.resS D.host.F PP)

theorem resT_add {D : D7} (PP : Pl D.host.E) {x y : EAf D} (hx : x ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (hy : y ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) : resT PP (x + y) = resT PP x + resT PP y := by
  rw [resT_of_mem PP hx, resT_of_mem PP hy, resT_of_mem PP (add_mem hx hy)]
  exact map_add (Formalism.L2.DIV.resS D.host.F PP) ⟨x, hx⟩ ⟨y, hy⟩

theorem resT_sum {D : D7} (PP : Pl D.host.E) {ι : Type} [Fintype ι] (f : ι → EAf D)
    (hf : ∀ i, f i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) : resT PP (∑ i, f i) = ∑ i, resT PP (f i) := by
  have hs : (∑ i, f i) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := sum_mem fun i _ => hf i
  rw [resT_of_mem PP hs]
  have e : (⟨∑ i, f i, hs⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = ∑ i, (⟨f i, hf i⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) := by
    apply Subtype.ext
    simp

  rw [e, map_sum]
  exact Finset.sum_congr rfl fun i _ => (resT_of_mem PP (hf i)).symm

theorem flagV_f {M : Type} [Zero M] {ρ k n : ℕ} (e f : Fin ρ → M) (b : Fin k → M) (z : M) (i : Fin n)
    (h1 : ρ + k < i.1) (h2 : i.1 < 2 * ρ + k + 1) :
    GlobalTheory.SeeConjRead.flagV ρ k n e f b z i = f ⟨2 * ρ + k - i.1, by omega⟩ := by
  unfold GlobalTheory.SeeConjRead.flagV
  rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_left h2]

theorem symmetricFlagBasisVectors_apply_middle {M : Type} [Zero M] {ρ k n : ℕ} (e f : Fin ρ → M) (b : Fin k → M) (z : M) (i : Fin n)
    (h1 : i.1 = ρ + k) : GlobalTheory.SeeConjRead.flagV ρ k n e f b z i = z := by
  unfold GlobalTheory.SeeConjRead.flagV
  rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_left h1]

theorem flagV_b {M : Type} [Zero M] {ρ k n : ℕ} (e f : Fin ρ → M) (b : Fin k → M) (z : M) (i : Fin n)
    (h1 : ρ ≤ i.1) (h2 : i.1 < ρ + k) : GlobalTheory.SeeConjRead.flagV ρ k n e f b z i = b ⟨i.1 - ρ, by omega⟩ := by
  unfold GlobalTheory.SeeConjRead.flagV
  rw [dite_eq_right (by omega), dite_eq_left h2]

end GlobalTheory.SeeConjChar.AtConj

open GlobalTheory.SeeConjChar GlobalTheory.SeeConjChar.AtConj

theorem GlobalTheory.SeeConjChar.resT_cP_argT : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → ∀ β : GL (Fin (Yc D 0).rank) (EAf D), IsFrame β (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → (∀ PP ∈ R.Pg, RedIs β PP (flagAt X h PP)) → ∀ PP ∈ R.Pg, ∀ κ : GA D (Yc D 0), finE (Yc D 0) κ ∈ St β → ((iotaX X h).toMulEquiv κ).2 ∈ X.K2 → GlobalTheory.SeeConjChar.resT (GlobalTheory.IdemSupport.cP PP) (GlobalTheory.SeeConjChar.argT X h (finE (Yc D 0) κ)) = GlobalTheory.SeeConjChar.conjRes PP (∑ i, ∑ j, if symEdge D.R.rS D.R.k i j then ((GlobalTheory.SeeConjChar.wB D.R.rS D.R.k (GlobalTheory.SeeConjChar.sideAt X h PP) i j : ℤ) : kP PP) * ((upperLeftBlock (r_le_Y (D := D) 0) (redFn β PP (finE (Yc D 0) κ)) : GL (Fin D.R.r) (kP PP)).val i j) else 0) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F X h hL hGrp β hβ hred PP hP κ hS hK2
  classical
  have hn : (Yc D 0).rank = 2 * D.R.rS + D.R.k + 1 := by
    have e := X.n_eq
    rw [h] at e
    have e2 := Formalism.L2.DIV.ranks_r_sym D
    change (Formalism.L2.SG.InstExistsPf.instOf D).n = _
    omega
  have hrn : D.R.r = (Yc D 0).rank := by
    have e := X.n_eq
    rw [h] at e
    change D.R.r = (Formalism.L2.SG.InstExistsPf.instOf D).n
    omega
  have hK : ((iotaX X h).toMulEquiv κ).2 ∈ X.B.I.Kset := (Formalism.L2.SG.Closed.level_subgroup_properties X).2.1 _ hK2
  have hU : upperLeftBlock (r_le_Y (D := D) 0) (redFn β PP (finE (Yc D 0) κ)) ∈ unip (kP PP) D.R.r :=
    unipCol_le _ _ _ (((GlobalTheory.T.mem_K2_iff_upperLeftBlock_reductions R F X h hL hGrp β hβ hred κ hK hS).1 hK2) PP hP)
  have hMinv : (finE (Yc D 0) κ)⁻¹ ∈ St β := inv_mem hS
  have hredinv : redFn β PP (finE (Yc D 0) κ)⁻¹ = (redFn β PP (finE (Yc D 0) κ))⁻¹ := extendOne_inv _ hS
  have hC : ∀ a j, hT X h (flagAt X h PP j) (Matrix.mulVec (finE (Yc D 0) κ).val (pairAt X h PP a)) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧
      resT (GlobalTheory.IdemSupport.cP PP) (hT X h (flagAt X h PP j) (Matrix.mulVec (finE (Yc D 0) κ).val (pairAt X h PP a))) =
        conjRes PP ((sgnD D.R.rS D.R.k a : kP PP) * ((redFn β PP (finE (Yc D 0) κ))⁻¹).val a j) := by
    intro a j
    have c1 := GlobalTheory.T.residue_conjugatePlace_hermitianForm_adjoint X h PP κ (flagAt X h PP j) (pairAt X h PP a)
    have c2 := GlobalTheory.T.residue_otherInstanceForm_frameStabilizer_mulVec X h β PP (flagAt X h PP) (hred PP hP) _ hMinv (pairAt X h PP a) (GlobalTheory.T.otherInstanceForm_flagPairing_integral_on_frameLattice X h β hβ PP a) j
    refine ⟨c1.1.2 c2.1, ?_⟩
    rw [c1.2, c2.2, hredinv]
    congr 1
    simp only [GlobalTheory.T.residue_otherInstanceForm_flagPairing_eq_signedDelta R X h hL PP hP a, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

  let fF : Fin D.R.rS → Fin (Yc D 0).rank := fun a => ⟨2 * D.R.rS + D.R.k - a.1, by have := a.2; omega⟩
  let fN : Fin D.R.rS → Fin (Yc D 0).rank := fun a =>
    ⟨if a.1 + 1 < D.R.rS then 2 * D.R.rS + D.R.k - (a.1 + 1) else D.R.rS + D.R.k, by have := a.2; split_ifs <;> omega⟩
  let gB : Fin D.R.k → Fin (Yc D 0).rank := fun i => ⟨D.R.rS + D.R.k - 1 - i.1, by have := i.2; omega⟩
  have hF : ∀ a, f0T X h a = flagAt X h PP (fF a) := by
    intro a
    have ha := a.2
    have e : (fF a).1 = 2 * D.R.rS + D.R.k - a.1 := rfl
    have h1 : D.R.rS + D.R.k < (fF a).1 := by omega
    have h2 : (fF a).1 < 2 * D.R.rS + D.R.k + 1 := by omega
    unfold flagAt
    split_ifs <;> rw [flagV_f _ _ _ _ _ h1 h2] <;> congr 1 <;> ext <;> simp only [e] <;> omega
  have hNx : ∀ a, Formalism.L2.SG.HidaSetting.nxt (e0T X h) (z0T X h) a = pairAt X h PP (fN a) := by
    intro a
    have ha := a.2
    have e : (fN a).1 = if a.1 + 1 < D.R.rS then 2 * D.R.rS + D.R.k - (a.1 + 1) else D.R.rS + D.R.k := rfl
    unfold Formalism.L2.SG.HidaSetting.nxt
    by_cases hlt : a.1 + 1 < D.R.rS
    · rw [dite_eq_left hlt]
      rw [if_pos hlt] at e
      have h1 : D.R.rS + D.R.k < (fN a).1 := by omega
      have h2 : (fN a).1 < 2 * D.R.rS + D.R.k + 1 := by omega
      unfold pairAt
      split_ifs <;> rw [flagV_f _ _ _ _ _ h1 h2] <;> congr 1 <;> ext <;> simp only [e] <;> omega
    · rw [dite_eq_right hlt]
      rw [if_neg hlt] at e
      unfold pairAt
      split_ifs <;> rw [symmetricFlagBasisVectors_apply_middle _ _ _ _ _ e]
  have hBd : GlobalTheory.SeeConjChar.sideAt X h PP ≠ true → ∀ i, bwdT X h i = flagAt X h PP (gB i) := by
    intro hs i
    have hi := i.2
    have e : (gB i).1 = D.R.rS + D.R.k - 1 - i.1 := rfl
    have hs' : ¬ GlobalTheory.StdFrames.cpt PP (ewT X h) = 1 := by simpa [GlobalTheory.SeeConjChar.sideAt] using hs
    unfold flagAt
    rw [if_neg hs', flagV_b _ _ _ _ _ (by omega) (by omega)]
    congr 1; ext; simp only [e, Fin.val_rev]; omega
  have hBw : GlobalTheory.SeeConjChar.sideAt X h PP ≠ true → ∀ i : Fin D.R.k, bwT X h i = pairAt X h PP (gB i) := by
    intro hs i
    have hi := i.2
    have e : (gB i).1 = D.R.rS + D.R.k - 1 - i.1 := rfl
    have hs' : ¬ GlobalTheory.StdFrames.cpt PP (ewT X h) = 1 := by simpa [GlobalTheory.SeeConjChar.sideAt] using hs
    unfold pairAt
    rw [if_neg hs', flagV_b _ _ _ _ _ (by omega) (by omega)]
    congr 1; ext; simp only [e, Fin.val_rev]; omega

  have hfterm : ∀ a, hT X h (f0T X h a) (Matrix.mulVec (finE (Yc D 0) κ).val (Formalism.L2.SG.HidaSetting.nxt (e0T X h) (z0T X h) a)) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧
      resT (GlobalTheory.IdemSupport.cP PP) (hT X h (f0T X h a) (Matrix.mulVec (finE (Yc D 0) κ).val (Formalism.L2.SG.HidaSetting.nxt (e0T X h) (z0T X h) a))) =
        conjRes PP ((sgnD D.R.rS D.R.k (fN a) : kP PP) * ((redFn β PP (finE (Yc D 0) κ))⁻¹).val (fN a) (fF a)) := by
    intro a
    rw [hF a, hNx a]
    exact hC _ _
  have hbterm : ∀ i : Fin D.R.k, (if hi : i.1 + 1 < D.R.k then hT X h (bwdT X h i) (Matrix.mulVec (finE (Yc D 0) κ).val (bwT X h ⟨i.1 + 1, hi⟩)) else 0) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧
      resT (GlobalTheory.IdemSupport.cP PP) (if hi : i.1 + 1 < D.R.k then hT X h (bwdT X h i) (Matrix.mulVec (finE (Yc D 0) κ).val (bwT X h ⟨i.1 + 1, hi⟩)) else 0) =
        conjRes PP (if hi : i.1 + 1 < D.R.k then (if GlobalTheory.SeeConjChar.sideAt X h PP then 0 else (sgnD D.R.rS D.R.k (gB ⟨i.1 + 1, hi⟩) : kP PP) * ((redFn β PP (finE (Yc D 0) κ))⁻¹).val (gB ⟨i.1 + 1, hi⟩) (gB i)) else 0) := by
    intro i
    by_cases hi : i.1 + 1 < D.R.k
    · rw [dite_eq_left hi, dite_eq_left hi]
      by_cases hs : GlobalTheory.SeeConjChar.sideAt X h PP = true
      · rw [if_pos hs]
        obtain ⟨h1, h2⟩ := GlobalTheory.T.residue_conjugatePlace_hermitian_dualBasis_stabiliser_eq_zero X h β hβ PP hs _ hS i ⟨i.1 + 1, hi⟩
        exact ⟨h1, by rw [h2, map_zero]⟩
      · rw [if_neg hs, hBd hs i, hBw hs ⟨i.1 + 1, hi⟩]
        exact hC _ _
    · rw [dite_eq_right hi, dite_eq_right hi]
      exact ⟨zero_mem _, by rw [map_zero, resT_zero]⟩
  unfold argT

  rw [resT_add _ (sum_mem fun a _ => (hfterm a).1) (sum_mem fun i _ => (hbterm i).1), resT_sum _ _ (fun a => (hfterm a).1),
  resT_sum _ _ (fun i => (hbterm i).1), Finset.sum_congr rfl fun a _ => (hfterm a).2,
  Finset.sum_congr rfl fun i _ => (hbterm i).2, ← map_sum, ← map_sum, ← map_add]
  congr 1
  exact GlobalTheory.T.conjugateResidue_flagTerms_reindex_symmetricEdge (r_le_Y (D := D) 0) D.R.rS D.R.k hn hrn _ hU (GlobalTheory.SeeConjChar.sideAt X h PP) fF fN gB (fun a => rfl) (fun a => rfl) (fun i => rfl)
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ResidueConjugatePlaceCharacterArgumentSignedSumStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead


theorem _root_.GlobalTheory.T.residue_conjugatePlace_characterArgument_signedSum : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → ∀ β : GL (Fin (Yc D 0).rank) (EAf D), IsFrame β (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → (∀ PP ∈ R.Pg, RedIs β PP (flagAt X h PP)) → ∀ PP ∈ R.Pg, ∀ κ : GA D (Yc D 0), finE (Yc D 0) κ ∈ St β → ((iotaX X h).toMulEquiv κ).2 ∈ X.K2 → GlobalTheory.SeeConjChar.resT (GlobalTheory.IdemSupport.cP PP) (GlobalTheory.SeeConjChar.argT X h (finE (Yc D 0) κ)) = GlobalTheory.SeeConjChar.conjRes PP (∑ i, ∑ j, if symEdge D.R.rS D.R.k i j then ((GlobalTheory.SeeConjChar.wB D.R.rS D.R.k (GlobalTheory.SeeConjChar.sideAt X h PP) i j : ℤ) : kP PP) * ((upperLeftBlock (r_le_Y (D := D) 0) (redFn β PP (finE (Yc D 0) κ)) : GL (Fin D.R.r) (kP PP)).val i j) else 0) := by
  first | exact @GlobalTheory.SeeConjChar.resT_cP_argT | exact GlobalTheory.SeeConjChar.resT_cP_argT | (intros; apply GlobalTheory.SeeConjChar.resT_cP_argT <;> assumption)
end
end
