module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.BunExists
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BSlotD
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ReductionMemUnipSymOfFlagCongruencesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ResidueCoordinatesInFrameLinearStabiliserStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BSlotD
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagGLConjApply
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteReal.AutomorphicEvaluation
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.NatCastKPZero
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentLevelMovesDualVectorUpper

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead
open GlobalTheory.SeeConjGroup Formalism.L2.SG.HidaSetting
open scoped Matrix

namespace GlobalTheory.SeeConjBwd


open Formalism.L2.SG.Pf.BunEx.Unip Formalism.L2.SG.Pf.unitaryCongruence in
theorem bwd_move : ∀ (I : AutInst) (g : ℕ) {r k : ℕ} (e0 f0 : Fin r → VA I) (z0 : VA I) (bw bwd : Fin k → VA I) (ew : I.E ⊗[I.F] Af I.F), Formalism.L2.SG.Pf.BunEx.Unip.FH I g e0 f0 z0 bw bwd ew → ∀ x : I.Gf, x ∈ I.Kset → K2cong I g e0 z0 bw x → ∀ j : Fin k, (I.fmat x - 1) *ᵥ bwd j ∈ Formalism.L2.SG.Pf.unitaryCongruence.Mo I g (Set.range e0 ∪ bwd '' {l | j < l}) := by
  intro I g r k e0 f0 z0 bw bwd ew h x hx hcx j
  have hm := h.mem
  have hcx' := Formalism.L2.SG.Pf.unitaryCongruence.cong_inv I g e0 z0 bw hx hcx
  have hw : (I.fmat x - 1) *ᵥ bwd j ∈ I.Lf := K_sub_mv I hx (hm.2.2 j).2
  refine Formalism.L2.SG.Pf.BunEx.Unip.mem_Mo_of (Formalism.L2.SG.Pf.BunEx.Unip.exp h _ hw) ?_
  set w := (I.fmat x - 1) *ᵥ bwd j with hwdef
  unfold Formalism.L2.SG.Pf.BunEx.Unip.Rc
  refine add_mem (add_mem (sub_mem (add_mem ?_ ?_) ?_) ?_) ?_
  · exact span_Mo (sumSpan I _ _ _ (fun a _ => hA_int I (hm.1 a).2 hw)
      (fun a _ => Or.inl ⟨a, rfl⟩))
  · refine Formalism.L2.SG.Pf.unitaryCongruence.mL_Mo I (sumZ I g _ _ _ (fun a _ => ?_) (fun a _ => (hm.1 a).2))
    rw [hwdef, Formalism.L2.SG.Pf.BunEx.Unip.adj]
    refine Zleft I g (hm.2.2 j).2 ?_ (hcx'.1 a)
    rintro _ ⟨c, -, rfl⟩
    exact ((h.W j).2.2 c).2.2.1
  · refine Formalism.L2.SG.Pf.unitaryCongruence.mL_Mo I (Zv I g ?_ hm.2.1)
    rw [hwdef, Formalism.L2.SG.Pf.BunEx.Unip.adj]
    refine Zleft I g (hm.2.2 j).2 ?_ hcx'.2.1
    rintro _ ⟨c, rfl⟩
    exact ((h.W j).2.2 c).2.2.1
  · refine Formalism.L2.SG.Pf.unitaryCongruence.mL_Mo I (sumZ I g _ _ _ (fun i _ => ?_) (fun i _ => (hm.2.2 i).1))
    have e : hA I (bwd i) w = 0 := by
      rw [hwdef, Matrix.sub_mulVec, Matrix.one_mulVec, hA_sub_right, bdbd h, sub_zero, h.bwd_w i,
        h.bwd_w j, Matrix.mulVec_smul]
      exact hA_sew I h.orth _ _
    rw [e]; exact Z_zero I g
  · refine Submodule.sum_mem _ fun i _ => ?_
    by_cases hji : j < i
    · exact span_Mo (smul_span I (hA_int I (hm.2.2 i).1 hw) (Or.inr ⟨i, hji, rfl⟩))
    · refine Formalism.L2.SG.Pf.unitaryCongruence.mL_Mo I (Zv I g ?_ (hm.2.2 i).2)
      rw [hwdef, Formalism.L2.SG.Pf.BunEx.Unip.adj]
      refine Zleft I g (hm.2.2 j).2 ?_ (hcx'.2.2 i)
      rintro _ (⟨c, rfl⟩ | ⟨l, hl, rfl⟩)
      · exact ((h.W j).2.2 c).2.2.1
      · have hl' : l.1 < i.1 := hl
        have hlj : j ≠ l := fun e => hji (by rw [e]; exact hl')
        have := Zsym (h.dual j l)
        rw [if_neg hlj, map_zero, sub_zero] at this
        exact this

end GlobalTheory.SeeConjBwd
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentLevelMovesDualVectorUpperStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead
open GlobalTheory.SeeConjGroup Formalism.L2.SG.HidaSetting
open scoped Matrix


theorem _root_.GlobalTheory.T.unipotentLevel_moves_dualVector_upper : ∀ (I : AutInst) (g : ℕ) {r k : ℕ} (e0 f0 : Fin r → VA I) (z0 : VA I) (bw bwd : Fin k → VA I) (ew : I.E ⊗[I.F] Af I.F), Formalism.L2.SG.Pf.BunEx.Unip.FH I g e0 f0 z0 bw bwd ew → ∀ x : I.Gf, x ∈ I.Kset → K2cong I g e0 z0 bw x → ∀ j : Fin k, (I.fmat x - 1) *ᵥ bwd j ∈ Formalism.L2.SG.Pf.unitaryCongruence.Mo I g (Set.range e0 ∪ bwd '' {l | j < l}) := by
  first | exact @GlobalTheory.SeeConjBwd.bwd_move | exact GlobalTheory.SeeConjBwd.bwd_move | (intros; apply GlobalTheory.SeeConjBwd.bwd_move <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.CongruencesReductionMemSymmetricUnipotent

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead
open GlobalTheory.SeeConjGroup Formalism.L2.SG.HidaSetting
open scoped Matrix

namespace GlobalTheory.SeeConjGroup

theorem congr_red_mem_unipSym : ∀ {D : D7} (g : ℕ) (e0 f0 : Fin D.R.rS → VA (II D)) (z0 : VA (II D)) (bw bwd : Fin D.R.k → VA (II D)) (ew : EAf D), Formalism.L2.SG.Pf.BunEx.Unip.FH (II D) g e0 f0 z0 bw bwd ew → ∀ (β : GL (Fin (Yc D 0).rank) (EAf D)) (PP : Pl D.host.E) (w : Bool), IsFrame β (II D).L → LocAt g e0 f0 z0 bw bwd ew β PP w → ∀ (x : (II D).Gf) (M : GL (Fin (Yc D 0).rank) (EAf D)), x ∈ (II D).Kset → (II D).fmat x = M.val → M ∈ St β → K2cong (II D) g e0 z0 bw x → upperLeftBlock (r_le_Y (D := D) 0) (redFn β PP M) ∈ unipSym (kP PP) D.R.r D.R.rS D.R.k := by
  intro D g e0 f0 z0 bw bwd ew hF β PP w hβ hL x M hx hM hSt hc
  have hred := GlobalTheory.T.residueCoordinatesInFrame_linear_stabiliser β (II D).L hβ PP
  have hLf : ∀ v, v ∈ (II D).Lf → v ∈ Formalism.L2.Herm.hatL (F := ↥D.host.F) (E := D.host.E) (II D).L := by
    intro v hv
    have e := Formalism.IndefR.Eqv.lamAf_eq_hatL (V := Yc D 0) (II D).L
    exact (Set.ext_iff.mp e v).mp hv
  have hint : ∀ i : Fin D.R.k, ew ∈ IntAf (II D).F (II D).E ∧ sigA (II D) ew ∈ IntAf (II D).F (II D).E := by
    intro i
    obtain ⟨t, ht, he⟩ := hF.dual i i
    obtain ⟨t', ht', he'⟩ := Formalism.L2.SG.Pf.BunEx.Unip.Zsym (hF.dual i i)
    simp only [if_pos (Eq.refl i), ↓reduceIte] at he he'
    have h1 := Formalism.L2.SG.Pf.unitaryCongruence.hA_int (II D) (hF.mem.2.2 i).2 (hF.mem.2.2 i).1
    have h2 := Formalism.L2.SG.Pf.unitaryCongruence.hA_int (II D) (hF.mem.2.2 i).1 (hF.mem.2.2 i).2
    have hg : ((g : (II D).E ⊗[(II D).F] Af (II D).F)) ∈ IntAf (II D).F (II D).E := natCast_mem _ g
    constructor
    · have e1 : ew = hA (II D) (bwd i) (bw i) - (g : (II D).E ⊗[(II D).F] Af (II D).F) * t := by
        rw [← he]; exact (sub_sub_cancel _ _).symm
      rw [e1]; exact sub_mem h1 (mul_mem hg ht)
    · have e1 : sigA (II D) ew = hA (II D) (bw i) (bwd i) - (g : (II D).E ⊗[(II D).F] Af (II D).F) * t' := by
        rw [← he']; exact (sub_sub_cancel _ _).symm
      rw [e1]; exact sub_mem h2 (mul_mem hg ht')
  cases w
  ·
    have hR : RedIs β PP (flagV D.R.rS D.R.k (Yc D 0).rank e0 f0 (fun i => bwd (Fin.rev i)) z0) := hL.2.2.2
    refine GlobalTheory.T.reduction_mem_unipSym_of_flag_congruences g e0 f0 z0 (fun i => bwd (Fin.rev i)) bw β PP hβ hL.1 hR ?_ M hSt ?_ ?_ ?_ ?_
    · intro i
      refine ⟨(hF.mem.2.2 i).1, ?_⟩
      have hi : ew ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := (hint i).1
      have hs := hred.2.1 ⟨ew, hi⟩ (bw i) (hLf _ (hF.mem.2.2 i).1)
      have h0 := hL.2.1 hi
      simp only [Bool.false_eq_true, if_false] at h0
      rw [h0, zero_smul] at hs
      rw [hF.bw_w i]; exact hs
    · intro a; rw [← hM]; exact hc.1 a
    · rw [← hM]; exact hc.2.1
    · intro i
      rw [← hM]
      have hb := GlobalTheory.T.unipotentLevel_moves_dualVector_upper (II D) g e0 f0 z0 bw bwd ew hF x hx hc (Fin.rev i)
      have hsub : Set.range e0 ∪ bwd '' {l | Fin.rev i < l} ⊆
          Set.range e0 ∪ Set.range bw ∪ (fun j => bwd (Fin.rev j)) '' {j | j.1 < i.1} := by
        rintro v (hv | ⟨l, hl, rfl⟩)
        · exact Or.inl (Or.inl hv)
        · refine Or.inr ⟨Fin.rev l, ?_, by simp⟩
          have hl' : (Fin.rev i).1 < l.1 := hl
          simp only [Fin.val_rev] at hl'
          show (Fin.rev l).1 < i.1
          simp only [Fin.val_rev]; omega
      exact Formalism.L2.SG.Pf.unitaryCongruence.Mo_mono (II D) hsub hb
    · intro b
      rw [← hM]
      have hf := Formalism.L2.SG.Pf.BunEx.Unip.F1 hF hx hc b
      have hsub : Set.range e0 ∪ {z0} ∪ Set.range bw ∪ Set.range bwd ∪ f0 '' {c | b < c} ⊆
          Set.range e0 ∪ {z0} ∪ Set.range (fun j => bwd (Fin.rev j)) ∪ Set.range bw ∪ f0 '' {c | b < c} := by
        rintro v ((((hv | hv) | hv) | hv) | hv)
        · exact Or.inl (Or.inl (Or.inl (Or.inl hv)))
        · exact Or.inl (Or.inl (Or.inl (Or.inr hv)))
        · exact Or.inl (Or.inr hv)
        · obtain ⟨j, rfl⟩ := hv
          exact Or.inl (Or.inl (Or.inr ⟨Fin.rev j, by simp⟩))
        · exact Or.inr hv
      exact Formalism.L2.SG.Pf.unitaryCongruence.Mo_mono (II D) hsub hf
  ·
    have hR : RedIs β PP (flagV D.R.rS D.R.k (Yc D 0).rank e0 f0 bw z0) := hL.2.2.2
    refine GlobalTheory.T.reduction_mem_unipSym_of_flag_congruences g e0 f0 z0 bw bwd β PP hβ hL.1 hR ?_ M hSt ?_ ?_ ?_ ?_
    · intro i
      refine ⟨(hF.mem.2.2 i).2, ?_⟩
      have hi : sigA (II D) ew ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := (hint i).2
      have hs := hred.2.1 ⟨sigA (II D) ew, hi⟩ (bwd i) (hLf _ (hF.mem.2.2 i).2)
      have h0 := hL.2.2.1 hi
      simp only [if_true] at h0
      rw [h0, zero_smul] at hs
      rw [hF.bwd_w i]; exact hs
    · intro a; rw [← hM]; exact hc.1 a
    · rw [← hM]; exact hc.2.1
    · intro i
      rw [← hM]
      have hsub : Set.range e0 ∪ bw '' {j | j.1 < i.1} ⊆ Set.range e0 ∪ Set.range bwd ∪ bw '' {j | j.1 < i.1} :=
        Set.union_subset_union_left _ Set.subset_union_left
      exact Formalism.L2.SG.Pf.unitaryCongruence.Mo_mono (II D) hsub (hc.2.2 i)
    · intro b
      rw [← hM]
      exact Formalism.L2.SG.Pf.BunEx.Unip.F1 hF hx hc b

end GlobalTheory.SeeConjGroup
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.CongruencesReductionMemSymmetricUnipotentStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead
open GlobalTheory.SeeConjGroup Formalism.L2.SG.HidaSetting
open scoped Matrix


theorem _root_.GlobalTheory.T.congruences_reduction_mem_symmetricUnipotent : ∀ {D : D7} (g : ℕ) (e0 f0 : Fin D.R.rS → VA (II D)) (z0 : VA (II D)) (bw bwd : Fin D.R.k → VA (II D)) (ew : EAf D), Formalism.L2.SG.Pf.BunEx.Unip.FH (II D) g e0 f0 z0 bw bwd ew → ∀ (β : GL (Fin (Yc D 0).rank) (EAf D)) (PP : Pl D.host.E) (w : Bool), IsFrame β (II D).L → LocAt g e0 f0 z0 bw bwd ew β PP w → ∀ (x : (II D).Gf) (M : GL (Fin (Yc D 0).rank) (EAf D)), x ∈ (II D).Kset → (II D).fmat x = M.val → M ∈ St β → K2cong (II D) g e0 z0 bw x → upperLeftBlock (r_le_Y (D := D) 0) (redFn β PP M) ∈ unipSym (kP PP) D.R.r D.R.rS D.R.k := by
  first | exact @GlobalTheory.SeeConjGroup.congr_red_mem_unipSym | exact GlobalTheory.SeeConjGroup.congr_red_mem_unipSym | (intros; apply GlobalTheory.SeeConjGroup.congr_red_mem_unipSym <;> assumption)
end
end
