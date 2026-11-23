module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGVanish
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqFam
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalNongenericBoundRecordFamily
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormChainLemmas
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LieAveraging.NonRelCharCHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RCocompactPfFinal
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.UnipotentInLevelSubgroup
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FormRelHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqClassHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqSteps
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.KExpCut
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.BlockEndMinorsOfCell
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StepNormOneOfLeaves
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
import Mathlib.Tactic.Basify
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
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LeadingMinorIntegrality
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGPinLoc
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LeadingMinors
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.NormGramAtOrigin
public import Formalism.PeriodIntegrals.NormGramAtOrigin

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqNormOne

section

@[expose] public section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.BesselShellMomentBounds Formalism.HermitianLatticeCounting.ExpansionTerms Formalism.L2.SG.RowsConc
  Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps

namespace Formalism.L2.SG.NGCut.LeadingMinorIntegrality.Gen

attribute [local instance] Formalism.BasicNotions.Host.cmStar


open Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.NGData Formalism.L2.SG.NGCut in
theorem stepNormOneG_of
    (hOV : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Formalism.L2.SG.TermOp.KExpCut.OOVanish (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') (X := X))
    (hAt : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word)
      (t : Formalism.L2.SG.TermDef.Term D u u' (X.Fu u) (Y.what₂ u)), t.G ≠ 0 → t.relevant → ∃ w, t.atPt w) :
    StepNormOneG := by
  intro Cg cb Cw cT CT C0
  refine ⟨0, 0, fun C' Cl _ _ D large₂ X Y u _ νL νB ng γ hγ => ?_⟩
  obtain ⟨c, ν, t, ht, hv, -, hpt, -⟩ := hγ
  have hG : t.toTerm.G ≠ 0 := by
    intro h
    apply ht.1
    show Gt t = 0
    have h' : t.G = 0 := h
    simp [Gt, h']
  have hrel : t.toTerm.relevant := by
    by_contra hr
    apply hv
    have h0 : OOt t = 0 := hOV D X Y u u t hr
    show vec (Y.cs u) (Y.cs u) (Y.FN u) (Y.FN u) t = 0
    unfold vec ampN
    rw [h0]
    simp
    rfl
  obtain ⟨w, hw⟩ := hAt D X Y u u t.toTerm hG hrel
  have hat := Formalism.L2.SG.PairVal.ptOf_spec t.toTerm ⟨w, hw, hrel⟩
  obtain ⟨F', ⟨hP, -⟩, hGv, hcell⟩ := hat
  have hrow := (Y.rowsOK u).1 t.toTerm.lam t.toTerm.mem
  have hun := hrow.2.1.2.1
  have hz := hrow.2.1.2.2.1.1
  have hX := hrow.2.2
  have hz' := hP.1.1
  have hX' := hP.2.2.2
  have hF : ∀ b, frame (lf D (X.Fu u)) b ∈ t.toTerm.lam := PtPf.frame_mem _ hz hX
  have hF' : ∀ b, frame F' b ∈ t.toTerm.lam := PtPf.frame_mem _ hz' hX'
  rw [← hpt]
  show 1 ≤ NGPt D.host.rdE ((Tu D u : ℕ) * (Tu D u : ℕ)) (toPts (Formalism.L2.SG.PairVal.ptOf t.toTerm)) ∧
    1 ≤ NDPt D.host.rdE (toPts (Formalism.L2.SG.PairVal.ptOf t.toTerm))
  have hlead : ∀ q, q ≤ D.R.rS + 1 → ∃ o ∈ dI D ^ (q * (2 * D.R.rS + 1 - q)),
      (o : D.host.E) = leadingPrincipalMinor (ptMat (Formalism.L2.SG.PairVal.ptOf t.toTerm)) q := fun q hq => by
    obtain ⟨o, ho, e⟩ := lead_mem hun (lf D (X.Fu u)) F' hz hX hz' hX' q hq
    exact ⟨o, ho, e.trans (lead_cell _ _ hcell q).symm⟩
  constructor
  · have hGeq := gpt_eq (T := Tu D u) (T' := Tu D u) (lf D (X.Fu u)) F' _ hcell
    obtain ⟨o1, ho1, e1⟩ := hlead (D.R.rS + 1) le_rfl
    obtain ⟨o0, ho0, e0⟩ := hlead D.R.rS (Nat.le_succ _)
    obtain ⟨o1', ho1', e1'⟩ := star_mem_pow _ o1 ho1
    obtain ⟨o0', ho0', e0'⟩ := star_mem_pow _ o0 ho0
    have ex1 : (D.R.rS + 1) * (2 * D.R.rS + 1 - (D.R.rS + 1)) + (D.R.rS + 1) * (2 * D.R.rS + 1 - (D.R.rS + 1)) =
        2 * D.R.rS * (D.R.rS + 1) := by
      rw [show 2 * D.R.rS + 1 - (D.R.rS + 1) = D.R.rS by omega]; ring
    have ex0 : D.R.rS * (2 * D.R.rS + 1 - D.R.rS) + D.R.rS * (2 * D.R.rS + 1 - D.R.rS) =
        2 * D.R.rS * (D.R.rS + 1) := by
      rw [show 2 * D.R.rS + 1 - D.R.rS = D.R.rS + 1 by omega]; ring
    have hm1 : o1 * o1' ∈ dI D ^ (2 * D.R.rS * (D.R.rS + 1)) := by
      rw [← ex1, pow_add]; exact Ideal.mul_mem_mul ho1 ho1'
    have hm0 : o0 * o0' ∈ dI D ^ (2 * D.R.rS * (D.R.rS + 1)) := by
      rw [← ex0, pow_add]; exact Ideal.mul_mem_mul ho0 ho0'
    refine one_le_NGPt _ _ (o1 * o1' - (((Tu D u : ℕ) * (Tu D u : ℕ) : ℕ) : 𝓞 D.host.E) * (o0 * o0'))
      (Ideal.sub_mem _ hm1 (Ideal.mul_mem_left _ _ hm0)) ?_ (by rw [hGeq]; exact hGv)
    have e1a : algebraMap (𝓞 D.host.E) D.host.E o1 = leadingPrincipalMinor (ptMat (Formalism.L2.SG.PairVal.ptOf t.toTerm)) (D.R.rS + 1) := e1
    have e0a : algebraMap (𝓞 D.host.E) D.host.E o0 = leadingPrincipalMinor (ptMat (Formalism.L2.SG.PairVal.ptOf t.toTerm)) D.R.rS := e0
    have e1b : algebraMap (𝓞 D.host.E) D.host.E o1' = star (algebraMap (𝓞 D.host.E) D.host.E o1) := e1'
    have e0b : algebraMap (𝓞 D.host.E) D.host.E o0' = star (algebraMap (𝓞 D.host.E) D.host.E o0) := e0'
    show algebraMap (𝓞 D.host.E) D.host.E _ = _
    unfold GPt
    rw [dlast_eq, dr_eq, map_sub, map_mul, map_mul, map_mul, map_natCast, e1b, e0b, e1a, e0a]
  · refine one_le_NDPt _ fun a => ?_
    have hj : endIdx (toPts (Formalism.L2.SG.PairVal.ptOf t.toTerm)) a ≤ D.R.rS + 1 :=
      (toPts (Formalism.L2.SG.PairVal.ptOf t.toTerm)).1.sizeUpTo_le _
    obtain ⟨o, ho, e⟩ := hlead _ hj
    have hE := PtPf.blockEndMinors_of_cell _ (PtPf.zhatOM_isIntegral _ _ hun hF hF') _ hcell
    exact ⟨o, ho, by rw [e, endMin_eq], (hE a).2⟩


open Formalism.L2.SG.TermOp.Vanish in
theorem stepNormOneG_of_leaves (hA : AvgCore) (hU : GinfUnimod) (hN : NLamNinf) (hC : ChiTrivialC) (hG : PsiInfChar)
    (h1 : RClosedC) (h2 : RODiscreteC) (h3 : RCocompactC) (h4 : NonRelCharC)
    (hAt : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)
      (t : Formalism.L2.SG.TermDef.Term D u u' (X.Fu u) (Y.what₂ u)), t.G ≠ 0 → t.relevant → ∃ w, t.atPt w) :
    Formalism.L2.SG.Pf.MainEqSteps.StepNormOneG := by
  refine stepNormOneG_of ?_ hAt
  intro D X Y u u'
  unfold Formalism.L2.SG.TermOp.KExpCut.OOVanish
  intro t ht
  exact ooVanish_of hA hU hN hC hG h1 h2 h3 h4 Y t ht

end Formalism.L2.SG.NGCut.LeadingMinorIntegrality.Gen
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqPoints

section

@[expose] public section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.NGCut.PtPf
  Formalism.L2.SG.Pf.MainEqSteps

namespace Formalism.L2.SG.Pf.MainEqPoints

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem stepPointsG_of
    (hOV : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Formalism.L2.SG.TermOp.KExpCut.OOVanish (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') (X := X))
    (hAt : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word)
      (t : Formalism.L2.SG.TermDef.Term D u u' (X.Fu u) (Y.what₂ u)), t.G ≠ 0 → t.relevant → ∃ w, t.atPt w) :
    StepPointsG := by
  intro Cg cb Cw cT CT C0
  refine ⟨0, 0, fun C' Cl _ _ D large₂ X Y u _ νL νB ng γ hγ => ?_⟩
  obtain ⟨c, ν, t, ht, hv, -, hpt, -⟩ := hγ
  have hG : t.toTerm.G ≠ 0 := by
    intro h
    apply ht.1
    show Gt t = 0
    have h' : t.G = 0 := h
    simp [Gt, h']
  have hrel : t.toTerm.relevant := by
    by_contra hr
    apply hv
    have h0 : OOt t = 0 := hOV D X Y u u t hr
    show vec (Y.cs u) (Y.cs u) (Y.FN u) (Y.FN u) t = 0
    unfold vec ampN
    rw [h0]
    simp
    rfl
  obtain ⟨w, hw⟩ := hAt D X Y u u t.toTerm hG hrel
  have hat := Formalism.L2.SG.PairVal.ptOf_spec t.toTerm ⟨w, hw, hrel⟩
  obtain ⟨F', ⟨hP, -⟩, -, hcell⟩ := hat
  have hrow := (Y.rowsOK u).1 t.toTerm.lam t.toTerm.mem
  have hF : ∀ b, frame (lf D (X.Fu u)) b ∈ t.toTerm.lam := frame_mem _ hrow.2.1.2.2.1.1 hrow.2.2
  have hF' : ∀ b, frame F' b ∈ t.toTerm.lam := frame_mem _ hP.1.1 hP.2.2.2
  have hE := blockEndMinors_of_cell _ (zhatOM_isIntegral _ _ hrow.2.1.2.1 hF hF') _ hcell
  rw [← hpt]
  exact hE

open Formalism.L2.SG.TermOp.Vanish in
theorem stepPointsG_of_leaves (hA : AvgCore) (hU : GinfUnimod) (hN : NLamNinf) (hC : ChiTrivialC) (hG : PsiInfChar)
    (h1 : RClosedC) (h2 : RODiscreteC) (h3 : RCocompactC) (h4 : NonRelCharC)
    (hAt : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word)
      (t : Formalism.L2.SG.TermDef.Term D u u' (X.Fu u) (Y.what₂ u)), t.G ≠ 0 → t.relevant → ∃ w, t.atPt w) :
    StepPointsG := by
  refine stepPointsG_of ?_ hAt
  intro D X Y u u'
  unfold Formalism.L2.SG.TermOp.KExpCut.OOVanish
  intro t ht
  exact ooVanish_of hA hU hN hC hG h1 h2 h3 h4 Y t ht

end Formalism.L2.SG.Pf.MainEqPoints
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.EqualWordsNonGenericEstimatesChain

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna

namespace GlobalTheory

theorem closed_steps_gram_vectors : NondegenerateGramTuple := by
  intro D X
  have hn : 2 * D.R.rS + 2 ≤ X.B.I.n := by
    rw [X.n_eq]
    have h1 := D.R.rS_two
    have h2 := D.R.r_eq
    have h3 := D.R.k_ge
    omega
  have hH : ∀ i j, star (X.B.I.J j i) = X.B.I.J i j := fun i j => by
    have := congrFun (congrFun X.B.I.J_herm i) j
    simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply] at this
    exact this
  obtain ⟨X0, hX⟩ := exists_nondegenerate X.B.I.E X.B.I.n (2 * D.R.rS + 2) hn X.B.I.J hH X.B.I.J_det
  refine ⟨X0, ?_⟩
  have e : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.gramE X.B.I.cm.sig X.B.I.J X0 =
      PI.NormGramAtOrigin.gram (starRingEnd _) X.B.I.J X0 := by
    ext a b; rfl
  rw [e]; exact hX

theorem closed_steps_equal_words :
    PN.NGChain ∧ StepClassG ∧ StepPointsG ∧ StepNormOneG ∧ TieOfCtx ∧ StepPinExists ∧
      StepTermVanishG ∧ Formalism.L2.SG.NGVanish.FormNGC ∧
      (Formalism.L2.SG.Pf.MainEqFam.StepFamG → StepLocGenPinnedG) := by
  have hPts : StepPointsG :=
    Formalism.L2.SG.Pf.MainEqPoints.stepPointsG_of_leaves Formalism.L2.SG.Closed.AvgCore_holds
      Formalism.L2.SG.Pf.ginfUnimod_holds Formalism.L2.SG.Pf.nLamNinf_holds Formalism.L2.SG.Closed.ChiTrivialC_holds
      Formalism.L2.SG.Pf.psiInfChar_holds Formalism.L2.SG.Pf.rClosedC_holds Formalism.L2.SG.Pf.roDiscreteC_holds
      Formalism.L2.SG.TermOp.Vanish.rational_cocompact_holds Formalism.L2.SG.NonRelPf.nonRelCharC_holds
      (fun D X Y u u' => Formalism.L2.SG.LeadingMinorsNonvanishing.atSomeAll_holds D X Y u u')
  have hNorm : StepNormOneG :=
    Formalism.L2.SG.NGCut.LeadingMinorIntegrality.Gen.stepNormOneG_of_leaves Formalism.L2.SG.Closed.AvgCore_holds
      Formalism.L2.SG.Pf.ginfUnimod_holds Formalism.L2.SG.Pf.nLamNinf_holds Formalism.L2.SG.Closed.ChiTrivialC_holds
      Formalism.L2.SG.Pf.psiInfChar_holds Formalism.L2.SG.Pf.rClosedC_holds Formalism.L2.SG.Pf.roDiscreteC_holds
      Formalism.L2.SG.TermOp.Vanish.rational_cocompact_holds Formalism.L2.SG.NonRelPf.nonRelCharC_holds
      (fun D X Y u u' => Formalism.L2.SG.LeadingMinorsNonvanishing.atSomeAll_holds D X Y u u')
  have hLoc : ∀ D, Formalism.MainNotions.NonGenericAndKTwoTheorems.Conclusion1 D 39 := fun D =>
    ((GlobalTheory.local_nongeneric_bound_record_family 39 le_rfl).2.1 D).1
  exact ⟨Formalism.FourierDecayAlt.P.norm_chain, Formalism.L2.SG.Pf.stepClassG_holds, hPts, hNorm,
    tieOfCtx_of closed_steps_gram_vectors, Formalism.L2.SG.NGPin.stepPinExists,
    Formalism.L2.SG.Pf.MainEqVanish.stepTermVanishG_of_form Formalism.L2.SG.Pf.formGC_holds,
    Formalism.L2.SG.Pf.formNGC_holds,
    fun hFam => Formalism.L2.SG.Pf.stepLocGenPinnedG_of_loc (Formalism.L2.SG.Pf.stepLocPinnedG_of_fam hLoc hFam)⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.EqualWordsNonGenericEstimatesChainStatement

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna

theorem _root_.GlobalTheory.T.equalWords_nonGeneric_estimates_chain : PN.NGChain ∧ StepClassG ∧ StepPointsG ∧ StepNormOneG ∧ TieOfCtx ∧ StepPinExists ∧ StepTermVanishG ∧ Formalism.L2.SG.NGVanish.FormNGC ∧ (Formalism.L2.SG.Pf.MainEqFam.StepFamG → StepLocGenPinnedG) := by
  first | exact @GlobalTheory.closed_steps_equal_words | exact GlobalTheory.closed_steps_equal_words | (intros; apply GlobalTheory.closed_steps_equal_words <;> assumption)
end
end
