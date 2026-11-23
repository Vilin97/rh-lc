module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CorankOneIsEquivalenceOnRow
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.StepLocGenPinnedGP
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RelCOfOcc
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AmpQNotEqAmpG
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CorankRelation
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FamGen1
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsPointOfGenericCorankOne
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Formalism.SharpRestriction.CuspSpanNormBounds.LatticeGluingRadicals
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Algebra.Order.Star.Int
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DifferentLocalIdentityFamiliesLemmaH
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FamilyGenericMassPositiveBoundedProof
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FamilyGroupSumFactorsRowWeightAmplitudeProof
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FamilyLocalObjectsExistAtTermsProof
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FamilyRowWeightSumUnfoldingIdentityProof
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalMassLeGenericMassConstNine
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalNongenericBoundRecordFamily
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormChainLemmas
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FormRelHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NormalCount

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CorankOneIsEquivalenceNonzeroGramTerms

section

@[expose] public section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.TermLoc Formalism.L2.SG.NGLocModel Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna Formalism.L2.SG.Pf.MainEqLoc Formalism.L2.SG.Pf.MainEqFam GlobalTheory.SnFam GlobalTheory.Core.One
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.One


open Formalism.L2.SG.NGCut.CorankRelation in
theorem corankOne_isEquivalence_nonzeroGram_terms : CorankOneIsEquivalenceOnRow := by
  intro D X Y u u' _hT
  have hdim := Formalism.L2.SG.Corank.finrank_VS D
  have hGv : ∀ t ∈ (Y.tO u u').nzSet, Gval (lf D (X.Fu u)) t.frame ≠ 0 := by
    intro t ht h
    apply ht
    show Formalism.L2.SG.TermOp.Gt t = 0
    unfold Formalism.L2.SG.TermOp.Gt
    rw [if_pos ((Formalism.L2.SG.Pf.SatGram.gterm_G Y t).trans h)]
  have hlat : ∀ t : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u'),
      Submodule.IsFullLattice D.host.E t.lam := fun t => ((Y.rowsOK u).1 t.lam t.mem).1.1
  have hLF : ∀ t : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u'),
      IsLift t.lam (lf D (X.Fu u)) := fun t => ((Y.rowsOK u).1 t.lam t.mem).2.1.2.2.1
  have hLt : ∀ t : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u'), IsLift t.lam t.frame :=
    fun t => t.rep.2.2.2.2.1
  refine ⟨fun t ht => ?_, fun t ht t' ht' hr h1 => ?_, fun t ht t' ht' t'' ht'' hr1 hr2 h1 h2 => ?_⟩
  · show Formalism.L2.SG.TermOp.s0T t t = 1
    unfold Formalism.L2.SG.TermOp.s0T
    rw [if_pos ⟨rfl, rfl⟩, mul_inv_cancel]
    exact (s0_eq_one_iff_Th_eq_Hp D.R.k hdim t.lam (hlat t) _ t.frame t.frame 1 (hLF t) (hLt t) (hGv t ht)).2
      (Th_one _ _ _)
  · have hlam : t.lam = t'.lam := congrArg (fun r => (r.1 : Submodule (𝓞 D.host.E) (VS D).V)) hr
    have hlam' : t.lam' = t'.lam' := congrArg (fun r => (r.2.1 : Submodule (𝓞 D.host.E) (VS D).V)) hr
    have h1' : Formalism.L2.SG.TermOp.s0T t t' = 1 := h1
    show Formalism.L2.SG.TermOp.s0T t' t = 1
    unfold Formalism.L2.SG.TermOp.s0T at h1' ⊢
    rw [if_pos ⟨hlam, hlam'⟩] at h1'
    rw [if_pos ⟨hlam.symm, hlam'.symm⟩, ← hlam]
    have hth := (s0_eq_one_iff_Th_eq_Hp D.R.k hdim t.lam (hlat t) _ t.frame t'.frame _ (hLF t) (hLt t)
      (hGv t ht)).1 h1'
    have hL' : IsLift t.lam t'.frame := by rw [hlam]; exact hLt t'
    have hsym := Th_symm D.R.k hdim t.lam (hlat t) _ t.frame t'.frame (t'.lin * t.lin⁻¹) (hLF t) (hLt t) hL'
      (hGv t ht) (hGv t' ht') (frame_mem_iff t t') hth
    have hinv : (t'.lin * t.lin⁻¹)⁻¹ = t.lin * t'.lin⁻¹ := by group
    rw [hinv] at hsym
    exact (s0_eq_one_iff_Th_eq_Hp D.R.k hdim t.lam (hlat t) _ t'.frame t.frame _ (hLF t) hL' (hGv t' ht')).2 hsym
  · have hl1 : t.lam = t'.lam := congrArg (fun r => (r.1 : Submodule (𝓞 D.host.E) (VS D).V)) hr1
    have hl1' : t.lam' = t'.lam' := congrArg (fun r => (r.2.1 : Submodule (𝓞 D.host.E) (VS D).V)) hr1
    have hl2 : t'.lam = t''.lam := congrArg (fun r => (r.1 : Submodule (𝓞 D.host.E) (VS D).V)) hr2
    have hl2' : t'.lam' = t''.lam' := congrArg (fun r => (r.2.1 : Submodule (𝓞 D.host.E) (VS D).V)) hr2
    have h1' : Formalism.L2.SG.TermOp.s0T t t' = 1 := h1
    have h2' : Formalism.L2.SG.TermOp.s0T t' t'' = 1 := h2
    show Formalism.L2.SG.TermOp.s0T t t'' = 1
    unfold Formalism.L2.SG.TermOp.s0T at h1' h2' ⊢
    rw [if_pos ⟨hl1, hl1'⟩] at h1'
    rw [if_pos ⟨hl2, hl2'⟩, ← hl1] at h2'
    rw [if_pos ⟨hl1.trans hl2, hl1'.trans hl2'⟩]
    have hL' : IsLift t.lam t'.frame := by rw [hl1]; exact hLt t'
    have hth1 := (s0_eq_one_iff_Th_eq_Hp D.R.k hdim t.lam (hlat t) _ t.frame t'.frame _ (hLF t) (hLt t)
      (hGv t ht)).1 h1'
    have hth2 := (s0_eq_one_iff_Th_eq_Hp D.R.k hdim t.lam (hlat t) _ t'.frame t''.frame _ (hLF t) hL'
      (hGv t' ht')).1 h2'
    have htr := Th_trans t.lam _ t.frame t'.frame t''.frame (t'.lin * t.lin⁻¹) (t''.lin * t'.lin⁻¹)
      (fun x hx => (frame_mem_iff t' t'' x).1 hx) hth1 hth2
    have hmul : (t''.lin * t'.lin⁻¹) * (t'.lin * t.lin⁻¹) = t''.lin * t.lin⁻¹ := by group
    rw [hmul] at htr
    exact (s0_eq_one_iff_Th_eq_Hp D.R.k hdim t.lam (hlat t) _ t.frame t''.frame _ (hLF t) (hLt t) (hGv t ht)).2 htr

end GlobalTheory.Core.One
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GenericTermsPointsAgreeGroupSumsCorankOne

section

@[expose] public section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.TermLoc Formalism.L2.SG.NGLocModel Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna Formalism.L2.SG.Pf.MainEqLoc Formalism.L2.SG.Pf.MainEqFam GlobalTheory.SnFam GlobalTheory.Core.One
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.One

theorem genericTerms_points_agree_groupSums_corankOne : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) (νL νB : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : PN.Pts D.host.E D.R.rS → ℝ), (∀ γ, PN.IsPt (genT (scT (Y.tO u u))) (NOf1 Y u νL νB ng) γ ↔ PN.IsPt (genT (Y.tO u u)) (NOfG Y u νL νB ng) γ) ∧ (∀ γ, PN.IsPt (genT (scT (Y.tO u u))) (NOf1 Y u νL νB ng) γ ↔ HasPt Y u u (Y.tO u u).genSet γ) ∧ (∀ c γ ν, PN.grp (genT (scT (Y.tO u u))) (NOf1 Y u νL νB ng) c γ ν = grpF Y u u (Y.tO u u).genSet (cls1 Y u) c γ ν) ∧ ((∀ t ∈ (Y.tO u u).genSet, J2of Y u u νL (ptPN t) = 0 → (Y.tO u u).vec t = 0) → PN.AmpInput (genT (scT (Y.tO u u))) (NOf1 Y u νL νB ng)) := by
  intro D X Y u νL νB ng
  have hs : (genT (scT (Y.tO u u))).ngSet = (Y.tO u u).genSet := genT_ngSet _
  have hs' : (genT (Y.tO u u)).ngSet = (Y.tO u u).genSet := genT_ngSet _
  have hA : ∀ γ, PN.IsPt (genT (scT (Y.tO u u))) (NOf1 Y u νL νB ng) γ ↔ HasPt Y u u (Y.tO u u).genSet γ := by
    intro γ
    constructor
    · rintro ⟨c, ν, t, ht, hv, -, hp, -⟩
      rw [hs] at ht
      exact ⟨t, ht, hv, hp⟩
    · rintro ⟨t, ht, hv, hp⟩
      exact ⟨cls1 Y u t, nmlOf Y u u t, t, hs ▸ ht, hv, rfl, hp, rfl⟩
  have hB : ∀ γ, PN.IsPt (genT (Y.tO u u)) (NOfG Y u νL νB ng) γ ↔ HasPt Y u u (Y.tO u u).genSet γ := by
    intro γ
    constructor
    · rintro ⟨c, ν, t, ht, hv, -, hp, -⟩
      rw [hs'] at ht
      exact ⟨t, ht, hv, hp⟩
    · rintro ⟨t, ht, hv, hp⟩
      exact ⟨clsG Y u t, nmlOf Y u u t, t, hs' ▸ ht, hv, rfl, hp, rfl⟩
  have hG : ∀ c γ ν, PN.grp (genT (scT (Y.tO u u))) (NOf1 Y u νL νB ng) c γ ν =
      grpF Y u u (Y.tO u u).genSet (cls1 Y u) c γ ν := by
    intro c γ ν
    unfold PN.grp grpF
    rw [hs]
    rfl
  refine ⟨fun γ => (hA γ).trans (hB γ).symm, hA, hG, ?_⟩
  intro h
  have hJ : ∀ γ, 0 ≤ J2of Y u u νL γ := fun γ => J2of_nonneg Y u u νL γ
  have hV : ∀ c γ ν, J2of Y u u νL γ = 0 → grpF Y u u (Y.tO u u).genSet (cls1 Y u) c γ ν = 0 := by
    intro c γ ν h0
    unfold grpF
    have hz : ∀ t, ((Y.tO u u).genSet ∩ {t | cls1 Y u t = c ∧ ptPN t = γ ∧ nmlOf Y u u t = ν}).indicator
        (Y.tO u u).vec t = 0 := by
      intro t
      by_cases ht : t ∈ (Y.tO u u).genSet ∩ {t | cls1 Y u t = c ∧ ptPN t = γ ∧ nmlOf Y u u t = ν}
      · rw [Set.indicator_apply, if_pos ht]
        exact h t ht.1 (by rw [ht.2.2.1]; exact h0)
      · rw [Set.indicator_apply, if_neg ht]
    simp only [hz, tsum_zero]
  refine ⟨fun c γ ν => ?_, hJ, fun c γ ν => ?_⟩
  · show 0 ≤ a2F Y u u (Y.tO u u).genSet (cls1 Y u) νL c γ ν
    unfold a2F
    exact div_nonneg (by positivity) (hJ γ)
  · rw [hG]
    show ‖grpF Y u u (Y.tO u u).genSet (cls1 Y u) c γ ν‖ ^ 2 ≤
      a2F Y u u (Y.tO u u).genSet (cls1 Y u) νL c γ ν * J2of Y u u νL γ
    unfold a2F
    by_cases h0 : J2of Y u u νL γ = 0
    · rw [hV c γ ν h0]; simp
    · rw [div_mul_cancel₀ _ h0]

end GlobalTheory.Core.One
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowGen1POfSteps

section

@[expose] public section

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.TermLoc Formalism.L2.SG.NGLocModel Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna Formalism.L2.SG.Pf.MainEqLoc Formalism.L2.SG.Pf.MainEqFam GlobalTheory.SnFam GlobalTheory.Core.One
open Formalism.L2.SG.Pf

namespace GlobalTheory.Core.One

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem scT_sc_genSet {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (X : PB.Terms τ Rw I H H₁) :
    (scT X).sc (scT X).genSet = X.one X.genSet := by
  ext p
  simp only [PB.Terms.one, PB.Terms.sc, PB.Terms.allPairs, Set.mem_setOf_eq]
  exact ⟨fun ⟨a, b, _⟩ => ⟨a, b⟩, fun ⟨a, b⟩ => ⟨a, b, trivial⟩⟩

theorem rowGen1P_of_steps (hCh : PN.NGChain) (hC : StepClass1) (hN : StepNormals1) (hP : StepPointsG)
    (hO : StepNormOneG) (hTi : TieOfCtx) (hB : StepChoiceConstantsC) (hE : StepPinExists) (hV : StepTermVanishG)
    (hL : StepLoc1) (hTB : GlobalTheory.SnPos.StepThmBGP) : RowGen1P := by
  intro Cg cb Cw cT CT C0 hcb hcT
  obtain ⟨C1, C0n, CSt, hCSt, a₀, b₀, hL2⟩ := hL Cg cb Cw cT CT C0
  obtain ⟨CB, hCB, a₁, b₁, hTB2⟩ := hTB Cg cb Cw cT CT C0 hcb hcT (C1 + C0n + 38)
  obtain ⟨Cgs, CTs, hCg, hCT, a₂, b₂, hS2⟩ := sizes_of_hypotheses Cg cb Cw cT CT C0
  obtain ⟨a₃, b₃, hN2⟩ := hN Cg cb Cw cT CT C0
  obtain ⟨a₄, b₄, hP2⟩ := hP Cg cb Cw cT CT C0
  obtain ⟨a₅, b₅, hH2⟩ := stepHeightG_of_normOne hO Cg cb Cw cT CT C0
  obtain ⟨a₆, b₆, hB2⟩ := hB Cg cb Cw cT CT C0
  obtain ⟨a₇, b₇, hT2⟩ := hTi Cg cb Cw cT CT C0
  obtain ⟨a₈, b₈, hE2⟩ := hE Cg cb Cw cT CT C0
  obtain ⟨a₉, b₉, hV2⟩ := hV Cg cb Cw cT CT C0
  obtain ⟨Cn, hCn, hK⟩ := rowGenJoint_of hCh meanAmplitudeGeneric_holds C1 C0n (C1 + C0n + 38) CB CSt Cgs CTs
    hCB hCSt hCg hCT le_rfl
  refine ⟨Cn, hCn, max a₀ (max a₁ (max a₂ (max a₃ (max a₄ (max a₅ (max a₆ (max a₇ (max a₈ a₉)))))))),
    max b₀ (max b₁ (max b₂ (max b₃ (max b₄ (max b₅ (max b₆ (max b₇ (max b₈ b₉)))))))),
    fun C' Cl e1 e2 D large₂ X Y u hTies hH0 hSt hT ha => ?_⟩
  simp only [max_le_iff] at e1 e2
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, p9⟩ := e1
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, q8, q9⟩ := e2
  have hc : Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u := ⟨hH0, hSt, hT⟩
  obtain ⟨hb, X0, ψ, hTie⟩ := hT2 C' Cl p7 q7 D large₂ X Y u u hc
  obtain ⟨sd, C, Th, F0, what₂, vR, Q, i0, i0', νq, Irat, Ire, hBk⟩ :=
    hB2 C' Cl p6 q6 D large₂ X Y u u hc hb X0 ψ hTie
  have hBk' : MassDataAdmissible X Y u u (bkU X hb Y u u X0 ψ sd C Th vR Q i0 i0' νq) (Irat * kapU D) (Ire * kapU D) :=
    massDataValid_unscale (kapU_pos D) hBk
  obtain ⟨ν, hν⟩ := hE2 C' Cl p8 q8 D large₂ X Y u u hc
  obtain ⟨s, hs1, hs0, hsb, hLe⟩ :=
    hL2 C' Cl p0 q0 D large₂ X Y u hc hb X0 ψ hTie sd C Th F0 what₂ vR Q i0 i0' νq _ _ hBk' ν hν
  have hSum := hTB2 C' Cl p1 q1 D large₂ X Y u hTies hc hb X0 ψ hTie sd C Th F0 what₂ vR Q i0 i0' νq _ _ hBk' ν hν
  generalize bkU X hb Y u u X0 ψ sd C Th vR Q i0 i0' νq = B at hBk' hLe
  have hSz := hS2 C' Cl p2 q2 D large₂ X Y u u hc
  have hrd : 0 < D.host.rdE := by
    obtain ⟨-, -, hrd, -⟩ := hSz
    have hv : 2 * D.host.v = D.host.rdE := by simp only [Formalism.BasicNotions.Host.v]; ring
    rwa [hv] at hrd
  have hb0 : 0 ≤ large₂.sc.b ^ (CSt * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 * D.R.f) :=
    le_trans (sq_nonneg _) (hsb 1)
  obtain ⟨hG, hdd, hNI, hFI⟩ := hBk'
  set ng : PN.Pts D.host.E D.R.rS → ℝ := fun γ => PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f * B.AA * 2 *
      HPt D.host.rdE (X.B.g : ℝ) ((Tu D u : ℕ) * (Tu D u : ℕ)) γ ^ PN.eN D.R.rS *
      nPt D.host.rdE D.R.k ((Tu D u : ℕ) * (Tu D u : ℕ)) γ with hng
  obtain ⟨hPt, -, -, hAmp⟩ := GlobalTheory.Core.One.genericTerms_points_agree_groupSums_corankOne D X Y u (sc s ν) ν ng
  have hVan : ∀ t ∈ (Y.tO u u).genSet, J2of Y u u (sc s ν) (ptPN t) = 0 → (Y.tO u u).vec t = 0 := by
    intro t ht h0
    obtain ⟨g, hg⟩ := J2of_sc Y u u s ν (ptPN t)
    rw [hg] at h0
    have hp : (0 : ℝ) < (s g : ℝ) ^ 2 := by have := hs0 g; positivity
    exact hV2 C' Cl p9 q9 D large₂ X Y u hc ν hν t ht ((mul_eq_zero.1 h0).resolve_left hp.ne')
  have hIn : GenInputs (scT (Y.tO u u)) (NOf1 Y u (sc s ν) ν ng) D.R.f C1 C0n (C1 + C0n + 38) CB large₂.sc.b
      (2 * D.host.v) (X.B.g : ℝ) (((Tu D u : ℕ) : ℝ) * ((Tu D u : ℕ) : ℝ))
      (large₂.sc.b ^ (CSt * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 * D.R.f))
      (PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f * B.AA) 2 (Ire * kapU D) := by
    refine ⟨hC D X Y u hT _ _ _, hAmp hVan, hN2 C' Cl p3 q3 D large₂ X Y u hc _ _ _, ?_,
      localInputG_of_le _ _ _ _ _ hLe (fun γ => rfl), ?_, ?_, ?_, ?_⟩
    · exact fun γ hγ => hP2 C' Cl p4 q4 D large₂ X Y u hc (sc s ν) ν ng γ ((hPt γ).1 hγ)
    · exact fun γ hγ => measureInputG_sc Y u s ν _ hsb ng γ ((hPt γ).1 hγ)
    · exact fun γ _ => ⟨nPt_nonneg _ hrd _ _ γ, le_rfl⟩
    · exact fun γ hγ => hH2 C' Cl p5 q5 D large₂ X Y u hc (sc s ν) ν ng γ ((hPt γ).1 hγ)
    · exact fun S hS => hSum (sc s ν) ng S (fun γ hγ => (hPt γ).1 (hS γ hγ))
  have hcard := Formalism.MainNotions.LatticeGluingRadicals.d_card D
  have key := hK D.host.E (TauC Y u u) _ _ _ _ (scT (Y.tO u u)) D.R.rS D.R.k (Set (TauC Y u u)) (NuC D)
    (NOf1 Y u (sc s ν) ν ng) _ B large₂.sc.b (2 * D.host.v) (X.B.g : ℝ) (((Tu D u : ℕ) : ℝ) * ((Tu D u : ℕ) : ℝ))
    (large₂.sc.b ^ (CSt * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 * D.R.f)) 2 (Irat * kapU D) (Ire * kapU D)
  rw [hcard] at key
  have r := key ha hG hNI hFI (ngSizes_of hSz hb0 le_rfl zero_le_two le_rfl) hIn
  rw [hdd] at r
  unfold PB.Terms.RowMain at r
  rw [scT_sc_genSet] at r
  exact r

end GlobalTheory.Core.One
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepClass1Of

section

@[expose] public section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.TermLoc Formalism.L2.SG.NGLocModel Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna Formalism.L2.SG.Pf.MainEqLoc Formalism.L2.SG.Pf.MainEqFam GlobalTheory.SnFam GlobalTheory.Core.One
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.One

theorem stepClass1_of (h : CorankOneIsEquivalenceOnRow) : StepClass1 := by
  intro D X Y u hc νL νB ng
  obtain ⟨hR, hS, hT⟩ := h D X Y u u hc
  have hsub : ∀ t ∈ (Y.tO u u).genSet, t ∈ (Y.tO u u).nzSet := fun t ht => ht.1
  intro t ht t' ht'
  rw [genT_ngSet] at ht ht'
  change t ∈ (Y.tO u u).genSet at ht
  change t' ∈ (Y.tO u u).genSet at ht'
  have es : (genT (scT (Y.tO u u))).s0 t t' = 1 ↔ (Y.tO u u).s0 t t' = 1 := by
    simp only [genT, scT, and_true]
    by_cases hc : (Y.tO u u).s0 t t' = 1
    · simp [hc]
    · simp [hc]
  show ((scT (Y.tO u u)).rowOf t = (scT (Y.tO u u)).rowOf t' ∧ (genT (scT (Y.tO u u))).s0 t t' = 1) ↔
    cls1 Y u t = cls1 Y u t'
  rw [es]
  change ((Y.tO u u).rowOf t = (Y.tO u u).rowOf t' ∧ (Y.tO u u).s0 t t' = 1) ↔ cls1 Y u t = cls1 Y u t'
  constructor
  · rintro ⟨hr, h1⟩
    have b1 := hS t (hsub t ht) t' (hsub t' ht') hr h1
    ext x
    simp only [cls1, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hx, hrx, hx1⟩
      exact ⟨hx, hrx.trans hr, hT t' (hsub t' ht') t (hsub t ht) x (hsub x hx) hr.symm hrx.symm b1 hx1⟩
    · rintro ⟨hx, hrx, hx1⟩
      exact ⟨hx, hrx.trans hr.symm, hT t (hsub t ht) t' (hsub t' ht') x (hsub x hx) hr hrx.symm h1 hx1⟩
  · intro hc
    have hm : t' ∈ cls1 Y u t' := ⟨ht', rfl, hR t' (hsub t' ht')⟩
    rw [← hc] at hm
    exact ⟨hm.2.1.symm, hm.2.2⟩

end GlobalTheory.Core.One
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepLoc1OfFam

section

@[expose] public section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.TermLoc Formalism.L2.SG.NGLocModel Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna Formalism.L2.SG.Pf.MainEqLoc Formalism.L2.SG.Pf.MainEqFam GlobalTheory.SnFam GlobalTheory.Core.One
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.One

theorem stepLoc1_of_fam (hQ5 : ∀ D : D7, Formalism.MainNotions.NonGenericAndKTwoTheorems.Conclusion1 D 39) (hF : StepFam1) : StepLoc1 := by
  intro Cg cb Cw cT CT C0
  obtain ⟨C0n, CSt, hCSt, a₀, b₀, h2⟩ := hF Cg cb Cw cT CT C0
  refine ⟨39, C0n, CSt, hCSt, a₀, b₀, fun C' Cl e1 e2 D large₂ X Y u hc hb X0 ψ hT sd C Th F0 what₂ vR Q i0 i0' νq
    Irat Ire hBk ν hν => ?_⟩
  obtain ⟨s, hs1, hs0, hsb, hL⟩ := h2 C' Cl e1 e2 D large₂ X Y u hc hb X0 ψ hT sd C Th F0 what₂ vR Q i0 i0' νq Irat
    Ire hBk ν hν
  have hk4 : 4 * D.R.rS + 7 ≤ D.R.k := by
    obtain ⟨⟨hH, _, _⟩, _, _⟩ := hc
    unfold Formalism.MainNotions.S.StandingHypotheses at hH
    dsimp only at hH
    obtain ⟨-, -, h3, h4, -⟩ := hH
    have hm2 := D.R.two_le_m
    obtain ⟨j, hj⟩ := D.R.m_even
    have hmr : 2 * D.R.rS + 2 = D.R.m := by simp only [Formalism.BasicNotions.Ranks.rS]; omega
    have : 2 * D.R.m + 3 ≤ D.R.m ^ 4 := by nlinarith [Nat.pow_le_pow_left hm2 3]
    omega
  have hQ : Formalism.MainNotions.NonGenericAndKTwoTheorems.NonGenericLocalBound D.R.k D.R.rS ((39 : ℕ) : ℝ) := by
    have := hQ5 D hk4
    exact_mod_cast this
  exact ⟨s, hs1, hs0, hsb, localLeG_of_fam _ _ 39 C0n _ (by omega) hQ hL⟩

end GlobalTheory.Core.One
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowGen1POfConstantsAndPoints

section

@[expose] public section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.TermLoc Formalism.L2.SG.NGLocModel Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna Formalism.L2.SG.Pf.MainEqLoc Formalism.L2.SG.Pf.MainEqFam GlobalTheory.SnFam GlobalTheory.Core.One
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.One

theorem rowGen1P_of_siegelWeil_of_points : PI.VolStabS.MassDataS.SWXS → Formalism.L2.SG.NGCut.NormalVectorPairings.NmlLine →
    Formalism.L2.SG.NGCut.NormalVectorPairings.NmlInt → Formalism.L2.SG.NGCut.NormalVectorPairings.NmlSep → StepPointsG → StepNormOneG → TieOfCtx →
    StepChoiceConstantsC → StepPinExists → GlobalTheory.SnPos.StepThmBGP → RowGen1P := by
  intro hSW hLine hInt hSep hPts hN1 hTie hCh hPin hThm
  have hEq : CorankOneIsEquivalenceOnRow := corankOne_isEquivalence_nonzeroGram_terms
  have hFam : FamGen1 := famGen1 hEq
  have hStepFam : StepFam1 :=
    stepFam1_of (fun D hk => GlobalTheory.localMass_le_genericMass_nine D.R.k D.R.rS hk) GlobalTheory.HTieLeaf.main hFam
      GlobalTheory.SnFam.familyRowWeightSumUnfoldingIdentity_proof (GlobalTheory.WeightsFamPf.weightsFam_of hSW) GlobalTheory.FamilyNormRational.familyGroupSumFactorsRowWeightAmplitude GlobalTheory.SnFam.existFam
  have hLoc : StepLoc1 :=
    stepLoc1_of_fam (fun D => ((GlobalTheory.local_nongeneric_bound_record_family 39 le_rfl).2.1 D).1) hStepFam
  have hNml : StepNormals1 :=
    GlobalTheory.Core.One.stepNormals1_of hEq hLine hInt hSep Formalism.L2.SG.NGCut.NormalCount.NormCount_holds hN1
  have hVan : StepTermVanishG :=
    Formalism.L2.SG.Pf.MainEqVanish.stepTermVanishG_of_form (Formalism.L2.SG.Pf.formGC_of_rel Formalism.L2.SG.Pf.formRelC_holds)
  exact rowGen1P_of_steps Formalism.FourierDecayAlt.P.norm_chain (stepClass1_of hEq) hNml hPts hN1 hTie hCh hPin hVan hLoc hThm

end GlobalTheory.Core.One
end
end
