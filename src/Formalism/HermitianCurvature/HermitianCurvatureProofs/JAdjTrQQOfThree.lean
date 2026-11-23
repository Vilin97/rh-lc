module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddOp
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDGaugeQQAsm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDQQ
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGroupAdjCut
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJALocCC
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStableAdjComm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGCut
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SlicesFiniteRegularityBuilt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGroupAdjPair
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStable2
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.cut_JA_LocLemmas
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellHermitian
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStableGerm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJALocToolsAgree
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJALocToolsTheta
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDJDJComm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PositiveOrbitOpen
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJALocDone
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJALocOpAdjProof
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAAsm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStable

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGACutGraded

section

@[expose] public section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA.GA

theorem graded_truncation_action_holds : GACutGraded := by
  refine ⟨2, by norm_num, ?_⟩
  intro k r Wp Wq _ _ _ _ _ _ Bs χ₀ hχ ε A Bg F hε hBg hF hFg
  obtain ⟨δ, -, hcut, -⟩ := Formalism.FourierDecayAlt.P.JCTx6.Lev0.isCutG_div hχ hε
  exact Formalism.FourierDecayAlt.P.CutMP.JA.gcut_graded Bs.z Bs.z' (fun x => χ₀ (x / ε)) (δ * ε) hcut
    (by linarith) hF hFg

end Formalism.FourierDecayAlt.P.CutMP.JA.GA

end
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGroupAdj

section

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutMP.JA

theorem jAGroupAdj_of_jComm (h : GA.GAJComm) : JAGroupAdj :=
  GA.jAGroupAdj_of_leaves GA.graded_truncation_action_holds h GA.group_action_pairing_holds

end Formalism.FourierDecayAlt.P.CutMP.JA
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGroupAdjJComm

section

@[expose] public section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA.GA

open NumberField Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem gAJComm_of_thetaJ (hT : LT.ThetaJ) : GAJComm := by
  refine ⟨12, 0, by norm_num, le_rfl, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v Θ d Bg hd hBg hΘ _hCoef η F _hη hFs hFg _hFsupp
    U J hU hJ hagree x hx hxU
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  have hTT : (D.parOf S v).TT = Tz S.G.k S.G.r (T v).base.z * Tz S.G.k S.G.r (T v).base.z' := by
    rw [hPl.2.2.2.1, hPl.2.2.2.2.1]; rfl
  have hBg0 : 0 ≤ Bg := le_trans (by simp) hBg

  have hAg := LT.agreement_on_domain_holds S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) (T v).base J F U hJ
    (fun q hq hqU => hagree q ⟨hq.1, by rw [hTT]; exact hq.2⟩ hqU)
  set V : Set (B.Mat S.G.k S.G.r) := Q.OmPlus S.G.k S.G.r (T v).base.z (T v).base.z' ∩
    (fun g => Gf S.G.k S.G.r (T v).base.z (T v).base.z' g) ⁻¹' U with hVdef
  have hVo : IsOpen V := (Formalism.FourierDecayAlt.P.PositiveOrbitOpen.omPlus_open _ _).inter
    (hU.preimage (Formalism.FourierDecayAlt.P.PositiveOrbitOpen.gf_cont _ _))
  have hJV : ∀ y ∈ V, y ∈ B.GV S.G.k S.G.r → J y = B.JF (T v).base F y := fun y hy hyG =>
    hAg y ⟨hyG, hy.1⟩ hy.2
  have hq : x ∈ JF.QDom S.G.k S.G.r (T v).base.z (T v).base.z' := ⟨hx.1, by rw [← hTT]; exact hx.2⟩
  have hg0 := Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom (T v).base hq
  have hg0V : B.gq (T v).base x ∈ V := ⟨hg0.2, hxU⟩

  have hJck : B.CkOn ⊤ (JF.Om S.G.k S.G.r (T v).base.z (T v).base.z') J :=
    Formalism.FourierDecayAlt.P.CutMP.jdc_ckOn_om _ _ hJ.1
  set UU : Set (B.Mat S.G.k S.G.r) := JF.Om S.G.k S.G.r (T v).base.z (T v).base.z' ∩ V with hUUdef
  have hUU : UU ⊆ JF.Om S.G.k S.G.r (T v).base.z (T v).base.z' := Set.inter_subset_left
  have hCkF : B.CkOn (B.opOrder Θ : ℕ∞) UU (B.JF (T v).base F) := by
    intro g₀ hg₀
    obtain ⟨U₁, f', hU₁, hgU₁, hc, he⟩ := hJck g₀ hg₀.1
    refine ⟨U₁ ∩ V, f', hU₁.inter hVo, ⟨hgU₁, hg₀.2⟩, (hc.mono Set.inter_subset_left).of_le ?_, ?_⟩
    · exact_mod_cast le_top
    · intro g hg hgG
      rw [← hJV g hg.2 hgG]
      exact he g hg.1 hgG
  have hg0UU : B.gq (T v).base x ∈ UU := ⟨hg0, hg0V⟩

  have hThr : Formalism.FourierDecayAlt.P.WeakThresholdClauses.WeakDominationThreshold S.G.k S.G.r
      (B.AB S.G.k S.G.r + 12 * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r ^ 2 +
          6 * (S.G.r : ℝ) * ((B.opOrder Θ : ℝ) + 5) + d + 2 * Bg * ((B.opOrder Θ : ℝ) + 5) -
        Bg * ((B.opOrder Θ : ℕ) : ℝ)) (B.opOrder Θ) := by
    have hAB : (0 : ℝ) ≤ B.AB S.G.k S.G.r := by unfold B.AB; positivity
    have hr : (0 : ℝ) ≤ S.G.r := Nat.cast_nonneg _
    have ho : (0 : ℝ) ≤ (B.opOrder Θ : ℝ) := Nat.cast_nonneg _
    apply Formalism.FourierDecayAlt.P.CutMP.jdc_thrW (B.opOrder Θ) _ (B.AB S.G.k S.G.r + 30 * (S.G.r : ℝ) + d +
      Bg * ((B.opOrder Θ : ℝ) + 10)) (by positivity)
    linarith
  obtain ⟨hT1, hT2⟩ := hT S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) (T v).base Θ _ F UU hThr hΘ.1 hΘ.2 hFs
    (hFg (B.opOrder Θ)) hUU hCkF

  have hg0G : B.gq (T v).base x ∈ B.GV S.G.k S.G.r := hg0.1
  refine ⟨?_, ?_⟩
  · rw [← hT1 _ hg0]
    unfold B.opApply
    congr 1
    apply List.map_congr_left
    intro Tm _
    rw [Formalism.FourierDecayAlt.P.CutMP.JA.FFS.rw_local Tm.word Tm.word_lie hVo hJV _ hg0V hg0G]
  · rw [← hT2 _ hg0UU]
    unfold B.opAdj
    congr 1
    apply List.map_congr_left
    intro Tm _
    rw [Formalism.FourierDecayAlt.P.CutMP.JA.FFS.rw_local Tm.word.reverse
      (fun X hX => Tm.word_lie X (List.mem_reverse.1 hX)) hVo
      (f := fun y => Tm.coefAdj y (J y)) (f' := fun y => Tm.coefAdj y (B.JF (T v).base F y))
      (fun y hy hyG => by simp only [hJV y hy hyG]) _ hg0V hg0G]

theorem gAJComm_of_adjComm (hAC : Formalism.FourierDecayAlt.P.CutMP.JA.FFS.AdjComm) : GAJComm :=
  gAJComm_of_thetaJ (LT.thetaJ_of_adjComm hAC)

end Formalism.FourierDecayAlt.P.CutMP.JA.GA

end
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAAdjDone

section

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutMP.JA

theorem local_adjoint_transfer_holds : JALocAdj := jALocAdj_of_adjComm FFS.adjoint_commutation_holds

theorem local_class_transfer_holds : JALocCC := jALocCC_of_op local_operator_transfer_holds local_adjoint_transfer_holds

theorem group_action_commutation_holds : GA.GAJComm := GA.gAJComm_of_adjComm FFS.adjoint_commutation_holds

theorem group_adjoint_transfer_holds : JAGroupAdj := jAGroupAdj_of_jComm group_action_commutation_holds

end Formalism.FourierDecayAlt.P.CutMP.JA
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAQQOpen

section

@[expose] public section

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA

open Formalism.FourierDecayAlt.P.CutMP

theorem jAdjTrQQ_of_open (h1 : JDHatOpQQ) (h7 : JABddOpQQ) (h11 : JAStarOp) (h12 : JAGroupAdj) (h13 : JALocCC) :
    JAdjTrQQ :=
  jAdjTrQQ_of_leaves quadratic_assembly_holds h1 h7 h11 h12 h13 smooth_forms_stability_holds

end Formalism.FourierDecayAlt.P.CutMP.JA
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.JAdjTrQQOfThree

section

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutMP.JA

theorem jAdjTrQQ_of_three (h1 : JDHatOpQQ) (h7 : JABddOpQQ) (h11 : JAStarOp) : JAdjTrQQ :=
  jAdjTrQQ_of_open h1 h7 h11 group_adjoint_transfer_holds local_class_transfer_holds

end Formalism.FourierDecayAlt.P.CutMP.JA
end
end
