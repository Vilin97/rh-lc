module

public import CompanionTheory.AutomorphicTheory.DiscreteGroupWaves.NFCoreC
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OnePointBasisFundamentalDomainVolume
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ThmBpAtEqOfShiftR
public import Formalism.HermitianCurvature.HerGenC
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutDec
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutMainCpt
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
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormSqLeShifted
public import CompanionTheory.AutomorphicTheory.CompactTopologicalForms.JacobiFieldSquareIntegrable
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFHypS
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutFpmDecay
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFMainS
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopForm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopPtw
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DominatedL2TruncationBoundHolds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftDegreeLemmas
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LimitOfModuleForms
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SlicesFiniteRegularityBuilt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TriangleInequalityAtPlace
public import CompanionTheory.AutomorphicTheory.DiscreteGroupWaves.NFTopFormCpt
public import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.NFHatProdKBS
import Formalism.FormalDegreeBessel.FormalDegreeRatio.BesselUnipotentEquivHolds
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDJDJComm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFApxDom
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.JfBetaAdjCOfLemmaBNorm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PbGermRateLowBOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PsiNormalization
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadJFExists
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WCellMemOmPlus
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CptCopy2
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutBPEqShift
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutMainCpt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopPtw
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSETopFinal

-- Source module: CompanionTheory.AutomorphicTheory.CompactTopologicalForms.FinalS

section

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutBP.CompactFormNormalFormDomination

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

theorem blockGrowthBound_apx_cutF (hA : P5.ThmPActualCpt) {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (p : KB.Pl P Wp Wq) (nn χ : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (Y : Finset ℝ) (K N : ℕ) (Cb : ℝ) (hCb : KB.InDDplus2 P p.l0 p.T.base Cb p.Θ) (hχ : C6.IsCut0 χ)
    (hF : B.CkOn ⊤ (B.GV P.k P.r) F) (hnn : ∀ y, 0 < nn y) :
    ∀ ε : ℝ, 0 < ε → ∀ n : ℕ, TBB.BlockGrowthBound p nn (apx (D.cutF p.T.base χ F ε) n) Y K N := fun _ hε n =>
  block_growth_bound_of_compact_coefCpt hA p nn _ Y K N Cb hCb (cptCoef_apx P p.T.base hχ hF hε n) hnn



end

end Formalism.FourierDecayAlt.P.CutBP.CompactFormNormalFormDomination

namespace Formalism.FourierDecayAlt.P.CutBPEq.CompactFormNormalFormDomination

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TBB Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBP.CompactFormNormalFormDomination MeasureTheory
open scoped ENNReal

noncomputable section


end

end Formalism.FourierDecayAlt.P.CutBPEq.CompactFormNormalFormDomination
end
end

-- Source module: CompanionTheory.AutomorphicTheory.DiscreteGroupWaves.NFDomC

section

@[expose] public section

namespace CompanionTheory.NFCpt

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Filter Topology MeasureTheory

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem nfTopDomAll_of_ptwC (hP : NFDomPtwC) (hJ : NFJCutFF) : NFTopDomAll := by
  intro Cb
  obtain ⟨C1, C₁, H1⟩ := hP Cb
  obtain ⟨C2, H2⟩ := dominated_L2_truncation_bound_holds Cb C₁
  obtain ⟨C3, H3⟩ := domination_measurability_holds Cb
  obtain ⟨C4, H4⟩ := limit_of_module_forms Cb
  refine ⟨max (max C1 C2) (max C3 C4), ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f A₀ p₀ χ Y N hH w hw hN
  have m1 := nfHyp_monoC hH (le_max_of_le_left (le_max_left C1 C2))
  have m2 := nfHyp_monoC hH (le_max_of_le_left (le_max_right C1 C2))
  have m3 := nfHyp_monoC hH (le_max_of_le_right (le_max_left C3 C4))
  have m4 := nfHyp_monoC hH (le_max_of_le_right (le_max_right C3 C4))
  obtain ⟨hχ, hCb, hf, hfA, -, hN2⟩ := hH
  have hid : B.CkOn ⊤ (B.GV P.k P.r) (fun _ : B.Mat P.k P.r => ContinuousLinearMap.id ℂ Wq) := fun g₀ _ =>
    ⟨Set.univ, fun _ => ContinuousLinearMap.id ℂ Wq, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩
  obtain ⟨m, Th, Mb, hMb, hok, hb⟩ := H1 Wp Wq P p p₀ χ Y N w hw hN
  choose hh hhi hhb using fun t => H2 Wp Wq P p f A₀ p₀ χ N m2 (Th t) (hok t)
  refine ⟨eventually_nhdsWithin_of_forall fun ε hε => H3 Wp Wq P p f A₀ p₀ χ Y N m3 w hw hN ε hε,
    fun c => Mb * ∑ t, |hh t c|, (integrable_finsetSum Finset.univ fun t _ => (hhi t).abs).const_mul Mb,
    eventually_nhdsWithin_of_forall fun ε hε => ?_⟩
  have hε' : 0 < ε := hε
  obtain ⟨-, hlim⟩ := H4 Wp Wq P p _ χ ε _ N (cutN P.k P.r) hCb hχ hε' (ckOn_fpm p p₀ hf hid)
    (inCC_fpm_id p p₀ hfA) m4.2.2.2.2.1 (fun _ _ => rfl)
  filter_upwards [ae_all_iff.2 fun n => ae_all_iff.2 fun t => hhb t n] with c hc
  by_cases hc' : D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) ∧ 0 < TBB.Gp p (TBB.bigPt P.r c)
  swap
  · rw [domination_at_zero_holds Wp Wq P p _ w c hc', norm_zero]
    exact mul_nonneg hMb (Finset.sum_nonneg fun t _ => abs_nonneg _)
  have hT : Tendsto (fun n => ‖topD p (apx (D.cutF p.T.base χ
      (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) n) w c‖) atTop
      (𝓝 ‖topD p (D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) w c‖) := by
    refine Tendsto.norm ?_
    unfold topD TBB.Ew TBB.NP
    exact (Complex.continuous_re.tendsto _).comp ((hlim (P.r + 1) w hw.1 hN _ _).const_mul _)
  refine le_of_tendsto' hT fun n => ?_
  set η : ℝ := TBB.Gp p (TBB.bigPt P.r c) / 2 with hη
  have hη0 : 0 < η := half_pos hc'.2
  have hηG : η < D.ptG (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') P.r (TBB.bigPt P.r c) := half_lt_self hc'.2
  set f' : B.Mat P.k P.r → (Wq →L[ℂ] Wp) := fun g => cutN P.k P.r n g • D.cutF p.T.base χ f η g with hf'
  have hcp : KB.CptCoef p.T.base f' := cptCoef_apx P p.T.base hχ hf hη0 n
  obtain ⟨_, -, hnice⟩ := PBL.nice_of_cpt hcp
  have hb' := hb f' A₀ ⟨hχ, hCb, hcp.1, fun m => hnice.2.1 A₀ m, m1.2.2.2.2.1, hN2⟩ hcp
    (hJ Wp Wq P p _ (JCTx6.Link2.ckOn_cutF p.T.base hχ hf η) n) ε hε' c hc'.1 hc'.2
  have eL : D.cutF p.T.base χ (TBBx4.fpm p f' (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε =
      D.cutF p.T.base χ (apx (D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) n) η := by
    funext g
    simp only [hf', apx, D.cutF, TBBx4.fpm, ContinuousLinearMap.smul_comp, smul_smul]
    congr 1
    ring
  have eL' : topD p (D.cutF p.T.base χ (TBBx4.fpm p f' (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) w c =
      topD p (apx (D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) n) w c := by
    rw [eL]
    unfold topD TBB.Ew TBB.NP
    rw [rrTop_cutF_eq p hCb hχ (cptCoef_apx P p.T.base hχ (ckOn_fpm p p₀ hf hid) hε' n).1 hη0 hw.1 _ (Or.inr hηG)]
  rw [eL'] at hb'
  refine hb'.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun t _ => ?_) hMb)
  have eR : TBB.Ew p (fun _ => 1) (B.opApply (Th t) f') (P.r + 1) [] (TBB.bigPt P.r c) =
      TBB.Ew p (fun _ => 1) (B.opApply (Th t) (fun g => cutN P.k P.r n g • f g)) (P.r + 1) [] (TBB.bigPt P.r c) := by
    rw [TBBx2.Tri.Ew_top p _ hc'.1, TBBx2.Tri.Ew_top p _ hc'.1]
    congr 4
    refine vecV_congr_gt _ _ _ _ η (fun g _ hg => ?_) (Or.inr hηG)
    refine JCTx6.Pos.opApply_congr_open (Th t) (O := {x | η < Gf P.k P.r p.T.base.z p.T.base.z' x})
      (isOpen_lt continuous_const (JCx1.contDiff_Gf p.T.base.z p.T.base.z').continuous) (fun x hx => ?_) g hg
    simp only [hf', D.cutF]
    rw [hχ.2.2 _ ((one_le_div hη0).2 (le_of_lt hx))]
    simp
  rw [eR]
  exact (hc n t).trans (le_abs_self _)

theorem nfTopDomAll_of_C (hT : NFTieHatC) (hH : NFHatProdKBS) (hJ : NFJCutFF) : NFTopDomAll :=
  nfTopDomAll_of_ptwC (nfDomPtwC_of_open hT hH) hJ

end

end CompanionTheory.NFCpt
end
end

-- Source module: CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.NFJCutFF

section

@[expose] public section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem jf_mem_ffkb {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (hF : ∀ (A : ℝ) (m : ℕ), B.InCC A m F) :
    B.JF p.T.base F ∈ FFKB p := by
  set Bs := p.T.base
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bs.haarW
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bs.haarN
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bs.haarW'
  have hN := bessel_unipotent_equiv_holds Wp Wq P.k P.r Bs.z Bs.z' cStd Bs.π Bs.π' Bs.μW Bs.μN Bs.μW' F Bs.z_mem Bs.z'_mem
    Bs.haarN.conc (fun n₀ h => Bs.haarN.left n₀ h)
  refine ⟨fun g₀ hg₀ => Formalism.FourierDecayAlt.P5.Rad.jf_smoothLev Bs F hF g₀ ⟨hg₀.1, (CutMP.jdc_om_of _ _ hg₀.1.1 hg₀.2).2⟩, ?_, ?_, ?_⟩
  · intro g _ n hn
    have e := hN g n hn.1 1 WeylGroupFacts.mem_n_one
    rw [Matrix.mul_one, BesselCapelliCommutation.psi_one Bs.z'_mem, mul_one] at e
    exact e
  · intro g _ n hn
    have e := hN g 1 WeylGroupFacts.mem_n_one n hn.1
    rw [Matrix.one_mul, BesselCapelliCommutation.psi_one Bs.z_mem, one_mul] at e
    exact e
  · intro g _ h hh h' hh'
    exact Formalism.FourierDecayAlt.P5.jf_uEquiv Bs F g hh hh'

theorem normal_form_jacobi_cutoff : NFJCutFF := by
  intro Wp Wq _ _ _ _ _ _ P p f hf n
  apply jf_mem_ffkb
  have hcomp : IsCompact {g : B.Mat P.k P.r | B.gN g ≤ 2 * ((n : ℝ) + 1)} := by
    have hcont : Continuous (fun g : B.Mat P.k P.r => B.gN g) := by
      unfold B.gN
      exact Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ =>
        continuous_finsetSum _ fun j _ =>
          Complex.continuous_normSq.comp ((continuous_apply j).comp (continuous_apply i)))
    have hsub : {g : B.Mat P.k P.r | B.gN g ≤ 2 * ((n : ℝ) + 1)}
        ⊆ Metric.closedBall (0 : B.Mat P.k P.r) (2 * ((n : ℝ) + 1)) := by
      intro g hg
      rw [Metric.mem_closedBall, dist_zero_right]
      refine (Matrix.norm_le_iff (by positivity)).mpr fun i j => le_trans ?_ hg
      unfold B.gN
      rw [← Real.sqrt_sq (norm_nonneg (g i j))]
      apply Real.sqrt_le_sqrt
      rw [← Complex.normSq_eq_norm_sq]
      calc Complex.normSq (g i j) ≤ ∑ j', Complex.normSq (g i j') :=
            Finset.single_le_sum (f := fun j' => Complex.normSq (g i j'))
              (fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ j)
        _ ≤ ∑ i', ∑ j', Complex.normSq (g i' j') :=
            Finset.single_le_sum (f := fun i' => ∑ j', Complex.normSq (g i' j'))
              (fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
    exact (isCompact_closedBall _ _).of_isClosed_subset (isClosed_le hcont continuous_const) hsub
  intro A m
  refine Formalism.FourierDecayAlt.P.JFxG.cptInCC_G (Formalism.FourierDecayAlt.P.CutBP.cutN_ckOn hf n) hcomp ?_ A m
  intro g hg hgC
  by_contra hne
  exact hgC (Formalism.FourierDecayAlt.P.FormNormSumIdentities.cutN_supp f n g hg hne)

end Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms
end
end
end

-- Source module: CompanionTheory.AutomorphicTheory.CompactTopologicalForms.FinalC

section

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutBP.CompactFormNormalFormDomination

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

theorem nfTopIdAll_of_dom (h3 : NFTopDomAll) : NFTopIdAll :=
  CompanionTheory.BpCpt.NFId.nfTopIdAll_of_diag (CompanionTheory.NFCpt.top_form_all_compact CutSE.actual_compact_theorem)
    top_pointwise_all_levels_holds h3

theorem nfTopDomAll_of_tieC (hT : CompanionTheory.NFCpt.NFTieHatC) : NFTopDomAll :=
  CompanionTheory.NFCpt.nfTopDomAll_of_C hT LimitNormalForms.normal_form_hat_product_bessel LimitNormalForms.normal_form_jacobi_cutoff


attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
theorem thmBpAt_dom (h3 : NFTopDomAll)
    (Cb C₃ CΛ C₀ : ℝ) (hC₃ : 0 ≤ C₃) (hCΛ : 0 ≤ CΛ) (hC₀ : 1 / 2 ≤ C₀) :
    ∃ C₄ c₃ Cc Cc' Cc'' : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
      [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
      (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b Λ A₀ : ℝ) (p₀ : ℕ) (χ nn : ℝ → ℝ) (Y : Finset ℝ) (K N : ℕ),
      3 ≤ b → 1 ≤ Λ → Λ ≤ b ^ (CΛ * ((2 * P.r + 2 : ℕ) : ℝ)) → 1 ≤ TBB.Tq p →
      (p₀ : ℝ) ≤ C₀ * (3 * ((P.r : ℝ) + 1)) + 1 →
      3 ≤ K → (P.r + 1) * K ≤ N → C6.IsCut0 χ → (∀ y, 0 < nn y) →
      KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A₀ m f) →
      c₃ * ((P.r : ℝ) + 1) ^ 2 * ((P.r : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) + 1) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) →
      Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) →
      Cc' * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) →
      Cc'' * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) →
      N ≤ 2 * p₀ →
      BigCellDerivativeExpansion p f b C₃ (2 * p₀ + 0) →
      TBBx5.WaveGrid p nn Y Λ K N → TBBx5.LiftGrid p nn Y Λ K N →
      LimBd p nn (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) Y N →
      TBB.ThmBpAt p f b C₄ 0 p₀ := by
  have hA : P5.ThmPActualCpt := CutSE.actual_compact_theorem
  obtain ⟨C₄, c₃, Cc, Cc', Cc'', h⟩ := thmBpAt_main4Cpt hA CompanionTheory.NFCpt.top_form_all_compact
    top_pointwise_all_levels_holds h3 (nfTopIdAll_of_dom h3) Cb C₃ CΛ C₀ hC₃ hCΛ hC₀
  refine ⟨C₄, c₃, Cc, Cc', Cc'', ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f b Λ A₀ p₀ χ nn Y K N hb hΛ hΛb hT hp₀ hK hKN hχ hnn hCb hf hfA hth1 hth2 hth3
    hth4 hN2 hexp hWG hLG hBd
  have hid : B.CkOn ⊤ (B.GV P.k P.r) (fun _ : B.Mat P.k P.r => ContinuousLinearMap.id ℂ Wq) := fun g₀ _ =>
    ⟨Set.univ, fun _ => ContinuousLinearMap.id ℂ Wq, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩
  exact h Wp Wq P p f b Λ A₀ p₀ χ nn Y K N hb hΛ hΛb hT hp₀ hK hKN hχ hnn hCb hf hfA hth1 hth2 hth3 hth4 hN2 hexp
    hWG hLG (blockGrowthBound_apx_cutF hA p nn χ _ Y K N Cb hCb hχ (ckOn_fpm p p₀ hf hid) hnn) hBd

end

end Formalism.FourierDecayAlt.P.CutBP.CompactFormNormalFormDomination

namespace Formalism.FourierDecayAlt.P.CutBPEq.CompactFormNormalFormDomination

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TBB Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBP.CompactFormNormalFormDomination MeasureTheory
open scoped ENNReal

noncomputable section


attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
theorem thmBpAt_eqR_dom (h3 : NFTopDomAll)
    (Cb C₃ CΛ C₀ : ℝ) (hC₃ : 0 ≤ C₃) (hCΛ : 0 ≤ CΛ) (hC₀ : 1 / 2 ≤ C₀) :
    ∃ C₄ c₃ Cc Cc' Cc'' : ℝ, ∀ (P : M.Par) (Wp Wq : Type)
      [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
      [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
      (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b : ℝ) (n₀ : ℕ) (S : ShiftAtR p f b n₀)
      (Λ A₀ : ℝ) (p₀ : ℕ) (χ nnp nnm : ℝ → ℝ) (Yp Ym : Finset ℝ) (K N : ℕ),
      3 ≤ b → 1 ≤ Λ → Λ ≤ b ^ (CΛ * ((2 * P.r + 2 : ℕ) : ℝ)) → 1 ≤ Tq p →
      n₀ ≤ 30 * (P.r + 1) ^ 2 + 6 → (p₀ : ℝ) ≤ C₀ * (3 * ((P.r : ℝ) + 1)) + 1 →
      3 ≤ K → (P.r + 1) * K ≤ N → C6.IsCut0 χ → (∀ y, 0 < nnp y) → (∀ y, 0 < nnm y) →
      KB.InDDplus2 (shP P S.up S.up') S.pp.l0 S.pp.T.base Cb S.pp.Θ →
      KB.InDDplus2 (shP P S.um S.um') S.pm.l0 S.pm.T.base Cb S.pm.Θ →
      B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A₀ m f) →
      c₃ * ((P.r : ℝ) + 1) ^ 2 * ((P.r : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) + 1) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) - ((n₀ * (P.r + 1) : ℕ) : ℝ) →
      Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) - ((n₀ * (P.r + 1) : ℕ) : ℝ) →
      Cc' * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) - ((n₀ * (P.r + 1) : ℕ) : ℝ) →
      Cc'' * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) - ((n₀ * (P.r + 1) : ℕ) : ℝ) →
      N ≤ 2 * p₀ →
      BigCellDerivativeExpansion p f b C₃ (2 * p₀ + n₀) →
      TBBx5.WaveGrid S.pp nnp Yp Λ K N → TBBx5.LiftGrid S.pp nnp Yp Λ K N →
      TBBx5.WaveGrid S.pm nnm Ym Λ K N → TBBx5.LiftGrid S.pm nnm Ym Λ K N →
      LimBd S.pp nnp (fpmSh S.pp f S.Ap p₀) Yp N → LimBd S.pm nnm (fpmSh S.pm f S.Am p₀) Ym N →
      ThmBpAt p f b C₄ n₀ p₀ := by
  have hA : P5.ThmPActualCpt := CutSE.actual_compact_theorem
  obtain ⟨C₄, c₃, Cc, Cc', Cc'', h⟩ := thmBpAt_eq_NFRCpt hA CompanionTheory.NFCpt.top_form_all_compact
    top_pointwise_all_levels_holds h3 (nfTopIdAll_of_dom h3) Cb C₃ CΛ C₀ hC₃ hCΛ hC₀
  refine ⟨C₄, c₃, Cc, Cc', Cc'', ?_⟩
  intro P Wp Wq _ _ _ _ _ _ p f b n₀ S Λ A₀ p₀ χ nnp nnm Yp Ym K N hb hΛ hΛb hT hn₀ hp₀ hK hKN hχ hnnp hnnm hDDp
    hDDm hf hfA hth1 hth2 hth3 hth4 hN2 hexp hWGp hLGp hWGm hLGm hBdp hBdm
  exact h P Wp Wq p f b n₀ S Λ A₀ p₀ χ nnp nnm Yp Ym K N hb hΛ hΛb hT hn₀ hp₀ hK hKN hχ hnnp hnnm hDDp
    hDDm hf hfA hth1 hth2 hth3 hth4 hN2 hexp hWGp hLGp hWGm hLGm
    (blockGrowthBound_apx_cutF hA S.pp nnp χ _ Yp K N Cb hDDp hχ (ckOn_fpmSh S.pp p₀ hf (ckOn_of_polyOp S.polyP)) hnnp)
    (blockGrowthBound_apx_cutF hA S.pm nnm χ _ Ym K N Cb hDDm hχ (ckOn_fpmSh S.pm p₀ hf (ckOn_of_polyOp S.polyM)) hnnm) hBdp hBdm

end

end Formalism.FourierDecayAlt.P.CutBPEq.CompactFormNormalFormDomination
end
end
