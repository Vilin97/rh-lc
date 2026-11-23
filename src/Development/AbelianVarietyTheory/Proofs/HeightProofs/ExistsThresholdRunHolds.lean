module

public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.ConclOfInputs4
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsIndexBoundHypothesesWithNetAllValuedPointsStatement
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroOfReducedInputs
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.CombBound4Of
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ExistsGlobalFamilyZeroChoice
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
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ExistsGlobalFamilyQuotientBounded
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ExistsGlobalFamilyZeroChoice
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LenAtEqZeroOfSubsingleton
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroBundledOfLift
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IntrinsicIndexBoundOfFiniteNetHypothesesStatement
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.RunNumericalConditionsOfIndexBoundBeyondThreshol
import Formalism.LocalToGlobal.ProjectiveLattices.XPlusWireT

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShareRhoAndShareRhoTOfShareRhoR

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps GlobalTheory.Shares

namespace GlobalTheory

theorem shareRho_and_shareRhoT_of_shareRhoR :
    ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (ka wL wF : WeightFamilies.Wt D j)
      (G : GlobalFamilyData X ka wL wF) (S : Scal B) (T d : ℕ) (Gc : ℝ), ShareRhoR G S T d → G.TiedZ S T Gc →
      (∀ la, InContainZ G la S T) →
      ShareRho (D := D) (j := j) T G.rz d ∧ ShareRhoT (D := D) (j := j) T G.rz G.rq d := by
  intro D B P j X ka wL wF G S T d Gc hR hT hZ
  obtain ⟨la0⟩ := Formalism.MainNotions.Gaps.EtaleWeightGaps.exists_prime B.KO
  have hr : Module.finrank (Kp X la0 G.N) ↥(Submodule.span (Kp X la0 G.N) (zAll G la0 S T)) = G.rz :=
    rz_eq_finrank G S T Gc la0 hT (hZ la0)
  have h := hR la0
  rw [hr] at h
  refine ⟨h, ?_⟩
  unfold ShareRhoT
  have h0 : (0 : ℝ) ≤ (G.rq : ℝ) := Nat.cast_nonneg _
  linarith

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.HeightProofs.IndexBoundChosenFamilyOfIntrinsicHypotheses

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin GlobalTheory.RunIn GlobalTheory.FinalJoin




namespace GlobalTheory.FinalJoin

theorem inputs4_of_inputsR : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (X : WeightAlgebra.Prov D B P) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (large₂ : SizeData₂ D) (K : KAdm) (H : KHyp) (Ch Ah Cq Aq C2 A2 CR CT : ℝ) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ), InputsR large₂ (X j h1 h2) K H Ch Ah Cq Aq C2 A2 CR CT S ka wL wF Tn nP nW h0 nus → TieC K H Ch Ah Cq Aq C2 A2 CR → PageAt large₂ C2 A2 → PageSupp D large₂ B C2 A2 nW S wL → Inputs4 large₂ (X j h1 h2) K H Ch Ah Cq Aq C2 A2 CR CT S ka wL wF Tn nP nW h0 nus := by
  intro D B P X j h1 h2 large₂ K H Ch Ah Cq Aq C2 A2 CR CT S ka wL wF T nP nW h0 nus hI hTC hPA hPS
  obtain ⟨⟨hH, hLat, hLAM, hQ, hSub⟩, hSup, hHerm, G, Gc, PH, Prw, Pet, Pd, hLogD,
    ⟨hW, hTh, hEt, hPGd, hPG4, hPGq, hRd, hRho, hRhoP, hPoly, hB, hM⟩, hComb, Qf, hC, hTie, hLift, hHt⟩ := hI
  have hSet := hH.2.1
  have hH2 := hH.2.2.2.2.1
  obtain ⟨hS0, hSK⟩ := shortG_of_scalB hH.2.2.1 hPG4
  have hDT : WeightFamilies.dimY D j ≤ T := hSet.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hwt : SizeBoundsAlt.wtIter wadd wL ((X j h1 h2).wF0 wL wF) (a0 D j T) = ka := by
    rw [iterated_weight_at_vanishingOrder (X j h1 h2) wL wF T hDT]; exact (ka_eq_addL_of_setC hSet).symm
  obtain ⟨rz, alz, th0, zc, hTZ, hZ⟩ := exists_global_family_zero_choice G S T Gc hwt hS0 hH2.2.2.1
  obtain ⟨th, hTQ⟩ := exists_global_family_quotient_bounded
    ({ G with rz := rz, alz := alz, th0 := th0, zc := zc } : GlobalFamilyData (X j h1 h2) ka wL wF) large₂ S K.CRm T
    (cc D large₂ C2 A2 CR wL) (Gc * ka.size) Ch Ah hSK hH2.2.2.2
    (mul_le_mul_of_nonneg_right hPGq (by linarith [ka.one_le_size]))
  obtain ⟨hR1, hR2⟩ := GlobalTheory.shareRho_and_shareRhoT_of_shareRhoR D B P j (X j h1 h2) ka wL wF
    (G.setZQ rz alz th0 zc _ th) S T _ Gc hRho hTZ hZ
  have hM' : ∀ la, InContainM (G.setZQ rz alz th0 zc _ th) la K.CRm T (cc D large₂ C2 A2 CR wL) :=
    fun la => inContainM_of _ la S _ T _ (hM la) (hZ la)
  have hLift' : ∀ la, ((Qf la).tr G rz alz th0 zc _ th).InLiftC S Gc Prw T :=
    fun la => tr_InLiftC G rz alz th0 zc _ th (Qf la) S Gc Prw T (hLift la)
  refine ⟨hH, hLat, hSup, hLAM, hQ, hTC, hPA, hPS, G.setZQ rz alz th0 zc _ th, Gc, PH, Prw, Pet, Pd,
    hW, hTh, hTZ, hTQ, hEt, hHerm, hSub, hLogD, pageGd4_iff.mpr hPGd, hRd, hR2, hRhoP, polyDom4_iff.mpr hPoly, hZ, hM',
    fun hj => ⟨fun la => (Qf la).tr G rz alz th0 zc _ th, hB, hC, hTie, hLift',
      combBound4_of hj (tr_CombBound G rz alz th0 zc _ th S _ nus hComb) _, hHt⟩,
    fun hj => depthAtM_of hj hComb, fun _ _ => ?_,
    fun _ => ⟨fun la => (Qf la).tr G rz alz th0 zc _ th, hB, hC, hTie, hLift', hHt⟩⟩
  exact theorem_zero_of_named_inputs large₂ X K H Ch Ah Cq Aq C2 A2 CR CT j h1 h2 S ka wL wF T nP nW h0 nus hH hLat hSup hLAM hQ
    (G.setZQ rz alz th0 zc _ th) Gc PH Prw Pet Pd (fun la => (Qf la).tr G rz alz th0 zc _ th)
    hW hTh hTZ hTQ hEt hHerm hSub hLogD hPGd hRd hR1 hRhoP hPoly hB hC hTie hLift' hZ hM' hComb hHt

end GlobalTheory.FinalJoin
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.HeightProofs.IndexBoundChosenFamilyOfIntrinsicHypothesesStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin GlobalTheory.RunIn GlobalTheory.FinalJoin

theorem _root_.GlobalTheory.T.indexBoundChosenFamily_of_intrinsicHypotheses : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (X : WeightAlgebra.Prov D B P) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (large₂ : SizeData₂ D) (K : KAdm) (H : KHyp) (Ch Ah Cq Aq C2 A2 CR CT : ℝ) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ), InputsR large₂ (X j h1 h2) K H Ch Ah Cq Aq C2 A2 CR CT S ka wL wF Tn nP nW h0 nus → TieC K H Ch Ah Cq Aq C2 A2 CR → PageAt large₂ C2 A2 → PageSupp D large₂ B C2 A2 nW S wL → Inputs4 large₂ (X j h1 h2) K H Ch Ah Cq Aq C2 A2 CR CT S ka wL wF Tn nP nW h0 nus := by
  first | exact @GlobalTheory.FinalJoin.inputs4_of_inputsR | exact GlobalTheory.FinalJoin.inputs4_of_inputsR | (intros; apply GlobalTheory.FinalJoin.inputs4_of_inputsR <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.HeightProofs.IndexBoundIntrinsicHypothesesNetBoundDegreeTwo

section

@[expose] public section

set_option autoImplicit false



open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin GlobalTheory.RunIn GlobalTheory.FinalJoin

namespace GlobalTheory.FinalJoin

theorem ppv_deg_three_eq_deg_two {D : D7} (large₂ : SizeData₂ D) :
    WeightFamilies.PPv D large₂ 1041 3 = WeightFamilies.PPv D large₂ (1041 * zBase large₂) 2 := by
  have h : (0 : ℝ) < zBase large₂ := lt_of_lt_of_le one_pos (WeightFamilies.one_le_zBase large₂)
  unfold WeightFamilies.PPv
  rw [show (3 : ℝ) = 1 + 2 by norm_num, Real.rpow_add h, Real.rpow_one, mul_assoc]

theorem inputsR_deg_two : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (large₂ : SizeData₂ D) (CL : ℝ) (H : KHyp) (Ch Ah Cq Aq C2 A2 CR CT : ℝ) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ), InputsR large₂ X (kR CL) H Ch Ah Cq Aq C2 A2 CR CT S ka wL wF Tn nP nW h0 nus → InputsR large₂ X (k4 large₂ CL) H Ch Ah Cq Aq C2 A2 CR CT S ka wL wF Tn nP nW h0 nus := by
  intro D B P j X large₂ CL H Ch Ah Cq Aq C2 A2 CR CT S ka wL wF Tn nP nW h0 nus h
  obtain ⟨h1, h2, h3, G, Gc, PH, Prw, Pet, Pd, h4, ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12⟩, h6⟩ := h
  have e := ppv_deg_three_eq_deg_two large₂
  refine ⟨h1, ?_, h3, G, Gc, PH, Prw, Pet, Pd, h4, ⟨f1, f2, f3, ?_, f5, f6, f7, f8, f9, f10, f11, f12⟩, h6⟩
  · intro F σ
    have := h2 F σ
    change _ ≤ Real.exp (WeightFamilies.PPv D large₂ 1041 3 * _) * _ at this
    rw [e] at this
    exact this
  · have := f4
    change WeightFamilies.PPv D large₂ 1041 3 * _ ≤ _ at this
    rw [e] at this
    exact this

end GlobalTheory.FinalJoin
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.HeightProofs.IndexBoundIntrinsicHypothesesNetBoundDegreeTwoStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin GlobalTheory.RunIn GlobalTheory.FinalJoin

theorem _root_.GlobalTheory.T.indexBoundIntrinsicHypotheses_netBound_degreeTwo : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (large₂ : SizeData₂ D) (CL : ℝ) (H : KHyp) (Ch Ah Cq Aq C2 A2 CR CT : ℝ) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ), InputsR large₂ X (kR CL) H Ch Ah Cq Aq C2 A2 CR CT S ka wL wF Tn nP nW h0 nus → InputsR large₂ X (k4 large₂ CL) H Ch Ah Cq Aq C2 A2 CR CT S ka wL wF Tn nP nW h0 nus := by
  first | exact @GlobalTheory.FinalJoin.inputsR_deg_two | exact GlobalTheory.FinalJoin.inputsR_deg_two | (intros; apply GlobalTheory.FinalJoin.inputsR_deg_two <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.HeightProofs.RunNumericalConditionsOfIndexBoundBeyondThresholStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin GlobalTheory.RunIn GlobalTheory.FinalJoin

theorem _root_.GlobalTheory.T.runNumericalConditions_of_indexBound_beyond_threshold : ∀ Z₀ : ℝ → ℝ → ℝ, ∃ x₀ : ℝ → ℝ → ℝ, ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), InR D j → PageRun large₂ X H C2 A2 CT ka wL wF Tn nP nW h0 → x₀ H.CA H.CK ≤ large₂.sc.x → PageOK large₂ X H C2 A2 CT ka wL wF Tn nP nW h0 ∧ Z₀ H.CA H.CK ≤ zBase large₂ := by
  first | exact @GlobalTheory.FinalJoin.pageOK_of_pageRun_beyond | exact GlobalTheory.FinalJoin.pageOK_of_pageRun_beyond | (intros; apply GlobalTheory.FinalJoin.pageOK_of_pageRun_beyond <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsThresholdRunHolds

section

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FinalJoin

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin GlobalTheory.RunIn GlobalTheory.FinalJoin

theorem scalOfP_base {D : D7} {B : WeightFamilies.Prov D} (n : SecNorm B) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D)
    (p : ℕ) {j : ℕ} (ka wL wF : WeightFamilies.Wt D j) (Tn : ℕ) :
    scalOfP n.base hinj EX p ka wL wF Tn = scalarsWithNorm n.N n.h0 n.h1 n.h2 n.h3 n.h4 (scalOfP B hinj EX p ka wL wF Tn) := rfl



theorem indexBoundConclusion_secondNorm_iff {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (n : SecNorm B) (X : PJ D B P j) (S : Scal B)
    (ka wL wF : WeightFamilies.Wt D j) (Tn : ℕ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) (a b c d : ℝ) :
    Concl (PJ.tol2NormAlt n.N n.h0 n.h1 n.h2 n.h3 n.h4 X) (scalarsWithNorm n.N n.h0 n.h1 n.h2 n.h3 n.h4 S) ka wL wF Tn nus
      ((PJ.tol2NormAlt n.N n.h0 n.h1 n.h2 n.h3 n.h4 X).rk ka (n.base.Mlat j ka) * a * b * c * d) ↔
    Concl X S ka wL wF Tn nus (X.rk ka (B.Mlat j ka) * a * b * c * d) := Iff.rfl



theorem inputs4_of_net {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} (X : WeightAlgebra.Prov D B P) (j : ℕ) (h1 : 1 ≤ j)
    (h2 : j ≤ D.R.m) (large₂ : SizeData₂ D) (CL : ℝ) (H : KHyp) (Cq C2 A2 CT : ℝ) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j)
    (Tn nP nW : ℕ) (h0 : ℝ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ)
    (hn : InputsNet large₂ (X j h1 h2) (kR CL) H 1 4 Cq 4 C2 A2 7 CT S ka wL wF Tn nP nW h0 nus)
    (ht : H.C1 = C2 ∧ H.A1 = A2 ∧ H.Cc = C2 ∧ H.Ac = A2 ∧ H.CRc = 7 ∧ 12 ≤ A2) (hp : PageAt large₂ C2 A2)
    (hs : PageSupp D large₂ B C2 A2 nW S wL) :
    ∃ n : SecNorm B,
      Inputs4 large₂ (PJ.tol2NormAlt n.N n.h0 n.h1 n.h2 n.h3 n.h4 (X j h1 h2)) (k4 large₂ CL) H 1 4 Cq 4 C2 A2 7 CT
        (scalarsWithNorm n.N n.h0 n.h1 n.h2 n.h3 n.h4 S) ka wL wF Tn nP nW h0 nus ∧
      Concl (PJ.tol2NormAlt n.N n.h0 n.h1 n.h2 n.h3 n.h4 (X j h1 h2)) (scalarsWithNorm n.N n.h0 n.h1 n.h2 n.h3 n.h4 S) ka wL wF Tn nus
        ((PJ.tol2NormAlt n.N n.h0 n.h1 n.h2 n.h3 n.h4 (X j h1 h2)).rk ka (n.base.Mlat j ka) * D.R.f * D.R.m * large₂.sc.b *
          large₂.de2) := by
  obtain ⟨n, hR⟩ := GlobalTheory.T.exists_secNorm_inputsR_of_inputsNet D B P j (X j h1 h2) large₂ (kR CL) H 1 4 Cq 4 C2 A2 7 CT S ka wL wF Tn nP nW h0 nus hn
  have hR' := GlobalTheory.T.indexBoundIntrinsicHypotheses_netBound_degreeTwo D _ P j _ large₂ CL H 1 4 Cq 4 C2 A2 7 CT _ ka wL wF Tn nP nW h0 _ hR
  obtain ⟨t1, t2, t3, t4, t5, t6⟩ := ht
  have hT : TieC (k4 large₂ CL) H 1 4 Cq 4 C2 A2 7 :=
    ⟨t1, t2, t3, t4, t5, rfl, rfl, t6, le_rfl, le_rfl, le_rfl, by norm_num [k4], le_rfl, le_rfl, by norm_num⟩
  let Y : WeightAlgebra.Prov D n.base P := fun j h1 h2 => PJ.tol2NormAlt n.N n.h0 n.h1 n.h2 n.h3 n.h4 (X j h1 h2)
  have h4 := GlobalTheory.T.indexBoundChosenFamily_of_intrinsicHypotheses D n.base P Y j h1 h2 large₂ (k4 large₂ CL) H 1 4 Cq 4 C2 A2 7 CT
    (scalarsWithNorm n.N n.h0 n.h1 n.h2 n.h3 n.h4 S) ka wL wF Tn nP nW h0 nus hR' hT hp hs
  exact ⟨n, h4, concl_of_inputs4 large₂ Y (k4 large₂ CL) H 1 4 Cq 4 C2 A2 7 CT j h1 h2 _ ka wL wF Tn nP nW h0 nus h4⟩




theorem runHolds_of_parOK : ∃ x₀ : ℝ → ℝ → ℝ, ∀ (D : D7) (T : Top D) (h : LawsP T) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ), (∀ j, InR D j → ParOK T EX p j) → RunHolds x₀ h hinj EX p := by
  obtain ⟨CL, Cq, Z₀, hrec⟩ := GlobalTheory.T.exists_indexBoundHypothesesWithNet_allValuedPoints
  obtain ⟨x₀, hx⟩ := GlobalTheory.T.runNumericalConditions_of_indexBound_beyond_threshold Z₀
  refine ⟨x₀, fun D T h hinj EX p hpar j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 hrun hx0 => ?_⟩
  obtain ⟨hok, hZ⟩ := hx D _ _ j _ large₂ H C2 A2 CT ka wL wF Tn nP nW h0 hj hrun hx0
  obtain ⟨hn, hs⟩ := hrec D T h hinj EX p j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 (hpar j hj) hok hZ
  obtain ⟨n, h4, hc⟩ := inputs4_of_net (fun j h1 h2 => recPlus h j ⟨h1, h2⟩) j hj.1 hj.2 large₂ CL H (Cq H.CA H.CK) C2 A2 CT
    _ ka wL wF Tn nP nW h0 _ hn hrun.tie hrun.page hs
  refine ⟨⟨n, k4 large₂ CL, Cq H.CA H.CK, ?_, ?_⟩, ?_, ?_⟩
  · rw [scalOfP_base]; exact h4
  · rw [scalOfP_base]; exact hc
  · exact (hypC_xplus (recPJ h j hj) (extAll h j hj) (intAtExt_extAll h j hj) large₂ H C2 A2 7 0 CT _ Tn nP nW h0 _).1 hn.1.1
  · exact (concl_xplus (recPJ h j hj) (extAll h j hj) (intAtExt_extAll h j hj) _ ka wL wF Tn _ _).1
      ((indexBoundConclusion_secondNorm_iff n _ _ ka wL wF Tn _ _ _ _ _).1 hc)

end GlobalTheory.FinalJoin
end
end
end
