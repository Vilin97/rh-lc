module

public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.GrowthConstantBoundGcR
public import Formalism.LocalToGlobal.ProjectiveLattices.CurveAsm
public import Formalism.LocalToGlobal.ProjectiveLattices.IntegralExtensionOfRegR1
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsCuspFormNonzeroEveryComponentStatement
public import Formalism.LocalToGlobal.ProjectiveLattices.AxHLAM
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.LowerBoundConstAtLargeMultipleNumericalBounds
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
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExpLeOfNegLogSqrtLe
public import Development.AbelianVarietyTheory.Definitions.UpperBounds.PhRec
public import Formalism.LocalToGlobal.ProjectiveLattices.CurveInstSt
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.TranscendenceDegreeRatiosCuspFormsComponentsStatement
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.HeightProofs.LowerBoundConstAtLargeMultipleNumericalBoundsStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin

theorem _root_.GlobalTheory.T.lowerBoundConst_at_large_multiple_numerical_bounds : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 CL : ℝ) (N del : ℕ), InR D j → PageOK large₂ X H C2 A2 CT ka wL wF Tn nP nW h0 → 0 < CL → 0 < N → 0 < del → Real.log N ≤ nbR large₂ wL → Real.log del ≤ 1041 * Zb D large₂ ^ 3 → LamConst j large₂ CL 2 (wsmul (8 * ((WeightFamilies.dimY D j + 2) * N) ^ 2 * (WeightFamilies.dimY D j + 1) * del * (1 + ⌈PO D large₂⌉₊)) wL) (lamR large₂ CL wL) (8 * ((WeightFamilies.dimY D j + 2) * N) ^ 2 * (WeightFamilies.dimY D j + 1) * del * (1 + ⌈PO D large₂⌉₊)) wL.size ∧ 3 ≤ WeightFamilies.dimY D j ∧ wL.n = nW ∧ 0 < wL.n ∧ (DF wL : ℝ) ≤ wL.size ∧ 2 ≤ wL.size ∧ 1 ≤ PO D large₂ ∧ 1 ≤ zBase large₂ ∧ cc D large₂ C2 A2 7 wL * (g0 D : ℝ) ≤ 1 / 2 ∧ PI4 D j (1009 * Zb D large₂) (81 * Zb D large₂ ^ 2) ≤ max 1 (PI4 D j (1009 * Zb D large₂) (81 * Zb D large₂ ^ 2)) := by
  first | exact @GlobalTheory.RunJoin.lamConst_lamR_rows | exact GlobalTheory.RunJoin.lamConst_lamR_rows | (intros; apply GlobalTheory.RunJoin.lamConst_lamR_rows <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.SetConstantsGoodEmbeddingRecursion

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.BigRec

noncomputable section

namespace GlobalTheory.BigRec

section Inst

variable {D : D7} {T : Top D}

variable (h : LawsP T) {j : ℕ} (hj : InR D j)

end Inst




theorem bigAt_record : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (c : ℝ) (large₂ : SizeData₂ D) (CK C1 A1 h0 : ℝ) (Tn nP nW : ℕ), SetC large₂ (recPlus h j hj) CK C1 A1 ka wL wF Tn nP nW h0 → NoCommonZero (T.Q.Xo j) T.Q.c (fun i => (G.w i).1) → (j < D.R.m → 0 < G.iet ∧ (recPlus h j hj).NonZeroComp _ G.et ∧ ∃ σ, GoodEmb T.Q.c σ ∧ PhRec h j σ G.w G.iet G.et c) → 0 ≤ c → 2 * c * g0 D ≤ 1 → (j < D.R.m → ∃ w1 : WeightFamilies.Wt D j, IsDoubledWeightWithShift wL w1 nW ∧ ∃ th : (recB h.toLawsCore).Cusp j w1, (recPlus h j hj).NonZeroComp w1 th) → BigAt h j hj hG G := by
  intro D T h j hj hG ka wL wF G c large₂ CK C1 A1 h0 Tn nP nW hS hN hE hc hcg _
  exact ⟨hN, GlobalTheory.T.transcendenceDegree_ratios_cuspForms_components D T h j hj hG ka wL wF G c large₂ CK C1 A1 h0 Tn nP nW hS hN hE hc hcg⟩

end GlobalTheory.BigRec
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.SetConstantsGoodEmbeddingRecursionStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.BigRec

theorem _root_.GlobalTheory.T.set_constants_good_embedding_recursion : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (c : ℝ) (large₂ : SizeData₂ D) (CK C1 A1 h0 : ℝ) (Tn nP nW : ℕ), SetC large₂ (recPlus h j hj) CK C1 A1 ka wL wF Tn nP nW h0 → NoCommonZero (T.Q.Xo j) T.Q.c (fun i => (G.w i).1) → (j < D.R.m → 0 < G.iet ∧ (recPlus h j hj).NonZeroComp _ G.et ∧ ∃ σ, GoodEmb T.Q.c σ ∧ PhRec h j σ G.w G.iet G.et c) → 0 ≤ c → 2 * c * g0 D ≤ 1 → (j < D.R.m → ∃ w1 : WeightFamilies.Wt D j, IsDoubledWeightWithShift wL w1 nW ∧ ∃ th : (recB h.toLawsCore).Cusp j w1, (recPlus h j hj).NonZeroComp w1 th) → BigAt h j hj hG G := by
  first | exact @GlobalTheory.BigRec.bigAt_record | exact GlobalTheory.BigRec.bigAt_record | (intros; apply GlobalTheory.BigRec.bigAt_record <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GenericRegularity.PageHypothesesAtCusp

section

@[expose] public section

noncomputable section

namespace GlobalTheory.RunJoin

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem lieFac_scalar {D : D7} (T : Top D) (j i : ℕ) : lieFac (T.Q.Dw j) (xiR D) (wtA (wEt D j i)) = 1 := by
  have : ∀ x, wtA (wEt D j i) x = 0 := by
    intro x
    simp [wtA, wEt, WeightAlgebra.wscalar, ext0]
  simp [lieFac, this]

theorem weight_add_eq_smul_of_G2 {D : D7} {j : ℕ} {wL wF w2 : WeightFamilies.Wt D j} (h : IsG2 wL wF w2) :
    wadd wF w2 = wsmul (WeightFamilies.dimY D j + 4) wL := by
  obtain ⟨h1, h2, h3⟩ := h
  unfold wadd wsmul
  congr 1
  · funext τ i; rw [add_comm]; exact h2 τ i
  · funext τ i; rw [add_comm]; exact h3 τ i
  · rw [add_comm]; exact h1

theorem thR_pos {D : D7} {j : ℕ} (w : WeightFamilies.Wt D j) (hg : ∀ i, 0 < D.host.g i) (hd : 0 < DF w) : 0 < thR w := by
  have hf : 0 < ReciprocityTheory.ChartRestriction.G.I2.PT.f D.host.E := by
    unfold ReciprocityTheory.ChartRestriction.G.I2.PT.f
    have h1 := IsTotallyComplex.finrank D.host.E
    have h2 : 0 < Module.finrank ℚ D.host.E := Module.finrank_pos
    omega
  have hrd : 0 < ReciprocityTheory.ChartRestriction.G.I2.PT.rd D.host.E := by
    unfold ReciprocityTheory.ChartRestriction.G.I2.PT.rd
    exact Real.rpow_pos_of_pos (abs_pos.2 (Int.cast_ne_zero.2 (NumberField.discr_ne_zero D.host.E))) _
  have h0 := hg 0
  have h1 := hg 1
  unfold thR I2.th I2.RR
  positivity




theorem curveHyp_of_run : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ) (S : Scal (recB h.toLawsCore)) (nus : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO) → ℝ) (hG : GenFrEx (T.Q.Xo j) T.Q.c), PageOK large₂ (recPJ h j hj) H C2 A2 CT ka wL wF Tn nP nW h0 → HypC large₂ (recPJ h j hj) H C2 A2 7 0 CT S ka wL wF Tn nP nW h0 nus → ∀ G : GlobalFamilyData (recPJ h j hj) ka wL wF, GenOK h j hj large₂ G S (cc D large₂ C2 A2 7 wL) → (j < D.R.m → EtaOK h j hj large₂ wL G.iet G.et) → ∃ g0 : (recB h.toLawsCore).Cusp j wF, CurveHyp h j hj hG ka wL wF (gd2Xplus G (extAll h j hj) (intAtExt_extAll h j hj)) S g0 := by
  intro D T h j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 S nus hG hP hC G hGen hEta
  obtain ⟨⟨g0, hg0, -⟩, hnz⟩ := GlobalTheory.T.exists_cuspForm_nonzero_everyComponent D T h j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 hG hP
  obtain ⟨hT, hN, hlN, hZ, hLow⟩ := hGen
  have hZb : 0 ≤ Zb D large₂ := by
    have hs := hP.hyp.2.1
    have hd : DomAt D large₂ j nW H.C1 := hs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    exact le_trans (by positivity) hd.2.1
  have hC2 : 0 ≤ C2 := by
    have hs := hP.hyp.2.1
    have hd : DomAt D large₂ j nW H.C1 := hs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    have := hd.1
    rw [hP.tie.1] at this
    linarith
  have hrow := (GlobalTheory.T.lowerBoundConst_at_large_multiple_numerical_bounds D _ _ j (recPJ h j hj) large₂ H C2 A2 CT ka wL wF Tn nP nW h0 1 G.N 1 hj hP one_pos hN one_pos hlN
    (by rw [Nat.cast_one, Real.log_one]; positivity)).2.2.2.2.2.2.2.2.1
  have hc0 : 0 ≤ cc D large₂ C2 A2 7 wL := by
    have h1 : 0 ≤ zBase large₂ := hZb
    have h2 : 0 ≤ D.host.rdE := le_trans (by positivity) hP.frd
    unfold cc WeightFamilies.RRv WeightFamilies.PPv
    positivity
  obtain ⟨hsz, PL, lN, -, -, hI1, w2, hw2, th2, -, hth2, -⟩ :=
    (FamilyHypotheses.fourthHypothesis_iff_sizes_and_index large₂ (recPJ h j hj) H C2 A2 7 ka wL wF Tn nW).1 hC.2.2.2.2.2.2.1
  have hth : 0 < thR wL := thR_pos wL (fun i => lt_of_le_of_lt (Nat.zero_le _) (hsz.2.2.2.2.2 i))
    (lt_of_lt_of_le (by norm_num) hP.df)
  refine ⟨g0, hT.1, ?_, ⟨WeightFamilies.dimY D j + 4, w2, th2, weight_add_eq_smul_of_G2 hw2, (hnz w2 th2 hth2).1⟩, hg0⟩
  refine GlobalTheory.T.set_constants_good_embedding_recursion D T h j hj hG ka wL wF (gd2Xplus G (extAll h j hj) (intAtExt_extAll h j hj))
    (cc D large₂ C2 A2 7 wL) large₂ H.CK H.C1 H.A1 h0 Tn nP nW hP.hyp.2.1 hZ (fun hjm => ?_) hc0 (by linarith) (fun hjm => ?_)
  · obtain ⟨hi, hcu, -, -, hA, -⟩ := hEta hjm
    refine ⟨hi, hcu.2, T.σ₀, T.toCore.good_σ₀, ?_⟩
    have e : Fin (G.N - 1 + 1) ≃ Fin G.N := finCongr (by omega)
    refine GlobalTheory.BigRec.phRec_of_firstMin D T h j hj T.σ₀ wL G.N (G.N - 1) G.iet G.w e G.et (thR wL) (p14R wL) (DF wL)
      (200000 * zBase large₂ ^ 2) _ T.toCore.good_σ₀ hth (fun σ hσ k x hx => ?_) hZ (fun k x hx => ?_)
    · have h1 := hLow σ hσ k x hx
      rw [← e.sum_comp] at h1
      exact h1
    · have h1 := hA T.σ₀ T.toCore.good_σ₀ k x hx
      rw [lieFac_scalar, one_mul] at h1
      exact h1
  · obtain ⟨w1, hw1, th1, -, hth1, -⟩ := hI1 hjm
    exact ⟨w1, hw1, th1, hth1⟩

end GlobalTheory.RunJoin
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GenericRegularity.PageHypothesesAtCuspStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin

theorem _root_.GlobalTheory.T.page_hypotheses_at_cusp : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ) (S : Scal (recB h.toLawsCore)) (nus : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO) → ℝ) (hG : GenFrEx (T.Q.Xo j) T.Q.c), PageOK large₂ (recPJ h j hj) H C2 A2 CT ka wL wF Tn nP nW h0 → HypC large₂ (recPJ h j hj) H C2 A2 7 0 CT S ka wL wF Tn nP nW h0 nus → ∀ G : GlobalFamilyData (recPJ h j hj) ka wL wF, GenOK h j hj large₂ G S (cc D large₂ C2 A2 7 wL) → (j < D.R.m → EtaOK h j hj large₂ wL G.iet G.et) → ∃ g0 : (recB h.toLawsCore).Cusp j wF, CurveHyp h j hj hG ka wL wF (gd2Xplus G (extAll h j hj) (intAtExt_extAll h j hj)) S g0 := by
  first | exact @GlobalTheory.RunJoin.curveHyp_of_run | exact GlobalTheory.RunJoin.curveHyp_of_run | (intros; apply GlobalTheory.RunJoin.curveHyp_of_run <;> assumption)
end
end
