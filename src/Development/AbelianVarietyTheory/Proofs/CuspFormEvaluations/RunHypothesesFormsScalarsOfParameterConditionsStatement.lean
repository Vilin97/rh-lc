module

public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.GrowthConstantBoundGcR
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.SWEqSOf
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import Formalism.LocalToGlobal.ProjectiveLattices.XcLat
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.WeightedPrimeSumBound
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LatOfLamSt
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.WeightModuleIsLatticeOfShortSeriesSpan
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
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsIntegralAuxiliaryCuspFormsSupBoundStatement
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroOfReducedInputs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupBoundPageRows
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsShortFiniteGeneratorsThetaLatticeStatement
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LogLeOfLePowMulPow
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.PageRowsOfLe
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.PageTwoLeLAndSigns
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ScaledFamily
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SupBoundsLeGeneratorConstantMulSizeStatement
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaLatticeWeightScalarNeZeroAndLogBounds
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.WeightsBelow
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.GamAtOfLawsCore
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RunScalarsNonzeroBoundedSupBoundStatement
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ScaledThetaLatticeGeneratorsNoCommonZeroStatement
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SizePageRowsOfSizePageAt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaLatticeWeightScalarNeZeroAndLogBounds
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.WeightsBelow
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.HarmonicGermValueChartIndependentStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DepthSumRecord
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ScaledRunLatticesInSupLatticesProofStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ScaledThetaLatticeLeSupLatticeEveryWeightStatement
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ShortThetaSeriesSpanCuspFormsWeightStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.WeightFloorInequalities

-- Source module: Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.WeightModuleIsLatticeOfShortSeriesSpanStatement

section

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.MainNotions Formalism.BasicNotions
open GlobalTheory GlobalTheory.RunIn


theorem _root_.GlobalTheory.T.weightModule_isLattice_of_shortSeries_span : ∀ (D : D7) (T : Core D) (h : LawsCore T), GamAt T → ∀ (large₂ : SizeData₂ D) (CA : ℝ), WeightAlgebra.ParA large₂ CA → ∀ (j : ℕ) (ka : WeightFamilies.Wt D j) (P : ModuliIntegralCharts.Prov D) (X : WeightAlgebra.PJ D (recB h) P j) (S : WeightAlgebra.Scal (recB h)) (wL wF : WeightFamilies.Wt D j), S.sK ≠ 0 → PullbackSections.SpanAt X ka → WeightAlgebra.H2 X S ka wL wF → Formalism.MainNotions.Gaps.EtaleWeightGaps.LatAt (recB h) j ka := by
  first | exact @GlobalTheory.latAt_record | exact GlobalTheory.latAt_record | (intros; apply GlobalTheory.latAt_record <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsRunDataGeneratingScaledThetaLatticeWeight

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.RunIn

theorem exists_tiedW_rec : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (h : LawsP T), GamAt T.toCore → ∀ (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ) (Gc Prw : ℝ), FamilyHypotheses.HypPage large₂ (recPJ h j hj) H C2 A2 CR CT ka wL wF Tn nP nW h0 → ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ ka → ThInt (recPJ h j hj) hinj EX wL → EtaleWeightGaps.GrowthConstantBound large₂ (recB h.toLawsCore) Gc → 38 * large₂.sc.L + PO D large₂ ≤ Prw → ∃ G : EtaleWeightGaps.GlobalFamilyData (recPJ h j hj) ka wL wF, G.TiedW (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn) Gc Prw := by
  intro hC D T h hG hinj EX p j hj large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 Gc Prw hP hR hI hG4 hPrw
  obtain ⟨hL, hf, hr, hlam, -, -⟩ := GlobalTheory.page_two_le_L_and_signs D _ _ j _ large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 hP hR
  obtain ⟨hDF, hn, hrn, hLP⟩ :=
    (GlobalTheory.RunWeights.weights_below D _ _ j _ large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 hj.1 hP).1 wL (by simp)
  have hL0 : 0 ≤ large₂.sc.L := by linarith
  have hRL := GlobalTheory.pageRows_of_le D large₂ j ka wL hL0 hDF hn hR
  have hn0 : 0 < wL.n := by omega
  have hO : OPO large₂ (recB h.toLawsCore) := by
    obtain ⟨-, ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hO, -⟩, -⟩ := hP
    exact hO
  obtain ⟨N, w0, hspan, hN, hsup⟩ := GlobalTheory.T.exists_short_finite_generators_thetaLattice hC D T h hG large₂ j hj wL hRL hL hrn hLP
  have hcount := log_count_le_mul_size D _ large₂ j wL N Prw hL hn0 hRL hO hPrw hN
  have hs : (0 : ℝ) ≤ wL.size := by
    have h1 := frn_le_size_sub_one wL
    have h2 : (0 : ℝ) ≤ (D.R.f : ℝ) * D.R.r * wL.n := by positivity
    push_cast at h1
    linarith
  have hp : 0 ≤ Real.log (D.host.pde : ℝ) := Real.log_natCast_nonneg _
  have hZ : 0 ≤ Zb D large₂ := by unfold Zb; positivity
  have hnum := (GlobalTheory.T.supBounds_le_generatorConstant_mul_size D (recB h.toLawsCore) large₂ j wL D.host.pde hL hn0).2.2
  have hGc := mul_le_mul_of_nonneg_right (hG4 D.host.pde (by simp)) hs
  have hd : 0 ≤ Real.log |((NumberField.discr (recB h.toLawsCore).KO : ℤ) : ℝ)| := by
    rw [Real.log_abs]; exact Real.log_intCast_nonneg _
  have hK : 0 ≤ Real.log (Module.finrank ℚ (recB h.toLawsCore).KO : ℝ) := Real.log_natCast_nonneg _
  refine (GlobalTheory.ScaledGenerators.scaled_family D _ _ j (recPJ h j hj) ka wL wF (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn) N w0
    ((lamStar D + 2 * Real.log D.host.pde) * wL.size) _ Gc Prw (by positivity) (by positivity) (fun σ => ?_)
    hspan hsup (hnum.trans hGc)).2 hI hcount
  rw [sW_eq_sOf]
  refine ((GlobalTheory.RunIn.sOf_ne_zero_and_log_bounds D _ hinj EX j wL).2 σ).2.2.2.trans ?_
  exact mul_le_mul_of_nonneg_right (by linarith) hs

end GlobalTheory.RunIn
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsRunDataGeneratingScaledThetaLatticeWeightStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.exists_runData_generating_scaled_thetaLattice_weight : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (h : LawsP T), GamAt T.toCore → ∀ (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ) (Gc Prw : ℝ), FamilyHypotheses.HypPage large₂ (recPJ h j hj) H C2 A2 CR CT ka wL wF Tn nP nW h0 → ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ ka → ThInt (recPJ h j hj) hinj EX wL → EtaleWeightGaps.GrowthConstantBound large₂ (recB h.toLawsCore) Gc → 38 * large₂.sc.L + PO D large₂ ≤ Prw → ∃ G : EtaleWeightGaps.GlobalFamilyData (recPJ h j hj) ka wL wF, G.TiedW (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn) Gc Prw := by
  first | exact @GlobalTheory.RunIn.exists_tiedW_rec | exact GlobalTheory.RunIn.exists_tiedW_rec | (intros; apply GlobalTheory.RunIn.exists_tiedW_rec <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsShortSpanThetaTieOfScalars

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn

namespace GlobalTheory

theorem exists_short_span_thetaTie_of_scalars : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (large₂ : SizeData₂ D) (C1 A1 Gc : ℝ) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (Tn : ℕ), ScalB large₂ X C1 A1 S ka wL wF Tn → EtaleWeightGaps.GrowthConstantBound large₂ B Gc → ∃ Sh : Finset (B.Cusp j wF), Submodule.span B.KO (Sh : Set (B.Cusp j wF)) = ⊤ ∧ (∀ g ∈ Sh, g ∈ X.Thc S.sF wF ∧ WeightFamilies.meanLogSup B g ≤ Gc * wF.size) ∧ ∀ G : EtaleWeightGaps.GlobalFamilyData X ka wL wF, (∀ i, G.th' i ∈ Sh) → G.TiedTh S Gc := by
  intro D B P j X large₂ C1 A1 Gc S ka wL wF Tn hS hG
  obtain ⟨-, -, -, -, -, po, hpo, -, PLam, hPLam, -, ⟨Sh, hSub, hSpan, hMean⟩, -, -⟩ := hS

  have hconst : Formalism.MainNotions.WeightAlgebra.Gc large₂ B PLam po ≤ Gc := by
    refine le_trans ?_ (hG po hpo)
    unfold Formalism.MainNotions.WeightAlgebra.Gc
    linarith
  have hbound : Formalism.MainNotions.WeightAlgebra.Gc large₂ B PLam po * wF.size ≤ Gc * wF.size :=
    mul_le_mul_of_nonneg_right hconst (le_trans zero_le_one wF.one_le_size)
  refine ⟨Sh, hSpan, fun g hg => ⟨hSub hg, (hMean g hg).trans hbound⟩, fun G hG' i => ?_⟩
  exact ⟨hSub (hG' i), (hMean _ (hG' i)).trans hbound⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SizePageRowsOfSizePageAtStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn

theorem _root_.GlobalTheory.T.sizePageRows_of_sizePageAt : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), FamilyHypotheses.HypPage large₂ X H C2 A2 CR CT ka wL wF Tn nP nW h0 → PageAt large₂ C2 A2 → 4 * H.CK ≤ WeightFamilies.PPv D large₂ C2 A2 ^ 2 * D.R.f → ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ ka ∧ 16 ≤ D.R.f := by
  first | exact @GlobalTheory.pageRows_of_pageAt | exact GlobalTheory.pageRows_of_pageAt | (intros; apply GlobalTheory.pageRows_of_pageAt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RunHypothesesFormsScalarsOfParameterConditions

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin

namespace GlobalTheory.RunJoin

theorem log_DF_le_of_rows {D : D7} {j : ℕ} (large₂ : SizeData₂ D) (ka w : WeightFamilies.Wt D j) (h3 : 3 ≤ DF w) (hle : DF w ≤ DF ka)
    (hrow : Real.log (1 + DF ka) ≤ 2 * large₂.sc.L) : Real.log (DF w) ≤ 2 * large₂.sc.L := by
  have hpos : (0 : ℝ) < (DF w : ℝ) := by
    have h0 : 0 < DF w := by omega
    exact_mod_cast h0
  have hmono : (DF w : ℝ) ≤ 1 + (DF ka : ℝ) := by
    have h1 : (DF w : ℝ) ≤ (DF ka : ℝ) := by exact_mod_cast hle
    linarith
  exact (Real.log_le_log hpos hmono).trans hrow


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem hypC_record : ∀ (D : D7) (T : Top D) (h : LawsP T) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), ParOK T EX p j → PageOK large₂ (recPJ h j hj) H C2 A2 CT ka wL wF Tn nP nW h0 → HypC large₂ (recPJ h j hj) H C2 A2 7 0 CT (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn) ka wL wF Tn nP nW h0 (nusR h j wL) ∧ LatAt (recB h.toLawsCore) j ka ∧ (∀ w : WeightFamilies.Wt D j, GlobalTheory.RunIn.ThInt (recPJ h j hj) hinj EX w) ∧ PageSupp D large₂ (recB h.toLawsCore) C2 A2 nW (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn) wL ∧ ∃ Sh : Finset ((recB h.toLawsCore).Cusp j wF), Submodule.span (recB h.toLawsCore).KO (Sh : Set ((recB h.toLawsCore).Cusp j wF)) = ⊤ ∧ ∀ G : GlobalFamilyData (recPJ h j hj) ka wL wF, (∀ i, G.th' i ∈ Sh) → G.TiedTh (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn) (gcR large₂ (recB h.toLawsCore)) := by
  intro D T h hinj EX p j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 hpar hpage
  have hj1 : 1 ≤ j := hj.1
  have hjm : j ≤ D.R.m := hj.2
  obtain ⟨hParA, hSetC, -, -, -⟩ := hpage.hyp
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hnW, -, hIsL, hIsF, -⟩ := hSetC
  have hchart := GlobalTheory.T.harmonic_germ_value_chart_independent
  have hgam : GlobalTheory.RunIn.GamAt T.toCore := GlobalTheory.RunIn.gamAt_of_lawsCore D T.toCore h.toLawsCore
  have hrows := (GlobalTheory.pageRows_of_pageAt D _ _ j (recPJ h j hj) large₂ H C2 A2 7 CT ka wL wF Tn nP nW h0
    hpage.hyp hpage.page hpage.ck).1
  have hwb := GlobalTheory.RunWeights.weights_below D _ _ j (recPJ h j hj) large₂ H C2 A2 7 CT ka wL wF Tn nP nW h0 hj1 hpage.hyp
  have hLle : DF wL ≤ DF ka := (hwb.1 wL (by simp)).1
  have hlogL : Real.log (DF wL) ≤ 2 * large₂.sc.L :=
    log_DF_le_of_rows large₂ ka wL hpage.df hLle hrows.2.2.2.2.2.2.2.1
  have hn : 2 * D.R.f * D.R.r ≤ wL.n := by
    rw [hIsL.1]
    have hr : 2 ≤ D.R.r + 1 := by have := hpage.r8; omega
    calc 2 * D.R.f * D.R.r = D.R.f * D.R.r * 2 := by ring
      _ ≤ D.R.f * D.R.r * (D.R.r + 1) := Nat.mul_le_mul_left _ hr
      _ ≤ nW := hnW
  have hH1 := (GlobalTheory.DepthSum.depth_sum_record D T h j hj large₂ wL hn hlogL).1
  have hown : FamilyHypotheses.OwnPr D p := by
    obtain ⟨q, hq, hall⟩ := hpar.sh.dPd
    have e : p = q := (hpar.own 0).symm.trans (hall j hj 0)
    subst e
    exact hq
  have hH2 := (GlobalTheory.T.scaledRunLattices_in_supLattices D T h hpar.sh j hj hinj EX hpar.orient p hpar.own ka wL wF Tn nP hIsF).1
  have hth : ∀ w : WeightFamilies.Wt D j, GlobalTheory.RunIn.ThInt (recPJ h j hj) hinj EX w :=
    fun w => GlobalTheory.T.scaledThetaLattice_le_supLattice_every_weight D T h j hj hinj EX hpar.orient w
  have helper : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (h : LawsP T), GlobalTheory.RunIn.GamAt T.toCore → LawsSh T → 0 < badN D → (∀ j, InR D j → ∀ n, (T.dδ j n).l₂.A = 1) → (∀ j, InR D j → ∀ k k', ((T.U j T.σ₀).X k).Gm = ((T.U j T.σ₀).X k').Gm ∧ ((T.U j T.σ₀).X k).ξ0 = ((T.U j T.σ₀).X k').ξ0) → ∀ (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ) (Gc Prw : ℝ), FamilyHypotheses.OwnPr D p → FamilyHypotheses.HypPage large₂ (recPJ h j hj) H C2 A2 CR CT ka wL wF Tn nP nW h0 → PageAt large₂ C2 A2 → 4 * H.CK ≤ WeightFamilies.PPv D large₂ C2 A2 ^ 2 * D.R.f → (∀ w2, IsG2 wL wF w2 → GlobalTheory.RunIn.ThInt (recPJ h j hj) hinj EX w2) → (j < D.R.m → ∀ w1, IsDoubledWeightWithShift wL w1 nW → GlobalTheory.RunIn.ThInt (recPJ h j hj) hinj EX w1) → H2 (recPJ h j hj) (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn) ka wL wF → EtaleWeightGaps.GrowthConstantBound large₂ (recB h.toLawsCore) Gc → 38 * large₂.sc.L + PO D large₂ ≤ Prw → (∀ nus, EtaleWeightGaps.WeightedPrimeSumBoundAlt large₂ (recPJ h j hj) wL nus → EtaleWeightGaps.HypC large₂ (recPJ h j hj) H C2 A2 CR 0 CT (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn) ka wL wF Tn nP nW h0 nus) ∧ ∃ (G₀ : EtaleWeightGaps.GlobalFamilyData (recPJ h j hj) ka wL wF) (Sh : Finset ((recB h.toLawsCore).Cusp j wF)), Submodule.span (recB h.toLawsCore).KO (Sh : Set ((recB h.toLawsCore).Cusp j wF)) = ⊤ ∧ G₀.TiedW (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn) Gc Prw ∧ NoCommonZero (T.Q.Xo j) T.Q.c (fun i => (G₀.w i).1) ∧ ∀ G : EtaleWeightGaps.GlobalFamilyData (recPJ h j hj) ka wL wF, (∀ i, G.th' i ∈ Sh) → G.TiedTh (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn) Gc := by
    suffices hInputs : _ by exact hInputs
    intro hCI D T h hGam hSh hbad hA1 hUX hinj EX p j hj large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 Gc Prw
      hOwn hHP hPA hCK hThG2 hThG1 hH2 hG4 hPrw
  
    obtain ⟨hRows, h16⟩ := GlobalTheory.T.sizePageRows_of_sizePageAt D (recB h.toLawsCore) T.G.P j (recPJ h j hj) large₂ H C2 A2 CR CT ka wL wF Tn nP
      nW h0 hHP hPA hCK
  
    obtain ⟨hW, hWn, -, -⟩ := GlobalTheory.RunWeights.weights_below D (recB h.toLawsCore) T.G.P j (recPJ h j hj) large₂ H C2 A2 CR CT
      ka wL wF Tn nP nW h0 hj.1 hHP
  
    have hSpan : ∀ w, w ∈ ({wL, wF, (recPJ h j hj).wF0 wL wF, ka} : Set (WeightFamilies.Wt D j)) →
        8 * D.R.f * D.R.r + 4 ≤ w.n → ReciprocityTheory.ChartRestriction.G.PullbackSections.SpanAt (recPJ h j hj) w := fun w hw hn =>
      GlobalTheory.T.shortThetaSeries_span_cuspForms_weight hCI D T h hSh hGam hbad hUX j hj.1 hj.2 w
        (ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.lastPos_wtA h hj w (hW w hw).2.2.2) hn
    have hSB := GlobalTheory.T.runScalars_nonzero_bounded_supBound hCI D T h hGam hSh hA1 hinj EX p j hj large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 hOwn hHP hRows
      (hSpan wF (by simp) (hWn wF (by simp))) (hSpan _ (by simp) (hWn _ (by simp))) (hSpan ka (by simp) (hWn ka (by simp)))
    have hI4 := GlobalTheory.T.exists_integral_auxiliary_cuspForms_supBound hCI D T h hGam hinj EX p j hj large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 hHP hRows h16 hThG2 hThG1
  
    have hThL : GlobalTheory.RunIn.ThInt (recPJ h j hj) hinj EX wL := by
      have hW0 := hH2.1
      rw [GlobalTheory.RunIn.sW_eq_sOf] at hW0
      exact hW0
    obtain ⟨G₀, hG₀⟩ := GlobalTheory.T.exists_runData_generating_scaled_thetaLattice_weight hCI D T h hGam hinj EX p j hj large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 Gc Prw hHP hRows
      hThL hG4 hPrw
    obtain ⟨Sh, hSh', -, hTh⟩ := GlobalTheory.exists_short_span_thetaTie_of_scalars D (recB h.toLawsCore) T.G.P j (recPJ h j hj) large₂
      H.C1 H.A1 Gc (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn) ka wL wF Tn hSB hG4
    have hsW : (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn).sW ≠ 0 := by
      rw [GlobalTheory.RunIn.sW_eq_sOf]
      exact (GlobalTheory.RunIn.sOf_ne_zero_and_log_bounds D (recB h.toLawsCore) hinj EX j wL).1
    refine ⟨fun nus hnus => (FamilyHypotheses.hypC_iff large₂ (recPJ h j hj) H C2 A2 CR CT _ ka wL wF Tn nP nW h0 nus).2
        ⟨hHP, hSB, hnus, hH2, hI4⟩, G₀, Sh, hSh', hG₀, ?_, hTh⟩
    exact GlobalTheory.T.scaledThetaLattice_generators_noCommonZero hCI D T h EX j hj _ large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 Gc Prw hHP hsW G₀ hG₀
  have main := helper hchart D T h hgam hpar.sh hpar.bad hpar.lvA hpar.same hinj EX p j hj large₂ H C2 A2 7 CT
    ka wL wF Tn nP nW h0 (gcR large₂ (recB h.toLawsCore)) (38 * large₂.sc.L + PO D large₂) hown hpage.hyp hpage.page hpage.ck
    (fun w2 _ => hth w2) (fun _ w1 _ => hth w1) hH2 (growthConstantBound_gcR large₂ _) le_rfl
  have hC := main.1 _ hH1
  obtain ⟨-, Sh, hspan, -, -, hTied⟩ := main.2
  have hsK := hC.2.2.1.2.2.2.1
  have hspanka := GlobalTheory.T.shortThetaSeries_span_cuspForms_weight hchart D T h hpar.sh hgam hpar.bad hpar.same j hj1 hjm ka
    (ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.lastPos_wtA h hj ka (hwb.1 ka (by simp)).2.2.2) (hwb.2.1 ka (by simp))
  have hlat := GlobalTheory.T.weightModule_isLattice_of_shortSeries_span D T.toCore h.toLawsCore hgam large₂ H.CA hParA j ka _ (recPJ h j hj) _ wL wF hsK hspanka
    hC.2.2.2.2.1
  refine ⟨hC, hlat, hth, ⟨hpage.p13, fun σ => ?_, hpage.frd, hpage.r8, hpage.df⟩, Sh, hspan, hTied⟩
  rw [GlobalTheory.RunIn.sW_eq_sOf]
  exact ((GlobalTheory.RunIn.sOf_ne_zero_and_log_bounds D _ hinj EX j wL).2 σ).2.2.1

end GlobalTheory.RunJoin
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RunHypothesesFormsScalarsOfParameterConditionsStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem _root_.GlobalTheory.T.runHypotheses_formsScalars_of_parameterConditions : ∀ (D : D7) (T : Top D) (h : LawsP T) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), ParOK T EX p j → PageOK large₂ (recPJ h j hj) H C2 A2 CT ka wL wF Tn nP nW h0 → HypC large₂ (recPJ h j hj) H C2 A2 7 0 CT (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn) ka wL wF Tn nP nW h0 (nusR h j wL) ∧ LatAt (recB h.toLawsCore) j ka ∧ (∀ w : WeightFamilies.Wt D j, GlobalTheory.RunIn.ThInt (recPJ h j hj) hinj EX w) ∧ PageSupp D large₂ (recB h.toLawsCore) C2 A2 nW (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn) wL ∧ ∃ Sh : Finset ((recB h.toLawsCore).Cusp j wF), Submodule.span (recB h.toLawsCore).KO (Sh : Set ((recB h.toLawsCore).Cusp j wF)) = ⊤ ∧ ∀ G : GlobalFamilyData (recPJ h j hj) ka wL wF, (∀ i, G.th' i ∈ Sh) → G.TiedTh (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn) (gcR large₂ (recB h.toLawsCore)) := by
  exact @GlobalTheory.RunJoin.hypC_record
end
end
