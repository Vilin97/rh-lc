module

public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.GrowthConstantBoundGcR
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.IsBlockProd
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
public import Formalism.LocalToGlobal.ProjectiveLattices.RecPJThAllNeBot
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupBoundPageRows
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsShortThetaFamilyWithBlockPolynomialRules
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
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.GamAtOfLawsCore
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LeExpOfLogLe
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LogLeOfLePowMulPow
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Development.AbelianVarietyTheory.Definitions.ThetaValues.IsBlockProd
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.QuotientParamNonneg
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LowerBoundAtFramesFamilyWithScaledThetaRulesStatement
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.PageRowsOfLe
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.PageTwoLeLAndSigns
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ScaledFamily
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ScaledThetaLatticeGeneratorsNoCommonZeroStatement
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SizePageRowsOfSizePageAt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SupBoundsLeGeneratorConstantMulSize
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaLatticeWeightScalarNeZeroAndLogBounds
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaRunParametersAtTypePrimesProductStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.WeightsBelow
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.HarmonicGermValueChartIndependentStatement
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ScaledThetaLatticeLeSupLatticeEveryWeightStatement
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.SWEqSOf

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsShortThetaFamilyWithBlockPolynomialRulesStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn GlobalTheory.BlockTh GlobalTheory.EtaAn ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.exists_short_thetaFamily_with_block_polynomial_rules : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (h : LawsP T), GamAt T.toCore → ∀ (large₂ : SizeData₂ D) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j), ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → D.R.r ≤ w.n → w.LastPos → D.R.f * D.R.r * (D.R.r + 1) ≤ 2 * w.n → ∃ (N : ℕ) (w0 : Fin N → (recB h.toLawsCore).Cusp j w) (P₁ : MvPolynomial (LtN (T.Q.Dw j) w.n) T.Q.c.F), P₁ ∈ harmA T.Q.c (wtA w) w.n ∧ IsBlockProd P₁ ∧ ContainsTh (T.Q.Xo j) T.Q.c (T.nab j) 1 P₁ (fun k => ((w0 k).1 : T.R j)) ∧ (fun (B : WeightFamilies.Prov D) (X : PJ D B T.G.P j) (w1 : Fin N → B.Cusp j w) => Submodule.span (𝓞 B.KO) (Set.range w1) = X.thAll w) (recB h.toLawsCore) (recPJ h j hj) w0 ∧ N ≤ 2 * ((D.host.g 0 * D.host.g 1) ^ (D.R.f * D.R.r * w.n) * (Module.finrank ℚ (recB h.toLawsCore).KO * (1 + WeightAlgebra.DF w) ^ (D.R.f * D.R.r * w.n))) ∧ ∀ k σ, Real.log ((recB h.toLawsCore).supN j w σ (w0 k)) ≤ 400 * Zb D large₂ * w.size + 3 * D.R.f * D.R.r * w.n * large₂.sc.L + 5 * Real.log (Module.finrank ℚ (recB h.toLawsCore).KO) + Real.log |((NumberField.discr (recB h.toLawsCore).KO : ℤ) : ℝ)| / Module.finrank ℚ (recB h.toLawsCore).KO + 2 := by
  first | exact @GlobalTheory.BlockTh.theta_family_block | exact GlobalTheory.BlockTh.theta_family_block | (intros; apply GlobalTheory.BlockTh.theta_family_block <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LogTwoMulCountLeMulSize

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn GlobalTheory.BlockTh GlobalTheory.EtaAn ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.RunIn

theorem log_two_mul_count_le_mul_size : ∀ (D : D7) (B : WeightFamilies.Prov D) (large₂ : SizeData₂ D) (j : ℕ) (w : WeightFamilies.Wt D j) (N : ℕ) (Prw : ℝ), 2 ≤ large₂.sc.L → 0 < w.n → ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w → OPO large₂ B → 38 * large₂.sc.L + PO D large₂ ≤ Prw → N ≤ 2 * ((D.host.g 0 * D.host.g 1) ^ (D.R.f * D.R.r * w.n) * (Module.finrank ℚ B.KO * (1 + WeightAlgebra.DF w) ^ (D.R.f * D.R.r * w.n))) → Real.log N ≤ Prw * (w.size - 1) := by
  intro D B large₂ j w N Prw hL hn hrows hO hPrw hN
  obtain ⟨hg, -, -, -, -, -, -, hX, -⟩ := hrows

  set m : ℕ := D.R.f * D.R.r * w.n with hm
  have hN' : N ≤ (D.host.g 0 * D.host.g 1) ^ m * ((2 * Module.finrank ℚ B.KO) * (1 + WeightAlgebra.DF w) ^ m) := by
    calc N ≤ _ := hN
      _ = _ := by ring
  have hL0 : (0 : ℝ) ≤ large₂.sc.L := by linarith
  have hPO : 0 ≤ PO D large₂ := by unfold PO; positivity
  have hd : Real.log ((2 * Module.finrank ℚ B.KO : ℕ) : ℝ) ≤ PO D large₂ + 1 := by
    rcases Nat.eq_zero_or_pos (Module.finrank ℚ B.KO) with h0 | hpos
    · simp [h0]; linarith
    · have hk : ((Module.finrank ℚ B.KO : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
      push_cast
      rw [Real.log_mul (by norm_num) hk]
      have h2 : Real.log 2 ≤ 1 := by
        have := Real.log_two_lt_d9; linarith
      linarith [hO.1]
  have hX' : Real.log ((1 + WeightAlgebra.DF w : ℕ) : ℝ) ≤ 2 * large₂.sc.L := by
    push_cast; exact hX
  have key := log_le_of_le_pow_mul_pow (a := 9 * large₂.sc.L + 1) (c := 2 * large₂.sc.L) (P := PO D large₂ + 1)
    (by linarith) (by linarith) (by linarith) (hg 0) (hg 1) hd hX' hN'

  have hf : 0 < D.R.f := by
    have h1 := D.R.two_le_m
    have h2 := D.R.m_le_f
    have h3 : D.R.f = 2 * D.R.ord := rfl
    omega
  have hr : 0 < D.R.r := by
    have h1 := D.R.two_le_m
    have h2 := D.R.m_add_three_le_k
    have h3 : D.R.r = D.R.k + D.R.m - 1 := rfl
    omega
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by
    have : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (by positivity)
    exact_mod_cast this
  have hms : (m : ℝ) ≤ w.size - 1 := frn_le_size_sub_one w
  have hPrw0 : 0 ≤ Prw := by linarith
  calc Real.log N ≤ (m : ℝ) * (2 * (9 * large₂.sc.L + 1) + 2 * large₂.sc.L) + (PO D large₂ + 1) := key
    _ ≤ (m : ℝ) * (38 * large₂.sc.L + PO D large₂) := by nlinarith
    _ ≤ (m : ℝ) * Prw := by gcongr
    _ ≤ Prw * (w.size - 1) := by rw [mul_comm]; exact mul_le_mul_of_nonneg_left hms hPrw0

end GlobalTheory.RunIn
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsAdmissibleThetaLatticeGenerators

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin
open GlobalTheory.RunIn GlobalTheory.BlockTh

namespace GlobalTheory.RunJoin

noncomputable def scaledFamily {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j) (ka wL wF : WeightFamilies.Wt D j)
    (S : Scal B) {N : ℕ} (w0 : Fin N → B.Cusp j wL) (m : ℝ) : GlobalFamilyData X ka wL wF :=
  ⟨N, fun k => (S.sW : B.KO) • w0 k, 0, fun k => k.elim0, 0, fun k => k.elim0, fun k => k.elim0,
    fun k => k.elim0, 0, fun k => k.elim0, 0, 0, fun _ => m⟩

theorem tiedW_scaledFamily {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j) (ka wL wF : WeightFamilies.Wt D j)
    (S : Scal B) {N : ℕ} (w0 : Fin N → B.Cusp j wL) (a b G Prw : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hs : ∀ σ : B.KO →+* ℂ, Real.log ‖σ (S.sW : B.KO)‖ ≤ a)
    (hspan : Submodule.span (𝓞 B.KO) (Set.range w0) = X.thAll wL)
    (hw : ∀ k σ, Real.log (B.supN j wL σ (w0 k)) ≤ b) (hG : a + b ≤ G * wL.size)
    (hM : X.WWc S.sW wL ≤ B.Mlat j wL) (hN : Real.log N ≤ Prw * (wL.size - 1)) :
    (scaledFamily X ka wL wF S w0 (a + b)).TiedW S G Prw := by
  obtain ⟨hsm, -, hmean⟩ := GlobalTheory.LogSupMultiple.log_supN_bounds D B j wL
  have hspan' := GlobalTheory.ScaledGenerators.span_scaled X wL S.sW w0 hspan
  refine ⟨hspan', ?_, hN, ?_, ?_⟩
  · intro k
    apply hM
    rw [← hspan']
    exact Submodule.subset_span ⟨k, rfl⟩
  · intro σ k
    exact hsm σ (S.sW : B.KO) (w0 k) a b (by linarith) (hs σ) (hw k σ) hb ha
  · show (∑ _σ : B.KO →+* ℂ, (a + b)) / (Fintype.card (B.KO →+* ℂ) : ℝ) ≤ G * wL.size
    rw [hmean]
    exact hG

theorem log_le_of_le_two_mul_pow {N a b d m : ℕ} (hN0 : 0 < N) (hN : N ≤ 2 * (a ^ m * (d * b ^ m))) :
    Real.log N ≤ Real.log 2 + (m : ℝ) * (Real.log a + Real.log b) + Real.log d := by
  have hR : (N : ℝ) ≤ 2 * ((a : ℝ) ^ m * ((d : ℝ) * (b : ℝ) ^ m)) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN0
  have hA : (a : ℝ) ^ m ≠ 0 := by
    intro h0
    rw [h0, zero_mul, mul_zero] at hR
    linarith
  have hD : (d : ℝ) ≠ 0 := by
    intro h0
    rw [h0, zero_mul, mul_zero, mul_zero] at hR
    linarith
  have hB : (b : ℝ) ^ m ≠ 0 := by
    intro h0
    rw [h0, mul_zero, mul_zero, mul_zero] at hR
    linarith
  calc Real.log N ≤ Real.log (2 * ((a : ℝ) ^ m * ((d : ℝ) * (b : ℝ) ^ m))) := Real.log_le_log hNpos hR
    _ = Real.log 2 + ((m : ℝ) * Real.log a + (Real.log d + (m : ℝ) * Real.log b)) := by
      rw [Real.log_mul two_ne_zero (mul_ne_zero hA (mul_ne_zero hD hB)), Real.log_mul hA (mul_ne_zero hD hB),
        Real.log_mul hD hB, Real.log_pow, Real.log_pow]
    _ = Real.log 2 + (m : ℝ) * (Real.log a + Real.log b) + Real.log d := by ring

private theorem containsTh_of_eq_smul {D : D7} {T : Top D} (j : ℕ) {n N : ℕ}
    (P₁ : MvPolynomial (LtN (T.Q.Dw j) n) T.Q.c.F) (s : T.Q.c.F) (u v : Fin N → T.R j)
    (huv : ∀ k p y, v k p y = algebraMap T.Q.c.F _ s * u k p y)
    (hc : ContainsTh (T.Q.Xo j) T.Q.c (T.nab j) 1 P₁ u) : ContainsTh (T.Q.Xo j) T.Q.c (T.nab j) s P₁ v := by
  obtain ⟨jb, hjb, hq⟩ := hc
  refine ⟨jb, hjb, fun q => ?_⟩
  obtain ⟨f, hf, hfe⟩ := hq q
  refine ⟨f, hf, fun p y => ?_⟩
  rw [huv, hfe, map_one, one_mul]


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem exists_genOK : ∀ (D : D7) (T : Top D) (h : LawsP T) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), GlobalTheory.PtTie.Oriented T EX → PageOK large₂ (recPJ h j hj) H C2 A2 CT ka wL wF Tn nP nW h0 → ∃ G : GlobalFamilyData (recPJ h j hj) ka wL wF, GenOK h j hj large₂ G (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn) (cc D large₂ C2 A2 7 wL) := by
  intro D T h hinj EX p j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 hOr hP
  have hC := GlobalTheory.T.harmonic_germ_value_chart_independent
  have hGam : GamAt T.toCore := GlobalTheory.RunIn.gamAt_of_lawsCore D T.toCore h.toLawsCore
  obtain ⟨hrows, -⟩ := GlobalTheory.pageRows_of_pageAt D _ _ j (recPJ h j hj) large₂ H C2 A2 7 CT ka wL wF Tn nP nW h0
    hP.hyp hP.page hP.ck
  obtain ⟨hL, -, hr6, hlam, -, -⟩ := GlobalTheory.page_two_le_L_and_signs D _ _ j (recPJ h j hj) large₂ H C2 A2 7 CT ka wL wF Tn
    nP nW h0 hP.hyp hrows
  obtain ⟨hw4, -⟩ := GlobalTheory.RunWeights.weights_below D _ _ j (recPJ h j hj) large₂ H C2 A2 7 CT ka wL wF Tn nP nW h0 hj.1
    hP.hyp
  obtain ⟨hDF, hnk, hrn, hlast⟩ := hw4 wL (by simp)
  have hrowsL := GlobalTheory.pageRows_of_le D large₂ j ka wL (by linarith) hDF hnk hrows
  have hS := GlobalTheory.RunIn.sW_eq_sOf (recB h.toLawsCore) hinj EX p ka wL wF Tn
  have hsOf := GlobalTheory.RunIn.sOf_ne_zero_and_log_bounds D (recB h.toLawsCore) hinj EX j wL
  have hsupp : EtaleWeightGaps.PageSupp D large₂ (recB h.toLawsCore) C2 A2 nW (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn) wL :=
    ⟨hP.p13, fun σ => by rw [hS]; exact (hsOf.2 σ).2.2.1, hP.frd, hP.r8, hP.df⟩
  obtain ⟨hC1, hA1, hCc, hAc, hCR, h12⟩ := hP.tie
  have htie : TieC (⟨0, 2, 0, 2, 0, 2, 0, 4, 7⟩ : KAdm) H 1 4 0 11 C2 A2 7 :=
    ⟨hC1, hA1, hCc, hAc, hCR, rfl, rfl, h12, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl⟩
  obtain ⟨-, -, -, hfrr⟩ := GlobalTheory.T.thetaRunParameters_at_typePrimes_product D _ _ j (recPJ h j hj) _ 1 4 0 11
    (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn) large₂ H C2 A2 7 CT ka wL wF Tn nP nW h0 hP.hyp htie hP.page hsupp
  obtain ⟨N, w0, P₁, hharm, hblk, hcont, hspan, hNle, hsup⟩ :=
    GlobalTheory.T.exists_short_thetaFamily_with_block_polynomial_rules hC D T h hGam large₂ j hj wL hrowsL hL hrn hlast hfrr
  have hO : OPO large₂ (recB h.toLawsCore) := by
    obtain ⟨-, hSet, -⟩ := hP.hyp
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hO, -⟩ := hSet
    exact hO
  have hN0 : 0 < N := by
    obtain ⟨jb, -, -⟩ := hcont
    exact Fin.pos (jb 0)
  obtain ⟨N', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN0.ne'
  have hn0 : 0 < wL.n := by omega
  have hsize : (1 : ℝ) ≤ wL.size := by
    have h1 := GlobalTheory.RunIn.frn_le_size_sub_one wL
    have h2 : (0 : ℝ) ≤ ((D.R.f * D.R.r * wL.n : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hM : (recPJ h j hj).WWc (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn).sW wL ≤
      (recB h.toLawsCore).Mlat j wL := by
    rw [hS]
    exact GlobalTheory.T.scaledThetaLattice_le_supLattice_every_weight D T h j hj hinj EX hOr wL
  have hNlog := GlobalTheory.RunIn.log_two_mul_count_le_mul_size D (recB h.toLawsCore) large₂ j wL (N' + 1)
    (38 * large₂.sc.L + PO D large₂) hL hn0 hrowsL hO le_rfl hNle
  have ha : 0 ≤ lamStar D * wL.size := mul_nonneg hlam (by linarith)
  have hs : ∀ σ : (recB h.toLawsCore).KO →+* ℂ,
      Real.log ‖σ ((scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn).sW : (recB h.toLawsCore).KO)‖ ≤
        lamStar D * wL.size := fun σ => by
    rw [hS]
    exact (hsOf.2 σ).2.2.2
  have hGc := (GlobalTheory.RunIn.sup_bounds_le_Gc D (recB h.toLawsCore) large₂ j wL D.host.pde hL hn0).2.2
  have hpde : 0 ≤ Real.log (D.host.pde : ℝ) := Real.log_natCast_nonneg _
  have hfin : 0 ≤ Real.log (Module.finrank ℚ (recB h.toLawsCore).KO : ℝ) := Real.log_natCast_nonneg _
  have hdisc : 0 ≤ Real.log |((NumberField.discr (recB h.toLawsCore).KO : ℤ) : ℝ)| /
      Module.finrank ℚ (recB h.toLawsCore).KO :=
    div_nonneg (by rw [Real.log_abs]; exact Real.log_intCast_nonneg _) (Nat.cast_nonneg _)
  have hZ : 0 ≤ Zb D large₂ := by
    unfold Zb
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (by linarith)
  have hGg : WeightAlgebra.Gc large₂ (recB h.toLawsCore) (1009 * Zb D large₂) D.host.pde ≤ gcR large₂ (recB h.toLawsCore) := by
    unfold gcR
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hT := tiedW_scaledFamily (recPJ h j hj) ka wL wF (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn) w0
    (lamStar D * wL.size) _ (gcR large₂ (recB h.toLawsCore)) (38 * large₂.sc.L + PO D large₂) ha
    (add_nonneg (add_nonneg (add_nonneg (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hZ) (by linarith))
      (mul_nonneg (by positivity) (by linarith))) (mul_nonneg (by norm_num) hfin)) hdisc) (by norm_num))
    hs hspan hsup (by nlinarith) hM hNlog
  refine ⟨scaledFamily (recPJ h j hj) ka wL wF (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn) w0 _, hT,
    Nat.succ_pos N', ?_, ?_, ?_⟩
  · show Real.log ((N' + 1 : ℕ) : ℝ) ≤ nbR large₂ wL
    have hl := log_le_of_le_two_mul_pow (Nat.succ_pos N') hNle
    unfold nbR
    push_cast at hl ⊢
    linarith [hO.1]
  · exact GlobalTheory.T.scaledThetaLattice_generators_noCommonZero hC D T h EX j hj (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn) large₂ H C2 A2 7 CT ka wL wF
      Tn nP nW h0 _ _ hP.hyp (by rw [hS]; exact hsOf.1) _ hT
  · exact GlobalTheory.T.lower_bound_at_frames_family_with_scaled_thetaRules hC D T h EX j hj _ 1 4 0 11 (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn) large₂ H C2 A2 7 CT
      ka wL wF Tn nP nW h0 hP.hyp htie hP.page hsupp P₁ hharm hblk N' _
      (containsTh_of_eq_smul j P₁ _ _ _ (fun k q y => by
        simp only [scaledFamily]
        try rw [Submodule.coe_smul_of_tower]
        try rw [Submodule.coe_smul]
        try rw [SetLike.val_smul]
        simp only [Pi.smul_apply]
        exact Algebra.smul_def _ _) hcont) (p14R wL) (le_max_right _ _)

end GlobalTheory.RunJoin
end
end
