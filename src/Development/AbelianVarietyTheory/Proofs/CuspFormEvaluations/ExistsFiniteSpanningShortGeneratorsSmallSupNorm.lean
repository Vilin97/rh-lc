module

public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupBoundPageRows
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LatOfLamSt
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
public import Formalism.LocalToGlobal.ProjectiveLattices.RecPJThAllNeBot
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsClearingIntegersPrincipalDatumHostStatement
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsShortHarmonicFamilyUnimodularStatement
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Formalism.LocalToGlobal.ProjectiveLattices.HasDataCondition
public import Formalism.LocalToGlobal.ProjectiveLattices.XcLat
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CuspFormHalfSupAtOrthonormalFrameFirstMinStatement
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.EqZeroOfForallAlgHom
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LogExpMulLeOfGeneratorSupBound
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicCoefficientSplitting
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.NormShortGeneratorEvalLeOrthonormalFrame
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.UnitaryDatumNumbersForSupBoundsStatement
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShortThetaRuleLinearInHarmonicPolynomialStatement
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SupBoundsLeGeneratorConstantMulSizeStatement
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.NumericalConsequencesOfPinsStatement
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.WeightFloorInequalities
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.IntegralValueOfChartValues
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.WeightFloorInequalities

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.NormShortGeneratorEvalLeOrthonormalFrameStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

theorem _root_.GlobalTheory.T.norm_short_generator_eval_le_orthonormal_frame : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → 1 ≤ r → ∀ t : ℝ, 0 < t → (∀ k τ, (U.X k).c τ = t) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → r ≤ n → ∀ d : DeltaDat Xo c n, d.IsLev → 0 < d.pd → l.A = 1 → d.l₂.A = 1 → (∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂) → (∃ ph ψ x₀, d.PhiPin ph ψ x₀) → UnitC d → ∀ (Λ : GenLat E n) (N : ℕ) (x0 : Fin n → Dw.La) (P : MvPolynomial (LtN Dw n) c.F) (f : Rul Xo c), Λ.Unimod → Λ.TrivAt d.l₂.M → Λ.LevOK N d.l₂.M → (∃ β : c.F, β ≠ 0 ∧ BetaIs (Dw := Dw) c Λ β ∧ BetaAbs (Dw := Dw) c Λ β) → P ∈ harmL c Λ a → IsShortRule Xo c d Λ N x0 P f → ∀ k (x : (U.X k).dom), (U.X k).IsOrtho x.1 → ∀ lam : ℝ, 0 < lam → lam ^ 2 ≤ (U.X k).firstMinimumSq x.1 → ‖Formalism.L2.PjFree.toC (evR Xo c f (U.un k x))‖ ≤ (d.pd : ℝ) ^ (fdeg E * r * n) * ((∑ m ∈ P.support, ‖σ (P.coeff m)‖) * (Real.pi * Real.exp 1 * t * (Formalism.L2.Pj.DF Dw a : ℕ)) ^ (((Formalism.L2.Pj.DF Dw a : ℕ) : ℝ) / 2) * Real.sqrt 2 * (1 + 4 * Real.sqrt (2 * (fdeg E * r : ℕ) * n) * (2 * (fdeg E : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rdE E) / (Real.sqrt Real.pi * lam)) ^ (fdeg E * r * n)) := by
  first | exact @GlobalTheory.Dict.ShortPoint.norm_evR_le | exact GlobalTheory.Dict.ShortPoint.norm_evR_le | (intros; apply GlobalTheory.Dict.ShortPoint.norm_evR_le <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LogSupNormShortThetaGeneratorLe

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

namespace GlobalTheory.RunIn



theorem log_sup_short_generator_le : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (_h : LawsP T), GamAt T.toCore → ∀ (large₂ : SizeData₂ D) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j), ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → D.R.r ≤ w.n → LastPos (T.Q.Dw j) (wtA w) → LawsSh T → (T.dδ j w.n).l₂.A = 1 → ∀ (Λ : GenLat D.host.E w.n) (N : ℕ) (x0 : Fin w.n → (T.Q.Dw j).La) (P : MvPolynomial (LtN (T.Q.Dw j) w.n) T.Q.c.F) (g : T.R j), Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ j w.n).l₂.M → Λ.LevOK N (T.dδ j w.n).l₂.M → AdmX (l := T.Q.l) (decide (w.n = D.R.nV)) x0 → P ∈ harmL T.Q.c Λ (wtA w) → IsShortRule (T.Q.Xo j) T.Q.c (T.dδ j w.n) Λ N x0 P g → g ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n → ∀ (σ : T.Q.c.F →+* ℂ) (ℓ : ℝ), 0 ≤ ℓ → l1At σ P ≤ Real.exp ℓ → Real.log (T.Ns j w σ g) ≤ ℓ + 10 * large₂.sc.L * absA w + 200 * D.R.f * D.R.r * w.n * large₂.sc.L := by
  intro hCh D T hT hG large₂ j hj w hRows hL hr hLast hSh hA Λ N x0 P g hU hTb hTM hLev hX hP hS hg σ ℓ hℓ hl1
  obtain ⟨hfd, hrd, hrd1, hf1, hr1, hxi, hDF, habs, hc, hlie, hlA, hpde, hpde', hl1g⟩ := GlobalTheory.T.unitaryDatumNumbers_for_supBounds D T hT j hj w
  have hRw := hRows
  obtain ⟨-, hlrd, -, -, hlf, hlp, hlp', hlDF, hln⟩ := hRows
  set σ' := goodOf T.Q.c σ with hσ'
  have hgood : GoodEmb T.Q.c σ' := goodEmb_goodOf _ σ
  have hgC : g ∈ T.C j w :=
    hSh.8 j hj (wtA w) w.n (dom_wtA w) hLast (dom_wtA w) hLast ⟨hg, Λ, N, x0, P, hU, hTb, hTM, hLev, hX, hP, hS⟩
  obtain ⟨Cls, _, _, δ, gdet, hcmp⟩ := hSh.6 j hj w.n
  have hUC : GlobalTheory.Dict.UnitC (T.dδ j w.n) := FiniteOrderRule.unitC_of_cmp _ _ _ _ _ _ _ _ Cls δ gdet hcmp
  obtain ⟨p, hp, hpd⟩ := hSh.4
  have hpdw : (T.dδ j w.n).pd = p := hpd j hj w.n
  have hp0 : 0 < p := by rcases hp with rfl | rfl <;> assumption
  have hlogp : Real.log p ≤ large₂.sc.L := by rcases hp with rfl | rfl <;> assumption
  obtain ⟨ph, ψ, xψ, -, hpin, -⟩ := hSh.5 j hj w.n hr
  have hunf : IsUnf (T.U j σ') := hT.unf j hj σ' hgood
  have hNs : T.Ns j w σ g = lieFac (T.Q.Dw j) (xiR D) (wtA w) *
      supN (T.U j σ').X (laU (T.U j σ') (wtA w) w.n) (rdU (T.U j σ') g) := rfl
  rw [hNs, hlie]
  set S := supN (T.U j σ').X (laU (T.U j σ') (wtA w) w.n) (rdU (T.U j σ') g) with hSdef
  have hS0 : 0 ≤ S := by rw [hSdef]; unfold supN; exact ENNReal.toReal_nonneg
  have hL0 : (0:ℝ) ≤ large₂.sc.L := by linarith
  have ha0 : (0:ℝ) ≤ absA w := by rw [habs]; positivity
  rcases hS0.eq_or_lt with hS00 | hSpos
  · rw [← hS00, mul_zero, Real.log_zero]
    positivity
  obtain ⟨k, xf, -, hortho, hSle, hla, hlog⟩ :=
    GlobalTheory.T.cuspForm_halfSup_at_orthonormalFrame_firstMin D T hT hG large₂ j hj w hRw hL hr hLast σ' hgood g hgC hSpos
  set lam := Real.sqrt (((T.U j σ').X k).firstMinimumSq xf.1) with hlam
  have hlam0 : 0 < lam := Real.sqrt_pos.mpr hla
  have hlam2 : lam ^ 2 = ((T.U j σ').X k).firstMinimumSq xf.1 := Real.sq_sqrt hla.le
  have hv := GlobalTheory.T.norm_short_generator_eval_le_orthonormal_frame hCh D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c σ' D.R.r
    (Formalism.L2.PjFree.Unf.ofPj (T.U j σ')) ((Formalism.L2.PjFree.goodEmb_iff σ').mpr hgood)
    ((Formalism.L2.PjFree.isUnf_ofPj _).mpr hunf) hr1 (2 * xiR D) (by linarith) (hc σ' hgood) (wtA w) w.n
    (dom_wtA w) hr (T.dδ j w.n) (hSh.2 j hj w.n) (by rw [hpdw]; exact hp0) hlA hA (hSh.3 j hj w.n)
    ⟨ph, ψ, xψ, hpin⟩ hUC Λ N x0 P g hU hTM hLev (hSh.1 j hj w.n (hT.kPsi j hj) Λ hU hTb) hP hS
    k xf hortho lam hlam0 hlam2.le
  have hp1eq : (∑ m ∈ P.support, ‖σ' (P.coeff m)‖) = l1At σ P := hl1g _ σ P
  rw [hfd, hp1eq] at hv
  have hcle : ((T.dδ j w.n).pd : ℝ) ^ (D.R.f * D.R.r * w.n) ≤
      Real.exp (D.R.f * D.R.r * w.n * large₂.sc.L) := by
    rw [hpdw]
    have hp' : (0:ℝ) < p := by exact_mod_cast hp0
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos hp']
    apply Real.exp_le_exp.mpr
    push_cast
    have hfrn : (0:ℝ) ≤ D.R.f * D.R.r * w.n := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hlogp hfrn]
  have hp1 : 0 ≤ l1At σ P := by unfold l1At; exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  exact GlobalTheory.log_exp_mul_le_of_generator_sup_bound D.R.f D.R.r w.n (Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w))
    large₂.sc.L ℓ (absA w) (rdE D.host.E) lam (2 * xiR D) _ S _ (l1At σ P) hL hf1 hr1 hr
    (by rw [habs]; exact_mod_cast hDF) (by rw [habs]; exact hlDF) hln hlf hrd1 (by rw [hrd]; exact hlrd)
    hlam0 (by rw [hlam2]; exact hlog) (by linarith) hℓ hp1 hl1 (by positivity) hcle hS0 hSle hv

end GlobalTheory.RunIn
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LogSupNormShortThetaGeneratorLeStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

theorem _root_.GlobalTheory.T.log_supNorm_shortThetaGenerator_le : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (_h : LawsP T), GamAt T.toCore → ∀ (large₂ : SizeData₂ D) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j), ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → D.R.r ≤ w.n → LastPos (T.Q.Dw j) (wtA w) → LawsSh T → (T.dδ j w.n).l₂.A = 1 → ∀ (Λ : GenLat D.host.E w.n) (N : ℕ) (x0 : Fin w.n → (T.Q.Dw j).La) (P : MvPolynomial (LtN (T.Q.Dw j) w.n) T.Q.c.F) (g : T.R j), Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ j w.n).l₂.M → Λ.LevOK N (T.dδ j w.n).l₂.M → AdmX (l := T.Q.l) (decide (w.n = D.R.nV)) x0 → P ∈ harmL T.Q.c Λ (wtA w) → IsShortRule (T.Q.Xo j) T.Q.c (T.dδ j w.n) Λ N x0 P g → g ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n → ∀ (σ : T.Q.c.F →+* ℂ) (ℓ : ℝ), 0 ≤ ℓ → l1At σ P ≤ Real.exp ℓ → Real.log (T.Ns j w σ g) ≤ ℓ + 10 * large₂.sc.L * absA w + 200 * D.R.f * D.R.r * w.n * large₂.sc.L := by
  first | exact @GlobalTheory.RunIn.log_sup_short_generator_le | exact GlobalTheory.RunIn.log_sup_short_generator_le | (intros; apply GlobalTheory.RunIn.log_sup_short_generator_le <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShortGeneratorMemSpanSmallSupNormShortGenerators

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.RunIn

theorem fg_of_trivAt_even {E : Type} [Field E] [NumberField E] {n : ℕ} (Λ : GenLat E n) {bad : ℕ}
    (h2 : 2 ∣ bad) (h : Λ.TrivAt bad) : Λ.La.FG := by
  obtain ⟨k, hk, hle, -⟩ := h
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [Nat.coprime_zero_left] at hk
    omega
  have hstd : (stdLat E n).FG := by
    unfold stdLat
    exact Submodule.fg_pi fun _ => Submodule.fg_unit 1
  have hkO : (k : 𝓞 E) ≠ 0 := by exact_mod_cast hk0
  have hinj : Function.Injective (LinearMap.lsmul (𝓞 E) (Fin n → E) (k : 𝓞 E)) :=
    LinearMap.lsmul_injective hkO
  refine Submodule.fg_of_fg_map_injective _ hinj ?_
  have hN := isNoetherian_of_fg_of_noetherian _ hstd
  refine isNoetherian_submodule.1 hN _ ?_
  rintro _ ⟨v, hv, rfl⟩
  exact hle (Submodule.smul_mem_smul (Ideal.subset_span rfl) hv)

theorem sh_mem_span_small : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (h : LawsP T), GamAt T.toCore → ∀ (large₂ : SizeData₂ D) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j), ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → D.R.r ≤ w.n → w.LastPos → LawsSh T → (T.dδ j w.n).l₂.A = 1 → ∀ g ∈ T.sh j w, g ∈ Submodule.span T.Q.c.F {g' : T.R j | g' ∈ T.sh j w ∧ ∀ σ, Real.log (T.Ns j w σ g') ≤ 400 * Zb D large₂ * w.size} := by
  intro hCI D T h hG large₂ j hj w hP hL hrn hlp hS hA g hg
  obtain ⟨hgs, Λ, N, x0, P, hU, hT1, hT2, hLev, hAdm, hPh, hR⟩ := hg
  obtain ⟨-, -, -, -, -, hfd, -, hrd, hfr, hf1, -⟩ := GlobalTheory.T.exists_clearing_integers_principalDatum_host D large₂.sc.L hL hP.2.1 hP.2.2.1 hP.2.2.2.1
  have hr : (T.Q.Dw j).p + (T.Q.Dw j).q = D.R.r := ((GlobalTheory.T.numerical_consequences_of_pins D T.Q h.pins).2.2.2.2.2.2 j hj).1
  have hfg : Λ.La.FG := fg_of_trivAt_even Λ (by
    unfold badN
    have h2 : 2 ∣ D.host.QS := (D.host.mem_small_iff.1 D.host.two_mem_small).2
    exact ((h2.mul_right _).mul_right _).mul_right _) hT1
  have hdf : (Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w) : ℝ) ≤ (Formalism.MainNotions.WeightAlgebra.DF w : ℝ) := by
    exact_mod_cast ReciprocityTheory.ChartRestriction.G.PullbackSections.DF_wtA_le T j w
  have e : ((Formalism.MainNotions.WeightAlgebra.DF w : ℕ) : ℝ) = absA w := by
    unfold absA Formalism.MainNotions.WeightAlgebra.DF degP
    push_cast
    rfl
  obtain ⟨S, hS1, hS2, -⟩ := GlobalTheory.T.exists_short_harmonic_family_unimodular D.host.E T.Q.H (T.Q.Dw j) T.Q.l T.Q.c w.n Λ hU hfg (hr ▸ hrn) (wtA w)
    large₂.sc.L hL hrd (by rw [hfd]; exact hP.2.2.2.2.1)
    ((Real.log_le_log (by positivity) (by linarith)).trans hP.2.2.2.2.2.2.2.1) hP.2.2.2.2.2.2.2.2
  obtain ⟨m, cf, Q, hsum⟩ := Submodule.mem_span_set'.1 (hS2 P hPh.1)
  have hQ : ∀ i, (Q i).1 ∈ harmL T.Q.c Λ (wtA w) := fun i => (hS1 _ (Q i).2).1
  choose gs hgs1 hgs2 using fun i =>
    (hS.shTot j hj (wtA w) w.n (dom_wtA w) Λ N x0 (Q i).1 hU hT1 hT2 hLev hAdm (hQ i)).2
  have hlin := GlobalTheory.T.shortThetaRule_linear_in_harmonic_polynomial hCI D T h hS j hj w Λ N x0 hU hT2 hLev m cf (fun i => (Q i).1) g gs hQ hgs hgs1
    (by rw [hsum]; exact hR) hgs2
  rw [hlin]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span
    ⟨⟨hgs1 i, Λ, N, x0, (Q i).1, hU, hT1, hT2, hLev, hAdm, hQ i, hgs2 i⟩, fun σ => ?_⟩)
  have hL0 : 0 ≤ large₂.sc.L := by linarith
  have hA0 : 0 ≤ absA w := by rw [← e]; positivity
  have hb : Real.log (l1At σ (Q i).1) ≤ 140 * D.R.r * large₂.sc.L * absA w := by
    refine ((hS1 _ (Q i).2).2 σ).trans ?_
    rw [hr, ← e]
    exact mul_le_mul_of_nonneg_left hdf (by positivity)
  have hl1 : l1At σ (Q i).1 ≤ Real.exp (140 * D.R.r * large₂.sc.L * absA w) :=
    (Real.le_exp_log _).trans (Real.exp_le_exp.2 hb)
  have hsup := GlobalTheory.T.log_supNorm_shortThetaGenerator_le hCI D T h hG large₂ j hj w hP hL hrn (ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.lastPos_wtA h hj w hlp) hS hA
    Λ N x0 (Q i).1 (gs i) hU hT1 hT2 hLev hAdm (hQ i) (hgs2 i) (hgs1 i) σ _ (by positivity) hl1
  exact hsup.trans (GlobalTheory.T.supBounds_le_generatorConstant_mul_size D (recB h.toLawsCore) large₂ j w 0 hL (by omega)).1

end GlobalTheory.RunIn
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShortGeneratorMemSpanSmallSupNormShortGeneratorsStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.shortGenerator_mem_span_small_supNorm_shortGenerators : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (h : LawsP T), GamAt T.toCore → ∀ (large₂ : SizeData₂ D) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j), ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → D.R.r ≤ w.n → w.LastPos → LawsSh T → (T.dδ j w.n).l₂.A = 1 → ∀ g ∈ T.sh j w, g ∈ Submodule.span T.Q.c.F {g' : T.R j | g' ∈ T.sh j w ∧ ∀ σ, Real.log (T.Ns j w σ g') ≤ 400 * Zb D large₂ * w.size} := by
  first | exact @GlobalTheory.RunIn.sh_mem_span_small | exact GlobalTheory.RunIn.sh_mem_span_small | (intros; apply GlobalTheory.RunIn.sh_mem_span_small <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFiniteSpanningShortGeneratorsSmallSupNorm

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.RunIn

theorem exists_finset_span_top_of_span {O K R : Type} [CommRing O] [Field K] [Algebra O K] [AddCommGroup R]
    [Module K R] [Module O R] [IsScalarTower O K R] (C : Submodule K R) [FiniteDimensional K C] (s A : Set R)
    (hA : A ⊆ C) (hs : ∀ g ∈ s, g ∈ Submodule.span K A)
    (htop : Submodule.span K
      (((Submodule.span O s).comap (C.subtype.restrictScalars O) : Submodule O C) : Set C) = ⊤) :
    ∃ Sh : Finset C, (∀ g ∈ Sh, (g : R) ∈ A) ∧ Submodule.span K (Sh : Set C) = ⊤ := by
  classical
  set A' : Set C := {x | (x : R) ∈ A} with hA'
  have hsub : ∀ x : C, (x : R) ∈ Submodule.span K A → x ∈ Submodule.span K A' := by
    intro x hx
    have himg : (C.subtype '' A') = A := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact hz
      · intro hy
        exact ⟨⟨y, hA hy⟩, hy, rfl⟩
    rw [← himg, ← Submodule.map_span] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have hyx' : y = x := Subtype.ext hyx
    rwa [← hyx']
  have htop' : Submodule.span K A' = ⊤ := by
    rw [eq_top_iff, ← htop, Submodule.span_le]
    intro x hx
    apply hsub
    have hx' : (x : R) ∈ Submodule.span O s := hx
    exact (Submodule.span_le.mpr hs) (Submodule.span_le_restrictScalars O K s hx')
  obtain ⟨b, hbA, hbspan, hbli⟩ := exists_linearIndependent K A'
  have hbfin : b.Finite := hbli.setFinite
  refine ⟨hbfin.toFinset, ?_, ?_⟩
  · intro g hg
    exact hbA (hbfin.mem_toFinset.mp hg)
  · rw [hbfin.coe_toFinset, hbspan, htop']


set_option synthInstance.maxHeartbeats 400000 in
theorem exists_short_family_small : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (h : LawsP T), GamAt T.toCore → ∀ (large₂ : SizeData₂ D) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j), ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → D.R.r ≤ w.n → w.LastPos → LawsSh T → (T.dδ j w.n).l₂.A = 1 → ReciprocityTheory.ChartRestriction.G.PullbackSections.SpanAt (recPJ h j hj) w → ∃ Sh : Finset ((recB h.toLawsCore).Cusp j w), (∀ g ∈ Sh, g ∈ (recPJ h j hj).shortTh w ∧ ∀ σ, Real.log ((recB h.toLawsCore).supN j w σ g) ≤ 400 * Zb D large₂ * w.size) ∧ Submodule.span (recB h.toLawsCore).KO (Sh : Set ((recB h.toLawsCore).Cusp j w)) = ⊤ := by
  intro hC D T h hG large₂ j hj w hP hL hn hw hS hA hsp
  have hlp := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.lastPos_wtA h hj w hw
  have hdom := dom_wtA w
  have hshC : T.sh j w ⊆ T.C j w := hS.shCusp j hj (wtA w) w.n hdom hlp hdom hlp
  have hsmall := GlobalTheory.T.shortGenerator_mem_span_small_supNorm_shortGenerators hC D T h hG large₂ j hj w hP hL hn hw hS hA
  unfold ReciprocityTheory.ChartRestriction.G.PullbackSections.SpanAt at hsp
  simp only [recPJ, recB, mkX, mkB] at hsp ⊢
  unfold spanIn cutN cutR at *
  have hmemC : ∀ x, x ∈ T.C j w → x ∈ (T.C j w ⊓ ⨅ (_ : ¬InR D j), ⊥ : Submodule T.Q.c.F (T.R j)) := by
    intro x hx
    simp [hx, hj]
  have : FiniteDimensional T.Q.c.F (T.C j w) := h.toLawsCore.fd j hj w
  have : FiniteDimensional T.Q.c.F (T.C j w ⊓ ⨅ (_ : ¬InR D j), ⊥ : Submodule T.Q.c.F (T.R j)) :=
    Submodule.finiteDimensional_of_le inf_le_left
  have hs : ∀ g ∈ T.sh j w, g ∈ Submodule.span T.Q.c.F
      {g' | g' ∈ (T.C j w ⊓ ⨅ (_ : ¬InR D j), ⊥ : Submodule T.Q.c.F (T.R j)) ∧ g' ∈ T.sh j w ∧
        ∀ σ, Real.log (T.Ns j w σ g') ≤ 400 * Zb D large₂ * w.size} := by
    intro g hg
    refine Submodule.span_mono ?_ (hsmall g hg)
    rintro x ⟨hx1, hx2⟩
    exact ⟨hmemC x (hshC hx1), hx1, hx2⟩
  obtain ⟨Sh, hShA, hShspan⟩ := exists_finset_span_top_of_span (O := 𝓞 T.Q.c.F)
    (T.C j w ⊓ ⨅ (_ : ¬InR D j), ⊥) (T.sh j w)
    {g' | g' ∈ (T.C j w ⊓ ⨅ (_ : ¬InR D j), ⊥ : Submodule T.Q.c.F (T.R j)) ∧ g' ∈ T.sh j w ∧
      ∀ σ, Real.log (T.Ns j w σ g') ≤ 400 * Zb D large₂ * w.size}
    (fun x hx => hx.1) hs hsp
  refine ⟨Sh, fun g hg => ?_, hShspan⟩
  obtain ⟨_, hgs, hgb⟩ := hShA g hg
  refine ⟨Submodule.subset_span hgs, fun σ => ?_⟩
  rw [if_pos hj]
  exact hgb σ

end GlobalTheory.RunIn
end
end
