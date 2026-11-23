module

public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.CuspFrame
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.NearNonzeroTerms
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CanonicalFlagExistsUniqueSemistable
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CountHypPAtAddQAt
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSizeEqLeast
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsRadicalSpanPrimeOfNcardPrimesOverEqFinrank
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LayerProdCountMulDensityLeTwo
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHasFlag
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
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PowLePowRatio
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SizeIntegralsAndCardCompositions
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralTypeLe

section

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.FlagPush

open GlobalTheory.FlagMeas

theorem simplex_meas (a : ℕ) : MeasurableSet (simplexH a) := by
  have h : simplexH a = (⋂ i : Fin a, ⋂ k : Fin a, {τ : Fin a → ℝ | i < k → τ i < τ k}) ∩
      ⋂ i : Fin a, ({τ : Fin a → ℝ | 0 < τ i} ∩ {τ | τ i < 1 / 2}) := by
    ext τ
    simp only [simplexH, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
    exact ⟨fun ⟨h1, h2⟩ => ⟨fun i k hik => h1 hik, fun i => h2 i⟩,
      fun ⟨h1, h2⟩ => ⟨fun i k hik => h1 i k hik, fun i => h2 i⟩⟩
  rw [h]
  refine MeasurableSet.inter (MeasurableSet.iInter fun i => MeasurableSet.iInter fun k => ?_)
    (MeasurableSet.iInter fun i => (measurableSet_lt measurable_const (measurable_pi_apply i)).inter
      (measurableSet_lt (measurable_pi_apply i) measurable_const))
  by_cases hik : i < k
  · simpa [hik] using measurableSet_lt (measurable_pi_apply i) (measurable_pi_apply k)
  · simp [hik]

theorem dens_meas (n f : ℕ) {a : ℕ} (j : Fin a → ℕ) : Measurable (FlagMeas.dens n f j) := by
  show Measurable fun τ => FlagMeas.dens n f j τ
  simp only [FlagMeas.dens, layerProd, id]
  fun_prop

theorem mem_simplex {I : AutInst} {x : I.GA} {a : ℕ} {j : Fin a → ℕ} {τ : Fin a → ℝ}
    (h : HasType I x j τ) : τ ∈ simplexH a := by
  obtain ⟨S, ⟨-, -, -, hmono, hτ, -⟩, -⟩ := h
  exact ⟨hmono, fun i => ⟨(hτ i).1, (hτ i).2.1⟩⟩

theorem lintegral_type_le : GlobalTheory.FlagMeas.FlagMeasureBound → ∀ (B : RowsAut) (p q : ℕ), SigIs B p q → 2 * q + 2 ≤ B.I.n → ∀ (a : ℕ) (j : Fin a → ℕ), 1 ≤ a → (∀ i, 1 ≤ j i) → ∑ i, j i ≤ q → ∀ (G : (Fin a → ℝ) → ENNReal) (Φ : B.I.GA → ENNReal), Measurable G → (∀ x τ, HasType B.I x j τ → Φ x ≤ G τ) → ∫⁻ x in {x | ∃ τ, HasType B.I x j τ} ∩ B.fund, Φ x ∂(B.I.muA B.μf) ≤ B.I.muA B.μf B.fund * ENNReal.ofReal (GlobalTheory.FlagMeas.kapBd B.I.E p q j) * ∫⁻ τ in GlobalTheory.FlagMeas.simplexH a, G τ * ENNReal.ofReal (GlobalTheory.FlagMeas.dens B.I.n B.I.f j τ) := by
  intro hFMB B p q hSig hn a j ha hj hsum G Φ hG hΦ
  have := B.haar
  have := B.sf
  obtain ⟨s, hs, hT, hsτ⟩ := GlobalTheory.FlagMeas.type_measurable B.I a j
  set T : Set B.I.GA := {x | ∃ τ, HasType B.I x j τ} with hTdef
  set μ := B.I.muA B.μf with hμ
  set K : ENNReal := μ B.fund * ENNReal.ofReal (GlobalTheory.FlagMeas.kapBd B.I.E p q j) with hK
  set ρ : Measure (Fin a → ℝ) := (volume.restrict (GlobalTheory.FlagMeas.simplexH a)).withDensity
    (fun τ => ENNReal.ofReal (GlobalTheory.FlagMeas.dens B.I.n B.I.f j τ)) with hρ
  have hd : Measurable (fun τ => ENNReal.ofReal (GlobalTheory.FlagMeas.dens B.I.n B.I.f j τ)) :=
    (dens_meas B.I.n B.I.f j).ennreal_ofReal

  have h1 : ∫⁻ x in T ∩ B.fund, Φ x ∂μ ≤ ∫⁻ x in T ∩ B.fund, G (s x) ∂μ := by
    rw [← Measure.restrict_restrict hT]
    refine lintegral_mono_ae ?_
    refine (ae_restrict_iff' hT).2 (Filter.Eventually.of_forall ?_)
    rintro x ⟨τ, hx⟩
    rw [hsτ x τ hx]
    exact hΦ x τ hx

  have h2 : Measure.map s (μ.restrict (T ∩ B.fund)) ≤ K • ρ := by
    rw [Measure.le_iff]
    intro A hA
    rw [Measure.map_apply hs hA, Measure.restrict_apply (hs hA), Measure.smul_apply, smul_eq_mul,
      hρ, withDensity_apply _ hA, Measure.restrict_restrict hA]
    have hsub : s ⁻¹' A ∩ (T ∩ B.fund) ⊆
        GlobalTheory.FlagMeas.typeSet B.I j (A ∩ GlobalTheory.FlagMeas.simplexH a) ∩ B.fund := by
      rintro x ⟨hxA, ⟨τ, hx⟩, hxf⟩
      refine ⟨⟨τ, ⟨?_, mem_simplex hx⟩, hx⟩, hxf⟩
      have hxs : s x = τ := hsτ x τ hx
      rw [← hxs]
      exact hxA
    obtain ⟨-, h0, htop, hle⟩ := hFMB B.I B.μf B.fund B.fund_spec p q hSig hn a j ha hj hsum
      (A ∩ GlobalTheory.FlagMeas.simplexH a) (hA.inter (simplex_meas a)) Set.inter_subset_right
    calc μ (s ⁻¹' A ∩ (T ∩ B.fund))
        ≤ μ (GlobalTheory.FlagMeas.typeSet B.I j (A ∩ GlobalTheory.FlagMeas.simplexH a) ∩ B.fund) := measure_mono hsub
      _ ≤ ENNReal.ofReal (GlobalTheory.FlagMeas.kapBd B.I.E p q j) *
            (∫⁻ τ in A ∩ GlobalTheory.FlagMeas.simplexH a, ENNReal.ofReal (GlobalTheory.FlagMeas.dens B.I.n B.I.f j τ)) *
            μ B.fund := (ENNReal.div_le_iff h0.ne' htop.ne).1 hle
      _ = K * ∫⁻ τ in A ∩ GlobalTheory.FlagMeas.simplexH a, ENNReal.ofReal (GlobalTheory.FlagMeas.dens B.I.n B.I.f j τ) := by
          rw [hK]; ring
  calc ∫⁻ x in T ∩ B.fund, Φ x ∂μ ≤ ∫⁻ x in T ∩ B.fund, G (s x) ∂μ := h1
    _ = ∫⁻ τ, G τ ∂(Measure.map s (μ.restrict (T ∩ B.fund))) := (lintegral_map hG hs).symm
    _ ≤ ∫⁻ τ, G τ ∂(K • ρ) := lintegral_mono' h2 le_rfl
    _ = K * ∫⁻ τ in GlobalTheory.FlagMeas.simplexH a, G τ * ENNReal.ofReal (GlobalTheory.FlagMeas.dens B.I.n B.I.f j τ) := by
        rw [lintegral_smul_measure, hρ, lintegral_withDensity_eq_lintegral_mul _ hd hG, smul_eq_mul]
        congr 1
        exact lintegral_congr fun τ => mul_comm _ _

end GlobalTheory.FlagPush
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.NearTermsModeratePointsOneTypeBound

section

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.NearType

open GlobalTheory.FlagMeas

theorem layerProd_meas (n f : ℕ) {a : ℕ} (j : Fin a → ℕ) (de : ℝ) :
    Measurable fun τ : Fin a → ℝ => layerProd n f j τ (fun la => 1 + 12 * de / la) := by
  unfold layerProd
  fun_prop

theorem layerProd_nonneg (n f : ℕ) {a : ℕ} (j : Fin a → ℕ) (de : ℝ) (hde : 0 ≤ de) (τ : Fin a → ℝ)
    (hτ : ∀ i, 0 < τ i) : 0 ≤ layerProd n f j τ (fun la => 1 + 12 * de / la) := by
  have hG : ∀ la : ℝ, 0 < la → 0 ≤ 1 + 12 * de / la := fun la hla =>
    add_nonneg zero_le_one (div_nonneg (mul_nonneg (by norm_num) hde) hla.le)
  unfold layerProd
  apply mul_nonneg
  · refine Finset.prod_nonneg fun i _ => Finset.prod_nonneg fun k _ => ?_
    exact mul_nonneg (pow_nonneg (hG _ (div_pos (hτ i) (hτ k))) _)
      (pow_nonneg (hG _ (mul_pos (hτ i) (hτ k))) _)
  · refine Finset.prod_nonneg fun i _ => ?_
    exact mul_nonneg (pow_nonneg (hG _ (hτ i)) _) (pow_nonneg (hG _ (pow_pos (hτ i) 2)) _)

theorem integral_count_dens (n f q a : ℕ) (j : Fin a → ℕ) (de lo M : ℝ) (hj : ∑ i, j i ≤ q) (hq : 2 * q ≤ n)
    (hde : 0 ≤ de) (hd : de * q * n * f ≤ 1 / 100) (hlo : 0 < lo) (hlo2 : lo ≤ 1 / 2) (hM : 0 ≤ M) :
    ∫⁻ τ in simplexH a, {τ : Fin a → ℝ | ∀ i, lo ≤ τ i}.indicator
        (fun τ => ENNReal.ofReal (M * layerProd n f j τ (fun la => 1 + 12 * de / la))) τ *
        ENNReal.ofReal (FlagMeas.dens n f j τ) ≤
      ENNReal.ofReal (M * 2 * ∏ i, 2 * (f : ℝ) * j i * Real.log (1 / (2 * lo))) := by
  let S : Set (Fin a → ℝ) := Set.pi Set.univ (fun _ => Set.Icc lo (1 / 2))
  have hSm : MeasurableSet S := MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have hc : ∀ i, 0 ≤ 2 * (f : ℝ) * j i := fun i => by positivity

  have hpt : ∀ τ ∈ simplexH a,
      {τ : Fin a → ℝ | ∀ i, lo ≤ τ i}.indicator
          (fun τ => ENNReal.ofReal (M * layerProd n f j τ (fun la => 1 + 12 * de / la))) τ *
        ENNReal.ofReal (FlagMeas.dens n f j τ) ≤
      S.indicator (fun τ => ENNReal.ofReal (M * 2 * ∏ i, 2 * (f : ℝ) * j i / τ i)) τ := by
    intro τ hτ
    obtain ⟨hmono, h01⟩ := hτ
    by_cases hl : ∀ i, lo ≤ τ i
    · have hmem : τ ∈ S := fun i _ => ⟨hl i, (h01 i).2.le⟩
      rw [Set.indicator_of_mem (show τ ∈ {τ : Fin a → ℝ | ∀ i, lo ≤ τ i} from hl),
        Set.indicator_of_mem hmem,
        ← ENNReal.ofReal_mul (mul_nonneg hM (layerProd_nonneg n f j de hde τ fun i => (h01 i).1))]
      apply ENNReal.ofReal_le_ofReal
      have h2 : layerProd n f j τ (fun la => 1 + 12 * de / la) * layerProd n f j τ id ≤ 2 :=
        (GlobalTheory.Count.layerProd_count_mul_density_le_two n f q a j τ de hj hq hmono h01 hde hd).1
      have hP : 0 ≤ ∏ i, 2 * (f : ℝ) * j i / τ i :=
        Finset.prod_nonneg fun i _ => div_nonneg (hc i) (h01 i).1.le
      rw [FlagMeas.dens]
      calc M * layerProd n f j τ (fun la => 1 + 12 * de / la) *
            (layerProd n f j τ id * ∏ i, 2 * (f : ℝ) * j i / τ i)
          = M * (layerProd n f j τ (fun la => 1 + 12 * de / la) * layerProd n f j τ id) *
              ∏ i, 2 * (f : ℝ) * j i / τ i := by ring
        _ ≤ M * 2 * ∏ i, 2 * (f : ℝ) * j i / τ i :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hM) hP
    · simp [Set.indicator_apply, hl]
  have hcont : ContinuousOn (fun τ : Fin a → ℝ => M * 2 * ∏ i, 2 * (f : ℝ) * j i / τ i) S := by
    refine continuousOn_const.mul (continuousOn_finsetProd _ fun i _ => ?_)
    exact continuousOn_const.div (continuous_apply i).continuousOn
      fun τ hτ => ne_of_gt (lt_of_lt_of_le hlo (hτ i (Set.mem_univ _)).1)
  have hint : IntegrableOn (fun τ : Fin a → ℝ => M * 2 * ∏ i, 2 * (f : ℝ) * j i / τ i) S :=
    hcont.integrableOn_compact (isCompact_univ_pi fun _ => isCompact_Icc)
  have hnn : ∀ᵐ τ ∂(volume.restrict S), (0 : (Fin a → ℝ) → ℝ) τ ≤ M * 2 * ∏ i, 2 * (f : ℝ) * j i / τ i := by
    refine ae_restrict_of_forall_mem hSm fun τ hτ => ?_
    have hpos : ∀ i, 0 < τ i := fun i => lt_of_lt_of_le hlo (hτ i (Set.mem_univ _)).1
    exact mul_nonneg (mul_nonneg hM (by norm_num))
      (Finset.prod_nonneg fun i _ => div_nonneg (hc i) (hpos i).le)
  have key := (GlobalTheory.sizeIntegrals_and_card_compositions).1 a (fun i => 2 * (f : ℝ) * j i) lo hlo hlo2 hc
  calc _ ≤ ∫⁻ τ in simplexH a,
          S.indicator (fun τ => ENNReal.ofReal (M * 2 * ∏ i, 2 * (f : ℝ) * j i / τ i)) τ :=
        setLIntegral_mono' (GlobalTheory.FlagPush.simplex_meas a) hpt
    _ ≤ ∫⁻ τ, S.indicator (fun τ => ENNReal.ofReal (M * 2 * ∏ i, 2 * (f : ℝ) * j i / τ i)) τ :=
        setLIntegral_le_lintegral _ _
    _ = ∫⁻ τ in S, ENNReal.ofReal (M * 2 * ∏ i, 2 * (f : ℝ) * j i / τ i) := lintegral_indicator hSm _
    _ = ENNReal.ofReal (∫ τ in S, M * 2 * ∏ i, 2 * (f : ℝ) * j i / τ i) :=
        (ofReal_integral_eq_lintegral_ofReal hint hnn).symm
    _ = ENNReal.ofReal (M * 2 * ∏ i, 2 * (f : ℝ) * j i * Real.log (1 / (2 * lo))) := by
        rw [integral_const_mul]
        exact congrArg (fun r => ENNReal.ofReal (M * 2 * r)) key

theorem tsum_le_card {α : Type} (s t : Set α) (hst : s ⊆ t) (ht : t.Finite) (g : α → ℂ) (M : ℝ)
    (hM : 0 ≤ M) (hg : ∀ y, ‖g y‖ ≤ M) : ∑' y : s, ‖g y.1‖ₑ ≤ ENNReal.ofReal (M * (t.ncard : ℝ)) := by
  have hs : s.Finite := ht.subset hst
  haveI : Fintype s := hs.fintype
  calc ∑' y : s, ‖g y.1‖ₑ ≤ ∑' _ : s, ENNReal.ofReal M := by
        refine ENNReal.tsum_le_tsum fun y => ?_
        rw [← ofReal_norm_eq_enorm]
        exact ENNReal.ofReal_le_ofReal (hg y.1)
    _ = (Fintype.card s : ENNReal) * ENNReal.ofReal M := by
        rw [tsum_fintype, Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    _ ≤ (t.ncard : ENNReal) * ENNReal.ofReal M := by
        gcongr
        rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
        exact Set.ncard_le_ncard hst ht
    _ = ENNReal.ofReal (M * (t.ncard : ℝ)) := by
        rw [ENNReal.ofReal_mul hM, ENNReal.ofReal_natCast, mul_comm]

theorem near_terms_one_type : GlobalTheory.FlagMeas.FlagMeasureBound → GlobalTheory.Dec.NearUnip → GlobalTheory.Deep.PtBound → ∀ (B : RowsAut) (Cg : ℝ) (n₀ : ℕ) (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (b : ℝ), 8 ≤ n₀ → 1 ≤ q → CountHyp B Cg n₀ d p q b → (∀ x, 1 / 2 ≤ least B.I x → GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearAbs B d x = 0) ∧ ∀ (a : ℕ) (j : Fin a → ℕ), 1 ≤ a → (∀ i, 1 ≤ j i) → ∑ i, j i ≤ q → ∫⁻ x in {x | ∃ τ, HasType B.I x j τ} ∩ B.fund, {x | tauStar B q b ≤ least B.I x}.indicator (GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearAbs B d) x ∂(B.I.muA B.μf) ≤ ENNReal.ofReal (mainTerm B d * (2 * GlobalTheory.FlagMeas.kapBd B.I.E p q j * (2 * B.I.f * q * (11 * q * Real.log (bigX B b))) ^ a)) := by
  intro hF hN hP B Cg n₀ d p q b hn0 hq hC
  obtain ⟨-, -, hf1, -, -, h2q, -, hmin, hdpos, hX16, htpos, hsmall, h, -, hgap, -, -, -, h120, -⟩ :=
    GlobalTheory.Dec.countHyp_numerics B Cg n₀ d p q b hn0 hC
  obtain ⟨hDS, hSig, hn0n, hq2, -, -, -, -, -, -, -, hg0p, hg0, hsplit, -⟩ := hC
  have hn1 : 1 ≤ B.I.n := by omega
  have hnpos : (0 : ℝ) < B.I.n := by exact_mod_cast (show 0 < B.I.n by omega)
  have hfpos : (0 : ℝ) < B.I.f := by exact_mod_cast (show 0 < B.I.f by omega)
  have hrad : (Ideal.span {(B.g₀ : 𝓞 B.I.E)}).IsRadical :=
    GlobalTheory.SplitRadical.isRadical_span_of_ncard_primesOver B.I.E B.g₀ hg0p hsplit

  set δ : ℝ := 3 * Real.sqrt (B.I.n * epN B) with hδdef
  obtain ⟨hnear, hδ4, hδq⟩ := hN B d (1 / 10 ^ 6) (by norm_num) (by norm_num) hn1 hg0 hrad (epN B) δ rfl rfl
  have hep : 0 < epN B := by
    unfold epN
    exact div_pos (by norm_num) (mul_pos (pow_pos hnpos 8) (pow_pos hfpos 2))
  have hδpos : 0 < δ := mul_pos (by norm_num) (Real.sqrt_pos.2 (mul_pos hnpos hep))
  have h120' : 120 * (B.I.n : ℝ) * ((min p q : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h := by rw [hmin]; exact h120
  obtain ⟨-, hbd, -, -, he1, -, -⟩ := hP B d p q h hDS hSig hgap h120'
  refine ⟨fun x hx => ?_, fun a j ha hj hjq => ?_⟩
  ·
    refine GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearAbs_eq_zero B d x fun γ hγ => ?_
    have hmem := (hnear x γ hγ).2.2
    rw [GlobalTheory.NearLower.nearSet_eq B.I x δ hδpos hδ4 hx] at hmem
    exact hmem
  · set M : ℝ := (∏ v, d v) * (B.e 1).re with hMdef
    have hM : 0 ≤ M := mul_nonneg hdpos.le he1
    set lo : ℝ := tauStar B q b with hlodef
    have hlo2 : lo ≤ 1 / 2 := (hsmall hq).1.le
    have hmeasS : MeasurableSet {τ : Fin a → ℝ | ∀ i, lo ≤ τ i} := by
      rw [Set.setOf_forall]
      exact MeasurableSet.iInter fun i => measurableSet_le measurable_const (measurable_pi_apply i)
    have hGm : Measurable (fun τ : Fin a → ℝ => {τ : Fin a → ℝ | ∀ i, lo ≤ τ i}.indicator
        (fun τ => ENNReal.ofReal (M * layerProd B.I.n B.I.f j τ (fun la => 1 + 12 * δ / la))) τ) :=
      (ENNReal.measurable_ofReal.comp (measurable_const.mul (layerProd_meas B.I.n B.I.f j δ))).indicator
        hmeasS

    have hΦ : ∀ x τ, HasType B.I x j τ →
        {x | tauStar B q b ≤ least B.I x}.indicator (GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearAbs B d) x ≤
          {τ : Fin a → ℝ | ∀ i, lo ≤ τ i}.indicator
            (fun τ => ENNReal.ofReal (M * layerProd B.I.n B.I.f j τ (fun la => 1 + 12 * δ / la))) τ := by
      intro x τ hx
      by_cases hl : tauStar B q b ≤ least B.I x
      · obtain ⟨S, hS, -⟩ := id hx
        have h0 := ((GlobalTheory.PointFlag.flag_spec B.I x).2.2 a S τ hS).2 hn1
        have hapos : 0 < a := by omega
        have hlo : ∀ i, lo ≤ τ i := by
          intro i
          have hm : τ ⟨0, hapos⟩ ≤ τ i := hS.2.2.2.1.monotone (Fin.le_iff_val_le_val.2 (Nat.zero_le _))
          rw [h0.2 hapos] at hm
          exact le_trans hl hm
        rw [Set.indicator_of_mem (show x ∈ {x | tauStar B q b ≤ least B.I x} from hl),
          Set.indicator_of_mem (show τ ∈ {τ : Fin a → ℝ | ∀ i, lo ≤ τ i} from hlo)]
        obtain ⟨hfin, hcount⟩ := GlobalTheory.NearCount.near_count B.I x δ hδpos hδ4 a j τ hx
        have hsub : GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearNe B d x ⊆ nearSet B.I x δ := fun γ hγ => (hnear x γ hγ.1).2.2
        calc GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearAbs B d x
            ≤ ENNReal.ofReal (M * ((nearSet B.I x δ).ncard : ℝ)) :=
              tsum_le_card _ _ hsub hfin (fun y => phe B d (x⁻¹ * y * x)) M hM fun y => hbd _
          _ ≤ ENNReal.ofReal (M * layerProd B.I.n B.I.f j τ (fun la => 1 + 12 * δ / la)) :=
              ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hcount hM)
      · simp [Set.indicator_apply, hl]
    have hfund := hF B.I B.μf B.fund B.fund_spec p q hSig h2q a j ha hj hjq (simplexH a)
      (GlobalTheory.FlagPush.simplex_meas a) le_rfl
    have hfin : B.I.muA B.μf B.fund ≠ ⊤ := hfund.2.2.1.ne
    have hint := integral_count_dens B.I.n B.I.f q a j δ lo M hjq (by omega) hδpos.le (hδq q hq2)
      htpos hlo2 hM

    have hX : 0 < bigX B b := lt_of_lt_of_le (by norm_num) hX16
    have hloX : lo * bigX B b ^ (11 * q) = 1 := by
      rw [hlodef]; unfold tauStar; rw [inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hX.ne')]
    have hL0 : 0 ≤ Real.log (1 / (2 * lo)) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ (by positivity)]
      linarith
    have hL : Real.log (1 / (2 * lo)) ≤ 11 * q * Real.log (bigX B b) := by
      have h1 : 1 / (2 * lo) ≤ bigX B b ^ (11 * q) := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [hloX]
      calc Real.log (1 / (2 * lo)) ≤ Real.log (bigX B b ^ (11 * q)) :=
            Real.log_le_log (by positivity) h1
        _ = 11 * q * Real.log (bigX B b) := by rw [Real.log_pow]; push_cast; ring
    have hPQ : ∏ i, 2 * (B.I.f : ℝ) * j i * Real.log (1 / (2 * lo)) ≤
        (2 * B.I.f * q * (11 * q * Real.log (bigX B b))) ^ a := by
      calc ∏ i, 2 * (B.I.f : ℝ) * j i * Real.log (1 / (2 * lo))
          ≤ ∏ _i : Fin a, 2 * (B.I.f : ℝ) * q * (11 * q * Real.log (bigX B b)) := by
            refine Finset.prod_le_prod₀ (fun i _ => by positivity) fun i _ => ?_
            have hji : (j i : ℝ) ≤ q := by
              exact_mod_cast le_trans (Finset.single_le_sum (fun k _ => Nat.zero_le (j k))
                (Finset.mem_univ i)) hjq
            have : 0 ≤ 2 * (B.I.f : ℝ) := by positivity
            calc 2 * (B.I.f : ℝ) * j i * Real.log (1 / (2 * lo))
                ≤ 2 * (B.I.f : ℝ) * q * Real.log (1 / (2 * lo)) :=
                  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hji this) hL0
              _ ≤ 2 * (B.I.f : ℝ) * q * (11 * q * Real.log (bigX B b)) :=
                  mul_le_mul_of_nonneg_left hL (by positivity)
        _ = _ := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hmain : mainTerm B d = (B.I.muA B.μf B.fund).toReal * M := by
      rw [hMdef]; unfold mainTerm Formalism.MainNotions.S.AutInst.Dstar Formalism.MainNotions.S.AutInst.vol; ring
    calc ∫⁻ x in {x | ∃ τ, HasType B.I x j τ} ∩ B.fund,
          {x | tauStar B q b ≤ least B.I x}.indicator (GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearAbs B d) x ∂(B.I.muA B.μf)
        ≤ B.I.muA B.μf B.fund * ENNReal.ofReal (GlobalTheory.FlagMeas.kapBd B.I.E p q j) *
            ∫⁻ τ in simplexH a, {τ : Fin a → ℝ | ∀ i, lo ≤ τ i}.indicator
              (fun τ => ENNReal.ofReal (M * layerProd B.I.n B.I.f j τ (fun la => 1 + 12 * δ / la))) τ *
              ENNReal.ofReal (GlobalTheory.FlagMeas.dens B.I.n B.I.f j τ) :=
          GlobalTheory.FlagPush.lintegral_type_le hF B p q hSig h2q a j ha hj hjq _ _ hGm hΦ
      _ ≤ B.I.muA B.μf B.fund * ENNReal.ofReal (GlobalTheory.FlagMeas.kapBd B.I.E p q j) *
            ENNReal.ofReal (M * 2 * ∏ i, 2 * (B.I.f : ℝ) * j i * Real.log (1 / (2 * lo))) :=
          mul_le_mul' le_rfl hint
      _ ≤ _ := by
          by_cases hk : GlobalTheory.FlagMeas.kapBd B.I.E p q j ≤ 0
          · rw [ENNReal.ofReal_of_nonpos hk, mul_zero, zero_mul]
            positivity
          · push_neg at hk
            have hvol : 0 ≤ (B.I.muA B.μf B.fund).toReal := ENNReal.toReal_nonneg
            rw [← ENNReal.ofReal_toReal hfin, ← ENNReal.ofReal_mul hvol,
              ← ENNReal.ofReal_mul (mul_nonneg hvol hk.le)]
            apply ENNReal.ofReal_le_ofReal
            rw [hmain]
            have hc : 0 ≤ (B.I.muA B.μf B.fund).toReal * M * (2 * GlobalTheory.FlagMeas.kapBd B.I.E p q j) :=
              mul_nonneg (mul_nonneg hvol hM) (by linarith)
            calc (B.I.muA B.μf B.fund).toReal * GlobalTheory.FlagMeas.kapBd B.I.E p q j *
                  (M * 2 * ∏ i, 2 * (B.I.f : ℝ) * j i * Real.log (1 / (2 * lo)))
                = (B.I.muA B.μf B.fund).toReal * M * (2 * GlobalTheory.FlagMeas.kapBd B.I.E p q j) *
                    ∏ i, 2 * (B.I.f : ℝ) * j i * Real.log (1 / (2 * lo)) := by ring
              _ ≤ (B.I.muA B.μf B.fund).toReal * M * (2 * GlobalTheory.FlagMeas.kapBd B.I.E p q j) *
                    (2 * B.I.f * q * (11 * q * Real.log (bigX B b))) ^ a :=
                  mul_le_mul_of_nonneg_left hPQ hc
              _ = _ := by ring

end GlobalTheory.NearType
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.NearTermsModeratePointsOneTypeBoundStatement

section

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

theorem _root_.GlobalTheory.T.nearTerms_moderate_points_one_type_bound : GlobalTheory.FlagMeas.FlagMeasureBound → GlobalTheory.Dec.NearUnip → GlobalTheory.Deep.PtBound → ∀ (B : RowsAut) (Cg : ℝ) (n₀ : ℕ) (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (b : ℝ), 8 ≤ n₀ → 1 ≤ q → CountHyp B Cg n₀ d p q b → (∀ x, 1 / 2 ≤ least B.I x → GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearAbs B d x = 0) ∧ ∀ (a : ℕ) (j : Fin a → ℕ), 1 ≤ a → (∀ i, 1 ≤ j i) → ∑ i, j i ≤ q → ∫⁻ x in {x | ∃ τ, HasType B.I x j τ} ∩ B.fund, {x | tauStar B q b ≤ least B.I x}.indicator (GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearAbs B d) x ∂(B.I.muA B.μf) ≤ ENNReal.ofReal (mainTerm B d * (2 * GlobalTheory.FlagMeas.kapBd B.I.E p q j * (2 * B.I.f * q * (11 * q * Real.log (bigX B b))) ^ a)) := by
  first | exact @GlobalTheory.NearType.near_terms_one_type | exact GlobalTheory.NearType.near_terms_one_type | (intros; apply GlobalTheory.NearType.near_terms_one_type <;> assumption)
end
end
