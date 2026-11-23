module

public import Formalism.PeriodIntegrals.ScMuExists
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.InstAll
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.InstDecomp
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.ContinuousUMatApply
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.TypeStar
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.HaarSub
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.InstLeftInvMuInf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.ModOne
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.ContinuousHPart
public import Formalism.RealPlaceAnalysis.FinalF
import Mathlib.Topology.Algebra.Group.Units

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.GenSemiOf

section

@[expose] public section

open MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

namespace PI.ScMuExists.UnitaryGroupMassFormula

theorem genSemi_of (hHaar : GenHaarSub) : GenSemi := by
  unfold GenSemi
  intro G _ _ _ _ _ _ _ _ N H hN hH hconj hinvN hprop
  obtain ⟨hσN, -, hcN, htN, hfinN, hposN⟩ := hHaar G N hN
  obtain ⟨hσH, -, hcH, htH, hfinH, hposH⟩ := hHaar G H hH
  set μN := haarSub N hN with hμN
  set μH := haarSub H hH with hμH
  haveI : SigmaFinite μN := hσN
  haveI : SigmaFinite μH := hσH
  have hmul : Measurable (fun p : G × G => p.1 * p.2) := measurable_fst.mul measurable_snd

  have hNH : (N : Set G) * (H : Set G) =
      (fun p : G × G => p.1 * p.2) '' ((N : Set G) ×ˢ (H : Set G)) := by
    ext x
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨(a, b), ⟨ha, hb⟩, rfl⟩
    · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
      exact ⟨a, ha, b, hb, rfl⟩
  have hmeasNH : MeasurableSet ((N : Set G) * (H : Set G)) := by
    rw [hNH]
    obtain ⟨K, hK, hKU⟩ := (isSigmaCompact_univ.of_isClosed_subset (hN.prod hH)
      (Set.subset_univ _)).image continuous_mul
    rw [← hKU]
    exact MeasurableSet.iUnion fun n => (hK n).measurableSet

  have hprodc : (μN.prod μH) ((N : Set G) ×ˢ (H : Set G))ᶜ = 0 := by
    rw [Set.compl_prod_eq_union]
    refine measure_union_null ?_ ?_
    · rw [Measure.prod_prod, hcN, zero_mul]
    · rw [Measure.prod_prod, hcH, mul_zero]
  refine ⟨?_, hmeasNH, ?_, ?_, ?_, ?_⟩
  · show SFinite ((μN.prod μH).map (fun p : G × G => p.1 * p.2))
    infer_instance
  · show ((μN.prod μH).map (fun p : G × G => p.1 * p.2)) ((N : Set G) * (H : Set G))ᶜ = 0
    rw [Measure.map_apply hmul hmeasNH.compl]
    refine measure_mono_null ?_ hprodc
    intro p hp hpNH
    exact hp ⟨p.1, hpNH.1, p.2, hpNH.2, rfl⟩
  · rintro t ⟨n0, hn0, h0, hh0, rfl⟩
    show ((μN.prod μH).map (fun p : G × G => p.1 * p.2)).map (fun x => n0 * h0 * x) =
      (μN.prod μH).map (fun p : G × G => p.1 * p.2)
    have hc : Measurable (fun x : G => h0 * x * h0⁻¹) := (measurable_const_mul h0).mul_const _
    have hf : Measurable (fun x : G => n0 * (h0 * x * h0⁻¹)) := (measurable_const_mul n0).comp hc
    have hg : Measurable (fun y : G => h0 * y) := measurable_const_mul h0
    have hfN : μN.map (fun x : G => n0 * (h0 * x * h0⁻¹)) = μN := by
      show μN.map ((fun x : G => n0 * x) ∘ (fun x : G => h0 * x * h0⁻¹)) = μN
      rw [← Measure.map_map (measurable_const_mul n0) hc, hinvN h0 hh0, htN n0 hn0]
    have hgH : μH.map (fun y : G => h0 * y) = μH := htH h0 hh0
    have hPM : Measurable (Prod.map (fun x : G => n0 * (h0 * x * h0⁻¹)) (fun y : G => h0 * y)) :=
      hf.prodMap hg
    have hcomp : (fun x : G => n0 * h0 * x) ∘ (fun p : G × G => p.1 * p.2) =
        (fun p : G × G => p.1 * p.2) ∘
          Prod.map (fun x : G => n0 * (h0 * x * h0⁻¹)) (fun y : G => h0 * y) := by
      funext p
      simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd]
      group
    rw [Measure.map_map (measurable_const_mul _) hmul, hcomp, ← Measure.map_map hmul hPM,
      ← Measure.map_prod_map μN μH hf hg, hfN, hgH]
  · intro U hU h1U
    show 0 < ((μN.prod μH).map (fun p : G × G => p.1 * p.2)) U
    rw [Measure.map_apply hmul hU.measurableSet]
    have hUo : IsOpen ((fun p : G × G => p.1 * p.2) ⁻¹' U) := hU.preimage continuous_mul
    have h11 : ((1 : G), (1 : G)) ∈ (fun p : G × G => p.1 * p.2) ⁻¹' U := by
      show (1 : G) * 1 ∈ U
      rwa [one_mul]
    obtain ⟨u, v, hu, hv, h1u, h1v, huv⟩ := isOpen_prod_iff.mp hUo 1 1 h11
    calc (0 : ℝ≥0∞) < μN u * μH v := ENNReal.mul_pos (hposN u hu h1u).ne' (hposH v hv h1v).ne'
      _ = (μN.prod μH) (u ×ˢ v) := (Measure.prod_prod u v).symm
      _ ≤ _ := measure_mono huv
  · intro C hC
    show ((μN.prod μH).map (fun p : G × G => p.1 * p.2)) C < ⊤
    rw [Measure.map_apply hmul hC.measurableSet]
    have hK := hprop C hC
    set P := {p : G × G | p.1 ∈ N ∧ p.2 ∈ H ∧ p.1 * p.2 ∈ C} with hP
    have hsub : (fun p : G × G => p.1 * p.2) ⁻¹' C ⊆ P ∪ ((N : Set G) ×ˢ (H : Set G))ᶜ := by
      intro p hp
      by_cases h : p ∈ (N : Set G) ×ˢ (H : Set G)
      · exact Or.inl ⟨h.1, h.2, hp⟩
      · exact Or.inr h
    have hPbox : P ⊆ (Prod.fst '' P) ×ˢ (Prod.snd '' P) := fun p hp => ⟨⟨p, hp, rfl⟩, ⟨p, hp, rfl⟩⟩
    have hPfin : (μN.prod μH) P < ⊤ := by
      refine lt_of_le_of_lt (measure_mono hPbox) ?_
      rw [Measure.prod_prod]
      exact ENNReal.mul_lt_top (hfinN _ (hK.image continuous_fst)) (hfinH _ (hK.image continuous_snd))
    calc (μN.prod μH) ((fun p : G × G => p.1 * p.2) ⁻¹' C)
        ≤ (μN.prod μH) (P ∪ ((N : Set G) ×ˢ (H : Set G))ᶜ) := measure_mono hsub
      _ ≤ (μN.prod μH) P + (μN.prod μH) ((N : Set G) ×ˢ (H : Set G))ᶜ := measure_union_le _ _
      _ < ⊤ := by rw [hprodc, add_zero]; exact hPfin

end PI.ScMuExists.UnitaryGroupMassFormula
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.GenericWeilRepresentation

section

@[expose] public section

open MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

namespace PI.ScMuExists.UnitaryGroupMassFormula

section Bruhat

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem exists_bruhat_left (μS : Measure G) [SFinite μS] (S : Set G) (hSc : μS Sᶜ = 0)
    (hinv : ∀ t ∈ S, μS.map (fun x => t * x) = μS)
    (hpos : ∀ U : Set G, IsOpen U → (1 : G) ∈ U → 0 < μS U)
    (hfin : ∀ K : Set G, IsCompact K → μS K < ⊤) :
    ∃ β : G → ℝ≥0∞, Measurable β ∧ ∀ y : G, ∫⁻ s, β (s⁻¹ * y) ∂μS = 1 := by

  obtain ⟨O, hOo, hOc, hcov⟩ : ∃ O : ℕ → Set G, (∀ n, IsOpen (O n)) ∧
      (∀ n, ∃ L : Set G, IsCompact L ∧ O n ⊆ L) ∧ ∀ y : G, ∃ n, y ∈ O n := by
    let K := CompactExhaustion.choice G
    exact ⟨fun n => interior (K (n + 1)), fun n => isOpen_interior,
      fun n => ⟨K (n + 1), K.isCompact _, interior_subset⟩,
      fun y => ⟨K.find y, K.subset_interior_succ _ (K.mem_find y)⟩⟩

  obtain ⟨f, hf⟩ : ∃ f : ℕ → G → ℝ≥0∞,
      ∀ n y, f n y = ∫⁻ s, (O n).indicator (1 : G → ℝ≥0∞) (s⁻¹ * y) ∂μS := ⟨_, fun _ _ => rfl⟩
  have hm : ∀ n y, Measurable (fun s : G => (O n).indicator (1 : G → ℝ≥0∞) (s⁻¹ * y)) :=
    fun n y => (measurable_one.indicator (hOo n).measurableSet).comp (measurable_inv.mul_const y)
  have hfm : ∀ n, Measurable (f n) := by
    intro n
    have h2 : Measurable (fun q : G × G => (O n).indicator (1 : G → ℝ≥0∞) (q.2⁻¹ * q.1)) :=
      (measurable_one.indicator (hOo n).measurableSet).comp (measurable_snd.inv.mul measurable_fst)
    rw [show f n = fun y => ∫⁻ s, (O n).indicator (1 : G → ℝ≥0∞) (s⁻¹ * y) ∂μS from funext (hf n)]
    exact h2.lintegral_prod_right'
  have hf_eq : ∀ n y, f n y = μS ((fun s : G => s⁻¹ * y) ⁻¹' O n) := by
    intro n y
    rw [hf n y, ← lintegral_indicator_one ((hOo n).measurableSet.preimage (measurable_inv.mul_const y))]
    rfl
  have hf_fin : ∀ n y, f n y < ⊤ := by
    intro n y
    obtain ⟨L, hL, hOL⟩ := hOc n
    have hc : IsCompact ((fun k : G => y * k⁻¹) '' L) := hL.image (by fun_prop)
    rw [hf_eq]
    refine lt_of_le_of_lt (measure_mono ?_) (hfin _ hc)
    intro s hs
    exact ⟨s⁻¹ * y, hOL hs, by group⟩
  have hf_pos : ∀ n y, y ∈ O n → 0 < f n y := by
    intro n y hy
    rw [hf_eq]
    refine hpos _ (IsOpen.preimage (f := fun s : G => s⁻¹ * y) (by fun_prop) (hOo n)) ?_
    show (1 : G)⁻¹ * y ∈ O n
    rwa [inv_one, one_mul]
  have hf_inv : ∀ n, ∀ t ∈ S, ∀ y, f n (t⁻¹ * y) = f n y := by
    intro n t ht y
    calc f n (t⁻¹ * y) = ∫⁻ r, (O n).indicator (1 : G → ℝ≥0∞) ((t * r)⁻¹ * y) ∂μS := by
          rw [hf n]
          refine lintegral_congr fun r => ?_
          rw [mul_inv_rev, mul_assoc]
      _ = ∫⁻ r, (O n).indicator (1 : G → ℝ≥0∞) (r⁻¹ * y) ∂(μS.map (fun x => t * x)) :=
          (lintegral_map (hm n y) (measurable_const_mul t)).symm
      _ = f n y := by rw [hinv t ht, hf n y]

  have hZm : Measurable (fun x : G => ∑' n, (2 : ℝ≥0∞)⁻¹ ^ n * (f n x)⁻¹ * f n x) :=
    Measurable.tsum fun n => (measurable_const.mul (hfm n).inv).mul (hfm n)
  have hTm : Measurable (fun x : G =>
      ∑' n, (2 : ℝ≥0∞)⁻¹ ^ n * (f n x)⁻¹ * (O n).indicator (1 : G → ℝ≥0∞) x) :=
    Measurable.tsum fun n =>
      (measurable_const.mul (hfm n).inv).mul (measurable_one.indicator (hOo n).measurableSet)
  refine ⟨fun x => (∑' n, (2 : ℝ≥0∞)⁻¹ ^ n * (f n x)⁻¹ * (O n).indicator (1 : G → ℝ≥0∞) x) *
      (∑' n, (2 : ℝ≥0∞)⁻¹ ^ n * (f n x)⁻¹ * f n x)⁻¹, hTm.mul hZm.inv, fun y => ?_⟩
  have hterm : ∀ n, (2 : ℝ≥0∞)⁻¹ ^ n * (f n y)⁻¹ * f n y ≤ (2 : ℝ≥0∞)⁻¹ ^ n := by
    intro n
    rcases eq_or_ne (f n y) 0 with h | h
    · rw [h, mul_zero]
      exact zero_le
    · rw [mul_assoc, ENNReal.inv_mul_cancel h (hf_fin n y).ne, mul_one]
  have hZtop : (∑' n, (2 : ℝ≥0∞)⁻¹ ^ n * (f n y)⁻¹ * f n y) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hterm)
    rw [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
    exact ENNReal.ofNat_ne_top
  have hZ0 : (∑' n, (2 : ℝ≥0∞)⁻¹ ^ n * (f n y)⁻¹ * f n y) ≠ 0 := by
    obtain ⟨n, hn⟩ := hcov y
    have hpos' := hf_pos n y hn
    have h1 : (2 : ℝ≥0∞)⁻¹ ^ n * (f n y)⁻¹ * f n y = (2 : ℝ≥0∞)⁻¹ ^ n := by
      rw [mul_assoc, ENNReal.inv_mul_cancel hpos'.ne' (hf_fin n y).ne, mul_one]
    refine ne_of_gt (lt_of_lt_of_le ?_ (ENNReal.le_tsum n))
    rw [h1]
    exact ENNReal.pow_pos (ENNReal.inv_pos.mpr ENNReal.ofNat_ne_top) n
  have hae : ∀ᵐ s ∂μS, s ∈ S := by
    rw [ae_iff]
    exact hSc
  calc ∫⁻ s, (∑' n, (2 : ℝ≥0∞)⁻¹ ^ n * (f n (s⁻¹ * y))⁻¹ *
          (O n).indicator (1 : G → ℝ≥0∞) (s⁻¹ * y)) *
          (∑' n, (2 : ℝ≥0∞)⁻¹ ^ n * (f n (s⁻¹ * y))⁻¹ * f n (s⁻¹ * y))⁻¹ ∂μS
        = ∫⁻ s, (∑' n, (2 : ℝ≥0∞)⁻¹ ^ n * (f n y)⁻¹ *
          (O n).indicator (1 : G → ℝ≥0∞) (s⁻¹ * y)) *
          (∑' n, (2 : ℝ≥0∞)⁻¹ ^ n * (f n y)⁻¹ * f n y)⁻¹ ∂μS := by
        refine lintegral_congr_ae ?_
        filter_upwards [hae] with s hs
        have hs' : ∀ n, f n (s⁻¹ * y) = f n y := fun n => hf_inv n s hs y
        simp only [hs']
    _ = (∫⁻ s, ∑' n, (2 : ℝ≥0∞)⁻¹ ^ n * (f n y)⁻¹ *
          (O n).indicator (1 : G → ℝ≥0∞) (s⁻¹ * y) ∂μS) *
          (∑' n, (2 : ℝ≥0∞)⁻¹ ^ n * (f n y)⁻¹ * f n y)⁻¹ :=
        lintegral_mul_const' _ _ (ENNReal.inv_ne_top.mpr hZ0)
    _ = (∑' n, (2 : ℝ≥0∞)⁻¹ ^ n * (f n y)⁻¹ * f n y) *
          (∑' n, (2 : ℝ≥0∞)⁻¹ ^ n * (f n y)⁻¹ * f n y)⁻¹ := by
        rw [lintegral_tsum fun n => ((hm n y).const_mul _).aemeasurable]
        congr 1
        refine tsum_congr fun n => ?_
        rw [lintegral_const_mul _ (hm n y), ← hf n y]
    _ = 1 := ENNReal.mul_inv_cancel hZ0 hZtop

theorem weil_of_bruhat (μG μS : Measure G) [SFinite μG] [μG.IsMulLeftInvariant] [SFinite μS]
    (S : Set G) (_hS : MeasurableSet S) (hSc : μS Sᶜ = 0)
    (hinv : ∀ t ∈ S, μS.map (fun x => t * x) = μS)
    (hpos : ∀ U : Set G, IsOpen U → (1 : G) ∈ U → 0 < μS U)
    (hfin : ∀ K : Set G, IsCompact K → μS K < ⊤) :
    ∃ ν : Measure G, ∀ f : G → ℝ≥0∞, Measurable f →
      ∫⁻ x, f x ∂μG = ∫⁻ x, (∫⁻ s, f (s * x) ∂μS) ∂ν := by
  obtain ⟨β, hβm, hβ⟩ := exists_bruhat_left μS S hSc hinv hpos hfin
  refine ⟨μG.withDensity β, fun f hf => ?_⟩
  have hF : Measurable (fun x : G => ∫⁻ s, f (s * x) ∂μS) :=
    (hf.comp (measurable_snd.mul measurable_fst)).lintegral_prod_right'
  rw [lintegral_withDensity_eq_lintegral_mul _ hβm hF]
  calc ∫⁻ x, f x ∂μG = ∫⁻ x, (∫⁻ s, β (s⁻¹ * x) ∂μS) * f x ∂μG := by
        simp only [hβ, one_mul]
    _ = ∫⁻ x, ∫⁻ s, β (s⁻¹ * x) * f x ∂μS ∂μG := by
        refine lintegral_congr fun x => ?_
        exact (lintegral_mul_const _ (hβm.comp (measurable_inv.mul_const x))).symm
    _ = ∫⁻ s, ∫⁻ x, β (s⁻¹ * x) * f x ∂μG ∂μS :=
        lintegral_lintegral_swap ((hβm.comp (measurable_snd.inv.mul measurable_fst)).mul
          (hf.comp measurable_fst)).aemeasurable
    _ = ∫⁻ s, ∫⁻ x, β x * f (s * x) ∂μG ∂μS := by
        refine lintegral_congr fun s => ?_
        simpa only [inv_mul_cancel_left] using
          (lintegral_mul_left_eq_self (fun x => β (s⁻¹ * x) * f x) s).symm
    _ = ∫⁻ x, ∫⁻ s, β x * f (s * x) ∂μS ∂μG :=
        lintegral_lintegral_swap ((hβm.comp measurable_snd).mul
          (hf.comp (measurable_fst.mul measurable_snd))).aemeasurable
    _ = ∫⁻ x, (β * fun x => ∫⁻ s, f (s * x) ∂μS) x ∂μG := by
        refine lintegral_congr fun x => ?_
        exact lintegral_const_mul _ (hf.comp (measurable_id.mul_const x))

end Bruhat

theorem generic_weil_representation : GenWeil := by
  unfold GenWeil
  intro G _ _ _ _ _ _ _ _ μG μS _ _ _ S hS hSc hinv hpos hfin
  exact weil_of_bruhat μG μS S hS hSc hinv hpos hfin

end PI.ScMuExists.UnitaryGroupMassFormula
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.Proper

section

@[expose] public section

noncomputable section

open Matrix
open scoped Pointwise

namespace PI.ScMuExists.UnitaryGroupMassFormula

theorem isClosedEmbedding_uMat {n : ℕ} (ε : Fin n → Bool) :
    Topology.IsClosedEmbedding (fun g : Formalism.REAL.UJ ε => Formalism.MainNotions.S.uMat g) :=
  (Formalism.REAL.uJEmb n ε).1

theorem proper_action_instance : InstProper := by
  intro I r e f z hF N H hNs hHs C hC
  let K : ∀ v, Set (Matrix (Fin I.n) (Fin I.n) ℂ) := fun v =>
    hPart (I.ε v) (fun a => rv I v (e a)) (fun a => rv I v (f a)) (rv I v z) ''
      ((fun s : I.Ginf => Formalism.MainNotions.S.uMat (s v)) '' C)
  have hK : ∀ v, IsCompact (K v) := fun v =>
    (hC.image (continuous_uMat_apply I v)).image (continuous_hPart _ _ _ _)
  let K2 : Set I.Ginf := Set.univ.pi fun v => (fun g : Formalism.REAL.UJ (I.ε v) => Formalism.MainNotions.S.uMat g) ⁻¹' K v
  have hK2 : IsCompact K2 :=
    isCompact_univ_pi fun v => (isClosedEmbedding_uMat (I.ε v)).isCompact_preimage (hK v)
  have hsub : {p : I.Ginf × I.Ginf | p.1 ∈ N ∧ p.2 ∈ H ∧ p.1 * p.2 ∈ C} ⊆ (C * K2⁻¹) ×ˢ K2 := by
    rintro ⟨x, h⟩ ⟨hx, hh, hxh⟩
    have hx' : x ∈ Ninf I e z := by rw [← hNs]; exact hx
    have hh' : h ∈ Hset I (frameSet I e f z) := by rw [← hHs]; exact hh
    have hK2h : h ∈ K2 := by
      intro v _
      refine ⟨Formalism.MainNotions.S.uMat ((x * h) v), ⟨x * h, hxh, rfl⟩, ?_⟩
      show hPart _ _ _ _ (Formalism.MainNotions.S.uMat (x v * h v)) = Formalism.MainNotions.S.uMat (h v)
      rw [uMat_mul]
      exact hPart_mul (rFrame_of hF v) (hx' v) (uMat_inUJ (h v))
        (fun a => hh' v _ (Or.inl (Or.inl ⟨a, rfl⟩))) (fun a => hh' v _ (Or.inl (Or.inr ⟨a, rfl⟩)))
        (hh' v _ (Or.inr rfl))
    refine ⟨?_, hK2h⟩
    rw [← mul_inv_cancel_right x h]
    exact Set.mul_mem_mul hxh (Set.inv_mem_inv.mpr hK2h)
  have hcl : IsClosed {p : I.Ginf × I.Ginf | p.1 ∈ N ∧ p.2 ∈ H ∧ p.1 * p.2 ∈ C} := by
    have hNc : IsClosed (N : Set I.Ginf) := by rw [hNs]; exact isClosed_Ninf I e z
    have hHc : IsClosed (H : Set I.Ginf) := by rw [hHs]; exact isClosed_Hset I _
    exact (hNc.preimage continuous_fst).inter ((hHc.preimage continuous_snd).inter
      (hC.isClosed.preimage continuous_mul))
  exact ((hC.mul hK2.inv).prod hK2).of_isClosed_subset hcl hsub

end PI.ScMuExists.UnitaryGroupMassFormula
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.TargetOfInstDecomp

section

@[expose] public section

namespace PI.ScMuExists.UnitaryGroupMassFormula

theorem target_of_instDecomp (hd : InstDecomp) : PI.ScMuExists.Target :=
  target_of_steps generic_haar_subgroup (genSemi_of generic_haar_subgroup) generic_weil_representation measure_subFacts
    (genModOne_of generic_haar_subgroup) hd proper_action_instance

end PI.ScMuExists.UnitaryGroupMassFormula
end
end

-- Source module: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ScMuExists

section

@[expose] public section

namespace PI

theorem sc_mu_exists : PI.ScMuExists.Target :=
  PI.ScMuExists.UnitaryGroupMassFormula.target_of_instDecomp PI.ScMuExists.UnitaryGroupMassFormula.place_decomposition_instance

end PI
end
end
