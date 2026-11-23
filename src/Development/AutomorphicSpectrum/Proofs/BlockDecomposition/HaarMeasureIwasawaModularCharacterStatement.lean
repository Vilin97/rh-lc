module

public import Mathlib.MeasureTheory.Group.ModularCharacter
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegralConjInnerMulInnerOfIsEmptyEquiv
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Sheaves.Init
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarMeasureClosedCompactDecomp

section

@[expose] public section

open MeasureTheory MeasureTheory.Measure Topology Pointwise
open scoped ENNReal NNReal

namespace GlobalTheory.HaarQK

theorem lintegral_mul_right_modular {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] [T2Space H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (ν : Measure H) [ν.IsHaarMeasure] {f : H → ℝ≥0∞} (hf : Measurable f) (h : H) :
    ∫⁻ x, f (x * h) ∂ν = (modularCharacterFun h : ℝ≥0∞) * ∫⁻ x, f x ∂ν := by
  rw [← lintegral_map hf (measurable_mul_const h), map_right_mul_eq_modularCharacterFun_smul,
    lintegral_smul_measure]
  rfl

theorem secondCountable_subgroup {G : Type} [Group G] [TopologicalSpace G]
    [SecondCountableTopology G] (Q : Subgroup G) : SecondCountableTopology Q :=
  TopologicalSpace.Subtype.secondCountableTopology (Q : Set G)

attribute [local instance] secondCountable_subgroup

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  {Q K : Subgroup G} [LocallyCompactSpace Q] [CompactSpace K]
  (ν : Measure Q) (κ : Measure K) [ν.IsHaarMeasure] [κ.IsHaarMeasure]

theorem iter_right (u : G → ℝ≥0∞) (hu : Measurable u) (q₀ : Q) (k₀ : K) :
    ∫⁻ k, ∫⁻ q, u (q.1 * (q₀.1 * k₀.1) * k.1) ∂ν ∂κ =
      (modularCharacterFun q₀ : ℝ≥0∞) * ∫⁻ k, ∫⁻ q, u (q.1 * k.1) ∂ν ∂κ := by
  have e1 : ∀ k : K, ∫⁻ q, u (q.1 * (q₀.1 * k₀.1) * k.1) ∂ν =
      (modularCharacterFun q₀ : ℝ≥0∞) * ∫⁻ q, u (q.1 * (k₀ * k).1) ∂ν := by
    intro k
    have hf : Measurable fun q : Q => u (q.1 * (k₀ * k).1) :=
      hu.comp ((continuous_subtype_val.mul continuous_const).measurable)
    rw [← lintegral_mul_right_modular ν hf q₀]
    congr 1
    ext q
    congr 1
    simp only [Subgroup.coe_mul]
    group
  simp_rw [e1]
  rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  congr 1
  exact lintegral_mul_left_eq_self (fun k : K => ∫⁻ q, u (q.1 * k.1) ∂ν) k₀

theorem iter_left (v : G → ℝ≥0∞) (q₀ : Q) (k₀ : K) :
    ∫⁻ k, ∫⁻ q, v ((q.1)⁻¹ * (q₀.1 * k₀.1) * (k.1)⁻¹) ∂ν ∂κ =
      ∫⁻ k, ∫⁻ q, v ((q.1)⁻¹ * k.1) ∂ν ∂κ := by
  haveI := GlobalTheory.isInvInvariant_of_compactSpace κ
  have e1 : ∀ k : K, ∫⁻ q, v ((q.1)⁻¹ * (q₀.1 * k₀.1) * (k.1)⁻¹) ∂ν =
      ∫⁻ q, v ((q.1)⁻¹ * (k₀ * k⁻¹).1) ∂ν := by
    intro k
    have := lintegral_mul_left_eq_self
      (μ := ν) (fun q : Q => v ((q.1)⁻¹ * (q₀.1 * k₀.1) * (k.1)⁻¹)) q₀
    rw [← this]
    congr 1
    ext q
    congr 1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  simp_rw [e1]
  have e2 := lintegral_inv_eq_self (μ := κ) (fun k : K => ∫⁻ q, v ((q.1)⁻¹ * (k₀ * k).1) ∂ν)
  rw [e2]
  exact lintegral_mul_left_eq_self (fun k : K => ∫⁻ q, v ((q.1)⁻¹ * k.1) ∂ν) k₀

end GlobalTheory.HaarQK

namespace GlobalTheory.HaarQK
attribute [local instance] secondCountable_subgroup

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  {Q K : Subgroup G} [LocallyCompactSpace Q] [CompactSpace K]
  (ν : Measure Q) (κ : Measure K) [ν.IsHaarMeasure] [κ.IsHaarMeasure]

theorem weil_exchange (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (u v : G → ℝ≥0∞) (hu : Measurable u) (hv : Measurable v) :
    ∫⁻ g, u g * ∫⁻ k, ∫⁻ q, v ((q.1)⁻¹ * g * (k.1)⁻¹) ∂ν ∂κ ∂μ =
      ∫⁻ g, v g * ∫⁻ k, ∫⁻ q, u (q.1 * g * k.1) ∂ν ∂κ ∂μ := by
  have cF : Continuous fun x : G × (Q × K) => (x.2.1.1)⁻¹ * x.1 * (x.2.2.1)⁻¹ := by fun_prop
  have cH : Continuous fun x : G × (Q × K) => x.2.1.1 * x.1 * x.2.2.1 := by fun_prop
  have mF : Measurable fun x : G × (Q × K) => u x.1 * v ((x.2.1.1)⁻¹ * x.1 * (x.2.2.1)⁻¹) :=
    (hu.comp measurable_fst).mul (hv.comp cF.measurable)
  have mH : Measurable fun x : G × (Q × K) => u (x.2.1.1 * x.1 * x.2.2.1) * v x.1 :=
    (hu.comp cH.measurable).mul (hv.comp measurable_fst)
  have mv : ∀ g : G, Measurable fun p : Q × K => v ((p.1.1)⁻¹ * g * (p.2.1)⁻¹) := fun g =>
    hv.comp (Continuous.measurable (by fun_prop))
  have mu : ∀ g : G, Measurable fun p : Q × K => u (p.1.1 * g * p.2.1) := fun g =>
    hu.comp (Continuous.measurable (by fun_prop))
  have p1 : ∀ g : G, ∫⁻ k, ∫⁻ q, v ((q.1)⁻¹ * g * (k.1)⁻¹) ∂ν ∂κ =
      ∫⁻ p : Q × K, v ((p.1.1)⁻¹ * g * (p.2.1)⁻¹) ∂(ν.prod κ) := fun g =>
    (lintegral_prod_symm (μ := ν) (ν := κ) (fun p : Q × K => v ((p.1.1)⁻¹ * g * (p.2.1)⁻¹))
      (mv g).aemeasurable).symm
  have p2 : ∀ g : G, ∫⁻ k, ∫⁻ q, u (q.1 * g * k.1) ∂ν ∂κ =
      ∫⁻ p : Q × K, u (p.1.1 * g * p.2.1) ∂(ν.prod κ) := fun g =>
    (lintegral_prod_symm (μ := ν) (ν := κ) (fun p : Q × K => u (p.1.1 * g * p.2.1))
      (mu g).aemeasurable).symm
  simp_rw [p1, p2]
  calc ∫⁻ g, u g * ∫⁻ p : Q × K, v ((p.1.1)⁻¹ * g * (p.2.1)⁻¹) ∂(ν.prod κ) ∂μ
      = ∫⁻ g, ∫⁻ p : Q × K, u g * v ((p.1.1)⁻¹ * g * (p.2.1)⁻¹) ∂(ν.prod κ) ∂μ := by
        congr 1; ext g
        exact (lintegral_const_mul _ (mv g)).symm
    _ = ∫⁻ p : Q × K, ∫⁻ g, u g * v ((p.1.1)⁻¹ * g * (p.2.1)⁻¹) ∂μ ∂(ν.prod κ) :=
        lintegral_lintegral_swap mF.aemeasurable
    _ = ∫⁻ p : Q × K, ∫⁻ g, u (p.1.1 * g * p.2.1) * v g ∂μ ∂(ν.prod κ) := by
        congr 1; ext p
        set F : G → ℝ≥0∞ := fun g => u (p.1.1 * g * p.2.1) * v g with hF
        have h1 : ∫⁻ g, F ((p.1.1)⁻¹ * g * (p.2.1)⁻¹) ∂μ = ∫⁻ g, F (g * (p.2.1)⁻¹) ∂μ :=
          lintegral_mul_left_eq_self (fun g => F (g * (p.2.1)⁻¹)) _
        have h2 : ∫⁻ g, F (g * (p.2.1)⁻¹) ∂μ = ∫⁻ g, F g ∂μ := lintegral_mul_right_eq_self F _
        rw [← h2, ← h1]
        congr 1; ext g
        simp only [hF]
        congr 1
        congr 1; group
    _ = ∫⁻ g, ∫⁻ p : Q × K, u (p.1.1 * g * p.2.1) * v g ∂(ν.prod κ) ∂μ :=
        lintegral_lintegral_swap (mH.comp measurable_swap).aemeasurable
    _ = ∫⁻ g, v g * ∫⁻ p : Q × K, u (p.1.1 * g * p.2.1) ∂(ν.prod κ) ∂μ := by
        congr 1; ext g
        rw [lintegral_mul_const _ (mu g), mul_comm]

end GlobalTheory.HaarQK

namespace GlobalTheory.HaarQK
attribute [local instance] secondCountable_subgroup

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  {Q K : Subgroup G} [LocallyCompactSpace Q] [CompactSpace K]
  (ν : Measure Q) (κ : Measure K) [ν.IsHaarMeasure] [κ.IsHaarMeasure]

theorem iter_indicator_pos_finite (hQ : IsClosed (Q : Set G)) {S : Set G} (hS : IsCompact S)
    (m : Q × K → G) (hm : Continuous m) (h1 : m 1 ∈ interior S) {C : Set G} (hC : IsCompact C)
    (hmC : ∀ p, m p ∈ S → (p.1 : G) ∈ C) :
    ∫⁻ k, ∫⁻ q, S.indicator 1 (m (q, k)) ∂ν ∂κ ≠ 0 ∧
      ∫⁻ k, ∫⁻ q, S.indicator 1 (m (q, k)) ∂ν ∂κ ≠ ⊤ := by
  have hmeas : Measurable fun p : Q × K => S.indicator (1 : G → ℝ≥0∞) (m p) :=
    (measurable_one.indicator hS.measurableSet).comp hm.measurable
  rw [← lintegral_prod_symm (μ := ν) (ν := κ) (fun p : Q × K => S.indicator (1 : G → ℝ≥0∞) (m p))
    hmeas.aemeasurable]
  have e : (fun p : Q × K => S.indicator (1 : G → ℝ≥0∞) (m p)) = (m ⁻¹' S).indicator 1 := by
    ext p; by_cases hp : m p ∈ S <;> simp [Set.indicator, hp]
  rw [e, lintegral_indicator_one (hm.measurable hS.measurableSet)]
  constructor
  · refine (lt_of_lt_of_le ?_ (measure_mono (Set.preimage_mono interior_subset))).ne'
    exact (hm.isOpen_preimage _ isOpen_interior).measure_pos (ν.prod κ) ⟨1, h1⟩
  · have hcpt : IsCompact ((Subtype.val ⁻¹' C : Set Q) ×ˢ (Set.univ : Set K)) :=
      (hQ.isClosedEmbedding_subtypeVal.isCompact_preimage hC).prod isCompact_univ
    refine (lt_of_le_of_lt (measure_mono ?_) hcpt.measure_lt_top).ne
    intro p hp
    exact ⟨hmC p hp, trivial⟩

end GlobalTheory.HaarQK

namespace GlobalTheory


open GlobalTheory.HaarQK in
attribute [local instance] secondCountable_subgroup in
theorem lintegral_haar_eq_mul_iterated_closed_compact :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (Q K : Subgroup G), IsClosed (Q : Set G) → IsCompact (K : Set G) → (∀ g, ∃ q ∈ Q, ∃ k ∈ K, g = q * k) →
    ∀ (ν : Measure Q) (κ : Measure K) [ν.IsHaarMeasure] [κ.IsHaarMeasure], ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧
      ∀ φ : G → ENNReal, Measurable φ → ∫⁻ g, φ g ∂μ = c * ∫⁻ k, ∫⁻ q, φ (q.1 * k.1) ∂ν ∂κ := by
  intro G _ _ _ _ _ _ _ _ μ _ _ Q K hQ hK hdec ν κ _ _
  haveI : LocallyCompactSpace Q := hQ.locallyCompactSpace
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨S, hS, hS1⟩ := exists_compact_mem_nhds (1 : G)
  have hS1' : (1 : G) ∈ interior S := mem_interior_iff_mem_nhds.mpr hS1
  set w : G → ℝ≥0∞ := S.indicator 1 with hw_def
  have hw : Measurable w := measurable_one.indicator hS.measurableSet

  obtain ⟨hσ0, hσT⟩ := iter_indicator_pos_finite ν κ hQ hS (fun p : Q × K => p.1.1 * p.2.1)
    (by fun_prop) (by simpa using hS1') (hS.mul hK) (by
      intro p hp
      have : (p.1 : G) = (p.1.1 * p.2.1) * (p.2.1)⁻¹ := by group
      rw [this]; exact Set.mul_mem_mul hp (K.inv_mem p.2.2))

  obtain ⟨hE0, hET⟩ := iter_indicator_pos_finite ν κ hQ hS (fun p : Q × K => (p.1.1)⁻¹ * p.2.1)
    (by fun_prop) (by simpa using hS1') (hK.mul hS.inv) (by
      intro p hp
      have : (p.1 : G) = p.2.1 * ((p.1.1)⁻¹ * p.2.1)⁻¹ := by group
      rw [this]; exact Set.mul_mem_mul p.2.2 (by simpa using hp))
  change ∫⁻ k, ∫⁻ q, w (q.1 * k.1) ∂ν ∂κ ≠ 0 at hσ0
  change ∫⁻ k, ∫⁻ q, w (q.1 * k.1) ∂ν ∂κ ≠ ⊤ at hσT
  change ∫⁻ k, ∫⁻ q, w ((q.1)⁻¹ * k.1) ∂ν ∂κ ≠ 0 at hE0
  change ∫⁻ k, ∫⁻ q, w ((q.1)⁻¹ * k.1) ∂ν ∂κ ≠ ⊤ at hET
  set σw := ∫⁻ k, ∫⁻ q, w (q.1 * k.1) ∂ν ∂κ with hσw
  set E := ∫⁻ k, ∫⁻ q, w ((q.1)⁻¹ * k.1) ∂ν ∂κ with hE
  have hμw0 : ∫⁻ g, w g ∂μ ≠ 0 := by
    rw [hw_def, lintegral_indicator_one hS.measurableSet]
    exact (measure_pos_of_mem_nhds μ hS1).ne'
  have hμwT : ∫⁻ g, w g ∂μ ≠ ⊤ := by
    rw [hw_def, lintegral_indicator_one hS.measurableSet]
    exact hS.measure_lt_top.ne

  have key1 : ∀ u : G → ℝ≥0∞, Measurable u →
      (∫⁻ g, u g ∂μ) * E = ∫⁻ g, w g * ∫⁻ k, ∫⁻ q, u (q.1 * g * k.1) ∂ν ∂κ ∂μ := by
    intro u hu
    rw [← weil_exchange ν κ μ u w hu hw, ← lintegral_mul_const _ hu]
    congr 1; ext g
    obtain ⟨q₀, hq₀, k₀, hk₀, rfl⟩ := hdec g
    rw [iter_left ν κ w ⟨q₀, hq₀⟩ ⟨k₀, hk₀⟩]
  have key2 : ∀ u : G → ℝ≥0∞, Measurable u → ∀ g : G,
      (∫⁻ k, ∫⁻ q, u (q.1 * g * k.1) ∂ν ∂κ) * σw =
        (∫⁻ k, ∫⁻ q, w (q.1 * g * k.1) ∂ν ∂κ) * ∫⁻ k, ∫⁻ q, u (q.1 * k.1) ∂ν ∂κ := by
    intro u hu g
    obtain ⟨q₀, hq₀, k₀, hk₀, rfl⟩ := hdec g
    rw [iter_right ν κ u hu ⟨q₀, hq₀⟩ ⟨k₀, hk₀⟩, iter_right ν κ w hw ⟨q₀, hq₀⟩ ⟨k₀, hk₀⟩]
    ring
  have mA : Measurable fun g => ∫⁻ k, ∫⁻ q, w (q.1 * g * k.1) ∂ν ∂κ := by
    have mf : Measurable fun x : G × (Q × K) => w (x.2.1.1 * x.1 * x.2.2.1) :=
      hw.comp (Continuous.measurable (by fun_prop))
    have e : (fun g => ∫⁻ k, ∫⁻ q, w (q.1 * g * k.1) ∂ν ∂κ) =
        fun g => ∫⁻ p : Q × K, w (p.1.1 * g * p.2.1) ∂(ν.prod κ) := by
      funext g
      exact (lintegral_prod_symm (μ := ν) (ν := κ) (fun p : Q × K => w (p.1.1 * g * p.2.1))
        (mf.comp (measurable_const.prodMk measurable_id)).aemeasurable).symm
    rw [e]
    exact mf.lintegral_prod_right'
  have key : ∀ u : G → ℝ≥0∞, Measurable u →
      (∫⁻ g, u g ∂μ) * σw = (∫⁻ g, w g ∂μ) * ∫⁻ k, ∫⁻ q, u (q.1 * k.1) ∂ν ∂κ := by
    intro u hu
    have mwA : Measurable fun g => w g * ∫⁻ k, ∫⁻ q, w (q.1 * g * k.1) ∂ν ∂κ := hw.mul mA
    have h : (∫⁻ g, u g ∂μ) * E * σw = (∫⁻ g, w g ∂μ) * E * ∫⁻ k, ∫⁻ q, u (q.1 * k.1) ∂ν ∂κ := by
      rw [key1 u hu, key1 w hw, ← lintegral_mul_const' _ _ hσT,
        ← lintegral_mul_const _ mwA]
      congr 1; ext g
      rw [mul_assoc, key2 u hu g, ← mul_assoc]
    rw [mul_right_comm, mul_right_comm (∫⁻ g, w g ∂μ)] at h
    exact (ENNReal.mul_left_inj hE0 hET).mp h
  refine ⟨(∫⁻ g, w g ∂μ) / σw, ?_, ?_, ?_⟩
  · exact ENNReal.div_ne_zero.mpr ⟨hμw0, hσT⟩
  · exact ENNReal.div_ne_top hμwT hσ0
  · intro φ hφ
    rw [← ENNReal.mul_div_cancel_right (a := ∫⁻ g, φ g ∂μ) hσ0 hσT, key φ hφ, ENNReal.mul_div_right_comm]

end GlobalTheory
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarMeasureIwasawaModularCharacter

section

@[expose] public section

open MeasureTheory Topology Pointwise
open scoped NNReal ENNReal

namespace GlobalTheory.CompanionTheory.QKAvg

theorem mass_const {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G]
    [BorelSpace G] (Q K : Subgroup G) [LocallyCompactSpace Q]
    (hdec : ∀ g, ∃ q ∈ Q, ∃ k ∈ K, g = q * k) (δ : Q →* ℝ≥0) (hδc : Continuous δ)
    (hΔ : ∀ q : Q, Measure.modularCharacterFun q = δ q) (ν : Measure Q) [ν.IsHaarMeasure]
    [SecondCountableTopology Q] {E : Set G} (hEm : MeasurableSet E)
    (hEK : ∀ g, ∀ k ∈ K, g * k ∈ E ↔ g ∈ E) (g : G) :
    ∫⁻ q : Q, E.indicator (1 : G → ℝ≥0∞) (q.1 * g) * (δ q : ℝ≥0∞) ∂ν =
      ∫⁻ q : Q, E.indicator (1 : G → ℝ≥0∞) q.1 * (δ q : ℝ≥0∞) ∂ν := by
  obtain ⟨q0, hq0, k, hk, rfl⟩ := hdec g
  obtain ⟨p, hp⟩ : ∃ p : Q, p.1 = q0 := ⟨⟨q0, hq0⟩, rfl⟩
  have hF : Measurable fun q : Q => E.indicator (1 : G → ℝ≥0∞) q.1 * (δ q : ℝ≥0∞) :=
    ((measurable_one.indicator hEm).comp measurable_subtype_coe).mul hδc.measurable.coe_nnreal_ennreal
  have hpt : ∀ q : Q, E.indicator (1 : G → ℝ≥0∞) (q.1 * (q0 * k)) * (δ q : ℝ≥0∞) =
      (δ p⁻¹ : ℝ≥0∞) * (E.indicator (1 : G → ℝ≥0∞) (q * p).1 * (δ (q * p) : ℝ≥0∞)) := by
    intro q
    have hmem : q.1 * (q0 * k) ∈ E ↔ (q * p).1 ∈ E := by
      rw [← mul_assoc, Subgroup.coe_mul, hp]
      exact hEK _ k hk
    have h2 : (δ q : ℝ≥0∞) = (δ (q * p) : ℝ≥0∞) * (δ p⁻¹ : ℝ≥0∞) := by
      rw [← ENNReal.coe_mul, ← map_mul, mul_inv_cancel_right]
    have h3 : E.indicator (1 : G → ℝ≥0∞) (q.1 * (q0 * k)) = E.indicator (1 : G → ℝ≥0∞) (q * p).1 := by
      classical
      by_cases hm : (q * p).1 ∈ E
      · rw [Set.indicator_apply, Set.indicator_apply, if_pos (hmem.mpr hm), if_pos hm]
        rfl
      · rw [Set.indicator_apply, Set.indicator_apply, if_neg (fun h => hm (hmem.mp h)), if_neg hm]
    rw [h3, h2]
    ring
  have hΔp : (Measure.modularCharacterFun p : ℝ≥0∞) = (δ p : ℝ≥0∞) := by
    rw [hΔ p]
  calc ∫⁻ q : Q, E.indicator (1 : G → ℝ≥0∞) (q.1 * (q0 * k)) * (δ q : ℝ≥0∞) ∂ν
      = ∫⁻ q : Q, (δ p⁻¹ : ℝ≥0∞) * (E.indicator (1 : G → ℝ≥0∞) (q * p).1 * (δ (q * p) : ℝ≥0∞)) ∂ν := by
        congr 1
        funext q
        exact hpt q
    _ = (δ p⁻¹ : ℝ≥0∞) * ∫⁻ q : Q, E.indicator (1 : G → ℝ≥0∞) (q * p).1 * (δ (q * p) : ℝ≥0∞) ∂ν :=
        lintegral_const_mul _ (hF.comp (measurable_mul_const p))
    _ = (δ p⁻¹ : ℝ≥0∞) * ((Measure.modularCharacterFun p : ℝ≥0∞) *
          ∫⁻ q : Q, E.indicator (1 : G → ℝ≥0∞) q.1 * (δ q : ℝ≥0∞) ∂ν) :=
        congrArg (fun t => (δ p⁻¹ : ℝ≥0∞) * t) (GlobalTheory.HaarQK.lintegral_mul_right_modular ν hF p)
    _ = ∫⁻ q : Q, E.indicator (1 : G → ℝ≥0∞) q.1 * (δ q : ℝ≥0∞) ∂ν := by
        rw [hΔp, ← mul_assoc, ← ENNReal.coe_mul, ← map_mul, inv_mul_cancel, map_one, ENNReal.coe_one,
          one_mul]

theorem lintegral_mul_right_of_modular_law : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (Q K : Subgroup G) [LocallyCompactSpace Q], IsClosed (Q : Set G) → IsCompact (K : Set G) → (∀ g, ∃ q ∈ Q, ∃ k ∈ K, g = q * k) → ∀ δ : Q →* ℝ≥0, Continuous δ → (∀ q : Q, Measure.modularCharacterFun q = δ q) → ∀ κ : Measure K, κ.IsHaarMeasure → ∀ s : G → ℝ≥0∞, Measurable s → (∀ (q : Q) (h : G), s (q * h) = (δ q : ℝ≥0∞) * s h) → ∀ g, ∫⁻ k, s (k * g) ∂κ = ∫⁻ k, s k ∂κ := by
  intro G _ _ _ _ _ _ _ _ μ _ _ Q K _ hQ hK hdec δ hδc hΔ κ hκ s hs hsq g
  haveI := hκ
  haveI : SecondCountableTopology Q := GlobalTheory.HaarQK.secondCountable_subgroup Q
  obtain ⟨ν, hν⟩ : ∃ ν : Measure Q, ν.IsHaarMeasure := ⟨Measure.haar, inferInstance⟩
  haveI := hν
  obtain ⟨c, hc0, hctop, hdecomp⟩ :=
    GlobalTheory.lintegral_haar_eq_mul_iterated_closed_compact G μ Q K hQ hK hdec ν κ
  obtain ⟨S, hSc, hS1⟩ := exists_compact_mem_nhds (1 : G)
  set E : Set G := S * (K : Set G) with hE
  have hEc : IsCompact E := hSc.mul hK
  have hEm : MeasurableSet E := hEc.isClosed.measurableSet
  have hEK : ∀ h : G, ∀ k ∈ K, h * k ∈ E ↔ h ∈ E := by
    intro h k hk
    constructor
    · rintro ⟨a, ha, b, hb, hab⟩
      have hab' : a * b = h * k := hab
      refine ⟨a, ha, b * k⁻¹, K.mul_mem hb (K.inv_mem hk), ?_⟩
      show a * (b * k⁻¹) = h
      rw [← mul_assoc, hab', mul_inv_cancel_right]
    · rintro ⟨a, ha, b, hb, hab⟩
      have hab' : a * b = h := hab
      refine ⟨a, ha, b * k, K.mul_mem hb hk, ?_⟩
      show a * (b * k) = h * k
      rw [← mul_assoc, hab']
  set M := ∫⁻ q : Q, E.indicator (1 : G → ℝ≥0∞) q.1 * (δ q : ℝ≥0∞) ∂ν with hMdef
  have hmass : ∀ t : G, ∫⁻ q : Q, E.indicator (1 : G → ℝ≥0∞) (q.1 * t) * (δ q : ℝ≥0∞) ∂ν = M :=
    fun t => mass_const Q K hdec δ hδc hΔ ν hEm hEK t
  have hT : IsCompact (((↑) : Q → G) ⁻¹' E) := hQ.isClosedEmbedding_subtypeVal.isCompact_preimage hEc
  have hMeq : M = ∫⁻ q in ((↑) : Q → G) ⁻¹' E, (δ q : ℝ≥0∞) ∂ν := by
    rw [hMdef, ← lintegral_indicator (hEm.preimage measurable_subtype_coe)]
    refine lintegral_congr fun q => ?_
    by_cases hq : q.1 ∈ E
    · simp [Set.indicator_apply, hq]
    · simp [Set.indicator_apply, hq]
  have hMtop : M ≠ ⊤ := by
    rw [hMeq]
    exact (setLIntegral_lt_top_of_isCompact hT.measure_lt_top.ne hT hδc).ne
  have hδ0 : ∀ q : Q, (δ q : ℝ≥0∞) ≠ 0 := by
    intro q hq
    have h1 := map_mul_eq_one δ (mul_inv_cancel q)
    rw [ENNReal.coe_eq_zero] at hq
    rw [hq, zero_mul] at h1
    exact zero_ne_one h1
  have hM0 : M ≠ 0 := by
    rw [hMeq]
    intro h0
    rw [lintegral_eq_zero_iff hδc.measurable.coe_nnreal_ennreal] at h0
    have h1 : ∀ᵐ q ∂(ν.restrict (((↑) : Q → G) ⁻¹' E)), False :=
      h0.mono fun q hq => hδ0 q hq
    rw [ae_iff] at h1
    have hTz : ν (((↑) : Q → G) ⁻¹' E) = 0 := by simpa using h1
    have hV : ((↑) : Q → G) ⁻¹' S ∈ 𝓝 (1 : Q) :=
      continuous_subtype_val.continuousAt.preimage_mem_nhds hS1
    have hpos := Measure.measure_pos_of_mem_nhds ν hV
    have hsub : ((↑) : Q → G) ⁻¹' S ⊆ ((↑) : Q → G) ⁻¹' E := fun q hq =>
      ⟨q.1, hq, 1, K.one_mem, mul_one _⟩
    have := measure_mono (μ := ν) hsub
    rw [hTz] at this
    exact (lt_irrefl 0 (hpos.trans_le this))
  have hin : ∀ a b : G, ∫⁻ q : Q, E.indicator (1 : G → ℝ≥0∞) (↑q * a) * s (↑q * b) ∂ν = M * s b := by
    intro a b
    have h1 : ∀ q : Q, E.indicator (1 : G → ℝ≥0∞) (↑q * a) * s (↑q * b) =
        E.indicator (1 : G → ℝ≥0∞) (↑q * a) * (δ q : ℝ≥0∞) * s b := by
      intro q
      rw [hsq q b, mul_assoc]
    have hmeas : Measurable fun q : Q => E.indicator (1 : G → ℝ≥0∞) (↑q * a) * (δ q : ℝ≥0∞) :=
      ((measurable_one.indicator hEm).comp ((measurable_mul_const a).comp measurable_subtype_coe)).mul
        hδc.measurable.coe_nnreal_ennreal
    rw [lintegral_congr h1, lintegral_mul_const _ hmeas, hmass a]
  have hA : ∫⁻ h, E.indicator (1 : G → ℝ≥0∞) h * s (h * g) ∂μ = c * (M * ∫⁻ k : K, s (↑k * g) ∂κ) := by
    have hmA : Measurable fun h : G => E.indicator (1 : G → ℝ≥0∞) h * s (h * g) :=
      (measurable_one.indicator hEm).mul (hs.comp (measurable_mul_const g))
    rw [hdecomp (fun h : G => E.indicator (1 : G → ℝ≥0∞) h * s (h * g)) hmA]
    congr 1
    rw [← lintegral_const_mul' M _ hMtop]
    refine lintegral_congr fun k => ?_
    simp only [mul_assoc]
    exact hin (↑k) (↑k * g)
  have hB : ∫⁻ h, E.indicator (1 : G → ℝ≥0∞) (h * g⁻¹) * s h ∂μ = c * (M * ∫⁻ k : K, s ↑k ∂κ) := by
    have hmB : Measurable fun h : G => E.indicator (1 : G → ℝ≥0∞) (h * g⁻¹) * s h :=
      ((measurable_one.indicator hEm).comp (measurable_mul_const g⁻¹)).mul hs
    rw [hdecomp (fun h : G => E.indicator (1 : G → ℝ≥0∞) (h * g⁻¹) * s h) hmB]
    congr 1
    rw [← lintegral_const_mul' M _ hMtop]
    refine lintegral_congr fun k => ?_
    simp only [mul_assoc]
    exact hin (↑k * g⁻¹) ↑k
  have hI : ∫⁻ h, E.indicator (1 : G → ℝ≥0∞) h * s (h * g) ∂μ =
      ∫⁻ h, E.indicator (1 : G → ℝ≥0∞) (h * g⁻¹) * s h ∂μ := by
    rw [← lintegral_mul_right_eq_self (fun h => E.indicator (1 : G → ℝ≥0∞) (h * g⁻¹) * s h) g]
    simp only [mul_inv_cancel_right]
  rw [hA, hB] at hI
  exact (ENNReal.mul_right_inj hM0 hMtop).mp ((ENNReal.mul_right_inj hc0 hctop).mp hI)

end GlobalTheory.CompanionTheory.QKAvg
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarMeasureIwasawaModularCharacterStatement

section

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal

theorem _root_.GlobalTheory.T.haar_measure_iwasawa_modular_character : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (Q K : Subgroup G) [LocallyCompactSpace Q], IsClosed (Q : Set G) → IsCompact (K : Set G) → (∀ g, ∃ q ∈ Q, ∃ k ∈ K, g = q * k) → ∀ δ : Q →* ℝ≥0, Continuous δ → (∀ q : Q, Measure.modularCharacterFun q = δ q) → ∀ κ : Measure K, κ.IsHaarMeasure → ∀ s : G → ℝ≥0∞, Measurable s → (∀ (q : Q) (h : G), s (q * h) = (δ q : ℝ≥0∞) * s h) → ∀ g, ∫⁻ k, s (k * g) ∂κ = ∫⁻ k, s k ∂κ := by
  first | exact @GlobalTheory.CompanionTheory.QKAvg.lintegral_mul_right_of_modular_law | exact GlobalTheory.CompanionTheory.QKAvg.lintegral_mul_right_of_modular_law | (intros; apply GlobalTheory.CompanionTheory.QKAvg.lintegral_mul_right_of_modular_law <;> assumption)
end
end
