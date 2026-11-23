module

public import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Mathlib.MeasureTheory.Group.Defs
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientMeasure.StepBruhat

section

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace PI.WeilQuotMeas.UnitaryGroupMassFormula

def StepBruhat : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (H : Subgroup G), IsClosed (H : Set G) →
    ∀ ν : Measure H, ν.IsHaarMeasure →
      ∃ β : G → ℝ≥0∞, Measurable β ∧ ∀ g : G, ∫⁻ h, β (g * (h : G)) ∂ν = 1

end PI.WeilQuotMeas.UnitaryGroupMassFormula
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientMeasure.LintegralMulAvgComm

section

@[expose] public section

noncomputable section

open MeasureTheory Topology
open scoped ENNReal Pointwise

namespace PI.WeilQuotMeas.UnitaryGroupMassFormula

section Lemmas

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {H : Subgroup G}

theorem measurable_mul_coe : Measurable (fun p : G × H => p.1 * (p.2 : G)) := measurable_fst.mul (measurable_subtype_coe.comp measurable_snd)

theorem measurable_avg (ν : Measure H) [SFinite ν] {f : G → ℝ≥0∞} (hf : Measurable f) :
    Measurable (fun g : G => ∫⁻ h, f (g * (h : G)) ∂ν) := (hf.comp measurable_mul_coe).lintegral_prod_right'

theorem avg_mul_right (ν : Measure H) [ν.IsMulLeftInvariant] (f : G → ℝ≥0∞) (g : G) (k : H) :
    ∫⁻ h, f (g * (k : G) * (h : G)) ∂ν = ∫⁻ h, f (g * (h : G)) ∂ν := by
  have e := lintegral_mul_left_eq_self (μ := ν) (fun h : H => f (g * (h : G))) k
  simpa [mul_assoc] using e

end Lemmas

end PI.WeilQuotMeas.UnitaryGroupMassFormula
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientMeasure.Bruhat

section

@[expose] public section

noncomputable section

open MeasureTheory Topology
open scoped ENNReal Pointwise

namespace PI.WeilQuotMeas.UnitaryGroupMassFormula

theorem stepBruhat : StepBruhat := by
  intro G _ _ _ _ _ _ _ _ H hH ν hν
  classical
  have : LocallyCompactSpace H := hH.locallyCompactSpace
  have : SecondCountableTopology H := TopologicalSpace.Subtype.secondCountableTopology (H : Set G)
  obtain ⟨K0, hK0, h1⟩ := exists_compact_mem_nhds (1 : G)
  obtain ⟨d, hd⟩ : ∃ d : ℕ → G, DenseRange d := TopologicalSpace.exists_dense_seq G
  obtain ⟨U, hU⟩ : ∃ U : ℕ → Set G, U = fun n => (fun x => d n * x) '' interior K0 := ⟨_, rfl⟩
  have hUo : ∀ n, IsOpen (U n) := fun n => by
    rw [hU]; exact isOpenMap_mul_left (d n) _ isOpen_interior
  have hUK : ∀ n, U n ⊆ (fun x => d n * x) '' K0 := fun n => by
    rw [hU]; exact Set.image_mono interior_subset
  have hcov : ∀ g : G, ∃ n, g ∈ U n := by
    intro g
    have ho : IsOpen ((fun x => g * x) '' (interior K0)⁻¹) :=
      isOpenMap_mul_left g _ isOpen_interior.inv
    have h1' : (1 : G) ∈ (interior K0)⁻¹ := by
      rw [Set.mem_inv, inv_one]; exact mem_interior_iff_mem_nhds.2 h1
    obtain ⟨n, hn⟩ := hd.exists_mem_open ho ⟨g, 1, h1', mul_one g⟩
    obtain ⟨z, hz, hzn⟩ := hn
    simp only at hzn
    refine ⟨n, ?_⟩
    rw [hU]
    show g ∈ (fun x => d n * x) '' interior K0
    exact ⟨z⁻¹, Set.mem_inv.1 hz, by simp only; rw [← hzn, mul_inv_cancel_right]⟩
  obtain ⟨A, hA⟩ : ∃ A : ℕ → G → ℝ≥0∞,
      A = fun n g => ∫⁻ h, (U n).indicator 1 (g * (h : G)) ∂ν := ⟨_, rfl⟩
  have hAm : ∀ n, Measurable (A n) := fun n => by
    rw [hA]; exact measurable_avg ν (measurable_one.indicator (hUo n).measurableSet)
  have hAinv : ∀ n g (k : H), A n (g * k) = A n g := fun n g k => by
    rw [hA]; exact avg_mul_right ν _ g k
  have hAeq : ∀ n g, A n g = ν {h : H | g * (h : G) ∈ U n} := fun n g => by
    have hS : MeasurableSet {h : H | g * (h : G) ∈ U n} :=
      (continuous_const.mul continuous_subtype_val).measurable (hUo n).measurableSet
    rw [← lintegral_indicator_one hS, hA]
    rfl
  have hApos : ∀ n g, g ∈ U n → 0 < A n g := fun n g hg => by
    rw [hAeq]
    refine IsOpen.measure_pos ν ((hUo n).preimage (continuous_const.mul continuous_subtype_val))
      ⟨1, ?_⟩
    show g * ((1 : H) : G) ∈ U n
    rw [OneMemClass.coe_one, mul_one]; exact hg
  have hAfin : ∀ n g, A n g < ⊤ := fun n g => by
    rw [hAeq]
    have hKc : IsCompact ((fun x => d n * x) '' K0) := hK0.image (continuous_const_mul (d n))
    have hpre : ∀ S : Set G, (fun x => g * x) ⁻¹' S = (fun x => g⁻¹ * x) '' S := fun S => by
      rw [Set.image_mul_left, inv_inv]
    have hc2 : IsCompact ((fun x => g * x) ⁻¹' ((fun x => d n * x) '' K0)) := by
      rw [hpre]; exact hKc.image (continuous_const_mul g⁻¹)
    have hc3 : IsCompact (Subtype.val ⁻¹' ((fun x => g * x) ⁻¹' ((fun x => d n * x) '' K0)) :
        Set H) := hH.isClosedEmbedding_subtypeVal.isCompact_preimage hc2
    refine lt_of_le_of_lt (measure_mono ?_) hc3.measure_lt_top
    intro h hh
    exact hUK n hh
  have hex : ∀ g, ∃ n, 0 < A n g := fun g => (hcov g).imp fun n hn => hApos n g hn
  obtain ⟨n₀, hn₀⟩ : ∃ n₀ : G → ℕ, n₀ = fun g => Nat.find (hex g) := ⟨_, rfl⟩
  have hspec : ∀ g, 0 < A (n₀ g) g := fun g => by rw [hn₀]; exact Nat.find_spec (hex g)
  have hmin : ∀ g m, 0 < A m g → n₀ g ≤ m := fun g m hm => by rw [hn₀]; exact Nat.find_min' _ hm
  have hn₀inv : ∀ g (k : H), n₀ (g * k) = n₀ g := fun g k =>
    le_antisymm (hmin _ _ (by rw [hAinv]; exact hspec g))
      (hmin _ _ (by rw [← hAinv _ g k]; exact hspec _))
  have hn₀m : Measurable n₀ := by
    rw [hn₀]
    exact measurable_find hex fun k => measurableSet_lt measurable_const (hAm k)
  obtain ⟨b, hb⟩ : ∃ b : G → ℝ≥0∞, b = fun g => (U (n₀ g)).indicator 1 g := ⟨_, rfl⟩
  have hbm : Measurable b := by
    intro t ht
    have e : b ⁻¹' t = ⋃ n, (n₀ ⁻¹' {n}) ∩ ((U n).indicator (1 : G → ℝ≥0∞)) ⁻¹' t := by
      ext g
      simp only [hb, Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_singleton_iff,
        exists_eq_left']
    rw [e]
    exact MeasurableSet.iUnion fun n => (hn₀m (measurableSet_singleton n)).inter
      ((measurable_one.indicator (hUo n).measurableSet) ht)
  obtain ⟨a, ha⟩ : ∃ a : G → ℝ≥0∞, a = fun g => ∫⁻ h, b (g * (h : G)) ∂ν := ⟨_, rfl⟩
  have ham : Measurable a := by rw [ha]; exact measurable_avg ν hbm
  have hainv : ∀ g (k : H), a (g * k) = a g := fun g k => by rw [ha]; exact avg_mul_right ν b g k
  have haA : ∀ g, a g = A (n₀ g) g := fun g => by
    rw [ha, hA]
    refine lintegral_congr fun h => ?_
    rw [hb]
    simp only [hn₀inv]
  have ha0 : ∀ g, a g ≠ 0 := fun g => by rw [haA]; exact (hspec g).ne'
  have hat : ∀ g, a g ≠ ⊤ := fun g => by rw [haA]; exact (hAfin _ g).ne
  refine ⟨fun g => b g * (a g)⁻¹, hbm.mul ham.inv, fun g => ?_⟩
  have hbg : Measurable (fun h : H => b (g * (h : G))) :=
    hbm.comp (continuous_const.mul continuous_subtype_val).measurable
  calc ∫⁻ h, b (g * (h : G)) * (a (g * (h : G)))⁻¹ ∂ν
      = ∫⁻ h, b (g * (h : G)) * (a g)⁻¹ ∂ν := by
        refine lintegral_congr fun h => ?_
        rw [hainv]
    _ = a g * (a g)⁻¹ := by rw [lintegral_mul_const _ hbg, ha]
    _ = 1 := ENNReal.mul_inv_cancel (ha0 g) (hat g)

end PI.WeilQuotMeas.UnitaryGroupMassFormula
end
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ClosedSubgroupQuotientMeasure

section

@[expose] public section

open MeasureTheory Topology
open scoped ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW

noncomputable def closedEmbeddingRangeEquiv {G G₁ : Type} [Group G] [TopologicalSpace G]
    [Group G₁] [TopologicalSpace G₁] (ι : G₁ →* G) (hι : IsClosedEmbedding ι) :
    G₁ ≃ₜ* ι.range :=
  have hemb : IsEmbedding ι.rangeRestrict :=
    IsEmbedding.of_comp (hι.continuous.subtype_mk _) continuous_subtype_val hι.isEmbedding
  { MulEquiv.ofBijective ι.rangeRestrict
      ⟨hemb.injective, ι.rangeRestrict_surjective⟩ with
    continuous_toFun := hemb.continuous
    continuous_invFun :=
      (hemb.toHomeomorphOfSurjective ι.rangeRestrict_surjective).symm.continuous }

theorem exists_weight_mass_one_right_coset :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (G₁ : Type) [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [SecondCountableTopology G₁] [MeasurableSpace G₁] [BorelSpace G₁] (ι : G₁ →* G), IsClosedEmbedding ι → ∀ (μ₁ : Measure G₁) [μ₁.IsHaarMeasure] [μ₁.IsMulRightInvariant], ∃ w : G → ℝ≥0∞, Measurable w ∧ ∀ g, ∫⁻ u, w (ι u * g) ∂μ₁ = 1 := by
  intro G _ _ _ _ _ _ _ _ G₁ _ _ _ _ _ _ _ ι hι μ₁ _ _
  have hclosed : IsClosed ((ι.range : Subgroup G) : Set G) := by
    rw [MonoidHom.coe_range]; exact hι.isClosed_range
  let e : G₁ ≃ₜ* ι.range := closedEmbeddingRangeEquiv ι hι
  haveI : IsFiniteMeasureOnCompacts μ₁.inv :=
    ⟨fun K hK => by rw [Measure.inv_apply]; exact hK.inv.measure_lt_top⟩
  haveI : μ₁.inv.IsOpenPosMeasure :=
    ⟨fun U hU hne => by
      rw [Measure.inv_apply]; exact hU.inv.measure_ne_zero μ₁ hne.inv⟩
  haveI hinv : μ₁.inv.IsHaarMeasure := {}
  have hν : (μ₁.inv.map e).IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map μ₁.inv e
  obtain ⟨β, hβ, hmass⟩ := PI.WeilQuotMeas.UnitaryGroupMassFormula.stepBruhat G ι.range hclosed _ hν
  refine ⟨fun g => β g⁻¹, hβ.comp measurable_inv, fun g => ?_⟩
  have hem : Measurable e := e.continuous.measurable
  have hf : Measurable fun h : ι.range => β (g⁻¹ * (h : G)) :=
    hβ.comp (measurable_const.mul measurable_subtype_coe)
  have h1 := hmass g⁻¹
  have hcomp : Measurable fun a : G₁ => β (g⁻¹ * (e a : G)) := hf.comp hem
  rw [lintegral_map hf hem, Measure.inv, lintegral_map hcomp measurable_inv] at h1
  refine Eq.trans (lintegral_congr fun u => ?_) h1
  have : ((e u⁻¹ : ι.range) : G) = (ι u)⁻¹ := by
    show ι u⁻¹ = _
    exact map_inv ι u
  show β (ι u * g)⁻¹ = β (g⁻¹ * ((e u⁻¹ : ι.range) : G))
  rw [this, mul_inv_rev]

end GlobalTheory.CompanionTheory.SW
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ClosedSubgroupQuotientMeasureStatement

section

@[expose] public section

open MeasureTheory Topology
open scoped ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.closed_subgroup_quotient_measure : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (G₁ : Type) [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [SecondCountableTopology G₁] [MeasurableSpace G₁] [BorelSpace G₁] (ι : G₁ →* G), IsClosedEmbedding ι → ∀ (μ₁ : Measure G₁) [μ₁.IsHaarMeasure] [μ₁.IsMulRightInvariant], ∃ w : G → ℝ≥0∞, Measurable w ∧ ∀ g, ∫⁻ u, w (ι u * g) ∂μ₁ = 1 := by
  first | exact @GlobalTheory.CompanionTheory.SW.exists_weight_mass_one_right_coset | exact GlobalTheory.CompanionTheory.SW.exists_weight_mass_one_right_coset | (intros; apply GlobalTheory.CompanionTheory.SW.exists_weight_mass_one_right_coset <;> assumption)
end
end
