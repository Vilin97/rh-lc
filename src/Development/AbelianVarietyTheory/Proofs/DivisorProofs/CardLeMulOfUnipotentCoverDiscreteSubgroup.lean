module

public import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactSpaceAxis
public import Mathlib.MeasureTheory.Group.FundamentalDomain
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EncardSmulMemLeEncardSmulInterNonempty
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLv
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactUnipFlag
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EisensteinIsotropicLine
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralConjNormalizerEqConstMulHaarStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureTranslateShellLeDivModulus
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.RingTheory.WittVector.IsPoly
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarFundDomainLeCardMulOfTranslateCover

section

@[expose] public section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

theorem measure_fund_le_card_mul_of_cover : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (N Λ : Subgroup G) [Countable Λ] (ν : Measure N) (DN : Set N) (b : G) (κ : ℝ≥0∞) (V : Set G) (Y : Finset G), ν.IsHaarMeasure → IsFundamentalDomain (Λ.subgroupOf N) DN ν → IsCompact V → (∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ u : N, f (b * u * b⁻¹) ∂ν = κ * ∫⁻ u : N, f u ∂ν) → (∀ y ∈ Y, y ∈ N) → (∀ u ∈ N, ∃ γ ∈ Λ, γ ∈ N ∧ ∃ y ∈ Y, ∃ w ∈ V, γ * u = y * b⁻¹ * w * b) → ν DN ≤ Y.card * (κ * ν {u | (u : G) ∈ V}) := by
  intro G _ _ _ _ _ _ _ _ N Λ _ ν DN b κ V Y hν hD hV hconj hY hcov
  have hVm : MeasurableSet V := hV.isClosed.measurableSet
  have hconjm : Measurable fun u : N => b * (u : G) * b⁻¹ :=
    (measurable_const.mul measurable_subtype_coe).mul measurable_const
  have hS₀m : MeasurableSet {u : N | b * (u : G) * b⁻¹ ∈ V} := hconjm hVm
  have hVNm : MeasurableSet {u : N | (u : G) ∈ V} := measurable_subtype_coe hVm
  have hS₀ : ν {u : N | b * (u : G) * b⁻¹ ∈ V} = κ * ν {u : N | (u : G) ∈ V} := by
    have h := hconj (V.indicator 1) (measurable_one.indicator hVm)
    have e1 : (fun u : N => V.indicator (1 : G → ℝ≥0∞) (b * u * b⁻¹))
        = {u : N | b * (u : G) * b⁻¹ ∈ V}.indicator 1 := by
      ext u; simp [Set.indicator]
    have e2 : (fun u : N => V.indicator (1 : G → ℝ≥0∞) u) = {u : N | (u : G) ∈ V}.indicator 1 := by
      ext u; simp [Set.indicator]
    rw [e1, e2, lintegral_indicator hS₀m, lintegral_indicator hVNm] at h
    simpa using h
  have hΛN : Countable (Λ.subgroupOf N) := by
    refine Function.Injective.countable (f := fun x : Λ.subgroupOf N => (⟨(x : N), x.2⟩ : Λ)) ?_
    intro x y h
    apply Subtype.ext; apply Subtype.ext
    simpa using congrArg (fun z : Λ => (z : G)) h
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableConstSMul_subgroup (Λ.subgroupOf N)
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.smulInvariant_subgroup (Λ.subgroupOf N) ν
  let T : G → Set N := fun y => {v : N | b * (y⁻¹ * (v : G)) * b⁻¹ ∈ V}
  have hle : ν DN ≤ ν (⋃ y ∈ Y, T y) := by
    refine GlobalTheory.measure_le_of_isFundamentalDomain_of_ae_covers hD (.of_forall fun u => ?_)
    obtain ⟨γ, hγΛ, hγN, y, hy, w, hw, heq⟩ := hcov u u.2
    refine ⟨⟨⟨γ, hγN⟩, (Subgroup.mem_subgroupOf).2 hγΛ⟩, Set.mem_biUnion hy ?_⟩
    show b * (y⁻¹ * (γ * (u : G))) * b⁻¹ ∈ V
    rw [heq]
    convert hw using 1
    group
  have hT : ∀ y ∈ Y, ν (T y) = κ * ν {u : N | (u : G) ∈ V} := by
    intro y hy
    have hyN : y⁻¹ ∈ N := N.inv_mem (hY y hy)
    have : T y = (fun v : N => (⟨y⁻¹, hyN⟩ : N) * v) ⁻¹' {u : N | b * (u : G) * b⁻¹ ∈ V} := by
      ext v; simp [T, mul_assoc]
    rw [this, measure_preimage_mul, hS₀]
  refine hle.trans ((measure_biUnion_finset_le _ _).trans ?_)
  rw [Finset.sum_congr rfl hT, Finset.sum_const, nsmul_eq_mul]

end GlobalTheory.SphEis
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarFundDomainLeCardMulOfTranslateCoverStatement

section

@[expose] public section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)


theorem _root_.GlobalTheory.T.haar_fundDomain_le_card_mul_of_translateCover : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (N Λ : Subgroup G) [Countable Λ] (ν : Measure N) (DN : Set N) (b : G) (κ : ℝ≥0∞) (V : Set G) (Y : Finset G), ν.IsHaarMeasure → IsFundamentalDomain (Λ.subgroupOf N) DN ν → IsCompact V → (∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ u : N, f (b * u * b⁻¹) ∂ν = κ * ∫⁻ u : N, f u ∂ν) → (∀ y ∈ Y, y ∈ N) → (∀ u ∈ N, ∃ γ ∈ Λ, γ ∈ N ∧ ∃ y ∈ Y, ∃ w ∈ V, γ * u = y * b⁻¹ * w * b) → ν DN ≤ Y.card * (κ * ν {u | (u : G) ∈ V}) := by
  first | exact @GlobalTheory.SphEis.measure_fund_le_card_mul_of_cover | exact GlobalTheory.SphEis.measure_fund_le_card_mul_of_cover | (intros; apply GlobalTheory.SphEis.measure_fund_le_card_mul_of_cover <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureTranslateShellLeDivModulusStatement

section

@[expose] public section

open MeasureTheory Filter Topology GlobalTheory.ResLine
open scoped ENNReal

theorem _root_.GlobalTheory.T.measure_translate_shell_le_div_modulus : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (N M Λ : Subgroup G) [Countable Λ] (ν : Measure N) (π : Measure M) (DN : Set N) (DM : Set M), SemiLat N M Λ ν π DN DM → ∀ (μ : Measure G) (D : Set G), μ.IsHaarMeasure → IsFundamentalDomain Λ D μ → ∀ C : Set G, IsCompact C → ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ (b : G) (κ : ℝ≥0∞), (∀ m ∈ M, b * m = m * b) → (∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ u : N, f (b * u * b⁻¹) ∂ν = κ * ∫⁻ u : N, f u ∂ν) → ∀ S : Set G, MeasurableSet S → (∀ x ∈ S, ∃ u ∈ N, ∃ m ∈ M, ∃ y ∈ C, b * x = u * m * y) → κ * μ (S ∩ D) ≤ B := by
  first | exact @GlobalTheory.ResLine.modulus_mul_measure_shell_le | exact GlobalTheory.ResLine.modulus_mul_measure_shell_le | (intros; apply GlobalTheory.ResLine.modulus_mul_measure_shell_le <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PackingCountInequivalentDiscreteSubgroup

section

@[expose] public section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

open scoped Pointwise

namespace GlobalTheory.Packing

theorem mem_smul_smul_iff {G : Type} [Group G] (Λ : Subgroup G) (γ : Λ) (t x : G) (U : Set G) :
    x ∈ γ • (t • U) ↔ t⁻¹ * ((γ : G)⁻¹ * x) ∈ U := by
  rw [Set.mem_smul_set_iff_inv_smul_mem, Set.mem_smul_set_iff_inv_smul_mem]
  simp [Subgroup.smul_def, smul_eq_mul]

theorem packing_count : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (Γ Λ : Subgroup G) [Countable Λ] (μ : Measure G) (D U : Set G), Λ ≤ Γ → (∀ K : Set G, IsCompact K → (K ∩ Γ).Finite) → μ.IsHaarMeasure → IsFundamentalDomain Λ D μ → IsCompact U → ∃ k : ℕ, ∀ (T : Finset G) (S : Set G), (∀ t ∈ T, t ∈ Γ) → (∀ t ∈ T, ∀ t' ∈ T, t' * t⁻¹ ∈ Λ → t = t') → MeasurableSet S → (∀ γ ∈ Λ, ∀ x ∈ S, γ * x ∈ S) → (∀ t ∈ T, ∀ u ∈ U, t * u ∈ S) → T.card * μ U ≤ k * μ (S ∩ D) := by
  intro G _ _ _ _ _ _ _ _ Γ Λ _ μ D U hΛΓ hdisc hHaar hD hU
  have hUc : IsCompact (U * U⁻¹) := hU.mul hU.inv
  have hfin : (U * U⁻¹ ∩ (Γ : Set G)).Finite := hdisc _ hUc
  refine ⟨hfin.toFinset.card, ?_⟩
  intro T S hTΓ hTdist hS hSinv hTS
  have hUm : MeasurableSet U := hU.isClosed.measurableSet
  have hmeasA : ∀ (γ : Λ) (t : G), MeasurableSet (γ • (t • U)) := by
    intro γ t
    have : γ • (t • U) = (fun y => t⁻¹ * ((γ : G)⁻¹ * y)) ⁻¹' U := by
      ext y; rw [mem_smul_smul_iff]; rfl
    rw [this]
    exact hUm.preimage (continuous_const.mul (continuous_const.mul continuous_id)).measurable
  have hsubS : ∀ (γ : Λ), ∀ t ∈ T, γ • (t • U) ⊆ S := by
    intro γ t ht y hy
    rw [mem_smul_smul_iff] at hy
    have h1 := hSinv (γ : G) γ.2 _ (hTS t ht _ hy)
    simpa [mul_assoc] using h1
  set ν := μ.restrict (S ∩ D) with hν
  have key : ∀ t ∈ T, μ U = ∑' γ : Λ, ∫⁻ x, (γ • (t • U)).indicator 1 x ∂ν := by
    intro t ht
    rw [← measure_smul μ t U, hD.measure_eq_tsum (t • U)]
    refine tsum_congr fun γ => ?_
    rw [lintegral_indicator_one (hmeasA γ t), hν, Measure.restrict_apply (hmeasA γ t)]
    congr 1
    ext y
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, hsubS γ t ht h1, h2⟩
    · rintro ⟨h1, _, h2⟩; exact ⟨h1, h2⟩
  have hpt : ∀ x : G, ∑ t ∈ T, ∑' γ : Λ, (γ • (t • U)).indicator (1 : G → ℝ≥0∞) x
      ≤ (hfin.toFinset.card : ℝ≥0∞) := by
    intro x
    classical
    have hswap : ∑ t ∈ T, ∑' γ : Λ, (γ • (t • U)).indicator (1 : G → ℝ≥0∞) x
        = ∑' γ : Λ, ∑ t ∈ T, (γ • (t • U)).indicator (1 : G → ℝ≥0∞) x := by
      first
      | exact (Summable.tsum_finsetSum fun _ _ => ENNReal.summable).symm
      | exact (tsum_sum fun _ _ => ENNReal.summable).symm
      | exact (ENNReal.tsum_finsetSum _ _).symm
    rw [hswap, ENNReal.tsum_eq_iSup_sum]
    refine iSup_le fun s => ?_
    have hbool : ∑ γ ∈ s, ∑ t ∈ T, (γ • (t • U)).indicator (1 : G → ℝ≥0∞) x
        = (((s ×ˢ T).filter (fun p : Λ × G => x ∈ p.1 • (p.2 • U))).card : ℝ≥0∞) := by
      rw [Finset.card_filter, Finset.sum_product]
      push_cast
      simp only [Set.indicator_apply, Pi.one_apply]
    rw [hbool]
    have hcard : ((s ×ˢ T).filter (fun p : Λ × G => x ∈ p.1 • (p.2 • U))).card
        ≤ hfin.toFinset.card := by
      set P := (s ×ˢ T).filter (fun p : Λ × G => x ∈ p.1 • (p.2 • U)) with hPdef
      have memP : ∀ p : Λ × G, p ∈ P → p.2 ∈ T ∧ x ∈ p.1 • (p.2 • U) := by
        intro p hp
        rw [hPdef, Finset.mem_filter, Finset.mem_product] at hp
        exact ⟨hp.1.2, hp.2⟩
      rcases P.eq_empty_or_nonempty with hP | ⟨p₀, h₀⟩
      · rw [hP]; exact Nat.zero_le _
      obtain ⟨ht₀, hx₀⟩ := memP p₀ h₀
      rw [mem_smul_smul_iff] at hx₀
      refine Finset.card_le_card_of_injOn
        (fun p : Λ × G => (p₀.2⁻¹ * (p₀.1 : G)⁻¹) * ((p.1 : G) * p.2)) ?_ ?_
      · intro p hp
        have hp' : p ∈ P := by first | exact Finset.mem_coe.1 hp | exact hp
        obtain ⟨ht, hx⟩ := memP p hp'
        rw [mem_smul_smul_iff] at hx
        show _ ∈ (hfin.toFinset : Set G)
        rw [Set.Finite.coe_toFinset]
        refine ⟨?_, ?_⟩
        · refine Set.mem_mul.2 ⟨_, hx₀, (p.2⁻¹ * ((p.1 : G)⁻¹ * x))⁻¹, ?_, ?_⟩
          · rw [Set.mem_inv, inv_inv]; exact hx
          · group
        · exact Γ.mul_mem (Γ.mul_mem (Γ.inv_mem (hTΓ _ ht₀)) (Γ.inv_mem (hΛΓ p₀.1.2)))
            (Γ.mul_mem (hΛΓ p.1.2) (hTΓ _ ht))
      · intro p hp q hq hpq
        have hp' : p ∈ P := by first | exact Finset.mem_coe.1 hp | exact hp
        have hq' : q ∈ P := by first | exact Finset.mem_coe.1 hq | exact hq
        have hpT := (memP p hp').1
        have hqT := (memP q hq').1
        have h1 : (p.1 : G) * p.2 = (q.1 : G) * q.2 := mul_left_cancel hpq
        have e : q.2 * p.2⁻¹ = (q.1 : G)⁻¹ * p.1 := by
          rw [mul_inv_eq_iff_eq_mul, mul_assoc, h1, ← mul_assoc, inv_mul_cancel, one_mul]
        have htt : p.2 = q.2 := hTdist _ hpT _ hqT (e ▸ Λ.mul_mem (Λ.inv_mem q.1.2) p.1.2)
        have hg : (p.1 : G) = q.1 := by
          rw [htt] at h1; exact mul_right_cancel h1
        exact Prod.ext (Subtype.ext hg) htt
    exact_mod_cast hcard
  calc (T.card : ℝ≥0∞) * μ U = ∑ t ∈ T, μ U := by rw [Finset.sum_const, nsmul_eq_mul]
    _ = ∑ t ∈ T, ∑' γ : Λ, ∫⁻ x, (γ • (t • U)).indicator 1 x ∂ν := Finset.sum_congr rfl key
    _ = ∫⁻ x, ∑ t ∈ T, ∑' γ : Λ, (γ • (t • U)).indicator (1 : G → ℝ≥0∞) x ∂ν := by
      rw [lintegral_finsetSum']
      · refine Finset.sum_congr rfl fun t _ => ?_
        rw [lintegral_tsum]
        exact fun γ => ((measurable_one.indicator (hmeasA γ t))).aemeasurable
      · intro t _
        exact (Measurable.tsum fun γ => measurable_one.indicator (hmeasA γ t)).aemeasurable
    _ ≤ ∫⁻ _x, (hfin.toFinset.card : ℝ≥0∞) ∂ν := lintegral_mono hpt
    _ = (hfin.toFinset.card : ℝ≥0∞) * μ (S ∩ D) := by
      rw [lintegral_const, hν, Measure.restrict_apply_univ]

end GlobalTheory.Packing
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PackingCountInequivalentDiscreteSubgroupStatement

section

@[expose] public section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)


theorem _root_.GlobalTheory.T.packing_count_inequivalent_discreteSubgroup : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (Γ Λ : Subgroup G) [Countable Λ] (μ : Measure G) (D U : Set G), Λ ≤ Γ → (∀ K : Set G, IsCompact K → (K ∩ Γ).Finite) → μ.IsHaarMeasure → IsFundamentalDomain Λ D μ → IsCompact U → ∃ k : ℕ, ∀ (T : Finset G) (S : Set G), (∀ t ∈ T, t ∈ Γ) → (∀ t ∈ T, ∀ t' ∈ T, t' * t⁻¹ ∈ Λ → t = t') → MeasurableSet S → (∀ γ ∈ Λ, ∀ x ∈ S, γ * x ∈ S) → (∀ t ∈ T, ∀ u ∈ U, t * u ∈ S) → T.card * μ U ≤ k * μ (S ∩ D) := by
  first | exact @GlobalTheory.Packing.packing_count | exact GlobalTheory.Packing.packing_count | (intros; apply GlobalTheory.Packing.packing_count <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardLeMulOfUnipotentCoverDiscreteSubgroup

section

@[expose] public section

open scoped TensorProduct NNReal ENNReal Matrix Pointwise
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

theorem card_le_mul_of_unip_cover : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (N M Λ Γ Q : Subgroup G) [Countable Λ] (ν : Measure N) (π : Measure M) (DN : Set N) (DM : Set M) (μ : Measure G) (D V W : Set G), SemiLat N M Λ ν π DN DM → Λ ≤ Γ → Λ ≤ Q → IsClosed (Q : Set G) → (∀ q ∈ Q, ∃ u ∈ N, ∃ x ∈ M, q = u * x) → (∀ K : Set G, IsCompact K → (K ∩ Γ).Finite) → μ.IsHaarMeasure → IsFundamentalDomain Λ D μ → IsCompact V → IsCompact W → ∃ B : ℝ, 0 ≤ B ∧ ∀ (a : G) (Y T : Finset G), (∀ x ∈ M, a * x = x * a) → (∀ u, u ∈ N ↔ a⁻¹ * u * a ∈ N) → (∀ y ∈ Y, y ∈ N) → (∀ u ∈ N, ∃ γ ∈ Λ, γ ∈ N ∧ ∃ y ∈ Y, ∃ w ∈ V, γ * u = y * a * w * a⁻¹) → (∀ t ∈ T, t ∈ Γ) → (∀ t ∈ T, ∀ t' ∈ T, t' * t⁻¹ ∈ Λ → t = t') → (∀ t ∈ T, ∃ q ∈ Q, ∃ w ∈ W, t = q * a * w) → (T.card : ℝ) ≤ B * Y.card := by
  intro G _ _ _ _ _ _ _ _ N M Λ Γ Q _ ν π DN DM μ D V W H hΛΓ hΛQ hQ hQd hdisc hμ hD hV hW
  haveI := H.haarN
  obtain ⟨U, hUc, hU1⟩ := exists_compact_mem_nhds (1 : G)
  have hU0 : μ U ≠ 0 := (lt_of_lt_of_le (isOpen_interior.measure_pos μ ⟨1, mem_interior_iff_mem_nhds.2 hU1⟩) (measure_mono interior_subset)).ne'
  have hUt : μ U ≠ ⊤ := hUc.measure_ne_top
  obtain ⟨k, hk⟩ := GlobalTheory.T.packing_count_inequivalent_discreteSubgroup G Γ Λ μ D U hΛΓ hdisc hμ hD hUc
  obtain ⟨B₀, hB₀t, hB₀⟩ := GlobalTheory.T.measure_translate_shell_le_div_modulus G N M Λ ν π DN DM H μ D hμ hD (W * U) (hW.mul hUc)
  have hνV : ν {u : N | (u : G) ∈ V} ≠ ⊤ :=
    (H.closedN.isClosedEmbedding_subtypeVal.isCompact_preimage hV).measure_ne_top
  have hDN0 : ν DN ≠ 0 := GlobalTheory.ResLine.Inhab.semiLat_ne_zero H
  have hDNt : ν DN ≠ ⊤ := H.finN
  refine ⟨(ν {u : N | (u : G) ∈ V} * k * B₀ / (ν DN * μ U)).toReal, ENNReal.toReal_nonneg, ?_⟩
  intro a Y T haM haN hY hcov hTΓ hTsep hTQ
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.lintegral_conj_normalizer_eq_const_mul_haar G N ν a⁻¹ H.closedN H.haarN (fun u => by rw [inv_inv]; exact haN u)
  let S : Set G := (Q : Set G) * (a • (W * U))
  have hSc : IsClosed S := hQ.mul_right_of_isCompact ((hW.mul hUc).smul a)
  have hSm : MeasurableSet S := hSc.measurableSet
  have hSinv : ∀ γ ∈ Λ, ∀ x ∈ S, γ * x ∈ S := by
    intro γ hγ x hx
    obtain ⟨q, hq, y, hy, rfl⟩ := Set.mem_mul.1 hx
    exact Set.mem_mul.2 ⟨γ * q, Q.mul_mem (hΛQ hγ) hq, y, hy, mul_assoc _ _ _⟩
  have hTS : ∀ t ∈ T, ∀ u ∈ U, t * u ∈ S := by
    intro t ht u hu
    obtain ⟨q, hq, w, hw, rfl⟩ := hTQ t ht
    have hm : a • (w * u) ∈ a • (W * U) := Set.smul_mem_smul_set (Set.mul_mem_mul hw hu)
    refine Set.mem_mul.2 ⟨q, hq, a • (w * u), hm, ?_⟩
    simp only [smul_eq_mul, mul_assoc]
  have hpack := hk T S hTΓ hTsep hSm hSinv hTS
  have hshell : κ * μ (S ∩ D) ≤ B₀ := by
    refine hB₀ a⁻¹ κ (fun m hm => (show Commute a m from haM m hm).inv_left) hκ S hSm fun x hx => ?_
    obtain ⟨q, hq, y, hy, rfl⟩ := Set.mem_mul.1 hx
    obtain ⟨c, hc, rfl⟩ := Set.mem_smul_set.1 hy
    obtain ⟨u, hu, m, hm, rfl⟩ := hQd q hq
    refine ⟨a⁻¹ * u * a, (haN u).1 hu, m, hm, c, hc, ?_⟩
    have e : m * a = a * m := (haM m hm).symm
    simp only [smul_eq_mul, mul_assoc]
    rw [← mul_assoc m a c, e, mul_assoc a m c]
  have hcover := GlobalTheory.T.haar_fundDomain_le_card_mul_of_translateCover G N Λ ν DN a⁻¹ κ V Y H.haarN H.domN hV hκ hY fun u hu => by
    obtain ⟨γ, hγ, hγN, y, hy, w, hw, e⟩ := hcov u hu
    exact ⟨γ, hγ, hγN, y, hy, w, hw, by rw [inv_inv]; exact e⟩
  have key : ν DN * (T.card * μ U) ≤ Y.card * (ν {u : N | (u : G) ∈ V} * k * B₀) := calc
    ν DN * (T.card * μ U) ≤ (Y.card * (κ * ν {u : N | (u : G) ∈ V})) * (T.card * μ U) := by gcongr
    _ = Y.card * ν {u : N | (u : G) ∈ V} * (κ * (T.card * μ U)) := by ring
    _ ≤ Y.card * ν {u : N | (u : G) ∈ V} * (κ * (k * μ (S ∩ D))) := by gcongr
    _ = Y.card * ν {u : N | (u : G) ∈ V} * k * (κ * μ (S ∩ D)) := by ring
    _ ≤ Y.card * ν {u : N | (u : G) ∈ V} * k * B₀ := by gcongr
    _ = Y.card * (ν {u : N | (u : G) ∈ V} * k * B₀) := by ring
  have hc0 : ν DN * μ U ≠ 0 := mul_ne_zero hDN0 hU0
  have hct : ν DN * μ U ≠ ⊤ := ENNReal.mul_ne_top hDNt hUt
  have hX : ν {u : N | (u : G) ∈ V} * k * B₀ ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top hνV (ENNReal.natCast_ne_top k)) hB₀t
  have h1 : (T.card : ℝ≥0∞) ≤ Y.card * (ν {u : N | (u : G) ∈ V} * k * B₀ / (ν DN * μ U)) := by
    rw [← mul_div_assoc, ENNReal.le_div_iff_mul_le (Or.inl hc0) (Or.inl hct)]
    calc (T.card : ℝ≥0∞) * (ν DN * μ U) = ν DN * (T.card * μ U) := by ring
      _ ≤ _ := key
  have hfin : ν {u : N | (u : G) ∈ V} * k * B₀ / (ν DN * μ U) ≠ ⊤ := (ENNReal.div_lt_top hX hc0).ne
  have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hfin) h1
  rw [mul_comm]
  simpa [ENNReal.toReal_mul] using h2

end GlobalTheory.SphEis
end
end
