module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.ReadLimit
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.EigArch
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.ReproOf
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.OrthogonalKeepingHolds
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.EntryLeOfLg
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.CompatFub
import Aesop.Main
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Finsupp.Pointwise
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.GelOfHolds
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.ConvTest
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.Imports
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.WdValAppend
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PInfConv
import Mathlib.Tactic.ENatToNat
import Mathlib.Topology.MetricSpace.Sequences
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Limitb

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.FinHecke

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf finH HeckeM heckeAct)
open scoped Classical

namespace PositivityTheory.Rg.BcB.CG

theorem finH_mul {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} (g h : Hf E a b) :
    finH (g * h) = finH g * finH h := by
  simp [finH, map_mul]

theorem finHecke : FinHecke := by
  intro E _ _ _ a b _ _ ν _ A κ _ _ ψ U hψ hUo hUc hψU

  set K : Set (Hf E a b) := ⋃ x, ⋃ y, tsupport (ψ x y) with hK
  have hKc : IsCompact K := isCompact_iUnion fun x => isCompact_iUnion fun y => (hψ x y).2

  let C : Hf E a b ⧸ U → Set (Hf E a b) := fun q => (fun h => q.out⁻¹ * h) ⁻¹' (U : Set (Hf E a b))
  have hCmem : ∀ q h, h ∈ C q ↔ (QuotientGroup.mk h : Hf E a b ⧸ U) = q := by
    intro q h
    show q.out⁻¹ * h ∈ U ↔ _
    rw [← QuotientGroup.eq]
    simp only [Quotient.out_eq]
    exact eq_comm
  have hCo : ∀ q, IsOpen (C q) := fun q => hUo.preimage (continuous_const.mul continuous_id)
  have hCm : ∀ q, MeasurableSet (C q) := fun q => (hCo q).measurableSet
  have hCf : ∀ q, ν (C q) ≠ ⊤ := by
    intro q
    show ν ((fun h => q.out⁻¹ * h) ⁻¹' (U : Set (Hf E a b))) ≠ ⊤
    rw [measure_preimage_mul]
    exact hUc.measure_lt_top.ne
  obtain ⟨t, ht⟩ := hKc.elim_finite_subcover C hCo (by
    intro h _
    exact Set.mem_iUnion.2 ⟨QuotientGroup.mk h, (hCmem _ h).2 rfl⟩)
  have hin : ∀ h, (∀ x y, ψ x y h ≠ 0 → (QuotientGroup.mk h : Hf E a b ⧸ U) ∈ t) := by
    intro h x y hne
    have hhK : h ∈ K := Set.mem_iUnion.2 ⟨x, Set.mem_iUnion.2 ⟨y, subset_tsupport _ hne⟩⟩
    obtain ⟨q, hq⟩ := Set.mem_iUnion.1 (ht hhK)
    obtain ⟨hqt, hq⟩ := Set.mem_iUnion.1 hq
    rwa [(hCmem q h).1 hq]
  refine ⟨fun i j => if i.1 = j.1 then ∑ q ∈ t, Finsupp.single q.out ((ν (C q)).toReal * ψ i.2 j.2 q.out) else 0,
    ?_, ?_, ?_⟩
  · intro i j hij
    simp [hij]
  · intro p q x y
    simp
  · intro f hf
    funext i X
    simp only [convF, heckeAct]
    rw [Fintype.sum_prod_type]
    simp only
    rw [Finset.sum_eq_single i.1 (fun p _ hp => by
      refine Finset.sum_eq_zero fun z _ => ?_
      rw [if_neg (Ne.symm hp)]
      simp) (by simp)]
    refine Finset.sum_congr rfl fun z _ => ?_
    simp only [if_true]
    rw [← Finsupp.sum_finsetSum_index (fun _ => by simp) (fun _ _ _ => by ring)]
    set Φ : Hf E a b → ℂ := fun h => ψ i.2 z h * f (i.1, z) (X * finH h) with hΦ
    have hΦU : ∀ h, ∀ u ∈ U, Φ (h * u) = Φ h := by
      intro h u hu
      simp only [hΦ]
      rw [finH_mul, ← mul_assoc, hf _ u hu, hψU _ _ u hu h]
    have hΦout : ∀ h, Φ (QuotientGroup.mk h : Hf E a b ⧸ U).out = Φ h := by
      intro h
      have h1 : ((QuotientGroup.mk h : Hf E a b ⧸ U).out)⁻¹ * h ∈ U := (hCmem _ h).2 rfl
      calc Φ (QuotientGroup.mk h : Hf E a b ⧸ U).out
          = Φ ((QuotientGroup.mk h : Hf E a b ⧸ U).out * ((QuotientGroup.mk h : Hf E a b ⧸ U).out⁻¹ * h)) :=
            (hΦU _ _ h1).symm
        _ = Φ h := by rw [mul_inv_cancel_left]
    have hpt : Φ = fun h => ∑ q ∈ t, (C q).indicator (fun _ => Φ q.out) h := by
      funext h
      rw [Finset.sum_eq_single (QuotientGroup.mk h : Hf E a b ⧸ U)]
      · rw [Set.indicator_of_mem ((hCmem _ h).2 rfl), hΦout]
      · intro q _ hq
        rw [Set.indicator_of_notMem]
        intro hc
        exact hq ((hCmem q h).1 hc).symm
      · intro hmem
        rw [Set.indicator_of_mem ((hCmem _ h).2 rfl), hΦout]
        by_contra hne
        apply hmem
        refine hin h i.2 z ?_
        intro h0
        apply hne
        simp only [hΦ, h0, zero_mul]
    rw [hpt, integral_finsetSum]
    · refine Finset.sum_congr rfl fun q _ => ?_
      rw [integral_indicator_const _ (hCm q), Finsupp.sum_single_index (by simp)]
      simp only [hΦ, Complex.real_smul, Measure.real]
      ring
    · intro q _
      exact (integrable_indicator_iff (hCm q)).2 (integrableOn_const (hCf q))

end PositivityTheory.Rg.BcB.CG

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.GelfandValueContinuity.InfLim

section

@[expose] public section

noncomputable section

open Polynomial Finset Filter Topology
open scoped Classical
open PositivityTheory.RgBcC.Bridge PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.CG.InfiniteConvergence

namespace PositivityTheory.Rg.BcB.F.Rd.B

theorem gelfVal_cont (n l : ℕ) : Continuous fun χ : Fin n → ℂ => GlobalTheory.Dec.gelfVal χ l := by
  unfold GlobalTheory.Dec.gelfVal
  have hA : Continuous fun χ : Fin n → ℂ => Formalism.REAL.Amat (fun c => χ c + ((n : ℂ) - 1) / 2) := by
    refine continuous_pi fun a => continuous_pi fun b => ?_
    simp only [Formalism.REAL.Amat, Matrix.of_apply]
    split_ifs
    · exact (continuous_apply a).add continuous_const
    · exact continuous_const
    · exact continuous_const
  exact continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ => (hA.pow l).matrix_elem a b

theorem coef_conv (m : ℕ) (x : ℕ → Fin (m + 1) → ℂ) (t : ℕ → ℂ)
    (ht : ∀ l, Tendsto (fun k => GlobalTheory.Dec.gelfVal (x k) l) atTop (𝓝 (t l))) :
    ∀ i, ∃ c, Tendsto (fun k => (cq m (x k)).coeff i) atTop (𝓝 c) := by
  have hind : ∀ j i, m + 1 - j ≤ i → ∃ c, Tendsto (fun k => (cq m (x k)).coeff i) atTop (𝓝 c) := by
    intro j
    induction j with
    | zero =>
      intro i hi
      rcases eq_or_lt_of_le (show m + 1 ≤ i by omega) with h | h
      · subst h
        have e : ∀ χ, (cq m χ).coeff (m + 1) = 1 := fun χ => by
          have := (cq_monic m χ).coeff_natDegree
          rwa [cq_natDegree] at this
        simp only [e]
        exact ⟨1, tendsto_const_nhds⟩
      · have e : ∀ χ, (cq m χ).coeff i = 0 := fun χ =>
          coeff_eq_zero_of_natDegree_lt (by rw [cq_natDegree]; exact h)
        simp only [e]
        exact ⟨0, tendsto_const_nhds⟩
    | succ j ih =>
      intro i hi
      by_cases hij : m + 1 - j ≤ i
      · exact ih i hij
      · have hr : i ≤ m := by omega
        have hij' : i + j = m := by omega
        have hne : ((j : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
        have hform : ∀ χ : Fin (m + 1) → ℂ, (cq m χ).coeff i =
            (defect (GlobalTheory.Dec.gelfVal χ) m (m + 1) (Hi i (m + 1) (cq m χ))).coeff (i + (m + 1)) / ((j : ℂ) + 1) := by
          intro χ
          have hk := key m χ i hr
          have hc : (i : ℂ) = (m : ℂ) - j := by rw [← hij']; push_cast; ring
          rw [eq_div_iff hne]
          linear_combination (-1 : ℂ) * hk + (cq m χ).coeff i * hc
        let c : ℕ → ℂ := fun l => if h : ∃ c, Tendsto (fun k => (cq m (x k)).coeff l) atTop (𝓝 c) then h.choose else 0
        have hc : ∀ l ∈ Ioc i (m + 1), Tendsto (fun k => (cq m (x k)).coeff l) atTop (𝓝 (c l)) := fun l hl => by
          have h := ih l (by simp only [mem_Ioc] at hl; omega)
          simp only [c, dif_pos h]
          exact h.choose_spec
        let Q₀ : ℂ[X] := ∑ l ∈ Ioc i (m + 1), Polynomial.C (c l) * X ^ l
        have h1 : CoefTo (fun k => Hi i (m + 1) (cq m (x k))) Q₀ := by
          simp only [Hi, Q₀]
          exact CoefTo.sum _ fun l hl => CoefTo.mul (CoefTo.C (hc l hl)) (CoefTo.const _)
        have hQc : Q₀.comp (X + 1) = ∑ l ∈ Ioc i (m + 1), Polynomial.C (c l) * (X + 1) ^ l := by
          simp only [Q₀]

          rw [← coe_compRingHom_apply, map_sum]
          simp only [coe_compRingHom_apply, mul_comp, C_comp, X_pow_comp]
        have h2 : CoefTo (fun k => (Hi i (m + 1) (cq m (x k))).comp (X + 1)) (Q₀.comp (X + 1)) := by
          simp only [Hi_comp, hQc]
          exact CoefTo.sum _ fun l hl => CoefTo.mul (CoefTo.C (hc l hl)) (CoefTo.const _)
        have h3 := CoefTo.defect (t := fun k => GlobalTheory.Dec.gelfVal (x k)) ht m (m + 1) h1 h2 (i + (m + 1))
        exact ⟨_, (h3.div_const ((j : ℂ) + 1)).congr fun k => (hform (x k)).symm⟩
  exact fun i => hind (m + 1) i (by omega)

theorem infLim : InfLim := by
  intro n x t ht
  rcases n with _ | m
  · have h0 : ∀ (χ : Fin 0 → ℂ) (l : ℕ), GlobalTheory.Dec.gelfVal χ l = 0 := fun χ l => by simp [GlobalTheory.Dec.gelfVal]
    refine ⟨Fin.elim0, fun l => ?_⟩
    have h := ht l
    simp only [h0] at h
    rw [h0]
    exact tendsto_nhds_unique tendsto_const_nhds h
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℂ, ∀ i, Tendsto (fun k => (cq m (x k)).coeff i) atTop (𝓝 (c i)) := by
    choose c hc using coef_conv m x t ht
    exact ⟨c, hc⟩
  have hbd : ∀ i, ∃ B, ∀ k, ‖(cq m (x k)).coeff i‖ ≤ B := fun i => by
    obtain ⟨B, hB⟩ := (Metric.isBounded_range_of_tendsto _ (hc i)).exists_norm_le
    exact ⟨B, fun k => hB _ ⟨k, rfl⟩⟩
  choose Cb hCb using hbd
  set B := max 1 (∑ i ∈ range (m + 1), Cb i) + ‖(m : ℂ) / 2‖ with hBdef
  have hB0 : 0 ≤ B := by
    have := le_max_left (1 : ℝ) (∑ i ∈ range (m + 1), Cb i)
    have := norm_nonneg ((m : ℂ) / 2)
    linarith
  have hxb : ∀ k s, ‖x k s‖ ≤ B := by
    intro k s
    have h1 := norm_root_le _ (cq_monic m (x k)) _ (cq_eval m (x k) s)
    rw [cq_natDegree] at h1
    have h2 : ∑ i ∈ range (m + 1), ‖(cq m (x k)).coeff i‖ ≤ ∑ i ∈ range (m + 1), Cb i :=
      sum_le_sum fun i _ => hCb i k
    have h3 : ‖x k s‖ ≤ ‖(m : ℂ) / 2‖ + ‖(m : ℂ) / 2 - x k s‖ := by
      have := norm_sub_le ((m : ℂ) / 2) ((m : ℂ) / 2 - x k s)
      rwa [sub_sub_cancel] at this
    have h4 := max_le_max (le_refl (1 : ℝ)) h2
    linarith
  have hmem : ∀ k, x k ∈ Metric.closedBall (0 : Fin (m + 1) → ℂ) B := fun k =>
    mem_closedBall_zero_iff.2 ((pi_norm_le_iff_of_nonneg hB0).2 fun s => hxb _ s)
  obtain ⟨z, -, ψ, hψm, hψ⟩ := tendsto_subseq_of_bounded Metric.isBounded_closedBall hmem
  refine ⟨z, fun l => ?_⟩
  have h1 : Tendsto (fun k => GlobalTheory.Dec.gelfVal (x (ψ k)) l) atTop (𝓝 (GlobalTheory.Dec.gelfVal z l)) :=
    ((gelfVal_cont (m + 1) l).tendsto z).comp hψ
  have h2 : Tendsto (fun k => GlobalTheory.Dec.gelfVal (x (ψ k)) l) atTop (𝓝 (t l)) :=
    (ht l).comp hψm.tendsto_atTop
  exact tendsto_nhds_unique h1 h2

end PositivityTheory.Rg.BcB.F.Rd.B

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.GelfandValueContinuity.ReadLimitOfEfinal

section

@[expose] public section

namespace PositivityTheory.Rg.BcB.F.Rd.P

open PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.F

theorem readLimit_of_efinal (ef : PositivityTheory.Rg.BcB.SpectralAccumulation.EFinal) : ReadLimit :=
  B.readLimit_of PositivityTheory.Rg.BcB.E2.proper_base_change pack_holds ef actVal_holds finHecke valCont_holds infConv B.infLim reproEx_holds tensMul
    BlockFiniteConvolution.blkOp₀ BlockFiniteConvolution.blkWord₀ blkSum adjWords

end PositivityTheory.Rg.BcB.F.Rd.P
end
end
