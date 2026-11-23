module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.VecClose
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.VecClose
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.UrysohnsLemma
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CellSumOfCntBasic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CntBasicOfKerBasic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoeFnSumAe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ColOp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ColSqOfKerBasic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompKey
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousAtOfSqBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CvAdjEqAvg
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqZeroOfLeSmall
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteOfCompact
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InnerEqIntegralConjMul
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableReflect
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelL2RowsColumns
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KerMulOfKerBasicOfCvTest
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelL2RowsColumns
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralEnormRpowTwoNeTop
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralWeightedSqLe
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RowIntOfKerBasic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchurOpOfSchurL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VecCloseOfKerBasicColSq
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VecLimOf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VecNormOfVecClose

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BumpEx

section

section

open MeasureTheory PositivityTheory.Rg.BcB.E1

namespace GlobalTheory.CompanionTheory.Bump

theorem bumpEx : BumpEx := by
  intro X W hW
  obtain ⟨N, hNn, hNW, hNc⟩ := local_compact_nhds hW
  have h1 : (1 : X.G) ∈ interior N := mem_interior_iff_mem_nhds.mpr hNn
  obtain ⟨b, hb1, hb0, hbc, hbI⟩ := exists_continuous_one_zero_of_isCompact
    (isCompact_singleton (x := (1 : X.G))) isOpen_interior.isClosed_compl
    (Set.disjoint_singleton_left.mpr (fun h => h h1))
  have hbnn : ∀ z, 0 ≤ b z := fun z => (hbI z).1
  have hb11 : b 1 = 1 := hb1 (Set.mem_singleton _)
  have hsupp : Function.support b ⊆ N := by
    intro x hx
    by_contra hxN
    exact hx (hb0 (fun hi => hxN (interior_subset hi)))
  have hts : tsupport b ⊆ N := closure_minimal hsupp hNc.isClosed
  have hcc : Continuous fun z : X.G => b z⁻¹ := b.continuous.comp continuous_inv
  have hcs : HasCompactSupport fun z : X.G => b z⁻¹ :=
    hbc.comp_homeomorph (Homeomorph.inv X.G)
  have hI : 0 < ∫ z, b z⁻¹ ∂X.μ :=
    hcc.integral_pos_of_hasCompactSupport_nonneg_nonzero hcs (fun z => hbnn _)
      (x := 1) (by simp [hb11])
  set I := ∫ z, b z⁻¹ ∂X.μ with hIdef
  have hnorm : ∀ z, ‖((b z / I : ℝ) : ℂ)‖ = b z / I := fun z => by
    rw [Complex.norm_real, Real.norm_of_nonneg (div_nonneg (hbnn z) hI.le)]
  have hsub : Function.support (fun z => ((b z / I : ℝ) : ℂ)) ⊆ Function.support b := by
    intro x hx h0
    apply hx
    simp [h0]
  refine ⟨fun z => ((b z / I : ℝ) : ℂ), ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · exact Complex.continuous_ofReal.comp (b.continuous.div_const I)
  · exact hbc.mono hsub
  · intro z
    simp only [hnorm]
  · simp only [hnorm]
    rw [integral_div, ← hIdef, div_self hI.ne']
  · exact (closure_mono hsub).trans (hts.trans hNW)

end GlobalTheory.CompanionTheory.Bump
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KerClose

section

section

open PositivityTheory.Rg.BcB.E1

namespace GlobalTheory.CompanionTheory.KernelClose

theorem kerClose : KerClose := by
  intro X Ω x y hΩ
  have hC : IsCompact ((fun o : X.G => x * o * y⁻¹) '' Ω) :=
    hΩ.image (by fun_prop)
  have hfin := X.proper _ hC
  have hsupp : ∀ φ : X.G → ℂ, Function.support φ ⊆ Ω →
      (Function.support fun γ : X.Γ => φ (x⁻¹ * (γ : X.G) * y)) ⊆ (hfin.toFinset : Set X.Γ) := by
    intro φ hφ γ hγ
    have hmem : x⁻¹ * (γ : X.G) * y ∈ Ω := hφ hγ
    simp only [Set.Finite.coe_toFinset, Set.mem_setOf_eq]
    exact ⟨_, hmem, by group⟩
  have hker : ∀ φ : X.G → ℂ, Function.support φ ⊆ Ω →
      ker X.Γ φ x y = ∑ γ ∈ hfin.toFinset, φ (x⁻¹ * (γ : X.G) * y) := fun φ hφ =>
    finsum_eq_sum_of_support_subset _ (hsupp φ hφ)
  refine ⟨(hfin.toFinset.card : ℝ), Nat.cast_nonneg _, ?_⟩
  intro φ φ' ε hφ hφ' hε
  rw [hker φ hφ, hker φ' hφ', ← Finset.sum_sub_distrib]
  calc ‖∑ γ ∈ hfin.toFinset, (φ (x⁻¹ * (γ : X.G) * y) - φ' (x⁻¹ * (γ : X.G) * y))‖
      ≤ ∑ γ ∈ hfin.toFinset, ‖φ (x⁻¹ * (γ : X.G) * y) - φ' (x⁻¹ * (γ : X.G) * y)‖ :=
        norm_sum_le _ _
    _ ≤ hfin.toFinset.card • ε := Finset.sum_le_card_nsmul _ _ _ fun γ _ => hε _
    _ = (hfin.toFinset.card : ℝ) * ε := nsmul_eq_mul _ _

end GlobalTheory.CompanionTheory.KernelClose
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KerLinOfKerBasic

section

@[expose] public section

open PositivityTheory.Rg.BcB.E1

namespace GlobalTheory.CompanionTheory.KerLinear

theorem kerLin_of_kerBasic : KerBasic → KerLin := by
  intro hb X ι _ φ c hφ
  constructor
  · refine ⟨continuous_finsetSum _ fun i _ => (hφ i).1.mul continuous_const, ?_⟩
    have key : ∀ s : Finset ι, HasCompactSupport (fun y => ∑ i ∈ s, φ i y * c i) := by
      intro s
      induction s using Finset.cons_induction with
      | empty => exact (HasCompactSupport.zero : HasCompactSupport (0 : X.G → ℂ))
      | cons a s ha ih =>
        have h1 : HasCompactSupport (fun y => φ a y * c a) :=
          (hφ a).2.mul_right
        have h2 := h1.add ih
        have h3 : (fun y => ∑ i ∈ Finset.cons a s ha, φ i y * c i) =
            (fun y => φ a y * c a) + fun y => ∑ i ∈ s, φ i y * c i := by
          funext y
          simp [Finset.sum_cons]
        rw [h3]
        exact h2
    exact key Finset.univ
  · intro x y
    have hfin : ∀ i, (Function.support fun γ : X.Γ => φ i (x⁻¹ * (γ : X.G) * y)).Finite :=
      fun i => (hb X (φ i) (hφ i)).1 x y
    have hfin' : ∀ i ∈ (Finset.univ : Finset ι),
        (Function.support fun γ : X.Γ => φ i (x⁻¹ * (γ : X.G) * y) * c i).Finite := fun i _ =>
      (hfin i).subset (Function.support_mul_subset_left _ _)
    unfold ker
    rw [finsum_sum_comm _ _ hfin']
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [finsum_mul]

end GlobalTheory.CompanionTheory.KerLinear
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelRowsColumnsSquareIntegrable

section

section

open MeasureTheory
open scoped ENNReal Pointwise
open PositivityTheory.Rg.BcB.E1

namespace GlobalTheory.CompanionTheory.KerSquare

theorem memLp_column (hK : KerBasic) (hC : CntBasic) (hS : ColSq) (X : Ctx) (φ : X.G → ℂ)
    (hφ : Tst φ) (y : X.G) : MemLp (fun x => ker X.Γ φ x y) 2 X.ν := by
  have hcont : Continuous fun x => ker X.Γ φ x y :=
    (hK X φ hφ).2.1.comp (continuous_id.prodMk continuous_const)
  obtain ⟨B, hB⟩ := hφ.1.bounded_above_of_compact_support hφ.2
  have hΩ : IsCompact (tsupport φ) := hφ.2
  have hbound := hS X φ B (tsupport φ) hφ hB hΩ (subset_tsupport φ) y
  have hμ : X.μ (tsupport φ)⁻¹ ≠ ⊤ := hΩ.inv.measure_lt_top.ne
  have hcnt : cnt X.Γ ((tsupport φ)⁻¹ * tsupport φ) y ≠ ⊤ :=
    (hC X).1 _ (hΩ.inv.mul hΩ) y
  have hfin : ENNReal.ofReal B ^ 2 * X.μ (tsupport φ)⁻¹ *
      cnt X.Γ ((tsupport φ)⁻¹ * tsupport φ) y < ⊤ :=
    ENNReal.mul_lt_top
      (ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top) hμ.lt_top) hcnt.lt_top
  rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_eNorm_lt_top
    (by norm_num) (by norm_num) hcont.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_ofNat]
  exact hbound.trans_lt hfin

theorem memLp_row (hK : KerBasic) (hC : CntBasic) (hS : ColSq) (X : Ctx) (φ : X.G → ℂ)
    (hφ : Tst φ) (x : X.G) : MemLp (fun y => ker X.Γ φ x y) 2 X.ν := by
  obtain ⟨-, hcont, -, hadj, hconj, -⟩ := hK X φ hφ
  have hc : Continuous fun y => ker X.Γ φ x y :=
    hcont.comp (continuous_const.prodMk continuous_id)
  refine (memLp_column hK hC hS X (adj φ) hadj x).of_le hc.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_)
  rw [hconj y x, RCLike.norm_conj]

theorem kernel_rows_columns_square_integrable : KerBasic → CntBasic → ColSq → KernelL2RowsColumns := fun hK hC hS X φ hφ =>
  ⟨memLp_column hK hC hS X φ hφ, memLp_row hK hC hS X φ hφ⟩

end GlobalTheory.CompanionTheory.KerSquare
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwoUnif

section

section

open PositivityTheory.Rg.BcB.E1
open scoped Pointwise Topology

namespace GlobalTheory.CompanionTheory.TwoSidedUnif

theorem twoUnif : TwoUnif := by
  intro X φ ε hφ hε
  obtain ⟨hc, hs⟩ := hφ
  obtain ⟨N, hNc, hN1⟩ := exists_compact_mem_nhds (1 : X.G)
  have hS : IsCompact (tsupport φ) := hs
  have hK : IsCompact (N⁻¹ * tsupport φ * N⁻¹) := (hNc.inv.mul hS).mul hNc.inv
  have h1N : (1 : X.G) ∈ N := mem_of_mem_nhds hN1
  have hf : Continuous fun q : (X.G × X.G) × X.G => ‖φ (q.1.1 * q.2 * q.1.2) - φ q.2‖ := by
    have : Continuous fun q : (X.G × X.G) × X.G => q.1.1 * q.2 * q.1.2 := by fun_prop
    exact ((hc.comp this).sub (hc.comp continuous_snd)).norm
  have hev : ∀ᶠ p : X.G × X.G in 𝓝 ((1 : X.G), (1 : X.G)), ∀ y ∈ N⁻¹ * tsupport φ * N⁻¹,
      ‖φ (p.1 * y * p.2) - φ y‖ < ε := by
    refine hK.eventually_forall_of_forall_eventually fun y _ => ?_
    have h0 : ‖φ ((((1 : X.G), (1 : X.G)), y).1.1 * (((1 : X.G), (1 : X.G)), y).2 *
        (((1 : X.G), (1 : X.G)), y).1.2) - φ (((1 : X.G), (1 : X.G)), y).2‖ < ε := by
      simpa using hε
    exact hf.continuousAt.eventually (Iio_mem_nhds h0)
  obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.1 hev
  refine ⟨U ∩ V ∩ N, Filter.inter_mem (Filter.inter_mem hU hV) hN1, ?_⟩
  rintro z ⟨⟨hzU, -⟩, hzN⟩ w ⟨⟨-, hwV⟩, hwN⟩ y
  by_cases hy : y ∈ N⁻¹ * tsupport φ * N⁻¹
  · exact (hUV (Set.mk_mem_prod hzU hwV) y hy).le
  · have hy0 : φ y = 0 := by
      refine image_eq_zero_of_notMem_tsupport fun hys => hy ?_
      refine Set.mem_mul.2 ⟨1 * y, Set.mem_mul.2 ⟨1, ?_, y, hys, rfl⟩, 1, ?_, by simp⟩
      · simpa using h1N
      · simpa using h1N
    have hzy0 : φ (z * y * w) = 0 := by
      refine image_eq_zero_of_notMem_tsupport fun hys => hy ?_
      refine Set.mem_mul.2 ⟨z⁻¹ * (z * y * w), Set.mem_mul.2 ⟨z⁻¹, ?_, z * y * w, hys, rfl⟩, w⁻¹, ?_, by group⟩
      · exact Set.inv_mem_inv.2 hzN
      · exact Set.inv_mem_inv.2 hwN
    simpa [hy0, hzy0] using hε.le

end GlobalTheory.CompanionTheory.TwoSidedUnif
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VecInnerOfKerBasic

section

section

noncomputable section

open MeasureTheory PositivityTheory.Rg.BcB.E1

namespace GlobalTheory.CompanionTheory.E1

theorem vecInner_of_kerBasic : KerBasic → VecInner := by
  intro hK X ι _ Φ y j k u hΦ
  constructor
  · intro hk
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hk l] with z hz
    rw [hz, RCLike.inner_apply, mul_comm]
  · intro hk
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hk l] with z hz
    have h := (hK X (Φ j l) (hΦ j l)).2.2.2.2.1 z y
    rw [hz, h, RCLike.inner_apply, Complex.conj_conj, mul_comm]

end GlobalTheory.CompanionTheory.E1

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelRowsColumnsSquareIntegrable

section

@[expose] public section

namespace PositivityTheory.Rg.BcB.E1

theorem kerBasic : KerBasic := GlobalTheory.CompanionTheory.KernelBasic.kerBasic
theorem kerLin : KerLin := GlobalTheory.CompanionTheory.KerLinear.kerLin_of_kerBasic kerBasic
theorem cntBasic : CntBasic := GlobalTheory.CompanionTheory.KernelCount.cntBasic_of_kerBasic kerBasic
theorem rowInt : RowInt := GlobalTheory.CompanionTheory.KernelRows.rowInt_of_kerBasic kerBasic
theorem colSq : ColSq := GlobalTheory.CompanionTheory.KernelColumn.colSq_of_kerBasic kerBasic
theorem kernel_rows_columns_square_integrable : KernelL2RowsColumns := GlobalTheory.CompanionTheory.KerSquare.kernel_rows_columns_square_integrable kerBasic cntBasic colSq
theorem schurL : SchurL := GlobalTheory.CompanionTheory.Schur.schurL
theorem schurInt : SchurInt := GlobalTheory.CompanionTheory.SchurKernel.schurInt_of_schurL schurL
theorem schurOp : SchurOp := GlobalTheory.CompanionTheory.Schur.schurOp_of_schurL schurL
theorem cvTest : CvTest := GlobalTheory.CompanionTheory.ConvTest.cvTest
theorem kerMul : KerMul := GlobalTheory.CompanionTheory.KernelComposition.kerMul_of_kerBasic_of_cvTest kerBasic cvTest
theorem opExA : OpExA := GlobalTheory.CompanionTheory.OpEx.opExA kerBasic rowInt schurOp
theorem opAdj : OpAdj := GlobalTheory.CompanionTheory.KerAdj.opAdj_of kerBasic rowInt schurInt opExA
theorem opMul : OpMul := GlobalTheory.CompanionTheory.KernelOperators.opMul kerBasic kerLin rowInt kernel_rows_columns_square_integrable schurInt cvTest kerMul
theorem colOp : ColOp := GlobalTheory.CompanionTheory.KernelColumns.colOp kerBasic cvTest kernel_rows_columns_square_integrable kerMul
theorem cellSum : CellSum := GlobalTheory.CompanionTheory.CellSumProof.cellSum_of_cntBasic cntBasic
theorem twoUnif : TwoUnif := GlobalTheory.CompanionTheory.TwoSidedUnif.twoUnif
theorem bumpEx : BumpEx := GlobalTheory.CompanionTheory.Bump.bumpEx
theorem approxU : ApproxU := GlobalTheory.CompanionTheory.ApproxUnit.approxU cvTest twoUnif
theorem kerClose : KerClose := GlobalTheory.CompanionTheory.KernelClose.kerClose
theorem vecClose : VecClose := GlobalTheory.CompanionTheory.KernelColumns.vecClose_of_kerBasic_colSq kerBasic colSq
theorem vecNorm : VecNorm := GlobalTheory.CompanionTheory.KernelColumns.vecNorm_of_vecClose vecClose
theorem vecEx : VecEx := GlobalTheory.CompanionTheory.KerVec.vecEx cntBasic kernel_rows_columns_square_integrable twoUnif vecClose
theorem vecInner : VecInner := GlobalTheory.CompanionTheory.E1.vecInner_of_kerBasic kerBasic
theorem vecLim : VecLim := GlobalTheory.CompanionTheory.KernelColumns.vecLim_of cntBasic cvTest colOp approxU vecClose
theorem ptEq : PtEq := GlobalTheory.CompanionTheory.KerPoint.ptEq_of kerBasic cvTest opAdj colOp bumpEx approxU kerClose vecLim

end PositivityTheory.Rg.BcB.E1
end
end
