module

public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsNumberFieldBoxCount
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsCovolumeRelIndex
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsEmbeddingSumPlaces
import Std.Tactic.BVDecide.Normalize.Prop
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsLatticeCountVolume
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Tactic.Linter.Style
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsLatticeImageZLattice
import Mathlib.Algebra.Module.Torsion.Prod
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.TotallySplit
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsMixedBoxCount
import Mathlib.Topology.Separation.CompletelyRegular
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PNumberFieldBoxCount

-- Source module: GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCovolumeRelIndex

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MeasureTheory Module ZLattice


open scoped Classical in
theorem CovolumeRelIndex.proof : CovolumeRelIndex.Statement := by
  intro E _ _ _ _ _ μ _ L₁ L₂ _ _ _ _ h
  let f : (Fin (finrank ℝ E) → ℝ) ≃L[ℝ] E := (Module.finBasis ℝ E).equivFunL.symm
  let ν : Measure (Fin (finrank ℝ E) → ℝ) := μ.map f.symm
  have : ν.IsAddHaarMeasure := f.symm.isAddHaarMeasure_map μ
  have hf : MeasurePreserving f ν μ := by
    refine ⟨f.continuous.measurable, ?_⟩
    simp only [ν]
    rw [Measure.map_map f.continuous.measurable f.symm.continuous.measurable]
    have : (⇑f ∘ ⇑f.symm) = id := by ext x; simp
    rw [this, Measure.map_id]
  obtain ⟨c, hν⟩ : ∃ c : NNReal, ν = c • volume := ⟨_, Measure.isAddLeftInvariant_eq_smul ν volume⟩
  have scale : ∀ (L : Submodule ℤ (Fin (finrank ℝ E) → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L],
      covolume L ν = (c : ℝ) * covolume L volume := by
    intro L _ _
    rw [covolume_eq_measure_fundamentalDomain L ν
        (ZLattice.isAddFundamentalDomain (Free.chooseBasis ℤ L) ν),
      covolume_eq_measure_fundamentalDomain L volume
        (ZLattice.isAddFundamentalDomain (Free.chooseBasis ℤ L) volume)]
    conv_lhs => rw [hν]
    exact measureReal_nnreal_smul_apply c
  have hidx : ((ZLattice.comap ℝ L₁ f.toLinearMap).toAddSubgroup.relIndex
      (ZLattice.comap ℝ L₂ f.toLinearMap).toAddSubgroup : ℝ) =
      (L₁.toAddSubgroup.relIndex L₂.toAddSubgroup : ℝ) := by
    rw [ZLattice.comap_toAddSubgroup, ZLattice.comap_toAddSubgroup, Nat.cast_inj,
      LinearEquiv.toAddMonoidHom_commutes, AddSubgroup.comap_equiv_eq_map_symm',
      AddSubgroup.comap_equiv_eq_map_symm',
      AddSubgroup.relIndex_map_map_of_injective _ _ f.symm.injective]
  have key := covolume_div_covolume_eq_relIndex (ZLattice.comap ℝ L₁ f.toLinearMap)
    (ZLattice.comap ℝ L₂ f.toLinearMap) (fun _ h' ↦ h h')
  have hne := covolume_ne_zero (ZLattice.comap ℝ L₂ f.toLinearMap) volume
  rw [← covolume_comap L₁ μ ν hf, ← covolume_comap L₂ μ ν hf, scale, scale, ← hidx, ← key]
  field_simp

end GroundTheory.Heights₂.Heights.Targets
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PEmbeddingSumPlaces

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open NumberField NumberField.InfinitePlace


open scoped Classical in
theorem EmbeddingSumPlaces.proof : EmbeddingSumPlaces.Statement := by
  intro F _ _ g hg
  rw [← Finset.univ.sum_fiberwise (fun σ => InfinitePlace.mk σ)]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  have h : ∀ σ ∈ ({σ | InfinitePlace.mk σ = w} : Finset (F →+* ℂ)), g σ = g w.embedding := by
    intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    subst hσ
    rcases embedding_mk_eq σ with h | h
    · rw [h]
    · rw [h, hg]
  rw [Finset.sum_congr rfl h, Finset.sum_const, nsmul_eq_mul]
  congr 1
  exact_mod_cast card_filter_mk_eq w

end GroundTheory.Heights₂.Heights.Targets
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PLatticeCountVolume

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace LatticeCountVolume

theorem measure_le_encard_mul {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [μ.IsAddHaarMeasure] (La : Submodule ℤ E) [DiscreteTopology La] [IsZLattice ℝ La]
    (S T : Set E) (hS : MeasurableSet S) (hST : ∀ x ∈ S, ∀ y ∈ S, x - y ∈ T) {F : Set E}
    (fund : IsAddFundamentalDomain La F μ) :
    μ S ≤ (({x : E | x ∈ La ∧ x ∈ T}.encard : ℕ∞) : ℝ≥0∞) * μ F := by
  have : MeasurableVAdd La E := (inferInstance : MeasurableVAdd La.toAddSubgroup E)
  have : VAddInvariantMeasure La E μ :=
    (inferInstance : VAddInvariantMeasure La.toAddSubgroup E μ)
  have : Countable La := inferInstance
  set A := {x : E | x ∈ La ∧ x ∈ T} with hAdef
  have key : ∀ y : E, ∑' g : La, S.indicator (1 : E → ℝ≥0∞) (g +ᵥ y) ≤
      ((A.encard : ℕ∞) : ℝ≥0∞) := by
    intro y
    set U : Set La := {g | (g : E) + y ∈ S} with hUdef
    have h1 : ∑' g : La, S.indicator (1 : E → ℝ≥0∞) (g +ᵥ y) =
        ∑' g : La, U.indicator (1 : La → ℝ≥0∞) g := by
      congr 1
    rw [h1, ← tsum_subtype]
    simp only [Pi.one_apply]
    rw [ENNReal.tsum_set_one]
    refine ENat.toENNReal_le.mpr ?_
    rcases U.eq_empty_or_nonempty with hU | ⟨g₀, hg₀⟩
    · simp [hU]
    refine Set.encard_le_encard_of_injOn (f := fun g : La => (g : E) - g₀) ?_ ?_
    · intro g hg
      refine ⟨La.sub_mem g.2 g₀.2, ?_⟩
      have hsub : (g : E) - g₀ = ((g : E) + y) - ((g₀ : E) + y) := by abel
      show (g : E) - g₀ ∈ T
      rw [hsub]
      exact hST _ hg _ hg₀
    · intro g _ g' _ h
      exact Subtype.ext (sub_left_injective h)
  calc μ S = ∫⁻ z, S.indicator 1 z ∂μ := (lintegral_indicator_one hS).symm
    _ = ∑' g : La, ∫⁻ z in F, S.indicator 1 (g +ᵥ z) ∂μ := fund.lintegral_eq_tsum'' _
    _ = ∫⁻ z in F, ∑' g : La, S.indicator 1 (g +ᵥ z) ∂μ :=
        (lintegral_tsum fun g => ((measurable_one.indicator hS).comp
          (measurable_const_vadd g)).aemeasurable).symm
    _ ≤ ∫⁻ _ in F, ((A.encard : ℕ∞) : ℝ≥0∞) ∂μ := lintegral_mono fun z => key z
    _ = ((A.encard : ℕ∞) : ℝ≥0∞) * μ F := setLIntegral_const _ _


open scoped Classical in
theorem proof : LatticeCountVolume.Statement := by
  intro E _ _ _ _ _ μ _ La _ _ S T hS hST
  set b := Module.Free.chooseBasis ℤ La
  have fund := ZLattice.isAddFundamentalDomain b μ
  have hcov := ZLattice.covolume_eq_measure_fundamentalDomain La μ fund
  have hFtop : μ (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ)) ≠ ⊤ :=
    (ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne
  rw [hcov, measureReal_def, ENNReal.ofReal_toReal hFtop]
  exact measure_le_encard_mul μ La S T hS hST fund

end LatticeCountVolume

end

end GroundTheory.Heights₂.Heights.Targets
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PLatticeImageZLattice

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open NumberField NumberField.mixedEmbedding

theorem LatticeImageZLattice.exists_int_mul_integral {F : Type} [Field F] [NumberField F]
    (L : AddSubgroup F) (hfg : L.FG) : ∃ N : ℤ, N ≠ 0 ∧ ∀ x ∈ L, IsIntegral ℤ (N • x) := by
  obtain ⟨S, hS⟩ := hfg
  have halg : ∀ s : F, ∃ y : ℤ, y ≠ 0 ∧ IsIntegral ℤ (y • s) := fun s =>
    ((IsFractionRing.isAlgebraic_iff ℤ ℚ F).mpr (Algebra.IsAlgebraic.isAlgebraic s)).exists_integral_multiple
  choose y hy0 hyint using halg
  refine ⟨∏ s ∈ S, y s, Finset.prod_ne_zero_iff.mpr fun s _ => hy0 s, ?_⟩
  have h : ∀ z : L, z ∈ AddSubsemigroup.closure (↑S : Set L) →
      IsIntegral ℤ ((∏ s ∈ S, y s) • (z : F)) := by
    intro z hz
    induction hz using AddSubsemigroup.closure_induction with
    | mem s hs =>
      obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun t : L => y t) (show s ∈ S from hs)
      rw [hc, mul_comm, mul_smul]
      exact (hyint s).zsmul c
    | add a b _ _ ha hb => simpa [smul_add] using ha.add hb
  intro x hx
  exact h ⟨x, hx⟩ (hS ▸ AddSubsemigroup.mem_top _)



open scoped Classical in
theorem LatticeImageZLattice.proof : LatticeImageZLattice.Statement := by
  intro F _ _ L hfg hfull
  obtain ⟨N, hN0, hLint⟩ := LatticeImageZLattice.exists_int_mul_integral L hfg

  let e : mixedSpace F →ₗ[ℝ] mixedSpace F := (N : ℝ) • LinearMap.id
  have he₁ : Continuous e := continuous_const_smul (N : ℝ)
  have he₂ : Function.Injective e := fun a b h =>
    smul_right_injective (mixedSpace F) (Int.cast_ne_zero.mpr hN0 : (N : ℝ) ≠ 0) h
  have hdisc : DiscreteTopology (ZLattice.comap ℝ (mixedEmbedding.integerLattice F) e) :=
    ZLattice.comap_discreteTopology ℝ _ he₁ he₂
  have hle : (latticeImage F L : Set (mixedSpace F)) ⊆
      ZLattice.comap ℝ (mixedEmbedding.integerLattice F) e := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := (mem_latticeImage L z).mp hz
    show e (mixedEmbedding F x) ∈ mixedEmbedding.integerLattice F
    refine ⟨⟨N • x, hLint x hx⟩, ?_⟩
    change mixedEmbedding F (N • x) = (N : ℝ) • mixedEmbedding F x
    rw [map_zsmul, Int.cast_smul_eq_zsmul]
  have : DiscreteTopology (latticeImage F L) := DiscreteTopology.of_subset hdisc hle
  refine ⟨this, ⟨?_⟩⟩

  rw [eq_top_iff, ← (latticeBasis F).span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  obtain ⟨n, hn, hnL⟩ := hfull (integralBasis F i)
  have hmem : mixedEmbedding F ((n : F) * integralBasis F i) ∈ latticeImage F L :=
    (mem_latticeImage L _).mpr ⟨_, hnL, rfl⟩
  have hb : latticeBasis F i = (n : ℝ)⁻¹ • mixedEmbedding F ((n : F) * integralBasis F i) := by
    rw [map_mul, map_natCast, ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
      inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hn.ne'), one_smul, latticeBasis_apply]
  rw [hb]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

end GroundTheory.Heights₂.Heights.Targets
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PMixedBoxCount

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding MeasureTheory Metric
open scoped ENNReal NNReal

namespace MixedBoxCount


open scoped Classical in
theorem finite_box (F : Type) [Field F] [NumberField F] (La : Submodule ℤ (mixedSpace F))
    [DiscreteTopology La] (f : InfinitePlace F → ℝ) (hf : ∀ w, 0 < f w) :
    {y : mixedSpace F | y ∈ La ∧ ∀ w, normAtPlace w y ≤ f w}.Finite := by
  have hsub : {y : mixedSpace F | y ∈ La ∧ ∀ w, normAtPlace w y ≤ f w} ⊆
      closedBall 0 (∑ w, f w) ∩ (La : Set (mixedSpace F)) := by
    rintro y ⟨hyL, hy⟩
    refine ⟨?_, hyL⟩
    rw [mem_closedBall_zero_iff, norm_eq_sup'_normAtPlace]
    refine Finset.sup'_le _ _ fun w _ => (hy w).trans ?_
    exact Finset.single_le_sum (fun v _ => (hf v).le) (Finset.mem_univ w)
  refine Set.Finite.subset ?_ hsub
  refine Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete isBounded_closedBall ?_
  rw [← Submodule.coe_toAddSubgroup]
  exact AddSubgroup.isClosed_of_discrete


open scoped Classical in
theorem normAtPlace_lt_of_mem (F : Type) [Field F] [NumberField F] (g : InfinitePlace F → ℝ≥0)
    {x : mixedSpace F} (hx : x ∈ convexBodyLT F g) (w : InfinitePlace F) : normAtPlace w x < g w := by
  rcases isReal_or_isComplex w with hw | hw
  · rw [normAtPlace_apply_of_isReal hw]
    have := hx.1 ⟨w, hw⟩ (Set.mem_univ _)
    simpa [mem_ball_zero_iff] using this
  · rw [normAtPlace_apply_of_isComplex hw]
    have := hx.2 ⟨w, hw⟩ (Set.mem_univ _)
    simpa [mem_ball_zero_iff] using this

end MixedBoxCount


open scoped Classical in
theorem MixedBoxCount.proof (h : LatticeCountVolume.Statement) : MixedBoxCount.Statement := by
  intro F _ _ La _ _ f hf
  have hfin := MixedBoxCount.finite_box F La f hf
  refine ⟨hfin, ?_⟩
  set B := {y : mixedSpace F | y ∈ La ∧ ∀ w, normAtPlace w y ≤ f w} with hB
  let g : InfinitePlace F → ℝ≥0 := fun w => ⟨f w / 2, (half_pos (hf w)).le⟩
  have hS : MeasurableSet (convexBodyLT F g) :=
    (MeasurableSet.univ_pi fun _ => measurableSet_ball).prod
      (MeasurableSet.univ_pi fun _ => measurableSet_ball)
  have hdiff : ∀ x ∈ convexBodyLT F g, ∀ y ∈ convexBodyLT F g,
      x - y ∈ {z : mixedSpace F | ∀ w, normAtPlace w z ≤ f w} := by
    intro x hx y hy w
    have h1 := MixedBoxCount.normAtPlace_lt_of_mem F g hx w
    have h2 := MixedBoxCount.normAtPlace_lt_of_mem F g hy w
    have h3 := normAtPlace_add_le w x (-y)
    rw [normAtPlace_neg, ← sub_eq_add_neg] at h3
    have : ((g w : ℝ≥0) : ℝ) = f w / 2 := rfl
    linarith
  have hle := h (mixedSpace F) volume La (convexBodyLT F g) _ hS hdiff
  have hset : {x : mixedSpace F | x ∈ La ∧ x ∈ {z : mixedSpace F | ∀ w, normAtPlace w z ≤ f w}} = B := rfl
  rw [hset, convexBodyLT_volume, ← hfin.cast_ncard_eq] at hle
  have hcpos := ZLattice.covolume_pos La volume
  have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top) hle
  simp only [ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.toReal_ofReal hcpos.le, NNReal.coe_prod,
    NNReal.coe_pow, ENat.toENNReal_coe, ENNReal.toReal_natCast] at hreal
  have hg : ∀ w, ((g w : ℝ≥0) : ℝ) = f w / 2 := fun _ => rfl
  simp only [hg] at hreal
  have hNpos : 0 < B.ncard :=
    (Set.ncard_pos hfin).mpr ⟨0, La.zero_mem, fun w => by simp [(hf w).le]⟩
  have hN : (0 : ℝ) < (B.ncard : ℝ) := by exact_mod_cast hNpos
  have hc : (0 : ℝ) < (convexBodyLTFactor F : ℝ) :=
    NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (convexBodyLTFactor_ne_zero F))
  have hfac : ∀ w, 0 < (f w / 2) ^ mult w := fun w => pow_pos (half_pos (hf w)) _
  have hprod : 0 < ∏ w, (f w / 2) ^ mult w := Finset.prod_pos fun w _ => hfac w
  have hlog := Real.log_le_log (mul_pos hc hprod) hreal
  rw [Real.log_mul hc.ne' hprod.ne', Real.log_mul hN.ne' hcpos.ne',
    Real.log_prod (fun w _ => (hfac w).ne')] at hlog
  have hl : ∀ w, Real.log ((f w / 2) ^ mult w) = (mult w : ℝ) * Real.log (f w) - (mult w : ℝ) * Real.log 2 :=
    fun w => by rw [Real.log_pow, Real.log_div (hf w).ne' two_ne_zero, mul_sub]
  have hcast : (∑ w : InfinitePlace F, (mult w : ℝ)) = (Module.finrank ℚ F : ℝ) := by
    exact_mod_cast sum_mult_eq
  simp only [hl, Finset.sum_sub_distrib, ← Finset.sum_mul, hcast] at hlog
  linarith

end GroundTheory.Heights₂.Heights.Targets
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PNumberFieldBoxCountX

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

theorem NumberFieldBoxCount.proof_closed : NumberFieldBoxCount.Statement :=
  NumberFieldBoxCount.proof LatticeImageZLattice.proof CovolumeRelIndex.proof EmbeddingSumPlaces.proof
    (MixedBoxCount.proof LatticeCountVolume.proof)

end GroundTheory.Heights₂.Heights.Targets
end
end
