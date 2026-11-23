module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.EnergyInst
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.HaarSubS
public import Formalism.PeriodIntegrals.NMeasInv
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.HaarSubSF
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.NMeasInv
public import Mathlib.MeasureTheory.Measure.Prod
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RightRegularIsometricMultiplicative
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Topology.Algebra.Group.Units

-- Source module: Formalism.PeriodIntegrals.QuotNuSigma

section

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace PI.QuotNuSigma

def Target : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (μG : Measure G) [IsFiniteMeasureOnCompacts μG] (A B : Set G) (μA μB ν : Measure G),
    (SigmaFinite μA ∧ μA ≠ 0 ∧ μA Aᶜ = 0 ∧ ∀ s ∈ A, μA.map (fun x => s * x) = μA) →
    (SigmaFinite μB ∧ μB ≠ 0 ∧ μB Bᶜ = 0 ∧ ∀ s ∈ B, μB.map (fun x => s * x) = μB) →
    (∀ f : G → ℝ≥0∞, Measurable f →
      ∫⁻ x, f x ∂μG = ∫⁻ x, (∫⁻ s, f (s * x) ∂((μA.prod μB).map (fun p => p.1 * p.2))) ∂ν) →
    SigmaFinite ν

end PI.QuotNuSigma
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuotientSigmaFiniteness.SigmaFiniteOfWeil

section

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal Pointwise

namespace PI.UnitaryGroupMassFormula.QuotNuSigma

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem pos_open_one (A : Set G) (μA : Measure G) (h0 : μA ≠ 0) (hc : μA Aᶜ = 0)
    (hinv : ∀ s ∈ A, μA.map (fun x => s * x) = μA) (U : Set G) (hU : IsOpen U) (h1 : (1 : G) ∈ U) :
    0 < μA U := by
  by_contra hpos
  have hU0 : μA U = 0 := nonpos_iff_eq_zero.1 (not_lt.1 hpos)
  let F : A → Set G := fun s => (fun x => (s : G)⁻¹ * x) ⁻¹' U
  have hFo : ∀ s, IsOpen (F s) := fun s => hU.preimage (continuous_const.mul continuous_id)
  have hF0 : ∀ s, μA (F s) = 0 := by
    intro s
    have hm := congrArg (fun m : Measure G => m (F s)) (hinv s s.2)
    rw [← hm, Measure.map_apply (measurable_const_mul _) (hFo s).measurableSet]
    have hpre : (fun x => (s : G) * x) ⁻¹' F s = U := by
      ext x
      simp [F]
    rw [hpre, hU0]
  obtain ⟨T, hT, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable F hFo
  have hcov : A ⊆ ⋃ s ∈ T, F s := by
    intro a ha
    rw [hTU]
    exact Set.mem_iUnion.2 ⟨⟨a, ha⟩, by simp [F, h1]⟩
  have hnull : μA (⋃ s ∈ T, F s) = 0 := (measure_biUnion_null_iff hT).2 fun s _ => hF0 s
  have huniv : μA Set.univ = 0 := by
    refine measure_mono_null (fun x _ => ?_) (measure_union_null hnull hc)
    by_cases hx : x ∈ A
    · exact Or.inl (hcov hx)
    · exact Or.inr hx
  exact h0 (Measure.measure_univ_eq_zero.1 huniv)

theorem pos_open_one_mul (A B : Set G) (μA μB : Measure G) [SigmaFinite μB]
    (hA0 : μA ≠ 0) (hAc : μA Aᶜ = 0) (hAi : ∀ s ∈ A, μA.map (fun x => s * x) = μA)
    (hB0 : μB ≠ 0) (hBc : μB Bᶜ = 0) (hBi : ∀ s ∈ B, μB.map (fun x => s * x) = μB)
    (U : Set G) (hU : IsOpen U) (h1 : (1 : G) ∈ U) :
    0 < ((μA.prod μB).map (fun p : G × G => p.1 * p.2)) U := by
  obtain ⟨V, hVo, hV1, hVV⟩ := exists_open_nhds_one_mul_subset (hU.mem_nhds h1)
  have hApos := pos_open_one A μA hA0 hAc hAi V hVo hV1
  have hBpos := pos_open_one B μB hB0 hBc hBi V hVo hV1
  have hsub : V ×ˢ V ⊆ (fun p : G × G => p.1 * p.2) ⁻¹' U := fun p hp =>
    hVV (Set.mul_mem_mul hp.1 hp.2)
  calc (0 : ℝ≥0∞) < μA V * μB V := ENNReal.mul_pos hApos.ne' hBpos.ne'
    _ = (μA.prod μB) (V ×ˢ V) := (Measure.prod_prod V V).symm
    _ ≤ (μA.prod μB) ((fun p : G × G => p.1 * p.2) ⁻¹' U) := measure_mono hsub
    _ ≤ _ := Measure.le_map_apply measurable_mul.aemeasurable U

theorem sigmaFinite_of_weil [LocallyCompactSpace G] [T2Space G]
    (μG : Measure G) [IsFiniteMeasureOnCompacts μG] (A B : Set G) (μA μB ν : Measure G)
    (hA : SigmaFinite μA ∧ μA ≠ 0 ∧ μA Aᶜ = 0 ∧ ∀ s ∈ A, μA.map (fun x => s * x) = μA)
    (hB : SigmaFinite μB ∧ μB ≠ 0 ∧ μB Bᶜ = 0 ∧ ∀ s ∈ B, μB.map (fun x => s * x) = μB)
    (hW : ∀ f : G → ℝ≥0∞, Measurable f →
      ∫⁻ x, f x ∂μG = ∫⁻ x, (∫⁻ s, f (s * x) ∂((μA.prod μB).map (fun p => p.1 * p.2))) ∂ν) :
    SigmaFinite ν := by
  obtain ⟨hAσ, hA0, hAc, hAi⟩ := hA
  obtain ⟨hBσ, hB0, hBc, hBi⟩ := hB
  have := hAσ
  have := hBσ
  set ρ := (μA.prod μB).map (fun p : G × G => p.1 * p.2) with hρ
  have hK : ∀ x : G, ∃ K, IsCompact K ∧ K ∈ nhds x := fun x => exists_compact_mem_nhds x
  choose K hKc hKn using hK
  have hmeasK : ∀ x, MeasurableSet (K x) := fun x => (hKc x).isClosed.measurableSet
  let h : G → G → ℝ≥0∞ := fun x y => ∫⁻ s, (K x).indicator 1 (s * y) ∂ρ
  have hhm : ∀ x, Measurable (h x) := by
    intro x
    have hq : Measurable fun q : G × G => (K x).indicator (1 : G → ℝ≥0∞) (q.2 * q.1) :=
      (measurable_one.indicator (hmeasK x)).comp (measurable_snd.mul measurable_fst)
    exact hq.lintegral_prod_right'
  have hint : ∀ x, ∫⁻ y, h x y ∂ν = μG (K x) := by
    intro x
    show ∫⁻ y, ∫⁻ s, (K x).indicator 1 (s * y) ∂ρ ∂ν = μG (K x)
    rw [← hW _ (measurable_one.indicator (hmeasK x)), lintegral_indicator_one (hmeasK x)]
  have hpos : ∀ x y, y ∈ interior (K x) → 0 < h x y := by
    intro x y hy
    let O := (fun s : G => s * y) ⁻¹' interior (K x)
    have hOo : IsOpen O := isOpen_interior.preimage (continuous_id.mul continuous_const)
    have hO1 : (1 : G) ∈ O := by simp [O, hy]
    have hρO : 0 < ρ O := pos_open_one_mul A B μA μB hA0 hAc hAi hB0 hBc hBi O hOo hO1
    have hle : ∫⁻ s, O.indicator 1 s ∂ρ ≤ ∫⁻ s, (K x).indicator 1 (s * y) ∂ρ := by
      refine lintegral_mono fun s => ?_
      by_cases hs : s ∈ O
      · have hs' : s * y ∈ K x := interior_subset hs
        simp [Set.indicator_of_mem hs, Set.indicator_of_mem hs']
      · simp [hs]
    rw [lintegral_indicator_one hOo.measurableSet] at hle
    exact lt_of_lt_of_le hρO hle
  obtain ⟨T, hT, hTU⟩ :=
    TopologicalSpace.isOpen_iUnion_countable (fun x => interior (K x)) (fun _ => isOpen_interior)
  have := hT.to_subtype
  let E : T × ℕ → Set G := fun p => {y | ((p.2 : ℝ≥0∞) + 1)⁻¹ ≤ h p.1 y}
  refine Measure.sigmaFinite_of_countable (S := Set.range E) (Set.countable_range E) ?_ ?_
  · rintro _ ⟨⟨x, n⟩, rfl⟩
    have hne0 : ((n : ℝ≥0∞) + 1)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 (by simp)
    have hneT : ((n : ℝ≥0∞) + 1)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 (by simp)
    calc ν (E (x, n)) ≤ (∫⁻ y, h x y ∂ν) / ((n : ℝ≥0∞) + 1)⁻¹ :=
          meas_ge_le_lintegral_div (hhm x).aemeasurable hne0 hneT
      _ < ⊤ := by
        rw [hint]
        exact ENNReal.div_lt_top (hKc x).measure_lt_top.ne hne0
  · refine Set.eq_univ_of_forall fun y => ?_
    have hy : y ∈ ⋃ x ∈ T, interior (K x) := by
      rw [hTU]
      exact Set.mem_iUnion.2 ⟨y, mem_interior_iff_mem_nhds.2 (hKn y)⟩
    obtain ⟨x, hxT, hyx⟩ := Set.mem_iUnion₂.1 hy
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt (hpos x y hyx).ne'
    refine Set.mem_sUnion.2 ⟨E (⟨x, hxT⟩, n), ⟨_, rfl⟩, ?_⟩
    show ((n : ℝ≥0∞) + 1)⁻¹ ≤ h x y
    exact le_trans (ENNReal.inv_le_inv.2 le_self_add) hn.le

end PI.UnitaryGroupMassFormula.QuotNuSigma
end
end
end

-- Source module: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QuotNuSigma

section

@[expose] public section

theorem quotient_sigma_finite : PI.QuotNuSigma.Target :=
  fun _ _ _ _ _ _ _ _ _ μG _ A B μA μB ν hA hB hW =>
    PI.UnitaryGroupMassFormula.QuotNuSigma.sigmaFinite_of_weil μG A B μA μB ν hA hB hW
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.HaarSubSWire

section

@[expose] public section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting
open scoped InnerProductSpace TensorProduct Classical ENNReal
open Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Formalism.L2.S.Pv.HaarSubS

theorem hform_crdX {D : D7} (X : HidaSetting D) (v w : (VS D).V) :
    X.ιE (Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J (crdOf X.B.I X.ιE X.bas v) (crdOf X.B.I X.ιE X.bas w)) =
      (VS D).hT v w := by
  conv_rhs => rw [← X.bas.sum_repr v, ← X.bas.sum_repr w]
  unfold Formalism.UG.hform crdOf

  simp only [map_sum, map_mul, X.ιE_conj, X.J_eq, RingEquiv.apply_symm_apply, LinearMap.map_smulₛₗ,
  LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, RingHom.id_apply, Finset.mul_sum]
  have hst : ∀ x : D.host.E, star x = D.host.conj x := fun x => Formalism.MainNotions.S.Inh.tie_star D x
  simp only [hst]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hform_eqX {D : D7} (X : HidaSetting D) (v w : (VS D).V) :
    Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J (crdOf X.B.I X.ιE X.bas v) (crdOf X.B.I X.ιE X.bas w) =
      X.ιE.symm ((VS D).hT v w) := by
  rw [← hform_crdX X v w, RingEquiv.symm_apply_apply]

theorem frameRelX {D : D7} (X : HidaSetting D) (u : D.what₂.Word) :
    PI.NMeasInv.FrameRel X.B.I X.eR X.fR (X.zR u) := by
  have h : ∀ v w, Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J (X.crd v) (X.crd w) =
      X.ιE.symm ((VS D).hT v w) := fun v w => hform_eqX X v w
  unfold Formalism.L2.SG.HidaSetting.HidaSetting.eR Formalism.L2.SG.HidaSetting.HidaSetting.fR Formalism.L2.SG.HidaSetting.HidaSetting.zR
  refine ⟨fun a b => ?_, fun a b => ?_, fun a b => ?_, fun a => ⟨?_, ?_⟩, ?_⟩
  · rw [h, X.ee, map_zero]
  · rw [h, X.ff, map_zero]
  · rw [h, X.ef]
    split_ifs <;> simp
  · rw [h, (X.zu_orth u a).1, map_zero]
  · rw [h, (X.zu_orth u a).2, map_zero]
  · rw [h, X.zu_norm, map_neg, map_natCast, neg_ne_zero, Nat.cast_ne_zero]
    exact (D.mem u).A.T_prime.ne_zero

theorem measN_holds : MeasN := by
  obtain ⟨h1, h2, h3, h4⟩ := PI.n_measure_invariant
  intro D X u
  have hF := frameRelX X u
  have hμ : PI.NMeasInv.IsHaarOnSet X.B.I (PI.NMeasInv.Ninf X.B.I X.eR (X.zR u)) (X.muN u) := X.muN_haar u
  exact ⟨h1 _ _ _ _ _ hF _ hμ, h2 _ _ _ _ _ hF _ hμ, h3 _ _ _ _ _ hF _ hμ, h4 _ _ _ _ _ hF _ hμ⟩

theorem nuQSFinite_holds : NuQSFinite := by
  intro D X u
  haveI : SigmaFinite (X.nuQ u) :=
    quotient_sigma_finite X.B.I.Ginf (Formalism.L2.SG.ProjRows.muInf X.B.I) _ _ (X.muN u) (X.muH u) (X.nuQ u)
      (X.muN_haar u) (X.muH_haar u) (X.nuQ_weil u)
  infer_instance

theorem stepSubG_holds : Formalism.L2.SG.RealObj.EnergyInst.StepSubG := stepSubG_of_MN measN_holds nuQSFinite_holds

end Formalism.L2.S.Pv.HaarSubS
end
end
end
