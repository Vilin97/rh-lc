module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.LatticeIndexLifts.MeasurableSpaceSecondLift
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalizedAbsCharacterization
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.LatticeIndexLifts.AvNonneg
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GaussianDualMeasure.SecondCountableTopologyAndT2Space
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
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.LatticeIndexLifts.SummandInv
import Mathlib.Algebra.Order.Star.Real
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.LatticeIndexLifts.MeasurableSpaceThirdLift

section

@[expose] public section

noncomputable section

open Matrix MeasureTheory GlobalTheory.SplitWeil GlobalTheory.BZMir Filter
open scoped Topology ENNReal NNReal

namespace PositivityTheory.RgUd.Form.U.Lift2

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Main

local instance measurableSpaceThirdLift : MeasurableSpace k := borel k
local instance borelSpaceThirdLift : BorelSpace k := ⟨rfl⟩
local instance instSCK3 : SecondCountableTopology k := GlobalTheory.SplitWeil.secondCountable k

variable {ψ : AddChar k Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) {m : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
  {col : (Fin (m + 1) → k) → V →ₗ[ℂ] V} {gl : GL (Fin (m + 1)) k →* (V →ₗ[ℂ] V)} (hS : Setup col gl) {s : ℝ}
  {B B' C : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} {A₀ : AddSubgroup (Fin (m + 1) → k)} (hA₀ : Lat A₀)
  (hBp : Psd B) (hBc : ∀ x v w, B (col x v) (col x w) = B v w)
  (hBg : ∀ g v w, B (gl g v) (gl g w) = ((md g ^ s : ℝ) : ℂ) * B v w)
  (hD : IsD ψ col A₀ B B') (hCp : Psd C) (hCc : ∀ x v w, C (col x v) w = ((ψ (xz m ⬝ᵥ x) : Circle) : ℂ) * C v w)
  (hC : ∀ p ∈ Mir k m, ∀ v w, C (gl p v) (gl p w) = ((md p ^ (s + 1) : ℝ) : ℂ) * C v w)
  (hCB : ∀ v, (C v v).re ≤ (B' v v).re)
  {ν : Measure (Fin (m + 1) → k)} [ν.IsAddHaarMeasure] (hν : ν (perp ψ A₀) = 1)


include hψ hψ1 hS hA₀ hBp hBc hBg hD hCp hC hCB hν in
theorem cov {K : Set (Fin (m + 1) → k)} (hK : IsCompact K) (h0 : (0 : Fin (m + 1) → k) ∉ K) (v : V) :
    ∫⁻ ξ in K, ENNReal.ofReal (Df gl s C ξ v v).re ∂ν ≤ ENNReal.ofReal (B v v).re := by
  classical
  have hloc : ∀ ζ ∈ K, ∃ M₀ : AddSubgroup (Fin (m + 1) → k), Lat M₀ ∧
      ∀ ξ, ξ - ζ ∈ perp ψ M₀ → Df gl s C ξ v v = Df gl s C ζ v v ∧
        ∀ M : AddSubgroup (Fin (m + 1) → k), Lat M → M₀ ≤ M →
          (Df gl s C ζ v v).re * (ν (perp ψ M)).toReal ≤ (B (av ψ col ξ M v) v).re :=
    fun ζ hζ => locB hψ hψ1 hS hA₀ hBg hD hCp hC hCB hν (fun h => h0 (h ▸ hζ)) v
  choose! M₀ hM₀L hM₀ using hloc
  obtain ⟨F, hFK, hFfin, hFcov⟩ := hK.elim_finite_subcover_image (b := K)
    (c := fun ζ => (fun ξ => ξ - ζ) ⁻¹' (perp ψ (M₀ ζ) : Set (Fin (m + 1) → k)))
    (fun ζ hζ => (perp_open ψ hψ hψ1 (hM₀L ζ hζ)).preimage (continuous_sub_right ζ))
    (fun ζ hζ => Set.mem_biUnion hζ (by simp))
  have hcomp : IsCompact (⋃ ζ ∈ F, (M₀ ζ : Set (Fin (m + 1) → k))) :=
    hFfin.isCompact_biUnion fun ζ hζ => (hM₀L ζ (hFK hζ)).1
  obtain ⟨M, hML, hMsub⟩ := lat_over hcomp
  have hMle : ∀ ζ ∈ F, M₀ ζ ≤ M := fun ζ hζ x hx => hMsub (Set.mem_biUnion hζ hx)
  have hPle : ∀ ζ ∈ F, perp ψ M ≤ perp ψ (M₀ ζ) := fun ζ hζ => perp_anti ψ (hMle ζ hζ)
  have hPo : IsOpen (perp ψ M : Set (Fin (m + 1) → k)) := perp_open ψ hψ hψ1 hML
  obtain ⟨T, hTK, hTfin, hTcov⟩ := hK.elim_finite_subcover_image (b := K)
    (c := fun t => (fun ξ => ξ - t) ⁻¹' (perp ψ M : Set (Fin (m + 1) → k)))
    (fun t _ => hPo.preimage (continuous_sub_right t))
    (fun ξ hξ => Set.mem_biUnion hξ (by simp))
  let q : (Fin (m + 1) → k) → (Fin (m + 1) → k) ⧸ perp ψ M := QuotientAddGroup.mk
  have hq : ∀ a b, q a = q b → a - b ∈ perp ψ M := fun a b h => by
    have h1 := (perp ψ M).neg_mem (QuotientAddGroup.eq.mp h)
    rwa [show -(-a + b) = a - b by abel] at h1
  have hq' : ∀ a b, a - b ∈ perp ψ M → q a = q b := fun a b h => by
    apply QuotientAddGroup.eq.mpr
    rw [show -a + b = -(a - b) by abel]
    exact (perp ψ M).neg_mem h
  have hout : ∀ t, q (q t).out = q t := fun t => QuotientAddGroup.out_eq' (q t)
  let S : Finset (Fin (m + 1) → k) := hTfin.toFinset.image (fun t => (q t).out)
  have hSF : ∀ η ∈ S, ∃ ζ ∈ F, ∀ ξ, ξ - η ∈ perp ψ M → ξ - ζ ∈ perp ψ (M₀ ζ) := by
    intro η hη
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hη
    have htK : t ∈ K := hTK (hTfin.mem_toFinset.mp ht)
    obtain ⟨ζ, hζ, hζt⟩ := Set.mem_iUnion₂.mp (hFcov htK)
    refine ⟨ζ, hζ, fun ξ hξ => ?_⟩
    have h1 : (q t).out - t ∈ perp ψ M := hq _ _ (hout t)
    have h2 : ξ - ζ = (ξ - (q t).out) + ((q t).out - t) + (t - ζ) := by abel
    rw [h2]
    exact add_mem (add_mem (hPle ζ hζ hξ) (hPle ζ hζ h1)) (show t - ζ ∈ perp ψ (M₀ ζ) from hζt)
  have hSd : ∀ η ∈ S, ∀ η' ∈ S, η - η' ∈ perp ψ M → η = η' := by
    intro η hη η' hη' h
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hη
    obtain ⟨t', -, rfl⟩ := Finset.mem_image.mp hη'
    have h1 := hq' _ _ h
    rw [hout, hout] at h1
    rw [h1]
  have hKS : K ⊆ ⋃ η ∈ S, (fun ξ => ξ - η) ⁻¹' (perp ψ M : Set (Fin (m + 1) → k)) := by
    intro ξ hξ
    obtain ⟨t, ht, hξt⟩ := Set.mem_iUnion₂.mp (hTcov hξ)
    refine Set.mem_iUnion₂.mpr ⟨(q t).out, Finset.mem_image.mpr ⟨t, hTfin.mem_toFinset.mpr ht, rfl⟩, ?_⟩
    have h1 : t - (q t).out ∈ perp ψ M := hq _ _ (hout t).symm
    show ξ - (q t).out ∈ perp ψ M
    rw [show ξ - (q t).out = (ξ - t) + (t - (q t).out) by abel]
    exact add_mem (show ξ - t ∈ perp ψ M from hξt) h1
  have hdisj : Set.PairwiseDisjoint (↑S)
      (fun η => (fun ξ => ξ - η) ⁻¹' (perp ψ M : Set (Fin (m + 1) → k))) := by
    intro η hη η' hη' hne
    refine Set.disjoint_left.mpr fun ξ h1 h2 => hne (hSd η hη η' hη' ?_)
    rw [show η - η' = (ξ - η') - (ξ - η) by abel]
    exact sub_mem (show ξ - η' ∈ perp ψ M from h2) (show ξ - η ∈ perp ψ M from h1)
  have hPfin : ν (perp ψ M) < ∞ := meas_perp_lt_top ψ ν hψ hψ1 hML
  have hbd : ∀ η ∈ S, (Df gl s C η v v).re * (ν (perp ψ M)).toReal ≤ (B (av ψ col η M v) v).re ∧
      ∃ ζ ∈ F, Df gl s C η v v = Df gl s C ζ v v ∧
        ∀ ξ, ξ - η ∈ perp ψ M → Df gl s C ξ v v = Df gl s C η v v := by
    intro η hη
    obtain ⟨ζ, hζ, hζη⟩ := hSF η hη
    have hζK := hFK hζ
    have e0 : Df gl s C η v v = Df gl s C ζ v v := ((hM₀ ζ hζK) η (hζη η (by simp))).1
    have hb := ((hM₀ ζ hζK) η (hζη η (by simp))).2 M hML (hMle ζ hζ)
    refine ⟨by rw [e0]; exact hb, ζ, hζ, e0, fun ξ hξ => ?_⟩
    rw [e0]
    exact ((hM₀ ζ hζK) ξ (hζη ξ hξ)).1
  have step : ∀ η ∈ S, ∫⁻ ξ in (fun ξ => ξ - η) ⁻¹' (perp ψ M : Set (Fin (m + 1) → k)),
      ENNReal.ofReal (Df gl s C ξ v v).re ∂ν ≤ ENNReal.ofReal (B (av ψ col η M v) v).re := by
    intro η hη
    obtain ⟨hb, -, -, -, hc⟩ := hbd η hη
    rw [setLIntegral_congr_fun (g := fun _ => ENNReal.ofReal (Df gl s C η v v).re)
      (hPo.preimage (continuous_sub_right η)).measurableSet
      (fun ξ hξ => by simp only; rw [hc ξ hξ]), setLIntegral_const]
    have hmeas : ν ((fun ξ => ξ - η) ⁻¹' (perp ψ M : Set (Fin (m + 1) → k))) = ν (perp ψ M) := by
      simp only [sub_eq_add_neg]
      exact measure_preimage_add_right ν (-η) _
    rw [hmeas, ← ENNReal.ofReal_toReal hPfin.ne, ← ENNReal.ofReal_mul (Df_re_nonneg hCp η v)]
    exact ENNReal.ofReal_le_ofReal hb
  have hnn : ∀ η ∈ S, 0 ≤ (B (av ψ col η M v) v).re := fun η hη =>
    le_trans (mul_nonneg (Df_re_nonneg hCp η v) ENNReal.toReal_nonneg) (hbd η hη).1
  have hbes := av_bessel ψ hψ col hS.col_zero hS.col_add hS.smooth_col B hBp hBc M hML S hSd v
  calc ∫⁻ ξ in K, ENNReal.ofReal (Df gl s C ξ v v).re ∂ν
      ≤ ∫⁻ ξ in ⋃ η ∈ S, (fun ξ => ξ - η) ⁻¹' (perp ψ M : Set (Fin (m + 1) → k)),
          ENNReal.ofReal (Df gl s C ξ v v).re ∂ν := lintegral_mono_set hKS
    _ = ∑ η ∈ S, ∫⁻ ξ in (fun ξ => ξ - η) ⁻¹' (perp ψ M : Set (Fin (m + 1) → k)),
          ENNReal.ofReal (Df gl s C ξ v v).re ∂ν :=
        lintegral_biUnion_finset hdisj (fun η _ => (hPo.preimage (continuous_sub_right η)).measurableSet) _
    _ ≤ ∑ η ∈ S, ENNReal.ofReal (B (av ψ col η M v) v).re := Finset.sum_le_sum step
    _ = ENNReal.ofReal (∑ η ∈ S, (B (av ψ col η M v) v).re) := (ENNReal.ofReal_sum_of_nonneg hnn).symm
    _ ≤ ENNReal.ofReal (B v v).re := ENNReal.ofReal_le_ofReal hbes


include hψ hψ1 hS hA₀ hBp hBc hBg hD hCp hC hCB hν in
theorem bessel (v : V) : ∫⁻ ξ, ENNReal.ofReal (Df gl s C ξ v v).re ∂ν ≤ ENNReal.ofReal (B v v).re := by
  classical
  let f : (Fin (m + 1) → k) → ℝ≥0∞ := fun ξ => ENNReal.ofReal (Df gl s C ξ v v).re
  have hDm : Measurable fun ξ => Df gl s C ξ v v := by
    apply measurable_of_continuousOn_compl_singleton 0
    intro ζ hζ
    exact (continuousAt_const.congr
      ((Df_loc hS hC hζ v v).mono fun ξ hξ => hξ.symm)).continuousWithinAt
  have hfm : Measurable f := ENNReal.measurable_ofReal.comp (Complex.measurable_re.comp hDm)
  obtain ⟨W, hWp, hW⟩ := (nhds_basis_opens (0 : Fin (m + 1) → k)).exists_antitone_subbasis
  let E := CompactExhaustion.choice (Fin (m + 1) → k)
  let K : ℕ → Set (Fin (m + 1) → k) := fun n => E n \ W n
  have hKc : ∀ n, IsCompact (K n) := fun n => (E.isCompact n).diff (hWp n).2
  have h0K : ∀ n, (0 : Fin (m + 1) → k) ∉ K n := fun n h => h.2 (hWp n).1
  have hKmono : Monotone K := fun a b hab => Set.diff_subset_diff (E.subset hab) (hW.antitone hab)
  let g : ℕ → (Fin (m + 1) → k) → ℝ≥0∞ := fun n => (K n).indicator f
  have hgm : ∀ n, Measurable (g n) := fun n => hfm.indicator (hKc n).measurableSet
  have hgmono : Monotone g := fun a b hab ξ =>
    Set.indicator_le_indicator_of_subset (hKmono hab) (fun _ => bot_le) ξ
  have hsup : ∀ ξ, f ξ = ⨆ n, g n ξ := by
    intro ξ
    by_cases hξ : ξ = 0
    · subst hξ
      have hf0 : f 0 = 0 := by simp [f, Df_zero]
      rw [hf0]
      symm
      exact ENNReal.iSup_eq_zero.mpr fun n => by simp [g, Set.indicator_apply, h0K n]
    · obtain ⟨n₁, hn₁⟩ := E.exists_mem ξ
      obtain ⟨i, -, hi⟩ := hW.toHasBasis.mem_iff.mp (isOpen_compl_singleton.mem_nhds (Ne.symm hξ))
      have hmem : ξ ∈ K (max n₁ i) := by
        refine ⟨E.subset (le_max_left _ _) hn₁, fun h => ?_⟩
        exact hi (hW.antitone (le_max_right _ _) h) rfl
      refine le_antisymm (le_iSup_of_le (max n₁ i) ?_) (iSup_le fun n => Set.indicator_le_self _ _ ξ)
      simp [g, Set.indicator_apply, hmem]
  show ∫⁻ ξ, f ξ ∂ν ≤ _
  calc ∫⁻ ξ, f ξ ∂ν = ∫⁻ ξ, ⨆ n, g n ξ ∂ν := lintegral_congr hsup
    _ = ⨆ n, ∫⁻ ξ, g n ξ ∂ν := lintegral_iSup hgm hgmono
    _ ≤ ENNReal.ofReal (B v v).re := iSup_le fun n => by
        simp only [g]
        rw [lintegral_indicator (hKc n).measurableSet]
        exact cov hψ hψ1 hS hA₀ hBp hBc hBg hD hCp hC hCB hν (hKc n) (h0K n) v

omit hψ hψ1 hA₀ hBp hBc hBg hD hCp hCB hν [ν.IsAddHaarMeasure] in
include hS hC in
theorem Df_meas (v w : V) : Measurable fun ξ => Df gl s C ξ v w := by
  apply measurable_of_continuousOn_compl_singleton 0
  intro ζ hζ
  exact (continuousAt_const.congr
    ((Df_loc hS hC hζ v w).mono fun ξ hξ => hξ.symm)).continuousWithinAt

include hψ hψ1 hS hA₀ hBp hBc hBg hD hCp hC hCB hν in
theorem integrable_re (v : V) : Integrable (fun ξ => (Df gl s C ξ v v).re) ν := by
  refine ⟨(Complex.measurable_re.comp (Df_meas hS hC v v)).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun ξ => Df_re_nonneg hCp ξ v)]
  exact lt_of_le_of_lt (bessel hψ hψ1 hS hA₀ hBp hBc hBg hD hCp hC hCB hν v) ENNReal.ofReal_lt_top

include hψ hψ1 hS hA₀ hBp hBc hBg hD hCp hC hCB hν in
theorem integrable_Df (v w : V) : Integrable (fun ξ => Df gl s C ξ v w) ν := by
  refine Integrable.mono'
    (((integrable_re hψ hψ1 hS hA₀ hBp hBc hBg hD hCp hC hCB hν v).add
      (integrable_re hψ hψ1 hS hA₀ hBp hBc hBg hD hCp hC hCB hν w)).div_const 2)
    (Df_meas hS hC v w).aestronglyMeasurable
    (Eventually.of_forall fun ξ => psd_norm_le _ ⟨Df_herm hCp ξ, Df_re_nonneg hCp ξ⟩ v w)

end Main

end PositivityTheory.RgUd.Form.U.Lift2
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.LatticeIndexLifts.MeasurableSpaceFourthLift

section

@[expose] public section

noncomputable section

open Matrix MeasureTheory GlobalTheory.SplitWeil GlobalTheory.BZMir Filter
open scoped Topology ENNReal NNReal

namespace PositivityTheory.RgUd.Form.U.Lift2

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Main

local instance measurableSpaceFourthLift : MeasurableSpace k := borel k
local instance borelSpaceOnK : BorelSpace k := ⟨rfl⟩
local instance instSCK4 : SecondCountableTopology k := GlobalTheory.SplitWeil.secondCountable k

variable {ψ : AddChar k Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) {m : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
  {col : (Fin (m + 1) → k) → V →ₗ[ℂ] V} {gl : GL (Fin (m + 1)) k →* (V →ₗ[ℂ] V)} (hS : Setup col gl) {s : ℝ}
  {B B' C : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} {A₀ : AddSubgroup (Fin (m + 1) → k)} (hA₀ : Lat A₀)
  (hBp : Psd B) (hBc : ∀ x v w, B (col x v) (col x w) = B v w)
  (hBg : ∀ g v w, B (gl g v) (gl g w) = ((md g ^ s : ℝ) : ℂ) * B v w)
  (hD : IsD ψ col A₀ B B') (hCp : Psd C) (hCc : ∀ x v w, C (col x v) w = ((ψ (xz m ⬝ᵥ x) : Circle) : ℂ) * C v w)
  (hC : ∀ p ∈ Mir k m, ∀ v w, C (gl p v) (gl p w) = ((md p ^ (s + 1) : ℝ) : ℂ) * C v w)
  (hCB : ∀ v, (C v v).re ≤ (B' v v).re)
  {ν : Measure (Fin (m + 1) → k)} [ν.IsAddHaarMeasure] (hν : ν (perp ψ A₀) = 1)

private theorem addHaar_singleton_zero_eq_zero {m : ℕ} {ψ : AddChar k Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
    (ν : Measure (Fin (m + 1) → k)) [ν.IsAddHaarMeasure] : ν {0} = 0 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (ValuativeRel.valuation k).integer
  have hϖ0 : (ϖ : k) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  set x : kˣ := Units.mk0 (ϖ : k) hϖ0 with hxdef
  have hx : nabs k x < 1 := by
    rw [nabs_uniformiser hϖ rfl]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast one_lt_resCard k)
  have hx0 : 0 < nabs k x := nabs_pos k x
  let g : GL (Fin (m + 1)) k :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero (((x⁻¹ : kˣ) : k) • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k))
      (by simp [Matrix.det_smul])
  have hdet : Matrix.GeneralLinearGroup.det g = x⁻¹ ^ (m + 1) := by
    ext
    simp [g, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_smul]
  have hg : md g = (nabs k x)⁻¹ ^ (m + 1) := by
    show nabs k (Matrix.GeneralLinearGroup.det g) = _
    rw [hdet]
    simp [nabs, map_pow, map_inv]
  have hg1 : 1 < md g := by
    rw [hg]
    exact one_lt_pow₀ (one_lt_inv₀ hx0 |>.2 hx) (Nat.succ_ne_zero m)
  obtain ⟨A, hA, -⟩ := lat_over (isCompact_empty (X := Fin (m + 1) → k))
  have hpow : ∀ j : ℕ, md (g ^ j) = md g ^ j := by
    intro j
    induction j with
    | zero => simp [md_one]
    | succ j ih => rw [pow_succ, md_mul, ih, pow_succ]
  have hbound : ∀ j : ℕ, (ν {0}).toReal ≤ ((md g)⁻¹) ^ j * (ν (perp ψ A)).toReal := by
    intro j
    have h0 : ({0} : Set (Fin (m + 1) → k)) ⊆ (perp ψ (gmap (g ^ j) A) : Set _) := by
      simp [(perp ψ (gmap (g ^ j) A)).zero_mem]
    calc (ν {0}).toReal ≤ (ν (perp ψ (gmap (g ^ j) A))).toReal :=
          ENNReal.toReal_mono (meas_perp_lt_top ψ ν hψ hψ1 (lat_gmap _ _ hA)).ne (measure_mono h0)
      _ = _ := by rw [meas_perp_gmap ψ ν hψ hψ1 _ hA, hpow, inv_pow]
  have hlim : Tendsto (fun j : ℕ => ((md g)⁻¹) ^ j * (ν (perp ψ A)).toReal) atTop (𝓝 0) := by
    have := tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.2 (md_pos g).le) (inv_lt_one_of_one_lt₀ hg1)
    simpa using this.mul_const (ν (perp ψ A)).toReal
  have hle : (ν {0}).toReal ≤ 0 := ge_of_tendsto' hlim hbound
  have hfin : ν {0} ≠ ⊤ := by
    refine ne_top_of_le_ne_top (meas_perp_lt_top ψ ν hψ hψ1 hA).ne (measure_mono ?_)
    simp [(perp ψ A).zero_mem]
  have := le_antisymm hle ENNReal.toReal_nonneg
  rcases (ENNReal.toReal_eq_zero_iff _).1 this with h | h
  · exact h
  · exact absurd h hfin


include hψ hψ1 hS hA₀ hBp hBc hBg hD hCp hCc hC hCB hν in
theorem lift_form : ∃ I : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ, Psd I ∧ (∀ x v w, I (col x v) (col x w) = I v w) ∧
      (∀ g v w, I (gl g v) (gl g w) = ((nabs k (Matrix.GeneralLinearGroup.det g) ^ s : ℝ) : ℂ) * I v w) ∧
      (∀ v, (I v v).re ≤ (B v v).re) ∧ IsD ψ col A₀ I C ∧ IsA col I 0 ∧
      ∀ Y : Submodule ℂ V, (∀ g, ∀ y ∈ Y, gl g y ∈ Y) → (∀ y ∈ Y, ∀ w, C y w = 0) → ∀ y ∈ Y, ∀ w, I y w = 0 := by
  have hC' : ∀ p ∈ Mir k m, ∀ v w, C (gl p v) (gl p w) = ((md p ^ (s + 1) : ℝ) : ℂ) * C v w := hC
  have hint : ∀ v w, Integrable (fun ξ => Df gl s C ξ v w) ν :=
    integrable_Df hψ hψ1 hS hA₀ hBp hBc hBg hD hCp hC' hCB hν
  let I : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ := LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
    (fun v w => ∫ ξ, Df gl s C ξ v w ∂ν)
    (fun v₁ v₂ w => by
      simp only [map_add (f := _), LinearMap.add_apply]
      exact integral_add (hint _ _) (hint _ _))
    (fun c v w => by
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
      exact integral_const_mul c _)
    (fun v w₁ w₂ => by
      simp only [map_add (f := _)]
      exact integral_add (hint _ _) (hint _ _))
    (fun c v w => by
      simp only [LinearMap.map_smulₛₗ, smul_eq_mul]
      exact integral_const_mul _ _)
  have hI : ∀ v w, I v w = ∫ ξ, Df gl s C ξ v w ∂ν := fun _ _ => rfl
  refine ⟨I, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v w
    rw [hI, hI, ← integral_conj]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ξ => Df_herm hCp ξ v w)
  · intro v
    rw [hI]
    have := integral_re (hint v v)
    simp only [RCLike.re_to_complex] at this
    rw [← this]
    exact integral_nonneg fun ξ => Df_re_nonneg hCp ξ v
  · intro x v w
    rw [hI, hI]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ξ => form_column_invariant hS hCp hCc hC' ξ x v w)
  · intro g v w
    rw [hI, hI]
    have h1 : ∀ ξ, Df gl s C ξ (gl g v) (gl g w) =
        ((md g ^ (s + 1) : ℝ) : ℂ) * Df gl s C (ξ ᵥ* (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k)) v w := by
      intro ξ
      by_cases hξ : ξ = 0
      · subst hξ
        simp [Df_zero, Matrix.zero_vecMul]
      · exact Df_gl hS hC' hξ g v w
    simp_rw [h1]
    rw [integral_const_mul, integral_vecMul ν (fun ξ => Df gl s C ξ v w) g, ← mul_assoc]
    congr 1
    have hp := md_pos g
    rw [Real.rpow_add_one hp.ne']
    push_cast
    exact mul_div_cancel_right₀ _ (by exact_mod_cast hp.ne')
  · intro v
    rw [hI]
    have := integral_re (hint v v)
    simp only [RCLike.re_to_complex] at this
    rw [← this]
    have hb := bessel hψ hψ1 hS hA₀ hBp hBc hBg hD hCp hC' hCB hν v
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun ξ => Df_re_nonneg hCp ξ v)
      (integrable_re hψ hψ1 hS hA₀ hBp hBc hBg hD hCp hC' hCB hν v).aestronglyMeasurable]
    calc _ ≤ (ENNReal.ofReal (B v v).re).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
      _ = _ := ENNReal.toReal_ofReal (hBp.2 v)
  · intro v w
    have hxz : xz m ≠ (0 : Fin (m + 1) → k) := by
      intro h
      have := congrFun h (Fin.last m)
      simp [xz] at this
    have hloc := Df_loc hS hC' hxz v w
    rw [Df_xz hC'] at hloc
    have hU : (fun η => xz m + η) ⁻¹' {ξ | Df gl s C ξ v w = C v w} ∈ 𝓝 (0 : Fin (m + 1) → k) := by
      have ht : Tendsto (fun η : Fin (m + 1) → k => xz m + η) (𝓝 0) (𝓝 (xz m)) := by
        have hc : Continuous (fun η : Fin (m + 1) → k => xz m + η) :=
          continuous_const.add continuous_id
        have := hc.tendsto (0 : Fin (m + 1) → k)
        simpa using this
      exact ht hloc
    obtain ⟨A₂, hA₂, hsub⟩ := lat_shrink ψ hψ hψ1 hU
    obtain ⟨A₁, hA₁, h01, h21⟩ := lat_sup hA₀ hA₂
    refine ⟨A₁, hA₁, h01, fun A hA hA1 => ?_⟩
    rw [hI]
    have hav : ∀ ξ, Df gl s C ξ (av ψ col (xz m) A v) w =
        Set.indicator {ξ | ξ - xz m ∈ perp ψ A} (fun _ => C v w) ξ := by
      intro ξ
      rw [AvA.av_eigen' ψ hψ col hS.col_zero hS.col_add hS.smooth_col (Df gl s C ξ) ψ ξ
        (Df_col hS hCc hC' ξ) A hA (xz m) v w]
      by_cases hm : ξ - xz m ∈ perp ψ A
      · rw [Set.indicator_of_mem (show ξ ∈ {ξ | ξ - xz m ∈ perp ψ A} from hm), if_pos]
        · have h2 : ξ - xz m ∈ perp ψ A₂ := perp_anti ψ (h21.trans hA1) hm
          have h3 := hsub h2
          simpa using h3
        · intro a ha
          have := (mem_perp ψ A _).1 hm a ha
          rw [sub_dotProduct, AddChar.map_sub_eq_div, div_eq_one] at this
          exact this
      · rw [Set.indicator_of_notMem (show ξ ∉ {ξ | ξ - xz m ∈ perp ψ A} from hm), if_neg]
        intro hall
        apply hm
        rw [mem_perp]
        intro a ha
        rw [sub_dotProduct, AddChar.map_sub_eq_div, hall a ha, div_self']
    have hset : {ξ | ξ - xz m ∈ perp ψ A} = (fun ξ => ξ + -xz m) ⁻¹' (perp ψ A : Set (Fin (m + 1) → k)) := by
      ext ξ
      simp [sub_eq_add_neg]
    have hmeas : MeasurableSet {ξ | ξ - xz m ∈ perp ψ A} := by
      rw [hset]
      exact (perp_open ψ hψ hψ1 hA).measurableSet.preimage (measurable_add_const _)
    simp_rw [hav]
    rw [integral_indicator_const _ hmeas, measureReal_def, hset, measure_preimage_add_right]
    have h1 : ((A₀.relIndex A : ℝ)) * (ν (perp ψ A)).toReal = 1 := by
      have := meas_perp_index ψ ν hψ hψ1 hA₀ hA (h01.trans hA1)
      rw [hν] at this
      have := congrArg ENNReal.toReal this
      rw [ENNReal.toReal_mul, ENNReal.toReal_natCast] at this
      simpa using this.symm
    have h2 : ((A₀.relIndex A : ℂ)) * (((ν (perp ψ A)).toReal : ℝ) : ℂ) = 1 := by
      exact_mod_cast h1
    rw [Complex.real_smul, ← mul_assoc, h2, one_mul]
  · intro v w
    simp only [LinearMap.zero_apply]
    have hone : Continuous ⇑(1 : AddChar k Circle) := by
      have : ⇑(1 : AddChar k Circle) = fun _ => 1 := by
        funext x
        exact AddChar.one_apply x
      rw [this]
      exact continuous_const
    have hav : ∀ A : {A : AddSubgroup (Fin (m + 1) → k) // Lat A},
        I (av 1 col 0 A.1 v) w = ∫ ξ in (perp ψ A.1 : Set (Fin (m + 1) → k)), Df gl s C ξ v w ∂ν := by
      intro A
      rw [hI, ← integral_indicator (perp_open ψ hψ hψ1 A.2).measurableSet]
      congr 1
      funext ξ
      rw [AvA.av_eigen' 1 hone col hS.col_zero hS.col_add hS.smooth_col (Df gl s C ξ) ψ ξ
        (Df_col hS hCc hC' ξ) A.1 A.2 0 v w]
      by_cases hm : ξ ∈ perp ψ A.1
      · rw [Set.indicator_of_mem (show ξ ∈ (perp ψ A.1 : Set (Fin (m + 1) → k)) from hm), if_pos]
        intro a ha
        rw [(mem_perp ψ _ _).1 hm a ha, AddChar.one_apply]
      · rw [Set.indicator_of_notMem (show ξ ∉ (perp ψ A.1 : Set (Fin (m + 1) → k)) from hm), if_neg]
        intro hall
        apply hm
        rw [mem_perp]
        intro a ha
        rw [hall a ha, AddChar.one_apply]
    have hfun : (fun A : {A : AddSubgroup (Fin (m + 1) → k) // Lat A} => I (av 1 col 0 A.1 v) w) =
        fun A => ∫ ξ in (perp ψ A.1 : Set (Fin (m + 1) → k)), Df gl s C ξ v w ∂ν := funext hav
    rw [hfun]
    apply (hint v w).tendsto_setIntegral_nhds_zero
    rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    have h0 : ν {0} < ε := by
      rw [addHaar_singleton_zero_eq_zero hψ hψ1 ν]
      exact hε
    obtain ⟨U, hU0, hUo, hUε⟩ := Set.exists_isOpen_lt_of_lt _ _ h0
    obtain ⟨A₂, hA₂, hsub⟩ := lat_shrink ψ hψ hψ1 (hUo.mem_nhds (hU0 rfl))
    filter_upwards [Filter.mem_atTop (⟨A₂, hA₂⟩ : {A : AddSubgroup (Fin (m + 1) → k) // Lat A})] with A hA
    have hsub2 : (perp ψ A.1 : Set (Fin (m + 1) → k)) ⊆ U :=
      (SetLike.coe_subset_coe.2 (perp_anti ψ (show A₂ ≤ A.1 from hA))).trans hsub
    exact (measure_mono hsub2).trans hUε.le
  · intro Y hY hCY y hy w
    rw [hI]
    have : (fun ξ => Df gl s C ξ y w) = fun _ => (0 : ℂ) := funext fun ξ => Df_ker hCp hC' Y hY hCY ξ hy w
    rw [this, integral_zero]

end Main

theorem absLift : @AbsLift k _ _ _ _ := by
  intro ψ hψ hψ1 m V _ _ col gl hS s B B' C A₀ hA₀ hBp hBc hBg hD hCp hCc hC hCB
  letI : MeasurableSpace k := measurableSpaceFourthLift
  haveI : BorelSpace k := borelSpaceOnK
  haveI : SecondCountableTopology k := instSCK4
  let μ : Measure (Fin (m + 1) → k) := Measure.addHaar
  have h0 : μ (perp ψ A₀) ≠ 0 := meas_perp_ne_zero ψ μ hψ hψ1 hA₀
  have htop : μ (perp ψ A₀) ≠ ⊤ := (meas_perp_lt_top ψ μ hψ hψ1 hA₀).ne
  let ν : Measure (Fin (m + 1) → k) := (μ (perp ψ A₀))⁻¹ • μ
  haveI : ν.IsAddHaarMeasure :=
    Measure.IsAddHaarMeasure.smul μ (ENNReal.inv_ne_zero.2 htop) (ENNReal.inv_ne_top.2 h0)
  have hν : ν (perp ψ A₀) = 1 := by
    simp only [ν, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.inv_mul_cancel h0 htop
  exact lift_form hψ hψ1 hS hA₀ hBp hBc hBg hD hCp hCc hC hCB hν

end PositivityTheory.RgUd.Form.U.Lift2
end
end
end
