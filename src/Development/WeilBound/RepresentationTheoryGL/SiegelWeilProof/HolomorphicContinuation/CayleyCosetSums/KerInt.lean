module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.MatInv
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.ConvPhi
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.ContinuousSecondCayleyBlockMapBis
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.MapsToUpToSign
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.RowsBlocks
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.IsCompactKSet
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.ParamCD
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
import Mathlib.Topology.Sheaves.Init
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.LocTauAlt
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.ContDiffMatrixMul

section

@[expose] public section

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt.Conv

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.HSt.GRH PositivityTheory.Rg.Sw.HSt.MI

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem contDiff_mul_M2 : ContDiff ℝ ∞ (fun p : M2 n × M2 n => p.1 * p.2) := by
  refine contDiff_of_entries fun a b => ?_
  have : (fun p : M2 n × M2 n => (p.1 * p.2) a b) = fun p => ∑ c, p.1 a c * p.2 c b := by
    funext p; rfl
  rw [this]
  exact ContDiff.sum fun c _ => ((contDiff_entry a c).comp contDiff_fst).mul ((contDiff_entry c b).comp contDiff_snd)

theorem tw_contDiff (m : ℕ) (e : ℤ) (μK : Measure (KR n)) [μK.IsHaarMeasure] {β : M2 n → ℝ}
    (hβ : ContDiff ℝ ∞ β) : ContDiff ℝ ∞ (tw m e μK β) := by
  have hk : ContDiffOn ℝ ∞ (fun p : M2 n × M2 n => ((β (p.2 * p.1) : ℝ) : ℂ)) (univ ×ˢ univ) := by
    have h1 : ContDiff ℝ ∞ (fun p : M2 n × M2 n => p.2 * p.1) := contDiff_mul_M2.comp (contDiff_snd.prodMk contDiff_fst)
    exact (Complex.ofRealCLM.contDiff.comp (hβ.comp h1)).contDiffOn
  have hv : Continuous (fun k : KR n => (mR (k : GR n))ᴴ) := continuous_kR.matrix_conjTranspose
  have hh : Continuous (fun k : KR n => (F0 m 0 e (k : GR n))⁻¹) :=
    ((Vac.continuous_weight_factor detU1 m 0 e).comp continuous_subtype_val).inv₀ fun k => Vac.spherical_section_ne_zero detU1 m 0 e _
  have := PCD.contDiffOn_integral' (F := M2 n) (X := KR n) isOpen_univ μK
    (fun p : M2 n × M2 n => ((β (p.2 * p.1) : ℝ) : ℂ)) hk (fun k : KR n => (mR (k : GR n))ᴴ) hv
    (fun k : KR n => (F0 m 0 e (k : GR n))⁻¹) hh
    (fun x _ => ⟨univ, univ_mem, univ, isCompact_univ, fun _ _ u hu => absurd (mem_univ u) hu⟩)
  rw [contDiffOn_univ] at this
  have e' : tw m e μK β = fun X => ∫ k : KR n, (F0 m 0 e (k : GR n))⁻¹ • ((β ((mR (k : GR n))ᴴ * X) : ℝ) : ℂ) ∂μK := by
    funext X; rfl
  rw [e']
  exact this

def kk (m : ℕ) (e : ℤ) (μK : Measure (KR n)) (β : M2 n → ℝ) (p : M2 n × M2 n) : ℂ := tw m e μK β (p.1⁻¹ * p.2)

theorem kk_contDiffOn (m : ℕ) (e : ℤ) (μK : Measure (KR n)) [μK.IsHaarMeasure] {β : M2 n → ℝ}
    (hβ : ContDiff ℝ ∞ β) : ContDiffOn ℝ ∞ (kk m e μK β) (Inv n ×ˢ univ) := by
  have h1 : ContDiffOn ℝ ∞ (fun p : M2 n × M2 n => (p.1⁻¹, p.2)) (Inv n ×ˢ univ) :=
    (contDiffOn_inv.comp contDiffOn_fst fun (p : M2 n × M2 n) (hp : p ∈ Inv n ×ˢ univ) => hp.1).prodMk contDiffOn_snd
  exact (tw_contDiff m e μK hβ).comp_contDiffOn (contDiff_mul_M2.comp_contDiffOn h1)

theorem kk_supp (m : ℕ) (e : ℤ) (μK : Measure (KR n)) {β : M2 n → ℝ} (hβs : HasCompactSupport β) :
    ∀ x ∈ Inv n, ∃ W ∈ 𝓝 x, ∃ C : Set (GR n), IsCompact C ∧ ∀ x' ∈ W, ∀ u ∉ C, kk m e μK β (x', mR u) = 0 := by
  intro x hx
  obtain ⟨r, hr, hrs⟩ := Metric.isOpen_iff.mp isOpen_Inv x hx
  have hFD : FiniteDimensional ℝ (M2 n) := inferInstanceAs (FiniteDimensional ℝ (Fin n ⊕ Fin n → Fin n ⊕ Fin n → ℂ))
  have hPS : ProperSpace (M2 n) := FiniteDimensional.proper ℝ (M2 n)
  set B := Metric.closedBall x (r / 2)
  have hB : IsCompact B := isCompact_closedBall x (r / 2)
  have hBI : B ⊆ Inv n := fun y hy => hrs (lt_of_le_of_lt (Metric.mem_closedBall.mp hy) (half_lt_self hr))
  set T := (fun p : M2 n × M2 n => p.1 * p.2) '' (B ×ˢ kSet (tsupport β))
  have hT : IsCompact T := (hB.prod (isCompact_kSet hβs)).image contDiff_mul_M2.continuous
  refine ⟨Metric.closedBall x (r / 2), Metric.closedBall_mem_nhds x (half_pos hr), (mR : GR n → M2 n) ⁻¹' T,
    isCompact_preimage_mR hT, fun x' hx' u hu => ?_⟩
  unfold kk
  refine tw_eq_zero m e μK β fun hmem => hu ?_
  refine ⟨(x', x'⁻¹ * mR u), ⟨hx', hmem⟩, ?_⟩
  show x' * (x'⁻¹ * mR u) = mR u
  have hdet : IsUnit x'.det := isUnit_iff_ne_zero.mpr (hBI hx')
  rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mul]

end PositivityTheory.Rg.Sw.HSt.Conv
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.DerivCurveOfHasFDerivAt

section

@[expose] public section

noncomputable section

open Matrix Set Filter Topology

namespace PositivityTheory.Rg.Sw.HSt.MI

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.HSt

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def Z1 (Z : M2 n) : M2 n := (1 / 2 : ℂ) • (Z + sig Z)

def Z2 (Z : M2 n) : M2 n := (1 / (2 * Complex.I)) • (Z - sig Z)

theorem curve_zero (x Y : M2 n) : x * NormedSpace.exp (((0 : ℝ) : ℂ) • Y) = x := by
  simp

theorem rC_eq (Z : M2 n) (F : M2 n → ℂ) (x : M2 n) :
    rC Z F x = deriv (fun t : ℝ => F (x * NormedSpace.exp ((t : ℂ) • Z1 Z))) 0 +
      Complex.I * deriv (fun t : ℝ => F (x * NormedSpace.exp ((t : ℂ) • Z2 Z))) 0 := rfl

theorem deriv_curve_of_hasFDerivAt {F : M2 n → ℂ} {D : M2 n →L[ℝ] ℂ} {x : M2 n} (hF : HasFDerivAt F D x) (Y : M2 n) :
    deriv (fun t : ℝ => F (x * NormedSpace.exp ((t : ℂ) • Y))) 0 = D (x * Y) := by
  exact (hF.comp_hasDerivAt_of_eq 0 (hasDerivAt_curve x Y) (curve_zero x Y).symm).deriv

theorem rC_of_diff {F : M2 n → ℂ} {x : M2 n} (hF : DifferentiableAt ℝ F x) (Z : M2 n) :
    rC Z F x = fderiv ℝ F x (x * Z1 Z) + Complex.I * fderiv ℝ F x (x * Z2 Z) := by
  rw [rC_eq, deriv_curve_of_hasFDerivAt hF.hasFDerivAt, deriv_curve_of_hasFDerivAt hF.hasFDerivAt]

theorem rC_congr {F F' : M2 n → ℂ} {O : Set (M2 n)} (hO : IsOpen O) {x : M2 n} (hx : x ∈ O) (h : EqOn F F' O)
    (Z : M2 n) : rC Z F x = rC Z F' x := by
  have key : ∀ Y : M2 n, deriv (fun t : ℝ => F (x * NormedSpace.exp ((t : ℂ) • Y))) 0 =
      deriv (fun t : ℝ => F' (x * NormedSpace.exp ((t : ℂ) • Y))) 0 := by
    intro Y
    apply Filter.EventuallyEq.deriv_eq
    have hc := (hasDerivAt_curve x Y).continuousAt
    have hO' : O ∈ 𝓝 (x * NormedSpace.exp (((0 : ℝ) : ℂ) • Y)) := by
      rw [curve_zero]
      exact hO.mem_nhds hx
    filter_upwards [hc.preimage_mem_nhds hO'] with t ht
    exact h ht
  rw [rC_eq, rC_eq, key, key]

end PositivityTheory.Rg.Sw.HSt.MI
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.KerInt

section

@[expose] public section

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt.Conv

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.HSt PositivityTheory.Rg.Sw.HSt.GRH PositivityTheory.Rg.Sw.HSt.MI

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section

variable (m : ℕ) (e : ℤ) (ν : Measure (GR n)) [ν.IsHaarMeasure] (μK : Measure (KR n)) [μK.IsHaarMeasure]
  {β : M2 n → ℝ} (hβ : ContDiff ℝ ∞ β) (hβs : HasCompactSupport β)

def Psi (β : M2 n → ℝ) (h : GR n → ℂ) (x : M2 n) : ℂ := ∫ u, h u • kk m e μK β (x, mR u) ∂ν

def Lk (β : M2 n → ℝ) (Z x₀ : M2 n) (u : GR n) : ℂ :=
  fderiv ℝ (fun x' => kk m e μK β (x', mR u)) x₀ (x₀ * Z1 Z) +
    Complex.I * fderiv ℝ (fun x' => kk m e μK β (x', mR u)) x₀ (x₀ * Z2 Z)

include hβ hβs in
theorem good (h : GR n → ℂ) (hh : Continuous h) :
    PCD.Good (Inv n) (fun x u => h u • kk m e μK β (x, mR u)) :=
  PCD.good_of_joint isOpen_Inv _ (kk_contDiffOn m e μK hβ) (fun u : GR n => mR u) continuous_mR h hh
    (kk_supp m e μK hβs)

include hβ hβs in
theorem psi_contDiffOn (h : GR n → ℂ) (hh : Continuous h) : ContDiffOn ℝ ∞ (Psi m e ν μK β h) (Inv n) :=
  PCD.contDiffOn_integral isOpen_Inv ν (good m e μK hβ hβs h hh)

include hβ in
theorem kk_diff {x₀ : M2 n} (hx₀ : x₀ ∈ Inv n) (u : GR n) :
    DifferentiableAt ℝ (fun x' => kk m e μK β (x', mR u)) x₀ := by
  have hsl : ContDiffOn ℝ ∞ (fun x' => kk m e μK β (x', mR u)) (Inv n) :=
    (kk_contDiffOn m e μK hβ).comp (contDiffOn_id.prodMk contDiffOn_const) fun x hx => ⟨hx, mem_univ _⟩
  exact (hsl.differentiableOn (by simp) x₀ hx₀).differentiableAt (isOpen_Inv.mem_nhds hx₀)

include hβ hβs in
theorem rC_psi (h : GR n → ℂ) (hh : Continuous h) (Z : M2 n) {x₀ : M2 n} (hx₀ : x₀ ∈ Inv n) :
    rC Z (Psi m e ν μK β h) x₀ = ∫ u, h u * Lk m e μK β Z x₀ u ∂ν := by
  have hG := good m e μK hβ hβs h hh
  have hF := hG.hasFDerivAt isOpen_Inv ν hx₀
  have hI := (hG.dK isOpen_Inv).integrable ν hx₀
  have hfd : ∀ u, fderiv ℝ (fun x => h u • kk m e μK β (x, mR u)) x₀ =
      h u • fderiv ℝ (fun x' => kk m e μK β (x', mR u)) x₀ := fun u =>
    fderiv_const_smul (kk_diff m e μK hβ hx₀ u) (h u)
  rw [show Psi m e ν μK β h = fun x => ∫ u, h u • kk m e μK β (x, mR u) ∂ν from rfl]
  rw [rC_of_diff hF.differentiableAt]
  erw [hF.fderiv, ContinuousLinearMap.integral_apply hI, ContinuousLinearMap.integral_apply hI]
  have i1 := hI.apply_continuousLinearMap (x₀ * Z1 Z)
  have i2 := hI.apply_continuousLinearMap (x₀ * Z2 Z)
  rw [← integral_const_mul, ← integral_add i1 (i2.const_mul _)]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  dsimp only
  erw [hfd u]
  change h u • (fderiv ℝ (fun x' => kk m e μK β (x', mR u)) x₀) (x₀ * Z1 Z) +
    Complex.I * (h u • (fderiv ℝ (fun x' => kk m e μK β (x', mR u)) x₀) (x₀ * Z2 Z)) = _
  simp only [Lk, smul_eq_mul]
  ring

include hβ in
theorem slice_fderiv {x₀ : M2 n} (hx₀ : x₀ ∈ Inv n) (v : M2 n) :
    fderiv ℝ (fun x' => kk m e μK β (x', v)) x₀ = (fderiv ℝ (kk m e μK β) (x₀, v)).comp (ContinuousLinearMap.inl ℝ (M2 n) (M2 n)) := by
  have hS : IsOpen (Inv n ×ˢ (univ : Set (M2 n))) := isOpen_Inv.prod isOpen_univ
  have hd : DifferentiableAt ℝ (kk m e μK β) (x₀, v) :=
    ((kk_contDiffOn m e μK hβ).differentiableOn (by simp) _ ⟨hx₀, mem_univ _⟩).differentiableAt
      (hS.mem_nhds ⟨hx₀, mem_univ _⟩)
  have hi : HasFDerivAt (fun x' : M2 n => (x', v)) (ContinuousLinearMap.inl ℝ (M2 n) (M2 n)) x₀ :=
    (hasFDerivAt_id x₀).prodMk (hasFDerivAt_const v x₀)
  exact (hd.hasFDerivAt.comp x₀ hi).fderiv

include hβ in
theorem Lk_cont (Z : M2 n) {x₀ : M2 n} (hx₀ : x₀ ∈ Inv n) : Continuous (Lk m e μK β Z x₀) := by
  have hS : IsOpen (Inv n ×ˢ (univ : Set (M2 n))) := isOpen_Inv.prod isOpen_univ
  have hc : ContinuousOn (fun p => fderiv ℝ (kk m e μK β) p) (Inv n ×ˢ univ) :=
    (kk_contDiffOn m e μK hβ).continuousOn_fderiv_of_isOpen hS (by simp)
  have hc' : Continuous fun u : GR n => fderiv ℝ (kk m e μK β) (x₀, mR u) :=
    hc.comp_continuous (continuous_const.prodMk continuous_mR) fun u => ⟨hx₀, mem_univ _⟩
  have e1 : Lk m e μK β Z x₀ = fun u => fderiv ℝ (kk m e μK β) (x₀, mR u) (ContinuousLinearMap.inl ℝ (M2 n) (M2 n) (x₀ * Z1 Z)) +
      Complex.I * fderiv ℝ (kk m e μK β) (x₀, mR u) (ContinuousLinearMap.inl ℝ (M2 n) (M2 n) (x₀ * Z2 Z)) := by
    funext u
    simp only [Lk, slice_fderiv m e μK hβ hx₀, ContinuousLinearMap.comp_apply]
  rw [e1]
  exact (hc'.clm_apply continuous_const).add (continuous_const.mul (hc'.clm_apply continuous_const))

omit [μK.IsHaarMeasure] in
include hβs in
theorem Lk_zero (Z : M2 n) {x₀ : M2 n} (hx₀ : x₀ ∈ Inv n) :
    ∃ C : Set (GR n), IsCompact C ∧ ∀ u ∉ C, Lk m e μK β Z x₀ u = 0 := by
  obtain ⟨W, hW, C, hC, hz⟩ := kk_supp m e μK hβs x₀ hx₀
  refine ⟨C, hC, fun u hu => ?_⟩
  have h0 : (fun x' => kk m e μK β (x', mR u)) =ᶠ[𝓝 x₀] fun _ => 0 := by
    filter_upwards [hW] with x' hx' using hz x' hx' u hu
  simp [Lk, h0.fderiv_eq]

end

end PositivityTheory.Rg.Sw.HSt.Conv
end
end
end
