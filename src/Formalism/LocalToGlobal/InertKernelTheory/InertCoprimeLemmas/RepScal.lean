module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.KernelLattices.XiIndCClass
public import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.DescentCore

-- Source module: Formalism.LocalToGlobal.PairingIndexBounds.PendingAdmissibility.LocalFDerivAdmissibility.IteratedFDerivConstSmul

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions

namespace Formalism.L2.PairingIndexBounds.PowerSeriesNecessity

theorem iteratedFDeriv_const_smul' {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
    [NormedSpace ℂ F] (c : ℂ) (hc : c ≠ 0) (f : E → F) (n : ℕ) :
    iteratedFDeriv ℂ n (fun y => c • f y) = c • iteratedFDeriv ℂ n f := by
  let _ : Invertible c := invertibleOfNonzero hc
  induction n with
  | zero =>
    ext x m
    simp [iteratedFDeriv_zero_apply]
  | succ n ih =>
    rw [iteratedFDeriv_succ_eq_comp_left, iteratedFDeriv_succ_eq_comp_left, ih]
    funext x
    simp only [Function.comp_apply]
    rw [fderiv_const_smul_of_invertible c, map_smul]
    rfl

theorem taylor_const_mul (D : D7) {N N' : ℕ} (s : ℂ) (hs : s ≠ 0) (G : TaylorLogMetric.VC D N N' → ℂ) (α : TaylorLogMetric.Mono D N N') :
    TaylorLogMetric.taylor D (fun z => s * G z) α = s * TaylorLogMetric.taylor D G α := by
  unfold TaylorLogMetric.taylor
  have h := iteratedFDeriv_const_smul' s hs G (Multiset.card α.toMultiset)
  simp only [smul_eq_mul] at h
  rw [h, Pi.smul_apply, ContinuousMultilinearMap.smul_apply, smul_eq_mul, mul_div_assoc]

theorem lamC_mul {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) {s : ℂ} (hs : s ∈ TaylorLogMetric.Qbar) (hs0 : s ≠ 0) (t : ℂ) :
    TaylorLogMetric.lamC lam (s * t) = TaylorLogMetric.lamC lam s * TaylorLogMetric.lamC lam t := by
  unfold TaylorLogMetric.lamC
  by_cases ht : t ∈ TaylorLogMetric.Qbar
  · have hst : s * t ∈ TaylorLogMetric.Qbar := TaylorLogMetric.Qbar.mul_mem hs ht
    rw [dite_eq_left hst, dite_eq_left hs, dite_eq_left ht, ← map_mul]
    rfl
  · have hst : s * t ∉ TaylorLogMetric.Qbar := by
      intro h
      apply ht
      have : s⁻¹ * (s * t) ∈ TaylorLogMetric.Qbar := TaylorLogMetric.Qbar.mul_mem (TaylorLogMetric.Qbar.inv_mem hs) h
      rwa [← mul_assoc, inv_mul_cancel₀ hs0, one_mul] at this
    rw [dite_eq_right hst, dite_eq_right ht, mul_zero]

theorem pSer_const_mul (D : D7) {N N' p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) {s : ℂ} (hs : s ∈ TaylorLogMetric.Qbar)
    (G : TaylorLogMetric.VC D N N' → ℂ) :
    TaylorLogMetric.pSer D lam (fun z => s * G z) = MvPowerSeries.C (TaylorLogMetric.lamC lam s) * TaylorLogMetric.pSer D lam G := by
  by_cases hs0 : s = 0
  · subst hs0
    ext α
    rw [MvPowerSeries.coeff_C_mul]
    have h0 : TaylorLogMetric.lamC lam 0 = 0 := by
      unfold TaylorLogMetric.lamC
      rw [dite_eq_left (TaylorLogMetric.Qbar.zero_mem)]
      exact map_zero lam
    show TaylorLogMetric.lamC lam (TaylorLogMetric.taylor D (fun z => 0 * G z) α) = _
    simp only [zero_mul]
    rw [h0, zero_mul]
    have : TaylorLogMetric.taylor D (fun _ : TaylorLogMetric.VC D N N' => (0 : ℂ)) α = 0 := by
      unfold TaylorLogMetric.taylor
      simp
    rw [this, h0]
  · ext α
    rw [MvPowerSeries.coeff_C_mul]
    show TaylorLogMetric.lamC lam (TaylorLogMetric.taylor D (fun z => s * G z) α) = TaylorLogMetric.lamC lam s * TaylorLogMetric.lamC lam (TaylorLogMetric.taylor D G α)
    rw [taylor_const_mul D s hs0 G α, lamC_mul lam hs hs0]

end Formalism.L2.PairingIndexBounds.PowerSeriesNecessity
end
end
end

-- Source module: Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.RepScal

section

@[expose] public section

noncomputable section

namespace Formalism.L2.KerInert.Rep

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker
open Formalism.MainNotions.FormalGroupSystem (Sys)

theorem isComb_smul (D : D7) (T : Tor D) (e : FamE D) {N N' p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p])
    {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    {F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]} (h : IsComb D T e lam L L' F) {c : ℂ_[p]}
    (hc : ‖c‖ ≤ 1) : IsComb D T e lam L L' (c • F) := by
  obtain ⟨m, r, t, L₁, L₁', hr, ht, hL, rfl⟩ := h
  refine ⟨m, fun k => c * r k, t, L₁, L₁', fun k => ?_, ht, hL, ?_⟩
  · have := hr k
    simp only [IsIntP] at this ⊢
    rw [norm_mul]
    exact mul_le_one₀ hc (norm_nonneg _) this
  · rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Algebra.smul_def, map_mul, mul_assoc]

theorem isComb_scalar (D : D7) (T : Tor D) (e : FamE D) {N N' p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p])
    {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (G : VC D N N' → ℂ) (h : IsComb D T e lam L L' (pSer D lam G)) {s : ℂ} (hs : s ∈ Qbar) (k : ℤ)
    (hk : ‖(p : ℂ_[p]) ^ k * lamC lam s‖ ≤ 1) :
    IsComb D T e lam L L' (((p : ℂ_[p]) ^ k) • pSer D lam (fun z => s * G z)) := by
  have e1 : ((p : ℂ_[p]) ^ k) • pSer D lam (fun z => s * G z) = ((p : ℂ_[p]) ^ k * lamC lam s) • pSer D lam G := by
    rw [Formalism.L2.PairingIndexBounds.PowerSeriesNecessity.pSer_const_mul D lam hs, Algebra.smul_def, Algebra.smul_def, map_mul, mul_assoc]
    rfl
  rw [e1]
  exact isComb_smul D T e lam h hk

end Formalism.L2.KerInert.Rep
end
end
end
