module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HasMultiplierLine
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelSummationBoundStatement
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.JoinCoordsUnitValues
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
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.JoinModelPointsProjectStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjugateHermitianLineIsometries
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HasMultiplier
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PotentialBoundedPshBothStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootModelFlagCompareStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginCompareFirstStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginCompareSecondStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginCompareThirdStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginPointCompareStatement
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Linter.Style
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.JoinCoordsUnitValuesStatement

section

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht

theorem _root_.GlobalTheory.T.join_coords_unit_values : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (M R : Top.RootModel Ψ N) (i : R.Ω →+* M.Ω) (u : Option (Ψ × Fin N) → M.Ω) (t : ℝ) (lam : Top.Wt Ψ N) (s lo hi : ℝ) (f : MRing (Cmp.joinIdx M.ι R.ι)), f ∉ mCoordIdeal (Ht.joinOf M R i) → (∀ j, Ht.GenUnit (Ht.joinOf M R i) (Ht.joinDeg M R j) (u j)) → (∀ w ∈ Small.ptsOver ℂ (mCoordIdeal (Ht.joinOf M R i)), Cmp.evC w f ≠ 0 → ∀ val : Option (Ψ × Fin N) → ℂ, (∀ j, Small.HasVal (Ht.joinOf M R i) (Ht.joinDeg M R j) (u j) w (val j)) → ∑ j, M.coef lam s j * (Real.log ((M.line t j).h (fun p => w (Cmp.joinInl M.ι R.ι p))) - Real.log ((R.line 1 j).h (fun p => w (Cmp.joinInr M.ι R.ι p))) - Real.log ‖val j‖) ∈ Set.Icc lo hi) → Ht.ArchBetween M R i u t lam s lo hi := by
  first | exact @GlobalTheory.CompanionTheory.Ar.OrArch.Ext.archBetween_of_off_form | exact GlobalTheory.CompanionTheory.Ar.OrArch.Ext.archBetween_of_off_form | (intros; apply GlobalTheory.CompanionTheory.Ar.OrArch.Ext.archBetween_of_off_form <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogHermitianSumBounded

section

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht

namespace GlobalTheory.CompanionTheory.Ar.CancelBound

theorem log_h_scale {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (A : HermLine ι) (c : K → ℂ)
    (z : (Σ k, ι k) → ℂ) (hc : ∀ k, c k ≠ 0) (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    Real.log (A.h fun p => c p.1 * z p) = (∑ k, (A.a k : ℝ) * Real.log ‖c k‖) + Real.log (A.h z) := by
  have hne : ∀ k, ‖c k‖ ^ A.a k ≠ 0 := fun k => zpow_ne_zero _ (norm_ne_zero_iff.mpr (hc k))
  rw [A.smul c z hc, Real.log_mul (Finset.prod_ne_zero_iff.mpr fun k _ => hne k) (A.pos z hz).ne',
    Real.log_prod (fun k _ => hne k)]
  congr 1
  exact Finset.sum_congr rfl fun k _ => Real.log_zpow _ _

theorem continuousOn_log_h {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (A : HermLine ι)
    (hA : IsSmoothHerm A) :
    ContinuousOn (fun z => Real.log (A.h z)) {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} :=
  ContinuousOn.log (ContDiffOn.continuousOn hA) fun z hz => (A.pos z hz).ne'

theorem log_metrics_bounded (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (J : Type) (A : HermLine ι)
    (B : J → HermLine ι) (T : Finset J) (hA : IsSmoothHerm A) (hB : ∀ j, IsSmoothHerm (B j))
    (hdeg : A.a = -∑ j ∈ T, (B j).a) :
    ∃ C : ℝ, ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ a, z ⟨k, a⟩ ≠ 0) →
      |Real.log (A.h z) + ∑ j ∈ T, Real.log ((B j).h z)| ≤ C := by
  classical
  let f : ((Σ k, ι k) → ℂ) → ℝ := fun z => Real.log (A.h z) + ∑ j ∈ T, Real.log ((B j).h z)
  let n : K → ((Σ k, ι k) → ℂ) → ℝ := fun k z => ∑ i, ‖z ⟨k, i⟩‖
  let S : Set ((Σ k, ι k) → ℂ) := {z | ∀ k, n k z = 1}
  have hcn : ∀ k, Continuous (n k) := fun k =>
    continuous_finsetSum _ fun i _ => (continuous_apply _).norm
  have hnpos : ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∀ k, 0 < n k z := by
    intro z hz k
    obtain ⟨i, hi⟩ := hz k
    exact Finset.sum_pos' (fun _ _ => norm_nonneg _) ⟨i, Finset.mem_univ _, norm_pos_iff.mpr hi⟩
  have hSU : S ⊆ {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
    intro z hz k
    by_contra hcon
    push Not at hcon
    have h0 : n k z = 0 := Finset.sum_eq_zero fun i _ => by simp [hcon i]
    have h1 : n k z = 1 := hz k
    rw [h0] at h1
    exact zero_ne_one h1
  have hScl : IsClosed S := by
    have hS : S = ⋂ k, {z | n k z = 1} := by
      ext z
      simp [S]
    rw [hS]
    exact isClosed_iInter fun k => isClosed_eq (hcn k) continuous_const
  have hSb : Bornology.IsBounded S := by
    refine (Metric.isBounded_closedBall (x := (0 : (Σ k, ι k) → ℂ)) (r := 1)).subset ?_
    intro z hz
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    rintro ⟨k, i⟩
    calc ‖z ⟨k, i⟩‖ ≤ n k z :=
          Finset.single_le_sum (f := fun i => ‖z ⟨k, i⟩‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i)
      _ = 1 := hz k
  have hScpt : IsCompact S := Metric.isCompact_of_isClosed_isBounded hScl hSb
  have hfc : ContinuousOn f S := by
    refine ContinuousOn.mono ?_ hSU
    exact (continuousOn_log_h A hA).add
      (continuousOn_finsetSum _ fun j _ => continuousOn_log_h (B j) (hB j))
  obtain ⟨C, hC⟩ := hScpt.exists_bound_of_continuousOn hfc
  refine ⟨C, fun z hz => ?_⟩
  let c : K → ℂ := fun k => (((n k z)⁻¹ : ℝ) : ℂ)
  let w : (Σ k, ι k) → ℂ := fun p => c p.1 * z p
  have hc : ∀ k, c k ≠ 0 := fun k =>
    Complex.ofReal_ne_zero.mpr (inv_ne_zero (hnpos z hz k).ne')
  have hwS : w ∈ S := by
    intro k
    have hn := (hnpos z hz k).ne'
    have hterm : ∀ i, ‖w ⟨k, i⟩‖ = (n k z)⁻¹ * ‖z ⟨k, i⟩‖ := by
      intro i
      simp only [w, c, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_pos (inv_pos.mpr (hnpos z hz k))]
    change ∑ i, ‖w ⟨k, i⟩‖ = 1
    simp only [hterm]
    rw [← Finset.mul_sum]
    exact inv_mul_cancel₀ hn
  have hdegk : ∀ k, (A.a k : ℝ) + ∑ j ∈ T, ((B j).a k : ℝ) = 0 := by
    intro k
    have hk : A.a k = -∑ j ∈ T, (B j).a k := by
      rw [hdeg]
      simp [Finset.sum_apply]
    rw [hk]
    push_cast
    ring
  have hfw : f w = f z := by
    simp only [f, w]
    rw [log_h_scale A c z hc hz,
      Finset.sum_congr rfl fun j _ => log_h_scale (B j) c z hc hz, Finset.sum_add_distrib,
      Finset.sum_comm]
    have hz0 : (∑ k, (A.a k : ℝ) * Real.log ‖c k‖) + ∑ k, ∑ j ∈ T, ((B j).a k : ℝ) * Real.log ‖c k‖ = 0 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [← Finset.sum_mul, ← add_mul, hdegk k, zero_mul]
    linarith
  have hb := hC w hwS
  rwa [hfw, Real.norm_eq_abs] at hb

end GlobalTheory.CompanionTheory.Ar.CancelBound
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogHermitianSumBoundedStatement

section

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht

theorem _root_.GlobalTheory.T.log_hermitian_sum_bounded : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (J : Type) (A : HermLine ι) (B : J → HermLine ι) (T : Finset J), IsSmoothHerm A → (∀ j, IsSmoothHerm (B j)) → A.a = -∑ j ∈ T, (B j).a → ∃ C : ℝ, ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ a, z ⟨k, a⟩ ≠ 0) → |Real.log (A.h z) + ∑ j ∈ T, Real.log ((B j).h z)| ≤ C := by
  first | exact @GlobalTheory.CompanionTheory.Ar.CancelBound.log_metrics_bounded | exact GlobalTheory.CompanionTheory.Ar.CancelBound.log_metrics_bounded | (intros; apply GlobalTheory.CompanionTheory.Ar.CancelBound.log_metrics_bounded <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootTowerUniformHeightBound

section

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.OrArch

theorem scale_facts {t₀ : ℝ} (h0 : 0 < t₀) (h1 : t₀ < 1) {s : ℝ} (hs : 0 < s)
    (hs' : s ≤ Real.sqrt (1 / Real.log (1 / t₀))) :
    0 < Top.scale s ∧ Top.scale s ≤ t₀ ∧ Real.log (Real.log (1 / Top.scale s)) = 2 * Real.log (1 / s) := by
  have hL : 0 < Real.log (1 / t₀) := Real.log_pos (by rw [lt_div_iff₀ h0]; linarith)
  have hs2 : 0 < s ^ 2 := by positivity
  have e1 : Real.log (1 / Top.scale s) = (s ^ 2)⁻¹ := by
    rw [Top.scale, one_div, Real.log_inv, Real.log_exp, neg_neg]
  refine ⟨Real.exp_pos _, ?_, ?_⟩
  · have hsq : s ^ 2 ≤ 1 / Real.log (1 / t₀) := by
      have := Real.sq_sqrt (show 0 ≤ 1 / Real.log (1 / t₀) by positivity)
      nlinarith [Real.sqrt_nonneg (1 / Real.log (1 / t₀))]
    have hinv : Real.log (1 / t₀) ≤ (s ^ 2)⁻¹ := by
      rw [le_inv_comm₀ hL hs2]
      simpa using hsq
    have : Real.log t₀ = -Real.log (1 / t₀) := by rw [one_div, Real.log_inv, neg_neg]
    rw [Top.scale, ← Real.exp_log h0, this]
    exact Real.exp_le_exp.2 (by linarith)
  · rw [e1, Real.log_inv, Real.log_pow, one_div, Real.log_inv]
    push_cast
    ring

theorem comp_bound (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H)
    (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (S₀ : Finset ℕ)
    (R : Top.RootModel (CMType H) (D.p + D.q))
    (Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys)
    (o₀ : RootOrigin Y S₀ R Fx) (hJ₀ : o₀.Re.J = ⊤)
    (hflat : ∀ (τ : CMType H) (p : Fin (D.p + D.q)), (p : ℕ) + 1 = D.p + D.q → ∀ t,
      ReciprocityTheory.AnForm.M.IsPsh Sys.A ((Sys.potT (some (τ, p)) t).rsmul (-1)) ∧
        ReciprocityTheory.AnForm.M.IsPsh Sys.A (Sys.potT (some (τ, p)) t)) :
    ∃ C s₀ : ℝ, 0 ≤ C ∧ 0 < s₀ ∧ s₀ ≤ 1 ∧ ∀ (S : Finset ℕ) (M : Top.RootModel (CMType H) (D.p + D.q))
      (o : RootOrigin Y S M Fx) (i : R.Ω →+* M.Ω), o.Re.J = ⊤ → i.comp o₀.g = o.g →
      ∀ (mu : Top.Wt (CMType H) (D.p + D.q)) (s : ℝ), Top.Dominant mu → ‖mu‖ ≤ 2 → 0 < s → s ≤ s₀ →
        Ht.ArchBetween M R i (fun j => j.elim 1 fun r => i (o₀.e r) / o.e r) (Top.scale s) mu s
          (-(C * Real.log (1 / s)) - C) C := by
  classical

  have hb : ∀ r : RootIx D, ∃ Cr : ℝ, ∀ z : (Σ k, R.ι k) → ℂ, (∀ k, ∃ a, z ⟨k, a⟩ ≠ 0) →
      |Real.log ((o₀.Re.ref (some r)).h z) + ∑ k ∈ Finset.Iic r.2, Real.log ((R.x 1 (r.1, k)).h z)| ≤ Cr := by
    rintro ⟨τ, p⟩
    refine GlobalTheory.T.log_hermitian_sum_bounded R.K R.ι (Fin (D.p + D.q)) (o₀.Re.ref (some (τ, p))) (fun k => R.x 1 (τ, k)) (Finset.Iic p)
      (o₀.Re.ref_smooth _) (fun k => R.x_smooth _ _) ?_
    rw [o₀.fund_deg]
    simp only [R.x_deg]
  choose Cb hCb using hb
  obtain ⟨B₁, hB₁⟩ := Finite.exists_le Cb
  have hc : ∀ r : RootIx D, ∃ Cr : ℝ, (r.2 : ℕ) + 1 = D.p + D.q → ∀ t, 0 < t → t ≤ Sys.t₀ → ∀ x,
      |Sys.phT (some r) t x| ≤ Cr := by
    rintro ⟨τ, p⟩
    by_cases hp : (p : ℕ) + 1 = D.p + D.q
    · obtain ⟨C, hC⟩ := GlobalTheory.T.potential_bounded_psh_both _ _ Sys (some (τ, p)) (hflat τ p hp)
      exact ⟨C, fun _ => hC⟩
    · exact ⟨0, fun h => absurd h hp⟩
  choose Cc hCc using hc
  obtain ⟨C₁, hC₁⟩ := Finite.exists_le Cc
  have ht₀ := (Sys.reg none).1
  have ht₁ := (Sys.reg none).2.1
  set Creg := |Sys.C| with hCreg
  set B₀ := max B₁ 0 with hB₀
  set C₀ := max C₁ 0 with hC₀
  set F : ℝ := (Fintype.card (CMType H) : ℝ) with hF
  have hF0 : 0 ≤ F := Nat.cast_nonneg _
  have hCreg0 : 0 ≤ Creg := abs_nonneg _
  have hB0 : 0 ≤ B₀ := le_max_right _ _
  have hC00 : 0 ≤ C₀ := le_max_right _ _
  refine ⟨F * (8 * Creg + 6 * B₀ + 2 * C₀), min 1 (Real.sqrt (1 / Real.log (1 / Sys.t₀))), by positivity,
    lt_min one_pos (Real.sqrt_pos.2 (one_div_pos.2 (Real.log_pos (by rw [lt_div_iff₀ ht₀]; linarith)))),
    min_le_left _ _, ?_⟩
  intro S M o i hJ hi mu s hmu hmu2 hs hs'
  obtain ⟨hs1, hst⟩ := le_min_iff.1 hs'
  obtain ⟨hsc0, hsct, hsll⟩ := scale_facts ht₀ ht₁ hs hst
  have hlog : 0 ≤ Real.log (1 / s) := Real.log_nonneg (by rw [le_div_iff₀ hs]; linarith)
  obtain ⟨f, hf, hfp⟩ := GlobalTheory.T.root_origin_compare_second E H D l Xo c Y S S₀ M R Sys Fx o o₀ i hi hJ hJ₀
  have hG := (GlobalTheory.T.root_origin_compare_third E H D l Xo c Y S S₀ M R Sys Fx o o₀ i hi)
  have hunit : ∀ j, Ht.GenUnit (Ht.joinOf M R i) (Ht.joinDeg M R j)
      ((fun j => j.elim 1 fun r => i (o₀.e r) / o.e r : Option (RootIx D) → M.Ω) j) := by
    rintro (_ | r)
    · exact hG.1
    · refine GlobalTheory.T.root_model_flag_compare E H D l Xo c Y S S₀ M R o.𝔐 o₀.𝔐 o.Fl o₀.Fl i o.e o₀.e ?_ ?_ o.lines o₀.lines r
      · rw [o.g_over, o₀.g_over, ← hi, ← Category.assoc, ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp]
      · intro s' k
        have hd : dualMap o.g = (dualMap i).comp (dualMap o₀.g) := by
          rw [← hi]
          ext a <;> simp [dualMap]
        rw [o.g_flag, o₀.g_flag, hd, ← Category.assoc, ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp]
  refine GlobalTheory.T.join_coords_unit_values _ _ M R i _ _ mu s _ _ f hf hunit ?_
  intro w hw hwf val hval
  obtain ⟨x, x', z₁, z₂, ho₁, ho₂, hπ, hop, hc₁, hc₂, hi₁, hi₂⟩ := hfp w hw hwf
  obtain ⟨hw₁, hw₂⟩ := (GlobalTheory.T.join_model_points_project _ _ M R i).2.2.1 ℂ w hw
  have hw₁' : (fun p => w (Cmp.joinInl M.ι R.ι p)) ∈ mcPts M.P := by
    rw [← Small.LineModel.ptsOver_complex]; exact hw₁
  have hw₂' : (fun p => w (Cmp.joinInr M.ι R.ι p)) ∈ mcPts R.P := by
    rw [← Small.LineModel.ptsOver_complex]; exact hw₂
  set w₁ := fun p => w (Cmp.joinInl M.ι R.ι p) with hw₁d
  set w₂ := fun p => w (Cmp.joinInr M.ι R.ι p) with hw₂d
  have hsing : ∀ r, ‖val (some r)‖ * (o₀.sing r).h w₂ = (o.sing r).h w₁ := fun r =>
    GlobalTheory.T.root_origin_compare_first E H D l Xo c Y S S₀ M R Sys Fx o o₀ i hi z₁ z₂ w hw hc₁ hc₂ hi₁ hi₂ r _ (hval (some r))
  have hpos : ∀ r, 0 < ‖val (some r)‖ := fun r => by
    have h1 := (o.sing r).pos w₁ hw₁'.1
    have h2 := (o₀.sing r).pos w₂ hw₂'.1
    rw [← hsing r] at h1
    exact (mul_pos_iff_of_pos_right h2).1 h1
  have hid := GlobalTheory.T.root_origin_point_compare E H D l Xo c Y S S₀ M R Sys Fx o o₀ x x' w₁ w₂ (fun r => ‖val (some r)‖) (Top.scale s) hsc0 hsct hw₁'
    hw₂' ho₁ ho₂ hπ hop fun r => ⟨hpos r, hsing r⟩

  have hA : Real.log (M.A.h w₁) - Real.log (R.A.h w₂) - Real.log ‖val none‖ = 0 := by
    have h1 := hG.2 w hw _ (hval none)
    have hp1 := M.A.pos w₁ hw₁'.1
    have hp2 := R.A.pos w₂ hw₂'.1
    have hv : 0 < ‖val none‖ := by
      rw [h1] at hp1
      exact (mul_pos_iff_of_pos_right hp2).1 hp1
    rw [h1, Real.log_mul hv.ne' hp2.ne']
    ring
  set Dd : RootIx D → ℝ := fun r => Real.log ((M.x (Top.scale s) r).h w₁) - Real.log ((R.x 1 r).h w₂) -
    Real.log ‖val (some r)‖ with hDd
  have hsum : ∑ j, M.coef mu s j * (Real.log ((M.line (Top.scale s) j).h w₁) - Real.log ((R.line 1 j).h w₂) -
      Real.log ‖val j‖) = ∑ τ, ∑ p, -mu τ p * Dd (τ, p) := by
    rw [Fintype.sum_option, Fintype.sum_prod_type]
    have : M.coef mu s none * (Real.log ((M.line (Top.scale s) none).h w₁) - Real.log ((R.line 1 none).h w₂) -
        Real.log ‖val none‖) = 0 := by
      show _ * (Real.log (M.A.h w₁) - Real.log (R.A.h w₂) - Real.log ‖val none‖) = 0
      rw [hA, mul_zero]
    rw [this, zero_add]
    rfl
  have hτ : ∀ τ : CMType H, -(4 * (2 * Creg * Real.log (1 / s) + B₀) + 2 * (C₀ + B₀)) ≤ ∑ p, -mu τ p * Dd (τ, p) ∧
      ∑ p, -mu τ p * Dd (τ, p) ≤ 4 * (Creg + B₀) + 2 * (C₀ + B₀) := by
    intro τ
    have hbr : ∀ p : Fin (D.p + D.q), |Real.log ((o₀.Re.ref (some (τ, p))).h w₂) +
        ∑ k ∈ Finset.Iic p, Real.log ((R.x 1 (τ, k)).h w₂)| ≤ B₀ := fun p =>
      ((hCb (τ, p) w₂ hw₂'.1).trans (hB₁ _)).trans (le_max_left _ _)
    have hY : ∀ p : Fin (D.p + D.q), -∑ k ∈ Finset.Iic p, Dd (τ, k) =
        Sys.phT (some (τ, p)) (Top.scale s) (o.Re.π x) + (Real.log ((o₀.Re.ref (some (τ, p))).h w₂) +
          ∑ k ∈ Finset.Iic p, Real.log ((R.x 1 (τ, k)).h w₂)) := fun p => hid τ p
    refine GlobalTheory.T.abel_summation_bound _ (mu τ) (fun p => Dd (τ, p)) (Creg + B₀) (2 * Creg * Real.log (1 / s) + B₀) (C₀ + B₀)
      (by positivity) (by positivity) (by positivity) (hmu τ) (fun p => ?_) (fun p _ => ?_) (fun p hp => ?_)
    · have := ((norm_le_pi_norm (mu τ) p).trans (norm_le_pi_norm mu τ)).trans hmu2
      simpa [Real.norm_eq_abs] using this
    · obtain ⟨-, hup, -, hlow, -⟩ := (Sys.reg (some (τ, p))).2.2 _ hsc0 hsct
      have h1 := hup (o.Re.π x)
      have h2 := hlow (o.Re.π x)
      rw [hsll] at h2
      have h3 := abs_le.1 (hbr p)
      have h4 := le_abs_self Sys.C
      rw [hY p]
      constructor
      · nlinarith [mul_nonneg (sub_nonneg.2 h4) hlog]
      · linarith
    · have h1 := (hCc (τ, p) hp _ hsc0 hsct (o.Re.π x)).trans ((hC₁ _).trans (le_max_left C₁ 0))
      rw [← abs_neg, hY p]
      exact (abs_add_le _ _).trans (add_le_add h1 (hbr p))
  rw [hsum]
  constructor
  · have := Finset.sum_le_sum fun τ (_ : τ ∈ Finset.univ) => (hτ τ).1
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at this
    rw [← hF] at this
    nlinarith [this, mul_nonneg hF0 (mul_nonneg hB0 hlog), mul_nonneg hF0 (mul_nonneg hC00 hlog), mul_nonneg hF0 hCreg0]
  · have := Finset.sum_le_sum fun τ (_ : τ ∈ Finset.univ) => (hτ τ).2
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at this
    rw [← hF] at this
    nlinarith [this, mul_nonneg hF0 hCreg0]

theorem arch_between : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (D.p + D.q)) (g : Top.GoodOrigin Y T), ∃ C s₀ : ℝ, 0 < s₀ ∧ ∀ (B : ℕ) (a : T.Comp) (i : (g.R a).Ω →+* (T.M B a).Ω), i.comp (g.refOr a).g = (g.Or B a).g → ∀ (mu : Top.Wt (CMType H) (D.p + D.q)) (s : ℝ), Top.Dominant mu → ‖mu‖ ≤ 2 → 0 < s → s ≤ s₀ → Ht.ArchBetween (T.M B a) (g.R a) i (fun j => j.elim 1 fun r => i ((g.refOr a).e r) / (g.Or B a).e r) (Top.scale s) mu s (-(C * Real.log (1 / s)) - C) C := by
  intro E _ _ _ H D l Xo c Y _ T g
  have hcomp := fun a : T.Comp => comp_bound E H D l Xo c Y ∅ (g.R a) (g.Sys a) (g.Fx a) (g.refOr a) (g.ref_top a)
    (fun τ p hp t => g.flat a τ p hp t)
  choose C s₀ hC0 hs₀ hs₁ hmain using hcomp
  obtain ⟨a₀, -, ha₀⟩ := Finset.exists_min_image Finset.univ s₀ ⟨Classical.arbitrary _, Finset.mem_univ _⟩
  refine ⟨∑ a, C a, s₀ a₀, hs₀ a₀, ?_⟩
  intro B a i hi mu s hmu hmu2 hs hs' z hz val hval
  have hCa : C a ≤ ∑ a, C a := Finset.single_le_sum (fun a _ => hC0 a) (Finset.mem_univ a)
  have hsa : s ≤ s₀ a := hs'.trans (ha₀ a (Finset.mem_univ a))
  have hlog : 0 ≤ Real.log (1 / s) :=
    Real.log_nonneg (by rw [le_div_iff₀ hs]; linarith [hs₁ a])
  have := hmain a _ _ (g.Or B a) i (g.smooth B a).1 hi mu s hmu hmu2 hs hsa z hz val hval
  obtain ⟨h1, h2⟩ := this
  exact ⟨by nlinarith [mul_le_mul_of_nonneg_right hCa hlog], by linarith⟩

end GlobalTheory.CompanionTheory.Ar.OrArch
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootTowerUniformHeightBoundStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.root_tower_uniform_height_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (D.p + D.q)) (g : Top.GoodOrigin Y T), ∃ C s₀ : ℝ, 0 < s₀ ∧ ∀ (B : ℕ) (a : T.Comp) (i : (g.R a).Ω →+* (T.M B a).Ω), i.comp (g.refOr a).g = (g.Or B a).g → ∀ (mu : Top.Wt (CMType H) (D.p + D.q)) (s : ℝ), Top.Dominant mu → ‖mu‖ ≤ 2 → 0 < s → s ≤ s₀ → Ht.ArchBetween (T.M B a) (g.R a) i (fun j => j.elim 1 fun r => i ((g.refOr a).e r) / (g.Or B a).e r) (Top.scale s) mu s (-(C * Real.log (1 / s)) - C) C := by
  first | exact @GlobalTheory.CompanionTheory.Ar.OrArch.arch_between | exact GlobalTheory.CompanionTheory.Ar.OrArch.arch_between | (intros; apply GlobalTheory.CompanionTheory.Ar.OrArch.arch_between <;> assumption)
end
end
