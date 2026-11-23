module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.BasePsiLeviLowerBound
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TorusAtData
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsGeneratorsLattice
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FirstMinimumSqMulIInfHeightLeCard
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LevelTupleSumEqRational
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.PointwiseNormCanonicalThetaEqSqThetaConstant
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.L2DbarEstimates.LeviForms.LogNormSq
import ReciprocityTheory.L2DbarEstimates.LeviForms.OfRealNormSqSumMul
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.AApproxA
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.AApproxC
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.DerivDerivNonposOfIsLocalMax
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustFStatementPfD
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfE
public import ReciprocityTheory.L2DbarEstimates.LeviForms.EventuallyDifferentiableAtOfContDiffAt
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.NormalisedThetaNormInvariant
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MajLactRmul
import Mathlib.Analysis.InnerProductSpace.Calculus
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.HoloSmooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MaximumBoundField
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthogonalFrameDomain
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.TorusAtExists

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LeviLogThetaSum

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst
open scoped ContDiff

namespace GlobalTheory.ThetaSumLevi

open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y Topology Filter

theorem levi_lower {n : ℕ} {ι : Type} (s : Finset ι) {g : ι → V n → ℂ} {D : V n → ℂ}
    {φ : V n → ℝ} {z : V n} (c d : ℝ) (hg : ∀ t, ContDiffAt ℂ 2 (g t) z) (hD : ContDiffAt ℂ 2 D z)
    (hD0 : D z ≠ 0) (hφ : ContDiffAt ℝ 2 φ z) (hpos : 0 < ∑ t ∈ s, Complex.normSq (g t z))
    (ξ : Fin n → ℂ) :
    -(c * (leviV n (fun w => ((φ w : ℝ) : ℂ)) z ξ).re) ≤
      (leviV n (fun w => ((Real.log (∑ t ∈ s, Complex.normSq (g t w)) +
        ((c * Real.log (Complex.normSq (D w)) + d) + (-c) * φ w) : ℝ) : ℂ)) z ξ).re := by
  have hS : ContDiffAt ℝ 2 (fun w => Real.log (∑ t ∈ s, Complex.normSq (g t w))) z :=
    (ContDiffAt.sum fun t _ => contDiffAt_normSq_comp (hg t)).log hpos.ne'
  have hL : ContDiffAt ℝ 2 (fun w => Real.log (Complex.normSq (D w))) z :=
    (contDiffAt_normSq_comp hD).log (Complex.normSq_pos.2 hD0).ne'
  have hL' : ContDiffAt ℝ 2 (fun w => c * Real.log (Complex.normSq (D w)) + d) z :=
    (contDiffAt_const.mul hL).add contDiffAt_const
  have hφ' : ContDiffAt ℝ 2 (fun w => (-c) * φ w) z := contDiffAt_const.mul hφ
  have e : ∀ w, ∑ t ∈ s, Complex.normSq (g t w) =
      ∑ i : Fin s.card, Complex.normSq (g (s.equivFin.symm i) w) := fun w => by
    rw [← Finset.sum_coe_sort s]
    exact (s.equivFin.symm.sum_comp fun t => Complex.normSq (g t w)).symm
  have h0 := leviV_log_sum_nonneg (u := fun (i : Fin s.card) w => Complex.normSq (g (s.equivFin.symm i) w))
    (x := z) (fun i => contDiffAt_normSq_comp (hg _)) (fun i => logPshAt_normSq (hg _))
    (by rw [← e]; exact hpos) ξ
  simp only [← e] at h0
  rw [LocalMaximumSecondDerivative.leviV_ofReal_add hS (hL'.add hφ'), LocalMaximumSecondDerivative.leviV_ofReal_add hL' hφ',
    leviV_const_mul hL, leviV_log_normSq hD hD0, LocalMaximumSecondDerivative.leviV_ofReal_const_mul _ hφ]
  simp only [mul_zero, zero_add, Complex.add_re, Complex.re_ofReal_mul]
  linarith

theorem levi_log_theta_sum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : DataX E r), (∃ ξ : Fin r → E, X.toData.IsIso ξ) → (∃ w0 : 𝓞 E, ∀ u ∈ X.Λ, ∀ v ∈ X.Λ, ∃ k : ℤ, Algebra.trace ℚ E (X.ξ0 * herm X.Gm u (((w0 : E) - cc (w0 : E)) • v)) - Algebra.trace ℚ E (X.ξ0 * herm X.Gm u v) = 2 * k) → ∀ ps : Frame X.Ψ r → ℝ, (∀ x ∈ X.dom, ∃ A : TorusAt X.toData x, ps x = Real.log (∑ᶠ (a : Fin A.T.r → Vsp A.T.dim) (_ : a ∈ {a : Fin A.T.r → Vsp A.T.dim | (∀ j, a j ∈ ZSpan.fundamentalDomain A.T.b) ∧ (∀ j, ((5 : ℂ) ^ 2) • a j ∈ A.T.L) ∧ ∀ x ∈ A.T.L, ∃ c : Fin A.T.r → 𝓞 E, ∃ y ∈ A.T.L, x = ∑ j, act (c j) (((5 : ℂ) ^ 2) • a j) + (5 : ℂ) • y}), ∏ b, A.T.ptN2 1 A.s (fun _ => a b) / A.T.l2 1 A.s)) → ∀ x0 ∈ X.dom, ∀ z, cpt X.toData x0 z ∈ X.dom → ∀ ξ : Fin (nd X.toData) → ℂ, -((r : ℝ) / 2 * leviM X.toData (phla X.toData (fun _ j => if X.p0 ≤ (j : ℕ) then 1 else -1)) x0 z ξ) ≤ leviM X.toData ps x0 z ξ := by
  intro E _ _ _ r X _ hw ps hps x0 _ z hz ξ
  obtain ⟨Θ, D, κ, hκ, hΘ, hD, hD0, hval⟩ := GlobalTheory.ThetaHol.normalised_theta_norm_holomorphic E r X hw
  obtain ⟨𝒯, h1, h2⟩ := GlobalTheory.LevelTupleSum.exists_reps X.Λ X.Λ_fg
  set la : Wt X.Ψ r := fun _ j => if X.p0 ≤ (j : ℕ) then 1 else -1 with hla
  have hO := ExF.isOpen_OmF X.toData x0
  have hz' : z ∈ OmF X.toData x0 := hz
  have hc : Differentiable ℂ (cpt X.toData x0) :=
    differentiable_pi.2 fun τ => differentiable_pi.2 fun a => differentiable_pi.2 fun b =>
      (IW.cpt_entry_cd X.toData x0 τ a b).differentiable (by simp)
  have hhol : ∀ {P : Frame X.Ψ r → ℂ}, DifferentiableOn ℂ P X.dom →
      ContDiffAt ℂ 2 (fun w => P (cpt X.toData x0 w)) z := fun hP =>
    contDiffAt_two_of_holo hO (hP.comp hc.differentiableOn fun _ hw => hw) hz'
  have key : ∀ w ∈ OmF X.toData x0,
      0 < ∑ t ∈ 𝒯, Complex.normSq (∏ b, Θ (t b) (cpt X.toData x0 w)) ∧
      ps (cpt X.toData x0 w) = Real.log (∑ t ∈ 𝒯, Complex.normSq (∏ b, Θ (t b) (cpt X.toData x0 w))) +
        (((r : ℝ) / 2 * Real.log (Complex.normSq (D (cpt X.toData x0 w))) + r * Real.log κ) +
          (-((r : ℝ) / 2)) * phla X.toData la (cpt X.toData x0 w)) := by
    intro w hw
    have hN : 0 < X.nfac la (cpt X.toData x0 w) := ReciprocityTheory.ChartRestriction.G.AR.Up.OntoE.nfac_pos X.toData x0 hw
    have hx : cpt X.toData x0 w ∈ X.dom := hw
    generalize cpt X.toData x0 w = x at hN hx
    obtain ⟨A, hA⟩ := hps x hx
    have hp := GlobalTheory.TupleSumPos.tuple_sum_pos E r X x A
    have hs := GlobalTheory.LevelTupleSum.sum_eq hx A 𝒯 h1 h2 _ (GlobalTheory.LevelTupleSum.torus_r A)
    rw [hs] at hA hp
    have hDp : 0 < ‖D x‖ := norm_pos_iff.2 (hD0 x hx)
    have hK : 0 < (κ * ‖D x‖ * X.nfac la x) ^ r := by positivity
    have e : ∑ t ∈ 𝒯, ∏ b, A.T.ptN2 1 A.s (fun _ => A.φ (t b)) / A.T.l2 1 A.s =
        (κ * ‖D x‖ * X.nfac la x) ^ r * ∑ t ∈ 𝒯, Complex.normSq (∏ b, Θ (t b) x) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [map_prod, ← Fin.prod_const, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun b _ => ?_
      rw [hval x hx A, Complex.normSq_eq_norm_sq]
      ring
    rw [e] at hA hp
    have hS := (mul_pos_iff_of_pos_left hK).1 hp
    refine ⟨hS, ?_⟩
    rw [hA, Real.log_mul hK.ne' hS.ne', Real.log_pow, Real.log_mul (by positivity) hN.ne',
      Real.log_mul hκ.ne' hDp.ne', IW.log_norm_eq, phla]
    ring
  have hev : (fun w => ((ps (cpt X.toData x0 w) : ℝ) : ℂ)) =ᶠ[𝓝 z] fun w =>
      ((Real.log (∑ t ∈ 𝒯, Complex.normSq (∏ b, Θ (t b) (cpt X.toData x0 w))) +
        (((r : ℝ) / 2 * Real.log (Complex.normSq (D (cpt X.toData x0 w))) + r * Real.log κ) +
          (-((r : ℝ) / 2)) * phla X.toData la (cpt X.toData x0 w)) : ℝ) : ℂ) := by
    filter_upwards [hO.mem_nhds hz'] with w hw
    rw [(key w hw).2]
  unfold leviM
  rw [leviV_congr hev]
  exact levi_lower 𝒯 (g := fun t w => ∏ b, Θ (t b) (cpt X.toData x0 w)) _ _
    (fun t => contDiffAt_prod fun b _ => hhol (hΘ _)) (hhol hD) (hD0 _ hz)
    ((IW.phla_cpt_cdAt X.toData x0 hz' la).of_le (by norm_cast)) (key z hz').1 ξ

end GlobalTheory.ThetaSumLevi
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LeviLogThetaSumStatement

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst
open scoped ContDiff

theorem _root_.GlobalTheory.T.levi_log_theta_sum_alt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : DataX E r), (∃ ξ : Fin r → E, X.toData.IsIso ξ) → (∃ w0 : 𝓞 E, ∀ u ∈ X.Λ, ∀ v ∈ X.Λ, ∃ k : ℤ, Algebra.trace ℚ E (X.ξ0 * herm X.Gm u (((w0 : E) - cc (w0 : E)) • v)) - Algebra.trace ℚ E (X.ξ0 * herm X.Gm u v) = 2 * k) → ∀ ps : Frame X.Ψ r → ℝ, (∀ x ∈ X.dom, ∃ A : TorusAt X.toData x, ps x = Real.log (∑ᶠ (a : Fin A.T.r → Vsp A.T.dim) (_ : a ∈ {a : Fin A.T.r → Vsp A.T.dim | (∀ j, a j ∈ ZSpan.fundamentalDomain A.T.b) ∧ (∀ j, ((5 : ℂ) ^ 2) • a j ∈ A.T.L) ∧ ∀ x ∈ A.T.L, ∃ c : Fin A.T.r → 𝓞 E, ∃ y ∈ A.T.L, x = ∑ j, act (c j) (((5 : ℂ) ^ 2) • a j) + (5 : ℂ) • y}), ∏ b, A.T.ptN2 1 A.s (fun _ => a b) / A.T.l2 1 A.s)) → ∀ x0 ∈ X.dom, ∀ z, cpt X.toData x0 z ∈ X.dom → ∀ ξ : Fin (nd X.toData) → ℂ, -((r : ℝ) / 2 * leviM X.toData (phla X.toData (fun _ j => if X.p0 ≤ (j : ℕ) then 1 else -1)) x0 z ξ) ≤ leviM X.toData ps x0 z ξ := by
  first | exact @GlobalTheory.ThetaSumLevi.levi_log_theta_sum | exact GlobalTheory.ThetaSumLevi.levi_log_theta_sum | (intros; apply GlobalTheory.ThetaSumLevi.levi_log_theta_sum <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LogThetaSumInvariantSmooth

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst
open scoped ContDiff

namespace GlobalTheory.ThetaLogSum

open GlobalTheory.LevelTupleSum

variable {E : Type} [Field E] [NumberField E] {r : ℕ}

theorem gen_map {Λ : Submodule (𝓞 E) (Fin r → E)} (e : (Fin r → E) ≃ₗ[E] (Fin r → E))
    (he : ∀ v, v ∈ Λ ↔ e v ∈ Λ) {t : Fin r → Fin r → E} (h : Gen Λ t) :
    Gen Λ fun j => e (t j) := by
  refine ⟨fun j => ?_, fun u hu => ?_⟩
  · rw [← map_smul]
    exact (he _).1 (h.1 j)
  · obtain ⟨c, y, hy, h2⟩ := h.2 (e.symm u) ((he _).2 (by simpa using hu))
    refine ⟨c, e y, (he _).1 hy, ?_⟩
    have := congrArg e h2

    simpa only [LinearEquiv.apply_symm_apply, map_add (f := _), map_sum, map_smul] using this

theorem exists_reps_map {Λ : Submodule (𝓞 E) (Fin r → E)} (e : (Fin r → E) ≃ₗ[E] (Fin r → E))
    (he : ∀ v, v ∈ Λ ↔ e v ∈ Λ) (𝒯 : Finset (Fin r → Fin r → E)) (h1 : ∀ t ∈ 𝒯, Gen Λ t)
    (h2 : ∀ t, Gen Λ t → ∃! t', t' ∈ 𝒯 ∧ ∀ j, t j - t' j ∈ Λ) :
    ∃ 𝒯' : Finset (Fin r → Fin r → E), (∀ t ∈ 𝒯', Gen Λ t) ∧
      (∀ t, Gen Λ t → ∃! t', t' ∈ 𝒯' ∧ ∀ j, t j - t' j ∈ Λ) ∧
      ∀ f : (Fin r → Fin r → E) → ℝ, ∑ t ∈ 𝒯', f t = ∑ t ∈ 𝒯, f fun j => e (t j) := by
  let ι : (Fin r → Fin r → E) ↪ (Fin r → Fin r → E) :=
    ⟨fun t j => e (t j), fun t t' h => funext fun j => e.injective (congrFun h j)⟩
  refine ⟨𝒯.map ι, fun t ht => ?_, fun t ht => ?_, fun f => Finset.sum_map _ _ _⟩
  · obtain ⟨s, hs, rfl⟩ := Finset.mem_map.1 ht
    exact gen_map e he (h1 s hs)
  · have he' : ∀ v, v ∈ Λ ↔ e.symm v ∈ Λ := fun v => by
      rw [he (e.symm v), LinearEquiv.apply_symm_apply]
    obtain ⟨s, ⟨hs, hs2⟩, hu⟩ := h2 _ (gen_map e.symm he' ht)
    refine ⟨ι s, ⟨Finset.mem_map_of_mem _ hs, fun j => ?_⟩, ?_⟩
    · have := (he _).1 (hs2 j)
      rwa [map_sub, LinearEquiv.apply_symm_apply] at this
    · rintro _ ⟨ht', h3⟩
      obtain ⟨s', hs', rfl⟩ := Finset.mem_map.1 ht'
      rw [hu s' ⟨hs', fun j => ?_⟩]
      rw [he, map_sub, LinearEquiv.apply_symm_apply]
      exact h3 j

variable [IsCMField E]

theorem contDiffOn_cpt (X : Data E r) (x0 : Frame X.Ψ r) {F : Frame X.Ψ r → ℂ}
    (hF : DifferentiableOn ℂ F X.dom) : ContDiffOn ℝ ∞ (fun z => F (cpt X x0 z)) (OmF X x0) := by
  have hc : Differentiable ℂ (cpt X x0) :=
    differentiable_pi.2 fun τ => differentiable_pi.2 fun a => differentiable_pi.2 fun b =>
      (IW.cpt_entry_cd X x0 τ a b).differentiable (by simp)
  exact (ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn _ _ _ (ExF.isOpen_OmF X x0)
    (hF.comp hc.differentiableOn fun z hz => hz)).restrict_scalars ℝ

theorem contDiffOn_nfac (X : Data E r) (x0 : Frame X.Ψ r) (la : Wt X.Ψ r) :
    ContDiffOn ℝ ∞ (fun z => X.nfac la (cpt X x0 z)) (OmF X x0) := by
  have h : ContDiffOn ℝ ∞ (fun z => Real.exp (phla X la (cpt X x0 z) / (-2))) (OmF X x0) :=
    fun z hz => ((IW.phla_cpt_cdAt X x0 hz la).div_const _).exp.contDiffWithinAt
  refine h.congr fun z hz => ?_
  rw [phla, mul_div_cancel_left₀ _ (by norm_num), Real.exp_log (flowTermNormDecay.nfac_pos X la hz)]

theorem log_theta_sum_invariant_smooth : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : DataX E r), (∃ ξ : Fin r → E, X.toData.IsIso ξ) → (∃ w0 : 𝓞 E, ∀ u ∈ X.Λ, ∀ v ∈ X.Λ, ∃ k : ℤ, Algebra.trace ℚ E (X.ξ0 * herm X.Gm u (((w0 : E) - cc (w0 : E)) • v)) - Algebra.trace ℚ E (X.ξ0 * herm X.Gm u v) = 2 * k) → ∀ ps : Frame X.Ψ r → ℝ, (∀ x ∈ X.dom, ∃ A : TorusAt X.toData x, ps x = Real.log (∑ᶠ (a : Fin A.T.r → Vsp A.T.dim) (_ : a ∈ {a : Fin A.T.r → Vsp A.T.dim | (∀ j, a j ∈ ZSpan.fundamentalDomain A.T.b) ∧ (∀ j, ((5 : ℂ) ^ 2) • a j ∈ A.T.L) ∧ ∀ x ∈ A.T.L, ∃ c : Fin A.T.r → 𝓞 E, ∃ y ∈ A.T.L, x = ∑ j, act (c j) (((5 : ℂ) ^ 2) • a j) + (5 : ℂ) • y}), ∏ b, A.T.ptN2 1 A.s (fun _ => a b) / A.T.l2 1 A.s)) → IsInvFn X.toData ps ∧ ∀ x0 ∈ X.dom, ContDiffOn ℝ ∞ (fun z => ps (cpt X.toData x0 z)) {z | cpt X.toData x0 z ∈ X.dom} := by
  intro E _ _ _ r X _ hw ps hps
  obtain ⟨𝒯, h1, h2⟩ := exists_reps X.Λ X.Λ_fg
  refine ⟨fun γ hγ x hx b hb => ?_, fun x0 _ => ?_⟩
  · have hs := X.Γ_stab γ hγ
    have hy := MajInv.lact_mem_dom X.toData hs (OrthogonalFrameDomain.rmul_mem_dom X.toData hx hb)
    obtain ⟨A, hA⟩ := hps x hx
    obtain ⟨A', hA'⟩ := hps _ hy
    obtain ⟨𝒯', h1', h2', h3⟩ := exists_reps_map (Matrix.GeneralLinearGroup.toLin γ).toLinearEquiv
      hs.2 𝒯 h1 h2
    rw [hA, hA', sum_eq hx A 𝒯 h1 h2 _ (torus_r A), sum_eq hy A' 𝒯' h1' h2' _ (torus_r A'), h3]
    congr 1
    refine Finset.sum_congr rfl fun t _ => Finset.prod_congr rfl fun j _ => ?_
    exact (ThetaRho.normalised_theta_norm_invariant E r X hw x hx b hb γ hs A A' (t j)).1
  · obtain ⟨Θ, D, κ, -, hΘ, hD, hD0, hf⟩ := ThetaHol.normalised_theta_norm_holomorphic E r X hw
    have key : ∀ x ∈ X.dom, 0 < ∑ t ∈ 𝒯, ∏ j, κ * ‖Θ (t j) x‖ ^ 2 * ‖D x‖ *
          X.nfac (fun _ j => if X.p0 ≤ (j : ℕ) then 1 else -1) x ∧
        ps x = Real.log (∑ t ∈ 𝒯, ∏ j, κ * ‖Θ (t j) x‖ ^ 2 * ‖D x‖ *
          X.nfac (fun _ j => if X.p0 ≤ (j : ℕ) then 1 else -1) x) := by
      intro x hx
      obtain ⟨A, hA⟩ := hps x hx
      have hp := TupleSumPos.tuple_sum_pos E r X x A
      rw [sum_eq hx A 𝒯 h1 h2 _ (torus_r A)] at hA hp
      simp only [hf x hx A] at hA hp
      exact ⟨hp, hA⟩
    refine ContDiffOn.congr (ContDiffOn.log ?_ fun z hz => (key _ hz).1.ne') fun z hz => (key _ hz).2
    refine ContDiffOn.sum fun t _ => contDiffOn_prod fun j _ => ?_
    exact ((contDiffOn_const.mul ((contDiffOn_cpt X.toData x0 (hΘ _)).norm_sq ℂ)).mul
      ((contDiffOn_cpt X.toData x0 hD).norm ℂ fun z hz => hD0 _ hz)).mul
      (contDiffOn_nfac X.toData x0 _)

end GlobalTheory.ThetaLogSum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LogThetaSumInvariantSmoothStatement

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst
open scoped ContDiff

theorem _root_.GlobalTheory.T.log_theta_sum_invariant_smooth_alt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : DataX E r), (∃ ξ : Fin r → E, X.toData.IsIso ξ) → (∃ w0 : 𝓞 E, ∀ u ∈ X.Λ, ∀ v ∈ X.Λ, ∃ k : ℤ, Algebra.trace ℚ E (X.ξ0 * herm X.Gm u (((w0 : E) - cc (w0 : E)) • v)) - Algebra.trace ℚ E (X.ξ0 * herm X.Gm u v) = 2 * k) → ∀ ps : Frame X.Ψ r → ℝ, (∀ x ∈ X.dom, ∃ A : TorusAt X.toData x, ps x = Real.log (∑ᶠ (a : Fin A.T.r → Vsp A.T.dim) (_ : a ∈ {a : Fin A.T.r → Vsp A.T.dim | (∀ j, a j ∈ ZSpan.fundamentalDomain A.T.b) ∧ (∀ j, ((5 : ℂ) ^ 2) • a j ∈ A.T.L) ∧ ∀ x ∈ A.T.L, ∃ c : Fin A.T.r → 𝓞 E, ∃ y ∈ A.T.L, x = ∑ j, act (c j) (((5 : ℂ) ^ 2) • a j) + (5 : ℂ) • y}), ∏ b, A.T.ptN2 1 A.s (fun _ => a b) / A.T.l2 1 A.s)) → IsInvFn X.toData ps ∧ ∀ x0 ∈ X.dom, ContDiffOn ℝ ∞ (fun z => ps (cpt X.toData x0 z)) {z | cpt X.toData x0 z ∈ X.dom} := by
  first | exact @GlobalTheory.ThetaLogSum.log_theta_sum_invariant_smooth | exact GlobalTheory.ThetaLogSum.log_theta_sum_invariant_smooth | (intros; apply GlobalTheory.ThetaLogSum.log_theta_sum_invariant_smooth <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.NonemptyTorusAt

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst
open scoped ContDiff

namespace GlobalTheory.ThetaWeight

theorem nonempty_torusAt {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : DataX E r)
    (w0 : 𝓞 E) (hw : ∀ u ∈ X.Λ, ∀ v ∈ X.Λ, ∃ k : ℤ,
      Algebra.trace ℚ E (X.ξ0 * herm X.Gm u (((w0 : E) - cc (w0 : E)) • v)) -
        Algebra.trace ℚ E (X.ξ0 * herm X.Gm u v) = 2 * k) :
    ∀ x ∈ X.dom, Nonempty (TorusAt X.toData x) := by
  intro x hx
  obtain ⟨A, -⟩ := GlobalTheory.torusAtExists E r X.toData (fun φ => by
    obtain ⟨u, hu, h⟩ := X.EF_perf (-φ)
    refine ⟨u, hu, fun v => ?_⟩
    have h1 := h v
    rw [EFf, neg_mul, map_neg, AddMonoidHom.neg_apply, Int.cast_neg] at h1
    exact neg_injective h1) w0 hw x hx
  exact ⟨A⟩

theorem exists_weight : TStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : DataX E r), (∃ ξ : Fin r → E, X.toData.IsIso ξ) → ((∃ w0 : 𝓞 E, ∀ u ∈ X.Λ, ∀ v ∈ X.Λ, ∃ k : ℤ, Algebra.trace ℚ E (X.ξ0 * herm X.Gm u (((w0 : E) - cc (w0 : E)) • v)) - Algebra.trace ℚ E (X.ξ0 * herm X.Gm u v) = 2 * k) ∧ (PT.f E : ℝ) ≤ PT.rd E ∧ (PT.f E : ℝ) ^ 2 ≤ PT.rd E ∧ 16 ≤ PT.rd E ∧ ∃ m : ℕ, 1 ≤ m ∧ m ^ 4 ≤ PT.f E ∧ (X.p0 ≤ m ∨ r - X.p0 ≤ m)) → ∃ ps : Frame X.Ψ r → ℝ, IsInvFn X.toData ps ∧ (∀ x0 ∈ X.dom, ContDiffOn ℝ ∞ (fun z => ps (cpt X.toData x0 z)) {z | cpt X.toData x0 z ∈ X.dom}) ∧ (∀ x0 ∈ X.dom, ∀ z, cpt X.toData x0 z ∈ X.dom → ∀ ξ : Fin (nd X.toData) → ℂ, -((r : ℝ) / 2 * leviM X.toData (phla X.toData (fun _ j => if X.p0 ≤ (j : ℕ) then 1 else -1)) x0 z ξ) ≤ leviM X.toData ps x0 z ξ) ∧ cfwM X.toData ps (1 / (2 * (5 : ℝ) ^ 4 * |(NumberField.discr E : ℝ)| ^ ((1 : ℝ) / X.Ψ.card))) := by
  intro hT E _ _ _ r X hiso ⟨hw, hf1, hf2, hrd, hm⟩
  obtain ⟨ps, hps⟩ : ∃ ps : Frame X.Ψ r → ℝ, ∀ x ∈ X.dom, ∃ A : TorusAt X.toData x, ps x = Real.log (∑ᶠ (a : Fin A.T.r → Vsp A.T.dim) (_ : a ∈ {a : Fin A.T.r → Vsp A.T.dim | (∀ j, a j ∈ ZSpan.fundamentalDomain A.T.b) ∧ (∀ j, ((5 : ℂ) ^ 2) • a j ∈ A.T.L) ∧ ∀ x ∈ A.T.L, ∃ c : Fin A.T.r → 𝓞 E, ∃ y ∈ A.T.L, x = ∑ j, act (c j) (((5 : ℂ) ^ 2) • a j) + (5 : ℂ) • y}), ∏ b, A.T.ptN2 1 A.s (fun _ => a b) / A.T.l2 1 A.s) := by
    obtain ⟨w0, hw0⟩ := hw
    have h : ∀ x : Frame X.Ψ r, ∃ t : ℝ, x ∈ X.dom → ∃ A : TorusAt X.toData x, t = Real.log (∑ᶠ (a : Fin A.T.r → Vsp A.T.dim) (_ : a ∈ {a : Fin A.T.r → Vsp A.T.dim | (∀ j, a j ∈ ZSpan.fundamentalDomain A.T.b) ∧ (∀ j, ((5 : ℂ) ^ 2) • a j ∈ A.T.L) ∧ ∀ x ∈ A.T.L, ∃ c : Fin A.T.r → 𝓞 E, ∃ y ∈ A.T.L, x = ∑ j, act (c j) (((5 : ℂ) ^ 2) • a j) + (5 : ℂ) • y}), ∏ b, A.T.ptN2 1 A.s (fun _ => a b) / A.T.l2 1 A.s) := by
      intro x
      by_cases hx : x ∈ X.dom
      · obtain ⟨A⟩ := nonempty_torusAt X w0 hw0 x hx
        exact ⟨_, fun _ => ⟨A, rfl⟩⟩
      · exact ⟨0, fun h => absurd h hx⟩
    choose ps hps using h
    exact ⟨ps, hps⟩
  obtain ⟨h1, h2⟩ := GlobalTheory.T.log_theta_sum_invariant_smooth_alt E r X hiso hw ps hps
  refine ⟨ps, h1, h2, GlobalTheory.T.levi_log_theta_sum_alt E r X hiso hw ps hps, ?_⟩
  obtain ⟨C, A', -, hC⟩ := GlobalTheory.ThetaSumBound.growth_decay hT E r X hiso hf1 hf2 hrd hm
  refine ⟨⟨C, A', fun x hx => ?_⟩, fun η hη _ => ⟨C, A', fun x hx ξ hξ ht => ?_⟩⟩
  · obtain ⟨A, hA⟩ := hps x hx
    rw [hA]
    exact (hC x hx A (GlobalTheory.TupleSumPos.tuple_sum_pos E r X x A)).1
  · obtain ⟨A, hA⟩ := hps x hx
    rw [hA]
    refine ((hC x hx A (GlobalTheory.TupleSumPos.tuple_sum_pos E r X x A)).2 ξ hξ).trans ?_
    have ht0 : 0 ≤ ⨅ τ, X.tt ξ x τ := Real.iInf_nonneg fun τ => zero_le_one.trans (ht τ)
    have ha : 0 ≤ 1 / (2 * (5 : ℝ) ^ 4 * |(NumberField.discr E : ℝ)| ^ ((1 : ℝ) / X.Ψ.card)) := by
      positivity
    generalize 1 / (2 * (5 : ℝ) ^ 4 * |(NumberField.discr E : ℝ)| ^ ((1 : ℝ) / X.Ψ.card)) = a at ha ⊢
    generalize ⨅ τ, X.tt ξ x τ = t at ht0 ⊢
    have := mul_nonneg (mul_nonneg (mul_nonneg Real.pi_pos.le hη.le) ha) ht0
    linarith

end GlobalTheory.ThetaWeight
end
end
