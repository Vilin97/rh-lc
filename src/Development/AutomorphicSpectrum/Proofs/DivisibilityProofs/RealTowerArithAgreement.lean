module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.RefLinked
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FunctionalProductLinearFormsStatement
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.MonomialLinesPermutationStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ArithmeticIntersectionMultilinearPolarStatement
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyBase
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsNonvanishingDense
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PResAboveCover

section

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial Topology Filter ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem ResAboveCover.sameOrbit_symm {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') : SameOrbit z' z := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k), funext fun p => ?_⟩
  simp [← mul_assoc, inv_mul_cancel₀ (hc p.1)]


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem ResAboveCover.sameOrbit_trans {a b d : (Σ k, ι k) → ℂ} (h₁ : SameOrbit a b)
    (h₂ : SameOrbit b d) : SameOrbit a d := by
  obtain ⟨c, hc, rfl⟩ := h₁
  obtain ⟨c', hc', rfl⟩ := h₂
  exact ⟨fun k => c k * c' k, fun k => mul_ne_zero (hc k) (hc' k), funext fun p => by simp [mul_assoc]⟩


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem ResAboveCover.sameOrbit_of_tendsto {α : Type*} {l : Filter α} [l.NeBot]
    {v u : α → (Σ k, ι k) → ℂ} {v₀ u₀ : (Σ k, ι k) → ℂ}
    (hv : Tendsto v l (𝓝 v₀)) (hu : Tendsto u l (𝓝 u₀))
    (hvu : ∀ᶠ a in l, SameOrbit (v a) (u a))
    (hv₀ : ∀ k, ∃ i, v₀ ⟨k, i⟩ ≠ 0) (hu₀ : ∀ k, ∃ i, u₀ ⟨k, i⟩ ≠ 0) :
    SameOrbit v₀ u₀ := by
  choose i hi using hu₀
  have hcross : ∀ k j, v₀ ⟨k, j⟩ * u₀ ⟨k, i k⟩ = v₀ ⟨k, i k⟩ * u₀ ⟨k, j⟩ := by
    intro k j
    have h₁ : Tendsto (fun a => v a ⟨k, j⟩ * u a ⟨k, i k⟩) l (𝓝 (v₀ ⟨k, j⟩ * u₀ ⟨k, i k⟩)) :=
      ((continuous_apply _).continuousAt.tendsto.comp hv).mul
        ((continuous_apply _).continuousAt.tendsto.comp hu)
    have h₂ : Tendsto (fun a => v a ⟨k, i k⟩ * u a ⟨k, j⟩) l (𝓝 (v₀ ⟨k, i k⟩ * u₀ ⟨k, j⟩)) :=
      ((continuous_apply _).continuousAt.tendsto.comp hv).mul
        ((continuous_apply _).continuousAt.tendsto.comp hu)
    refine tendsto_nhds_unique h₁ (h₂.congr' ?_)
    filter_upwards [hvu] with a ha
    obtain ⟨c, -, hc⟩ := ha
    simp only [hc]
    ring
  refine ⟨fun k => v₀ ⟨k, i k⟩ / u₀ ⟨k, i k⟩, fun k => div_ne_zero ?_ (hi k), ?_⟩
  · intro h0
    obtain ⟨j, hj⟩ := hv₀ k
    have h := hcross k j
    rw [h0, zero_mul] at h
    exact hj ((mul_eq_zero.mp h).resolve_right (hi k))
  · funext p
    obtain ⟨k, j⟩ := p
    show v₀ ⟨k, j⟩ = v₀ ⟨k, i k⟩ / u₀ ⟨k, i k⟩ * u₀ ⟨k, j⟩
    rw [div_mul_eq_mul_div, eq_div_iff (hi k)]
    exact hcross k j


omit [Fintype K] in
theorem ResAboveCover.tendsto_lift {P J : Ideal (MRing ι)} {e : ℕ} (R : AnLogRes P J e) (x : R.X) :
    Tendsto (R.lift x) (𝓝 x) (𝓝 (R.lift x x)) := by
  refine tendsto_pi_nhds.2 fun p => ?_
  obtain ⟨j, hj⟩ := R.A.cover x
  have han := R.holo x p j (R.A.chart j x)
    ⟨(R.A.chart j).map_source hj, by simp [(R.A.chart j).left_inv hj, R.mem_U x]⟩
  have h₁ := han.continuousAt.comp ((R.A.chart j).continuousAt hj)
  have h₂ : ((fun y => R.lift x y p) ∘ (R.A.chart j).symm) ∘ (R.A.chart j) =ᶠ[𝓝 x]
      fun y => R.lift x y p := by
    filter_upwards [(R.A.chart j).eventually_left_inverse hj] with y hy
    simp [hy]
  exact (h₁.congr h₂).tendsto


omit [Fintype K] in
theorem ResAboveCover.limit {P J : Ideal (MRing ι)} {e : ℕ} (R : AnLogRes P J e) {α : Type*}
    {l : Filter α} [l.NeBot] {v : α → (Σ k, ι k) → ℂ} {x : α → R.X} {v₀ : (Σ k, ι k) → ℂ}
    {x₀ : R.X} (hv : Tendsto v l (𝓝 v₀)) (hx : Tendsto x l (𝓝 x₀))
    (hvx : ∀ᶠ a in l, SameOrbit (v a) (R.lift (x a) (x a))) (hv₀ : ∀ k, ∃ i, v₀ ⟨k, i⟩ ≠ 0) :
    SameOrbit v₀ (R.lift x₀ x₀) ∧
      ∀ᶠ a in l, x a ∈ R.U x₀ ∧ SameOrbit (v a) (R.lift x₀ (x a)) := by
  have hU : ∀ᶠ a in l, x a ∈ R.U x₀ := hx ((R.isOpen_U x₀).mem_nhds (R.mem_U x₀))
  have h₂ : ∀ᶠ a in l, x a ∈ R.U x₀ ∧ SameOrbit (v a) (R.lift x₀ (x a)) := by
    filter_upwards [hU, hvx] with a ha hva
    exact ⟨ha, ResAboveCover.sameOrbit_trans hva
      (ResAboveCover.sameOrbit_symm (R.compat x₀ (x a) (x a) ⟨ha, R.mem_U _⟩))⟩
  refine ⟨ResAboveCover.sameOrbit_of_tendsto hv ((ResAboveCover.tendsto_lift R x₀).comp hx)
    (h₂.mono fun a h => h.2) hv₀ (R.mem x₀ x₀ (R.mem_U x₀)).1, h₂⟩


omit [Fintype K] in
theorem ResAboveCover.exists_limit {P J : Ideal (MRing ι)} {e : ℕ} (R : AnLogRes P J e) {α : Type*}
    {l : Filter α} [l.NeBot] {v : α → (Σ k, ι k) → ℂ} {v₀ : (Σ k, ι k) → ℂ}
    (hv : Tendsto v l (𝓝 v₀)) (hv₀ : ∀ k, ∃ i, v₀ ⟨k, i⟩ ≠ 0)
    (hex : ∀ᶠ a in l, ∃ x, SameOrbit (v a) (R.lift x x)) :
    ∃ (F : Ultrafilter α) (x : α → R.X) (x₀ : R.X), (F : Filter α) ≤ l ∧
      Tendsto x F (𝓝 x₀) ∧ SameOrbit v₀ (R.lift x₀ x₀) ∧
      ∀ᶠ a in (F : Filter α), x a ∈ R.U x₀ ∧ SameOrbit (v a) (R.lift x₀ (x a)) := by
  classical
  obtain ⟨-, x₁, -⟩ := hex.exists
  let x : α → R.X := fun a => if h : ∃ x, SameOrbit (v a) (R.lift x x) then h.choose else x₁
  have hvx : ∀ᶠ a in l, SameOrbit (v a) (R.lift (x a) (x a)) :=
    hex.mono fun a h => by simp only [x, dif_pos h]; exact h.choose_spec
  let F := Ultrafilter.of l
  have hFl : (F : Filter α) ≤ l := Ultrafilter.of_le l
  obtain ⟨x₀, -, hx₀⟩ := isCompact_univ.ultrafilter_le_nhds (F.map x) (by simp)
  have hx : Tendsto x F (𝓝 x₀) := by
    rw [Tendsto, ← Ultrafilter.coe_map]
    exact hx₀
  exact ⟨F, x, x₀, hFl, hx, ResAboveCover.limit R (hv.mono_left hFl) hx (hvx.filter_mono hFl) hv₀⟩

theorem ResAboveCover.surj_all (hND : HilbertSamuel.NonvanishingDense.Statement)
    (P J : Ideal (MRing ι)) {e d : ℕ} (R : AnLogRes P J e) (hP : IsArithVar P d) :
    ∀ v ∈ mcPts P, ∃ x, SameOrbit v (R.lift x x) := by
  intro v hv
  obtain ⟨f, hfJ, hfP⟩ := SetLike.not_le_iff_exists.1 R.nondeg
  have hcl := hND K ι P d f hP hfP hv
  have := mem_closure_iff_nhdsWithin_neBot.1 hcl
  have hex : ∀ᶠ w in 𝓝[{w | w ∈ mcPts P ∧ eval w (map (Int.castRingHom ℂ) f) ≠ 0}] v,
      ∃ x, SameOrbit w (R.lift x x) := by
    filter_upwards [self_mem_nhdsWithin] with w hw
    obtain ⟨x, hx⟩ := R.surj w hw.1 (fun hJ => hw.2 (hJ.2 f hfJ))
    exact ⟨x, ResAboveCover.sameOrbit_symm hx⟩
  obtain ⟨-, -, x₀, -, -, h, -⟩ := ResAboveCover.exists_limit R (v := fun w => w)
    (tendsto_id.mono_left nhdsWithin_le_nhds) hv.1 hex
  exact ⟨x₀, h⟩

end GroundTheory.Heights₂.Heights.Targets
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RealTowerArithAgreement

section

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Top.RootNum

def rc {N : ℕ} (i k : Fin N) : ℤ := (if (k : ℕ) + 1 = i then 1 else 0) - (if k = i then 1 else 0)

theorem sum_rc_smul {N : ℕ} {A : Type} [AddCommGroup A] (a : Fin N → A) (i : Fin N) :
    ∑ k : Fin N, rc i k • (-∑ l ∈ Finset.Iic k, a l) = a i := by
  have h1 : ∀ k : Fin N, rc i k • (-∑ l ∈ Finset.Iic k, a l) =
      (if (k : ℕ) + 1 = i then (-∑ l ∈ Finset.Iic k, a l) else 0) -
        (if k = i then (-∑ l ∈ Finset.Iic k, a l) else 0) := by
    intro k
    unfold rc
    split_ifs <;> simp
  simp only [h1, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  obtain ⟨i, hi⟩ := i
  cases i with
  | zero =>
    have h2 : Finset.Iic (⟨0, hi⟩ : Fin N) = {⟨0, hi⟩} := by
      ext l
      simp [Fin.ext_iff, Fin.le_def]
    simp [h2]
  | succ j =>
    have hj : j < N := by omega
    have h3 : ∑ k : Fin N, (if (k : ℕ) + 1 = j + 1 then (-∑ l ∈ Finset.Iic k, a l) else 0) =
        -∑ l ∈ Finset.Iic (⟨j, hj⟩ : Fin N), a l := by
      rw [Finset.sum_eq_single ⟨j, hj⟩]
      · simp
      · intro b _ hb
        rw [if_neg]
        intro h
        exact hb (Fin.ext (by simpa using h))
      · simp
    have h4 : Finset.Iic (⟨j + 1, hi⟩ : Fin N) = insert ⟨j + 1, hi⟩ (Finset.Iic ⟨j, hj⟩) := by
      ext l
      simp [Fin.ext_iff, Fin.le_def]
      omega
    simp only [h3]
    rw [h4, Finset.sum_insert (by simp [Fin.le_def])]
    abel

theorem sum_mul_rc {N : ℕ} (l : Fin N → ℝ) (k : Fin N) :
    ∑ i : Fin N, l i * (rc i k : ℝ) = (if h : (k : ℕ) + 1 < N then l ⟨k + 1, h⟩ else 0) - l k := by
  have h1 : ∀ i : Fin N, l i * (rc i k : ℝ) =
      (if (k : ℕ) + 1 = i then l i else 0) - (if k = i then l i else 0) := by
    intro i
    unfold rc
    split_ifs <;> simp
  simp only [h1, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  congr 1
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨k + 1, h⟩]
    · simp
    · intro b _ hb
      rw [if_neg]
      intro e
      exact hb (Fin.ext e.symm)
    · simp
  · refine Finset.sum_eq_zero fun b _ => ?_
    rw [if_neg]
    intro e
    exact h (e ▸ b.2)

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

def rootC : Option (Ψ × Fin N) → Option (Ψ × Fin N) → ℤ
  | none, none => 1
  | none, some _ => 0
  | some _, none => 0
  | some p, some q => if q.1 = p.1 then rc p.2 q.2 else 0

theorem sum_rootC_none {A : Type} [AddCommGroup A] (g : Option (Ψ × Fin N) → A) :
    ∑ b, rootC none b • g b = g none := by
  simp [Fintype.sum_option, rootC]

theorem sum_rootC_some {A : Type} [AddCommGroup A] (g : Option (Ψ × Fin N) → A) (a : Ψ × Fin N → A)
    (hg : ∀ τ k, g (some (τ, k)) = -∑ l ∈ Finset.Iic k, a (τ, l)) (p : Ψ × Fin N) :
    ∑ b, rootC (some p) b • g b = a p := by
  rw [Fintype.sum_option]
  simp only [rootC, zero_smul, zero_add]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single p.1]
  · simp only [if_true, hg]
    exact sum_rc_smul (fun l => a (p.1, l)) p.2
  · intro b _ hb
    simp [hb]
  · simp

theorem sum_coef_rootC (M : RootModel Ψ N) (lam : Wt Ψ N) (s : ℝ) (b : Option (Ψ × Fin N)) :
    ∑ o, M.coef lam s o * (rootC o b : ℝ) = PB.gapS (fun x => lam x.1 x.2) (s / M.kA) b := by
  rw [Fintype.sum_option]
  cases b with
  | none => simp [rootC, RootModel.coef, PB.gapS]
  | some q =>
    simp only [rootC, RootModel.coef, Int.cast_zero, mul_zero, zero_add]
    rw [Fintype.sum_prod_type, Finset.sum_eq_single q.1]
    · simp only [if_true, mul_comm, neg_mul]
      have := sum_mul_rc (fun i => lam q.1 i) q.2
      simp only [PB.gapS, Option.elim, PB.gap, PB.gapX]
      rw [Finset.sum_neg_distrib, this]
      by_cases h : (q.2 : ℕ) + 1 < N <;> simp [h]
    · intro c _ hc
      simp [Ne.symm hc]
    · simp

section Lines

variable {M : RootModel Ψ N} {S : PB.AnSys (dimFl Ψ N) (Option (Ψ × Fin N))} {n : ℕ}

theorem line_none_h (R : RealTie M S n) (t : ℝ) (ht0 : 0 < t) (ht : t ≤ S.t₀) (z : (Σ k, M.ι k) → ℂ)
    (hz : z ∈ mcPts M.P) : (R.Re.line none t).h z = M.A.h z := by
  obtain ⟨x, c, hc, hzx⟩ := GroundTheory.Heights₂.Heights.Targets.ResAboveCover.surj_all
    GroundTheory.Heights₂.Heights.HilbertSamuel.NonvanishingDense.full M.P R.Re.J R.Re.R R.Re.arith z hz
  have hum : R.Re.R.lift x x ∈ mcPts M.P := R.Re.R.mem x x (R.Re.R.mem_U x)
  have e := R.Re.line_eq none t ht0 ht x
  rw [R.phT_none, add_zero] at e
  have e' : (R.Re.line none t).h (R.Re.R.lift x x) = (R.Re.ref none).h (R.Re.R.lift x x) :=
    Real.log_injOn_pos (Set.mem_Ioi.2 ((R.Re.line none t).pos _ hum.1))
      (Set.mem_Ioi.2 ((R.Re.ref none).pos _ hum.1)) e
  rw [← R.ref_none.2 z hz, hzx, (R.Re.line none t).smul c _ hc, (R.Re.ref none).smul c _ hc, e',
    R.Re.line_deg]

theorem comb_a (R : RealTie M S n) (t : ℝ) (o : Option (Ψ × Fin N)) :
    (PB.combLine (fun b => R.Re.line b t) (rootC o)).a = (M.line t o).a := by
  funext κ
  rw [PB.combLine_a]
  simp only [← smul_eq_mul]
  cases o with
  | none =>
    rw [sum_rootC_none (fun b => (R.Re.line b t).a κ), R.Re.line_deg, R.ref_none.1]
    rfl
  | some p =>
    rw [sum_rootC_some (fun b => (R.Re.line b t).a κ) (fun q => M.xdeg q κ)]
    · show _ = (M.x t p).a κ
      rw [M.x_deg]
    · intro τ k
      rw [R.Re.line_deg, R.fund_deg]
      simp [Finset.sum_apply]

theorem comb_h (R : RealTie M S n) (t : ℝ) (ht0 : 0 < t) (ht : t ≤ S.t₀) (o : Option (Ψ × Fin N))
    (z : (Σ k, M.ι k) → ℂ) (hz : z ∈ mcPts M.P) :
    (PB.combLine (fun b => R.Re.line b t) (rootC o)).h z = (M.line t o).h z := by
  have hp : ∀ b, 0 < (R.Re.line b t).h z := fun b => (R.Re.line b t).pos z hz.1
  have hlog : Real.log ((PB.combLine (fun b => R.Re.line b t) (rootC o)).h z) =
      ∑ b, rootC o b • Real.log ((R.Re.line b t).h z) := by
    rw [PB.combLine_h, Real.log_prod (fun b _ => (zpow_pos (hp b) _).ne')]
    simp [Real.log_zpow]
  refine Real.log_injOn_pos (Set.mem_Ioi.2 ((PB.combLine (fun b => R.Re.line b t) (rootC o)).pos z hz.1))
    (Set.mem_Ioi.2 ((M.line t o).pos z hz.1)) ?_
  rw [hlog]
  cases o with
  | none =>
    rw [sum_rootC_none (fun b => Real.log ((R.Re.line b t).h z)), line_none_h R t ht0 ht z hz]
    rfl
  | some p =>
    rw [sum_rootC_some (fun b => Real.log ((R.Re.line b t).h z)) (fun q => Real.log ((M.x t q).h z))]
    · rfl
    · intro τ k
      exact R.fund_reg τ k t ht0 ht z hz

theorem smooth_line (M : RootModel Ψ N) (t : ℝ) (o : Option (Ψ × Fin N)) : IsSmoothHerm (M.line t o) := by
  cases o with
  | none => exact M.A_smooth
  | some p => exact M.x_smooth t p

theorem word_eq (hL : ReciprocityTheory.ChartRestriction.G.AI.I2.MetricLocalStatement) (II : IntersectionSystem)
    (hII : IsFullIntersectionSystem II) (R : RealTie M S n) (t : ℝ) (ht0 : 0 < t) (ht : t ≤ S.t₀)
    (w : Fin (dimFl Ψ N + 1) → Option (Ψ × Fin N)) :
    II M.K M.ι M.P (dimFl Ψ N + 1) (fun r => M.line t (w r)) =
      PB.polar (dimFl Ψ N + 1) (fun v => II M.K M.ι M.P (dimFl Ψ N + 1) fun r => R.Re.line (v r) t)
        (fun r a => (rootC (w r) a : ℝ)) := by
  have hc := GlobalTheory.T.arithmetic_intersection_multilinear_polar hL II hII M.K M.ι (Option (Ψ × Fin N)) M.P (dimFl Ψ N + 1)
    (fun a => R.Re.line a t) (fun r => rootC (w r)) R.Re.arith (fun a => R.Re.line_smooth a t ht0 ht)
  rw [← hc.2]
  exact hL M.K M.ι (II M.K M.ι) (hII.1 M.K M.ι) M.P _ _ _ R.Re.arith (fun j => smooth_line M t _) hc.1
    (fun j => (comb_a R t _).symm) (fun j z hz => (comb_h R t ht0 ht _ z hz).symm)

end Lines

theorem eval_formPoly {σ : Type} [Fintype σ] (d : ℕ) (a : (Fin d → σ) → ℝ) (c : σ → ℝ) :
    eval c (PB.formPoly d a) = ∑ w, a w * ∏ j, c (w j) := by

  simp [PB.formPoly, map_sum, map_prod]

theorem polar_swap {J : Type} [Fintype J] [DecidableEq J] {d : ℕ} (c : J → ℝ) (nn : J → J → ℝ)
    (I : (Fin d → J) → ℝ) :
    ∑ w : Fin d → J, (∏ k, c (w k)) * PB.polar d I (fun r a => nn (w r) a) =
      ∑ v : Fin d → J, (∏ r, ∑ o, c o * nn o (v r)) * I v := by
  simp only [PB.polar, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.sum_mul]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finset.prod_mul_distrib, mul_assoc]

def cS (lam : Wt Ψ N) (s : ℝ) : Option (Ψ × Fin N) → ℝ := fun o => o.elim s fun r => -lam r.1 r.2

theorem linA_eq (lam : Wt Ψ N) (s : ℝ) : linA lam s = ∑ j, C (cS lam s j) * X j := by
  rw [Fintype.sum_option]

  simp [linA, toA, linRoot, cS, map_sum, add_comm]

variable (M : RootModel Ψ N) (II : IntersectionSystem)

theorem arFun_monomial (t : ℝ) (m : Option (Ψ × Fin N) →₀ ℕ) :
    M.arFun II t (monomial m 1) = M.arMono II t m := by
  have := (basisMonomials (Option (Ψ × Fin N)) ℝ).constr_basis ℝ (M.arMono II t) m
  simpa [RootModel.arFun] using this

theorem PP_monomial (m : Option (Ψ × Fin N) →₀ ℕ) :
    M.PP II (monomial m 1) = limUnder (𝓝[>] 0) fun t => M.arMono II t m := by
  have := (basisMonomials (Option (Ψ × Fin N)) ℝ).constr_basis ℝ
    (fun m => limUnder (𝓝[>] (0 : ℝ)) fun t => M.arMono II t m) m
  simpa [RootModel.PP] using this

theorem prod_cS (lam : Wt Ψ N) (s : ℝ) {d : ℕ} (w : Fin d → Option (Ψ × Fin N)) :
    ∏ k, cS lam s (w k) = (∏ k, M.coef lam s (w k)) *
      (M.kA : ℝ) ^ ((∑ k, Finsupp.single (w k) 1 : Option (Ψ × Fin N) →₀ ℕ) none) := by
  have hk : (M.kA : ℝ) ≠ 0 := Nat.cast_ne_zero.2 M.kA_pos.ne'
  rw [Finsupp.finsetSum_apply, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  cases w k with
  | none => simp [cS, RootModel.coef, hk]
  | some r => simp [cS, RootModel.coef]

theorem arFun_lin (hII : IsFullIntersectionSystem II) (lam : Wt Ψ N) (s t : ℝ) :
    M.arFun II t (linA lam s ^ (dimFl Ψ N + 1)) =
      (∑ w : Fin (dimFl Ψ N + 1) → Option (Ψ × Fin N), (∏ k, M.coef lam s (w k)) *
        II M.K M.ι M.P (dimFl Ψ N + 1) (fun r => M.line t (w r))) / M.δ := by
  have hk : (M.kA : ℝ) ≠ 0 := Nat.cast_ne_zero.2 M.kA_pos.ne'
  have hd : (M.δ : ℝ) ≠ 0 := Nat.cast_ne_zero.2 M.δ_pos.ne'
  have e : linA lam s ^ (dimFl Ψ N + 1) =
      ∏ _k : Fin (dimFl Ψ N + 1), ∑ j, C (cS lam s j) * X j := by
    rw [linA_eq, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [e]
  have h1 := GlobalTheory.T.functional_product_linear_forms (Option (Ψ × Fin N)) (dimFl Ψ N + 1) (M.arFun II t)
    (fun _ => cS lam s)
  rw [h1, Finset.sum_div]
  refine Finset.sum_congr rfl fun w _ => ?_
  obtain ⟨hdeg, σ, -, hii⟩ := GlobalTheory.T.monomial_lines_permutation II hII.1 M.K M.ι M.P (dimFl Ψ N + 1)
    (Option (Ψ × Fin N)) (M.line t) w M.arith (smooth_line M t)
  rw [arFun_monomial, RootModel.arMono, if_pos hdeg, hii, prod_cS M lam s w]
  have hp : ((M.kA : ℝ) ^ ((∑ k, Finsupp.single (w k) 1 : Option (Ψ × Fin N) →₀ ℕ) none)) ≠ 0 :=
    pow_ne_zero _ hk
  field_simp

theorem exists_word {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {J : Type} (m : J →₀ ℕ) {d : ℕ}
    (hm : m.degree = d) : ∃ w : Fin d → J, ∀ ℓ : J → HermLine ι, monoLines ℓ m d = fun k => ℓ (w k) := by
  have hlen : (Finsupp.toMultiset m).toList.length = d := by
    rw [Multiset.length_toList, Finsupp.card_toMultiset, ← hm]
    simp only [Finsupp.sum, id]
    rfl
  refine ⟨fun k => (Finsupp.toMultiset m).toList.get ⟨k, by omega⟩, fun ℓ => funext fun k => ?_⟩
  simp only [monoLines]
  rw [dite_eq_left (by omega)]

section Limits

variable {M II} {S : PB.AnSys (dimFl Ψ N) (Option (Ψ × Fin N))} {n : ℕ}

theorem num_eq (hL : ReciprocityTheory.ChartRestriction.G.AI.I2.MetricLocalStatement) (hII : IsFullIntersectionSystem II)
    (R : RealTie M S n) (lam : Wt Ψ N) (s t : ℝ) (ht0 : 0 < t) (ht : t ≤ S.t₀) :
    (n : ℝ) * M.arFun II t (linA lam s ^ (dimFl Ψ N + 1)) =
      eval (PB.gapS (fun x => lam x.1 x.2) (s / M.kA)) (R.Re.FT II t) := by
  have hdeg : (R.Re.deg : ℝ) ≠ 0 := Nat.cast_ne_zero.2 R.Re.deg_pos.ne'
  have hδ : (M.δ : ℝ) = n * R.Re.deg := by exact_mod_cast R.δ_eq
  have hn : (n : ℝ) ≠ 0 := by
    intro h
    have h' : (M.δ : ℝ) = 0 := by rw [hδ, h, zero_mul]
    exact (Nat.cast_ne_zero.2 M.δ_pos.ne') h'
  have e : ∑ w : Fin (dimFl Ψ N + 1) → Option (Ψ × Fin N), (∏ k, M.coef lam s (w k)) *
        II M.K M.ι M.P (dimFl Ψ N + 1) (fun r => M.line t (w r)) =
      ∑ v : Fin (dimFl Ψ N + 1) → Option (Ψ × Fin N),
        (∏ r, PB.gapS (fun x => lam x.1 x.2) (s / M.kA) (v r)) *
          II M.K M.ι M.P (dimFl Ψ N + 1) (fun r => R.Re.line (v r) t) := by
    simp only [word_eq hL II hII R t ht0 ht]
    refine (polar_swap (M.coef lam s) (fun o a => (rootC o a : ℝ)) _).trans ?_
    simp only [sum_coef_rootC]
  rw [arFun_lin M II hII, PB.Realis.FT, eval_formPoly, e, hδ, Finset.sum_div, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [PB.Realis.num]
  field_simp

theorem exists_lim_arMono (hL : ReciprocityTheory.ChartRestriction.G.AI.I2.MetricLocalStatement)
    (hII : IsFullIntersectionSystem II) (R : RealTie M S n)
    (hconv : ∀ w, Tendsto (fun t => R.Re.num II t w) (𝓝[>] 0) (𝓝 (R.Re.limNum II w)))
    (h0 : 0 < S.t₀) (m : Option (Ψ × Fin N) →₀ ℕ) :
    ∃ L, Tendsto (fun t => M.arMono II t m) (𝓝[>] 0) (𝓝 L) := by
  by_cases hm : m.degree = dimFl Ψ N + 1
  · obtain ⟨w, hw⟩ := exists_word (ι := M.ι) m hm
    have hdeg : (R.Re.deg : ℝ) ≠ 0 := Nat.cast_ne_zero.2 R.Re.deg_pos.ne'
    have h1 : Tendsto (fun t => PB.polar (dimFl Ψ N + 1) (fun v => (R.Re.deg : ℝ) * R.Re.num II t v)
          (fun r a => (rootC (w r) a : ℝ)) / ((M.δ : ℝ) * (M.kA : ℝ) ^ m none)) (𝓝[>] 0)
        (𝓝 (PB.polar (dimFl Ψ N + 1) (fun v => (R.Re.deg : ℝ) * R.Re.limNum II v)
          (fun r a => (rootC (w r) a : ℝ)) / ((M.δ : ℝ) * (M.kA : ℝ) ^ m none))) := by
      refine Tendsto.div_const ?_ _
      simp only [PB.polar]
      exact tendsto_finsetSum _ fun v _ => ((hconv v).const_mul _).const_mul _
    refine ⟨_, h1.congr' ?_⟩
    filter_upwards [Ioc_mem_nhdsGT h0] with t ht
    have e : (fun v => (R.Re.deg : ℝ) * R.Re.num II t v) =
        fun v => II M.K M.ι M.P (dimFl Ψ N + 1) fun r => R.Re.line (v r) t := by
      funext v
      rw [PB.Realis.num]
      field_simp
    rw [RootModel.arMono, if_pos hm, hw, word_eq hL II hII R t ht.1 ht.2, e]
  · refine ⟨0, ?_⟩
    simp only [RootModel.arMono, if_neg hm]
    exact tendsto_const_nhds

theorem tendsto_arFun (hC : M.Converges II) (F : RPA Ψ N) :
    Tendsto (fun t => M.arFun II t F) (𝓝[>] 0) (𝓝 (M.PP II F)) := by
  induction F using MvPolynomial.induction_on' with
  | monomial u a =>
    have e : monomial u a = a • (monomial u (1 : ℝ) : RPA Ψ N) := by
      rw [smul_monomial, smul_eq_mul, mul_one]
    obtain ⟨L, hLim⟩ := hC u
    simp only [e, map_smul, arFun_monomial, PP_monomial, smul_eq_mul]
    rw [hLim.limUnder_eq]
    exact hLim.const_mul a
  | add p q hp hq => simpa only [map_add (f := _)] using hp.add hq

end Limits

theorem arith_degrees : PB.Inputs → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (M : RootModel Ψ N) (S : PB.AnSys (dimFl Ψ N) (Option (Ψ × Fin N))) (n : ℕ) (R : RealTie M S n) (lam : Wt Ψ N) (s : ℝ), 0 < n ∧ (∀ t, 0 < t → t ≤ S.t₀ → (n : ℝ) * M.arFun II t (linA lam s ^ (dimFl Ψ N + 1)) = eval (PB.gapS (fun x => lam x.1 x.2) (s / M.kA)) (R.Re.FT II t)) ∧ ((∀ w, Tendsto (fun t => R.Re.num II t w) (𝓝[>] 0) (𝓝 (R.Re.limNum II w))) → 0 < S.t₀ → M.Converges II ∧ (n : ℝ) * M.PP II (linA lam s ^ (dimFl Ψ N + 1)) = eval (PB.gapS (fun x => lam x.1 x.2) (s / M.kA)) (R.Re.PB II)) := by
  intro hI II hII Ψ _ _ N M S n R lam s
  have hL := hI.metricLocal
  refine ⟨Nat.pos_of_ne_zero fun h => M.δ_pos.ne' (R.δ_eq.trans (Nat.mul_eq_zero.2 (Or.inl h))),
    fun t ht0 ht => num_eq hL hII R lam s t ht0 ht, fun hconv h0 => ?_⟩
  have hC : M.Converges II := exists_lim_arMono hL hII R hconv h0
  refine ⟨hC, ?_⟩
  have h1 := (tendsto_arFun hC (linA lam s ^ (dimFl Ψ N + 1))).const_mul (n : ℝ)
  have h2 : Tendsto (fun t => eval (PB.gapS (fun x => lam x.1 x.2) (s / M.kA)) (R.Re.FT II t)) (𝓝[>] 0)
      (𝓝 (eval (PB.gapS (fun x => lam x.1 x.2) (s / M.kA)) (R.Re.PB II))) := by
    simp only [PB.Realis.FT, PB.Realis.PB, eval_formPoly]
    exact tendsto_finsetSum _ fun v _ => (hconv v).mul_const _
  refine tendsto_nhds_unique (h1.congr' ?_) h2
  filter_upwards [Ioc_mem_nhdsGT h0] with t ht
  exact num_eq hL hII R lam s t ht.1 ht.2

end GlobalTheory.CompanionTheory.Ar.Top.RootNum
end
end
end
