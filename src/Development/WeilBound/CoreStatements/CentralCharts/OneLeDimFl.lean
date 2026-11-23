module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
public import Development.WeilBound.CoreStatements.CentralCharts.PshAt0
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FlagIndices.InstFintypeFlIdx
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFinsetOfMemNhds
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BoundaryPointsClosedStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicAtlasCoordCompatStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelAnalyticDataExists
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FubiniStudyMetricSmooth
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsArithVarOfSncModelStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionFubiniStudyPositive
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LowerBoundHeightOnBoundaryStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SmoothContinuous
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SameOrbitRefl
public import Development.WeilBound.CoreStatements.CentralCharts.ExistsPermFirst
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AdaptedAtlasSncSectionStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.AdaptedAtlasSmoothPotentialLocalStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ConjugationAntiholomorphicChartsStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ConjugationInvariantSingularPotentialStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LiftSystemComplexConjugationStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LiftSystemRealStructureStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SingularPotentialLogGrowthPshStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SingularWeightMonotoneRegularization
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SmoothFunctionAsDegreeZeroMetric
public import Development.WeilBound.CoreStatements.CentralCharts.SmoothOnOfTame
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
import ReciprocityTheory.AnalyticForms.LeviForms.TailCutA
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
public import Development.WeilBound.CoreStatements.CentralCharts.IsPosPotBlock
public import Development.WeilBound.CoreStatements.CentralCharts.PshAt0LogNorm
import Development.WeilBound.CoreStatements.CentralCharts.SmoothOnOfTame
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: Development.WeilBound.CoreStatements.CentralCharts.CommonMembers

section

@[expose] public section

noncomputable section

namespace AnalyticReference.An

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo Filter Topology Metric
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar.PB

variable {n : ℕ} {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {P : Ideal (MRing J)}

theorem isLiftSys (R : AnLogRes P ⊤ n) : Cj.IsLiftSys R.A P R.U R.lift :=
  ⟨R.isOpen_U, R.mem_U, R.holo, R.mem, R.compat, fun z hz => R.surj z hz (not_mem_top _),
    fun x x' h => R.inj x x' (not_mem_top _) h, fun x p hp j hj => R.immersion x (not_mem_top _) p hp j hj⟩

def IsMember (R : AnLogRes P ⊤ n) (L : LocPot R.X) (s : R.X → R.X → ℂ) (d : K → ℤ) (u : R.X → ℝ) (cen : Prop)
    (ph : R.X → ℝ) (phT : ℝ → R.X → ℝ) (line : ℝ → HermLine J) (C₅ C t₀ : ℝ) : Prop :=
  IsSingWeight R.A L s (potOf R (fsHerm J d)) ph C₅ ∧
  IsRegFamily R.A (potOf R (fsHerm J fun _ => 1)) L s (potOf R (fsHerm J d)) ph phT C t₀ ∧
  IsRegFamilyC2 R.A s ph phT ∧ (∀ x ∉ bdry s, ph x = u x) ∧
  (∀ t, (line t).a = d ∧ IsSmoothHerm (line t) ∧ IsConjInvariantH (line t)) ∧
  (∀ t, 0 < t → t ≤ t₀ → ∀ x, Real.log ((line t).h (R.lift x x)) =
    Real.log ((fsHerm J d).h (R.lift x x)) + phT t x) ∧
  (cen → ∀ t, IsPsh R.A ((potOf R (fsHerm J d) + LocPot.ofFun (phT t)).rsmul (-1)) ∧
    IsPsh R.A (potOf R (fsHerm J d) + LocPot.ofFun (phT t)))

theorem exists_line (R : AnLogRes P ⊤ n) (c : R.X → R.X)
    (hc : ∀ x, SameOrbit (R.lift (c x) (c x)) (Cj.cj (R.lift x x))) (d : K → ℤ) (f : R.X → ℝ) (hf : R.A.Smooth f)
    (hfc : ∀ x, f (c x) = f x) : ∃ B : HermLine J, B.a = d ∧ IsSmoothHerm B ∧ IsConjInvariantH B ∧
      ∀ x, Real.log (B.h (R.lift x x)) = Real.log ((fsHerm J d).h (R.lift x x)) + f x := by
  obtain ⟨B, a0, hs, hl⟩ := exists_hermLine_log_eq_of_smooth _ _ _ n R f hf
  have hfs : IsSmoothHerm (fsHerm J d) := StepW.fsHerm_isSmoothHerm K J d
  have hmem : ∀ x, ∀ k, ∃ i, R.lift x x ⟨k, i⟩ ≠ 0 := fun x => (R.mem x x (R.mem_U x)).1
  have hB : ∀ x, Real.log ((Cj.conjAvg B).h (R.lift x x)) = f x := fun x => by
    rw [Cj.conjAvg_log _ (hmem x), ← FA.deg0_orbit B a0 (hc x), hl, hl, hfc]
    ring
  refine ⟨(fsHerm J d).tensor (Cj.conjAvg B), ?_, ?_, fun z => ?_, fun x => ?_⟩
  · show d + B.a = d
    rw [a0, add_zero]
  · exact ContDiffOn.mul hfs (Cj.conjAvg_smooth hs)
  · show (fsHerm J d).h _ * (Cj.conjAvg B).h _ = (fsHerm J d).h _ * (Cj.conjAvg B).h _
    rw [Cj.fs_conj d z, Cj.conjAvg_conj B z]
  · show Real.log ((fsHerm J d).h _ * (Cj.conjAvg B).h _) = _
    rw [Real.log_mul ((fsHerm J d).pos _ (hmem x)).ne' ((Cj.conjAvg B).pos _ (hmem x)).ne', hB]

theorem exists_member (hR : RegGlobalStatement) (R : AnLogRes P ⊤ n) (L : LocPot R.X) (s : R.X → R.X → ℂ) {nb : ℕ}
    (m : Fin nb → ℕ) (W : Fin nb → Set R.X) (hL : IsPotential R.A L) (hs : IsSection R.A L s)
    (snc : IsSNC R.A L s m W) (hn : ∀ y, logNormSec L s y ≤ 0)
    (hcb : ∀ x x', SameOrbit (R.lift x' x') (Cj.cj (R.lift x x)) → (x' ∈ bdry s ↔ x ∈ bdry s) ∧ rW L s x' = rW L s x)
    (d : K → ℤ) (u : R.X → ℝ) (cen : Prop)
    (huc : ∀ x x', SameOrbit (R.lift x' x') (Cj.cj (R.lift x x)) → u x' = u x)
    (hT : ∀ x, ∃ ψ a M, NChart R.A (R.U x) L s x ψ a M ∧ Tame a fun t => u (ψ.symm t))
    (hP : ∀ x ∉ bdry s, ∃ ψ : OpenPartialHomeomorph R.X (Fin n → ℂ), IsCompatChart R.A ψ ∧ x ∈ ψ.source ∧ ψ x = 0 ∧
      PshAt0 (fun t => Real.log ((fsHerm J d).h (R.lift x (ψ.symm t))) + u (ψ.symm t)) ∧
      (cen → PshAt0 fun t => -1 * (Real.log ((fsHerm J d).h (R.lift x (ψ.symm t))) + u (ψ.symm t)))) :
    ∃ ph phT line C₅ C t₀, IsMember R L s d u cen ph phT line C₅ C t₀ := by
  obtain ⟨hA, hfs, hΘ⟩ := fs_pos_potential K J P n R
  have hfd : IsSmoothHerm (fsHerm J d) := StepW.fsHerm_isSmoothHerm K J d
  have hth := hA _ hfd
  have hsys := isLiftSys R
  obtain ⟨c, hspec, hcont, hinv⟩ := GlobalTheory.T.lift_system_complex_conjugation hsys
  have hanal := GlobalTheory.T.conjugation_antiholomorphic_charts hsys c hspec hcont
  have hsm := smoothOn_of_tame hT
  obtain ⟨C₁, hC₁⟩ := size_of_tame hn hT
  have hpsh : IsPshOn R.A (bdry s)ᶜ (potOf R (fsHerm J d) + LocPot.ofFun u) := by
    refine pshOn_of_local _ (fun x z hz => ?_) fun z hz => ?_
    · obtain ⟨V, h1, h2, G, h3, h4⟩ := hth.2 x z z ⟨hz.1, R.mem_U z⟩
      refine ⟨V, h1, h2, G, h3, fun w hw => ?_⟩
      have := h4 w ⟨⟨hw.1.1, hw.1.2.1⟩, hw.2.1⟩
      show (potOf R (fsHerm J d)).φ x w + u w - ((potOf R (fsHerm J d)).φ z w + u w) = _
      linarith
    · obtain ⟨ψ, h1, h2, h3, h4, -⟩ := hP z hz
      exact ⟨ψ, h1, h2, h3, h4⟩
  obtain ⟨C₅, hsw⟩ := GlobalTheory.T.singular_potential_log_growth_psh n R.X R.A L s nb m W hL hs snc hn _ u C₁ hth hsm hpsh hC₁
  have hlines : ∀ (phT : ℝ → R.X → ℝ) (t₀ : ℝ), (∀ t, 0 < t → t ≤ t₀ → R.A.Smooth (phT t)) →
      (∀ t x, phT t (c x) = phT t x) → ∃ line : ℝ → HermLine J,
      (∀ t, (line t).a = d ∧ IsSmoothHerm (line t) ∧ IsConjInvariantH (line t)) ∧
      (∀ t, 0 < t → t ≤ t₀ → ∀ x, Real.log ((line t).h (R.lift x x)) =
        Real.log ((fsHerm J d).h (R.lift x x)) + phT t x) := by
    intro phT t₀ h1 h2
    have : ∀ t, ∃ B : HermLine J, (B.a = d ∧ IsSmoothHerm B ∧ IsConjInvariantH B) ∧ (0 < t → t ≤ t₀ → ∀ x,
        Real.log (B.h (R.lift x x)) = Real.log ((fsHerm J d).h (R.lift x x)) + phT t x) := fun t => by
      by_cases ht : 0 < t ∧ t ≤ t₀
      · obtain ⟨B, b1, b2, b3, b4⟩ := exists_line R c hspec d (phT t) (h1 t ht.1 ht.2) (h2 t)
        exact ⟨B, ⟨b1, b2, b3⟩, fun _ _ => b4⟩
      · exact ⟨fsHerm J d, ⟨rfl, hfd, Cj.fs_conj d⟩, fun a b => absurd ⟨a, b⟩ ht⟩
    choose line h3 h4 using this
    exact ⟨line, h3, h4⟩
  by_cases hcen : cen
  · have hneg : IsPshOn R.A (bdry s)ᶜ ((potOf R (fsHerm J d) + LocPot.ofFun u).rsmul (-1)) := by
      refine pshOn_of_local _ (fun x z hz => ?_) fun z hz => ?_
      · obtain ⟨V, h1, h2, G, h3, h4⟩ := hth.2 x z z ⟨hz.1, R.mem_U z⟩
        refine ⟨V, h1, h2, fun w => -G w, fun j y hy => (h3 j y hy).neg, fun w hw => ?_⟩
        have := h4 w ⟨⟨hw.1.1, hw.1.2.1⟩, hw.2.1⟩
        show -1 * ((potOf R (fsHerm J d)).φ x w + u w) - -1 * ((potOf R (fsHerm J d)).φ z w + u w) = _
        rw [Complex.neg_re]
        linarith
      · obtain ⟨ψ, h1, h2, h3, -, h4⟩ := hP z hz
        exact ⟨ψ, h1, h2, h3, h4 hcen⟩
    obtain ⟨u', C₀, hu', heq, p1, p2, s1, r1, c1⟩ := FA.central_regular R.A (potOf R (fsHerm J fun _ => 1)) L s m W
      hL hs snc hn (hA _ hfs) hΘ _ u C₅ hsw hneg
    have hc1 := Cj.smooth_continuous hu'
    have hd : Dense (bdry s)ᶜ := interior_eq_empty_iff_dense_compl.1 (LeviFormBoundaryTopology.interior_bdry_eq_empty hs snc)
    have hcp : ∀ y, u' (c y) = u' y :=
      congrFun (Continuous.ext_on hd (hc1.comp hcont) hc1 fun y hy => by
        have hy' : c y ∉ bdry s := fun h => hy ((hcb _ _ (hspec y)).1.1 h)
        show u' (c y) = u' y
        rw [heq _ hy', heq _ hy, huc _ _ (hspec y)])
    obtain ⟨line, l1, l2⟩ := hlines (fun _ => u') (Real.exp (-Real.exp 1)) (fun _ _ _ => hu') fun _ => hcp
    exact ⟨u', fun _ => u', line, C₀, C₀, _, s1, r1, c1, heq, l1, l2, fun _ _ => ⟨p2, p1⟩⟩
  · obtain ⟨B, hB⟩ := GlobalTheory.T.adapted_atlas_snc_section R.A L s m W hL hs snc hn
    obtain ⟨C₆, hg⟩ := GlobalTheory.T.adapted_atlas_smooth_potential_local n R.X R.A B L s nb m W hL hs snc hn hB u hsm fun x => by
      obtain ⟨ψ, a, M, h, ht⟩ := hT x
      obtain ⟨V', c, h1, h2, h3, h4⟩ := local_of_tame hn h ht
      exact ⟨ψ, V', c, h.1, h1, h2, h3, fun x' a b => (h4 x' a b).2⟩
    obtain ⟨m₁, -, -⟩ := enlarging_constants_smooth_members n R.X R.A (potOf R (fsHerm J fun _ => 1)) L s nb m W
      hL hs snc hn (hA _ hfs) hΘ
    have hsw' := m₁ _ _ _ _ (le_max_left C₅ C₆) hsw
    obtain ⟨C, t₀, phT, r, c2⟩ := hR R.A B _ L s m W (hA _ hfs) hΘ hL hs snc hn hB _ u _ hsw' (hg _ (le_max_right _ _))
    have hthc := GlobalTheory.T.lift_system_real_structure hsys c hspec hcont hanal (fsHerm J d) (Cj.fs_conj d) (potOf R (fsHerm J d)) fun x =>
      ⟨Set.univ, isOpen_univ, trivial, fun _ => 0, fun _ => analyticOnNhd_const,
        fun z _ => (sub_self _).trans Complex.zero_re.symm⟩
    obtain ⟨C', t', r', c'⟩ := GlobalTheory.T.conjugation_invariant_singular_potential n R.X R.A _ L s nb m W hL hs snc hn (hA _ hfs) hΘ c hcont hinv hanal
      (fun y => (hcb _ _ (hspec y)).1) (fun y => (hcb _ _ (hspec y)).2) _ u phT C t₀ hth hthc
      (fun y _ => huc _ _ (hspec y)) r c2
    obtain ⟨line, l1, l2⟩ := hlines (fun t y => (phT t y + phT t (c y)) / 2) t' (fun t h0 h1 => (r'.2.2 t h0 h1).1)
      fun t x => by rw [hinv, add_comm]
    exact ⟨u, _, line, C₅, C', t', hsw, r', c', fun _ _ => rfl, l1, l2, fun h => absurd h hcen⟩

theorem IsMember.mono {R : AnLogRes P ⊤ n} {L : LocPot R.X} {s : R.X → R.X → ℂ} {nb : ℕ}
    {m : Fin nb → ℕ} {W : Fin nb → Set R.X} (hL : IsPotential R.A L) (hs : IsSection R.A L s)
    (snc : IsSNC R.A L s m W) (hn : ∀ y, logNormSec L s y ≤ 0) {d : K → ℤ} {u : R.X → ℝ} {cen : Prop}
    {ph : R.X → ℝ} {phT : ℝ → R.X → ℝ} {line : ℝ → HermLine J} {C₅ C t₀ D₅ D T : ℝ}
    (h : IsMember R L s d u cen ph phT line C₅ C t₀) (h₅ : C₅ ≤ D₅) (hD : |C| ≤ D) (hT0 : 0 < T) (hT : T ≤ t₀)
    (hT1 : T ≤ Real.exp (-1)) : IsMember R L s d u cen ph phT line D₅ D T := by
  obtain ⟨hA, hfs, hΘ⟩ := fs_pos_potential K J P n R
  obtain ⟨m₁, m₂, -⟩ := enlarging_constants_smooth_members n R.X R.A (potOf R (fsHerm J fun _ => 1)) L s nb m W
    hL hs snc hn (hA _ hfs) hΘ
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := h
  exact ⟨m₁ _ _ _ _ h₅ a1, m₂ _ _ _ _ _ _ _ hD hT0 hT hT1 a2 a1.1, a3, a4, a5, fun t h0 h1 => a6 t h0 (h1.trans hT), a7⟩

theorem member_zero (R : AnLogRes P ⊤ n) {L : LocPot R.X} {s : R.X → R.X → ℂ} {nb : ℕ}
    {m : Fin nb → ℕ} {W : Fin nb → Set R.X} (hL : IsPotential R.A L) (hs : IsSection R.A L s)
    (snc : IsSNC R.A L s m W) (hn : ∀ y, logNormSec L s y ≤ 0) (d : K → ℤ)
    (hd : IsPosPot R.A (potOf R (fsHerm J d))) :
    ∃ C₅ C t₀, IsMember R L s d 0 False 0 (fun _ => 0) (fun _ => fsHerm J d) C₅ C t₀ := by
  obtain ⟨hA, hfs, hΘ⟩ := fs_pos_potential K J P n R
  have hfd : IsSmoothHerm (fsHerm J d) := StepW.fsHerm_isSmoothHerm K J d
  obtain ⟨-, -, m₃⟩ := enlarging_constants_smooth_members n R.X R.A (potOf R (fsHerm J fun _ => 1)) L s nb m W
    hL hs snc hn (hA _ hfs) hΘ
  have hsm0 : R.A.Smooth (0 : R.X → ℝ) := fun jj => by
    show ContDiffOn ℝ _ (fun _ => (0 : ℝ)) _
    exact contDiffOn_const
  have hpsh0 : IsPsh R.A (potOf R (fsHerm J d) + LocPot.ofFun (0 : R.X → ℝ)) := by
    intro x jj z hz w
    have e1 : (potOf R (fsHerm J d) + LocPot.ofFun (0 : R.X → ℝ)).φ x ∘ (R.A.chart jj).symm =
        (potOf R (fsHerm J d)).φ x ∘ (R.A.chart jj).symm := by
      funext u
      show (potOf R (fsHerm J d)).φ x _ + (0 : ℝ) = _
      rw [add_zero]
      rfl
    rw [e1]
    by_cases hw : w = 0
    · rw [hw, levi_zero]
    · exact (hd x jj z ⟨hz.1, hz.2.1⟩ w hw).le
  obtain ⟨C₀, s0, r0, c0⟩ := m₃ _ 0 (hA _ hfd) hsm0 hpsh0
  exact ⟨C₀, C₀, _, s0, r0, c0, fun _ _ => rfl, fun _ => ⟨rfl, hfd, Cj.fs_conj d⟩,
    fun _ _ _ _ => (add_zero _).symm, False.elim⟩

theorem common_members {σ : Type} [Finite σ] {R : AnLogRes P ⊤ n} {L : LocPot R.X} {s : R.X → R.X → ℂ} {nb : ℕ}
    {m : Fin nb → ℕ} {W : Fin nb → Set R.X} (hL : IsPotential R.A L) (hs : IsSection R.A L s)
    (snc : IsSNC R.A L s m W) (hn : ∀ y, logNormSec L s y ≤ 0) {d : σ → K → ℤ} {u : σ → R.X → ℝ} {cen : σ → Prop}
    {ph : σ → R.X → ℝ} {phT : σ → ℝ → R.X → ℝ} {line : σ → ℝ → HermLine J}
    (h : ∀ a, ∃ C₅ C t₀, IsMember R L s (d a) (u a) (cen a) (ph a) (phT a) (line a) C₅ C t₀) :
    ∃ C₅ C t₀, ∀ a, IsMember R L s (d a) (u a) (cen a) (ph a) (phT a) (line a) C₅ C t₀ := by
  choose C₅ C t₀ hm using h
  obtain ⟨D₅, hD₅⟩ := FA.common_bound C₅
  obtain ⟨D, hD⟩ := FA.common_bound fun a => |C a|
  obtain ⟨T, hT0, hT⟩ := FA.common_scale (fun o : Option σ => o.elim (Real.exp (-1)) t₀) (by
    rintro (_ | p)
    · exact Real.exp_pos _
    · exact (hm p).2.1.1)
  exact ⟨D₅, D, T, fun a => (hm a).mono hL hs snc hn (hD₅ a) (hD a) hT0 (hT (some a)) (hT none)⟩

end AnalyticReference.An
end
end
end

-- Source module: Development.WeilBound.CoreStatements.CentralCharts.OneLeDimFl

section

@[expose] public section

noncomputable section

namespace AnalyticReference.An

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB Filter Topology Metric

theorem weight_orbit {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {σ : Type} (S : Finset σ)
    (A : σ → HermLine J) {z z' : (Σ k, J k) → ℂ} (hz : ∀ k, ∃ i, z' ⟨k, i⟩ ≠ 0) (h : SameOrbit z z') :
    -∑ k ∈ S, Real.log ((A k).h z) - Real.log ((fsHerm J (-∑ k ∈ S, (A k).a)).h z) =
      -∑ k ∈ S, Real.log ((A k).h z') - Real.log ((fsHerm J (-∑ k ∈ S, (A k).a)).h z') := by
  obtain ⟨c, hc, rfl⟩ := h
  have e : ∀ B : HermLine J, Real.log (B.h fun p => c p.1 * z' p) =
      ∑ k, (B.a k : ℝ) * Real.log ‖c k‖ + Real.log (B.h z') := fun B => by
    rw [B.smul c z' hc, Real.log_mul (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (hc k)))
      (B.pos z' hz).ne', Real.log_prod fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (hc k))]
    simp only [Real.log_zpow]
  simp only [e, Finset.sum_add_distrib]
  have : ∑ k, (((fsHerm J (-∑ k ∈ S, (A k).a)).a k : ℤ) : ℝ) * Real.log ‖c k‖ =
      -∑ j ∈ S, ∑ k, ((A j).a k : ℝ) * Real.log ‖c k‖ := by
    have e2 : ∀ k, (fsHerm J (-∑ j ∈ S, (A j).a)).a k = -∑ j ∈ S, (A j).a k := fun k => by
      show (-∑ j ∈ S, (A j).a : K → ℤ) k = _
      simp [Finset.sum_apply]
    simp only [e2]
    rw [Finset.sum_comm]
    simp [Finset.sum_mul]
  rw [this]
  ring

theorem one_le_dimFl {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) {N : ℕ} (hN : 2 ≤ N) :
    1 ≤ Top.dimFl (CMType H) N := by
  have h1 : Fintype.card (CMType H) = Module.finrank ℚ E / 2 := by
    rw [Fintype.card_eq_nat_card]; exact GlobalTheory.PeriodCoord.card_cmType H
  have h2 : 2 ≤ Module.finrank ℚ E := by
    have := IsTotallyComplex.finrank E
    have h0 : 0 < Module.finrank ℚ E := Module.finrank_pos
    omega
  have h3 : 2 * 1 ≤ N * (N - 1) := Nat.mul_le_mul hN (by omega)
  unfold Top.dimFl
  exact Nat.mul_pos (by omega) (by omega)

theorem of_local (hI : PB.Inputs) {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {l : Tor.Level H} {Xo : Moduli D l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)}
    (hp : 1 ≤ D.p) (hq : 1 ≤ D.q) (G : RefGeo Y) (sing : RootIx D → HermLine G.J)
    (hdeg : ∀ r, (sing r).a = G.xdeg r) (hhodge : ∀ r, G.Fl.IsHodgeLine r (G.e r) (sing r))
    (hconj : ∀ r, IsConjInvariantH (sing r))
    (hloc : ∀ (χ : SncChart (mCoordIdeal G.y) (Top.dimFl (CMType H) (D.p + D.q)) (mcPts G.bd)) (τ : CMType H)
      (i : Fin (D.p + D.q)),
      Tame χ.a (fun t => -∑ k ∈ Finset.Iic i, Real.log ((sing (τ, k)).h (χ.γ t))) ∧
      (χ.a = 0 → PshAt0 (fun t => -∑ k ∈ Finset.Iic i, Real.log ((sing (τ, k)).h (χ.γ t))) ∧
        ((i : ℕ) + 1 = D.p + D.q → PshAt0 fun t => ∑ k ∈ Finset.Iic i, Real.log ((sing (τ, k)).h (χ.γ t))))) :
    ∃ A : G.An, (∃ inv : A.Sys.X → A.Re.R.X, ReciprocityTheory.AnForm.M.HoloMap A.Sys.A A.Re.R.A inv ∧
      ∀ x, inv (A.Re.π x) = x) := by
  classical
  have harith := GlobalTheory.T.isArithVar_of_snc_model G.𝔐.X G.Ω G.𝔐.ξ G.K G.J G.y _ G.bd (one_le_dimFl H (by omega)) G.𝔐.tie G.snc
  obtain ⟨y1, y2, y3⟩ := GlobalTheory.T.boundary_points_closed G.𝔐.X G.Ω G.𝔐.ξ G.K G.J G.y (abLocus G.𝔐.t.G) G.bd G.𝔐.tie G.bd_iff
  obtain ⟨R, L, s, nb, m, W, hL, hs, snc, hn, hbd, hrc⟩ := GlobalTheory.T.lowerBound_height_on_boundary G.K G.J G.Ω G.y _ G.bd G.snc harith y1 y2 y3
  have hmem : ∀ x, R.lift x x ∈ mcPts (mCoordIdeal G.y) := fun x => R.mem x x (R.mem_U x)
  have horb : ∀ z ∈ mcPts (mCoordIdeal G.y), ∀ z', SameOrbit z' z → z ∈ mcPts G.bd → z' ∈ mcPts G.bd := by
    rintro z hz z' ⟨c, hc, rfl⟩ h
    exact (y2 z ⟨hz, h⟩ c hc).2
  have hBd : ∀ x₀, ∀ x ∈ R.U x₀, R.lift x₀ x ∈ mcPts G.bd ↔ x ∈ bdry s := fun x₀ x hx => by
    rw [hbd]
    exact ⟨horb _ (R.mem _ _ hx) _ (R.compat _ _ _ ⟨R.mem_U _, hx⟩),
      horb _ (hmem x) _ (R.compat _ _ _ ⟨hx, R.mem_U _⟩)⟩
  have hcb1 : ∀ x x', SameOrbit (R.lift x' x') (Cj.cj (R.lift x x)) → x ∈ bdry s → x' ∈ bdry s := fun x x' h hx => by
    rw [hbd] at hx ⊢
    have := y3 _ ⟨hmem x, hx⟩
    exact horb _ this.1 _ h this.2
  have hcb : ∀ x x', SameOrbit (R.lift x' x') (Cj.cj (R.lift x x)) →
      (x' ∈ bdry s ↔ x ∈ bdry s) ∧ rW L s x' = rW L s x := fun x x' h =>
    ⟨⟨hcb1 x' x (by
      have := Cj.sameOrbit_symm (Cj.sameOrbit_cj h)
      rwa [Cj.cj_cj] at this), hcb1 x x' h⟩, hrc x x' h⟩
  have hemb : Cmp.IsEmbedded R.A (mCoordIdeal G.y) R.U R.lift :=
    ⟨R.isOpen_U, R.mem_U, R.holo, R.mem, R.compat, fun z hz => R.surj z hz (not_mem_top _),
      fun x x' h => R.inj x x' (not_mem_top _) h, fun x p hp j hj => R.immersion x (not_mem_top _) p hp j hj⟩
  have hpos : IsPosPot R.A (potOf R (fsHerm G.J (Pi.single G.k₀ 1))) := isPosPot_block R G.k₀ fun x p hp j hj =>
    (GlobalTheory.T.holomorphic_atlas_coord_compat G.𝔐.X G.Ω G.𝔐.ξ G.K G.J G.y G.k₀ G.𝔐.tie G.embeds _ R.X R.A R.U R.lift hemb (G.J G.k₀)
      (Equiv.refl _) x p hp j hj).2
  let d : RootIx D → G.K → ℤ := fun r => -∑ k ∈ Finset.Iic r.2, (sing (r.1, k)).a
  let wt : RootIx D → ((Σ k, G.J k) → ℂ) → ℝ := fun r z =>
    -∑ k ∈ Finset.Iic r.2, Real.log ((sing (r.1, k)).h z) - Real.log ((fsHerm G.J (d r)).h z)
  have hwt : ∀ r z z', (∀ k, ∃ i, z' ⟨k, i⟩ ≠ 0) → SameOrbit z z' → wt r z = wt r z' := fun r z z' hz h =>
    weight_orbit (Finset.Iic r.2) (fun k => sing (r.1, k)) hz h
  let u : RootIx D → R.X → ℝ := fun r x => wt r (R.lift x x)
  have hu : ∀ r x₀, ∀ x ∈ R.U x₀, u r x = wt r (R.lift x₀ x) := fun r x₀ x hx =>
    hwt r _ _ (R.mem _ _ hx).1 (R.compat _ _ _ ⟨R.mem_U _, hx⟩)
  have hball : ∀ᶠ t in 𝓝 (0 : Fin (Top.dimFl (CMType H) (D.p + D.q)) → ℂ), t ∈ ball 0 1 :=
    isOpen_ball.mem_nhds (mem_ball_self one_pos)
  have hsome : ∀ r : RootIx D, ∃ ph phT line C₅ C t₀,
      IsMember R L s (d r) (u r) ((r.2 : ℕ) + 1 = D.p + D.q) ph phT line C₅ C t₀ := by
    intro r
    refine exists_member hI.regGlobal R L s m W hL hs snc hn hcb _ _ _ (fun x x' h => ?_) (fun x => ?_) fun x hx => ?_
    · show wt r _ = wt r _
      rw [hwt r _ _ (Cj.cj_nonzero (hmem x).1) h]
      simp only [wt]
      rw [Cj.fs_conj (d r) (R.lift x x)]
      congr 2
      exact Finset.sum_congr rfl fun k _ => congrArg Real.log (hconj _ _)
    · obtain ⟨ψ, a, M, h⟩ := exists_nchart R.A L s hL hs snc x (R.U x) (R.isOpen_U x) (R.mem_U x)
      refine ⟨ψ, a, M, h, ?_⟩
      have t1 : Tame a _ := (hloc (h.snc R _ (hBd x)) r.1 r.2).1
      have t2 : Tame a fun t => Real.log ((fsHerm G.J (d r)).h (R.lift x (ψ.symm t))) := tame_smooth a fun t ht => by
        obtain ⟨h1, h2, -⟩ := h.2.2.2.2 t ht
        have hz := (R.mem _ _ h2).1
        have hopen : {z : (Σ k, G.J k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} ∈ 𝓝 (R.lift x (ψ.symm t)) := by
          refine Filter.eventually_all.mpr fun k => ?_
          obtain ⟨i, hi⟩ := hz k
          exact Filter.mem_of_superset (((continuous_apply _).isOpen_preimage _ isOpen_ne).mem_nhds hi)
            fun y hy => ⟨i, hy⟩
        have h3 := ((StepW.fsHerm_isSmoothHerm G.K G.J (d r)).contDiffAt hopen).log ((fsHerm G.J (d r)).pos _ hz).ne'
        exact h3.comp t ((analyticAt_lift R h.1 x h1 h2).restrictScalars (𝕜 := ℝ)).contDiffAt
      refine (t1.add (t2.const_mul (-1))).congr ?_
      filter_upwards [hball] with t ht _
      rw [hu r x _ (h.2.2.2.2 t ht).2.1]
      show _ - _ = -∑ k ∈ Finset.Iic r.2, Real.log ((sing (r.1, k)).h (R.lift x (ψ.symm t))) + _
      ring
    · obtain ⟨ψ, a, M, h⟩ := exists_nchart R.A L s hL hs snc x (R.U x) (R.isOpen_U x) (R.mem_U x)
      obtain ⟨p1, p2⟩ := (hloc (h.snc R _ (hBd x)) r.1 r.2).2 (h.zero_of_not_mem hx)
      refine ⟨ψ, h.1, h.2.1, h.2.2.1, p1.congr ?_, fun hc => (p2 hc).congr ?_⟩
      · filter_upwards [hball] with t ht
        rw [hu r x _ (h.2.2.2.2 t ht).2.1]
        show _ + (_ - _) = -∑ k ∈ Finset.Iic r.2, Real.log ((sing (r.1, k)).h (R.lift x (ψ.symm t)))
        ring
      · filter_upwards [hball] with t ht
        rw [hu r x _ (h.2.2.2.2 t ht).2.1]
        show -1 * (_ + (-∑ k ∈ Finset.Iic r.2, Real.log ((sing (r.1, k)).h (R.lift x (ψ.symm t))) - _)) =
          ∑ k ∈ Finset.Iic r.2, Real.log ((sing (r.1, k)).h (R.lift x (ψ.symm t)))
        ring
  choose ph phT line hm using hsome
  obtain ⟨C₅, C, T, hM⟩ := common_members (σ := Option (RootIx D)) (R := R) hL hs snc hn
    (d := fun o => o.elim (Pi.single G.k₀ 1) d) (u := fun o => o.elim 0 u)
    (cen := fun o => o.elim False fun r => (r.2 : ℕ) + 1 = D.p + D.q) (ph := fun o => o.elim 0 ph)
    (phT := fun o => o.elim (fun _ => 0) phT)
    (line := fun o => o.elim (fun _ => fsHerm G.J (Pi.single G.k₀ 1)) line) (by
      rintro (_ | r)
      · exact member_zero R hL hs snc hn _ hpos
      · exact hm r)
  obtain ⟨hA, hfs, hΘ⟩ := fs_pos_potential G.K G.J _ _ R
  let S : AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D)) :=
    { X := R.X
      A := R.A
      Θ := potOf R (fsHerm G.J fun _ => 1)
      L := L
      s := s
      nb := nb
      m := m
      W := W
      potΘ := hA _ hfs
      posΘ := hΘ
      potL := hL
      sec := hs
      snc := snc
      norm_le := hn
      th := fun o => potOf R (fsHerm G.J (o.elim (Pi.single G.k₀ 1) d))
      ph := fun o => o.elim 0 ph
      phT := fun o => o.elim (fun _ => 0) phT
      C₅ := C₅
      C := C
      t₀ := T
      sing := fun o => (hM o).1
      reg := fun o => (hM o).2.1
      c2 := fun o => (hM o).2.2.1 }
  let Re : Realis S (mCoordIdeal G.y) :=
    { arith := harith
      J := ⊤
      R := R
      π := id
      holo := ⟨continuous_id, fun jj k => R.A.holo jj k⟩
      deg := 1
      deg_pos := one_pos
      br := ∅
      degree := FA.degree_id_self R.A
      ref := fun o => fsHerm G.J (o.elim (Pi.single G.k₀ 1) d)
      ref_smooth := fun o => StepW.fsHerm_isSmoothHerm G.K G.J _
      ref_pot := fun o x _ => ⟨Set.univ, isOpen_univ, trivial, fun _ => 0, fun _ => analyticOnNhd_const,
          fun z _ => (sub_self _).trans Complex.zero_re.symm⟩
      line := fun o => o.elim (fun _ => fsHerm G.J (Pi.single G.k₀ 1)) line
      line_deg := fun o t => ((hM o).2.2.2.2.1 t).1
      line_smooth := fun o t _ _ => ((hM o).2.2.2.2.1 t).2.1
      line_eq := fun o t h0 h1 x => (hM o).2.2.2.2.2.1 t h0 h1 x }
  have hnd : (Pi.single G.k₀ 1 : G.K → ℤ) G.k₀ = 1 ∧ ∀ k, k ≠ G.k₀ → (Pi.single G.k₀ 1 : G.K → ℤ) k = 0 :=
    ⟨by simp, fun k hk => by simp [hk]⟩
  refine ⟨{ sing := sing, sing_deg := hdeg, hodge := hhodge, Sys := S, Re := Re, J_top := rfl, deg_one := rfl
            π_bij := Function.bijective_id, embedded := hemb, interior := fun x z hz => ?_
            fund_deg := fun τ i => ?_, fund_sing := fun τ i x hx => ?_
            conj := fun o t => ((hM o).2.2.2.2.1 t).2
            none_deg := hnd
            none_h := fun z => fs_single_h G.k₀ z, pos := hpos, ph_none := fun x => ⟨rfl, fun _ => rfl⟩
            flat := fun τ i hi t => (hM (some (τ, i))).2.2.2.2.2.2 hi t },
    id, ⟨continuous_id, fun jj k => R.A.holo jj k⟩, fun _ => rfl⟩
  · have h1 := G.bd_iff z _ hz
    show _ ↔ ¬ x ∈ bdry s
    rw [hbd]
    tauto
  · show d (τ, i) = _
    simp only [d, hdeg]
  · have h1 : ph (τ, i) x = u (τ, i) x := (hM (some (τ, i))).2.2.2.1 x hx
    show Real.log ((fsHerm G.J (d (τ, i))).h (R.lift x x)) + ph (τ, i) x =
      -∑ k ∈ Finset.Iic i, Real.log ((sing (τ, k)).h (R.lift x x))
    rw [h1]
    simp only [u, wt]
    ring

end AnalyticReference.An
end
end
end
