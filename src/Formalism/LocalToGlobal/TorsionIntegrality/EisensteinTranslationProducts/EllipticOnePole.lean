module

public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.ThetaLine
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.Elliptic
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.ThetaLine
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.AnalyticIdentityTheoremsZetaFacts
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
import Mathlib.Tactic.Lemma
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
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.PDeriv
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.SigmaAdd
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Legendre
public import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.ThreeTermNumEqTwistedGammaOfSigmaZero
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.QuasiPeriodConstUnique
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.SigmaLogDeriv2

-- Source module: Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.OnePole

section

section

noncomputable section
open Filter Topology

namespace Formalism.L2.Th1.F
namespace OnePole

open AnalyticIdentityTheoremsZetaFacts

lemma eq_of_eventuallyEq_nhdsNE {g₁ g₂ : ℂ → ℂ} {z : ℂ} (h₁ : ContinuousAt g₁ z)
    (h₂ : ContinuousAt g₂ z) (h : g₁ =ᶠ[𝓝[≠] z] g₂) : g₁ z = g₂ z := by
  exact tendsto_nhds_unique (h₁.tendsto.mono_left nhdsWithin_le_nhds)
    ((h₂.tendsto.mono_left nhdsWithin_le_nhds).congr' h.symm)

lemma tendsto_add_nhdsNE (z ω : ℂ) : Tendsto (fun w : ℂ => w + ω) (𝓝[≠] z) (𝓝[≠] (z + ω)) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    ((continuous_add_const ω).continuousAt.tendsto.mono_left nhdsWithin_le_nhds) ?_
  filter_upwards [self_mem_nhdsWithin] with w hw
  simpa using hw

lemma eventually_notMem (L : PeriodPair) (p z : ℂ) : ∀ᶠ w in 𝓝[≠] z, w - p ∉ L.lattice := by
  have hx : ∀ x : ℂ, ∀ᶠ u in 𝓝[≠] x, u ∉ L.lattice := by
    intro x
    by_cases hx : x ∈ L.lattice
    · have hd : DiscreteTopology (L.lattice : Set ℂ) := (inferInstance : DiscreteTopology L.lattice)
      exact Filter.inf_principal_eq_bot.1 ((discreteTopology_subtype_iff.1 hd) x hx)
    · exact eventually_nhdsWithin_of_eventually_nhds ((L.isClosed_lattice.isOpen_compl).mem_nhds hx)
  have := (tendsto_add_nhdsNE z (-p)).eventually (hx (z + -p))
  simpa [sub_eq_add_neg] using this

lemma analyticAt_wZeta (L : PeriodPair) (z : ℂ) (hz : z ∉ L.lattice) : AnalyticAt ℂ (wZeta L) z := by
  exact (differentiableOn_wZeta L).analyticAt ((L.isClosed_lattice.isOpen_compl).mem_nhds hz)

lemma analyticAt_zetaExcept (L : PeriodPair) : AnalyticAt ℂ (zetaExcept L 0) 0 := by
  refine (differentiableOn_zetaExcept L 0).analyticAt ?_
  filter_upwards [eventually_nhdsWithin_iff.1 (eventually_notMem L 0 0)] with w hw
  simp only [Set.mem_compl_iff, Set.mem_diff, Set.mem_singleton_iff, SetLike.mem_coe, not_and, not_not]
  intro hmem
  by_contra hne
  exact hw hne (by simpa using hmem)

lemma zeta_local (hq : ZetaQuasi) (L : PeriodPair) (p z₀ : ℂ) (h : z₀ - p ∈ L.lattice) :
    ∀ᶠ w in 𝓝[≠] z₀,
      wZeta L (w - p) = zetaExcept L 0 (w - z₀) + 1 / (w - z₀) + wEta L (z₀ - p) := by
  filter_upwards [eventually_notMem L z₀ z₀] with w hw
  rw [show w - p = w - z₀ + (z₀ - p) by ring, hq L (z₀ - p) (w - z₀) h hw, ← zetaExcept_zero_add]

lemma simple_local {f : ℂ → ℂ} {p : ℂ} (hf : MeromorphicAt f p) (ho : -1 ≤ meromorphicOrderAt f p) :
    ∃ (r : ℂ) (k : ℂ → ℂ), AnalyticAt ℂ k p ∧ ∀ᶠ w in 𝓝[≠] p, f w = r / (w - p) + k w := by
  cases h : meromorphicOrderAt f p with
  | top =>
    refine ⟨0, fun _ => 0, analyticAt_const, ?_⟩
    filter_upwards [meromorphicOrderAt_eq_top_iff.1 h] with w hw
    simp [hw]
  | coe n =>
    obtain ⟨g, hg, -, hfg⟩ := (meromorphicOrderAt_eq_int_iff hf).1 h
    have hn : (-1 : ℤ) ≤ n := by
      rw [h] at ho
      have h2 : ((-1 : ℤ) : WithTop ℤ) ≤ (n : WithTop ℤ) := by simpa using ho
      exact WithTop.coe_le_coe.1 h2
    rcases eq_or_lt_of_le hn with hn | hn
    · subst hn
      obtain ⟨q, hq⟩ := hg
      refine ⟨g p, dslope g p, ⟨_, hq.has_fpower_series_dslope_fslope⟩, ?_⟩
      filter_upwards [hfg, self_mem_nhdsWithin] with w hw hwp
      have hwp' : w ≠ p := hwp
      have hne : w - p ≠ 0 := sub_ne_zero.2 hwp'
      rw [hw, zpow_neg_one, smul_eq_mul, dslope_of_ne _ hwp', slope_def_field]
      field_simp
      ring
    · have hn0 : 0 ≤ n := by omega
      lift n to ℕ using hn0
      refine ⟨0, fun w => (w - p) ^ n * g w, by fun_prop, ?_⟩
      filter_upwards [hfg] with w hw
      rw [hw]
      simp [zpow_natCast, smul_eq_mul]

end OnePole

open OnePole AnalyticIdentityTheoremsZetaFacts

theorem ellipticOnePole_of (hN : EllipticNoPole) (hE : EllipticEntire) (hq : ZetaQuasi)
    (hL : Legendre) : EllipticOnePole := by
  intro L f p hmer hper hord hp
  obtain ⟨r, k, hk, hfk⟩ := simple_local (hmer p) hp
  set g : ℂ → ℂ := fun w => f w - r * wZeta L (w - p) with hg

  have hB : ∀ z, 0 ≤ meromorphicOrderAt f z →
      ∃ B : ℂ → ℂ, AnalyticAt ℂ B z ∧ f =ᶠ[𝓝[≠] z] B := by
    intro z hz
    cases h : meromorphicOrderAt f z with
    | top =>
      exact ⟨fun _ => 0, analyticAt_const, meromorphicOrderAt_eq_top_iff.1 h⟩
    | coe n =>
      obtain ⟨B, hBa, -, hfB⟩ := (meromorphicOrderAt_eq_int_iff (hmer z)).1 h
      have hn : 0 ≤ n := by rw [h] at hz; exact_mod_cast hz
      lift n to ℕ using hn
      refine ⟨fun w => (w - z) ^ n * B w, by fun_prop, ?_⟩
      filter_upwards [hfB] with w hw
      rw [hw]
      simp [zpow_natCast, smul_eq_mul]

  have hloc : ∀ z, ∃ A : ℂ → ℂ, AnalyticAt ℂ A z ∧ g =ᶠ[𝓝[≠] z] A := by
    intro z
    by_cases hz : z - p ∈ L.lattice
    · refine ⟨fun w => k (w - (z - p)) - r * zetaExcept L 0 (w - z) - r * wEta L (z - p), ?_, ?_⟩
      · have h1 : AnalyticAt ℂ (fun w => k (w - (z - p))) z := by
          have hk' : AnalyticAt ℂ k (z - (z - p)) := by simpa using hk
          exact AnalyticAt.comp (f := fun w : ℂ => w - (z - p)) (g := k) hk' (by fun_prop)
        have h2 : AnalyticAt ℂ (fun w => zetaExcept L 0 (w - z)) z := by
          have hz' : AnalyticAt ℂ (zetaExcept L 0) (z - z) := by simpa using analyticAt_zetaExcept L
          exact AnalyticAt.comp (f := fun w : ℂ => w - z) (g := zetaExcept L 0) hz' (by fun_prop)
        exact (h1.sub (analyticAt_const.mul h2)).sub analyticAt_const
      · have hshift : Tendsto (fun w : ℂ => w - (z - p)) (𝓝[≠] z) (𝓝[≠] p) := by
          have h' := tendsto_add_nhdsNE z (-(z - p))
          rw [show z + -(z - p) = p by ring] at h'
          simpa only [← sub_eq_add_neg] using h'
        filter_upwards [hshift.eventually hfk, zeta_local hq L p z hz] with w hw1 hw2
        have hfw : f w = f (w - (z - p)) := by
          have := hper (z - p) hz (w - (z - p))
          rw [sub_add_cancel] at this
          exact this
        show f w - r * wZeta L (w - p) = _
        rw [hfw, hw1, hw2, show w - (z - p) - p = w - z by ring]
        ring
    · obtain ⟨B, hBa, hfB⟩ := hB z (hord z hz)
      refine ⟨fun w => B w - r * wZeta L (w - p), ?_, ?_⟩
      · have : AnalyticAt ℂ (wZeta L) (z - p) := analyticAt_wZeta L _ hz
        exact hBa.sub (analyticAt_const.mul
          (AnalyticAt.comp (f := fun w : ℂ => w - p) (g := wZeta L) this (by fun_prop)))
      · filter_upwards [hfB] with w hw
        show f w - r * wZeta L (w - p) = _
        rw [hw]

  set G : ℂ → ℂ := fun w => limUnder (𝓝[≠] w) g with hG
  have hGA : ∀ z, ∀ A : ℂ → ℂ, AnalyticAt ℂ A z → g =ᶠ[𝓝[≠] z] A → G =ᶠ[𝓝 z] A := by
    intro z A hA hgA
    have h1 : ∀ᶠ y in 𝓝 z, y ∈ ({z}ᶜ : Set ℂ) → g y = A y := eventually_nhdsWithin_iff.1 hgA
    filter_upwards [eventually_eventually_nhds.2 h1, hA.eventually_analyticAt] with w hw hAw
    show limUnder (𝓝[≠] w) g = A w
    apply Tendsto.limUnder_eq
    by_cases hwz : w = z
    · subst hwz
      exact (hAw.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' hgA.symm
    · have hgw : g =ᶠ[𝓝[≠] w] A := by
        apply eventually_nhdsWithin_of_eventually_nhds
        filter_upwards [hw, isOpen_ne.mem_nhds hwz] with y hy hyz
        exact hy hyz
      exact (hAw.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' hgw.symm
  have hGd : Differentiable ℂ G := fun z => by
    obtain ⟨A, hA, hgA⟩ := hloc z
    exact hA.differentiableAt.congr_of_eventuallyEq (hGA z A hA hgA)
  have hgG : ∀ z, g =ᶠ[𝓝[≠] z] G := fun z => by
    obtain ⟨A, hA, hgA⟩ := hloc z
    filter_upwards [hgA, nhdsWithin_le_nhds (hGA z A hA hgA)] with w h1 h2
    rw [h1, h2]

  have hGq : ∀ ω ∈ L.lattice, ∀ w, G (w + ω) = G w - r * wEta L ω := by
    intro ω hω w
    refine eq_of_eventuallyEq_nhdsNE (g₁ := fun y => G (y + ω)) (g₂ := fun y => G y - r * wEta L ω)
      (hGd.continuous.comp (continuous_add_const ω)).continuousAt
      (hGd.continuous.sub continuous_const).continuousAt ?_
    filter_upwards [(tendsto_add_nhdsNE w ω).eventually (hgG (w + ω)), hgG w,
      eventually_notMem L p w] with y h1 h2 h3
    show G (y + ω) = G y - r * wEta L ω
    rw [← h1, ← h2]
    show f (y + ω) - r * wZeta L (y + ω - p) = f y - r * wZeta L (y - p) - r * wEta L ω
    rw [hper ω hω y, show y + ω - p = (y - p) + ω by ring, hq L ω (y - p) hω h3]
    ring

  have hDd : Differentiable ℂ (deriv G) := fun z => ((hGd.analyticAt z).deriv).differentiableAt
  have hDp : IsPeriodic L (deriv G) := by
    intro ω hω z
    have hfun : (fun y => G (y + ω)) = fun y => G y - r * wEta L ω := funext fun y => hGq ω hω y
    rw [← deriv_comp_add_const, hfun, deriv_sub_const]
  have hDc := hE L (deriv G) hDd hDp
  set a := deriv G 0 with ha
  have hlin : ∀ w, G w = a * w + G 0 := by
    have hH : Differentiable ℂ (fun w => G w - a * w) := hGd.sub (differentiable_id.const_mul a)
    have hH' : ∀ x, deriv (fun w => G w - a * w) x = 0 := by
      intro x
      have h1 : HasDerivAt G a x := by rw [← hDc x]; exact (hGd x).hasDerivAt
      have h2 : HasDerivAt (fun w : ℂ => a * w) (a * 1) x := (hasDerivAt_id' x).const_mul a
      have h3 : HasDerivAt (fun w => G w - a * w) (a - a * 1) x := h1.sub h2
      rw [h3.deriv]
      ring
    intro w
    have := is_const_of_deriv_eq_zero hH hH' w 0
    simp only [mul_zero, sub_zero] at this
    linear_combination this

  have hr : r = 0 := by
    have e1 := hGq L.ω₁ L.ω₁_mem_lattice 0
    have e2 := hGq L.ω₂ L.ω₂_mem_lattice 0
    rw [zero_add, hlin L.ω₁] at e1
    rw [zero_add, hlin L.ω₂] at e2
    have hs : (if 0 < (L.ω₂ / L.ω₁).im then (1 : ℂ) else -1) * (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
      apply mul_ne_zero
      · split_ifs <;> norm_num
      · simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have key : r * (wEta L L.ω₁ * L.ω₂ - wEta L L.ω₂ * L.ω₁) = 0 := by
      linear_combination L.ω₂ * e1 - L.ω₁ * e2
    rw [hL L] at key
    exact (mul_eq_zero.1 key).resolve_right hs

  have hGp : IsPeriodic L G := fun ω hω w => by rw [hGq ω hω w, hr]; ring
  refine ⟨G 0, fun z hz => ?_⟩
  have hfG : f =ᶠ[𝓝[≠] z] G := by
    filter_upwards [hgG z] with w hw
    rw [← hw]
    show f w = f w - r * wZeta L (w - p)
    rw [hr]
    ring
  rw [eq_of_eventuallyEq_nhdsNE hz (hGd z).continuousAt hfG]
  exact hE L G hGd hGp z

end Formalism.L2.Th1.F
end
end
end

-- Source module: Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.SigmaOrder

section

@[expose] public section

noncomputable section

namespace Formalism.L2.Th1.F

theorem sigmaOrder_of (he : SigmaEntire) (hz : SigmaZero) (hs : SigmaSimple) : SigmaOrder := by
  intro L a b z ha
  classical
  set f : ℂ → ℂ := fun w => wSigma L (a * w + b) with hfdef
  have hlin : Differentiable ℂ (fun w : ℂ => a * w + b) :=
    (differentiable_id.const_mul a).add_const b
  have hfd : Differentiable ℂ f := (he L).comp hlin
  have hfa : AnalyticAt ℂ f z := hfd.analyticAt z
  have hder : HasDerivAt f (deriv (wSigma L) (a * z + b) * (a * 1)) z := by
    have h1 : HasDerivAt (fun w : ℂ => a * w + b) (a * 1) z :=
      ((hasDerivAt_id z).const_mul a).add_const b
    exact ((he L) (a * z + b)).hasDerivAt.comp z h1
  rw [hfa.meromorphicOrderAt_eq]
  split_ifs with hmem
  · have h0 : f z = 0 := (hz L (a * z + b)).2 hmem
    have hord : analyticOrderAt f z = ((1 : ℕ) : ℕ∞) := by
      rw [hfa.analyticOrderAt_eq_natCast]
      refine ⟨dslope f z, ?_, ?_, ?_⟩
      · have hon : DifferentiableOn ℂ (dslope f z) Set.univ :=
          (Complex.differentiableOn_dslope Filter.univ_mem).2 hfd.differentiableOn
        exact (differentiableOn_univ.1 hon).analyticAt z
      · rw [dslope_same, hder.deriv]
        exact mul_ne_zero ((hs L).2 _ hmem) (by simpa using ha)
      · filter_upwards with w
        rw [pow_one, sub_smul_dslope, h0, sub_zero]
    rw [hord]
    rfl
  · have hne : f z ≠ 0 := fun h => hmem ((hz L (a * z + b)).1 h)
    have hord : analyticOrderAt f z = 0 := analyticOrderAt_eq_zero.2 (Or.inr hne)
    rw [hord]
    rfl

end Formalism.L2.Th1.F
end
end
end

-- Source module: Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EllipticOnePole

section

@[expose] public section

namespace Formalism.L2.Th1.F

theorem ellipticEntire : EllipticEntire := elliptic_entire_const
theorem ellipticNoPole : EllipticNoPole := elliptic_no_pole_const
theorem ellipticOnePole : EllipticOnePole :=
  ellipticOnePole_of ellipticNoPole ellipticEntire zetaQuasi legendre
theorem sigmaOrder : SigmaOrder := sigmaOrder_of sigmaEntire sigmaZero sigmaSimple
theorem sigmaAdd : SigmaAdd :=
  sigmaAdd_of ellipticNoPole sigmaEntire sigmaOdd sigmaZero sigmaSimple sigmaQuasi sigmaOrder
theorem sgStarAdd : SgStarAdd := sgStarAdd_of sigmaAdd
theorem pInjective : PInjective := pInjective_of sigmaAdd sigmaZero
theorem sigmaDouble : SigmaDouble := sigmaDouble_of sigmaAdd sigmaEntire sigmaSimple
theorem pDerivZero : PDerivZero := pDerivZero_of sigmaDouble sigmaZero
theorem discNeZero : DiscNeZero := discNeZero_of pDerivZero pInjective
theorem zetaAdd : ZetaAdd := zetaAdd_of sigmaAdd sigmaLogDeriv sigmaZero
theorem sigmaThree : SigmaThree :=
  sigmaThree_of ellipticOnePole sigmaOrder sigmaQuasi sigmaZero sigmaEntire sigmaOdd sigmaSimple sigmaAdd
theorem sgStarThree : SgStarThree := sgStarThree_of sigmaThree
theorem thetaLine : ThetaLine := thetaLine_of ellipticOnePole sgStarQuasi sgStarBasic

end Formalism.L2.Th1.F
end
end
