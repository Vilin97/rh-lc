module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SignedLogMeans
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.EquidistributedConjugates
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.PeriodLatticeAgreement
public import Formalism.LocalToGlobal.GlobalTheory.GL3.Statement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeInvariantsPeriodPairDictionary
public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.PeriodRelations.ConjCls
public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.WeierstrassUniqueness.LatOfDiscrHolds
public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.WeierstrassUniqueness.ExistsPeriodPairOfIsLat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Convex.Contractible
public import Formalism.LocalToGlobal.GlobalTheory.GL3.PLinkThU
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.EqOfLeOfAbsNormEq
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.ComplexMultiplication.UniqInvOfLat

-- Source module: Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.WeierstrassUniqueness.WeierstrassPEventuallyEq

section

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.WeierstrassODE

open Filter Topology

lemma wp_eq (L : PeriodPair) (z : ℂ) :
    L.weierstrassP z = L.weierstrassPExcept 0 z + 1 / z ^ 2 := by
  have h := L.weierstrassPExcept_def 0 z
  simp only [ZeroMemClass.coe_zero, sub_zero] at h
  rw [h]; simp

lemma dwp_eq (L : PeriodPair) (z : ℂ) :
    L.derivWeierstrassP z = L.derivWeierstrassPExcept 0 z - 2 / z ^ 3 := by
  have h := L.derivWeierstrassPExcept_def 0 z
  simp only [ZeroMemClass.coe_zero, sub_zero] at h
  rw [h]; ring

lemma ode_shape (L : PeriodPair) (z : ℂ) (hz : z ∉ L.lattice) (hz0 : z ≠ 0) :
    (z ^ 3 * L.derivWeierstrassPExcept 0 z - 2) ^ 2 =
      4 * (z ^ 2 * L.weierstrassPExcept 0 z + 1) ^ 3
        - L.g₂ * (z ^ 6 * L.weierstrassPExcept 0 z + z ^ 4) - L.g₃ * z ^ 6 := by
  have e := L.derivWeierstrassP_sq z hz
  rw [wp_eq, dwp_eq] at e
  set f := L.weierstrassPExcept 0 z
  set f' := L.derivWeierstrassPExcept 0 z
  have key : (z ^ 3 * f' - 2) ^ 2 - (4 * (z ^ 2 * f + 1) ^ 3
        - L.g₂ * (z ^ 6 * f + z ^ 4) - L.g₃ * z ^ 6) =
      z ^ 6 * ((f' - 2 / z ^ 3) ^ 2 - (4 * (f + 1 / z ^ 2) ^ 3 - L.g₂ * (f + 1 / z ^ 2) - L.g₃)) := by
    field_simp
  rw [e, sub_self, mul_zero] at key
  exact sub_eq_zero.mp key

lemma hasDerivAt_wpe (L : PeriodPair) {z : ℂ} (hz : z ∈ ((L.lattice : Set ℂ) \ {0})ᶜ) :
    HasDerivAt (L.weierstrassPExcept 0) (L.derivWeierstrassPExcept 0 z) z := by
  have h1 := (L.analyticOnNhd_weierstrassPExcept 0 z hz).differentiableAt.hasDerivAt
  rwa [L.eqOn_deriv_weierstrassPExcept_derivWeierstrassPExcept 0 hz] at h1

lemma wpe_eventually (L : PeriodPair) :
    ∀ᶠ z in 𝓝 (0:ℂ), HasDerivAt (L.weierstrassPExcept 0) (L.derivWeierstrassPExcept 0 z) z ∧
      (z ≠ 0 → z ∉ L.lattice) := by
  filter_upwards [L.compl_lattice_sdiff_singleton_mem_nhds 0] with z hz
  refine ⟨hasDerivAt_wpe L hz, fun h0 hl => hz ⟨hl, h0⟩⟩

lemma diff_identity (L L' : PeriodPair) (h2 : L.g₂ = L'.g₂) (h3 : L.g₃ = L'.g₃) (z : ℂ)
    (hz0 : z ≠ 0) (hz : z ∉ L.lattice) (hz' : z ∉ L'.lattice) :
    z * (L.derivWeierstrassPExcept 0 z - L'.derivWeierstrassPExcept 0 z) *
        (z ^ 3 * (L.derivWeierstrassPExcept 0 z + L'.derivWeierstrassPExcept 0 z) - 4) =
      (L.weierstrassPExcept 0 z - L'.weierstrassPExcept 0 z) *
        (4 * ((1 + z ^ 2 * L.weierstrassPExcept 0 z) ^ 2
          + (1 + z ^ 2 * L.weierstrassPExcept 0 z) * (1 + z ^ 2 * L'.weierstrassPExcept 0 z)
          + (1 + z ^ 2 * L'.weierstrassPExcept 0 z) ^ 2) - L.g₂ * z ^ 4) := by
  have e1 := ode_shape L z hz hz0
  have e2 := ode_shape L' z hz' hz0
  rw [← h2, ← h3] at e2
  apply mul_left_cancel₀ (pow_ne_zero 2 hz0)
  linear_combination e1 - e2

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.WeierstrassODE

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

open NumberField Classical
open Formalism.BasicNotions (D7)
open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity (IsLat jL Uniformization CMTransitive)
open Formalism.MainNotions.TaylorLogMetric (lamOf)


open Filter Topology in
theorem weierstrassP_eventuallyEq (L L' : PeriodPair) (h2 : L.g₂ = L'.g₂) (h3 : L.g₃ = L'.g₃) :
    L.weierstrassP =ᶠ[𝓝[≠] 0] L'.weierstrassP := by
  set f := L.weierstrassPExcept 0
  set F := L'.weierstrassPExcept 0
  set f' := L.derivWeierstrassPExcept 0
  set F' := L'.derivWeierstrassPExcept 0
  have hf : AnalyticAt ℂ f 0 := L.analyticAt_weierstrassPExcept 0
  have hF : AnalyticAt ℂ F 0 := L'.analyticAt_weierstrassPExcept 0
  have hf' : AnalyticAt ℂ f' 0 := L.analyticAt_derivWeierstrassPExcept 0
  have hF' : AnalyticAt ℂ F' 0 := L'.analyticAt_derivWeierstrassPExcept 0
  have hw : AnalyticAt ℂ (fun z => f z - F z) 0 := hf.sub hF
  suffices hw0 : ∀ᶠ z in 𝓝 (0:ℂ), f z - F z = 0 by
    filter_upwards [nhdsWithin_le_nhds hw0] with z hz
    rw [WeierstrassODE.wp_eq, WeierstrassODE.wp_eq]; linear_combination hz
  by_contra hne
  obtain ⟨n, g, hg, hg0, hwg⟩ := hw.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hne
  simp only [sub_zero, smul_eq_mul] at hwg

  have hder : ∀ᶠ z in 𝓝 (0:ℂ), z * (f' z - F' z) = z ^ n * (n * g z + z * deriv g z) := by
    filter_upwards [WeierstrassODE.wpe_eventually L, WeierstrassODE.wpe_eventually L', hg.eventually_analyticAt,
      hwg.eventually_nhds] with z h1 h1' hgz hwz
    have d1 : HasDerivAt (fun y => f y - F y) (f' z - F' z) z := h1.1.sub h1'.1
    have d2 : HasDerivAt (fun y => f y - F y) (n * z ^ (n - 1) * g z + z ^ n * deriv g z) z :=
      ((hasDerivAt_pow n z).mul hgz.differentiableAt.hasDerivAt).congr_of_eventuallyEq hwz
    rw [d1.unique d2]
    rcases n with _ | m
    · simp
    · push_cast; ring
  have hid : ∀ᶠ z in 𝓝[≠] (0:ℂ), (n * g z + z * deriv g z) *
        (z ^ 3 * (f' z + F' z) - 4) - g z *
        (4 * ((1 + z ^ 2 * f z) ^ 2 + (1 + z ^ 2 * f z) * (1 + z ^ 2 * F z)
          + (1 + z ^ 2 * F z) ^ 2) - L.g₂ * z ^ 4) = 0 := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hder,
      nhdsWithin_le_nhds (WeierstrassODE.wpe_eventually L), nhdsWithin_le_nhds (WeierstrassODE.wpe_eventually L'),
      nhdsWithin_le_nhds hwg] with z hz0 hd h1 h1' hwz
    have hz0' : z ≠ 0 := hz0
    have e := WeierstrassODE.diff_identity L L' h2 h3 z hz0' (h1.2 hz0') (h1'.2 hz0')
    rw [hd, hwz] at e
    apply mul_left_cancel₀ (pow_ne_zero n hz0')
    linear_combination e
  have hcont : ContinuousAt (fun z => (n * g z + z * deriv g z) *
        (z ^ 3 * (f' z + F' z) - 4) - g z *
        (4 * ((1 + z ^ 2 * f z) ^ 2 + (1 + z ^ 2 * f z) * (1 + z ^ 2 * F z)
          + (1 + z ^ 2 * F z) ^ 2) - L.g₂ * z ^ 4)) 0 := by
    have hgd : AnalyticAt ℂ (deriv g) 0 := hg.deriv
    apply AnalyticAt.continuousAt (𝕜 := ℂ)
    fun_prop
  have hlim := tendsto_nhds_unique (hcont.tendsto.mono_left nhdsWithin_le_nhds)
    (tendsto_const_nhds.congr' (EventuallyEq.symm hid))
  simp at hlim
  have : (4 * (n : ℂ) + 12) * g 0 = 0 := by linear_combination -hlim
  rcases mul_eq_zero.mp this with h | h
  · have : (4 * n + 12 : ℕ) = (0 : ℂ) := by push_cast; exact h
    exact absurd (Nat.cast_eq_zero.mp this) (by omega)
  · exact hg0 h

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

end
end
end

-- Source module: Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.WeierstrassUniqueness.WeierstrassPEventuallyEqNhdsNEOfZero

section

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

open NumberField Classical
open Formalism.BasicNotions (D7)
open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity (IsLat jL Uniformization CMTransitive)
open Formalism.MainNotions.TaylorLogMetric (lamOf)


open Filter Topology in
theorem weierstrassP_eventuallyEq_nhdsNE_of_zero (L L' : PeriodPair)
    (h : L.weierstrassP =ᶠ[𝓝[≠] 0] L'.weierstrassP) (x : ℂ) :
    L.weierstrassP =ᶠ[𝓝[≠] x] L'.weierstrassP := by
  set f : ℂ → ℂ := fun z => L.weierstrassP z - L'.weierstrassP z with hf
  have hm : MeromorphicOn f Set.univ := fun z _ =>
    (L.meromorphic_weierstrassP z).sub (L'.meromorphic_weierstrassP z)
  have h0 : meromorphicOrderAt f 0 = ⊤ := by
    rw [meromorphicOrderAt_eq_top_iff]
    filter_upwards [h] with z hz
    simp [hf, hz]
  have hx : meromorphicOrderAt f x = ⊤ := by
    by_contra hne
    have := (hm.exists_meromorphicOrderAt_ne_top_iff_forall isConnected_univ).1
      ⟨⟨x, Set.mem_univ _⟩, hne⟩ ⟨0, Set.mem_univ _⟩
    exact this h0
  rw [meromorphicOrderAt_eq_top_iff] at hx
  filter_upwards [hx] with z hz
  exact sub_eq_zero.1 hz


open Filter Topology in
theorem lattice_subset_of_weierstrassP (L L' : PeriodPair)
    (h : L.weierstrassP =ᶠ[𝓝[≠] 0] L'.weierstrassP) :
    (L.lattice : Set ℂ) ⊆ L'.lattice := by
  intro l hl
  by_contra hl'
  have h1 := L.order_weierstrassP l hl
  have h2 : 0 ≤ meromorphicOrderAt L'.weierstrassP l :=
    (L'.analyticOnNhd_weierstrassP l hl').meromorphicOrderAt_nonneg
  rw [← meromorphicOrderAt_congr (weierstrassP_eventuallyEq_nhdsNE_of_zero L L' h l), h1] at h2
  exact absurd h2 (by decide)


open Filter Topology in
theorem lattice_eq_of_weierstrassP (L L' : PeriodPair)
    (h : L.weierstrassP =ᶠ[𝓝[≠] 0] L'.weierstrassP) :
    (L.lattice : Set ℂ) = L'.lattice :=
  Set.Subset.antisymm (lattice_subset_of_weierstrassP L L' h)
    (lattice_subset_of_weierstrassP L' L h.symm)

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

end
end
end

-- Source module: Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.WeierstrassUniqueness.UniqInvHolds

section

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

open NumberField Classical
open Formalism.BasicNotions (D7)
open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity (IsLat jL Uniformization CMTransitive)
open Formalism.MainNotions.TaylorLogMetric (lamOf)

theorem uniqLat_holds (Λ Λ' : AddSubgroup ℂ) (hΛ : IsLat Λ) (hΛ' : IsLat Λ')
    (h2 : Formalism.MainNotions.TaylorLogMetric.g2 Λ = Formalism.MainNotions.TaylorLogMetric.g2 Λ') (h3 : Formalism.MainNotions.TaylorLogMetric.g3 Λ = Formalism.MainNotions.TaylorLogMetric.g3 Λ') : Λ = Λ' := by
  obtain ⟨L, hL⟩ := exists_periodPair_of_isLat Λ hΛ
  obtain ⟨L', hL'⟩ := exists_periodPair_of_isLat Λ' hΛ'
  obtain ⟨a2, a3⟩ := g2_g3_eq_periodPair Λ L hL
  obtain ⟨b2, b3⟩ := g2_g3_eq_periodPair Λ' L' hL'
  have e : (L.lattice : Set ℂ) = L'.lattice :=
    lattice_eq_of_weierstrassP L L'
      (weierstrassP_eventuallyEq L L' (by rw [← a2, ← b2, h2]) (by rw [← a3, ← b3, h3]))
  apply SetLike.coe_injective
  rw [← hL, ← hL', e]

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UniformizationHolds

section

@[expose] public section

noncomputable section

namespace GlobalTheory.ConjLattice

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric GlobalTheory.Glob.IntegralWittCoefficients GlobalTheory.IndefiniteRowSideFullHecke

abbrev cj : ℂ →+ ℂ := (starRingEnd ℂ).toAddMonoidHom

theorem cj_apply (z : ℂ) : cj z = starRingEnd ℂ z := rfl

theorem map_cj_map_cj (Λ : AddSubgroup ℂ) : (Λ.map cj).map cj = Λ := by
  rw [AddSubgroup.map_map]
  have : cj.comp cj = AddMonoidHom.id ℂ := by ext z; simp [cj_apply]
  rw [this, AddSubgroup.map_id]

theorem eisG_map_cj (Λ : AddSubgroup ℂ) (k : ℕ) :
    eisG (Λ.map cj) k = starRingEnd ℂ (eisG Λ k) := by
  unfold eisG
  let e : {w : ℂ // w ∈ Λ ∧ w ≠ 0} ≃ {w : ℂ // w ∈ Λ.map cj ∧ w ≠ 0} :=
    { toFun := fun w => ⟨starRingEnd ℂ w.1, ⟨w.1, w.2.1, rfl⟩, by simpa using w.2.2⟩
      invFun := fun w => ⟨starRingEnd ℂ w.1, by
          obtain ⟨v, hv, hv'⟩ := AddSubgroup.mem_map.1 w.2.1
          have : starRingEnd ℂ w.1 = v := by rw [← hv']; simp [cj_apply]
          rw [this]; exact hv, by simpa using w.2.2⟩
      left_inv := fun w => by ext; simp
      right_inv := fun w => by ext; simp }
  rw [← e.tsum_eq, Complex.conj_tsum]
  congr 1
  ext w
  show (1 : ℂ) / (starRingEnd ℂ (w : ℂ)) ^ (2 * k) = starRingEnd ℂ (1 / (w : ℂ) ^ (2 * k))
  simp [map_div₀, map_pow]

theorem eisenstein_g_two_map_conj (Λ : AddSubgroup ℂ) : g2 (Λ.map cj) = starRingEnd ℂ (g2 Λ) := by
  unfold g2; rw [eisG_map_cj, map_mul, map_ofNat]

theorem eisenstein_g_three_map_conj (Λ : AddSubgroup ℂ) : g3 (Λ.map cj) = starRingEnd ℂ (g3 Λ) := by
  unfold g3; rw [eisG_map_cj, map_mul, map_ofNat]

theorem discr_map_cj (Λ : AddSubgroup ℂ) :
    Formalism.MainNotions.TaylorLogMetric.discr (Λ.map cj) = starRingEnd ℂ (Formalism.MainNotions.TaylorLogMetric.discr Λ) := by
  unfold Formalism.MainNotions.TaylorLogMetric.discr; rw [eisenstein_g_two_map_conj, eisenstein_g_three_map_conj, map_sub, map_mul, map_pow, map_pow, map_ofNat]

theorem lamConj_spec (hU : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.Uniformization) (M : IntermediateField ℚ ℂ)
    (ρ : M →ₐ[ℚ] ℂ) (Λ : AddSubgroup ℂ) (h2 : g2 Λ ∈ M) (h3 : g3 Λ ∈ M) (h1 : Formalism.MainNotions.TaylorLogMetric.discr Λ = 1) :
    g2 (lamConj M ρ Λ) = ρ ⟨g2 Λ, h2⟩ ∧ g3 (lamConj M ρ Λ) = ρ ⟨g3 Λ, h3⟩ ∧
      Formalism.MainNotions.TaylorLogMetric.discr (lamConj M ρ Λ) = 1 := by
  have hl2 : liftM M (g2 Λ) = ⟨g2 Λ, h2⟩ := dif_pos h2
  have hl3 : liftM M (g3 Λ) = ⟨g3 Λ, h3⟩ := dif_pos h3
  have hdM : (⟨g2 Λ, h2⟩ : M) ^ 3 - 27 * (⟨g3 Λ, h3⟩ : M) ^ 2 = 1 := by
    apply M.val.injective
    rw [map_sub, map_mul, map_pow, map_pow, map_ofNat, map_one]
    exact h1
  have hab : (ρ ⟨g2 Λ, h2⟩) ^ 3 - 27 * (ρ ⟨g3 Λ, h3⟩) ^ 2 = 1 := by
    rw [← map_pow, ← map_pow, ← map_ofNat ρ 27, ← map_mul, ← map_sub, hdM, map_one]
  obtain ⟨Λ', -, h2', h3'⟩ := (hU _ _ (by rw [hab]; exact one_ne_zero)).1
  have hex : ∃ Λ' : AddSubgroup ℂ, g2 Λ' = ρ (liftM M (g2 Λ)) ∧ g3 Λ' = ρ (liftM M (g3 Λ)) :=
    ⟨Λ', by rw [hl2]; exact h2', by rw [hl3]; exact h3'⟩
  have hs := Classical.epsilon_spec hex
  have e2 : g2 (lamConj M ρ Λ) = ρ ⟨g2 Λ, h2⟩ := hs.1.trans (by rw [hl2])
  have e3 : g3 (lamConj M ρ Λ) = ρ ⟨g3 Λ, h3⟩ := hs.2.trans (by rw [hl3])
  refine ⟨e2, e3, ?_⟩
  show g2 _ ^ 3 - 27 * g3 _ ^ 2 = 1
  rw [e2, e3, hab]

def conjO (D : D7) : 𝓞 D.host.K ≃+* 𝓞 D.host.K :=
  haveI := Formalism.MainNotions.UnusedSlot33.HK.isGalK D.host
  RingOfIntegers.mapRingEquiv
    ((AlgEquiv.restrictNormal D.host.conj D.host.K : D.host.K ≃ₐ[ℚ] D.host.K) : D.host.K ≃+* D.host.K)

theorem phi_conjO (D : D7) (a : 𝓞 D.host.K) :
    D.host.φ₀ (((conjO D a : 𝓞 D.host.K) : D.host.K) : D.host.E) =
      starRingEnd ℂ (D.host.φ₀ ((a : D.host.K) : D.host.E)) := by
  haveI := Formalism.MainNotions.UnusedSlot33.HK.isGalK D.host
  have h : (((conjO D a : 𝓞 D.host.K) : D.host.K) : D.host.E) = D.host.conj ((a : D.host.K) : D.host.E) := by
    rw [conjO, RingOfIntegers.mapRingEquiv_apply]
    exact AlgEquiv.restrictNormal_commutes D.host.conj D.host.K (a : D.host.K)
  rw [h]
  exact D.host.toHostAx.conjE_apply _ _

theorem lamOf_map_cj (D : D7) (c : Ideal (𝓞 D.host.K)) (x : ℂ) :
    (lamOf D c x).map cj = lamOf D (c.map (conjO D)) (starRingEnd ℂ x) := by
  unfold lamOf
  rw [AddMonoidHom.map_closure]
  congr 1
  ext w
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    refine ⟨conjO D a, Ideal.mem_map_of_mem _ ha, ?_⟩
    rw [phi_conjO, cj_apply, map_mul]
  · rintro ⟨b, hb, rfl⟩
    rw [Ideal.mem_map_of_equiv] at hb
    obtain ⟨a, ha, rfl⟩ := hb
    exact ⟨_, ⟨a, ha, rfl⟩, by rw [phi_conjO, cj_apply, map_mul]⟩

end GlobalTheory.ConjLattice

namespace GlobalTheory.ConjLattice

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric GlobalTheory.Glob.IntegralWittCoefficients GlobalTheory.IndefiniteRowSideFullHecke

theorem containsData {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {M : IntermediateField ℚ ℂ}
    (h : DataIn D (tor0 D cc δ) M) : EquidistributedConjugates.ContainsData D M (lamOf D cc δ) := by
  refine ⟨fun x => ?_, h.2.1, h.2.2⟩
  have := h.1 (D.eTau.symm 1) (x : D.host.E)
  rwa [show (tor0 D cc δ).emb (D.eTau.symm 1) (x : D.host.E) = embT D (D.eTau.symm 1) (x : D.host.E) from rfl,
    Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FL.embT_K D _ _ x.2] at this

theorem conj_lattice : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.Uniformization →
    EquidistributedConjugates.ConjugatesEquidistributed → PeriodLatticeAgreement.LatticePeriodEta →
    ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M]
      (t : (M →ₐ[ℚ] ℂ) → ℂ), SignedLogMeans.HidaSetting D cc δ M t → ∀ ρ : M →ₐ[ℚ] ℂ,
      Formalism.MainNotions.TaylorLogMetric.discr (lamConj M ρ (lamOf D cc δ)) = 1 ∧ ∃ c : Ideal (𝓞 D.host.K), c ≠ ⊥ ∧ ∃ x : ℂ, x ≠ 0 ∧
        lamConj M ρ (lamOf D cc δ) = lamOf D c x := by
  intro hU hCE _ D cc δ M _ t hS ρ
  obtain ⟨hcc, hδ, hM, -⟩ := hS
  have h1 : Formalism.MainNotions.TaylorLogMetric.discr (lamOf D cc δ) = 1 := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.br_discr_lamOf D cc hcc δ hδ
  have h2 : g2 (lamOf D cc δ) ∈ M := hM.2.1
  have h3 : g3 (lamOf D cc δ) ∈ M := hM.2.2
  have hsp := fun ρ' => lamConj_spec hU M ρ' (lamOf D cc δ) h2 h3 h1
  refine ⟨(hsp ρ).2.2, ?_⟩
  obtain ⟨⟨c, hcH, -⟩, hC2, -⟩ := hCE D cc δ hcc hδ M (containsData hM)
  by_cases hρ : EquidistributedConjugates.FixesK D M ρ
  · obtain ⟨x, hx, hxe⟩ := hcH ⟨ρ, hρ⟩
    exact ⟨_, nonZeroDivisors.coe_ne_zero _, x, hx, hxe⟩
  · obtain ⟨hρ', -⟩ := hC2 ρ hρ
    obtain ⟨x, hx, hxe⟩ := hcH ⟨EquidistributedConjugates.conjEmb M ρ, hρ'⟩
    have hUI : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.UniqInv :=
      Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.uniqInv_of_lat Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.latOfDiscr_holds hU
    have hmap : (lamConj M ρ (lamOf D cc δ)).map cj = lamConj M (EquidistributedConjugates.conjEmb M ρ) (lamOf D cc δ) := by
      apply hUI
      · rw [discr_map_cj, (hsp ρ).2.2, map_one]; exact one_ne_zero
      · rw [eisenstein_g_two_map_conj, (hsp ρ).1, (hsp _).1]; exact (EquidistributedConjugates.conjEmb_apply _ _ _).symm
      · rw [eisenstein_g_three_map_conj, (hsp ρ).2.1, (hsp _).2.1]; exact (EquidistributedConjugates.conjEmb_apply _ _ _).symm
    have hback : lamConj M ρ (lamOf D cc δ) = (lamConj M (EquidistributedConjugates.conjEmb M ρ) (lamOf D cc δ)).map cj := by
      rw [← hmap, map_cj_map_cj]
    refine ⟨(c ⟨EquidistributedConjugates.conjEmb M ρ, hρ'⟩ : Ideal (𝓞 D.host.K)).map (conjO D), ?_, starRingEnd ℂ x,
      (map_ne_zero _).2 hx, by rw [hback, hxe, lamOf_map_cj]⟩
    intro hbot
    rw [Ideal.map_eq_bot_iff_of_injective (conjO D).injective] at hbot
    exact nonZeroDivisors.coe_ne_zero _ hbot

end GlobalTheory.ConjLattice

namespace GlobalTheory.ConjLattice

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric GlobalTheory.Glob.IntegralWittCoefficients GlobalTheory.IndefiniteRowSideFullHecke

theorem uniformization_holds : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.Uniformization := by
  intro a b h
  refine ⟨?_, fun Λ Λ' hΛ hΛ' h2 h3 h2' h3' =>
    Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.uniqLat_holds Λ Λ' hΛ hΛ' (h2.trans h2'.symm) (h3.trans h3'.symm)⟩
  obtain ⟨L, h2, h3⟩ := GlobalTheory.LatticeInvariants.exists_periodPair_of_invariants h
  obtain ⟨e2, e3, hΔ, -⟩ := GlobalTheory.LatticeInvariants.invariants_dictionary L L.lattice.toAddSubgroup (fun _ => Iff.rfl)
  exact ⟨_, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.latOfDiscr_holds _ hΔ, e2.trans h2, e3.trans h3⟩

theorem conj_lattice_holds : EquidistributedConjugates.ConjugatesEquidistributed → PeriodLatticeAgreement.LatticePeriodEta →
    ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M]
      (t : (M →ₐ[ℚ] ℂ) → ℂ), SignedLogMeans.HidaSetting D cc δ M t → ∀ ρ : M →ₐ[ℚ] ℂ,
      discr (lamConj M ρ (lamOf D cc δ)) = 1 ∧ ∃ c : Ideal (𝓞 D.host.K), c ≠ ⊥ ∧ ∃ x : ℂ, x ≠ 0 ∧
        lamConj M ρ (lamOf D cc δ) = lamOf D c x :=
  conj_lattice uniformization_holds

end GlobalTheory.ConjLattice
end
end
end
