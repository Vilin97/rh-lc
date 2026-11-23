module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AbsNormLeOfMemBoxSet
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.FinitePrimesOfMem
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AlphaNOfVdZeroUnit
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.UnitaryDensityFieldFurther
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
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AbsNormLeOfMemIdeal
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.IsUnimodularAtIffVd
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocalDensityRatio
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.NeBotOfIsMaximal
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.NkCountLocF
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.TendstoMeanAlphaN
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.TendstoSumOfMean
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.TendstoWeightedTprod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Topology.Sheaves.Presheaf
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ALocEqRoL

section

@[expose] public section

open NumberField Module Filter Topology

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.A5

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

def aLoc (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal})
    (n : 𝓞 F) : ℝ :=
  alphaN h L 𝔭.1 n / eFac K (finrank K V) 𝔭.1


open scoped Classical in
def roL (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V)
    (S : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) (𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) (j : ℕ) : ℝ :=
  if 𝔭 ∈ S then 1 else aLoc h L 𝔭 (exists_vF_eq 𝔭.2 j).choose

variable (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
  {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
  (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (hm : 2 ≤ finrank K V)
  {S : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}}
  (hS : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, vd h L 𝔭.1 ≠ 0 → 𝔭 ∈ S)

include hK hF hs hd hL hLi hS

theorem aLoc_eq_roL {𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}} (h𝔭 : 𝔭 ∉ S) {n : 𝓞 F} (hn : n ≠ 0) :
    aLoc h L 𝔭 n = roL h L S 𝔭 (valF n 𝔭) := by
  have hv : vd h L 𝔭.1 = 0 := by
    by_contra hne
    exact h𝔭 (hS 𝔭 hne)
  obtain ⟨hn', hvn'⟩ := (exists_vF_eq 𝔭.2 (valF n 𝔭)).choose_spec
  rw [roL, if_neg h𝔭]
  unfold aLoc
  rw [alphaN_eq_of_vF_eq hK hF hs hd (by first | exact hL | exact hL.toIsLattice) hLi 𝔭.2 hv hn hn' (by rw [hvn', valF_apply hn])]

include hm

theorem roL_zero (𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) : roL h L S 𝔭 0 = 1 := by
  by_cases h𝔭 : 𝔭 ∈ S
  · rw [roL, if_pos h𝔭]
  · have hv : vd h L 𝔭.1 = 0 := by
      by_contra hne
      exact h𝔭 (hS 𝔭 hne)
    obtain ⟨hn', hvn'⟩ := (exists_vF_eq 𝔭.2 0).choose_spec
    have hn𝔭 : (exists_vF_eq 𝔭.2 0).choose ∉ 𝔭.1 := by
      intro hmem
      have := (mem_pow_iff_le_vF 𝔭.2 hn' 1).mp (by rw [pow_one]; exact hmem)
      omega
    rw [roL, if_neg h𝔭]
    unfold aLoc
    rw [unitaryAbsoluteValueBounds.alphaN_unit hK hF hs hd (by first | exact hL | exact hL.toIsLattice) hLi 𝔭.2 hv (by omega) hn𝔭]
    have he := eFac_pos (K := K) 𝔭.2 (m := finrank K V) (by omega)
    unfold eFac at he ⊢
    exact div_self he.ne'

theorem roL_diff (𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) (j : ℕ) :
    |roL h L S 𝔭 (j + 1) - roL h L S 𝔭 j| ≤
      8 * ((j : ℝ) + 2) ^ 2 / (Ideal.absNorm 𝔭.1 : ℝ) := by
  by_cases h𝔭 : 𝔭 ∈ S
  · have h1 : ∀ i, roL h L S 𝔭 i = 1 := fun i => by rw [roL, if_pos h𝔭]
    rw [h1, h1, sub_self, abs_zero]
    positivity
  · have hv : vd h L 𝔭.1 = 0 := by
      by_contra hne
      exact h𝔭 (hS 𝔭 hne)
    have hro : ∀ i, roL h L S 𝔭 i = aLoc h L 𝔭 (exists_vF_eq 𝔭.2 i).choose := fun i => by
      rw [roL, if_neg h𝔭]
    obtain ⟨hn1, hv1⟩ := (exists_vF_eq 𝔭.2 (j + 1)).choose_spec
    obtain ⟨hn0, hv0⟩ := (exists_vF_eq 𝔭.2 j).choose_spec
    rw [hro, hro]
    unfold aLoc eFac
    have hb := alphaN_rho_diff_bound hK hF hs hd (by first | exact hL | exact hL.toIsLattice) hLi hm 𝔭.2 hv hn1 hn0 (by rw [hv1, hv0])
    refine hb.trans ?_
    rw [hv1]

    have key : ∀ e : ℕ, 1 ≤ e → 8 * (((j + 1 : ℕ) : ℝ) + 1) ^ 2 *
        (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(e : ℤ)) ≤ 8 * ((j : ℝ) + 2) ^ 2 / (Ideal.absNorm 𝔭.1 : ℝ) := by
      intro e he
      have hj : (((j + 1 : ℕ) : ℝ) + 1) = (j : ℝ) + 2 := by push_cast; ring
      rw [hj, div_eq_mul_inv]
      rcases Nat.eq_zero_or_pos (Ideal.absNorm 𝔭.1) with h0 | hpos
      · rw [h0, Nat.cast_zero, zero_zpow _ (by omega), inv_zero]
      · have hx : (1 : ℝ) ≤ (Ideal.absNorm 𝔭.1 : ℝ) := by exact_mod_cast hpos
        have hz : (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(e : ℤ)) ≤ (Ideal.absNorm 𝔭.1 : ℝ) ^ (-1 : ℤ) :=
          zpow_le_zpow_right₀ hx (by omega)
        rw [zpow_neg_one] at hz
        exact mul_le_mul_of_nonneg_left hz (by positivity)
    exact key _ (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)))

omit hm in
theorem prod_aLoc {U : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}} (hU : S ⊆ U) {n : 𝓞 F}
    (hn : n ≠ 0) :
    ∏ 𝔭 ∈ U, aLoc h L 𝔭 n = (∏ 𝔭 ∈ S, aLoc h L 𝔭 n) * ∏ 𝔭 ∈ U, roL h L S 𝔭 (valF n 𝔭) := by
  rw [← Finset.prod_sdiff hU (f := fun 𝔭 => aLoc h L 𝔭 n),
    ← Finset.prod_sdiff hU (f := fun 𝔭 => roL h L S 𝔭 (valF n 𝔭))]
  have h1 : ∏ 𝔭 ∈ S, roL h L S 𝔭 (valF n 𝔭) = 1 :=
    Finset.prod_eq_one fun 𝔭 h𝔭 => by rw [roL, if_pos h𝔭]
  have h2 : ∏ 𝔭 ∈ U \ S, aLoc h L 𝔭 n = ∏ 𝔭 ∈ U \ S, roL h L S 𝔭 (valF n 𝔭) :=
    Finset.prod_congr rfl fun 𝔭 h𝔭 =>
      aLoc_eq_roL (hK := hK) (hF := hF) (hs := hs) (hd := hd) (hL := hL) (hLi := hLi) (hS := hS) (Finset.mem_sdiff.mp h𝔭).2 hn
  rw [h1, h2, mul_one, mul_comm]

theorem singS_eq {n : 𝓞 F} (hn : n ≠ 0) :
    singS F h L n = (∏ 𝔭 ∈ S, aLoc h L 𝔭 n) * (valF n).prod (roL h L S) := by
  classical
  have hz : ∀ 𝔭, roL h L S 𝔭 0 = 1 := fun 𝔭 => roL_zero (hK := hK) (hF := hF) (hs := hs) (hd := hd) (hL := hL) (hLi := hLi) (hm := hm) (hS := hS) 𝔭
  have e1 : singS F h L n = ∏' 𝔭, aLoc h L 𝔭 n := rfl
  have hsup : (valF n).support ⊆ S ∪ (valF n).support := Finset.subset_union_right
  rw [e1, tprod_eq_prod (s := S ∪ (valF n).support) ?_,
    prod_aLoc (hK := hK) (hF := hF) (hs := hs) (hd := hd) (hL := hL) (hLi := hLi) (hS := hS) Finset.subset_union_left hn,
    Finsupp.prod_of_support_subset _ hsup _ (fun 𝔭 _ => hz 𝔭)]
  intro 𝔭 h𝔭
  rw [Finset.mem_union, not_or] at h𝔭
  have h0 : valF n 𝔭 = 0 := by
    by_contra hne
    exact h𝔭.2 (Finsupp.mem_support_iff.mpr hne)
  rw [aLoc_eq_roL (hK := hK) (hF := hF) (hs := hs) (hd := hd) (hL := hL) (hLi := hLi) (hS := hS) h𝔭.1 hn, h0, hz]

omit hS in
theorem prodS_bound (S : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) :
    ∃ C : ℝ, ∀ n : 𝓞 F, n ≠ 0 →
      0 ≤ ∏ 𝔭 ∈ S, aLoc h L 𝔭 n ∧ ∏ 𝔭 ∈ S, aLoc h L 𝔭 n ≤ C := by
  have hm1 : 1 ≤ finrank K V := by omega
  choose C hC using fun 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} =>
    alphaN_bound hK hF hs hd hL hLi hm 𝔭.2
  refine ⟨∏ 𝔭 ∈ S, C 𝔭 / eFac K (finrank K V) 𝔭.1, fun n hn => ?_⟩
  have hpos : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, 0 < eFac K (finrank K V) 𝔭.1 :=
    fun 𝔭 => eFac_pos 𝔭.2 hm1
  have h0 : ∀ 𝔭 ∈ S, 0 ≤ aLoc h L 𝔭 n := fun 𝔭 _ => div_nonneg (hC 𝔭 n hn).1 (hpos 𝔭).le
  refine ⟨Finset.prod_nonneg h0, Finset.prod_le_prod₀ h0 fun 𝔭 _ => ?_⟩
  exact div_le_div_of_nonneg_right (hC 𝔭 n hn).2 (hpos 𝔭).le

end Formalism.HermitianLattices.Ext.L3.A5
end
end
end

-- Source module: Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.TendstoSumBoxIdeal

section

@[expose] public section

open NumberField Module Filter Topology

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem exists_abs_alphaN_le (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (hm : 2 ≤ finrank K V)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : ∃ C : ℝ, ∀ n : 𝓞 F, |alphaN h L 𝔭 n| ≤ C := by
  obtain ⟨C, hC⟩ := nkCount_le hK hF hs hd hL hLi hm h𝔭
  have hq : (0 : ℝ) < (Ideal.absNorm 𝔭 : ℝ) := zero_lt_one.trans (BoxSum.one_lt_absNorm h𝔭)
  refine ⟨max C |alphaN h L 𝔭 0|, fun n => ?_⟩
  by_cases hn : n = 0
  · rw [hn]; exact le_max_right _ _
  refine le_trans ?_ (le_max_left _ _)
  set u : ℕ → ℝ := fun k => (nkCount h L 𝔭 k n : ℝ) /
    (Ideal.absNorm 𝔭 : ℝ) ^ (k * (2 * finrank K V - 1)) with hu
  set k₀ := 2 * vd h L 𝔭 + 2 * vF 𝔭 n + 2 with hk₀
  have hstep : ∀ k, k₀ ≤ k → u k = u k₀ := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => rfl
    | succ k hk ih =>
      rw [← ih]
      simp only [hu]
      rw [nkCount_succ hK hF hs hd hL hLi h𝔭 hn hk, add_mul, one_mul, pow_add]
      push_cast
      field_simp
  have hlim : Tendsto u atTop (𝓝 (u k₀)) :=
    tendsto_atTop_of_eventually_const (i₀ := k₀) fun k hk => hstep k hk
  have hα : alphaN h L 𝔭 n = u k₀ := hlim.limUnder_eq
  rw [hα, abs_of_nonneg (by simp only [hu]; positivity)]
  simp only [hu]
  rw [div_le_iff₀ (by positivity)]
  exact hC _ _

theorem tendsto_sum_box_ideal (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (hm : 2 ≤ finrank K V) (S : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal})
    (hS : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, vd h L 𝔭.1 ≠ 0 → 𝔭 ∈ S) {b : Ideal (𝓞 F)} (hb : b ≠ ⊥)
    (hbS : ∀ 𝔭 ∈ S, b ⊔ 𝔭.1 = ⊤) :
    Tendsto (fun j : ℕ => ((j : ℝ) ^ 2) ^ (-((Formalism.HermitianLatticesTheory.fDeg K * finrank K V : ℕ) : ℤ)) *
        ∑ᶠ n ∈ {n : 𝓞 F | n ∈ boxSet K F ((j : ℝ) ^ 2) ∧ n ∈ b},
          (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (finrank K V - 1) *
            ∏ 𝔭 ∈ S, alphaN h L 𝔭.1 n / (1 - etaF K F 𝔭.1 ^ finrank K V *
              (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(finrank K V : ℤ))))
      atTop (𝓝 ((finrank K V : ℝ) ^ (-(Formalism.HermitianLatticesTheory.fDeg K : ℤ)) /
        Real.sqrt ((2 * Formalism.HermitianLatticesTheory.vInv K) ^ Formalism.HermitianLatticesTheory.fDeg K) / (Ideal.absNorm b : ℝ) *
          ∏ 𝔭 ∈ S, (1 - etaF K F 𝔭.1 ^ finrank K V *
            (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(finrank K V : ℤ)))⁻¹)) := by
  choose C hC using fun 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} =>
    exists_abs_alphaN_le hK hF hs hd hL hLi hm 𝔭.2
  have key := BoxSum.tendsto_sum_of_mean hK hF (m := finrank K V) (by omega) S
    (fun 𝔭 n => alphaN h L 𝔭.1 n) C (fun 𝔭 => 2 * vd h L 𝔭.1 + 2) (fun 𝔭 _ n => hC 𝔭 n)
    (fun 𝔭 _ n n' k hn hk hc => alphaN_congr hK hF hs hd hL hLi 𝔭.2 hn (by omega) hc)
    (fun 𝔭 _ => tendsto_mean_alphaN hK hF hs hd hL hLi hm 𝔭.2) hb hbS
  refine (key.mul_const (∏ 𝔭 ∈ S, (1 - etaF K F 𝔭.1 ^ finrank K V *
            (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(finrank K V : ℤ)))⁻¹)).congr fun j => ?_
  rw [mul_assoc, finsum_mem_mul]
  congr 1
  refine finsum_mem_congr rfl fun n _ => ?_
  simp only [div_eq_mul_inv]
  rw [Finset.prod_mul_distrib, mul_assoc]

end Formalism.HermitianLattices.Ext.L3
end
end
end

-- Source module: Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.TendstoSingSSum

section

@[expose] public section

open NumberField Module Filter Topology

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

namespace A5

open scoped Classical in
theorem coe_filter_box (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (T : ℝ)
    (v : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} →₀ ℕ) :
    {n : 𝓞 F | n ∈ boxSet K F T ∧ n ∈ bId v} =
      ↑((boxSet_finite hK hF T).toFinset.filter fun n => v ≤ valF n) := by
  ext n
  simp only [Set.mem_setOf_eq, Finset.coe_filter, Set.Finite.mem_toFinset]
  constructor
  · rintro ⟨hb, hI⟩
    exact ⟨hb, (mem_bId_iff (ne_zero_of_mem_boxSet hb) v).mp hI⟩
  · rintro ⟨hb, hv⟩
    exact ⟨hb, (mem_bId_iff (ne_zero_of_mem_boxSet hb) v).mpr hv⟩

open scoped Classical in
theorem dominated (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (hm : 2 ≤ finrank K V)
    (S : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) :
    ∃ C : ℝ, ∀ T : ℝ, 1 ≤ T → ∀ v : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} →₀ ℕ,
      |T ^ (-((Formalism.HermitianLatticesTheory.fDeg K * finrank K V : ℕ) : ℤ)) *
        ∑ n ∈ (boxSet_finite hK hF T).toFinset.filter (fun n => v ≤ valF n),
          (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (finrank K V - 1) * ∏ 𝔭 ∈ S, aLoc h L 𝔭 n| ≤
        C / nrm (fun 𝔭 => (Ideal.absNorm 𝔭.1 : ℝ)) v := by
  obtain ⟨C1, hC1⟩ := prodS_bound hK hF hs hd (by first | exact hL | exact hL.toIsLattice) hLi hm S
  refine ⟨2 ^ Formalism.HermitianLatticesTheory.fDeg K * C1, fun T hT v => ?_⟩
  have hT0 : 0 < T := lt_of_lt_of_le one_pos hT
  have hsum0 : 0 ≤ ∑ n ∈ (boxSet_finite hK hF T).toFinset.filter (fun n => v ≤ valF n),
      (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (finrank K V - 1) * ∏ 𝔭 ∈ S, aLoc h L 𝔭 n := by
    refine Finset.sum_nonneg fun n hn => ?_
    have hb : n ∈ boxSet K F T := by
      simpa using (Finset.mem_filter.mp hn).1
    exact mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (hC1 n (ne_zero_of_mem_boxSet hb)).1
  rw [abs_of_nonneg (mul_nonneg (zpow_nonneg hT0.le _) hsum0)]
  have hterm : ∀ n ∈ (boxSet_finite hK hF T).toFinset.filter (fun n => v ≤ valF n),
      (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (finrank K V - 1) * ∏ 𝔭 ∈ S, aLoc h L 𝔭 n ≤
        (T ^ Formalism.HermitianLatticesTheory.fDeg K) ^ (finrank K V - 1) * C1 := fun n hn => by
    have hb : n ∈ boxSet K F T := by
      simpa using (Finset.mem_filter.mp hn).1
    have hP := hC1 n (ne_zero_of_mem_boxSet hb)
    exact mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _) (absNorm_le_of_mem_boxSet hK hF hb) _) hP.2 hP.1
      (pow_nonneg (pow_nonneg hT0.le _) _)
  have hcard : (((boxSet_finite hK hF T).toFinset.filter (fun n => v ≤ valF n)).card : ℝ) ≤
      2 ^ Formalism.HermitianLatticesTheory.fDeg K * T ^ Formalism.HermitianLatticesTheory.fDeg K / (Ideal.absNorm (bId v) : ℝ) := by
    have h1 := Formalism.HermitianLattices.Ext.L3.BoxCube.card_box_le hK hF (bId_ne_bot v) hT0.le
    have h2 : ((boxSet_finite hK hF T).toFinset.filter (fun n => v ≤ valF n)).card =
        Nat.card {n : 𝓞 F // n ∈ boxSet K F T ∧ n ∈ bId v} := by
      rw [← Set.ncard_coe_finset, ← coe_filter_box hK hF T v, ← Nat.card_coe_set_eq]
      rfl
    rw [h2]
    exact h1
  have hle := Finset.sum_le_card_nsmul _ _ _ hterm
  rw [nsmul_eq_mul] at hle
  have hexp : Formalism.HermitianLatticesTheory.fDeg K * finrank K V =
      Formalism.HermitianLatticesTheory.fDeg K + Formalism.HermitianLatticesTheory.fDeg K * (finrank K V - 1) := by
    conv_lhs => rw [show finrank K V = (finrank K V - 1) + 1 by omega]
    ring
  have hTT : T ^ (-((Formalism.HermitianLatticesTheory.fDeg K * finrank K V : ℕ) : ℤ)) *
      (T ^ Formalism.HermitianLatticesTheory.fDeg K * (T ^ Formalism.HermitianLatticesTheory.fDeg K) ^ (finrank K V - 1)) = 1 := by
    rw [zpow_neg, zpow_natCast, ← pow_mul, ← pow_add, ← hexp]
    exact inv_mul_cancel₀ (pow_ne_zero _ hT0.ne')
  have hC1n : 0 ≤ C1 := by
    have := hC1 1 one_ne_zero
    exact this.1.trans this.2
  rw [← absNorm_bId]
  calc T ^ (-((Formalism.HermitianLatticesTheory.fDeg K * finrank K V : ℕ) : ℤ)) *
        ∑ n ∈ (boxSet_finite hK hF T).toFinset.filter (fun n => v ≤ valF n),
          (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (finrank K V - 1) * ∏ 𝔭 ∈ S, aLoc h L 𝔭 n
      ≤ T ^ (-((Formalism.HermitianLatticesTheory.fDeg K * finrank K V : ℕ) : ℤ)) *
        ((2 ^ Formalism.HermitianLatticesTheory.fDeg K * T ^ Formalism.HermitianLatticesTheory.fDeg K / (Ideal.absNorm (bId v) : ℝ)) *
          ((T ^ Formalism.HermitianLatticesTheory.fDeg K) ^ (finrank K V - 1) * C1)) := by
        refine mul_le_mul_of_nonneg_left (hle.trans ?_) (zpow_nonneg hT0.le _)
        exact mul_le_mul_of_nonneg_right hcard
          (mul_nonneg (pow_nonneg (pow_nonneg hT0.le _) _) hC1n)
    _ = (2 ^ Formalism.HermitianLatticesTheory.fDeg K * C1 / (Ideal.absNorm (bId v) : ℝ)) *
        (T ^ (-((Formalism.HermitianLatticesTheory.fDeg K * finrank K V : ℕ) : ℤ)) *
          (T ^ Formalism.HermitianLatticesTheory.fDeg K * (T ^ Formalism.HermitianLatticesTheory.fDeg K) ^ (finrank K V - 1))) := by ring
    _ = 2 ^ Formalism.HermitianLatticesTheory.fDeg K * C1 / (Ideal.absNorm (bId v) : ℝ) := by rw [hTT, mul_one]

end A5

open A5 in
theorem tendsto_singS_sum (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (hm : 2 ≤ finrank K V) :
    Tendsto (fun j : ℕ => ((j : ℝ) ^ 2) ^ (-((Formalism.HermitianLatticesTheory.fDeg K * finrank K V : ℕ) : ℤ)) *
        ∑ᶠ n ∈ boxSet K F ((j : ℝ) ^ 2),
          (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (finrank K V - 1) * singS F h L n)
      atTop (𝓝 ((finrank K V : ℝ) ^ (-(Formalism.HermitianLatticesTheory.fDeg K : ℤ)) /
        Real.sqrt ((2 * Formalism.HermitianLatticesTheory.vInv K) ^ Formalism.HermitianLatticesTheory.fDeg K) * lValEtaF K F (finrank K V))) := by
  classical
  set S : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} :=
    (finite_vd_ne_zero (F := F) hK hF hs hd hL hLi).toFinset with hSdef
  have hS : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, vd h L 𝔭.1 ≠ 0 → 𝔭 ∈ S := fun 𝔭 h𝔭 =>
    (Set.Finite.mem_toFinset _).mpr h𝔭
  obtain ⟨C, hC⟩ := dominated hK hF hs hd hL hLi hm S
  set c0 : ℝ := (finrank K V : ℝ) ^ (-(Formalism.HermitianLatticesTheory.fDeg K : ℤ)) /
    Real.sqrt ((2 * Formalism.HermitianLatticesTheory.vInv K) ^ Formalism.HermitianLatticesTheory.fDeg K) with hc0
  have main := tendsto_weighted_tprod
    (q := fun 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} => (Ideal.absNorm 𝔭.1 : ℝ))
    (fun 𝔭 => by exact_mod_cast two_le_absNorm 𝔭.2) summable_inv_absNorm_sq S
    (ρ := roL h L S) (roL_zero hK hF hs hd (by first | exact hL | exact hL.toIsLattice) hLi hm hS) (fun 𝔭 h𝔭 j => by simp [roL, h𝔭])
    (roL_diff hK hF hs hd (by first | exact hL | exact hL.toIsLattice) hLi hm hS) valF
    (fun j : ℕ => (boxSet_finite hK hF ((j : ℝ) ^ 2)).toFinset)
    (fun n => (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (finrank K V - 1) * ∏ 𝔭 ∈ S, aLoc h L 𝔭 n)
    (fun j : ℕ => ((j : ℝ) ^ 2) ^ (-((Formalism.HermitianLatticesTheory.fDeg K * finrank K V : ℕ) : ℤ)))
    (c0 * ∏ 𝔭 ∈ S, (eFac K (finrank K V) 𝔭.1)⁻¹) c0 C
    (fun 𝔭 => (eFac K (finrank K V) 𝔭.1)⁻¹) (fun h0 => by rw [h0, zero_mul]) ?_ ?_ ?_
  · refine main.congr fun j => ?_
    rw [finsum_mem_eq_finite_toFinset_sum _ (boxSet_finite hK hF ((j : ℝ) ^ 2))]
    congr 1
    refine Finset.sum_congr rfl fun n hn => ?_
    have hb : n ∈ boxSet K F ((j : ℝ) ^ 2) := (Set.Finite.mem_toFinset _).mp hn
    rw [singS_eq hK hF hs hd (by first | exact hL | exact hL.toIsLattice) hLi hm hS (ne_zero_of_mem_boxSet hb), mul_assoc]
  · intro v hv
    have ht := tendsto_sum_box_ideal hK hF hs hd hL hLi hm S hS (bId_ne_bot v)
      (fun 𝔭 h𝔭 => bId_sup_eq_top (Finset.disjoint_right.mp hv h𝔭))
    simp_rw [coe_filter_box hK hF, finsum_mem_coe_finset] at ht
    rw [absNorm_bId] at ht
    have he : c0 * (∏ 𝔭 ∈ S, (eFac K (finrank K V) 𝔭.1)⁻¹) /
        nrm (fun 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} => (Ideal.absNorm 𝔭.1 : ℝ)) v =
        c0 / nrm (fun 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} => (Ideal.absNorm 𝔭.1 : ℝ)) v *
          ∏ 𝔭 ∈ S, (eFac K (finrank K V) 𝔭.1)⁻¹ := by ring
    rw [he]
    exact ht
  · filter_upwards [eventually_ge_atTop 1] with j hj v
    refine hC _ ?_ v
    have : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    nlinarith
  · intro S' hS'
    have ht := tendsto_sum_box_ideal hK hF hs hd hL hLi hm S' (fun 𝔭 h𝔭 => hS' (hS 𝔭 h𝔭))
      (b := ⊤) (by simp) (fun 𝔭 _ => by simp)
    simp only [Submodule.mem_top, and_true, Ideal.absNorm_top, Nat.cast_one, div_one] at ht
    refine ht.congr fun j => ?_
    have hset : {n : 𝓞 F | n ∈ boxSet K F ((j : ℝ) ^ 2)} = boxSet K F ((j : ℝ) ^ 2) := rfl
    rw [hset, finsum_mem_eq_finite_toFinset_sum _ (boxSet_finite hK hF ((j : ℝ) ^ 2))]
    congr 1
    refine Finset.sum_congr rfl fun n hn => ?_
    have hb : n ∈ boxSet K F ((j : ℝ) ^ 2) := (Set.Finite.mem_toFinset _).mp hn
    rw [mul_assoc, ← prod_aLoc hK hF hs hd (by first | exact hL | exact hL.toIsLattice) hLi hS hS' (ne_zero_of_mem_boxSet hb)]
    rfl

end Formalism.HermitianLattices.Ext.L3
end
end
end
