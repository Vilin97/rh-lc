module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EncardSmallSectionsMulLeQuotientPowerTwistStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogNcardSeminormBallExpSmallLeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundlePairSectionBallFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSeminormBallFamilySectionBallsStatement
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Floor.Semifield
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.SpecificLimits.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundlePairSectionBallFiniteStatement
import Mathlib.Algebra.Order.Floor.Semifield
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundlePairSectionsMulMemNormMulStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermPairPowSectionMemAndNormPowStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSectionBallOfMulSmallSectionPowTwistStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyLeAtNearbyIndices

section

@[expose] public section

open Filter Topology

namespace GlobalTheory

theorem tendsto_comp_div_pow_of_ratio (d : ℕ) (h : ℕ → ℝ) (L r : ℝ) (u : ℕ → ℕ) (hr : 0 < r)
    (hh : Tendsto (fun j : ℕ => h j / (j : ℝ) ^ d) atTop (𝓝 L))
    (hu : Tendsto (fun M : ℕ => (u M : ℝ) / M) atTop (𝓝 r)) :
    Tendsto (fun M : ℕ => h (u M) / (M : ℝ) ^ d) atTop (𝓝 (L * r ^ d)) ∧
      Tendsto u atTop atTop := by
  have hu' : Tendsto (fun M : ℕ => (u M : ℝ)) atTop atTop := by
    have h1 : Tendsto (fun M : ℕ => (u M : ℝ) / M * M) atTop atTop :=
      Tendsto.pos_mul_atTop hr hu tendsto_natCast_atTop_atTop
    refine h1.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with M hM
    have : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
    field_simp
  have huN : Tendsto u atTop atTop := tendsto_natCast_atTop_iff.1 hu'
  refine ⟨?_, huN⟩
  have h2 := (hh.comp huN).mul (hu.pow d)
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop 0, huN.eventually (eventually_gt_atTop 0)] with M hM huM
  have a : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have b : (u M : ℝ) ≠ 0 := by exact_mod_cast huM.ne'
  simp only [Function.comp]
  rw [div_pow]
  field_simp

theorem tendsto_natDiv_div_self (n : ℕ) (hn : 0 < n) :
    Tendsto (fun M : ℕ => ((M / n : ℕ) : ℝ) / M) atTop (𝓝 (1 / n)) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hlow : Tendsto (fun M : ℕ => 1 / (n:ℝ) - 1 / (M:ℝ)) atTop (𝓝 (1 / n)) := by
    have := (tendsto_one_div_atTop_nhds_zero_nat).const_sub (1 / (n:ℝ))
    rwa [sub_zero] at this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with M hM
    have hMR : (0:ℝ) < M := by exact_mod_cast hM
    have key : (M:ℝ) / n - 1 ≤ ((M / n : ℕ) : ℝ) := by
      have := Nat.lt_floor_add_one ((M:ℝ) / n)
      rw [Nat.floor_div_eq_div] at this
      linarith
    rw [le_div_iff₀ hMR]
    have : (1 / (n:ℝ) - 1 / M) * M = M / n - 1 := by field_simp
    linarith
  · filter_upwards [eventually_gt_atTop 0] with M hM
    have hMR : (0:ℝ) < M := by exact_mod_cast hM
    rw [div_le_iff₀ hMR]
    have := Nat.cast_div_le (α := ℝ) (m := M) (n := n)
    have e : 1 / (n:ℝ) * M = M / n := by ring
    linarith

theorem eventually_le_at_nearby_indices :
    ∀ (d b c : ℕ) (f : ℝ → ℕ → ℝ) (g : ℤ → ℝ) (f₀ : ℤ → ℝ) (α β : ℝ), 0 < d → 0 < b →
      (∀ η, 0 ≤ η → Tendsto (fun j : ℕ => f η j / (j : ℝ) ^ d) atTop (𝓝 (α + β * η))) →
      (∀ j : ℕ, f₀ j = f 0 j) → (∀ η, 0 < η → ∀ᶠ j : ℕ in atTop, g j ≤ f η j) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ᶠ M : ℕ in atTop,
        g (b * M + (M / n : ℕ) - c) ≤ f₀ (b * M - c) + ε * (M : ℝ) ^ d := by
  intro d b c f g f₀ α β _hd hb hf hf₀ hg ε hε
  have hbR : (0:ℝ) < b := by exact_mod_cast hb
  have hlim : Tendsto (fun n : ℕ => α * ((b:ℝ) + 1 / (n:ℝ)) ^ d) atTop
      (𝓝 (α * (b:ℝ) ^ d)) := by
    have := ((tendsto_one_div_atTop_nhds_zero_nat.const_add (b : ℝ)).pow d).const_mul α
    rwa [add_zero] at this
  have hn : ∀ᶠ n : ℕ in atTop, α * ((b:ℝ) + 1 / (n:ℝ)) ^ d < α * (b:ℝ) ^ d + ε / 3 :=
    (tendsto_order.1 hlim).2 _ (by linarith)
  filter_upwards [hn, eventually_gt_atTop 0] with n hn hn0
  have hnR : (0:ℝ) < n := by exact_mod_cast hn0
  have hrpos : (0:ℝ) < (b:ℝ) + 1 / (n:ℝ) := by positivity
  obtain ⟨η, hη, hηlt⟩ : ∃ η : ℝ, 0 < η ∧
      (α + β * η) * ((b:ℝ) + 1 / (n:ℝ)) ^ d < α * ((b:ℝ) + 1 / (n:ℝ)) ^ d + ε / 3 := by
    have hcont : Tendsto (fun η : ℝ => (α + β * η) * ((b:ℝ) + 1 / (n:ℝ)) ^ d) (𝓝[>] 0)
        (𝓝 (α * ((b:ℝ) + 1 / (n:ℝ)) ^ d)) := by
      have : Tendsto (fun η : ℝ => (α + β * η) * ((b:ℝ) + 1 / (n:ℝ)) ^ d) (𝓝 0)
          (𝓝 ((α + β * 0) * ((b:ℝ) + 1 / (n:ℝ)) ^ d)) :=
        ((continuous_const.add (continuous_const.mul continuous_id)).mul
          continuous_const).tendsto 0
      rw [mul_zero, add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    have hev := (hcont.eventually (gt_mem_nhds (show α * ((b:ℝ) + 1 / (n:ℝ)) ^ d <
      α * ((b:ℝ) + 1 / (n:ℝ)) ^ d + ε / 3 by linarith))).and
      (self_mem_nhdsWithin : ∀ᶠ x in 𝓝[>] (0:ℝ), x ∈ Set.Ioi 0)
    obtain ⟨η, h1, h2⟩ := hev.exists
    exact ⟨η, h2, h1⟩
  have hc0 : Tendsto (fun M : ℕ => (c:ℝ) / M) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have hr₁ : Tendsto (fun M : ℕ => ((b * M + M / n - c : ℕ) : ℝ) / M) atTop
      (𝓝 ((b:ℝ) + 1 / (n:ℝ))) := by
    have : Tendsto (fun M : ℕ => (b:ℝ) + ((M / n : ℕ) : ℝ) / M - (c:ℝ) / M) atTop
        (𝓝 ((b:ℝ) + 1 / n - 0)) :=
      ((tendsto_natDiv_div_self n hn0).const_add _).sub hc0
    rw [sub_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop c, eventually_gt_atTop 0] with M hMc hM0
    have hMR : (M:ℝ) ≠ 0 := by exact_mod_cast hM0.ne'
    have hle : c ≤ b * M + M / n :=
      le_trans hMc (le_trans (Nat.le_mul_of_pos_left M hb) (Nat.le_add_right _ _))
    rw [Nat.cast_sub hle]
    push_cast
    field_simp
  have hr₀ : Tendsto (fun M : ℕ => ((b * M - c : ℕ) : ℝ) / M) atTop (𝓝 (b:ℝ)) := by
    have : Tendsto (fun M : ℕ => (b:ℝ) - (c:ℝ) / M) atTop (𝓝 ((b:ℝ) - 0)) :=
      tendsto_const_nhds.sub hc0
    rw [sub_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop c, eventually_gt_atTop 0] with M hMc hM0
    have hMR : (M:ℝ) ≠ 0 := by exact_mod_cast hM0.ne'
    have hle : c ≤ b * M := le_trans hMc (Nat.le_mul_of_pos_left M hb)
    rw [Nat.cast_sub hle]
    push_cast
    field_simp
  obtain ⟨hA, hu₁⟩ := tendsto_comp_div_pow_of_ratio d (f η) (α + β * η) _ _ hrpos
    (hf η hη.le) hr₁
  obtain ⟨hB, -⟩ := tendsto_comp_div_pow_of_ratio d (f 0) (α + β * 0) _ _ hbR
    (hf 0 le_rfl) hr₀
  have hev : ∀ᶠ M : ℕ in atTop,
      f η (b * M + M / n - c) / (M:ℝ) ^ d - f 0 (b * M - c) / (M:ℝ) ^ d < ε :=
    (tendsto_order.1 (hA.sub hB)).2 ε (by rw [mul_zero, add_zero]; linarith)
  filter_upwards [hev, hu₁.eventually (hg η hη), eventually_ge_atTop c, eventually_gt_atTop 0]
    with M hM hgM hMc hM0
  have hMR : (0:ℝ) < M := by exact_mod_cast hM0
  have hle1 : c ≤ b * M + M / n :=
    le_trans hMc (le_trans (Nat.le_mul_of_pos_left M hb) (Nat.le_add_right _ _))
  have hle0 : c ≤ b * M := le_trans hMc (Nat.le_mul_of_pos_left M hb)
  have e1 : ((b:ℤ) * M + ((M / n : ℕ) : ℤ) - c) = ((b * M + M / n - c : ℕ) : ℤ) := by
    rw [Nat.cast_sub hle1]; push_cast; ring
  have e0 : ((b:ℤ) * M - c) = ((b * M - c : ℕ) : ℤ) := by
    rw [Nat.cast_sub hle0]; push_cast; ring
  rw [e1, e0, hf₀]
  have hpos : 0 < (M:ℝ) ^ d := pow_pos hMR d
  rw [← sub_div, div_lt_iff₀ hpos] at hM
  linarith

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogCountNearbyPowersSecondBundleLe

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem lc_mono_radius {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {D : ℕ}
    (hX : IsArithVar p D) (P : Pair p) (a b : ℤ) {R R' : ℝ} (h : R ≤ R') : P.lc a b R ≤ P.lc a b R' := by
  have hsub : P.Bl a b R ⊆ P.Bl a b R' := fun f hf => ⟨hf.1, fun σ y => (hf.2 σ y).trans h⟩
  have hfin : (P.Bl a b R').Finite := GlobalTheory.T.hermLineBundlePair_sectionBall_finite k X p D hX P a b R'
  have hle : (P.Bl a b R).ncard ≤ (P.Bl a b R').ncard := Set.ncard_le_ncard hsub hfin
  unfold VolBr.Pair.lc
  rcases Nat.eq_zero_or_pos (P.Bl a b R).ncard with h0 | h0
  · rw [h0, Nat.cast_zero, Real.log_zero]
    exact Real.log_natCast_nonneg _
  · exact Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast hle)

theorem lc_nearby_le : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D →
    ∀ (P : Pair p) (b c : ℕ), 0 < b → Regime P D → ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ᶠ M : ℕ in atTop,
      P.lc 0 (b * M + (M / n : ℕ) - c) 2 ≤ P.lc 0 (b * M - c) 1 + ε * (M : ℝ) ^ (D + 1) := by
  intro k _ X _ p D hX P b c hb hR ε hε
  obtain ⟨α, β, hαβ⟩ := hR
  refine GlobalTheory.eventually_le_at_nearby_indices (D + 1) b c
    (fun η j => P.lc 0 (j : ℤ) (Real.exp (η * j))) (fun j => P.lc 0 j 2) (fun j => P.lc 0 j 1) α β
    (Nat.succ_pos D) hb hαβ ?_ ?_ ε hε
  · intro j
    simp
  · intro η hη
    have ht : Tendsto (fun j : ℕ => Real.exp (η * j)) atTop atTop :=
      Real.tendsto_exp_atTop.comp (Tendsto.const_mul_atTop hη tendsto_natCast_atTop_atTop)
    filter_upwards [ht.eventually (eventually_ge_atTop 2)] with j hj
    exact lc_mono_radius hX P 0 (j : ℤ) hj

end GlobalTheory.HSNef
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogCountNearbyPowersSecondBundleLeStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem _root_.GlobalTheory.T.log_count_nearby_powers_second_bundle_le : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (b c : ℕ), 0 < b → Regime P D → ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ᶠ M : ℕ in atTop, P.lc 0 (b * M + (M / n : ℕ) - c) 2 ≤ P.lc 0 (b * M - c) 1 + ε * (M : ℝ) ^ (D + 1) := by
  first | exact @GlobalTheory.HSNef.lc_nearby_le | exact GlobalTheory.HSNef.lc_nearby_le | (intros; apply GlobalTheory.HSNef.lc_nearby_le <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogCountTwistExpRadiusLePowSucc

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem lc_twist_le_of_good {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} (P : Pair p)
    {D b : ℕ} {s t : X.functionField} (hG : P.Good D b s t) (N c : ℕ) (R : ℝ)
    (hfin : (P.Bl 0 ((N : ℤ) * b) R).Finite) :
    P.lc N (-c) R ≤ P.lc 0 ((N : ℤ) * b) R := by
  have nu_nonneg : ∀ (a e : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField), 0 ≤ P.nu a e σ y f :=
    fun a e σ y f => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  obtain ⟨htH, htn⟩ := hG.t_mem
  obtain ⟨hsH, hsn⟩ := hG.s_mem
  obtain ⟨hpH, hpn⟩ := GlobalTheory.T.hermPair_pow_section_mem_and_norm_pow k X p P (-1) b t htH N
  obtain ⟨hqH, hqn⟩ := GlobalTheory.T.hermPair_pow_section_mem_and_norm_pow k X p P 0 1 s hsH c
  have e1 : (N : ℤ) + N * -1 + c * 0 = 0 := by ring
  have e2 : -(c : ℤ) + N * b + c * 1 = N * b := by ring
  have hmaps : ∀ f ∈ P.Bl N (-c) R, f * t ^ N * s ^ c ∈ P.Bl 0 ((N : ℤ) * b) R := by
    rintro f ⟨hfH, hfn⟩
    obtain ⟨hH1, hn1⟩ := GlobalTheory.T.hermLineBundlePair_sections_mul_mem_norm_mul k X p P N (-c) (N * -1) (N * b) f (t ^ N) hfH hpH
    obtain ⟨hH, hn⟩ := GlobalTheory.T.hermLineBundlePair_sections_mul_mem_norm_mul k X p P (N + N * -1) (-c + N * b) (c * 0) (c * 1) (f * t ^ N) (s ^ c) hH1 hqH
    rw [e1, e2] at hH hn
    refine ⟨hH, fun σ y => ?_⟩
    rw [hn σ y, hn1 σ y, hpn σ y, hqn σ y]
    have h1 : P.nu (-1) b σ y t ^ N ≤ 1 := pow_le_one₀ (nu_nonneg _ _ _ _ _) (htn σ y)
    have h2 : P.nu 0 1 σ y s ^ c ≤ 1 := pow_le_one₀ (nu_nonneg _ _ _ _ _) (hsn σ y)
    have h3 : P.nu N (-c) σ y f * P.nu (-1) b σ y t ^ N ≤ R :=
      (mul_le_of_le_one_right (nu_nonneg _ _ _ _ _) h1).trans (hfn σ y)
    exact (mul_le_of_le_one_right (mul_nonneg (nu_nonneg _ _ _ _ _) (pow_nonneg (nu_nonneg _ _ _ _ _) _)) h2).trans h3
  have hinj : Set.InjOn (fun f => f * t ^ N * s ^ c) (P.Bl N (-c) R) := fun x _ y _ h =>
    mul_right_cancel₀ (pow_ne_zero N hG.t_ne) (mul_right_cancel₀ (pow_ne_zero c hG.s_ne) h)
  have hcard := Set.ncard_le_ncard_of_injOn _ hmaps hinj hfin
  unfold Pair.lc
  rcases Nat.eq_zero_or_pos (P.Bl N (-c) R).ncard with h0 | h0
  · rw [h0, Nat.cast_zero, Real.log_zero]
    exact Real.log_natCast_nonneg _
  · exact Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast hcard)

theorem crude_upper_lc_twist : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (b : ℕ) (s t : X.functionField), P.Good D b s t → ∀ c : ℕ, Regime P D → ∃ C : ℝ, ∀ᶠ N : ℕ in atTop, P.lc N (-c) (Real.exp (3 * N)) ≤ C * (N : ℝ) ^ (D + 1) := by
  intro k _ X _ p D hX P b s t hG c hR
  obtain ⟨α, β, hαβ⟩ := hR
  have hb : (0 : ℝ) < b := by exact_mod_cast hG.pos
  have hlim := hαβ (3 / b) (by positivity)
  have hsub : Tendsto (fun N : ℕ => b * N) atTop atTop :=
    tendsto_id.const_mul_atTop' hG.pos
  obtain ⟨C, hev⟩ : ∃ C : ℝ, ∀ᶠ N : ℕ in atTop,
      P.lc 0 ((b * N : ℕ) : ℤ) (Real.exp (3 / b * ((b * N : ℕ) : ℝ))) / ((b * N : ℕ) : ℝ) ^ (D + 1) < C :=
    ⟨_, (hlim.comp hsub).eventually (gt_mem_nhds (lt_add_one _))⟩
  refine ⟨C * (b : ℝ) ^ (D + 1), ?_⟩
  filter_upwards [hev, eventually_ge_atTop 1] with N hN hN1
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have e1 : 3 / (b : ℝ) * ((b * N : ℕ) : ℝ) = 3 * N := by push_cast; field_simp
  have e2 : ((b * N : ℕ) : ℤ) = (N : ℤ) * b := by push_cast; ring
  have hpos : (0 : ℝ) < ((b * N : ℕ) : ℝ) ^ (D + 1) := by push_cast; positivity
  rw [e1, e2, div_lt_iff₀ hpos] at hN
  calc P.lc N (-c) (Real.exp (3 * N)) ≤ P.lc 0 ((N : ℤ) * b) (Real.exp (3 * N)) :=
        lc_twist_le_of_good P hG N c _ (GlobalTheory.T.hermLineBundlePair_sectionBall_finite k X p D hX P 0 _ _)
    _ ≤ C * ((b * N : ℕ) : ℝ) ^ (D + 1) := hN.le
    _ = C * (b : ℝ) ^ (D + 1) * (N : ℝ) ^ (D + 1) := by push_cast; ring

end GlobalTheory.HSNef
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogCountTwistExpRadiusLePowSuccStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem _root_.GlobalTheory.T.log_count_twist_exp_radius_le_pow_succ : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (b : ℕ) (s t : X.functionField), P.Good D b s t → ∀ c : ℕ, Regime P D → ∃ C : ℝ, ∀ᶠ N : ℕ in atTop, P.lc N (-c) (Real.exp (3 * N)) ≤ C * (N : ℝ) ^ (D + 1) := by
  first | exact @GlobalTheory.HSNef.crude_upper_lc_twist | exact GlobalTheory.HSNef.crude_upper_lc_twist | (intros; apply GlobalTheory.HSNef.crude_upper_lc_twist <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionCountLogTwistContinuityAbove

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem log_add_log_le_of_mul_le_mul (a b c d e : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (h : a * b ≤ c * d) (hce : c ≤ e) :
    Real.log a + Real.log b ≤ Real.log e + Real.log d := by
  have hab : 1 ≤ a * b := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hcd : 1 ≤ c * d := hab.trans h
  have hc : c ≠ 0 := by rintro rfl; simp at hcd
  have hd : d ≠ 0 := by rintro rfl; simp at hcd
  have he : e ≠ 0 := by omega
  have h1 : Real.log ((a : ℝ) * b) ≤ Real.log ((e : ℝ) * d) := by
    apply Real.log_le_log
    · have : (1 : ℝ) ≤ (a : ℝ) * b := by exact_mod_cast hab
      linarith
    · have : a * b ≤ e * d := h.trans (Nat.mul_le_mul_right d hce)
      exact_mod_cast this
  rwa [Real.log_mul (by exact_mod_cast (by omega : a ≠ 0)) (by exact_mod_cast (by omega : b ≠ 0)),
    Real.log_mul (by exact_mod_cast he) (by exact_mod_cast hd)] at h1

theorem lc_add_div_sub_le : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (P : Pair p) (b : ℕ) (s t : X.functionField), P.Good D b s t → ∀ c : ℕ, GenAt P c →
    Regime P D → ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ᶠ M : ℕ in atTop,
    P.lc M ((M / n : ℕ) - c) 1 ≤ P.lc M (-c) 1 + ε * (M : ℝ) ^ (D + 1) := by
  intro k _ X _ p D hD P b s t hG c hgen hreg ε hε
  have hfin : ∀ (a c : ℤ) (R : ℝ), (P.Bl a c R).Finite := GlobalTheory.T.hermLineBundlePair_sectionBall_finite k X p D hD P
  have hball : ∀ a c : ℤ, IsBallFam (P.H a c) (P.Bl a c) := GlobalTheory.T.isSeminormBallFamily_sectionBalls k X p P
  have hpos : ∀ (a c : ℤ) (R : ℝ), 0 ≤ R → 1 ≤ (P.Bl a c R).ncard := fun a c R hR =>
    Nat.one_le_iff_ne_zero.mpr ((Set.ncard_pos (hfin a c R)).mpr ⟨0, (hball a c).zero_mem R hR⟩).ne'
  obtain ⟨C0, hC0⟩ := GlobalTheory.T.log_count_twist_exp_radius_le_pow_succ k X p D hD P b s t hG c hreg
  obtain ⟨δ, hδ, hrad⟩ := GlobalTheory.T.exists_log_ncard_seminormBall_exp_small_le X.functionField (fun N => P.H (N : ℤ) (-c)) (fun N => P.Bl (N : ℤ) (-c))
    (D + 1) (Nat.succ_pos D) (fun N => hball N _) (fun N R => hfin N _ R) C0 hC0 (ε / 2) (by positivity)
  obtain ⟨C, hC, hdiv⟩ := GlobalTheory.T.mem_sectionBall_of_mul_smallSection_pow_twist k X p D hD P c hgen s hG.s_mem.1 hG.s_ne (δ / 3) (by positivity)
  have hdA := GlobalTheory.T.log_count_nearby_powers_second_bundle_le k X p D hD P b c hG.pos hreg (ε / 2) (by positivity)
  have hn : ∀ᶠ n : ℕ in atTop, 3 * C / δ ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  filter_upwards [hdA, hn] with n hdAn hnC
  filter_upwards [hdAn, hrad, hn] with M hdm hradm hMC
  have hnδ : 3 * C ≤ (n : ℝ) * δ := (div_le_iff₀ hδ).mp hnC
  have hMδ : 3 * C ≤ (M : ℝ) * δ := (div_le_iff₀ hδ).mp hMC
  have hmn : ((M / n : ℕ) : ℝ) * n ≤ M := by exact_mod_cast Nat.div_mul_le_self M n
  generalize M / n = m at *
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m

  have hrad_le : Real.exp (δ / 3 * (M : ℝ) + C * m + C) ≤ Real.exp (δ * (M : ℝ)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hnδ hm0, mul_le_mul_of_nonneg_right hmn hδ.le]
  have hSsub : {f | f ∈ P.H M (-c) ∧ f * s ^ m ∈ P.Bl M (m - c) 2} ⊆ P.Bl M (-c) (Real.exp (δ * (M : ℝ))) := by
    rintro f ⟨hf1, hf2⟩
    have hf := hdiv M m f hf1 hf2
    exact ⟨hf.1, fun σ y => (hf.2 σ y).trans hrad_le⟩
  have hEfin := hfin M (-c) (Real.exp (δ * (M : ℝ)))
  have hSfin := hEfin.subset hSsub
  have hlev := GlobalTheory.T.encard_small_sections_mul_le_quotient_power_twist k X p D hD P b s t hG c M m
  rw [← (hfin _ _ _).cast_ncard_eq, ← (hfin _ _ _).cast_ncard_eq, ← hSfin.cast_ncard_eq,
    ← (hfin _ _ _).cast_ncard_eq] at hlev
  have hnat : ∀ x y z w : ℕ, (x : ℕ∞) * y ≤ z * w → x * y ≤ z * w := fun x y z w h => by exact_mod_cast h
  have hkey := log_add_log_le_of_mul_le_mul _ _ _ _ _ (hpos _ _ _ zero_le_one) (hpos _ _ _ zero_le_one)
    (hnat _ _ _ _ hlev)
    (Set.ncard_le_ncard hSsub hEfin)
  simp only [Pair.lc] at hdm ⊢
  linarith

end GlobalTheory.HSNef
end
end
