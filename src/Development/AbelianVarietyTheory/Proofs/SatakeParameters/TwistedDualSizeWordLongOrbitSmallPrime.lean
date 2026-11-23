module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MulSmallBoundsLeParametersRoundedSizeBoundStatement
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
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParametersLeastPowerDepthSpecStatement
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AtMostTwoThickInWindowLongOrbitStatement
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualOrbitPageWordBoxStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualOrbitPageWordThickIffThickEmbeddingStatement
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualSizeWordLetterEqPageWordStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ClusterDepthAtPrimeEqLeastPowerDepth

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem jA_eq_depth : ∀ {D : D7} (L : SizeData₂ D) (l : ℕ), 11 ≤ l → (l : ℝ) < LevelStarExponents.lA L → jA L l = depth L l := by
  intro D L l hl hlA
  have hl' : (11 : ℝ) ≤ l := by exact_mod_cast hl
  have hx : (1 : ℝ) < (l : ℝ) - 1 := by linarith
  have hA : (0 : ℝ) < LevelStarExponents.lA L := by linarith
  have key : ∀ j : ℕ, LevelStarExponents.lA L ≤ ((l : ℝ) - 1) ^ j ↔ ⌈Real.logb ((l : ℝ) - 1) (LevelStarExponents.lA L)⌉₊ ≤ j := by
    intro j
    rw [Nat.ceil_le, Real.logb_le_iff_le_rpow hx hA, Real.rpow_natCast]
  have hlog : 1 < Real.logb ((l : ℝ) - 1) (LevelStarExponents.lA L) := by
    rw [Real.lt_logb_iff_rpow_lt hx hA, Real.rpow_one]; linarith
  have hc : 1 ≤ ⌈Real.logb ((l : ℝ) - 1) (LevelStarExponents.lA L)⌉₊ := by
    rw [Nat.one_le_ceil_iff]; linarith
  have hset : {j : ℕ | LevelStarExponents.lA L ≤ ((l : ℝ) - 1) ^ j} = Set.Ici ⌈Real.logb ((l : ℝ) - 1) (LevelStarExponents.lA L)⌉₊ := by
    ext j; simp only [Set.mem_setOf_eq, Set.mem_Ici]; exact key j
  unfold jA depth
  rw [hset, csInf_Ici, max_eq_right hc]

end GlobalTheory.HTW.Rec
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParametersClusterDepthAtPrimeEqLeastPowerDepthStatement

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.clusterDepthAtPrime_eq_leastPowerDepth : ∀ {D : D7} (L : SizeData₂ D) (l : ℕ), 11 ≤ l → (l : ℝ) < LevelStarExponents.lA L → jA L l = depth L l := by
  first | exact @GlobalTheory.HTW.Rec.jA_eq_depth | exact GlobalTheory.HTW.Rec.jA_eq_depth | (intros; apply GlobalTheory.HTW.Rec.jA_eq_depth <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.CyclicWordMarkedClustersOfAtMostTwoInWindow

section

@[expose] public section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem winClusters_exists_step {n : ℕ} (th : ZMod n → Prop) (j : ℕ) (x : ZMod n) :
    ∃ s : ℕ, s ≤ j ∧ (s = 0 → ∀ q : ℕ, 1 ≤ q → q ≤ j → ¬ th (x + q)) ∧ (0 < s → th (x + s)) ∧
      ∀ q : ℕ, 0 < q → q < s → ¬ th (x + q) := by
  classical
  by_cases h : ∃ q : ℕ, 1 ≤ q ∧ q ≤ j ∧ th (x + q)
  · obtain ⟨h1, h2, h3⟩ := Nat.find_spec h
    refine ⟨Nat.find h, h2, fun h0 => absurd h0 (by omega), fun _ => h3, ?_⟩
    intro q hq hqs hth
    exact Nat.find_min h hqs ⟨hq, by omega, hth⟩
  · push_neg at h
    refine ⟨0, Nat.zero_le _, fun _ q hq hqj hth => absurd hth (h q hq hqj), fun h0 => absurd h0 (lt_irrefl 0),
      fun q hq hq0 => absurd hq0 (by omega)⟩

theorem winClusters : ∀ {n : ℕ} (th : ZMod n → Prop) (L j : ℕ), 1 ≤ j → 2 * j + 1 ≤ L → 2 * j < n →
    WindowTwo th L → Clusters th j := by
  intro n th L j _ hL hn hW
  choose sp hsp using winClusters_exists_step th j
  set F : Set (ZMod n) := {x | th x ∧ ∀ q : ℕ, 1 ≤ q → q ≤ j → ¬ th (x - q)} with hFdef
  have key : ∀ x1 x2 : ZMod n, x1 ∈ F → x2 ∈ F → ∀ s1 s2 : ℕ, s1 ≤ s2 → s2 ≤ j →
      x1 + s1 = x2 + s2 → x1 = x2 := by
    intro x1 x2 hx1 hx2 s1 s2 hs hs2 he
    rcases Nat.lt_or_ge s1 s2 with hlt | hge
    · exfalso
      apply hx1.2 (s2 - s1) (by omega) (by omega)
      have : x1 - ((s2 - s1 : ℕ) : ZMod n) = x2 := by
        rw [Nat.cast_sub hs]
        linear_combination he
      rw [this]; exact hx2.1
    · have : s1 = s2 := le_antisymm hs hge
      subst this
      exact add_right_cancel he
  have ofCl : ∀ x y : ZMod n, (y = x ∨ y = x + (sp x : ZMod n)) → ∃ s : ℕ, s ≤ j ∧ y = x + s := by
    intro x y h
    rcases h with h | h
    · exact ⟨0, Nat.zero_le _, by simp [h]⟩
    · exact ⟨sp x, (hsp x).1, h⟩
  refine ⟨F, sp, ?_, ?_⟩
  · rintro x ⟨hx, hxF⟩
    obtain ⟨h1, _, h3, h4⟩ := hsp x
    refine ⟨hx, h1, by omega, ?_, h4, hxF⟩
    rcases Nat.eq_zero_or_pos (sp x) with h | h
    · rw [h]; simpa using hx
    · exact h3 h
  · intro y hy
    have ex : ∃ x, x ∈ F ∧ (y = x ∨ y = x + (sp x : ZMod n)) := by
      by_cases hyF : ∀ q : ℕ, 1 ≤ q → q ≤ j → ¬ th (y - q)
      · exact ⟨y, ⟨hy, hyF⟩, Or.inl rfl⟩
      · push_neg at hyF
        obtain ⟨q, hq1, hqj, hq⟩ := hyF
        have hxF : y - (q : ZMod n) ∈ F := by
          refine ⟨hq, ?_⟩
          intro q' hq'1 hq'j hth
          apply hW (y - q - q') 0 q' (q' + q) (by omega) (by omega) (by omega)
          refine ⟨by simpa using hth, ?_, ?_⟩
          · have : y - (q : ZMod n) - q' + (q' : ℕ) = y - q := by ring
            rw [this]; exact hq
          · have : y - (q : ZMod n) - q' + ((q' + q : ℕ) : ZMod n) = y := by push_cast; ring
            rw [this]; exact hy
        have hyx : y - (q : ZMod n) + (q : ZMod n) = y := by ring
        obtain ⟨h1, h2, h3, h4⟩ := hsp (y - q)
        have hspq : sp (y - q) = q := by
          rcases Nat.eq_zero_or_pos (sp (y - q)) with h0 | hpos
          · exact absurd (by rw [hyx]; exact hy) (h2 h0 q hq1 hqj)
          rcases lt_trichotomy (sp (y - q)) q with hlt | heq | hgt
          · exfalso
            apply hW (y - q) 0 (sp (y - q)) q hpos hlt (by omega)
            refine ⟨by simpa using hq, h3 hpos, ?_⟩
            rw [hyx]; exact hy
          · exact heq
          · exact absurd (by rw [hyx]; exact hy) (h4 q (by omega) hgt)
        refine ⟨y - q, hxF, Or.inr ?_⟩
        rw [hspq, hyx]
    obtain ⟨x, hxF, hx⟩ := ex
    refine ⟨x, ⟨hxF, hx⟩, ?_⟩
    rintro z ⟨hzF, hz⟩
    obtain ⟨s1, hs1, e1⟩ := ofCl z y hz
    obtain ⟨s2, hs2, e2⟩ := ofCl x y hx
    rcases le_total s1 s2 with h | h
    · exact key z x hzF hxF s1 s2 h hs2 (e1.symm.trans e2)
    · exact (key x z hxF hzF s2 s1 h hs1 (e2.symm.trans e1)).symm

end GlobalTheory.HTW
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.CyclicWordMarkedClustersOfAtMostTwoInWindowStatement

section

@[expose] public section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.cyclicWord_markedClusters_of_atMostTwoInWindow : ∀ {n : ℕ} (th : ZMod n → Prop) (L j : ℕ), 1 ≤ j → 2 * j + 1 ≤ L → 2 * j < n → WindowTwo th L → Clusters th j := by
  first | exact @GlobalTheory.HTW.winClusters | exact GlobalTheory.HTW.winClusters | (intros; apply GlobalTheory.HTW.winClusters <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.LongOrbitThickLettersClustersAndLength

section

@[expose] public section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory

theorem long_clusters : ∀ {R : Ranks} (H : Host R) (τ φ : R.GG) (j : ℕ), 4 * H.Lw < orderOf φ.2 → 1 ≤ j →
    2 * j + 2 ≤ H.Lw →
    Clusters (fun i : ZMod (orderOf φ) => Thick H (letter τ φ i)) j ∧ j + 1 ≤ orderOf φ := by
  intro R H τ φ j h4 hj hjL
  have hpos : 0 < orderOf φ := orderOf_pos φ
  have hdvd : orderOf φ.2 ∣ orderOf φ := orderOf_snd_dvd_orderOf
  have hle : orderOf φ.2 ≤ orderOf φ := Nat.le_of_dvd hpos hdvd
  have hw := GlobalTheory.T.atMostTwoThick_in_window_long_orbit H τ φ h4
  refine ⟨GlobalTheory.T.cyclicWord_markedClusters_of_atMostTwoInWindow _ H.Lw j hj (by omega) (by omega) hw, by omega⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.LongOrbitThickLettersClustersAndLengthStatement

section

@[expose] public section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.longOrbit_thickLetters_clusters_and_length : ∀ {R : Ranks} (H : Host R) (τ φ : R.GG) (j : ℕ), 4 * H.Lw < orderOf φ.2 → 1 ≤ j → 2 * j + 2 ≤ H.Lw → Clusters (fun i : ZMod (orderOf φ) => Thick H (letter τ φ i)) j ∧ j + 1 ≤ orderOf φ := by
  first | exact @GlobalTheory.long_clusters | exact GlobalTheory.long_clusters | (intros; apply GlobalTheory.long_clusters <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualPageWordClusterDepthLongOrbit

section

@[expose] public section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem pageWord_hypA_depth_of_long_orbit {D : D7} (L : SizeData₂ D) (hP : ParameterChoice' D L) (C : ℝ)
    (j : Fin D.R.m) (ε : ℤˣ) (τ φ : D.R.GG) (l : ℕ) (hR : Roomy L C) (hl : 11 ≤ l)
    (hlA : (l : ℝ) < LevelStarExponents.lA L) (ho : 4 * D.host.Lw < orderOf φ.2) :
    (pageWord L j ε τ φ).HypA (depth L l) := by
  obtain ⟨-, hLw, h2⟩ := GlobalTheory.T.leastPowerDepth_spec L hP l hl
  have h1 : 1 ≤ depth L l := le_trans (by norm_num) (h2 hlA)
  obtain ⟨hcl, hn⟩ := GlobalTheory.T.longOrbit_thickLetters_clusters_and_length D.host τ φ (depth L l) ho h1 hLw
  have hbox := GlobalTheory.T.twistedDualOrbitPageWord_box L C j ε τ φ hR
  have hth : (pageWord L j ε τ φ).thick = fun i : ZMod (orderOf φ) => Thick D.host (letter τ φ i) :=
    funext fun i => propext (GlobalTheory.T.twistedDualOrbitPageWord_thick_iff_thickEmbedding L C j ε τ φ hR i)
  have hpar := GlobalTheory.T.mul_smallBounds_le_roundedSizeBound L 40 C (depth L l) hR (by norm_num) (by linarith [hR.1]) hLw
  refine ⟨fun i => ?_, h1, hn, fun _ => ?_, ?_⟩
  · have := hbox.2.2.2.2.2 i
    have h0 : (0 : ℤ) ≤ ((pageWord L j ε τ φ).η : ℤ) := Int.natCast_nonneg _
    linarith
  · show 40 * (depth L l + 1) * (wHat D + sHat L + etaHat L + 1) ≤ bHat L
    exact_mod_cast hpar
  · rw [hth]; exact hcl

end GlobalTheory.HTW
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualPageWordClusterDepthLongOrbitStatement

section

@[expose] public section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.twistedDualPageWord_clusterDepth_long_orbit : ∀ {D : D7} (L : SizeData₂ D) (_ : ParameterChoice' D L) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) (τ φ : D.R.GG) (l : ℕ), Roomy L C → 11 ≤ l → (l : ℝ) < LevelStarExponents.lA L → 4 * D.host.Lw < orderOf φ.2 → (pageWord L j ε τ φ).HypA (depth L l) := by
  first | exact @GlobalTheory.HTW.pageWord_hypA_depth_of_long_orbit | exact GlobalTheory.HTW.pageWord_hypA_depth_of_long_orbit | (intros; apply GlobalTheory.HTW.pageWord_hypA_depth_of_long_orbit <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualSizeWordLongOrbitSmallPrime

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem wordsB_recWord_of_long_orbit : ∀ {D : D7} (L : SizeData₂ D) (_ : ParameterChoice' D L) (C C₂ : ℝ) (j : Fin D.R.m)
    (ε : ℤˣ) {n : ℕ} (g : ZMod n → D.R.GG) (ψ : D.R.GG) (l : ℕ), Roomy L C → IsOrbit g ψ → 2 * C₂ ≤ C →
    11 ≤ l → (l : ℝ) < LevelStarExponents.lA L → 4 * D.host.Lw < orderOf ψ.2 → WordsB L l C₂ (recWord L j ε g) := by
  intro D L hP C C₂ j ε n g ψ l hR hO hC hl hlA hord
  obtain ⟨hn, hg⟩ := hO
  subst hn
  have hgl : g = letter (g 0) ψ := by
    funext a
    rw [hg a]
    rfl
  generalize g 0 = τ at hgl
  subst hgl
  have hjA : jA L l = depth L l := GlobalTheory.T.clusterDepthAtPrime_eq_leastPowerDepth L l hl hlA
  have hA := GlobalTheory.T.twistedDualPageWord_clusterDepth_long_orbit L hP C j ε τ ψ l hR hl hlA hord
  obtain ⟨_, _, hjn, _, hcl⟩ := hA
  have hD := GlobalTheory.T.leastPowerDepth_spec L hP l hl
  have hth : ThickN (recWord L j ε (letter τ ψ)).b
      (recWord L j ε (letter τ ψ)).η (recWord L j ε (letter τ ψ)).sz =
      (pageWord L j ε τ ψ).thick := by
    funext a
    exact propext (GlobalTheory.T.twistedDualSizeWord_letter_eq_pageWord L C j ε τ ψ hR a).2.2.2
  refine ⟨?_, ?_, ?_⟩
  · rw [hjA]; exact hjn
  · rcases le_or_gt 0 C₂ with h0 | h0
    · rw [hjA]
      exact GlobalTheory.T.mul_smallBounds_le_roundedSizeBound L C₂ C (depth L l) hR h0 hC hD.2.1
    · have h1 : (0 : ℝ) ≤ ((jA L l : ℝ) + 1) * ((((recWord L j ε (letter τ ψ)).w +
          (recWord L j ε (letter τ ψ)).S + (recWord L j ε (letter τ ψ)).η : ℕ) : ℝ) + 1) := by
        positivity
      have h2 : C₂ * ((jA L l : ℝ) + 1) * ((((recWord L j ε (letter τ ψ)).w +
          (recWord L j ε (letter τ ψ)).S + (recWord L j ε (letter τ ψ)).η : ℕ) : ℝ) + 1) ≤ 0 := by
        rw [mul_assoc]; exact mul_nonpos_of_nonpos_of_nonneg h0.le h1
      exact h2.trans (Nat.cast_nonneg _)
  · rw [hth, hjA]; exact hcl

end GlobalTheory.HTW.Rec
end
end
