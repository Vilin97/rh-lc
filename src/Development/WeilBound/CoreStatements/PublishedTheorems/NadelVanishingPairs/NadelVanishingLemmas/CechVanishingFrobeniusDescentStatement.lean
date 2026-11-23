module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CechFam
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFlatLift
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechAndTotalDifferentialAdditiveSquareZero
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.LogSectionsDifferentialClosedStatement
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechAndTotalDifferentialAdditiveSquareZeroStatement

section

@[expose] public section

open GlobalTheory GlobalTheory.DI

theorem _root_.GlobalTheory.T.cech_and_total_differential_additive_square_zero : ∀ {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E] (d : E →+ E), (∀ c c' : Finset ι → E, delta (c + c') = delta c + delta c') ∧ (∀ c c' : Finset ι → E, delta (c - c') = delta c - delta c') ∧ (∀ c c' : Finset ι → E, Dtot d (c + c') = Dtot d c + Dtot d c') ∧ (∀ c c' : Finset ι → E, Dtot d (c - c') = Dtot d c - Dtot d c') ∧ (∀ c : Finset ι → E, delta (delta c) = 0) ∧ ((∀ x, d (d x) = 0) → ∀ c : Finset ι → E, Dtot d (Dtot d c) = 0) := by
  first | exact @GlobalTheory.DI.delta_Dtot_props | exact GlobalTheory.DI.delta_Dtot_props | (intros; apply GlobalTheory.DI.delta_Dtot_props <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTotalCochainOfDegreeSuccOfDifferentials

section

@[expose] public section

open GlobalTheory GlobalTheory.DI

namespace GlobalTheory.DI

theorem _root_.GlobalTheory.DI.inTot_delta_Dtot : ∀ {ι : Type} [LinearOrder ι] {E : Type}
    [AddCommGroup E] (d : E →+ E)
    (T : ℕ → Finset ι → AddSubgroup E), (∀ q s t, s.Nonempty → s ⊆ t → T q s ≤ T q t) →
    ∀ m c, _root_.GlobalTheory.DI.InTot T m c → _root_.GlobalTheory.DI.InTot T (m + 1)
        (_root_.GlobalTheory.DI.delta c) ∧
      ((∀ q s x, x ∈ T q s → d x ∈ T (q + 1) s) →
        _root_.GlobalTheory.DI.InTot T (m + 1) (_root_.GlobalTheory.DI.Dtot d c)) := by
  intro ι _ E _ d T hmono m c hc
  unfold _root_.GlobalTheory.DI.InTot at hc
  obtain ⟨h0, hmem, hzero⟩ := hc
  have hδ0 : _root_.GlobalTheory.DI.delta c ∅ = 0 := by
    unfold _root_.GlobalTheory.DI.delta; simp
  have hδmem : ∀ (q : ℕ) (t : Finset ι), q + t.card = m + 1 →
      _root_.GlobalTheory.DI.delta c t ∈ T q t := by
    intro q t hqt
    unfold _root_.GlobalTheory.DI.delta
    refine AddSubgroup.sum_mem _ fun i hi => AddSubgroup.zsmul_mem _ ?_ _
    have hcard : (t.erase i).card = t.card - 1 := Finset.card_erase_of_mem hi
    have hpos : 0 < t.card := Finset.card_pos.mpr ⟨i, hi⟩
    have hq : q + (t.erase i).card = m := by omega
    rcases (t.erase i).eq_empty_or_nonempty with he | hne
    · rw [he, h0]; exact zero_mem _
    · exact hmono q _ _ hne (Finset.erase_subset i t) (hmem q _ hq)
  have hδz : ∀ t : Finset ι, m + 1 < t.card → _root_.GlobalTheory.DI.delta c t = 0 := by
    intro t ht
    unfold _root_.GlobalTheory.DI.delta
    refine Finset.sum_eq_zero fun i hi => ?_
    have hcard : (t.erase i).card = t.card - 1 := Finset.card_erase_of_mem hi
    rw [hzero _ (by omega), smul_zero]
  refine ⟨⟨hδ0, hδmem, hδz⟩, fun hd => ⟨?_, ?_, ?_⟩⟩
  · unfold _root_.GlobalTheory.DI.Dtot; simp [hδ0, h0]
  · intro q t hqt
    unfold _root_.GlobalTheory.DI.Dtot
    refine add_mem (hδmem q t hqt) (AddSubgroup.zsmul_mem _ ?_ _)
    rcases q with _ | q
    · rw [hzero t (by omega), map_zero]; exact zero_mem _
    · exact hd q t _ (hmem q t (by omega))
  · intro t ht
    unfold _root_.GlobalTheory.DI.Dtot
    rw [hδz t ht, hzero t (by omega), map_zero, smul_zero, add_zero]

end GlobalTheory.DI
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTotalCochainOfDegreeSuccOfDifferentialsStatement

section

@[expose] public section

open GlobalTheory GlobalTheory.DI

theorem _root_.GlobalTheory.T.isTotalCochainOfDegree_succ_of_differentials : ∀ {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E] (d : E →+ E) (T : ℕ → Finset ι → AddSubgroup E), (∀ q s t, s.Nonempty → s ⊆ t → T q s ≤ T q t) → ∀ m c, InTot T m c → InTot T (m + 1) (delta c) ∧ ((∀ q s x, x ∈ T q s → d x ∈ T (q + 1) s) → InTot T (m + 1) (Dtot d c)) := by
  first | exact @GlobalTheory.DI.inTot_delta_Dtot | exact GlobalTheory.DI.inTot_delta_Dtot | (intros; apply GlobalTheory.DI.inTot_delta_Dtot <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeltaTopPartEqZero

section

@[expose] public section

set_option autoImplicit false

open GlobalTheory GlobalTheory.DI

namespace GlobalTheory.DI

theorem delta_topPart_eq_zero {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E] (d : E →+ E)
    (c : Finset ι → E) (k : ℕ) (hc : Dtot d c = 0) (hk : ∀ s, k < s.card → c s = 0) :
    delta (fun s => if s.card = k then c s else 0) = 0 := by
  funext t
  by_cases ht : t.card = k + 1
  · have h1 : delta c t = 0 := by
      have h := congrFun hc t
      simpa [Dtot, hk t (by omega)] using h
    rw [Pi.zero_apply, ← h1]
    refine Finset.sum_congr rfl fun i hi => ?_
    have : (t.erase i).card = k := by rw [Finset.card_erase_of_mem hi]; omega
    simp only [this, if_true]
  · refine Finset.sum_eq_zero fun i hi => ?_
    have h0 := Finset.card_erase_add_one hi
    have : (t.erase i).card ≠ k := by omega
    simp only [this, if_false, smul_zero]

theorem hypZero_of_cechZero : ∀ {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E] (d : E →+ E) (T : ℕ → Finset ι → AddSubgroup E), (∀ x, d (d x) = 0) → (∀ q s t, s.Nonempty → s ⊆ t → T q s ≤ T q t) → (∀ q s x, x ∈ T q s → d x ∈ T (q + 1) s) → ∀ n, (∀ q b, q + b = n → CechZero (T q) b) → HypZero d T n := by
  intro ι _ E _ d T hdd hmono hdT n hC
  obtain ⟨-, -, hadd, hsub, -, hDD⟩ := GlobalTheory.T.cech_and_total_differential_additive_square_zero (ι := ι) d
  have key : ∀ k, k ≤ n + 1 → ∀ c, InTot T (n + 1) c → Dtot d c = 0 →
      (∀ s, k < s.card → c s = 0) → ∃ y, InTot T n y ∧ Dtot d y = c := by
    intro k
    induction k with
    | zero =>
      intro _ c hc _ h0
      refine ⟨0, ⟨rfl, fun q s _ => (T q s).zero_mem, fun _ _ => rfl⟩, ?_⟩
      funext s
      have hs : c s = 0 := by
        rcases Nat.eq_zero_or_pos s.card with h | h
        · rw [Finset.card_eq_zero.1 h]; exact hc.1
        · exact h0 s h
      simp [Dtot, delta, hs]
    | succ b ih =>
      intro hb c hc hD h0
      obtain ⟨q, hq⟩ : ∃ q, q + b = n := ⟨n - b, by omega⟩
      have hin : InCech (T q) (b + 1) (fun s => if s.card = b + 1 then c s else 0) := by
        refine ⟨by simp, fun s => ?_, fun s hs => by simp [hs]⟩
        by_cases hs : s.card = b + 1
        · simp only [hs, if_true]
          exact hc.2.1 q s (by omega)
        · simp only [hs, if_false]
          exact (T q s).zero_mem
      obtain ⟨y, hy, hyc⟩ := hC q b hq _ hin (delta_topPart_eq_zero d c (b + 1) hD h0)
      have hyT : InTot T n y := by
        refine ⟨hy.1, fun q' s hs => ?_, fun s hs => hy.2.2 s (by omega)⟩
        by_cases h : s.card = b
        · obtain rfl : q' = q := by omega
          exact hy.2.1 s
        · rw [hy.2.2 s h]; exact (T q' s).zero_mem
      have hDy : InTot T (n + 1) (Dtot d y) := (GlobalTheory.T.isTotalCochainOfDegree_succ_of_differentials d T hmono n y hyT).2 hdT
      have h1 : InTot T (n + 1) (c - Dtot d y) := by
        refine ⟨?_, fun q' s hs => (T q' s).sub_mem (hc.2.1 q' s hs) (hDy.2.1 q' s hs),
          fun s hs => ?_⟩
        · rw [Pi.sub_apply, hc.1, hDy.1, sub_zero]
        · rw [Pi.sub_apply, hc.2.2 s hs, hDy.2.2 s hs, sub_zero]
      have h2 : Dtot d (c - Dtot d y) = 0 := by rw [hsub, hD, hDD hdd, sub_zero]
      have h3 : ∀ s, b < s.card → (c - Dtot d y) s = 0 := by
        intro s hs
        have hys : y s = 0 := hy.2.2 s (by omega)
        by_cases h : s.card = b + 1
        · simp [Dtot, hyc, hys, h]
        · simp [Dtot, hyc, hys, h, h0 s (by omega)]
      obtain ⟨z, hz, hzc⟩ := ih (by omega) _ h1 h2 h3
      refine ⟨z + y, ⟨?_, fun q' s hs => (T q' s).add_mem (hz.2.1 q' s hs) (hyT.2.1 q' s hs),
        fun s hs => ?_⟩, ?_⟩
      · rw [Pi.add_apply, hz.1, hyT.1, add_zero]
      · rw [Pi.add_apply, hz.2.2 s hs, hyT.2.2 s hs, add_zero]
      · rw [hadd, hzc, sub_add_cancel]
  intro c hc hD
  exact key (n + 1) le_rfl c hc hD hc.2.2

end GlobalTheory.DI
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CechVanishingFrobeniusDescent

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.LogDR GlobalTheory.LogPair

set_option autoImplicit false

namespace GlobalTheory.LogDR

theorem descend_vanishing : ∀ (p : ℕ) [Fact p.Prime] (X : Scheme.{0}) [IsIntegral X] [CharP X.functionField p] {C : Type} [Fintype C] (E : C → CartierDiv X) {n : ℕ} {ι : Type} [LinearOrder ι] (𝒜 : SncAtlas E n ι) (G : ℕ → CartierDiv X), Decomp p 𝒜 → (∀ e, ∃ ρ : C → ℕ, (∀ c, ρ c < p) ∧ G (e + 1) = p • G e + ∑ c, ρ c • E c) → ∀ e₀ : ℕ, (∀ a b : ℕ, n < a + b → DI.CechZero (cechFam 𝒜 (G e₀) a) b) → ∀ a b : ℕ, n < a + b → DI.CechZero (cechFam 𝒜 (G 0) a) b := by
  intro p _ X _ _ C _ E n ι _ 𝒜 G hD hG e₀ h0
  have step : ∀ e, (∀ a b : ℕ, n < a + b → DI.CechZero (cechFam 𝒜 (G (e + 1)) a) b) →
      ∀ a b : ℕ, n < a + b → DI.CechZero (cechFam 𝒜 (G e) a) b := by
    intro e he a b hab
    obtain ⟨ρ, hρ, hGe⟩ := hG e
    refine hD (G e) ρ hρ a b ?_
    rw [← hGe]
    refine DI.hypZero_of_cechZero (extD X.functionField) _ (fun x => CechDR.dDR_dDR x) ?_ ?_ (a + b) ?_
    · intro q s t _ hst
      show latSec _ _ ≤ latSec _ _
      have hle : inter 𝒜.U t ≤ inter 𝒜.U s := Finset.inf_mono hst
      intro x hx
      simp only [latSec, AddSubgroup.mem_iInf] at hx ⊢
      exact fun y hy => hx y (hle hy)
    · intro q s x hx
      have := GlobalTheory.T.log_sections_differential_closed p 𝒜 (G e) ρ hρ q (inter 𝒜.U s) x (by rw [← hGe]; exact hx)
      rw [← hGe] at this
      exact this
    · intro q b' hqb
      exact he q b' (by omega)
  induction e₀ with
  | zero => exact h0
  | succ k ih => exact ih (step k h0)

end GlobalTheory.LogDR
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CechVanishingFrobeniusDescentStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.LogDR GlobalTheory.LogPair

theorem _root_.GlobalTheory.T.cech_vanishing_frobenius_descent : ∀ (p : ℕ) [Fact p.Prime] (X : Scheme.{0}) [IsIntegral X] [CharP X.functionField p] {C : Type} [Fintype C] (E : C → CartierDiv X) {n : ℕ} {ι : Type} [LinearOrder ι] (𝒜 : SncAtlas E n ι) (G : ℕ → CartierDiv X), Decomp p 𝒜 → (∀ e, ∃ ρ : C → ℕ, (∀ c, ρ c < p) ∧ G (e + 1) = p • G e + ∑ c, ρ c • E c) → ∀ e₀ : ℕ, (∀ a b : ℕ, n < a + b → DI.CechZero (cechFam 𝒜 (G e₀) a) b) → ∀ a b : ℕ, n < a + b → DI.CechZero (cechFam 𝒜 (G 0) a) b := by
  first | exact @_root_.GlobalTheory.LogDR.descend_vanishing | exact _root_.GlobalTheory.LogDR.descend_vanishing | (intros; apply _root_.GlobalTheory.LogDR.descend_vanishing <;> assumption)
end
end
