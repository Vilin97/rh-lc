module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardInnerLatticesWithDefiniteTraceLeNormStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CommonUnipotentStabiliserPreservesTermsAndDatum
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagPairDefiniteThetaLatticeLeFixedIndexBoundStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairOmSumSameDatumLe
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
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalFormTerminalDeterminantStatement
import Mathlib.Algebra.Order.Star.Real
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.TypeStar
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InvVolPos

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairOmSumSameDatumLeStatement

section

@[expose] public section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.hermFramePair_omSum_same_datum_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∀ i b : ℕ, N.omSum (fun Λ' => N.IsTerm g Λ' ∧ N.SameDat g Λ Λ' ∧ N.iI g Λ' = i ∧ N.bI Λ' = b) ≤ ENNReal.ofReal (((i : ℝ) * b) ^ Module.finrank K N.Wt * (i : ℝ) ^ cf K * (N.Db * N.Del * N.NT) ^ (10000 * (r + 1) ^ 3)) := by
  first | exact @GlobalTheory.DegCnt.OmCount.main | exact GlobalTheory.DegCnt.OmCount.main | (intros; apply GlobalTheory.DegCnt.OmCount.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFrameWeightSumSameDatumLe

section

@[expose] public section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegCnt

theorem tsum_ite_le_sum_fibres {α β : Type*} (Q : α → Prop) (R : β → α → Prop) (f : α → ℝ≥0∞) (S : Finset β)
    [∀ a, Decidable (Q a)] [∀ p a, Decidable (R p a)]
    (h : ∀ a, Q a → ∃ p ∈ S, R p a) :
    (∑' a, if Q a then f a else 0) ≤ ∑ p ∈ S, ∑' a, if R p a then f a else 0 := by
  rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  refine ENNReal.tsum_le_tsum fun a => ?_
  split_ifs with hq
  · obtain ⟨p, hp, hr⟩ := h a hq
    refine le_trans ?_ (Finset.single_le_sum (f := fun p => if R p a then f a else 0)
      (fun _ _ => zero_le) hp)
    simp [hr]
  · exact zero_le

theorem cf_nonneg_of_numberField (K : Type) [Field K] [NumberField K] : 0 ≤ cf K := by
  have h : (1 : ℝ) ≤ (Module.finrank ℚ K : ℝ) := by exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)
  have := Real.logb_nonneg (b := 2) (by norm_num) h
  unfold cf
  linarith

theorem index_pair_bound {G D c X : ℝ} (k i b : ℕ) (hG : 0 < G) (hc : 0 ≤ c) (hX : 0 ≤ X)
    (h : G * (i : ℝ) ^ 2 * (b : ℝ) ^ 2 ≤ D) (hi : (i : ℝ) ≤ D) :
    ((i : ℝ) * b) ^ k * (i : ℝ) ^ c * X ≤ (D / G) ^ ((k : ℝ) / 2) * D ^ c * X := by
  have h0 : (0 : ℝ) ≤ (i : ℝ) * b := by positivity
  have h1 : ((i : ℝ) * b) ^ 2 ≤ D / G := by
    rw [le_div_iff₀ hG]; nlinarith
  have h2 : ((i : ℝ) * b) ^ k ≤ (D / G) ^ ((k : ℝ) / 2) := by
    calc ((i : ℝ) * b) ^ k = (((i : ℝ) * b) ^ 2) ^ ((k : ℝ) / 2) := by
          rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul h0, ← Real.rpow_natCast]
          congr 1; push_cast; ring
      _ ≤ _ := Real.rpow_le_rpow (by positivity) h1 (by positivity)
  have h3 : (i : ℝ) ^ c ≤ D ^ c := Real.rpow_le_rpow (by positivity) hi hc
  have h4 : 0 ≤ (D / G) ^ ((k : ℝ) / 2) := le_trans (by positivity) h2
  gcongr

theorem omSum_sameDat_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → N.omSum (fun Λ' => N.IsTerm g Λ' ∧ N.SameDat g Λ Λ') ≤ ENNReal.ofReal ((N.Del / N.gI g Λ) ^ ((Module.finrank K N.Wt : ℝ) / 2) * N.Del ^ (cf K + 2) * (N.Db * N.Del * N.NT) ^ (10000 * (r + 1) ^ 3)) := by
  intro K V _ _ _ _ _ _ _ _ H hK r N g Λ hg hΛ
  obtain ⟨-, hG, hI, -, hGI, -⟩ := GlobalTheory.T.flagPairDefiniteThetaLattice_le_fixed_index_bound K V H hK r N g Λ hg hΛ
  have hG1 : (1 : ℝ) ≤ N.gI g Λ := by exact_mod_cast hG
  have hI1 : (1 : ℝ) ≤ N.iI g Λ := by exact_mod_cast hI
  have hD : 1 ≤ N.Del := le_trans (by nlinarith) hGI
  have hnD : ∀ l, 0 ≤ N.nD l := fun l => by
    unfold NF.nD
    split_ifs
    · positivity
    · exact le_rfl
  have hDb : 0 ≤ N.Db := Finset.prod_nonneg fun l _ => hnD l
  have hNT : 0 ≤ N.NT := by unfold NF.NT; positivity
  have hX : 0 ≤ (N.Db * N.Del * N.NT) ^ (10000 * (r + 1) ^ 3) := by positivity
  set X := (N.Db * N.Del * N.NT) ^ (10000 * (r + 1) ^ 3) with hXdef
  set S : Finset (ℕ × ℕ) := (Finset.Icc 1 ⌊N.Del⌋₊ ×ˢ Finset.Icc 1 ⌊N.Del⌋₊).filter
    (fun p => (N.gI g Λ : ℝ) * (p.1 : ℝ) ^ 2 * (p.2 : ℝ) ^ 2 ≤ N.Del) with hS
  have hcard : (S.card : ℝ) ≤ N.Del ^ 2 := by
    have h1 : S.card ≤ ⌊N.Del⌋₊ * ⌊N.Del⌋₊ := by
      refine (Finset.card_filter_le _ _).trans ?_
      simp
    have h2 : (⌊N.Del⌋₊ : ℝ) ≤ N.Del := Nat.floor_le (by linarith)
    calc (S.card : ℝ) ≤ (⌊N.Del⌋₊ : ℝ) * ⌊N.Del⌋₊ := by exact_mod_cast h1
      _ ≤ N.Del * N.Del := by gcongr
      _ = _ := by ring
  have hcover : ∀ Λ' : Submodule (𝓞 K) V, N.IsTerm g Λ' ∧ N.SameDat g Λ Λ' →
      ∃ p ∈ S, N.IsTerm g Λ' ∧ N.SameDat g Λ Λ' ∧ N.iI g Λ' = p.1 ∧ N.bI Λ' = p.2 := by
    rintro Λ' ⟨h1, h2⟩
    refine ⟨(N.iI g Λ', N.bI Λ'), ?_, h1, h2, rfl, rfl⟩
    obtain ⟨-, -, hI', hb, -⟩ := GlobalTheory.T.flagPairDefiniteThetaLattice_le_fixed_index_bound K V H hK r N g Λ' hg h1
    have hb0 := (GlobalTheory.T.normal_form_terminal_determinant K V H hK r N g Λ' hg h1).1
    have hgg : N.gI g Λ' = N.gI g Λ := by
      unfold NF.gI flagPairDefinitePartLattice latLa
      rw [h2.1, h2.2.2]
    rw [hgg] at hb
    have hi1 : (1 : ℝ) ≤ N.iI g Λ' := by exact_mod_cast hI'
    have hb1 : (1 : ℝ) ≤ N.bI Λ' := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hb0
    have hi2 : (N.iI g Λ' : ℝ) ≤ (N.iI g Λ' : ℝ) ^ 2 := by nlinarith only [hi1]
    have hb2 : (N.bI Λ' : ℝ) ≤ (N.bI Λ' : ℝ) ^ 2 := by nlinarith only [hb1]
    rw [hS, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
    refine ⟨⟨⟨hI', Nat.le_floor ?_⟩, Nat.one_le_iff_ne_zero.2 hb0, Nat.le_floor ?_⟩, hb⟩
    · refine le_trans ?_ hb
      calc (N.iI g Λ' : ℝ) = 1 * (N.iI g Λ' : ℝ) * 1 := by ring
        _ ≤ _ := by gcongr; linarith
    · refine le_trans ?_ hb
      calc (N.bI Λ' : ℝ) = 1 * 1 * (N.bI Λ' : ℝ) := by ring
        _ ≤ _ := by gcongr; linarith
  have hc := cf_nonneg_of_numberField K
  have hY : 0 ≤ (N.Del / N.gI g Λ) ^ ((Module.finrank K N.Wt : ℝ) / 2) * N.Del ^ cf K * X := by
    have : 0 ≤ N.Del := by linarith
    positivity
  calc N.omSum (fun Λ' => N.IsTerm g Λ' ∧ N.SameDat g Λ Λ')
      ≤ ∑ p ∈ S, N.omSum (fun Λ' => N.IsTerm g Λ' ∧ N.SameDat g Λ Λ' ∧ N.iI g Λ' = p.1 ∧ N.bI Λ' = p.2) := by
        unfold NF.omSum
        exact @tsum_ite_le_sum_fibres _ _ _ _ _ S (fun _ => Classical.propDecidable _)
          (fun _ _ => Classical.propDecidable _) fun o ho => hcover _ ho
    _ ≤ ∑ _p ∈ S, ENNReal.ofReal
          ((N.Del / N.gI g Λ) ^ ((Module.finrank K N.Wt : ℝ) / 2) * N.Del ^ cf K * X) := by
        refine Finset.sum_le_sum fun p hp => ?_
        refine (GlobalTheory.T.hermFramePair_omSum_same_datum_le K V H hK r N g Λ hg hΛ p.1 p.2).trans (ENNReal.ofReal_le_ofReal ?_)
        rw [hS, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
        refine index_pair_bound _ _ _ (by linarith) hc hX hp.2 ?_
        exact le_trans (by exact_mod_cast hp.1.1.2) (Nat.floor_le (by linarith : 0 ≤ N.Del))
    _ = ENNReal.ofReal (S.card *
          ((N.Del / N.gI g Λ) ^ ((Module.finrank K N.Wt : ℝ) / 2) * N.Del ^ cf K * X)) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ((mul_le_mul_of_nonneg_right hcard hY).trans (le_of_eq ?_))
        rw [Real.rpow_add (by linarith), Real.rpow_two]
        ring

end GlobalTheory.DegCnt
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFrameWeightSumSameDatumLeStatement

section

@[expose] public section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.hermFrame_weightSum_sameDatum_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → N.omSum (fun Λ' => N.IsTerm g Λ' ∧ N.SameDat g Λ Λ') ≤ ENNReal.ofReal ((N.Del / N.gI g Λ) ^ ((Module.finrank K N.Wt : ℝ) / 2) * N.Del ^ (cf K + 2) * (N.Db * N.Del * N.NT) ^ (10000 * (r + 1) ^ 3)) := by
  first | exact @GlobalTheory.DegCnt.omSum_sameDat_le | exact GlobalTheory.DegCnt.omSum_sameDat_le | (intros; apply GlobalTheory.DegCnt.omSum_sameDat_le <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumWeightsInequivalentHermFrameTermsLe

section

@[expose] public section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegAsm.FixedForm

theorem sum_le_orbit {G α ι : Type} [Group G] [MulAction G α] (Q : α → Prop) (w : α → ℝ≥0∞)
    (t : Finset ι) (x : ι → α) (hQ : ∀ i ∈ t, ∀ ρ : G, Q (ρ • x i) ∧ w (ρ • x i) = w (x i))
    (hd : ∀ i ∈ t, ∀ i' ∈ t, (∃ ρ : G, ρ • x i = x i') → i = i') :
    ∑ i ∈ t, w (x i) ≤ ∑' o : MulAction.orbitRel.Quotient G α, if Q o.out then w o.out else 0 := by
  let q : ι → MulAction.orbitRel.Quotient G α := fun i => Quotient.mk _ (x i)
  have hinj : ∀ i ∈ t, ∀ i' ∈ t, q i = q i' → i = i' := by
    intro i hi i' hi' h
    have h1 : (MulAction.orbitRel G α) (x i') (x i) := Quotient.exact h.symm
    rw [MulAction.orbitRel_apply] at h1
    exact hd i hi i' hi' h1
  have h1 : ∑ i ∈ t, w (x i) = ∑ o ∈ t.image q, if Q o.out then w o.out else 0 := by
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun i hi => ?_
    have h2 : (MulAction.orbitRel G α) (q i).out (x i) := Quotient.exact (Quotient.out_eq (q i))
    rw [MulAction.orbitRel_apply] at h2
    obtain ⟨ρ, hρ⟩ := h2
    have hρ' : ρ • x i = (q i).out := hρ
    rw [← hρ', if_pos (hQ i hi ρ).1, (hQ i hi ρ).2]
  rw [h1]
  exact ENNReal.sum_le_tsum _

theorem nD_nonneg {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ} (N : NF H r) (l : ℕ) :
    0 ≤ N.nD l := by
  unfold NF.nD
  split_ifs
  · positivity
  · exact le_rfl

theorem main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ), ∀ (N : NF H r) (g : ℕ) (Λ₀ : Submodule (𝓞 K) V) (ι : Type) (s : Finset ι) (Λ : ι → Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ₀ → (∀ i ∈ s, N.IsTerm g (Λ i) ∧ latL N.F N.F' (Λ i) = latL N.F N.F' Λ₀ ∧ flagPairDefinitePartLattice N.F' N.F (Λ i) = flagPairDefinitePartLattice N.F' N.F Λ₀ ∧ iotaGraph N.F N.F' (Λ i) (g : 𝓞 K) = iotaGraph N.F N.F' Λ₀ (g : 𝓞 K)) → (∀ i ∈ s, ∀ i' ∈ s, (∃ ρ ∈ N.R, ρ • Λ i = Λ i') → i = i') → ∑ i ∈ s, N.om (Λ i) ≤ N.NT ^ 2 * ((N.Del / N.gI g Λ₀) ^ ((Module.finrank K N.Wt : ℝ) / 2) * N.Del ^ (cf K + 2) * (N.Db * N.Del * N.NT) ^ (10000 * (r + 1) ^ 3)) := by
  intro K V _ _ _ _ _ _ _ _ H hK r N g Λ₀ ι s Λ hg h0 hs hd
  set B : ℝ := (N.Del / N.gI g Λ₀) ^ ((Module.finrank K N.Wt : ℝ) / 2) * N.Del ^ (cf K + 2) * (N.Db * N.Del * N.NT) ^ (10000 * (r + 1) ^ 3) with hB
  have hDel : 0 ≤ N.Del := nD_nonneg N _
  have hDb : 0 ≤ N.Db := Finset.prod_nonneg fun l _ => nD_nonneg N l
  have hNT : 0 ≤ N.NT := by unfold NF.NT; positivity
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hom := (GlobalTheory.DegAsm.WeightInf.main K V H hK r).1 N g
  let f : ι → Submodule (𝓞 K) V := fun i => latL N.F' N.F (Λ i)
  have hcard : ((s.image f).card : ℝ) ≤ N.NT ^ 2 := by
    have h1 := GlobalTheory.T.card_innerLattices_with_definite_trace_le_norm K V H hK r N g Λ₀ hg h0
    have h2 : ((s.image f : Finset _) : Set (Submodule (𝓞 K) V)) ⊆ {L' : Submodule (𝓞 K) V | ∃ Λ', N.IsTerm g Λ' ∧ L' = latL N.F' N.F Λ' ∧ flagPairDefinitePartLattice N.F' N.F Λ' = flagPairDefinitePartLattice N.F' N.F Λ₀} := by
      intro L hL
      rw [Finset.mem_coe, Finset.mem_image] at hL
      obtain ⟨i, hi, rfl⟩ := hL
      exact ⟨Λ i, (hs i hi).1, rfl, (hs i hi).2.2.1⟩
    have h3 := (ENat.toENNReal_le.2 (Set.encard_le_encard h2)).trans h1
    rw [Set.encard_coe_eq_coe_finsetCard, ENat.toENNReal_coe, ← ENNReal.ofReal_natCast,
      ENNReal.ofReal_le_ofReal_iff (by positivity)] at h3
    exact h3
  have hfib : ∀ L ∈ s.image f, ∑ i ∈ s with f i = L, N.om (Λ i) ≤ B := by
    intro L hL
    obtain ⟨i₀, hi₀, rfl⟩ := Finset.mem_image.1 hL
    have h1 := GlobalTheory.T.hermFrame_weightSum_sameDatum_le K V H hK r N g (Λ i₀) hg (hs i₀ hi₀).1
    have hgI : N.gI g (Λ i₀) = N.gI g Λ₀ := by
      unfold NF.gI latLa flagPairDefinitePartLattice
      rw [(hs i₀ hi₀).2.1, (hs i₀ hi₀).2.2.2]
    rw [hgI, ← hB] at h1
    have h2 := sum_le_orbit (G := N.R) (fun Λ' => N.IsTerm g Λ' ∧ N.SameDat g (Λ i₀) Λ')
      (fun Λ' => ENNReal.ofReal (N.om Λ')) (s.filter fun i => f i = f i₀) Λ
      (by
        intro i hi ρ
        obtain ⟨hi, hfi⟩ := Finset.mem_filter.1 hi
        obtain ⟨a1, ⟨a2, a3, a4⟩, -⟩ := GlobalTheory.DegCnt.StabInv.main K V H hK r N g (Λ i) hg (hs i hi).1 ρ.1 ρ.2
        refine ⟨⟨a1, a2.trans ((hs i hi).2.1.trans (hs i₀ hi₀).2.1.symm), a3.trans hfi,
          a4.trans ((hs i hi).2.2.2.trans (hs i₀ hi₀).2.2.2.symm)⟩, ?_⟩
        exact congrArg ENNReal.ofReal ((hom (Λ i) hg (hs i hi).1).2 ρ.1 ρ.2))
      (by
        rintro i hi i' hi' ⟨ρ, hρ⟩
        exact hd i (Finset.mem_filter.1 hi).1 i' (Finset.mem_filter.1 hi').1 ⟨ρ.1, ρ.2, hρ⟩)
    have h3 : ∑ i ∈ s with f i = f i₀, ENNReal.ofReal (N.om (Λ i)) ≤ ENNReal.ofReal B := by
      refine le_trans ?_ h1
      unfold NF.omSum
      convert h2
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i hi =>
      (hom (Λ i) hg (hs i (Finset.mem_filter.1 hi).1).1).1.le), ENNReal.ofReal_le_ofReal_iff hB0] at h3
    exact h3
  calc ∑ i ∈ s, N.om (Λ i) = ∑ L ∈ s.image f, ∑ i ∈ s with f i = L, N.om (Λ i) :=
        (Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem f hi) _).symm
    _ ≤ (s.image f).card • B := Finset.sum_le_card_nsmul _ _ _ hfib
    _ = ((s.image f).card : ℝ) * B := nsmul_eq_mul _ _
    _ ≤ N.NT ^ 2 * B := mul_le_mul_of_nonneg_right hcard hB0

end GlobalTheory.DegAsm.FixedForm
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumWeightsInequivalentHermFrameTermsLeStatement

section

@[expose] public section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.sum_weights_inequivalent_hermFrameTerms_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ), ∀ (N : NF H r) (g : ℕ) (Λ₀ : Submodule (𝓞 K) V) (ι : Type) (s : Finset ι) (Λ : ι → Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ₀ → (∀ i ∈ s, N.IsTerm g (Λ i) ∧ latL N.F N.F' (Λ i) = latL N.F N.F' Λ₀ ∧ flagPairDefinitePartLattice N.F' N.F (Λ i) = flagPairDefinitePartLattice N.F' N.F Λ₀ ∧ iotaGraph N.F N.F' (Λ i) (g : 𝓞 K) = iotaGraph N.F N.F' Λ₀ (g : 𝓞 K)) → (∀ i ∈ s, ∀ i' ∈ s, (∃ ρ ∈ N.R, ρ • Λ i = Λ i') → i = i') → ∑ i ∈ s, N.om (Λ i) ≤ N.NT ^ 2 * ((N.Del / N.gI g Λ₀) ^ ((Module.finrank K N.Wt : ℝ) / 2) * N.Del ^ (cf K + 2) * (N.Db * N.Del * N.NT) ^ (10000 * (r + 1) ^ 3)) := by
  first | exact @GlobalTheory.DegAsm.FixedForm.main | exact GlobalTheory.DegAsm.FixedForm.main | (intros; apply GlobalTheory.DegAsm.FixedForm.main <;> assumption)
end
end
