module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmpSqLeCardMulSum
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardEqPowAndIndexGe
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetTermBasicFacts
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermExponentsNonnegAndDefectGroupBoundStatement
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermExponentsNonnegAndDefectGroupBound
import Mathlib.Algebra.Order.Star.Int
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelIndexEqCardMap

section

@[expose] public section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.LevelFamilies

theorem relIndex_eq_card_map {O V : Type} [Ring O] [AddCommGroup V] [Module O V]
    (M A : Submodule O V) :
    M.toAddSubgroup.relIndex A.toAddSubgroup = Nat.card (A.map M.mkQ) := by
  have h := AddSubgroup.relIndex_ker A.toAddSubgroup M.mkQ.toAddMonoidHom
  have hk : M.mkQ.toAddMonoidHom.ker = M.toAddSubgroup := by
    ext x
    simp [AddMonoidHom.mem_ker]
  rw [hk] at h
  rw [h]
  rfl

theorem ncard_classes {O V : Type} [Ring O] [AddCommGroup V] [Module O V]
    (M B A : Submodule O V) (hMB : M ≤ B) (hBA : B ≤ A) [Finite (A.map M.mkQ)] :
    Set.ncard {C : Set V | ∃ y ∈ A, y ∉ B ∧ C = {x | x - y ∈ M}} =
      Nat.card (A.map M.mkQ) - Nat.card (B.map M.mkQ) := by
  have hinj : Function.Injective (fun c : V ⧸ M => (M.mkQ ⁻¹' {c} : Set V)) := by
    intro c c' h
    obtain ⟨v, rfl⟩ := M.mkQ_surjective c
    have : v ∈ (M.mkQ ⁻¹' {c'} : Set V) := by
      have h' : (M.mkQ ⁻¹' {M.mkQ v} : Set V) = M.mkQ ⁻¹' {c'} := h
      rw [← h']; simp
    simpa using this
  have hpre : ∀ y : V, (M.mkQ ⁻¹' {M.mkQ y} : Set V) = {x | x - y ∈ M} := by
    intro y
    ext x
    simp [Submodule.Quotient.eq]
  have hmem : ∀ y : V, M.mkQ y ∈ B.map M.mkQ ↔ y ∈ B := by
    intro y
    constructor
    · rintro ⟨b, hb, hby⟩
      have h1 : b - y ∈ M := by simpa [Submodule.Quotient.eq] using hby
      have h2 : y = b - (b - y) := by abel
      rw [h2]
      exact B.sub_mem hb (hMB h1)
    · intro hy
      exact ⟨y, hy, rfl⟩
  have hset : {C : Set V | ∃ y ∈ A, y ∉ B ∧ C = {x | x - y ∈ M}} =
      (fun c : V ⧸ M => (M.mkQ ⁻¹' {c} : Set V)) ''
        ((A.map M.mkQ : Set (V ⧸ M)) \ (B.map M.mkQ : Set (V ⧸ M))) := by
    ext C
    constructor
    · rintro ⟨y, hyA, hyB, rfl⟩
      exact ⟨M.mkQ y, ⟨⟨y, hyA, rfl⟩, fun h => hyB ((hmem y).1 h)⟩, hpre y⟩
    · rintro ⟨c, ⟨⟨y, hyA, rfl⟩, hc⟩, rfl⟩
      exact ⟨y, hyA, fun h => hc ((hmem y).2 h), hpre y⟩
  have hsub : (B.map M.mkQ : Set (V ⧸ M)) ⊆ (A.map M.mkQ : Set (V ⧸ M)) :=
    Submodule.map_mono hBA
  have hfin : (A.map M.mkQ : Set (V ⧸ M)).Finite := Set.toFinite _
  rw [hset, Set.ncard_image_of_injective _ hinj, Set.ncard_diff hsub (hfin.subset hsub)]
  rfl

theorem two_le_resQ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) : 2 ≤ resQ ϖ := by
  have h : Ideal.span {ϖ} = IsLocalRing.maximalIdeal 𝒪[F] := hϖ.maximalIdeal_eq.symm
  have h1 : resQ ϖ = Nat.card (IsLocalRing.ResidueField 𝒪[F]) := by
    unfold resQ
    rw [h]
    rfl
  rw [h1]
  exact Finite.one_lt_card

theorem exists_family : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.TypeBe d Λ → ∃ i J i' : ℕ, 1 ≤ i ∧ (i : ℤ) ≤ S.a ∧ 1 ≤ J ∧ J ≤ r ∧ i' < i ∧ S.InFF (S.q ^ i) J (S.q ^ i - S.q ^ i') d Λ := by
  intro F _ _ _ _ _ E _ _ _ L r k S d Λ hT hB
  obtain ⟨-, -, -, -, -, ⟨i, hia, hbe⟩, -, -, -, hlev0, hlev⟩ := GlobalTheory.T.term_exponents_nonneg_and_defect_group_bound L r k S d Λ hT
  have hMA : S.M d Λ ≤ S.sat Λ := (GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hT).2.2.1
  have hq : 2 ≤ S.q := two_le_resQ S.ϖ S.ϖ_irr
  have hcard : Nat.card ((S.sat Λ).map (S.M d Λ).mkQ) = S.q ^ i := by
    rw [← hbe, ← relIndex_eq_card_map]; rfl
  haveI hfin : Finite ((S.sat Λ).map (S.M d Λ).mkQ) := by
    apply Nat.finite_of_card_ne_zero
    rw [hcard]
    positivity

  let P : ℕ → Prop := fun j => ∃ y ∈ S.sat Λ, S.levC d Λ y = j
  obtain ⟨y0, hy0A, hy0M⟩ : ∃ y ∈ S.sat Λ, y ∉ S.M d Λ := by
    by_contra h
    push_neg at h
    exact hB.1 (le_antisymm hMA h)
  let J := Nat.findGreatest P r
  have hle : ∀ y ∈ S.sat Λ, S.levC d Λ y ≤ J := fun y hy =>
    Nat.le_findGreatest (hB.2.1 y hy) ⟨y, hy, rfl⟩
  have hPJ : P J := Nat.findGreatest_spec (hB.2.1 y0 hy0A) ⟨y0, hy0A, rfl⟩
  have hJr : J ≤ r := Nat.findGreatest_le r
  have hJ1 : 1 ≤ J := by
    have h1 : S.levC d Λ y0 ≠ 0 := fun h => hy0M ((hlev0 y0 hy0A).1 h)
    have := hle y0 hy0A
    omega

  let B : Submodule L.O S.V := S.sat Λ ⊓
    ((S.spanTo S.f (J - 1) ⊔ S.spanTo S.f' (J - 1)).restrictScalars L.O ⊔ S.M d Λ)
  have hBmem : ∀ y ∈ S.sat Λ, y ∈ B ↔ S.levC d Λ y ≤ J - 1 := by
    intro y hy
    rw [hlev y hy]
    constructor
    · rintro ⟨-, h⟩
      obtain ⟨u, hu, m, hm, rfl⟩ := Submodule.mem_sup.1 h
      exact ⟨u, hu, by simpa using hm⟩
    · rintro ⟨u, hu, hm⟩
      exact ⟨hy, Submodule.mem_sup.2 ⟨u, hu, y - u, hm, by abel⟩⟩
  have hMB : S.M d Λ ≤ B := le_inf hMA le_sup_right
  have hBA : B ≤ S.sat Λ := inf_le_left
  have hle' : B.map (S.M d Λ).mkQ ≤ (S.sat Λ).map (S.M d Λ).mkQ := Submodule.map_mono hBA
  haveI hfinB : Finite (B.map (S.M d Λ).mkQ) :=
    Finite.of_injective _ (Submodule.inclusion_injective hle')
  obtain ⟨i', hi'⟩ := (GlobalTheory.FiniteModuleOrder.card_eq_pow_and_index_ge L S.ϖ S.ϖ_irr
    (B.map (S.M d Λ).mkQ)).1
  have hi'q : Nat.card (B.map (S.M d Λ).mkQ) = S.q ^ i' := hi'
  have hn : S.nLev d Λ J = S.q ^ i - S.q ^ i' := by
    rw [← hcard, ← hi'q, ← ncard_classes _ _ _ hMB hBA]
    unfold Frames.nLev
    congr 1
    ext C
    constructor
    · rintro ⟨y, hy, hl, rfl⟩
      refine ⟨y, hy, fun h => ?_, rfl⟩
      have := (hBmem y hy).1 h
      omega
    · rintro ⟨y, hy, hl, rfl⟩
      refine ⟨y, hy, ?_, rfl⟩
      have h1 := hle y hy
      have h2 : ¬ S.levC d Λ y ≤ J - 1 := fun h => hl ((hBmem y hy).2 h)
      omega
  have hlt : S.q ^ i' < S.q ^ i := by
    rw [← hcard, ← hi'q]
    obtain ⟨y, hy, hl⟩ := hPJ
    have hss : (B.map (S.M d Λ).mkQ : Set (S.V ⧸ S.M d Λ)) ⊂
        ((S.sat Λ).map (S.M d Λ).mkQ : Set (S.V ⧸ S.M d Λ)) := by
      refine ⟨hle', fun h => ?_⟩
      obtain ⟨b, hb, hby⟩ := h (⟨y, hy, rfl⟩ : (S.M d Λ).mkQ y ∈ (S.sat Λ).map (S.M d Λ).mkQ)
      have h1 : b - y ∈ S.M d Λ := by simpa [Submodule.Quotient.eq] using hby
      have h2 : y ∈ B := by
        have h3 : y = b - (b - y) := by abel
        rw [h3]
        exact B.sub_mem hb (hMB h1)
      have := (hBmem y hy).1 h2
      omega
    exact Set.ncard_lt_ncard hss (Set.toFinite _)
  have hii : i' < i := (Nat.pow_lt_pow_iff_right (by omega)).1 hlt
  exact ⟨i, J, i', by omega, hia, hJ1, hJr, hii, hB, hbe, hle, hPJ, hn⟩

end GlobalTheory.HL.LevelFamilies
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmpSqLeOfHermitianTermTypesCauchySchwarz

section

@[expose] public section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.TypesCS

theorem count_le (r a : ℕ) (H : ℝ) (ha : 1 ≤ a) (hH : (2 : ℝ) ^ a ≤ H) :
    ((a + a * (r * a) : ℕ) : ℝ) ≤ H ^ (r + 2) := by
  have hnat : a + a * (r * a) ≤ 2 ^ (a * (r + 2)) := by
    have h1 : a < 2 ^ a := Nat.lt_two_pow_self
    have h2 : r * a < 2 ^ (r * a) := Nat.lt_two_pow_self
    calc a + a * (r * a) = a * (1 + r * a) := by ring
      _ ≤ 2 ^ a * 2 ^ (r * a) := Nat.mul_le_mul h1.le (by omega)
      _ = 2 ^ (a + r * a) := (pow_add 2 a (r * a)).symm
      _ ≤ 2 ^ (a * (r + 2)) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  calc ((a + a * (r * a) : ℕ) : ℝ) ≤ ((2 ^ (a * (r + 2)) : ℕ) : ℝ) := by exact_mod_cast hnat
    _ = ((2 : ℝ) ^ a) ^ (r + 2) := by push_cast; rw [pow_mul]
    _ ≤ H ^ (r + 2) := by gcongr

theorem ampSq_le_of_types : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 4 * r + 7 ≤ k → ∀ B : ℝ≥0∞, (∀ β, (S.ampSq fun d Λ => ¬ S.BBzero d Λ ∧ ¬ S.TypeBe d Λ ∧ S.be d Λ = β) ≤ B) → (∀ β J βJ, S.ampSq (S.InFF β J βJ) ≤ B) → (S.ampSq fun d Λ => ¬ S.BBzero d Λ) ≤ ENNReal.ofReal (S.Hp ^ (2 * (r + 2))) * B := by
  intro F _ _ _ _ _ E _ _ _ L r k S hk B hB1 hB2
  have hk1 : 1 ≤ k := by omega
  have hq2 : 2 ≤ S.q := GlobalTheory.HL.LevelFamilies.two_le_resQ S.ϖ S.ϖ_irr
  by_cases hex : ∃ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ
  swap
  ·
    simp only [not_exists] at hex
    have h0 := GlobalTheory.AmpCS.ampSq_le_card_mul_sum L r k S hk1 (∅ : Finset ℕ)
      (fun _ _ _ => False) (fun d Λ => ¬ S.BBzero d Λ)
      (fun d Λ ht => absurd ht (hex d Λ)) (fun d Λ ht => absurd ht (hex d Λ))
    simp only [Finset.card_empty, Nat.cast_zero, zero_mul] at h0
    exact h0.trans zero_le
  obtain ⟨d₀, Λ₀, ht₀⟩ := hex
  obtain ⟨ha0, -, -, hqa, hHp1, -⟩ := GlobalTheory.HL.Defect.exponents_and_defect L r k S d₀ Λ₀ ht₀
  obtain ⟨A, hAa⟩ : ∃ A : ℕ, (A : ℤ) = S.a := ⟨_, Int.toNat_of_nonneg ha0⟩

  let s : Finset (ℕ ⊕ (ℕ × ℕ × ℕ)) :=
    (Finset.Icc 1 A).disjSum
      ((Finset.Icc 1 A ×ˢ Finset.Icc 1 r ×ˢ Finset.range A).filter fun t => t.2.2 < t.1)
  let P : ℕ ⊕ (ℕ × ℕ × ℕ) → S.Datum → Submodule L.O S.V → Prop := fun x =>
    Sum.elim (fun i d Λ => ¬ S.BBzero d Λ ∧ ¬ S.TypeBe d Λ ∧ S.be d Λ = S.q ^ i)
      (fun t => S.InFF (S.q ^ t.1) t.2.1 (S.q ^ t.1 - S.q ^ t.2.2)) x
  have hinj : ∀ m n : ℕ, S.q ^ m = S.q ^ n → m = n := fun m n h =>
    Nat.pow_right_injective hq2 h
  have hcover : ∀ d Λ, S.IsTerm d Λ → ((¬ S.BBzero d Λ) ↔ ∃ x ∈ s, P x d Λ) := by
    intro d Λ ht
    obtain ⟨-, -, -, -, -, ⟨i, hia, hbe⟩, hBB, -⟩ :=
      GlobalTheory.HL.Defect.exponents_and_defect L r k S d Λ ht
    constructor
    · intro hnz
      have hi1 : 1 ≤ i := by
        rcases Nat.eq_zero_or_pos i with h | h
        · exact absurd (hBB.mpr (by rw [hbe, h, pow_zero])) hnz
        · exact h
      by_cases hT : S.TypeBe d Λ
      · obtain ⟨i₁, J, i', h1, h1a, hJ1, hJr, hi', hF⟩ :=
          GlobalTheory.HL.LevelFamilies.exists_family L r k S d Λ ht hT
        refine ⟨Sum.inr (i₁, J, i'), ?_, hF⟩
        simp only [s, Finset.inr_mem_disjSum, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
          Finset.mem_range]
        omega
      · refine ⟨Sum.inl i, ?_, hnz, hT, hbe⟩
        simp only [s, Finset.inl_mem_disjSum, Finset.mem_Icc]
        omega
    · rintro ⟨x, -, hx⟩
      rcases x with i | ⟨i, J, i'⟩
      · exact hx.1
      · exact hx.1.1
  have hdisj : ∀ d Λ, S.IsTerm d Λ → ∀ x ∈ s, ∀ y ∈ s, P x d Λ → P y d Λ → x = y := by
    intro d Λ _ x hx y hy hPx hPy
    rcases x with i | ⟨i, J, i'⟩ <;> rcases y with j | ⟨j, J', j'⟩ <;>
      dsimp only [P, Sum.elim_inl, Sum.elim_inr] at hPx hPy
    · exact congrArg Sum.inl (hinj _ _ (hPx.2.2.symm.trans hPy.2.2))
    · exact absurd hPy.1 hPx.2.1
    · exact absurd hPx.1 hPy.2.1
    · obtain ⟨-, hb, hle, ⟨y₀, hy₀, hlev⟩, hn⟩ := hPx
      obtain ⟨-, hb', hle', ⟨y₁, hy₁, hlev'⟩, hn'⟩ := hPy
      have hij : i = j := hinj _ _ (hb.symm.trans hb')
      subst hij
      have hJJ : J = J' := le_antisymm (hlev ▸ hle' y₀ hy₀) (hlev' ▸ hle y₁ hy₁)
      subst hJJ
      simp only [s, Finset.inr_mem_disjSum, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
        Finset.mem_range] at hx hy
      have hlt1 : S.q ^ i' ≤ S.q ^ i := Nat.pow_le_pow_right (by omega) hx.2.le
      have hlt2 : S.q ^ j' ≤ S.q ^ i := Nat.pow_le_pow_right (by omega) hy.2.le
      have hpow : S.q ^ i' = S.q ^ j' := by
        generalize S.q ^ i' = u at hn hlt1
        generalize S.q ^ j' = v at hn' hlt2
        generalize S.q ^ i = w at hn hn' hlt1 hlt2
        omega
      rw [hinj _ _ hpow]
  have hmain := GlobalTheory.AmpCS.ampSq_le_card_mul_sum L r k S hk1 s P (fun d Λ => ¬ S.BBzero d Λ)
    hcover hdisj
  have hsumB : ∑ x ∈ s, S.ampSq (P x) ≤ s.card * B := by
    have hle : ∀ x ∈ s, S.ampSq (P x) ≤ B := by
      intro x _
      rcases x with i | ⟨i, J, i'⟩
      · exact hB1 _
      · exact hB2 _ _ _
    simpa [nsmul_eq_mul] using Finset.sum_le_card_nsmul s (fun x => S.ampSq (P x)) B hle
  have hcard : s.card ≤ A + A * (r * A) := by
    simp only [s, Finset.card_disjSum, Nat.card_Icc, Nat.add_sub_cancel]
    have h := Finset.card_filter_le (Finset.Icc 1 A ×ˢ Finset.Icc 1 r ×ˢ Finset.range A)
      (fun t => t.2.2 < t.1)
    simp only [Finset.card_product, Nat.card_Icc, Nat.add_sub_cancel, Finset.card_range] at h
    omega
  have hHp0 : 0 ≤ S.Hp := le_trans zero_le_one hHp1
  have hreal : ((s.card : ℕ) : ℝ) ≤ S.Hp ^ (r + 2) := by
    rcases Nat.eq_zero_or_pos A with hA | hA
    · have : s.card = 0 := by rw [hA] at hcard; simpa using hcard
      rw [this, Nat.cast_zero]
      positivity
    · have h2A : (2 : ℝ) ^ A ≤ S.Hp :=
        calc (2 : ℝ) ^ A ≤ (S.q : ℝ) ^ A := by gcongr; exact_mod_cast hq2
          _ = (S.q : ℝ) ^ S.a := by rw [← hAa, zpow_natCast]
          _ ≤ S.Hp := hqa
      calc ((s.card : ℕ) : ℝ) ≤ ((A + A * (r * A) : ℕ) : ℝ) := by exact_mod_cast hcard
        _ ≤ S.Hp ^ (r + 2) := count_le r A S.Hp hA h2A
  have hN : ((s.card : ℝ≥0∞) * s.card) ≤ ENNReal.ofReal (S.Hp ^ (2 * (r + 2))) := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    rw [pow_mul', sq]
    exact mul_le_mul hreal hreal (Nat.cast_nonneg _) (le_trans (Nat.cast_nonneg _) hreal)
  calc (S.ampSq fun d Λ => ¬ S.BBzero d Λ) ≤ s.card * ∑ x ∈ s, S.ampSq (P x) := hmain
    _ ≤ s.card * (s.card * B) := by gcongr
    _ = (s.card * s.card) * B := (mul_assoc _ _ _).symm
    _ ≤ ENNReal.ofReal (S.Hp ^ (2 * (r + 2))) * B := by gcongr

end GlobalTheory.HL.TypesCS
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmpSqLeOfHermitianTermTypesCauchySchwarzStatement

section

@[expose] public section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.ampSq_le_of_hermitianTermTypes_cauchySchwarz : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 4 * r + 7 ≤ k → ∀ B : ℝ≥0∞, (∀ β, (S.ampSq fun d Λ => ¬ S.BBzero d Λ ∧ ¬ S.TypeBe d Λ ∧ S.be d Λ = β) ≤ B) → (∀ β J βJ, S.ampSq (S.InFF β J βJ) ≤ B) → (S.ampSq fun d Λ => ¬ S.BBzero d Λ) ≤ ENNReal.ofReal (S.Hp ^ (2 * (r + 2))) * B := by
  first | exact @GlobalTheory.HL.TypesCS.ampSq_le_of_types | exact GlobalTheory.HL.TypesCS.ampSq_le_of_types | (intros; apply GlobalTheory.HL.TypesCS.ampSq_le_of_types <;> assumption)
end
end
