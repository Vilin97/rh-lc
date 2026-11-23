module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermLat
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsEqZpowMulUnit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
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
public import Mathlib.RingTheory.OrderOfVanishing.Basic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardQuotEqPow

section

@[expose] public section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.UnramCard

theorem card_quot_mul {R : Type*} [CommRing R] {a : R} (ha : a ∈ nonZeroDivisors R) (b : R) :
    Nat.card (R ⧸ Ideal.span {a * b}) =
      Nat.card (R ⧸ Ideal.span {a}) * Nat.card (R ⧸ Ideal.span {b}) := by
  have h : Ideal.span {a * b} = a • Ideal.span {b} := by
    rw [← Ideal.span_singleton_mul_span_singleton, ← Submodule.ideal_span_singleton_smul,
      smul_eq_mul]
  rw [h]
  have hi := Ideal.mulQuot_injective (Ideal.span {b}) ha
  have hs := Ideal.quotOfMul_surjective (a := a) (Ideal.span {b})
  have he := Ideal.exact_mulQuot_quotOfMul (a := a) (Ideal.span {b})
  rw [Submodule.card_eq_card_quotient_mul_card (LinearMap.ker (Ideal.quotOfMul a (Ideal.span {b}))),
    Nat.card_congr (LinearMap.quotKerEquivOfSurjective _ hs).toEquiv, he.linearMap_ker_eq,
    ← Nat.card_congr (LinearEquiv.ofInjective _ hi).toEquiv, mul_comm]

theorem card_quot_map {R : Type*} [CommRing R] (c : R ≃+* R) (a : R) :
    Nat.card (R ⧸ Ideal.span {c a}) = Nat.card (R ⧸ Ideal.span {a}) := by
  refine (Nat.card_congr (Ideal.quotientEquiv (Ideal.span {a}) (Ideal.span {c a}) c ?_).toEquiv).symm
  rw [Ideal.map_span]
  simp

theorem card_quot_eq_pow : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ δ : L.O, IsUnit (δ : E) → 0 ≤ vE L ϖ ((δ : E) * L.cj δ) ∧ Nat.card (L.O ⧸ Ideal.span {δ}) = resQ ϖ ^ (vE L ϖ ((δ : E) * L.cj δ)).toNat := by
  intro F _ _ _ _ _ E _ _ _ L ϖ hϖ δ hδ
  obtain ⟨-, h2, -, -, h5, h6, -, -⟩ := GlobalTheory.UnramOrder.order_facts L ϖ hϖ
  obtain ⟨-, -, v3, v4⟩ := GlobalTheory.UnramVal.vE_valuation L ϖ hϖ
  obtain ⟨hcm, -, n, hn⟩ := h2 δ δ.2
  have hinj := GlobalTheory.UnramOrder.algebraMap_inj L
  have hE : Nontrivial E := hinj.nontrivial
  have hn0 : (n : F) ≠ 0 := by
    intro h
    rw [h, map_zero] at hn
    exact (hδ.mul (hδ.map L.cj)).ne_zero hn
  rw [hn]
  have hv : 0 ≤ vE L ϖ (algebraMap F E (n : F)) := (v3 _ hn0).2 n.2
  refine ⟨hv, ?_⟩
  obtain ⟨u, hu⟩ := v4 _ hn0
  obtain ⟨j, hj⟩ := Int.eq_ofNat_of_zero_le hv
  rw [hj, zpow_natCast] at hu
  rw [hj, Int.toNat_natCast]
  let c : L.O ≃+* L.O :=
    { toFun := fun x => ⟨L.cj x, GlobalTheory.UnramOrder.cj_mem L x.2⟩
      invFun := fun x => ⟨L.cj x, GlobalTheory.UnramOrder.cj_mem L x.2⟩
      left_inv := fun x => Subtype.ext (L.cj_cj x)
      right_inv := fun x => Subtype.ext (L.cj_cj x)
      map_mul' := fun x y => Subtype.ext (map_mul L.cj (x : E) y)
      map_add' := fun x y => Subtype.ext (map_add L.cj (x : E) y) }
  have hnz : δ ∈ nonZeroDivisors L.O := by
    rw [mem_nonZeroDivisors_iff_right]
    intro x hx
    have hx' : (x : E) * δ = 0 := by exact_mod_cast congrArg Subtype.val hx
    exact Subtype.ext (hδ.mul_left_eq_zero.1 hx')
  have hmul := card_quot_mul hnz (c δ)
  rw [card_quot_map] at hmul
  let ι : 𝒪[F] →+* L.O :=
    ((algebraMap F E).comp (𝒪[F]).subtype).codRestrict L.O (fun x => (h5 _).2 x.2)
  have hset : {y : L.O | (y : E) = algebraMap F E ((ϖ : F) ^ j)} = {ι (ϖ ^ j)} := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, Subtype.ext_iff]
    rfl
  have hprod : δ * c δ = ι (ϖ ^ j) * ι u := by
    apply Subtype.ext
    change (δ : E) * L.cj δ = algebraMap F E ((ϖ : F) ^ j) * algebraMap F E ((u : 𝒪[F]) : F)
    rw [hn, ← map_mul, ← hu]
  have h7 := h6 j
  rw [hset] at h7
  rw [hprod, Ideal.span_singleton_mul_right_unit (u.isUnit.map ι), h7, two_mul, pow_add] at hmul
  exact (Nat.mul_self_inj.1 hmul).symm

end GlobalTheory.UnramCard
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.EncardUniCosetsLe

section

@[expose] public section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.UniCount

section
variable {E : Type} [CommRing E] {N : ℕ}

theorem isUni_mul {s t : Matrix (Fin N) (Fin N) E} (hs : IsUni s) (ht : IsUni t) :
    IsUni (s * t) := by
  refine ⟨fun i j h => ?_, fun i => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rcases lt_or_ge l i with h1 | h1
    · rw [hs.1 i l h1, zero_mul]
    · rw [ht.1 l j (lt_of_lt_of_le h h1), mul_zero]
  · rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [hs.2, ht.2, one_mul]
    · intro l _ hl
      rcases lt_or_gt_of_ne hl with h1 | h1
      · rw [hs.1 i l h1, zero_mul]
      · rw [ht.1 l i h1, mul_zero]
    · simp

def rowM (k : Fin N) (c : Fin N → E) : Matrix (Fin N) (Fin N) E :=
  1 + Matrix.of fun a b => if a = k then c b else 0

theorem mul_rowM (w : Matrix (Fin N) (Fin N) E) (k : Fin N) (c : Fin N → E) (i j : Fin N) :
    (w * rowM k c) i j = w i j + w i k * c j := by
  rw [rowM, Matrix.mul_add, Matrix.mul_one, Matrix.add_apply, Matrix.mul_apply]
  simp

theorem isUni_rowM (k : Fin N) (c : Fin N → E) (hc : ∀ j, j ≤ k → c j = 0) :
    IsUni (rowM k c) := by
  refine ⟨fun i j h => ?_, fun i => ?_⟩
  · simp only [rowM, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply_ne h.ne']
    split_ifs with h1
    · rw [hc j (h1 ▸ h.le), add_zero]
    · simp
  · simp only [rowM, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply_eq]
    split_ifs with h1
    · rw [hc i h1.le, add_zero]
    · simp
end

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] {N : ℕ}

theorem isIntM_mul (L : LocE F E) {s t : Matrix (Fin N) (Fin N) E} (hs : IsIntM L s)
    (ht : IsIntM L t) : IsIntM L (s * t) := fun i j => by
  rw [Matrix.mul_apply]
  exact sum_mem fun l _ => mul_mem (hs i l) (ht l j)

theorem isIntM_rowM (L : LocE F E) (k : Fin N) (c : Fin N → E) (hc : ∀ j, c j ∈ L.O) :
    IsIntM L (rowM k c) := fun i j => by
  simp only [rowM, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply]
  refine add_mem ?_ ?_
  · split_ifs
    exacts [one_mem _, zero_mem _]
  · split_ifs
    exacts [hc j, zero_mem _]

def cos (L : LocE F E) (u : Matrix (Fin N) (Fin N) E) : Set (Matrix (Fin N) (Fin N) E) :=
  {v | ∃ A, IsUni A ∧ IsIntM L A ∧ v = u * A}

theorem cos_mul_subset (L : LocE F E) (u B : Matrix (Fin N) (Fin N) E) (h1 : IsUni B)
    (h2 : IsIntM L B) : cos L (u * B) ⊆ cos L u := by
  rintro v ⟨A, hA, hA', rfl⟩
  exact ⟨B * A, isUni_mul h1 hA, isIntM_mul L h2 hA', Matrix.mul_assoc _ _ _⟩

theorem cos_rowM (L : LocE F E) (u : Matrix (Fin N) (Fin N) E) (k : Fin N) (c : Fin N → E)
    (hc : ∀ j, j ≤ k → c j = 0) (hc' : ∀ j, c j ∈ L.O) : cos L (u * rowM k c) = cos L u := by
  refine (cos_mul_subset L u _ (isUni_rowM k c hc) (isIntM_rowM L k c hc')).antisymm ?_
  have : u = u * rowM k c * rowM k (-c) := by
    ext i j
    rw [mul_rowM, mul_rowM, mul_rowM, hc k le_rfl]
    simp
  conv_lhs => rw [this]
  exact cos_mul_subset L _ _ (isUni_rowM k _ fun j hj => by simp [hc j hj])
    (isIntM_rowM L k _ fun j => neg_mem (hc' j))

theorem exists_rep (L : LocE F E) (δ : E) (R : Set E)
    (hR : ∀ x : E, δ * x ∈ L.O → ∃ r ∈ R, r - x ∈ L.O)
    (u : Matrix (Fin N) (Fin N) E) (hu : IsUni u) (hδ : ∀ i j, δ * u i j ∈ L.O) (m : ℕ) :
    ∃ w : Matrix (Fin N) (Fin N) E, IsUni w ∧ (∀ i j, δ * w i j ∈ L.O) ∧ cos L w = cos L u ∧
      ∀ i j : Fin N, N ≤ i.val + m → i < j → w i j ∈ R := by
  induction m with
  | zero => exact ⟨u, hu, hδ, rfl, fun i j h _ => absurd i.2 (by omega)⟩
  | succ m ih =>
    obtain ⟨w, hw, hwδ, hc, hg⟩ := ih
    by_cases hm : N ≤ m
    · exact ⟨w, hw, hwδ, hc, fun i j _ h => hg i j (by omega) h⟩
    let k : Fin N := ⟨N - 1 - m, by omega⟩
    choose r hrR hr using fun j => hR (w k j) (hwδ k j)
    let c : Fin N → E := fun j => if k < j then r j - w k j else 0
    have hc0 : ∀ j, j ≤ k → c j = 0 := fun j hj => if_neg (not_lt.2 hj)
    have hc1 : ∀ j, c j ∈ L.O := fun j => by
      simp only [c]
      split_ifs
      exacts [hr j, zero_mem _]
    refine ⟨w * rowM k c, isUni_mul hw (isUni_rowM k c hc0), fun i j => ?_,
      (cos_rowM L w k c hc0 hc1).trans hc, fun i j h hij => ?_⟩
    · rw [mul_rowM, mul_add, ← mul_assoc]
      exact add_mem (hwδ i j) (mul_mem (hwδ i k) (hc1 j))
    · rw [mul_rowM]
      by_cases hik : i = k
      · subst hik
        rw [hw.2, one_mul]
        simp only [c, if_pos hij]
        simpa using hrR j
      · have h2 : i.val ≠ N - 1 - m := fun h => hik (Fin.ext h)
        have h3 : k < i := by
          show N - 1 - m < i.val
          omega
        rw [hw.1 i k h3, zero_mul, add_zero]
        exact hg i j (by omega) hij

theorem encard_le (L : LocE F E) (δ : L.O) (hδ : IsUnit (δ : E))
    [Finite (L.O ⧸ Ideal.span {δ})] (N : ℕ) :
    {C : Set (Matrix (Fin N) (Fin N) E) | ∃ u, IsUni u ∧ (∀ i j, (δ : E) * u i j ∈ L.O) ∧
      C = cos L u}.encard ≤
      ((Nat.card (L.O ⧸ Ideal.span {δ}) ^ (N * (N - 1) / 2) : ℕ) : ℕ∞) := by
  obtain ⟨d, hd⟩ := hδ
  let ρ : (L.O ⧸ Ideal.span {δ}) → E := fun q => (d⁻¹ : Eˣ) * (Quotient.out q : L.O)
  have hR : ∀ x : E, (δ : E) * x ∈ L.O → ∃ r ∈ Set.range ρ, r - x ∈ L.O := by
    intro x hx
    let y : L.O := ⟨_, hx⟩
    refine ⟨_, ⟨Ideal.Quotient.mk _ y, rfl⟩, ?_⟩
    have h1 : Quotient.out (Ideal.Quotient.mk (Ideal.span {δ}) y) - y ∈ Ideal.span {δ} :=
      Ideal.Quotient.eq.1 (Ideal.Quotient.mk_out _)
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 h1
    have h2 : ((Quotient.out (Ideal.Quotient.mk (Ideal.span {δ}) y) : L.O) : E)
        = (a : E) * d + d * x := by
      have := congrArg (Subtype.val) ha
      push_cast at this
      rw [hd, this]
      simp [y]
    have h3 : ρ (Ideal.Quotient.mk _ y) - x = a := by
      simp only [ρ]
      rw [h2]
      have := d.inv_mul
      linear_combination ((a : E) + x) * this
    rw [h3]
    exact a.2
  let P := {p : Fin N × Fin N // p.1 < p.2}
  let mk : (P → L.O ⧸ Ideal.span {δ}) → Matrix (Fin N) (Fin N) E := fun f =>
    Matrix.of fun i j => if h : i < j then ρ (f ⟨(i, j), h⟩) else if i = j then 1 else 0
  have hsub : {C : Set (Matrix (Fin N) (Fin N) E) | ∃ u, IsUni u ∧
      (∀ i j, (δ : E) * u i j ∈ L.O) ∧ C = cos L u} ⊆ (fun f => cos L (mk f)) '' Set.univ := by
    rintro C ⟨u, hu, huδ, rfl⟩
    obtain ⟨w, hw, -, hc, hg⟩ := exists_rep L δ _ hR u hu huδ N
    choose f hf using fun p : P => hg p.1.1 p.1.2 (by omega) p.2
    refine ⟨f, trivial, ?_⟩
    rw [← hc]
    show cos L (mk f) = _
    congr 1
    ext i j
    simp only [mk, Matrix.of_apply]
    split_ifs with h1 h2
    · exact hf ⟨(i, j), h1⟩
    · rw [h2, hw.2]
    · exact (hw.1 i j (lt_of_le_of_ne (not_lt.1 h1) (Ne.symm h2))).symm
  refine (Set.encard_le_encard hsub).trans ((Set.encard_image_le _ _).trans (le_of_eq ?_))
  have hP : Nat.card P = N * (N - 1) / 2 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Fintype.card_product_filter_lt,
      Fintype.card_fin, Nat.choose_two_right]
  rw [Set.encard_univ, ENat.card_eq_coe_natCard, Nat.card_fun, hP]

theorem resQ_ne_zero [IsNonarchimedeanLocalField F] (ϖ : 𝒪[F]) (h : Irreducible ϖ) :
    resQ ϖ ≠ 0 := by
  have : Finite (𝒪[F] ⧸ Ideal.span {ϖ}) := by
    rw [← h.maximalIdeal_eq]
    exact inferInstanceAs (Finite 𝓀[F])
  exact Nat.card_pos.ne'

end GlobalTheory.HL.UniCount

theorem GlobalTheory.HL.encard_uniCosets_le : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ (δ : E), δ ∈ L.O → IsUnit δ → ∀ N : ℕ, ({C : Set (Matrix (Fin N) (Fin N) E) | ∃ u, IsUni u ∧ (∀ i j, δ * u i j ∈ L.O) ∧ C = {v | ∃ A, IsUni A ∧ IsIntM L A ∧ v = u * A}}.encard : ℝ≥0∞) ≤ (resQ ϖ : ℝ≥0∞) ^ ((vE L ϖ (δ * L.cj δ)).toNat * (N * (N - 1) / 2)) := by
  intro F _ _ _ _ _ E _ _ _ L ϖ hϖ δ hδ hu N
  have hc := (GlobalTheory.UnramCard.card_quot_eq_pow L ϖ hϖ ⟨δ, hδ⟩ hu).2
  have hfin : Finite (L.O ⧸ Ideal.span {(⟨δ, hδ⟩ : L.O)}) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; exact pow_ne_zero _ (UniCount.resQ_ne_zero ϖ hϖ))
  have h := UniCount.encard_le L ⟨δ, hδ⟩ hu N
  rw [hc, ← pow_mul] at h
  have h2 := ENat.toENNReal_le.2 h
  rw [ENat.toENNReal_coe, Nat.cast_pow] at h2
  exact h2
end
end
