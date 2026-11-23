module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CharacterIdealPrincipalEigenStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FundamentalIdealFrobeniusProductStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderIdealsEqTopStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StableHopfOrderSubgroupQuotient
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StableHopfOrderSubgroupTranslationStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TeichmullerCharacterOrderGeneratesStatement
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.WeilBound.CoreStatements.HodgeTatePoints.PowCongr

section

@[expose] public section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace PositivityTheory.HtPt.Rd

theorem powadd : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] (v : Valuation C NNReal) (x y z : C), v x ≤ 1 → v y ≤ 1 → v (z - x - y) ≤ v (p : C) → v (z ^ p - x ^ p - y ^ p) ≤ v (p : C) := by
  intro p hp C _ v x y z hx hy h
  have hp1 : v (p : C) ≤ 1 := by
    exact natCast_mem v.integer p
  have hz : v z ≤ 1 := by
    have e : z = (z - x - y) + x + y := by ring
    rw [e]
    exact v.map_add_le (v.map_add_le (h.trans hp1) hx) hy
  let X : v.integer := ⟨x, hx⟩
  let Y : v.integer := ⟨y, hy⟩
  let Z : v.integer := ⟨z, hz⟩
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp.out X Y
  obtain ⟨s, hs⟩ := sub_dvd_pow_sub_pow Z (X + Y) p
  have hr' := congrArg v.integer.subtype hr
  have hs' := congrArg v.integer.subtype hs
  simp only [map_add (f := _), map_mul, map_pow, map_sub, map_natCast, Subring.subtype_apply, X, Y, Z]
    at hr' hs'
  have e : z ^ p - x ^ p - y ^ p = (z - x - y) * (s : C) + (p : C) * (x * y * (r : C)) := by
    linear_combination hr' + hs'
  rw [e]
  refine v.map_add_le ?_ ?_
  · rw [map_mul]
    exact (mul_le_of_le_one_right' (α := NNReal) s.2).trans h
  · rw [map_mul]
    refine mul_le_of_le_one_right' ?_
    rw [map_mul, map_mul]
    exact mul_le_one' (mul_le_one' hx hy) r.2

section

variable {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]

theorem mem_pInt [CharZero C] (hv : v.Integers R) {p : ℕ} (hp : p ≠ 0) (x : C) :
    x ∈ pInt (C := C) R p ↔ v x ≤ v (p : C) := by
  have h0 : (p : C) ≠ 0 := Nat.cast_ne_zero.2 hp
  rw [pInt, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨r, rfl⟩
    rw [Algebra.smul_def, map_mul]
    exact mul_le_of_le_one_left' (hv.map_le_one r)
  · intro h
    have h1 : v (x / p) ≤ 1 := by
      rw [map_div₀]
      exact div_le_one_of_le₀ h zero_le
    obtain ⟨r, hr⟩ := hv.exists_of_le_one h1
    exact ⟨r, by rw [Algebra.smul_def, hr, div_mul_cancel₀ _ h0]⟩

theorem val_le_one (hv : v.Integers R) {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
    (AA : HopfOrder (C := C) R N) {g : N → C} (hg : g ∈ AA.carrier) (x : N) : v (g x) ≤ 1 := by
  obtain ⟨r, hr⟩ := AA.le_int hg x
  rw [← hr]
  exact hv.map_le_one r

theorem pow_mem {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
    (AA : HopfOrder (C := C) R N) {g : N → C} (hg : g ∈ AA.carrier) (k : ℕ) :
    g ^ k ∈ AA.carrier := by
  induction k with
  | zero => rw [pow_zero]; exact AA.one_mem
  | succ k ih => rw [pow_succ]; exact AA.mul_mem _ _ ih hg

theorem pow_congr (p : ℕ) [hp : Fact p.Prime] {x z : C} (hx : v x ≤ 1)
    (h : v (z - x) ≤ v (p : C)) : v (z ^ p - x ^ p) ≤ v (p : C) := by
  have := powadd p C v x 0 z hx (by simp) (by simpa using h)
  simpa [zero_pow hp.out.ne_zero] using this

end

theorem a_pow : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable (F := F) AA.carrier → ∀ (K : Submodule F N) (t : N) (τ : MulChar F R) (c : R), c ∈ idealD p AA.carrier K t τ → c ^ p ∈ idealD p AA.carrier K t (τ ^ p) := by
  intro p hp C _ _ _ v R _ _ hv hp1 F _ _ _ _ f hF N _ _ _ _ AA hst K t τ c hc
  obtain ⟨g, ⟨hg, hadd⟩, h1, h2, h3⟩ := hc
  have hp0 := hp.out.ne_zero
  have hb := val_le_one hv AA hg
  refine ⟨g ^ p, ⟨pow_mem AA hg p, fun x y => ?_⟩, fun a x => ?_, fun k hk => ?_, ?_⟩
  · rw [mem_pInt hv hp0]
    exact powadd p C v _ _ _ (hb x) (hb y) ((mem_pInt hv hp0 _).1 (hadd x y))
  · rw [mem_pInt hv hp0, MulChar.pow_apply' _ hp0, map_pow, Pi.pow_apply, Pi.pow_apply, ← mul_pow]
    refine pow_congr p ?_ ((mem_pInt hv hp0 _).1 (h1 a x))
    rw [map_mul]
    exact mul_le_one' (hv.map_le_one _) (hb x)
  · rw [mem_pInt hv hp0]
    have := pow_congr (v := v) p (x := 0) (z := g k) (by simp)
      (by simpa using (mem_pInt hv hp0 _).1 (h2 k hk))
    simpa [zero_pow hp0] using this
  · rw [mem_pInt hv hp0, map_pow, Pi.pow_apply]
    exact pow_congr p (hv.map_le_one _) ((mem_pInt hv hp0 _).1 h3)

end PositivityTheory.HtPt.Rd
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StableHopfOrderSubgroupLength

section

@[expose] public section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem idealD_pow_mem : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (K : Submodule F N) (t : N) (τ : MulChar F R) (c : R), c ∈ idealD p AA.carrier K t τ → c ^ p ∈ idealD p AA.carrier K t (τ ^ p) :=
  @PositivityTheory.HtPt.Rd.a_pow

end GlobalTheory.CompanionTheory.Ar.GR
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StableHopfOrderSubgroupLengthStatement

section

@[expose] public section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

theorem _root_.GlobalTheory.T.stable_hopf_order_subgroup_length : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (K : Submodule F N) (t : N) (τ : MulChar F R) (c : R), c ∈ idealD p AA.carrier K t τ → c ^ p ∈ idealD p AA.carrier K t (τ ^ p) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GR.idealD_pow_mem | exact GlobalTheory.CompanionTheory.Ar.GR.idealD_pow_mem | (intros; apply GlobalTheory.CompanionTheory.Ar.GR.idealD_pow_mem <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StableHopfOrderSubgroupQuotientStatement

section

@[expose] public section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

theorem _root_.GlobalTheory.T.stable_hopf_order_subgroup_quotient : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (K : Submodule F N) (t : N), t ∉ K → GenAF p AA.carrier K.toAddSubgroup → ∀ τ : MulChar F R, IsFund p τ → ∀ c' c : R, idealX AA.carrier K t τ = Ideal.span {c'} → idealX AA.carrier K t (τ ^ p) = Ideal.span {c} → v (algebraMap R C c') ^ p < v (algebraMap R C c) → c ∈ idealD p AA.carrier K t (τ ^ p) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.stable_hopf_order_subgroup_quotient | exact GlobalTheory.CompanionTheory.Relay.stable_hopf_order_subgroup_quotient | (intros; apply GlobalTheory.CompanionTheory.Relay.stable_hopf_order_subgroup_quotient <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StableHopfOrderSubgroupGeneration

section

@[expose] public section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem idealX_le_idealD : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (K : Submodule F N) (t : N), t ∉ K → GenAF p AA.carrier K.toAddSubgroup → ∀ τ : MulChar F R, IsFund p τ → idealX AA.carrier K t τ ≤ idealD p AA.carrier K t τ := by
  intro p _ C _ _ _ v R _ _ hv hp F _ _ _ _ f hq N _ _ _ _ AA hst K t ht hgen τ hτ
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  obtain ⟨⟨S, hS, hSst⟩, -⟩ := GlobalTheory.T.stable_hopf_order_subgroup_translation p C v R hv hp F f hq N AA hst K t ht
  obtain ⟨hord, -, hfund, hfunds, -⟩ := GlobalTheory.T.teichmuller_character_order_generates p C v R hv hp F f hq τ hτ
  have hf0 : f ≠ 0 := by
    rintro rfl
    have := Fintype.one_lt_card (α := F)
    rw [hq, pow_zero] at this
    exact lt_irrefl _ this
  have hq1 : 1 < p ^ f := Nat.one_lt_pow hf0 hp1
  have hper1 : τ ^ p ^ f = τ := by
    have : p ^ f = orderOf τ + 1 := by omega
    rw [this, pow_succ, pow_orderOf_eq_one, one_mul]
  have hper : ∀ m, τ ^ p ^ (f * m) = τ := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, hper1]
  have hprin : ∀ χ : MulChar F R, ∃ c : R, c ≠ 0 ∧ xIdeal S.carrier χ = Ideal.span {c} :=
    fun χ => (GlobalTheory.T.character_ideal_principal_eigen p C v R hv hp F f hq S hSst χ).1
  choose c0 hc0 hc0' using hprin
  let c : ℕ → R := fun n => c0 (τ ^ p ^ n)
  have hcX : ∀ n, idealX AA.carrier K t (τ ^ p ^ n) = Ideal.span {c n} := by
    intro n
    rw [idealX, ← hS]
    exact hc0' _
  have hom := GlobalTheory.T.fundamental_ideal_frobenius_product p C v R hv hp F f hq S hSst τ hτ c (fun n => hc0' _)
  have hcper : ∀ m, c (f * m) = c 0 := by
    intro m
    simp only [c, hper m, pow_zero, pow_one]
  let y : ℕ → NNReal := fun n => v (algebraMap R C (c n))
  have hy1 : ∀ n, y n ≤ 1 := fun n => hv.map_le_one _
  have hy0 : ∀ n, y n ≠ 0 := by
    intro n
    refine (Valuation.ne_zero_iff _).2 fun h => hc0 (τ ^ p ^ n) (hv.hom_inj ?_)
    simpa [c] using h
  have hle : ∀ n, y n ^ p ≤ y (n + 1) := by
    intro n
    obtain ⟨δ, hδ⟩ := (hom n).2.1
    have : y n ^ p = v (algebraMap R C δ) * y (n + 1) := by
      simp only [y]
      rw [← map_pow, ← map_pow, hδ, map_mul, map_mul]
    rw [this]
    exact mul_le_of_le_one_left' (hv.map_le_one _)
  have hpowp : ∀ n, (τ ^ p ^ n) ^ p = τ ^ p ^ (n + 1) := by
    intro n
    rw [← pow_mul, ← pow_succ]
  have hlt : ∀ n, y n ^ p < y (n + 1) → c (n + 1) ∈ idealD p AA.carrier K t (τ ^ p ^ (n + 1)) := by
    intro n h
    have := GlobalTheory.T.stable_hopf_order_subgroup_quotient p C v R hv hp F f hq N AA hst K t ht hgen (τ ^ p ^ n) (hfund n)
      (c n) (c (n + 1)) (hcX n) (by rw [hpowp]; exact hcX (n + 1)) h
    rwa [hpowp] at this
  have heq : ∀ n, y n ^ p = y (n + 1) → c n ∈ idealD p AA.carrier K t (τ ^ p ^ n) →
      c (n + 1) ∈ idealD p AA.carrier K t (τ ^ p ^ (n + 1)) := by
    intro n h hg
    have h1 := GlobalTheory.T.stable_hopf_order_subgroup_length p C v R hv hp F f hq N AA hst K t (τ ^ p ^ n) (c n) hg
    rw [hpowp] at h1
    obtain ⟨δ, hδ⟩ := (hom n).2.1
    have hv1 : v (algebraMap R C δ) = 1 := by
      have h2 : y n ^ p = v (algebraMap R C δ) * y (n + 1) := by
        simp only [y]
        rw [← map_pow, ← map_pow, hδ, map_mul, map_mul]
      rw [h] at h2
      exact (mul_right_cancel₀ (hy0 (n + 1)) (by rw [one_mul]; exact h2)).symm
    have hu : IsUnit δ := by
      refine hv.isUnit_of_one ?_ hv1
      refine IsUnit.mk0 _ fun h0 => ?_
      rw [h0, map_zero] at hv1
      exact zero_ne_one hv1
    rw [hδ] at h1
    exact (Ideal.unit_mul_mem_iff_mem _ hu).1 h1
  have hex : ∃ n, c n ∈ idealD p AA.carrier K t (τ ^ p ^ n) := by
    by_cases h : ∃ n, y n ^ p < y (n + 1)
    · obtain ⟨n, hn⟩ := h
      exact ⟨n + 1, hlt n hn⟩
    · have hall : ∀ n, y n ^ p = y (n + 1) := fun n =>
        le_antisymm (hle n) (not_lt.1 fun h' => h ⟨n, h'⟩)
      have hyn : ∀ n, y n = y 0 ^ p ^ n := by
        intro n
        induction n with
        | zero => simp
        | succ n ih => rw [← hall n, ih, ← pow_mul, pow_succ]
      have hyf : y 0 ^ p ^ f = y 0 := by
        rw [← hyn f]
        have := hcper 1
        rw [mul_one] at this
        simp only [y, this]
      have hy01 : y 0 = 1 := by
        refine le_antisymm (hy1 0) (not_lt.1 fun h' => ?_)
        have := pow_lt_self_of_lt_one₀ (pos_iff_ne_zero.2 (hy0 0)) h' hq1
        exact absurd hyf this.ne
      have hu : IsUnit (c 0) := by
        refine hv.isUnit_of_one ?_ hy01
        refine IsUnit.mk0 _ fun h0 => ?_
        have : y 0 = 0 := by simp only [y, h0, map_zero]
        exact hy0 0 this
      have hX : idealX AA.carrier K t τ = ⊤ := by
        have := hcX 0
        rw [pow_zero, pow_one] at this
        rw [this]
        exact Ideal.span_singleton_eq_top.2 hu
      obtain ⟨τ', hτ', hD⟩ := GlobalTheory.T.hopf_order_ideals_eq_top p C v R hv hp F f hq N AA hst K t ht hgen τ hX
      obtain ⟨n, -, rfl⟩ := hfunds τ' hτ'
      exact ⟨n, by rw [hD]; trivial⟩
  obtain ⟨n, hn⟩ := hex
  have hlater : ∀ k, c (n + k) ∈ idealD p AA.carrier K t (τ ^ p ^ (n + k)) := by
    intro k
    induction k with
    | zero => exact hn
    | succ k ih =>
      rcases (hle (n + k)).lt_or_eq with h | h
      · exact hlt _ h
      · exact heq _ h ih
  have hnf : n ≤ f * n := Nat.le_mul_of_pos_left n (Nat.pos_of_ne_zero hf0)
  have hg := hlater (f * n - n)
  rw [Nat.add_sub_cancel' hnf, hper n] at hg
  have hX := hcX (f * n)
  rw [hper n] at hX
  rw [hX]
  exact (Ideal.span_singleton_le_iff_mem _).2 hg

end GlobalTheory.CompanionTheory.Ar.GR
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StableHopfOrderSubgroupGenerationStatement

section

@[expose] public section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

theorem _root_.GlobalTheory.T.stable_hopf_order_subgroup_generation : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (K : Submodule F N) (t : N), t ∉ K → GenAF p AA.carrier K.toAddSubgroup → ∀ τ : MulChar F R, IsFund p τ → idealX AA.carrier K t τ ≤ idealD p AA.carrier K t τ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GR.idealX_le_idealD | exact GlobalTheory.CompanionTheory.Ar.GR.idealX_le_idealD | (intros; apply GlobalTheory.CompanionTheory.Ar.GR.idealX_le_idealD <;> assumption)
end
end
