module

public import Formalism.WachLatticeTwists.CoprimeLiftBounds.StatBridgeChiOne
public import Mathlib.Data.Nat.PadicValNat
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Formalism.CharacterColumnKernels.IdempotentNormalForms.LengthKerOfDetEqZero
public import Formalism.WachLatticeTwists.CoprimeLiftBounds.CoprimeLiftProofs.SelmerInjColumnPlace
public import Mathlib.NumberTheory.Multiplicity
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Formalism.WachLatticeTwists.CoprimeLiftBounds.WachTwistTheoremDeltaClause

section

@[expose] public section

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.BR

open Formalism.NG

def StatPowSubOneO : Prop :=
  ∀ (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ℓ : ℕ), ℓ.Prime →
    ¬ IsUnit (ℓ : O) → ∀ s₀ : ℕ, 1 ≤ s₀ → (ℓ = 2 → 2 ≤ s₀) →
    ∀ (x : O) (y : Oˣ), x - 1 = (ℓ : O) ^ s₀ * (y : O) → ∀ n : ℕ, n ≠ 0 →
      IsDiscreteValuationRing.addVal O (x ^ n - 1) =
        IsDiscreteValuationRing.addVal O (ℓ : O) * ((s₀ + padicValNat ℓ n : ℕ) : ℕ∞)

def WachTwistTheoremDeltaClause : Prop :=
  ∀ (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ℓ : ℕ), ℓ.Prime →
    ¬ IsUnit (ℓ : O) → ∀ s₀ : ℕ, 1 ≤ s₀ → (ℓ = 2 → 2 ≤ s₀) →
    ∀ x y u₁ : Oˣ, (x : O) - 1 = (ℓ : O) ^ s₀ * (y : O) → ∀ t : ℕ,
    let δO : O := ∏ i ∈ Finset.Ioo 0 t, ((u₁ : O) - (u₁ : O) * ((x⁻¹ ^ i : Oˣ) : O))
    let eO : ℕ∞ := Module.length O (O ⧸ Ideal.span {(ℓ : O)})
    IsDiscreteValuationRing.addVal O δO =
      eO * ((∑ i ∈ Finset.Ioo 0 t, (s₀ + padicValNat ℓ i) : ℕ) : ℕ∞) ∧
    IsDiscreteValuationRing.addVal O δO ≤ eO * ((t * s₀ + padicValNat ℓ t.factorial : ℕ) : ℕ∞)

def WachTwistTheoremDeltaSum : Prop :=
  ∀ (ℓ : ℕ), ℓ.Prime → ∀ s₀ t : ℕ,
    ∑ i ∈ Finset.Ioo 0 (t + 1), (s₀ + padicValNat ℓ i) = t * s₀ + padicValNat ℓ t.factorial

section Defs
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {A T' G : Type*} [Ring A] [Algebra O A] [CommRing T'] [Algebra T' A] [Group G]

def InRhoTensor (M : Type*) [AddCommGroup M] [Module A M] [Module O M] [SMulCommClass A O M]
    (r : G →* A) (χ : G →* T'ˣ) (E e₁ : A) (δ : T') {ι : Type*} [Fintype ι] [DecidableEq ι]
    (colIdx : ι → ℕ) (D : ℕ → Subgroup G) (j e' : ℕ → ℕ) (Kc : ∀ l, Fin (j (colIdx l)) → G → A)
    (k0 : ι → G → A) (ℓ : ℕ) (what₂ : Finset ℕ) (s : ℕ∞)
    {L : Type*} [AddCommGroup L] [Module A L] [Module O L] [SMulCommClass A O L]
    (tens : L →ₗ[O] KO O →ₗ[O] M) (v₁ : L)
    (κ : ∀ l, Fin (j (colIdx l)) → G → L)
    {V : Type*} [AddCommGroup V] [Module A V] [Module O V] [Module (FractionRing O) V]
    (iL : L →ₗ[O] V) (qV : V →ₗ[O] M)
    (Ff : ∀ l, Submodule O (H1z (resRep (uRep O (M := L) r χ) (D (colIdx l)))))
    (κz : ∀ l, Fin (j (colIdx l)) → coZ1s (resRep (uRep O (M := L) r χ) (D (colIdx l))))
    (HcG : Submodule O (H1z (uRep O (M := M) r χ)))
    (Hc F : ∀ w, Submodule O (H1z (resRep (uRep O (M := M) r χ) (D w))))
    {Vo : Type*} (Io : Vo → Subgroup G) (ε : G →* Oˣ)
    {T₁ T₂ : Type*} [AddCommGroup T₁] [Module O T₁] [AddCommGroup T₂] [Module O T₂]
    (ρ₁ : Representation O G T₁) (ρ₂ : Representation O G T₂) (inc : T₁ →ₗ[O] A)
    (π : T₁ →ₗ[O] T₂) (γ : T₂ →ₗ[O] M →ₗ[O] KO O) (lam : M →ₗ[O] KO O)
    {Cs : ℕ → Type*} [∀ w, AddCommGroup (Cs w)] [∀ w, Module O (Cs w)]
    (cls : ∀ w, (D w → T₂) → Cs w) (pr : ∀ w, Hc w →ₗ[O] Cs w →ₗ[O] KO O)
    (Fs Im : ∀ w, Submodule O (Cs w)) : Prop :=
  (∀ (a : A) v x, tens (a • v) x = a • tens v x) ∧
  (∀ m : M, e₁ • m = m → ∃ x, m = tens v₁ x) ∧
  (∀ l a, ∀ g ∈ D (colIdx l), Kc l a g • v₁ = ((ℓ : O) ^ e' (colIdx l)) • κ l a g) ∧
  (∀ l (z : coZ1s (resRep (uRep O (M := M) r χ) (D (colIdx l)))) (x : Fin (j (colIdx l)) → KO O),
    (∀ g : D (colIdx l), (z : D (colIdx l) → M) g = ∑ a, tens (κ l a g) (x a)) →
    Submodule.mkQ _ z ∈ F (colIdx l)) ∧
  ((∀ (a : A) v, iL (a • v) = a • iL v) ∧ (∀ (a : A) v, qV (a • v) = a • qV v) ∧
    (∀ v (x : FractionRing O), tens v (Submodule.Quotient.mk x) = qV (x • iL v)) ∧
    Function.Injective iL ∧ Function.Surjective qV ∧ LinearMap.ker qV = LinearMap.range iL ∧
    (∀ v : V, ∃ c : O, c ≠ 0 ∧ c • v ∈ LinearMap.range iL) ∧
    ∀ l, (∀ a (g : D (colIdx l)), (κz l a : D (colIdx l) → L) g = κ l a g) ∧
      (∀ (c : O) z, c ≠ 0 → c • z ∈ Ff l → z ∈ Ff l) ∧
      (∀ a, Submodule.mkQ _ (κz l a) ∈ Ff l) ∧
      (∀ z ∈ Ff l, ∃ (b : Fin (j (colIdx l)) → O) (c : O), c ≠ 0 ∧
        c • (z - ∑ a, b a • (Submodule.mkQ _ (κz l a) :
          H1z (resRep (uRep O (M := L) r χ) (D (colIdx l))))) = 0) ∧
      (∀ (b : Fin (j (colIdx l)) → O) (c : O), c ≠ 0 →
        c • ∑ a, b a • (Submodule.mkQ _ (κz l a) :
          H1z (resRep (uRep O (M := L) r χ) (D (colIdx l)))) = 0 → b = 0)) ∧
  (∀ φ, Submodule.mkQ _ (colPsi (O := O) (M := M) r χ E e₁ δ (fun l => D (colIdx l))
    (fun l => j (colIdx l)) Kc k0 φ) ∈ HcG) ∧
  (∀ w ∈ what₂, HcG ≤ (Hc w).comap (resH1 (uRep O (M := M) r χ) (D w))) ∧
  (∀ v, ∀ g ∈ Io v, r g = 1 ∧ χ g = 1) ∧
  (∀ g b, inc (ρ₁ g b) = ((ε g : Oˣ) : O) • (((χ g : T'ˣ) : T') • (inc b * r g⁻¹))) ∧
  IsEquivMap ρ₁ ρ₂ π ∧ (∀ b m, γ (π b) m = lam (inc b • m)) ∧
  (∀ w ∈ what₂, InRowRho M r χ E (D w) ε ρ₁ inc π γ (Hc w) (F w) (cls w) (pr w) (Fs w) (Im w)) ∧
  Module.length O ↥((HcG ⊓ ⨅ v, unrH1 (uRep O (M := M) r χ) (Io v)) ⊓
    ⨅ w ∈ what₂ ∪ univ.image colIdx, (F w).comap (resH1 (uRep O (M := M) r χ) (D w))) ≤ s

end Defs

def SelmerInjConditions : Prop :=
  ∀ (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (A T' G : Type*) [Ring A] [Algebra O A] [CommRing T'] [Algebra T' A] [Group G]
    (M : Type*) [AddCommGroup M] [Module A M] [Module O M] [SMulCommClass A O M]
    (r : G →* A) (χ : G →* T'ˣ) (E e₁ : A) (δ : T') (ι : Type*) [Fintype ι]
    [DecidableEq ι] (colIdx : ι → ℕ) (D : ℕ → Subgroup G) (j e' : ℕ → ℕ)
    (Kc : ∀ l, Fin (j (colIdx l)) → G → A) (k0 : ι → G → A) (ℓ : ℕ) (what₂ : Finset ℕ) (s : ℕ∞)
    (L : Type*) [AddCommGroup L] [Module A L] [Module O L] [SMulCommClass A O L]
    (tens : L →ₗ[O] KO O →ₗ[O] M) (v₁ : L)
    (κ : ∀ l, Fin (j (colIdx l)) → G → L)
    (V : Type*) [AddCommGroup V] [Module A V] [Module O V] [Module (FractionRing O) V]
    [IsScalarTower O (FractionRing O) V] [SMulCommClass A (FractionRing O) V]
    (iL : L →ₗ[O] V) (qV : V →ₗ[O] M)
    (Ff : ∀ l, Submodule O (H1z (resRep (uRep O (M := L) r χ) (D (colIdx l)))))
    (κz : ∀ l, Fin (j (colIdx l)) → coZ1s (resRep (uRep O (M := L) r χ) (D (colIdx l))))
    (HcG : Submodule O (H1z (uRep O (M := M) r χ)))
    (Hc F : ∀ w, Submodule O (H1z (resRep (uRep O (M := M) r χ) (D w))))
    (Vo : Type*) (Io : Vo → Subgroup G) (ε : G →* Oˣ)
    (T₁ T₂ : Type*) [AddCommGroup T₁] [Module O T₁] [AddCommGroup T₂] [Module O T₂]
    (ρ₁ : Representation O G T₁) (ρ₂ : Representation O G T₂) (inc : T₁ →ₗ[O] A)
    (π : T₁ →ₗ[O] T₂) (γ : T₂ →ₗ[O] M →ₗ[O] KO O) (lam : M →ₗ[O] KO O)
    (Cs : ℕ → Type*) [∀ w, AddCommGroup (Cs w)] [∀ w, Module O (Cs w)]
    (cls : ∀ w, (D w → T₂) → Cs w) (pr : ∀ w, Hc w →ₗ[O] Cs w →ₗ[O] KO O)
    (Fs Im : ∀ w, Submodule O (Cs w)),
    InRhoTensor M r χ E e₁ δ colIdx D j e' Kc k0 ℓ what₂ s tens v₁ κ iL qV Ff κz HcG Hc F Io ε ρ₁ ρ₂ inc
      π γ lam cls pr Fs Im →
    InRho M r χ E e₁ δ colIdx D j e' Kc k0 ℓ what₂ s tens v₁ κ HcG Hc F Io ε ρ₁ ρ₂ inc π γ lam
      cls pr Fs Im

end Formalism.RepresentationBoundsCohomology.BR
end
end
end

-- Source module: Formalism.WachLatticeTwists.CoprimeLiftBounds.CoprimeLiftProofs.TheoremNFiveDeltaClause

section

@[expose] public section

open Finset

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.BR

open Formalism.NG IsDiscreteValuationRing

namespace DeltaValuation

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

lemma unit_add {w a : O} (hw : IsUnit w) (ha : ¬ IsUnit a) : IsUnit (w + a) := by
  by_contra h
  have h1 : w + a ∈ nonunits O := h
  have h2 : -a ∈ nonunits O := by
    intro hh
    exact ha (by simpa using hh.neg)
  have h3 := IsLocalRing.nonunits_add h1 h2
  rw [add_neg_cancel_right] at h3
  exact h3 hw

lemma nonunit_mul {a : O} (ha : ¬ IsUnit a) (b : O) : ¬ IsUnit (a * b) :=
  fun h => ha (isUnit_of_mul_isUnit_left h)

lemma unit_of_coprime {l m : ℕ} (hl : ¬ IsUnit (l : O)) (h : Nat.Coprime m l) : IsUnit (m : O) := by
  have h1 : IsCoprime (m : ℤ) (l : ℤ) := Nat.isCoprime_iff_coprime.mpr h
  obtain ⟨a, b, hab⟩ := h1
  have h2 : (a : O) * (m : O) + (b : O) * (l : O) = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → O) hab
  by_contra hm
  have h3 : (a : O) * (m : O) + (b : O) * (l : O) ∈ nonunits O :=
    IsLocalRing.nonunits_add (by rw [mul_comm]; exact nonunit_mul hm _)
      (by rw [mul_comm]; exact nonunit_mul hl _)
  rw [h2] at h3
  exact h3 isUnit_one

lemma geom_unit {l m : ℕ} (hl : ¬ IsUnit (l : O)) (h : Nat.Coprime m l) {x : O}
    (hx : ¬ IsUnit (x - 1)) : IsUnit (∑ i ∈ range m, x ^ i) := by
  have h1 : x - 1 ∣ (∑ i ∈ range m, x ^ i) - m := by
    have : (∑ i ∈ range m, x ^ i) - m = ∑ i ∈ range m, (x ^ i - 1) := by
      rw [Finset.sum_sub_distrib]; simp
    rw [this]
    exact Finset.dvd_sum fun i _ => by simpa using sub_dvd_pow_sub_pow x 1 i
  obtain ⟨c, hc⟩ := h1
  have : ∑ i ∈ range m, x ^ i = (m : O) + (x - 1) * c := by rw [← hc]; ring
  rw [this]
  exact unit_add (unit_of_coprime hl h) (nonunit_mul hx c)

lemma step {l : ℕ} (hp : l.Prime) (hl : ¬ IsUnit (l : O)) (x : O) (s : ℕ) (hs : 1 ≤ s)
    (hs2 : l = 2 → 2 ≤ s) (h : ∃ y : Oˣ, x - 1 = (l : O) ^ s * y) :
    ∃ y : Oˣ, x ^ l - 1 = (l : O) ^ (s + 1) * y := by
  obtain ⟨y, hy⟩ := h
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  have hx : x = 1 + (l : O) * ((l : O) ^ s' * y) := by
    have : x = 1 + (x - 1) := by ring
    rw [this, hy]; ring
  have hsum : ∃ w : Oˣ, ∑ i ∈ range l, x ^ i = (l : O) * w := by
    by_cases h2 : l = 2
    · subst h2
      obtain ⟨s'', rfl⟩ : ∃ s'', s' = s'' + 1 := ⟨s' - 1, by have := hs2 rfl; omega⟩
      have hu : IsUnit (1 + ((2 : ℕ) : O) * (((2 : ℕ) : O) ^ s'' * y)) :=
        unit_add isUnit_one (nonunit_mul hl _)
      refine ⟨hu.unit, ?_⟩
      rw [IsUnit.unit_spec, Finset.sum_range_succ, Finset.sum_range_one, hx]
      push_cast
      ring
    · have hodd : Odd l := hp.odd_of_ne_two h2
      obtain ⟨c, hc⟩ := odd_sq_dvd_geom_sum₂_sub (R := O) (a := 1) (b := (l : O) ^ s' * y) hodd
      have hu : IsUnit (1 + (l : O) * c) := unit_add isUnit_one (nonunit_mul hl _)
      refine ⟨hu.unit, ?_⟩
      rw [IsUnit.unit_spec]
      simp only [one_pow, mul_one] at hc
      rw [← hx] at hc
      have : ∑ i ∈ range l, x ^ i = (l : O) + (l : O) ^ 2 * c := by rw [← hc]; ring
      rw [this]; ring
  obtain ⟨w, hw⟩ := hsum
  refine ⟨y * w, ?_⟩
  rw [← mul_geom_sum, hy, hw]
  push_cast
  ring

lemma iter {l : ℕ} (hp : l.Prime) (hl : ¬ IsUnit (l : O)) (x : O) (s : ℕ) (hs : 1 ≤ s)
    (hs2 : l = 2 → 2 ≤ s) (h : ∃ y : Oˣ, x - 1 = (l : O) ^ s * y) (k : ℕ) :
    ∃ y : Oˣ, x ^ (l ^ k) - 1 = (l : O) ^ (s + k) * y := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    have := step hp hl (x ^ (l ^ k)) (s + k) (by omega) (fun h2 => by have := hs2 h2; omega) ih
    rwa [← pow_mul, ← pow_succ, add_assoc] at this

lemma pow_sub_one {l : ℕ} (hp : l.Prime) (hl : ¬ IsUnit (l : O)) (x : O) (s : ℕ) (hs : 1 ≤ s)
    (hs2 : l = 2 → 2 ≤ s) (h : ∃ y : Oˣ, x - 1 = (l : O) ^ s * y) (n : ℕ) (hn : n ≠ 0) :
    ∃ y : Oˣ, x ^ n - 1 = (l : O) ^ (s + padicValNat l n) * y := by
  have : Fact l.Prime := ⟨hp⟩
  obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn l hp.ne_one
  have hm0 : m ≠ 0 := fun h0 => hm (by rw [h0]; exact dvd_zero _)
  have hv : padicValNat l (l ^ k * m) = k := by
    rw [Nat.padicValNat_def, Nat.multiplicity_mul (pow_ne_zero _ hp.ne_zero) hm0,
      Nat.multiplicity_prime_pow, multiplicity_eq_zero_of_not_dvd hm, add_zero]
  obtain ⟨y, hy⟩ := iter hp hl x s hs hs2 h k
  have hnu : ¬ IsUnit (x ^ (l ^ k) - 1) := by
    rw [hy, show s + k = (s + k - 1) + 1 by omega, pow_succ', mul_assoc]
    exact nonunit_mul hl _
  have hg := geom_unit hl ((Nat.Prime.coprime_iff_not_dvd hp).mpr hm).symm hnu
  refine ⟨y * hg.unit, ?_⟩
  rw [hv, pow_mul, ← mul_geom_sum, hy]
  push_cast
  rw [IsUnit.unit_spec]
  ring

end DeltaValuation

theorem powSubOneO : StatPowSubOneO := by
  intro O _ _ _ ℓ hℓ hℓu s₀ hs hs2 x y hx n hn
  obtain ⟨w, hw⟩ := DeltaValuation.pow_sub_one hℓ hℓu x s₀ hs hs2 ⟨y, hx⟩ n hn
  rw [hw, addVal_mul, addVal_pow, addVal_eq_zero_of_unit, add_zero, nsmul_eq_mul, mul_comm]

theorem theorem_n_five_delta_sum : WachTwistTheoremDeltaSum := by
  intro ℓ hℓ s₀ t
  have : Fact ℓ.Prime := ⟨hℓ⟩
  induction t with
  | zero =>
    rw [show Finset.Ioo 0 (0 + 1) = ∅ from by
      ext i; simp only [Finset.mem_Ioo, Finset.notMem_empty, iff_false]; omega]
    simp [Nat.padicValNat_def]
  | succ t ih =>
    have h : Finset.Ioo 0 (t + 1 + 1) = insert (t + 1) (Finset.Ioo 0 (t + 1)) := by
      ext i; simp only [Finset.mem_Ioo, Finset.mem_insert]; omega
    rw [h, Finset.sum_insert (by simp), ih, Nat.factorial_succ,
      (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (Nat.succ_ne_zero t) (Nat.factorial_ne_zero t)]
    ring

theorem theorem_n_five_delta_clause : WachTwistTheoremDeltaClause := by
  intro O _ _ _ ℓ hℓ hℓu s₀ hs hs2 x y u₁ hx t δO eO
  have he : eO = addVal O (ℓ : O) := IdempotentNormalFormsLenFacts.length_quot_span _
  have hfac : ∀ i ∈ Finset.Ioo 0 t, addVal O ((u₁ : O) - (u₁ : O) * ((x⁻¹ ^ i : Oˣ) : O)) =
      eO * ((s₀ + padicValNat ℓ i : ℕ) : ℕ∞) := by
    intro i hi
    have hi0 : i ≠ 0 := by rw [Finset.mem_Ioo] at hi; omega
    have h1 : ((x⁻¹ ^ i : Oˣ) : O) * (x : O) ^ i = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← Units.val_mul, inv_pow, inv_mul_cancel, Units.val_one]
    have h2 : (u₁ : O) - (u₁ : O) * ((x⁻¹ ^ i : Oˣ) : O) =
        ((u₁ * x⁻¹ ^ i : Oˣ) : O) * ((x : O) ^ i - 1) := by
      rw [Units.val_mul, mul_sub, mul_assoc, h1]; ring
    rw [h2, addVal_mul, addVal_eq_zero_of_unit, zero_add,
      powSubOneO O ℓ hℓ hℓu s₀ hs hs2 x y hx i hi0, he]
  have hval : addVal O δO = eO * ((∑ i ∈ Finset.Ioo 0 t, (s₀ + padicValNat ℓ i) : ℕ) : ℕ∞) := by
    show addVal O (∏ i ∈ Finset.Ioo 0 t, ((u₁ : O) - (u₁ : O) * ((x⁻¹ ^ i : Oˣ) : O))) = _
    rw [IdempotentNormalFormsLenFacts.addVal_prod, Finset.sum_congr rfl hfac, ← Finset.mul_sum, Nat.cast_sum]
  refine ⟨hval, ?_⟩
  rw [hval]
  have hle : ∑ i ∈ Finset.Ioo 0 t, (s₀ + padicValNat ℓ i) ≤ t * s₀ + padicValNat ℓ t.factorial := by
    have : Fact ℓ.Prime := ⟨hℓ⟩
    cases t with
    | zero => simp
    | succ t =>
      rw [theorem_n_five_delta_sum ℓ hℓ s₀ t, Nat.factorial_succ,
        (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (Nat.succ_ne_zero t) (Nat.factorial_ne_zero t)]
      exact add_le_add (Nat.mul_le_mul_right _ (Nat.le_succ t)) (Nat.le_add_left _ _)
  gcongr

theorem inputs_from_selmer_inj : SelmerInjConditions := by
  intro O _ _ _ A T' G _ _ _ _ _ M _ _ _ _ r χ E e₁ δ ι _ _ colIdx D j e' Kc k0 ℓ what₂ s
    L _ _ _ _ tens v₁ κ V _ _ _ _ _ _ iL qV Ff κz HcG Hc F Vo Io ε T₁ T₂ _ _ _ _ ρ₁ ρ₂ inc π γ lam
    Cs _ _ cls pr Fs Im h
  obtain ⟨h1, h2, h3, h4, ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩, h6⟩ := h
  refine ⟨h1, h2, h3, h4, fun l => ?_, h6⟩
  obtain ⟨b1, b2, b3, b4, b5⟩ := a8 l
  exact selmer_inj_column_place O A T' G M L V r χ (D (colIdx l)) iL qV tens a1 a2 a3 a4 a5 a6 a7 (Ff l)
    (j (colIdx l)) (κ l) (κz l) b1 b2 b3 b4 b5


end Formalism.RepresentationBoundsCohomology.BR
end
end
end
