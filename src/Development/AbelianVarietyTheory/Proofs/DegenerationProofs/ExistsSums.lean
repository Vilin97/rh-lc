module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPowerSeriesRingHomExtendingFiniteFreeStatement
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Expand
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TwistTxEvEqMapArcRootStatement
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.Valuation.LocalSubring
public import Mathlib.Topology.Algebra.Valued.NormedValued

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRingHomPowerSeriesRoot

section

@[expose] public section

open PowerSeries

namespace GlobalTheory

namespace SeriesRoot

variable {O : Type*} [CommRing O]

noncomputable def residuePart (k l : ℕ) : PowerSeries O →+ PowerSeries O where
  toFun f := PowerSeries.mk fun n => coeff (k * n + l) f
  map_zero' := by ext n; simp
  map_add' f g := by ext n; simp

theorem coeff_residuePart (k l n : ℕ) (f : PowerSeries O) :
    coeff n (residuePart k l f) = coeff (k * n + l) f := by
  simp [residuePart]

theorem coeff_X_pow_mul_expand {k : ℕ} (hk : k ≠ 0) {j : ℕ} (hj : j < k) (g : PowerSeries O)
    (m : ℕ) :
    coeff m (X ^ j * expand k hk g) = if m % k = j then coeff (m / k) g else 0 := by
  rw [coeff_X_pow_mul', coeff_expand]
  by_cases h : m % k = j
  · have hm : m = k * (m / k) + j := by rw [← h]; exact (Nat.div_add_mod m k).symm
    have h1 : j ≤ m := by omega
    have h2 : m - j = k * (m / k) := by omega
    rw [if_pos h1, if_pos h, h2, if_pos (dvd_mul_right _ _),
      Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hk)]
  · rw [if_neg h]
    split_ifs with h1 h2
    · exfalso
      obtain ⟨c, hc⟩ := h2
      apply h
      have : m = j + k * c := by omega
      rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
    · rfl
    · rfl

theorem sum_residuePart {k : ℕ} (hk : k ≠ 0) (f : PowerSeries O) :
    ∑ l ∈ Finset.range k, X ^ l * expand k hk (residuePart k l f) = f := by
  ext m

  rw [map_sum, Finset.sum_congr rfl
  (fun l hl => coeff_X_pow_mul_expand hk (Finset.mem_range.1 hl) _ m), Finset.sum_ite_eq,
  if_pos (Finset.mem_range.2 (Nat.mod_lt _ (Nat.pos_of_ne_zero hk))), coeff_residuePart,
  Nat.div_add_mod]

theorem residuePart_X_pow_mul_expand {k : ℕ} (hk : k ≠ 0) {j l : ℕ} (hj : j < k) (hl : l < k)
    (g : PowerSeries O) :
    residuePart k l (X ^ j * expand k hk g) = if l = j then g else 0 := by
  ext n
  rw [coeff_residuePart, coeff_X_pow_mul_expand hk hj, Nat.mul_add_mod, Nat.mod_eq_of_lt hl,
    Nat.mul_add_div (Nat.pos_of_ne_zero hk), Nat.div_eq_of_lt hl, add_zero]
  split_ifs <;> simp

variable {K : Type*} [CommRing K]

noncomputable def extendAdd (φ : PowerSeries O →+* K) (k : ℕ) (t : K) : PowerSeries O →+ K where
  toFun f := ∑ l ∈ Finset.range k, t ^ l * φ (residuePart k l f)
  map_zero' := by simp
  map_add' f g := by simp [mul_add, Finset.sum_add_distrib]

theorem extendAdd_apply (φ : PowerSeries O →+* K) (k : ℕ) (t : K) (f : PowerSeries O) :
    extendAdd φ k t f = ∑ l ∈ Finset.range k, t ^ l * φ (residuePart k l f) := rfl

theorem extendAdd_X_pow_mul_expand_of_lt (φ : PowerSeries O →+* K) {k : ℕ} (hk : k ≠ 0) (t : K)
    {j : ℕ} (hj : j < k) (g : PowerSeries O) :
    extendAdd φ k t (X ^ j * expand k hk g) = t ^ j * φ g := by
  rw [extendAdd_apply, Finset.sum_eq_single j]
  · rw [residuePart_X_pow_mul_expand hk hj hj, if_pos rfl]
  · intro l hl hlj
    rw [residuePart_X_pow_mul_expand hk hj (Finset.mem_range.1 hl), if_neg hlj, map_zero,
      mul_zero]
  · intro h
    exact absurd (Finset.mem_range.2 hj) h

theorem extendAdd_X_pow_mul_expand (φ : PowerSeries O →+* K) {k : ℕ} (hk : k ≠ 0) {t : K}
    (ht : t ^ k = φ X) (j : ℕ) (g : PowerSeries O) :
    extendAdd φ k t (X ^ j * expand k hk g) = t ^ j * φ g := by
  have h : (X : PowerSeries O) ^ j * expand k hk g =
      X ^ (j % k) * expand k hk (X ^ (j / k) * g) := by
    rw [map_mul, map_pow, expand_X, ← pow_mul, ← mul_assoc, ← pow_add, Nat.mod_add_div]
  rw [h, extendAdd_X_pow_mul_expand_of_lt φ hk t (Nat.mod_lt _ (Nat.pos_of_ne_zero hk)),
    map_mul, map_pow, ← ht, ← pow_mul, ← mul_assoc, ← pow_add, Nat.mod_add_div]

theorem extendAdd_mul (φ : PowerSeries O →+* K) {k : ℕ} (hk : k ≠ 0) {t : K}
    (ht : t ^ k = φ X) (f g : PowerSeries O) :
    extendAdd φ k t (f * g) = extendAdd φ k t f * extendAdd φ k t g := by
  conv_lhs => rw [← sum_residuePart hk f, ← sum_residuePart hk g]

  rw [extendAdd_apply φ k t f, extendAdd_apply φ k t g, Finset.sum_mul_sum, Finset.sum_mul_sum,
  map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_

  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_mul_mul_comm, ← pow_add, ← map_mul, extendAdd_X_pow_mul_expand φ hk ht, map_mul,
    pow_add]
  ring

noncomputable def extendHom (φ : PowerSeries O →+* K) {k : ℕ} (hk : k ≠ 0) {t : K}
    (ht : t ^ k = φ X) : PowerSeries O →+* K where
  toFun := extendAdd φ k t
  map_zero' := map_zero _
  map_add' := map_add _
  map_one' := by simpa using extendAdd_X_pow_mul_expand φ hk ht 0 1
  map_mul' := extendAdd_mul φ hk ht

theorem extendHom_expand (φ : PowerSeries O →+* K) {k : ℕ} (hk : k ≠ 0) {t : K}
    (ht : t ^ k = φ X) (g : PowerSeries O) : extendHom φ hk ht (expand k hk g) = φ g := by
  have := extendAdd_X_pow_mul_expand φ hk ht 0 g
  rw [pow_zero, pow_zero, one_mul, one_mul] at this
  exact this

theorem extendHom_X (φ : PowerSeries O →+* K) {k : ℕ} (hk : k ≠ 0) {t : K}
    (ht : t ^ k = φ X) : extendHom φ hk ht X = t := by
  have := extendAdd_X_pow_mul_expand φ hk ht 1 1
  rw [pow_one, pow_one, map_one, map_one, mul_one, mul_one] at this
  exact this

end SeriesRoot

theorem exists_ringHom_powerSeries_root :
    ∀ (O K : Type) [CommRing O] [CommRing K] (φ : PowerSeries O →+* K) (k : ℕ) (t : K), 0 < k →
      t ^ k = φ PowerSeries.X → ∃ Φ : PowerSeries O →+* K,
        (∀ a, Φ (PowerSeries.C a) = φ (PowerSeries.C a)) ∧ Φ PowerSeries.X = t ∧
          ∀ f, Φ f ∈ Subring.closure (Set.range φ ∪ {t}) := by
  intro O K _ _ φ k t hk ht
  refine ⟨SeriesRoot.extendHom φ hk.ne' ht, fun a => ?_, SeriesRoot.extendHom_X φ hk.ne' ht,
    fun f => ?_⟩
  · rw [← SeriesRoot.extendHom_expand φ hk.ne' ht (PowerSeries.C a), expand_C]
  · change ∑ l ∈ Finset.range k, t ^ l * φ (SeriesRoot.residuePart k l f) ∈ _
    refine Subring.sum_mem _ fun l _ => Subring.mul_mem _ (Subring.pow_mem _ ?_ l) ?_
    · exact Subring.subset_closure (Or.inr rfl)
    · exact Subring.subset_closure (Or.inl ⟨_, rfl⟩)

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRingHomPowerSeriesRootStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.exists_ringHom_powerSeries_root' : ∀ (O K : Type) [CommRing O] [CommRing K] (φ : PowerSeries O →+* K) (k : ℕ) (t : K), 0 < k → t ^ k = φ PowerSeries.X → ∃ Φ : PowerSeries O →+* K, (∀ a, Φ (PowerSeries.C a) = φ (PowerSeries.C a)) ∧ Φ PowerSeries.X = t ∧ ∀ f, Φ f ∈ Subring.closure (Set.range φ ∪ {t}) := by
  first | exact @GlobalTheory.exists_ringHom_powerSeries_root | exact GlobalTheory.exists_ringHom_powerSeries_root | (intros; apply GlobalTheory.exists_ringHom_powerSeries_root <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSums

section

@[expose] public section

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Ex
open scoped BigOperators

noncomputable section
namespace GlobalTheory.ArcSeries

section Comp
variable {O O' O'' : Type} [CommRing O] [CommRing O'] [CommRing O''] {f : O →+* O'} {g : O' →+* O''}
  {N : NumD O} {N' : NumD O'} {N'' : NumD O''}

def homComp (I : NumD.Hom f N N') (I' : NumD.Hom g N' N'') (k : O →+* O'') (hk : ∀ x, k x = g (f x)) :
    NumD.Hom k N N'' :=
  have e : ∀ x : Oˣ, Units.map k.toMonoidHom x = Units.map g.toMonoidHom (Units.map f.toMonoidHom x) :=
    fun x => Units.ext (hk x)
  { φ := I'.φ.comp I.φ
    h x := I'.h (I.φ x) * Units.map g.toMonoidHom (I.h x)
    h_one := by rw [map_one, I'.h_one, I.h_one, map_one, mul_one]
    θ_eq x y u := by
      have a := congrArg (fun t => Additive.ofMul (Units.map g.toMonoidHom t)) (I.θ_eq x y u)
      have b := congrArg Additive.ofMul (I'.θ_eq (I.φ x) (I.φ y) (I.φ u))
      apply Additive.ofMul.injective
      simp only [e, map_mul, ofMul_mul, MonoidHom.comp_apply] at a b ⊢
      linear_combination (norm := abel) a + b
    σ_eq x := by
      have a := congrArg (fun t => Additive.ofMul (Units.map g.toMonoidHom t)) (I.σ_eq x)
      have b := congrArg Additive.ofMul (I'.σ_eq (I.φ x))
      apply Additive.ofMul.injective
      simp only [e, map_mul, map_inv, ofMul_mul, MonoidHom.comp_apply] at a b ⊢
      linear_combination (norm := abel) a + b
    lam := I'.lam * Units.map g.toMonoidHom I.lam
    th_eq x := by
      rw [MonoidHom.comp_apply, I'.th_eq, I.th_eq, hk]
      simp only [Units.val_mul, map_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass]
      ring
    e := I.e.trans I'.e
    c_eq χ := by rw [AddEquiv.trans_apply, I'.c_eq, I.c_eq]; rfl
    ψ_eq χ := by
      have a := congrArg (fun t => Additive.ofMul (Units.map g.toMonoidHom t)) (I.ψ_eq χ)
      have b := congrArg Additive.ofMul (I'.ψ_eq (I.e χ))
      apply Additive.ofMul.injective
      simp only [e, map_mul, ofMul_mul, AddEquiv.trans_apply, I.c_eq] at a b ⊢
      linear_combination (norm := abel) a + b }

theorem homComp_rel (I : NumD.Hom f N N') (I' : NumD.Hom g N' N'') (k : O →+* O'') (hk : ∀ x, k x = g (f x))
    {a : N.Gt} {b : N'.Gt} {c : N''.Gt} (h : I.Rel a b) (h' : I'.Rel b c) : (homComp I I' k hk).Rel a c := by
  refine ⟨h'.1.trans (congrArg I'.φ h.1), fun χ => ?_⟩
  have e : ∀ x : Oˣ, Units.map k.toMonoidHom x = Units.map g.toMonoidHom (Units.map f.toMonoidHom x) :=
    fun x => Units.ext (hk x)
  have p := congrArg (fun t => Additive.ofMul (Units.map g.toMonoidHom t)) (h.2 χ)
  have q := congrArg Additive.ofMul (h'.2 (I.e χ))
  apply Additive.ofMul.injective
  simp only [homComp, e, map_mul, ofMul_mul, AddEquiv.trans_apply, I.c_eq, h.1] at p q ⊢
  linear_combination (norm := abel) p + q
end Comp

theorem exists_ball (C : Type) [NormedField C] [IsUltrametricDist C] :
    ∃ S : ValuationSubring C, ∀ x, x ∈ S ↔ ‖x‖ ≤ 1 :=
  ⟨(NormedField.valuation (K := C)).valuationSubring, fun x => by
    rw [Valuation.mem_valuationSubring_iff, NormedField.valuation_apply]; exact Iff.rfl⟩

theorem mem_of_isIntegral {R K : Type} [CommRing R] [Field K] [Algebra R K] (S : ValuationSubring K)
    (h : ∀ r, algebraMap R K r ∈ S) {x : K} (hx : IsIntegral R x) : x ∈ S := by
  have : IsIntegral S x := hx.map_of_comp_eq ((algebraMap R K).codRestrict S h) (RingHom.id K) rfl
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 this
  exact y.2

theorem exists_map {O O₁ K : Type} [CommRing O] [CommRing O₁] [Field K] [Algebra O O₁] [Module.Free O O₁]
    [Module.Finite O O₁] [Algebra (PowerSeries O) K] (io : O₁ →+* K)
    (hio : ∀ a, io (algebraMap O O₁ a) = algebraMap (PowerSeries O) K (PowerSeries.C a)) {k : ℕ} (hk : 0 < k) {t : K}
    (ht : t ^ k = algebraMap (PowerSeries O) K PowerSeries.X) :
    ∃ (R₁ : Subalgebra (PowerSeries O) K) (Φ : PowerSeries O₁ →+* K), Module.Finite (PowerSeries O) R₁ ∧
      (∀ a, Φ (PowerSeries.C a) = io a) ∧ Φ PowerSeries.X = t ∧ ∀ f, Φ f ∈ R₁ := by
  obtain ⟨Φ₁, h1, h2, h3⟩ := GlobalTheory.T.exists_powerSeries_ringHom_extending_finite_free O O₁ K (algebraMap _ K) io hio
  obtain ⟨Φ, h4, h5, h6⟩ := GlobalTheory.T.exists_ringHom_powerSeries_root' O₁ K Φ₁ k t hk (ht.trans h2.symm)
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := O) (M := O₁)
  refine ⟨Algebra.adjoin _ (io '' s ∪ {t}), Φ, Algebra.finite_adjoin_of_finite_of_isIntegral
    ((s.finite_toSet.image _).union (Set.finite_singleton _)) ?_, fun a => (h4 a).trans (h1 a), h5, fun f => ?_⟩
  · rintro x (⟨a, -, rfl⟩ | rfl)
    · exact (Algebra.IsIntegral.isIntegral (R := O) a).map_of_comp_eq PowerSeries.C io (RingHom.ext fun a => (hio a).symm)
    · exact IsIntegral.of_pow hk (ht ▸ isIntegral_algebraMap)
  · refine (Subring.closure_le (t := (Algebra.adjoin _ (io '' s ∪ {t})).toSubring)).2 ?_ (h6 f)
    rintro x (⟨g, rfl⟩ | rfl)
    · refine (Subring.closure_le (t := (Algebra.adjoin _ (io '' s ∪ {t})).toSubring)).2 ?_ (h3 g)
      rintro x (⟨g, rfl⟩ | ⟨a, rfl⟩)
      · exact Subalgebra.algebraMap_mem _ g
      · have ha : a ∈ Submodule.span O (s : Set O₁) := hs ▸ Submodule.mem_top
        change io a ∈ Algebra.adjoin (PowerSeries O) (io '' s ∪ {t})
        induction ha using Submodule.span_induction with
        | mem x hx => exact Algebra.subset_adjoin (.inl ⟨x, hx, rfl⟩)
        | zero => rw [map_zero]; exact zero_mem _
        | add x y _ _ a b => rw [map_add]; exact add_mem a b
        | smul c x _ a => rw [Algebra.smul_def, map_mul, hio]; exact mul_mem (Subalgebra.algebraMap_mem _ _) a
    · exact Algebra.subset_adjoin (.inr rfl)

def Sums {R K F : Type} [CommRing R] [Field K] [Field F] [Algebra R K] (X : R) (io : F →+* K) (N : NumD F)
    (be : LinearMap.BilinForm ℤ N.X) (m j : ℕ) {La : Type} (q : La → N.QT (m ^ 2)) (qz : N.QT j) (t : Kˣ)
    (v w : La → K) : Prop :=
  ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] (gam : K →+* C),
    (∀ r, ‖gam (algebraMap R K r)‖ ≤ 1) → ‖gam (algebraMap R K X)‖ < 1 →
    ∀ (N' : NumD C) (I : NumD.Hom (gam.comp io) N N') (k : ℕ) (β : N'.Form k), I.lam = 1 →
    (∀ y z, β.be (I.e y) (I.e z) = be y z) → ∀ u rm rj : Cˣ, (u : C) = gam (algebraMap R K X) →
    (rm : C) = gam (t ^ j : Kˣ) → (rj : C) = gam (t ^ m ^ 2 : Kˣ) →
    ∀ (q' : La → N'.QT (m ^ 2)) (p : La → (N'.twist β u).QT (m ^ 2)),
    (∀ x, (q' x).1.1.toAdd = I.e (q x).1.1.toAdd ∧ I.Rel (q x).1.2 (q' x).1.2) → (∀ x, TwRel β u rm (q' x) (p x)) →
    (∀ x, gam (v x) = (N'.twist β u).tx m (p x)) ∧
    ∀ (qz' : N'.QT j) (pz : (N'.twist β u).QT j), qz'.1.1.toAdd = I.e qz.1.1.toAdd → I.Rel qz.1.2 qz'.1.2 →
      TwRel β u rj qz' pz → ∃ s : Cˣ, ∀ x, gam (w x) = s * (N'.twist β u).ev m (p x) pz.1.2

theorem exists_sums {O O₁ K F : Type} [CommRing O] [CommRing O₁] [Field K] [Field F] [Algebra O O₁] [Module.Free O O₁]
    [Module.Finite O O₁] [Algebra (PowerSeries O) K] (f : O₁ →+* F) (io : F →+* K)
    (hio : ∀ a, io (f (algebraMap O O₁ a)) = algebraMap (PowerSeries O) K (PowerSeries.C a)) {N : NumD F}
    (be : LinearMap.BilinForm ℤ N.X) {m j : ℕ} (hm : Odd m) (hj : 0 < j) {La : Type} (q : La → N.QT (m ^ 2)) (qz : N.QT j)
    (t : Kˣ) (ht : (t : K) ^ (m ^ 2 * j) = algebraMap (PowerSeries O) K PowerSeries.X) {N₀ : NumD O₁}
    (I₀ : NumD.Hom f N₀ N) (hl : I₀.lam = 1)
    (hq : ∀ x, ∃ p₀ : N₀.QT (m ^ 2), (q x).1.1.toAdd = I₀.e p₀.1.1.toAdd ∧ I₀.Rel p₀.1.2 (q x).1.2)
    (hz : ∃ p₀ : N₀.QT j, qz.1.1.toAdd = I₀.e p₀.1.1.toAdd ∧ I₀.Rel p₀.1.2 qz.1.2) :
    ∃ (R₁ : Subalgebra (PowerSeries O) K) (v w : La → K), Module.Finite (PowerSeries O) R₁ ∧ (∀ x, v x ∈ R₁) ∧
      Sums (PowerSeries.X : PowerSeries O) io N be m j q qz t v w := by
  have hk : 0 < m ^ 2 * j := Nat.mul_pos (pow_pos hm.pos 2) hj
  obtain ⟨R₁, Φ, hR, h1, h2, h3⟩ := exists_map (io.comp f) hio hk ht
  choose p₀ hp hp' using hq
  obtain ⟨q₀, hz, hz'⟩ := hz
  let be₀ : LinearMap.BilinForm ℤ N₀.X := be.comp I₀.e.toAddMonoidHom.toIntLinearMap I₀.e.toAddMonoidHom.toIntLinearMap
  let s : ℕ := ((m : ℤ) ^ 2 * (((m ^ 2 * j : ℕ) : ℤ) * be₀ q₀.1.1.toAdd q₀.1.1.toAdd)).toNat
  refine ⟨R₁, fun x => Φ (N₀.arcTx (((m ^ 2 * j : ℕ) : ℤ) • be₀) m (p₀ x)),
    fun x => Φ (N₀.arcEv (((m ^ 2 * j : ℕ) : ℤ) • be₀) m (p₀ x) q₀ s), hR, fun x => h3 _, ?_⟩
  intro C _ _ _ gam g1 g2 N' I k β hI hβ u rm rj hu hrm hrj q' p hq' hp''
  obtain ⟨S, hS⟩ := exists_ball C
  have n1 : ∀ g, ‖(gam.comp Φ) g‖ ≤ 1 := fun g => (hS _).1 (mem_of_isIntegral (S.comap gam)
    (fun r => (hS _).2 (g1 r)) ((Algebra.IsIntegral.isIntegral (⟨_, h3 g⟩ : R₁)).map R₁.val))
  have n2 : ‖(gam.comp Φ) PowerSeries.X‖ < 1 := by
    rw [← ht, map_pow, norm_pow, pow_lt_one_iff_of_nonneg (norm_nonneg _) hk.ne'] at g2
    rwa [RingHom.comp_apply, h2]
  let t' : Cˣ := Units.map gam.toMonoidHom t
  let J := homComp I₀ I ((gam.comp Φ).comp PowerSeries.C) fun x => congrArg gam (h1 x)
  have hJ : J.lam = 1 := by
    change I.lam * Units.map _ I₀.lam = 1
    rw [hI, hl, map_one, mul_one]
  have e1 : t' ^ j = rm := Units.ext (by rw [hrm, ← map_pow]; rfl)
  have key := fun x => GlobalTheory.T.twist_tx_ev_eq_map_arc_root_alt O₁ C (gam.comp Φ) n1 n2 t' u rm rj m j hm hj (congrArg gam h2.symm) e1
    (Units.ext (by rw [hrj, ← map_pow]; rfl))
    (Units.ext (by rw [hu, ← e1, ← pow_mul, mul_comm j, ← ht, ← map_pow, map_pow gam]; simp))
    N₀ N' J k be₀ β (fun y z => hβ _ _) (p₀ x) (q' x) (p x) ((hq' x).1.trans (congrArg I.e (hp x)))
    (homComp_rel _ _ _ _ (hp' x) (hq' x).2) (hp'' x)
  refine ⟨fun x => ?_, fun qz' pz a b c => ⟨(J.lam * J.h q₀.1.2.b ^ (m ^ 2))⁻¹ * t' ^ s, fun x => ?_⟩⟩
  · rw [(key x).1, hJ, Units.val_one, one_mul]; rfl
  · have := (key x).2 q₀ qz' pz (a.trans (congrArg I.e hz)) (homComp_rel _ _ _ _ hz' b) c s (Int.self_le_toNat _)
    rw [Units.val_mul, mul_assoc, Units.val_pow_eq_pow_val, this, Units.inv_mul_cancel_left]; rfl

end GlobalTheory.ArcSeries
end
end
end
