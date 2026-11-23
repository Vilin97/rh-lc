module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.IsHermHyperbolic
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.QuasiReflectionEqUnitaryTransvectionMul
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.TransvectionIdentitiesUnitary
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitaryTransvectionSubmonoidNormalDetOne
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.TransvectionIdentitiesUnitary
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryGeneratedByQuasiReflectionsAndWittStatement
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryCharacterKillsUnitaryTransvections

section

@[expose] public section

open scoped Matrix

namespace GlobalTheory.UTrans.TvKill

open GlobalTheory.UTrans GlobalTheory.UTrans.Calc

variable {E : Type} [Field E] {n : ℕ} {σ : E →+* E} {G : Matrix (Fin n) (Fin n) E}

def rk (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) : Matrix (Fin n) (Fin n) E :=
  Matrix.of fun a b => x a * ∑ e, G b e * σ (y e)

theorem rk_mulVec (x y v : Fin n → E) : rk σ G x y *ᵥ v = hf σ G v y • x := by
  funext a
  simp only [rk, Matrix.mulVec, dotProduct, Matrix.of_apply, hf, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun e _ => ?_
  ring

theorem exists_dual (hG : IsHerm σ G) {x : Fin n → E} (hx : x ≠ 0) : ∃ y, hf σ G x y = 1 := by
  have h1 : Matrix.vecMul x G ≠ 0 := fun h => hx (Matrix.eq_zero_of_vecMul_eq_zero hG.det_ne h)
  obtain ⟨b, hb⟩ := Function.ne_iff.mp h1
  refine ⟨Pi.single b (σ (Matrix.vecMul x G b)⁻¹), ?_⟩
  have : hf σ G x (Pi.single b (σ (Matrix.vecMul x G b)⁻¹)) =
      Matrix.vecMul x G b * (Matrix.vecMul x G b)⁻¹ := by
    simp only [hf, Pi.single_apply, apply_ite σ, map_zero, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, hG.invol, ← Finset.sum_mul]
    rfl
  rw [this, mul_inv_cancel₀ hb]

theorem exists_dual_iso [CharZero E] (hG : IsHerm σ G) {x : Fin n → E} (hx : x ≠ 0)
    (hxx : hf σ G x x = 0) : ∃ y, hf σ G x y = 1 ∧ hf σ G y y = 0 := by
  obtain ⟨y, hy⟩ := exists_dual hG hx
  have hyx : hf σ G y x = 1 := by rw [← hf_conj σ G hG.invol hG.herm, hy, map_one]
  have hc : σ (-(hf σ G y y / 2)) = -(hf σ G y y / 2) := by
    rw [map_neg, map_div₀, hf_conj σ G hG.invol hG.herm, map_ofNat]
  refine ⟨y + (-(hf σ G y y / 2)) • x, ?_, ?_⟩
  · rw [hf_add_right, hf_smul_right, hxx, hy]; ring
  · simp only [hf_add_left, hf_add_right, hf_smul_left, hf_smul_right, hc, hxx, hy, hyx]
    ring

theorem exists_double [CharZero E] (hG : IsHerm σ G) {x : Fin n → E} (hx : x ≠ 0)
    (hxx : hf σ G x x = 0) : ∃ γ, IsU σ G γ ∧ γ *ᵥ x = (2 : E) • x := by
  obtain ⟨y, hy, hyy⟩ := exists_dual_iso hG hx hxx
  have hyx : hf σ G y x = 1 := by rw [← hf_conj σ G hG.invol hG.herm, hy, map_one]
  have hc : σ (-(1 / 2)) = -(1 / 2) := by
    rw [map_neg, map_div₀, map_one, map_ofNat]
  have hm : ∀ v, (1 + rk σ G x y + (-(1 / 2) : E) • rk σ G y x) *ᵥ v =
      v + hf σ G v y • x + (-(1 / 2) : E) • hf σ G v x • y := by
    intro v
    rw [Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, rk_mulVec,
      rk_mulVec]
  refine ⟨1 + rk σ G x y + (-(1 / 2) : E) • rk σ G y x, ?_, ?_⟩
  · intro v w
    rw [hm, hm]
    simp only [hf_add_left, hf_add_right, hf_smul_left, hf_smul_right, hc, hxx, hy, hyx, hyy,
      hf_conj σ G hG.invol hG.herm]
    ring
  · rw [hm, hy, hxx, zero_smul, smul_zero, add_zero, one_smul, two_smul]

theorem char_tvGen : ∀ (E : Type) [Field E] [CharZero E] (n : ℕ) (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E), GlobalTheory.UTrans.IsHerm σ G → ∀ (A : Type) [CommGroup A] (X : Matrix (Fin n) (Fin n) E → A), (∀ a b, GlobalTheory.UTrans.IsU σ G a → GlobalTheory.UTrans.IsU σ G b → X (a * b) = X a * X b) → ∀ m ∈ GlobalTheory.UTrans.TvGen σ G, X m = 1 := by
  intro E _ _ n σ G hG A _ X hX
  have hU1 : IsU σ G 1 := fun x y => by simp
  have hX1 : X 1 = 1 := by
    have := hX 1 1 hU1 hU1
    rw [mul_one] at this
    exact mul_eq_left.mp this.symm
  have key : ∀ m ∈ TvGen σ G, IsU σ G m ∧ X m = 1 := by
    intro m hm
    induction hm using Submonoid.closure_induction with
    | mem m hm =>
      obtain ⟨x, t, hx, ht, rfl⟩ := hm
      have hUq : ∀ q : ℚ, IsU σ G (tv σ G x (q * t)) := by
        intro q
        refine isU_tv σ G hG.invol hG.herm x _ ?_
        rw [hx, map_mul, map_ratCast]
        linear_combination (q : E) * ht
      have hUt : IsU σ G (tv σ G x t) := by simpa using hUq 1
      refine ⟨hUt, ?_⟩
      by_cases hx0 : x = 0
      · subst hx0
        have : tv σ G 0 t = 1 := by
          ext a b
          simp [tv]
        rw [this, hX1]
      · obtain ⟨γ, hγ, hγx⟩ := exists_double hG hx0 hx
        have h3 : IsU σ G (tv σ G x (1 / 3 * t)) := by
          have := hUq (1 / 3)
          push_cast at this
          exact this
        have hc := conj_tv σ G γ x (1 / 3 * t) hγ
        have he : tv σ G (γ *ᵥ x) (1 / 3 * t) = tv σ G x (1 / 3 * t) * tv σ G x t := by
          rw [hγx, tv_smul, tv_mul, hx, map_ofNat]
          congr 1
          ring
        rw [he] at hc
        have h4 := congrArg X hc
        rw [hX _ _ hγ h3, hX _ _ (isU_mul σ G _ _ h3 hUt) hγ, hX _ _ h3 hUt, mul_comm (X γ)] at h4
        exact mul_eq_left.mp (mul_right_cancel h4).symm
    | one => exact ⟨hU1, hX1⟩
    | mul a b _ _ ha hb =>
      exact ⟨isU_mul σ G _ _ ha.1 hb.1, by rw [hX _ _ ha.1 hb.1, ha.2, hb.2, mul_one]⟩
  exact fun m hm => (key m hm).2

end GlobalTheory.UTrans.TvKill
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryCharacterKillsUnitaryTransvectionsStatement

section

@[expose] public section

open scoped Matrix

theorem _root_.GlobalTheory.T.unitaryCharacter_kills_unitaryTransvections : ∀ (E : Type) [Field E] [CharZero E] (n : ℕ) (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E), GlobalTheory.UTrans.IsHerm σ G → ∀ (A : Type) [CommGroup A] (X : Matrix (Fin n) (Fin n) E → A), (∀ a b, GlobalTheory.UTrans.IsU σ G a → GlobalTheory.UTrans.IsU σ G b → X (a * b) = X a * X b) → ∀ m ∈ GlobalTheory.UTrans.TvGen σ G, X m = 1 := by
  first | exact @GlobalTheory.UTrans.TvKill.char_tvGen | exact GlobalTheory.UTrans.TvKill.char_tvGen | (intros; apply GlobalTheory.UTrans.TvKill.char_tvGen <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.CharEqOneOfDetEqOne

section

@[expose] public section

open scoped Matrix

namespace GlobalTheory.UTrans.CharDet

variable {E : Type} [Field E] {n : ℕ} {σ : E →+* E} {G : Matrix (Fin n) (Fin n) E}

theorem isU_one : IsU σ G 1 := fun x y => by simp

theorem isU_refl (hG : IsHerm σ G) {x : Fin n → E} {u : E} (hx : hf σ G x x ≠ 0) (hu : u * σ u = 1) :
    IsU σ G (tv σ G x ((u - 1) / hf σ G x x)) := by
  apply Calc.isU_tv σ G hG.invol hG.herm
  rw [map_div₀, Calc.hf_conj σ G hG.invol hG.herm, map_sub, map_one]
  field_simp
  linear_combination hu

theorem refl_mul {x : Fin n → E} (u v : E) (hx : hf σ G x x ≠ 0) :
    tv σ G x ((u - 1) / hf σ G x x) * tv σ G x ((v - 1) / hf σ G x x) =
      tv σ G x ((u * v - 1) / hf σ G x x) := by
  rw [Calc.tv_mul]
  congr 1
  field_simp
  ring

theorem refl_det {x : Fin n → E} (u : E) (hx : hf σ G x x ≠ 0) :
    (tv σ G x ((u - 1) / hf σ G x x)).det = u := by
  rw [Calc.tv_det]
  field_simp
  ring

theorem refl_one (x : Fin n → E) : tv σ G x ((1 - 1) / hf σ G x x) = 1 := by
  ext a b
  simp [tv]

variable [CharZero E] {A : Type} [CommGroup A] {X : Matrix (Fin n) (Fin n) E → A}

theorem char_refl_eq (hG : IsHerm σ G)
    (h : (∃ z : Fin n → E, z ≠ 0 ∧ hf σ G z z = 0) ∨ ∀ x y : Fin n → E, hf σ G x x ≠ 0 → hf σ G y y ≠ 0 →
      ∃ a : E, hf σ G y y = σ a * a * hf σ G x x)
    (hX : ∀ a b, IsU σ G a → IsU σ G b → X (a * b) = X a * X b)
    {x y : Fin n → E} {u : E} (hx : hf σ G x x ≠ 0) (hy : hf σ G y y ≠ 0) (hu : u * σ u = 1) :
    X (tv σ G x ((u - 1) / hf σ G x x)) = X (tv σ G y ((u - 1) / hf σ G y y)) := by
  rcases h with h | h
  · obtain ⟨m, hm, e⟩ := quasiReflection_eq_tvGen_mul E n σ G hG h x y u hx hy hu
    rw [e, hX _ _ ((tvGen_normal E n σ G hG).2 m hm).1 (isU_refl hG hy hu),
      GlobalTheory.T.unitaryCharacter_kills_unitaryTransvections E n σ G hG A X hX m hm, one_mul]
  · obtain ⟨a, ha⟩ := h x y hx hy
    have h1 : hf σ G (a • x) (a • x) = hf σ G y y := by
      rw [Calc.hf_smul_left, Calc.hf_smul_right, ha]; ring
    obtain ⟨γ, hγ, e⟩ := (GlobalTheory.T.unitary_generated_by_quasiReflections_and_witt E n σ G hG).2 y (a • x) hy h1
    have ha0 : a ≠ 0 := by
      rintro rfl
      simp at ha
      exact hy ha
    have ha1 : σ a ≠ 0 := (map_ne_zero σ).2 ha0
    have h2 : tv σ G x ((u - 1) / hf σ G x x) = tv σ G (a • x) ((u - 1) / hf σ G y y) := by
      rw [Calc.tv_smul, ha]
      congr 1
      field_simp
    have h3 : γ * tv σ G x ((u - 1) / hf σ G x x) = tv σ G y ((u - 1) / hf σ G y y) * γ := by
      rw [h2, Calc.conj_tv σ G γ _ _ hγ, e]
    have h4 := congrArg X h3
    rw [hX _ _ hγ (isU_refl hG hx hu), hX _ _ (isU_refl hG hy hu) hγ, mul_comm] at h4
    exact mul_right_cancel h4

theorem char_prod (hG : IsHerm σ G)
    (h : (∃ z : Fin n → E, z ≠ 0 ∧ hf σ G z z = 0) ∨ ∀ x y : Fin n → E, hf σ G x x ≠ 0 → hf σ G y y ≠ 0 →
      ∃ a : E, hf σ G y y = σ a * a * hf σ G x x)
    (hX : ∀ a b, IsU σ G a → IsU σ G b → X (a * b) = X a * X b)
    {x : Fin n → E} (hx : hf σ G x x ≠ 0) (l : List ((Fin n → E) × E))
    (hl : ∀ p ∈ l, hf σ G p.1 p.1 ≠ 0 ∧ p.2 * σ p.2 = 1) :
    IsU σ G (l.map fun p => tv σ G p.1 ((p.2 - 1) / hf σ G p.1 p.1)).prod ∧
      X (l.map fun p => tv σ G p.1 ((p.2 - 1) / hf σ G p.1 p.1)).prod =
        X (tv σ G x (((l.map fun p => tv σ G p.1 ((p.2 - 1) / hf σ G p.1 p.1)).prod.det - 1) / hf σ G x x)) := by
  induction l with
  | nil => exact ⟨isU_one, by simp only [List.map_nil, List.prod_nil, Matrix.det_one, refl_one]⟩
  | cons p l ih =>
    obtain ⟨h1, h2⟩ := ih fun q hq => hl q (List.mem_cons_of_mem _ hq)
    obtain ⟨hp, hv⟩ := hl p List.mem_cons_self
    rw [List.map_cons, List.prod_cons]
    refine ⟨Calc.isU_mul σ G _ _ (isU_refl hG hp hv) h1, ?_⟩
    rw [hX _ _ (isU_refl hG hp hv) h1, h2, char_refl_eq hG h hX hp hx hv, Matrix.det_mul, refl_det _ hp,
      ← refl_mul _ _ hx, hX _ _ (isU_refl hG hx hv) (isU_refl hG hx (h1.det_mul_conj_det hG.det_ne))]

end GlobalTheory.UTrans.CharDet

theorem GlobalTheory.UTrans.char_eq_one_of_det_eq_one : ∀ (E : Type) [Field E] [CharZero E] (n : ℕ) (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E), GlobalTheory.UTrans.IsHerm σ G → ((∃ z : Fin n → E, z ≠ 0 ∧ GlobalTheory.UTrans.hf σ G z z = 0) ∨ ∀ x y : Fin n → E, GlobalTheory.UTrans.hf σ G x x ≠ 0 → GlobalTheory.UTrans.hf σ G y y ≠ 0 → ∃ a : E, GlobalTheory.UTrans.hf σ G y y = σ a * a * GlobalTheory.UTrans.hf σ G x x) → ∀ (A : Type) [CommGroup A] (X : Matrix (Fin n) (Fin n) E → A), (∀ a b, GlobalTheory.UTrans.IsU σ G a → GlobalTheory.UTrans.IsU σ G b → X (a * b) = X a * X b) → ∀ γ, GlobalTheory.UTrans.IsU σ G γ → γ.det = 1 → X γ = 1 := by
  intro E _ _ n σ G hG h A _ X hX γ hγ hd
  have h1 : X 1 = 1 := by
    have := hX 1 1 CharDet.isU_one CharDet.isU_one
    rw [mul_one] at this
    exact left_eq_mul.1 this
  obtain ⟨l, hl, e⟩ := (GlobalTheory.T.unitary_generated_by_quasiReflections_and_witt E n σ G hG).1 γ hγ
  cases l with
  | nil => rw [e]; simpa using h1
  | cons p l =>
    have h2 := (CharDet.char_prod hG h hX (hl p List.mem_cons_self).1 _ hl).2
    rw [← e, hd, CharDet.refl_one] at h2
    rw [h2, h1]
end
end
