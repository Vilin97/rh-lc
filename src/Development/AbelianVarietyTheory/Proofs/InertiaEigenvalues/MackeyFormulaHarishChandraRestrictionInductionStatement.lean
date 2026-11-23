module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsMirClass
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BlockParabolicUnitriangularSubgroupsGLnPrimeFiel
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardDoubleCosetMulCardInter
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsShuffle
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MackeyCellTermOfBlockSizes
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BlockParabolicUnitriangularSubgroupsGLnPrimeFielStatement
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraInductionRestrictionIsClassFunction
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.Reciprocity

section

@[expose] public section

noncomputable section

namespace GlobalTheory.GLm.Recip

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

theorem toG_coe {g : ℕ} [Fact g.Prime] {n : ℕ} (h : Gn g n) : toG (h : Mt g n) = h := by
  unfold toG
  rw [dite_eq_left h.isUnit]
  exact Units.ext (IsUnit.unit_spec _)

theorem coe_toG {g : ℕ} [Fact g.Prime] {n : ℕ} {M : Mt g n} (h : IsUnit M) : ((toG M : Gn g n) : Mt g n) = M := by
  unfold toG
  rw [dite_eq_left h]
  exact IsUnit.unit_spec _

theorem mean_conj {G : Type} [Group G] [Fintype G] (χ F : G → ℂ) (hχ : IsClass χ) (c : ℂ) :
    mean (fun x => χ x * (c * ∑ y, F (y⁻¹ * x * y))) = c * ∑ x, F x * χ x := by
  unfold mean
  have h1 : ∀ y : G, ∑ x, χ x * F (y⁻¹ * x * y) = ∑ x, F x * χ x := by
    intro y
    symm
    refine Fintype.sum_equiv (MulAut.conj y).toEquiv _ _ ?_
    intro x
    have : y⁻¹ * (y * x * y⁻¹) * y = x := by group
    simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply]
    rw [hχ, this, mul_comm]
  have h2 : ∑ x, χ x * (c * ∑ y, F (y⁻¹ * x * y)) = c * ∑ y : G, ∑ x, χ x * F (y⁻¹ * x * y) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.mul_sum]; ring
  have h3 : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [h2]
  simp only [h1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

theorem mean_res (g : ℕ) [Fact g.Prime] (c d n : ℕ) (hn : n = c + d) (χ : Gn g n → ℂ)
    (Λ : Gn g c → Gn g d → ℂ) :
    mean (fun p : Gn g c × Gn g d => Λ p.1 p.2 * res c d χ p.1 p.2) =
      ((Finset.univ.filter fun x : Gn g n => InPar c (x : Mt g n)).card : ℂ)⁻¹ * ∑ x : Gn g n,
        if InPar c (x : Mt g n) then Λ (toG (tl c (x : Mt g n))) (toG (br c d (x : Mt g n))) * χ x else 0 := by
  obtain ⟨-, -, hu, -, -, hcard⟩ := GlobalTheory.T.blockParabolic_unitriangular_subgroups_GLnPrimeField g c d n hn
  have key : ∀ x : Gn g n, (∑ p : Gn g c × Gn g d, Λ p.1 p.2 *
      (if InPar c (x : Mt g n) ∧ tl c (x : Mt g n) = (p.1 : Mt g c) ∧ br c d (x : Mt g n) = (p.2 : Mt g d)
        then χ x else 0)) =
      if InPar c (x : Mt g n) then Λ (toG (tl c (x : Mt g n))) (toG (br c d (x : Mt g n))) * χ x else 0 := by
    intro x
    by_cases hx : InPar c (x : Mt g n)
    · obtain ⟨h1, h2⟩ := hu x hx
      rw [if_pos hx, Finset.sum_eq_single (toG (tl c (x : Mt g n)), toG (br c d (x : Mt g n)))]
      · rw [if_pos ⟨hx, (coe_toG h1).symm, (coe_toG h2).symm⟩]
      · intro p _ hp
        rw [if_neg, mul_zero]
        rintro ⟨-, e1, e2⟩
        apply hp
        rw [e1, e2, toG_coe, toG_coe]
      · intro h; exact absurd (Finset.mem_univ _) h
    · simp [hx]
  unfold mean res
  rw [hcard]
  simp only [← key]
  rw [Finset.sum_comm (γ := Gn g n), Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← Finset.mul_sum, Fintype.card_prod]
  push_cast
  rw [mul_inv (_ * _)]
  ring

theorem eq_of_mean (G₁ G₂ : Type) [Group G₁] [Group G₂] [Fintype G₁] [Fintype G₂] (A B : G₁ → G₂ → ℂ)
    (hA1 : ∀ y, IsClass fun x => A x y) (hA2 : ∀ x, IsClass (A x)) (hB1 : ∀ y, IsClass fun x => B x y)
    (hB2 : ∀ x, IsClass (B x))
    (h : ∀ Λ : G₁ → G₂ → ℂ, (∀ y, IsClass fun x => Λ x y) → (∀ x, IsClass (Λ x)) →
      mean (fun p : G₁ × G₂ => Λ p.1 p.2 * A p.1 p.2) = mean (fun p : G₁ × G₂ => Λ p.1 p.2 * B p.1 p.2)) :
    A = B := by
  have h0 := h (fun x y => (starRingEnd ℂ) (A x y - B x y))
    (fun y x z => by
      have e1 := hA1 y x z
      have e2 := hB1 y x z
      simp only at e1 e2 ⊢
      rw [e1, e2])
    (fun x y z => by
      simp only
      rw [hA2 x y z, hB2 x y z])
  unfold mean at h0
  have h3 : (Fintype.card (G₁ × G₂) : ℂ)⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast Fintype.card_ne_zero)
  have h1 := sub_eq_zero.mpr (mul_left_cancel₀ h3 h0)
  rw [← Finset.sum_sub_distrib] at h1
  have h2 : ∑ p : G₁ × G₂, Complex.normSq (A p.1 p.2 - B p.1 p.2) = 0 := by
    apply Complex.ofReal_injective
    rw [Complex.ofReal_sum, Complex.ofReal_zero, ← h1]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Complex.normSq_eq_conj_mul_self]; ring
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Complex.normSq_nonneg _)] at h2
  funext x y
  exact sub_eq_zero.mp (Complex.normSq_eq_zero.mp (h2 (x, y) (Finset.mem_univ _)))

theorem reciprocity : ∀ (g : ℕ) [Fact g.Prime] , (∀ (a b n : ℕ), n = a + b → ∀ (χ : Gn g n → ℂ) (Φ : Gn g a → Gn g b → ℂ), IsClass χ → mean (fun x => χ x * hcT a b Φ n x) = mean (fun p : Gn g a × Gn g b => res a b χ p.1 p.2 * Φ p.1 p.2)) ∧ (∀ (c d n : ℕ), n = c + d → ∀ (χ : Gn g n → ℂ) (Λ : Gn g c → Gn g d → ℂ), mean (fun p : Gn g c × Gn g d => Λ p.1 p.2 * res c d χ p.1 p.2) = ((Finset.univ.filter fun x : Gn g n => InPar c (x : Mt g n)).card : ℂ)⁻¹ * ∑ x : Gn g n, if InPar c (x : Mt g n) then Λ (toG (tl c (x : Mt g n))) (toG (br c d (x : Mt g n))) * χ x else 0) ∧ ∀ (G₁ G₂ : Type) [Group G₁] [Group G₂] [Fintype G₁] [Fintype G₂] (A B : G₁ → G₂ → ℂ), (∀ y, IsClass fun x => A x y) → (∀ x, IsClass (A x)) → (∀ y, IsClass fun x => B x y) → (∀ x, IsClass (B x)) → (∀ Λ : G₁ → G₂ → ℂ, (∀ y, IsClass fun x => Λ x y) → (∀ x, IsClass (Λ x)) → mean (fun p : G₁ × G₂ => Λ p.1 p.2 * A p.1 p.2) = mean (fun p : G₁ × G₂ => Λ p.1 p.2 * B p.1 p.2)) → A = B := by
  intro g _
  refine ⟨?_, mean_res g, eq_of_mean⟩
  intro a b n hn χ Φ hχ
  have h1 := mean_res g a b n hn χ Φ
  have h2 := mean_conj χ (fun x : Gn g n => if InPar a (x : Mt g n) then
    Φ (toG (tl a (x : Mt g n))) (toG (br a b (x : Mt g n))) else 0) hχ
    ((Finset.univ.filter fun x : Gn g n => InPar a (x : Mt g n)).card : ℂ)⁻¹
  simp only [ite_mul, zero_mul] at h2
  rw [← h1] at h2
  simp only [mul_comm (res a b χ _ _)]
  exact h2

end GlobalTheory.GLm.Recip
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraInductionRestrictionIsClassFunctionStatement

section

@[expose] public section

open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

theorem _root_.GlobalTheory.T.harishChandra_induction_restriction_isClassFunction : ∀ (g : ℕ) [Fact g.Prime] (a b n : ℕ), n = a + b → (∀ Φ : Gn g a → Gn g b → ℂ, IsClass (hcT a b Φ n)) ∧ ∀ χ : Gn g n → ℂ, IsClass χ → (∀ h, IsClass (res a b χ h)) ∧ ∀ h, IsClass (fun x => res a b χ x h) := by
  first | exact @GlobalTheory.GLq.HcClass.hc_class | exact GlobalTheory.GLq.HcClass.hc_class | (intros; apply GlobalTheory.GLq.HcClass.hc_class <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MackeyFormulaHarishChandraRestrictionInduction

section

@[expose] public section

noncomputable section

namespace GlobalTheory.GLq.Mackey

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

variable {g : ℕ} [Fact g.Prime]

theorem blocks_conj (a b n : ℕ) (hn : n = a + b) (P : Subgroup (Gn g n))
    (hP : ∀ x, x ∈ P ↔ InPar a (x : Mt g n)) (Λ : Gn g a → Gn g b → ℂ)
    (h1 : ∀ y, IsClass fun x => Λ x y) (h2 : ∀ x, IsClass (Λ x)) :
    ∀ h ∈ P, ∀ x ∈ P, Λ (toG (tl a ((h * x * h⁻¹ : Gn g n) : Mt g n))) (toG (br a b ((h * x * h⁻¹ : Gn g n) : Mt g n)))
      = Λ (toG (tl a (x : Mt g n))) (toG (br a b (x : Mt g n))) := by
  obtain ⟨-, -, hu, hmul, -, -⟩ := GlobalTheory.GLm.ParBasic.par_basic g a b n hn
  let f₁ : P →* Gn g a := MonoidHom.mk' (fun p => toG (tl a ((p : Gn g n) : Mt g n))) (by
    intro p q
    have hp : InPar a ((p : Gn g n) : Mt g n) := (hP p).1 p.2
    have hq : InPar a ((q : Gn g n) : Mt g n) := (hP q).1 q.2
    apply Units.ext
    rw [Subgroup.coe_mul, Units.val_mul, (hmul _ _ hp hq).1, Units.val_mul,
      Recip.coe_toG ((hu _ hp).1.mul (hu _ hq).1), Recip.coe_toG (hu _ hp).1, Recip.coe_toG (hu _ hq).1])
  let f₂ : P →* Gn g b := MonoidHom.mk' (fun p => toG (br a b ((p : Gn g n) : Mt g n))) (by
    intro p q
    have hp : InPar a ((p : Gn g n) : Mt g n) := (hP p).1 p.2
    have hq : InPar a ((q : Gn g n) : Mt g n) := (hP q).1 q.2
    apply Units.ext
    rw [Subgroup.coe_mul, Units.val_mul, (hmul _ _ hp hq).2, Units.val_mul,
      Recip.coe_toG ((hu _ hp).2.mul (hu _ hq).2), Recip.coe_toG (hu _ hp).2, Recip.coe_toG (hu _ hq).2])
  intro h hh x hx
  have E1 : toG (tl a ((h * x * h⁻¹ : Gn g n) : Mt g n)) = f₁ ⟨h, hh⟩ * f₁ ⟨x, hx⟩ * (f₁ ⟨h, hh⟩)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul]; rfl
  have E2 : toG (br a b ((h * x * h⁻¹ : Gn g n) : Mt g n)) = f₂ ⟨h, hh⟩ * f₂ ⟨x, hx⟩ * (f₂ ⟨h, hh⟩)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul]; rfl
  rw [E1, E2]
  exact (h2 _ _ _).trans (h1 _ _ _)

theorem mean_prod_right {A B : Type} [Fintype A] [Fintype B] (F : A → B → ℂ) :
    mean (fun p : A × B => F p.1 p.2) = mean (fun b => mean (fun a => F a b)) := by
  unfold mean
  rw [Fintype.sum_prod_type_right, Fintype.card_prod]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  push_cast; rw [mul_inv]; ring

theorem mean_prod_left {A B : Type} [Fintype A] [Fintype B] (F : A → B → ℂ) :
    mean (fun p : A × B => F p.1 p.2) = mean (fun a => mean (fun b => F a b)) := by
  unfold mean
  rw [Fintype.sum_prod_type, Fintype.card_prod]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  push_cast; rw [mul_inv]; ring

theorem mean_swap {A B : Type} [Fintype A] [Fintype B] (F : A → B → ℂ) :
    mean (fun b => mean (fun a => F a b)) = mean (fun a => mean (fun b => F a b)) := by
  rw [← mean_prod_right, mean_prod_left]

theorem mean_equiv {A B : Type} [Fintype A] [Fintype B] (e : A ≃ B) (F : B → ℂ) :
    mean (fun x => F (e x)) = mean F := by
  unfold mean
  rw [Fintype.card_congr e, Equiv.sum_comp e F]

theorem mean_sum {A ι : Type} [Fintype A] (R : Finset ι) (Λ : A → ℂ) (T : ι → A → ℂ) :
    mean (fun p => Λ p * ∑ i ∈ R, T i p) = ∑ i ∈ R, mean (fun p => Λ p * T i p) := by
  unfold mean
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]

theorem res_comm {p q r s m k : ℕ} (Λ : Gn g m → Gn g k → ℂ) (y₁ : Gn g p) (y₃ : Gn g q) (y₂ : Gn g r)
    (y₄ : Gn g s) :
    res r s (fun h₂ => res p q (fun x => Λ x h₂) y₁ y₃) y₂ y₄ =
      res p q (fun z => res r s (Λ z) y₂ y₄) y₁ y₃ := by
  unfold res
  simp only [← Finset.sum_filter, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun z _ => ?_
  ring

theorem left_side (a b c d n : ℕ) (hn1 : n = a + b) (hn2 : n = c + d) (Φ : Gn g a → Gn g b → ℂ)
    (hΦ1 : ∀ y, IsClass fun x => Φ x y) (hΦ2 : ∀ x, IsClass (Φ x))
    (Λ : Gn g c → Gn g d → ℂ) (hΛ1 : ∀ y, IsClass fun x => Λ x y) (hΛ2 : ∀ x, IsClass (Λ x)) :
    mean (fun p : Gn g c × Gn g d => Λ p.1 p.2 * res c d (hcT a b Φ n) p.1 p.2) =
      ∑ i ∈ (Finset.range (a + 1)).filter (fun i => i ≤ c ∧ c - i ≤ b),
        mean (fun y : (Gn g i × Gn g (a - i)) × (Gn g (c - i) × Gn g (b - (c - i))) =>
          res i (c - i) (fun z => res (a - i) (b - (c - i)) (Λ z) y.1.2 y.2.2) y.1.1 y.2.1 *
            res i (a - i) (fun x => res (c - i) (b - (c - i)) (Φ x) y.2.1 y.2.2) y.1.1 y.1.2) := by
  obtain ⟨-, R2, -⟩ := Recip.reciprocity g
  obtain ⟨⟨Pc, hPc⟩, -, -, -, -, -⟩ := GlobalTheory.GLm.ParBasic.par_basic g c d n hn2
  obtain ⟨⟨Pa, hPa⟩, -, -, -, -, -⟩ := GlobalTheory.GLm.ParBasic.par_basic g a b n hn1
  have hR : ∀ x : Gn g n, ∃! i, i ∈ (Finset.range (a + 1)).filter (fun i => i ≤ c ∧ c - i ≤ b) ∧
      ∃ h ∈ Pc, ∃ k ∈ Pa, x = h * wI g a c i n * k := by
    intro x
    obtain ⟨i, ⟨hi, p, q, hp, hq, e⟩, hu⟩ := GlobalTheory.GLm.ParCoset.doubleCoset g a b c d n hn1 hn2 x
    refine ⟨i, ⟨hi, p, (hPc p).2 hp, q, (hPa q).2 hq, e⟩, ?_⟩
    rintro j ⟨hj, h, hh, k, hk, e'⟩
    exact hu j ⟨hj, h, k, (hPc h).1 hh, (hPa k).1 hk, e'⟩
  have hm := mackey_doubleCoset_pairing (Gn g n) Pc Pa ℕ
    ((Finset.range (a + 1)).filter (fun i => i ≤ c ∧ c - i ≤ b)) (fun i => wI g a c i n) hR
    (fun x => Λ (toG (tl c (x : Mt g n))) (toG (br c d (x : Mt g n))))
    (fun z => Φ (toG (tl a (z : Mt g n))) (toG (br a b (z : Mt g n))))
    (blocks_conj c d n hn2 Pc hPc Λ hΛ1 hΛ2) (blocks_conj a b n hn1 Pa hPa Φ hΦ1 hΦ2)
  have cc : ∀ (P : Subgroup (Gn g n)) (Q : Gn g n → Prop), (∀ x, x ∈ P ↔ Q x) →
      Nat.card P = (Finset.univ.filter Q).card := by
    intro P Q hP
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext x
    simp [hP]
  rw [cc Pc _ hPc, cc Pa _ hPa] at hm
  simp only [hPc, hPa] at hm
  rw [R2 c d n hn2]
  unfold hcT
  rw [hm]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp only [Finset.mem_filter, Finset.mem_range] at hi
  exact mackey_cell_term g a b c d n i hn1 hn2 (by omega) hi.2.1 hi.2.2 Λ Φ

theorem right_term (a b c d n i : ℕ) (hn1 : n = a + b) (hn2 : n = c + d) (hia : i ≤ a) (hic : i ≤ c)
    (hcb : c - i ≤ b) (Φ : Gn g a → Gn g b → ℂ) (Λ : Gn g c → Gn g d → ℂ)
    (hΛ1 : ∀ y, IsClass fun x => Λ x y) (hΛ2 : ∀ x, IsClass (Λ x)) :
    mean (fun p : Gn g c × Gn g d => Λ p.1 p.2 * hcT i (c - i) (fun y₁ y₃ => hcT (a - i) (b - (c - i))
      (fun y₂ y₄ => res i (a - i) (fun x => res (c - i) (b - (c - i)) (Φ x) y₃ y₄) y₁ y₂) d p.2) c p.1) =
    mean (fun y : (Gn g i × Gn g (a - i)) × (Gn g (c - i) × Gn g (b - (c - i))) =>
      res i (c - i) (fun z => res (a - i) (b - (c - i)) (Λ z) y.1.2 y.2.2) y.1.1 y.2.1 *
        res i (a - i) (fun x => res (c - i) (b - (c - i)) (Φ x) y.2.1 y.2.2) y.1.1 y.1.2) := by
  have hc : c = i + (c - i) := by omega
  have hd : d = (a - i) + (b - (c - i)) := by omega
  obtain ⟨R1, -, -⟩ := Recip.reciprocity g
  rw [mean_prod_right (fun (h₁ : Gn g c) (h₂ : Gn g d) => Λ h₁ h₂ * hcT i (c - i) (fun y₁ y₃ => hcT (a - i) (b - (c - i))
      (fun y₂ y₄ => res i (a - i) (fun x => res (c - i) (b - (c - i)) (Φ x) y₃ y₄) y₁ y₂) d h₂) c h₁)]
  calc _ = mean (fun h₂ : Gn g d => mean (fun q : Gn g i × Gn g (c - i) =>
          res i (c - i) (fun x => Λ x h₂) q.1 q.2 * hcT (a - i) (b - (c - i))
            (fun y₂ y₄ => res i (a - i) (fun x => res (c - i) (b - (c - i)) (Φ x) q.2 y₄) q.1 y₂) d h₂)) := by
        congr 1; funext h₂
        exact R1 i (c - i) c hc (fun x => Λ x h₂) _ (hΛ1 h₂)
    _ = mean (fun q : Gn g i × Gn g (c - i) => mean (fun h₂ : Gn g d =>
          res i (c - i) (fun x => Λ x h₂) q.1 q.2 * hcT (a - i) (b - (c - i))
            (fun y₂ y₄ => res i (a - i) (fun x => res (c - i) (b - (c - i)) (Φ x) q.2 y₄) q.1 y₂) d h₂)) :=
        mean_swap _
    _ = mean (fun q : Gn g i × Gn g (c - i) => mean (fun r : Gn g (a - i) × Gn g (b - (c - i)) =>
          res (a - i) (b - (c - i)) (fun h₂ => res i (c - i) (fun x => Λ x h₂) q.1 q.2) r.1 r.2 *
            res i (a - i) (fun x => res (c - i) (b - (c - i)) (Φ x) q.2 r.2) q.1 r.1)) := by
        congr 1; funext q
        refine R1 (a - i) (b - (c - i)) d hd _ _ ?_
        intro x y
        show res i (c - i) (fun z => Λ z (y * x * y⁻¹)) q.1 q.2 = res i (c - i) (fun z => Λ z x) q.1 q.2
        rw [show (fun z => Λ z (y * x * y⁻¹)) = (fun z => Λ z x) from funext fun z => hΛ2 z x y]
    _ = mean (fun w : (Gn g i × Gn g (c - i)) × (Gn g (a - i) × Gn g (b - (c - i))) =>
          res (a - i) (b - (c - i)) (fun h₂ => res i (c - i) (fun x => Λ x h₂) w.1.1 w.1.2) w.2.1 w.2.2 *
            res i (a - i) (fun x => res (c - i) (b - (c - i)) (Φ x) w.1.2 w.2.2) w.1.1 w.2.1) :=
        (mean_prod_left (fun (q : Gn g i × Gn g (c - i)) (r : Gn g (a - i) × Gn g (b - (c - i))) =>
          res (a - i) (b - (c - i)) (fun h₂ => res i (c - i) (fun x => Λ x h₂) q.1 q.2) r.1 r.2 *
            res i (a - i) (fun x => res (c - i) (b - (c - i)) (Φ x) q.2 r.2) q.1 r.1)).symm
    _ = _ := by
        rw [← mean_equiv (Equiv.prodProdProdComm (Gn g i) (Gn g (a - i)) (Gn g (c - i)) (Gn g (b - (c - i))))]
        congr 1; funext y
        simp only [Equiv.prodProdProdComm_apply]
        rw [res_comm]

theorem mackey_formula : ∀ (g : ℕ) [Fact g.Prime] (a b c d n : ℕ), n = a + b → n = c + d →
    ∀ Φ : Gn g a → Gn g b → ℂ, (∀ y, IsClass fun x => Φ x y) → (∀ x, IsClass (Φ x)) → ∀ h₁ h₂,
      res c d (hcT a b Φ n) h₁ h₂ = ∑ i ∈ (Finset.range (a + 1)).filter (fun i => i ≤ c ∧ c - i ≤ b),
        hcT i (c - i) (fun y₁ y₃ => hcT (a - i) (b - (c - i)) (fun y₂ y₄ =>
          res i (a - i) (fun x => res (c - i) (b - (c - i)) (Φ x) y₃ y₄) y₁ y₂) d h₂) c h₁ := by
  intro g _ a b c d n hn1 hn2 Φ hΦ1 hΦ2 h₁ h₂
  obtain ⟨-, -, R3⟩ := Recip.reciprocity g
  have hcl : IsClass (hcT a b Φ n) := (GlobalTheory.T.harishChandra_induction_restriction_isClassFunction g a b n hn1).1 Φ
  have hres := (GlobalTheory.T.harishChandra_induction_restriction_isClassFunction g c d n hn2).2 _ hcl
  suffices H : (fun (h₁ : Gn g c) (h₂ : Gn g d) => res c d (hcT a b Φ n) h₁ h₂) =
      (fun (h₁ : Gn g c) (h₂ : Gn g d) => ∑ i ∈ (Finset.range (a + 1)).filter (fun i => i ≤ c ∧ c - i ≤ b),
        hcT i (c - i) (fun y₁ y₃ => hcT (a - i) (b - (c - i)) (fun y₂ y₄ =>
          res i (a - i) (fun x => res (c - i) (b - (c - i)) (Φ x) y₃ y₄) y₁ y₂) d h₂) c h₁) from
    congrFun (congrFun H h₁) h₂
  refine R3 (Gn g c) (Gn g d) _ _ hres.2 hres.1 ?_ ?_ ?_
  · intro y x z
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    exact (GlobalTheory.T.harishChandra_induction_restriction_isClassFunction g i (c - i) c (by omega)).1 _ x z
  · intro x y z
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    have hd' : ∀ Ψ, hcT (a - i) (b - (c - i)) Ψ d (z * y * z⁻¹) = hcT (a - i) (b - (c - i)) Ψ d y :=
      fun Ψ => (GlobalTheory.T.harishChandra_induction_restriction_isClassFunction g (a - i) (b - (c - i)) d (by omega)).1 Ψ y z
    simp only [hd']
  · intro Λ hΛ1 hΛ2
    rw [left_side a b c d n hn1 hn2 Φ hΦ1 hΦ2 Λ hΛ1 hΛ2, mean_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    exact (right_term a b c d n i hn1 hn2 (by omega) hi.2.1 hi.2.2 Φ Λ hΛ1 hΛ2).symm

end GlobalTheory.GLq.Mackey
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MackeyFormulaHarishChandraRestrictionInductionStatement

section

@[expose] public section

open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

theorem _root_.GlobalTheory.T.mackey_formula_harishChandra_restriction_induction : ∀ (g : ℕ) [Fact g.Prime] (a b c d n : ℕ), n = a + b → n = c + d → ∀ Φ : Gn g a → Gn g b → ℂ, (∀ y, IsClass fun x => Φ x y) → (∀ x, IsClass (Φ x)) → ∀ h₁ h₂, res c d (hcT a b Φ n) h₁ h₂ = ∑ i ∈ (Finset.range (a + 1)).filter (fun i => i ≤ c ∧ c - i ≤ b), hcT i (c - i) (fun y₁ y₃ => hcT (a - i) (b - (c - i)) (fun y₂ y₄ => res i (a - i) (fun x => res (c - i) (b - (c - i)) (Φ x) y₃ y₄) y₁ y₂) d h₂) c h₁ := by
  first | exact @GlobalTheory.GLq.Mackey.mackey_formula | exact GlobalTheory.GLq.Mackey.mackey_formula | (intros; apply GlobalTheory.GLq.Mackey.mackey_formula <;> assumption)
end
end
