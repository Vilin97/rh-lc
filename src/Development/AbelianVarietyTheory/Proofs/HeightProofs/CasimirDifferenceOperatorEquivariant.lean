module

public import Development.AbelianVarietyTheory.Proofs.HeightProofs.InnerDRepSq
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.InvSqrtTwo
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.OrthonormalBasesMemUnitaryLieAlgebraStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.ENatToNat
import Std.Tactic.BVDecide.Normalize.Bool
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.SignatureLieSetExpandOrthonormalBasesStatement
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.SkewHermitianOrthonormalBasisTraceOrthonormalStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.HeightProofs.ReTraceHermitianOrthonormalBasisMulEqIte

section

@[expose] public section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.TypeSum.CasBasis GlobalTheory.LowTypeDetermined

noncomputable section

namespace GlobalTheory.TypeSum.CasBasis.PB

variable {n : ℕ}

theorem tr_unit (a b c d : Fin n) :
    trace (unitE a b * unitE c d) = if b = c ∧ d = a then 1 else 0 := by
  by_cases hbc : b = c
  · subst hbc
    rw [unitE, unitE, Matrix.single_mul_single_same, one_mul]
    by_cases hda : d = a
    · subst hda; simp [Matrix.trace_single_eq_same]
    · rw [Matrix.trace_single_eq_of_ne (h := Ne.symm hda)]; simp [hda]
  · rw [unitE, unitE, Matrix.single_mul_single_of_ne _ _ _ _ hbc]; simp [hbc]

theorem sq_inv : invSqrtTwo * invSqrtTwo = (1 / 2 : ℂ) := by
  rw [invSqrtTwo, ← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  push_cast; ring

def B (X Y : Mx n) : ℝ := (trace (X * Y)).re

theorem B_comm (X Y : Mx n) : B X Y = B Y X := by
  simp only [B, Matrix.trace_mul_comm X Y]

def f (p : Fin n × Fin n) : List (Mx n) :=
  [invSqrtTwo • (unitE p.1 p.2 + unitE p.2 p.1), (invSqrtTwo * Complex.I) • (unitE p.1 p.2 - unitE p.2 p.1)]

theorem pList_eq (ε : Fin n → Bool) : pList ε = (pairs ε false).flatMap f := rfl

theorem mem_pairs' {ε : Fin n → Bool} {p : Fin n × Fin n} (h : p ∈ pairs ε false) : p.1 < p.2 := by
  simp only [pairs, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2.1

theorem nodup_pairs (ε : Fin n → Bool) : (pairs ε false).Nodup :=
  (List.Nodup.product (List.nodup_finRange n) (List.nodup_finRange n)).filter _

theorem norm_one {a b : Fin n} (hab : a < b) : ∀ X ∈ f (a, b), B X X = 1 := by
  have h1 : a ≠ b := hab.ne
  have h2 : b ≠ a := hab.ne'
  intro X hX
  simp only [f, List.mem_cons, List.not_mem_nil, or_false] at hX
  rcases hX with rfl | rfl
  · simp only [B, smul_mul_smul_comm, Matrix.trace_smul, mul_add, add_mul, Matrix.trace_add, tr_unit,
      h1, h2, and_self, and_false, false_and, if_true, if_false, sq_inv, smul_eq_mul]
    norm_num
  · simp only [B, smul_mul_smul_comm, Matrix.trace_smul, mul_sub, sub_mul, Matrix.trace_sub, tr_unit,
      h1, h2, and_self, and_false, false_and, if_true, if_false, smul_eq_mul]
    have : invSqrtTwo * Complex.I * (invSqrtTwo * Complex.I) = -(1 / 2 : ℂ) := by
      rw [show invSqrtTwo * Complex.I * (invSqrtTwo * Complex.I) = invSqrtTwo * invSqrtTwo * (Complex.I * Complex.I) by ring,
        sq_inv, Complex.I_mul_I]; ring
    rw [this]; norm_num

theorem within {a b : Fin n} (hab : a < b) : (f (a, b)).Pairwise fun X Y => B X Y = 0 := by
  have h1 : a ≠ b := hab.ne
  have h2 : b ≠ a := hab.ne'
  simp only [f, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
    List.Pairwise.nil, and_true, IsEmpty.forall_iff, implies_true]
  simp only [B, smul_mul_smul_comm, Matrix.trace_smul, mul_sub, add_mul, Matrix.trace_sub, Matrix.trace_add, tr_unit,
    h1, h2, and_self, and_false, false_and, if_true, if_false, smul_eq_mul]
  simp

theorem across {a b c d : Fin n} (hab : a < b) (hcd : c < d) (hne : (a, b) ≠ (c, d)) :
    ∀ X ∈ f (a, b), ∀ Y ∈ f (c, d), B X Y = 0 := by
  have e1 : ¬ (b = c ∧ d = a) := by rintro ⟨rfl, rfl⟩; exact lt_asymm hab hcd
  have e2 : ¬ (b = d ∧ c = a) := by rintro ⟨rfl, rfl⟩; exact hne rfl
  have e3 : ¬ (a = c ∧ d = b) := by rintro ⟨rfl, rfl⟩; exact hne rfl
  have e4 : ¬ (a = d ∧ c = b) := by rintro ⟨rfl, rfl⟩; exact lt_asymm hab hcd
  intro X hX Y hY
  simp only [f, List.mem_cons, List.not_mem_nil, or_false] at hX hY
  rcases hX with rfl | rfl <;> rcases hY with rfl | rfl <;>
  simp only [B, smul_mul_smul_comm, Matrix.trace_smul, mul_sub, sub_mul, mul_add, add_mul, Matrix.trace_sub,
    Matrix.trace_add, tr_unit, e1, e2, e3, e4, if_false, sub_zero, add_zero, smul_zero, Complex.zero_re]

theorem pairwise_pList (ε : Fin n → Bool) : (pList ε).Pairwise fun X Y => B X Y = 0 := by
  rw [pList_eq, List.pairwise_flatMap]
  refine ⟨fun p hp => ?_, ?_⟩
  · obtain ⟨a, b⟩ := p
    exact within (mem_pairs' hp)
  · refine (nodup_pairs ε).imp_of_mem fun {p q} hp hq hne => ?_
    obtain ⟨a, b⟩ := p
    obtain ⟨c, d⟩ := q
    exact across (mem_pairs' hp) (mem_pairs' hq) hne

theorem norm_pList (ε : Fin n → Bool) : ∀ X ∈ pList ε, B X X = 1 := by
  intro X hX
  rw [pList_eq, List.mem_flatMap] at hX
  obtain ⟨⟨a, b⟩, hp, hX⟩ := hX
  exact norm_one (mem_pairs' hp) X hX

end GlobalTheory.TypeSum.CasBasis.PB

namespace GlobalTheory.TypeSum.CasBasis

theorem pB_orthonormal : ∀ (n : ℕ) (ε : Fin n → Bool) (a b : Fin (pList ε).length),
    (trace (pB ε a * pB ε b)).re = if a = b then 1 else 0 := by
  intro n ε a b
  have hpw := List.pairwise_iff_get.1 (PB.pairwise_pList ε)
  show PB.B (pB ε a) (pB ε b) = _
  rcases lt_trichotomy a b with h | rfl | h
  · rw [if_neg h.ne]; exact hpw a b h
  · rw [if_pos rfl]; exact PB.norm_pList ε _ (List.get_mem _ _)
  · rw [if_neg h.ne', PB.B_comm]; exact hpw b a h

end GlobalTheory.TypeSum.CasBasis

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.HeightProofs.ReTraceHermitianOrthonormalBasisMulEqIteStatement

section

@[expose] public section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.TypeSum.CasBasis GlobalTheory.LowTypeDetermined

theorem _root_.GlobalTheory.T.re_trace_hermitianOrthonormalBasis_mul_eq_ite : ∀ (n : ℕ) (ε : Fin n → Bool) (a b : Fin (pList ε).length), (trace (pB ε a * pB ε b)).re = if a = b then 1 else 0 := by
  first | exact @GlobalTheory.TypeSum.CasBasis.pB_orthonormal | exact GlobalTheory.TypeSum.CasBasis.pB_orthonormal | (intros; apply GlobalTheory.TypeSum.CasBasis.pB_orthonormal <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.HeightProofs.ReTraceSkewHermitianMulHermitianOrthonormalBasis

section

@[expose] public section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.TypeSum.CasBasis GlobalTheory.LowTypeDetermined

namespace GlobalTheory.TypeSum.CasBasis

theorem unitE_apply_eq_zero_of_sign {n : ℕ} {ε : Fin n → Bool} {i j a b : Fin n}
    (h : (ε i = ε j) ≠ (ε a = ε b)) : unitE i j a b = 0 := by
  rw [unitE, Matrix.single_apply, if_neg]
  rintro ⟨rfl, rfl⟩
  exact h rfl

theorem kList_entry_zero {n : ℕ} {ε : Fin n → Bool} {X : Mx n} (hX : X ∈ kList ε) {a b : Fin n}
    (hab : ε a ≠ ε b) : X a b = 0 := by
  unfold kList at hX
  rcases List.mem_append.1 hX with h | h
  · obtain ⟨c, -, rfl⟩ := List.mem_map.1 h
    have h1 : unitE c c a b = 0 :=
      unitE_apply_eq_zero_of_sign (ε := ε) (by simp [hab])
    simp only [Matrix.smul_apply, h1, smul_zero]
  · obtain ⟨p, hp, hX⟩ := List.mem_flatMap.1 h
    have hpe : ε p.1 = ε p.2 := by
      have := (List.mem_filter.1 hp).2
      simp at this
      exact this.2
    have h1 : unitE p.1 p.2 a b = 0 :=
      unitE_apply_eq_zero_of_sign (ε := ε) (by simp [hab, hpe])
    have h2 : unitE p.2 p.1 a b = 0 :=
      unitE_apply_eq_zero_of_sign (ε := ε) (by simp [hab, hpe])
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hX
    rcases hX with rfl | rfl <;>
      simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, h1, h2, sub_zero, add_zero, smul_zero]

theorem pList_entry_zero {n : ℕ} {ε : Fin n → Bool} {Y : Mx n} (hY : Y ∈ pList ε) {a b : Fin n}
    (hab : ε a = ε b) : Y a b = 0 := by
  unfold pList at hY
  obtain ⟨p, hp, hY⟩ := List.mem_flatMap.1 hY
  have hpe : ε p.1 ≠ ε p.2 := by
    have := (List.mem_filter.1 hp).2
    simp at this
    exact this.2
  have h1 : unitE p.1 p.2 a b = 0 :=
    unitE_apply_eq_zero_of_sign (ε := ε) (by simp [hab, hpe])
  have h2 : unitE p.2 p.1 a b = 0 :=
    unitE_apply_eq_zero_of_sign (ε := ε) (by simp [hab, Ne.symm hpe])
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hY
  rcases hY with rfl | rfl <;>
    simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, h1, h2, sub_zero, add_zero, smul_zero]

theorem re_trace_kB_mul_pB : ∀ (n : ℕ) (ε : Fin n → Bool) (i : Fin (kList ε).length) (b : Fin (pList ε).length),
    (trace (kB ε i * pB ε b)).re = 0 := by
  intro n ε i b
  have hX : kB ε i ∈ kList ε := List.get_mem _ _
  have hY : pB ε b ∈ pList ε := List.get_mem _ _
  have : trace (kB ε i * pB ε b) = 0 := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun c _ => ?_
    by_cases h : ε a = ε c
    · rw [pList_entry_zero hY h.symm, mul_zero]
    · rw [kList_entry_zero hX h, zero_mul]
  rw [this, Complex.zero_re]

end GlobalTheory.TypeSum.CasBasis
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.HeightProofs.ReTraceSkewHermitianMulHermitianOrthonormalBasisStatement

section

@[expose] public section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.TypeSum.CasBasis GlobalTheory.LowTypeDetermined

theorem _root_.GlobalTheory.T.re_trace_skewHermitian_mul_hermitianOrthonormalBasis : ∀ (n : ℕ) (ε : Fin n → Bool) (i : Fin (kList ε).length) (b : Fin (pList ε).length), (trace (kB ε i * pB ε b)).re = 0 := by
  first | exact @GlobalTheory.TypeSum.CasBasis.re_trace_kB_mul_pB | exact GlobalTheory.TypeSum.CasBasis.re_trace_kB_mul_pB | (intros; apply GlobalTheory.TypeSum.CasBasis.re_trace_kB_mul_pB <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.HeightProofs.CasimirDifferenceOperatorEquivariant

section

@[expose] public section

noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.TypeSum.CasBasis GlobalTheory.LowTypeDetermined
open scoped InnerProductSpace

namespace GlobalTheory.TypeSum.CasEquiv

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Mx n → (H →L[ℂ] H)}

abbrev trF (U V : Mx n) : ℝ := (trace (U * V)).re

theorem trF_sum_left {ι : Type} (s : Finset ι) (r : ι → ℝ) (Z : ι → Mx n) (V : Mx n) :
    trF (∑ c ∈ s, r c • Z c) V = ∑ c ∈ s, r c * trF (Z c) V := by
  simp [trF, Finset.sum_mul, Matrix.trace_sum, Complex.re_sum]

theorem trF_comm (U V : Mx n) : trF U V = trF V U := by
  simp only [trF, Matrix.trace_mul_comm U V]

theorem dRep_finsum (hσ : IsURepOn (UJset ε) σ) {Z : Mx n} (hZ : Z ∈ lieSet ε) {ι : Type} (s : Finset ι)
    (w : ι → H) (hw : ∀ i, Sm ε σ (w i)) : dRep σ Z (∑ i ∈ s, w i) = ∑ i ∈ s, dRep σ Z (w i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have := Dw_smul hσ (l := [Z]) (by simp [hZ]) (0 : ℂ) (x := 0) ((smooth (Jm ε) σ).zero_mem)
    simpa using this
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    exact Dw_add hσ (l := [Z]) (by simp [hZ]) (hw _) ((smooth (Jm ε) σ).sum_mem fun i _ => hw i)

variable [CompleteSpace H]

theorem dRep_sum_fin (h : Std ε σ) {ι : Type} [Fintype ι] {Z : ι → Mx n} (hZ : ∀ c, Z c ∈ lieSet ε) {w : H}
    (hw : Sm ε σ w) (a : ι → ℝ) : dRep σ (∑ c, a c • Z c) w = ∑ c, (a c : ℂ) • dRep σ (Z c) w := by
  let e := Fintype.equivFin ι
  have := h.dRep_sum (B := Z ∘ e.symm) (fun i => hZ _) hw (a ∘ e.symm)
  simpa only [Function.comp_apply, e.symm.sum_comp (fun c => a c • Z c),
    e.symm.sum_comp (fun c => (a c : ℂ) • dRep σ (Z c) w)] using this

theorem dRep_dRep_sum (h : Std ε σ) {ι : Type} [Fintype ι] {Z : ι → Mx n} (hZ : ∀ c, Z c ∈ lieSet ε) {v : H}
    (hv : Sm ε σ v) (a b : ι → ℝ) :
    dRep σ (∑ c, a c • Z c) (dRep σ (∑ d, b d • Z d) v) =
      ∑ c, ∑ d, ((a c * b d : ℝ) : ℂ) • dRep σ (Z c) (dRep σ (Z d) v) := by
  have hs : ∀ d, Sm ε σ (dRep σ (Z d) v) := fun d => dRep_mem (isUnit_Jm ε) h.1 hv (hZ d)
  have hw : Sm ε σ (∑ d, (b d : ℂ) • dRep σ (Z d) v) :=
    (smooth (Jm ε) σ).sum_mem fun d _ => (smooth (Jm ε) σ).smul_mem _ (hs d)
  rw [dRep_sum_fin h hZ hv b, dRep_sum_fin h hZ hw a]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [dRep_finsum h.1 (hZ c) _ _ fun d => (smooth (Jm ε) σ).smul_mem _ (hs d), Finset.smul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  have := Dw_smul h.1 (l := [Z c]) (by simp [hZ c]) (b d : ℂ) (hs d)
  rw [show dRep σ (Z c) ((b d : ℂ) • dRep σ (Z d) v) = (b d : ℂ) • dRep σ (Z c) (dRep σ (Z d) v) from this,
    smul_smul]
  push_cast; ring_nf

theorem trF_conj {g : Mx n} (hg : g ∈ UJset ε) (U V : Mx n) : trF (g⁻¹ * U * g) V = trF U (g * V * g⁻¹) := by
  unfold trF
  congr 1
  rw [show g⁻¹ * U * g * V = g⁻¹ * (U * g * V) by simp only [Matrix.mul_assoc], Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem trF_conj_conj {g : Mx n} (hg : g ∈ UJset ε) (U V : Mx n) :
    trF (g * U * g⁻¹) (g * V * g⁻¹) = trF U V := by
  unfold trF
  congr 1
  have e : g * U * g⁻¹ * (g * V * g⁻¹) = g * (U * V * g⁻¹) := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc g⁻¹ g, inv_mul_UJ hg, Matrix.one_mul]
  rw [e, Matrix.trace_mul_comm, Matrix.mul_assoc, inv_mul_UJ hg, Matrix.mul_one]

theorem conj_mem' {g : Mx n} (hg : g ∈ UJset ε) {X : Mx n} (hX : X ∈ lieSet ε) : g * X * g⁻¹ ∈ lieSet ε := by
  have := conj_mem_lie (isUnit_Jm ε) (inv_mem_UJ hg) hX
  rwa [Matrix.nonsing_inv_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 (isUnit_of_UJ hg))] at this

theorem coef_orth {ι : Type} [Fintype ι] [DecidableEq ι] {Z : ι → Mx n} {s : ι → ℝ} (hs : ∀ c, s c * s c = 1)
    (hO : ∀ c d, trF (Z c) (Z d) = if c = d then s c else 0)
    (hE : ∀ U ∈ lieSet ε, U = ∑ c, (s c * trF U (Z c)) • Z c) (hZ : ∀ c, Z c ∈ lieSet ε) {g : Mx n}
    (hg : g ∈ UJset ε) (d e : ι) :
    ∑ c, s c * (s d * trF (g⁻¹ * Z c * g) (Z d)) * (s e * trF (g⁻¹ * Z c * g) (Z e)) =
      if d = e then s d else 0 := by
  have h3 : ∑ c, s c * trF (Z c) (g * Z d * g⁻¹) * trF (Z c) (g * Z e * g⁻¹) =
      trF (g * Z d * g⁻¹) (g * Z e * g⁻¹) := by
    conv_rhs => rw [hE _ (conj_mem' hg (hZ d)), trF_sum_left]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [trF_comm (g * Z d * g⁻¹) (Z c)]
  rw [trF_conj_conj hg, hO] at h3
  simp only [trF_conj hg]
  calc _ = s d * s e * ∑ c, s c * trF (Z c) (g * Z d * g⁻¹) * trF (Z c) (g * Z e * g⁻¹) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun c _ => ?_; ring
    _ = _ := by
        rw [h3]; split_ifs with hde
        · subst hde; rw [mul_assoc, hs, mul_one]
        · simp

theorem sum_sq_conj (h : Std ε σ) {ι : Type} [Fintype ι] [DecidableEq ι] {Z : ι → Mx n} {s : ι → ℝ}
    (hs : ∀ c, s c * s c = 1) (hO : ∀ c d, trF (Z c) (Z d) = if c = d then s c else 0)
    (hE : ∀ U ∈ lieSet ε, U = ∑ c, (s c * trF U (Z c)) • Z c) (hZ : ∀ c, Z c ∈ lieSet ε) {g : Mx n}
    (hg : g ∈ UJset ε) {v : H} (hv : Sm ε σ v) :
    ∑ c, (s c : ℂ) • dRep σ (g⁻¹ * Z c * g) (dRep σ (g⁻¹ * Z c * g) v) =
      ∑ c, (s c : ℂ) • dRep σ (Z c) (dRep σ (Z c) v) := by
  set a : ι → ι → ℝ := fun c d => s d * trF (g⁻¹ * Z c * g) (Z d) with ha
  have hW : ∀ c, g⁻¹ * Z c * g = ∑ d, a c d • Z d := fun c =>
    hE _ (conj_mem_lie (isUnit_Jm ε) hg (hZ c))
  have key := coef_orth hs hO hE hZ hg
  calc _ = ∑ c, (s c : ℂ) • ∑ d, ∑ e, ((a c d * a c e : ℝ) : ℂ) • dRep σ (Z d) (dRep σ (Z e) v) :=
        Finset.sum_congr rfl fun c _ => by rw [hW c, dRep_dRep_sum h hZ hv]
    _ = ∑ d, ∑ e, ((∑ c, s c * a c d * a c e : ℝ) : ℂ) • dRep σ (Z d) (dRep σ (Z e) v) := by
        simp only [Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [Complex.ofReal_sum, Finset.sum_smul]
        refine Finset.sum_congr rfl fun c _ => ?_
        congr 1; push_cast; ring
    _ = _ := by
        simp only [ha, key]
        refine Finset.sum_congr rfl fun d _ => ?_
        simp [apply_ite]

omit [CompleteSpace H] in
theorem casOp_translate (hσ : IsURepOn (UJset ε) σ) {d e : ℕ} {X : Fin d → Mx n} {Y : Fin e → Mx n}
    (hX : ∀ i, X i ∈ lieSet ε) (hY : ∀ b, Y b ∈ lieSet ε) {g : Mx n} (hg : g ∈ UJset ε) {v : H} (hv : Sm ε σ v) :
    casOp σ X Y (σ g v) = σ g (casOp σ (fun i => g⁻¹ * X i * g) (fun b => g⁻¹ * Y b * g) v) := by
  have h : ∀ Z ∈ lieSet ε, dRep σ Z (dRep σ Z (σ g v)) = σ g (dRep σ (g⁻¹ * Z * g) (dRep σ (g⁻¹ * Z * g) v)) :=
    fun Z hZ => Dw_translate hσ hg hv (l := [Z, Z]) (by simp [hZ])

  simp only [casOp, h _ (hX _), h _ (hY _), map_sub, map_sum]

theorem kk_orth (n : ℕ) (ε : Fin n → Bool) (i j : Fin (kList ε).length) :
    (trace (kB ε i * kB ε j)).re = if i = j then -1 else 0 := GlobalTheory.T.skewHermitianOrthonormalBasis_trace_orthonormal n ε i j
theorem pp_orth (n : ℕ) (ε : Fin n → Bool) (a b : Fin (pList ε).length) :
    (trace (pB ε a * pB ε b)).re = if a = b then 1 else 0 := GlobalTheory.T.re_trace_hermitianOrthonormalBasis_mul_eq_ite n ε a b
theorem kp_orth (n : ℕ) (ε : Fin n → Bool) (i : Fin (kList ε).length) (b : Fin (pList ε).length) :
    (trace (kB ε i * pB ε b)).re = 0 := GlobalTheory.T.re_trace_skewHermitian_mul_hermitianOrthonormalBasis n ε i b
theorem expand (n : ℕ) (ε : Fin n → Bool) : ∀ U ∈ lieSet ε,
    U = ∑ b, (trace (U * pB ε b)).re • pB ε b - ∑ i, (trace (U * kB ε i)).re • kB ε i := GlobalTheory.T.signature_lieSet_expand_orthonormal_bases n ε

theorem casOp_equivariant : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∀ g ∈ UJset ε, ∀ v, Sm ε σ v →
      casOp σ (kB ε) (pB ε) (σ g v) = σ g (casOp σ (kB ε) (pB ε) v) := by
  intro n ε H _ _ _ σ h g hg v hv
  obtain ⟨hk, hp⟩ := GlobalTheory.T.orthonormalBases_mem_unitaryLieAlgebra n ε
  let Z : Fin (kList ε).length ⊕ Fin (pList ε).length → Mx n := Sum.elim (kB ε) (pB ε)
  let s : Fin (kList ε).length ⊕ Fin (pList ε).length → ℝ := Sum.elim (fun _ => -1) (fun _ => 1)
  have hs : ∀ c, s c * s c = 1 := by rintro (c | c) <;> simp [s]
  have hZ : ∀ c, Z c ∈ lieSet ε := by rintro (c | c); exacts [hk c, hp c]
  have hO : ∀ c d, trF (Z c) (Z d) = if c = d then s c else 0 := by
    rintro (c | c) (d | d)
    · simpa [Z, s] using kk_orth n ε c d
    · simpa [Z, s] using kp_orth n ε c d
    · simpa [Z, s, trF_comm] using kp_orth n ε d c
    · simpa [Z, s] using pp_orth n ε c d
  have hE : ∀ U ∈ lieSet ε, U = ∑ c, (s c * trF U (Z c)) • Z c := by
    intro U hU
    simp only [Fintype.sum_sum_type, Z, s, Sum.elim_inl, Sum.elim_inr, neg_one_mul, one_mul, neg_smul,
      Finset.sum_neg_distrib]
    conv_lhs => rw [expand n ε U hU]
    abel
  have := sum_sq_conj h hs hO hE hZ hg hv
  simp only [Fintype.sum_sum_type, Z, s, Sum.elim_inl, Sum.elim_inr, Complex.ofReal_neg, Complex.ofReal_one, neg_smul,
    one_smul, Finset.sum_neg_distrib] at this
  rw [casOp_translate h.1 hk hp hg hv]
  congr 1
  simp only [casOp, sub_eq_neg_add]
  exact this

end GlobalTheory.TypeSum.CasEquiv

end
end
end
