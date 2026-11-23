module

public import Development.AbelianVarietyTheory.Definitions.Jets.SameFns
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MinusHatsTaylorCoeffLeibnizRule
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormalFormProductSpanLeftMulClosedStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PlusHatsTaylorCoeffLeibnizRule
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Span.Defs
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.VecPolyMemSpanValues
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Development.AbelianVarietyTheory.Definitions.Jets.SameFns
import Formalism.FormalDegreeBessel.StatementWR
import Formalism.HermitianCurvature.StatementFr
import Formalism.HermitianCurvature.StatementI
import Formalism.HermitianCurvature.StatementR
import Formalism.HermitianCurvature.StatementWd
import Formalism.RealPlaceAnalysis.StatementA
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.MinusHatsTaylorCoeffLeibnizRuleStatement

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

theorem _root_.GlobalTheory.T.minusHats_taylorCoeff_leibniz_rule : ∀ (A : Type) [Ring A] [Algebra ℂ A] (r : ℕ) (L : LevelData A r), ∀ Y : ℂ, ∃ Xa Xr : ℕ → A, (∀ s : ℂ, L.Ahatv (Y - s) = ∑ j ∈ Finset.range (r + 2), s ^ j • Xa j) ∧ (∀ s : ℂ, L.R0v (Y - s) = ∑ j ∈ Finset.range (r + 2), s ^ j • Xr j) ∧ ∀ m : ℕ → A, MulRel L m → ∀ q, L.Ahatv Y * m q = ∑ j ∈ Finset.range (r + 2), m (q + j) * Xa j ∧ L.R0v Y * m q = ∑ j ∈ Finset.range (r + 2), m (q + j) * Xr j := by
  first | exact @GlobalTheory.HatNF.TaylorMinus.taylor_minus | exact GlobalTheory.HatNF.TaylorMinus.taylor_minus | (intros; apply GlobalTheory.HatNF.TaylorMinus.taylor_minus <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.PlusHatsTaylorCoeffLeibnizRuleStatement

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

theorem _root_.GlobalTheory.T.plusHats_taylorCoeff_leibniz_rule : ∀ (A : Type) [Ring A] [Algebra ℂ A] (r : ℕ) (L : LevelData A r), ∀ Y : ℂ, ∃ Xa Xr : ℕ → A, (∀ s : ℂ, L.Ahat (Y + s) = ∑ j ∈ Finset.range (r + 2), s ^ j • Xa j) ∧ (∀ s : ℂ, L.R0 (Y + s) = ∑ j ∈ Finset.range (r + 2), s ^ j • Xr j) ∧ ∀ m : ℕ → A, MulRel L m → ∀ q, L.Ahat Y * m q = ∑ j ∈ Finset.range (r + 2), m (q + j) * Xa j ∧ L.R0 Y * m q = ∑ j ∈ Finset.range (r + 2), m (q + j) * Xr j := by
  first | exact @GlobalTheory.HatTaylorPlus.taylor_plus | exact GlobalTheory.HatTaylorPlus.taylor_plus | (intros; apply GlobalTheory.HatTaylorPlus.taylor_plus <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.R0MemNfSpanOfHatHyp

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF.HatCommutators

section lists
variable {A : Type} [Ring A]

theorem comm_ofFn {n : ℕ} (f : Fin n → A) (a : A) (h : ∀ l, Commute a (f l)) :
    Commute a (List.ofFn f).prod := by
  apply Commute.list_prod_right
  intro x hx
  rw [List.mem_ofFn] at hx
  obtain ⟨l, rfl⟩ := hx
  exact h l

theorem ofFn_mul_inv : ∀ {n : ℕ} (f g : Fin n → A), (∀ l, f l * g l = 1) → (∀ l m, Commute (g l) (f m)) →
    (List.ofFn f).prod * (List.ofFn g).prod = 1
  | 0, _, _, _, _ => by simp
  | n + 1, f, g, h, hc => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons]
    have ih := ofFn_mul_inv (n := n) (fun i => f i.succ) (fun i => g i.succ)
      (fun l => h l.succ) (fun l m => hc l.succ m.succ)
    have hc' := comm_ofFn (fun i : Fin n => f i.succ) (g 0) (fun l => hc 0 l.succ)
    rw [mul_assoc, ← mul_assoc _ (g 0), ← hc'.eq, mul_assoc, ih, mul_one, h]

theorem star_ofFn [StarRing A] : ∀ {n : ℕ} (f g : Fin n → A), (∀ l, star (f l) = g l) →
    (∀ l m, Commute (g l) (g m)) → star (List.ofFn f).prod = (List.ofFn g).prod
  | 0, _, _, _, _ => by simp
  | n + 1, f, g, h, hc => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, star_mul]
    have ih := star_ofFn (n := n) (fun i => f i.succ) (fun i => g i.succ)
      (fun l => h l.succ) (fun l m => hc l.succ m.succ)
    have hc' := comm_ofFn (fun i : Fin n => g i.succ) (g 0) (fun l => hc 0 l.succ)
    rw [ih, h, hc'.eq]

end lists

variable {A : Type} [Ring A] [Algebra ℂ A]

section level
variable {r : ℕ} (L : LevelData A r)

theorem c_mem (l : Fin r) : L.c l ∈ L.fns := by simp [LevelData.fns]
theorem ci_mem (l : Fin r) : L.ci l ∈ L.fns := by simp [LevelData.fns]
theorem cb_mem (l : Fin r) : L.cb l ∈ L.fns := by simp [LevelData.fns]
theorem cbi_mem (l : Fin r) : L.cbi l ∈ L.fns := by simp [LevelData.fns]
theorem GG_mem : L.GG ∈ L.fns := by simp [LevelData.fns]

theorem fcomm {x y : A} (hx : x ∈ L.fns) (hy : y ∈ L.fns) : Commute x y := L.fns_comm x hx y hy

theorem comm_Dr {a : A} (h : ∀ g ∈ L.fns, Commute a g) : Commute a L.Dr :=
  comm_ofFn _ _ fun l => h _ (c_mem L l)
theorem comm_Drb {a : A} (h : ∀ g ∈ L.fns, Commute a g) : Commute a L.Drb :=
  comm_ofFn _ _ fun l => h _ (cb_mem L l)

theorem Dri_Dr : L.Dri * L.Dr = 1 :=
  ofFn_mul_inv _ _ L.ci_c fun l m => fcomm L (c_mem L l) (ci_mem L m)
theorem Drbi_Drb : L.Drbi * L.Drb = 1 :=
  ofFn_mul_inv _ _ L.cbi_cb fun l m => fcomm L (cb_mem L l) (cbi_mem L m)
theorem Dr_Drb : Commute L.Dr L.Drb :=
  comm_ofFn _ _ fun l => (comm_Dr L fun _ hg => fcomm L (cb_mem L l) hg).symm

end level

variable [StarRing A] {P : M.Par} (d : Q.NFData P A)

theorem mem_span {b h : A} (hb : b ∈ bmon d) (hh : h ∈ basics d) : b * h ∈ nfSpan d (basics d) 0 0 1 :=
  Submodule.subset_span ⟨b, hb, [h], rfl, by simpa using hh, by simp⟩

theorem kap_mem (f : M.Ty P → ℂ) : d.κ f ∈ bmon d :=
  Submonoid.subset_closure (Or.inl (Or.inl (Or.inr ⟨f, rfl⟩)))

theorem ssn_mem {l : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1)) : ssn d l ∈ bmon d :=
  Submonoid.subset_closure (Or.inl (Or.inr ⟨l, by simpa using hl, rfl⟩))

theorem star_ssn_mem {l : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1)) : star (ssn d l) ∈ bmon d :=
  Submonoid.subset_closure (Or.inr ⟨l, by simpa using hl, rfl⟩)

theorem rh_eq (hR : d.Rel) (y : ℂ) :
    rh d y = d.x y * d.L.R0 y +
      ∑ l ∈ Finset.Icc 1 (P.k - 1), ssn d l * (d.κ fun ρ => M.xEx P {l} ρ y) * d.L.Ahat y := by
  obtain ⟨-, hκ, hS, -⟩ := hR
  have hκ' : ∀ f, ∀ g ∈ d.L.fns, Commute (d.κ f) g := fun f g hg => hκ f g (Or.inl hg)
  have hS' : ∀ l, ∀ g ∈ d.L.fns, Commute (d.SS l) g := fun l g hg => hS l g (Or.inl (Or.inl hg))
  have h1 : d.L.Drb * (d.L.GG * d.x y) = d.x y * (d.L.Drb * d.L.GG) := by
    have := ((comm_Drb d.L (hκ' fun ρ => M.xC P ρ y)).mul_right (hκ' _ _ (GG_mem d.L))).eq
    rw [← mul_assoc]; exact this.symm
  have h2 : ∀ l, ssn d l * (d.κ fun ρ => M.xEx P {l} ρ y) * d.L.Ahat y =
      d.L.Drb * (d.SS l * (d.κ fun ρ => M.xEx P {l} ρ y)) * d.L.Ar y := by
    intro l
    have hc := ((comm_Dr d.L (hS' l)).mul_left (comm_Dr d.L (hκ' fun ρ => M.xEx P {l} ρ y))).eq
    calc _ = d.L.Drb * d.L.Dri * ((d.SS l * (d.κ fun ρ => M.xEx P {l} ρ y)) * d.L.Dr) * d.L.Ar y := by
          simp only [ssn, LevelData.Ahat, mul_assoc]
      _ = d.L.Drb * (d.L.Dri * d.L.Dr) * (d.SS l * (d.κ fun ρ => M.xEx P {l} ρ y)) * d.L.Ar y := by
          rw [hc]; simp only [mul_assoc]
      _ = _ := by rw [Dri_Dr, mul_one]
  simp only [h2]
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  change d.L.Drb * ((d.L.GG * d.x y * d.L.l0 y + d.weightedSumBis y) * d.L.Ar y + d.L.GG * d.x y * d.L.Br y) =
    d.x y * (d.L.Drb * d.L.GG * (d.L.l0 y * d.L.Ar y + d.L.Br y)) + d.L.Drb * d.weightedSumBis y * d.L.Ar y
  rw [← mul_assoc (d.x y), ← h1]
  noncomm_ring

theorem rhv_eq (hR : d.Rel) (hc : ∀ l, star (d.L.c l) = d.L.cb l) (hci : ∀ l, star (d.L.ci l) = d.L.cbi l)
    (y : ℂ) :
    rhv d y = d.x y * d.L.R0v y +
      ∑ l ∈ Finset.Icc 1 (P.k - 1), (d.κ fun ρ => M.xEx P {l} ρ y) * star (ssn d l) * d.L.Ahatv y := by
  obtain ⟨-, hκ, hS, -⟩ := hR
  have hκ' : ∀ f, ∀ g ∈ d.L.fns, Commute (d.κ f) g := fun f g hg => hκ f g (Or.inl hg)
  have hS' : ∀ l, ∀ g ∈ d.L.fns, Commute (d.SS l) g := fun l g hg => hS l g (Or.inl (Or.inl hg))
  have h1 : d.L.Dr * (d.L.GG * d.x y) = d.x y * (d.L.Dr * d.L.GG) := by
    have := ((comm_Dr d.L (hκ' fun ρ => M.xC P ρ y)).mul_right (hκ' _ _ (GG_mem d.L))).eq
    rw [← mul_assoc]; exact this.symm
  have s1 : star d.L.Drb = d.L.Dr :=
    star_ofFn _ _ (fun l => by rw [← hc, star_star]) fun l m => fcomm d.L (c_mem _ l) (c_mem _ m)
  have s2 : star d.L.Dri = d.L.Drbi :=
    star_ofFn _ _ hci fun l m => fcomm d.L (cbi_mem _ l) (cbi_mem _ m)
  have h2 : ∀ l, (d.κ fun ρ => M.xEx P {l} ρ y) * star (ssn d l) * d.L.Ahatv y =
      d.L.Dr * ((d.κ fun ρ => M.xEx P {l} ρ y) * star (d.SS l)) * d.L.Avr y := by
    intro l
    have hs : Commute (star (d.SS l)) d.L.Dr := by
      rw [← s1]; exact (comm_Drb d.L (hS' l)).star_star
    have hc := ((comm_Dr d.L (hκ' fun ρ => M.xEx P {l} ρ y)).mul_left hs).eq
    calc _ = (d.κ fun ρ => M.xEx P {l} ρ y) * star (d.SS l) * (d.L.Drbi * (d.L.Dr * d.L.Drb)) * d.L.Avr y := by
          simp only [ssn, LevelData.Ahatv, star_mul, s1, s2, mul_assoc]
      _ = (d.κ fun ρ => M.xEx P {l} ρ y) * star (d.SS l) * d.L.Dr * d.L.Avr y := by
          rw [(Dr_Drb d.L).eq, ← mul_assoc d.L.Drbi, Drbi_Drb, one_mul]
      _ = _ := by rw [hc]
  simp only [h2]
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  change d.L.Dr * ((d.L.GG * d.x y * d.L.m0 y + d.S12 y) * d.L.Avr y + d.L.GG * d.x y * d.L.Bvr y) =
    d.x y * (d.L.Dr * d.L.GG * (d.L.m0 y * d.L.Avr y + d.L.Bvr y)) + d.L.Dr * d.S12 y * d.L.Avr y
  rw [← mul_assoc (d.x y), ← h1]
  noncomm_ring

theorem xinv_mul (y : ℂ) (hy : ∀ ρ : M.Ty P, M.xC P ρ y ≠ 0) :
    (d.κ fun ρ => (M.xC P ρ y)⁻¹) * d.x y = 1 := by
  rw [Q.NFData.x, ← map_mul, ← map_one d.κ]
  congr 1
  funext ρ
  exact inv_mul_cancel₀ (hy ρ)

end GlobalTheory.HatNF.HatCommutators

namespace GlobalTheory.HatNF

open HatCommutators

theorem r0_mem_nfSpan_basics : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ y : ℝ, (∀ ρ : M.Ty P, M.xC P ρ (y : ℂ) ≠ 0 ∧ M.xC P ρ ((y : ℂ) - 1) ≠ 0 ∧ M.xC P ρ ((y : ℂ) + 1) ≠ 0) → d.L.R0 y ∈ nfSpan d (basics d) 0 0 1 ∧ d.L.R0v y ∈ nfSpan d (basics d) 0 0 1 := by
  intro P A _ _ _ _ d hd y hy
  obtain ⟨-, -, hR, -, hc, hci, -⟩ := hd
  have hx := xinv_mul d (y : ℂ) fun ρ => (hy ρ).1
  have hk := kap_mem d fun ρ => (M.xC P ρ (y : ℂ))⁻¹
  set k := d.κ fun ρ => (M.xC P ρ (y : ℂ))⁻¹
  constructor
  · have e : d.L.R0 y = k * rh d y - ∑ l ∈ Finset.Icc 1 (P.k - 1),
        (k * ssn d l * (d.κ fun ρ => M.xEx P {l} ρ y)) * d.L.Ahat y := by
      rw [rh_eq d hR, mul_add, ← mul_assoc, hx, one_mul, Finset.mul_sum]
      simp only [mul_assoc, add_sub_cancel_right]
    rw [e]
    refine Submodule.sub_mem _ (mem_span d hk ⟨y, hy, by simp⟩) (Submodule.sum_mem _ fun l hl => ?_)
    exact mem_span d (mul_mem (mul_mem hk (ssn_mem d hl)) (kap_mem d _)) ⟨y, hy, by simp⟩
  · have e : d.L.R0v y = k * rhv d y - ∑ l ∈ Finset.Icc 1 (P.k - 1),
        (k * (d.κ fun ρ => M.xEx P {l} ρ y) * star (ssn d l)) * d.L.Ahatv y := by
      rw [rhv_eq d hR hc hci, mul_add, ← mul_assoc, hx, one_mul, Finset.mul_sum]
      simp only [mul_assoc, add_sub_cancel_right]
    rw [e]
    refine Submodule.sub_mem _ (mem_span d hk ⟨y, hy, by simp⟩) (Submodule.sum_mem _ fun l hl => ?_)
    exact mem_span d (mul_mem (mul_mem hk (kap_mem d _)) (star_ssn_mem d hl)) ⟨y, hy, by simp⟩

end GlobalTheory.HatNF
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.R0MemNfSpanOfHatHypStatement

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

theorem _root_.GlobalTheory.T.R0_and_R0v_mem_nfSpan_basics_of_xC_ne_zero : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ y : ℝ, (∀ ρ : M.Ty P, M.xC P ρ (y : ℂ) ≠ 0 ∧ M.xC P ρ ((y : ℂ) - 1) ≠ 0 ∧ M.xC P ρ ((y : ℂ) + 1) ≠ 0) → d.L.R0 y ∈ nfSpan d (basics d) 0 0 1 ∧ d.L.R0v y ∈ nfSpan d (basics d) 0 0 1 := by
  first | exact @GlobalTheory.HatNF.r0_mem_nfSpan_basics | exact GlobalTheory.HatNF.r0_mem_nfSpan_basics | (intros; apply GlobalTheory.HatNF.r0_mem_nfSpan_basics <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.VecPolyMemSpanValuesStatement

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

theorem _root_.GlobalTheory.T.mem_span_values_of_vector_polynomial : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (Z : ℂ → V) (X : ℕ → V) (ν : Fin n → ℂ), Function.Injective ν → (∀ s : ℂ, Z s = ∑ j ∈ Finset.range n, s ^ j • X j) → (∀ j, j < n → X j ∈ Submodule.span ℂ (Set.range fun i => Z (ν i))) ∧ ∀ s : ℂ, Z s ∈ Submodule.span ℂ (Set.range fun i => Z (ν i)) := by
  first | exact @GlobalTheory.vecPoly_mem_span_values | exact GlobalTheory.vecPoly_mem_span_values | (intros; apply GlobalTheory.vecPoly_mem_span_values <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.HatLettersMemNormalFormProductSpan

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF

theorem hatExp_exists_bound (P : M.Par) :
    ∃ C : ℝ, ∀ t : ℝ, C ≤ t → ∀ ρ : M.Ty P, M.xC P ρ (t : ℂ) ≠ 0 := by
  obtain ⟨C, hC⟩ := (Set.toFinite
    ((fun x : M.Ty P × ℕ => -M.rho P x.1 x.2) ''
      ((Finset.univ ×ˢ Finset.Icc 1 (P.k - 1) : Finset (M.Ty P × ℕ)) : Set (M.Ty P × ℕ)))).bddAbove
  refine ⟨C + 1, fun t ht ρ => ?_⟩
  unfold M.xC
  refine Finset.prod_ne_zero_iff.2 fun i hi => ?_
  have h1 : -M.rho P ρ i ≤ C :=
    hC ⟨(ρ, i), Finset.mem_coe.2 (Finset.mem_product.2 ⟨Finset.mem_univ _, hi⟩), rfl⟩
  have h2 : t + M.rho P ρ i ≠ 0 := (show 0 < t + M.rho P ρ i by linarith).ne'
  exact_mod_cast h2

theorem hatExp_exists_nodes (P : M.Par) (n : ℕ) :
    ∃ y : Fin n → ℝ, Function.Injective y ∧ ∀ i, ∀ ρ : M.Ty P,
      M.xC P ρ (y i : ℂ) ≠ 0 ∧ M.xC P ρ ((y i : ℂ) - 1) ≠ 0 ∧ M.xC P ρ ((y i : ℂ) + 1) ≠ 0 := by
  obtain ⟨C, hC⟩ := hatExp_exists_bound P
  refine ⟨fun i => C + 1 + (i : ℕ), fun i j h => ?_, fun i ρ => ?_⟩
  · have h' : ((i : ℕ) : ℝ) = (j : ℕ) := by simpa using h
    exact Fin.ext (by exact_mod_cast h')
  · have h0 : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := Nat.cast_nonneg _
    refine ⟨hC _ (by linarith) ρ, ?_, ?_⟩
    · have := hC (C + 1 + (i : ℕ) - 1) (by linarith) ρ
      rwa [Complex.ofReal_sub, Complex.ofReal_one] at this
    · have := hC (C + 1 + (i : ℕ) + 1) (by linarith) ρ
      rwa [Complex.ofReal_add _ 1, Complex.ofReal_one] at this

theorem hats_mem_nfSpan : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ (T : Set A) (a : ℕ), (∀ x ∈ basics d, x ∈ nfSpan d T 0 a 1) → ∀ X ∈ hats d.L, X ∈ nfSpan d T 0 a 1 := by
  intro P A _ _ _ _ d hd T a hT
  have hle : nfSpan d (basics d) 0 0 1 ≤ nfSpan d T 0 a 1 := by
    unfold nfSpan
    refine Submodule.span_le.2 ?_
    rintro x ⟨b, hb, H, hH, hHT, rfl⟩
    obtain ⟨h, rfl⟩ := List.length_eq_one_iff.1 hH
    have h1 := ((GlobalTheory.T.normalFormProductSpan_left_mul_closed P A d hd T).1 0 a 1 h (hT h (hHT h (List.mem_singleton_self h)))).1 b hb
    simpa [nfSpan] using h1
  obtain ⟨y, hy, hreg⟩ := hatExp_exists_nodes P (P.r + 2)
  have hyc : Function.Injective fun i => (y i : ℂ) := fun i j h => hy (Complex.ofReal_injective h)
  have hyn : Function.Injective fun i => -(y i : ℂ) := fun i j h => hyc (neg_injective h)
  have key : ∀ (Z : ℂ → A) (X : ℕ → A) (ν : Fin (P.r + 2) → ℂ), Function.Injective ν →
      (∀ s : ℂ, Z s = ∑ j ∈ Finset.range (P.r + 2), s ^ j • X j) →
      (∀ i, Z (ν i) ∈ nfSpan d T 0 a 1) → ∀ s, Z s ∈ nfSpan d T 0 a 1 := by
    intro Z X ν hν hZ hi s
    refine (Submodule.span_le.2 ?_) ((GlobalTheory.T.mem_span_values_of_vector_polynomial A (P.r + 2) Z X ν hν hZ).2 s)
    rintro _ ⟨i, rfl⟩
    exact hi i
  obtain ⟨Xa, Xr, hXa, hXr, -⟩ := GlobalTheory.T.plusHats_taylorCoeff_leibniz_rule A P.r d.L 0
  obtain ⟨Va, Vr, hVa, hVr, -⟩ := GlobalTheory.T.minusHats_taylorCoeff_leibniz_rule A P.r d.L 0
  rintro X (((⟨s, rfl⟩ | ⟨s, rfl⟩) | ⟨s, rfl⟩) | ⟨s, rfl⟩)
  · have := key (fun s => d.L.Ahat (0 + s)) Xa _ hyc hXa
      (fun i => by simpa using hT _ ⟨y i, hreg i, Or.inl rfl⟩) s
    simpa using this
  · have := key (fun s => d.L.R0 (0 + s)) Xr _ hyc hXr
      (fun i => by simpa using hle (GlobalTheory.T.R0_and_R0v_mem_nfSpan_basics_of_xC_ne_zero P A d hd (y i) (hreg i)).1) s
    simpa using this
  · have := key (fun s => d.L.Ahatv (0 - s)) Va _ hyn hVa
      (fun i => by simpa using hT _ ⟨y i, hreg i, Or.inr (Or.inl rfl)⟩) (-s)
    simpa using this
  · have := key (fun s => d.L.R0v (0 - s)) Vr _ hyn hVr
      (fun i => by simpa using hle (GlobalTheory.T.R0_and_R0v_mem_nfSpan_basics_of_xC_ne_zero P A d hd (y i) (hreg i)).2) (-s)
    simpa using this

end GlobalTheory.HatNF
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.HatLettersMemNormalFormProductSpanStatement

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

theorem _root_.GlobalTheory.T.hatLetters_mem_normalFormProductSpan : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ (T : Set A) (a : ℕ), (∀ x ∈ basics d, x ∈ nfSpan d T 0 a 1) → ∀ X ∈ hats d.L, X ∈ nfSpan d T 0 a 1 := by
  first | exact @GlobalTheory.HatNF.hats_mem_nfSpan | exact GlobalTheory.HatNF.hats_mem_nfSpan | (intros; apply GlobalTheory.HatNF.hats_mem_nfSpan <;> assumption)
end
end
