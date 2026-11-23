module

public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInvariantPreimageAverage
public import Formalism.SharpRestriction.LevelLetterCocycles.LetterConditionGlobal
public import Formalism.SharpRestriction.LevelLetterCocycles.LevelClauseOfOpenTool
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsMemMapEqSmul
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
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
import Mathlib.Algebra.Order.Star.Real

-- Source module: Formalism.SharpRestriction.LevelLetterCocycles.SumSubEqSumIocOfSub

section

@[expose] public section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.FactorialSumBounds

open Finset

variable (l : ℕ) [hl : Fact l.Prime]

theorem sum_Ioc_zero_eq_factorial (y : ℕ) :
    ∑ m ∈ Ioc 0 y, padicValNat l m = padicValNat l y.factorial := by
  induction y with
  | zero => simp [Nat.padicValNat_def]
  | succ n ih =>
    rw [Finset.sum_Ioc_succ_top (Nat.zero_le n), ih, Nat.factorial_succ,
      (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (by omega) (Nat.factorial_ne_zero n)]
    ring

theorem padicValNat_factorial_le_div_sub_one (y : ℕ) :
    ((padicValNat l y.factorial : ℕ) : ℝ) ≤ (y : ℝ) / ((l : ℝ) - 1) := by
  have h1 : 1 < l := hl.out.one_lt
  have hc : (0:ℝ) < (l:ℝ) - 1 := by
    have : (1:ℝ) < l := by exact_mod_cast h1
    linarith
  have key : (l - 1) * padicValNat l y.factorial ≤ y := by
    rw [Nat.padicValNat_def, hl.out.sub_one_mul_multiplicity_factorial]; exact Nat.sub_le _ _
  have key' : (((l - 1 : ℕ) : ℝ)) * (padicValNat l y.factorial : ℝ) ≤ y := by
    exact_mod_cast key
  rw [Nat.cast_sub h1.le, Nat.cast_one] at key'
  rw [le_div_iff₀ hc]; linarith

theorem padicValNat_choose_le_logb' (k n : ℕ) :
    ((padicValNat l (k.choose n) : ℕ) : ℝ) ≤ Real.logb l k := by
  have h1 : padicValNat l (k.choose n) ≤ Nat.log l k := by
    rw [Nat.padicValNat_def, ← Nat.factorization_def _ hl.out]
    exact Nat.factorization_choose_le_log
  have h2 : ((Nat.log l k : ℕ) : ℝ) ≤ Real.logb l k := by
    first
    | exact Real.natLog_le_logb k l
    | rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk; simp
      · have hl1 : (1:ℝ) < l := by exact_mod_cast hl.out.one_lt
        rw [Real.le_logb_iff_rpow_le hl1 (by exact_mod_cast hk), Real.rpow_natCast]
        exact_mod_cast Nat.pow_log_le_self l hk.ne'
  calc ((padicValNat l (k.choose n) : ℕ) : ℝ) ≤ ((Nat.log l k : ℕ) : ℝ) := by exact_mod_cast h1
    _ ≤ Real.logb l k := h2

theorem sum_Ioc_padicValNat_le_div_sub_one_add_logb (k0 k1 : ℕ) (h : k0 ≤ k1) :
    ((∑ m ∈ Ioc k0 k1, padicValNat l m : ℕ) : ℝ) ≤
      ((k1 - k0 : ℕ) : ℝ) / ((l : ℝ) - 1) + Real.logb l k1 := by
  have hsplit : ∑ m ∈ Ioc 0 k0, padicValNat l m + ∑ m ∈ Ioc k0 k1, padicValNat l m
      = ∑ m ∈ Ioc 0 k1, padicValNat l m :=
    Finset.sum_Ioc_consecutive _ (Nat.zero_le k0) h
  rw [sum_Ioc_zero_eq_factorial, sum_Ioc_zero_eq_factorial] at hsplit
  have hA : k1.choose k0 * k0.factorial ≠ 0 :=
    mul_ne_zero (Nat.choose_pos h).ne' (Nat.factorial_ne_zero k0)
  have hfac : k1.factorial = k1.choose k0 * k0.factorial * (k1 - k0).factorial :=
    (Nat.choose_mul_factorial_mul_factorial h).symm
  rw [hfac, (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) hA (Nat.factorial_ne_zero _),
    (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (Nat.choose_pos h).ne' (Nat.factorial_ne_zero k0)] at hsplit
  have heq : ∑ m ∈ Ioc k0 k1, padicValNat l m
      = padicValNat l (k1.choose k0) + padicValNat l (k1 - k0).factorial := by omega
  rw [heq, Nat.cast_add]
  have h2 := padicValNat_factorial_le_div_sub_one l (k1 - k0)
  have h3 := padicValNat_choose_le_logb' l k1 k0
  linarith

theorem sum_sub_eq_sum_Ioc (j0 : ℤ) (k0 k1 : ℕ) (T : Finset ℤ)
    (hT : ∀ j, j ∈ T ↔ (k0 : ℤ) < j0 - j ∧ j0 - j ≤ k1) :
    ∑ j ∈ T, padicValInt l (j0 - j) = ∑ m ∈ Ioc k0 k1, padicValNat l m := by
  refine Finset.sum_nbij' (fun j => (j0 - j).toNat) (fun m => j0 - (m : ℤ)) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_coe, Finset.mem_Ioc, hT] at ha ⊢
    omega
  · intro a ha
    simp only [Finset.mem_coe, Finset.mem_Ioc, hT] at ha ⊢
    omega
  · intro a ha
    simp only [Finset.mem_coe, hT] at ha ⊢
    omega
  · intro a ha
    simp only [Finset.mem_coe, Finset.mem_Ioc] at ha ⊢
    omega
  · intro a ha
    simp only [Finset.mem_coe, hT] at ha
    simp only [padicValInt, ← Nat.padicValNat_def]
    congr 1
    omega

theorem sum_sub_eq_sum_Ioc_of_sub (j0 : ℤ) (k0 k1 : ℕ) (T : Finset ℤ)
    (hT : ∀ j, j ∈ T ↔ (k0 : ℤ) < j - j0 ∧ j - j0 ≤ k1) :
    ∑ j ∈ T, padicValInt l (j0 - j) = ∑ m ∈ Ioc k0 k1, padicValNat l m := by
  refine Finset.sum_nbij' (fun j => (j - j0).toNat) (fun m => j0 + (m : ℤ)) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_coe, Finset.mem_Ioc, hT] at ha ⊢
    omega
  · intro a ha
    simp only [Finset.mem_coe, Finset.mem_Ioc, hT] at ha ⊢
    omega
  · intro a ha
    simp only [Finset.mem_coe, hT] at ha ⊢
    omega
  · intro a ha
    simp only [Finset.mem_coe, Finset.mem_Ioc] at ha ⊢
    omega
  · intro a ha
    simp only [Finset.mem_coe, hT] at ha
    simp only [padicValInt, ← Nat.padicValNat_def]
    congr 1
    omega

theorem sum_erase_add_sum_le (a b S η h : ℕ) (hb : 2 * a + η ≤ b) (hbh : b ≤ h) (S₂ : Finset ℤ)
    (hS₂ : S₂ ⊆ Icc ((b : ℤ) + 1) ((b : ℤ) + S + a) ∪ Icc (1 - (η : ℤ)) ((η : ℤ) + a))
    (j₀ : ℤ) (hj₀ : j₀ ∈ Icc ((b : ℤ) - a + 1) (b : ℤ)) :
    (((∑ j ∈ (Icc ((b : ℤ) - a + 1) (b : ℤ)).erase j₀, padicValInt l (j₀ - j)) +
        ∑ j ∈ S₂, padicValInt l (j₀ - j) : ℕ) : ℝ) ≤
      (3 * (a : ℝ) + S + 2 * η - 1) / ((l : ℝ) - 1) + Real.logb l ((h + η : ℕ) : ℝ) := by
  have hl1 : (1:ℝ) < l := by exact_mod_cast hl.out.one_lt
  have hc : (0:ℝ) < (l:ℝ) - 1 := by linarith
  rw [Finset.mem_Icc] at hj₀
  obtain ⟨p, hp⟩ : ∃ p : ℕ, j₀ = (b : ℤ) - p := ⟨((b : ℤ) - j₀).toNat, by omega⟩
  subst hp
  have hpa : p + 1 ≤ a := by omega
  have e1 : ∑ j ∈ ((Icc ((b : ℤ) - a + 1) (b : ℤ)).erase ((b : ℤ) - p)).filter
        (fun j => j < (b : ℤ) - p), padicValInt l ((b : ℤ) - p - j)
      = ∑ m ∈ Ioc 0 (a - 1 - p), padicValNat l m := by
    apply sum_sub_eq_sum_Ioc
    intro j
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_Icc]
    constructor <;> intro hj <;> omega
  have e2 : ∑ j ∈ ((Icc ((b : ℤ) - a + 1) (b : ℤ)).erase ((b : ℤ) - p)).filter
        (fun j => ¬ j < (b : ℤ) - p), padicValInt l ((b : ℤ) - p - j)
      = ∑ m ∈ Ioc 0 p, padicValNat l m := by
    apply sum_sub_eq_sum_Ioc_of_sub
    intro j
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_Icc]
    constructor <;> intro hj <;> omega
  have e12 : ∑ j ∈ (Icc ((b : ℤ) - a + 1) (b : ℤ)).erase ((b : ℤ) - p),
        padicValInt l ((b : ℤ) - p - j)
      = ∑ m ∈ Ioc 0 (a - 1 - p), padicValNat l m + ∑ m ∈ Ioc 0 p, padicValNat l m := by
    rw [← e1, ← e2]
    exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hdisj : Disjoint (Icc ((b : ℤ) + 1) ((b : ℤ) + S + a))
      (Icc (1 - (η : ℤ)) ((η : ℤ) + a)) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [Finset.mem_Icc] at hx hx'
    omega
  have e3 : ∑ j ∈ S₂, padicValInt l ((b : ℤ) - p - j) ≤
      ∑ j ∈ Icc ((b : ℤ) + 1) ((b : ℤ) + S + a), padicValInt l ((b : ℤ) - p - j) +
      ∑ j ∈ Icc (1 - (η : ℤ)) ((η : ℤ) + a), padicValInt l ((b : ℤ) - p - j) := by
    rw [← Finset.sum_union hdisj]
    exact Finset.sum_le_sum_of_subset hS₂
  have eA : ∑ j ∈ Icc ((b : ℤ) + 1) ((b : ℤ) + S + a), padicValInt l ((b : ℤ) - p - j)
      = ∑ m ∈ Ioc p (p + S + a), padicValNat l m := by
    apply sum_sub_eq_sum_Ioc_of_sub
    intro j
    rw [Finset.mem_Icc]
    constructor <;> intro hj <;> omega
  have eB : ∑ j ∈ Icc (1 - (η : ℤ)) ((η : ℤ) + a), padicValInt l ((b : ℤ) - p - j)
      = ∑ m ∈ Ioc (b - p - η - a - 1) (b - p + η - 1), padicValNat l m := by
    apply sum_sub_eq_sum_Ioc
    intro j
    rw [Finset.mem_Icc]
    constructor <;> intro hj <;> omega
  have ePQ : ∑ m ∈ Ioc 0 p, padicValNat l m + ∑ m ∈ Ioc p (p + S + a), padicValNat l m
      = padicValNat l (p + S + a).factorial := by
    rw [Finset.sum_Ioc_consecutive _ (Nat.zero_le p) (by omega : p ≤ p + S + a),
      sum_Ioc_zero_eq_factorial]
  have eR : ∑ m ∈ Ioc 0 (a - 1 - p), padicValNat l m = padicValNat l (a - 1 - p).factorial :=
    sum_Ioc_zero_eq_factorial l _
  have hN : (∑ j ∈ (Icc ((b : ℤ) - a + 1) (b : ℤ)).erase ((b : ℤ) - p),
        padicValInt l ((b : ℤ) - p - j)) + ∑ j ∈ S₂, padicValInt l ((b : ℤ) - p - j)
      ≤ padicValNat l (a - 1 - p).factorial + padicValNat l (p + S + a).factorial +
        ∑ m ∈ Ioc (b - p - η - a - 1) (b - p + η - 1), padicValNat l m := by
    rw [eA, eB] at e3
    rw [e12]
    omega
  have hR := padicValNat_factorial_le_div_sub_one l (a - 1 - p)
  have hP := padicValNat_factorial_le_div_sub_one l (p + S + a)
  have hB := sum_Ioc_padicValNat_le_div_sub_one_add_logb l (b - p - η - a - 1) (b - p + η - 1) (by omega)
  have hx : (0:ℝ) < ((b - p + η - 1 : ℕ) : ℝ) := by
    have : 0 < b - p + η - 1 := by omega
    exact_mod_cast this
  have hxy : ((b - p + η - 1 : ℕ) : ℝ) ≤ ((h + η : ℕ) : ℝ) := by
    exact_mod_cast (by omega : b - p + η - 1 ≤ h + η)
  have hlog : Real.logb l ((b - p + η - 1 : ℕ) : ℝ) ≤ Real.logb l ((h + η : ℕ) : ℝ) := by
    first
    | exact Real.logb_le_logb_of_le hl1 hx hxy
    | exact (Real.logb_le_logb hl1 hx (by linarith)).mpr hxy
  have hnum : ((a - 1 - p : ℕ) : ℝ) + ((p + S + a : ℕ) : ℝ) +
      (((b - p + η - 1) - (b - p - η - a - 1) : ℕ) : ℝ) = 3 * (a : ℝ) + S + 2 * η - 1 := by
    have e4 : (b - p + η - 1) - (b - p - η - a - 1) = 2 * η + a := by omega
    have e6 : ((a - 1 - p : ℕ) : ℝ) + 1 + p = a := by
      exact_mod_cast (by omega : a - 1 - p + 1 + p = a)
    rw [e4]
    push_cast
    linarith
  have hdiv : ((a - 1 - p : ℕ) : ℝ) / ((l : ℝ) - 1) + ((p + S + a : ℕ) : ℝ) / ((l : ℝ) - 1) +
      (((b - p + η - 1) - (b - p - η - a - 1) : ℕ) : ℝ) / ((l : ℝ) - 1)
      = (3 * (a : ℝ) + S + 2 * η - 1) / ((l : ℝ) - 1) := by
    rw [← hnum]; ring
  calc _ ≤ ((padicValNat l (a - 1 - p).factorial + padicValNat l (p + S + a).factorial +
          ∑ m ∈ Ioc (b - p - η - a - 1) (b - p + η - 1), padicValNat l m : ℕ) : ℝ) :=
        Nat.cast_le.mpr hN
    _ = ((padicValNat l (a - 1 - p).factorial : ℕ) : ℝ) +
          ((padicValNat l (p + S + a).factorial : ℕ) : ℝ) +
          ((∑ m ∈ Ioc (b - p - η - a - 1) (b - p + η - 1), padicValNat l m : ℕ) : ℝ) := by
        rw [Nat.cast_add, Nat.cast_add]
    _ ≤ _ := by linarith

end Formalism.MainNotions.RamifiedCoefficientChains.S9.FactorialSumBounds
end
end

-- Source module: Formalism.SharpRestriction.LevelLetterCocycles.DerivativeProdSubEval

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains Polynomial

section LemG2Main

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem derivative_prod_sub_eval {R : Type} [CommRing R] (S₀ : Finset ℤ) (c : ℤ → R) (a : ℤ)
    (ha : a ∈ S₀) :
    (derivative (∏ b ∈ S₀, (X - C (c b)))).eval (c a) = ∏ b ∈ S₀.erase a, (c a - c b) := by
  classical
  have h1 : (∏ b ∈ S₀, (X - C (c b))) = (Multiset.map (fun x => X - C x) (S₀.val.map c)).prod := by
    rw [Finset.prod_eq_multiset_prod, Multiset.map_map]
    rfl
  rw [h1, eval_multiset_prod_X_sub_C_derivative (Multiset.mem_map_of_mem c ha),
    ← Multiset.map_erase_of_mem c S₀.val ha, Multiset.map_map, Finset.prod_eq_multiset_prod, Finset.erase_val]
  rfl

theorem addValuation_prod (w : AddValuation LL (WithTop ℚ)) {ι : Type} (S₀ : Finset ι) (f : ι → LL) :
    w (∏ b ∈ S₀, f b) = ∑ b ∈ S₀, w (f b) := by
  classical
  induction S₀ using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, AddValuation.map_mul, ih]

theorem algebraMap_cc_eq (W : LocWach PD LL O v n) (cc : ℤ → O)
    (hcc : ∀ x : ℤ, (-((PD.p : ℕ) : O)) * cc x = (((W.χΓ W.gam) ^ (-x) : Oˣ) : O) - 1) (j : ℤ) :
    algebraMap O LL (cc j) = Formalism.MainNotions.CrystallineLiftingInputs.cR W j := by
  have hp0 : (PD.p : LL) ≠ 0 := by
    intro h
    have := W.v_l
    rw [h, AddValuation.map_zero] at this
    exact WithTop.top_ne_one this
  unfold Formalism.MainNotions.CrystallineLiftingInputs.cR
  rw [eq_div_iff (neg_ne_zero.2 hp0)]
  have h1 := congrArg (algebraMap O LL) (hcc j)
  rw [map_mul, map_neg, map_natCast, map_sub, map_one] at h1
  rw [← h1]
  ring

theorem valuation_cc_sub (W : LocWach PD LL O v n) (hRN : Formalism.MainNotions.CrystallineLiftingInputs.RToolNum W) (cc : ℤ → O)
    (hcc : ∀ x : ℤ, (-((PD.p : ℕ) : O)) * cc x = (((W.χΓ W.gam) ^ (-x) : Oˣ) : O) - 1)
    (a b : ℤ) (hab : a ≠ b) :
    v (algebraMap O LL (cc a - cc b)) = ((padicValInt PD.p (a - b) : ℕ) : WithTop ℚ) := by
  rw [map_sub, algebraMap_cc_eq W cc hcc, algebraMap_cc_eq W cc hcc, hRN.2 a b hab, WithTop.coe_natCast]

theorem lemGB_of [NeZero n] (W : LocWach PD LL O v n) (hQ : Formalism.MainNotions.CrystallineLiftingInputs.QTool W)
    (hRN : Formalism.MainNotions.LiftingTheory.CaseA W → Formalism.MainNotions.CrystallineLiftingInputs.RToolNum W) (hC4 : Formalism.MainNotions.N.LetterConditionLocal W)
    (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hL : Formalism.MainNotions.LiftingTheory.coreL W)
    (hcc : Formalism.MainNotions.LiftingTheory.CaseA W → ∃ cc : ℤ → O,
      ∀ x : ℤ, (-((PD.p : ℕ) : O)) * cc x = (((W.χΓ W.gam) ^ (-x) : Oˣ) : O) - 1)
    (hΔ : Formalism.MainNotions.LiftingTheory.CaseA W → IsUnit ((PD.p - 1 : ℕ) : O)) (h56 : WachGammaDerivation W) : LemGB W := by
  intro d T₁ T₂ F b S η m hS i hi
  have hA : Formalism.MainNotions.LiftingTheory.CaseA W := hS.1
  have hl : 11 ≤ PD.p := hS.2.1
  have hsur : Formalism.MainNotions.LiftingTheory.Sur W F := hS.2.2.2.2.2.1
  have hjump := hS.2.2.2.2.2.2.1
  have hbR := hS.2.2.2.2.2.2.2.2.1 i
  have : Fact PD.p.Prime := ⟨PD.hp⟩
  have hRN := hRN hA
  obtain ⟨cc, hcc⟩ := hcc hA
  obtain ⟨hπ, hπΔ, hmod₁, hcard⟩ := uniformizer_unit_and_delta_card W h9 hA hsur.1
  have hΔ : IsUnit ((W.DelF.card : ℕ) : O) := by rw [hcard]; exact hΔ hA
  have hq := isUnit_q_of_uniformizer_unit W hπ
  obtain ⟨dop₁, hd₁⟩ := exists_derivation_gamma_sub W T₁ hπ
  obtain ⟨dop₂, hd₂⟩ := exists_derivation_gamma_sub W T₂ hπ
  have hl2 : 2 ≤ PD.p := by omega
  have hpR : (11 : ℝ) ≤ PD.p := by exact_mod_cast hl
  have haR0 : 0 ≤ aR PD.p (hpar n b S + η) := aR_nonneg PD.p _ hl2
  have haR3 : (3 : ℝ) ≤ aR PD.p (hpar n b S + η) := by
    have h1 := one_le_lam PD.p (hpar n b S + η) hl2
    have h2 : 0 ≤ (((hpar n b S + η : ℕ) : ℝ)) * (2 * (PD.p : ℝ) - 1) / ((PD.p : ℝ) - 1) ^ 2 :=
      div_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith)) (sq_nonneg _)
    unfold aR
    linarith
  obtain ⟨a, ha⟩ : ∃ a, a = ⌈aR PD.p (hpar n b S + η)⌉₊ := ⟨_, rfl⟩
  have halt : (a : ℝ) < aR PD.p (hpar n b S + η) + 1 := ha ▸ Nat.ceil_lt_add_one haR0
  have hale : aR PD.p (hpar n b S + η) ≤ a := ha ▸ Nat.le_ceil _
  have ha1 : 1 ≤ a := by
    have : (1 : ℝ) ≤ a := by linarith
    exact_mod_cast this
  have hab : 2 * a + η ≤ b i := by
    have : ((2 * a + η : ℕ) : ℝ) < ((b i + 1 : ℕ) : ℝ) := by push_cast; linarith
    have := Nat.cast_lt.1 this
    omega
  have hbh : b i ≤ hpar n b S := by
    unfold hpar
    have := Finset.le_sup (f := b) (Finset.mem_univ i)
    omega

  obtain ⟨Bd, hBd⟩ : ∃ Bd : ℝ, Bd = (3 * (a : ℝ) + S + 2 * η - 1) / ((PD.p : ℝ) - 1) +
      Real.logb PD.p ((hpar n b S + η : ℕ) : ℝ) := ⟨_, rfl⟩
  have hpos : (0 : ℝ) < (PD.p : ℝ) - 1 := by linarith
  have hH1 : (1 : ℝ) ≤ ((hpar n b S + η : ℕ) : ℝ) := by
    have : 1 ≤ hpar n b S + η := by omega
    exact_mod_cast this
  have hp1 : (1 : ℝ) < PD.p := by linarith
  have hB0 : 0 ≤ Bd := by
    rw [hBd]
    have : (1 : ℝ) ≤ a := by exact_mod_cast ha1
    have hS0 : (0 : ℝ) ≤ S := Nat.cast_nonneg _
    have hη0 : (0 : ℝ) ≤ η := Nat.cast_nonneg _
    have h1 : 0 ≤ (3 * (a : ℝ) + S + 2 * η - 1) / ((PD.p : ℝ) - 1) :=
      div_nonneg (by linarith) hpos.le
    have h2 := Real.logb_nonneg hp1 hH1
    linarith
  refine ⟨⌊Bd⌋₊, ?_, ?_⟩
  · have hfl : (⌊Bd⌋₊ : ℝ) ≤ Bd := Nat.floor_le hB0
    have h1 : (3 * (a : ℝ) + S + 2 * η - 1) / ((PD.p : ℝ) - 1) ≤
        (3 * aR PD.p (hpar n b S + η) + S + 2 * η) / ((PD.p : ℝ) - 1) + 1 := by
      rw [div_le_iff₀ hpos, add_mul, div_mul_cancel₀ _ hpos.ne', one_mul]
      linarith
    have h2 : Real.logb PD.p ((hpar n b S + η : ℕ) : ℝ) ≤ lam PD.p (hpar n b S + η) - 1 := by
      unfold lam
      have := Real.logb_le_logb_of_le hp1 (by linarith : (0 : ℝ) < ((hpar n b S + η : ℕ) : ℝ))
        (by linarith : ((hpar n b S + η : ℕ) : ℝ) ≤ 2 * ((hpar n b S + η : ℕ) : ℝ))
      linarith
    calc (⌊Bd⌋₊ : ℝ) ≤ Bd := hfl
      _ = (3 * (a : ℝ) + S + 2 * η - 1) / ((PD.p : ℝ) - 1) +
          Real.logb PD.p ((hpar n b S + η : ℕ) : ℝ) := hBd
      _ ≤ _ := by linarith
  intro x la hP
  have hxN : x ∈ W.N T₂ := hP.1
  have hxe : (letE i : LetA O n) • x = x := hP.2.1.1
  have hxΔ : ∀ δ ∈ W.DelF, W.γD T₂ δ x = x := hP.2.1.2
  have hxl : x ∈ W.Nl T₂ i := mem_letter_of_idempotent_smul W hxN hxe

  have hJL : Formalism.MainNotions.LiftingTheory.JumpsLet W T₁ (fun _ => hpar n b S + η) (fun _ => hpar n b S + η) := by
    intro j τ hτ u hu
    have h1 := hjump j τ hτ u hu
    have hbj : b j + S ≤ hpar n b S := by
      unfold hpar
      have := Finset.le_sup (f := b) (Finset.mem_univ j)
      omega
    unfold JumpWinS at h1
    split_ifs at h1 <;> simp only [Set.mem_union, Set.mem_Icc] at h1 ⊢ <;> omega
  have hK := ((hQ d T₁ T₂ F b S η m _ _ hS hJL).1 i).2.2
  rw [← ha] at hK

  obtain ⟨y₀, hy₀, hy₀F⟩ := Submodule.mem_map.1 (hK x hxl)
  have htx : ∀ δ ∈ W.DelF, W.γD T₂ δ (Formalism.MainNotions.LiftingTheory.qp W ^ a • x) = Formalism.MainNotions.LiftingTheory.qp W ^ a • x := by
    intro δ hδ
    rw [gammaD_smul_letA, map_pow, gammaA_q_of_mem_delta W hπΔ δ hδ, hxΔ δ hδ]
  obtain ⟨y₂, hy₂N, hy₂F⟩ := exists_invariant_preimage_average W hΔ F i hy₀ htx hy₀F
  let qi : W.EE := ((hq.unit⁻¹ : W.EEˣ) : W.EE)
  have hqz : Formalism.MainNotions.LiftingTheory.qp W ^ a • (qi ^ a • y₂) = y₂ := by
    rw [← algebraMap_smul W.EE (Formalism.MainNotions.LiftingTheory.qp W ^ a), smul_smul, map_pow, ← mul_pow,
      hq.mul_val_inv, one_pow, one_smul]
  have hFz : W.map F (qi ^ a • y₂) = x := by
    have hqa : IsUnit (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W ^ a)) := by
      rw [map_pow]; exact hq.pow a
    refine (hqa.smul_left_cancel).1 ?_
    rw [algebraMap_smul, algebraMap_smul, ← map_letA_smul_comm, hqz, hy₂F]
  have hX : ∀ (τ : K →ₐ[Qp] LL) (u : ℤ) (j : ℕ), Formalism.MainNotions.LiftingTheory.Over W τ i → IsJumpV PD T₁.ρ τ u →
      1 ≤ j → j ≤ a → u + (j : ℤ) ∈ Finset.Icc ((b i : ℤ) + 1) ((b i : ℤ) + S + a) ∪
        Finset.Icc (1 - (η : ℤ)) ((η : ℤ) + a) := by
    intro τ u j hτ hu hj1 hj2
    have h1 := hjump i τ hτ u hu
    unfold JumpWinS at h1
    rw [if_neg (by omega)] at h1
    simp only [Set.mem_union, Set.mem_Icc, Finset.mem_union, Finset.mem_Icc] at h1 ⊢
    omega
  have hC := hC4 hA T₁ hsur.1 i a ha1 dop₁ hd₁ cc hcc _ hX (qi ^ a • y₂) (by
    change Formalism.MainNotions.LiftingTheory.InNΔi W T₁ i (Formalism.MainNotions.LiftingTheory.qp W ^ a • (qi ^ a • y₂))
    rw [hqz]
    exact hy₂N)

  obtain ⟨w, ⟨⟨-, hwΔ⟩, hwl⟩, hP1⟩ := h56 d T₁ T₂ F b S η m hS i hi dop₂ hd₂ cc hcc x la hP
  rw [← ha] at hP1
  obtain ⟨y₁', hy₁', hy₁F'⟩ := Submodule.mem_map.1 (hK w hwl)
  have htw : ∀ δ ∈ W.DelF, W.γD T₂ δ (Formalism.MainNotions.LiftingTheory.qp W ^ a • w) = Formalism.MainNotions.LiftingTheory.qp W ^ a • w := by
    intro δ hδ
    rw [gammaD_smul_letA, map_pow, gammaA_q_of_mem_delta W hπΔ δ hδ, hwΔ δ hδ]
  obtain ⟨y₁, hy₁N, hy₁F⟩ := exists_invariant_preimage_average W hΔ F i hy₁' htw hy₁F'

  have hdis : Disjoint (Finset.Icc ((b i : ℤ) - a + 1) (b i : ℤ))
      (Finset.Icc ((b i : ℤ) + 1) ((b i : ℤ) + S + a) ∪ Finset.Icc (1 - (η : ℤ)) ((η : ℤ) + a)) := by
    rw [Finset.disjoint_left]
    intro u hu hu'
    simp only [Finset.mem_union, Finset.mem_Icc] at hu hu'
    omega
  have hval : ∀ a' ∈ Finset.Icc ((b i : ℤ) - a + 1) (b i : ℤ) ∪
      (Finset.Icc ((b i : ℤ) + 1) ((b i : ℤ) + S + a) ∪ Finset.Icc (1 - (η : ℤ)) ((η : ℤ) + a)),
      ∀ b' ∈ Finset.Icc ((b i : ℤ) - a + 1) (b i : ℤ) ∪
      (Finset.Icc ((b i : ℤ) + 1) ((b i : ℤ) + S + a) ∪ Finset.Icc (1 - (η : ℤ)) ((η : ℤ) + a)),
      a' ≠ b' → v (algebraMap O LL (cc a' - cc b')) =
        ((0 + padicValInt PD.p (a' - b') : ℕ) : WithTop ℚ) := by
    intro a' _ b' _ h
    rw [zero_add]
    exact valuation_cc_sub W hRN cc hcc a' b' h
  have hE : ∀ j₀ ∈ Finset.Icc ((b i : ℤ) - a + 1) (b i : ℤ),
      v (algebraMap O LL ((∏ b' ∈ Finset.Icc ((b i : ℤ) + 1) ((b i : ℤ) + S + a) ∪
          Finset.Icc (1 - (η : ℤ)) ((η : ℤ) + a), (X - C (cc b'))).eval (cc j₀))) +
        v (algebraMap O LL ((derivative (∏ b' ∈ Finset.Icc ((b i : ℤ) - a + 1) (b i : ℤ),
          (X - C (cc b')))).eval (cc j₀))) ≤ ((⌊Bd⌋₊ : ℕ) : WithTop ℚ) := by
    intro j₀ hj₀
    have hj₀' := Finset.disjoint_left.1 hdis hj₀
    rw [derivative_prod_sub_eval _ cc j₀ hj₀, eval_prod]
    simp only [eval_sub, eval_X, eval_C]
    rw [map_prod (algebraMap O LL), map_prod (algebraMap O LL), addValuation_prod v, addValuation_prod v]
    have e2 : ∀ b' ∈ Finset.Icc ((b i : ℤ) + 1) ((b i : ℤ) + S + a) ∪
        Finset.Icc (1 - (η : ℤ)) ((η : ℤ) + a),
        v (algebraMap O LL (cc j₀ - cc b')) = ((padicValInt PD.p (j₀ - b') : ℕ) : WithTop ℚ) :=
      fun b' hb' => valuation_cc_sub W hRN cc hcc j₀ b' (fun h => hj₀' (h ▸ hb'))
    have e1 : ∀ b' ∈ (Finset.Icc ((b i : ℤ) - a + 1) (b i : ℤ)).erase j₀,
        v (algebraMap O LL (cc j₀ - cc b')) = ((padicValInt PD.p (j₀ - b') : ℕ) : WithTop ℚ) :=
      fun b' hb' => valuation_cc_sub W hRN cc hcc j₀ b' (Finset.ne_of_mem_erase hb').symm
    rw [Finset.sum_congr rfl e2, Finset.sum_congr rfl e1, ← Nat.cast_sum, ← Nat.cast_sum,
      ← Nat.cast_add, ← WithTop.coe_natCast, ← WithTop.coe_natCast, WithTop.coe_le_coe, Nat.cast_le]
    apply Nat.le_floor
    have h11 := FactorialSumBounds.sum_erase_add_sum_le PD.p a (b i) S η (hpar n b S) hab hbh _ subset_rfl j₀ hj₀
    rw [hBd]
    push_cast at h11 ⊢
    linarith
  have hlag := hL _ _ 0 cc hdis hval ⌊Bd⌋₊ hE
  let fO : W.DD T₁ →ₗ[O] W.DD T₂ := ((W.map F).restrictScalars (LetA O n)).restrictScalars O
  have hf : ∀ y, fO (dop₁ y) = dop₂ (fO y) := fun y => map_comm_derivation W F hπ dop₁ hd₁ dop₂ hd₂ y
  have h2' : fO (aeval dop₁ (∏ x ∈ Finset.Icc ((b i : ℤ) + 1) ((b i : ℤ) + S + a) ∪
      Finset.Icc (1 - (η : ℤ)) ((η : ℤ) + a), (X - C (cc x))) (qi ^ a • y₂)) =
      aeval dop₂ (∏ x ∈ Finset.Icc ((b i : ℤ) + 1) ((b i : ℤ) + S + a) ∪
        Finset.Icc (1 - (η : ℤ)) ((η : ℤ) + a), (X - C (cc x))) x := by
    rw [FactorialSumBounds.linearMap_aeval_apply_comm_of_intertwine fO dop₁ dop₂ hf]
    exact congrArg _ hFz
  obtain ⟨y, hyN, hyF⟩ := FactorialSumBounds.exists_mem_map_eq_smul fO dop₁ dop₂ hf (invariantLetter W T₁ i)
    (derivation_preserves_invariants W i hπ hmod₁ dop₁ hd₁) _ _ _ hlag x ⟨y₁, hy₁N, hy₁F.trans hP1.symm⟩
    ⟨_, hC, h2'⟩
  obtain ⟨⟨hyN1, hyΔ⟩, hyl⟩ := hyN
  exact ⟨y, hyN1, ⟨idempotent_smul_of_mem_letter W hyl, hyΔ⟩, hyF⟩

end LemG2Main

end Formalism.MainNotions.RamifiedCoefficientChains.S9
end
end
end
