module

public import Formalism.LocalToGlobal.CharacterGerms.CoefficientIdentitySelfConjugate
public import Formalism.SharpRestriction.GrowthBounds.PowerSeriesFrobeniusCongruence
public import Formalism.LocalToGlobal.CharacterGerms.FrobPowSmul
public import Formalism.LocalToGlobal.CharacterGerms.MmMulSeries
public import Formalism.SharpRestriction.GrowthBounds.AlongCvSmul
import Formalism.SharpRestriction.GrowthBounds.CoeffIdentityPlainChartOfThree
public import Formalism.SharpRestriction.GrowthBounds.CoeffOneAlongCvLg
public import Formalism.SharpRestriction.GrowthBounds.ConstantCoeffUnshiftLogarithm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
public import Formalism.SharpRestriction.GrowthBounds.MixedCoefficientClosed
public import Formalism.LocalToGlobal.CharacterGerms.ConstMemTypeSetOfNonneg
public import Formalism.LocalToGlobal.CharacterGerms.GeOfPowEqOne
public import Formalism.LocalToGlobal.CharacterGerms.MaximalOfValuationGeOne
public import Formalism.LocalToGlobal.CharacterGerms.ValNonnegLeadingCoeffOfMemTySet
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Polynomial.Basic
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.SharpRestriction.GrowthBounds.PsOfIntS
public import Formalism.LocalToGlobal.CharacterGerms.RowTieDefs
public import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Topology.Sheaves.Init

-- Source module: Formalism.SharpRestriction.GrowthBounds.R1sExpLowHolds

section

@[expose] public section

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds SelfConjCharts MvPowerSeries

theorem r1sExpLow_holds : ExpLowOrderTruncation := by
  intro C _ _ F m hm hK i j hj
  have h2 : ∀ k, coeff (ee i j) (F ^ (k + 1 + 1)) = 0 := by
    intro k
    have e : F ^ (k + 1 + 1) = (F * F) * F ^ k := by ring
    rw [e]
    exact kmul (a := 2 * m) (b := 0) (fun i j h => kmul hK hK i j (by omega))
      (fun _ _ h => absurd h (Nat.not_lt_zero _)) i j (by omega)
  show ∑ k ∈ Finset.range ((ee i j).degree + 1), coeff (ee i j) (F ^ k) / (k.factorial : C) = _
  rw [Finset.sum_range_succ']
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
  rw [add_comm]
  congr 1
  cases hd : (ee i j).degree with
  | zero =>
    rw [Finset.sum_range_zero]
    have h0 : ee i j = 0 := (Finsupp.degree_eq_zero_iff _).1 hd
    have hj0 : j = 0 := by
      have := DFunLike.congr_fun h0 1
      simpa [ee_one] using this
    exact (hK i j (by omega)).symm
  | succ n =>
    rw [Finset.sum_range_succ', Finset.sum_eq_zero (fun k _ => by rw [h2 k, zero_div])]
    simp

end Formalism.L2.FormalSeriesBounds
end
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.SumRescaleTySTwo

section

@[expose] public section

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds

namespace SelfConjCharts

variable {C : Type} [Field C]

theorem subst_X_pow_X_pow {l : ℕ} (hl : 0 < l) (f : PowerSeries C) :
    PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ l) (PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ l) f) =
      PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ (l ^ 2)) f := by
  have hS : PowerSeries.HasSubst ((PowerSeries.X : PowerSeries C) ^ l) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [hl.ne'])
  rw [PowerSeries.subst_comp_subst_apply hS hS]
  congr 1
  rw [← PowerSeries.coe_substAlgHom hS, map_pow, PowerSeries.coe_substAlgHom hS, PowerSeries.subst_X hS, ← pow_mul, sq]

theorem sum_rescale_tyS_two {l : ℕ} (hl : 2 ≤ l) {ζ : C} (hζ : IsPrimitiveRoot ζ l) (a : ℕ → C) (ha : a 1 = 0) :
    ∑ k ∈ Finset.range l, PowerSeries.rescale (ζ ^ k) (tyS l a) =
      PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ (l ^ 2)) (tyS l fun s => (l : C) * a (s + 2)) := by
  have e : (fun s => (l : C) * a (s + 1)) = fun s => if s < 1 then 0 else (l : C) * a (s - 1 + 2) := by
    funext s
    cases s with
    | zero => simp [ha]
    | succ s => simp
  rw [← subst_tyS_Fs hl hζ a, ← subst_X_pow_X_pow (by omega)]
  congr 1
  rw [← tyS_Vpow hl, e]

theorem sum_root_pow {l : ℕ} {ζ : C} (hζ : IsPrimitiveRoot ζ l) (j : ℕ) (hj : 1 ≤ j) :
    ∑ k ∈ Finset.range l, (ζ ^ k) ^ (l ^ j) = (l : C) := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have h1 : ∀ k, (ζ ^ k) ^ (l ^ (i + 1)) = 1 := by
    intro k
    rw [← pow_mul, mul_comm, pow_mul, pow_succ', pow_mul, hζ.pow_eq_one, one_pow, one_pow]
  simp [h1]

theorem coeff_sum_rescale {l : ℕ} {ζ : C} (hζ : IsPrimitiveRoot ζ l) (j : ℕ) (hj : 1 ≤ j) (f : PowerSeries C) :
    PowerSeries.coeff (l ^ j) (∑ k ∈ Finset.range l, PowerSeries.rescale (ζ ^ k) f) =
      (l : C) * PowerSeries.coeff (l ^ j) f := by

  rw [map_sum]
  simp only [PowerSeries.coeff_rescale]
  rw [← Finset.sum_mul, sum_root_pow hζ j hj]

section MM

variable {V : VF C}

theorem mmA_add {a b : C} (ha : V.MM a) (hb : V.MM b) : V.MM (a + b) := by
  unfold VF.MM at *
  exact lt_of_lt_of_le (lt_min ha hb) (V.v.map_add a b)

theorem mmA_zero : V.MM (0 : C) := by
  unfold VF.MM
  simp

theorem mmA_sum {ι : Type} (s : Finset ι) (f : ι → C) (h : ∀ i ∈ s, V.MM (f i)) : V.MM (∑ i ∈ s, f i) :=
  Finset.sum_induction f (fun x => V.MM x) (fun _ _ => mmA_add) mmA_zero h

theorem mmA_mul_int {a b : C} (ha : V.MM a) (hb : V.Ge 0 b) : V.MM (a * b) := by
  rw [mul_comm]
  exact MaximalIdealCongruence.mm_mul_ge' hb ha

end MM

end SelfConjCharts

open SelfConjCharts in
theorem good_curve_closed : GoodCurveClosed := by
  intro C _ _ V d I _ κ _ X hB H ζ hζ g a w x hG hV2
  have hl2 := V.l_prime.two_le
  have hl0 : 0 < V.l := by omega
  have hxT : x ∈ X.TySet V g := hG.1.1
  have hx1 : ∀ c, x 1 (Sum.inl c) = 0 := hG.2

  have hyT : Vpow 1 (fun i n => (V.l : C) * x (i + 2) n) ∈ X.TySet V g := by
    have hF := (H g).Fm x hxT
    have h3 := (H g).t3 (fun q => (RawChart.cart (H g)).c0' x q) (fun q => hG.c0'_int q)
    have hsub := (H g).add _ _ hF ((H g).neg _ h3)
    convert hsub using 1
    funext i n
    cases i with
    | zero =>
      cases n with
      | inl c => simp [Vpow, Fs, const0, hx1 c]
      | inr q => simp [Vpow, Fs, const0, Cart.c0']
    | succ i => simp [Vpow, Fs, const0]
  have hyT' := X.unV_mem V g hB.lg0 hB.exlg hζ _ hyT
  obtain ⟨γ, lam, hγ, hlam, hγ1, hγ2⟩ := id hxT
  obtain ⟨δ, -, hδ, -, hδ1, -⟩ := hyT'
  refine ⟨γ, δ, hγ, hδ, ?_, ?_, ?_⟩
  ·
    intro i
    rw [hδ1 i, hγ1 i, subst_pow_sum_smul (by positivity)]
    simp only [rescale_sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Finset.smul_sum, sum_rescale_tyS_two hl2 hζ _ (hx1 c)]
  · intro i
    rw [coeff_one_of_mem X hB (x := fun i n => (V.l : C) * x (i + 2) n) (fun i => (hδ i).1) hδ1 i]
    exact mmA_sum _ _ fun c _ => MaximalIdealCongruence.mm_mul_ge' (hB.uint g c i) (hV2 c)
  · intro q
    have hA : ∀ n, PowerSeries.coeff n (alongCv γ (X.sg (X.u (1 - g) q))) =
        PowerSeries.coeff n (lam q) - PowerSeries.coeff n (tyS V.l fun s => x s (Sum.inr q)) +
          ∑ c : I g, (if X.ty g c = X.ty (1 - g) q then
            X.sg1 (X.u g c) (X.u (1 - g) q) * PowerSeries.coeff n (tyS V.l fun s => x s (Sum.inl c)) else 0) := by
      intro n
      have e := congrArg (PowerSeries.coeff n) (hγ2 q)

      simp only [map_add (f := _), map_sub, map_sum, apply_ite (PowerSeries.coeff n), PowerSeries.coeff_smul, map_zero,
      smul_eq_mul] at e
      linear_combination e
    have hT1 : ∀ b : ℕ → C, PowerSeries.coeff V.l (tyS V.l b) = b 1 := fun b => by
      simpa using coeff_tyS_pow hl2 b 1
    have hT2 : ∀ b : ℕ → C, PowerSeries.coeff (V.l ^ 2) (tyS V.l b) = b 2 := fun b => coeff_tyS_pow hl2 b 2
    have hN1 : ∀ f : PowerSeries C, PowerSeries.coeff V.l (∑ k ∈ Finset.range V.l, PowerSeries.rescale (ζ ^ k) f) =
        (V.l : C) * PowerSeries.coeff V.l f := fun f => by simpa using coeff_sum_rescale hζ 1 le_rfl f
    have hN2 : ∀ f : PowerSeries C,
        PowerSeries.coeff (V.l ^ 2) (∑ k ∈ Finset.range V.l, PowerSeries.rescale (ζ ^ k) f) =
          (V.l : C) * PowerSeries.coeff (V.l ^ 2) f := fun f => coeff_sum_rescale hζ 2 (by norm_num) f
    have hl2pos : 0 < V.l ^ 2 := by positivity
    have hS1 : ∀ f : PowerSeries C,
        PowerSeries.coeff V.l (PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ (V.l ^ 2)) f) = 0 := fun f =>
      coeff_subst_X_pow_of_not_dvd hl2pos f V.l (fun h => by
        have := Nat.le_of_dvd hl0 h
        nlinarith)
    have hS2 : ∀ f : PowerSeries C,
        PowerSeries.coeff (V.l ^ 2) (PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ (V.l ^ 2)) f) =
          PowerSeries.coeff 1 f := fun f => by simpa using coeff_subst_X_pow hl2pos f 1
    refine ⟨hG.c0'_int q, ?_, ?_⟩
    · have e : PowerSeries.coeff V.l (phi X V.l ζ γ δ (X.u (1 - g) q)) - (RawChart.cart (H g)).c0' x q =
          -((V.l : C) * PowerSeries.coeff V.l (lam q)) := by
        unfold phi
        rw [map_sub, hS1, hN1, hA]
        simp only [hT1, hx1, mul_zero, ite_self, Finset.sum_const_zero, add_zero, Cart.c0']
        ring
      rw [e]
      exact MaximalIdealCongruence.mm_neg (MaximalIdealCongruence.mm_l_mul ((hlam q).2 _))
    · have hB1 : PowerSeries.coeff 1 (alongCv δ (X.sg (X.u (1 - g) q))) =
          ∑ c : I g, ((V.l : C) * x 2 (Sum.inl c)) * X.sg1 (X.u g c) (X.u (1 - g) q) := by
        rw [coeff_alongCv_low le_rfl (fun j m hm => by
            obtain rfl : m = 0 := by omega
            rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, (hδ j).1]) (X.constantCoeff_sg hB.axis0 _)]
        simp only [coeff_one_of_mem X hB (x := fun i n => (V.l : C) * x (i + 2) n) (fun i => (hδ i).1) hδ1,
          RawChart.sg1, Finset.mul_sum, zero_add]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun j _ => ?_
        ring
      have key : (∑ c : I g, ((V.l : C) * x 2 (Sum.inl c)) * X.sg1 (X.u g c) (X.u (1 - g) q)) -
          (V.l : C) * ∑ c : I g, (if X.ty g c = X.ty (1 - g) q then
            X.sg1 (X.u g c) (X.u (1 - g) q) * x 2 (Sum.inl c) else 0) =
          ∑ c : I g, (if X.ty g c = X.ty (1 - g) q then 0 else
            ((V.l : C) * x 2 (Sum.inl c)) * X.sg1 (X.u g c) (X.u (1 - g) q)) := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun c _ => ?_
        split_ifs <;> ring
      have e : PowerSeries.coeff (V.l ^ 2) (phi X V.l ζ γ δ (X.u (1 - g) q)) - (V.l : C) * x 2 (Sum.inr q) =
          (∑ c : I g, (if X.ty g c = X.ty (1 - g) q then 0 else
            ((V.l : C) * x 2 (Sum.inl c)) * X.sg1 (X.u g c) (X.u (1 - g) q))) +
            -((V.l : C) * PowerSeries.coeff (V.l ^ 2) (lam q)) := by
        unfold phi
        rw [map_sub, hS2, hN2, hA, hB1]
        simp only [hT2]
        linear_combination key
      rw [e]
      refine mmA_add (mmA_sum _ _ fun c _ => ?_) (MaximalIdealCongruence.mm_neg (MaximalIdealCongruence.mm_l_mul ((hlam q).2 _)))
      split_ifs with hm
      · exact mmA_zero
      · exact mmA_mul_int (hV2 c) (hB.hmis g c q hm)

end Formalism.L2.FormalSeriesBounds
end
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.CoeffIdentitySelfConjOfFourOpen

section

@[expose] public section

noncomputable section

namespace Formalism.L2.FormalSeriesBounds

theorem r1sFrob_holds : PowerSeriesFrobeniusCongruence := frobPow_smul

theorem r1sRoots_holds : RootsOfUnityProductCongruence := fun C _ V ζ hζ j f hf μ => rootsProd C V ζ hζ j f hf μ

theorem coeffIdentity_selfConj_of_four_open (hHL : GaugeLeadingTermLinear) (hHR : GaugeRescalingSymmetry) (hHI : IntegralUnitFamilies) (hGe : GenericPointUnitCongruence) : CoefficientIdentitySelfConjugate :=
  coeffIdentity_selfConj_of_four good_curve_closed r1sRestB_holds
    (r1sRestC_of r1sFrob_holds r1sRoots_holds r1sExpLow_holds hHL hHR hHI hGe) biadditive_on_columns

end Formalism.L2.FormalSeriesBounds
end
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.RescaleInV

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

namespace SelfConjPoints

variable {C : Type} [Field C] {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]

def pairSubst {τ : Type} (a b : κ → MvPowerSeries τ C) : Fin 2 × κ → MvPowerSeries τ C :=
  fun q => if q.1 = 0 then a q.2 else b q.2

def hAt (X : RawChart C d I κ) {τ : Type} (a b : κ → MvPowerSeries τ C) : MvPowerSeries τ C :=
  MvPowerSeries.subst (pairSubst a b) X.h

def inV (j : Fin 2) (f : PowerSeries C) : MvPowerSeries (Fin 2) C :=
  PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries (Fin 2) C) f

def HH (X : RawChart C d I κ) (x z : κ → PowerSeries C) : MvPowerSeries (Fin 2) C :=
  hAt X (fun i => inV 0 (x i)) (fun i => inV 1 (z i))

def rs (j : Fin 2) (c : C) : MvPowerSeries (Fin 2) C →+* MvPowerSeries (Fin 2) C :=
  MvPowerSeries.rescale (fun i => if i = j then c else 1)

def rc (c : C) (γ : κ → PowerSeries C) : κ → PowerSeries C := fun i => PowerSeries.rescale c (γ i)

theorem hsX (j : Fin 2) : MvPowerSeries.HasSubst (fun _ : Unit => (MvPowerSeries.X j : MvPowerSeries (Fin 2) C)) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => MvPowerSeries.constantCoeff_X _

theorem inV_cc (j : Fin 2) {f : PowerSeries C} (hf : PowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (inV j f) = 0 :=
  constantCoeff_subst_zero (fun _ => MvPowerSeries.constantCoeff_X _) hf

theorem rescale_inV (w : Fin 2 → C) (j : Fin 2) (f : PowerSeries C) :
    MvPowerSeries.rescale w (inV j f) = inV j (PowerSeries.rescale (w j) f) := by
  have hw : MvPowerSeries.HasSubst (w • MvPowerSeries.X : Fin 2 → MvPowerSeries (Fin 2) C) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => by simp
  have hc : MvPowerSeries.HasSubst (fun _ : Unit => (w j • PowerSeries.X : PowerSeries C)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => by
      show MvPowerSeries.constantCoeff (w j • (PowerSeries.X : PowerSeries C)) = 0
      rw [MvPowerSeries.smul_eq_C_mul, map_mul,
        show MvPowerSeries.constantCoeff (PowerSeries.X : PowerSeries C) = 0 from MvPowerSeries.constantCoeff_X (), mul_zero]
  unfold inV
  rw [MvPowerSeries.rescale_eq_subst, PowerSeries.rescale_eq_subst]
  unfold PowerSeries.subst
  rw [MvPowerSeries.subst_comp_subst_apply (hsX j) hw, MvPowerSeries.subst_comp_subst_apply hc (hsX j)]
  congr 1
  funext u
  rw [MvPowerSeries.subst_X hw, ← MvPowerSeries.coe_substAlgHom (hsX j), map_smul, MvPowerSeries.coe_substAlgHom (hsX j)]
  have h1 : MvPowerSeries.subst (fun _ : Unit => (MvPowerSeries.X j : MvPowerSeries (Fin 2) C)) (PowerSeries.X : PowerSeries C) =
      MvPowerSeries.X j := MvPowerSeries.subst_X (hsX j) ()
  rw [h1]
  rfl

theorem rescale_HH (X : RawChart C d I κ) (x z : κ → PowerSeries C) (hx : ∀ i, PowerSeries.constantCoeff (x i) = 0)
    (hz : ∀ i, PowerSeries.constantCoeff (z i) = 0) (w : Fin 2 → C) :
    MvPowerSeries.rescale w (HH X x z) = HH X (rc (w 0) x) (rc (w 1) z) := by
  have hP : MvPowerSeries.HasSubst (pairSubst (fun i => inV 0 (x i)) (fun i => inV 1 (z i))) := by
    refine MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => ?_
    unfold pairSubst
    split_ifs
    · exact inV_cc 0 (hx q.2)
    · exact inV_cc 1 (hz q.2)
  have hw : MvPowerSeries.HasSubst (w • MvPowerSeries.X : Fin 2 → MvPowerSeries (Fin 2) C) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => by simp
  unfold HH hAt
  rw [MvPowerSeries.rescale_eq_subst, MvPowerSeries.subst_comp_subst_apply hP hw]
  congr 1
  funext q
  rw [← MvPowerSeries.rescale_eq_subst]
  unfold pairSubst rc
  split_ifs
  · exact rescale_inV w 0 (x q.2)
  · exact rescale_inV w 1 (z q.2)

end SelfConjPoints


open SelfConjPoints in
theorem r1sHResc (C : Type) [Field C] (d : ℕ) (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ]
    (X : RawChart C d I κ) (x z : κ → PowerSeries C) (hx : ∀ i, PowerSeries.constantCoeff (x i) = 0)
    (hz : ∀ i, PowerSeries.constantCoeff (z i) = 0) (c : C) :
    HH X (rc c x) z = rs 0 c (HH X x z) ∧ HH X x (rc c z) = rs 1 c (HH X x z) := by
  have e1 : ∀ y : κ → PowerSeries C, rc 1 y = y := fun y => by
    funext i; unfold rc; rw [PowerSeries.rescale_one]; rfl
  refine ⟨?_, ?_⟩
  · unfold rs
    rw [rescale_HH X x z hx hz]
    simp [e1]
  · unfold rs
    rw [rescale_HH X x z hx hz]
    simp [e1]

end Formalism.L2.FormalSeriesBounds
end
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.CoeffIdentitySelfConjOfTwo

section

@[expose] public section

noncomputable section

namespace Formalism.L2.FormalSeriesBounds

theorem r1sHInt_holds : IntegralUnitFamilies :=
  fun C _ _ V d I _ κ _ X _ hBi ζ hζ n hn γ δ c hγ hδ hc hN => SelfConjGauge.hInt_core V X hBi ζ hζ n hn γ δ c hγ hδ hc hN

theorem r1sHResc_holds : GaugeRescalingSymmetry := r1sHResc

theorem coeffIdentity_selfConj_of_two (hHL : GaugeLeadingTermLinear) (hGe : GenericPointUnitCongruence) : CoefficientIdentitySelfConjugate :=
  coeffIdentity_selfConj_of_four_open hHL r1sHResc_holds r1sHInt_holds hGe

end Formalism.L2.FormalSeriesBounds
end
end
end
