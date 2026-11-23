module

public import Formalism.SharpRestriction.GrowthBounds.ExponentialPartialDerivatives.SumAtOf
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePCEqDer
import Formalism.FormalGroupLog.FormalGroupLogProofs.ChainRule
import Formalism.LocalToGlobal.CharacterGerms.ConstMemTypeSetOfNonneg
import Formalism.LocalToGlobal.CharacterGerms.RowTieCartAdd
import Formalism.LocalToGlobal.CharacterGerms.RowTieCartFB
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePAddCvSelf
import Formalism.LocalToGlobal.CharacterGerms.RowTiePOActLog
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePGerm
public import Formalism.LocalToGlobal.CharacterGerms.RowTieCartAdd
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePCEqSum2
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Formalism.LocalToGlobal.CharacterGerms.RowTiePCEqM2
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePCEqM2

-- Source module: Formalism.LocalToGlobal.CharacterGerms.RowTiePCEqEx

section

@[expose] public section

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace Formalism.L2.FormalSeriesBounds

open PartialDerivEval RowTiePCEqM

namespace RowTiePCEqEx

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

theorem pderiv_eval_single {n : ℕ} {a : Fin 1 → Pt C n dd} (ha : Z0 a) (f : PS C 1 dd) (q : Fin n × Fin dd) :
    pderiv (R := C) q (ev a f) = ∑ j, ev a (pderiv (R := C) ((0 : Fin 1), j) f) * pderiv (R := C) q (a 0 j) := by
  unfold ev
  rw [Formalism.G.LogCR.pderiv_subst (a := fun p : Fin 1 × Fin dd => a p.1 p.2) (fun p => ha p.1 p.2) f q,
    Fintype.sum_prod_type, Fin.sum_univ_one]

theorem germEval_oneStandardPoint_self (f : PS C 1 dd) : ev (n := 1) ![pt C dd 0] f = f := by
  unfold ev
  have : (fun p : Fin 1 × Fin dd => (![pt C dd 0] : Fin 1 → Pt C 1 dd) p.1 p.2) = X := by
    funext p
    obtain ⟨k, j⟩ := p
    fin_cases k
    rfl
  rw [this, subst_self]
  rfl

theorem constantCoeff_pderiv {σ : Type} (q : σ) (f : MvPowerSeries σ C) :
    constantCoeff (pderiv (R := C) q f) = coeff (Finsupp.single q 1) f := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_pderiv, zero_add]
  simp

theorem ev_zero_pt {n : ℕ} (f : PS C 1 dd) : ev (n := n) (![0] : Fin 1 → Pt C n dd) f = MvPowerSeries.C (constantCoeff f) := by
  apply Formalism.L2.FormalSeriesBounds.OActLog.ev_zero_pt <;> assumption

theorem ex_lin (Y : FBChart C V O dd) (i m : Fin dd) :
    constantCoeff (pderiv (R := C) ((0 : Fin 1), i) (Y.ex m)) = if i = m then 1 else 0 := by
  have hZ : Z0 (![Y.ex] : Fin 1 → Pt C 1 dd) := z0_1 _ Y.ex_const
  have h : constantCoeff (pderiv (R := C) ((0 : Fin 1), i) (comp1 Y.lg Y.ex m)) =
      constantCoeff (pderiv (R := C) ((0 : Fin 1), i) (pt C (n := 1) dd 0 m)) := by
    rw [Y.lg_ex]
  unfold comp1 at h

  rw [pderiv_eval_single hZ, map_sum] at h
  simp only [map_mul, constantCoeff_ev hZ, constantCoeff_pderiv] at h
  have hl : ∀ k, coeff (Finsupp.single ((0 : Fin 1), k) 1) (Y.lg m) = if k = m then 1 else 0 := by
    intro k
    rw [Y.lg_lin m _ (by simp), coeff_X]
    by_cases hk : k = m
    · rw [if_pos hk, if_pos (by rw [hk])]
    · rw [if_neg hk, if_neg]
      intro e
      exact hk (Prod.mk.inj (Finsupp.single_left_injective one_ne_zero e)).2
  simp only [hl, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  rw [← constantCoeff_pderiv] at h
  change constantCoeff (pderiv (R := C) ((0 : Fin 1), i) (Y.ex m)) =
    coeff (Finsupp.single ((0 : Fin 1), i) 1) (X ((0 : Fin 1), m) : PS C 1 dd) at h
  rw [h, coeff_X]
  by_cases him : i = m
  · rw [if_pos him, if_pos (by rw [him])]
  · rw [if_neg him, if_neg]
    intro e
    exact him (Prod.mk.inj (Finsupp.single_left_injective one_ne_zero e)).2

end RowTiePCEqEx

namespace RowTiePCEqEx

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

theorem ex_add (Y : FBChart C V O dd) (j : Fin dd) :
    ev (n := 2) ![fun m => pt C (n := 2) dd 0 m + pt C dd 1 m] (Y.ex j) =
      ev (n := 2) ![comp1 Y.ex (pt C (n := 2) dd 0), comp1 Y.ex (pt C (n := 2) dd 1)] (Y.B.G.F j) := by
  have hA0 : ∀ m, constantCoeff (comp1 Y.ex (pt C (n := 2) dd 0) m) = 0 := fun m =>
    const_ev (z0_1 _ (z0_pt 0)) (Y.ex_const m)
  have hB0 : ∀ m, constantCoeff (comp1 Y.ex (pt C (n := 2) dd 1) m) = 0 := fun m =>
    const_ev (z0_1 _ (z0_pt 1)) (Y.ex_const m)
  have hAB : Z0 (![comp1 Y.ex (pt C (n := 2) dd 0), comp1 Y.ex (pt C (n := 2) dd 1)] : Fin 2 → Pt C 2 dd) := by
    intro k i; fin_cases k
    · exact hA0 i
    · exact hB0 i
  have hZex : Z0 (![Y.ex] : Fin 1 → Pt C 1 dd) := z0_1 _ Y.ex_const
  have hlgk : ∀ (k : Fin 2) m, ev (n := 2) ![comp1 Y.ex (pt C (n := 2) dd k)] (Y.lg m) = pt C dd k m := by
    intro k m
    have e : ev (n := 2) ![comp1 Y.ex (pt C (n := 2) dd k)] (Y.lg m) =
        ev (n := 2) ![pt C dd k] (ev (n := 1) ![Y.ex] (Y.lg m)) := by
      rw [ev_ev hZex (z0_1 _ (z0_pt k))]
      congr 1
      funext k' i
      fin_cases k'
      rfl
    rw [e, show ev (n := 1) ![Y.ex] (Y.lg m) = comp1 Y.lg Y.ex m from rfl, Y.lg_ex,
      show (pt C (n := 1) dd 0 m) = X ((0 : Fin 1), m) from rfl, ev_X (z0_1 _ (z0_pt k))]
    rfl
  set P : Pt C 2 dd := fun j => ev (n := 2) ![comp1 Y.ex (pt C (n := 2) dd 0), comp1 Y.ex (pt C (n := 2) dd 1)]
    (Y.B.G.F j) with hP
  have hP0 : ∀ m, constantCoeff (P m) = 0 := fun m => const_ev hAB (Y.B.G.const m)
  have hZP : Z0 (![P] : Fin 1 → Pt C 2 dd) := z0_1 _ hP0
  have hPl : ∀ m, ev (n := 2) ![P] (Y.lg m) = pt C (n := 2) dd 0 m + pt C dd 1 m := by
    intro m
    have e1 : ev (n := 2) ![P] (Y.lg m) =
        ev (n := 2) ![comp1 Y.ex (pt C (n := 2) dd 0), comp1 Y.ex (pt C (n := 2) dd 1)]
          (ev (n := 2) ![addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C dd 1)] (Y.lg m)) := by
      rw [ev_ev (z0_1 _ (const_addOf Y 0 1)) hAB]
      congr 1
      funext k i
      fin_cases k
      show P i = _
      rw [hP]
      exact congrArg _ (addOf_pts Y.B.G.F i).symm
    rw [e1, Y.lg_add m, ev_add hAB, ev_ev (z0_1 _ (z0_pt 0)) hAB, ev_ev (z0_1 _ (z0_pt 1)) hAB]
    have e2 : ∀ k : Fin 2, (fun k' i => ev (n := 2)
        (![comp1 Y.ex (pt C (n := 2) dd 0), comp1 Y.ex (pt C (n := 2) dd 1)] : Fin 2 → Pt C 2 dd)
        ((![pt C (n := 2) dd k] : Fin 1 → Pt C 2 dd) k' i)) = ![comp1 Y.ex (pt C (n := 2) dd k)] := by
      intro k
      funext k' i
      fin_cases k'
      show ev (n := 2) _ (X (k, i) : PS C 2 dd) = _
      rw [ev_X hAB]
      fin_cases k <;> rfl
    rw [e2 0, e2 1, hlgk 0, hlgk 1]
  have hPS : ∀ j, P j = ev (n := 2) ![fun m => pt C (n := 2) dd 0 m + pt C dd 1 m] (Y.ex j) := by
    intro j
    have e1 : ev (n := 2) ![P] (comp1 Y.ex Y.lg j) = P j := by
      rw [Y.ex_lg, show (pt C (n := 1) dd 0 j) = X ((0 : Fin 1), j) from rfl, ev_X hZP]
      rfl
    rw [← e1]
    unfold comp1
    rw [ev_ev (z0_1 _ Y.lg_const) hZP]
    congr 1
    funext k i
    fin_cases k
    exact hPl i
  exact (hPS j).symm

end RowTiePCEqEx


open RowTiePCEqEx in
theorem exDer_holds {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
    (Y : FBChart C V O dd) : ExDerSt Y := by
  intro v j
  have hZex : Z0 (![Y.ex] : Fin 1 → Pt C 1 dd) := z0_1 _ Y.ex_const
  have hQ : Z0 ((![pt C dd 0, 0] : Fin 2 → Pt C 1 dd)) := z0_p0 _ (z0_pt 0)
  have hS0 : ∀ m, constantCoeff (pt C (n := 2) dd 0 m + pt C dd 1 m) = 0 := fun m => by
    rw [map_add (f := _), z0_pt, z0_pt, add_zero]
  have hZS : Z0 (![fun m => pt C (n := 2) dd 0 m + pt C dd 1 m] : Fin 1 → Pt C 2 dd) := z0_1 _ hS0
  have hA0 : ∀ m, constantCoeff (comp1 Y.ex (pt C (n := 2) dd 0) m) = 0 := fun m =>
    const_ev (z0_1 _ (z0_pt 0)) (Y.ex_const m)
  have hB0 : ∀ m, constantCoeff (comp1 Y.ex (pt C (n := 2) dd 1) m) = 0 := fun m =>
    const_ev (z0_1 _ (z0_pt 1)) (Y.ex_const m)
  have hAB : Z0 (![comp1 Y.ex (pt C (n := 2) dd 0), comp1 Y.ex (pt C (n := 2) dd 1)] : Fin 2 → Pt C 2 dd) := by
    intro k i; fin_cases k
    · exact hA0 i
    · exact hB0 i
  have pderiv_pt_ne {k : Fin 2} (hk : k ≠ 1) (i m : Fin dd) :
      pderiv (R := C) ((1 : Fin 2), i) (pt C dd k m) = 0 :=
    pderiv_X_of_ne (fun e => hk (Prod.mk.inj e).1)
  have sum_pderiv_pt (i : Fin dd) (a : Fin dd → PS C 2 dd) :
      ∑ m, a m * pderiv (R := C) ((1 : Fin 2), i) (pt C dd 1 m) = a i := by
    rw [Finset.sum_eq_single i]
    · rw [show pt C dd 1 i = X ((1 : Fin 2), i) from rfl, pderiv_X_self, mul_one]
    · intro m _ hm
      rw [show pt C dd 1 m = X ((1 : Fin 2), m) from rfl,
        pderiv_X_of_ne (fun e => hm (Prod.mk.inj e).2), mul_zero]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  have hdk : ∀ (k : Fin 2) (i m : Fin dd), pderiv (R := C) ((1 : Fin 2), i) (comp1 Y.ex (pt C (n := 2) dd k) m) =
      if k = 1 then ev (n := 2) ![pt C dd 1] (pderiv (R := C) ((0 : Fin 1), i) (Y.ex m)) else 0 := by
    intro k i m
    show pderiv (R := C) _ (ev (n := 2) ![pt C (n := 2) dd k] (Y.ex m)) = _
    rw [pderiv_eval_single (z0_1 _ (z0_pt k))]
    split_ifs with hk
    · subst hk
      exact sum_pderiv_pt i _
    · exact Finset.sum_eq_zero fun l _ => by
        rw [show ((![pt C (n := 2) dd k] : Fin 1 → Pt C 2 dd) 0 l) = pt C dd k l from rfl, pderiv_pt_ne hk i l,
          mul_zero]
  have hpt1 : ∀ k : Fin 2, (fun k' l => ev (n := 1) (![pt C dd 0, 0] : Fin 2 → Pt C 1 dd) ((![pt C (n := 2) dd k] : Fin 1 → Pt C 2 dd) k' l)) =
      ![((![pt C dd 0, 0] : Fin 2 → Pt C 1 dd)) k] := by
    intro k
    funext k' l
    fin_cases k'
    exact ev_X hQ k l
  have hL : ∀ i, ev (n := 1) (![pt C dd 0, 0] : Fin 2 → Pt C 1 dd) (pderiv (R := C) ((1 : Fin 2), i)
      (ev (n := 2) ![fun m => pt C (n := 2) dd 0 m + pt C dd 1 m] (Y.ex j))) = pderiv (R := C) ((0 : Fin 1), i) (Y.ex j) := by
    intro i
    rw [pderiv_eval_single hZS]
    have e0 : ∀ m, pderiv (R := C) ((1 : Fin 2), i)
        ((![fun m => pt C (n := 2) dd 0 m + pt C dd 1 m] : Fin 1 → Pt C 2 dd) 0 m) =
        pderiv (R := C) ((1 : Fin 2), i) (pt C (n := 2) dd 1 m) := fun m => by
      show pderiv (R := C) _ (pt C (n := 2) dd 0 m + pt C dd 1 m) = _
      rw [map_add (f := _), pderiv_pt_ne (by decide) i m, zero_add]
    simp only [e0]
    rw [sum_pderiv_pt i, ev_ev hZS hQ]
    have e : (fun k m => ev (n := 1) (![pt C dd 0, 0] : Fin 2 → Pt C 1 dd)
        ((![fun m => pt C (n := 2) dd 0 m + pt C dd 1 m] : Fin 1 → Pt C 2 dd) k m)) = ![pt C (n := 1) dd 0] := by
      funext k m
      fin_cases k
      show ev (n := 1) (![pt C dd 0, 0] : Fin 2 → Pt C 1 dd) ((X ((0 : Fin 2), m) : PS C 2 dd) + X ((1 : Fin 2), m)) = pt C dd 0 m
      rw [ev_add hQ, ev_X hQ, ev_X hQ]
      show pt C dd 0 m + 0 = pt C dd 0 m
      rw [add_zero]
    rw [e, germEval_oneStandardPoint_self]
  have eB : ∀ g : PS C 1 dd, ev (n := 1) (![pt C dd 0, 0] : Fin 2 → Pt C 1 dd) (ev (n := 2) ![pt C dd 1] g) = MvPowerSeries.C (constantCoeff g) := by
    intro g
    rw [ev_ev (z0_1 _ (z0_pt 1)) hQ, hpt1 1]
    exact ev_zero_pt g
  have eAB : ∀ f : PS C 2 dd, ev (n := 1) (![pt C dd 0, 0] : Fin 2 → Pt C 1 dd)
      (ev (n := 2) ![comp1 Y.ex (pt C (n := 2) dd 0), comp1 Y.ex (pt C (n := 2) dd 1)] f) =
      ev (n := 1) ![Y.ex, 0] f := by
    intro f
    rw [ev_ev hAB hQ]
    congr 1
    funext k m
    fin_cases k
    · show ev (n := 1) (![pt C dd 0, 0] : Fin 2 → Pt C 1 dd) (ev (n := 2) ![pt C dd 0] (Y.ex m)) = Y.ex m
      rw [ev_ev (z0_1 _ (z0_pt 0)) hQ, hpt1 0]
      exact germEval_oneStandardPoint_self _
    · show ev (n := 1) (![pt C dd 0, 0] : Fin 2 → Pt C 1 dd) (ev (n := 2) ![pt C dd 1] (Y.ex m)) = 0
      rw [eB, Y.ex_const, map_zero]
  have hR : ∀ i, ev (n := 1) (![pt C dd 0, 0] : Fin 2 → Pt C 1 dd) (pderiv (R := C) ((1 : Fin 2), i)
      (ev (n := 2) ![comp1 Y.ex (pt C (n := 2) dd 0), comp1 Y.ex (pt C (n := 2) dd 1)] (Y.B.G.F j))) =
      ev (n := 1) ![Y.ex] (ev (n := 1) ![pt C dd 0, 0] (pderiv (R := C) ((1 : Fin 2), i) (Y.B.G.F j))) := by
    intro i
    rw [pderiv_eval_pair hAB]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hdk,
      ite_eq_right (by decide : (0 : Fin 2) ≠ 1), ite_true,
      mul_zero, Finset.sum_const_zero, zero_add]
    rw [ev_sum hQ]
    simp only [ev_mul hQ, eAB, eB, ex_lin]
    rw [Finset.sum_eq_single i]
    · rw [if_pos rfl, map_one, mul_one, ev_ev (z0_p0 _ (z0_pt 0)) hZex]
      congr 1
      funext k m
      fin_cases k
      · exact (ev_X hZex 0 m).symm
      · exact (ev_zero hZex).symm
    · intro m _ hm
      rw [if_neg (Ne.symm hm), map_zero, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  have key : ∀ i, pderiv (R := C) ((0 : Fin 1), i) (Y.ex j) =
      ev (n := 1) ![Y.ex] (ev (n := 1) ![pt C dd 0, 0] (pderiv (R := C) ((1 : Fin 2), i) (Y.B.G.F j))) := by
    intro i
    rw [← hL i, ex_add Y j, hR i]
  unfold FBChart.dF
  rw [ev_sum hZex]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ev_mul hZex, ev_C, key i]

end Formalism.L2.FormalSeriesBounds
end
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.ExponentialPartialDerivatives.UnshiftEvalEqSubstRawUnit

section

@[expose] public section

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds
namespace CEqGen

open Formalism.IncomingBounds PartialDerivEval RowTiePCEq RowTiePCEqSum RowTiePCEqDer ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
  (Y : FBChart C V O dd) (d : ℕ) {I : Fin 2 → Type} [∀ g, Fintype (I g)] (u : ∀ g, I g → Fin dd → C)

def rawU : RawChart C d I (Fin dd) where
  lg := fun i => un1 (Y.lg i)
  ex := fun i => un1 (Y.ex i)
  h := Y.h
  k := Y.k
  u := u
  ty := fun _ _ => 0
  n := 0
  j := 0
  j' := 0
  big := fun _ _ => False

theorem rawU_sg (v : Fin dd → C) : (rawU Y d u).sg v = un1 (Y.sgP v) := Y.rawCol_sg v

theorem constantCoeff_rawUnit_exp (i : Fin dd) : MvPowerSeries.constantCoeff ((rawU Y d u).ex i) = 0 := by
  show MvPowerSeries.constantCoeff (un1 (Y.ex i)) = 0
  rw [constantCoeff_uncurry, Y.ex_const i]

theorem unshift_eval_eq_subst_rawUnit (f : PS C 1 dd) :
    un1 (ev (n := 1) ![Y.ex] f) = MvPowerSeries.subst (rawU Y d u).ex (un1 f) := by
  show _ = MvPowerSeries.subst (fun j => un1 (Y.ex j)) (un1 f)
  rw [eval_single_eq_subst, subst_oneVariableUncurry_eq_subst (b := fun q : Fin 1 × Fin dd => Y.ex q.2) (fun q => Y.ex_const q.2),
    subst_singlePointUncurry (fun j => by rw [constantCoeff_uncurry, Y.ex_const j])]

theorem pderiv_expG_U (hE : ExDerSt Y) (g : Fin 2) (k : I g)
    (j : Fin dd) :
    MvPowerSeries.pderiv (R := C) k ((rawU Y d u).expG g j) =
      MvPowerSeries.subst ((rawU Y d u).expG g) (un1 (Y.dF ((rawU Y d u).u g k) j)) := by
  have hlin0 := lin_const (rawU Y d u) g
  have hL := MvPowerSeries.hasSubst_of_constantCoeff_zero hlin0
  have hx0 : ∀ i, MvPowerSeries.constantCoeff ((rawU Y d u).ex i) = 0 := constantCoeff_rawUnit_exp Y d u
  have e1 : MvPowerSeries.subst (rawU Y d u).ex (un1 (Y.dF ((rawU Y d u).u g k) j)) =
      ∑ i, MvPowerSeries.C ((rawU Y d u).u g k i) * MvPowerSeries.pderiv (R := C) i ((rawU Y d u).ex j) := by
    rw [← unshift_eval_eq_subst_rawUnit Y d u, ← hE, uncurry_linear_combination]
    simp only [← pderiv_uncurry]
    rfl
  unfold RawChart.expG
  rw [Formalism.G.LogCR.pderiv_subst hlin0,
    ← MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero hx0) hL]
  simp only [pderiv_lin]

  rw [e1, ← MvPowerSeries.coe_substAlgHom hL, map_sum, MvPowerSeries.coe_substAlgHom]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [MvPowerSeries.subst_mul hL, MvPowerSeries.subst_C, mul_comm]

theorem derAt_rawU (hu : ∀ g c i, V.Ge 0 (u g c i)) : DerAt V (rawU Y d u) := by
  intro g k
  have hvI : ∀ i, V.Ge 0 ((rawU Y d u).u (1 - g) k i) := fun i => hu (1 - g) k i
  have hE0 : ∀ q : Fin 2 × Fin dd, MvPowerSeries.constantCoeff ((rawU Y d u).expPt q.1 q.2) = 0 := fun q => by
    rw [expPt_eq]
    exact upG_const _ (constantCoeff_subst_zero (lin_const (rawU Y d u) q.1) (constantCoeff_rawUnit_exp Y d u q.2))
  have hES := MvPowerSeries.hasSubst_of_constantCoeff_zero hE0
  have hd : ∀ (g' : Fin 2) (j : Fin dd), MvPowerSeries.pderiv (R := C) (⟨1 - g, k⟩ : WV I) ((rawU Y d u).expPt g' j) =
      if g' = 1 - g then MvPowerSeries.subst ((rawU Y d u).expPt (1 - g)) (un1 (Y.dF ((rawU Y d u).u (1 - g) k) j))
      else 0 := by
    intro g' j
    split_ifs with hg
    · rw [hg, expPt_eq, pderiv_upG_same, pderiv_expG_U Y d u (exDer_holds Y) (1 - g) k j,
        upG_subst (1 - g) (a := (rawU Y d u).expG (1 - g))
          (fun i => constantCoeff_subst_zero (lin_const (rawU Y d u) (1 - g)) (constantCoeff_rawUnit_exp Y d u i))]
      congr 1
      funext i
      exact (expPt_eq _ _ _).symm
    · rw [expPt_eq, pderiv_upG_ne (1 - g) g' hg k]
  have hch : MvPowerSeries.pderiv (R := C) (⟨1 - g, k⟩ : WV I)
      (MvPowerSeries.subst (fun q : Fin 2 × Fin dd => (rawU Y d u).expPt q.1 q.2) Y.h) =
      ∑ j, MvPowerSeries.subst (fun q : Fin 2 × Fin dd => (rawU Y d u).expPt q.1 q.2)
          (MvPowerSeries.pderiv (R := C) ((1 - g : Fin 2), j) Y.h) *
        MvPowerSeries.subst ((rawU Y d u).expPt (1 - g)) (un1 (Y.dF ((rawU Y d u).u (1 - g) k) j)) := by
    rw [Formalism.G.LogCR.pderiv_subst hE0, Fintype.sum_prod_type, Finset.sum_eq_single (1 - g)]
    · simp only [hd, if_true]
    · intro g' _ hg'
      simp only [hd, if_neg hg', mul_zero, Finset.sum_const_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  set J : PS C 2 dd := (∑ j, ev (n := 2) ![pt C dd (1 - g)] (Y.dF ((rawU Y d u).u (1 - g) k) j) *
      MvPowerSeries.pderiv (R := C) ((1 - g : Fin 2), j) Y.h) + ev (n := 2) ![pt C dd g] (Y.sgP ((rawU Y d u).u (1 - g) k))
    with hJd
  have hsubD : MvPowerSeries.subst (fun q : Fin 2 × Fin dd => (rawU Y d u).expPt q.1 q.2)
      (∑ j, ev (n := 2) ![pt C dd (1 - g)] (Y.dF ((rawU Y d u).u (1 - g) k) j) *
        MvPowerSeries.pderiv (R := C) ((1 - g : Fin 2), j) Y.h) =
      ∑ j, MvPowerSeries.subst (fun q : Fin 2 × Fin dd => (rawU Y d u).expPt q.1 q.2)
          (MvPowerSeries.pderiv (R := C) ((1 - g : Fin 2), j) Y.h) *
        MvPowerSeries.subst ((rawU Y d u).expPt (1 - g)) (un1 (Y.dF ((rawU Y d u).u (1 - g) k) j)) := by

    rw [← MvPowerSeries.coe_substAlgHom hES, map_sum, MvPowerSeries.coe_substAlgHom]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [MvPowerSeries.subst_mul hES, subst_exp_eval_two _ hE0, mul_comm]
  have hJ : IntS V J := by
    have hg2 : ∀ x : Fin 2, x = 0 ∨ x = 1 := by decide
    rcases hg2 g with rfl | rfl
    · have h := germII_holds Y _ hvI
      convert h using 2
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [ev_pt_dF]
      rfl
    · have h := germIIM_holds Y _ hvI
      convert h using 2
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [ev_pt_dF]
      rfl
  refine ⟨J, hJ, ?_⟩
  rw [dVar_eq]
  show MvPowerSeries.pderiv (R := C) _ (((Y.k : ℕ) : C) •
    MvPowerSeries.subst (fun q : Fin 2 × Fin dd => (rawU Y d u).expPt q.1 q.2) Y.h) = _
  rw [Derivation.map_smul, hch, ← hsubD, hJd, MvPowerSeries.subst_add hES, subst_exp_eval_two _ hE0, rawU_sg Y d u,
    add_sub_cancel_right]
  rfl

theorem addM_rawU : AddM V (rawU Y d u) := by
  intro τ _ γ γ' hγ hγ'
  set ρ : Fin 2 × Fin dd → MvPowerSeries τ C := fun q => ![γ, γ'] q.1 q.2 with hρ
  have hρ0 : ∀ q, MvPowerSeries.constantCoeff (ρ q) = 0 := by
    rintro ⟨b, j⟩
    fin_cases b
    · exact (hγ j).1
    · exact (hγ' j).1
  have hρI : ∀ q, IntS V (ρ q) := by
    rintro ⟨b, j⟩
    fin_cases b
    · exact (hγ j).2
    · exact (hγ' j).2
  have hρS := MvPowerSeries.hasSubst_of_constantCoeff_zero hρ0
  set γ'' : Fin dd → MvPowerSeries τ C := fun j => MvPowerSeries.subst ρ (Y.B.G.F j) with hγ''
  have hγ''0 : ∀ j, MvPowerSeries.constantCoeff (γ'' j) = 0 := fun j =>
    constantCoeff_subst_zero hρ0 (Y.B.G.const j)
  have hev : ∀ (a : Pt C 2 dd), (∀ j, MvPowerSeries.constantCoeff (a j) = 0) → ∀ f : PS C 1 dd,
      MvPowerSeries.subst ρ (ev ![a] f) = MvPowerSeries.subst (fun j => MvPowerSeries.subst ρ (a j)) (un1 f) := by
    intro a ha f
    rw [eval_single_eq_subst, MvPowerSeries.subst_comp_subst_apply
      (MvPowerSeries.hasSubst_of_constantCoeff_zero fun q : Fin 1 × Fin dd => ha q.2) hρS,
      subst_singlePointUncurry (fun j => constantCoeff_subst_zero hρ0 (ha j))]
  have hp0 : (fun j => MvPowerSeries.subst ρ (pt C (n := 2) dd 0 j)) = γ := by
    funext j
    show MvPowerSeries.subst ρ (MvPowerSeries.X ((0 : Fin 2), j)) = γ j
    rw [MvPowerSeries.subst_X hρS]
    rfl
  have hp1 : (fun j => MvPowerSeries.subst ρ (pt C (n := 2) dd 1 j)) = γ' := by
    funext j
    show MvPowerSeries.subst ρ (MvPowerSeries.X ((1 : Fin 2), j)) = γ' j
    rw [MvPowerSeries.subst_X hρS]
    rfl
  have hpa : (fun j => MvPowerSeries.subst ρ (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1) j)) = γ'' := by
    funext j
    rw [addOf_pts]
  have hc0 : ∀ j, MvPowerSeries.constantCoeff (pt C (n := 2) dd 0 j) = 0 := fun j => MvPowerSeries.constantCoeff_X _
  have hc1 : ∀ j, MvPowerSeries.constantCoeff (pt C (n := 2) dd 1 j) = 0 := fun j => MvPowerSeries.constantCoeff_X _
  have hca : ∀ j, MvPowerSeries.constantCoeff (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1) j) = 0 :=
    fun j => by rw [addOf_pts]; exact Y.B.G.const j
  refine ⟨γ'', fun j => ⟨hγ''0 j, IntS.subst hρ0 hρI (Y.intF j)⟩, ?_, ?_⟩
  · intro i
    have h := congrArg (MvPowerSeries.subst ρ) (Y.lg_add i)
    rw [← MvPowerSeries.coe_substAlgHom hρS, map_add (f := _), MvPowerSeries.coe_substAlgHom hρS, hev _ hca, hev _ hc0,
      hev _ hc1, hpa, hp0, hp1] at h
    exact h
  · intro v hv
    have h := IntS.subst hρ0 hρI (germI_holds Y v hv)
    rw [← MvPowerSeries.coe_substAlgHom hρS, map_sub, map_sub, MvPowerSeries.coe_substAlgHom hρS, hev _ hca,
      hev _ hc0, hev _ hc1, hpa, hp0, hp1, ← rawU_sg Y d u v] at h
    exact h

end CEqGen
end Formalism.L2.FormalSeriesBounds
end
end
end
