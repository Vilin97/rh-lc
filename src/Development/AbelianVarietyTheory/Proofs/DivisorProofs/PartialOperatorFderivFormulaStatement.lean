module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClmSupBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzSeminormTranslateSubLineDerivLe
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeminormSliceRLe
public import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormIteratedFDerivPdLe

section

@[expose] public section

open GlobalTheory.SliceSchwartz GlobalTheory.SliceOp
open scoped ContDiff

noncomputable section

namespace GlobalTheory.SliceTaylor

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem norm_padL_le {κ κ' : Type} [Fintype κ] [Fintype κ'] (h : κ → V) :
    ‖(padL (κ' := κ') h : κ ⊕ κ' → V)‖ ≤ ‖h‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  cases i with
  | inl i => simpa [padL] using norm_le_pi_norm h i
  | inr j => simp [padL]

theorem norm_inrL_le (κ κ' : Type) [Fintype κ] [Fintype κ'] :
    ‖(inrL (V := V) κ κ')‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => ?_
  rw [one_mul]
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  cases i with
  | inl i => simp [inrL]
  | inr j => simpa [inrL] using norm_le_pi_norm y j

theorem norm_le_norm_elim_add {κ κ' : Type} [Fintype κ] [Fintype κ'] (x h : κ → V) (y : κ' → V) (s : ℝ) :
    ‖y‖ ≤ ‖(Sum.elim x y : κ ⊕ κ' → V) + s • padL h‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => ?_
  have := norm_le_pi_norm ((Sum.elim x y : κ ⊕ κ' → V) + s • padL h) (Sum.inr j)
  simp only [Pi.add_apply, Pi.smul_apply, padL, Sum.elim_inr, Pi.zero_apply, smul_zero, add_zero] at this
  exact this

theorem norm_iteratedFDeriv_pd_le {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (a : X) (g : SchwartzMap X ℂ) (n : ℕ) (w : X) :
    ‖iteratedFDeriv ℝ n (pd a g) w‖ ≤ ‖a‖ * ‖iteratedFDeriv ℝ (n + 1) g w‖ := by
  have e1 : (⇑(pd a g)) = fun y => fderiv ℝ g y a := by funext y; exact pd_apply a g y
  have hd : Differentiable ℝ (iteratedFDeriv ℝ n g) :=
    g.smooth'.differentiable_iteratedFDeriv (by exact_mod_cast ENat.natCast_lt_top n)
  have e : iteratedFDeriv ℝ n (pd a g) w = fderiv ℝ (iteratedFDeriv ℝ n g) w a := by
    ext m
    rw [e1, ← GlobalTheory.SchwartzTranslate.fderiv_iteratedFDeriv_apply_comm a n g g.smooth']
    have := ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => X) ℂ m).hasFDerivAt.comp
      w (hd w).hasFDerivAt).fderiv
    have e2 : (fun y => iteratedFDeriv ℝ n g y m) =
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => X) ℂ m) ∘ iteratedFDeriv ℝ n g := rfl
    rw [e2, this]
    rfl
  rw [e, ← norm_fderiv_iteratedFDeriv, mul_comm]
  exact (fderiv ℝ (iteratedFDeriv ℝ n g) w).le_opNorm a

theorem elim_add_padL {κ κ' : Type} [Fintype κ] [Fintype κ'] (x h : κ → V) (y : κ' → V) :
    (Sum.elim (x + h) y : κ ⊕ κ' → V) = Sum.elim x y + padL h := by
  funext i
  cases i with
  | inl i => simp [padL]
  | inr j => simp [padL]

theorem seminorm_slice_taylor_le (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (κ κ' : Type) [Fintype κ] [Fintype κ'] (f : SchwartzMap (κ ⊕ κ' → V) ℂ) (k n : ℕ) (x h : κ → V) :
    SchwartzMap.seminorm ℂ k n (sliceR f (x + h) - sliceR f x - sliceR (pd (padL (κ' := κ') h) f) x) ≤
      ‖h‖ ^ 2 * SchwartzMap.seminorm ℂ k (n + 2) f := by
  set a : κ ⊕ κ' → V := padL (κ' := κ') h with ha
  set f1 := pd a f with hf1
  set f2 := pd a f1 with hf2
  set M := ‖h‖ ^ 2 * SchwartzMap.seminorm ℂ k (n + 2) f with hM
  refine SchwartzMap.seminorm_le_bound ℂ k n _ (by positivity) fun y => ?_
  have hnn : ((n : ℕ) : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  have c0 : ContDiff ℝ ∞ f := f.smooth'
  have c1 : ContDiff ℝ ∞ f1 := f1.smooth'
  have e1 : (fun z => fderiv ℝ f z a) = ⇑f1 := by funext z; exact (pd_apply a f z).symm
  have e2 : (fun z => fderiv ℝ f1 z a) = ⇑f2 := by funext z; exact (pd_apply a f1 z).symm
  set G : (κ ⊕ κ' → V) → ℂ := fun w => f (w + a) - f w - f1 w with hG
  have cG : ContDiff ℝ ∞ G :=
    ((c0.comp (contDiff_id.add contDiff_const)).sub c0).sub c1
  set c : κ ⊕ κ' → V := Sum.elim x 0 with hc
  have efun : ⇑(sliceR f (x + h) - sliceR f x - sliceR f1 x)
      = (fun u => G (u + c)) ∘ ⇑(inrL (V := V) κ κ') := by
    funext y'
    have hy : (Sum.elim x y' : κ ⊕ κ' → V) = inrL κ κ' y' + c := by
      rw [add_comm]; exact congrFun (elim_eq_add x) y'
    simp only [SchwartzMap.sub_apply, sliceR_apply, Function.comp_apply, hG, ← hy,
      elim_add_padL, ha]
  have cGc : ContDiff ℝ ∞ (fun u => G (u + c)) := cG.comp (contDiff_id.add contDiff_const)
  have eit : iteratedFDeriv ℝ n ⇑(sliceR f (x + h) - sliceR f x - sliceR f1 x) y
      = (iteratedFDeriv ℝ n f (Sum.elim x y + a) - iteratedFDeriv ℝ n f (Sum.elim x y)
          - iteratedFDeriv ℝ n f1 (Sum.elim x y)).compContinuousLinearMap
          (fun _ => inrL (V := V) κ κ') := by
    have hy : inrL (V := V) κ κ' y + c = Sum.elim x y := by
      rw [add_comm]; exact (congrFun (elim_eq_add x) y).symm
    rw [efun, ContinuousLinearMap.iteratedFDeriv_comp_right _ cGc _ hnn, iteratedFDeriv_comp_add_right, hy]
    congr 1
    have ct : ContDiff ℝ ∞ (fun z => f (z + a)) := c0.comp (contDiff_id.add contDiff_const)
    change iteratedFDeriv ℝ n (((fun z => f (z + a)) - ⇑f) - ⇑f1) _ = _
    rw [iteratedFDeriv_sub_apply (f := (fun z => f (z + a)) - ⇑f) (g := ⇑f1) ((ct.sub c0).of_le hnn).contDiffAt (c1.of_le hnn).contDiffAt,
      iteratedFDeriv_sub_apply (ct.of_le hnn).contDiffAt (c0.of_le hnn).contDiffAt,
      iteratedFDeriv_comp_add_right]
  rw [eit]
  set z : κ ⊕ κ' → V := Sum.elim x y with hz
  have key := GlobalTheory.SchwartzTranslate.taylor_two (fun s : ℝ => ‖y‖ ^ k • iteratedFDeriv ℝ n f (z + s • a))
    (fun s : ℝ => ‖y‖ ^ k • iteratedFDeriv ℝ n f1 (z + s • a))
    (fun s : ℝ => ‖y‖ ^ k • iteratedFDeriv ℝ n f2 (z + s • a))
    (fun s => by
      have := GlobalTheory.SchwartzTranslate.hasDerivAt_iteratedFDeriv_line a n f c0 z s
      rw [e1] at this
      exact this.const_smul (‖y‖ ^ k))
    (fun s => by
      have := GlobalTheory.SchwartzTranslate.hasDerivAt_iteratedFDeriv_line a n f1 c1 z s
      rw [e2] at this
      exact this.const_smul (‖y‖ ^ k))
    M
    (fun s _ => by
      set w := z + s • a
      have hyw : ‖y‖ ≤ ‖w‖ := norm_le_norm_elim_add x h y s
      have b1 := norm_iteratedFDeriv_pd_le a f1 n w
      have b2 := norm_iteratedFDeriv_pd_le a f (n + 1) w
      have hah : ‖a‖ ≤ ‖h‖ := norm_padL_le h
      have hS := SchwartzMap.le_seminorm ℂ k (n + 2) f w
      have hb : ‖iteratedFDeriv ℝ n f2 w‖ ≤ ‖h‖ ^ 2 * ‖iteratedFDeriv ℝ (n + 2) f w‖ := by
        calc ‖iteratedFDeriv ℝ n f2 w‖ ≤ ‖a‖ * ‖iteratedFDeriv ℝ (n + 1) f1 w‖ := b1
          _ ≤ ‖a‖ * (‖a‖ * ‖iteratedFDeriv ℝ (n + 1 + 1) f w‖) := by gcongr
          _ ≤ ‖h‖ * (‖h‖ * ‖iteratedFDeriv ℝ (n + 2) f w‖) := by gcongr
          _ = _ := by ring
      rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      calc ‖y‖ ^ k * ‖iteratedFDeriv ℝ n f2 w‖
          ≤ ‖w‖ ^ k * (‖h‖ ^ 2 * ‖iteratedFDeriv ℝ (n + 2) f w‖) := by gcongr
        _ = ‖h‖ ^ 2 * (‖w‖ ^ k * ‖iteratedFDeriv ℝ (n + 2) f w‖) := by ring
        _ ≤ M := by rw [hM]; gcongr) 1 (by simp)
  simp only [zero_smul, add_zero, one_smul, one_pow, mul_one] at key
  rw [← smul_sub, ← smul_sub, norm_smul, Real.norm_of_nonneg (by positivity)] at key
  calc ‖y‖ ^ k * ‖(iteratedFDeriv ℝ n f (z + a) - iteratedFDeriv ℝ n f z - iteratedFDeriv ℝ n f1 z).compContinuousLinearMap
          (fun _ => inrL (V := V) κ κ')‖
      ≤ ‖y‖ ^ k * ‖iteratedFDeriv ℝ n f (z + a) - iteratedFDeriv ℝ n f z - iteratedFDeriv ℝ n f1 z‖ := by
        gcongr
        refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
        refine mul_le_of_le_one_right (norm_nonneg _) ?_
        exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => norm_inrL_le κ κ')
    _ ≤ M := key

end GlobalTheory.SliceTaylor
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialOperatorFderivFormula

section

@[expose] public section

open GlobalTheory.SliceSchwartz GlobalTheory.SliceOp
open scoped ContDiff

noncomputable section

namespace GlobalTheory.SliceOpDeriv

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {κ κ' κ₁' : Type} [Fintype κ] [Fintype κ'] [Fintype κ₁']

theorem pd_padL_add (f : SchwartzMap (κ ⊕ κ' → V) ℂ) (h h' : κ → V) :
    pd (padL (κ' := κ') (h + h')) f = pd (padL h) f + pd (padL h') f := by
  have e : (padL (κ' := κ') (h + h') : κ ⊕ κ' → V) = padL h + padL h' := by
    funext i; cases i <;> simp [padL]
  ext z
  rw [SchwartzMap.add_apply, pd_apply, pd_apply, pd_apply, e, map_add (f := _)]

theorem pd_padL_smul (f : SchwartzMap (κ ⊕ κ' → V) ℂ) (c : ℝ) (h : κ → V) :
    pd (padL (κ' := κ') (c • h)) f = (c : ℂ) • pd (padL h) f := by
  have e : (padL (κ' := κ') (c • h) : κ ⊕ κ' → V) = c • padL h := by
    funext i; cases i <;> simp [padL]
  ext z
  rw [SchwartzMap.smul_apply, pd_apply, pd_apply, e, map_smul, Complex.real_smul, smul_eq_mul]

def xPartL (P : SchwartzMap (κ' → V) ℂ →L[ℂ] SchwartzMap (κ₁' → V) ℂ) (f : SchwartzMap (κ ⊕ κ' → V) ℂ)
    (x : κ → V) (y : κ₁' → V) : (κ → V) →ₗ[ℝ] ℂ where
  toFun h := P (sliceR (pd (padL (κ' := κ') h) f) x) y
  map_add' h h' := by
    simp only [pd_padL_add, ← sliceRL_apply, map_add (f := _), SchwartzMap.add_apply]
  map_smul' c h := by
    simp only [pd_padL_smul, ← sliceRL_apply, map_smul, SchwartzMap.smul_apply, RingHom.id_apply,
      Complex.real_smul, smul_eq_mul]

variable [FiniteDimensional ℝ V]

def xPart (P : SchwartzMap (κ' → V) ℂ →L[ℂ] SchwartzMap (κ₁' → V) ℂ) (f : SchwartzMap (κ ⊕ κ' → V) ℂ)
    (x : κ → V) (y : κ₁' → V) : (κ → V) →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap (xPartL P f x y)

theorem xPart_apply (P : SchwartzMap (κ' → V) ℂ →L[ℂ] SchwartzMap (κ₁' → V) ℂ) (f : SchwartzMap (κ ⊕ κ' → V) ℂ)
    (x : κ → V) (y : κ₁' → V) (h : κ → V) :
    xPart P f x y h = P (sliceR (pd (padL (κ' := κ') h) f) x) y := rfl

end GlobalTheory.SliceOpDeriv

namespace GlobalTheory.SliceOpDeriv
open GlobalTheory.SliceSchwartz GlobalTheory.SliceOp

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {κ κ' κ₁' : Type} [Fintype κ] [Fintype κ'] [Fintype κ₁']

theorem hasFDerivAt_sliceR_apply (P : SchwartzMap (κ' → V) ℂ →L[ℂ] SchwartzMap (κ₁' → V) ℂ) (f : SchwartzMap (κ ⊕ κ' → V) ℂ)
    (x : κ → V) (y : κ₁' → V) :
    HasFDerivAt (fun x' => P (sliceR f x') y) (xPart P f x y) x := by
  obtain ⟨s', C, hC, hP⟩ := clm_sup_bound P {((0 : ℕ), (0 : ℕ))}
  set M : ℝ := s'.sup (fun m : ℕ × ℕ => SchwartzMap.seminorm ℂ m.1 (m.2 + 2)) f
  have hM : 0 ≤ M := by positivity
  have hb : ∀ h : κ → V, ‖P (sliceR f (x + h)) y - P (sliceR f x) y - xPart P f x y h‖ ≤ C * M * ‖h‖ ^ 2 := by
    intro h
    set D := sliceR f (x + h) - sliceR f x - sliceR (pd (padL (κ' := κ') h) f) x
    have e : P (sliceR f (x + h)) y - P (sliceR f x) y - xPart P f x y h = P D y := by
      simp only [D, xPart_apply, map_sub, SchwartzMap.sub_apply]
    rw [e]
    have h1 : ‖P D y‖ ≤ ({((0 : ℕ), (0 : ℕ))} : Finset (ℕ × ℕ)).sup (schwartzSeminormFamily ℂ (κ₁' → V) ℂ) (P D) := by
      simpa [schwartzSeminormFamily] using SchwartzMap.norm_le_seminorm ℂ (P D) y
    have h2 : s'.sup (schwartzSeminormFamily ℂ (κ' → V) ℂ) D ≤ ‖h‖ ^ 2 * M := by
      refine Seminorm.finset_sup_apply_le (by positivity) fun i hi => ?_
      refine (GlobalTheory.SliceTaylor.seminorm_slice_taylor_le V κ κ' f i.1 i.2 x h).trans ?_
      gcongr
      exact Seminorm.le_finset_sup_apply (p := fun m : ℕ × ℕ => (SchwartzMap.seminorm ℂ m.1 (m.2 + 2) : Seminorm ℂ (SchwartzMap (κ ⊕ κ' → V) ℂ))) (x := f) hi
    calc ‖P D y‖ ≤ C * s'.sup (schwartzSeminormFamily ℂ (κ' → V) ℂ) D := h1.trans (hP D)
      _ ≤ C * (‖h‖ ^ 2 * M) := mul_le_mul_of_nonneg_left h2 hC
      _ = C * M * ‖h‖ ^ 2 := by ring
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  refine Asymptotics.IsBigO.trans_isLittleO ?_ (Asymptotics.isLittleO_norm_pow_id one_lt_two)
  refine Asymptotics.IsBigO.of_bound (C * M) (Filter.Eventually.of_forall fun h => ?_)
  refine (hb h).trans (le_of_eq ?_)
  rw [Real.norm_of_nonneg (by positivity)]

end GlobalTheory.SliceOpDeriv

namespace GlobalTheory.SliceOpDeriv
open GlobalTheory.SliceSchwartz GlobalTheory.SliceOp

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {κ κ' κ₁' : Type} [Fintype κ] [Fintype κ'] [Fintype κ₁']

theorem continuous_elim_pair :
    Continuous (fun p : (κ → V) × (κ₁' → V) => (Sum.elim p.1 p.2 : κ ⊕ κ₁' → V)) := by
  refine continuous_pi fun i => ?_
  cases i with
  | inl i => simp only [Sum.elim_inl]; fun_prop
  | inr j => simp only [Sum.elim_inr]; fun_prop

theorem qOp_elim (P : SchwartzMap (κ' → V) ℂ →L[ℂ] SchwartzMap (κ₁' → V) ℂ) (f : SchwartzMap (κ ⊕ κ' → V) ℂ)
    (x : κ → V) (y : κ₁' → V) : qOp P f (Sum.elim x y) = P (sliceR f x) y := by
  simp [qOp]

theorem continuous_xPart (P : SchwartzMap (κ' → V) ℂ →L[ℂ] SchwartzMap (κ₁' → V) ℂ)
    (f : SchwartzMap (κ ⊕ κ' → V) ℂ) :
    Continuous (fun p : (κ → V) × (κ₁' → V) => xPart P f p.1 p.2) := by
  refine continuous_clm_apply.2 fun h => ?_
  have e : (fun p : (κ → V) × (κ₁' → V) => xPart P f p.1 p.2 h) =
      fun p => qOp P (pd (padL (κ' := κ') h) f) (Sum.elim p.1 p.2) := by
    funext p; rw [qOp_elim, xPart_apply]
  rw [e]
  exact (continuous_qOp V κ κ' κ₁' P _).comp continuous_elim_pair

theorem continuous_yPart (P : SchwartzMap (κ' → V) ℂ →L[ℂ] SchwartzMap (κ₁' → V) ℂ)
    (f : SchwartzMap (κ ⊕ κ' → V) ℂ) :
    Continuous (fun p : (κ → V) × (κ₁' → V) => fderiv ℝ (P (sliceR f p.1)) p.2) := by
  refine continuous_clm_apply.2 fun w => ?_
  have e : (fun p : (κ → V) × (κ₁' → V) => fderiv ℝ (P (sliceR f p.1)) p.2 w) =
      fun p => qOp ((pd w).comp P) f (Sum.elim p.1 p.2) := by
    funext p; rw [qOp_elim, ContinuousLinearMap.comp_apply, pd_apply]
  rw [e]
  exact (continuous_qOp V κ κ' κ₁' _ _).comp continuous_elim_pair

def splitL : (κ ⊕ κ₁' → V) →L[ℝ] (κ → V) × (κ₁' → V) :=
  (ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : κ ⊕ κ₁' => V) (Sum.inl i)).prod
    (ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : κ ⊕ κ₁' => V) (Sum.inr j))

theorem hasFDerivAt_qOp (P : SchwartzMap (κ' → V) ℂ →L[ℂ] SchwartzMap (κ₁' → V) ℂ)
    (f : SchwartzMap (κ ⊕ κ' → V) ℂ) (s : κ ⊕ κ₁' → V) :
    HasFDerivAt (qOp P f)
      (((xPart P f (s ∘ Sum.inl) (s ∘ Sum.inr)).coprod
        (fderiv ℝ (P (sliceR f (s ∘ Sum.inl))) (s ∘ Sum.inr))).comp splitL) s := by
  let F : (κ → V) → (κ₁' → V) → ℂ := fun x y => P (sliceR f x) y
  have key := hasStrictFDerivAt_uncurry_coprod (𝕜 := ℝ) (u := splitL s) (f := F)
    (f₁ := fun x y => xPart P f x y) (f₂ := fun x y => fderiv ℝ (P (sliceR f x)) y)
    (Filter.Eventually.of_forall fun v => hasFDerivAt_sliceR_apply P f v.1 v.2)
    (Filter.Eventually.of_forall fun v => ((P (sliceR f v.1)).differentiableAt).hasFDerivAt)
    (continuous_xPart P f).continuousAt (continuous_yPart P f).continuousAt
  have h2 := key.hasFDerivAt.comp s ((splitL (V := V) (κ := κ) (κ₁' := κ₁')).hasFDerivAt (x := s))
  exact h2

end GlobalTheory.SliceOpDeriv

open GlobalTheory.SliceSchwartz GlobalTheory.SliceOp in
theorem GlobalTheory.SliceOp.differentiable_qOp_and_fderiv : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (κ κ' κ₁' : Type) [Fintype κ] [Fintype κ'] [Fintype κ₁']
    (P : SchwartzMap (κ' → V) ℂ →L[ℂ] SchwartzMap (κ₁' → V) ℂ) (f : SchwartzMap (κ ⊕ κ' → V) ℂ),
    Differentiable ℝ (qOp P f) ∧ ∀ (s v : κ ⊕ κ₁' → V),
      fderiv ℝ (qOp P f) s v = qOp P (pd (padL (κ' := κ') (v ∘ Sum.inl)) f) s + qOp ((pd (v ∘ Sum.inr)).comp P) f s := by
  intro V _ _ _ κ κ' κ₁' _ _ _ P f
  refine ⟨fun s => (GlobalTheory.SliceOpDeriv.hasFDerivAt_qOp P f s).differentiableAt, fun s v => ?_⟩
  rw [(GlobalTheory.SliceOpDeriv.hasFDerivAt_qOp P f s).fderiv]
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coprod_apply]
  rfl
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialOperatorFderivFormulaStatement

section

@[expose] public section

open GlobalTheory.SliceSchwartz GlobalTheory.SliceOp
open scoped ContDiff

theorem _root_.GlobalTheory.T.partial_operator_fderiv_formula : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (κ κ' κ₁' : Type) [Fintype κ] [Fintype κ'] [Fintype κ₁']
    (P : SchwartzMap (κ' → V) ℂ →L[ℂ] SchwartzMap (κ₁' → V) ℂ) (f : SchwartzMap (κ ⊕ κ' → V) ℂ),
    Differentiable ℝ (qOp P f) ∧ ∀ (s v : κ ⊕ κ₁' → V),
      fderiv ℝ (qOp P f) s v = qOp P (pd (padL (κ' := κ') (v ∘ Sum.inl)) f) s + qOp ((pd (v ∘ Sum.inr)).comp P) f s := by
  first | exact @GlobalTheory.SliceOp.differentiable_qOp_and_fderiv | exact GlobalTheory.SliceOp.differentiable_qOp_and_fderiv | (intros; apply GlobalTheory.SliceOp.differentiable_qOp_and_fderiv <;> assumption)
end
end
