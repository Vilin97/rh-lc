module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.InductiveHeisenbergInputs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Matrix.MeasurableSpace
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.HermitianFormLiftVecFirstVector
public import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.TailInt
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.RingTheory.Norm.Transitivity
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.HermExpand
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.LevelDeterminantOfTriangularChange
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.InvSqrtTwoMulSelf

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.MpUnitary

section

@[expose] public section

noncomputable section
open Matrix MeasureTheory
open scoped ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

namespace BL

section cont
variable {p m : ℕ}

theorem cont_ite {β : Type} [TopologicalSpace β] [Zero β] (c : Prop) [Decidable c] {f : Xp p m → β}
    (hf : Continuous f) : Continuous (fun x => if c then f x else 0) := by
  by_cases h : c
  · simp only [h, if_true]; exact hf
  · simp only [h, if_false]; exact continuous_const

theorem cont_Lsq (l : Fin (p + 1)) : Continuous (fun x : Xp p m => Lsq x l) := by
  unfold Lsq
  exact continuous_const.fun_add (continuous_finsetSum _ fun j _ =>
    cont_ite _ (((continuous_apply j).comp continuous_fst).norm.pow 2))

theorem cont_rhoSq (l : Fin (p + 1)) : Continuous (fun x : Xp p m => rhoSq x l) := by
  unfold rhoSq
  refine ((cont_Lsq _).add (continuous_finsetSum _ fun i _ => ?_)).add (continuous_finsetSum _ fun j _ => ?_)
  · exact ((continuous_apply i).comp (continuous_fst.comp (continuous_snd.comp continuous_snd))).norm.pow 2
  · exact cont_ite _ (((continuous_apply j).comp (continuous_fst.comp continuous_snd)).norm.pow 2)

theorem cont_bco (l : Fin (p + 1)) : Continuous (fun x : Xp p m => bco x l) := by
  unfold bco
  refine ((Complex.continuous_ofReal.comp ((continuous_finsetSum _ fun i _ => ?_).fun_neg.div_const 2)).add
    ((Complex.continuous_ofReal.comp (continuous_snd.comp (continuous_snd.comp continuous_snd))).mul
      continuous_const)).sub (continuous_finsetSum _ fun j _ => ?_)
  · exact ((continuous_apply i).comp (continuous_fst.comp (continuous_snd.comp continuous_snd))).norm.pow 2
  · exact cont_ite _ (((continuous_apply j).comp (continuous_fst.comp continuous_snd)).mul
      ((continuous_apply j).comp continuous_fst).star)

theorem cont_de (l : Fin (p + 1)) : Continuous (fun x : Xp p m => de x l) := by
  unfold de
  exact Real.continuous_sqrt.comp (((cont_Lsq l).mul (cont_rhoSq l)).add ((cont_bco l).norm.pow 2))

theorem cont_linF (η η' : Fin p → ℂ) (ζ : Fin m → ℂ) : Continuous (fun x : Xp p m => linF η η' ζ x) := by
  unfold linF
  refine (continuous_finsetSum _ fun j _ => ?_).add (continuous_finsetSum _ fun i _ => ?_)
  · exact (((continuous_apply j).comp continuous_fst).mul continuous_const).add
      (((continuous_apply j).comp (continuous_fst.comp continuous_snd)).mul continuous_const)
  · exact ((continuous_apply i).comp (continuous_fst.comp (continuous_snd.comp continuous_snd))).mul continuous_const

def GI (s : Fin (p + 1) → ℝ) (δ : ℝ) (η η' : Fin p → ℂ) (ζ : Fin m → ℂ) (c₀ : ℝ) (x : Xp p m) : ℝ≥0∞ :=
  (∏ l, ENNReal.ofReal (de x l ^ (-s l))) * ENNReal.ofReal ((1 + |2 * (linF η η' ζ x).im + c₀|) ^ (-δ))

theorem meas_GI (s : Fin (p + 1) → ℝ) (δ : ℝ) (η η' : Fin p → ℂ) (ζ : Fin m → ℂ) (c₀ : ℝ) :
    Measurable (GI s δ η η' ζ c₀) := by
  unfold GI
  refine (Finset.measurable_prod _ fun l _ => ?_).mul ?_
  · exact ENNReal.measurable_ofReal.comp ((cont_de l).measurable.pow_const _)
  · exact ENNReal.measurable_ofReal.comp ((continuous_const.add ((continuous_const.mul
      (Complex.continuous_im.comp (cont_linF η η' ζ))).add continuous_const).abs).measurable.pow_const _)

end cont

theorem mp_unitary {N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ) (hU : Uᴴ * U = 1) :
    MeasurePreserving (fun y : Fin N → ℂ => U *ᵥ y) volume volume := by
  set f : (Fin N → ℂ) →ₗ[ℝ] (Fin N → ℂ) := (Matrix.toLin' U).restrictScalars ℝ with hf
  have hfU : (fun y : Fin N → ℂ => U *ᵥ y) = ⇑f := by funext y; simp [hf, Matrix.toLin'_apply]
  have hn : ((Complex.normSq U.det : ℝ) : ℂ) = 1 := by
    have h := congrArg Matrix.det hU
    rw [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] at h
    rw [Complex.normSq_eq_conj_mul_self]; exact h
  have hdet : LinearMap.det f = 1 := by
    rw [hf, LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply]; exact_mod_cast hn
  rw [hfU]
  refine ⟨f.continuous_of_finiteDimensional.measurable, ?_⟩
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume (by rw [hdet]; norm_num), hdet]
  simp

theorem mp_hpar {k n : ℕ} (U : Mat k n) (hU : Uᴴ * U = 1) :
    MeasurePreserving (fun X : HPar k n => (U *ᵥ X.1, X.2)) volume volume :=
  (mp_unitary U hU).prod (MeasurePreserving.id volume)

theorem os_q (hOS : OS) (q p m : ℕ) (hq : q = p + 1) (δ γ : ℝ) (e : Fin (q + 1) → ℝ) (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (hγ : 0 < γ) (hγ8 : γ ≤ δ / 8) (he : ∀ l, 0 < e l) (hsum : e 0 + 2 * ∑ i : Fin q, e i.succ < γ / 2) :
    ∃ C : ℝ, ∀ (η η' : Fin q → ℂ) (ζ : Fin m → ℂ) (c₀ : ℝ), η' ⟨0, by omega⟩ ≠ 0 →
      ∫⁻ x, GI (fun l => s0N q m l - e l) δ η η' ζ c₀ x ≤
        ENNReal.ofReal (C * ‖η' ⟨0, by omega⟩‖ ^ (-γ) * (1 + |c₀|) ^ (-δ / 4)) := by
  subst hq
  obtain ⟨C, hC⟩ := hOS p m δ γ e hδ hδ2 hγ hγ8 he hsum
  refine ⟨C, fun η η' ζ c₀ h0 => ?_⟩
  have e0 : (⟨0, by omega⟩ : Fin (p + 1)) = 0 := Fin.ext (by simp)
  rw [e0] at h0 ⊢
  exact hC η η' ζ c₀ h0

end BL

end ReciprocityTheory.ChartRestriction.DS.Xi
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.InnerBound

section

@[expose] public section

noncomputable section
open Matrix MeasureTheory
open scoped ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

namespace BL

theorem cz0 {k : ℕ} (hk : 1 ≤ k) (z : Fin (2 * 0 + k + 1) → ℂ) (hT : 0 < Tz k 0 z) :
    herm (Hpk k 0) (epsV k 0) z ≠ 0 := by
  intro h
  have sgl : ∀ p : Fin (2 * 0 + k + 1), sg k 0 p.val = p.val := fun p => by
    have := p.2; unfold sg; rw [if_neg (by omega)]
  have hmv : ∀ (v : Fin (2 * 0 + k + 1) → ℂ) (p : Fin (2 * 0 + k + 1)),
      (Hpk k 0 *ᵥ v) p = (if p.val = 0 + k then -1 else 1) * v p := by
    intro v p; simp only [mulVec, dotProduct]
    rw [Finset.sum_eq_single p]
    · rw [hpk_apply, sgl, if_pos rfl]
    · intro q _ hq; rw [hpk_apply, sgl, if_neg (fun e => hq (Fin.ext e)), zero_mul]
    · intro hp; exact absurd (Finset.mem_univ _) hp
  have hw0 : (wI k 0 0).val = 0 := by simp [wI]
  have hwk : (wI k 0 (Fin.last k)).val = k := by simp [wI]
  have e1 : Hpk k 0 *ᵥ bvec (wI k 0 0) = bvec (wI k 0 0) := by
    funext p; rw [hmv]; split_ifs with hp
    · rw [bvec_ne _ _ (by omega), mul_zero]
    · rw [one_mul]
  have e2 : Hpk k 0 *ᵥ bvec (wI k 0 (Fin.last k)) = -bvec (wI k 0 (Fin.last k)) := by
    funext p; rw [hmv, Pi.neg_apply]; split_ifs with hp
    · rw [neg_one_mul]
    · rw [bvec_ne _ _ (by omega), mul_zero, neg_zero]
  have hh : herm (Hpk k 0) (epsV k 0) z =
      ((Real.sqrt 2)⁻¹ : ℂ) * (star (z (wI k 0 0)) - star (z (wI k 0 (Fin.last k)))) := by
    unfold epsV herm
    rw [mulVec_smul, mulVec_add, e1, e2, dotProduct_smul, dotProduct_add, dotProduct_neg, dot_bvec_r, dot_bvec_r,
      Pi.star_apply, Pi.star_apply, smul_eq_mul, sub_eq_add_neg]
  have hc : ((Real.sqrt 2)⁻¹ : ℂ) ≠ 0 := by
    have : ((Real.sqrt 2)⁻¹ : ℂ) * ((Real.sqrt 2)⁻¹ : ℂ) ≠ 0 := by rw [sq2_mul_sq2_eq_half]; norm_num
    exact left_ne_zero_of_mul this
  rw [hh] at h
  have hzz : z (wI k 0 0) = z (wI k 0 (Fin.last k)) :=
    star_injective (sub_eq_zero.1 ((mul_eq_zero.1 h).resolve_left hc))
  have hre : (herm (Hpk k 0) z z).re = ∑ p, (if p.val = 0 + k then (-1 : ℝ) else 1) * Complex.normSq (z p) := by
    unfold herm
    simp only [dotProduct, hmv, Complex.re_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Pi.star_apply]
    split_ifs <;> simp [Complex.mul_re, Complex.normSq_apply]
  have hne : wI k 0 0 ≠ wI k 0 (Fin.last k) := fun e => by have := congrArg Fin.val e; omega
  have key : 0 ≤ ∑ p, (if p.val = 0 + k then (-1 : ℝ) else 1) * Complex.normSq (z p) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (wI k 0 (Fin.last k))),
      ← Finset.add_sum_erase _ _ (Finset.mem_erase.2 ⟨hne, Finset.mem_univ (wI k 0 0)⟩)]
    rw [if_pos (show (wI k 0 (Fin.last k)).val = 0 + k by omega), if_neg (show ¬ (wI k 0 0).val = 0 + k by omega),
      hzz]
    have hrest : 0 ≤ ∑ p ∈ (Finset.univ.erase (wI k 0 (Fin.last k))).erase (wI k 0 0),
        (if p.val = 0 + k then (-1 : ℝ) else 1) * Complex.normSq (z p) := by
      refine Finset.sum_nonneg fun p hp => ?_
      have hpk : p ≠ wI k 0 (Fin.last k) := (Finset.mem_erase.1 (Finset.mem_erase.1 hp).2).1
      rw [if_neg (show ¬ (p.val = 0 + k) from fun e => hpk (Fin.ext (by omega)))]
      exact mul_nonneg zero_le_one (Complex.normSq_nonneg _)
    linarith
  unfold Tz at hT
  rw [hre] at hT
  linarith

theorem cz_ne {k n : ℕ} (hk : 1 ≤ k) (z1 : Fin (2 * n + k + 1) → ℂ) (hT : 0 < Tz k n z1) :
    herm (Hpk k n) (phiV k n ⟨0, by omega⟩) (fvec k n z1 ⟨0, by omega⟩) ≠ 0 := by
  by_cases hn : 0 < n
  · unfold phiV fvec
    rw [dite_eq_left hn, dite_eq_left hn, herm_bb, hpk_apply]
    rw [if_pos (show (esI k n ⟨0, hn⟩).val = sg k n (eI k n ⟨0, hn⟩).val by
        show 2 * n + k - 0 = sg k n 0; unfold sg; rw [if_pos (Or.inl hn)]),
      if_neg (show ¬ (eI k n ⟨0, hn⟩).val = n + k by show ¬ 0 = n + k; omega)]
    norm_num
  · have hn0 : n = 0 := by omega
    subst hn0
    unfold phiV fvec
    rw [dite_eq_right (lt_irrefl 0), dite_eq_right (lt_irrefl 0)]
    exact cz0 hk z1 hT

def etaF (k n : ℕ) (w : Fin (2 * n + k + 1) → ℂ) : Fin (1 + n) → ℂ :=
  fun j => herm (Hpk k n) (phiV' k n (Fin.cast (by omega) j)) w

def eta'F (k n : ℕ) (w : Fin (2 * n + k + 1) → ℂ) : Fin (1 + n) → ℂ :=
  fun j => herm (Hpk k n) (phiV k n (Fin.cast (by omega) j)) w

def zetaF (k n : ℕ) (w : Fin (2 * n + k + 1) → ℂ) : Fin (k - 1) → ℂ := fun i => herm (Hpk k n) (wv k n i) w

theorem herm_linF' {k n : ℕ} (hk : 1 ≤ k) (y w : Fin (2 * n + k + 1) → ℂ) (s : ℝ) :
    herm (Hpk k n) y w = linF (etaF k n w) (eta'F k n w) (zetaF k n w) (hcoord k n (y, s)) :=
  herm_linF k n hk y w s

section inner
variable {k r' : ℕ}

theorem inner_bound (hIW : IW) (hF : FormulaF) (hHC : HeisConjLev) (hHA : HeisAct) (hk : 1 ≤ k)
    (s : Fin (1 + r' + 1) → ℝ) (δ γ C : ℝ) (z1 : Fin (2 * r' + k + 1) → ℂ)
    (hC : ∀ (η η' : Fin (1 + r') → ℂ) (ζ : Fin (k - 1) → ℂ) (c₀ : ℝ), η' ⟨0, by omega⟩ ≠ 0 →
      ∫⁻ x, GI s δ η η' ζ c₀ x ≤ ENNReal.ofReal (C * ‖η' ⟨0, by omega⟩‖ ^ (-γ) * (1 + |c₀|) ^ (-δ / 4)))
    (hcz : herm (Hpk k r') (phiV k r' ⟨0, by omega⟩) (fvec k r' z1 ⟨0, by omega⟩) ≠ 0)
    (m : Mat k r') (hm : m ∈ UH (Hpk k r')) :
    ∫⁻ X : HPar k r', ENNReal.ofReal (xiR k (1 + r') s (heis0 k r' X * ιLev k 1 r' m)) *
        ENNReal.ofReal ((1 + |lam k (1 + r') (liftVec k 1 r' z1) (heis0 k r' X * ιLev k 1 r' m)|) ^ (-δ)) ≤
      ENNReal.ofReal (C * ‖herm (Hpk k r') (phiV k r' ⟨0, by omega⟩) (fvec k r' z1 ⟨0, by omega⟩)‖ ^ (-γ)) *
        (ENNReal.ofReal (xiR k r' (fun a => s (su a) - if a = 0 then γ else 0) m) *
          ENNReal.ofReal ((1 + |lam k r' z1 m|) ^ (-(δ / 4)))) := by
  obtain ⟨κ, hκG, hκU, t, ht, htn, hD⟩ := lev_data hIW hHC hk m hm
  have hκU' : κ * κᴴ = 1 := mul_eq_one_comm.1 hκU
  have h00 : (0 : Fin (r' + 1)) = ⟨0, by omega⟩ := Fin.ext (by simp)
  have ht' : m *ᵥ phiV k r' ⟨0, by omega⟩ = t • (κ *ᵥ phiV k r' ⟨0, by omega⟩) := by rw [← h00]; exact ht
  obtain ⟨w, hw⟩ : ∃ w, w = κᴴ *ᵥ (m *ᵥ fvec k r' z1 ⟨0, by omega⟩) := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A, A = ∏ a : Fin (r' + 1), Del k r' a m ^ (-s (su a)) := ⟨_, rfl⟩
  have hDel : ∀ (n : ℕ) (l : Fin (n + 1)) (x : Mat k n), 0 ≤ Del k n l x := fun n l x => Real.sqrt_nonneg _
  have hA0 : 0 ≤ A := by rw [hA]; exact Finset.prod_nonneg fun a _ => Real.rpow_nonneg (hDel _ _ _) _
  have hpt : ∀ X : HPar k r',
      ENNReal.ofReal (xiR k (1 + r') s (heis0 k r' X * ιLev k 1 r' m)) *
        ENNReal.ofReal ((1 + |lam k (1 + r') (liftVec k 1 r' z1) (heis0 k r' X * ιLev k 1 r' m)|) ^ (-δ)) =
      ENNReal.ofReal A * GI s δ (etaF k r' w) (eta'F k r' w) (zetaF k r' w) (lam k r' z1 m)
        (hcoord k r' (κᴴ *ᵥ X.1, X.2)) := by
    intro X
    obtain ⟨hD0, hDS⟩ := hD X
    have hde : ∀ (x : Xp (1 + r') (k - 1)) (l : Fin (1 + r' + 1)), 0 ≤ de x l := fun x l => Real.sqrt_nonneg _
    have hmr : ∀ a : Fin (r' + 1), (Del k r' a m * de (hcoord k r' (κᴴ *ᵥ X.1, X.2)) (su a)) ^ (-s (su a)) =
        Del k r' a m ^ (-s (su a)) * de (hcoord k r' (κᴴ *ᵥ X.1, X.2)) (su a) ^ (-s (su a)) :=
      fun a => Real.mul_rpow (hDel _ _ _) (hde _ _)
    have hxi : xiR k (1 + r') s (heis0 k r' X * ιLev k 1 r' m) =
        A * ∏ l, de (hcoord k r' (κᴴ *ᵥ X.1, X.2)) l ^ (-s l) := by
      unfold xiR
      rw [prod_su, prod_su (fun l => de (hcoord k r' (κᴴ *ᵥ X.1, X.2)) l ^ (-s l)), hD0]
      simp only [hDS, (hF k r' hk).1, hmr, Finset.prod_mul_distrib]
      rw [hA]; ring
    have hX : X.1 = κ *ᵥ (κᴴ *ᵥ X.1) := by rw [mulVec_mulVec, hκU', one_mulVec]
    have hmf : m *ᵥ fvec k r' z1 ⟨0, by omega⟩ = κ *ᵥ w := by rw [hw, mulVec_mulVec, hκU', one_mulVec]
    have hh : herm (Hpk k r') (κ *ᵥ w) X.1 = star (herm (Hpk k r') (κᴴ *ᵥ X.1) w) := by
      conv_lhs => rw [hX]
      rw [herm_UH _ _ hκG]
      exact (herm_conj _ (hpk_conjT k r') _ _).symm
    have hlam : lam k (1 + r') (liftVec k 1 r' z1) (heis0 k r' X * ιLev k 1 r' m) =
        2 * (linF (etaF k r' w) (eta'F k r' w) (zetaF k r' w) (hcoord k r' (κᴴ *ᵥ X.1, X.2))).im + lam k r' z1 m := by
      rw [lam_lev hHA, hmf, hh, herm_linF' hk _ w X.2, Complex.star_def, Complex.conj_im]
      ring
    rw [hxi, hlam, ENNReal.ofReal_mul hA0, ENNReal.ofReal_prod_of_nonneg (fun l _ => Real.rpow_nonneg (hde _ l) _)]
    unfold GI; rw [mul_assoc]
  have key : t * eta'F k r' w ⟨0, by omega⟩ = herm (Hpk k r') (phiV k r' ⟨0, by omega⟩) (fvec k r' z1 ⟨0, by omega⟩) := by
    show t * herm (Hpk k r') (phiV k r' ⟨0, by omega⟩) w = _
    rw [hw, ← herm_UH _ _ hκG (phiV k r' ⟨0, by omega⟩) (κᴴ *ᵥ (m *ᵥ fvec k r' z1 ⟨0, by omega⟩)),
      mulVec_mulVec (m *ᵥ fvec k r' z1 ⟨0, by omega⟩) κ κᴴ, hκU', one_mulVec, ← herm_smul_l, ← ht', herm_UH _ _ hm]
  have ht0 : t ≠ 0 := fun h => hcz (by rw [← key, h, zero_mul])
  have hη0 : eta'F k r' w ⟨0, by omega⟩ ≠ 0 := fun h => hcz (by rw [← key, h, mul_zero])
  have hκH : (κᴴ)ᴴ * κᴴ = 1 := by rw [conjTranspose_conjTranspose]; exact hκU'
  have hg : Measurable (fun x => GI s δ (etaF k r' w) (eta'F k r' w) (zetaF k r' w) (lam k r' z1 m) (hcoord k r' x)) :=
    (meas_GI _ _ _ _ _ _).comp (hF k r' hk).2.measurable
  have hD0pos : 0 < Del k r' 0 m := by rw [← htn]; exact norm_pos_iff.2 ht0
  have hcz0 : 0 < ‖herm (Hpk k r') (phiV k r' ⟨0, by omega⟩) (fvec k r' z1 ⟨0, by omega⟩)‖ := norm_pos_iff.2 hcz
  have hnorm : ‖eta'F k r' w ⟨0, by omega⟩‖ =
      ‖herm (Hpk k r') (phiV k r' ⟨0, by omega⟩) (fvec k r' z1 ⟨0, by omega⟩)‖ / Del k r' 0 m := by
    have : eta'F k r' w ⟨0, by omega⟩ = herm (Hpk k r') (phiV k r' ⟨0, by omega⟩) (fvec k r' z1 ⟨0, by omega⟩) / t := by
      rw [eq_div_iff ht0, mul_comm]; exact key
    rw [this, norm_div, htn]
  have hQ : xiR k r' (fun a => s (su a) - if a = 0 then γ else 0) m = A * Del k r' 0 m ^ γ := by
    unfold xiR; rw [hA, Fin.prod_univ_succ, Fin.prod_univ_succ]
    simp only [if_true, Fin.succ_ne_zero, if_false, sub_zero]
    rw [show -(s (su 0) - γ) = -s (su 0) + γ by ring, Real.rpow_add hD0pos]; ring
  have hQ0 : 0 ≤ xiR k r' (fun a => s (su a) - if a = 0 then γ else 0) m :=
    Finset.prod_nonneg fun a _ => Real.rpow_nonneg (hDel _ _ _) _
  have hR0 : 0 ≤ (1 + |lam k r' z1 m|) ^ (-(δ / 4)) := Real.rpow_nonneg (by positivity) _
  calc _ = ∫⁻ X : HPar k r', ENNReal.ofReal A * GI s δ (etaF k r' w) (eta'F k r' w) (zetaF k r' w) (lam k r' z1 m)
          (hcoord k r' (κᴴ *ᵥ X.1, X.2)) := lintegral_congr hpt
    _ = ENNReal.ofReal A * ∫⁻ X : HPar k r', GI s δ (etaF k r' w) (eta'F k r' w) (zetaF k r' w) (lam k r' z1 m)
          (hcoord k r' (κᴴ *ᵥ X.1, X.2)) := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal A * ∫⁻ X : HPar k r', GI s δ (etaF k r' w) (eta'F k r' w) (zetaF k r' w) (lam k r' z1 m)
          (hcoord k r' X) := by rw [(mp_hpar κᴴ hκH).lintegral_comp hg]
    _ = ENNReal.ofReal A * ∫⁻ x, GI s δ (etaF k r' w) (eta'F k r' w) (zetaF k r' w) (lam k r' z1 m) x := by
          rw [(hF k r' hk).2.lintegral_comp (meas_GI _ _ _ _ _ _)]
    _ ≤ ENNReal.ofReal A * ENNReal.ofReal (C * ‖eta'F k r' w ⟨0, by omega⟩‖ ^ (-γ) * (1 + |lam k r' z1 m|) ^ (-δ / 4)) := by
          gcongr; exact hC _ _ _ _ hη0
    _ = ENNReal.ofReal (A * (C * ‖eta'F k r' w ⟨0, by omega⟩‖ ^ (-γ) * (1 + |lam k r' z1 m|) ^ (-δ / 4))) :=
          (ENNReal.ofReal_mul hA0).symm
    _ = ENNReal.ofReal ((C * ‖herm (Hpk k r') (phiV k r' ⟨0, by omega⟩) (fvec k r' z1 ⟨0, by omega⟩)‖ ^ (-γ)) *
          (xiR k r' (fun a => s (su a) - if a = 0 then γ else 0) m * (1 + |lam k r' z1 m|) ^ (-(δ / 4)))) := by
          congr 1
          rw [hnorm, Real.div_rpow hcz0.le hD0pos.le, Real.rpow_neg hD0pos.le, div_inv_eq_mul, hQ, neg_div]; ring
    _ = _ := by rw [ENNReal.ofReal_mul' (mul_nonneg hQ0 hR0), ENNReal.ofReal_mul hQ0]

end inner

end BL

end ReciprocityTheory.ChartRestriction.DS.Xi
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.BStepSuccOf

section

@[expose] public section

noncomputable section
open Matrix MeasureTheory
open scoped ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 BL

theorem bStepBase_of (hB2 : InductiveHeisenbergInputs) : BStepBase := by
  obtain ⟨-, -, -, -, hNB, -⟩ := hB2
  intro k _ δ _
  refine ⟨1, one_pos, fun s _ z _ _ μN hμ => ?_⟩
  set o : Mt k 0 := ((1 : Mat k 0) : Mt k 0) with ho
  have hc : μN ({o}ᶜ : Set (Mt k 0)) = 0 := by
    have h := hμ.conc; rw [hNB k] at h; exact h
  have hr : μN.restrict {o} = μN :=
    Measure.restrict_eq_self_of_ae_mem (ae_iff.2 (by simpa [Set.compl_def] using hc))
  unfold IInt
  rw [← hr, lintegral_singleton]
  exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
    (hμ.finite_compact _ isCompact_singleton)

theorem bStepSucc_of (hB2 : InductiveHeisenbergInputs) (hIW : IW) (hF : FormulaF) (hOS : OS) : BStepSucc := by
  obtain ⟨-, -, -, hNR, -, hHC, -, -, -, -, -, hHH, -, -, -, -, hHU, -, -, -, hCN, -, -, -, hHN, -, hHA⟩ := hB2
  intro k r r' hr hk δ hδ hδ2 hB'
  subst hr
  obtain ⟨e', he', hB'⟩ := hB'
  obtain ⟨γ, hγd⟩ : ∃ γ : ℝ, γ = min (δ / 8) (e' / 2) := ⟨_, rfl⟩
  have hγ : 0 < γ := by rw [hγd]; exact lt_min (by positivity) (by positivity)
  have hγ8 : γ ≤ δ / 8 := by rw [hγd]; exact min_le_left _ _
  have hγe : γ ≤ e' / 2 := by rw [hγd]; exact min_le_right _ _
  have hD : (0 : ℝ) < 4 * (1 + r') + 4 := by positivity
  refine ⟨min (e' / 2) (γ / (4 * (1 + r') + 4)), lt_min (by positivity) (div_pos hγ hD), ?_⟩
  intro s hs z hzW hzT μN hμN
  have he0 : ∀ l, 0 < s0 k (1 + r') l - s l := fun l => (hs l).1
  have heS : ∀ l, s0 k (1 + r') l - s l ≤ γ / (4 * (1 + r') + 4) := fun l => le_trans (hs l).2 (min_le_right _ _)
  have heS' : ∀ l, s0 k (1 + r') l - s l ≤ e' / 2 := fun l => le_trans (hs l).2 (min_le_left _ _)
  have hs0 : ∀ l, s0N (1 + r') (k - 1) l = s0 k (1 + r') l := by
    intro l; unfold s0N s0; split_ifs
    · rfl
    · push_cast [Nat.cast_sub hk]; ring
  have hsum : (s0 k (1 + r') 0 - s 0) + 2 * ∑ i : Fin (1 + r'), (s0 k (1 + r') i.succ - s i.succ) < γ / 2 := by
    have h1 : ∑ i : Fin (1 + r'), (s0 k (1 + r') i.succ - s i.succ) ≤ (1 + r') * (γ / (4 * (1 + r') + 4)) := by
      calc _ ≤ ∑ _i : Fin (1 + r'), γ / (4 * (1 + r') + 4) := Finset.sum_le_sum fun i _ => heS _
        _ = _ := by simp [Finset.sum_const, Finset.card_univ]
    have key : (3 + 2 * (r' : ℝ)) * (γ / (4 * (1 + r') + 4)) < γ / 2 := by
      rw [mul_div_assoc', div_lt_div_iff₀ hD (by norm_num)]; nlinarith
    linarith [heS 0]
  obtain ⟨C, hC⟩ := os_q hOS (1 + r') r' (k - 1) (by omega) δ γ (fun l => s0 k (1 + r') l - s l) hδ hδ2 hγ hγ8 he0 hsum
  have hC' : ∀ (η η' : Fin (1 + r') → ℂ) (ζ : Fin (k - 1) → ℂ) (c₀ : ℝ), η' ⟨0, by omega⟩ ≠ 0 →
      ∫⁻ x, GI s δ η η' ζ c₀ x ≤ ENNReal.ofReal (C * ‖η' ⟨0, by omega⟩‖ ^ (-γ) * (1 + |c₀|) ^ (-δ / 4)) := by
    intro η η' ζ c₀ h
    have hse : s = fun l => s0N (1 + r') (k - 1) l - (s0 k (1 + r') l - s l) := by funext l; rw [hs0]; ring
    rw [hse]; exact hC η η' ζ c₀ h
  obtain ⟨z1, hz1W, rfl⟩ : ∃ z1, inWb k r' z1 ∧ z = liftVec k 1 r' z1 := ⟨_, shifted_mem_weightSpace z hzW, z_lift z hzW⟩
  have hz1T : 0 < Tz k r' z1 := by rw [← tz_lift]; exact hzT
  have hcz := cz_ne hk z1 hz1T
  have hsP : ∀ a : Fin (r' + 1), 0 < s0 k r' a - (s (su a) - if a = 0 then γ else 0) ∧
      s0 k r' a - (s (su a) - if a = 0 then γ else 0) ≤ e' := by
    intro a
    have hs0a : s0 k r' a = s0 k (1 + r') (su a) := by
      unfold s0
      by_cases h : a.val < r'
      · rw [if_pos h, if_pos (show (su a).val < 1 + r' by rw [su_val]; omega)]
      · rw [if_neg h, if_neg (show ¬ (su a).val < 1 + r' by rw [su_val]; omega)]
    rw [hs0a]
    have h1 := he0 (su a); have h2 := heS' (su a)
    split_ifs <;> constructor <;> linarith
  obtain ⟨μ', hμ'⟩ := hHN k r'
  have hfin := hB' _ hsP z1 hz1W hz1T μ' hμ'
  obtain ⟨c, hc⟩ := hHU k (1 + r') (Nset k (1 + r')) _ μN (hCN k (1 + r')) (hNR k r' μ' hμ') hμN.conc hμN.left
    hμN.finite_compact
  rw [hc]; unfold IInt; rw [lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]
  refine ENNReal.mul_lt_top ENNReal.coe_lt_top ?_
  have : IsFiniteMeasureOnCompacts μ' := ⟨fun ⦃K⦄ hK => hμ'.finite_compact K hK⟩
  have : IsFiniteMeasureOnCompacts (μHeis k r') := ⟨fun ⦃K⦄ hK => (hHH k r').finite_compact K hK⟩
  set F : Mt k (1 + r') → ℝ≥0∞ := fun n => ENNReal.ofReal (xiR k (1 + r') s (Matrix.of n)) *
    ENNReal.ofReal ((1 + |lam k (1 + r') (liftVec k 1 r' z1) (Matrix.of n)|) ^ (-δ)) with hFd
  have hmul : Measurable (mulM (k := k) (r := 1 + r')) := by
    apply Continuous.measurable
    unfold mulM
    exact (continuous_fst (X := Mt k (1 + r')) (Y := Mt k (1 + r'))).matrix_mul continuous_snd
  have hlev : Measurable (levM k r') := by
    apply Continuous.measurable
    refine continuous_pi fun p => continuous_pi fun q => ?_
    change Continuous fun m : Mt k r' => ιLev k 1 r' (Matrix.of m) p q
    unfold ιLev
    split_ifs <;> first | exact (continuous_apply _).comp (continuous_apply _) | exact continuous_const
  have hheis : Measurable (fun X : HPar k r' => (heis0 k r' X : Mt k (1 + r'))) := by
    apply Continuous.measurable
    have hherm {ι : Type} [Fintype ι] (H : Matrix ι ι ℂ) :
        Continuous (fun p : (ι → ℂ) × (ι → ℂ) => herm H p.1 p.2) := by
      unfold herm
      exact continuous_snd.star.dotProduct (continuous_const.matrix_mulVec continuous_fst)
    have hlift : Continuous (fun X : HPar k r' => liftVec k 1 r' X.1) := by
      refine continuous_pi fun p => ?_
      change Continuous fun X : HPar k r' => liftVec k 1 r' X.1 p
      unfold liftVec
      split_ifs
      · exact (continuous_apply _).comp continuous_fst
      · exact continuous_const
    have hself : Continuous (fun X : HPar k r' => herm (Hpk k r') X.1 X.1) :=
      (hherm _).comp (continuous_fst.prodMk continuous_fst)
    have hhb : Continuous (fun X : HPar k r' => hb k r' X.1 X.2) := by
      unfold hb
      exact (Complex.continuous_ofReal.comp ((Complex.continuous_re.comp hself).neg.div_const 2)).add
        ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)
    have hrow : Continuous (fun X : HPar k r' =>
        fun j => herm (Hpk k (1 + r')) (bvec j) (liftVec k 1 r' X.1)) :=
      continuous_pi fun j => (hherm _).comp (continuous_const.prodMk hlift)
    unfold heis0 heisG
    exact (continuous_const.sub (continuous_const.matrix_vecMulVec hrow)).add
      ((hlift.add (hhb.smul continuous_const)).matrix_vecMulVec continuous_const)
  have hsw : (μHeis k r').prod (μ'.map (levM k r')) = ((μ'.map (levM k r')).prod (μHeis k r')).map Prod.swap :=
    (Measure.prod_swap).symm
  have hae : ∀ᵐ m ∂μ', m ∈ Nset k r' := ae_iff.2 hμ'.conc
  have hpt : ∀ m ∈ Nset k r', ∫⁻ h, F (mulM (h, levM k r' m)) ∂(μHeis k r') ≤
      ENNReal.ofReal (C * ‖herm (Hpk k r') (phiV k r' ⟨0, by omega⟩) (fvec k r' z1 ⟨0, by omega⟩)‖ ^ (-γ)) *
        (ENNReal.ofReal (xiR k r' (fun a => s (su a) - if a = 0 then γ else 0) (Matrix.of m)) *
          ENNReal.ofReal ((1 + |lam k r' z1 (Matrix.of m)|) ^ (-(δ / 4)))) := by
    intro m hm
    calc _ ≤ ∫⁻ X, F (mulM (heis0 k r' X, levM k r' m)) ∂volume := by
          unfold μHeis
          exact lintegral_map_le _ hheis.aemeasurable
      _ ≤ _ := by rw [hFd]; exact inner_bound hIW hF hHC hHA hk s δ γ C z1 hC' hcz (Matrix.of m) hm.1
  calc ∫⁻ n, F n ∂(((μHeis k r').prod (μ'.map (levM k r'))).map mulM)
      ≤ ∫⁻ q, F (mulM q) ∂((μHeis k r').prod (μ'.map (levM k r'))) := lintegral_map_le _ hmul.aemeasurable
    _ = ∫⁻ q, F (mulM q) ∂(((μ'.map (levM k r')).prod (μHeis k r')).map Prod.swap) := by rw [hsw]
    _ ≤ ∫⁻ q, F (mulM q.swap) ∂((μ'.map (levM k r')).prod (μHeis k r')) :=
      lintegral_map_le _ measurable_swap.aemeasurable
    _ ≤ ∫⁻ n', ∫⁻ h, F (mulM (h, n')) ∂(μHeis k r') ∂(μ'.map (levM k r')) := lintegral_prod_le _
    _ ≤ ∫⁻ m, ∫⁻ h, F (mulM (h, levM k r' m)) ∂(μHeis k r') ∂μ' := lintegral_map_le _ hlev.aemeasurable
    _ ≤ ∫⁻ m, ENNReal.ofReal (C * ‖herm (Hpk k r') (phiV k r' ⟨0, by omega⟩) (fvec k r' z1 ⟨0, by omega⟩)‖ ^ (-γ)) *
          (ENNReal.ofReal (xiR k r' (fun a => s (su a) - if a = 0 then γ else 0) (Matrix.of m)) *
            ENNReal.ofReal ((1 + |lam k r' z1 (Matrix.of m)|) ^ (-(δ / 4)))) ∂μ' := lintegral_mono_ae (hae.mono hpt)
    _ = ENNReal.ofReal (C * ‖herm (Hpk k r') (phiV k r' ⟨0, by omega⟩) (fvec k r' z1 ⟨0, by omega⟩)‖ ^ (-γ)) *
          ∫⁻ m, ENNReal.ofReal (xiR k r' (fun a => s (su a) - if a = 0 then γ else 0) (Matrix.of m)) *
            ENNReal.ofReal ((1 + |lam k r' z1 (Matrix.of m)|) ^ (-(δ / 4))) ∂μ' :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin

end ReciprocityTheory.ChartRestriction.DS.Xi
end
end
end
