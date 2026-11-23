module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.CasValK
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.BigRep
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.LayerWeight
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.Weights
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirAlgebra.CasimirKKhwVec
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.Permute
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.BigCas
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.KhwWeightEqOfIrr
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.CrossOpSlotBound
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.CrossOpSlotBound
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.InnerCrossOpEigEqZero
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.KUnitB
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.LayerBasic
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.PhiPerm
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.PositionPrependMemNoncompactPositionSubmodule
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.SchPhiOneApply
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.CFCoreA
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.IsInfUnitary
import Mathlib.Algebra.Order.Star.Real
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SchSharpA
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.CARUnit
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.LowFock
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.NcVOneDecomp

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.BochIneq

section

@[expose] public section

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.G2
variable {n : ℕ}

section Boch

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M} {lam : Fin n → ℝ}

theorem bochner_ineq (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hmono : StrictAnti lam) {h : ℝ} (hh : GapAtLeast ε lam h)
    (hbig : 2 * (n : ℝ) < h) {k : ℕ} {P : Big n k M} (hP : P ∈ ncV ε V k)
    (hposition : ∀ i κ, slice i κ P ∈ Wp ε E V) :
    (casValK ε (lowK ε lam) + 2 * (k : ℝ) * (h - n + 1)) * ‖P‖ ^ 2 ≤
      RCLike.re (inner ℂ (casimirK ε (bAct E k) P) P) := by
  classical

  have hP' := hP
  simp only [ReciprocityTheory.ChartRestriction.DS.ncV, Submodule.mem_iInf, Submodule.mem_comap] at hP'

  have hcas : casimirK ε (mAct E k) P = ((casValK ε (lowK ε lam) : ℝ) : ℂ) • P := by
    refine PiLp.ext fun κ => ?_
    rw [ReciprocityTheory.ChartRestriction.DS.casimirK_mAct_apply, PiLp.smul_apply]
    have hm := hP' κ
    by_cases hκ : ∀ i, ε (κ i).1 ≠ ε (κ i).2
    · rw [if_pos hκ] at hm
      have hm' : P κ ∈ V := hm
      exact ReciprocityTheory.ChartRestriction.DS.casimirK_irr hE hV _ hm'
    · rw [if_neg hκ] at hm
      have hz : P κ = 0 := (Submodule.mem_bot ℂ).1 hm
      rw [hz, map_zero, smul_zero]

  have hsplit : RCLike.re (inner ℂ (casimirK ε (bAct E k) P) P)
      = RCLike.re (inner ℂ (factorCasimir ε k P) P) + RCLike.re (inner ℂ (casimirK ε (mAct E k) P) P)
        + 2 * ∑ i, RCLike.re (inner ℂ (crossOp ε E k i P) P) := by
    rw [ReciprocityTheory.ChartRestriction.DS.casimirK_bAct]

    simp only [two_nsmul, LinearMap.add_apply, LinearMap.sum_apply,
    inner_add_left, sum_inner, map_add, map_sum]
    ring
  have h1 : 0 ≤ RCLike.re (inner ℂ (factorCasimir ε k P) P) :=
    ReciprocityTheory.ChartRestriction.DS.factorCasimir_nonneg k P
  have h2 : RCLike.re (inner ℂ (casimirK ε (mAct E k) P) P) = casValK ε (lowK ε lam) * ‖P‖ ^ 2 := by
    rw [hcas, inner_smul_left, Complex.conj_ofReal, ← inner_self_eq_norm_sq (𝕜 := ℂ) P]
    simp [Complex.mul_re]

  have h3 : ∀ i : Fin k, 2 * (h - n + 1) * ‖P‖ ^ 2 ≤ 2 * RCLike.re (inner ℂ (crossOp ε E k i P) P) :=
    fun i => ReciprocityTheory.ChartRestriction.DS.G2.crossOp_position_bound hE hU hV hmono hh hbig i (fun κ => hposition i κ)
  have h4 : (k : ℝ) * (2 * (h - n + 1) * ‖P‖ ^ 2) ≤ ∑ i : Fin k, 2 * RCLike.re (inner ℂ (crossOp ε E k i P) P) := by
    have := Finset.sum_le_sum (s := Finset.univ) (fun i _ => h3 i)
    simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using this
  rw [hsplit, h2, ← Finset.mul_sum] at *
  nlinarith [h1, h4]

end Boch

end ReciprocityTheory.ChartRestriction.DS.G2
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SchSharp

section

@[expose] public section

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem sch_sharp {ε : Fin n → Bool} {lam : Fin n → ℝ} (hmono : StrictAnti lam) {h : ℝ}
    (hh : GapAtLeast ε lam h) (h2 : 2 < h)
    {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {E : Fin n → Fin n → Module.End ℂ M}
    (hE : IsGlRep E) (hU : IsInfUnitary ε E) {a b : Fin n} (hab : a < b) (hε : ε a ≠ ε b)
    {W : Submodule ℂ M} (hW : IsKIrrHW ε E (lowK ε lam - root a b) W)
    (hc : ∀ v ∈ W, casimir E v = (casVal lam : ℂ) • v) : False := by
  classical
  have hne : a ≠ b := hab.ne
  have hΛ : lowK ε (lam - root a b) = lowK ε lam - root a b := by
    unfold lowK; abel
  have hW' : IsKIrrHW ε E (lowK ε (lam - root a b)) W := by rw [hΛ]; exact hW
  have hmono' := ssh_strictAnti hmono hh h2 hE a b hW'
  obtain ⟨z, hzW, -, hz0, hzK⟩ := lowFock_exists ε hE hmono' hW'
  have hzK' : IsKHWVec ε (diagE ε (eT E) cpT cmT) ((lam - root a b - rhoC ε) + rhoHol ε) z := hzK
  have hcas : casimir (eT E) z = ((casVal lam : ℝ) : ℂ) • z := by
    obtain ⟨z0, hz0eq⟩ := LinearMap.mem_range.mp hzW
    rw [ssh_casimir_eT, ← hz0eq]
    clear hz0eq
    induction z0 using TensorProduct.induction_on with
    | zero => simp
    | tmul m f => simp [TensorProduct.map_tmul, hc _ m.2, TensorProduct.smul_tmul']
    | add x y hx hy => simp only [map_add (f := _), hx, hy, smul_add]
  have hD2 := two_D_sq_khw (eT_isGlRep hE) cpT_cmT_isCAR (eT_commutesCAR E) hzK' hcas
  have hval : nsq (lam - root a b - rhoC ε + rhoC ε) - nsq (rho n) - casVal lam = 2 - 2 * (lam a - lam b) := by
    rw [sub_add_cancel, ssh_nsq_sub_root lam hne]
    unfold casVal
    ring
  have hgap : h ≤ lam a - lam b := by
    have := hh a b hε
    rwa [abs_of_pos (sub_pos.mpr (hmono hab))] at this
  set D := dOp ε (eT E) cpT + dOp' ε (eT E) cmT with hDdef
  have key : tform z ((2 : ℂ) • (D * D) z) = ((2 - 2 * (lam a - lam b) : ℝ) : ℂ) * tform z z := by
    rw [hD2, tform_smul_right, ← hval]
    push_cast
    ring
  rw [tform_smul_right, Module.End.mul_apply, ← tform_D hU] at key
  have hre := congrArg Complex.re key
  rw [Complex.re_ofReal_mul] at hre
  simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero] at hre
  have p1 := tform_self_re_nonneg (D z)
  have p2 := tform_self_re_pos hz0
  have hneg : (2 - 2 * (lam a - lam b)) < 0 := by linarith
  nlinarith

end ReciprocityTheory.ChartRestriction.DS
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.KhwEqZeroSharp

section

@[expose] public section

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.G2
variable {n : ℕ}

section Sch

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M} {lam : Fin n → ℝ}


omit [NormedAddCommGroup M] [InnerProductSpace ℂ M] in
theorem two_lt_of_gap {a b : Fin n} (hε : ε a ≠ ε b) {h : ℝ} (hbig : 2 * (n : ℝ) < h) : 2 < h := by
  have hab : a ≠ b := fun e => hε (by rw [e])
  have ha := a.isLt
  have hb := b.isLt
  have hv : a.val ≠ b.val := fun e => hab (Fin.ext e)
  have : (2 : ℝ) ≤ n := by exact_mod_cast (by omega : 2 ≤ n)
  linarith

theorem khw_eq_zero_sharp (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hmono : StrictAnti lam) {h : ℝ}
    (hh : GapAtLeast ε lam h) (h2 : 2 < h) {a b : Fin n} (hab : a < b) (hε : ε a ≠ ε b)
    {T : Submodule ℂ M} (hTf : FiniteDimensional ℂ T) (hTk : IsKStableSub ε E T)
    (hTc : ∀ v ∈ T, casimir E v = (casVal lam : ℂ) • v) {y : M} (hyT : y ∈ T)
    (hy : IsKHWVec ε E (lowK ε lam - root a b) y) : y = 0 := by
  by_contra hy0
  have hle := kLowSpan_le (E := E) hTk hyT
  have hfin : FiniteDimensional ℂ (kLowSpan ε E y) := Submodule.finiteDimensional_of_le hle
  exact sch_sharp hmono hh h2 hE hU hab hε (kLowSpan_kIrrHW hE hU hy hy0 hfin)
    (fun v hv => hTc v (hle hv))

theorem phi_one_Wm (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hmono : StrictAnti lam) {h : ℝ} (hh : GapAtLeast ε lam h)
    (hbig : 2 * (n : ℝ) < h) {x : Big n 1 M} (hx : x ∈ Wm ε E V) : phi E 1 x = 0 := by
  by_contra hne
  have := finiteDimensional_ncV (ε := ε) hV.1 1
  have hfdW : FiniteDimensional ℂ (Wm ε E V) := Submodule.finiteDimensional_of_le Wm_le_ncV
  have hWst : IsKStableSub ε (bAct E 1) (Wm ε E V) := Wm_kStable hE hU hV
  set T : Submodule ℂ M := (Wm ε E V).map (phi E 1) with hTdef
  have hfdT : FiniteDimensional ℂ T := inferInstance
  have hTst : IsKStableSub ε E T := by
    intro a b hab v hv
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hv
    rw [← phi_bAct hE 1 hab y]
    exact Submodule.mem_map_of_mem (hWst a b hab y hy)
  have hTne : T ≠ ⊥ := by
    intro hT
    have : phi E 1 x ∈ T := Submodule.mem_map_of_mem hx
    rw [hT, Submodule.mem_bot] at this
    exact hne this
  have hKU : IsKUnitary ε E := isKUnitary_of_isInfUnitary hU
  obtain ⟨y, hyT, hy0, μ, hyμ⟩ := exists_khw hE hKU hfdT hTst hTne
  obtain ⟨x₀, hx₀, rfl⟩ := Submodule.mem_map.1 hyT
  obtain ⟨x1, hx1, -, hkhw, hfx⟩ := lift_khw (A := bAct E 1) (bAct_isKUnitary hU 1) (phi E 1)
    (fun a b hab z => phi_bAct hE 1 hab z) hfdW hWst hx₀ hyμ
  have hx10 : x1 ≠ 0 := by
    rintro rfl
    rw [map_zero] at hfx
    exact hy0 hfx.symm
  obtain ⟨a, b, hab, hε, hμ⟩ := Wm_khw hE hU hV hmono hh hbig hx1 hx10 hkhw
  have hTc : ∀ v ∈ T, casimir E v = (casVal lam : ℂ) • v := by
    intro v hv
    obtain ⟨x', hx', rfl⟩ := Submodule.mem_map.1 hv
    exact casimir_genSub hE hc _ (layer_le_genSub (ε := ε) 1 (phi_mem_layer (Wm_le_ncV hx')))
  rw [hμ] at hyμ
  exact hy0 (khw_eq_zero_sharp hE hU hmono hh (two_lt_of_gap hε hbig) hab hε hfdT hTst hTc hyT hyμ)

theorem phi_Wm_last (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hmono : StrictAnti lam) {h : ℝ} (hh : GapAtLeast ε lam h)
    (hbig : 2 * (n : ℝ) < h) {k : ℕ} {F : Big n (k + 1) M}
    (hF : ∀ κ, slice (Fin.last k) κ F ∈ Wm ε E V) : phi E (k + 1) F = 0 := by
  have key : ∀ init : Fin k → Fin n × Fin n,
      ∑ p : Fin n × Fin n, E p.1 p.2 (F (Fin.snoc init p : Fin (k + 1) → Fin n × Fin n)) = 0 := by
    intro init
    rcases isEmpty_or_nonempty (Fin n × Fin n) with h0 | hne
    · simp [Finset.univ_eq_empty]
    · obtain ⟨p0⟩ := hne
      have := phi_one_Wm hE hU hV hc hmono hh hbig (hF (Fin.snoc init p0))
      rw [sch_phi_one_apply] at this
      simpa only [sch_slice_apply, Fin.update_snoc_last] using this
  unfold phi
  rw [LinearMap.sum_apply, ← (Fin.snocEquiv (fun _ => Fin n × Fin n)).sum_comp,
    Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_eq_zero (fun init _ => ?_)
  have hs : ∀ p, (Fin.snocEquiv (fun _ => Fin n × Fin n)) (p, init) =
      (Fin.snoc init p : Fin (k + 1) → Fin n × Fin n) := fun p => rfl
  simp only [hs, LinearMap.comp_apply, sch_coord_apply, sch_word_snoc, Module.End.mul_apply]

  rw [← map_sum, key, map_zero]

theorem phi_Wm_position (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hmono : StrictAnti lam) {h : ℝ} (hh : GapAtLeast ε lam h)
    (hbig : 2 * (n : ℝ) < h) {k : ℕ} (i : Fin (k + 1)) {F : Big n (k + 1) M} (hF0 : F ∈ ncV ε V (k + 1))
    (hF : ∀ κ, slice i κ F ∈ Wm ε E V) : phi E (k + 1) F ∈ layer ε E V k := by
  set σ : Equiv.Perm (Fin (k + 1)) := Equiv.swap i (Fin.last k) with hσ
  have hperm : ∀ κ, slice (Fin.last k) κ (permute σ F) = slice i (κ ∘ σ) F := by
    intro κ
    unfold slice
    congr 1
    funext ι
    rw [sch_permute_apply, Function.update_comp_equiv, hσ, Equiv.symm_swap, Equiv.swap_apply_right]
  have h0 : phi E (k + 1) (permute σ F) = 0 :=
    phi_Wm_last hE hU hV hc hmono hh hbig (fun κ => by rw [hperm]; exact hF _)
  have hs := phi_permute_sub_mem hE hV.2.1 σ hF0
  rwa [h0, sub_zero] at hs

end Sch

end ReciprocityTheory.ChartRestriction.DS.G2
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.LayerBound

section

@[expose] public section

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.G2
variable {n : ℕ}

section LayerBound

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M} {lam : Fin n → ℝ}

theorem khw_layer_succ_bound (hE : IsGlRep E) (hU : IsInfUnitary ε E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hmono : StrictAnti lam) {h : ℝ} (hh : GapAtLeast ε lam h)
    (hbig : 2 * (n : ℝ) < h) (k : ℕ) {μ : Fin n → ℝ} {w : M}
    (hw : w ∈ layer ε E V (k + 1)) (hperp : ∀ u ∈ layer ε E V k, inner ℂ u w = 0)
    (hw0 : w ≠ 0) (hμ : IsKHWVec ε E μ w) :
    IsNCSum ε (k + 1) (μ - lowK ε lam) ∧
      casValK ε (lowK ε lam) + 2 * ((k : ℝ) + 1) * (h - n + 1) ≤ casValK ε μ := by
  obtain ⟨hVfd, hVk, -, -⟩ := id hV
  obtain ⟨P, hP, hP0, hPμ, hPperp⟩ := lift_layer hE hU hVfd hVk hw hperp hμ hw0
  refine ⟨khw_big_weight hE hV hP hP0 hPμ, ?_⟩
  have hposition : ∀ i κ, slice i κ P ∈ Wp ε E V := fun i =>
    position_perp hE hU hV hmono hh hbig i hP
      (fun F hF hFs => hPperp F hF (phi_Wm_position hE hU hV hc hmono hh hbig i hF hFs))
  have hb := bochner_ineq hE hU hV hmono hh hbig hP hposition
  have hcas := casimirK_khwVec ε (bAct_isGlRep hE (k + 1)) hPμ
  rw [hcas, inner_smul_left, inner_self_eq_norm_sq_to_K, Complex.conj_ofReal,
    ← RCLike.ofReal_pow, RCLike.re_mul_ofReal] at hb
  simp only [RCLike.re_to_complex, Complex.ofReal_re] at hb
  change _ ≤ casValK ε μ * ‖P‖ ^ 2 at hb
  have hpos : 0 < ‖P‖ ^ 2 := pow_pos (norm_pos_iff.2 hP0) 2
  push_cast at hb
  exact le_of_mul_le_mul_right hb hpos

end LayerBound

end ReciprocityTheory.ChartRestriction.DS.G2
end
end
end
