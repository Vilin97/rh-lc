module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.DetColumnPerturbation
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.Matrix.Normed
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.AnalyticAtDeterminantPowerZeroInt
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.FderivDeterminantPowerColumnSum
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.FderivDeterminantPowerCornerInt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.AnalyticAtDet
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.SingToDiffAlt
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.CruxSt
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.AnalyticAtDeterminantPowerZeroInt
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.CayleyG
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.DetDFin
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.FderivDeterminantPowerColumnNeg

section

@[expose] public section

noncomputable section

open Matrix Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt.CKC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.CK

variable {N : ℕ}

def Hc (N : ℕ) (t : ℂ) (T : Matrix (Fin N) (Fin N) ℂ) : ℂ := (1 + T).det ^ t

theorem analyticAt_Hc (N : ℕ) (t : ℂ) (T0 : Matrix (Fin N) (Fin N) ℂ) (h : (1 + T0).det ∈ Complex.slitPlane) :
    AnalyticAt ℂ (Hc N t) T0 := by
  unfold Hc
  have h1 : AnalyticAt ℂ (fun T : Matrix (Fin N) (Fin N) ℂ => (1 + T).det) T0 :=
    (CK.analyticAt_det (1 + T0)).comp (analyticAt_const.add analyticAt_id)
  exact h1.cpow analyticAt_const h

theorem one_det_slit : (1 + (0 : Matrix (Fin N) (Fin N) ℂ)).det ∈ Complex.slitPlane := by
  simpa using Complex.one_mem_slitPlane

theorem analyticAt_determinant_power_zero (N : ℕ) (t : ℂ) : AnalyticAt ℂ (Hc N t) 0 := analyticAt_Hc N t 0 one_det_slit

theorem det_phiF_slit (X : Matrix (Fin N) (Fin (N + 1)) ℂ) (hX : (1 + piF X).det ∈ Complex.slitPlane) :
    (1 + phiF X).det ∈ Complex.slitPlane := by rw [det_phiF]; exact hX

theorem fderiv_determinant_power_corner (t : ℂ) (X : Matrix (Fin N) (Fin (N + 1)) ℂ) (hX : (1 + piF X).det ∈ Complex.slitPlane) :
    fderiv ℂ (Hc (N + 1) t) (phiF X) (Matrix.single 0 0 1) = t * Hc N t (piF X) := by
  have hD := det_phiF_slit X hX
  have h1 := fderiv_line (Hc (N + 1) t) (phiF X) (Matrix.single 0 0 1) (analyticAt_Hc _ t _ hD).differentiableAt
  have hD0 : (1 + piF X).det ≠ 0 := Complex.slitPlane_ne_zero hX
  have hfun : (fun s : ℂ => Hc (N + 1) t (phiF X + s • Matrix.single 0 0 1))
      = fun s : ℂ => ((1 + s) * (1 + piF X).det) ^ t := by
    funext s
    simp only [Hc]
    rw [← add_assoc, det_corner_perturbation]
  rw [hfun] at h1
  have hf : HasDerivAt (fun s : ℂ => (1 + s) * (1 + piF X).det) (1 * (1 + piF X).det) 0 :=
    ((hasDerivAt_id' (0 : ℂ)).const_add 1).mul_const _
  have h2 := hf.cpow_const (c := t) (by simpa using hX)
  refine (h1.unique h2).trans ?_
  simp only [Hc, add_zero, one_mul]
  rw [Complex.cpow_sub _ _ hD0, Complex.cpow_one]
  field_simp

theorem fderiv_determinant_power_column_neg (t : ℂ) (X : Matrix (Fin N) (Fin (N + 1)) ℂ) (hX : (1 + piF X).det ∈ Complex.slitPlane)
    (c : Fin N) :
    fderiv ℂ (Hc (N + 1) t) (phiF X) (Matrix.single 0 c.succ 1) = -fderiv ℂ (Hc N t) (piF X) (colQ X c) := by
  have hA : AnalyticAt ℂ (Hc (N + 1) t) (phiF X) := analyticAt_Hc _ t _ (det_phiF_slit X hX)
  have h1 := fderiv_line (Hc (N + 1) t) (phiF X) (Matrix.single 0 c.succ 1) hA.differentiableAt
  have e : (fun s : ℂ => Hc (N + 1) t (phiF X + s • Matrix.single 0 c.succ 1)) =
      fun s : ℂ => Hc N t (piF X + s • (-colQ X c)) := by
    funext s
    simp only [Hc]
    rw [← add_assoc, det_column_perturbation, smul_neg, ← sub_eq_add_neg, add_sub_assoc]
  rw [e] at h1
  have hB : AnalyticAt ℂ (Hc N t) (piF X) := analyticAt_Hc _ t _ hX
  have h2 := fderiv_line (Hc N t) (piF X) (-colQ X c) hB.differentiableAt
  exact (h1.unique h2).trans (map_neg _ _)

theorem ev_piFc (N : ℕ) :
    ∀ᶠ X in 𝓝 (0 : Matrix (Fin N) (Fin (N + 1)) ℂ), (1 + piF X).det ∈ Complex.slitPlane := by
  have hc : ContinuousAt (fun X : Matrix (Fin N) (Fin (N + 1)) ℂ => (1 + piF X).det) 0 :=
    ((analyticAt_det _).comp (analyticAt_const.add (analyticAt_piF 0))).continuousAt
  have h0 : (1 + piF (0 : Matrix (Fin N) (Fin (N + 1)) ℂ)).det ∈ Complex.slitPlane := by
    rw [piF_zero, add_zero, Matrix.det_one]
    exact Complex.one_mem_slitPlane
  exact hc.eventually_mem (Complex.isOpen_slitPlane.mem_nhds h0)

theorem iterated_derivative_corner_case (t : ℂ) (e : Equiv.Perm (Fin N)) :
    iteratedFDeriv ℂ N (fun y => fderiv ℂ (Hc (N + 1) t) y (Matrix.single 0 0 1)) 0
        (fun k => Matrix.single k.succ (e k).succ 1) =
      t * iteratedFDeriv ℂ N (Hc N t) 0 (fun k => Matrix.single k (e k) 1) := by
  set G : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ → ℂ :=
    fun y => fderiv ℂ (Hc (N + 1) t) y (Matrix.single 0 0 1) with hG
  have hGa : AnalyticAt ℂ G 0 := analyticAt_fderiv_apply (Hc (N + 1) t) 0 _ (analyticAt_determinant_power_zero (N + 1) t)
  have e1 := icompL G phiF phiF_add phiF_smul 0 0 phiF_zero hGa N
    (fun k => Matrix.single k (e k).succ 1) (fun k => Matrix.single k.succ (e k).succ 1)
    (fun i => phiF_single _ _)
  rw [← e1]
  have hev : (G ∘ phiF) =ᶠ[𝓝 0] (fun X : Matrix (Fin N) (Fin (N + 1)) ℂ => t * Hc N t (piF X)) := by
    filter_upwards [ev_piFc N] with X hX
    exact fderiv_determinant_power_corner t X hX
  rw [(hev.iteratedFDeriv ℂ N).eq_of_nhds]
  have hHa : AnalyticAt ℂ (fun X : Matrix (Fin N) (Fin (N + 1)) ℂ => Hc N t (piF X)) 0 := by
    have h0 : AnalyticAt ℂ (Hc N t) (piF (0 : Matrix (Fin N) (Fin (N + 1)) ℂ)) := by
      rw [piF_zero]
      exact analyticAt_determinant_power_zero N t
    exact h0.comp (analyticAt_piF 0)
  rw [iconst_mul _ 0 t hHa N]
  congr 1
  exact icompL (Hc N t) piF piF_add piF_smul 0 0 piF_zero (analyticAt_determinant_power_zero N t) N
    (fun k => Matrix.single k (e k).succ 1) (fun k => Matrix.single k (e k) 1)
    (fun i => piF_single_succ _ _)

def fsumc (t : ℂ) (c : Fin N) (X : Matrix (Fin N) (Fin (N + 1)) ℂ) : ℂ :=
  -∑ k, X k 0 * fderiv ℂ (Hc N t) (piF X) (Matrix.single k c 1)

theorem fderiv_determinant_power_column (t : ℂ) (X : Matrix (Fin N) (Fin (N + 1)) ℂ) (hX : (1 + piF X).det ∈ Complex.slitPlane)
    (c : Fin N) : fderiv ℂ (Hc (N + 1) t) (phiF X) (Matrix.single 0 c.succ 1) = fsumc t c X := by

  rw [fderiv_determinant_power_column_neg t X hX c, colQ_expand, map_sum]
  simp only [map_smul, smul_eq_mul, fsumc]

theorem analyticAt_fsumc (t : ℂ) (c : Fin N) (X0 : Matrix (Fin N) (Fin (N + 1)) ℂ)
    (h : (1 + piF X0).det ∈ Complex.slitPlane) : AnalyticAt ℂ (fsumc t c) X0 := by
  have hs := Finset.analyticAt_sum
    (f := fun k (X : Matrix (Fin N) (Fin (N + 1)) ℂ) => X k 0 * fderiv ℂ (Hc N t) (piF X) (Matrix.single k c 1))
    Finset.univ (fun k _ => (analyticAt_entry k 0 X0).mul
      ((analyticAt_fderiv_apply (Hc N t) (piF X0) _ (analyticAt_Hc N t _ h)).comp (analyticAt_piF X0)))
  rw [Finset.sum_fn] at hs
  exact hs.neg

theorem fsum_linec (t : ℂ) (c k0 : Fin N) (y : Matrix (Fin N) (Fin (N + 1)) ℂ) (s : ℂ) :
    fsumc t c (y + s • Matrix.single k0 0 1) =
      fsumc t c y - s * fderiv ℂ (Hc N t) (piF y) (Matrix.single k0 c 1) := by
  simp only [fsumc]
  rw [piF_add, piF_smul, piF_single_zero, smul_zero, add_zero]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.single_apply, and_true, mul_ite, mul_one,
    mul_zero, ite_mul, zero_mul, add_mul, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring

theorem fderiv_fsumc (t : ℂ) (c k0 : Fin N) (y : Matrix (Fin N) (Fin (N + 1)) ℂ)
    (hy : (1 + piF y).det ∈ Complex.slitPlane) :
    fderiv ℂ (fsumc t c) y (Matrix.single k0 0 1) = -fderiv ℂ (Hc N t) (piF y) (Matrix.single k0 c 1) := by
  have h1 := fderiv_line (fsumc t c) y (Matrix.single k0 0 1) (analyticAt_fsumc t c y hy).differentiableAt
  have hfun : (fun s : ℂ => fsumc t c (y + s • Matrix.single k0 0 1))
      = fun s : ℂ => fsumc t c y - s * fderiv ℂ (Hc N t) (piF y) (Matrix.single k0 c 1) := by
    funext s
    exact fsum_linec t c k0 y s
  rw [hfun] at h1
  have h2 : HasDerivAt (fun s : ℂ => fsumc t c y - s * fderiv ℂ (Hc N t) (piF y) (Matrix.single k0 c 1))
      (0 - 1 * fderiv ℂ (Hc N t) (piF y) (Matrix.single k0 c 1)) 0 :=
    (hasDerivAt_const _ _).sub ((hasDerivAt_id' (0 : ℂ)).mul_const _)
  refine (h1.unique h2).trans ?_
  ring

end PositivityTheory.Rg.Sw.HSt.CKC
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.CapelliDeterminantRisingFactorial

section

@[expose] public section

noncomputable section

open Matrix Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt.CKC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.CK

theorem iterated_derivative_column_case (t : ℂ) (M : ℕ) (e : Equiv.Perm (Fin (M + 1))) (c : Fin (M + 1)) :
    iteratedFDeriv ℂ (M + 1) (fun y => fderiv ℂ (Hc (M + 1 + 1) t) y (Matrix.single 0 c.succ 1)) 0
        (fun k => Matrix.single k.succ (Equiv.Perm.decomposeFin.symm (c.succ, e) k.succ) 1) =
      -iteratedFDeriv ℂ (M + 1) (Hc (M + 1) t) 0 (fun k => Matrix.single k (e k) 1) := by
  set σ := Equiv.Perm.decomposeFin.symm (c.succ, e) with hσ
  set k0 : Fin (M + 1) := e.symm c with hk0
  have hek0 : e k0 = c := by rw [hk0, Equiv.apply_symm_apply]
  have hσk0 : σ k0.succ = 0 := by
    rw [hσ, Equiv.Perm.decomposeFin_symm_apply_succ, hek0, Equiv.swap_apply_right]
  have hσo : ∀ j : Fin M, σ (k0.succAbove j).succ = (e (k0.succAbove j)).succ := by
    intro j
    rw [hσ, Equiv.Perm.decomposeFin_symm_apply_succ]
    apply Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _)
    intro h
    have h' := Fin.succ_injective _ h
    rw [← hek0] at h'
    exact Fin.succAbove_ne k0 j (e.injective h')
  have hslit0 : (1 + piF (0 : Matrix (Fin (M + 1)) (Fin (M + 1 + 1)) ℂ)).det ∈ Complex.slitPlane := by
    simp [piF_zero]
  have hA := icompL (fun y => fderiv ℂ (Hc (M + 1 + 1) t) y (Matrix.single 0 c.succ 1)) phiF
    phiF_add phiF_smul 0 0 phiF_zero
    (analyticAt_fderiv_apply _ _ _ (analyticAt_determinant_power_zero _ t)) (M + 1)
    (fun k => Matrix.single k (σ k.succ) 1)
    (fun k => Matrix.single k.succ (σ k.succ) 1) (fun k => phiF_single _ _)
  rw [← hA]
  have hB : (fun y => fderiv ℂ (Hc (M + 1 + 1) t) y (Matrix.single 0 c.succ 1)) ∘ phiF
      =ᶠ[𝓝 0] fsumc t c := by
    filter_upwards [ev_piFc (M + 1)] with X hX
    exact fderiv_determinant_power_column t X hX c
  rw [(hB.iteratedFDeriv ℂ (M + 1)).eq_of_nhds]
  rw [ipeel (fsumc t c) 0 (analyticAt_fsumc t c 0 hslit0) M _ k0]
  have hD : (fun y => fderiv ℂ (fsumc t c) y (Matrix.single k0 (σ k0.succ) 1)) =ᶠ[𝓝 0]
      fun y => (-1 : ℂ) *
        ((fun z => fderiv ℂ (Hc (M + 1) t) z (Matrix.single k0 c 1)) ∘ piF) y := by
    filter_upwards [ev_piFc (M + 1)] with X hX
    have h := fderiv_fsumc t c k0 X hX
    simp only [Function.comp_apply]
    rw [hσk0]
    erw [h]
    ring
  refine (congrFun (congrArg DFunLike.coe (hD.iteratedFDeriv ℂ M).eq_of_nhds) _).trans ?_
  have hG0 : AnalyticAt ℂ (fun z => fderiv ℂ (Hc (M + 1) t) z (Matrix.single k0 c 1)) 0 :=
    analyticAt_fderiv_apply _ _ _ (analyticAt_determinant_power_zero _ t)
  have hGc : AnalyticAt ℂ
      ((fun z => fderiv ℂ (Hc (M + 1) t) z (Matrix.single k0 c 1)) ∘ piF) 0 := by
    have hcomp : ((fun z => fderiv ℂ (Hc (M + 1) t) z (Matrix.single k0 c 1)) ∘ piF) =
        (fun z => fderiv ℂ (Hc (M + 1) t) z (Matrix.single k0 c 1)) ∘ (piL (M + 1)) := by
      funext X
      simp only [Function.comp_apply, piL_apply]
    rw [hcomp]
    refine AnalyticAt.comp ?_ ((piL (M + 1)).analyticAt 0)
    rw [piL_apply, piF_zero]
    exact hG0
  refine (iconst_mul _ 0 (-1) hGc M _).trans ?_
  rw [icompL (fun z => fderiv ℂ (Hc (M + 1) t) z (Matrix.single k0 c 1)) piF
    piF_add piF_smul 0 0 piF_zero hG0 M _
    (fun k => Matrix.single (k0.succAbove k) (e (k0.succAbove k)) 1)
    (fun k => by simp only [hσo, piF_single_succ])]
  rw [neg_one_mul, ipeel (Hc (M + 1) t) 0 (analyticAt_determinant_power_zero _ t) M _ k0, hek0]
  rfl

theorem term_pc (t : ℂ) (N : ℕ) (p : Fin (N + 1)) (e : Equiv.Perm (Fin N)) :
    iteratedFDeriv ℂ (N + 1) (Hc (N + 1) t) 0
        (fun k => Matrix.single k (Equiv.Perm.decomposeFin.symm (p, e) k) 1) =
      iteratedFDeriv ℂ N (fun y => fderiv ℂ (Hc (N + 1) t) y (Matrix.single 0 p 1)) 0
        (fun k => Matrix.single k.succ (Equiv.Perm.decomposeFin.symm (p, e) k.succ) 1) := by
  rw [ipeel0 (Hc (N + 1) t) 0 (analyticAt_determinant_power_zero (N + 1) t) N]
  simp only [Equiv.Perm.decomposeFin_symm_apply_zero]
  rfl

theorem rec_stepc (t : ℂ) (N : ℕ) : detD (Hc (N + 1) t) = (t + N) * detD (Hc N t) := by
  have h0 : ∀ e : Equiv.Perm (Fin N),
      iteratedFDeriv ℂ (N + 1) (Hc (N + 1) t) 0
        (fun k => Matrix.single k (Equiv.Perm.decomposeFin.symm (0, e) k) 1) =
      t * iteratedFDeriv ℂ N (Hc N t) 0 (fun k => Matrix.single k (e k) 1) := by
    intro e
    rw [term_pc]
    simp only [Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self, Equiv.refl_apply]
    exact iterated_derivative_corner_case t e
  have h1 : ∀ (c : Fin N) (e : Equiv.Perm (Fin N)),
      iteratedFDeriv ℂ (N + 1) (Hc (N + 1) t) 0
        (fun k => Matrix.single k (Equiv.Perm.decomposeFin.symm (c.succ, e) k) 1) =
      -iteratedFDeriv ℂ N (Hc N t) 0 (fun k => Matrix.single k (e k) 1) := by
    intro c e
    cases N with
    | zero => exact c.elim0
    | succ M =>
      rw [term_pc]
      exact iterated_derivative_column_case t M e c
  rw [detD_fin (N + 1) _ (analyticAt_determinant_power_zero (N + 1) t), detD_fin N _ (analyticAt_determinant_power_zero N t),
    ← Equiv.sum_comp Equiv.Perm.decomposeFin.symm, Fintype.sum_prod_type, Fin.sum_univ_succ]
  simp only [Equiv.Perm.decomposeFin.symm_sign, h0, h1, Fin.succ_ne_zero, if_true, if_false,
    Units.val_mul, Units.val_neg, Units.val_one, Int.cast_mul, Int.cast_neg, Int.cast_one,
    one_mul, neg_one_mul, mul_neg, neg_neg, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  rw [add_mul, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun e _ => by ring

theorem capelli_determinant_rising_factorial (t : ℂ) : ∀ N : ℕ, detD (Hc N t) = ∏ i ∈ Finset.range N, (t + i)
  | 0 => by
    rw [detD_fin 0 _ (analyticAt_determinant_power_zero 0 t)]
    simp [Hc, iteratedFDeriv_zero_apply]
  | N + 1 => by
    rw [rec_stepc, capelli_determinant_rising_factorial t N, Finset.prod_range_succ]
    ring

end PositivityTheory.Rg.Sw.HSt.CKC

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw.LVs

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem kappaC : KappaC := fun N t => CKC.capelli_determinant_rising_factorial t N

theorem analyticAt_det_one_add_cpow {ι : Type} [Fintype ι] [DecidableEq ι] (t : ℂ) :
    AnalyticAt ℂ (fun T : Matrix ι ι ℂ => (1 + T).det ^ t) 0 := by
  have h1 : AnalyticAt ℂ (fun T : Matrix ι ι ℂ => (1 + T).det) 0 :=
    (LVs.analyticAt_det (1 + 0)).comp (analyticAt_const.add analyticAt_id)
  exact h1.cpow analyticAt_const (by simpa using Complex.one_mem_slitPlane)

end PositivityTheory.Rg.Sw.HSt
end
end
end
