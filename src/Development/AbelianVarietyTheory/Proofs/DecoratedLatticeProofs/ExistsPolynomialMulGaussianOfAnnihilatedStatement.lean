module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EqEvalOfDirDerivVanish

section

@[expose] public section

open scoped ContDiff

namespace GlobalTheory.PolyOfDeriv

theorem taylor_of_chain (N : ℕ) : ∀ (G : ℕ → ℝ → ℂ) (_ : ∀ k t, HasDerivAt (G k) (G (k+1) t) t)
    (_ : G N = 0) (t : ℝ),
    G 0 t = ∑ k ∈ Finset.range N, G k 0 * ((t ^ k / k.factorial : ℝ) : ℂ) := by
  induction N with
  | zero => intro G _ hN t; simp [hN]
  | succ N ih =>
    intro G hG hN t
    have h1 : ∀ s, G 1 s = ∑ k ∈ Finset.range N, G (k+1) 0 * ((s ^ k / k.factorial : ℝ) : ℂ) :=
      fun s => ih (fun k => G (k+1)) (fun k t => hG (k+1) t) hN s
    have hm : ∀ (k : ℕ) (s : ℝ), HasDerivAt
        (fun s : ℝ => ((s ^ (k+1) / (k+1).factorial : ℝ) : ℂ))
        ((s ^ k / k.factorial : ℝ) : ℂ) s := by
      intro k s
      have h := (hasDerivAt_pow (k+1) s).div_const ((k+1).factorial : ℝ)
      have e : ((k+1 : ℕ) : ℝ) * s ^ (k + 1 - 1) / ((k+1).factorial : ℝ) = s ^ k / k.factorial := by
        rw [Nat.factorial_succ, Nat.add_sub_cancel, Nat.cast_mul]
        have : ((k+1 : ℕ) : ℝ) ≠ 0 := by positivity
        have : ((k.factorial : ℕ) : ℝ) ≠ 0 := by positivity
        field_simp
      rw [e] at h
      exact h.ofReal_comp
    have hH : ∀ s, HasDerivAt (fun s => G 0 s - ∑ k ∈ Finset.range N,
        G (k+1) 0 * ((s ^ (k+1) / (k+1).factorial : ℝ) : ℂ)) 0 s := by
      intro s
      have h2 : HasDerivAt (fun s : ℝ => ∑ k ∈ Finset.range N,
          G (k+1) 0 * ((s ^ (k+1) / (k+1).factorial : ℝ) : ℂ)) (G 1 s) s := by
        rw [h1 s]
        exact HasDerivAt.fun_sum fun k _ => (hm k s).const_mul _
      have h3 := (hG 0 s).fun_sub h2
      rwa [zero_add, sub_self] at h3
    have hc := is_const_of_deriv_eq_zero (fun s => (hH s).differentiableAt)
      (fun s => (hH s).deriv) t 0
    rw [Finset.sum_range_succ']
    simp only [ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true, zero_pow,
      zero_div, Complex.ofReal_zero, mul_zero, Finset.sum_const_zero, sub_zero] at hc
    rw [← hc]
    simp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem hasDerivAt_iter {u : E → ℂ} (hu : ContDiff ℝ ∞ u) (k : ℕ) (y x : E) (t : ℝ) :
    HasDerivAt (fun t : ℝ => iteratedFDeriv ℝ k u (y + t • x) (fun _ => x))
      (iteratedFDeriv ℝ (k+1) u (y + t • x) (fun _ => x)) t := by
  have hk : (k : WithTop ℕ∞) < ∞ := by exact_mod_cast ENat.coe_lt_top k
  have hd := ((hu.differentiable_iteratedFDeriv hk) (y + t • x)).hasFDerivAt
  have hl : HasDerivAt (fun t : ℝ => y + t • x) x t := by
    simpa using ((hasDerivAt_id t).smul_const x).const_add y
  have h1 := hd.comp_hasDerivAt t hl
  have h2 := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => E) ℂ
    (fun _ => x)).hasFDerivAt.comp_hasDerivAt t h1
  rw [iteratedFDeriv_succ_apply_left]
  exact h2

theorem foldr_replicate {u : E → ℂ} (hu : ContDiff ℝ ∞ u) (x : E) (k : ℕ) :
    (List.replicate k x).foldr
      (fun y g => fun z => deriv (fun t : ℝ => g (z + t • y)) 0) u
      = fun y => iteratedFDeriv ℝ k u y (fun _ => x) := by
  induction k with
  | zero => funext y; simp
  | succ k ih =>
    rw [List.replicate_succ, List.foldr_cons, ih]
    funext y
    have := (hasDerivAt_iter hu k y x 0).deriv
    simpa using this

theorem multilinear_diag_poly {ι : Type} [Fintype ι] [DecidableEq ι] {k : ℕ}
    (M : ContinuousMultilinearMap ℝ (fun _ : Fin k => ι → ℝ) ℂ) :
    ∃ q : MvPolynomial ι ℂ, ∀ x : ι → ℝ,
      M (fun _ => x) = MvPolynomial.eval (fun i => (x i : ℂ)) q := by
  refine ⟨∑ r : Fin k → ι, MvPolynomial.C (M (fun j => Pi.single (r j) (1:ℝ))) *
    ∏ j, MvPolynomial.X (r j), ?_⟩
  intro x
  have hx : (fun _ : Fin k => x) = fun _ => ∑ i, x i • (Pi.single i (1:ℝ) : ι → ℝ) := by
    funext _; ext l; simp [Pi.single_apply]

  rw [hx, M.map_sum]

  simp only [map_sum, map_mul, MvPolynomial.eval_C, map_prod, MvPolynomial.eval_X]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [M.map_smul_univ (fun j => x (r j)) (fun j => Pi.single (r j) 1)]
  rw [Complex.real_smul, Complex.ofReal_prod, mul_comm]

theorem eq_eval_of_dirDeriv_vanish : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ)
    (u : (ι → ℝ) → ℂ), ContDiff ℝ ∞ u →
    (∀ L : List (ι → ℝ), L.length = N →
      L.foldr (fun y g => fun x => deriv (fun t : ℝ => g (x + t • y)) 0) u = 0) →
    ∃ p : MvPolynomial ι ℂ, ∀ x, u x = MvPolynomial.eval (fun i => (x i : ℂ)) p := by
  intro ι _ _ N u hu hL
  choose q hq using fun k => multilinear_diag_poly (iteratedFDeriv ℝ k u 0)
  refine ⟨∑ k ∈ Finset.range N, MvPolynomial.C ((k.factorial : ℂ)⁻¹) * q k, ?_⟩
  intro x
  have hrep := hL (List.replicate N x) List.length_replicate
  rw [foldr_replicate hu] at hrep
  have key := taylor_of_chain N (fun k t => iteratedFDeriv ℝ k u (0 + t • x) (fun _ => x))
    (fun k t => hasDerivAt_iter hu k 0 x t) (by funext t; exact congrFun hrep _) 1
  simp only [zero_add, one_smul, zero_smul, iteratedFDeriv_zero_apply, hq] at key
  rw [key]

  simp only [map_sum, map_mul, MvPolynomial.eval_C]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm]; simp

end GlobalTheory.PolyOfDeriv
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsPolynomialMulGaussianOfAnnihilated

section

@[expose] public section

open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AnnPoly

section Generic

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def dirD (y : E) (g : E → ℂ) : E → ℂ := fun x => deriv (fun t : ℝ => g (x + t • y)) 0

theorem hasDerivAt_line {g : E → ℂ} {x : E} (hg : DifferentiableAt ℝ g x) (y : E) :
    HasDerivAt (fun t : ℝ => g (x + t • y)) (fderiv ℝ g x y) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => x + t • y) y 0 := by
    simpa using ((hasDerivAt_id' (0:ℝ)).smul_const y).const_add x
  have h2 : HasFDerivAt g (fderiv ℝ g x) (x + (0:ℝ) • y) := by simpa using hg.hasFDerivAt
  exact h2.comp_hasDerivAt 0 h1

theorem dirD_eq {g : E → ℂ} (hg : Differentiable ℝ g) (y : E) : dirD y g = fun x => fderiv ℝ g x y := by
  funext x
  exact (hasDerivAt_line (hg x) y).deriv

theorem contDiff_dirD {g : E → ℂ} (hg : ContDiff ℝ ∞ g) (y : E) : ContDiff ℝ ∞ (dirD y g) := by
  rw [dirD_eq (hg.differentiable (by simp)) y]
  exact ((contDiff_infty_iff_fderiv.1 hg).2).clm_apply contDiff_const

theorem foldr_ofFn_dirD {u : E → ℂ} (hu : ContDiff ℝ ∞ u) : ∀ (k : ℕ) (m : Fin k → E),
    (List.ofFn m).foldr dirD u = fun x => iteratedFDeriv ℝ k u x m := by
  intro k
  induction k with
  | zero => intro m; funext x; simp [iteratedFDeriv_zero_apply]
  | succ k ih =>
    intro m
    rw [List.ofFn_succ, List.foldr_cons, ih (fun i => m i.succ)]
    have hd : Differentiable ℝ (iteratedFDeriv ℝ k u) :=
      ContDiff.differentiable_iteratedFDeriv (by exact_mod_cast ENat.coe_lt_top k) hu
    funext x
    have hA : HasFDerivAt (iteratedFDeriv ℝ k u) (fderiv ℝ (iteratedFDeriv ℝ k u) x) (x + (0:ℝ) • m 0) := by
      simpa using (hd x).hasFDerivAt
    have hl : HasDerivAt (fun t : ℝ => x + t • m 0) (m 0) 0 := by
      simpa using ((hasDerivAt_id' (0:ℝ)).smul_const (m 0)).const_add x
    have h3 := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => E) ℂ (fun i => m i.succ)).hasFDerivAt.comp_hasDerivAt 0
      (hA.comp_hasDerivAt 0 hl)
    rw [iteratedFDeriv_succ_apply_left]
    exact h3.deriv

theorem foldr_dirD_eq_zero {T : Type} [Fintype T] [DecidableEq T] {W : Type} [NormedAddCommGroup W]
    [NormedSpace ℝ W] {u : (T → W) → ℂ} (hu : ContDiff ℝ ∞ u) (N : ℕ)
    (h : ∀ L : List (T × W), L.length = N → L.foldr (fun q g => dirD (Pi.single q.1 q.2) g) u = 0) :
    ∀ L : List (T → W), L.length = N → L.foldr dirD u = 0 := by
  intro L hL
  funext x
  rw [← List.ofFn_get L, foldr_ofFn_dirD hu]
  have hs : L.get = fun i => ∑ τ, Pi.single τ (L.get i τ) := funext fun i => (Finset.univ_sum_single (L.get i)).symm
  simp only [Pi.zero_apply]

  rw [hs, ContinuousMultilinearMap.map_sum]
  refine Finset.sum_eq_zero fun r _ => ?_
  have e1 : List.ofFn (fun i => (Pi.single (r i) (L.get i (r i)) : T → W)) =
      (List.ofFn fun i => (r i, L.get i (r i))).map (fun q => (Pi.single q.1 q.2 : T → W)) := by
    rw [List.map_ofFn]; rfl
  have h2 := congrFun (h (List.ofFn fun i => (r i, L.get i (r i))) (by simp [hL])) x
  rw [← List.foldr_map, ← e1, foldr_ofFn_dirD hu] at h2
  exact h2

end Generic

section Gauss

open Classical

variable {D : D7} (V : HSp D) {n : ℕ} (l : D.what₂.Tau → ℝ) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)

def gam (z : D.what₂.Tau → Fin V.rank → Fin n → ℂ) : ℂ := gauss V l s (fun τ => Matrix.of (z τ))

def expo (z : D.what₂.Tau → Fin V.rank → Fin n → ℂ) : ℂ :=
  -(2 * Real.pi) * ∑ τ, ((|l τ| : ℝ) : ℂ) *
    Matrix.trace ((Matrix.of (z τ))ᴴ * (gramAt D V τ * s τ) * Matrix.of (z τ))

theorem gam_eq (z : D.what₂.Tau → Fin V.rank → Fin n → ℂ) : gam V l s z = Complex.exp (expo V l s z) := rfl

theorem contDiff_expo : ContDiff ℝ ∞ (expo V l s (n := n)) := by
  unfold expo
  have hst : ContDiff ℝ ∞ (fun w : ℂ => star w) := Complex.conjCLE.contDiff
  simp only [Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.diag_apply]
  fun_prop

theorem trace_line {k : ℕ} (M : Matrix (Fin k) (Fin k) ℂ) (A B : Matrix (Fin k) (Fin n) ℂ) (t : ℝ) :
    Matrix.trace ((A + t • B)ᴴ * M * (A + t • B)) = Matrix.trace (Aᴴ * M * A) +
      (t : ℂ) * (Matrix.trace (Bᴴ * M * A) + Matrix.trace (Aᴴ * M * B)) + (t : ℂ) ^ 2 * Matrix.trace (Bᴴ * M * B) := by
  have ht : t • B = (t : ℂ) • B := by ext i j; simp [Complex.real_smul]
  rw [ht]
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal,
    Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul]
  ring

theorem hasDerivAt_expo (z : D.what₂.Tau → Fin V.rank → Fin n → ℂ) (τ : D.what₂.Tau) (X : Fin V.rank → Fin n → ℂ) :
    HasDerivAt (fun t : ℝ => expo V l s (z + t • (Pi.single τ X : D.what₂.Tau → Fin V.rank → Fin n → ℂ)))
      (-(2 * Real.pi) * (((|l τ| : ℝ) : ℂ) * (Matrix.trace ((Matrix.of X)ᴴ * (gramAt D V τ * s τ) * Matrix.of (z τ)) +
        Matrix.trace ((Matrix.of (z τ))ᴴ * (gramAt D V τ * s τ) * Matrix.of X)))) 0 := by
  set e : D.what₂.Tau → Fin V.rank → Fin n → ℂ := Pi.single τ X with he
  have hfun : (fun t : ℝ => expo V l s (z + t • e)) = fun t : ℝ => -(2 * Real.pi) * ∑ σ, ((|l σ| : ℝ) : ℂ) *
      (Matrix.trace ((Matrix.of (z σ))ᴴ * (gramAt D V σ * s σ) * Matrix.of (z σ)) +
        (t : ℂ) * (Matrix.trace ((Matrix.of (e σ))ᴴ * (gramAt D V σ * s σ) * Matrix.of (z σ)) +
          Matrix.trace ((Matrix.of (z σ))ᴴ * (gramAt D V σ * s σ) * Matrix.of (e σ))) +
        (t : ℂ) ^ 2 * Matrix.trace ((Matrix.of (e σ))ᴴ * (gramAt D V σ * s σ) * Matrix.of (e σ))) := by
    funext t
    unfold expo
    congr 1
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [← trace_line]
    rfl
  rw [hfun]
  refine HasDerivAt.const_mul _ ?_
  have hc : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := by simpa using (hasDerivAt_id (0:ℝ)).ofReal_comp
  have hs : ∀ σ ∈ (Finset.univ : Finset D.what₂.Tau), HasDerivAt (fun t : ℝ => ((|l σ| : ℝ) : ℂ) *
      (Matrix.trace ((Matrix.of (z σ))ᴴ * (gramAt D V σ * s σ) * Matrix.of (z σ)) +
        (t : ℂ) * (Matrix.trace ((Matrix.of (e σ))ᴴ * (gramAt D V σ * s σ) * Matrix.of (z σ)) +
          Matrix.trace ((Matrix.of (z σ))ᴴ * (gramAt D V σ * s σ) * Matrix.of (e σ))) +
        (t : ℂ) ^ 2 * Matrix.trace ((Matrix.of (e σ))ᴴ * (gramAt D V σ * s σ) * Matrix.of (e σ))))
      (((|l σ| : ℝ) : ℂ) * (Matrix.trace ((Matrix.of (e σ))ᴴ * (gramAt D V σ * s σ) * Matrix.of (z σ)) +
          Matrix.trace ((Matrix.of (z σ))ᴴ * (gramAt D V σ * s σ) * Matrix.of (e σ)))) 0 := by
    intro σ _
    set A := Matrix.trace ((Matrix.of (z σ))ᴴ * (gramAt D V σ * s σ) * Matrix.of (z σ))
    set B := Matrix.trace ((Matrix.of (e σ))ᴴ * (gramAt D V σ * s σ) * Matrix.of (z σ)) +
          Matrix.trace ((Matrix.of (z σ))ᴴ * (gramAt D V σ * s σ) * Matrix.of (e σ))
    set C := Matrix.trace ((Matrix.of (e σ))ᴴ * (gramAt D V σ * s σ) * Matrix.of (e σ))
    have h := (((hc.mul_const B).const_add A).add ((hc.pow 2).mul_const C)).const_mul (((|l σ| : ℝ) : ℂ))
    exact h.congr_deriv (by simp)
  have hsum := HasDerivAt.fun_sum hs
  refine hsum.congr_deriv ?_
  rw [Finset.sum_eq_single τ]
  · simp [he]
  · intro σ _ hσ; simp [he, Pi.single_eq_of_ne hσ]
  · simp

theorem hasDerivAt_gam (hM : ∀ τ, (gramAt D V τ * s τ)ᴴ = gramAt D V τ * s τ)
    (z : D.what₂.Tau → Fin V.rank → Fin n → ℂ) (τ : D.what₂.Tau) (X : Fin V.rank → Fin n → ℂ) :
    HasDerivAt (fun t : ℝ => gam V l s (z + t • (Pi.single τ X : D.what₂.Tau → Fin V.rank → Fin n → ℂ)))
      (-(linF V l s τ (Matrix.of X) (Matrix.of (z τ))) * gam V l s z) 0 := by
  have h : HasDerivAt (fun t : ℝ => gam V l s (z + t • (Pi.single τ X : D.what₂.Tau → Fin V.rank → Fin n → ℂ))) _ 0 :=
    (hasDerivAt_expo V l s z τ X).cexp
  refine h.congr_deriv ?_
  have hc : Matrix.trace ((Matrix.of (z τ))ᴴ * (gramAt D V τ * s τ) * Matrix.of X) =
      conj (Matrix.trace ((Matrix.of X)ᴴ * (gramAt D V τ * s τ) * Matrix.of (z τ))) := by
    rw [← Complex.star_def, ← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hM τ,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [hc, Complex.add_conj, zero_smul, add_zero, ← gam_eq]
  unfold linF
  push_cast
  ring

theorem annC_gam_mul (hM : ∀ τ, (gramAt D V τ * s τ)ᴴ = gramAt D V τ * s τ)
    {h : (D.what₂.Tau → Fin V.rank → Fin n → ℂ) → ℂ} (hh : Differentiable ℝ h) (τ : D.what₂.Tau)
    (X : Matrix (Fin V.rank) (Fin n) ℂ) :
    annC V l s τ X (fun z => gam V l s z * h z) =
      fun z => gam V l s z * dirD (Pi.single τ (fun i j => X i j) : D.what₂.Tau → Fin V.rank → Fin n → ℂ) h z := by
  funext z
  have h1 := hasDerivAt_gam V l s hM z τ (fun i j => X i j)
  have h2 := hasDerivAt_line (hh z) (Pi.single τ (fun i j => X i j) : D.what₂.Tau → Fin V.rank → Fin n → ℂ)
  show deriv (fun t : ℝ => gam V l s (z + t • (Pi.single τ (fun i j => X i j) : D.what₂.Tau → Fin V.rank → Fin n → ℂ)) *
      h (z + t • (Pi.single τ (fun i j => X i j) : D.what₂.Tau → Fin V.rank → Fin n → ℂ))) 0 +
      linF V l s τ X (Matrix.of (z τ)) * (gam V l s z * h z) = _
  rw [(h1.fun_mul h2).deriv, dirD_eq hh]
  have hX : Matrix.of (fun i j => X i j) = X := rfl
  simp only [zero_smul, add_zero, hX]
  ring

theorem foldr_annC (hM : ∀ τ, (gramAt D V τ * s τ)ᴴ = gramAt D V τ * s τ)
    {u : (D.what₂.Tau → Fin V.rank → Fin n → ℂ) → ℂ} (hu : ContDiff ℝ ∞ u) :
    ∀ L : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin n) ℂ),
      ContDiff ℝ ∞ (L.foldr (fun q g => dirD (Pi.single q.1 (fun i j => q.2 i j) : D.what₂.Tau → Fin V.rank → Fin n → ℂ) g) u) ∧
      L.foldr (fun q g => annC V l s q.1 q.2 g) (fun z => gam V l s z * u z) =
        fun z => gam V l s z *
          L.foldr (fun q g => dirD (Pi.single q.1 (fun i j => q.2 i j) : D.what₂.Tau → Fin V.rank → Fin n → ℂ) g) u z := by
  intro L
  induction L with
  | nil => exact ⟨hu, rfl⟩
  | cons q L ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨contDiff_dirD h1 _, ?_⟩
    simp only [List.foldr_cons]
    rw [h2]
    exact annC_gam_mul V l s hM (h1.differentiable (by simp)) q.1 q.2

end Gauss

end GlobalTheory.AnnPoly

namespace GlobalTheory.StdUnn

open GlobalTheory.AnnPoly

theorem exists_poly_mul_gauss_of_annC : ∀ (D : D7) (V : HSp D) (n : ℕ) (l : D.what₂.Tau → ℝ) (s : RealMat V), (∀ τ, IsCartanInv (gramAt D V τ) (s τ)) → ∀ (N : ℕ) (f : (D.what₂.Tau → Fin V.rank → Fin n → ℂ) → ℂ), ContDiff ℝ ∞ f → (∀ L : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin n) ℂ), L.length = N → L.foldr (fun q g => annC V l s q.1 q.2 g) f = 0) → ∃ p : MvPolynomial (D.what₂.Tau × Fin V.rank × Fin n × Bool) ℂ, ∀ z, f z = evalPoly p (fun τ => Matrix.of (z τ)) * gauss V l s (fun τ => Matrix.of (z τ)) := by
  classical
  intro D V n l s hs N f hf hL
  have hM : ∀ τ, (gramAt D V τ * s τ)ᴴ = gramAt D V τ * s τ := fun τ => (hs τ).2.2.1
  set u : (D.what₂.Tau → Fin V.rank → Fin n → ℂ) → ℂ := fun z => f z * Complex.exp (-(expo V l s z)) with hu_def
  have hu : ContDiff ℝ ∞ u := hf.mul (contDiff_expo V l s).neg.cexp
  have hfu : (fun z => gam V l s z * u z) = f := by
    funext z
    rw [hu_def, gam_eq, mul_left_comm, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one]
  have hU : ∀ L : List (D.what₂.Tau × (Fin V.rank → Fin n → ℂ)), L.length = N →
      L.foldr (fun q g => dirD (Pi.single q.1 q.2) g) u = 0 := by
    intro L hlen
    have h0 := hL (L.map fun q => (q.1, Matrix.of q.2)) (by simp [hlen])
    rw [← hfu, (foldr_annC V l s hM hu _).2, List.foldr_map] at h0
    funext z
    have h := congrFun h0 z
    exact (mul_eq_zero.1 h).resolve_left (Complex.exp_ne_zero _)
  have hall := foldr_dirD_eq_zero hu N hU
  let eL : (D.what₂.Tau × Fin V.rank × Fin n × Bool → ℝ) →ₗ[ℝ] (D.what₂.Tau → Fin V.rank → Fin n → ℂ) :=
    { toFun := fun x τ i j => (x (τ, i, j, false) : ℂ) + (x (τ, i, j, true) : ℂ) * Complex.I
      map_add' := by intro x y; funext τ i j; simp; ring
      map_smul' := by intro c x; funext τ i j; simp; ring }
  have hv : ContDiff ℝ ∞ (u ∘ eL) := hu.comp (LinearMap.toContinuousLinearMap eL).contDiff
  have htr : ∀ L : List (D.what₂.Tau × Fin V.rank × Fin n × Bool → ℝ),
      L.foldr dirD (u ∘ eL) = (L.map eL).foldr dirD u ∘ eL := by
    intro L
    induction L with
    | nil => rfl
    | cons y L ih =>
      funext x
      simp only [List.foldr_cons, List.map_cons, ih, dirD, Function.comp, map_add (f := _), map_smul]
  obtain ⟨p, hp⟩ := GlobalTheory.PolyOfDeriv.eq_eval_of_dirDeriv_vanish _ N (u ∘ eL) hv (fun L hlen => by
    have h := htr L
    rw [hall (L.map eL) (by simp [hlen])] at h
    exact h)
  let φ : D.what₂.Tau × Fin V.rank × Fin n × Bool → MvPolynomial (D.what₂.Tau × Fin V.rank × Fin n × Bool) ℂ := fun k =>
    if k.2.2.2 then MvPolynomial.C (2 * Complex.I)⁻¹ *
        (MvPolynomial.X (k.1, k.2.1, k.2.2.1, false) - MvPolynomial.X (k.1, k.2.1, k.2.2.1, true))
    else MvPolynomial.C (2 : ℂ)⁻¹ *
        (MvPolynomial.X (k.1, k.2.1, k.2.2.1, false) + MvPolynomial.X (k.1, k.2.1, k.2.2.1, true))
  refine ⟨MvPolynomial.bind₁ φ p, fun z => ?_⟩
  let r : D.what₂.Tau × Fin V.rank × Fin n × Bool → ℝ := fun k =>
    if k.2.2.2 then (z k.1 k.2.1 k.2.2.1).im else (z k.1 k.2.1 k.2.2.1).re
  have her : eL r = z := by
    funext τ i j
    exact Complex.re_add_im (z τ i j)
  have h1 : f z = u z * gam V l s z := by rw [← congrFun hfu z, mul_comm]
  have h2 : u z = MvPolynomial.eval (fun k => (r k : ℂ)) p := by rw [← hp r, Function.comp_apply, her]
  rw [h1, h2]
  congr 1
  unfold evalPoly
  rw [← MvPolynomial.aeval_eq_eval, ← MvPolynomial.aeval_eq_eval, MvPolynomial.aeval_bind₁]
  congr 2
  funext k
  obtain ⟨τ, i, j, b⟩ := k
  cases b
  · simp only [φ, r, Bool.false_eq_true, if_false, if_true, map_mul, map_add (f := _), MvPolynomial.aeval_C, MvPolynomial.aeval_X,
      Matrix.of_apply, Algebra.algebraMap_self, RingHom.id_apply, Complex.re_eq_add_conj]
    ring
  · simp only [φ, r, Bool.false_eq_true, if_false, if_true, map_mul, map_sub, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
      Matrix.of_apply, Algebra.algebraMap_self, RingHom.id_apply, Complex.im_eq_sub_conj]
    ring

end GlobalTheory.StdUnn

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsPolynomialMulGaussianOfAnnihilatedStatement

section

@[expose] public section

open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_polynomial_mul_gaussian_of_annihilated : ∀ (D : D7) (V : HSp D) (n : ℕ) (l : D.what₂.Tau → ℝ) (s : RealMat V), (∀ τ, IsCartanInv (gramAt D V τ) (s τ)) → ∀ (N : ℕ) (f : (D.what₂.Tau → Fin V.rank → Fin n → ℂ) → ℂ), ContDiff ℝ ∞ f → (∀ L : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin n) ℂ), L.length = N → L.foldr (fun q g => annC V l s q.1 q.2 g) f = 0) → ∃ p : MvPolynomial (D.what₂.Tau × Fin V.rank × Fin n × Bool) ℂ, ∀ z, f z = evalPoly p (fun τ => Matrix.of (z τ)) * gauss V l s (fun τ => Matrix.of (z τ)) := by
  first | exact @GlobalTheory.StdUnn.exists_poly_mul_gauss_of_annC | exact GlobalTheory.StdUnn.exists_poly_mul_gauss_of_annC | (intros; apply GlobalTheory.StdUnn.exists_poly_mul_gauss_of_annC <;> assumption)
end
end
