module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.FourierZeroN
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSchwartzPolyMulGauss
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
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.InvGroup
public import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.TypeStar

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.MatLApply

section

@[expose] public section

noncomputable section

open Filter Topology MvPolynomial Set
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.Glob.SchDH

variable {m n : ℕ}

def matLin (M : Matrix (Fin m) (Fin m) ℂ) : (Fin m → Fin n → ℂ) →ₗ[ℝ] (Fin m → Fin n → ℂ) where
  toFun y := fun a i => ∑ c, M a c * y c i
  map_add' y z := by funext a i; simp [mul_add, Finset.sum_add_distrib]
  map_smul' r y := by
    funext a i
    simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Complex.real_smul, Complex.real_smul]; ring

def matL (M : Matrix (Fin m) (Fin m) ℂ) : (Fin m → Fin n → ℂ) →L[ℝ] (Fin m → Fin n → ℂ) :=
  LinearMap.toContinuousLinearMap (matLin M)

theorem matL_apply (M : Matrix (Fin m) (Fin m) ℂ) (y : Fin m → Fin n → ℂ) (a : Fin m) (i : Fin n) :
    matL M y a i = ∑ c, M a c * y c i := rfl

theorem matL_mul (M N : Matrix (Fin m) (Fin m) ℂ) (y : Fin m → Fin n → ℂ) : matL (M * N) y = matL M (matL N y) := by
  funext a i
  simp only [matL_apply, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

theorem matL_one (y : Fin m → Fin n → ℂ) : matL (1 : Matrix (Fin m) (Fin m) ℂ) y = y := by
  funext a i
  simp [matL_apply, Matrix.one_apply]

theorem contDiff_A (X : Matrix (Fin m) (Fin m) ℂ) :
    ContDiff ℝ ∞ (fun t : ℝ => matL (n := n) (NormedSpace.exp ((t : ℂ) • X))) := by
  letI : NormedAddCommGroup (Matrix (Fin m) (Fin m) ℂ) := Matrix.linftyOpNormedAddCommGroup
  letI : NormedSpace ℝ (Matrix (Fin m) (Fin m) ℂ) := Matrix.linftyOpNormedSpace
  letI : NormedRing (Matrix (Fin m) (Fin m) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin m) (Fin m) ℂ) := Matrix.linftyOpNormedAlgebra
  let Lm : Matrix (Fin m) (Fin m) ℂ →ₗ[ℝ] ((Fin m → Fin n → ℂ) →L[ℝ] (Fin m → Fin n → ℂ)) :=
    { toFun := matL
      map_add' := fun M N => by ext y a i; simp [matL_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := fun r M => by
        ext y a i
        simp only [matL_apply, Matrix.smul_apply, RingHom.id_apply, ContinuousLinearMap.smul_apply, Pi.smul_apply,
          Finset.smul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Complex.real_smul, Complex.real_smul]; ring }
  have hexp : ContDiff ℝ ∞ (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) := by
    have e : (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) = NormedSpace.exp ∘ (fun t : ℝ => t • X) := by
      funext t; simp only [Function.comp_apply, Complex.coe_smul]
    rw [e]
    exact (contDiff_iff_contDiffAt.2 fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt).comp
      (contDiff_id.smul contDiff_const)
  exact (LinearMap.toContinuousLinearMap Lm).contDiff.comp hexp

theorem hasDerivAt_entry (X : Matrix (Fin m) (Fin m) ℂ) (a c : Fin m) :
    HasDerivAt (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X)) a c) (X a c) 0 := by
  letI : NormedAddCommGroup (Matrix (Fin m) (Fin m) ℂ) := Matrix.linftyOpNormedAddCommGroup
  letI : NormedSpace ℝ (Matrix (Fin m) (Fin m) ℂ) := Matrix.linftyOpNormedSpace
  letI : NormedRing (Matrix (Fin m) (Fin m) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin m) (Fin m) ℂ) := Matrix.linftyOpNormedAlgebra
  let ent : Matrix (Fin m) (Fin m) ℂ →ₗ[ℝ] ℂ :=
    { toFun := fun M => M a c, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have h := (hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ))
  have h2 := (LinearMap.toContinuousLinearMap ent).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
  have e : (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X)) a c) =
      (LinearMap.toContinuousLinearMap ent) ∘ (fun u : ℝ => NormedSpace.exp (u • X)) := by
    funext t; simp only [Function.comp_apply, Complex.coe_smul]; rfl
  have h3 : HasDerivAt (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X)) a c)
      ((LinearMap.toContinuousLinearMap ent) (NormedSpace.exp ((0 : ℝ) • X) * X)) 0 := by
    rw [e]; exact h2
  have h4 : (LinearMap.toContinuousLinearMap ent) (NormedSpace.exp ((0 : ℝ) • X) * X) = X a c := by
    rw [zero_smul, NormedSpace.exp_zero, one_mul]; rfl
  rw [h4] at h3
  exact h3

theorem exists_gs (c : ℝ) (hc : 0 < c) : ∃ g : SchwartzMap (Fin m → Fin n → ℂ) ℂ, ∀ u, g u = gs c u := by
  obtain ⟨g0, hg0⟩ := GlobalTheory.CompanionTheory.PolyGaussSchwartz.exists_gauss (m := m) (n := n)
  set s : ℝ := Real.sqrt (c / (2 * Real.pi)) with hs
  have hs0 : s ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
  let L : (Fin m → Fin n → ℂ) ≃L[ℝ] (Fin m → Fin n → ℂ) :=
    (LinearEquiv.smulOfNeZero ℝ (Fin m → Fin n → ℂ) s hs0).toContinuousLinearEquiv
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L g0, fun u => ?_⟩
  rw [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, hg0]
  have key : 2 * Real.pi * ∑ a, ∑ i, ‖(L u) a i‖ ^ 2 = c * ∑ a, ∑ i, ‖u a i‖ ^ 2 := by
    have h1 : ∀ a i, ‖(L u) a i‖ ^ 2 = s ^ 2 * ‖u a i‖ ^ 2 := fun a i => by
      change ‖(s • u) a i‖ ^ 2 = _
      rw [Pi.smul_apply, Pi.smul_apply, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    simp only [h1, ← Finset.mul_sum]
    rw [hs, Real.sq_sqrt (by positivity)]
    field_simp
  unfold gs
  rw [key]

theorem exists_fP (c : ℝ) (hc : 0 < c) (P : PX m n) :
    ∃ φ : SchwartzMap (Fin m → Fin n → ℂ) ℂ, ∀ u, φ u = fP c P u := by
  obtain ⟨g, hg⟩ := exists_gs (m := m) (n := n) c hc
  refine ⟨SchwartzMap.smulLeftCLM ℂ (fun u => MvPolynomial.eval (fun k => GlobalTheory.CompanionTheory.PolyGaussSchwartz.coord k u) P) g,
    fun u => ?_⟩
  rw [SchwartzMap.smulLeftCLM_apply_apply (GlobalTheory.CompanionTheory.PolyGaussSchwartz.eval_temperate P), hg, smul_eq_mul]
  rfl

end PositivityTheory.Rg.Sw.Glob.SchDH
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DerivationOfQuadraticForm

section

@[expose] public section

noncomputable section

open Filter Topology MvPolynomial

namespace PositivityTheory.Rg.Sw.Glob.SchDH

variable {m n : ℕ}

def Dv (X : Matrix (Fin m) (Fin m) ℂ) : Derivation ℂ (PX m n) (PX m n) :=
  MvPolynomial.mkDerivation ℂ (fun k : Fin m × Fin n × Bool => xyP X k.1 k.2.1 k.2.2)

theorem Dv_X (X : Matrix (Fin m) (Fin m) ℂ) (k : Fin m × Fin n × Bool) :
    Dv X (MvPolynomial.X k : PX m n) = xyP X k.1 k.2.1 k.2.2 :=
  MvPolynomial.mkDerivation_X _ _ _

theorem Dv_eq (X : Matrix (Fin m) (Fin m) ℂ) (P : PX m n) :
    Dv X P = ∑ k : Fin m × Fin n × Bool, xyP X k.1 k.2.1 k.2.2 * pderiv k P := by
  let D₂ : Derivation ℂ (PX m n) (PX m n) :=
    ∑ k : Fin m × Fin n × Bool, xyP X k.1 k.2.1 k.2.2 • pderiv k
  have hs : ∀ Q : PX m n, D₂ Q = ∑ k : Fin m × Fin n × Bool, xyP X k.1 k.2.1 k.2.2 * pderiv k Q := by
    intro Q
    show (Derivation.coeFnAddMonoidHom (R := ℂ) (A := PX m n) (M := PX m n)
      (∑ k : Fin m × Fin n × Bool, xyP X k.1 k.2.1 k.2.2 • (pderiv k : Derivation ℂ (PX m n) (PX m n)))) Q = _

    rw [map_sum, Finset.sum_apply]
    simp only [Derivation.coeFnAddMonoidHom_apply, Derivation.smul_apply, smul_eq_mul]
  have h : Dv X P = D₂ P := by
    refine MvPolynomial.derivation_eq_of_forall_mem_vars (fun i _ => ?_)
    rw [hs, Dv_X]
    simp [pderiv_X, Pi.single_apply]
  rw [h, hs]

def Q2 (m n : ℕ) : PX m n := ∑ a, ∑ i, MvPolynomial.X (a, i, false) * MvPolynomial.X (a, i, true)

theorem derivation_quadraticForm_eq_sum (X : Matrix (Fin m) (Fin m) ℂ) :
    Dv X (Q2 m n) = ∑ a, ∑ i, (MvPolynomial.X (a, i, false) * xyP X a i true + MvPolynomial.X (a, i, true) * xyP X a i false) := by

  simp only [Q2, map_sum, Derivation.leibniz, Dv_X, smul_eq_mul]

theorem vfX_eq_Dv (c : ℝ) (X : Matrix (Fin m) (Fin m) ℂ) (P : PX m n) :
    vfX c X P = Dv X P - C (c : ℂ) * Dv X (Q2 m n) * P := by
  rw [Dv_eq, derivation_quadraticForm_eq_sum, vfX]
  simp only [Fintype.sum_prod_type]
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Fintype.sum_bool]
  ring

theorem eval_xyP (X : Matrix (Fin m) (Fin m) ℂ) (u : Fin m → Fin n → ℂ) (a : Fin m) (i : Fin n) (b : Bool) :
    MvPolynomial.eval (fun k => GlobalTheory.CompanionTheory.PolyGaussSchwartz.coord k u) (xyP X a i b) =
      if b then star (matL X u a i) else matL X u a i := by
  cases b <;> simp [xyP, GlobalTheory.CompanionTheory.PolyGaussSchwartz.coord, matL_apply, star_sum, star_mul']

theorem gs_eq (c : ℝ) (u : Fin m → Fin n → ℂ) :
    gs c u = Complex.exp (-(c : ℂ) * MvPolynomial.eval (fun k => GlobalTheory.CompanionTheory.PolyGaussSchwartz.coord k u) (Q2 m n)) := by
  rw [gs]
  congr 1

  simp only [Q2, map_sum, map_mul, MvPolynomial.eval_X, GlobalTheory.CompanionTheory.PolyGaussSchwartz.coord]
  push_cast
  simp [Complex.mul_conj, Complex.normSq_eq_norm_sq, Finset.mul_sum]

private theorem hasDerivAt_clm_comp_of_tendsto_slope {σ : Type*} [Fintype σ] (g : ℝ → σ → ℂ) (g' : σ → ℂ)
    (hg : ∀ k, HasDerivAt (fun t => g t k) (g' k) 0) (Q : MvPolynomial σ ℂ) :
    HasDerivAt (fun t => MvPolynomial.eval (g t) Q)
      (∑ k, g' k * MvPolynomial.eval (g 0) (pderiv k Q)) 0 := by
  classical
  refine MvPolynomial.induction_on
    (motive := fun Q => HasDerivAt (fun t => MvPolynomial.eval (g t) Q)
      (∑ k, g' k * MvPolynomial.eval (g 0) (pderiv k Q)) 0) Q ?_ ?_ ?_
  · intro a
    simpa using hasDerivAt_const (0 : ℝ) a
  · intro p q hp hq
    refine ((hp.fun_add hq).congr_deriv ?_).congr_of_eventuallyEq ?_
    · simp [mul_add, Finset.sum_add_distrib]
    · exact Filter.Eventually.of_forall (fun t => by simp)
  · intro p k hp
    refine ((hp.fun_mul (hg k)).congr_deriv ?_).congr_of_eventuallyEq ?_
    · simp [Derivation.leibniz, pderiv_X, Pi.single_apply, mul_add, Finset.sum_add_distrib,
        apply_ite, Finset.sum_ite_eq]
      rw [add_comm]
      congr 1
      · ring
      · rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun _ _ => by ring)
    · exact Filter.Eventually.of_forall (fun t => by simp)

theorem hasDerivAt_curve (c : ℝ) (X : Matrix (Fin m) (Fin m) ℂ) (P : PX m n) (x : Fin m → Fin n → ℂ) :
    HasDerivAt (fun t : ℝ => fP c P (matL (NormedSpace.exp ((t : ℂ) • X)) x)) (fP c (vfX c X P) x) 0 := by
  set u : ℝ → (Fin m → Fin n → ℂ) := fun t => matL (NormedSpace.exp ((t : ℂ) • X)) x with hu
  have hu0 : u 0 = x := by simp [hu, matL_one]
  clear_value u
  rw [show (fun t : ℝ => fP c P (matL (NormedSpace.exp ((t : ℂ) • X)) x)) =
    fun t => fP c P (u t) by rw [hu]]
  let e : (Fin m → Fin n → ℂ) → Fin m × Fin n × Bool → ℂ :=
    fun v k => GlobalTheory.CompanionTheory.PolyGaussSchwartz.coord k v
  have hg : ∀ k, HasDerivAt (fun t => e (u t) k) (MvPolynomial.eval (e x) (xyP X k.1 k.2.1 k.2.2)) 0 := by
    rintro ⟨a, i, b⟩
    have hlin : HasDerivAt (fun t => u t a i) (matL X x a i) 0 := by
      have hs := HasDerivAt.fun_sum (u := Finset.univ)
        (fun c (_ : c ∈ Finset.univ) => (hasDerivAt_entry X a c).mul_const (x c i))
      simpa only [hu, matL_apply] using hs
    rw [eval_xyP]
    cases b
    · simpa [e, GlobalTheory.CompanionTheory.PolyGaussSchwartz.coord] using hlin
    · simpa [e, GlobalTheory.CompanionTheory.PolyGaussSchwartz.coord] using hlin.star
  have hf : (fun t : ℝ => fP c P (u t)) = fun t => MvPolynomial.eval (e (u t)) P *
      Complex.exp (-(c : ℂ) * MvPolynomial.eval (e (u t)) (Q2 m n)) := by
    funext t
    rw [fP, gs_eq]
    rfl
  have hx : fP c (vfX c X P) x = MvPolynomial.eval (e x) (vfX c X P) *
      Complex.exp (-(c : ℂ) * MvPolynomial.eval (e x) (Q2 m n)) := by
    rw [fP, gs_eq]
    rfl
  rw [hf, hx, vfX_eq_Dv, Dv_eq X P, Dv_eq X (Q2 m n)]
  have hP := hasDerivAt_clm_comp_of_tendsto_slope (fun t => e (u t)) _ hg P
  have hQ := hasDerivAt_clm_comp_of_tendsto_slope (fun t => e (u t)) _ hg (Q2 m n)
  have H := hP.fun_mul ((hQ.const_mul (-(c : ℂ))).cexp)
  rw [hu0] at H
  refine H.congr_deriv ?_

  simp only [map_sub, map_mul, map_sum, MvPolynomial.eval_C]
  ring

end PositivityTheory.Rg.Sw.Glob.SchDH
end
end
end
