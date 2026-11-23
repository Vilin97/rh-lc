module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.DensDefs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.Tactic.TypeStar
public import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.ContinuousEvX
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.ContinuousEvXI
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.DerivFA

section

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace PositivityTheory.Rg.Sw.WR.D

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR

variable {m n : ℕ}

theorem continuous_evXD (P : PX m n) : Continuous (evX P) := by
  unfold evX
  have h : Continuous fun x : Fin m → Fin n → ℂ =>
      (fun k : Fin m × Fin n × Bool => if k.2.2 then star (x k.1 k.2.1) else x k.1 k.2.1) := by
    refine continuous_pi fun k => ?_
    rcases k with ⟨a, i, b⟩
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact (continuous_apply i).comp (continuous_apply a)
    · simp only [↓reduceIte]
      exact continuous_star.comp ((continuous_apply i).comp (continuous_apply a))
  exact (MvPolynomial.continuous_eval P).comp h

theorem continuous_gsD (c : ℝ) : Continuous (gs (m := m) (n := n) c) := by
  have h : Continuous fun x : Fin m → Fin n → ℂ => (c * ∑ a, ∑ i, ‖x a i‖ ^ 2 : ℝ) := by fun_prop
  exact Complex.continuous_exp.comp (Complex.continuous_ofReal.comp h).neg

theorem continuous_ip_right (y : E n) : Continuous (fun q : E n => ip y q) := by
  unfold ip; fun_prop

theorem norm_exp_I_mul (t r : ℝ) : ‖Complex.exp (Complex.I * t * r)‖ = 1 := by
  have : Complex.I * (t : ℂ) * (r : ℂ) = ((t * r : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [this]; exact Complex.norm_exp_ofReal_mul_I _

def pr (a b : Fin n) : E n →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) b).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => Fin n → ℝ) a)

theorem pr_apply (a b : Fin n) (w : E n) : pr a b w = w a b := rfl

def Lc (q : E n) : E n →L[ℝ] ℂ := ∑ a, ∑ b, q a b • (Complex.ofRealCLM.comp (pr a b))

theorem Lc_apply (q w : E n) : Lc q w = ((ip w q : ℝ) : ℂ) := by
  simp only [Lc, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    Complex.ofRealCLM_apply, pr_apply, ip, Complex.ofReal_sum, Complex.ofReal_mul, Complex.real_smul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem norm_Lc_le (q : E n) : ‖Lc q‖ ≤ ∑ a, ∑ b, |q a b| := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
  rw [Lc_apply, Complex.norm_real, Real.norm_eq_abs, ip, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ => ?_)
  rw [abs_mul, mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have h1 : ‖w a b‖ ≤ ‖w a‖ := norm_le_pi_norm (w a) b
  have h2 : ‖w a‖ ≤ ‖w‖ := norm_le_pi_norm w a
  rw [← Real.norm_eq_abs]; exact h1.trans h2

theorem continuous_Lc_comp {X : Type*} [TopologicalSpace X] {f : X → E n} (hf : Continuous f) :
    Continuous fun x => Lc (f x) := by
  unfold Lc
  refine continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ => ?_
  exact (((continuous_apply b).comp (continuous_apply a)).comp hf).smul
    (continuous_const : Continuous fun _ : X => Complex.ofRealCLM.comp (pr a b))

theorem abs_qX_le (ε : Fin m → Bool) (x : Fin m → Fin n → ℂ) (a b : Fin n) :
    |qX ε x a b| ≤ 2 * ‖evX (Qp ε a b) x‖ := by
  have h : qX ε x a b = (gramX ε x a b).re + (gramX ε x a b).im := rfl
  rw [h]
  have h1 := Complex.abs_re_le_norm (gramX ε x a b)
  have h2 := Complex.abs_im_le_norm (gramX ε x a b)
  have : gramX ε x a b = evX (Qp ε a b) x := rfl
  rw [← this]
  linarith [abs_add_le (gramX ε x a b).re (gramX ε x a b).im]

variable (ε : Fin m → Bool) (c t : ℝ)

def Fi (P : PX m n) (y : E n) (x : Fin m → Fin n → ℂ) : ℂ :=
  evX P x * gs c x * Complex.exp (Complex.I * t * ip y (qX ε x))

def Fd (P : PX m n) (y : E n) (x : Fin m → Fin n → ℂ) : E n →L[ℝ] ℂ :=
  (evX P x * gs c x * Complex.exp (Complex.I * t * ip y (qX ε x)) * (Complex.I * t)) • Lc (qX ε x)

variable {ε c t}

theorem continuous_Fi (hq : Continuous (qX (n := n) ε)) (P : PX m n) (y : E n) : Continuous (Fi ε c t P y) := by
  unfold Fi
  refine ((continuous_evXD P).mul (continuous_gsD c)).mul (Complex.continuous_exp.comp ?_)
  exact continuous_const.mul (Complex.continuous_ofReal.comp ((continuous_ip_right y).comp hq))

theorem continuous_Fd (hq : Continuous (qX (n := n) ε)) (P : PX m n) (y : E n) : Continuous (Fd ε c t P y) := by
  unfold Fd
  have h1 : Continuous fun x => evX P x * gs c x * Complex.exp (Complex.I * t * ip y (qX ε x)) * (Complex.I * t) :=
    (continuous_Fi hq P y).mul continuous_const
  exact h1.smul (continuous_Lc_comp hq)

theorem norm_Fi (P : PX m n) (y : E n) (x : Fin m → Fin n → ℂ) : ‖Fi ε c t P y x‖ = ‖evX P x * gs c x‖ := by
  unfold Fi; rw [norm_mul, norm_exp_I_mul, mul_one]

theorem integrable_Fi (hI : IntG) (hq : Continuous (qX (n := n) ε)) (hc : 0 < c) (P : PX m n) (y : E n) :
    Integrable (Fi ε c t P y) :=
  (hI m n c hc P).mono (continuous_Fi hq P y).aestronglyMeasurable
    (ae_of_all _ fun x => (norm_Fi P y x).le)

def bnd (ε : Fin m → Bool) (c t : ℝ) (P : PX m n) (x : Fin m → Fin n → ℂ) : ℝ :=
  |t| * ∑ a, ∑ b, 2 * ‖evX (Qp ε a b * P) x * gs c x‖

theorem integrable_bnd (hI : IntG) (hc : 0 < c) (P : PX m n) : Integrable (bnd ε c t P) := by
  unfold bnd
  refine Integrable.const_mul ?_ _
  refine integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => ?_
  exact ((hI m n c hc (Qp ε a b * P)).norm).const_mul 2

theorem norm_Fd_le (P : PX m n) (y : E n) (x : Fin m → Fin n → ℂ) : ‖Fd ε c t P y x‖ ≤ bnd ε c t P x := by
  have e0 : ‖Fd ε c t P y x‖ = ‖evX P x * gs c x‖ * |t| * ‖Lc (qX ε x)‖ := by
    simp only [Fd, norm_smul, norm_mul, norm_exp_I_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      one_mul, mul_one]
  rw [e0]
  unfold bnd
  calc ‖evX P x * gs c x‖ * |t| * ‖Lc (qX ε x)‖
      ≤ ‖evX P x * gs c x‖ * |t| * ∑ a, ∑ b, |qX ε x a b| :=
        mul_le_mul_of_nonneg_left (norm_Lc_le _) (by positivity)
    _ = |t| * ∑ a, ∑ b, ‖evX P x * gs c x‖ * |qX ε x a b| := by
        simp only [Finset.mul_sum]; refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_; ring
    _ ≤ |t| * ∑ a, ∑ b, 2 * ‖evX (Qp ε a b * P) x * gs c x‖ := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_) (abs_nonneg _)
        have h := abs_qX_le ε x a b
        have e : evX (Qp ε a b * P) x * gs c x = evX (Qp ε a b) x * (evX P x * gs c x) := by
          simp only [evX, map_mul]; ring
        rw [e]
        simp only [norm_mul]
        have hn : 0 ≤ ‖evX P x‖ * ‖gs c x‖ := by positivity
        nlinarith [mul_le_mul_of_nonneg_left h hn]

theorem hasFDerivAt_Fi (P : PX m n) (y : E n) (x : Fin m → Fin n → ℂ) :
    HasFDerivAt (fun y => Fi ε c t P y x) (Fd ε c t P y x) y := by
  have h1 : HasFDerivAt (fun y : E n => ((ip y (qX ε x) : ℝ) : ℂ)) (Lc (qX ε x)) y := by
    have : (fun y : E n => ((ip y (qX ε x) : ℝ) : ℂ)) = fun y => Lc (qX ε x) y :=
      funext fun y => (Lc_apply _ y).symm
    rw [this]; exact (Lc (qX ε x)).hasFDerivAt
  have h2 := (h1.const_mul (Complex.I * t)).cexp.const_mul (evX P x * gs c x)
  have e : (evX P x * gs c x) • Complex.exp (Complex.I * t * ((ip y (qX ε x) : ℝ) : ℂ)) • (Complex.I * t) • Lc (qX ε x)
      = Fd ε c t P y x := by
    rw [Fd, smul_smul, smul_smul, mul_assoc (evX P x * gs c x)]
  exact h2.congr_fderiv e

theorem hasFDerivAt_FP (hI : IntG) (hq : Continuous (qX (n := n) ε)) (hc : 0 < c) (P : PX m n) (y : E n) :
    HasFDerivAt (FP ε c t P) (∫ x, Fd ε c t P y x) y := by
  have := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume) (F := fun y x => Fi ε c t P y x)
    (F' := fun y x => Fd ε c t P y x) (x₀ := y) (bound := bnd ε c t P) (s := Set.univ) Filter.univ_mem
    (Eventually.of_forall fun y' => (continuous_Fi hq P y').aestronglyMeasurable) (integrable_Fi hI hq hc P y)
    (continuous_Fd hq P y).aestronglyMeasurable (ae_of_all _ fun x y' _ => norm_Fd_le P y' x)
    (integrable_bnd hI hc P) (ae_of_all _ fun x y' _ => hasFDerivAt_Fi P y' x)
  exact this

theorem integrable_Fd (hI : IntG) (hq : Continuous (qX (n := n) ε)) (hc : 0 < c) (P : PX m n) (y : E n) :
    Integrable (Fd ε c t P y) :=
  (integrable_bnd hI hc P).mono' (continuous_Fd hq P y).aestronglyMeasurable (ae_of_all _ fun x => norm_Fd_le P y x)

end PositivityTheory.Rg.Sw.WR.D
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.DerivF

section

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace PositivityTheory.Rg.Sw.WR.D

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR

variable {m n : ℕ} {ε : Fin m → Bool} {c t : ℝ}

theorem FP_eq_integral_Fi (P : PX m n) (y : E n) : FP ε c t P y = ∫ x, Fi ε c t P y x := rfl

theorem fderiv_FP_apply (hI : IntG) (hq : Continuous (qX (n := n) ε)) (hc : 0 < c) (P : PX m n) (y w : E n) :
    fderiv ℝ (FP ε c t P) y w = ∫ x, Fi ε c t P y x * (Complex.I * t) * ((ip w (qX ε x) : ℝ) : ℂ) := by
  rw [(hasFDerivAt_FP hI hq hc P y).fderiv, ContinuousLinearMap.integral_apply (integrable_Fd hI hq hc P y)]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [Fd, ContinuousLinearMap.smul_apply, Lc_apply, smul_eq_mul, Fi]

theorem integrable_Fi_mul (hI : IntG) (hq : Continuous (qX (n := n) ε)) (hc : 0 < c) (P : PX m n) (y w : E n) :
    Integrable fun x => Fi ε c t P y x * (Complex.I * t) * ((ip w (qX ε x) : ℝ) : ℂ) := by
  have h := (integrable_Fd (t := t) hI hq hc P y).apply_continuousLinearMap w
  refine h.congr (ae_of_all _ fun x => ?_)
  simp only [Fd, ContinuousLinearMap.smul_apply, Lc_apply, smul_eq_mul, Fi]

theorem dirC_FP (hI : IntG) (hq : Continuous (qX (n := n) ε)) (hc : 0 < c) (P : PX m n)
    (v : Fin n → Fin n → ℂ) (y : E n) :
    dirC (FP ε c t P) v y =
      ∫ x, Fi ε c t P y x * (Complex.I * t) * ∑ a, ∑ b, v a b * (qX ε x a b : ℂ) := by
  unfold dirC
  rw [fderiv_FP_apply hI hq hc, fderiv_FP_apply hI hq hc, ← integral_const_mul,
    ← integral_add (integrable_Fi_mul hI hq hc P y _) ((integrable_Fi_mul hI hq hc P y _).const_mul _)]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  have e : ∀ a b, v a b = ((v a b).re : ℂ) + Complex.I * ((v a b).im : ℂ) := fun a b => by
    rw [mul_comm]; exact (Complex.re_add_im (v a b)).symm
  simp only [ip, Complex.ofReal_sum, Complex.ofReal_mul]
  conv_rhs => rw [show (∑ a, ∑ b, v a b * (qX ε x a b : ℂ)) =
    ∑ a, ∑ b, (((v a b).re : ℂ) + Complex.I * ((v a b).im : ℂ)) * (qX ε x a b : ℂ) from
      Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by rw [← e]]
  simp only [add_mul, Finset.sum_add_distrib, mul_add, Finset.mul_sum]
  ring_nf

theorem sum_ite_pair (k l : Fin n) (α : ℂ) (f : Fin n → Fin n → ℂ) :
    ∑ a, ∑ b, (if a = k ∧ b = l then α else 0) * f a b = α * f k l := by
  rw [Finset.sum_eq_single k, Finset.sum_eq_single l]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro a _ ha; simp [ha]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem sum_vkl (hA : AlgA) (k l : Fin n) (x : Fin m → Fin n → ℂ) :
    ∑ a, ∑ b, vkl k l a b * (qX ε x a b : ℂ) = evX (Qp ε k l) x := by
  have h := congrFun (congrFun ((hA m n ε).2.1 x) k) l
  have g : gramX ε x k l = evX (Qp ε k l) x := rfl
  rw [← g, ← h]
  simp only [vkl, add_mul, Finset.sum_add_distrib]
  rw [sum_ite_pair k l _ (fun a b => (qX ε x a b : ℂ)), sum_ite_pair l k _ (fun a b => (qX ε x a b : ℂ))]
  simp only [herm]
  push_cast
  ring

theorem Dkl_FP (hI : IntG) (hA : AlgA) (hc : 0 < c) (P : PX m n) (k l : Fin n) :
    Dkl k l (FP ε c t P) = FP ε c t (MvPolynomial.C (Complex.I * t) * Qp ε k l * P) := by
  have hq := (hA m n ε).2.2.2.2
  funext y
  unfold Dkl
  rw [dirC_FP hI hq hc]
  unfold FP
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  dsimp only
  rw [sum_vkl hA]
  simp only [Fi, evX, map_mul, MvPolynomial.eval_C]
  ring

theorem FP_add (hI : IntG) (hA : AlgA) (hc : 0 < c) (P Q : PX m n) :
    FP ε c t (P + Q) = FP ε c t P + FP ε c t Q := by
  have hq := (hA m n ε).2.2.2.2
  funext y
  simp only [Pi.add_apply]
  rw [FP_eq_integral_Fi, FP_eq_integral_Fi, FP_eq_integral_Fi,
    ← integral_add (integrable_Fi hI hq hc P y) (integrable_Fi hI hq hc Q y)]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [Fi, evX, map_add (f := _)]; ring

theorem FP_C_mul (a : ℂ) (P : PX m n) :
    FP ε c t (MvPolynomial.C a * P) = a • FP ε c t P := by
  funext y
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [FP_eq_integral_Fi, FP_eq_integral_Fi, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [Fi, evX, map_mul, MvPolynomial.eval_C]; ring

theorem FP_sum (hI : IntG) (hA : AlgA) (hc : 0 < c) {ι : Type*} (s : Finset ι) (f : ι → PX m n) :
    FP ε c t (∑ i ∈ s, f i) = ∑ i ∈ s, FP ε c t (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    funext y
    simp only [Finset.sum_empty, Finset.sum_apply, Pi.zero_apply]
    rw [FP_eq_integral_Fi]
    simp [Fi, evX]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, FP_add hI hA hc, ih]

theorem foldr_FP (hI : IntG) (hA : AlgA) (hc : 0 < c) (σ : Equiv.Perm (Fin n)) (L : List (Fin n)) (P : PX m n) :
    L.foldr (fun k g => Dkl k (σ k) g) (FP ε c t P) =
      FP ε c t ((L.map fun k => MvPolynomial.C (Complex.I * t) * Qp ε k (σ k)).prod * P) := by
  induction L with
  | nil => simp
  | cons k L ih =>
    rw [List.foldr_cons, ih, Dkl_FP hI hA hc, List.map_cons, List.prod_cons]
    congr 1; ring

theorem sum_perm_eq_det :
    ∑ σ : Equiv.Perm (Fin n), MvPolynomial.C ((Equiv.Perm.sign σ : ℤ) : ℂ) *
      (((List.finRange n).map fun k => MvPolynomial.C (Complex.I * t) * Qp ε k (σ k)).prod)
      = MvPolynomial.C ((Complex.I * t) ^ n) * detQ ε := by
  have hprod : ∀ σ : Equiv.Perm (Fin n),
      ((List.finRange n).map fun k => MvPolynomial.C (Complex.I * t) * Qp ε k (σ k)).prod =
        MvPolynomial.C ((Complex.I * t) ^ n) * ∏ k, Qp ε k (σ k) := by
    intro σ
    rw [← Fin.prod_univ_def, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      map_pow]
  simp only [hprod]
  rw [detQ, ← Matrix.det_transpose, Matrix.det_apply', Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [Matrix.transpose_apply, Matrix.of_apply]
  rw [show (MvPolynomial.C (((Equiv.Perm.sign σ : ℤ) : ℂ)) : PX m n) = (((Equiv.Perm.sign σ : ℤ) : PX m n)) by
    simp]
  ring

theorem Delta_FP (hI : IntG) (hA : AlgA) (hc : 0 < c) (P : PX m n) :
    Delta (FP ε c t P) = FP ε c t (MvPolynomial.C ((Complex.I * t) ^ n) * detQ ε * P) := by
  unfold Delta
  simp only [foldr_FP hI hA hc]
  rw [← sum_perm_eq_det (ε := ε) (t := t), Finset.sum_mul, FP_sum hI hA hc]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [mul_assoc, FP_C_mul]

theorem derivF_of (hI : IntG) (hA : AlgA) : DerivF := by
  intro m n ε c t hc P N
  have hq := (hA m n ε).2.2.2.2
  refine ⟨continuous_iff_continuousAt.2 fun y => (hasFDerivAt_FP hI hq hc P y).continuousAt, ?_⟩
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Function.iterate_succ_apply', ih, Delta_FP hI hA hc, pow_succ]
    congr 1; ring

theorem derivF : DerivF := derivF_of intG algA

end PositivityTheory.Rg.Sw.WR.D
end
end
end
