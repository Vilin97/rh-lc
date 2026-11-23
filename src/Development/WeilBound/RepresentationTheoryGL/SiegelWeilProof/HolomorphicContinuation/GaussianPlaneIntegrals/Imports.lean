module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GaussianPlaneIntegrals.AssemblyAlt
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GaussianPlaneIntegrals.ContinuousPhi
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GaussianPlaneIntegrals.IntegralHkDiag
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
public import Mathlib.MeasureTheory.Integral.Pi
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Matrix.PosDef
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Topology.Algebra.MvPolynomial
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.MvPolynomial.Funext

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GaussianPlaneIntegrals.IntegralMonSelf

section

@[expose] public section

noncomputable section

open MeasureTheory MvPolynomial Module
open scoped ComplexConjugate

namespace PositivityTheory.Rg.Sw.FFTSteps.PosProof

variable {ι A B : Type} [Fintype ι] [DecidableEq ι] [Fintype A] [Fintype B]

theorem gw_prod (z : Sg ι A B → ℂ) : Complex.exp (-(∑ s, ‖z s‖ ^ 2 : ℝ)) = ∏ s, e1 (z s) := by
  simp only [e1]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  simp [Finset.sum_neg_distrib]

def mon (m : Sg ι A B →₀ ℕ) (z : Sg ι A B → ℂ) : ℂ := ∏ s, z s ^ m s

theorem mon_prod (m m' : Sg ι A B →₀ ℕ) (z : Sg ι A B → ℂ) :
    mon m z * star (mon m' z) * Complex.exp (-(∑ s, ‖z s‖ ^ 2 : ℝ)) = ∏ s, hk (m s) (m' s) (z s) := by
  rw [gw_prod]
  simp only [mon, hk, Complex.star_def, map_prod, map_pow, Finset.prod_mul_distrib]

theorem integrable_mon (m m' : Sg ι A B →₀ ℕ) :
    Integrable (fun z : Sg ι A B → ℂ => mon m z * star (mon m' z) * Complex.exp (-(∑ s, ‖z s‖ ^ 2 : ℝ))) := by
  simp_rw [mon_prod]
  have := Integrable.fintype_prod (f := fun s => hk (m s) (m' s)) (μ := fun _ => (volume : Measure ℂ))
    (fun s => integrable_hk _ _)
  rwa [← volume_pi] at this

theorem integral_mon (m m' : Sg ι A B →₀ ℕ) :
    ∫ z : Sg ι A B → ℂ, mon m z * star (mon m' z) * Complex.exp (-(∑ s, ‖z s‖ ^ 2 : ℝ)) =
      ∏ s, ∫ w, hk (m s) (m' s) w := by
  simp_rw [mon_prod]
  exact integral_fintype_prod_volume_eq_prod (fun s w => hk (m s) (m' s) w)

theorem integral_mon_ne (m m' : Sg ι A B →₀ ℕ) (h : m ≠ m') :
    ∫ z : Sg ι A B → ℂ, mon m z * star (mon m' z) * Complex.exp (-(∑ s, ‖z s‖ ^ 2 : ℝ)) = 0 := by
  rw [integral_mon]
  obtain ⟨s, hs⟩ : ∃ s, m s ≠ m' s := by
    by_contra hc
    push Not at hc
    exact h (Finsupp.ext hc)
  exact Finset.prod_eq_zero (Finset.mem_univ s) (integral_hk_ne _ _ hs)

theorem integral_mon_self (m : Sg ι A B →₀ ℕ) :
    ∫ z : Sg ι A B → ℂ, mon m z * star (mon m z) * Complex.exp (-(∑ s, ‖z s‖ ^ 2 : ℝ)) =
      ((∏ s, jr (m s) : ℝ) : ℂ) := by
  rw [integral_mon]
  push_cast
  exact Finset.prod_congr rfl fun s _ => integral_hk_diag _

def kap (d : ι → ℝ) : Sg ι A B → ℝ := Sum.elim (fun _ => 1) (fun y => d y.1)

def lam (d : ι → ℝ) (m : Sg ι A B →₀ ℕ) : ℝ := ∏ s, kap d s ^ m s

theorem Phi_diag (d : ι → ℝ) (z : Sg ι A B → ℂ) :
    Phi (Matrix.diagonal fun i => (d i : ℂ)) z = fun s => (kap d s : ℂ) * z s := by
  funext s
  rcases s with x | ⟨i, b⟩
  · simp [Phi, kap]
  · simp [Phi, kap, Matrix.diagonal_apply]

theorem gip_diag (d : ι → ℝ) (g : PV ι A B) :
    gip (sub 1 (Matrix.diagonal fun i => (d i : ℂ)) g) g =
      ((∑ m ∈ g.support, Complex.normSq (g.coeff m) * lam d m * ∏ s, jr (m s) : ℝ) : ℂ) := by
  unfold gip
  have hpt : ∀ z : Sg ι A B → ℂ,
      eval z (sub 1 (Matrix.diagonal fun i => (d i : ℂ)) g) * star (eval z g) * Complex.exp (-(∑ s, ‖z s‖ ^ 2 : ℝ)) =
        ∑ m ∈ g.support, ∑ m' ∈ g.support, (g.coeff m * (lam d m : ℂ) * star (g.coeff m')) *
          (mon m z * star (mon m' z) * Complex.exp (-(∑ s, ‖z s‖ ^ 2 : ℝ))) := by
    intro z
    rw [eval_sub, Phi_diag, MvPolynomial.eval_eq', MvPolynomial.eval_eq']
    have hl : ∀ m : Sg ι A B →₀ ℕ, ∏ s, ((kap d s : ℂ) * z s) ^ m s = (lam d m : ℂ) * mon m z := by
      intro m
      simp only [mul_pow, Finset.prod_mul_distrib, lam, mon]
      push_cast
      rfl
    simp_rw [hl]
    rw [star_sum, Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun m' _ => ?_
    have hmon : (∏ i, z i ^ m' i) = mon m' z := rfl
    try simp only [star_mul']
    try rw [hmon]
    ring
  simp_rw [hpt]
  have hint : ∀ m m' : Sg ι A B →₀ ℕ, Integrable fun z : Sg ι A B → ℂ => mon m z * star (mon m' z) * Complex.exp (-(∑ s, ‖z s‖ ^ 2 : ℝ)) :=
    integrable_mon
  rw [MeasureTheory.integral_finsetSum _ fun m _ => MeasureTheory.integrable_finsetSum _ fun m' _ => (hint m m').const_mul _]
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [MeasureTheory.integral_finsetSum _ fun m' _ => (hint m m').const_mul _]
  simp_rw [integral_const_mul]
  rw [Finset.sum_eq_single_of_mem m hm fun m' _ hne => by rw [integral_mon_ne m m' hne.symm, mul_zero]]
  rw [integral_mon_self]
  have hc : ((Complex.normSq (g.coeff m) : ℝ) : ℂ) = g.coeff m * star (g.coeff m) := by
    rw [Complex.star_def, Complex.mul_conj]
  rw [Complex.ofReal_mul, Complex.ofReal_mul, hc]
  ring

end PositivityTheory.Rg.Sw.FFTSteps.PosProof
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GaussianPlaneIntegrals.Imports

section

@[expose] public section

noncomputable section

open MeasureTheory MvPolynomial Module
open scoped ComplexConjugate ComplexOrder

namespace PositivityTheory.Rg.Sw.FFTSteps

open PosProof

private theorem gip_monomial_self_eq_prod_jr {ι A B : Type} [Fintype ι] [DecidableEq ι] [Fintype A] [Fintype B]
    (m : Sg ι A B →₀ ℕ) :
    gip (monomial m (1 : ℂ)) (monomial m (1 : ℂ)) = ((∏ s : Sg ι A B, jr (m s) : ℝ) : ℂ) := by
  rw [← integral_mon_self m]
  unfold gip
  congr 1
  funext z
  rw [mon_prod]
  have h1 : (eval z) (monomial m (1 : ℂ)) = ∏ s : Sg ι A B, z s ^ m s := by
    rw [eval_monomial, one_mul, Finsupp.prod_fintype]
    intro i
    simp
  rw [h1, star_prod, ← Finset.prod_mul_distrib, Complex.ofReal_sum, ← Finset.sum_neg_distrib,
    Complex.exp_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [hk_diag, star_pow, ← mul_pow]
  have h2 : z s * star (z s) = ((‖z s‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [h2]
  push_cast
  ring_nf

private theorem pos_lemma {ι A B : Type} [Fintype ι] [DecidableEq ι] [Fintype A] [Fintype B]
    (d : ι → ℝ) (m : Sg ι A B →₀ ℕ) :
    sub 1 (Matrix.diagonal fun i => (d i : ℂ)) (monomial m (1 : ℂ)) =
      C ((∏ s : Sg ι A B, kap d s ^ m s : ℝ) : ℂ) * monomial m (1 : ℂ) := by
  apply MvPolynomial.funext
  intro z
  rw [PosProof.eval_sub, Phi_diag, eval_mul, eval_C, eval_monomial, eval_monomial, one_mul, one_mul,
    Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp)]
  push_cast
  simp only [mul_pow, Finset.prod_mul_distrib]

private theorem lam_eq_prod_kap_pow {ι A B : Type} [Fintype ι] [DecidableEq ι] [Fintype A] [Fintype B]
    (d : ι → ℝ) (m : Sg ι A B →₀ ℕ) :
    lam d m = ∏ s : Sg ι A B, kap d s ^ m s := by
  classical
  have hP : (0 : ℝ) < ∏ s : Sg ι A B, jr (m s) := Finset.prod_pos fun s _ => jr_pos _
  have h := gip_diag (A := A) (B := B) d (monomial m (1 : ℂ))
  rw [pos_lemma, support_monomial, if_neg one_ne_zero, Finset.sum_singleton, coeff_monomial, if_pos rfl,
    Complex.normSq_one, one_mul] at h
  have h3 : gip (C ((∏ s : Sg ι A B, kap d s ^ m s : ℝ) : ℂ) * monomial m (1 : ℂ)) (monomial m (1 : ℂ)) =
      ((∏ s : Sg ι A B, kap d s ^ m s : ℝ) : ℂ) * ((∏ s : Sg ι A B, jr (m s) : ℝ) : ℂ) := by
    rw [← gip_monomial_self_eq_prod_jr]
    unfold gip
    rw [← integral_const_mul]
    congr 1
    funext z
    rw [eval_mul, eval_C]
    ring
  rw [h3] at h
  have h4 : (∏ s : Sg ι A B, kap d s ^ m s) * (∏ s : Sg ι A B, jr (m s)) =
      lam d m * ∏ s : Sg ι A B, jr (m s) := by
    exact_mod_cast h
  exact (mul_right_cancel₀ hP.ne' h4).symm

private theorem gip_sub_eq_of_unitary_conj_diag {ι A B : Type} [Fintype ι] [DecidableEq ι] [Fintype A] [Fintype B]
    (M U D : Matrix ι ι ℂ) (hU1 : star U * U = 1) (hU2 : U * star U = 1) (hMU : M * U = U * D)
    (f : PV ι A B) :
    gip (sub 1 M f) f = gip (sub 1 D (sub 1 U f)) (sub 1 U f) := by
  have hcont : Continuous fun z : Sg ι A B → ℂ =>
      (eval z) (sub 1 M f) * star ((eval z) f) * Complex.exp (-↑(∑ s : Sg ι A B, ‖z s‖ ^ 2)) :=
    ((continuous_eval _).mul (continuous_star.comp (continuous_eval _))).mul
      (Complex.continuous_exp.comp (Complex.continuous_ofReal.comp
        (continuous_finsetSum _ fun s _ => (continuous_norm.comp (continuous_apply s)).pow 2)).neg)
  unfold gip
  rw [integral_Phi U hU1 hU2 _ hcont]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  simp only [PosProof.eval_sub]
  rw [← Phi_mul, ← Phi_mul, hMU, norm_Phi U hU1]

theorem pos : Pos := by
  intro ι A B _ _ _ _ M hM f
  have hH := hM.isHermitian
  have hMe : M = (hH.eigenvectorUnitary : Matrix ι ι ℂ) *
      Matrix.diagonal (fun i => (hH.eigenvalues i : ℂ)) * star (hH.eigenvectorUnitary : Matrix ι ι ℂ) := by
    conv_lhs => rw [hH.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply]
    rfl
  have hU1 : star (hH.eigenvectorUnitary : Matrix ι ι ℂ) * (hH.eigenvectorUnitary : Matrix ι ι ℂ) = 1 :=
    Unitary.coe_star_mul_self _
  have hU2 : (hH.eigenvectorUnitary : Matrix ι ι ℂ) * star (hH.eigenvectorUnitary : Matrix ι ι ℂ) = 1 := by
    simpa [Unitary.coe_star] using Unitary.coe_mul_star_self hH.eigenvectorUnitary
  have hMU : M * (hH.eigenvectorUnitary : Matrix ι ι ℂ) =
      (hH.eigenvectorUnitary : Matrix ι ι ℂ) * Matrix.diagonal (fun i => (hH.eigenvalues i : ℂ)) := by
    have h := congrArg (· * (hH.eigenvectorUnitary : Matrix ι ι ℂ)) hMe
    rw [h, Matrix.mul_assoc (_ * _), hU1, Matrix.mul_one]
  have hkap : ∀ s : Sg ι A B, 0 ≤ kap hH.eigenvalues s := by
    intro s
    rcases s with s | s
    · simp [kap]
    · simp only [kap, Sum.elim_inr]
      exact hM.eigenvalues_nonneg _
  rw [gip_sub_eq_of_unitary_conj_diag M _ _ hU1 hU2 hMU f, gip_diag]
  simp only [Complex.ofReal_re, Complex.ofReal_im]
  refine ⟨?_, trivial, ?_⟩
  · refine Finset.sum_nonneg fun m _ => mul_nonneg (mul_nonneg (Complex.normSq_nonneg _) ?_)
      (Finset.prod_nonneg fun s _ => (jr_pos _).le)
    rw [lam_eq_prod_kap_pow]
    exact Finset.prod_nonneg fun s _ => pow_nonneg (hkap s) _
  · intro hPD hf
    have hkap' : ∀ s : Sg ι A B, 0 < kap hH.eigenvalues s := by
      intro s
      rcases s with s | s
      · simp [kap]
      · simp only [kap, Sum.elim_inr]
        exact hPD.eigenvalues_pos _
    have hinv : sub 1 (star (hH.eigenvectorUnitary : Matrix ι ι ℂ))
        (sub 1 (hH.eigenvectorUnitary : Matrix ι ι ℂ) f) = f := by
      apply MvPolynomial.funext
      intro z
      rw [PosProof.eval_sub, PosProof.eval_sub, ← Phi_mul, hU2, Phi_one]
    have hg : sub 1 (hH.eigenvectorUnitary : Matrix ι ι ℂ) f ≠ 0 := by
      intro hg
      apply hf
      rw [← hinv, hg, map_zero]
    refine Finset.sum_pos (fun m hm => mul_pos (mul_pos (Complex.normSq_pos.2 (mem_support_iff.1 hm)) ?_)
      (Finset.prod_pos fun s _ => jr_pos _)) ?_
    · rw [lam_eq_prod_kap_pow]
      exact Finset.prod_pos fun s _ => pow_pos (hkap' s) _
    · exact Finset.nonempty_iff_ne_empty.2 (by rwa [Ne, MvPolynomial.support_eq_empty])

end PositivityTheory.Rg.Sw.FFTSteps
end
end
end
