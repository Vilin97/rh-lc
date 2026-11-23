module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.NullStableAlt
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.FockMomOfBasic
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.HopPderivComm
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.MapDomainFlpFlp
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.NullSec
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
import Mathlib.Topology.Sheaves.Init
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.PolyExpBound
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.SumPderivXMem
import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.RingTheory.Derivation.Lie
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Bool
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.Linter.Style

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.NullSecKAlg

section

@[expose] public section

noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.LC

open PositivityTheory.Rg.Sw

def MomLin : Prop :=
  ∀ (m n : ℕ) (c : ℝ), 0 < c → ∀ (P Q : PX m n) (r : ℂ), mom c (P + Q) = mom c P + mom c Q ∧ mom c (r • P) = r * mom c P

end PositivityTheory.Rg.Sw.LC
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.MomLin

section

@[expose] public section

noncomputable section

open MvPolynomial MeasureTheory

namespace PositivityTheory.Rg.Sw.LC

open PositivityTheory.Rg.Sw

theorem momLin : MomLin := by
  intro m n c hc P Q r
  have hP := NullS.integrable_pg c hc P
  have hQ := NullS.integrable_pg c hc Q
  constructor
  · unfold mom
    rw [← integral_add hP hQ]
    congr 1
    funext x
    simp [evX]
    ring
  · unfold mom
    rw [← integral_const_mul]
    congr 1
    funext x
    simp [evX]
    ring

end PositivityTheory.Rg.Sw.LC
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.NullStable

section

@[expose] public section

namespace PositivityTheory.Rg.Sw.LC

theorem nullStable : NullStable := NullS.nullStable

end PositivityTheory.Rg.Sw.LC
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.PderivComm

section

@[expose] public section

noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.LC.FK

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC

variable {m n : ℕ}

def sw (k : Fin m × Fin n × Bool) : Fin m × Fin n × Bool := (k.1, k.2.1, !k.2.2)

theorem sw_inj {k k' : Fin m × Fin n × Bool} : sw k = sw k' ↔ k = k' := by
  obtain ⟨a, i, b⟩ := k
  obtain ⟨a', i', b'⟩ := k'
  cases b <;> cases b' <;> simp [sw]

theorem pderiv_comm (i j : Fin m × Fin n × Bool) (P : PX m n) :
    pderiv i (pderiv j P) = pderiv j (pderiv i P) := by
  classical
  have h : ⁅(pderiv (R := ℂ) i : Derivation ℂ (PX m n) (PX m n)), pderiv (R := ℂ) j⁆ = 0 := by
    apply MvPolynomial.derivation_ext
    intro k
    rw [Derivation.commutator_apply, pderiv_X, pderiv_X]
    by_cases hi : i = k <;> by_cases hj : j = k <;> simp [Pi.single_apply, hi, hj]
  have := congrArg (fun D : Derivation ℂ (PX m n) (PX m n) => D P) h
  simpa [Derivation.commutator_apply, sub_eq_zero] using this

theorem cr_apply (c : ℝ) (k : Fin m × Fin n × Bool) (Q : PX m n) :
    cr c k Q = -(pderiv k Q) + (2 * c : ℂ) • ((X (sw k) : PX m n) * Q) := by
  obtain ⟨a, i, b⟩ := k
  cases b <;> simp [cr, sw]

theorem pderiv_cr (c : ℝ) (k k' : Fin m × Fin n × Bool) (Q : PX m n) :
    pderiv (sw k') (cr c k Q) = cr c k (pderiv (sw k') Q) + (if k = k' then (2 * c : ℂ) else 0) • Q := by
  classical
  rw [cr_apply, cr_apply, map_add (f := _), map_neg, Derivation.map_smul, pderiv_mul, pderiv_X, pderiv_comm (sw k') k]
  by_cases h : k = k'
  · subst h; simp; ring
  · have : sw k' ≠ sw k := fun e => h (sw_inj.1 e).symm
    simp [h, this]

theorem fock_one (c : ℝ) : fock c (1 : PX m n) = 1 := by
  classical
  have h1 : (1 : PX m n) = monomial 0 1 := rfl
  unfold fock
  rw [h1, support_monomial, if_neg one_ne_zero, Finset.sum_singleton, coeff_monomial, if_pos rfl, one_smul]
  simp [fockMono]

theorem fock_C (hB : FockBasic) (c : ℝ) (hc : 0 < c) (a : ℂ) : fock c (C a : PX m n) = C a := by
  have hL := (hB m n c hc).1
  rw [show (C a : PX m n) = a • 1 by rw [smul_eq_C_mul, mul_one], hL.map_smul, fock_one, smul_eq_C_mul, mul_one]

theorem der_fock (hB : FockBasic) (c : ℝ) (hc : 0 < c) (k : Fin m × Fin n × Bool) (p : PX m n) :
    pderiv (sw k) (fock c p) = (2 * c : ℂ) • fock c (pderiv k p) := by
  classical
  have hL := (hB m n c hc).1
  have hX := (hB m n c hc).2.2
  induction p using MvPolynomial.induction_on with
  | C a => rw [fock_C hB c hc]; simp [hL.map_zero]
  | add p q hp hq => rw [hL.map_add (f := _), map_add (f := _), hp, hq, map_add (f := _), hL.map_add (f := _), smul_add]
  | mul_X p k0 hp =>
    rw [mul_comm, hX, pderiv_cr, hp, map_smul, ← hX, pderiv_mul, pderiv_X, hL.map_add (f := _), smul_add]
    by_cases h : k0 = k
    · subst h
      simp only [Pi.single_eq_same, if_true, mul_comm (X k0) (pderiv k0 p)]
      rw [one_mul, add_comm]
    · simp only [Pi.single_apply, h, if_false, add_zero, zero_smul, mul_comm (X k0) (pderiv k p)]
      rw [zero_mul, hL.map_zero, smul_zero, zero_add]

theorem qp_sum (ε : Fin m → Bool) (i j : Fin n) :
    Qp ε i j = ∑ a, C (sgn ε a) * ((X (a, i, true) : PX m n) * X (a, j, false)) := by
  unfold Qp Qb
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  cases h : ε a <;> simp [sgn, h]

theorem op_id (c : ℝ) (ε : Fin m → Bool) (i j : Fin n) (P : PX m n) :
    (∑ a ∈ Finset.univ.filter (fun a => ε a = true), cr c (a, i, false) (pderiv (a, j, true) P)) -
      ∑ a ∈ Finset.univ.filter (fun a => ε a = false), cr c (a, j, true) (pderiv (a, i, false) P) =
    ((c : ℂ) ^ 2) • mulQ ε i j P - lapS ε c i j P - (c : ℂ) • eulH c i j P + (c : ℂ) • eulA c i j P -
      (if i = j then (c : ℂ) * ∑ a, sgn ε a else 0) • P := by
  classical
  have hd : (if i = j then (c : ℂ) * ∑ a, sgn ε a else 0) • P =
      ∑ a, (if i = j then (c : ℂ) * sgn ε a else 0) • P := by
    by_cases hij : i = j <;> simp [hij, Finset.mul_sum, Finset.sum_smul]
  rw [hd, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
  unfold mulQ lapS eulH eulA
  rw [qp_sum, Finset.sum_mul, Finset.smul_sum, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  cases hε : ε a
  · simp only [hε, Bool.false_eq_true, if_false, if_true, zero_sub, cr_apply, sw, Bool.not_true]
    rw [pderiv_comm (a, j, true) (a, i, false)]
    by_cases hij : i = j
    · subst hij
      simp [sgn, hε, pderiv_mul, pderiv_X, Pi.single_apply, smul_eq_C_mul, pderiv_C_mul, map_ofNat]
      ring
    · have hne : (a, j, false) ≠ (a, i, false) := by simp [Ne.symm hij]
      simp [sgn, hε, pderiv_mul, pderiv_X, Pi.single_apply, smul_eq_C_mul, pderiv_C_mul, hij, hne, map_ofNat]
      ring
  · simp only [hε, if_true, Bool.true_eq_false, if_false, sub_zero, cr_apply, sw, Bool.not_false]
    by_cases hij : i = j
    · subst hij
      simp [sgn, hε, pderiv_mul, pderiv_X, Pi.single_apply, smul_eq_C_mul, pderiv_C_mul, map_ofNat]
      ring
    · have hne : (a, j, false) ≠ (a, i, false) := by simp [Ne.symm hij]
      simp [sgn, hε, pderiv_mul, pderiv_X, Pi.single_apply, smul_eq_C_mul, pderiv_C_mul, hij, hne, map_ofNat]
      ring

theorem kopL_apply (ε : Fin m → Bool) (i j : Fin n) (p : PX m n) :
    KopL ε i j p = ∑ a ∈ Finset.univ.filter (fun a => ε a = true), (X (a, i, false) : PX m n) * pderiv (a, j, false) p -
      ∑ a ∈ Finset.univ.filter (fun a => ε a = false), (X (a, j, true) : PX m n) * pderiv (a, i, true) p := by
  simp [KopL]

end PositivityTheory.Rg.Sw.LC.FK

namespace PositivityTheory.Rg.Sw.LC

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC.FK

theorem fockK_of (hB : FockBasic) : FockK := by
  intro m n ε c hc
  have hc2 : (2 * c : ℂ) ≠ 0 := by
    have : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    exact mul_ne_zero two_ne_zero this
  refine ⟨(2 * c : ℂ)⁻¹ * (c : ℂ) ^ 2, -(2 * c : ℂ)⁻¹, -((2 * c : ℂ)⁻¹ * c), (2 * c : ℂ)⁻¹ * c,
    -((2 * c : ℂ)⁻¹ * ((c : ℂ) * ∑ a, sgn ε a)), fun i j p => ?_⟩
  have hL := (hB m n c hc).1
  have hX := (hB m n c hc).2.2
  let L : PX m n →ₗ[ℂ] PX m n := hL.mk' (fock c)
  have eL : ∀ x, fock c x = L x := fun x => rfl
  have hd : ∀ k (q : PX m n), fock c (pderiv k q) = (2 * c : ℂ)⁻¹ • pderiv (sw k) (fock c q) := by
    intro k q
    rw [der_fock hB c hc, inv_smul_smul₀ hc2]
  have key : fock c (KopL ε i j p) = (2 * c : ℂ)⁻¹ •
      ((∑ a ∈ Finset.univ.filter (fun a => ε a = true), cr c (a, i, false) (pderiv (a, j, true) (fock c p))) -
        ∑ a ∈ Finset.univ.filter (fun a => ε a = false), cr c (a, j, true) (pderiv (a, i, false) (fock c p))) := by

    rw [kopL_apply, eL, map_sub, map_sum, map_sum, smul_sub, Finset.smul_sum, Finset.smul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun a _ => ?_
      rw [← eL, hX, hd, map_smul]
      rfl
    · refine Finset.sum_congr rfl fun a _ => ?_
      rw [← eL, hX, hd, map_smul]
      rfl
  rw [key, op_id]
  by_cases hij : i = j
  · simp only [hij, if_true]
    module
  · simp only [hij, if_false, zero_smul, sub_zero, add_zero]
    module

end PositivityTheory.Rg.Sw.LC
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.LcOfCore

section

@[expose] public section

namespace PositivityTheory.Rg.Sw.LC

private theorem nullSec_add' {m n : ℕ} {ε : Fin m → Bool} {c : ℝ} (hc : 0 < c) {P Q : PX m n}
    (hP : NullSec ε c P) (hQ : NullSec ε c Q) : NullSec ε c (P + Q) := by
  intro R hR
  rw [mul_add, (momLin m n c hc (R * P) (R * Q) 1).1, hP R hR, hQ R hR, add_zero]

private theorem nullSec_smul' {m n : ℕ} {ε : Fin m → Bool} {c : ℝ} (hc : 0 < c) {P : PX m n}
    (r : ℂ) (hP : NullSec ε c P) : NullSec ε c (r • P) := by
  intro R hR
  rw [mul_smul_comm, (momLin m n c hc (R * P) 0 r).2, hP R hR, mul_zero]

private theorem nullSec_fock_apply_of_mem_kAlg {m n : ℕ} {ε : Fin m → Bool} {c : ℝ} (hc : 0 < c)
    (w : Module.End ℂ (PX m n)) (hw : w ∈ kAlg ε) :
    ∀ p : PX m n, NullSec ε c (fock c p) → NullSec ε c (fock c (w p)) := by
  have hlin := (fockBasic m n c hc).1
  obtain ⟨a₁, a₂, a₃, a₄, a₅, hk⟩ := fockK_of fockBasic m n ε c hc
  have hN := nullStable m n ε c hc
  have hw' : w ∈ Algebra.adjoin ℂ (Set.range fun ij : Fin n × Fin n => KopL ε ij.1 ij.2) := hw
  clear hw
  induction hw' using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨⟨i, j⟩, rfl⟩ := hx
    intro p hp
    show NullSec ε c (fock c (KopL ε i j p))
    rw [hk i j p]
    obtain ⟨h1, h2, h3, h4⟩ := hN i j _ hp
    exact nullSec_add' hc (nullSec_add' hc (nullSec_add' hc (nullSec_add' hc
      (nullSec_smul' hc _ h4) (nullSec_smul' hc _ h1)) (nullSec_smul' hc _ h2))
      (nullSec_smul' hc _ h3)) (nullSec_smul' hc _ hp)
  | algebraMap r =>
    intro p hp
    rw [Module.algebraMap_end_apply, hlin.map_smul]
    exact nullSec_smul' hc r hp
  | add x y _ _ hx hy =>
    intro p hp
    rw [LinearMap.add_apply, hlin.map_add (f := _)]
    exact nullSec_add' hc (hx p hp) (hy p hp)
  | mul x y _ _ hx hy =>
    intro p hp
    exact hx _ (hy p hp)

theorem lc_of_core (hC : CoreLC) : PositivityTheory.Rg.Sw.LC := by
  intro m n ε c hc lam hlam P hP
  obtain ⟨hlin, hbij, -⟩ := fockBasic m n c hc
  let F : PX m n →ₗ[ℂ] PX m n := hlin.mk' _
  let Λ : PX m n →ₗ[ℂ] ℂ := lam.comp F
  have hΛ : ∀ (a b : Fin m) (p : PX m n), Λ (Dop ε c a b p) = 0 := by
    intro a b p
    show lam (fock c (Dop ε c a b p)) = 0
    rw [← fockHOp_of fockBasic m n ε c hc a b p]
    exact hlam a b _
  obtain ⟨p, rfl⟩ := hbij.2 P
  obtain ⟨w, hw, hval⟩ := hC m n ε c hc Λ hΛ p
  have h1 : lam (fock c p) = contr c (w p) := hval
  rw [h1]
  have hM := fockMom_of_basic fockBasic m n c hc
  have h0 : mom c (fock c (w p)) = 0 := by
    simpa using nullSec_fock_apply_of_mem_kAlg hc w hw p hP 1 (Subalgebra.one_mem _)
  rw [hM.2] at h0
  exact (mul_eq_zero.mp h0).resolve_left hM.1

end PositivityTheory.Rg.Sw.LC
end
end
