module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.IntegrableMonomial
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.NullStableAlt
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.FockMono
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Bool
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.RingTheory.Derivation.Lie
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.IntegrableRpowGauss

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.ContrEqOfSubset

section

@[expose] public section

noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.LC

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

def hC (c : ℝ) (p q : ℕ) : ℂ := if p = q then (p.factorial : ℂ) * (2 * c : ℂ) ^ p else 0

def wC (c : ℝ) (s : Fin m × Fin n × Bool →₀ ℕ) : ℂ := ∏ a, ∏ i, hC c (s (a, i, false)) (s (a, i, true))

theorem hC_comm (c : ℝ) (p q : ℕ) : hC c p q = hC c q p := by
  unfold hC; by_cases h : p = q
  · subst h; rfl
  · rw [if_neg h, if_neg (Ne.symm h)]

theorem hC_rel (c : ℝ) (p q : ℕ) : hC c (p + 1) q = (2 * c : ℂ) * (q : ℂ) * hC c p (q - 1) := by
  rcases q with _ | q
  · simp [hC]
  · simp only [hC, Nat.add_sub_cancel, Nat.add_right_cancel_iff]
    split_ifs with h
    · subst h; rw [Nat.factorial_succ]; push_cast; ring
    · simp

theorem contr_eq (c : ℝ) (p : PX m n) : contr c p = ∑ s ∈ p.support, p.coeff s * wC c s := by
  unfold contr wC
  refine Finset.sum_congr rfl fun s _ => ?_
  have : (∏ a, ∏ i, hC c (s (a, i, false)) (s (a, i, true))) =
      if ∀ a i, s (a, i, false) = s (a, i, true) then
        ∏ a, ∏ i, (((s (a, i, false)).factorial : ℂ) * (2 * c : ℂ) ^ (s (a, i, false))) else 0 := by
    simp only [hC, Finset.prod_ite_zero, Finset.mem_univ, true_implies]
  rw [this]
  split_ifs <;> simp

theorem contr_eq_of_subset (c : ℝ) (p : PX m n) (S : Finset (Fin m × Fin n × Bool →₀ ℕ)) (hS : p.support ⊆ S) :
    contr c p = ∑ s ∈ S, p.coeff s * wC c s := by
  rw [contr_eq]
  refine Finset.sum_subset hS fun s _ hs => ?_
  rw [notMem_support_iff.1 hs, zero_mul]

theorem contr_add (c : ℝ) (p q : PX m n) : contr c (p + q) = contr c p + contr c q := by
  classical
  rw [contr_eq_of_subset c (p + q) (p.support ∪ q.support) support_add,
    contr_eq_of_subset c p (p.support ∪ q.support) Finset.subset_union_left,
    contr_eq_of_subset c q (p.support ∪ q.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [MvPolynomial.coeff_add, add_mul]

theorem contr_monomial (c : ℝ) (s : Fin m × Fin n × Bool →₀ ℕ) (r : ℂ) : contr c (monomial s r) = r * wC c s := by
  classical
  rw [contr_eq_of_subset c _ {s} support_monomial_subset, Finset.sum_singleton, coeff_monomial, if_pos rfl]

theorem contr_C (c : ℝ) (r : ℂ) : contr c (C r : PX m n) = r := by
  rw [← monomial_zero', contr_monomial]
  simp [wC, hC]

theorem wC_split (c : ℝ) (s : Fin m × Fin n × Bool →₀ ℕ) (a : Fin m) (i : Fin n) :
    wC c s = hC c (s (a, i, false)) (s (a, i, true)) *
      ∏ x ∈ Finset.univ.erase (a, i), hC c (s (x.1, x.2, false)) (s (x.1, x.2, true)) := by
  unfold wC
  rw [← Fintype.prod_prod_type' (f := fun a i => hC c (s (a, i, false)) (s (a, i, true)))]
  exact (Finset.mul_prod_erase _ (fun x : Fin m × Fin n => hC c (s (x.1, x.2, false)) (s (x.1, x.2, true)))
    (Finset.mem_univ (a, i))).symm

theorem wC_rel (c : ℝ) (u : Fin m × Fin n × Bool →₀ ℕ) (k : Fin m × Fin n × Bool) :
    wC c (Finsupp.single k 1 + u) = (2 * c : ℂ) * (u (flip k) : ℂ) * wC c (u - Finsupp.single (flip k) 1) := by
  obtain ⟨a, i, b⟩ := k
  rw [wC_split c _ a i, wC_split c _ a i]
  have hrest : ∏ x ∈ Finset.univ.erase (a, i), hC c ((Finsupp.single (a, i, b) 1 + u : Fin m × Fin n × Bool →₀ ℕ) (x.1, x.2, false))
        ((Finsupp.single (a, i, b) 1 + u : Fin m × Fin n × Bool →₀ ℕ) (x.1, x.2, true)) =
      ∏ x ∈ Finset.univ.erase (a, i), hC c ((u - Finsupp.single (flip (a, i, b)) 1 : Fin m × Fin n × Bool →₀ ℕ) (x.1, x.2, false))
        ((u - Finsupp.single (flip (a, i, b)) 1 : Fin m × Fin n × Bool →₀ ℕ) (x.1, x.2, true)) := by
    refine Finset.prod_congr rfl fun x hx => ?_
    have hx' := (Finset.mem_erase.1 hx).1
    have key : ∀ b', (Finsupp.single (a, i, b) 1 + u : Fin m × Fin n × Bool →₀ ℕ) (x.1, x.2, b') = (u - Finsupp.single (flip (a, i, b)) 1 : Fin m × Fin n × Bool →₀ ℕ) (x.1, x.2, b') := by
      intro b'
      have h1 : (a, i, b) ≠ (x.1, x.2, b') := fun h => hx' (by
        have := congrArg (fun y : Fin m × Fin n × Bool => (y.1, y.2.1)) h; simp at this; exact this.symm)
      have h2 : flip (a, i, b) ≠ (x.1, x.2, b') := fun h => hx' (by
        have := congrArg (fun y : Fin m × Fin n × Bool => (y.1, y.2.1)) h; simp [flip] at this; exact this.symm)
      simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply,
        if_neg h1, if_neg h2, tsub_zero, zero_add]
    rw [key false, key true]
  rw [hrest, ← mul_assoc]
  congr 1
  have e1 : (a, i, true) ≠ (a, i, false) := by simp
  cases b
  · simp only [flip, Bool.not_false, Finsupp.coe_tsub, Pi.sub_apply, Finsupp.coe_add, Pi.add_apply,
      Finsupp.single_apply, if_pos, if_neg e1, if_neg e1.symm, tsub_zero, zero_add]
    rw [add_comm]
    exact hC_rel c _ _
  · simp only [flip, Bool.not_true, Finsupp.coe_tsub, Pi.sub_apply, Finsupp.coe_add, Pi.add_apply,
      Finsupp.single_apply, if_pos, if_neg e1, if_neg e1.symm, tsub_zero, zero_add]
    rw [hC_comm c (u (a, i, false)), hC_comm c (u (a, i, false) - 1), add_comm]
    exact hC_rel c _ _

theorem contr_X_mul (c : ℝ) (k : Fin m × Fin n × Bool) (p : PX m n) :
    contr c (X k * p) = (2 * c : ℂ) * contr c (pderiv (flip k) p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial u r =>
    have hX : (X k : PX m n) * monomial u r = monomial (Finsupp.single k 1 + u) r := by
      rw [X, monomial_mul, one_mul]
    rw [hX, pderiv_monomial, contr_monomial, contr_monomial, wC_rel]
    ring
  | add P Q hP hQ => rw [mul_add, contr_add, hP, hQ, map_add (f := _), contr_add, mul_add]

end PositivityTheory.Rg.Sw.LC
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.GaussianMomentRecurrence

section

@[expose] public section

noncomputable section

open MvPolynomial MeasureTheory

namespace PositivityTheory.Rg.Sw.LC

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

theorem gaussian_moment_symm (c : ℝ) (p q : ℕ) : g1 c p q = g1 c q p := by
  unfold g1; by_cases h : p = q
  · subst h; rfl
  · rw [if_neg h, if_neg (Ne.symm h)]

theorem gaussian_moment_recurrence (c : ℝ) (hc : 0 < c) (p q : ℕ) : (p : ℂ) * g1 c (p - 1) q = (c : ℂ) * g1 c p (q + 1) := by
  rcases p with _ | p
  · simp [g1]
  · simp only [Nat.add_sub_cancel, g1, Nat.add_right_cancel_iff]
    split_ifs with h
    · subst h
      have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
      push_cast
      rw [Nat.factorial_succ]
      push_cast
      field_simp
      ring
    · simp

theorem phi_split (c : ℝ) (s : Fin m × Fin n × Bool →₀ ℕ) (a : Fin m) (i : Fin n) :
    phi c s = g1 c (s (a, i, false)) (s (a, i, true)) *
      ∏ x ∈ Finset.univ.erase (a, i), g1 c (s (x.1, x.2, false)) (s (x.1, x.2, true)) := by
  unfold phi
  rw [← Fintype.prod_prod_type' (f := fun a i => g1 c (s (a, i, false)) (s (a, i, true)))]
  exact (Finset.mul_prod_erase _ (fun x : Fin m × Fin n => g1 c (s (x.1, x.2, false)) (s (x.1, x.2, true)))
    (Finset.mem_univ (a, i))).symm

theorem rest_congr (c : ℝ) (s s' : Fin m × Fin n × Bool →₀ ℕ) (a : Fin m) (i : Fin n)
    (h : ∀ x : Fin m × Fin n, x ≠ (a, i) → ∀ b, s (x.1, x.2, b) = s' (x.1, x.2, b)) :
    ∏ x ∈ Finset.univ.erase (a, i), g1 c (s (x.1, x.2, false)) (s (x.1, x.2, true)) =
      ∏ x ∈ Finset.univ.erase (a, i), g1 c (s' (x.1, x.2, false)) (s' (x.1, x.2, true)) := by
  refine Finset.prod_congr rfl fun x hx => ?_
  have hx' := (Finset.mem_erase.1 hx).1
  rw [h x hx' false, h x hx' true]

theorem phi_rel (c : ℝ) (hc : 0 < c) (u : Fin m × Fin n × Bool →₀ ℕ) (k : Fin m × Fin n × Bool) :
    (u k : ℂ) * phi c (u - Finsupp.single k 1) = (c : ℂ) * phi c (Finsupp.single (flip k) 1 + u) := by
  obtain ⟨a, i, b⟩ := k
  rw [phi_split c _ a i, phi_split c _ a i,
    rest_congr c (u - Finsupp.single (a, i, b) 1) (Finsupp.single (flip (a, i, b)) 1 + u) a i (fun x hx b' => by
      have h1 : (x.1, x.2, b') ≠ (a, i, b) := fun h => hx (by
        have := congrArg (fun y : Fin m × Fin n × Bool => (y.1, y.2.1)) h; simpa using this)
      have h2 : (x.1, x.2, b') ≠ flip (a, i, b) := fun h => hx (by
        have := congrArg (fun y : Fin m × Fin n × Bool => (y.1, y.2.1)) h; simpa [flip] using this)
      simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply,
        if_neg (Ne.symm h1), if_neg (Ne.symm h2), tsub_zero, zero_add])]
  rw [← mul_assoc, ← mul_assoc]
  congr 1
  cases b
  · have e1 : (a, i, true) ≠ (a, i, false) := by simp
    simp only [flip, Bool.not_false, Finsupp.coe_tsub, Pi.sub_apply, Finsupp.coe_add, Pi.add_apply,
      Finsupp.single_apply, if_pos, if_neg e1, if_neg e1.symm, tsub_zero, zero_add]
    rw [add_comm]
    exact gaussian_moment_recurrence c hc _ _
  · have e1 : (a, i, true) ≠ (a, i, false) := by simp
    simp only [flip, Bool.not_true, Finsupp.coe_tsub, Pi.sub_apply, Finsupp.coe_add, Pi.add_apply,
      Finsupp.single_apply, if_pos, if_neg e1, if_neg e1.symm, tsub_zero, zero_add]
    rw [gaussian_moment_symm c _ (u (a, i, true) - 1), gaussian_moment_symm c (1 + u (a, i, false)), add_comm]
    exact gaussian_moment_recurrence c hc _ _

variable (hM : OneMom)


include hM in
theorem mom_pderiv (c : ℝ) (hc : 0 < c) (k : Fin m × Fin n × Bool) (Q : PX m n) :
    mom c (pderiv k Q) = (c : ℂ) * mom c (X (flip k) * Q) := by
  induction Q using MvPolynomial.induction_on' with
  | monomial u r =>
    have hX : (X (flip k) : PX m n) * monomial u r = monomial (Finsupp.single (flip k) 1 + u) r := by
      rw [X, monomial_mul, one_mul]
    rw [pderiv_monomial, hX, mom_monomial hM c hc, mom_monomial hM c hc, mul_assoc, phi_rel c hc u k]
    ring
  | add P Q hP hQ => rw [map_add (f := _), mom_add hM c hc, hP, hQ, mul_add, mom_add hM c hc, mul_add]

theorem pderiv_comm (k j : Fin m × Fin n × Bool) (Q : PX m n) :
    pderiv k (pderiv j Q) = pderiv j (pderiv k Q) := by
  have : ⁅(pderiv k : Derivation ℂ (PX m n) (PX m n)), (pderiv j : Derivation ℂ (PX m n) (PX m n))⁆ = 0 := by
    apply MvPolynomial.derivation_ext
    intro l
    rw [Derivation.commutator_apply, Derivation.zero_apply]
    classical
    rw [pderiv_X, pderiv_X]
    simp only [Pi.single_apply]
    split_ifs <;> simp
  have h := congrArg (fun D : Derivation ℂ (PX m n) (PX m n) => D Q) this
  simp only [Derivation.commutator_apply, Derivation.zero_apply] at h
  exact sub_eq_zero.1 h

theorem cr_apply (c : ℝ) (k : Fin m × Fin n × Bool) (Q : PX m n) :
    cr c k Q = -pderiv k Q + (2 * c : ℂ) • (X (flip k) * Q) := by
  obtain ⟨a, i, b⟩ := k
  cases b <;> simp [cr, flip]

theorem pderiv_cr (c : ℝ) (k j : Fin m × Fin n × Bool) (Q : PX m n) :
    pderiv k (cr c j Q) = cr c j (pderiv k Q) + (if k = flip j then (2 * c : ℂ) else 0) • Q := by
  classical
  rw [cr_apply, cr_apply, map_add (f := _), map_neg, Derivation.map_smul, pderiv_mul, pderiv_X, pderiv_comm k j]
  by_cases h : k = flip j
  · subst h; simp [Pi.single_apply]; ring
  · simp [Pi.single_apply, h, Ne.symm h]

end PositivityTheory.Rg.Sw.LC
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.FockMomOfBasic

section

@[expose] public section

noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.LC

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

theorem fockMono_zero (c : ℝ) : fockMono c (0 : Fin m × Fin n × Bool →₀ ℕ) = (1 : PX m n) := by
  simp [fockMono]

theorem fock_C (c : ℝ) (r : ℂ) : fock c (C r : PX m n) = C r := by
  classical
  by_cases hr : r = 0
  · subst hr; simp [fock]
  · rw [fock, ← monomial_zero', support_monomial, if_neg hr, Finset.sum_singleton, coeff_monomial, if_pos rfl,
      fockMono_zero, smul_eq_C_mul, mul_one, monomial_zero']

theorem deg_lt (s : Fin m × Fin n × Bool →₀ ℕ) (k : Fin m × Fin n × Bool) (hk : s k ≠ 0)
    (t : Fin m × Fin n × Bool →₀ ℕ) (ht : ∀ x, t x ≤ (s - Finsupp.single k 1 : Fin m × Fin n × Bool →₀ ℕ) x) : ∑ x, t x < ∑ x, s x := by
  refine lt_of_le_of_lt (Finset.sum_le_sum fun x _ => ht x) ?_
  refine Finset.sum_lt_sum (fun x _ => by simp) ⟨k, Finset.mem_univ _, ?_⟩
  simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_same]
  omega

variable (hB : FockBasic)

include hB in
theorem pderiv_fock (c : ℝ) (hc : 0 < c) (k : Fin m × Fin n × Bool) (p : PX m n) :
    pderiv k (fock c p) = (2 * c : ℂ) • fock c (pderiv (flip k) p) := by
  classical
  obtain ⟨hL, -, hX⟩ := hB m n c hc
  induction p using MvPolynomial.induction_on with
  | C r => rw [fock_C, pderiv_C, pderiv_C, hL.map_zero, smul_zero]
  | add p q hp hq => rw [hL.map_add (f := _), map_add (f := _), hp, hq, map_add (f := _), hL.map_add (f := _), smul_add]
  | mul_X p j hp =>
    rw [mul_comm, hX, pderiv_cr, hp, map_smul, pderiv_mul, pderiv_X, hL.map_add (f := _), hX, Pi.single_apply]
    by_cases h : k = flip j
    · have h' : j = flip k := by rw [h, flip_flip]
      rw [if_pos h, if_pos h', one_mul, smul_add, add_comm]
    · have h' : ¬ j = flip k := fun e => h (by rw [e, flip_flip])
      rw [if_neg h, if_neg h', zero_mul, hL.map_zero, zero_smul, add_zero, zero_add]

variable (hM : OneMom)

include hB hM in
theorem mom_fock_X (c : ℝ) (hc : 0 < c) (k : Fin m × Fin n × Bool) (p : PX m n) :
    mom c (fock c (X k * p)) = (2 * c : ℂ) * mom c (fock c (pderiv (flip k) p)) := by
  obtain ⟨hL, -, hX⟩ := hB m n c hc
  have e1 := mom_pderiv hM c hc k (fock c p)
  have e2 : mom c (pderiv k (fock c p)) = (2 * c : ℂ) * mom c (fock c (pderiv (flip k) p)) := by
    rw [pderiv_fock hB c hc, mom_smul]
  rw [hX, cr_apply, mom_add hM c hc, ← neg_one_smul ℂ (pderiv k (fock c p)), mom_smul, mom_smul, ← e2, e1]
  ring

include hB hM in
theorem fockMom_of : FockMom := by
  intro m n c hc
  obtain ⟨hL, -, -⟩ := hB m n c hc
  have h1 : mom c (1 : PX m n) ≠ 0 := by
    rw [← C_1, ← monomial_zero', mom_monomial hM c hc, one_mul, phi]
    refine Finset.prod_ne_zero_iff.2 fun a _ => Finset.prod_ne_zero_iff.2 fun i _ => ?_
    simp only [Finsupp.coe_zero, Pi.zero_apply, g1, Nat.factorial_zero, Nat.cast_one, mul_one, zero_add,
      pow_one, if_true]
    exact_mod_cast (div_pos Real.pi_pos hc).ne'
  refine ⟨h1, ?_⟩
  let D : PX m n → ℂ := fun p => mom c (fock c p) - mom c (1 : PX m n) * contr c p
  have hDadd : ∀ p q, D (p + q) = D p + D q := by
    intro p q; simp only [D]; rw [hL.map_add (f := _), mom_add hM c hc, contr_add]; ring
  have hDC : ∀ r, D (C r) = 0 := by
    intro r; simp only [D]
    rw [fock_C, contr_C, C_eq_smul_one, mom_smul]; ring
  have hDX : ∀ k p, D (X k * p) = (2 * c : ℂ) * D (pderiv (flip k) p) := by
    intro k p; simp only [D]; rw [mom_fock_X hB hM c hc, contr_X_mul]; ring
  have hmono : ∀ N, ∀ s : Fin m × Fin n × Bool →₀ ℕ, ∑ x, s x = N → ∀ r, D (monomial s r) = 0 := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro s hs r
      by_cases h0 : s = 0
      · subst h0; rw [monomial_zero']; exact hDC r
      · obtain ⟨k, hk⟩ := Finsupp.ne_iff.1 h0
        have hk' : s k ≠ 0 := by simpa using hk
        have hs' : Finsupp.single k 1 + (s - Finsupp.single k 1) = s := by
          ext x
          simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, Finsupp.single_apply]
          split_ifs with hx
          · subst hx; omega
          · simp
        have hXm : monomial s r = (X k : PX m n) * monomial (s - Finsupp.single k 1) r := by
          rw [X, monomial_mul, one_mul, hs']
        rw [hXm, hDX, pderiv_monomial]
        have hlt : ∑ x, ((s - Finsupp.single k 1 - Finsupp.single (flip k) 1 : Fin m × Fin n × Bool →₀ ℕ) x) < N :=
          hs ▸ deg_lt s k hk' _ (fun x => by simp only [Finsupp.coe_tsub, Pi.sub_apply]; exact tsub_le_self)
        rw [ih _ hlt _ rfl, mul_zero]
  intro p
  have hD0 : D p = 0 := by
    induction p using MvPolynomial.induction_on' with
    | monomial s r => exact hmono _ s rfl r
    | add p q hp hq => rw [hDadd, hp, hq, add_zero]
  exact sub_eq_zero.1 hD0

theorem fockMom_of_basic (hB : FockBasic) : FockMom := fockMom_of hB oneMom

end PositivityTheory.Rg.Sw.LC
end
end
end
