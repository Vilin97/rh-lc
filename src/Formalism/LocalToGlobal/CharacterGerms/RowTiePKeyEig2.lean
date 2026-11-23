module

public import Formalism.LocalToGlobal.CharacterGerms.RowTiePKeyDef
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePKeyJointDef
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePKeyTeichDef
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePKeyEigA
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePGmExLem
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.CharacterGerms.RowTiePProjFB
import Mathlib.Tactic.Linter.Style
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Pi
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePKeyTeich2

-- Source module: Formalism.LocalToGlobal.CharacterGerms.RowTiePKeyEigB

section

@[expose] public section

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

namespace RowTiePKeyEig

open RowTiePE0 RowTiePKey RowTiePProj GmExArith

variable {C : Type} [Field C] {V : VF C} {O : Type} [CommRing O] {n d : ℕ} (K : KeyData C V O n d)

theorem em_iter (x : O) (a : ZMod d) (k : ℕ) : V.MM (K.em (a + k) x - K.em a x ^ V.l ^ k) := by
  induction k with
  | zero => simp [mm_zero]
  | succ k ih =>
    have h1 := K.em_frob (a + k) x
    have h2 := mm_pow_sub (K.em_int _ x) ((K.em_int a x).pow _) ih V.l
    have e : K.em (a + ((k + 1 : ℕ) : ZMod d)) x - K.em a x ^ V.l ^ (k + 1) =
        (K.em (a + k + 1) x - K.em (a + k) x ^ V.l) + (K.em (a + k) x ^ V.l - (K.em a x ^ V.l ^ k) ^ V.l) := by
      rw [← pow_mul, ← pow_succ, Nat.cast_succ, ← add_assoc]; ring
    rw [e]
    exact mm_add h1 h2

theorem em_cong (x : O) (a : ZMod d) : V.MM (K.em a (x ^ V.l ^ d - x)) := by
  have h := em_iter K x a d
  rw [ZMod.natCast_self, add_zero] at h
  rw [map_sub, map_pow]
  have := mm_neg h
  rwa [neg_sub] at this

theorem star_S (x : O) : (V.l : C)⁻¹ • ((K.P * K.ρ x) ^ V.l ^ d - K.P * K.ρ x) ∈ Acl K := by
  obtain ⟨y, hy⟩ := K.ε_ann (x ^ V.l ^ d - x) fun a => em_cong K x a
  have hl0 : (V.l : C) ≠ 0 := V.l_ne_zero
  have hq : V.l ^ d = (V.l ^ d - 1) + 1 := (Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
    (pow_ne_zero _ V.l_prime.ne_zero))).symm
  have eM : (K.P * K.ρ x) ^ V.l ^ d - K.P * K.ρ x = K.P * (K.P * K.ρ (x ^ V.l ^ d - x)) := by
    rw [← Matrix.mul_assoc, P_idem, map_sub, Matrix.mul_sub, hq, S_pow, ← hq]
  rw [eM]
  refine ⟨fun k => K.ε ^ (V.l ^ k - 1) * y, ?_⟩
  have key : ∀ k : ℕ, K.P * K.ρ (K.ε ^ (V.l ^ k - 1) * y) =
      (V.l : C)⁻¹ • (K.ρ (K.ε ^ V.l ^ k) * (K.P * K.ρ (x ^ V.l ^ d - x))) := by
    intro k
    have hk : V.l ^ k ≠ 0 := pow_ne_zero _ V.l_prime.ne_zero
    have e1 : K.ε ^ V.l ^ k * (x ^ V.l ^ d - x) = (V.l : O) * (K.ε ^ (V.l ^ k - 1) * y) := by
      rw [← pow_sub_one_mul hk, mul_assoc, hy]; ring
    rw [← Matrix.mul_assoc, ← P_comm, Matrix.mul_assoc, ← map_mul, e1, ρ_natmul, Matrix.mul_smul, smul_smul,
      inv_mul_cancel₀ hl0, one_smul]
  have hseq : (fun k => K.P * K.ρ (K.ε ^ (V.l ^ k - 1) * y)) =
      fun k => (V.l : C)⁻¹ • (K.ρ (K.ε ^ V.l ^ k) * (K.P * K.ρ (x ^ V.l ^ d - x))) := funext key
  rw [hseq]
  exact MT.smul _ ((hPT K).mul (MT.const _))

theorem star_mem {B : Matrix (Fin n) (Fin n) C} (hB : B ∈ Acl K) : (V.l : C)⁻¹ • (B ^ V.l ^ d - B) ∈ Acl K := by
  obtain ⟨s, hs⟩ := hB
  exact closed_mem K (fun k => star_S K (s k)) (MT.smul _ ((hs.pow _).sub hs))

end RowTiePKeyEig

end Formalism.L2.FormalSeriesBounds
end
end
end

-- Source module: Formalism.LocalToGlobal.CharacterGerms.RowTiePKeyEigC

section

@[expose] public section

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

namespace RowTiePKeyEig

open RowTiePE0 RowTiePKey RowTiePProj GmExArith

variable {C : Type} [Field C] {V : VF C} {O : Type} [CommRing O] {n d : ℕ} (K : KeyData C V O n d)

theorem teich_acl (hT : TeichSt)
    (hc : ∀ s : ℕ → C, (∀ n : ℕ, V.Ge n (s (n + 1) - s n)) → ∃ x, ∀ n : ℕ, V.Ge n (x - s n)) (hd : d ≠ 0)
    {B : Matrix (Fin n) (Fin n) C} (hB : B ∈ Acl K) :
    ∃ τ ∈ Acl K, τ ^ V.l ^ d = τ ∧ ((V.l : C)⁻¹) • (B - τ) ∈ Acl K :=
  hT C V hc n d hd (Acl K) (fun _ ha _ hb => add_mem K ha hb) (fun _ ha => neg_mem K ha)
    (fun _ ha _ hb => mul_mem K ha hb) (fun _ ha _ hb => comm_mem K ha hb) (fun _ ha => int_mem K ha)
    (fun _ _ hs h => closed_mem K hs h) (fun _ ha => star_mem K ha) B hB

theorem scal (hT : TeichSt)
    (hc : ∀ s : ℕ → C, (∀ n : ℕ, V.Ge n (s (n + 1) - s n)) → ∃ x, ∀ n : ℕ, V.Ge n (x - s n)) (hd : d ≠ 0)
    {B : Matrix (Fin n) (Fin n) C} (hB : B ∈ Acl K) (w : Fin n → C)
    (hw : ∀ τ ∈ Acl K, τ ^ V.l ^ d = τ → ∃ c : C, Matrix.mulVec τ w = c • w) :
    ∃ σ : C, Matrix.mulVec B w = σ • w := by
  by_cases hw0 : w = 0
  · exact ⟨0, by rw [hw0, Matrix.mulVec_zero, smul_zero]⟩
  have ht : ∀ b : {b // b ∈ Acl K}, ∃ τ : Matrix (Fin n) (Fin n) C,
      τ ∈ Acl K ∧ τ ^ V.l ^ d = τ ∧ ((V.l : C)⁻¹) • (b.1 - τ) ∈ Acl K := by
    intro b
    obtain ⟨τ, h1, h2, h3⟩ := teich_acl K hT hc hd b.2
    exact ⟨τ, h1, h2, h3⟩
  choose tf htf using ht
  let nx : {b // b ∈ Acl K} → {b // b ∈ Acl K} := fun b => ⟨((V.l : C)⁻¹) • (b.1 - tf b), (htf b).2.2⟩
  let bs : ℕ → {b // b ∈ Acl K} := fun k => nx^[k] ⟨B, hB⟩
  have hl0 : (V.l : C) ≠ 0 := V.l_ne_zero
  have hrel : ∀ k, (bs k).1 = tf (bs k) + (V.l : C) • (bs (k + 1)).1 := by
    intro k
    show (bs k).1 = tf (bs k) + (V.l : C) • (nx^[k + 1] ⟨B, hB⟩).1
    rw [Function.iterate_succ_apply']
    show (bs k).1 = tf (bs k) + (V.l : C) • (((V.l : C)⁻¹) • ((bs k).1 - tf (bs k)))
    rw [smul_smul, mul_inv_cancel₀ hl0, one_smul]
    abel
  have hcs : ∀ k, ∃ c : C, Matrix.mulVec (tf (bs k)) w = c • w := fun k => hw _ (htf _).1 (htf _).2.1
  choose cs hcs using hcs
  have hcsi : ∀ k, V.Ge 0 (cs k) := fun k =>
    eig_int (tf (bs k)) (int_mem K (htf _).1) w hw0 (cs k) (hcs k)
  let σs : ℕ → C := fun K' => ∑ k ∈ Finset.range K', (V.l : C) ^ k * cs k
  have hid : ∀ K', Matrix.mulVec B w = σs K' • w + ((V.l : C) ^ K') • Matrix.mulVec (bs K').1 w := by
    intro K'
    induction K' with
    | zero => simp [σs, bs]
    | succ K' ih =>
      rw [ih, hrel K', Matrix.add_mulVec, Matrix.smul_mulVec, hcs K', smul_add, smul_smul, smul_smul,
        ← add_assoc, ← add_smul, ← pow_succ]
      simp only [σs, Finset.sum_range_succ]
  have hcau : ∀ N : ℕ, ∃ n0 : ℕ, ∀ m ≥ n0, V.Ge N (σs (m + 1) - σs m) := by
    intro N
    refine ⟨N, fun m hm => ?_⟩
    simp only [σs, Finset.sum_range_succ, add_sub_cancel_left]
    have := (RowTiePKeyEig.ge_lpow (V := V) m).mul (hcsi m)
    refine this.mono ?_
    have : (N : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  obtain ⟨σ, hσ⟩ := exists_tends hc hcau
  refine ⟨σ, funext fun i => ?_⟩
  rw [← sub_eq_zero]
  refine RowTiePE0.eq_zero_of_ge_all (V := V) fun r => ?_

  choose Kj hKj using fun j => exists_ge (V := V) (w j)
  set W0 : ℝ := -∑ j, |Kj j| with hW0
  have hW : ∀ j, V.Ge W0 (w j) := fun j => (hKj j).mono (by
    have h1 : |Kj j| ≤ ∑ j', |Kj j'| := Finset.single_le_sum (f := fun j' => |Kj j'|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ j)
    have h2 := neg_abs_le (Kj j)
    linarith)
  obtain ⟨n0, h0⟩ := hσ (r - W0)
  obtain ⟨N, hN⟩ := exists_nat_ge (r - W0)
  set K' := max n0 N
  have e := congrFun (hid K') i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e
  rw [e, Pi.smul_apply, smul_eq_mul]
  have e2 : σs K' * w i + (V.l : C) ^ K' * Matrix.mulVec (bs K').1 w i - σ * w i =
      -((σ - σs K') * w i) + (V.l : C) ^ K' * Matrix.mulVec (bs K').1 w i := by ring
  rw [e2]
  refine VF.Ge.add ?_ ?_
  · have := ((h0 K' (le_max_left _ _)).mul (hW i)).neg
    simpa using this
  · have hv : V.Ge W0 (Matrix.mulVec (bs K').1 w i) := by
      simp only [Matrix.mulVec, dotProduct]
      exact VF.Ge.sum fun j _ => (int_mem K (bs K').2 i j).mul_int (hW j)
    have := (RowTiePKeyEig.ge_lpow (V := V) K').mul hv
    refine this.mono ?_
    have : (N : ℝ) ≤ K' := by exact_mod_cast le_max_right n0 N
    linarith

end RowTiePKeyEig

end Formalism.L2.FormalSeriesBounds
end
end
end

-- Source module: Formalism.LocalToGlobal.CharacterGerms.RowTiePKeyEigD

section

@[expose] public section

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

namespace RowTiePKeyEig

open RowTiePE0 RowTiePKey

theorem keyEig_of (hT : TeichSt) (hJ : JointEigSt) : KeyEigSt := by
  intro C _ _ V hAlg hc O _ n d hd0 K v
  have hd : d ≠ 0 := NeZero.ne d
  have hq2 : 2 ≤ V.l ^ d := le_trans V.l_prime.two_le (Nat.le_self_pow hd _)
  obtain ⟨m, w, hsum, hw⟩ := hJ C hAlg n (V.l ^ d) hq2 {τ | τ ∈ Acl K ∧ τ ^ V.l ^ d = τ}
    (fun _ ht => ht.2) (fun _ hs _ ht => comm_mem K hs.1 ht.1) (Matrix.mulVec K.P v)
  set w' : Fin m → Fin n → C := fun j => Matrix.mulVec K.P (w j) with hw'
  have hPq : K.P ^ V.l ^ d = K.P := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (pow_ne_zero d V.l_prime.ne_zero)
    rw [hk]
    clear hk
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ih, P_idem]

  have hw'e : ∀ j, ∀ τ ∈ Acl K, τ ^ V.l ^ d = τ → ∃ c : C, Matrix.mulVec τ (w' j) = c • w' j := by
    intro j τ hτ hτq
    obtain ⟨c, hc'⟩ := hw j τ ⟨hτ, hτq⟩
    refine ⟨c, ?_⟩
    rw [hw', Matrix.mulVec_mulVec, comm_mem K hτ (P_mem K), ← Matrix.mulVec_mulVec, hc', Matrix.mulVec_smul]
  have hPw' : ∀ j, Matrix.mulVec K.P (w' j) = w' j := fun j => by
    rw [hw', Matrix.mulVec_mulVec, P_idem]
  have hρ : ∀ j x, ∃ σ : C, Matrix.mulVec (K.ρ x) (w' j) = σ • w' j := by
    intro j x
    obtain ⟨σ, hσ⟩ := scal K hT hc hd (S_mem K x) (w' j) (hw'e j)
    refine ⟨σ, ?_⟩
    rw [← hPw' j, Matrix.mulVec_mulVec, ← P_comm, hPw' j]
    exact hσ
  have hχ : ∀ j, ∃ χ : O →+* C, ∀ x, Matrix.mulVec (K.ρ x) (w' j) = χ x • w' j := by
    intro j
    by_cases h0 : w' j = 0
    · exact ⟨K.em 0, fun x => by rw [h0, Matrix.mulVec_zero, smul_zero]⟩
    choose σ hσ using hρ j
    have uniq : ∀ a b : C, a • w' j = b • w' j → a = b := fun a b h => smul_left_injective C h0 h
    refine ⟨{ toFun := σ, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, hσ⟩
    · exact uniq _ _ (by rw [← hσ 1, map_one, Matrix.one_mulVec, one_smul])
    · intro x y
      refine uniq _ _ ?_
      rw [← hσ (x * y), map_mul, ← Matrix.mulVec_mulVec, hσ y, Matrix.mulVec_smul, hσ x, smul_smul, mul_comm]
    · exact uniq _ _ (by rw [← hσ 0, map_zero, Matrix.zero_mulVec, zero_smul])
    · intro x y
      refine uniq _ _ ?_
      rw [← hσ (x + y), map_add (f := _), Matrix.add_mulVec, hσ x, hσ y, add_smul]
  choose χ hχ using hχ
  refine ⟨m, w', χ, ?_, fun j => ⟨hPw' j, hχ j⟩⟩
  rw [hw', ← Matrix.mulVec_sum, ← hsum, Matrix.mulVec_mulVec, P_idem]

end RowTiePKeyEig

end Formalism.L2.FormalSeriesBounds
end
end
end

-- Source module: Formalism.LocalToGlobal.CharacterGerms.RowTiePKeyJoint

section

@[expose] public section

namespace Formalism.L2.FormalSeriesBounds

namespace RowTiePKey

section Eig

variable {C : Type} [Field C] [CharZero C] {n : ℕ}

theorem sq_to_eig {q : ℕ} (hq : 2 ≤ q) (t : Matrix (Fin n) (Fin n) C) (ht : t ^ q = t) (μ : C) (u : Fin n → C)
    (h2 : Matrix.mulVec t (Matrix.mulVec t u - μ • u) = μ • (Matrix.mulVec t u - μ • u)) :
    Matrix.mulVec t u = μ • u := by
  set x := Matrix.mulVec t u - μ • u with hxdef
  have htu : Matrix.mulVec t u = μ • u + x := by rw [hxdef]; abel
  have hx : ∀ k : ℕ, Matrix.mulVec (t ^ k) x = μ ^ k • x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ' t k, ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, h2, smul_smul, ← pow_succ]
  have hu : ∀ k : ℕ, Matrix.mulVec (t ^ (k + 1)) u = μ ^ (k + 1) • u + (((k : C) + 1) * μ ^ k) • x := by
    intro k
    induction k with
    | zero => simp [htu]
    | succ k ih =>
      rw [pow_succ' t (k + 1), ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_add, Matrix.mulVec_smul,
        Matrix.mulVec_smul, htu, h2]
      push_cast
      module
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 2 := ⟨q - 2, by omega⟩
  have hA := hu (r + 1)
  rw [show r + 1 + 1 = r + 2 from rfl, ht, htu] at hA
  have hB := hx (r + 2)
  rw [ht, h2] at hB
  suffices hx0 : x = 0 by rw [htu, hx0, add_zero]
  by_cases hμ : μ = 0
  · subst hμ
    simp at hA
    exact hA
  · have hB' : (μ ^ (r + 2) - μ) • x = 0 := by rw [sub_smul, ← hB, sub_self]
    rcases smul_eq_zero.mp hB' with h | h
    · have h1 : μ ^ (r + 1) = 1 := by
        have e1 : μ ^ (r + 1) * μ = 1 * μ := by
          rw [← pow_succ, one_mul]
          exact sub_eq_zero.mp h
        exact mul_right_cancel₀ hμ e1
      rw [sub_eq_zero.mp h, h1, mul_one] at hA
      have hA2 := add_left_cancel hA
      have e : (((r + 1 : ℕ) : C) + 1) • x = ((r : C) + 1) • x + x := by
        push_cast
        rw [add_smul, one_smul]
      rw [e] at hA2
      have h3 : ((r : C) + 1) • x = 0 := add_eq_right.mp hA2.symm
      exact (smul_eq_zero.mp h3).resolve_left (Nat.cast_add_one_ne_zero r)
    · exact h

theorem gen_to_eig {q : ℕ} (hq : 2 ≤ q) (t : Matrix (Fin n) (Fin n) C) (ht : t ^ q = t) (μ : C) (w : Fin n → C)
    (hw : w ∈ Module.End.maxGenEigenspace (Matrix.toLin' t : Module.End C (Fin n → C)) μ) : Matrix.mulVec t w = μ • w := by
  rw [Module.End.mem_maxGenEigenspace] at hw
  obtain ⟨k, hk⟩ := hw
  induction k generalizing w with
  | zero =>
    simp only [pow_zero, Module.End.one_apply] at hk
    subst hk
    simp
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply] at hk
    have hy := ih _ hk
    have e : (Matrix.toLin' t - μ • (1 : Module.End C (Fin n → C))) w = Matrix.mulVec t w - μ • w := by
      simp [Matrix.toLin'_apply]
    rw [e] at hy
    exact sq_to_eig hq t ht μ w hy

end Eig

theorem jointEig_holds : JointEigSt := by
  intro C _ _ hC n q hq T hT hcomm v
  let f : T → Module.End C (Fin n → C) := fun t => Matrix.toLin' t.1
  have htop := Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute f
    (fun i j _ => by
      show (Matrix.toLin' i.1).comp (Matrix.toLin' j.1) = (Matrix.toLin' j.1).comp (Matrix.toLin' i.1)
      rw [← Matrix.toLin'_mul, ← Matrix.toLin'_mul, hcomm i.1 i.2 j.1 j.2])
    (fun i => Module.End.iSup_maxGenEigenspace_eq_top (f i))
  have hv : v ∈ ⨆ χ : T → C, ⨅ i, (f i).maxGenEigenspace (χ i) := by
    rw [htop]
    exact Submodule.mem_top
  refine Submodule.iSup_induction _ (motive := fun v => ∃ (m : ℕ) (w : Fin m → Fin n → C),
    v = ∑ j, w j ∧ ∀ j, ∀ t ∈ T, ∃ c : C, Matrix.mulVec t (w j) = c • w j) hv ?_ ?_ ?_
  · intro χ x hx
    refine ⟨1, fun _ => x, by simp, fun _ t ht => ⟨χ ⟨t, ht⟩, gen_to_eig hq t (hT t ht) _ x ?_⟩⟩
    exact (Submodule.mem_iInf _).mp hx ⟨t, ht⟩
  · exact ⟨0, Fin.elim0, by simp, fun j => Fin.elim0 j⟩
  · rintro x y ⟨m₁, w₁, rfl, h₁⟩ ⟨m₂, w₂, rfl, h₂⟩
    refine ⟨m₁ + m₂, Fin.append w₁ w₂, by rw [Fin.sum_univ_add]; simp, fun j => ?_⟩
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simpa using h₁ j
    · simpa using h₂ j

end RowTiePKey

end Formalism.L2.FormalSeriesBounds
end
end

-- Source module: Formalism.LocalToGlobal.CharacterGerms.RowTiePKeyEig2

section

@[expose] public section

namespace Formalism.L2.FormalSeriesBounds

namespace RowTiePKey

theorem keyEig_holds : KeyEigSt := RowTiePKeyEig.keyEig_of RowTiePKeyTeich.teich_holds jointEig_holds

end RowTiePKey

end Formalism.L2.FormalSeriesBounds
end
end
