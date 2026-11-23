module

public import Formalism.GradedWeylDivisibility.StatementE
public import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.TransposeVariables
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LClosedeqLemmas
public import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.CoeffTransposeVariables
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Sheaves.Init
public import Formalism.GradedWeylDivisibility.StatementC
public import Formalism.GradedWeylDivisibility.FinalC
public import Formalism.GradedWeylDivisibility.FinalD
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LCassemLemmas
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.NablaLKBasis
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.HaveILetI
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QnPtEmpty
import Mathlib.Tactic.Linter.Style

-- Source module: Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QnFactRowDivDiag

section

@[expose] public section

open MvPolynomial

noncomputable section

namespace Formalism.InvariantFactorPaths.ColumnFamilies

open Formalism.GradedWeylDivisibility

theorem qn_rowDiv_zero (n : ℕ) (a b : Fin n) (F : MvPolynomial (Fin n × Fin n) ℚ) :
    rowDiv ℚ a b 0 F = F := by
  unfold rowDiv
  rw [Polynomial.coeff_zero_eq_eval_zero]
  have h : (Polynomial.evalRingHom (0 : MvPolynomial (Fin n × Fin n) ℚ)).comp
      (rowGen ℚ (r := n) (n := n) a b).toRingHom =
      RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [rowGen]
    · intro v
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, rowGen, aeval_X,
        Polynomial.coe_evalRingHom, Polynomial.eval_add, Polynomial.eval_C, RingHom.id_apply]
      split_ifs <;> simp
  have h2 := RingHom.congr_fun h F
  simpa using h2

theorem qn_natsmul (n : ℕ) (k : ℕ) (p : MvPolynomial (Fin n × Fin n) ℚ) :
    p * ((k : MvPolynomial (Fin n × Fin n) ℚ) + 1) = ((k + 1 : ℕ) : ℚ) • p := by
  rw [MvPolynomial.smul_eq_C_mul, mul_comm]
  congr 1
  simp

theorem qn_rowDiv_succ (n : ℕ) (a b : Fin n) (hab : a ≠ b) (k : ℕ) (f : MvPolynomial (Fin n × Fin n) ℚ) :
    ((k + 1 : ℕ) : ℚ) • rowDiv ℚ a b (k + 1) (transposeVariables ℚ n f) = rowDiv ℚ a b k (transposeVariables ℚ n (qn_D n a b f)) := by
  unfold rowDiv
  rw [← qn_deriv_rowGen n a b hab f, Polynomial.coeff_derivative, qn_natsmul]

theorem qn_rowDiv_succ_diag (n : ℕ) (a : Fin n) (k : ℕ) (f : MvPolynomial (Fin n × Fin n) ℚ) :
    ((k + 1 : ℕ) : ℚ) • rowDiv ℚ a a (k + 1) (transposeVariables ℚ n f) =
      rowDiv ℚ a a k (transposeVariables ℚ n (qn_D n a a f - (k : ℚ) • f)) := by
  unfold rowDiv
  rw [map_sub, map_smul, map_sub, map_smul, ← qn_deriv_rowGen_diag n a f, Polynomial.coeff_sub,
    Polynomial.coeff_smul, add_mul, one_mul, Polynomial.coeff_add]
  cases k with
  | zero =>
    rw [Polynomial.coeff_X_mul_zero, Polynomial.coeff_derivative]
    simp
  | succ m =>
    rw [Polynomial.coeff_X_mul, Polynomial.coeff_derivative, Polynomial.coeff_derivative]
    simp only [MvPolynomial.smul_eq_C_mul, map_natCast, Nat.cast_add, Nat.cast_one, map_add (f := _), map_one]
    ring

theorem qn_fact_rowDiv (n : ℕ) (a b : Fin n) (hab : a ≠ b) (k : ℕ) :
    ∀ f : MvPolynomial (Fin n × Fin n) ℚ,
    (k.factorial : ℚ) • rowDiv ℚ a b k (transposeVariables ℚ n f) =
      transposeVariables ℚ n (((glOps ℚ n (rowLetters n) Set.univ a b) ^ k) f) := by
  induction k with
  | zero =>
    intro f
    simp [qn_rowDiv_zero]
  | succ k ih =>
    intro f
    rw [Nat.factorial_succ, Nat.cast_mul, mul_comm ((k + 1 : ℕ) : ℚ), mul_smul, qn_rowDiv_succ n a b hab k f,
      ih, pow_succ, Module.End.mul_apply, qn_E_eq]

theorem qn_T_divPowE (n : ℕ) (a b : Fin n) (hab : a ≠ b) (k : ℕ) (f : MvPolynomial (Fin n × Fin n) ℚ) :
    transposeVariables ℚ n (divPowE (glOps ℚ n (rowLetters n) Set.univ) a b k f) = rowDiv ℚ a b k (transposeVariables ℚ n f) := by
  have hk : (k.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero k)
  rw [divPowE, LinearMap.smul_apply, map_smul, ← qn_fact_rowDiv n a b hab k f, smul_smul,
    inv_mul_cancel₀ hk, one_smul]

theorem qn_fact_rowDiv_diag (n : ℕ) (a : Fin n) (k : ℕ) :
    ∀ f : MvPolynomial (Fin n × Fin n) ℚ,
    (k.factorial : ℚ) • rowDiv ℚ a a k (transposeVariables ℚ n f) =
      transposeVariables ℚ n ((((List.range k).map fun j : ℕ => glOps ℚ n (rowLetters n) Set.univ a a -
        (j : ℚ) • (1 : Module.End ℚ (MvPolynomial (Fin n × Fin n) ℚ))).prod) f) := by
  induction k with
  | zero =>
    intro f
    simp [qn_rowDiv_zero]
  | succ k ih =>
    intro f
    rw [List.range_succ, List.map_append, List.prod_append, List.map_singleton, List.prod_singleton,
      Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, qn_E_eq, ← ih,
      Nat.factorial_succ, Nat.cast_mul, mul_comm ((k + 1 : ℕ) : ℚ), mul_smul, qn_rowDiv_succ_diag]

theorem qn_T_binomE (n : ℕ) (a : Fin n) (k : ℕ) (f : MvPolynomial (Fin n × Fin n) ℚ) :
    transposeVariables ℚ n (binomE (glOps ℚ n (rowLetters n) Set.univ) a k f) = rowDiv ℚ a a k (transposeVariables ℚ n f) := by
  have hk : (k.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero k)
  rw [binomE, LinearMap.smul_apply, map_smul, ← qn_fact_rowDiv_diag n a k f, smul_smul,
    inv_mul_cancel₀ hk, one_smul]

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end
end

-- Source module: Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QnInterlacedLowerTri

section

@[expose] public section

open MvPolynomial

namespace Formalism.InvariantFactorPaths.ColumnFamilies

open Formalism.GradedWeylDivisibility
open scoped MonomialOrder

theorem qn_interlaced_lowerTri {r n : ℕ} (m : Fin r × Fin n →₀ ℕ) (h : Interlaced m) : LowerTri m := by
  have key : ∀ k : ℕ, ∀ s : Fin n, s.val = k → ∀ a : Fin r, a.val < k → m (a, s) = 0 := by
    intro k
    induction k with
    | zero =>
      intro s _ a ha
      omega
    | succ k ih =>
      intro s hs a ha
      have hl : k < n := by
        have := s.isLt
        omega
      have hI := h ⟨k, hl⟩ s (by simp [hs]) a
      have hR : (∑ b : Fin r with b < a, m (b, (⟨k, hl⟩ : Fin n))) = 0 := by
        apply Finset.sum_eq_zero
        intro b hb
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
        have hba : b.val < a.val := hb
        exact ih ⟨k, hl⟩ rfl b (by omega)
      rw [hR, add_zero, Nat.le_zero, Finset.sum_eq_zero_iff] at hI
      exact hI a (by simp)
  intro a s has
  exact key s.val s rfl a has

theorem qn_lowerTriIntegral : LowerTriIntegral := by
  classical
  intro r n ν
  haveI := (colLex r n).wellFoundedLT_syn
  obtain ⟨b, hbB, hbdeg⟩ := sSBasis ℤ r n ν
  have hBmem : ∀ i, intQ r n (b i) ∈ dualWeyl ℚ r n ν := by
    intro i
    rw [← span_map_weightBasis_eq_dualWeyl (K := ℚ) hbB]
    apply Submodule.subset_span
    exact ⟨i, by rw [algebraMap_int_eq]; rfl⟩
  suffices H : ∀ s : (colLex r n).syn, ∀ Q : MvPolynomial (Fin r × Fin n) ℚ,
      (colLex r n).toSyn ((colLex r n).degree Q) = s → Q ∈ dualWeyl ℚ r n ν →
      (∀ e : Fin r × Fin n →₀ ℕ, LowerTri e → ∃ z : ℤ, AddMonoidAlgebra.coeff Q e = z) →
      ∃ Q' : MvPolynomial (Fin r × Fin n) ℤ, Q = intQ r n Q' by
    intro Q hQ hint
    exact H _ Q rfl hQ hint
  intro s
  induction s using WellFoundedLT.induction with
  | ind s ih =>
    intro Q hs hQ hint
    by_cases hQ0 : Q = 0
    · exact ⟨0, by rw [hQ0, map_zero]⟩
    set m := (colLex r n).degree Q with hm
    have hInt : Interlaced m := leadInterlaced ℚ r n ν Q hQ hQ0
    have hLT : LowerTri m := qn_interlaced_lowerTri m hInt
    have hcol : ∀ t : Fin n, ∑ a : Fin r, m (a, t) = ν t := by
      have hhom : IsWeightedHomogeneous (colW r n) Q ν :=
        (mem_weightedHomogeneousSubmodule _ _ _ _).1 (Submodule.mem_inf.1 hQ).1
      have hw : Finsupp.weight (colW r n) m = ν :=
        hhom ((colLex r n).leadingCoeff_ne_zero_iff.2 hQ0)
      intro t
      rw [← hw]
      simp [Finsupp.weight_apply, Finsupp.sum_fintype, Fintype.sum_prod_type, colW, Pi.single_apply]
    let mi : ssIdx r n ν := ⟨m, hInt, hcol⟩
    obtain ⟨hbd, hblc, -⟩ := hbdeg mi
    set B := intQ r n (b mi) with hB
    have hBmap : B = map (Int.castRingHom ℚ) (b mi) := rfl
    have hinj : Function.Injective (Int.castRingHom ℚ) := Int.cast_injective
    have hBsupp : B.support = (b mi).support := by
      rw [hBmap]
      exact support_map_of_injective _ hinj
    have hBdeg : (colLex r n).degree B = m := by
      have h1 : (colLex r n).degree (b mi) = m := hbd
      rw [← h1]
      unfold MonomialOrder.degree
      rw [hBsupp]
    have hBlc : (colLex r n).leadingCoeff B = 1 := by
      unfold MonomialOrder.leadingCoeff
      rw [hBdeg, hBmap, coeff_map]
      have h1 : (colLex r n).degree (b mi) = m := hbd
      have h2 : (b mi).coeff ((colLex r n).degree (b mi)) = 1 := hblc
      rw [h1] at h2
      rw [h2, map_one]
    obtain ⟨z, hz⟩ := hint m hLT
    have hlcQ : (colLex r n).leadingCoeff Q = (z : ℚ) := hz
    set Q1 := Q - (colLex r n).leadingCoeff Q • B with hQ1
    have hQ1mem : Q1 ∈ dualWeyl ℚ r n ν :=
      Submodule.sub_mem _ hQ (Submodule.smul_mem _ _ (hBmem mi))
    have hQ1int : ∀ e : Fin r × Fin n →₀ ℕ, LowerTri e → ∃ z' : ℤ, AddMonoidAlgebra.coeff Q1 e = z' := by
      intro e he
      obtain ⟨w, hw⟩ := hint e he
      refine ⟨w - z * (b mi).coeff e, ?_⟩
      rw [hQ1, MvPolynomial.coeff_sub, MvPolynomial.coeff_smul, hw, hlcQ, hBmap, coeff_map]
      push_cast
      simp [smul_eq_mul]
    have hfinal : ∀ Q1' : MvPolynomial (Fin r × Fin n) ℤ, Q1 = intQ r n Q1' →
        ∃ Q' : MvPolynomial (Fin r × Fin n) ℤ, Q = intQ r n Q' := by
      intro Q1' h
      refine ⟨Q1' + z • b mi, ?_⟩
      rw [map_add (f := _), map_zsmul, ← h, ← hB, hQ1, hlcQ, Int.cast_smul_eq_zsmul]
      abel
    by_cases hQ10 : Q1 = 0
    · exact hfinal 0 (by rw [hQ10, map_zero])
    · have hlt := lcassem_sub_lt (colLex r n) (hBdeg.trans hm) hBlc hQ10
      obtain ⟨Q1', h⟩ := ih _ (by rw [← hs]; exact hlt) Q1 rfl hQ1mem hQ1int
      exact hfinal Q1' h

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

-- Source module: Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QnEvalMap

section

@[expose] public section

open MvPolynomial

noncomputable section

namespace Formalism.InvariantFactorPaths.ColumnFamilies

open Formalism.GradedWeylDivisibility

def qn_InZ (n : ℕ) (ν : Fin n → ℕ) (x : MvPolynomial (Fin n × Fin n) ℚ) : Prop :=
  ∃ Y ∈ dualWeyl ℤ n n ν, transposeVariables ℚ n x = map (Int.castRingHom ℚ) Y

theorem qn_eval_map (n : ℕ) (Y : MvPolynomial (Fin n × Fin n) ℤ) :
    eval (idFrame ℚ n n) (map (Int.castRingHom ℚ) Y) = ((eval (idFrame ℤ n n) Y : ℤ) : ℚ) := by
  have h : (eval (idFrame ℚ n n)).comp (map (Int.castRingHom ℚ)) =
      (Int.castRingHom ℚ).comp (eval (idFrame ℤ n n)) := by
    apply MvPolynomial.ringHom_ext
    · intro c; simp
    · intro v
      simp only [RingHom.coe_comp, Function.comp_apply, map_X, eval_X, idFrame]
      split_ifs <;> simp
  exact congrArg (fun φ => φ Y) h

theorem qn_InZ_UZ (n : ℕ) (ν : Fin n → ℕ) (u : Module.End ℚ (MvPolynomial (Fin n × Fin n) ℚ))
    (hu : u ∈ UZmon (glOps ℚ n (rowLetters n) Set.univ)) :
    ∀ x, qn_InZ n ν x → qn_InZ n ν (u x) := by
  unfold UZmon at hu
  induction hu using Submonoid.closure_induction with
  | mem g hg =>
    rintro x ⟨Y, hY, hx⟩
    rcases hg with ⟨a, b, k, hab, rfl⟩ | ⟨a, k, rfl⟩
    · exact ⟨rowDiv ℤ a b k Y, rowDivStable ℤ n n ν a b k Y hY, by
        rw [qn_T_divPowE n a b hab, hx, lclosedeq_rowDiv_map]⟩
    · exact ⟨rowDiv ℤ a a k Y, rowDivStable ℤ n n ν a a k Y hY, by
        rw [qn_T_binomE, hx, lclosedeq_rowDiv_map]⟩
  | one => intro x hx; exact hx
  | mul g h _ _ ihg ihh => intro x hx; exact ihg _ (ihh x hx)

theorem qn_InZ_span (n : ℕ) (ν : Fin n → ℕ) {ι : Type} (P : ι → MvPolynomial (Fin n × Fin n) ℤ)
    (h1 : ∀ i, transposeVariables ℤ n (P i) ∈ dualWeyl ℤ n n ν) (x : MvPolynomial (Fin n × Fin n) ℚ)
    (hx : x ∈ Submodule.span ℤ (Set.range fun i => map (Int.castRingHom ℚ) (P i))) : qn_InZ n ν x := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact ⟨_, h1 i, qn_T_map n (P i)⟩
  | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨Y1, h1, e1⟩ := hx
    obtain ⟨Y2, h2, e2⟩ := hy
    exact ⟨Y1 + Y2, Submodule.add_mem _ h1 h2, by rw [map_add (f := _), map_add (f := _), e1, e2]⟩
  | smul c x _ hx =>
    obtain ⟨Y1, h1, e1⟩ := hx
    exact ⟨c • Y1, Submodule.smul_mem _ _ h1, by rw [map_zsmul, map_zsmul, e1]⟩

theorem qn_main (n : ℕ) (ν : Fin n → ℕ) (hν : Antitone ν) {ι : Type}
    (P : ι → MvPolynomial (Fin n × Fin n) ℤ) (i0 : ι)
    (h1 : ∀ i, transposeVariables ℤ n (P i) ∈ dualWeyl ℤ n n ν)
    (h2 : dualWeyl ℤ n n ν ≤ Submodule.span ℤ (Set.range fun i => transposeVariables ℤ n (P i)))
    (h3 : eval (idFrame ℤ n n) (transposeVariables ℤ n (P i0)) = 1) :
    (Submodule.span ℤ (Set.range fun i => map (Int.castRingHom ℚ) (P i)) :
        Set (MvPolynomial (Fin n × Fin n) ℚ)) =
      {x | x ∈ Submodule.span ℚ (Set.range fun i => map (Int.castRingHom ℚ) (P i)) ∧
        x ∈ Nabla (O := ℤ) (glOps ℚ n (rowLetters n) Set.univ) (fun a => (ν a : ℤ))
          (map (Int.castRingHom ℚ) (P i0))} := by
  classical
  set v := map (Int.castRingHom ℚ) (P i0) with hv
  have hTv : transposeVariables ℚ n v = map (Int.castRingHom ℚ) (transposeVariables ℤ n (P i0)) := qn_T_map n (P i0)
  have hTvmem : transposeVariables ℚ n v ∈ dualWeyl ℚ n n ν := by
    rw [hTv]; exact dualWeylMap ℤ ℚ _ n n ν _ (h1 i0)
  have hTvev : eval (idFrame ℚ n n) (transposeVariables ℚ n v) = 1 := by
    rw [hTv, qn_eval_map, h3, Int.cast_one]
  ext x
  simp only [SetLike.mem_coe, Set.mem_setOf_eq]
  constructor
  · intro hx
    refine ⟨Submodule.span_le_restrictScalars ℤ ℚ _ hx, ?_⟩
    intro u hu
    obtain ⟨Y, hY, hy⟩ := qn_InZ_UZ n ν u hu x (qn_InZ_span n ν P h1 x hx)
    refine ⟨eval (idFrame ℤ n n) Y, ?_⟩
    apply qn_mem_otherWts'
    have hYQ : transposeVariables ℚ n (u x) ∈ dualWeyl ℚ n n ν := by
      rw [hy]; exact dualWeylMap ℤ ℚ _ n n ν _ hY
    rw [map_sub, map_smul, map_sub, map_smul, qn_comp n ν hν _ hYQ, qn_comp n ν hν _ hTvmem, hTvev, hy,
      qn_eval_map, one_smul, eq_intCast, sub_self]
  · rintro ⟨hxQ, hxN⟩
    have hxD : transposeVariables ℚ n x ∈ dualWeyl ℚ n n ν := by
      have hle : Submodule.span ℚ (Set.range fun i => map (Int.castRingHom ℚ) (P i)) ≤
          (dualWeyl ℚ n n ν).comap (transposeVariables ℚ n).toLinearMap := by
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        show transposeVariables ℚ n (map (Int.castRingHom ℚ) (P i)) ∈ dualWeyl ℚ n n ν
        rw [qn_T_map]
        exact dualWeylMap ℤ ℚ _ n n ν _ (h1 i)
      exact hle hxQ
    set W : Set (MvPolynomial (Fin n × Fin n) ℚ) :=
      {F | ∃ y, F = transposeVariables ℚ n y ∧ transposeVariables ℚ n y ∈ dualWeyl ℚ n n ν ∧
        y ∈ Nabla (O := ℤ) (glOps ℚ n (rowLetters n) Set.univ) (fun a => (ν a : ℤ)) v} with hWdef
    have hW : ∀ F ∈ W, ∀ (a b : Fin n) (k : ℕ), a ≠ b → rowDiv ℚ a b k F ∈ W := by
      rintro F ⟨y, rfl, hyD, hyN⟩ a b k hab
      refine ⟨divPowE (glOps ℚ n (rowLetters n) Set.univ) a b k y, (qn_T_divPowE n a b hab k y).symm, ?_, ?_⟩
      · rw [qn_T_divPowE n a b hab]
        exact rowDivStable ℚ n n ν a b k _ hyD
      · intro u hu
        have hg : divPowE (glOps ℚ n (rowLetters n) Set.univ) a b k ∈
            UZmon (glOps ℚ n (rowLetters n) Set.univ) :=
          Submonoid.subset_closure (Or.inl ⟨a, b, k, hab, rfl⟩)
        exact hyN (u * divPowE (glOps ℚ n (rowLetters n) Set.univ) a b k) (Submonoid.mul_mem _ hu hg)
    have hev : ∀ F ∈ W, ∃ z : ℤ, eval (idFrame ℚ n n) F = z := by
      rintro F ⟨y, rfl, hyD, hyN⟩
      obtain ⟨c, hc⟩ := hyN 1 (Submonoid.one_mem _)
      refine ⟨c, ?_⟩
      have h := qn_otherWts_coeff' n ν _ hc
      rw [Module.End.one_apply, map_sub, map_smul, MvPolynomial.coeff_sub, MvPolynomial.coeff_smul,
        ← qn_eval_eq_coeff n ν _ (qn_colHom ℚ n ν _ hyD), ← qn_eval_eq_coeff n ν _ (qn_colHom ℚ n ν _ hTvmem),
        hTvev, smul_eq_mul, mul_one, eq_intCast, sub_eq_zero] at h
      exact h
    have hcol : ∀ F ∈ W, IsWeightedHomogeneous (colW n n) F ν := by
      rintro F ⟨y, rfl, hyD, _⟩
      exact qn_colHom ℚ n ν _ hyD
    have htri := qn_tri n ν W hW hev hcol (transposeVariables ℚ n x) ⟨x, rfl, hxD, hxN⟩
    obtain ⟨Q', hQ'⟩ := qn_lowerTriIntegral n n ν (transposeVariables ℚ n x) hxD htri
    have hQ'' : transposeVariables ℚ n x = map (Int.castRingHom ℚ) Q' := hQ'
    have hQmem : Q' ∈ dualWeyl ℤ n n ν := (dualWeylIntRat n n ν Q').mpr (hQ'' ▸ hxD)
    have hQs := h2 hQmem
    set φ : MvPolynomial (Fin n × Fin n) ℤ →ₗ[ℤ] MvPolynomial (Fin n × Fin n) ℚ :=
      (intQ n n).comp (transposeVariables ℤ n).toLinearMap with hφ
    have hφx : φ Q' = x := by
      show map (Int.castRingHom ℚ) (transposeVariables ℤ n Q') = x
      rw [← qn_T_map, ← hQ'', transposeVariables_involutive]
    have hx := Submodule.mem_map_of_mem (f := φ) hQs
    rw [Submodule.map_span, hφx] at hx
    refine Submodule.span_mono ?_ hx
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    refine ⟨i, ?_⟩
    show _ = map (Int.castRingHom ℚ) (transposeVariables ℤ n (transposeVariables ℤ n (P i)))
    rw [transposeVariables_involutive]

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end
end
