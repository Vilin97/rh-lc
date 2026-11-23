module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.InstDecomp
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.InstDefs
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.InstAdapt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.Linter.Style
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
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.HJMulVecGen
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.InstExp
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.InstPlace
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.InstTop

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.AdaptedBasisInstance

section

@[expose] public section

noncomputable section

open Matrix

namespace PI.ScMuExists.UnitaryGroupMassFormula

theorem adapted_basis_instance : InstAdaptBasis := by
  intro n ε ι _ _ B hG
  have hJJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
    simp only [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal]
    rw [← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> norm_num
  have hJs : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := by
    simp only [Formalism.REAL.Jm, Matrix.diagonal_conjTranspose]
    congr 1
    funext a
    by_cases h : ε a <;> simp [h]
  set J := Formalism.REAL.Jm ε with hJdef
  set G := Bᴴ * J * B with hGdef
  have hdet : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).mp hG
  have hGi : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul G hdet
  have hGh : Gᴴ = G := by
    rw [hGdef, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hJs, Matrix.mul_assoc]
  have hGih : (G⁻¹)ᴴ = G⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, hGh]
  set Q := B * G⁻¹ * Bᴴ * J with hQdef
  have hQB : Q * B = B := by
    calc Q * B = B * (G⁻¹ * (Bᴴ * J * B)) := by simp only [hQdef, Matrix.mul_assoc]
      _ = B := by rw [← hGdef, hGi, Matrix.mul_one]
  have hQQ : Q * Q = Q := by
    calc Q * Q = (Q * B) * (G⁻¹ * Bᴴ * J) := by simp only [hQdef, Matrix.mul_assoc]
      _ = Q := by rw [hQB]; simp only [hQdef, Matrix.mul_assoc]
  have hQJ : Qᴴ * J = J * Q := by
    simp only [hQdef, Matrix.conjTranspose_mul, hJs, hGih, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc]
  set P := 1 - Q with hPdef
  have hPP : P * P = P := by
    simp only [hPdef, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hQQ]
    abel
  have hPJ : Pᴴ * J = J * P := by
    rw [hPdef, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.sub_mul, Matrix.mul_sub, hQJ,
      Matrix.one_mul, Matrix.mul_one]
  have hQP : Q * P = 0 := by rw [hPdef, Matrix.mul_sub, Matrix.mul_one, hQQ, sub_self]
  have hPQ : P * Q = 0 := by rw [hPdef, Matrix.sub_mul, Matrix.one_mul, hQQ, sub_self]
  obtain ⟨W1, l1, hW1J, hQW1, hsp1, hcard1, -⟩ := inst_qfamily ε Q hQQ hQJ
  obtain ⟨W2, l2, hW2J, hPW2, -, hcard2, -⟩ := inst_qfamily ε P hPP hPJ
  have hcross : W1ᴴ * J * W2 = 0 := by
    calc W1ᴴ * J * W2 = (Q * W1)ᴴ * J * (P * W2) := by rw [hQW1, hPW2]
      _ = W1ᴴ * (Qᴴ * J) * P * W2 := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = 0 := by
        rw [hQJ]
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc Q P, hQP]
        simp
  have hcross' : W2ᴴ * J * W1 = 0 := by
    calc W2ᴴ * J * W1 = (P * W2)ᴴ * J * (Q * W1) := by rw [hQW1, hPW2]
      _ = W2ᴴ * (Pᴴ * J) * Q * W1 := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = 0 := by
        rw [hPJ]
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc P Q, hPQ]
        simp
  have hrk : Q.rank + P.rank = n := by
    apply le_antisymm
    · have h1 : LinearMap.range P.mulVecLin ≤ LinearMap.ker Q.mulVecLin := by
        rintro _ ⟨x, rfl⟩
        rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec,
          hQP, Matrix.zero_mulVec]
      have h2 := LinearMap.finrank_range_add_finrank_ker Q.mulVecLin
      have h3 := Submodule.finrank_mono h1
      have h4 : Module.finrank ℂ (Fin n → ℂ) = n := by
        first
          | exact Module.finrank_fin_fun ℂ
          | simp
      simp only [← Matrix.finrank_range_mulVecLin]
      omega
    · have h := inst_rank_add_le Q P
      have hsum : Q + P = 1 := by rw [hPdef]; abel
      rw [hsum, Matrix.rank_one, Fintype.card_fin] at h
      exact h
  have hcardsum : Fintype.card ({i // l1 i ≠ 0} ⊕ {i // l2 i ≠ 0}) = n := by
    refine Eq.trans ?_ hrk
    rw [Fintype.card_sum]
    convert congrArg₂ (· + ·) hcard1 hcard2 using 2
  obtain ⟨e⟩ : Nonempty (Fin n ≃ ({i // l1 i ≠ 0} ⊕ {i // l2 i ≠ 0})) :=
    ⟨(Fintype.equivFinOfCardEq hcardsum).symm⟩
  obtain ⟨A, hAe⟩ : ∃ A : Matrix (Fin n) (Fin n) ℂ, ∀ r k, A r k =
      Sum.elim (fun j : {i // l1 i ≠ 0} => W1 r j) (fun j : {i // l2 i ≠ 0} => W2 r j) (e k) :=
    ⟨Matrix.of fun r k =>
      Sum.elim (fun j : {i // l1 i ≠ 0} => W1 r j) (fun j : {i // l2 i ≠ 0} => W2 r j) (e k),
      fun _ _ => rfl⟩
  obtain ⟨ε', hε'⟩ : ∃ ε' : Fin n → Bool, ∀ k, ε' k =
      Sum.elim (fun j : {i // l1 i ≠ 0} => decide (0 < l1 j))
        (fun j : {i // l2 i ≠ 0} => decide (0 < l2 j)) (e k) :=
    ⟨fun k => Sum.elim (fun j : {i // l1 i ≠ 0} => decide (0 < l1 j))
        (fun j : {i // l2 i ≠ 0} => decide (0 < l2 j)) (e k), fun _ => rfl⟩
  have hcol : ∀ (M : Matrix (Fin n) (Fin n) ℂ) (k : Fin n), M *ᵥ Pi.single k 1 = fun r => M r k := by
    intro M k
    funext r
    simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
  refine ⟨A, ε', Finset.univ.filter (fun k => (e k).isLeft = true), ?_, ?_, ?_⟩
  · ext k k'
    rw [inst_gram_entry]
    simp only [Formalism.REAL.Jm, Matrix.diagonal_apply, hAe, hε']
    rcases hk : e k with j | j <;> rcases hk' : e k' with j' | j' <;>
      simp only [Sum.elim_inl, Sum.elim_inr]
    · rw [← inst_gram_entry W1 J W1 (j : Fin n) j', hW1J, Matrix.diagonal_apply]
      have hkk : k = k' ↔ (j : Fin n) = j' := by
        rw [← e.apply_eq_iff_eq, hk, hk', Sum.inl.injEq, Subtype.ext_iff]
      by_cases h : (j : Fin n) = j'
      · rw [if_pos h, if_pos (hkk.mpr h), if_neg j.2]
        by_cases hp : 0 < l1 j <;> simp [hp]
      · rw [if_neg h, if_neg (fun h' => h (hkk.mp h'))]
    · rw [← inst_gram_entry W1 J W2 (j : Fin n) j', hcross, Matrix.zero_apply, if_neg]
      intro h
      subst h
      rw [hk] at hk'
      exact Sum.inl_ne_inr hk'
    · rw [← inst_gram_entry W2 J W1 (j : Fin n) j', hcross', Matrix.zero_apply, if_neg]
      intro h
      subst h
      rw [hk] at hk'
      exact Sum.inr_ne_inl hk'
    · rw [← inst_gram_entry W2 J W2 (j : Fin n) j', hW2J, Matrix.diagonal_apply]
      have hkk : k = k' ↔ (j : Fin n) = j' := by
        rw [← e.apply_eq_iff_eq, hk, hk', Sum.inr.injEq, Subtype.ext_iff]
      by_cases h : (j : Fin n) = j'
      · rw [if_pos h, if_pos (hkk.mpr h), if_neg j.2]
        by_cases hp : 0 < l2 j <;> simp [hp]
      · rw [if_neg h, if_neg (fun h' => h (hkk.mp h'))]
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    rcases hk : e i with j | j
    · refine ⟨G⁻¹ *ᵥ (Bᴴ *ᵥ (J *ᵥ (W1 *ᵥ Pi.single (j : Fin n) 1))), ?_⟩
      have h1 : A *ᵥ Pi.single i 1 = W1 *ᵥ Pi.single (j : Fin n) 1 := by
        rw [hcol, hcol]
        funext r
        show A r i = W1 r (j : Fin n)
        rw [hAe, hk, Sum.elim_inl]
      rw [h1]
      calc W1 *ᵥ Pi.single (j : Fin n) 1 = (Q * W1) *ᵥ Pi.single (j : Fin n) 1 := by rw [hQW1]
        _ = _ := by simp only [hQdef, Matrix.mulVec_mulVec, Matrix.mul_assoc]
    · rw [hk] at hi
      simp at hi
  · intro j
    have hb : Q *ᵥ (B *ᵥ Pi.single j 1) = B *ᵥ Pi.single j 1 := by rw [Matrix.mulVec_mulVec, hQB]
    obtain ⟨y, hy0, hy⟩ := hsp1 _ hb
    refine ⟨fun k => Sum.elim (fun j' : {i // l1 i ≠ 0} => y j') (fun _ => (0 : ℂ)) (e k), ?_, ?_⟩
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
      rcases he : e k with j' | j'
      · rw [he] at hk
        simp at hk
      · simp only [he, Sum.elim_inr]
    · rw [hy]
      funext r
      simp only [Matrix.mulVec, dotProduct, hAe]
      symm
      rw [Fintype.sum_equiv e _ (fun x => Sum.elim (fun j : {i // l1 i ≠ 0} => W1 r j)
        (fun j : {i // l2 i ≠ 0} => W2 r j) x *
          Sum.elim (fun j' : {i // l1 i ≠ 0} => y j') (fun _ => (0 : ℂ)) x) (fun k => rfl)]
      rw [Fintype.sum_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, mul_zero, Finset.sum_const_zero, add_zero]
      rw [← Fintype.sum_subtype_add_sum_subtype (fun i => l1 i ≠ 0) (fun i => W1 r i * y i)]
      have h0 : ∑ i : {i // ¬ l1 i ≠ 0}, W1 r i * y i = 0 :=
        Finset.sum_eq_zero fun i _ => by rw [hy0 i (not_not.mp i.2), mul_zero]
      rw [h0, add_zero]

end PI.ScMuExists.UnitaryGroupMassFormula
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.FrameGramInstance

section

@[expose] public section

noncomputable section

open Matrix

namespace PI.ScMuExists.UnitaryGroupMassFormula

theorem gram_entry (I : Formalism.MainNotions.S.AutInst) (v : NumberField.InfinitePlace I.F) {r : ℕ}
    (e f : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E) (j k : Fin r ⊕ Fin r ⊕ Unit) :
    ((instBmat I v e f z)ᴴ * Formalism.REAL.Jm (I.ε v) * instBmat I v e f z) j k =
      hJ (I.ε v) (rv I v (instFvec e f z j)) (rv I v (instFvec e f z k)) := by
  unfold instBmat hJ
  rw [Matrix.mul_assoc]
  simp [Matrix.mul_apply, dotProduct, mulVec, Finset.mul_sum]

theorem frame_gram_instance : InstFrameGram := by
  intro I r e f z hF v
  obtain ⟨hee, hff, hef, hz, hzz⟩ := rv_frame (I := I) hF v
  have hJH : (Formalism.REAL.Jm (I.ε v))ᴴ = Formalism.REAL.Jm (I.ε v) := by
    unfold Formalism.REAL.Jm
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext a
    by_cases h : I.ε v a <;> simp [h]
  have hH : ((instBmat I v e f z)ᴴ * Formalism.REAL.Jm (I.ε v) * instBmat I v e f z)ᴴ =
      (instBmat I v e f z)ᴴ * Formalism.REAL.Jm (I.ε v) * instBmat I v e f z := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hJH, Matrix.mul_assoc]
  have hent := gram_entry I v e f z
  generalize (instBmat I v e f z)ᴴ * Formalism.REAL.Jm (I.ε v) * instBmat I v e f z = G at hH hent ⊢
  have hS : ∀ j k, G j k = star (G k j) := by
    intro j k
    have hjk := congrFun (congrFun hH j) k
    rw [Matrix.conjTranspose_apply] at hjk
    exact hjk.symm
  have h1 : ∀ a b, G (Sum.inl a) (Sum.inl b) = 0 := fun a b => by rw [hent]; exact hee a b
  have h3 : ∀ a b, G (Sum.inl a) (Sum.inr (Sum.inl b)) = if a = b then 1 else 0 :=
    fun a b => by rw [hent]; exact hef a b
  have h4 : ∀ a (u : Unit), G (Sum.inl a) (Sum.inr (Sum.inr u)) = 0 :=
    fun a u => by rw [hent]; exact (hz a).1
  have h5 : ∀ a (u : Unit), G (Sum.inr (Sum.inl a)) (Sum.inr (Sum.inr u)) = 0 :=
    fun a u => by rw [hent]; exact (hz a).2
  have h3' : ∀ a b, G (Sum.inr (Sum.inl a)) (Sum.inl b) = if b = a then 1 else 0 := by
    intro a b
    rw [hS, h3]
    split_ifs <;> simp
  have h4' : ∀ a (u : Unit), G (Sum.inr (Sum.inr u)) (Sum.inl a) = 0 := by
    intro a u
    rw [hS, h4, star_zero]
  have h5' : ∀ a (u : Unit), G (Sum.inr (Sum.inr u)) (Sum.inr (Sum.inl a)) = 0 := by
    intro a u
    rw [hS, h5, star_zero]
  have h6 : ∀ u u' : Unit, G (Sum.inr (Sum.inr u)) (Sum.inr (Sum.inr u')) ≠ 0 := by
    intro u u'
    rw [hent]
    exact hzz
  have hker : ∀ w, G *ᵥ w = 0 → w = 0 := by
    intro w hw
    have hf : ∀ a, w (Sum.inr (Sum.inl a)) = 0 := by
      intro a
      have := congrFun hw (Sum.inl a)
      simpa [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, h1, h3, h4] using this
    have he : ∀ a, w (Sum.inl a) = 0 := by
      intro a
      have := congrFun hw (Sum.inr (Sum.inl a))
      simpa [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, h3', h5, hf] using this
    have hzw : ∀ u : Unit, w (Sum.inr (Sum.inr u)) = 0 := by
      intro u
      have := congrFun hw (Sum.inr (Sum.inr u))
      simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, h4', h5', zero_mul,
        Finset.sum_const_zero, zero_add, Pi.zero_apply] at this
      rw [Fintype.sum_unique] at this
      rcases (mul_eq_zero.mp this) with h | h
      · exact absurd h (h6 _ _)
      · cases u
        exact h
    funext j
    rcases j with a | a | u
    · exact he a
    · exact hf a
    · exact hzw u
  refine Matrix.mulVec_injective_iff_isUnit.mp ?_
  intro w₁ w₂ h
  have h0 : G *ᵥ (w₁ - w₂) = 0 := by rw [Matrix.mulVec_sub, h, sub_self]
  exact sub_eq_zero.mp (hker _ h0)

end PI.ScMuExists.UnitaryGroupMassFormula
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.InstAll

section

@[expose] public section

namespace PI.ScMuExists.UnitaryGroupMassFormula

theorem place_decomposition_instance : InstDecomp :=
  instDecomp_of (placeDecomp_of exponent_fixed_instance adapted_basis_instance) frame_gram_instance

end PI.ScMuExists.UnitaryGroupMassFormula
end
end
