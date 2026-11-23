module

public import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ColGeR
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Basic.Complex.Basic
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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ColGeR
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.FiniteDimensionalHcSpace
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockEmbeddingGLInverseStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalUnipotentRadicalSumZeroStatement
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PatternSetCardColumnStepStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerBlockEmbeddingConjStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerColumnRecursionStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerVanishesOfRadicalSumsStatement
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdditiveCharacterSumOrthogonality

section

@[expose] public section

open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep

namespace GlobalTheory.CompanionTheory.TyFin.Orth

theorem sum_inv_addChar_mul_left (K : Type) [Field K] [Fintype K] [DecidableEq K]
    (ψ₀ : AddChar K ℂ) (hψ : ψ₀ ≠ 1) (x : K) :
    (∑ t : K, (ψ₀ (t * x))⁻¹) = if x = 0 then (Fintype.card K : ℂ) else 0 := by
  by_cases hx : x = 0
  · subst hx
    simp
  · rw [if_neg hx]
    have hbij : Function.Bijective (fun t : K => -(t * x)) := by
      refine ⟨fun a b h => ?_, fun b => ⟨-(b * x⁻¹), ?_⟩⟩
      · exact mul_right_cancel₀ hx (neg_injective h)
      · simp [hx]
    have h1 : (∑ t : K, (ψ₀ (t * x))⁻¹) = ∑ t : K, ψ₀ (-(t * x)) :=
      Finset.sum_congr rfl fun t _ => (AddChar.map_neg_eq_inv ψ₀ (t * x)).symm
    rw [h1, hbij.sum_comp (fun u => ψ₀ u)]
    exact AddChar.sum_eq_zero_of_ne_one hψ

theorem sum_inv_addChar_dot (K : Type) [Field K] [Fintype K] [DecidableEq K] (j : ℕ)
    (ψ₀ : AddChar K ℂ) (hψ : ψ₀ ≠ 1) (x : Fin j → K) :
    (∑ r : Fin j → K, (ψ₀ (∑ i, r i * x i))⁻¹)
      = if x = 0 then (Fintype.card K : ℂ) ^ j else 0 := by
  have h1 : ∀ r : Fin j → K, (ψ₀ (∑ i, r i * x i))⁻¹ = ∏ i, (ψ₀ (r i * x i))⁻¹ := by
    intro r
    have hs : ∀ s : Finset (Fin j), ψ₀ (∑ i ∈ s, r i * x i) = ∏ i ∈ s, ψ₀ (r i * x i) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]
    rw [hs, Finset.prod_inv_distrib]
  have h2 : (∑ r : Fin j → K, ∏ i, (ψ₀ (r i * x i))⁻¹)
      = ∏ i, ∑ t : K, (ψ₀ (t * x i))⁻¹ := by
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  simp_rw [h1]
  rw [h2]
  simp_rw [sum_inv_addChar_mul_left K ψ₀ hψ]
  by_cases hx : x = 0
  · subst hx
    simp
  · rw [if_neg hx]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

theorem orth : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (j : ℕ) (ψ₀ : AddChar K ℂ),
    ψ₀ ≠ 1 → ∀ x : Fin j → K,
    (∑ r : Fin j → K, (ψ₀ (∑ i, r i * x i))⁻¹) = if x = 0 then (Fintype.card K : ℂ) ^ j else 0 :=
  fun K _ _ _ j ψ₀ hψ x => sum_inv_addChar_dot K j ψ₀ hψ x

end GlobalTheory.CompanionTheory.TyFin.Orth
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdditiveCharacterSumOrthogonalityStatement

section

@[expose] public section

open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep

theorem _root_.GlobalTheory.T.additive_character_sum_orthogonality : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (j : ℕ) (ψ₀ : AddChar K ℂ), ψ₀ ≠ 1 → ∀ x : Fin j → K,
    (∑ r : Fin j → K, (ψ₀ (∑ i, r i * x i))⁻¹) = if x = 0 then (Fintype.card K : ℂ) ^ j else 0 := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.Orth.orth | exact GlobalTheory.CompanionTheory.TyFin.Orth.orth | (intros; apply GlobalTheory.CompanionTheory.TyFin.Orth.orth <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GLTransitiveNonzeroVectors

section

@[expose] public section

open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep

namespace GlobalTheory.CompanionTheory.TyFin.RowTrans

theorem exists_linearEquiv_apply_eq_of_ne_zero {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) : ∃ e : V ≃ₗ[K] V, e x = y := by
  have hx1 : (LinearEquiv.toSpanNonzeroSingleton K V x hx).symm
      ⟨x, Submodule.mem_span_singleton_self x⟩ = 1 := by
    rw [LinearEquiv.symm_apply_eq, LinearEquiv.toSpanNonzeroSingleton_one]
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq
    ((LinearEquiv.toSpanNonzeroSingleton K V x hx).symm.trans
      (LinearEquiv.toSpanNonzeroSingleton K V y hy))
  refine ⟨g, ?_⟩
  have h := hg ⟨x, Submodule.mem_span_singleton_self x⟩
  rw [LinearEquiv.trans_apply, hx1, LinearEquiv.toSpanNonzeroSingleton_one] at h
  exact h.symm

theorem gl_transitive_rows : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (j : ℕ)
    (r r' : Fin j → K), r ≠ 0 → r' ≠ 0 →
    ∃ g : GL (Fin j) K, Matrix.vecMul r (g : Matrix (Fin j) (Fin j) K) = r' := by
  intro K _ _ _ j r r' hr hr'
  obtain ⟨e, he⟩ := GlobalTheory.CompanionTheory.TyFin.RowTrans.exists_linearEquiv_apply_eq_of_ne_zero (K := K) hr hr'
  have h1 : (e.symm : (Fin j → K) →ₗ[K] Fin j → K) ∘ₗ (e : (Fin j → K) →ₗ[K] Fin j → K) =
      LinearMap.id := LinearMap.ext fun v => by simp
  have h2 : (e : (Fin j → K) →ₗ[K] Fin j → K) ∘ₗ (e.symm : (Fin j → K) →ₗ[K] Fin j → K) =
      LinearMap.id := LinearMap.ext fun v => by simp
  refine ⟨⟨(LinearMap.toMatrix' (e : (Fin j → K) →ₗ[K] Fin j → K)).transpose,
    (LinearMap.toMatrix' (e.symm : (Fin j → K) →ₗ[K] Fin j → K)).transpose, ?_, ?_⟩, ?_⟩
  · rw [← Matrix.transpose_mul, ← LinearMap.toMatrix'_comp, h1, LinearMap.toMatrix'_id,
      Matrix.transpose_one]
  · rw [← Matrix.transpose_mul, ← LinearMap.toMatrix'_comp, h2, LinearMap.toMatrix'_id,
      Matrix.transpose_one]
  · change Matrix.vecMul r (LinearMap.toMatrix' (e : (Fin j → K) →ₗ[K] Fin j → K)).transpose = r'
    rw [Matrix.vecMul_transpose, LinearMap.toMatrix'_mulVec, LinearEquiv.coe_coe]
    exact he

end GlobalTheory.CompanionTheory.TyFin.RowTrans
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GLTransitiveNonzeroVectorsStatement

section

@[expose] public section

open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep

theorem _root_.GlobalTheory.T.GL_transitive_nonzero_vectors : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (j : ℕ) (r r' : Fin j → K), r ≠ 0 → r' ≠ 0 →
    ∃ g : GL (Fin j) K, Matrix.vecMul r (g : Matrix (Fin j) (Fin j) K) = r' := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.RowTrans.gl_transitive_rows | exact GlobalTheory.CompanionTheory.TyFin.RowTrans.gl_transitive_rows | (intros; apply GlobalTheory.CompanionTheory.TyFin.RowTrans.gl_transitive_rows <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalWhittaker

section

@[expose] public section

open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep

noncomputable section

namespace GlobalTheory.CompanionTheory.TyFin.ColStep

theorem colGeR_single (K : Type) [Field K] (d j : ℕ) (hj : 1 ≤ j) :
    colGeR K d j (Pi.single (⟨j - 1, by omega⟩ : Fin j) (1 : K) : Fin j → K) = colGeE K d j := by
  funext i l
  by_cases hl : (l : ℕ) = j
  · by_cases hi : (l : ℕ) = i + 1
    · have hlt : (i : ℕ) < j := by omega
      have hij : (⟨(i : ℕ), hlt⟩ : Fin j) = ⟨j - 1, by omega⟩ := Fin.ext (by simp; omega)
      simp only [colGeR, colGeE]
      rw [dite_eq_left ⟨hl, hlt⟩, hij]
      simp [hl, hi]
      omega
    · simp only [colGeR, colGeE]
      by_cases hlt : (i : ℕ) < j
      · rw [dite_eq_left ⟨hl, hlt⟩]
        have hne : (⟨(i : ℕ), hlt⟩ : Fin j) ≠ ⟨j - 1, by omega⟩ := by
          intro h; have := congrArg Fin.val h; simp at this; omega
        simp [hi, Pi.single_eq_of_ne hne]
      · rw [dite_eq_right (by tauto)]
        simp [hi]
  · simp only [colGeR, colGeE]
    rw [dite_eq_right (by tauto)]
    have : (j + 1 ≤ (l : ℕ)) ↔ j ≤ (l : ℕ) := by omega
    simp [this]

theorem wh_row_ne_zero (K : Type) [Field K] [Fintype K] [DecidableEq K] (d j : ℕ) (ψ₀ : AddChar K ℂ)
    (χ : GL (Fin d) K → ℂ) (hj : 1 ≤ j) (hd : j < d) (hχ : ∀ x y, χ (x * y * x⁻¹) = χ y)
    (r : Fin j → K) (hr : r ≠ 0) :
    wh (colGe d j) (colGeR K d j r) ψ₀ χ = wh (colGe d j) (colGeE K d j) ψ₀ χ := by
  have hs : (Pi.single (⟨j - 1, by omega⟩ : Fin j) (1 : K) : Fin j → K) ≠ 0 := by
    intro h
    have := congrFun h ⟨j - 1, by omega⟩
    simp at this
  obtain ⟨g, hg⟩ := GlobalTheory.T.GL_transitive_nonzero_vectors K j r _ hr hs
  obtain ⟨h, h1, h2⟩ := GlobalTheory.T.block_embedding_GL_inverse K d j hd.le g
  rw [GlobalTheory.T.whittaker_block_embedding_conj K d j ψ₀ χ g h r hd hχ h1 h2, hg, colGeR_single K d j hj]

theorem wh_step (K : Type) [Field K] [Fintype K] [DecidableEq K] (d j : ℕ) (ψ₀ : AddChar K ℂ)
    (τ : FDRep ℂ (GL (Fin d) K)) (hψ : ψ₀ ≠ 1) (hτ : IsCuspidal K τ) (hj : 1 ≤ j) (hd : j < d) :
    wh (colGe d (j + 1)) (colGeE K d (j + 1)) ψ₀ τ.character =
      ((Fintype.card K : ℂ) ^ j - 1) * wh (colGe d j) (colGeE K d j) ψ₀ τ.character := by
  rw [GlobalTheory.T.whittaker_column_recursion K d j ψ₀ τ.character hd (GlobalTheory.T.pattern_set_card_column_step K d j hd) (GlobalTheory.T.additive_character_sum_orthogonality K j ψ₀ hψ)]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin j → K)),
    GlobalTheory.T.whittaker_vanishes_of_radical_sums K d j ψ₀ τ.character (GlobalTheory.T.cuspidal_unipotent_radical_sum_zero K d j τ hj hd hτ), zero_add,
    Finset.sum_congr rfl (fun r hr => wh_row_ne_zero K d j ψ₀ τ.character hj hd
      (fun x y => FDRep.char_conj τ y x) r (Finset.ne_of_mem_erase hr))]
  rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
  have h1 : 1 ≤ Fintype.card K ^ j := Nat.one_le_pow _ _ Fintype.card_pos
  rw [Nat.cast_sub h1]
  simp

theorem wh_top (K : Type) [Field K] [Fintype K] [DecidableEq K] (d : ℕ) (ψ₀ : AddChar K ℂ)
    (τ : FDRep ℂ (GL (Fin d) K)) :
    wh (colGe d d) (colGeE K d d) ψ₀ τ.character = (Module.finrank ℂ τ : ℂ) := by
  classical
  have hset : patSet K (colGe d d) = {1} := by
    ext u
    simp only [patSet, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · intro h
      ext i l
      by_cases hil : i = l
      · subst hil; simpa using (h i i).1 rfl
      · have := (h i l).2 hil (fun hc => by have := hc.2; have := l.2; omega)
        simp [this, Matrix.one_apply_ne hil]
    · rintro rfl i l
      exact ⟨fun h => by simp [h], fun h _ => by simp [Matrix.one_apply_ne h]⟩
  have hE : patChar (colGeE K d d) ψ₀ (1 : GL (Fin d) K) = 1 := by
    have : ∀ i l : Fin d, colGeE K d d i l = 0 := by
      intro i l
      simp only [colGeE]
      rw [if_neg]
      rintro ⟨-, h⟩
      have := l.2
      omega
    simp [patChar, this]
  simp only [wh, hset, Set.ncard_singleton, Set.mem_singleton_iff]
  simp [hE, FDRep.char_one]

theorem wh_one_eq (K : Type) [Field K] [Fintype K] [DecidableEq K] (d : ℕ) (ψ₀ : AddChar K ℂ) (χ : GL (Fin d) K → ℂ) :
    wh (colGe d 1) (colGeE K d 1) ψ₀ χ = wh (fun i j : Fin d => i < j) (cutE K d 0) ψ₀ χ := by
  have h1 : colGe d 1 = fun i j : Fin d => i < j := by
    funext i l
    simp only [colGe, eq_iff_iff, and_iff_left_iff_imp]
    intro h
    have : (i : ℕ) < l := h
    omega
  have h2 : colGeE K d 1 = cutE K d 0 := by
    funext i l
    simp only [colGeE, cutE]
    congr 1
    apply propext
    omega
  rw [h1, h2]

theorem wh_prod (K : Type) [Field K] [Fintype K] [DecidableEq K] (d : ℕ) (ψ₀ : AddChar K ℂ)
    (τ : FDRep ℂ (GL (Fin d) K)) (hψ : ψ₀ ≠ 1) (hτ : IsCuspidal K τ) (k : ℕ) (hk : 1 ≤ k) (hkd : k ≤ d) :
    wh (colGe d k) (colGeE K d k) ψ₀ τ.character =
      wh (colGe d 1) (colGeE K d 1) ψ₀ τ.character * ∏ i ∈ Finset.Ico 1 k, ((Fintype.card K : ℂ) ^ i - 1) := by
  induction k, hk using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    rw [wh_step K d k ψ₀ τ hψ hτ hk (by omega), ih (by omega), Finset.prod_Ico_succ_top hk]
    ring

theorem cuspWh : ReciprocityTheory.Ty.Fin.St.CuspWh := by
  intro K _ _ _ d ψ₀ τ hψ hτ
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · rw [← wh_top K 0 ψ₀ τ]
    have h1 : colGe 0 0 = fun i j : Fin 0 => i < j := by
      funext i; exact i.elim0
    have h2 : colGeE K 0 0 = cutE K 0 0 := by
      funext i; exact i.elim0
    rw [h1, h2]
    simp
  · rw [← wh_top K d ψ₀ τ, wh_prod K d ψ₀ τ hψ hτ d hd le_rfl, wh_one_eq]

end GlobalTheory.CompanionTheory.TyFin.ColStep
end
end
end
