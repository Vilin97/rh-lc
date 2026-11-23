module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjLowUni
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNhdsOneConjLowerUnipotentSchurBlocksSmallStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIdempotentElemIdemSf
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitBlockDetOfConjLower
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIdempotentElemIdemSf

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FirstColumnInvFiniteMemCompactOnSupport

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

namespace GlobalTheory.NmUnfCol

theorem continuous_pFin (E : Type) [Field E] [NumberField E] : Continuous (pFin E) := by
  unfold pFin; exact continuous_snd

theorem col_inv_mul {E : Type} [Field E] [NumberField E] {a : ℕ}
    (u p : GA E (a + 1)) (hu : u ∈ GlobalTheory.JSW.NA (E := E) (a := (a + 1))) (l : Fin (a + 1)) :
    ((p⁻¹ : GA E (a + 1)) : Matrix (Fin (a + 1)) (Fin (a + 1)) (Ad E)) l 0 =
      (((u⁻¹ * p)⁻¹ : GA E (a + 1)) : Matrix (Fin (a + 1)) (Fin (a + 1)) (Ad E)) l 0 := by
  have e : ((u⁻¹ * p)⁻¹ : GA E (a + 1)) = p⁻¹ * u := by group
  rw [e, Units.val_mul, Matrix.mul_apply]
  have hcol : ∀ j : Fin (a + 1), (u : Matrix (Fin (a + 1)) (Fin (a + 1)) (Ad E)) j 0 = if j = 0 then 1 else 0 := by
    intro j
    by_cases hj : j = 0
    · subst hj; simp [hu.2 0]
    · rw [if_neg hj]; exact hu.1 j 0 (Fin.pos_iff_ne_zero.2 hj)
  simp only [hcol, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem finite_first_col_inv_compact : ∀ (E : Type) [Field E] [NumberField E] (r : ℕ) (b₁ : GA E (r + 1) → ℂ), (∃ C : Set (GA E (r + 1)), IsCompact C ∧ ∀ p, b₁ p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (r + 1)), u⁻¹ * p ∈ C) → ∃ K : Set (Fin (r + 1) → Af E), IsCompact K ∧ ∀ p, b₁ p ≠ 0 → (fun l => pFin E (((p⁻¹ : GA E (r + 1)) : Matrix (Fin (r + 1)) (Fin (r + 1)) (Ad E)) l 0)) ∈ K := by
  intro E _ _ r b₁ ⟨C, hC, hsupp⟩
  let f : GA E (r + 1) → (Fin (r + 1) → Af E) :=
    fun c l => pFin E (((c⁻¹ : GA E (r + 1)) : Matrix (Fin (r + 1)) (Fin (r + 1)) (Ad E)) l 0)
  have hf : Continuous f := by
    refine continuous_pi fun l => (continuous_pFin E).comp ?_
    have h0 : Continuous (fun c : GA E (r + 1) => ((c⁻¹ : GA E (r + 1)) : Matrix (Fin (r + 1)) (Fin (r + 1)) (Ad E))) :=
      Units.continuous_coe_inv
    exact (continuous_apply 0).comp ((continuous_apply l).comp h0)
  refine ⟨f '' C, hC.image hf, fun p hp => ?_⟩
  obtain ⟨u, hu, huC⟩ := hsupp p hp
  refine ⟨u⁻¹ * p, huC, funext fun l => ?_⟩
  simp only [f]
  rw [col_inv_mul u p hu l]

end GlobalTheory.NmUnfCol
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FirstColumnInvFiniteMemCompactOnSupportStatement

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

theorem _root_.GlobalTheory.T.firstColumn_inv_finite_mem_compact_on_support : ∀ (E : Type) [Field E] [NumberField E] (r : ℕ) (b₁ : GA E (r + 1) → ℂ), (∃ C : Set (GA E (r + 1)), IsCompact C ∧ ∀ p, b₁ p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (r + 1)), u⁻¹ * p ∈ C) → ∃ K : Set (Fin (r + 1) → Af E), IsCompact K ∧ ∀ p, b₁ p ≠ 0 → (fun l => pFin E (((p⁻¹ : GA E (r + 1)) : Matrix (Fin (r + 1)) (Fin (r + 1)) (Ad E)) l 0)) ∈ K := by
  first | (exact @GlobalTheory.NmUnfCol.finite_first_col_inv_compact) | (exact GlobalTheory.NmUnfCol.finite_first_col_inv_compact) | (intros; apply GlobalTheory.NmUnfCol.finite_first_col_inv_compact  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LastRowFiniteMemCompactOnSupport

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

theorem GlobalTheory.JSW.lastRow_finite_compact : ∀ (E : Type) [Field E] [NumberField E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (β : GA E (m + 1) → ℂ), (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, β h ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * h ∈ C) → ∃ K : Set (Fin (m + 1) → Af E), IsCompact K ∧ ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, β h ≠ 0 → (fun j => pFin E ((h : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) j)) ∈ K := by
  intro E _ _ m S β ⟨C, hC, hCβ⟩
  let F : GA E (m + 1) → (Fin (m + 1) → Af E) :=
    fun c j => pFin E ((c : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) j)
  have hF : Continuous F := by
    refine continuous_pi fun j => ?_
    have h0 : Continuous fun c : GA E (m + 1) => (c : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) :=
      Units.continuous_val
    have h1 : Continuous fun c : GA E (m + 1) => (c : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) j :=
      h0.matrix_elem (Fin.last m) j
    exact continuous_snd.comp h1
  refine ⟨F '' C, hC.image hF, fun h hS hβ => ?_⟩
  obtain ⟨u, hu, huC⟩ := hCβ h hS hβ
  refine ⟨u⁻¹ * h, huC, ?_⟩
  set c : GA E (m + 1) := u⁻¹ * h with hc
  have hh : h = u * c := by rw [hc]; group
  have key : ∀ j, (h : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) j =
      (c : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) j := by
    intro j
    have hm : (h : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) =
        (u : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) * (c : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) := by
      rw [hh]; rfl
    rw [hm, Matrix.mul_apply, Finset.sum_eq_single (Fin.last m)]
    · rw [hu.2, one_mul]
    · intro l _ hl
      rw [hu.1 (Fin.last m) l (lt_of_le_of_ne (Fin.le_last l) hl), zero_mul]
    · intro h'; exact absurd (Finset.mem_univ _) h'
  funext j
  simp only [F, key j]
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LastRowFiniteMemCompactOnSupportStatement

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

theorem _root_.GlobalTheory.T.lastRow_finite_mem_compact_on_support : ∀ (E : Type) [Field E] [NumberField E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (β : GA E (m + 1) → ℂ), (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, β h ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * h ∈ C) → ∃ K : Set (Fin (m + 1) → Af E), IsCompact K ∧ ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, β h ≠ 0 → (fun j => pFin E ((h : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) j)) ∈ K := by
  first
  | exact @GlobalTheory.JSW.lastRow_finite_compact
  | exact GlobalTheory.JSW.lastRow_finite_compact
  | (intros; apply GlobalTheory.JSW.lastRow_finite_compact <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurComplementMemAdelicGLSupportedAtFinitePlace

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

namespace GlobalTheory.SchurExt

theorem map_blocks_of_map_eq_one {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {m r : ℕ}
    (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) (h : M.map f = 1) :
    (Aof M).map f = 1 ∧ (Bof M).map f = 0 ∧ (Cof M).map f = 0 := by
  refine ⟨Matrix.ext fun i j => ?_, Matrix.ext fun i j => ?_, Matrix.ext fun i j => ?_⟩
  · have := congrFun (congrFun h ((eqv m r).symm (Sum.inl i))) ((eqv m r).symm (Sum.inl j))
    simp only [Matrix.map_apply] at this ⊢
    simp only [Aof, blk, Matrix.toBlocks₁₁, Matrix.submatrix_apply, Matrix.of_apply, this, Matrix.one_apply,
      (eqv m r).symm.injective.eq_iff, Sum.inl.injEq]
  · have := congrFun (congrFun h ((eqv m r).symm (Sum.inl i))) ((eqv m r).symm (Sum.inr j))
    simp only [Matrix.map_apply] at this ⊢
    simp only [Bof, blk, Matrix.toBlocks₁₂, Matrix.submatrix_apply, Matrix.of_apply, this, Matrix.one_apply,
      (eqv m r).symm.injective.eq_iff, reduceCtorEq, if_false, Matrix.zero_apply]
  · have := congrFun (congrFun h ((eqv m r).symm (Sum.inr i))) ((eqv m r).symm (Sum.inl j))
    simp only [Matrix.map_apply] at this ⊢
    simp only [Cof, blk, Matrix.toBlocks₂₁, Matrix.submatrix_apply, Matrix.of_apply, this, Matrix.one_apply,
      (eqv m r).symm.injective.eq_iff, reduceCtorEq, if_false, Matrix.zero_apply]

theorem map_Scof_eq_one {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {m r : ℕ}
    (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) (h : M.map f = 1) :
    (Scof M).map f = 1 := by
  obtain ⟨hA, hB, hC⟩ := map_blocks_of_map_eq_one f M h
  have hmul : ∀ {a b c : ℕ} (P : Matrix (Fin a) (Fin b) R) (Q : Matrix (Fin b) (Fin c) R),
      (P * Q).map f = P.map f * Q.map f := fun P Q => Matrix.map_mul
  rw [Scof, Matrix.map_sub _ (map_sub f), hmul, hmul, hA, hB, hC, Matrix.zero_mul, Matrix.mul_zero, sub_zero]

end GlobalTheory.SchurExt

theorem GlobalTheory.SchurExt.mkGL_Scof_mem_supS : ∀ (E : Type) [Field E] [NumberField E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (x : GA E (m + r + 1 + 1)), x ∈ GlobalTheory.JSW.supS (E := E) (a := (m + r + 1 + 1)) S → IsUnit (Dof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).det → mkGL (Scof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))) ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S := by
  intro E _ _ m r S x hx _ w hw
  have h1 := hx w hw
  set f := (pLoc E w).comp (pFin E)
  have hM : (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).map f = 1 := by
    have := Units.ext_iff.mp h1
    simpa using this
  have hS := map_Scof_eq_one f _ hM
  by_cases hu : IsUnit (Scof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).det
  · refine Units.ext ?_
    change ((mkGL (Scof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))) :
      GL (Fin (m + 1)) (Ad E)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)).map f = 1
    rw [coe_mkGL hu]
    exact hS
  · rw [mkGL, dite_eq_right hu, map_one]
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurComplementMemAdelicGLSupportedAtFinitePlaceStatement

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

theorem _root_.GlobalTheory.T.schurComplement_mem_adelicGLSupportedAtFinitePlaces : ∀ (E : Type) [Field E] [NumberField E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (x : GA E (m + r + 1 + 1)), x ∈ GlobalTheory.JSW.supS (E := E) (a := (m + r + 1 + 1)) S → IsUnit (Dof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).det → mkGL (Scof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))) ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S := by
  first | (exact @GlobalTheory.SchurExt.mkGL_Scof_mem_supS) | (exact GlobalTheory.SchurExt.mkGL_Scof_mem_supS) | (intros; apply GlobalTheory.SchurExt.mkGL_Scof_mem_supS  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurFunctionSmoothRightInvariant

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

noncomputable section

namespace GlobalTheory.SchurExt.InvParts

theorem L_bridge : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m r : ℕ) (x : GA E (m + r + 1 + 1)) (k : GL (Fin (m + r + 1 + 1)) (Af E)), IsUnit (Dof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).det → IsUnit (Dof (conjLowUni ((Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map (pFin E)) (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E)))).det → IsUnit (Scof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).det ∧ IsUnit (Dof ((x * finGL E (m + r + 1 + 1) k : GA E (m + r + 1 + 1)) : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).det ∧ mkGL (Dof ((x * finGL E (m + r + 1 + 1) k : GA E (m + r + 1 + 1)) : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))) = mkGL (Dof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))) * finGL E (r + 1) (mkGL (Dof (conjLowUni ((Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map (pFin E)) (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E))))) ∧ mkGL (Scof ((x * finGL E (m + r + 1 + 1) k : GA E (m + r + 1 + 1)) : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))) = mkGL (Scof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))) * finGL E (m + 1) (mkGL (Scof (conjLowUni ((Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map (pFin E)) (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E))))) ∧ (∀ i j, pInf E (Yof ((x * finGL E (m + r + 1 + 1) k : GA E (m + r + 1 + 1)) : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) i j) = pInf E (Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) i j)) ∧ (∀ i j, pFin E (Yof ((x * finGL E (m + r + 1 + 1) k : GA E (m + r + 1 + 1)) : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) i j) = pFin E (Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) i j) + Yof (conjLowUni ((Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map (pFin E)) (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E))) i j) ∧ Xof ((x * finGL E (m + r + 1 + 1) k : GA E (m + r + 1 + 1)) : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) (Fin.last m) 0 = Xof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) (Fin.last m) 0 + sFin E (∑ j, ∑ l, pFin E (Scof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) (Fin.last m) j) * Xof (conjLowUni ((Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map (pFin E)) (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E))) j l * pFin E ((Dof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)))⁻¹ l 0)) := GlobalTheory.T.isUnit_block_det_of_conj_lower

theorem L_top : ∀ (E : Type) [Field E] [NumberField E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (Uβ : Subgroup (GL (Fin (m + 1)) (Af E))) (Ub : Subgroup (GL (Fin (r + 1)) (Af E))), IsOpen (Uβ : Set (GL (Fin (m + 1)) (Af E))) → IsOpen (Ub : Set (GL (Fin (r + 1)) (Af E))) → ∀ (Krow : Set (Fin (m + 1) → Af E)) (Kcol : Set (Fin (r + 1) → Af E)), IsCompact Krow → IsCompact Kcol → ∃ W ∈ 𝓝 (1 : GL (Fin (m + r + 1 + 1)) (Af E)), ∀ k ∈ W, (∀ w ∉ S, Matrix.GeneralLinearGroup.map (pLoc E w) k = 1) → ∀ Y : Matrix (Fin (r + 1)) (Fin (m + 1)) (Af E), (∀ i j, Y i j ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E) → IsUnit (Dof (conjLowUni Y (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E)))).det ∧ mkGL (Dof (conjLowUni Y (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E)))) ∈ Ub ∧ mkGL (Scof (conjLowUni Y (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E)))) ∈ Uβ ∧ (∀ i j, Yof (conjLowUni Y (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E))) i j ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E) ∧ ∀ ρ ∈ Krow, ∀ γ ∈ Kcol, (∑ j, ∑ l, ρ j * Xof (conjLowUni Y (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E))) j l * γ l) ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E := GlobalTheory.T.exists_nhds_one_conjLowerUnipotent_schurBlocks_small

theorem L_row : ∀ (E : Type) [Field E] [NumberField E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (β : GA E (m + 1) → ℂ), (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, β h ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * h ∈ C) → ∃ K : Set (Fin (m + 1) → Af E), IsCompact K ∧ ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, β h ≠ 0 → (fun j => pFin E ((h : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) j)) ∈ K := GlobalTheory.T.lastRow_finite_mem_compact_on_support

theorem L_col : ∀ (E : Type) [Field E] [NumberField E] (r : ℕ) (b₁ : GA E (r + 1) → ℂ), (∃ C : Set (GA E (r + 1)), IsCompact C ∧ ∀ p, b₁ p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (r + 1)), u⁻¹ * p ∈ C) → ∃ K : Set (Fin (r + 1) → Af E), IsCompact K ∧ ∀ p, b₁ p ≠ 0 → (fun l => pFin E (((p⁻¹ : GA E (r + 1)) : Matrix (Fin (r + 1)) (Fin (r + 1)) (Ad E)) l 0)) ∈ K := GlobalTheory.T.firstColumn_inv_finite_mem_compact_on_support

theorem L_supSc : ∀ (E : Type) [Field E] [NumberField E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (x : GA E (m + r + 1 + 1)), x ∈ GlobalTheory.JSW.supS (E := E) (a := (m + r + 1 + 1)) S → IsUnit (Dof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).det → mkGL (Scof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))) ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S := GlobalTheory.T.schurComplement_mem_adelicGLSupportedAtFinitePlaces

end GlobalTheory.SchurExt.InvParts

namespace GlobalTheory.SchurExt

variable {E : Type} [Field E] [NumberField E]

theorem psi_sFin_of_mem {z : Af E} (hz : z ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E) : psi (sFin E z) = 1 := by
  have h := GroundTheory.Global.adelicChar_of_mem_invDifferentAdeles (K := E) (y := sFin E z)
    (GroundTheory.Global.mem_invDifferentAdeles.mpr (GroundTheory.Global.mem_finiteInvDifferent_of_mem_integralFiniteAdeles hz))
  have h0 : (sFin E z).1 = 0 := rfl
  rw [psi, h, h0]
  simp

theorem psi_add (a b : Ad E) : psi (a + b) = psi a * psi b := by
  simp only [psi, AddChar.map_add_eq_mul, Circle.coe_mul]

theorem supS_mul {a : ℕ} {S : Finset (HeightOneSpectrum (𝓞 E))} {x y : GA E a}
    (hx : x ∈ GlobalTheory.JSW.supS (E := E) (a := a) S) (hy : y ∈ GlobalTheory.JSW.supS (E := E) (a := a) S) : x * y ∈ GlobalTheory.JSW.supS (E := E) (a := a) S := by
  intro w hw
  rw [map_mul, hx w hw, hy w hw, mul_one]

theorem supS_inv {a : ℕ} {S : Finset (HeightOneSpectrum (𝓞 E))} {x : GA E a}
    (hx : x ∈ GlobalTheory.JSW.supS (E := E) (a := a) S) : x⁻¹ ∈ GlobalTheory.JSW.supS (E := E) (a := a) S := by
  intro w hw
  rw [map_inv, hx w hw, inv_one]

theorem finGL_mem_supS {a : ℕ} {S : Finset (HeightOneSpectrum (𝓞 E))} {k : GL (Fin a) (Af E)}
    (hk : finGL E a k ∈ GlobalTheory.JSW.supS (E := E) (a := a) S) (w : HeightOneSpectrum (𝓞 E)) (hw : w ∉ S) :
    Matrix.GeneralLinearGroup.map (pLoc E w) k = 1 := by
  have h := hk w hw
  rw [← h]
  refine Units.ext (Matrix.ext fun i j => ?_)
  change pLoc E w (k i j) = pLoc E w (pFin E ((finGL E a k : GA E a) i j))
  congr 1
  exact (congrArg (fun y : GL (Fin a) (Af E) => (y : Matrix (Fin a) (Fin a) (Af E)) i j) (pFin_finGL (E := E) k)).symm

end GlobalTheory.SchurExt


open GlobalTheory.SchurExt.InvParts in
theorem GlobalTheory.SchurExt.schurF_mul_finGL_eq : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (β : GA E (m + 1) → ℂ) (b₁ : GA E (r + 1) → ℂ) (χ : (Fin (r + 1) → Fin (m + 1) → Cinf E) → ℝ), (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, β (g * finGL E (m + 1) u) = β g) → (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, β h ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * h ∈ C) → (∃ U : Subgroup (GL (Fin (r + 1)) (Af E)), IsOpen (U : Set (GL (Fin (r + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, b₁ (g * finGL E (r + 1) u) = b₁ g) → (∃ C : Set (GA E (r + 1)), IsCompact C ∧ ∀ p, b₁ p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (r + 1)), u⁻¹ * p ∈ C) → ∃ W ∈ 𝓝 (1 : GL (Fin (m + r + 1 + 1)) (Af E)), ∀ k ∈ W, finGL E (m + r + 1 + 1) k ∈ GlobalTheory.JSW.supS (E := E) (a := (m + r + 1 + 1)) S → ∀ x ∈ GlobalTheory.JSW.supS (E := E) (a := (m + r + 1 + 1)) S, schurF β b₁ χ (x * finGL E (m + r + 1 + 1) k) = schurF β b₁ χ x := by
  intro E _ _ _ m r S β b₁ χ ⟨Uβ, hUβo, hUβ⟩ hβC ⟨Ub, hUbo, hUb⟩ hbC
  obtain ⟨Krow, hKr, hKrow⟩ := L_row E m S β hβC
  obtain ⟨Kcol, hKc, hKcol⟩ := L_col E r b₁ hbC
  obtain ⟨W₀, hW₀, hW⟩ := L_top E m r S Uβ Ub hUβo hUbo Krow Kcol hKr hKc
  have fwd : ∀ k ∈ W₀, finGL E (m + r + 1 + 1) k ∈ GlobalTheory.JSW.supS (E := E) (a := (m + r + 1 + 1)) S →
      ∀ x ∈ GlobalTheory.JSW.supS (E := E) (a := (m + r + 1 + 1)) S, schurF β b₁ χ x ≠ 0 →
        schurF β b₁ χ (x * finGL E (m + r + 1 + 1) k) = schurF β b₁ χ x := by
    intro k hk hkS x hx hF
    classical
    have hD : IsUnit (Dof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).det := by
      by_contra hD
      exact hF (by rw [schurF, ite_eq_right hD])
    rw [schurF, ite_eq_left hD] at hF
    have hβ0 := left_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul hF))
    have hβ0' := right_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul hF))
    have hb0 := right_ne_zero_of_mul (left_ne_zero_of_mul hF)
    have hχ0 := right_ne_zero_of_mul hF
    have hYint : ∀ i j, pFin E (Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) i j) ∈
        GroundTheory.Global.integralFiniteAdeles (𝓞 E) E := by
      by_contra hY
      exact hχ0 (by rw [chiF, ite_eq_right hY, mul_zero])
    obtain ⟨hdu, hdU, hsU, hyI, hX⟩ := hW k hk (finGL_mem_supS hkS)
      ((Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map (pFin E)) (fun i j => hYint i j)
    obtain ⟨hSc, hD', eD, eSc, eYi, eYf, eX⟩ := L_bridge E m r x k hD hdu
    have hrow := hKrow _ (L_supSc E m r S x hx hD) hβ0'
    have hcol := hKcol _ hb0
    rw [coe_mkGL hSc] at hrow
    rw [Matrix.coe_units_inv, coe_mkGL hD] at hcol
    have hz := hX _ hrow _ hcol
    have hchi : chiF χ (Yof ((x * finGL E (m + r + 1 + 1) k : GA E (m + r + 1 + 1)) :
        Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))) =
        chiF χ (Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))) := by
      have h1 : (fun i j => pInf E (Yof ((x * finGL E (m + r + 1 + 1) k : GA E (m + r + 1 + 1)) :
          Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) i j)) =
          fun i j => pInf E (Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) i j) :=
        funext fun i => funext fun j => eYi i j
      have h2 : ∀ i j, pFin E (Yof ((x * finGL E (m + r + 1 + 1) k : GA E (m + r + 1 + 1)) :
          Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) i j) ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E :=
        fun i j => by rw [eYf]; exact add_mem (hYint i j) (hyI i j)
      rw [chiF, chiF, h1, ite_eq_left h2, ite_eq_left hYint]
    rw [schurF, ite_eq_left hD', eD, eSc, hUb _ hdU, hUβ _ hsU, hchi, eX, psi_add, psi_sFin_of_mem hz, mul_one, schurF, ite_eq_left hD]
  open scoped Pointwise in
  exact by
    refine ⟨W₀ ∩ W₀⁻¹, Filter.inter_mem hW₀ (inv_mem_nhds_one _ hW₀), ?_⟩
    intro k hk hkS x hx
    by_cases h0 : schurF β b₁ χ x = 0
    · by_cases h1 : schurF β b₁ χ (x * finGL E (m + r + 1 + 1) k) = 0
      · rw [h0, h1]
      · have h2 := fwd k⁻¹ hk.2 (by rw [map_inv]; exact supS_inv hkS) _ (supS_mul hx hkS) h1
        rw [mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one] at h2
        exact absurd (h2.symm.trans h0) h1
    · exact fwd k hk.1 hkS x hx h0
end
end
end
