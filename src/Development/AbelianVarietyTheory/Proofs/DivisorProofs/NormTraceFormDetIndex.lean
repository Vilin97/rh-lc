module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKMOne
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LiftFactorization
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DefiniteBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfTraceFormSkewHermitianStatement
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormGramDetEqIndexStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceIntegralOfPreservedLatticeStatement
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.PicardGroup

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceProductSkewHermitianReal

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

namespace GlobalTheory

theorem skew_transpose_mul_add_mul_conj {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (G X : Matrix (Fin r) (Fin r) E)
    (hX : ∀ u w, herm G (X *ᵥ u) w + herm G u (X *ᵥ w) = 0) :
    Xᵀ * G + G * X.map (fun x => cc x) = 0 := by
  ext i j
  have h := hX (Pi.single i 1) (Pi.single j 1)
  have c0 : cc (0 : E) = 0 := map_zero _
  have c1 : cc (1 : E) = 1 := map_one _
  have hc : ∀ b : Fin r, cc (if b = j then (1 : E) else 0) = if b = j then 1 else 0 := by
    intro b; split_ifs <;> simp [c0, c1]
  simp [herm, Matrix.mulVec_single, Pi.single_apply, c0, c1, hc, Matrix.mul_apply] at h ⊢
  exact h

theorem conj_eq_of_skew {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (G X : Matrix (Fin r) (Fin r) E) (hG : G.det ≠ 0)
    (hX : ∀ u w, herm G (X *ᵥ u) w + herm G u (X *ᵥ w) = 0) :
    X.map (fun x => cc x) = -(G⁻¹ * Xᵀ * G) := by
  have h := skew_transpose_mul_add_mul_conj G X hX
  have hu : IsUnit G.det := isUnit_iff_ne_zero.mpr hG
  have h2 : G * X.map (fun x => cc x) = -(Xᵀ * G) := eq_neg_of_add_eq_zero_right h
  calc X.map (fun x => cc x) = G⁻¹ * (G * X.map (fun x => cc x)) := by
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
    _ = -(G⁻¹ * Xᵀ * G) := by rw [h2, Matrix.mul_neg, Matrix.mul_assoc]

theorem trace_mul_skew_mem_maximalRealSubfield :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (X Y : Matrix (Fin r) (Fin r) E), (∀ a b, cc (G a b) = G b a) → G.det ≠ 0 → (∀ u w, herm G (X *ᵥ u) w + herm G u (X *ᵥ w) = 0) → (∀ u w, herm G (Y *ᵥ u) w + herm G u (Y *ᵥ w) = 0) → (X * Y).trace ∈ maximalRealSubfield E := by
  intro E _ _ _ r G X Y _ hG hX hY
  have hu : IsUnit G.det := isUnit_iff_ne_zero.mpr hG
  have hXc := conj_eq_of_skew G X hG hX
  have hYc := conj_eq_of_skew G Y hG hY
  rw [← IsCMField.complexConj_eq_self_iff]
  change cc (X * Y).trace = (X * Y).trace
  have hmap : cc (X * Y).trace = ((X * Y).map (fun x => cc x)).trace := by
    simp only [Matrix.trace, Matrix.diag, Matrix.map_apply]
    exact map_sum (IsCMField.complexConj E : E →+* E) _ _
  have hmul : (X * Y).map (fun x => cc x) = X.map (fun x => cc x) * Y.map (fun x => cc x) :=
    Matrix.map_mul (f := ((IsCMField.complexConj E : E ≃ₐ[maximalRealSubfield E] E) : E →+* E))
  rw [hmap, hmul, hXc, hYc, neg_mul_neg]
  have e1 : G⁻¹ * Xᵀ * G * (G⁻¹ * Yᵀ * G) = G⁻¹ * (Xᵀ * Yᵀ * G) := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc G G⁻¹, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]
  rw [e1, Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one,
    ← Matrix.transpose_mul, Matrix.trace_transpose, Matrix.trace_mul_comm]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceProductSkewHermitianRealStatement

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

theorem _root_.GlobalTheory.T.trace_product_skew_hermitian_real : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (X Y : Matrix (Fin r) (Fin r) E), (∀ a b, cc (G a b) = G b a) → G.det ≠ 0 → (∀ u w, herm G (X *ᵥ u) w + herm G u (X *ᵥ w) = 0) → (∀ u w, herm G (Y *ᵥ u) w + herm G u (Y *ᵥ w) = 0) → (X * Y).trace ∈ maximalRealSubfield E := by
  first | exact @GlobalTheory.trace_mul_skew_mem_maximalRealSubfield | exact GlobalTheory.trace_mul_skew_mem_maximalRealSubfield | (intros; apply GlobalTheory.trace_mul_skew_mem_maximalRealSubfield <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieBasisSpansUnitaryLie

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

namespace GlobalTheory.SkewSpan

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem herm_eq_dot (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) :
    herm G x y = (x ᵥ* G) ⬝ᵥ (fun b => cc (y b)) := by
  unfold herm
  rw [Finset.sum_comm]
  simp [dotProduct, vecMul, Finset.sum_mul]

theorem herm_sum_left {ι : Type} [Fintype ι] (G : Matrix (Fin r) (Fin r) E) (c : ι → E)
    (v : ι → Matrix (Fin r) (Fin r) E) (u w : Fin r → E) :
    herm G ((∑ i, c i • v i) *ᵥ u) w = ∑ i, c i * herm G (v i *ᵥ u) w := by
  simp only [herm_eq_dot, Matrix.sum_mulVec, Matrix.smul_mulVec, Matrix.sum_vecMul,
    Matrix.smul_vecMul, sum_dotProduct, smul_dotProduct, smul_eq_mul]

theorem herm_sum_right {ι : Type} [Fintype ι] (G : Matrix (Fin r) (Fin r) E) (c : ι → E)
    (v : ι → Matrix (Fin r) (Fin r) E) (u w : Fin r → E) :
    herm G u ((∑ i, c i • v i) *ᵥ w) = ∑ i, cc (c i) * herm G u (v i *ᵥ w) := by
  have : (fun b => cc (((∑ i, c i • v i) *ᵥ w) b))
      = ∑ i, cc (c i) • (fun b => cc ((v i *ᵥ w) b)) := by
    funext b
    simp [cc, Matrix.sum_mulVec, Matrix.smul_mulVec, Finset.sum_apply]
  simp only [herm_eq_dot, this, dotProduct_sum, dotProduct_smul, smul_eq_mul]

theorem eq_zero_of_herm (G : Matrix (Fin r) (Fin r) E) (hG : G.det ≠ 0)
    (Y : Matrix (Fin r) (Fin r) E) (h : ∀ u w, herm G (Y *ᵥ u) w = 0) : Y = 0 := by
  have key : ∀ u, Y *ᵥ u = 0 := by
    intro u
    apply Matrix.eq_zero_of_vecMul_eq_zero hG
    funext b
    have := h u (Pi.single b 1)
    rw [herm_eq_dot] at this
    have h2 : (fun b' => cc ((Pi.single b (1 : E) : Fin r → E) b')) = Pi.single b 1 := by
      funext b'
      by_cases hb : b' = b
      · subst hb; simp [cc]
      · simp [cc, hb]
    rw [h2] at this
    simpa using this
  ext a b
  have := congrFun (key (Pi.single b 1)) a
  simpa using this

theorem linearIndependent_of_skew {ι : Type} [Fintype ι] (G : Matrix (Fin r) (Fin r) E)
    (hG : G.det ≠ 0) (v : ι → Matrix (Fin r) (Fin r) E)
    (hv : ∀ i u w, herm G (v i *ᵥ u) w + herm G u (v i *ᵥ w) = 0)
    (hli : LinearIndependent (maximalRealSubfield E) v) : LinearIndependent E v := by
  rw [Fintype.linearIndependent_iff] at hli ⊢
  have step : ∀ c : ι → E, ∑ i, c i • v i = 0 → ∀ i, c i + cc (c i) = 0 := by
    intro c hc
    have h1 : ∑ i, cc (c i) • v i = 0 := by
      apply eq_zero_of_herm G hG
      intro u w
      have h := herm_sum_right G c v u w
      rw [hc] at h
      have h0 : herm G u ((0 : Matrix (Fin r) (Fin r) E) *ᵥ w) = 0 := by simp [herm, cc]
      rw [h0] at h
      rw [herm_sum_left, ← neg_eq_zero, ← Finset.sum_neg_distrib, h]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [eq_neg_of_add_eq_zero_right (hv i u w)]; ring
    have hm : ∀ i, c i + cc (c i) ∈ maximalRealSubfield E := by
      intro i
      rw [← IsCMField.complexConj_eq_self_iff]
      simp [cc, add_comm]
    intro i
    have := hli (fun i => ⟨c i + cc (c i), hm i⟩) (by
      have : ∑ i, (c i + cc (c i)) • v i = 0 := by
        simp only [add_smul, Finset.sum_add_distrib, hc, h1, add_zero]
      exact this) i
    exact congrArg Subtype.val this
  intro c hc j
  have h := step (fun i => cc (c j) * c i) (by
    simp only [mul_smul, ← Finset.smul_sum, hc, smul_zero]) j
  have h2 : 2 * (cc (c j) * c j) = 0 := by
    rw [← h]; simp [cc]; ring
  simp [cc] at h2
  exact h2

theorem finrank_ker_trace (K : Type) [Field K] (r : ℕ) :
    Module.finrank K (LinearMap.ker (Matrix.traceLinearMap (Fin (r + 1)) K K)) = (r + 1) ^ 2 - 1 := by
  have h := LinearMap.finrank_range_add_finrank_ker (Matrix.traceLinearMap (Fin (r + 1)) K K)
  have hs : LinearMap.range (Matrix.traceLinearMap (Fin (r + 1)) K K) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro a
    exact ⟨Matrix.single 0 0 a, by simp⟩
  rw [hs, finrank_top, Module.finrank_self, Module.finrank_matrix] at h
  simp only [Fintype.card_fin, Module.finrank_self, mul_one] at h
  rw [sq]; omega

theorem mem_span_of_skew : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (e : Fin (r ^ 2 - 1) → Matrix (Fin r) (Fin r) E), (∀ a b, cc (G a b) = G b a) → G.det ≠ 0 → (∀ i, (e i).trace = 0 ∧ ∀ u w, herm G (e i *ᵥ u) w + herm G u (e i *ᵥ w) = 0) → LinearIndependent (maximalRealSubfield E) e → ∀ X : Matrix (Fin r) (Fin r) E, X.trace = 0 → (∀ u w, herm G (X *ᵥ u) w + herm G u (X *ᵥ w) = 0) → X ∈ Submodule.span (maximalRealSubfield E) (Set.range e) := by
  intro E _ _ _ r G e _ hG he hli X hX hXs
  rcases r with _ | r
  · have : X = 0 := Subsingleton.elim _ _
    rw [this]; exact Submodule.zero_mem _
  by_contra hn
  have h1 : LinearIndependent (maximalRealSubfield E) (fun o : Option _ => Option.casesOn' o X e) :=
    hli.option hn
  have h2 := linearIndependent_of_skew G hG _ (by
    rintro (_ | i)
    · exact hXs
    · exact (he i).2) h1
  let f : Option (Fin ((r + 1) ^ 2 - 1)) →
      LinearMap.ker (Matrix.traceLinearMap (Fin (r + 1)) E E) := fun o =>
    ⟨Option.casesOn' o X e, by
      rcases o with _ | i
      · exact hX
      · exact (he i).1⟩
  have h3 : LinearIndependent E f := LinearIndependent.of_comp (Submodule.subtype _) h2
  have h4 := h3.fintype_card_le_finrank
  rw [finrank_ker_trace] at h4
  simp at h4

end GlobalTheory.SkewSpan
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieBasisSpansUnitaryLieStatement

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

theorem _root_.GlobalTheory.T.lie_basis_spans_unitary_lie : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (e : Fin (r ^ 2 - 1) → Matrix (Fin r) (Fin r) E), (∀ a b, cc (G a b) = G b a) → G.det ≠ 0 → (∀ i, (e i).trace = 0 ∧ ∀ u w, herm G (e i *ᵥ u) w + herm G u (e i *ᵥ w) = 0) → LinearIndependent (maximalRealSubfield E) e → ∀ X : Matrix (Fin r) (Fin r) E, X.trace = 0 → (∀ u w, herm G (X *ᵥ u) w + herm G u (X *ᵥ w) = 0) → X ∈ Submodule.span (maximalRealSubfield E) (Set.range e) := by
  first | exact @GlobalTheory.SkewSpan.mem_span_of_skew | exact GlobalTheory.SkewSpan.mem_span_of_skew | (intros; apply GlobalTheory.SkewSpan.mem_span_of_skew <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormTraceFormDetIndex

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

namespace GlobalTheory.LieIndex

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def skewSub (G : Matrix (Fin r) (Fin r) E) : Submodule (maximalRealSubfield E) (Matrix (Fin r) (Fin r) E) where
  carrier := {X | X.trace = 0 ∧ ∀ u w, herm G (X *ᵥ u) w + herm G u (X *ᵥ w) = 0}
  zero_mem' := ⟨by simp, by simp [herm, cc]⟩
  add_mem' {X Y} hX hY := by
    refine ⟨by rw [trace_add, hX.1, hY.1, add_zero], fun u w => ?_⟩
    have h1 := hX.2 u w
    have h2 := hY.2 u w
    simp only [herm, cc, add_mulVec, Pi.add_apply, map_add (f := _), add_mul, mul_add, Finset.sum_add_distrib] at h1 h2 ⊢
    linear_combination h1 + h2
  smul_mem' c X hX := by
    have hc : IsCMField.complexConj E (c : E) = c := IsCMField.complexConj_apply_eq_self E c
    have e : c • X = (c : E) • X := rfl
    refine ⟨by rw [e, trace_smul, hX.1, smul_zero], fun u w => ?_⟩
    have h1 := hX.2 u w
    rw [e]
    simp only [herm, cc, smul_mulVec, Pi.smul_apply, smul_eq_mul, map_mul, hc] at h1 ⊢
    have e1 : ∀ a b, ((c : E) * (X *ᵥ u) a) * G a b * (IsCMField.complexConj E) (w b) =
        (c : E) * ((X *ᵥ u) a * G a b * (IsCMField.complexConj E) (w b)) := fun a b => by ring
    have e2 : ∀ a b, u a * G a b * ((c : E) * (IsCMField.complexConj E) ((X *ᵥ w) b)) =
        (c : E) * (u a * G a b * (IsCMField.complexConj E) ((X *ᵥ w) b)) := fun a b => by ring
    simp only [e1, e2, ← Finset.mul_sum]
    rw [← mul_add, h1, mul_zero]

def trForm (G : Matrix (Fin r) (Fin r) E) (hG : ∀ a b, cc (G a b) = G b a) (hd : G.det ≠ 0) :
    LinearMap.BilinForm (maximalRealSubfield E) (skewSub G) :=
  LinearMap.mk₂ (maximalRealSubfield E)
    (fun X Y => ⟨(X.1 * Y.1).trace, GlobalTheory.T.trace_product_skew_hermitian_real E r G X.1 Y.1 hG hd X.2.2 Y.2.2⟩)
    (fun X₁ X₂ Y => Subtype.ext (by simp [add_mul, trace_add]))
    (fun c X Y => Subtype.ext (by simp [trace_smul]; rfl))
    (fun X Y₁ Y₂ => Subtype.ext (by simp [mul_add, trace_add]))
    (fun c X Y => Subtype.ext (by simp [trace_smul]; rfl))

theorem trForm_apply (G : Matrix (Fin r) (Fin r) E) (hG : ∀ a b, cc (G a b) = G b a) (hd : G.det ≠ 0)
    (X Y : skewSub G) : ((trForm G hG hd X Y : maximalRealSubfield E) : E) = (X.1 * Y.1).trace := rfl

theorem norm_algebraMap_real (d : maximalRealSubfield E) :
    Algebra.norm ℚ (algebraMap (maximalRealSubfield E) E d) = (Algebra.norm ℚ d) ^ 2 := by
  rw [← Algebra.norm_norm (R := ℚ) (S := maximalRealSubfield E), Algebra.norm_algebraMap,
    Algebra.IsQuadraticExtension.finrank_eq_two, map_pow]

theorem isIntegral_coe_iff (x : maximalRealSubfield E) : IsIntegral ℤ (x : E) ↔ IsIntegral ℤ x :=
  isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ (maximalRealSubfield E) E)
    (IsScalarTower.toAlgHom ℤ (maximalRealSubfield E) E).toRingHom.injective

theorem abs_norm_gram_eq_index : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (e : Fin (r ^ 2 - 1) → Matrix (Fin r) (Fin r) E), 2 ≤ r → SelfDualLat G Λ → (∀ i, e i ∈ lieLat G Λ) → LinearIndependent (maximalRealSubfield E) e → |((Algebra.norm ℚ (Matrix.of fun i j => Matrix.trace (e i * e j)).det : ℚ) : ℝ)| = (((lieLat G Λ).relIndex (AddSubgroup.closure {Y : Matrix (Fin r) (Fin r) E | Y.trace = 0 ∧ (∀ u w, herm G (Y *ᵥ u) w + herm G u (Y *ᵥ w) = 0) ∧ ∀ X ∈ lieLat G Λ, IsIntegral ℤ (Matrix.trace (X * Y))}) : ℝ) * ((Submodule.span (𝓞 (maximalRealSubfield E)) (Set.range e)).toAddSubgroup.relIndex (lieLat G Λ) : ℝ) ^ 2) ^ 2 := by
  intro E _ _ _ r G Λ e hr hΛ he hli
  obtain ⟨hG, hd, hfg, hsp, -⟩ := hΛ
  have heV : ∀ i, e i ∈ skewSub G := fun i => ⟨(he i).1, (he i).2.1⟩
  set v : Fin (r ^ 2 - 1) → skewSub G := fun i => ⟨e i, heV i⟩ with hv_def
  have hve : (skewSub G).subtype ∘ v = e := rfl
  have hvli : LinearIndependent (maximalRealSubfield E) v :=
    LinearIndependent.of_comp (skewSub G).subtype (by rw [hve]; exact hli)
  have hmapv : Submodule.map (skewSub G).subtype (Submodule.span (maximalRealSubfield E) (Set.range v)) =
      Submodule.span _ (Set.range e) := by
    rw [Submodule.map_span, ← Set.range_comp, hve]
  have hspan : ⊤ ≤ Submodule.span (maximalRealSubfield E) (Set.range v) := by
    rintro ⟨X, hX⟩ -
    have h := GlobalTheory.T.lie_basis_spans_unitary_lie E r G e hG hd heV hli X hX.1 hX.2
    rw [← hmapv] at h
    obtain ⟨y, hy, hyX⟩ := h
    have : y = ⟨X, hX⟩ := Subtype.ext hyX
    rwa [← this]
  set b := Module.Basis.mk hvli hspan with hb
  have hbv : ∀ i, b i = v i := fun i => Module.Basis.mk_apply hvli hspan i
  set B := trForm G hG hd with hB
  set f : skewSub G →+ Matrix (Fin r) (Fin r) E := (skewSub G).subtype.toAddMonoidHom with hf_def
  have hf : Function.Injective f := Subtype.val_injective
  set L' := (lieLat G Λ).comap f with hL'
  have hLrange : lieLat G Λ ≤ f.range := fun X hX => ⟨⟨X, hX.1, hX.2.1⟩, rfl⟩
  have hLmap : L'.map f = lieLat G Λ := AddSubgroup.map_comap_eq_self hLrange
  have hsymm : B.IsSymm := ⟨fun x y => Subtype.ext (by rw [hB, trForm_apply, trForm_apply]; exact Matrix.trace_mul_comm _ _)⟩
  have hsep : ∀ X : skewSub G, (∀ Y : skewSub G, B X Y = 0) → X = 0 := by
    intro X hX
    apply Subtype.ext
    refine GlobalTheory.T.eq_zero_of_trace_form_skew_hermitian E r G X.1 hG hd X.2.1 X.2.2 fun Y hY1 hY2 => ?_
    have := congrArg (fun z : maximalRealSubfield E => (z : E)) (hX ⟨Y, hY1, hY2⟩)
    simpa [hB, trForm_apply] using this
  have hnd : B.Nondegenerate := ⟨fun X hX => hsep X hX, fun Y hY => hsep Y fun X => by rw [hsymm.eq]; exact hY X⟩
  have hbL : ∀ i, b i ∈ L' := fun i => by rw [hbv]; exact he i
  have hsm : ∀ (a : 𝓞 (maximalRealSubfield E)) x, x ∈ L' → a • x ∈ L' := by
    intro a x hx
    refine ⟨(a • x).2.1, (a • x).2.2, fun y hy => ?_⟩
    have hc : IsIntegral ℤ (((a : maximalRealSubfield E) : E)) := (isIntegral_coe_iff _).2 a.isIntegral_coe
    have e1 : (f (a • x)) = (((a : maximalRealSubfield E) : E)) • x.1 := rfl
    rw [e1, smul_mulVec]
    have e2 : (((a : maximalRealSubfield E) : E)) • (x.1 *ᵥ y) = (⟨_, (mem_integralClosure_iff ℤ E).2 hc⟩ : 𝓞 E) • (x.1 *ᵥ y) := by
      rw [← algebraMap_smul E (⟨_, (mem_integralClosure_iff ℤ E).2 hc⟩ : 𝓞 E) (x.1 *ᵥ y)]; rfl
    rw [e2]
    exact Λ.smul_mem _ (hx.2.2 y hy)
  have hint : ∀ x ∈ L', ∀ y ∈ L', IsIntegral ℤ (B x y) := by
    intro x hx y hy
    rw [← isIntegral_coe_iff, hB, trForm_apply]
    refine GlobalTheory.T.trace_integral_of_preserved_lattice E r Λ _ hfg hsp fun z hz => ?_
    rw [← mulVec_mulVec]
    exact hx.2.2 _ (hy.2.2 z hz)
  have key := GlobalTheory.T.norm_gram_det_eq_index (maximalRealSubfield E) (skewSub G) (r ^ 2 - 1) b B L' hsymm hnd hbL hsm hint
  have hdet : (Matrix.of fun i j => Matrix.trace (e i * e j)).det =
      algebraMap (maximalRealSubfield E) E (Matrix.of fun i j => B (b i) (b j)).det := by
    rw [RingHom.map_det]
    congr 1
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, hbv]
    rfl
  have I1 : (lieLat G Λ).relIndex (AddSubgroup.closure {Y : Matrix (Fin r) (Fin r) E | Y.trace = 0 ∧
      (∀ u w, herm G (Y *ᵥ u) w + herm G u (Y *ᵥ w) = 0) ∧ ∀ X ∈ lieLat G Λ, IsIntegral ℤ (Matrix.trace (X * Y))}) =
      L'.relIndex (AddSubgroup.closure {y | ∀ x ∈ L', IsIntegral ℤ (B x y)}) := by
    rw [← AddSubgroup.relIndex_map_map_of_injective _ _ hf, hLmap, AddMonoidHom.map_closure]
    congr 2
    ext Y
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨⟨Y, h1, h2⟩, fun x hx => ?_, rfl⟩
      rw [← isIntegral_coe_iff, hB, trForm_apply]
      exact h3 _ hx
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2.1, y.2.2, fun X hX => ?_⟩
      have := hy ⟨X, hX.1, hX.2.1⟩ hX
      rw [← isIntegral_coe_iff, hB, trForm_apply] at this
      exact this
  have I2 : (Submodule.span (𝓞 (maximalRealSubfield E)) (Set.range e)).toAddSubgroup.relIndex (lieLat G Λ) =
      (Submodule.span (𝓞 (maximalRealSubfield E)) (Set.range b)).toAddSubgroup.relIndex L' := by
    rw [← AddSubgroup.relIndex_map_map_of_injective _ _ hf, hLmap]
    congr 1
    let g : skewSub G →ₗ[𝓞 (maximalRealSubfield E)] Matrix (Fin r) (Fin r) E :=
      { toFun := Subtype.val, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    have hg : (Submodule.span (𝓞 (maximalRealSubfield E)) (Set.range b)).map g =
        Submodule.span (𝓞 (maximalRealSubfield E)) (Set.range e) := by
      rw [Submodule.map_span, ← Set.range_comp]
      congr 2
      funext i
      simp [g, hbv, v]
    rw [← hg, Submodule.map_toAddSubgroup]
    rfl
  rw [hdet, norm_algebraMap_real, I1, I2, ← key]
  push_cast
  rw [abs_pow, sq_abs]

end GlobalTheory.LieIndex
end
end
