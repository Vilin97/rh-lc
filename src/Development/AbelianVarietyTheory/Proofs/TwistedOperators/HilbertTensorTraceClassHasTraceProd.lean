module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsHilbertSchmidtOfFiniteDimensional
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SplitHeightSummableExpNegAbs
public import Mathlib.Analysis.InnerProductSpace.l2Space
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumTupleProdOfSummableNormComplex

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousMultilinearMapExtHilbertBasis

section

@[expose] public section

open scoped InnerProductSpace

namespace GlobalTheory

theorem continuousMultilinearMap_ext_hilbertBasis (ι : Type) [Fintype ι] [DecidableEq ι]
    (Hs : ι → Type) [∀ i, NormedAddCommGroup (Hs i)] [∀ i, InnerProductSpace ℂ (Hs i)]
    (J : ι → Type) (e : ∀ i, HilbertBasis (J i) ℂ (Hs i)) (F : Type) [NormedAddCommGroup F]
    [NormedSpace ℂ F] (f g : ContinuousMultilinearMap ℂ Hs F)
    (h : ∀ j : ∀ i, J i, f (fun i => e i (j i)) = g (fun i => e i (j i))) : f = g := by
  have key : ∀ s : Finset ι, ∀ y : ∀ i, Hs i,
      (∀ i, i ∉ s → y i ∈ Set.range (e i)) → f y = g y := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro y hy
      choose j hj using fun i => hy i (by simp)
      have hy' : y = fun i => e i (j i) := funext fun i => (hj i).symm
      rw [hy']
      exact h j
    | insert a s ha ih =>
      intro y hy
      let L : Hs a →L[ℂ] F := (f - g).toContinuousLinearMap y a
      have hL : Set.EqOn (L : Hs a → F) (0 : Hs a →L[ℂ] F) (Set.range (e a)) := by
        intro z hz
        simp only [L, ContinuousMultilinearMap.toContinuousLinearMap_apply,
          ContinuousMultilinearMap.sub_apply, ContinuousLinearMap.zero_apply, sub_eq_zero]
        apply ih
        intro i hi
        by_cases hia : i = a
        · subst hia
          simpa using hz
        · rw [Function.update_of_ne hia]
          exact hy i (by simp [hia, hi])
      have hdense : Dense (Submodule.span ℂ (Set.range (e a)) : Set (Hs a)) := by
        exact Submodule.dense_iff_topologicalClosure_eq_top.mpr (e a).dense_span
      have hL0 : L = 0 := ContinuousLinearMap.ext_on hdense hL
      have hya := congrArg (fun M : Hs a →L[ℂ] F => M (y a)) hL0
      simp only [L, ContinuousMultilinearMap.toContinuousLinearMap_apply,
        ContinuousMultilinearMap.sub_apply, ContinuousLinearMap.zero_apply, sub_eq_zero,
        Function.update_eq_self] at hya
      exact hya
  ext y
  exact key Finset.univ y (by simp)

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousMultilinearMapExtHilbertBasisStatement

section

@[expose] public section

open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.continuousMultilinearMap_ext_hilbertBasis' : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Hs : ι → Type) [∀ i, NormedAddCommGroup (Hs i)] [∀ i, InnerProductSpace ℂ (Hs i)] (J : ι → Type) (e : ∀ i, HilbertBasis (J i) ℂ (Hs i)) (F : Type) [NormedAddCommGroup F] [NormedSpace ℂ F] (f g : ContinuousMultilinearMap ℂ Hs F), (∀ j : ∀ i, J i, f (fun i => e i (j i)) = g (fun i => e i (j i))) → f = g := by
  first | exact @GlobalTheory.continuousMultilinearMap_ext_hilbertBasis | exact GlobalTheory.continuousMultilinearMap_ext_hilbertBasis | (intros; apply GlobalTheory.continuousMultilinearMap_ext_hilbertBasis <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsHilbertSchmidtOrthonormalApply

section

@[expose] public section

open scoped InnerProductSpace

namespace GlobalTheory

theorem exists_isHilbertSchmidt_orthonormal_apply : ∀ (H K : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] (J : Type) (u : J → H) (w : J → K), Orthonormal ℂ u → Summable (fun j => ‖w j‖ ^ 2) → ∃ G : H →L[ℂ] K, (∀ j, G (u j) = w j) ∧ (∀ v, (∀ j, inner ℂ (u j) v = 0) → G v = 0) ∧ GlobalTheory.OpTrace.IsHilbertSchmidt G := by
  intro H K _ _ _ _ _ _ J u w hu hw
  classical
  set S : ℝ := ∑' j, ‖w j‖ ^ 2
  have hbes : ∀ v : H, Summable fun j => ‖⟪u j, v⟫_ℂ‖ ^ 2 := fun v => hu.inner_products_summable v
  have hbes_le : ∀ v : H, ∑' j, ‖⟪u j, v⟫_ℂ‖ ^ 2 ≤ ‖v‖ ^ 2 := fun v => hu.tsum_inner_products_le v
  have hsn : ∀ v : H, Summable fun j => ‖⟪u j, v⟫_ℂ‖ * ‖w j‖ := fun v =>
    Summable.of_nonneg_of_le (fun j => by positivity)
      (fun j => by nlinarith [sq_nonneg (‖⟪u j, v⟫_ℂ‖ - ‖w j‖)]) (((hbes v).add hw).div_const 2)
  have hsn' : ∀ v : H, Summable fun j => ‖⟪u j, v⟫_ℂ • w j‖ := fun v =>
    (hsn v).congr fun j => (norm_smul _ _).symm
  have hs : ∀ v : H, Summable fun j => ⟪u j, v⟫_ℂ • w j := fun v => (hsn' v).of_norm
  let L : H →ₗ[ℂ] K :=
    { toFun := fun v => ∑' j, ⟪u j, v⟫_ℂ • w j
      map_add' := fun v v' => by
        simp only [inner_add_right, add_smul]
        exact (hs v).tsum_add (hs v')
      map_smul' := fun c v => by
        simp only [inner_smul_right, mul_smul, RingHom.id_apply]
        exact (hs v).tsum_const_smul c }
  have hbound : ∀ v, ‖L v‖ ≤ ((1 + S) / 2) * ‖v‖ := by
    intro v
    by_cases hv : v = 0
    · subst hv; simp
    set t := ‖v‖ with htdef
    have ht : 0 < t := norm_pos_iff.2 hv
    set A : ℝ := ∑' j, ‖⟪u j, v⟫_ℂ‖ ^ 2
    have key : ∀ a b : ℝ, a * b ≤ (a ^ 2 * t⁻¹ + t * b ^ 2) / 2 := by
      intro a b
      have h : a ^ 2 * t⁻¹ + t * b ^ 2 - 2 * (a * b) = t⁻¹ * (a - t * b) ^ 2 := by
        field_simp; ring
      have : 0 ≤ t⁻¹ * (a - t * b) ^ 2 := by positivity
      linarith
    have h1 : ‖L v‖ ≤ ∑' j, ‖⟪u j, v⟫_ℂ‖ * ‖w j‖ := by
      refine (norm_tsum_le_tsum_norm (hsn' v)).trans_eq ?_
      simp only [norm_smul]
    have hA : HasSum (fun j => (‖⟪u j, v⟫_ℂ‖ ^ 2 * t⁻¹ + t * ‖w j‖ ^ 2) / 2) ((A * t⁻¹ + t * S) / 2) :=
      (((hbes v).hasSum.mul_right t⁻¹).add (hw.hasSum.mul_left t)).div_const 2
    have h2 : ∑' j, ‖⟪u j, v⟫_ℂ‖ * ‖w j‖ ≤ (A * t⁻¹ + t * S) / 2 :=
      hasSum_le (fun j => key _ _) (hsn v).hasSum hA
    have h3 : A * t⁻¹ ≤ t := by
      have : A * t⁻¹ ≤ t ^ 2 * t⁻¹ := mul_le_mul_of_nonneg_right (hbes_le v) (inv_nonneg.2 ht.le)
      have e : t ^ 2 * t⁻¹ = t := by field_simp
      linarith
    have : (A * t⁻¹ + t * S) / 2 ≤ (1 + S) / 2 * t := by nlinarith
    linarith
  let G : H →L[ℂ] K := L.mkContinuous ((1 + S) / 2) hbound
  have hG : ∀ v, G v = ∑' j, ⟪u j, v⟫_ℂ • w j := fun v => rfl
  have hval : ∀ j, G (u j) = w j := by
    intro j
    rw [hG, tsum_eq_single j (fun k hk => by rw [orthonormal_iff_ite.1 hu k j, if_neg hk, zero_smul]),
      orthonormal_iff_ite.1 hu j j, if_pos rfl, one_smul]
  have hvan : ∀ v, (∀ j, inner ℂ (u j) v = 0) → G v = 0 := by
    intro v h
    rw [hG]
    simp [h]
  refine ⟨G, hval, hvan, ?_⟩
  obtain ⟨W, b, hsub, hb⟩ :=
    ((orthonormal_subtype_range hu.linearIndependent.injective).2 hu).exists_hilbertBasis_extension
  rw [GlobalTheory.OpTrace.isHilbertSchmidt_iff b]
  let e : J → W := fun j => ⟨u j, hsub ⟨j, rfl⟩⟩
  have hbe : ∀ j, b (e j) = u j := fun j => congrFun hb (e j)
  have he : Function.Injective e := fun j k hjk =>
    hu.linearIndependent.injective (congrArg Subtype.val hjk)
  refine (he.summable_iff fun i hi => ?_).1 (hw.congr fun j => ?_)
  · have : G (b i) = 0 := hvan _ fun j => by
      rw [← hbe j]
      exact b.orthonormal.2 fun h => hi ⟨j, h⟩
    simp [this]
  · simp only [Function.comp_apply, hbe, hval]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsHilbertSchmidtOrthonormalApplyStatement

section

@[expose] public section

open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.exists_isHilbertSchmidt_orthonormal_apply_alt : ∀ (H K : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] (J : Type) (u : J → H) (w : J → K), Orthonormal ℂ u → Summable (fun j => ‖w j‖ ^ 2) → ∃ G : H →L[ℂ] K, (∀ j, G (u j) = w j) ∧ (∀ v, (∀ j, inner ℂ (u j) v = 0) → G v = 0) ∧ GlobalTheory.OpTrace.IsHilbertSchmidt G := by
  first | exact @GlobalTheory.exists_isHilbertSchmidt_orthonormal_apply | exact GlobalTheory.exists_isHilbertSchmidt_orthonormal_apply | (intros; apply GlobalTheory.exists_isHilbertSchmidt_orthonormal_apply <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumTupleProdOfSummableNormComplexStatement

section

@[expose] public section

open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.hasSum_tuple_prod_of_summable_norm_complex : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (J : ι → Type) (f : ∀ i, J i → ℂ), (∀ i, Summable (fun j => ‖f i j‖)) → HasSum (fun j : ∀ i, J i => ∏ i, f i (j i)) (∏ i, ∑' j, f i j) := by
  first | exact @GlobalTheory.hasSum_pi_prod_of_summable_norm | exact GlobalTheory.hasSum_pi_prod_of_summable_norm | (intros; apply GlobalTheory.hasSum_pi_prod_of_summable_norm <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.HilbertTensorTraceClassHasTraceProd

section

@[expose] public section

open ContinuousLinearMap
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory

open GlobalTheory.OpTrace

theorem tensorTrace_summable_sq {ι : Type} [Fintype ι] {Hs : ι → Type} [∀ i, NormedAddCommGroup (Hs i)]
    [∀ i, InnerProductSpace ℂ (Hs i)] [∀ i, CompleteSpace (Hs i)] {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (Ψ : ContinuousMultilinearMap ℂ Hs H) (c : ℂ)
    (hΨ : ∀ y y', ⟪Ψ y', Ψ y⟫_ℂ = c * ∏ i, ⟪y' i, y i⟫_ℂ) (A : ∀ i, Hs i →L[ℂ] Hs i)
    (hA : ∀ i, IsHilbertSchmidt (A i)) :
    Summable fun j : ∀ i, stdIndex (Hs i) => ‖Ψ (fun i => A i (stdBasis (H := Hs i) (j i)))‖ ^ 2 := by
  have hs := (splitHeight_summable_pi_prod (α := fun i => stdIndex (Hs i))
    (f := fun i k => ‖A i (stdBasis (H := Hs i) k)‖ ^ 2) (fun _ _ => sq_nonneg _) hA).mul_left c.re
  refine hs.congr fun j => ?_
  have h1 := hΨ (fun i => A i (stdBasis (H := Hs i) (j i))) (fun i => A i (stdBasis (H := Hs i) (j i)))
  simp only [inner_self_eq_norm_sq_to_K] at h1
  have h2 : ((‖Ψ (fun i => A i (stdBasis (H := Hs i) (j i)))‖ ^ 2 : ℝ) : ℂ)
      = c * ((∏ i, ‖A i (stdBasis (H := Hs i) (j i))‖ ^ 2 : ℝ) : ℂ) := by
    push_cast; exact h1
  have h3 := congrArg Complex.re h2
  rw [Complex.ofReal_re, Complex.re_mul_ofReal] at h3
  exact h3.symm

theorem tensorTrace_hasTrace : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Hs : ι → Type) [∀ i, NormedAddCommGroup (Hs i)] [∀ i, InnerProductSpace ℂ (Hs i)] [∀ i, CompleteSpace (Hs i)] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (Φ Φ' : ContinuousMultilinearMap ℂ Hs H) (κ κ' : ℂ), (∀ y y', inner ℂ (Φ y') (Φ y) = ∏ i, inner ℂ (y' i) (y i)) → (∀ y y', inner ℂ (Φ y') (Φ' y) = κ * ∏ i, inner ℂ (y' i) (y i)) → (∀ y y', inner ℂ (Φ' y') (Φ' y) = κ' * ∏ i, inner ℂ (y' i) (y i)) → ∀ (B : ∀ i, Hs i →L[ℂ] Hs i) (b : ι → ℂ), (∀ i, HasTrace (B i) (b i)) → ∀ X : H →L[ℂ] H, (∀ y, X (Φ y) = Φ' fun i => B i (y i)) → (∀ v, (∀ y, inner ℂ (Φ y) v = 0) → X v = 0) → HasTrace X (κ * ∏ i, b i) := by
  intro ι _ _ Hs _ _ _ H _ _ _ Φ Φ' κ κ' hΦ hΦΦ' hΦ' B b hB X hX hX0
  classical
  let J : ι → Type := fun i => stdIndex (Hs i)
  let e : ∀ i, HilbertBasis (J i) ℂ (Hs i) := fun i => stdBasis (H := Hs i)
  let u : (∀ i, J i) → H := fun j => Φ (fun i => e i (j i))

  have hu : Orthonormal ℂ u := by
    rw [orthonormal_iff_ite]
    intro j' j
    change ⟪Φ _, Φ _⟫_ℂ = _
    rw [hΦ]
    have : ∀ i, ⟪e i (j' i), e i (j i)⟫_ℂ = if j' i = j i then 1 else 0 := fun i =>
      (orthonormal_iff_ite.1 (e i).orthonormal) _ _
    simp only [this]
    by_cases h : ∀ x, j' x = j x
    · rw [if_pos (funext h)]
      exact Finset.prod_eq_one fun i _ => if_pos (h i)
    · rw [if_neg fun h' => h (congrFun h')]
      push_neg at h
      obtain ⟨i, hi⟩ := h
      exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

  have hperp : ∀ x : H, (∀ j, ⟪u j, x⟫_ℂ = 0) → ∀ y, ⟪Φ y, x⟫_ℂ = 0 := by
    intro x hx y
    have hL := GlobalTheory.T.continuousMultilinearMap_ext_hilbertBasis' ι Hs J e ℂ
      ((innerSL ℂ x).compContinuousMultilinearMap Φ) 0 fun j => by
        simp only [compContinuousMultilinearMap_coe, Function.comp_apply, innerSL_apply_apply,
          ContinuousMultilinearMap.zero_apply]
        rw [← inner_conj_symm]; simp [u] at hx; simp [hx]
    have := congrArg (fun L : ContinuousMultilinearMap ℂ Hs ℂ => L y) hL
    simp only [compContinuousMultilinearMap_coe, Function.comp_apply, innerSL_apply_apply,
      ContinuousMultilinearMap.zero_apply] at this
    rw [← inner_conj_symm, this, map_zero]

  have hinj : Function.Injective u := hu.linearIndependent.injective
  obtain ⟨w, bH, hsw, hb⟩ :=
    Orthonormal.exists_hilbertBasis_extension ((orthonormal_subtype_range hinj).2 hu)
  have hoff : ∀ x ∈ w, x ∉ Set.range u → ∀ y, ⟪Φ y, x⟫_ℂ = 0 := by
    intro x hxw hxu
    refine hperp x fun j => ?_
    have hne : (⟨u j, hsw ⟨j, rfl⟩⟩ : w) ≠ ⟨x, hxw⟩ := fun h => hxu ⟨j, congrArg Subtype.val h⟩
    have := bH.orthonormal.2 hne
    simpa [hb] using this

  choose n C D hC hD hBeq using fun i => (hB i).1

  have hG : ∀ (Ψ : ContinuousMultilinearMap ℂ Hs H) (c : ℂ),
      (∀ y y', ⟪Ψ y', Ψ y⟫_ℂ = c * ∏ i, ⟪y' i, y i⟫_ℂ) → ∀ A : ∀ i, Hs i →L[ℂ] Hs i,
      (∀ i, IsHilbertSchmidt (A i)) → ∃ G : H →L[ℂ] H, (∀ y, G (Φ y) = Ψ (fun i => A i (y i))) ∧
        (∀ v, (∀ y, ⟪Φ y, v⟫_ℂ = 0) → G v = 0) ∧ IsHilbertSchmidt G := by
    intro Ψ c hΨ A hA
    obtain ⟨G, hG1, hG2, hG3⟩ := GlobalTheory.T.exists_isHilbertSchmidt_orthonormal_apply_alt H H (∀ i, J i) u
      (fun j => Ψ (fun i => A i (e i (j i)))) hu (tensorTrace_summable_sq Ψ c hΨ A hA)
    refine ⟨G, fun y => ?_, fun v hv => hG2 v fun j => hv _, hG3⟩
    have := GlobalTheory.T.continuousMultilinearMap_ext_hilbertBasis' ι Hs J e H (G.compContinuousMultilinearMap Φ)
      (Ψ.compContinuousLinearMap A) fun j => by simpa using hG1 j
    simpa using congrArg (fun L : ContinuousMultilinearMap ℂ Hs H => L y) this
  have hΦ1 : ∀ y y', ⟪Φ y', Φ y⟫_ℂ = 1 * ∏ i, ⟪y' i, y i⟫_ℂ := fun y y' => by rw [one_mul, hΦ]
  choose GD hGD1 hGD2 hGD3 using fun k : ∀ i, Fin (n i) => hG Φ 1 hΦ1 (fun i => D i (k i)) fun i => hD i _
  choose GC hGC1 hGC2 hGC3 using fun k : ∀ i, Fin (n i) => hG Φ' κ' hΦ' (fun i => C i (k i)) fun i => hC i _

  have hXeq : X = ∑ k, GC k ∘L GD k := by
    have hd : Dense (Submodule.span ℂ w : Set H) := by
      have := bH.dense_span
      rw [hb, Subtype.range_coe] at this
      exact Submodule.dense_iff_topologicalClosure_eq_top.2 this
    refine ContinuousLinearMap.ext_on hd fun x hx => ?_
    by_cases hxu : x ∈ Set.range u
    · obtain ⟨j, rfl⟩ := hxu
      change X (Φ _) = _
      rw [hX, ContinuousLinearMap.sum_apply]
      simp only [comp_apply]
      rw [show (fun i => B i (e i (j i))) = fun i => ∑ m, C i m (D i m (e i (j i))) from
        funext fun i => by rw [hBeq i]; simp]

      rw [Φ'.map_sum (fun i m => C i m (D i m (e i (j i))))]
      refine Finset.sum_congr rfl fun k _ => ?_
      change _ = GC k (GD k (Φ fun i => e i (j i)))
      rw [hGD1, hGC1]
    · have h0 := hoff x hx hxu
      rw [hX0 x h0, ContinuousLinearMap.sum_apply]
      simp [hGD2 _ x h0]
  have hTC : IsTraceClass X := by
    rw [hXeq]; exact isTraceClass_sum _ fun k _ => (hGC3 k).isTraceClass_comp (hGD3 k)
  refine ⟨hTC, ?_⟩

  have htr := hTC.hasSum_trace bH
  let g : (∀ i, J i) → w := fun j => ⟨u j, hsw ⟨j, rfl⟩⟩
  have hg : Function.Injective g := fun j j' h => hinj (congrArg Subtype.val h)
  have hz : ∀ x ∉ Set.range g, ⟪bH x, X (bH x)⟫_ℂ = 0 := by
    intro x hx
    have hxu : x.1 ∉ Set.range u := fun ⟨j, hj⟩ => hx ⟨j, Subtype.ext hj⟩
    simp [hb, hX0 _ (hoff x.1 x.2 hxu)]
  rw [← hg.hasSum_iff hz] at htr
  have hval : ∀ j, ⟪bH (g j), X (bH (g j))⟫_ℂ = κ * ∏ i, ⟪e i (j i), B i (e i (j i))⟫_ℂ := by
    intro j
    simp only [hb, g]
    change ⟪Φ _, X (Φ _)⟫_ℂ = _
    rw [hX, hΦΦ']
  have hprod := (GlobalTheory.T.hasSum_tuple_prod_of_summable_norm_complex ι J (fun i k => ⟪e i k, B i (e i k)⟫_ℂ)
    fun i => (hB i).1.summable_norm (e i)).mul_left κ
  have hb' : ∀ i, ∑' k, ⟪e i k, B i (e i k)⟫_ℂ = b i := fun i =>
    ((hB i).1.hasSum_trace (e i)).tsum_eq.trans (hB i).2
  simp only [hb'] at hprod
  refine htr.unique ?_
  simpa only [Function.comp_def, hval] using hprod

end GlobalTheory
end
end
end
