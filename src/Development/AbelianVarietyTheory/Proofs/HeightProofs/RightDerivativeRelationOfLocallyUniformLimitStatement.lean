module

public import Development.AbelianVarietyTheory.Proofs.HeightProofs.NotMemOfMulExp
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.KoszulLowersPower
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ModularCharacterEqOneOnExpHermitian
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.HeightProofs.RightDerivativeRelationOfLocallyUniformLimit

section

@[expose] public section

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped Topology ContDiff

namespace GlobalTheory.TypeSum.CoefClos

theorem integral_rder_eq_zero {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [SFinite μ]
    [IsFiniteMeasureOnCompacts μ] [μ.IsMulRightInvariant] (c : ℝ → G) (hc : Continuous c) (h0 : c 0 = 1)
    (hadd : ∀ a b, c (a + b) = c a * c b) (h h' : G → ℂ) (hh : Continuous h) (hh' : Continuous h')
    (hs : HasCompactSupport h) (hs' : HasCompactSupport h')
    (hd : ∀ x, HasDerivAt (fun t => h (x * c t)) (h' x) 0) : ∫ x, h' x ∂μ = 0 := by
  have i0 : Integrable h μ := hh.integrable_of_hasCompactSupport hs
  have i1 : Integrable h' μ := hh'.integrable_of_hasCompactSupport hs'
  have pt : ∀ x, ∫ t in Set.Ioc (0 : ℝ) 1, h' (x * c t) = h (x * c 1) - h x := by
    intro x
    rw [← intervalIntegral.integral_of_le zero_le_one]
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 1) (f := fun t => h (x * c t))
      (f' := fun t => h' (x * c t)) (fun r _ => ?_)
      ((hh'.comp (continuous_const.mul hc)).intervalIntegrable 0 1)
    · simpa only [h0, mul_one] using this
    · have h1 : HasDerivAt (fun t => h (x * c r * c t)) (h' (x * c r)) (r - r) := by
        rw [sub_self]; exact hd _
      have h2 := h1.comp_sub_const r r
      refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
      simp only [mul_assoc, ← hadd, add_sub_cancel]
  have hint : Integrable (Function.uncurry fun (x : G) (t : ℝ) => h' (x * c t))
      (μ.prod (volume.restrict (Set.Ioc (0 : ℝ) 1))) := by
    have hcont : Continuous (Function.uncurry fun (x : G) (t : ℝ) => h' (x * c t)) :=
      hh'.comp (continuous_fst.mul (hc.comp continuous_snd))
    rw [integrable_prod_iff' hcont.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall fun t => i1.comp_mul_right (c t), ?_⟩
    simp only [Function.uncurry_apply_pair, fun t => integral_mul_right_eq_self (μ := μ) (fun x => ‖h' x‖) (c t)]
    exact integrable_const _
  have sw := integral_integral_swap hint
  simp only [pt, fun t => integral_mul_right_eq_self (μ := μ) h' (c t)] at sw
  rw [integral_sub (i0.comp_mul_right _) i0, integral_mul_right_eq_self h, sub_self] at sw
  simpa using sw.symm

variable {n : ℕ} {ε : Fin n → Bool}

noncomputable def mkU (g : Mx n) (hg : g ∈ UJset ε) : UJ ε :=
  ⟨(isUnit_of_UJ hg).unit, show inUJ ε _ from hg⟩

theorem umat_mkU (g : Mx n) (hg : g ∈ UJset ε) : umat (mkU g hg) = g := rfl

theorem umat_emb (ε : Fin n → Bool) : Topology.IsClosedEmbedding (fun g : UJ ε => umat g) := (isClosedEmbeddingMatrix n ε).1

theorem CSm.continuous {f : Mx n → ℂ} (h : CSm ε f) : Continuous fun g : UJ ε => f (umat g) := by
  obtain ⟨F, h1, -, h3⟩ := h
  exact ((h3 [] (by simp)).congr fun g hg => (h1 g hg).symm).comp_continuous (umat_emb ε).continuous fun g => g.2

theorem cSm_of_contDiff (φ : Mx n → ℂ) (hφ : ContDiff ℝ ∞ (fun y : Fin n → Fin n → ℂ => φ (Matrix.of y))) :
    CSm ε φ := by
  letI := Matrix.linftyOpNormedRing (n := Fin n) (α := ℂ)
  letI := Matrix.linftyOpNormedAlgebra (R := ℝ) (n := Fin n) (α := ℂ)
  have hφ' : ContDiff ℝ ∞ φ := by
    let L : Mx n →L[ℝ] (Fin n → Fin n → ℂ) :=
      LinearMap.toContinuousLinearMap (Matrix.ofLinearEquiv ℝ).symm.toLinearMap
    exact hφ.comp L.contDiff
  let F : List (Mx n) → Mx n → ℂ := fun l => l.foldr (fun X f g => fderiv ℝ f g (g * X)) φ
  have hF : ∀ l, ContDiff ℝ ∞ (F l) := by
    intro l
    induction l with
    | nil => exact hφ'
    | cons X l ih =>
      exact (ih.fderiv_right (m := ∞) (by simp)).clm_apply (contDiff_id.mul contDiff_const)
  refine ⟨F, fun _ _ => rfl, fun l _ X _ g _ => ?_, fun l _ => (hF l).continuous.continuousOn⟩
  have h1 := (hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)).const_mul g
  have h2 : HasFDerivAt (F l) (fderiv ℝ (F l) g) (g * NormedSpace.exp ((0 : ℝ) • X)) := by
    rw [zero_smul, NormedSpace.exp_zero, Matrix.mul_one]
    exact (((hF l).differentiable (by simp)) g).hasFDerivAt
  have h3 := h2.comp_hasDerivAt (0 : ℝ) h1
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at h3
  exact h3

def IsTest (ε : Fin n → Bool) (φ : Mx n → ℂ) : Prop := CSm ε φ ∧ HasCompactSupport fun g : UJ ε => φ (umat g)

theorem IsTest.integrable {φ F : Mx n → ℂ} (hφ : IsTest ε φ) (hF : CSm ε F) :
    Integrable (fun g : UJ ε => φ (umat g) * F (umat g)) (muG ε) :=
  (hφ.1.continuous.mul hF.continuous).integrable_of_hasCompactSupport hφ.2.mul_right

theorem exists_adjoint_ltr (x : Ltr ε) {φ : Mx n → ℂ} (hφ : IsTest ε φ) : ∃ ψ, IsTest ε ψ ∧ ∀ F, CSm ε F →
    ∫ g : UJ ε, φ (umat g) * ltrF x F (umat g) ∂(muG ε) = ∫ g : UJ ε, ψ (umat g) * F (umat g) ∂(muG ε) := by
  haveI : (muG ε).IsMulRightInvariant := ⟨fun g => indefinite_unitary_unimodular n ε g⟩
  rcases x with ⟨X, hX⟩ | ⟨k, hk⟩
  · let c : ℝ → UJ ε := fun t => mkU (NormedSpace.exp (t • X)) (exp_mem_UJ hX t)
    have hc : Continuous c := (umat_emb ε).isInducing.continuous_iff.2 (continuous_exp_smul X)
    have h0 : c 0 = 1 := (umat_emb ε).injective (by
      change NormedSpace.exp ((0 : ℝ) • X) = 1
      simp)
    have hadd : ∀ a b, c (a + b) = c a * c b := fun a b => (umat_emb ε).injective (exp_add_smul X a b)
    have ht : IsTest ε (rder X φ) := by
      refine ⟨hφ.1.rder hX, hφ.2.mono' fun g hg => ?_⟩
      by_contra hn
      apply hg
      have h1 := notMem_tsupport_iff_eventuallyEq.1 hn
      have h2 : Filter.Tendsto (fun t => g * c t) (𝓝 0) (𝓝 g) := by
        have h4 : Continuous fun t => g * c t := continuous_const.mul hc
        simpa only [h0, mul_one] using h4.tendsto 0
      have h3 : (fun t : ℝ => φ (umat g * NormedSpace.exp (t • X))) =ᶠ[𝓝 0] fun _ => 0 := h2.eventually h1
      show deriv _ 0 = 0
      rw [h3.deriv_eq, deriv_const]
    refine ⟨(-1 : ℂ) • rder X φ, ⟨ht.1.smul _, ht.2.mul_left⟩, fun F hF => ?_⟩
    have key := integral_rder_eq_zero (muG ε) c hc h0 hadd (fun g => φ (umat g) * F (umat g))
      (fun g => rder X φ (umat g) * F (umat g) + φ (umat g) * rder X F (umat g))
      (hφ.1.continuous.mul hF.continuous)
      ((ht.1.continuous.mul hF.continuous).add (hφ.1.continuous.mul (hF.rder hX).continuous))
      hφ.2.mul_right (ht.2.mul_right.add hφ.2.mul_right) (fun g => by
        have := (hφ.1.hasDerivAt hX g.2).fun_mul (hF.hasDerivAt hX g.2)
        simp only [zero_smul, NormedSpace.exp_zero, Matrix.mul_one] at this
        exact this)
    rw [integral_add (ht.integrable hF) (hφ.integrable (hF.rder hX))] at key
    simp only [Pi.smul_apply, smul_eq_mul, neg_mul, one_mul, integral_neg]
    exact eq_neg_of_add_eq_zero_right key
  · have hkU := K_le_UJ hk
    have hk' : k⁻¹ ∈ Kset ε := by
      refine ((maximal_compact_facts n ε).2.2.2.2 _).2 ⟨inv_mem_UJ hkU, ?_⟩
      rw [Matrix.inv_eq_left_inv (Matrix.mem_unitaryGroup_iff'.1 hk.1)]
      exact Unitary.star_mem hk.1
    refine ⟨fun g => φ (g * k⁻¹), ⟨hφ.1.rt hk', ?_⟩, fun F hF => ?_⟩
    · exact hφ.2.comp_homeomorph (Homeomorph.mulRight (mkU k⁻¹ (K_le_UJ hk')))
    · rw [← integral_mul_right_eq_self (fun g : UJ ε => φ (umat g * k⁻¹) * F (umat g)) (mkU k hkU)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
      show φ (umat g) * F (umat g * k) = φ (umat g * k * k⁻¹) * F (umat g * k)
      rw [Matrix.mul_assoc, mul_inv_UJ hkU, Matrix.mul_one]

theorem exists_adjoint_word (u : List (Ltr ε)) : ∀ {φ : Mx n → ℂ}, IsTest ε φ → ∃ ψ, IsTest ε ψ ∧ ∀ F, CSm ε F →
    ∫ g : UJ ε, φ (umat g) * wordF u F (umat g) ∂(muG ε) = ∫ g : UJ ε, ψ (umat g) * F (umat g) ∂(muG ε) := by
  induction u with
  | nil => exact fun hφ => ⟨_, hφ, fun _ _ => rfl⟩
  | cons x u ih =>
    intro φ hφ
    obtain ⟨ψ, h1, h2⟩ := exists_adjoint_ltr x hφ
    obtain ⟨χ, h3, h4⟩ := ih h1
    exact ⟨χ, h3, fun F hF => (h2 _ (hF.wordF u)).trans (h4 F hF)⟩

theorem eq_zero_of_test (H : UJ ε → ℂ) (hH : Continuous H)
    (h : ∀ φ, IsTest ε φ → ∫ g : UJ ε, φ (umat g) * H g ∂(muG ε) = 0) (y : UJ ε) : H y = 0 := by
  by_contra hy
  have hc : Continuous fun g => (star (H y) * H g).re := by fun_prop
  have hpos : 0 < (star (H y) * H y).re := by
    rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
    positivity
  have hU : {g | 0 < (star (H y) * H g).re} ∈ 𝓝 y := (isOpen_lt continuous_const hc).mem_nhds hpos
  have hemb : Topology.IsClosedEmbedding (fun g : UJ ε => (Matrix.of.symm (umat g) : Fin n → Fin n → ℂ)) :=
    umat_emb ε
  rw [hemb.isInducing.nhds_eq_comap] at hU
  obtain ⟨V, hV, hVU⟩ := Filter.mem_comap.1 hU
  obtain ⟨φ, hφs, hφc, hφd, hφr, hφ1⟩ := exists_contDiff_tsupport_subset (n := ⊤) hV
  have hψ : Continuous fun g : UJ ε => φ (Matrix.of.symm (umat g)) := hφd.continuous.comp hemb.continuous
  have hψc : HasCompactSupport fun g : UJ ε => φ (Matrix.of.symm (umat g)) := hφc.comp_isClosedEmbedding hemb
  have ht : IsTest ε (fun g => (φ (Matrix.of.symm g) : ℂ)) :=
    ⟨cSm_of_contDiff _ (Complex.ofRealCLM.contDiff.comp hφd), hψc.comp_left Complex.ofReal_zero⟩
  have hi : Integrable (fun g : UJ ε => star (H y) * ((φ (Matrix.of.symm (umat g)) : ℂ) * H g)) (muG ε) :=
    ((ht.1.continuous.mul hH).integrable_of_hasCompactSupport ht.2.mul_right).const_mul _
  have h1 := integral_re hi
  rw [integral_const_mul, h _ ht] at h1
  have h2 : 0 < ∫ g : UJ ε, φ (Matrix.of.symm (umat g)) * (star (H y) * H g).re ∂(muG ε) := by
    refine (hψ.mul hc).integral_pos_of_hasCompactSupport_nonneg_nonzero (x := y) hψc.mul_right (fun g => ?_) ?_
    · by_cases h0 : φ (Matrix.of.symm (umat g)) = 0
      · rw [h0, zero_mul]; exact le_rfl
      · exact mul_nonneg (hφr ⟨_, rfl⟩).1 (le_of_lt (hVU (hφs (subset_tsupport _ h0))))
    · rw [hφ1, one_mul]; exact hpos.ne'
  refine h2.ne' ?_
  simp only [mul_left_comm (star (H y)), RCLike.re_to_complex, Complex.re_ofReal_mul] at h1
  simpa using h1

end GlobalTheory.TypeSum.CoefClos
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.HeightProofs.RightDerivativeRelationOfLocallyUniformLimitStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TypeSum.CoefClos


theorem _root_.GlobalTheory.T.rightDerivativeRelation_of_locallyUniformLimit : ∀ (n : ℕ) (ε : Fin n → Bool) (F : Mx n → ℂ), CSm ε F → ∀ (m : ℕ) (c : Fin m → ℂ) (u : Fin m → List (Ltr ε)),
    (∀ C : Set (Mx n), IsCompact C → ∀ δ : ℝ, 0 < δ → ∃ f : Mx n → ℂ, CSm ε f ∧
      (∀ y ∈ C, y ∈ UJset ε → ‖F y - f y‖ < δ) ∧ ∀ y ∈ UJset ε, ∑ i, c i * wordF (u i) f y = 0) →
    ∀ y ∈ UJset ε, ∑ i, c i * wordF (u i) F y = 0 := by
  intro n ε F hF m c u hlim y hy
  have hmem : ∀ g : UJ ε, umat g ∈ UJset ε := fun g => g.2
  have hcont : Continuous fun g : UJ ε => ∑ i, c i * wordF (u i) F (umat g) := by
    refine continuous_finsetSum _ (fun i _ => ?_)
    exact continuous_const.mul (CSm.continuous (CSm.wordF hF (u i)))
  have key : ∀ φ, IsTest ε φ →
      ∫ g : UJ ε, φ (umat g) * ∑ i, c i * wordF (u i) F (umat g) ∂(muG ε) = 0 := by
    intro φ hφ
    choose ψ hψ hadj using fun i => exists_adjoint_word (u i) hφ

    have expand : ∀ G, CSm ε G →
        ∫ g : UJ ε, φ (umat g) * ∑ i, c i * wordF (u i) G (umat g) ∂(muG ε)
          = ∑ i, c i * ∫ g : UJ ε, ψ i (umat g) * G (umat g) ∂(muG ε) := by
      intro G hG
      have hfun : (fun g : UJ ε => φ (umat g) * ∑ i, c i * wordF (u i) G (umat g))
          = fun g => ∑ i, c i * (φ (umat g) * wordF (u i) G (umat g)) := by
        funext g
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => by ring)
      rw [hfun, MeasureTheory.integral_finsetSum]
      · refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [MeasureTheory.integral_const_mul, hadj i G hG]
      · intro i _
        exact (IsTest.integrable hφ (CSm.wordF hG (u i))).const_mul (c i)
    have h1 : CSm ε (fun _ : Mx n => (1 : ℂ)) := cSm_of_contDiff _ contDiff_const
    have hint1 : ∀ i, MeasureTheory.Integrable (fun g : UJ ε => ‖ψ i (umat g)‖) (muG ε) := by
      intro i
      simpa using (IsTest.integrable (hψ i) h1).norm
    set A : Fin m → ℝ := fun i => ∫ g : UJ ε, ‖ψ i (umat g)‖ ∂(muG ε) with hA
    set B : ℝ := ∑ i, ‖c i‖ * A i with hB
    have hA0 : ∀ i, 0 ≤ A i := fun i => MeasureTheory.integral_nonneg (fun g => norm_nonneg _)
    have hB0 : 0 ≤ B := Finset.sum_nonneg (fun i _ => mul_nonneg (norm_nonneg _) (hA0 i))
    set X := ∫ g : UJ ε, φ (umat g) * ∑ i, c i * wordF (u i) F (umat g) ∂(muG ε) with hX

    have bound : ∀ δ : ℝ, 0 < δ → ‖X‖ ≤ δ * B := by
      intro δ hδ
      let K : Set (UJ ε) := ⋃ i, tsupport (fun g : UJ ε => ψ i (umat g))
      have hK : IsCompact K := isCompact_iUnion (fun i => (hψ i).2.isCompact)
      have hC : IsCompact ((fun g : UJ ε => umat g) '' K) := hK.image (umat_emb ε).continuous
      obtain ⟨f, hf, hclose, hzero⟩ := hlim _ hC δ hδ
      have e0 : ∑ i, c i * ∫ g : UJ ε, ψ i (umat g) * f (umat g) ∂(muG ε) = 0 := by
        rw [← expand f hf]
        have hz : (fun g : UJ ε => φ (umat g) * ∑ i, c i * wordF (u i) f (umat g)) = fun _ => 0 := by
          funext g
          rw [hzero _ (hmem g), mul_zero]
        rw [hz, MeasureTheory.integral_zero]
      have hXf : X = ∑ i, c i * ((∫ g : UJ ε, ψ i (umat g) * F (umat g) ∂(muG ε))
          - ∫ g : UJ ε, ψ i (umat g) * f (umat g) ∂(muG ε)) := by
        rw [hX, expand F hF]
        simp only [mul_sub, Finset.sum_sub_distrib, e0, sub_zero]
      rw [hXf]
      refine (norm_sum_le _ _).trans ?_
      refine (Finset.sum_le_sum (fun i _ => ?_ : ∀ i ∈ Finset.univ, _ ≤ ‖c i‖ * (δ * A i))).trans
        (le_of_eq ?_)
      · rw [norm_mul]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        show _ ≤ δ * ∫ g : UJ ε, ‖ψ i (umat g)‖ ∂(muG ε)
        rw [← MeasureTheory.integral_sub (IsTest.integrable (hψ i) hF) (IsTest.integrable (hψ i) hf),
          ← MeasureTheory.integral_const_mul]
        refine MeasureTheory.norm_integral_le_of_norm_le ((hint1 i).const_mul δ)
          (Filter.Eventually.of_forall (fun g => ?_))
        rw [← mul_sub, norm_mul]
        by_cases hg : g ∈ tsupport (fun g : UJ ε => ψ i (umat g))
        · have hgC : umat g ∈ (fun g : UJ ε => umat g) '' K := ⟨g, Set.mem_iUnion.2 ⟨i, hg⟩, rfl⟩
          rw [mul_comm δ]
          exact mul_le_mul_of_nonneg_left (hclose _ hgC (hmem g)).le (norm_nonneg _)
        · have h0 : ψ i (umat g) = 0 :=
            image_eq_zero_of_notMem_tsupport (f := fun g : UJ ε => ψ i (umat g)) hg
          rw [h0]
          simp
      · rw [hB, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => by ring)
    by_contra hne
    have hpos : 0 < ‖X‖ := norm_pos_iff.2 hne
    have hle := bound (‖X‖ / (B + 1)) (div_pos hpos (by linarith))
    have hlt : ‖X‖ / (B + 1) * B < ‖X‖ := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
      nlinarith
    linarith
  have h := eq_zero_of_test (fun g : UJ ε => ∑ i, c i * wordF (u i) F (umat g)) hcont key (mkU y hy)
  simpa [umat_mkU] using h
end
end
