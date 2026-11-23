module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ToDegInjective
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.EventuallyMQGrFiniteAnnihilator
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.FgHolds
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.GrEqRange
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.HerbrandFinLen
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.HomHolds
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.LocLenAPieceIdeal2LeTwoPow
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.LocLenQuotientWeightPieceLeOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.LocalizedLengthLeOfSurjective
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.SignHolds
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.TspHolds
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.OrbitVanishingLocal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ToDegInjective
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.EulerVanishingBelowDimension
import Mathlib.Tactic.Linter.HaveILetI
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.RuleFin
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.RuleGr
public import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.UZGen

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.IntHolds

section

@[expose] public section

open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

theorem UpperTheory.V.Alg.M.int_holds :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (K : Type) [Field K] [Algebra O K] [IsAlgClosed K] [FaithfulSMul O K] (v : K → ℝ), IsNVal O K v → ∀ y : K, IsIntegral O y → y ≠ 0 → 0 ≤ v y := by
  intro O _ _ _ _ _ K _ _ _ _ v hv y hy hy0
  have v1 : v 1 = 0 := by
    have h := hv.mul 1 1 one_ne_zero one_ne_zero
    rw [one_mul] at h
    linarith
  have vneg : ∀ z : K, z ≠ 0 → v (-z) = v z := by
    intro z hz
    have h1 := hv.mul (-1) (-1) (neg_ne_zero.mpr one_ne_zero) (neg_ne_zero.mpr one_ne_zero)
    rw [neg_one_mul, neg_neg, v1] at h1
    have h2 := hv.mul (-1) z (neg_ne_zero.mpr one_ne_zero) hz
    rw [neg_one_mul] at h2
    linarith
  have vpow : ∀ k : ℕ, v (y ^ k) = k * v y := by
    intro k
    induction k with
    | zero => simp [v1]
    | succ k ih =>
      rw [pow_succ, hv.mul _ _ (pow_ne_zero _ hy0) hy0, ih]
      push_cast
      ring
  have vsum : ∀ (s : Finset ℕ) (f : ℕ → K) (c : ℝ), (∀ i ∈ s, f i ≠ 0 → c ≤ v (f i)) →
      (∑ i ∈ s, f i) ≠ 0 → c ≤ v (∑ i ∈ s, f i) := by
    intro s f c
    induction s using Finset.induction_on with
    | empty => intro _ h; simp at h
    | insert a s ha ih =>
      intro hf hs
      rw [Finset.sum_insert ha] at hs ⊢
      by_cases hfa : f a = 0
      · rw [hfa, zero_add] at hs ⊢
        exact ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)) hs
      by_cases hS : (∑ i ∈ s, f i) = 0
      · rw [hS, add_zero]
        exact hf a (Finset.mem_insert_self a s) hfa
      have h1 := hv.add _ _ hfa hS hs
      have h2 := hf a (Finset.mem_insert_self a s) hfa
      have h3 := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)) hS
      exact le_trans (le_min h2 h3) h1
  by_contra hneg
  push_neg at hneg
  obtain ⟨p, hpm, hp⟩ := hy
  have hsum := hp
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hpm.coeff_natDegree, map_one, one_mul] at hsum
  have hS : (∑ i ∈ Finset.range p.natDegree, algebraMap O K (p.coeff i) * y ^ i) = -(y ^ p.natDegree) :=
    eq_neg_of_add_eq_zero_left hsum
  have hyn : y ^ p.natDegree ≠ 0 := pow_ne_zero _ hy0
  have hS0 : (∑ i ∈ Finset.range p.natDegree, algebraMap O K (p.coeff i) * y ^ i) ≠ 0 := by
    rw [hS]
    exact neg_ne_zero.mpr hyn
  have hnpos : 0 < p.natDegree := by
    rcases Nat.eq_zero_or_pos p.natDegree with h | h
    · exfalso
      rw [h, Finset.sum_range_zero, pow_zero] at hS
      exact one_ne_zero (neg_eq_zero.mp hS.symm)
    · exact h
  have hterm : ∀ i ∈ Finset.range p.natDegree, algebraMap O K (p.coeff i) * y ^ i ≠ 0 →
      ((p.natDegree - 1 : ℕ) : ℝ) * v y ≤ v (algebraMap O K (p.coeff i) * y ^ i) := by
    intro i hi hne
    have hc : p.coeff i ≠ 0 := by
      intro h
      apply hne
      simp [h]
    have hmc : algebraMap O K (p.coeff i) ≠ 0 := by
      intro h
      apply hc
      exact (FaithfulSMul.algebraMap_injective O K) (by rw [h, map_zero])
    rw [hv.mul _ _ hmc (pow_ne_zero _ hy0), hv.base _ hc, vpow]
    have hi' : i ≤ p.natDegree - 1 := by
      have := Finset.mem_range.mp hi
      omega
    have hle : ((p.natDegree - 1 : ℕ) : ℝ) * v y ≤ (i : ℝ) * v y := by
      apply mul_le_mul_of_nonpos_right _ hneg.le
      exact_mod_cast hi'
    have h0 : (0 : ℝ) ≤ ((IsDiscreteValuationRing.addVal O (p.coeff i)).toNat : ℝ) := Nat.cast_nonneg _
    linarith
  have hbound : ((p.natDegree - 1 : ℕ) : ℝ) * v y ≤
      v (∑ i ∈ Finset.range p.natDegree, algebraMap O K (p.coeff i) * y ^ i) :=
    vsum (Finset.range p.natDegree) (fun i => algebraMap O K (p.coeff i) * y ^ i) _ hterm hS0
  rw [hS, vneg _ hyn, vpow, Nat.cast_pred hnpos] at hbound
  linarith
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ValuationNonnegApplyDegreeZeroOfOnS

section

@[expose] public section

open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

theorem UpperTheory.V.Alg.M.valuation_nonneg_apply_degreeZero_of_onS :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (K : Type) [Field K] [Algebra O K] [IsAlgClosed K] [FaithfulSMul O K] (v : K → ℝ), IsNVal O K v →
    ∀ (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O) (I : Ideal A), M2 𝒜 I → ∀ ξ : A →ₐ[O] K, OnS I ξ → ∀ b ∈ 𝒜 0, ξ b ≠ 0 → 0 ≤ v (ξ b) := by
  intro O _ _ _ _ _ K _ _ _ _ v hv A _ _ 𝒜 _ _ x I hI ξ hξ b hb hne
  classical
  set M : Submodule O K := Submodule.map ξ.toLinearMap (𝒜 0) with hMdef
  have hker : ∀ f ∈ I, ξ f = 0 := hξ
  let ξ' : (A ⧸ I) →ₐ[O] K := Ideal.Quotient.liftₐ I ξ hker
  have hcomp : ξ.toLinearMap = ξ'.toLinearMap.comp (Ideal.Quotient.mkₐ O I).toLinearMap := by
    apply LinearMap.ext
    intro a
    rfl
  have hMfg : M.FG := by
    rw [hMdef, hcomp, Submodule.map_comp]
    exact Submodule.FG.map _ hI
  haveI : IsNoetherian O M := isNoetherian_of_fg_of_noetherian M hMfg
  have hle : Subalgebra.toSubmodule (Algebra.adjoin O {ξ b}) ≤ M := by
    intro z hz
    have hz' : z ∈ Algebra.adjoin O {ξ b} := hz
    clear hz
    rw [hMdef, Submodule.mem_map]
    induction hz' using Algebra.adjoin_induction with
    | mem w hw =>
      rw [Set.mem_singleton_iff] at hw
      exact ⟨b, hb, hw.symm⟩
    | algebraMap r =>
      exact ⟨algebraMap O A r, SetLike.algebraMap_mem_graded 𝒜 r, by simp⟩
    | add w₁ w₂ _ _ h₁ h₂ =>
      obtain ⟨c₁, hc₁, e₁⟩ := h₁
      obtain ⟨c₂, hc₂, e₂⟩ := h₂
      exact ⟨c₁ + c₂, add_mem hc₁ hc₂, by simp [← e₁, ← e₂]⟩
    | mul w₁ w₂ _ _ h₁ h₂ =>
      obtain ⟨c₁, hc₁, e₁⟩ := h₁
      obtain ⟨c₂, hc₂, e₂⟩ := h₂
      have hm : c₁ * c₂ ∈ 𝒜 (0 + 0) := SetLike.mul_mem_graded hc₁ hc₂
      rw [add_zero] at hm
      exact ⟨c₁ * c₂, hm, by simp [← e₁, ← e₂]⟩
  haveI : IsNoetherian O (Subalgebra.toSubmodule (Algebra.adjoin O {ξ b})) := isNoetherian_of_le hle
  have hint : IsIntegral O (ξ b) :=
    isIntegral_of_submodule_noetherian (Algebra.adjoin O {ξ b}) inferInstance (ξ b)
      (Algebra.subset_adjoin (Set.mem_singleton _))
  exact int_holds O K v hv (ξ b) hint hne
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.TwoSigned

section

@[expose] public section

open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

theorem UpperTheory.V.Alg.M.up_holds :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (K : Type) [Field K] [Algebra O K] [IsAlgClosed K] [FaithfulSMul O K] (v : K → ℝ), IsNVal O K v →
    ∀ (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O), IsWRing 𝒜 x →
    ∀ (r s r' s' m : ℕ) (Q : Eqns 𝒜 x r s r' s' m),
    SpansCot x 𝒜 (-1) Q.F → SpansCot x 𝒜 (-2) Q.G → M2 𝒜 Q.ideal → M3 𝒜 K x Q.ideal → M4 𝒜 K Q.ideal →
    ∀ a : 𝒜 0, M5 𝒜 K x Q.ideal a → ∀ T : Finset (A →ₐ[O] K), Covers 𝒜 Q.ideal T →
    ∀ J : Ideal (mR Q), (GMod.self (mGr Q)).IsHomSub J → secs (ts Q) ≤ J → (∀ i, algebraMap (𝒜 0) (mR Q) ⟨Q.Z i, (Q.hZ i).1⟩ ∈ J) →
      ∀ᶠ d in atTop, (chi [(0, algebraMap (𝒜 0) (mR Q) a)] (mQ Q J) d : ℝ) ≤ 2 ^ (r + 1 + r') * ∑ ξ ∈ T, v (ξ a) := by
  intro O _ _ _ _ _ K _ _ _ _ v hv A _ _ 𝒜 _ _ x hW r s r' s' m Q hF hG h2 h3 h4 a h5 T hT J hJ hsec hZ
  classical
  have hfg := fg_holds O A 𝒜 x hW
  have hN : ∀ i, (mN 𝒜 (Q.F (Fin.last r)) i).FG := by
    intro i
    fin_cases i
    · exact hfg _
    · exact hfg _
    · exact (Submodule.fg_span_singleton _).sup (((hfg _).mul (hfg _)).mul (hfg _))
  let X : HidaSetting 3 := { B := 𝒜 0, R := mR Q, 𝒜 := mGr Q, std := std_holds (𝒜 0) A 3 _ hN }
  have hself : (GMod.self (mGr Q)).IsGr (mGr Q) :=
    ⟨fun {d e} {p} {q : mR Q} (hp : p ∈ mGr Q d) (hq : q ∈ mGr Q e) => (SetLike.mul_mem_graded hp hq : p * q ∈ mGr Q (d + e)),
      rees_internal _, Module.Finite.self (mR Q)⟩
  have hGr : (mQ Q J).IsGr (mGr Q) := ((ruleGr 3 X _ hself).1 J hJ).2
  have hfin : ∀ d, Module.Finite (𝒜 0) ((mQ Q J).gr d) := (ruleFin 3 X _ hGr).1
  obtain ⟨hI, -, -⟩ := hom_holds O A 𝒜 x hW r s r' s' m Q
  have hD : ∀ ξ : A →ₐ[O] K, TwoSigned 𝒜 ξ ↔ ¬ idD 𝒜 ≤ RingHom.ker (res0 𝒜 ξ) := by
    intro ξ
    obtain ⟨hn, hp⟩ := sign_holds O A 𝒜 x hW K ξ
    rw [TwoSigned, hn, hp]
    constructor
    · rintro ⟨⟨f, hf, hf0⟩, g, hg, hg0⟩ hle
      have hm : f * g ∈ 𝒜 0 := by
        have := SetLike.GradedMul.mul_mem hf hg
        simpa using this
      have h1 : (⟨f * g, hm⟩ : 𝒜 0) ∈ idD 𝒜 := Ideal.subset_span ⟨f, hf, g, hg, rfl⟩
      have h2 : ξ (f * g) = 0 := hle h1
      rw [map_mul] at h2
      exact mul_ne_zero hf0 hg0 h2
    · intro h
      by_contra hc
      refine h (Ideal.span_le.2 ?_)
      rintro b ⟨f, hf, g, hg, hb⟩
      show ξ (b : A) = 0
      rw [hb, map_mul]
      by_contra hne
      exact hc ⟨⟨f, hf, left_ne_zero_of_mul hne⟩, g, hg, right_ne_zero_of_mul hne⟩
  have hpos : ∀ ξ ∈ T, ξ a ≠ 0 ∧ 0 ≤ v (ξ a) := fun ξ hξ =>
    ⟨h5.2.2 ξ (hT.1 ξ hξ).1 (hT.1 ξ hξ).2,
      valuation_nonneg_apply_degreeZero_of_onS O K v hv A 𝒜 x Q.ideal h2 ξ (hT.1 ξ hξ).1 a a.2 (h5.2.2 ξ (hT.1 ξ hξ).1 (hT.1 ξ hξ).2)⟩
  have hsum : ∑ σ ∈ T.image (res0 𝒜), v (σ a) ≤ ∑ ξ ∈ T, v (ξ a) :=
    Finset.sum_image_le_of_nonneg (f := fun σ : 𝒜 0 →ₐ[O] K => v (σ a)) (g := res0 𝒜) (s := T) fun σ hσ => by
      obtain ⟨ξ, hξ, rfl⟩ := Finset.mem_image.1 hσ
      exact (hpos ξ hξ).2
  filter_upwards [eventually_mQ_gr_finite_annihilator O K A 𝒜 x hW r s r' s' m Q hF hG h2 h3 J hJ hsec hZ, eventually_ge_atTop 1] with d hd hd1
  haveI := hfin d
  have key := th_holds O K v hv (𝒜 0) ((mQ Q J).gr d) hd.1 a (T.image (res0 𝒜)) (2 ^ (r + 1 + r')) ?_ ?_
  · rw [chi_single0 _ hGr.internal]
    refine key.trans ?_
    push_cast
    exact mul_le_mul_of_nonneg_left hsum (by positivity)
  · intro σ hσ
    obtain ⟨ξ, hξ, rfl⟩ := Finset.mem_image.1 hσ
    refine ⟨(hpos ξ hξ).1, (hpos ξ hξ).2, ?_⟩
    have hσ' := (hD ξ).1 (hT.1 ξ hξ).2
    refine (locLen_mQ_gr_le_locLen_aPiece O K A 𝒜 x hW r s r' s' m Q J hsec hZ _ hσ' d hd1).trans ?_
    push_cast
    exact locLen_aPiece_ideal2_le_two_pow O K A 𝒜 x hW r s r' s' m Q _ (locLen_quotientWeightPiece_le_one O K A 𝒜 x hW _ hI h2 h4 _ hσ') _
  · intro σ hσ
    refine hd.2 σ ?_
    by_contra hc
    rw [not_or] at hc
    obtain ⟨ξ, hξ, rfl⟩ := tsp_holds O K A 𝒜 x hW _ hI σ fun b hb => by
      by_contra hne
      exact hc.2 ⟨b, hb, hne⟩
    obtain ⟨ξ', hξ', t, rfl⟩ := hT.2 ξ hξ ((hD ξ).2 hc.1)
    refine hσ (Finset.mem_image.2 ⟨ξ', hξ', AlgHom.ext fun b => ?_⟩)
    show ξ' (b : A) = act 𝒜 (tz t) ξ' (b : A)
    rw [act_of_mem 𝒜 _ _ b.2]
    simp
end
end
