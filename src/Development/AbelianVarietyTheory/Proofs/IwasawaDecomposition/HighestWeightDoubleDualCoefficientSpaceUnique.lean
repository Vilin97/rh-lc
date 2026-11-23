module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IncludeLInjective
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.RingHomOfBaseOrderToFraction
public import Formalism.LocalToGlobal.Divisibility.CoefMod
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.ConjugateSelfDual.Statement
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Objects
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Mathlib.Algebra.MvPolynomial.Funext
import ReciprocityTheory.Automorphisms.PlaceA
import ReciprocityTheory.GaloisValuations.GlobalA
import Mathlib.RingTheory.MvPolynomial
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HighestWeightDoubleDualUpperTriangularEigenvectoStatement
public import Formalism.LocalRingCardinality.DataCoeff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightTensorDualRepDualHighestWeightAtEmbedding
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.GradedWeylDivisibility.FinalB
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.ExtremalFactsProofA
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSpecialisationCoefficientSpaceToDualWeyl

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

namespace GlobalTheory.SpecFactor

open MvPolynomial

variable {K : Type} [Field K] {ι : Type} [DecidableEq ι] {n : ℕ}

noncomputable def specAt (τ₀ : ι) (y : ι × Fin n × Fin n → K) :
    Formalism.L2.DIV.Pol K ι n →ₐ[K] MvPolynomial (Fin n × Fin n) K :=
  MvPolynomial.aeval fun v => if v.1 = τ₀ then MvPolynomial.X v.2 else MvPolynomial.C (y v)

theorem eval_specAt (τ₀ : ι) (y : ι × Fin n × Fin n → K) (z : Fin n × Fin n → K) (w : Formalism.L2.DIV.Pol K ι n) :
    MvPolynomial.eval z (specAt τ₀ y w) =
      MvPolynomial.eval (fun v => if v.1 = τ₀ then z v.2 else y v) w := by
  have h : (MvPolynomial.eval z).comp (specAt τ₀ y).toRingHom =
      MvPolynomial.eval (fun v : ι × Fin n × Fin n => if v.1 = τ₀ then z v.2 else y v) := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp [specAt]
    · intro v
      by_cases hv : v.1 = τ₀ <;> simp [specAt, hv]
  exact congrArg (fun f : Formalism.L2.DIV.Pol K ι n →+* K => f w) h

theorem exists_specAt_ne [Infinite K] (τ₀ : ι) (w : Formalism.L2.DIV.Pol K ι n) (hw : w ≠ 0) :
    ∃ y, specAt τ₀ y w ≠ 0 := by
  by_contra h
  push_neg at h
  apply hw
  apply MvPolynomial.funext
  intro z
  have := congrArg (MvPolynomial.eval (fun v : Fin n × Fin n => z (τ₀, v))) (h z)
  rw [eval_specAt, map_zero] at this
  rw [map_zero, ← this]
  congr 2
  funext v
  split_ifs with hv
  · obtain ⟨a, b⟩ := v; simp only at hv; subst hv; rfl
  · rfl

theorem specAt_blockEmb (τ₀ : ι) (y : ι × Fin n × Fin n → K) (τ : ι) (F : MvPolynomial (Fin n × Fin n) K) :
    specAt τ₀ y (Formalism.GradedWeylDivisibility.blockEmb K τ F) =
      if τ = τ₀ then F else MvPolynomial.C (MvPolynomial.eval (fun v => y (τ, v)) F) := by
  unfold specAt Formalism.GradedWeylDivisibility.blockEmb
  rw [MvPolynomial.aeval_rename]
  split_ifs with h
  · subst h
    simp only [Function.comp_def, if_true]
    exact MvPolynomial.aeval_X_left_apply F
  · simp only [Function.comp_def, h, if_false]
    have hh : (MvPolynomial.aeval (R := K) fun x : Fin n × Fin n => (MvPolynomial.C (y (τ, x)) : MvPolynomial (Fin n × Fin n) K)).toRingHom =
        MvPolynomial.C.comp (MvPolynomial.eval fun v => y (τ, v)) := by
      apply MvPolynomial.ringHom_ext
      · intro r; simp
      · intro v; simp
    exact congrArg (fun f : MvPolynomial (Fin n × Fin n) K →+* MvPolynomial (Fin n × Fin n) K => f F) hh

end GlobalTheory.SpecFactor

namespace GlobalTheory.SpecFactor

open MvPolynomial

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}

theorem specAt_mem (lam : ι → DomWeight n) (τ₀ : ι) (y : ι × Fin n × Fin n → K) (P : Formalism.L2.DIV.Pol K ι n)
    (hP : P ∈ Formalism.L2.DIV.VV K lam) : specAt τ₀ y P ∈ nablaSq K n (lam τ₀) := by
  unfold Formalism.L2.DIV.VV Formalism.GradedWeylDivisibility.tensorLat at hP
  induction hP using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨F, hF, rfl⟩ := hx
    rw [map_prod]
    simp only [specAt_blockEmb]
    rw [Fintype.prod_eq_mul_prod_compl τ₀, if_pos rfl, mul_comm]
    have : ∏ i ∈ ({τ₀}ᶜ : Finset ι), (if i = τ₀ then F i else
        MvPolynomial.C (MvPolynomial.eval (fun v => y (i, v)) (F i))) =
        MvPolynomial.C (∏ i ∈ ({τ₀}ᶜ : Finset ι), MvPolynomial.eval (fun v => y (i, v)) (F i)) := by
      rw [map_prod]
      refine Finset.prod_congr rfl fun i hi => ?_
      rw [if_neg (by simpa using hi)]
    rw [this, ← MvPolynomial.smul_eq_C_mul]
    exact Submodule.smul_mem _ _ (hF τ₀)
  | zero => simp
  | add x z _ _ hx hz => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hz
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

theorem specAt_blockAct (τ₀ : ι) (y : ι × Fin n × Fin n → K) (M : Matrix (Fin n) (Fin n) K)
    (P : Formalism.L2.DIV.Pol K ι n) :
    specAt τ₀ y (Formalism.GradedWeylDivisibility.blockAct K (fun τ => if τ = τ₀ then M else 1) P) =
      Formalism.GradedWeylDivisibility.rowAct K M (specAt τ₀ y P) := by
  have h : (specAt τ₀ y).comp (Formalism.GradedWeylDivisibility.blockAct K (n := n) (fun τ => if τ = τ₀ then M else 1)) =
      (Formalism.GradedWeylDivisibility.rowAct K M).comp (specAt τ₀ y) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨τ, a, b⟩
    by_cases hτ : τ = τ₀
    · subst hτ
      simp [specAt, Formalism.GradedWeylDivisibility.blockAct, Formalism.GradedWeylDivisibility.rowAct]
    · set_option synthInstance.maxHeartbeats 100000 in
      simp only [AlgHom.comp_apply, Formalism.GradedWeylDivisibility.blockAct, specAt, MvPolynomial.aeval_X, hτ, if_false, map_sum, map_mul,
        MvPolynomial.aeval_C, Matrix.one_apply]
      rw [Finset.sum_eq_single a]
      · simp [hτ]
      · intro c _ hc; simp [Ne.symm hc]
      · simp
  exact congrArg (fun f : Formalism.L2.DIV.Pol K ι n →ₐ[K] MvPolynomial (Fin n × Fin n) K => f P) h

end GlobalTheory.SpecFactor

theorem GlobalTheory.specialise_factor : ∀ (K : Type) [Field K] [Infinite K] (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (lam : ι → DomWeight n) (τ₀ : ι) (w : Formalism.L2.DIV.Pol K ι n), w ∈ Formalism.L2.DIV.VV K lam → w ≠ 0 →
    ∃ φ : Formalism.L2.DIV.Pol K ι n →ₗ[K] MvPolynomial (Fin n × Fin n) K, φ w ≠ 0 ∧
      (∀ P ∈ Formalism.L2.DIV.VV K lam, φ P ∈ nablaSq K n (lam τ₀)) ∧
      ∀ (M : Matrix (Fin n) (Fin n) K) (P : Formalism.L2.DIV.Pol K ι n),
        φ (Formalism.GradedWeylDivisibility.blockAct K (fun τ => if τ = τ₀ then M else 1) P) = Formalism.GradedWeylDivisibility.rowAct K M (φ P) := by
  intro K _ _ n ι _ _ lam τ₀ w _ hw
  obtain ⟨y, hy⟩ := GlobalTheory.SpecFactor.exists_specAt_ne τ₀ w hw
  exact ⟨(GlobalTheory.SpecFactor.specAt τ₀ y).toLinearMap, hy,
    fun P hP => GlobalTheory.SpecFactor.specAt_mem lam τ₀ y P hP,
    fun M P => GlobalTheory.SpecFactor.specAt_blockAct τ₀ y M P⟩
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSpecialisationCoefficientSpaceToDualWeylStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_specialisation_coefficientSpace_to_dualWeyl : ∀ (K : Type) [Field K] [Infinite K] (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (lam : ι → DomWeight n) (τ₀ : ι) (w : Formalism.L2.DIV.Pol K ι n), w ∈ Formalism.L2.DIV.VV K lam → w ≠ 0 →
    ∃ φ : Formalism.L2.DIV.Pol K ι n →ₗ[K] MvPolynomial (Fin n × Fin n) K, φ w ≠ 0 ∧
      (∀ P ∈ Formalism.L2.DIV.VV K lam, φ P ∈ nablaSq K n (lam τ₀)) ∧
      ∀ (M : Matrix (Fin n) (Fin n) K) (P : Formalism.L2.DIV.Pol K ι n),
        φ (Formalism.GradedWeylDivisibility.blockAct K (fun τ => if τ = τ₀ then M else 1) P) = Formalism.GradedWeylDivisibility.rowAct K M (φ P) := by
  first | exact @GlobalTheory.specialise_factor | exact GlobalTheory.specialise_factor | (intros; apply GlobalTheory.specialise_factor <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NablaSqUpperEigenvectorWeightEqHighest

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section

open scoped Matrix

namespace GlobalTheory.HwEigen

theorem rowAct_transvection_eq_eval (K : Type) [Field K] (n : ℕ) (a b : Fin n) (hab : a ≠ b) (s : K)
    (f : MvPolynomial (Fin n × Fin n) K) :
    Formalism.GradedWeylDivisibility.rowAct K (n := n) (Matrix.transvection a b s)ᵀ f =
      (Formalism.GradedWeylDivisibility.rowGen K a b f).eval (MvPolynomial.C s) := by
  have h : (Polynomial.evalRingHom (MvPolynomial.C s)).comp (Formalism.GradedWeylDivisibility.rowGen K (n := n) a b).toRingHom =
      (Formalism.GradedWeylDivisibility.rowAct K (n := n) (Matrix.transvection a b s)ᵀ).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [Formalism.GradedWeylDivisibility.rowGen, Formalism.GradedWeylDivisibility.rowAct]
    · intro v
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Formalism.GradedWeylDivisibility.rowGen,
        Formalism.GradedWeylDivisibility.rowAct, MvPolynomial.aeval_X, Polynomial.coe_evalRingHom]
      simp [Matrix.transvection, Matrix.transpose_apply, Matrix.add_apply, Matrix.one_apply,
        Matrix.single_apply, add_mul, Finset.sum_add_distrib]
      split_ifs with hv
      · rw [Finset.sum_eq_single a]
        · simp only [hv, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, and_self, if_true]
          exact mul_comm _ _
        · intro c _ hc
          simp [Ne.symm hc]
        · simp
      · simp [Ne.symm hv]
  exact (congrArg (fun φ => φ f) h).symm

end GlobalTheory.HwEigen

namespace GlobalTheory.HwEigen

theorem sqAct_smul' (K : Type) [Field K] (n : ℕ) (lam : DomWeight n) (B : GL (Fin n) K) (c : K)
    (f : MvPolynomial (Fin n × Fin n) K) : sqAct K n lam B (c • f) = c • sqAct K n lam B f := by
  unfold sqAct
  rw [map_smul, smul_comm]

theorem rowDiv_eq_zero_of_fixed (K : Type) [Field K] [Infinite K] (n : ℕ) (a b : Fin n) (hab : a ≠ b)
    (f : MvPolynomial (Fin n × Fin n) K)
    (hfix : ∀ s : K, Formalism.GradedWeylDivisibility.rowAct K (n := n) (Matrix.transvection a b s)ᵀ f = f)
    (k : ℕ) (hk : 1 ≤ k) : Formalism.GradedWeylDivisibility.rowDiv K a b k f = 0 := by
  have hP : Formalism.GradedWeylDivisibility.rowGen K a b f - Polynomial.C f = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply Set.infinite_of_injective_forall_mem (f := fun s : K => (MvPolynomial.C s : MvPolynomial (Fin n × Fin n) K))
      (MvPolynomial.C_injective _ _)
    intro s
    simp only [Set.mem_setOf_eq, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_C]
    rw [← rowAct_transvection_eq_eval K n a b hab s, hfix s, sub_self]
  have h := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p k) hP
  simp only [Polynomial.coeff_sub, Polynomial.coeff_C, Polynomial.coeff_zero] at h
  rw [if_neg (by omega), sub_zero] at h
  exact h

theorem mu_eq_of_upper_eigen : ∀ (K : Type) [Field K] [CharZero K] (n : ℕ) (lam0 : DomWeight n) (mu : Fin n → ℤ)
    (f : MvPolynomial (Fin n × Fin n) K), f ∈ nablaSq K n lam0 → f ≠ 0 →
    (∀ B : GL (Fin n) K, (B : Matrix (Fin n) (Fin n) K).BlockTriangular id →
      sqAct K n lam0 B f = (∏ a, (B : Matrix (Fin n) (Fin n) K) a a ^ mu a) • f) → mu = lam0.w := by
  intro K _ _ n lam0 mu f hf hf0 hB
  haveI : Infinite K := inferInstance

  have hkill : ∀ a b : Fin n, a < b → ∀ k : ℕ, 1 ≤ k → Formalism.GradedWeylDivisibility.rowDiv K a b k f = 0 := by
    intro a b hab k hk
    have hne : a ≠ b := ne_of_lt hab
    apply rowDiv_eq_zero_of_fixed K n a b hne f _ k hk
    intro s
    have hdet : (Matrix.transvection a b s).det = 1 := Matrix.det_transvection_of_ne a b hne s
    let B : GL (Fin n) K := Matrix.nonsingInvUnit _ (by rw [hdet]; exact isUnit_one)
    have hBv : (B : Matrix (Fin n) (Fin n) K) = Matrix.transvection a b s := rfl
    have hent : ∀ i j, (B : Matrix (Fin n) (Fin n) K) i j = (if i = j then 1 else 0) + (if a = i ∧ b = j then s else 0) := by
      intro i j
      rw [hBv]
      simp [Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
    have htri : (B : Matrix (Fin n) (Fin n) K).BlockTriangular id := by
      intro i j hij
      rw [hent]
      have h1 : i ≠ j := fun h => by subst h; exact lt_irrefl _ hij
      have h2 : ¬ (a = i ∧ b = j) := by
        rintro ⟨rfl, rfl⟩
        exact lt_asymm hab hij
      simp [h1, h2]
    have hdiag : ∀ i, (B : Matrix (Fin n) (Fin n) K) i i = 1 := by
      intro i
      rw [hent]
      have h2 : ¬ (a = i ∧ b = i) := by
        rintro ⟨rfl, h⟩
        exact hne h.symm
      simp [h2]
    have h := hB B htri
    simp only [hdiag, one_zpow, Finset.prod_const_one, one_smul] at h
    have hdp : detPow K n B lam0.detShift = 1 := by
      unfold detPow
      have : Matrix.GeneralLinearGroup.det B = 1 := by
        ext
        simp [Matrix.GeneralLinearGroup.val_det_apply, hBv, hdet]
      rw [this, one_zpow, Units.val_one]
    unfold sqAct at h
    rw [hdp, one_smul, hBv] at h
    exact h

  obtain ⟨c, hc⟩ := Formalism.GradedWeylDivisibility.hwLine K n n le_rfl lam0.natW (PI.WGB.natW_anti_A lam0) f hf hkill
  have he : extremal K n lam0 ≠ 0 := Formalism.GradedWeylDivisibility.hwNe K n n le_rfl lam0.natW
  have hce : f = c • extremal K n lam0 := hc
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hf0 (by rw [hce, zero_smul])

  funext i
  let d : Fin n → K := Function.update (fun _ => 1) i 2
  have hdd : (Matrix.diagonal d).det = 2 := by
    rw [Matrix.det_diagonal, Finset.prod_eq_single i]
    · simp [d]
    · intro j _ hj
      simp [d, hj]
    · simp
  let B : GL (Fin n) K := Matrix.nonsingInvUnit _ (by rw [hdd]; exact isUnit_iff_ne_zero.mpr two_ne_zero)
  have hBv : (B : Matrix (Fin n) (Fin n) K) = Matrix.diagonal d := rfl
  have htri : (B : Matrix (Fin n) (Fin n) K).BlockTriangular id := by
    rw [hBv]; exact Matrix.blockTriangular_diagonal d
  have h := hB B htri
  rw [hce, sqAct_smul', GlobalTheory.AlgWtF.DDHw.sqAct_upper K n lam0 B htri, smul_smul, smul_smul] at h
  have h2 := smul_left_injective K he h
  have hprod : ∀ m : Fin n → ℤ, (∏ a, (B : Matrix (Fin n) (Fin n) K) a a ^ m a) = (2 : K) ^ m i := by
    intro m
    rw [Finset.prod_eq_single i]
    · simp [hBv, d]
    · intro j _ hj
      simp [hBv, d, hj]
    · simp
  simp only [hprod] at h2
  have h3 : ((2 : K) ^ lam0.w i) = (2 : K) ^ mu i := by
    have := h2
    rw [mul_comm] at this
    exact (mul_right_cancel₀ hc0 this)
  have h4 : (((2 : ℚ) ^ lam0.w i : ℚ) : K) = (((2 : ℚ) ^ mu i : ℚ) : K) := by
    rw [Rat.cast_zpow, Rat.cast_zpow, Rat.cast_ofNat]
    exact h3
  have h5 := Rat.cast_injective h4
  exact (zpow_right_injective₀ (by norm_num : (0 : ℚ) < 2) (by norm_num) h5).symm

end GlobalTheory.HwEigen
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NablaSqUpperEigenvectorWeightEqHighestStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

theorem _root_.GlobalTheory.T.nablaSq_upperEigenvector_weight_eq_highest : ∀ (K : Type) [Field K] [CharZero K] (n : ℕ) (lam0 : DomWeight n) (mu : Fin n → ℤ)
    (f : MvPolynomial (Fin n × Fin n) K), f ∈ nablaSq K n lam0 → f ≠ 0 →
    (∀ B : GL (Fin n) K, (B : Matrix (Fin n) (Fin n) K).BlockTriangular id →
      sqAct K n lam0 B f = (∏ a, (B : Matrix (Fin n) (Fin n) K) a a ^ mu a) • f) → mu = lam0.w := by
  first | exact @GlobalTheory.HwEigen.mu_eq_of_upper_eigen | exact GlobalTheory.HwEigen.mu_eq_of_upper_eigen | (intros; apply GlobalTheory.HwEigen.mu_eq_of_upper_eigen <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HighestWeightDoubleDualCoefficientSpaceUnique

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

namespace GlobalTheory.AlgWtF.DDHw

theorem dd_hw_unique : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (ι : Type) [Fintype ι] (K : Type) [Field K] [CharZero K]
    (emb : ι → L →+* K) (lam : ι → DomWeight n), GlobalTheory.AlgWtF.CMDist emb → ∀ (τ₀ : ι) (mu : Fin n → ℤ),
      NX.HWAtF (IsCMField.complexConj L : L →+* L) (GlobalTheory.AlgWtF.wtRepF emb lam).dual (emb τ₀) mu → mu = (lam τ₀).w := by
  intro L _ _ _ n ι _ K _ _ emb lam hd τ₀ mu h
  classical
  haveI : Infinite K := Infinite.of_injective (Nat.cast : ℕ → K) Nat.cast_injective
  obtain ⟨w, hwV, hw0, hB⟩ := GlobalTheory.T.highestWeight_doubleDual_upperTriangular_eigenvector L n ι K emb lam hd τ₀ mu h
  obtain ⟨φ, hφ0, hφV, hφA⟩ := GlobalTheory.T.exists_specialisation_coefficientSpace_to_dualWeyl K n ι lam τ₀ w hwV hw0
  refine GlobalTheory.T.nablaSq_upperEigenvector_weight_eq_highest K n (lam τ₀) mu (φ w) (hφV w hwV) hφ0 fun B hBt => ?_
  have hc0 : detPow K n B (lam τ₀).detShift ≠ 0 := by
    rw [detPow]; exact Units.ne_zero _
  rw [sqAct, ← hφA, hB B hBt, map_smul, smul_smul, ← mul_assoc, mul_inv_cancel₀ hc0, one_mul]

end GlobalTheory.AlgWtF.DDHw
end
end
