module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.IsOrdProjZeroOfIsNilpotent
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
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
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.IsOrdProjZeroOfIsNilpotent
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap
public import Mathlib.RingTheory.Ideal.BigOperators
public import Mathlib.RingTheory.Ideal.GoingUp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.EigSum
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.EigUnitInt
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.EigNilInt

section

@[expose] public section

open UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite TensorProduct

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.eigNilInt :
    ∀ {O K : Type*} [CommRing O] [Field K] [Algebra O K] [IsLocalRing O] {M : Type*} [AddCommGroup M] [Module O M] [Module.Finite O M] (T : Module.End O M), LinearMap.range T ≤ IsLocalRing.maximalIdeal O • ⊤ → ∀ (μ : K) (y : K ⊗[O] M), y ≠ 0 → T.baseChange K y = μ • y → μ ≠ 0 → ¬ IsIntegral O μ⁻¹ := by
  intro O K _ _ _ _ M _ _ _ T hT μ y hy hμy hμ hint
  obtain ⟨p, hmon, -, hcoef, hp⟩ :=
    LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero
      (f := T) (I := IsLocalRing.maximalIdeal O) (hI := hT)
  have hK : Polynomial.aeval (T.baseChange K) p = 0 := by
    have e : T.baseChange K = Module.End.baseChangeHom O K M T := rfl
    rw [e, Polynomial.aeval_algHom_apply, hp, map_zero]
  have hev : Module.End.HasEigenvector (T.baseChange K) μ y :=
    Module.End.hasEigenvector_iff.mpr ⟨Module.End.mem_eigenspace_iff.mpr hμy, hy⟩
  have hq : Polynomial.aeval μ p = 0 := by
    have h1 := Module.End.aeval_apply_of_hasEigenvector (p := p.map (algebraMap O K)) hev
    rw [Polynomial.aeval_map_algebraMap, Polynomial.eval_map_algebraMap, hK,
      LinearMap.zero_apply] at h1
    exact (smul_eq_zero.mp h1.symm).resolve_right hy
  set n := p.natDegree with hn
  set ν := μ⁻¹ with hνdef
  have hνμ : ν * μ = 1 := inv_mul_cancel₀ hμ
  have key : (1 : K) + ∑ i ∈ Finset.range n, algebraMap O K (p.coeff i) * ν ^ (n - i) = 0 := by
    rw [Polynomial.aeval_eq_sum_range, Finset.sum_range_succ, hmon.coeff_natDegree, one_smul] at hq
    have h2 : ν ^ n * (∑ i ∈ Finset.range n, p.coeff i • μ ^ i + μ ^ n) = 0 := by
      rw [hq, mul_zero]
    rw [mul_add, Finset.mul_sum, ← mul_pow, hνμ, one_pow, add_comm] at h2
    rw [← h2]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hin : i ≤ n := (Finset.mem_range.mp hi).le
    have hp' : ν ^ n = ν ^ (n - i) * ν ^ i := by rw [← pow_add, Nat.sub_add_cancel hin]
    have e : ν ^ i * μ ^ i = 1 := by rw [← mul_pow, hνμ, one_pow]
    rw [Algebra.smul_def, hp']
    calc algebraMap O K (p.coeff i) * ν ^ (n - i)
        = algebraMap O K (p.coeff i) * ν ^ (n - i) * (ν ^ i * μ ^ i) := by rw [e, mul_one]
      _ = ν ^ (n - i) * ν ^ i * (algebraMap O K (p.coeff i) * μ ^ i) := by ring
  let C := integralClosure O K
  let ν' : C := ⟨ν, hint⟩
  have hs : (1 : C) + ∑ i ∈ Finset.range n, algebraMap O C (p.coeff i) * ν' ^ (n - i) = 0 := by
    apply Subtype.ext
    simpa [C, ν'] using key
  have hmem : ∑ i ∈ Finset.range n, algebraMap O C (p.coeff i) * ν' ^ (n - i) ∈
      (IsLocalRing.maximalIdeal O).map (algebraMap O C) := by
    refine Ideal.sum_mem _ fun i hi => Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_)
    have hin : i < n := Finset.mem_range.mp hi
    exact Ideal.pow_le_self (by omega) (hcoef i)
  have htop : (IsLocalRing.maximalIdeal O).map (algebraMap O C) = ⊤ := by
    rw [Ideal.eq_top_iff_one, eq_neg_of_add_eq_zero_left hs]
    exact (Ideal.neg_mem_iff _).mpr hmem
  have hker : RingHom.ker (algebraMap O C) ≤ IsLocalRing.maximalIdeal O :=
    IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top _)
  have hint' : (algebraMap O C).IsIntegral := fun x => Algebra.IsIntegral.isIntegral x
  exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top
    ((Ideal.map_eq_top_iff_of_ker_le _ hker hint').mp htop)
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.EigOrdInt

section

@[expose] public section

open UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite TensorProduct

private theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.eigOrdInt_inv
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] {I : Ideal R}
    {U e : Module.End R M} (h : IsOrdProj I U e) : ∃ V : Module.End R M, V * U * e = e := by
  have hm : ∀ x ∈ LinearMap.range e, U x ∈ LinearMap.range e := fun x hx => h.bij.mapsTo hx
  have hb : Function.Bijective (U.restrict hm) := by
    constructor
    · intro x y hxy
      exact Subtype.ext (h.bij.injOn x.2 y.2 (congrArg Subtype.val hxy))
    · intro y
      obtain ⟨x, hx, hxy⟩ := h.bij.surjOn y.2
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  let E := LinearEquiv.ofBijective _ hb
  let V : Module.End R M := (LinearMap.range e).subtype ∘ₗ E.symm.toLinearMap ∘ₗ e.rangeRestrict
  have hc : ∀ x, U (e x) = e (U x) := fun x => LinearMap.congr_fun h.comm.eq x
  have hV : ∀ z, e z = z → V (U z) = z := by
    intro z hz
    have : e.rangeRestrict (U z) = E ⟨z, z, hz⟩ := Subtype.ext (by
      show e (U z) = U z
      rw [← hc, hz])
    simp only [V, LinearMap.comp_apply, this]
    simp
  refine ⟨V, LinearMap.ext fun x => ?_⟩
  exact hV (e x) (LinearMap.congr_fun h.idem.eq x)

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.eigOrdInt :
    ∀ {O K : Type*} [CommRing O] [Field K] [Algebra O K] [IsLocalRing O] [IsAlgClosed K] {M : Type*} [AddCommGroup M] [Module O M] [Module.Finite O M] {U e : Module.End O M}, IsOrdProj (IsLocalRing.maximalIdeal O) U e → LinearMap.range (e.baseChange K) = ⨆ μ ∈ {μ : K | μ ≠ 0 ∧ IsIntegral O μ ∧ IsIntegral O μ⁻¹}, Module.End.maxGenEigenspace (U.baseChange K) μ := by
  intro O K _ _ _ _ _ M _ _ _ U e h
  refine UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.eigSum (U.baseChange K) (e.baseChange K) _ ?_ ?_ ?_ ?_
  · show _ * _ = _
    rw [← LinearMap.baseChange_mul, h.idem.eq]
  · show _ * _ = _ * _
    rw [← LinearMap.baseChange_mul, ← LinearMap.baseChange_mul, h.comm.eq]
  · intro μ y hy he hU
    obtain ⟨V, hV⟩ := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.eigOrdInt_inv h
    exact UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.eigUnitInt U V e hV μ y hy he hU
  · rintro μ y hy he hU ⟨h0, -, hi⟩
    obtain ⟨n, hn⟩ := h.nil 1
    have hp : ∀ k : ℕ, (U ^ k).baseChange K y = μ ^ k • y := by
      intro k
      induction k with
      | zero => rw [pow_zero, pow_zero, LinearMap.baseChange_one, one_smul, Module.End.one_apply]
      | succ k ih =>
        rw [pow_succ, LinearMap.baseChange_mul, Module.End.mul_apply, hU, map_smul, ih, smul_smul,
          pow_succ']
    refine UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.eigNilInt (U ^ n * (1 - e)) ?_ (μ ^ n) y hy ?_ (pow_ne_zero n h0) ?_
    · rintro _ ⟨x, rfl⟩
      have := hn x
      rw [pow_one] at this
      exact this
    · rw [LinearMap.baseChange_mul, Module.End.mul_apply, LinearMap.baseChange_sub,
        LinearMap.baseChange_one, LinearMap.sub_apply, he, sub_zero, Module.End.one_apply, hp]
    · rw [← inv_pow]
      exact hi.pow n
end
end
