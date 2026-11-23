module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.IsOrdProjZeroOfIsNilpotent
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Noetherian.Defs
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
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.CompleteFin

section

@[expose] public section

open UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite TensorProduct

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.completeFin :
    ∀ {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R] [Module.Finite R M], IsAdicComplete I M := by
  intro R _ M _ _ _ I _ _
  have hH : IsHausdorff I M := IsHausdorff.of_le_jacobson I M (IsAdicComplete.le_jacobson I)
  have hP : IsPrecomplete I M := by
    rw [← AdicCompletion.of_surjective_iff]
    have hR : Function.Surjective (AdicCompletion.of I R) := AdicCompletion.of_surjective_iff.mpr inferInstance
    intro x
    obtain ⟨t, rfl⟩ := AdicCompletion.ofTensorProduct_surjective_of_finite I M x
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul a m =>
      obtain ⟨r, rfl⟩ := hR a
      refine ⟨r • m, ?_⟩
      rw [AdicCompletion.ofTensorProduct_tmul, map_smul]
      ext n
      rw [AdicCompletion.val_smul_apply]
      simp
      try rfl
    | add a b ha hb =>
      obtain ⟨u, hu⟩ := ha
      obtain ⟨v, hv⟩ := hb
      exact ⟨u + v, by rw [map_add (f := _), map_add (f := _), hu, hv]⟩
  exact { toIsHausdorff := hH, toIsPrecomplete := hP }
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.AdmLocal

section

@[expose] public section

open UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite TensorProduct

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.ordAdm_maximalIdeal_and_finite_quotients :
    ∀ {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] [IsNoetherianRing R] [IsLocalRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [Module.Finite R M], OrdAdm (M := M) (IsLocalRing.maximalIdeal R) ∧ (Finite (IsLocalRing.ResidueField R) → ∀ k : ℕ, Finite (M ⧸ (IsLocalRing.maximalIdeal R ^ k • ⊤ : Submodule R M))) := by
  intro R _ M _ _ _ _ _ _
  haveI : IsArtinianRing (R ⧸ IsLocalRing.maximalIdeal R) := by
    letI := Ideal.Quotient.field (IsLocalRing.maximalIdeal R)
    infer_instance
  have hOrd : OrdAdm (M := M) (IsLocalRing.maximalIdeal R) := by
    refine ⟨UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.completeFin (IsLocalRing.maximalIdeal R), fun k => ?_⟩
    have hMax {I : Ideal R} [IsArtinianRing (R ⧸ I)] (P : Ideal R) [P.IsPrime]
        (h : I ≤ P) : P.IsMaximal := by
      have h1 : (P.map (Ideal.Quotient.mk I)).IsPrime :=
        Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
      have h2 : (P.map (Ideal.Quotient.mk I)).IsMaximal := IsArtinianRing.isMaximal_of_isPrime _
      have h3 := Ideal.comap_isMaximal_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
        (K := P.map (Ideal.Quotient.mk I))
      rwa [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
        Ideal.mk_ker, sup_eq_left.2 h] at h3
    have hArtPow (k : ℕ) : IsArtinianRing (R ⧸ IsLocalRing.maximalIdeal R ^ k) := by
      rw [isArtinianRing_iff_krullDimLE_zero, Ring.krullDimLE_zero_iff]
      intro p hp
      have h0 : IsLocalRing.maximalIdeal R ^ k ≤ p.comap (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ k)) := by
        intro x hx
        simp [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
      have h1 : (p.comap (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ k))).IsMaximal :=
        hMax _ (Ideal.IsPrime.le_of_pow_le h0)
      have h2 := Ideal.map_comap_of_surjective (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ k))
        Ideal.Quotient.mk_surjective p
      rcases Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ k))
          Ideal.Quotient.mk_surjective h1 with h | h
      · exact absurd (h2 ▸ h) hp.ne_top
      · exact h2 ▸ h
    haveI := hArtPow k
    rw [isFiniteLength_iff_isNoetherian_isArtinian]
    refine ⟨inferInstance, ?_⟩
    haveI : Module.Finite (R ⧸ IsLocalRing.maximalIdeal R ^ k)
        (M ⧸ (IsLocalRing.maximalIdeal R ^ k • ⊤ : Submodule R M)) :=
      Module.Finite.of_restrictScalars_finite R _ _
    exact isArtinian_of_surjective_algebraMap (R := R ⧸ IsLocalRing.maximalIdeal R ^ k)
      Ideal.Quotient.mk_surjective
  refine ⟨hOrd, fun hfin k => ?_⟩
  haveI : Finite (R ⧸ IsLocalRing.maximalIdeal R) := hfin
  haveI : IsNoetherian R M := isNoetherian_of_isNoetherianRing_of_finite R M
  induction k with
  | zero =>
    rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]
    infer_instance
  | succ n ih =>
    rw [pow_succ', Submodule.mul_smul]
    exact Submodule.finite_quotient_smul _ (IsNoetherian.noetherian _)
end
end
