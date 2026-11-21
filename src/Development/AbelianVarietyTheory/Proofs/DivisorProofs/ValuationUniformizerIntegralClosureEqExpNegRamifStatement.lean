module

public import Mathlib

@[expose] public section

open IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_uniformizer_integralClosure_eq_exp_neg_ramificationIdx : ∀ (R K L : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra R L] [IsScalarTower R K L] [IsDedekindDomain (integralClosure R L)] [IsFractionRing (integralClosure R L) L] (P : IsDedekindDomain.HeightOneSpectrum (integralClosure R L)) (π : R), Irreducible π → P.valuation L (algebraMap K L (algebraMap R K π)) = WithZero.exp (-(P.asIdeal.ramificationIdx R : ℤ)) := by
  intro R K L _ _ _ _ _ _ _ _ _ _ _ _ _ P π hπ
  let v : HeightOneSpectrum R := IsDiscreteValuationRing.maximalIdeal R
  have hinj : Function.Injective (algebraMap R (integralClosure R L)) := by
    have h : Function.Injective (algebraMap R L) := by
      rw [IsScalarTower.algebraMap_eq R K L]
      exact (algebraMap K L).injective.comp (IsFractionRing.injective R K)
    rw [IsScalarTower.algebraMap_eq R (integralClosure R L) L, RingHom.coe_comp] at h
    exact Function.Injective.of_comp h
  let : FaithfulSMul R (integralClosure R L) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  let : P.asIdeal.LiesOver v.asIdeal := by
    constructor
    have hne : P.asIdeal.under R ≠ ⊥ := Ideal.under_ne_bot R P.ne_bot
    exact (IsLocalRing.eq_maximalIdeal (Ideal.IsPrime.isMaximal inferInstance hne)).symm
  rw [← HeightOneSpectrum.valuation_liesOver L v P, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_singleton v hπ.ne_zero hπ.maximalIdeal_eq,
    ← WithZero.exp_nsmul]
  simp
