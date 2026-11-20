import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreFlagProjSpecialDimSteps
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericDimGe
import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

namespace PrimeDimLeTrdeg

attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem proof : Statement := by
  intro O _ _ _ K _ _ ι _ P hPp hPC
  classical
  let F := FractionRing O

  let M : Submonoid (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) := (nonZeroDivisors O).map (C : O →+* ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)
  have : IsLocalization M (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι) := MvPolynomial.isLocalization (nonZeroDivisors O) F
  have hdisj : Disjoint (M : Set (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)) (P : Set (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)) := by
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨a, ha, rfl⟩ hmem
    have : a ∈ P.comap (C : O →+* ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) := hmem
    rw [hPC] at this
    exact nonZeroDivisors.ne_zero ha ((Submodule.mem_bot _).1 this)
  have hG : (genFib P).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint M (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι) P hPp hdisj
  have hle : ringKrullDim (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι ⧸ P) ≤ ringKrullDim (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ genFib P) + 1 :=
    GenericDimGe.proof.{0} O K ι P hPp hPC

  have hB : ringKrullDim (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ genFib P) =
      (Algebra.trdeg F (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ genFib P)).toENat :=
    GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg F
  have hcomap : (genFib P).comap (algebraMap (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι)) = P :=
    IsLocalization.under_map_of_isPrime_disjoint M (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι) hPp hdisj
  let φ : (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι ⧸ P) →+* (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ genFib P) :=
    Ideal.quotientMap (genFib P) (algebraMap (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι)) hcomap.ge
  have hφ : Function.Injective φ := Ideal.quotientMap_injective' hcomap.le
  let _ : Algebra (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι ⧸ P) (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ genFib P) := φ.toAlgebra
  have : IsScalarTower O (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι ⧸ P) (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ genFib P) :=
    IsScalarTower.of_algebraMap_eq fun a => by
      change _ = φ (Ideal.Quotient.mk P (C a))
      simp [φ, Ideal.quotientMap_mk]
      rfl
  have : FaithfulSMul (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι ⧸ P) (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ genFib P) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hφ
  have : FaithfulSMul O (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι ⧸ P) := by
    refine (faithfulSMul_iff_algebraMap_injective _ _).2 ((injective_iff_map_eq_zero (algebraMap O (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι ⧸ P))).2 fun a ha => ?_)
    have h : (C a : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) ∈ P :=
      Ideal.Quotient.eq_zero_iff_mem.1 (show Ideal.Quotient.mk P (C a) = 0 from ha)
    have : a ∈ P.comap (C : O →+* ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) := h
    rw [hPC] at this
    exact (Submodule.mem_bot _).1 this
  have : FaithfulSMul O F :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (IsFractionRing.injective O F)
  have : FaithfulSMul F (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ genFib P) :=
    (faithfulSMul_iff_algebraMap_injective F (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ genFib P)).2 (algebraMap F _).injective
  have : Algebra.IsAlgebraic O F := IsLocalization.isAlgebraic F (nonZeroDivisors O)
  have : Algebra.IsAlgebraic (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι ⧸ P) (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ genFib P) := by
    refine ⟨fun b => ?_⟩
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective b
    obtain ⟨⟨s, m⟩, rfl⟩ := IsLocalization.mk'_surjective M g
    have hspec := IsLocalization.mk'_spec (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι) s m
    let y := algebraMap (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι ⧸ P) (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ genFib P) (Ideal.Quotient.mk P (m : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι))
    have hy0 : y ≠ 0 := by
      refine (map_ne_zero_iff _ hφ).2 fun h => ?_
      exact Set.disjoint_left.1 hdisj m.2 (Ideal.Quotient.eq_zero_iff_mem.1 h)
    refine IsAlgebraic.of_mul (mem_nonZeroDivisors_of_ne_zero hy0) (isAlgebraic_algebraMap _) ?_
    have : y * Ideal.Quotient.mk (genFib P) (IsLocalization.mk' (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι) s m) =
        algebraMap (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι ⧸ P) (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ genFib P) (Ideal.Quotient.mk P s) := by
      change φ _ * _ = φ _
      simp only [φ, Ideal.quotientMap_mk, ← map_mul]
      rw [mul_comm, hspec]
    rw [this]
    exact isAlgebraic_algebraMap _
  have h1 := trdeg_add_eq O F (A := ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ genFib P)
  have h2 := trdeg_add_eq O (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι ⧸ P) (A := ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ genFib P)
  rw [trdeg_eq_zero (R := O) (A := F), zero_add] at h1
  rw [trdeg_eq_zero (R := ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι ⧸ P) (A := ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ genFib P), add_zero] at h2
  rw [hB, h1, ← h2] at hle
  exact hle

end PrimeDimLeTrdeg

end

end GroundTheory.Heights₂.Heights.NumbersDVR
