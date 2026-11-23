module

public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.ComapMaximalIdealParDVR
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PChartTorsion
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PChowFormHomog
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Statements
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
import Mathlib.RingTheory.Nullstellensatz
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
import Mathlib.Topology.Sheaves.Init
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PLengthDecomp
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PNormFormEval
import Mathlib.RingTheory.Localization.NormTrace
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PNormLength
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.IntToFracInjective
import Mathlib.Tactic.TypeStar
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.IntToFracInjective
import Mathlib.RingTheory.RegularLocalRing.Defs
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.ComapMaximalIdealParDVR
import Mathlib.Algebra.AffineMonoid.Basic
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PPrimitiveScale
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PSecBFinite
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PSecBGeneric

-- Source module: GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PIncidenceNull

section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

theorem IncidenceNull.proof : IncidenceNull.Statement := by
  intro F _ n k I f hf
  have hvan : ∀ j : Fin n, rename Sum.inr f * X (Sum.inl j) ∈
      MvPolynomial.vanishingIdeal F
        (MvPolynomial.zeroLocus (AlgebraicClosure F) (incIdeal I k)) := by
    intro j z hz
    have hI : ∀ g ∈ I, aeval (z ∘ Sum.inl) g = 0 := by
      intro g hg
      have hmem : rename Sum.inl g ∈ incIdeal I k :=
        Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hg)
      have h := hz _ hmem
      rwa [aeval_rename] at h
    have hlin : ∀ i : Fin k, ∑ j, (z ∘ Sum.inr) (i, j) * (z ∘ Sum.inl) j = 0 := by
      intro i
      have hmem : (∑ j, X (Sum.inr (i, j)) * X (Sum.inl j) :
          MvPolynomial (Fin n ⊕ (Fin k × Fin n)) F) ∈ incIdeal I k :=
        Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩)
      have h := hz _ hmem
      simpa using h
    rw [map_mul, aeval_rename, aeval_X]
    by_cases hx : z ∘ Sum.inl = 0
    · have h0 : z (Sum.inl j) = 0 := congrFun hx j
      rw [h0, mul_zero]
    · have hu : z ∘ Sum.inr ∈ incidence I k := ⟨z ∘ Sum.inl, hx, hI, hlin⟩
      rw [(hf.2 f).2 dvd_rfl _ hu, zero_mul]
  have hrad : ∀ j : Fin n, ∃ m, (rename Sum.inr f * X (Sum.inl j)) ^ m ∈ incIdeal I k := by
    intro j
    have h := hvan j
    rw [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical] at h
    exact h
  choose m hm using hrad
  exact ⟨Finset.univ.sup m, fun j =>
    Ideal.pow_mem_of_pow_mem _ (hm j) (Finset.le_sup (Finset.mem_univ j))⟩

end GroundTheory.Heights₂.Heights.Vertical
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PNormFormLocalization

section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

noncomputable section

theorem NormFormLocalization.proof : NormFormLocalization.Statement := by
  intro R F A A' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ n x
  classical
  let b := Module.Free.chooseBasis R A
  let b' := b.localizationLocalization F (nonZeroDivisors R) A'
  have hM : ∀ j, Algebra.leftMulMatrix b' (algebraMap A A' (x j)) =
      (algebraMap R F).mapMatrix (Algebra.leftMulMatrix b (x j)) := fun j =>
    (Algebra.map_leftMulMatrix_localization R (nonZeroDivisors R) b (x j)).symm
  rw [normForm_eq_det b, normForm_eq_det b', RingHom.map_det]
  congr 1
  ext i k

  simp only [hM, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply,
  smul_eq_mul, map_sum, map_mul, map_X, map_C]

end

end GroundTheory.Heights₂.Heights.Vertical
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PParAlgIndep

section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem eval_parYF_comp (K : Type*) [Field K] [NumberField K] (e n : ℕ) :
    (eval₂Hom (kToFrac K e n) (parYF K e n)).comp
        (algebraMap (MvPolynomial (Par e n) (𝓞 K)) (MvPolynomial (Par e n) K)) =
      algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParFrac K e n) := by
  refine MvPolynomial.ringHom_ext (fun x => ?_) (fun p => ?_)
  · simp only [RingHom.coe_comp, Function.comp_apply, MvPolynomial.algebraMap_def, map_C,
      eval₂Hom_C]
    rw [kToFrac, IsFractionRing.lift_algebraMap, RingHom.comp_apply]
  · simp [parYF]

theorem ParAlgIndep.proof : ParAlgIndep.Statement := by
  intro K _ _ e n
  let _ := (kToFrac K e n).toAlgebra
  rw [algebraicIndependent_iff_injective_aeval]
  change Function.Injective (eval₂Hom (kToFrac K e n) (parYF K e n))
  let M : Submonoid (MvPolynomial (Par e n) (𝓞 K)) := (nonZeroDivisors (𝓞 K)).map C
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective M z
  have h := IsLocalization.mk'_spec (MvPolynomial (Par e n) K) a s
  have hc := eval_parYF_comp K e n
  have ha : algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParFrac K e n) a = 0 := by
    rw [← hc, RingHom.comp_apply, ← h, map_mul, hz, zero_mul]
  have ha0 : a = 0 := IsFractionRing.injective _ _ (ha.trans (map_zero _).symm)
  subst ha0
  exact IsLocalization.mk'_zero _

end

end GroundTheory.Heights₂.Heights.Vertical
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PParDVRIsDVR

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain IsLocalRing

noncomputable section

theorem ParDVRIsDVR.proof : ParDVRIsDVR.Statement := by
  intro K _ _ e n v
  let A := MvPolynomial (Par e n) (𝓞 K)
  let R := ParDVR e n v
  let Rv := Localization.AtPrime v.asIdeal
  have : IsDiscreteValuationRing Rv :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K) v.ne_bot Rv
  have : IsNoetherianRing R :=
    IsLocalization.isNoetherianRing (parPrime e n v).primeCompl R inferInstance

  have hC : ∀ s : 𝓞 K, s ∉ v.asIdeal → (C s : A) ∉ parPrime e n v := by
    intro s hs h
    rw [parPrime, MvPolynomial.mem_map_C_iff] at h
    exact hs (by simpa using h 0)
  have hOR : algebraMap (𝓞 K) R = (algebraMap A R).comp C := by
    rw [IsScalarTower.algebraMap_eq (𝓞 K) A R, MvPolynomial.algebraMap_eq]
  let φ : Rv →+* R := IsLocalization.lift (M := v.asIdeal.primeCompl) (g := algebraMap (𝓞 K) R)
    fun s => by
      rw [hOR, RingHom.comp_apply]
      exact IsLocalization.map_units R (⟨C (s : 𝓞 K), hC s s.2⟩ : (parPrime e n v).primeCompl)
  have hφ : φ.comp (algebraMap (𝓞 K) Rv) = algebraMap (𝓞 K) R := IsLocalization.lift_comp _
  have hmax : maximalIdeal R = (maximalIdeal Rv).map φ := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (parPrime e n v) R,
      ← IsLocalization.AtPrime.map_eq_maximalIdeal v.asIdeal Rv, Ideal.map_map, hφ, hOR, ← Ideal.map_map]
    rfl
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible Rv
  have hspan : maximalIdeal R = Ideal.span {φ ϖ} := by
    rw [hmax, (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.map_span,
      Set.image_singleton]

  have hne : maximalIdeal R ≠ ⊥ := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
    intro hbot
    have hmem : algebraMap (𝓞 K) R x ∈ maximalIdeal R := by
      rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (parPrime e n v) R, hOR, RingHom.comp_apply]
      exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem C hx)
    rw [hbot, Ideal.mem_bot, hOR, RingHom.comp_apply] at hmem
    have hinj : Function.Injective (algebraMap A R) :=
      IsLocalization.injective R (Ideal.primeCompl_le_nonZeroDivisors (parPrime e n v))
    exact hx0 (MvPolynomial.C_injective _ _ (hinj (by rw [hmem, map_zero, map_zero])))
  have hnf : ¬IsField R := fun h => hne (isField_iff_maximalIdeal_eq.mp h)
  exact ((IsDiscreteValuationRing.TFAE R hnf).out 5 1).mp
    (show (maximalIdeal R).IsPrincipal from ⟨⟨φ ϖ, hspan⟩⟩)

end

end GroundTheory.Heights₂.Heights.Vertical
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PParFracIsFractionRing

section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

theorem ParFracIsFractionRing.proof : ParFracIsFractionRing.Statement := by
  intro K _ _ e n v
  let := (parToFrac e n v).toAlgebra
  have : IsScalarTower (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v) (ParFrac K e n) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      change _ = parToFrac e n v (algebraMap _ _ x)
      unfold parToFrac
      rw [IsLocalization.lift_eq]
  exact IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (parPrime e n v).primeCompl
    (ParDVR e n v) (ParFrac K e n)

end

end GroundTheory.Heights₂.Heights.Vertical
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PVertTermEq

section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

theorem vertComps_finite {K : Type*} [Field K] [NumberField K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) (u : Fin n → 𝓞 K) (v : HeightOneSpectrum (𝓞 K)) :
    (vertComps I u v).Finite :=
  (Ideal.finite_minimalPrimes_of_isNoetherianRing _ _).subset fun _ hW => hW.1.1

theorem VertTermEq.proof : VertTermEq.Statement := by
  intro K _ _ n e I u v
  have hfin := vertComps_finite I u v
  unfold vertTermAt vertDeg
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin,
    Nat.cast_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun W _ => ?_
  push_cast
  ring

end

end GroundTheory.Heights₂.Heights.Vertical
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.AssemblyPartial

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

theorem NormLength.full : NormLength.Statement := NormLength.proof
theorem VertTermEq.full : VertTermEq.Statement := VertTermEq.proof
theorem ParAlgIndep.full : ParAlgIndep.Statement := ParAlgIndep.proof
theorem NormFormEval.full : NormFormEval.Statement := NormFormEval.proof
theorem ChartTorsion.full : ChartTorsion.Statement := ChartTorsion.proof
theorem ChowFormHomog.full : ChowFormHomog.Statement := ChowFormHomog.proof
theorem IncidenceNull.full : IncidenceNull.Statement := IncidenceNull.proof
theorem LengthDecomp.full : LengthDecomp.Statement := LengthDecomp.proof
theorem NormFormLocalization.full : NormFormLocalization.Statement := NormFormLocalization.proof
theorem ParDVRIsDVR.full : ParDVRIsDVR.Statement := ParDVRIsDVR.proof
theorem ParFracIsFractionRing.full : ParFracIsFractionRing.Statement := ParFracIsFractionRing.proof
theorem PrimitiveScale.full : PrimitiveScale.Statement := PrimitiveScale.proof
theorem SecBGeneric.full : SecBGeneric.Statement := SecBGeneric.proof
theorem SecBFinite.full : SecBFinite.Statement :=
  SecBFinite.proof IncidenceNull.full ChartTorsion.full PrimitiveScale.full

end GroundTheory.Heights₂.Heights.Vertical
end
end
