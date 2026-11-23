module

public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.ABHNPrep
public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleRestriction.ExistsInfIdelesLocalResIdelesResFieldEqZeroOfInf
public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleInvariants.Transport
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleRestriction.IsDiscreteRepResGlobalDecompLimitRep
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
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.Splitting
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleRestriction.Components
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.RealPlaces

-- Source module: GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleInvariants.LocalInf

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IntermediateField GroundTheory.Global FiniteSubfield IsDedekindDomain IdeleLimit
  GroundTheory.Global.SemiLocal

open scoped NumberField.LiesOver

noncomputable section

local notation "ℚ̄" => AlgebraicClosure ℚ

variable {K E : GroundTheory.Global.FiniteSubfield} [Fact (K ≤ E)]


theorem quadraticInv_infIdelesLocalRes_idelesResField_of_finrank_eq_one {v : InfinitePlace K.1}
    (ι : ℚ̄ →ₐ[K.1] AlgebraicClosure v.Completion)
    (ιE : ℚ̄ →ₐ[E.1] AlgebraicClosure (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion)
    (y : cohomology (limitRep K) 2)
    (h1 : Module.finrank v.Completion (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion = 1) :
    quadraticInv (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion
        (AlgebraicClosure (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion)
        (infAlgClosure_finrank_le_two _) (infAlgClosure_mul_mem_range_norm _)
        ((infIdelesLocalRes ιE 2).hom ((idelesResField K E 2).hom y)) =
      quadraticInv v.Completion (AlgebraicClosure v.Completion) (infAlgClosure_finrank_le_two v)
        (infAlgClosure_mul_mem_range_norm v) ((infIdelesLocalRes ι 2).hom y) := by
  have : (infPlaceOfEmbedding ι E : InfinitePlace E.1).LiesOver v := (infPlaceOfEmbedding ι E).2
  let c := infCompletionEmbedding ι E
  let L := c.fieldRange
  let : Algebra (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion (AlgebraicClosure v.Completion) :=
    c.toRingHom.toAlgebra
  have : IsScalarTower v.Completion (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion
      (AlgebraicClosure v.Completion) :=
    IsScalarTower.of_algebraMap_eq fun a => (c.commutes a).symm
  have : Algebra.IsAlgebraic (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion (AlgebraicClosure v.Completion) :=
    Algebra.IsAlgebraic.tower_top (K := v.Completion) _
  have : IsAlgClosure (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion (AlgebraicClosure v.Completion) :=
    ⟨inferInstance, inferInstance⟩
  let θ : AlgebraicClosure (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion ≃ₐ[(infPlaceOfEmbedding ι E :
      InfinitePlace E.1).Completion] AlgebraicClosure v.Completion := IsAlgClosure.equiv _ _ _
  let : Algebra E.1 (AlgebraicClosure v.Completion) :=
    ((algebraMap (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion (AlgebraicClosure v.Completion)).comp
      (algebraMap E.1 (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion)).toAlgebra
  have : IsScalarTower E.1 (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion (AlgebraicClosure v.Completion) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let ιE' : ℚ̄ →ₐ[E.1] AlgebraicClosure v.Completion :=
    { ι.toRingHom with commutes' := fun t => (infCompletionEmbedding_algebraMap ι E t).symm }
  let ιE0 : ℚ̄ →ₐ[E.1] AlgebraicClosure (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion :=
    (θ.symm.toAlgHom.restrictScalars E.1).comp ιE'
  have hι : ∀ t, θ.toRingEquiv (ιE0 t) = ι t := fun t => θ.apply_symm_apply (ι t)
  have hL : ∀ l ∈ L, ∃ t : (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion,
      θ.toRingEquiv (algebraMap _ (AlgebraicClosure (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion) t) = l := by
    intro l hl
    obtain ⟨t, rfl⟩ := (AlgHom.mem_fieldRange).1 hl
    exact ⟨t, θ.commutes t⟩
  have : Algebra.IsIntegral L (AlgebraicClosure v.Completion) := Algebra.IsIntegral.tower_top v.Completion
  have hproj : ∀ z : IdeleLimit, θ.toRingEquiv (infIdelesProj ιE0 z : AlgebraicClosure _) =
      (infIdelesProj ι z : AlgebraicClosure v.Completion) :=
    infIdelesProj_eq_of_algebraMap (infPlaceOfEmbedding ι E) ι ιE0 θ.toRingEquiv hι fun a => by
      change θ (algebraMap _ (AlgebraicClosure (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion)
        (algebraMap v.Completion _ a)) = _
      rw [θ.commutes]
      exact c.commutes a
  have key := cohomologyMapAlong_globalDecomp_idelesResField v.Completion
    (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion L θ.toRingEquiv hL ι ιE0 hι (infIdelesLocalMor ι)
    (infIdelesLocalMor ιE0) hproj 2 y

  let φ := (AlgEquiv.restrictScalarsHom v.Completion).comp (fieldConjHom v.Completion L θ.toRingEquiv hL)
  have hφ : Continuous φ := (continuous_restrictScalarsHom_of_tower v.Completion L (AlgebraicClosure v.Completion)).comp
    (continuous_fieldConjHom v.Completion L θ.toRingEquiv hL)
  let fφ : Rep.res φ (galUnitsZ v.Completion (AlgebraicClosure v.Completion)) ⟶
      galUnitsZ (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion
        (AlgebraicClosure (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion) := (Rep.resFunctor (fieldConjHom v.Completion L θ.toRingEquiv hL)).map
    (unitsScalarsMor v.Completion (AlgebraicClosure v.Completion) L) ≫ fieldConjUnitsMor v.Completion L θ.toRingEquiv hL
  have key' : (infIdelesLocalRes ιE0 2).hom ((idelesResField K E 2).hom y) =
      (cohomologyMapAlong φ hφ fφ 2).hom ((infIdelesLocalRes ι 2).hom y) := by
    refine key.trans ?_
    rw [unitsScalarsRes, cohomologyMapAlong_comp]
    rfl
  refine (congrArg (quadraticInv (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion
    (AlgebraicClosure (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion)
    (infAlgClosure_finrank_le_two _) (infAlgClosure_mul_mem_range_norm _))
    ((congrArg (fun f => f.hom ((idelesResField K E 2).hom y))
      (infIdelesLocalRes_eq_of_algHom ιE0 ιE 2)).trans key')).trans ?_

  have hbot := Subalgebra.bot_eq_top_of_finrank_eq_one h1
  have hfix : ∀ (σ : Gal(AlgebraicClosure v.Completion / v.Completion))
      (t : (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion),
      θ.symm (σ (θ (algebraMap _ (AlgebraicClosure (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion) t))) =
        algebraMap _ _ t := by
    intro σ t
    have ht : t ∈ (⊥ : Subalgebra v.Completion (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion) := by
      rw [hbot]
      trivial
    obtain ⟨k, rfl⟩ := Algebra.mem_bot.1 ht
    have hk : θ (algebraMap _ (AlgebraicClosure (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion)
        (algebraMap v.Completion (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion k)) =
          algebraMap v.Completion (AlgebraicClosure v.Completion) k := by
      rw [θ.commutes]
      exact c.commutes k
    rw [hk, σ.commutes, ← hk, AlgEquiv.symm_apply_apply]
  let ψ : Gal(AlgebraicClosure v.Completion / v.Completion) →*
      Gal(AlgebraicClosure (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion /
        (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion) :=
    { toFun := fun σ => AlgEquiv.ofRingEquiv (f := (θ.toRingEquiv.trans σ.toRingEquiv).trans θ.toRingEquiv.symm)
        (hfix σ)
      map_one' := AlgEquiv.ext fun x => θ.symm_apply_apply x
      map_mul' := fun σ τ => AlgEquiv.ext fun x => by
        change θ.symm (σ (τ (θ x))) = θ.symm (σ (θ (θ.symm (τ (θ x)))))
        rw [AlgEquiv.apply_symm_apply] }
  have hψ_apply : ∀ σ x, ψ σ x = θ.symm (σ (θ x)) := fun _ _ => rfl
  have hψ : Continuous ψ := by
    refine continuous_of_continuousAt_one _ ?_
    rw [ContinuousAt, map_one]
    intro s hs
    obtain ⟨M, hM, hMs⟩ := (krullTopology_mem_nhds_one_iff _ _ s).1 hs
    rw [Filter.mem_map, krullTopology_mem_nhds_one_iff]
    have : Module.Free (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion M := Module.Free.of_divisionRing _ M
    let b := Module.finBasis (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion M
    let T : Set (AlgebraicClosure v.Completion) :=
      Set.range fun i => θ (b i : AlgebraicClosure (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion)
    refine ⟨IntermediateField.adjoin v.Completion T, ?_, ?_⟩
    · refine IntermediateField.finiteDimensional_adjoin fun x _ => ?_
      exact Algebra.IsIntegral.isIntegral x
    · intro σ hσ
      apply hMs
      rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hσ ⊢
      intro x hx
      have hT : ∀ i, ψ σ (b i : AlgebraicClosure (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion) =
          b i := fun i => by
        change θ.symm (σ (θ (b i : AlgebraicClosure (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion))) = _
        exact (congrArg θ.symm (hσ _ (IntermediateField.subset_adjoin v.Completion T ⟨i, rfl⟩))).trans
          (θ.symm_apply_apply _)
      have hlin : (ψ σ).toAlgHom.toLinearMap ∘ₗ M.val.toLinearMap = M.val.toLinearMap :=
        b.ext fun i => hT i
      exact LinearMap.congr_fun hlin ⟨x, hx⟩
  let f' : Rep.res ψ (galUnitsZ (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion
      (AlgebraicClosure (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion)) ⟶
      galUnitsZ v.Completion (AlgebraicClosure v.Completion) :=
    Rep.ofHom ⟨(MonoidHom.toAdditive (Units.map θ.toRingEquiv.toRingHom.toMonoidHom)).toIntLinearMap,
      fun σ => LinearMap.ext fun x => congrArg Additive.ofMul (Units.ext (by
        change θ (θ.symm (σ (θ ((Additive.toMul x : (AlgebraicClosure _)ˣ) : AlgebraicClosure _)))) =
          σ (θ ((Additive.toMul x : (AlgebraicClosure _)ˣ) : AlgebraicClosure _))
        exact θ.apply_symm_apply _))⟩
  have hinj : Function.Injective (cohomologyMapAlong φ hφ fφ 2).hom := by
    refine cohomologyMapAlong_injective_of_leftInverse φ hφ ψ hψ (fun σ => AlgEquiv.ext fun x => ?_) fφ f'
      (fun a => ?_) 2
    · change θ (θ.symm (σ (θ (θ.symm x)))) = σ x
      rw [AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
    · apply Additive.toMul.injective
      apply Units.ext
      change θ (θ.symm ((Additive.toMul a : (AlgebraicClosure v.Completion)ˣ) : AlgebraicClosure v.Completion)) = _
      exact θ.apply_symm_apply _
  exact quadraticInv_cohomologyMapAlong_of_injective _ _ _ _ hφ fφ hinj _

end

end GroundTheory.ProfCoh
end
end

-- Source module: GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleInvariants.BrauerInvZOfIsSepClosureIdelesLocalResIdelesResF

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IntermediateField GroundTheory.Global FiniteSubfield IsDedekindDomain IdeleLimit
  GroundTheory.Global.SemiLocal GroundTheory.LocalField ValuativeRel

noncomputable section

section Valuation

variable {K F Ω : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field F] [ValuativeRel F] [Algebra K F] [ValuativeExtension K F] [Algebra.IsAlgebraic K F]
  [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]

theorem algebraicValuativeRel_vle_algHom_iff (c : F →ₐ[K] Ω) (x y : F) :
    (letI := algebraicValuativeRel K Ω; c x ≤ᵥ c y) ↔ x ≤ᵥ y := by
  let := algebraicValuativeRel K Ω
  have := algebraicValuativeRel_valuativeExtension K Ω
  rw [vle_iff_spectralNorm_le (K := K) (c x) (c y), vle_iff_spectralNorm_le (K := K) x y]
  let := normedField K
  change spectralNorm K Ω (c x) ≤ spectralNorm K Ω (c y) ↔ spectralNorm K F x ≤ spectralNorm K F y
  rw [spectralNorm, spectralNorm, spectralNorm, spectralNorm, minpoly.algHom_eq c c.injective,
    minpoly.algHom_eq c c.injective]

end Valuation

variable {K E : FiniteSubfield} [Fact (K ≤ E)]

section Finite

local notation "ℚ̄" => AlgebraicClosure ℚ


theorem brauerInvZOfIsSepClosure_idelesLocalRes_idelesResField (v : HeightOneSpectrum (𝓞 K.1))
    (ι : ℚ̄ →ₐ[K.1] AlgebraicClosure (v.adicCompletion K.1))
    (ιE : ℚ̄ →ₐ[E.1] AlgebraicClosure ((placeOfEmbedding ι E).1.adicCompletion E.1))
    (y : cohomology (limitRep K) 2) :
    brauerInvZOfIsSepClosure ((placeOfEmbedding ι E).1.adicCompletion E.1)
        (AlgebraicClosure ((placeOfEmbedding ι E).1.adicCompletion E.1))
        ((idelesLocalRes ιE 2).hom ((idelesResField K E 2).hom y)) =
      Module.finrank (v.adicCompletion K.1) ((placeOfEmbedding ι E).1.adicCompletion E.1) •
        brauerInvZOfIsSepClosure (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1))
          ((idelesLocalRes ι 2).hom y) := by
  have := finiteDimensional_adicCompletion_placesOver (E := E) (placeOfEmbedding ι E)
  let c := completionEmbedding ι E
  let L := c.fieldRange
  let : Algebra ((placeOfEmbedding ι E).1.adicCompletion E.1) (AlgebraicClosure (v.adicCompletion K.1)) :=
    c.toRingHom.toAlgebra
  have : IsScalarTower (v.adicCompletion K.1) ((placeOfEmbedding ι E).1.adicCompletion E.1)
      (AlgebraicClosure (v.adicCompletion K.1)) :=
    IsScalarTower.of_algebraMap_eq fun a => (c.commutes a).symm
  have : Algebra.IsAlgebraic ((placeOfEmbedding ι E).1.adicCompletion E.1) (AlgebraicClosure (v.adicCompletion K.1)) :=
    Algebra.IsAlgebraic.tower_top (K := v.adicCompletion K.1) _
  have : IsAlgClosure ((placeOfEmbedding ι E).1.adicCompletion E.1) (AlgebraicClosure (v.adicCompletion K.1)) :=
    ⟨inferInstance, inferInstance⟩
  let θ : AlgebraicClosure ((placeOfEmbedding ι E).1.adicCompletion E.1) ≃ₐ[(placeOfEmbedding ι E).1.adicCompletion E.1]
      AlgebraicClosure (v.adicCompletion K.1) := IsAlgClosure.equiv _ _ _
  let : Algebra E.1 (AlgebraicClosure (v.adicCompletion K.1)) :=
    ((algebraMap ((placeOfEmbedding ι E).1.adicCompletion E.1) (AlgebraicClosure (v.adicCompletion K.1))).comp
      (algebraMap E.1 ((placeOfEmbedding ι E).1.adicCompletion E.1))).toAlgebra
  have : IsScalarTower E.1 ((placeOfEmbedding ι E).1.adicCompletion E.1) (AlgebraicClosure (v.adicCompletion K.1)) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let ιE' : ℚ̄ →ₐ[E.1] AlgebraicClosure (v.adicCompletion K.1) :=
    { ι.toRingHom with commutes' := fun t => (completionEmbedding_algebraMap ι E t).symm }
  let ιE0 : ℚ̄ →ₐ[E.1] AlgebraicClosure ((placeOfEmbedding ι E).1.adicCompletion E.1) :=
    (θ.symm.toAlgHom.restrictScalars E.1).comp ιE'
  have hι : ∀ t, θ.toRingEquiv (ιE0 t) = ι t := fun t => θ.apply_symm_apply (ι t)
  have hL : ∀ l ∈ L, ∃ t : (placeOfEmbedding ι E).1.adicCompletion E.1,
      θ.toRingEquiv (algebraMap _ (AlgebraicClosure ((placeOfEmbedding ι E).1.adicCompletion E.1)) t) = l := by
    intro l hl
    obtain ⟨t, rfl⟩ := (AlgHom.mem_fieldRange).1 hl
    exact ⟨t, θ.commutes t⟩
  have : FiniteDimensional (v.adicCompletion K.1) L := LinearEquiv.finiteDimensional c.equivFieldRange.toLinearEquiv
  have : Algebra.IsIntegral L (AlgebraicClosure (v.adicCompletion K.1)) :=
    Algebra.IsIntegral.tower_top (v.adicCompletion K.1)
  have hfin : Module.finrank (v.adicCompletion K.1) L =
      Module.finrank (v.adicCompletion K.1) ((placeOfEmbedding ι E).1.adicCompletion E.1) :=
    c.equivFieldRange.toLinearEquiv.finrank_eq.symm
  have hproj : ∀ z : IdeleLimit, θ.toRingEquiv (idelesProj ιE0 z : AlgebraicClosure _) =
      (idelesProj ι z : AlgebraicClosure (v.adicCompletion K.1)) :=
    idelesProj_eq_of_algebraMap (placeOfEmbedding ι E) ι ιE0 θ.toRingEquiv hι fun a => by
      change θ (algebraMap _ (AlgebraicClosure ((placeOfEmbedding ι E).1.adicCompletion E.1))
        (algebraMap (v.adicCompletion K.1) _ a)) = _
      rw [θ.commutes]
      exact c.commutes a
  have key := cohomologyMapAlong_globalDecomp_idelesResField (v.adicCompletion K.1)
    ((placeOfEmbedding ι E).1.adicCompletion E.1) L θ.toRingEquiv hL ι ιE0 hι (idelesLocalMor ι) (idelesLocalMor ιE0)
    hproj 2 y
  have key' : (idelesLocalRes ιE0 2).hom ((idelesResField K E 2).hom y) =
      (cohomologyMapAlong (fieldConjHom (v.adicCompletion K.1) L θ.toRingEquiv hL)
        (continuous_fieldConjHom (v.adicCompletion K.1) L θ.toRingEquiv hL)
        (fieldConjUnitsMor (v.adicCompletion K.1) L θ.toRingEquiv hL) 2).hom
        ((unitsScalarsRes (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1)) L 2).hom
          ((idelesLocalRes ι 2).hom y)) := key
  rw [idelesLocalRes_eq_of_algHom ιE0 ιE, key']
  let := algebraicValuativeRel (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1))
  let := algebraicTopology (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1))
  have := algebraicTopology_isValuativeTopology (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1))
  have := algebraicValuativeRel_valuativeExtension (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1))
  let e : (placeOfEmbedding ι E).1.adicCompletion E.1 ≃+* L := c.equivFieldRange.toRingEquiv
  have hε : ∀ x, θ.toRingEquiv (algebraMap ((placeOfEmbedding ι E).1.adicCompletion E.1)
      (AlgebraicClosure ((placeOfEmbedding ι E).1.adicCompletion E.1)) x) =
      algebraMap L (AlgebraicClosure (v.adicCompletion K.1)) (e x) := fun x => θ.commutes x
  have he : ∀ x y : (placeOfEmbedding ι E).1.adicCompletion E.1, e x ≤ᵥ e y ↔ x ≤ᵥ y := fun x y => by
    rw [← IntermediateField.coe_vle_coe_iff]
    exact algebraicValuativeRel_vle_algHom_iff c x y
  have hρ : ∀ (σ : Gal(AlgebraicClosure ((placeOfEmbedding ι E).1.adicCompletion E.1) /
      (placeOfEmbedding ι E).1.adicCompletion E.1)) (x : AlgebraicClosure ((placeOfEmbedding ι E).1.adicCompletion E.1)),
      fieldConjHom (v.adicCompletion K.1) L θ.toRingEquiv hL σ (θ.toRingEquiv x) = θ.toRingEquiv (σ x) :=
    fun σ x => by rw [fieldConjHom_apply, RingEquiv.symm_apply_apply]
  rw [brauerInvZOfIsSepClosure_cohomologyMapAlong_transport e θ.toRingEquiv hε _
    (continuous_fieldConjHom (v.adicCompletion K.1) L θ.toRingEquiv hL) hρ _ (fun _ => rfl) he,
    brauerInvZOfIsSepClosure_unitsScalarsRes, hfin]

end Finite

end

end GroundTheory.ProfCoh
end
end

-- Source module: GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleInvariants

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IntermediateField GroundTheory.Global FiniteSubfield IsDedekindDomain IdeleLimit
  GroundTheory.Global.SemiLocal

open scoped NumberField.LiesOver DirectSum

noncomputable section

variable {K E : FiniteSubfield} [Fact (K ≤ E)] (ι : LocalEmbeddings K) (ιE : LocalEmbeddings E)

section Places



theorem placeInv_idelesResField_inr (y : cohomology (limitRep K) 2) (v : HeightOneSpectrum (𝓞 K.1))
    (w : PlacesOver E.1 v) :
    placeInv (.inr w.1) (idelesLimitCohomologyEquiv ιE (by norm_num : 1 ≤ 2) ((idelesResField K E 2).hom y) (.inr w.1)) =
      Module.finrank (v.adicCompletion K.1) (w.1.adicCompletion E.1) •
        placeInv (.inr v) (idelesLimitCohomologyEquiv ι (by norm_num : 1 ≤ 2) y (.inr v)) := by
  rw [idelesLimitCohomologyEquiv_apply_inr, idelesLimitCohomologyEquiv_apply_inr]
  obtain ⟨ι', hι'⟩ := exists_placeOfEmbedding_eq w
  have key : ∀ u : PlacesOver E.1 v, placeOfEmbedding ι' E = u →
      placeInv (K := E) (.inr u.1) ((idelesLocalRes (ιE.fin u.1) 2).hom ((idelesResField K E 2).hom y)) =
        Module.finrank (v.adicCompletion K.1) (u.1.adicCompletion E.1) •
          placeInv (K := K) (.inr v) ((idelesLocalRes (ι.fin v) 2).hom y) := by
    rintro u rfl
    rw [idelesLocalRes_eq_of_algHom ι' (ι.fin v)]
    exact brauerInvZOfIsSepClosure_idelesLocalRes_idelesResField v ι' (ιE.fin _) y
  exact key w hι'



theorem placeInv_idelesResField_inl (y : cohomology (limitRep K) 2) (v : InfinitePlace K.1) (w : v.placesOver E.1) :
    placeInv (.inl (w : InfinitePlace E.1))
        (idelesLimitCohomologyEquiv ιE (by norm_num : 1 ≤ 2) ((idelesResField K E 2).hom y) (.inl w)) =
      Module.finrank v.Completion (w : InfinitePlace E.1).Completion •
        placeInv (.inl v) (idelesLimitCohomologyEquiv ι (by norm_num : 1 ≤ 2) y (.inl v)) := by
  rw [idelesLimitCohomologyEquiv_apply_inl, idelesLimitCohomologyEquiv_apply_inl]
  by_cases hw : (w : InfinitePlace E.1).IsComplex
  · have h0 : placeInv (K := E) (.inl (w : InfinitePlace E.1))
        ((infIdelesLocalRes (ιE.inf (w : InfinitePlace E.1)) 2).hom ((idelesResField K E 2).hom y)) = 0 := by
      have : Subsingleton (cohomology (galUnitsZ (w : InfinitePlace E.1).Completion
          (AlgebraicClosure (w : InfinitePlace E.1).Completion)) 2) :=
        subsingleton_cohomology_two_of_isComplex _ hw
      exact (congrArg _ (Subsingleton.elim _ 0)).trans (map_zero _)
    rw [h0]
    by_cases hv : v.IsReal
    · rw [(InfinitePlace.finrank_completion_eq_two_iff (w : InfinitePlace E.1)).2 ⟨hv, hw⟩]
      rcases placeInv_inl_eq_zero_or_eq_half v ((infIdelesLocalRes (ι.inf v) 2).hom y) with h | h
      · rw [h, smul_zero]
      · rw [h, two_nsmul, QZ.mk_half_add_mk_half]
    · have h0 : placeInv (K := K) (.inl v) ((infIdelesLocalRes (ι.inf v) 2).hom y) = 0 := by
        have : Subsingleton (cohomology (galUnitsZ v.Completion (AlgebraicClosure v.Completion)) 2) :=
          subsingleton_cohomology_two_of_isComplex v (InfinitePlace.not_isReal_iff_isComplex.1 hv)
        exact (congrArg _ (Subsingleton.elim _ 0)).trans (map_zero _)
      rw [h0, smul_zero]
  · have h1 : Module.finrank v.Completion (w : InfinitePlace E.1).Completion = 1 :=
      (InfinitePlace.finrank_completion_eq_one_iff (w : InfinitePlace E.1)).2 fun h => hw h.2
    rw [h1, one_smul]
    obtain ⟨ι', hι'⟩ := exists_infPlaceOfEmbedding_eq w
    have key : ∀ u : v.placesOver E.1, infPlaceOfEmbedding ι' E = u →
        Module.finrank v.Completion (u : InfinitePlace E.1).Completion = 1 →
        placeInv (K := E) (.inl (u : InfinitePlace E.1))
            ((infIdelesLocalRes (ιE.inf (u : InfinitePlace E.1)) 2).hom ((idelesResField K E 2).hom y)) =
          placeInv (K := K) (.inl v) ((infIdelesLocalRes (ι.inf v) 2).hom y) := by
      rintro u rfl hu
      rw [infIdelesLocalRes_eq_of_algHom ι' (ι.inf v)]
      exact quadraticInv_infIdelesLocalRes_idelesResField_of_finrank_eq_one ι' (ιE.inf _) y hu
    exact key w hι' h1

end Places

section Sum

theorem sumPlaceInv_eq_sum (D : ⨁ w : Place E.1, localGaloisCohomology E 2 w) (S : Finset (Place E.1))
    (hS : ∀ w ∉ S, D w = 0) : sumPlaceInv E D = ∑ w ∈ S, placeInv w (D w) := by
  classical
  have hD : D = ∑ w ∈ S, DirectSum.of _ w (D w) := by
    refine DFinsupp.ext fun w => ?_
    rw [DFinsupp.finsetSum_apply]
    by_cases hw : w ∈ S
    · rw [Finset.sum_eq_single w (fun b _ hb => DirectSum.of_eq_of_ne _ _ _ (Ne.symm hb))
        (fun h => absurd hw h), DirectSum.of_eq_same]
    · rw [hS w hw, Finset.sum_eq_zero fun b hb => DirectSum.of_eq_of_ne _ _ _ (by rintro rfl; exact hw hb)]
  conv_lhs => rw [hD]

  rw [map_sum]
  exact Finset.sum_congr rfl fun w _ => sumPlaceInv_of w (D w)



open Classical in
theorem idelesSumInv_idelesResField_of (u : Place K.1) (t : localGaloisCohomology K 2 u) :
    idelesSumInv ιE ((idelesResField K E 2).hom
        ((idelesLimitCohomologyEquiv ι (by norm_num : 1 ≤ 2)).symm (DirectSum.of _ u t))) =
      Module.finrank K.1 E.1 •
        idelesSumInv ι ((idelesLimitCohomologyEquiv ι (by norm_num : 1 ≤ 2)).symm (DirectSum.of _ u t)) := by
  set_option synthInstance.maxHeartbeats 200000 in
    classical
    set y := (idelesLimitCohomologyEquiv ι (by norm_num : 1 ≤ 2)).symm (DirectSum.of _ u t) with hy_def
    have hy : idelesLimitCohomologyEquiv ι (by norm_num : 1 ≤ 2) y = DirectSum.of _ u t :=
      AddEquiv.apply_symm_apply _ _
    set D := idelesLimitCohomologyEquiv ιE (by norm_num : 1 ≤ 2) ((idelesResField K E 2).hom y) with hD_def
    rw [idelesSumInv_apply, idelesSumInv_apply, hy, sumPlaceInv_of]
  
    have hinl : ∀ w : InfinitePlace E.1, placeInv (.inl w) (D (.inl w)) =
        Module.finrank (w.comap (algebraMap K.1 E.1)).Completion w.Completion •
          placeInv (.inl (w.comap (algebraMap K.1 E.1)))
            (DirectSum.of (localGaloisCohomology K 2) u t (.inl (w.comap (algebraMap K.1 E.1)))) := fun w => by
      rw [← hy]
      exact placeInv_idelesResField_inl ι ιE y (w.comap (algebraMap K.1 E.1)) ⟨w, ⟨rfl⟩⟩
    have hinr : ∀ w : HeightOneSpectrum (𝓞 E.1), placeInv (.inr w) (D (.inr w)) =
        Module.finrank ((AdeleBaseChange.below K.1 w).adicCompletion K.1) (w.adicCompletion E.1) •
          placeInv (.inr (AdeleBaseChange.below K.1 w))
            (DirectSum.of (localGaloisCohomology K 2) u t (.inr (AdeleBaseChange.below K.1 w))) := fun w => by
      rw [← hy]
      exact placeInv_idelesResField_inr ι ιE y (AdeleBaseChange.below K.1 w) ⟨w, AdeleBaseChange.liesOver_below w⟩
    rcases u with v | v
    ·
      let S : Finset (Place E.1) := Finset.univ.map ⟨fun w : v.placesOver E.1 => (.inl (w : InfinitePlace E.1) :
        Place E.1), fun a b h => Subtype.ext (Sum.inl_injective h)⟩
      have hS : ∀ w ∉ S, D w = 0 := by
        intro w hw
        apply placeInv_injective w
        rw [map_zero]
        rcases w with w | w
        · rw [hinl]
          by_cases hv : w.comap (algebraMap K.1 E.1) = v
          · exact absurd (Finset.mem_map.2 ⟨(⟨w, by subst hv; exact ⟨rfl⟩⟩ : v.placesOver E.1), Finset.mem_univ _, rfl⟩) hw
          · rw [DirectSum.of_eq_of_ne _ _ _ (fun h => hv (Sum.inl_injective h)), map_zero, smul_zero]
        · rw [hinr, DirectSum.of_eq_of_ne _ _ _ Sum.inr_ne_inl, map_zero, smul_zero]
      rw [sumPlaceInv_eq_sum D S hS, Finset.sum_map]
      change ∑ w : v.placesOver E.1, placeInv (.inl (w : InfinitePlace E.1)) (D (.inl (w : InfinitePlace E.1))) = _
      have hw : ∀ w : v.placesOver E.1, placeInv (.inl (w : InfinitePlace E.1)) (D (.inl (w : InfinitePlace E.1))) =
          Module.finrank v.Completion (w : InfinitePlace E.1).Completion • placeInv (.inl v) t := fun w => by
        rw [hD_def, placeInv_idelesResField_inl ι ιE y v w, hy, DirectSum.of_eq_same]
      rw [Finset.sum_congr rfl fun w _ => hw w, ← Finset.sum_smul,
        GroundTheory.Global.InfinitePlace.sum_finrank_completion (L := E.1) v]
    ·
      let S : Finset (Place E.1) := Finset.univ.map ⟨fun w : PlacesOver E.1 v => (.inr w.1 : Place E.1),
        fun a b h => Subtype.ext (Sum.inr_injective h)⟩
      have hS : ∀ w ∉ S, D w = 0 := by
        intro w hw
        apply placeInv_injective w
        rw [map_zero]
        rcases w with w | w
        · rw [hinl, DirectSum.of_eq_of_ne _ _ _ Sum.inl_ne_inr, map_zero, smul_zero]
        · rw [hinr]
          by_cases hv : AdeleBaseChange.below K.1 w = v
          · refine absurd (Finset.mem_map.2 ⟨(⟨w, ?_⟩ : PlacesOver E.1 v), Finset.mem_univ _, rfl⟩) hw
            rw [← hv]
            exact AdeleBaseChange.liesOver_below w
          · rw [DirectSum.of_eq_of_ne _ _ _ (fun h => hv (Sum.inr_injective h)), map_zero, smul_zero]
      rw [sumPlaceInv_eq_sum D S hS, Finset.sum_map]
      change ∑ w : PlacesOver E.1 v, placeInv (.inr w.1) (D (.inr w.1)) = _
      have hw : ∀ w : PlacesOver E.1 v, placeInv (.inr w.1) (D (.inr w.1)) =
          Module.finrank (v.adicCompletion K.1) (w.1.adicCompletion E.1) • placeInv (.inr v) t := fun w => by
        rw [hD_def, placeInv_idelesResField_inr ι ιE y v w, hy, DirectSum.of_eq_same]
      rw [Finset.sum_congr rfl fun w _ => hw w, ← Finset.sum_smul, sum_finrank_eq E.1 v]

theorem idelesSumInv_idelesResField (y : cohomology (limitRep K) 2) :
    idelesSumInv ιE ((idelesResField K E 2).hom y) = Module.finrank K.1 E.1 • idelesSumInv ι y := by
  classical
  set Φ := idelesLimitCohomologyEquiv ι (by norm_num : 1 ≤ 2)
  obtain ⟨D, rfl⟩ := Φ.symm.surjective y

  rw [← DirectSum.sum_support_of D, map_sum, map_sum, map_sum, map_sum, Finset.smul_sum]
  exact Finset.sum_congr rfl fun u _ => idelesSumInv_idelesResField_of ι ιE u (D u)

end Sum

end

end GroundTheory.ProfCoh
end
end
