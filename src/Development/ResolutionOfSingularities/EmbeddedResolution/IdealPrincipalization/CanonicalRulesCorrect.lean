module

public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionHypotheses
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.GeometryHypotheses
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.CanonicalDivisorReduction
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.ControlledTransformOrderBound
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.CoordinateSubspaceIdeal
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialPrincipalization
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StalkKrullDimension
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FiniteKrullDim
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialGeometryHypotheses
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.CoordinateDimensionBound
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
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
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.ChartRing
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.OrderOffExceptionalDivisor
import Mathlib.SetTheory.ZFC.PSet
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.ComponentUnionIdeal
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.ComponentsInSupport
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.TotalTransform
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.StrictTransformComponents
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.TransformedBoundaryComponents
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.MaxOrderReduction
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.OrderReductionCompatibility

-- Source module: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.IntersectionComponentCodimension

section

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution

namespace MonomialCodimension

theorem lt_krullDimSucc_of_le_ringKrullDim_stalk (X : Scheme.{u}) (x : ↥X) (n : ℕ)
    (hn : (n : WithBot ℕ∞) ≤ ringKrullDim (X.presheaf.stalk x))
    (hfin : topologicalKrullDim ↥X ≠ ⊤) : n < krullDimSucc X := by
  have hn' : ((n : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim (X.presheaf.stalk x) := hn
  have hle : ((n : ℕ∞) : WithBot ℕ∞) ≤ topologicalKrullDim ↥X :=
    le_trans hn' (ringKrullDim_stalk_le_topologicalKrullDim X x)
  rw [krullDimSucc_eq_withBotSuccToNat_topologicalKrullDim]
  by_cases hb : topologicalKrullDim ↥X = ⊥
  · rw [hb] at hle
    exact absurd (le_bot_iff.mp hle) WithBot.coe_ne_bot
  · obtain ⟨e, he⟩ := WithBot.ne_bot_iff_exists.mp hb
    rw [← he] at hle hfin ⊢
    have he' : e ≠ ⊤ := by
      intro hcon
      apply hfin
      rw [hcon]
      simp
    lift e to ℕ using he' with m
    rw [withBotSuccToNat_coe]
    have hmm : ((m : ℕ∞)).toNat = m := by simp
    rw [hmm]
    have hnm : n ≤ m := by exact_mod_cast hle
    omega

theorem card_lt_krullDimSucc_of_mem_intersectionComponents : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (J : Finset (Fin T.boundary.length)) (C : Set ↥T.scheme),
      C ∈ intersectionComponents T.boundary J → J.card < krullDimSucc T.scheme := by
  classical
  intro T hT J C hC
  have hC' : IsIrreducible C ∧ C ⊆ (↑(intersectionIdeal T.boundary J).support : Set ↥T.scheme) ∧
      ∀ C' : Set ↥T.scheme, IsIrreducible C' → C ⊆ C' →
        C' ⊆ (↑(intersectionIdeal T.boundary J).support : Set ↥T.scheme) → C' = C :=
    (mem_intersectionComponents_iff T.boundary J C).mp hC
  obtain ⟨hirr, hsub, -⟩ := hC'
  obtain ⟨x, hxC⟩ := hirr.nonempty
  have hxsupp : x ∈ (intersectionIdeal T.boundary J).support := hsub hxC
  have hxj : ∀ j ∈ J, x ∈ (T.boundary.get j).support := by
    intro j hj
    rw [mem_support_iff_stalkIdeal_ne_top]
    intro htop
    rw [mem_support_iff_stalkIdeal_ne_top] at hxsupp
    have hle : T.boundary.get j ≤ intersectionIdeal T.boundary J := by
      rw [intersectionIdeal_eq_iSup]
      exact le_iSup₂ (f := fun (i : Fin T.boundary.length) (_ : i ∈ J) => T.boundary.get i) j hj
    have h1 := stalkIdeal_mono hle x
    rw [htop] at h1
    exact hxsupp (top_le_iff.mp h1)
  obtain ⟨-, hsnc⟩ := (inStrictNormalCrossingPosition_iff T.structMap T.boundary).mp hT.snc
  obtain ⟨U, hxU, m, c, a, hinj, hnone, hsome⟩ := (hsnc x).exists_etaleChart
  obtain ⟨V, hVB, hxV, hVU⟩ :=
    Opens.isBasis_iff_nbhd.mp T.scheme.isBasis_affineOpens hxU
  have hV : IsAffineOpen V := hVB
  have hex : ∀ j : Fin T.boundary.length, j ∈ J → ∃ t : Fin m, a (j : ℕ) = some t := by
    intro j hj
    have hne : a (j : ℕ) ≠ none := by
      intro hj'
      have htop := hnone (j : ℕ) j.isLt hj'
      have hx' := hxj j hj
      rw [List.get_eq_getElem] at hx'
      exact Scheme.IdealSheafData.notMem_support_of_comap_ι_eq_top _ htop hxU hx'
    exact Option.ne_none_iff_exists'.mp hne
  choose F hFspec using hex
  have hGinj : Function.Injective
      (fun p : {j : Fin T.boundary.length // j ∈ J} => F p.1 p.2) := by
    intro p q h
    have h1 : a (q.1 : ℕ) = some (F p.1 p.2) := by
      rw [hFspec q.1 q.2]
      exact congrArg Option.some h.symm
    have h2 := hinj (p.1 : ℕ) p.1.isLt (q.1 : ℕ) q.1.isLt (F p.1 p.2) (hFspec p.1 p.2) h1
    exact Subtype.ext (Fin.val_injective h2)
  have hcard : (J.attach.image
      (fun p : {j : Fin T.boundary.length // j ∈ J} => F p.1 p.2)).card = J.card := by
    rw [Finset.card_image_of_injective _ hGinj, Finset.card_attach]
  let d : EtaleChart T.structMap V m := {
    map := T.scheme.homOfLE hVU ≫ c.map
    comp_struct := by rw [Category.assoc, c.comp_struct, ← Category.assoc, Scheme.homOfLE_ι]
    isEtale := by
      have := c.isEtale
      infer_instance }
  have hmem : ∀ t ∈ J.attach.image
      (fun p : {j : Fin T.boundary.length // j ∈ J} => F p.1 p.2),
      d.coord t ∈ (hV.primeIdealOf ⟨x, hxV⟩).asIdeal := by
    intro t ht
    obtain ⟨p, -, hpt⟩ := Finset.mem_image.mp ht
    have hat : a (p.1 : ℕ) = some t := by
      rw [hFspec p.1 p.2]
      exact congrArg Option.some hpt
    have hU' := hsome (p.1 : ℕ) p.1.isLt t hat
    have hV' : restrictIdeal T.boundary[p.1.val] V = d.coordIdeal {t} := by
      have h' : T.boundary[p.1.val].comap U.ι =
          (coordSubspaceIdeal _ m {t}).comap c.map := by
        rw [← restrictIdeal_eq_comap_ι, hU', EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal]
      rw [restrictIdeal_eq_comap_ι, EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal]
      change _ = (coordSubspaceIdeal _ m {t}).comap (T.scheme.homOfLE hVU ≫ c.map)
      rw [Scheme.IdealSheafData.comap_comp, ← h', ← Scheme.IdealSheafData.comap_comp,
        Scheme.homOfLE_ι]
    have hx' := hxj p.1 p.2
    rw [List.get_eq_getElem] at hx'
    exact coord_mem_primeIdealOf_of_restrictIdeal_eq_coordIdeal_singleton hV
      d t _ hV' x hxV hx'
  have hle2 := card_le_ringKrullDim_stalk hV d x hxV
    (J.attach.image (fun p : {j : Fin T.boundary.length // j ∈ J} => F p.1 p.2)) hmem
  have hfin : topologicalKrullDim ↥T.scheme ≠ ⊤ := ne_of_lt hT.topologicalKrullDim_lt_top
  have hlt := lt_krullDimSucc_of_le_ringKrullDim_stalk T.scheme x _ hle2 hfin
  rwa [hcard] at hlt

theorem card_lt_krullDimSucc_of_nonempty (T : MarkedIdealWithBoundary.{u}) (hT : T.IsAdmissible)
    (J : Finset (Fin T.boundary.length)) (hJ : (intersectionComponents T.boundary J).Nonempty) :
    J.card < krullDimSucc T.scheme := by
  obtain ⟨C, hC⟩ := hJ
  exact card_lt_krullDimSucc_of_mem_intersectionComponents T hT J C hC

end MonomialCodimension

end FunctorialResolution.EmbeddedResolution
end
end

-- Source module: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.MonomialCenterHypotheses

section

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

namespace MonomialCenterCase

structure MonomialCenterHypotheses : Prop where
  center_smooth :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (J : Finset (Fin T.boundary.length)),
        ∀ 𝒞 ⊆ intersectionComponents T.boundary J,
          ∀ (hop : IsOpen (⇑(intersectionIdeal T.boundary J).subschemeι ⁻¹' ⋃₀ 𝒞)),
            AlgebraicGeometry.Smooth
              ((componentUnionIdeal T.boundary J 𝒞 hop).subschemeι ≫ T.structMap)
  center_snc :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (J : Finset (Fin T.boundary.length)),
        ∀ 𝒞 ⊆ intersectionComponents T.boundary J,
          ∀ (hop : IsOpen (⇑(intersectionIdeal T.boundary J).subschemeι ⁻¹' ⋃₀ 𝒞)),
            HasStrictNormalCrossingsWith T.structMap (componentUnionIdeal T.boundary J 𝒞 hop) T.boundary
  blowup_total_transform :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (Z : T.scheme.IdealSheafData),
        AlgebraicGeometry.Smooth (Z.subschemeι ≫ T.structMap) →
          HasStrictNormalCrossingsWith T.structMap Z T.boundary →
            ∀ (X' : Scheme.{u}) (π : X' ⟶ T.scheme), Blowup.IsBlowupAlongIdealSheaf π Z →
              ∀ D ∈ T.boundary,
                ∀ x' : ↥X',
                  ∃ (U' : X'.Opens) (ε : ℕ),
                    x' ∈ U' ∧ (ε = 0 ∨ ε = 1) ∧
                      (ε = 1 ↔ ∃ V : T.scheme.Opens, π x' ∈ V ∧
                        (Z.support : Set ↥T.scheme) ∩ (V : Set ↥T.scheme)
                          ⊆ (D.support : Set ↥T.scheme)) ∧
                      (D.comap π).comap U'.ι =
                        (Blowup.strictTransform π Z D).comap U'.ι *
                          (Blowup.exceptionalIdeal π Z).comap U'.ι ^ ε
  components_subset_divisor_iff :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (J : Finset (Fin T.boundary.length)),
        ∀ C ∈ intersectionComponents T.boundary J,
          ∀ i : Fin T.boundary.length,
            C ⊆ ((T.boundary.get i).support : Set ↥T.scheme) ↔ i ∈ J
  transformed_components :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (J₀ : Finset (Fin T.boundary.length)),
        ∀ 𝒞 ⊆ intersectionComponents T.boundary J₀,
          ∀ (hop : IsOpen (⇑(intersectionIdeal T.boundary J₀).subschemeι ⁻¹' ⋃₀ 𝒞))
            (X' : Scheme.{u}) (π : X' ⟶ T.scheme),
            Blowup.IsBlowupAlongIdealSheaf π (componentUnionIdeal T.boundary J₀ 𝒞 hop) →
              ∀ (J : Finset (Fin T.boundary.length)),
                ∀ C' ∈ intersectionComponents
                    (transformedBoundary π (componentUnionIdeal T.boundary J₀ 𝒞 hop) T.boundary)
                    (Finset.image
                      (strictTransformIndex π (componentUnionIdeal T.boundary J₀ 𝒞 hop) T.boundary) J),
                  ∀ ξ' : ↥X', IsGenericPoint ξ' C' →
                    ξ' ∉ (Blowup.exceptionalIdeal π
                        (componentUnionIdeal T.boundary J₀ 𝒞 hop)).support ∧
                      ∃ C ∈ intersectionComponents T.boundary J,
                        C ∉ 𝒞 ∧
                          C' = closure (⇑π ⁻¹' C \
                              ((Blowup.exceptionalIdeal π
                                (componentUnionIdeal T.boundary J₀ 𝒞 hop)).support :
                                  Set ↥X')) ∧
                            ∀ ξ : ↥T.scheme, IsGenericPoint ξ C → π ξ' = ξ

theorem monomialCaseHypotheses_of_monomialCenterHypotheses (h : MonomialCenterHypotheses.{u}) :
    MonomialCaseHypotheses.{u} := by
  exact {
    card_lt_dim := MonomialCodimension.card_lt_krullDimSucc_of_nonempty
    center_smooth := h.center_smooth
    center_snc := h.center_snc
    blowup_total_transform := h.blowup_total_transform
    components_subset_divisor_iff := h.components_subset_divisor_iff
    transformed_components := h.transformed_components
    stratum_smooth := MonomialChart.smooth_intersectionIdeal_subscheme
    orderAt_comap_off_exceptional := fun T hT X' π Z hπ x' hx' A =>
      orderAt_comap_eq_of_notMem_exceptionalIdeal T hT Z X' π hπ x' hx' A
    orderAt_boundary_eq_one := MonomialChart.orderAt_boundary_eq_one }

end MonomialCenterCase

namespace StrictTransformCase

structure StrictTransformHypotheses : Prop extends MonomialCenterCase.MonomialCenterHypotheses.{u} where
  strictTransform_components :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (Z : T.scheme.IdealSheafData),
        AlgebraicGeometry.Smooth (Z.subschemeι ≫ T.structMap) →
          HasStrictNormalCrossingsWith T.structMap Z T.boundary →
            ∀ (X' : Scheme.{u}) (π : X' ⟶ T.scheme), Blowup.IsBlowupAlongIdealSheaf π Z →
              ∀ D ∈ T.boundary,
                ∀ C' : Set ↥X',
                  IsIrreducibleComponentOf C' ((Blowup.strictTransform π Z D).support : Set ↥X') →
                    ∃ (ξ' : ↥X') (C : Set ↥T.scheme),
                      C' = closure ({ξ'} : Set ↥X') ∧
                        ξ' ∉ (Blowup.exceptionalIdeal π Z).support ∧
                          IsIrreducibleComponentOf C (D.support : Set ↥T.scheme) ∧
                            ¬ C ⊆ (Z.support : Set ↥T.scheme) ∧
                              C = closure ({π ξ'} : Set ↥T.scheme)

theorem strictTransformHypotheses_of_residualHypotheses (h : StrictTransformHypotheses.{u}) :
    StrictTransformAndMonomialCaseHypotheses.{u} := by
  exact {
    strictTransform_components := h.strictTransform_components
    monomial := MonomialCenterCase.monomialCaseHypotheses_of_monomialCenterHypotheses
      h.toMonomialCenterHypotheses }

end StrictTransformCase

end FunctorialResolution.EmbeddedResolution
end
end

-- Source module: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.TransformedComponentHypotheses

section

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace MonomialStrictTransformComponents

structure TransformedComponentHypotheses : Prop where
  transformed_components :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (J₀ : Finset (Fin T.boundary.length)),
        ∀ 𝒞 ⊆ intersectionComponents T.boundary J₀,
          ∀ (hop : IsOpen (⇑(intersectionIdeal T.boundary J₀).subschemeι ⁻¹' ⋃₀ 𝒞))
            (X' : Scheme.{u}) (π : X' ⟶ T.scheme),
            Blowup.IsBlowupAlongIdealSheaf π (componentUnionIdeal T.boundary J₀ 𝒞 hop) →
              ∀ (J : Finset (Fin T.boundary.length)),
                ∀ C' ∈ intersectionComponents
                    (transformedBoundary π (componentUnionIdeal T.boundary J₀ 𝒞 hop) T.boundary)
                    (Finset.image
                      (strictTransformIndex π (componentUnionIdeal T.boundary J₀ 𝒞 hop) T.boundary) J),
                  ∀ ξ' : ↥X', IsGenericPoint ξ' C' →
                    ξ' ∉ (Blowup.exceptionalIdeal π
                        (componentUnionIdeal T.boundary J₀ 𝒞 hop)).support ∧
                      ∃ C ∈ intersectionComponents T.boundary J,
                        C ∉ 𝒞 ∧
                          C' = closure (⇑π ⁻¹' C \
                              ((Blowup.exceptionalIdeal π
                                (componentUnionIdeal T.boundary J₀ 𝒞 hop)).support :
                                  Set ↥X')) ∧
                            ∀ ξ : ↥T.scheme, IsGenericPoint ξ C → π ξ' = ξ
  strictTransform_components :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (Z : T.scheme.IdealSheafData),
        AlgebraicGeometry.Smooth (Z.subschemeι ≫ T.structMap) →
          HasStrictNormalCrossingsWith T.structMap Z T.boundary →
            ∀ (X' : Scheme.{u}) (π : X' ⟶ T.scheme), Blowup.IsBlowupAlongIdealSheaf π Z →
              ∀ D ∈ T.boundary,
                ∀ C' : Set ↥X',
                  IsIrreducibleComponentOf C' ((Blowup.strictTransform π Z D).support : Set ↥X') →
                    ∃ (ξ' : ↥X') (C : Set ↥T.scheme),
                      C' = closure ({ξ'} : Set ↥X') ∧
                        ξ' ∉ (Blowup.exceptionalIdeal π Z).support ∧
                          IsIrreducibleComponentOf C (D.support : Set ↥T.scheme) ∧
                            ¬ C ⊆ (Z.support : Set ↥T.scheme) ∧
                              C = closure ({π ξ'} : Set ↥T.scheme)

theorem strictTransformHypotheses_of_transformedComponents (h : TransformedComponentHypotheses.{u}) :
    StrictTransformCase.StrictTransformHypotheses.{u} := by
  exact {
    toMonomialCenterHypotheses := {
      center_smooth := MonomialCenterGeometry.smooth_componentUnionIdeal
      center_snc := MonomialCenterGeometry.hasStrictNormalCrossingsWith_componentUnionIdeal
      blowup_total_transform := comap_eq_strictTransform_mul_exceptionalIdeal_pow
      components_subset_divisor_iff := intersectionComponents_subset_support_iff
      transformed_components := h.transformed_components }
    strictTransform_components := h.strictTransform_components }

end MonomialStrictTransformComponents

end FunctorialResolution.EmbeddedResolution

end
end
end

-- Source module: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.GeometricPrincipalization

section

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

theorem MonomialStrictTransformComponents.transformedComponentHypotheses :
    MonomialStrictTransformComponents.TransformedComponentHypotheses.{u} := by
  exact {
    transformed_components := intersectionComponents_transformedBoundary_of_isBlowupAlongIdealSheaf
    strictTransform_components := exists_eq_closure_of_isIrreducibleComponentOf_strictTransform }

theorem principalizationGeometryHypotheses : PrincipalizationGeometryHypotheses.{u} := by
  have h := StrictTransformCase.strictTransformHypotheses_of_residualHypotheses
    (MonomialStrictTransformComponents.strictTransformHypotheses_of_transformedComponents
      MonomialStrictTransformComponents.transformedComponentHypotheses)
  have hOrder : OrderReductionHypotheses.{u} := {
    controlledTransform_orderAt_le := orderAt_controlledTransform_le_of_orderAt_eq_on_center
    strictTransform_components := h.strictTransform_components
    monomial := h.monomial }
  exact geometricHypotheses_of_orderReductionHypotheses hOrder

end FunctorialResolution.EmbeddedResolution

end
end
end

-- Source module: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.CanonicalRulesCorrect

section

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

theorem isCorrect_canonicalAlgorithmRules_of_hypotheses
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hdiv : DivisorReduction.DivisorReductionHypotheses hres)
    (hG : PrincipalizationGeometryHypotheses.{u}) :
    (canonicalAlgorithmRules hres).ReducesInductivelyOnDimension :=
  { divisorSpec := isBoundaryDivisorReduction_divisorFamily_canonicalAlgorithmRules hres hdiv
    divisorShift := isBoundaryPositionInvariant_divisorFamily_canonicalAlgorithmRules hres hdiv
    maxOrderSpec := fun n A L hspec =>
      MaxOrderReduction.isMaxOrderReduction_canonicalAlgorithmRules hG hres n A L hspec
    orderSpec := OrderReductionProperties.isOrderReduction_orderFamily_of_strictTransformIsBlowup hres }

theorem isCorrect_canonicalAlgorithmRules
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) :
    (canonicalAlgorithmRules hres).ReducesInductivelyOnDimension :=
  isCorrect_canonicalAlgorithmRules_of_hypotheses hres
    (divisorReductionHypotheses_canonicalAlgorithmRules hres)
    principalizationGeometryHypotheses.{u}

end FunctorialResolution.EmbeddedResolution
end
end
