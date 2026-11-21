module

public import Mathlib
public import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
public import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DimensionRecursion
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.CanonicalPrincipalization
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.GeometryHypotheses
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.MonomialCenterHypotheses
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.TransformedComponentHypotheses
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.OrderReductionHypotheses
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.ControlledTransformOrderBound
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.StrictTransformComponents
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.TransformedBoundaryComponents
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

theorem MonomialStrictTransformComponents.transformedComponentHypotheses :
    MonomialStrictTransformComponents.TransformedComponentHypotheses.{u} :=
  { transformed_components := intersectionComponents_transformedBoundary_of_isBlowupAlongIdealSheaf
    strictTransform_components := exists_eq_closure_of_isIrreducibleComponentOf_strictTransform }

theorem principalizationGeometryHypotheses : PrincipalizationGeometryHypotheses.{u} := by
  have h := MonomialStrictTransformComponents.transformedComponentHypotheses.{u}
  have hR : OrderReductionHypotheses.{u} :=
    { controlledTransform_orderAt_le := orderAt_controlledTransform_le_of_orderAt_eq_on_center
      strictTransform_components := h.strictTransform_components
      monomial :=
        { card_lt_dim := MonomialCodimension.card_lt_krullDimSucc_of_nonempty
          center_smooth := MonomialCenterGeometry.smooth_componentUnionIdeal
          center_snc := MonomialCenterGeometry.hasStrictNormalCrossingsWith_componentUnionIdeal
          blowup_total_transform := comap_eq_strictTransform_mul_exceptionalIdeal_pow
          components_subset_divisor_iff := intersectionComponents_subset_support_iff
          transformed_components := h.transformed_components
          stratum_smooth := MonomialChart.smooth_intersectionIdeal_subscheme
          orderAt_comap_off_exceptional := fun T hT X' π Z hπ x' hx' A =>
            orderAt_comap_eq_of_notMem_exceptionalIdeal T hT Z X' π hπ x' hx' A
          orderAt_boundary_eq_one := MonomialChart.orderAt_boundary_eq_one } }
  exact geometricHypotheses_of_orderReductionHypotheses hR

end FunctorialResolution.EmbeddedResolution

end
