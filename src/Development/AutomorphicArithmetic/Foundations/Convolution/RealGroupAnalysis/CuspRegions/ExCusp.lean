module

public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.FormsIrr
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.CuspRegions.CarrierEq

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

theorem UpperTheory.ConvolutionTheory.Dr.exCusp :
    UpperTheory.ConvolutionTheory.Dr.ExCusp := by
  intro E _ _ _ n μ _ V hV
  obtain ⟨hs, hne, hirr, -⟩ := formsIrr E n μ V hV
  let π₀ := Fb.ofIrr _ hs (hs.isIrreducible_iff.2 ⟨hne, hirr⟩)
  have hπ₀ : Fb.carrier π₀ = formsIn μ V := Fb.carrier_ofIrr _ _ _
  refine ⟨π₀, ⟨hV, hπ₀⟩, fun π h => TR.CuspSub.ext ?_⟩
  rw [← Fb.map_carrier π, ← Fb.map_carrier π₀, h.carrier_eq, hπ₀]
