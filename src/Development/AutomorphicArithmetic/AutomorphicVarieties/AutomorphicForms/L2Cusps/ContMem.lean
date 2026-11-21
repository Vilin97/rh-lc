module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.AbsCompactAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.Assemble
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.SplitEq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.LiftCmp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ConstantTermEqZeroOfIsCuspidal

@[expose] public section

open MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GlobalTheory.DiscSpec
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum

theorem UpperTheory.V.KernelIndexFullLattice.contMem_holds :
    UpperTheory.V.KernelIndexFullLattice.ContMem := by
  intro E _ _ _ a μ _ μ₁ _ hp φ hφ h
  obtain ⟨hc, hl, hz, hcu⟩ := mem_cuspCont.1 hφ
  have hL : IsLeftInvariant φ := fun γ g => hl γ g
  have hcusp : AutomorphicForm.IsCuspidal φ := UpperTheory.constantTerm_eq_zero_of_isCuspidal E a φ hL hc hcu
  have hr : ∀ g : GA E a, φ (retractOne g : UpperTheory.V.KernelIndexFullLattice.G1 E a) = φ g := fun g => by
    obtain ⟨t, ht⟩ := UpperTheory.V.KernelIndexFullLattice.exists_split (E := E) (a := a) UpperTheory.V.KernelIndexFullLattice.splitEq_holds
      (Reduction.detModule E a g)
    have h1 := hz t (retractOne g : UpperTheory.V.KernelIndexFullLattice.G1 E a)
    rw [← h1, splitCentre_comm, coe_retractOne, ← ht, inv_mul_cancel_right]
  have hΦ : cuspQuot hL ∘ UpperTheory.V.KernelIndexFullLattice.quotMap E a = descend (latticeGL E a) φ :=
    funext fun q => hr q.out
  have hm : MemLp (cuspQuot hL) 2 (RightCosetSpace.quotientMeasure (UpperTheory.V.KernelIndexFullLattice.Γ1 E a) μ₁) := by
    have hs := (continuous_cuspQuot hL hc).aestronglyMeasurable
      (μ := Measure.map (UpperTheory.V.KernelIndexFullLattice.quotMap E a) (quotMeasure (latticeGL E a) μ))
    rw [← hp.map_eq, memLp_map_measure_iff hs hp.measurable.aemeasurable, hΦ]
    exact h.2
  have hv : hm.toLp _ ∈ cuspidalL2 μ₁ := by
    intro r h0 h1
    filter_upwards [ae_ctFun_congr μ₁ r (MemLp.coeFn_toLp hm)] with y hy
    rw [constantTermL2, hy]
    exact hcusp r h0 h1 y
  refine ⟨⟨hm.toLp _, hv⟩, l2DiscreteQuotient_ext_iff_lift_ae_eq.2 ?_⟩
  have h2 : lift (latticeGL E a) (UpperTheory.V.KernelIndexFullLattice.cmp hp ⟨hm.toLp _, hv⟩) =ᵐ[μ]
      fun g => cuspQuot hL (RightCosetSpace.mk (UpperTheory.V.KernelIndexFullLattice.Γ1 E a) (retractOne g)) := by
    have h1 := Lp.coeFn_compMeasurePreserving (hm.toLp _) hp
    have h2 := hp.quasiMeasurePreserving.ae (MemLp.coeFn_toLp hm)
    have h3 : ∀ᵐ q ∂(quotMeasure (latticeGL E a) μ),
        (UpperTheory.V.KernelIndexFullLattice.cmp hp ⟨hm.toLp _, hv⟩ : Quot (latticeGL E a) → ℂ) q =
          cuspQuot hL (UpperTheory.V.KernelIndexFullLattice.quotMap E a q) := by
      filter_upwards [h1, h2] with q hq1 hq2
      exact hq1.trans hq2
    filter_upwards [ae_quotMeasure_iff.1 h3] with g hg
    rw [← UpperTheory.V.KernelIndexFullLattice.quotMk_holds E a g]
    exact hg
  refine h2.trans (Filter.EventuallyEq.trans (Filter.Eventually.of_forall fun g => ?_) h.lift_toL2_ae_eq.symm)
  exact hr g
