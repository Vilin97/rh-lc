module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraMapCompStalkAlg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopPairDForm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.Linter.Style
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
import ReciprocityTheory.AnalyticForms.RegularLocalRings.DivSheaf
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotangentImagesLinearIndependent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComponentStalkDerivationOfFunctionFieldExtStatement
import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanLogDerGermsStatement
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Monomial
import ReciprocityTheory.AnalyticForms.RegularLocalRings.RegDom

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundaryComponentStalkRegularBoundaryIdealProdPa

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

theorem GlobalTheory.LogKSDiv.boundary_germ_snc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), ∀ [IsIntegral (X₀ TF.Y Z)] [SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z)] (x : X₀ TF.Y Z) (U : TF.Y.X.affineOpens), ∀ (hx : (barComp TF.Y Z).ι x ∈ U.1), x ∉ (j₀ TF.Y Z).opensRange → IsRegularLocalRing ((X₀ TF.Y Z).presheaf.stalk x) ∧ ∃ (n : ℕ) (f : Fin n → (X₀ TF.Y Z).presheaf.stalk x) (J : Finset (Fin n)), ReciprocityTheory.AnForm.R.FinalTheorems.Rsp ((X₀ TF.Y Z).presheaf.stalk x) n f ∧ J.Nonempty ∧ Ideal.map (GlobalTheory.LogKSDiv.stalkHom TF Z x U hx) ((Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl).ideal U) = Ideal.span {∏ i ∈ J, f i} := by
  intro E _ _ _ H Dw l Xo c TF Z _ _ x U hx hnot
  classical
  obtain ⟨hreg, V, hyV, n, f', J, hrsp, hV⟩ := TF.snc ((barComp TF.Y Z).ι x)
  let φ : TF.Y.X.presheaf.stalk ((barComp TF.Y Z).ι x) ≃+* (X₀ TF.Y Z).presheaf.stalk x :=
    (asIso ((barComp TF.Y Z).ι.stalkMap x)).commRingCatIsoToRingEquiv
  have hφ : ∀ a, φ a = ((barComp TF.Y Z).ι.stalkMap x).hom a := fun _ => rfl
  refine ⟨IsRegularLocalRing.of_ringEquiv φ, n, fun i => φ (TF.Y.X.presheaf.germ V.1 _ hyV (f' i)), J, ?_, ?_, ?_⟩
  · obtain ⟨hspan, hdim⟩ := hrsp
    refine ⟨?_, hdim.trans (ringKrullDim_eq_of_ringEquiv φ)⟩
    have hr : Set.range (fun i => φ (TF.Y.X.presheaf.germ V.1 _ hyV (f' i))) =
        φ '' Set.range (fun i => TF.Y.X.presheaf.germ V.1 _ hyV (f' i)) := Set.range_comp _ _
    rw [hr, ← Ideal.map_span, hspan]
    exact (IsLocalRing.eq_maximalIdeal (Ideal.map_isMaximal_of_equiv φ))
  · rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    apply hnot
    rw [Finset.prod_empty, Ideal.span_singleton_one] at hV
    have hst : ReciprocityTheory.AnForm.R.FinalTheorems.stalkId (LogKS.boundary TF.Y) ((barComp TF.Y Z).ι x) = ⊤ := by
      rw [ReciprocityTheory.AnForm.R.ds_stalkId_eq_map _ V _ hyV, hV, Ideal.map_top]
    have hns := (ReciprocityTheory.AnForm.R.mem_support_iff_stalkId (LogKS.boundary TF.Y) ((barComp TF.Y Z).ι x)).not.mpr
      (not_not.mpr hst)
    rw [LogKS.boundary, Scheme.IdealSheafData.coe_support_vanishingIdeal] at hns
    have hin : (barComp TF.Y Z).ι x ∈ LogKS.interior TF.Y := by
      simpa using hns
    rw [LogKS.interior] at hin
    obtain ⟨z, hz⟩ := hin
    have hzB : z ∈ TF.Y.j ⁻¹ᵁ barComp TF.Y Z := by
      show TF.Y.j z ∈ barComp TF.Y Z
      rw [hz]; first | exact x.2 | simp | exact (barComp TF.Y Z).range_ι.le ⟨x, rfl⟩
    refine ⟨⟨z, hzB⟩, (barComp TF.Y Z).ι.isOpenEmbedding.injective ?_⟩
    have h2 := congrArg (fun f => f.base ⟨z, hzB⟩) (j₀_ι TF.Y Z)
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h2
    first | exact h2.trans hz | (refine Eq.trans ?_ hz; exact h2) | (rw [Scheme.Hom.comp_apply] at h2; exact h2.trans hz)
  · have e1 : Ideal.map (GlobalTheory.LogKSDiv.stalkHom TF Z x U hx)
        ((Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl).ideal U) =
        Ideal.map φ.toRingHom (Ideal.map (TF.Y.X.presheaf.germ U.1 _ hx).hom
          ((Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl).ideal U)) := by
      rw [Ideal.map_map]
      congr 1
      ext r
      simp only [GlobalTheory.LogKSDiv.stalkHom, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, hφ]
      rw [Scheme.Hom.germ_stalkMap_apply]
    have hVb : (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl).ideal V =
        Ideal.span {∏ i ∈ J, f' i} := hV
    rw [e1, ← ReciprocityTheory.AnForm.R.ds_stalkId_eq_map _ U _ hx, ReciprocityTheory.AnForm.R.ds_stalkId_eq_map _ V _ hyV, hVb,
      Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton, map_prod]
    rw [map_prod]
    rfl
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundaryComponentStalkRegularBoundaryIdealProdPaStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

theorem _root_.GlobalTheory.T.boundary_componentStalk_regular_boundaryIdeal_prod_params : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), ∀ [IsIntegral (X₀ TF.Y Z)] [SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z)] (x : X₀ TF.Y Z) (U : TF.Y.X.affineOpens), ∀ (hx : (barComp TF.Y Z).ι x ∈ U.1), x ∉ (j₀ TF.Y Z).opensRange → IsRegularLocalRing ((X₀ TF.Y Z).presheaf.stalk x) ∧ ∃ (n : ℕ) (f : Fin n → (X₀ TF.Y Z).presheaf.stalk x) (J : Finset (Fin n)), ReciprocityTheory.AnForm.R.FinalTheorems.Rsp ((X₀ TF.Y Z).presheaf.stalk x) n f ∧ J.Nonempty ∧ Ideal.map (GlobalTheory.LogKSDiv.stalkHom TF Z x U hx) ((Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl).ideal U) = Ideal.span {∏ i ∈ J, f i} := by
  first | exact @GlobalTheory.LogKSDiv.boundary_germ_snc | exact GlobalTheory.LogKSDiv.boundary_germ_snc | (intros; apply GlobalTheory.LogKSDiv.boundary_germ_snc <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartRestrEqGerm

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

namespace GlobalTheory.LogKSDiv.Spread'

theorem germ_pt' {X : Scheme.{0}} (B : X.Opens) (y : B.toScheme) {U : X.Opens} (hU : IsAffineOpen U)
    (hy : B.ι y ∈ U) :
    spMap (X.presheaf.germ U (B.ι y) hy ≫ B.ι.stalkMap y).hom ≫ hU.fromSpec = B.toScheme.fromSpecStalk y ≫ B.ι := by
  show Spec.map (X.presheaf.germ U (B.ι y) hy ≫ B.ι.stalkMap y) ≫ _ = _
  rw [Spec.map_comp, Category.assoc, ← IsAffineOpen.fromSpecStalk, hU.fromSpecStalk_eq_fromSpecStalk,
    Scheme.SpecMap_stalkMap_fromSpecStalk]

end GlobalTheory.LogKSDiv.Spread'

set_option autoImplicit false

theorem GlobalTheory.LogKSDiv.chartRestr_eq_germ : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), ∀ [IsIntegral (X₀ TF.Y Z)] [SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z)] (x : X₀ TF.Y Z) (U : TF.Y.X.affineOpens), U.1 ≤ barComp TF.Y Z → ∀ (hx : (barComp TF.Y Z).ι x ∈ U.1) (ρ : Γ(TF.Y.X, U.1) →+* (X₀ TF.Y Z).functionField), spMap ρ ≫ LogKS.chart U = GlobalTheory.LogKSDiv.genPt TF Z ≫ (barComp TF.Y Z).ι → ∀ r, ρ r = algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField (GlobalTheory.LogKSDiv.stalkHom TF Z x U hx r) := by
  intro E _ _ _ H Dw l Xo c TF Z _ _ x U hU hx ρ hρ r
  have hη : (barComp TF.Y Z).ι (genericPoint (X₀ TF.Y Z)) ∈ U.1 := by
    have h := (genericPoint_spec (X₀ TF.Y Z)).mem_open_set_iff ((barComp TF.Y Z).ι ⁻¹ᵁ U.1).isOpen
    exact h.2 ⟨x, trivial, hx⟩
  set ψ := (TF.Y.X.presheaf.germ U.1 _ hη ≫ (barComp TF.Y Z).ι.stalkMap (genericPoint (X₀ TF.Y Z))).hom with hψ
  have hg := GlobalTheory.LogKSDiv.Spread'.germ_pt' (barComp TF.Y Z) (genericPoint (X₀ TF.Y Z)) U.2 hη
  have hmono : Mono (LogKS.chart U) := by
    unfold LogKS.chart
    have : IsOpenImmersion U.2.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec U.2
    infer_instance
  have e1 : spMap ρ = spMap ψ := by
    rw [← cancel_mono (LogKS.chart U), hρ]
    exact hg.symm
  have e2 : ρ = ψ := by
    have := Spec.map_injective e1
    exact congrArg CommRingCat.Hom.hom this
  rw [e2, hψ, CommRingCat.hom_comp, RingHom.comp_apply, Scheme.Hom.germ_stalkMap_apply]
  simp only [GlobalTheory.LogKSDiv.stalkHom, RingHom.comp_apply, RingHom.algebraMap_toAlgebra]
  change _ = ((X₀ TF.Y Z).presheaf.germ _ x hx ≫ (X₀ TF.Y Z).presheaf.stalkSpecializes _).hom _
  erw [TopCat.Presheaf.germ_stalkSpecializes]
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameEqUnitSmulDForm

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogKSDiv

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.TopForm

theorem frame_eq_unit_smul_dForm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), ∀ [IsIntegral (X₀ TF.Y Z)] [SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z)] (x : X₀ TF.Y Z) (U' : (X₀ TF.Y Z).Opens) (ω : TopForm.FormsOn (s₀ TF.Y Z) Dw.dim U'), TopForm.IsFrame ω → ∀ hx : x ∈ U', letI := (GlobalTheory.LogKSDiv.stalkAlg TF Z x).toAlgebra; ∃ (g : Fin Dw.dim → (X₀ TF.Y Z).presheaf.stalk x) (bΩ : Module.Basis (Fin Dw.dim) ((X₀ TF.Y Z).presheaf.stalk x) Ω[(X₀ TF.Y Z).presheaf.stalk x⁄c.F]) (u : (X₀ TF.Y Z).presheaf.stalk x), (∀ i, bΩ i = KaehlerDifferential.D c.F ((X₀ TF.Y Z).presheaf.stalk x) (g i)) ∧ IsUnit u ∧ formOf U' (gen_mem hx) ω = algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField u • TopForm.dForm (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)) (fun i => algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField (g i)) := by
  intro E _ _ _ H Dw l Xo c TF Z _ _ x U' ω hω hx
  letI := (GlobalTheory.LogKSDiv.stalkAlg TF Z x).toAlgebra
  obtain ⟨U, y, b, hUU', hxU, hU, hb⟩ :=
    GlobalTheory.AdaptedFrame.exists_basis_dFun (s₀ TF.Y Z) Dw.dim hx
  have hy : IsFreeGen Γ(X₀ TF.Y Z, U) (dOn (s₀ TF.Y Z) y) := isFreeGen_dForm y b hb
  have hres : IsFrame (resForm hUU' ω) := hω.res hU hUU'
  obtain ⟨a, ha⟩ := hy.2 (resForm hUU' ω)
  have hau : IsUnit a := by
    have := hres.gen
    rw [← ha] at this
    exact hy.smul_iff.1 this
  have hgU : genericPoint (X₀ TF.Y Z) ∈ U := gen_mem hxU
  have hform : formOf U' (gen_mem hx) ω =
      fnOf U hgU a • dForm (constFn (s₀ TF.Y Z)) (fun i => fnOf U hgU (y i)) := by
    rw [← formOf_resForm hUU' hgU ω, ← ha, map_smulₛₗ]
    congr 1
    exact formMap_dForm _ _ _
  letI iΓ : Algebra c.F Γ(X₀ TF.Y Z, U) := (algX (s₀ TF.Y Z) U).toAlgebra
  letI iΓA : Algebra Γ(X₀ TF.Y Z, U) ((X₀ TF.Y Z).presheaf.stalk x) :=
    ((X₀ TF.Y Z).presheaf.germ U x hxU).hom.toAlgebra
  have hsc : algebraMap c.F ((X₀ TF.Y Z).presheaf.stalk x) =
      (algebraMap Γ(X₀ TF.Y Z, U) ((X₀ TF.Y Z).presheaf.stalk x)).comp
        (algebraMap c.F Γ(X₀ TF.Y Z, U)) := by
    ext t
    change ((X₀ TF.Y Z).presheaf.germ ⊤ x trivial).hom (algX (s₀ TF.Y Z) ⊤ t) =
      ((X₀ TF.Y Z).presheaf.germ U x hxU).hom (algX (s₀ TF.Y Z) U t)
    rw [← resG_comp_algX (s₀ TF.Y Z) (le_top : U ≤ ⊤), RingHom.comp_apply, germ_resG]
  haveI : IsScalarTower c.F Γ(X₀ TF.Y Z, U) ((X₀ TF.Y Z).presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_eq' hsc
  haveI : IsLocalization.AtPrime ((X₀ TF.Y Z).presheaf.stalk x) (hU.primeIdealOf ⟨x, hxU⟩).asIdeal :=
    hU.isLocalization_stalk ⟨x, hxU⟩
  haveI : Algebra.FormallyEtale Γ(X₀ TF.Y Z, U) ((X₀ TF.Y Z).presheaf.stalk x) :=
    .of_isLocalization (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
  have hbc := KaehlerDifferential.isBaseChange_of_formallyEtale c.F Γ(X₀ TF.Y Z, U)
    ((X₀ TF.Y Z).presheaf.stalk x)
  refine ⟨fun i => ((X₀ TF.Y Z).presheaf.germ U x hxU).hom (y i), hbc.basis b,
    ((X₀ TF.Y Z).presheaf.germ U x hxU).hom a, fun i => ?_, hau.map _, ?_⟩
  · rw [IsBaseChange.basis_apply, hb]
    exact KaehlerDifferential.map_D c.F c.F _ _ (y i)
  · rw [hform]
    simp only [algebraMap_germ]
end GlobalTheory.LogKSDiv
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogVectorFieldTopFormPairingRegularAtPoint

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogKSDiv

open IsLocalRing

theorem isUnit_det_of_span_eq_top (k A : Type) [CommRing k] [CommRing A] [Algebra k A] {N : ℕ} (g : Fin N → A)
    (bΩ : Module.Basis (Fin N) A Ω[A⁄k]) (hg : ∀ i, bΩ i = KaehlerDifferential.D k A (g i))
    (δ : Fin N → Derivation k A A) (hδ : Submodule.span A (Set.range δ) = ⊤) :
    IsUnit (Matrix.of fun i j => δ j (g i)).det := by
  classical
  have h : ∀ i, ∃ a : Fin N → A, ∑ j, a j • δ j = KaehlerDifferential.linearMapEquivDerivation k A (bΩ.coord i) :=
    fun i => (Submodule.mem_span_range_iff_exists_fun A).1 (hδ ▸ Submodule.mem_top)
  choose a ha using h
  have hm : (Matrix.of fun i j => δ j (g i)) * (Matrix.of fun j i => a i j) = 1 := by
    ext l i
    have h1 := congrArg (fun d : Derivation k A A => d (g l)) (ha i)
    simp only [KaehlerDifferential.linearMapEquivDerivation_apply_apply, ← hg] at h1
    rw [Matrix.mul_apply, Matrix.one_apply]
    have h2 : (∑ j, a i j • δ j) (g l) = ∑ j, a i j * δ j (g l) := by
      have := map_sum (FunLike.coeAddMonoidHom (Derivation k A A) A A) (fun j => a i j • δ j) Finset.univ
      have h3 := congrFun this (g l)
      rw [Finset.sum_apply] at h3
      exact h3
    rw [h2] at h1
    simp only [Matrix.of_apply, mul_comm (δ _ _)]
    rw [h1]
    simp [Finsupp.single_apply]
  exact Matrix.isUnit_det_of_right_inverse hm

theorem det_mem_maximalIdeal (k A : Type) [CommRing k] [CommRing A] [IsLocalRing A] [Algebra k A] {N : ℕ}
    (g : Fin N → A) (bΩ : Module.Basis (Fin N) A Ω[A⁄k]) (hg : ∀ i, bΩ i = KaehlerDifferential.D k A (g i))
    (δ : Fin N → Derivation k A A) (t : A) (ht : t ∈ maximalIdeal A)
    (hd : KaehlerDifferential.D k A t ∉ (maximalIdeal A) • (⊤ : Submodule A Ω[A⁄k]))
    (hδ : ∀ j, δ j t ∈ Ideal.span {t}) : (Matrix.of fun i j => δ j (g i)).det ∈ maximalIdeal A := by
  classical
  set c : Fin N → A := fun i => bΩ.repr (KaehlerDifferential.D k A t) i with hc
  have hsum : KaehlerDifferential.D k A t = ∑ i, c i • bΩ i := (bΩ.sum_repr _).symm
  have hne : (fun i => residue A (c i)) ≠ 0 := by
    intro h0
    apply hd
    rw [hsum]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul ?_ Submodule.mem_top
    exact (residue_eq_zero_iff _).1 (congrFun h0 i)
  rw [← residue_eq_zero_iff, RingHom.map_det]
  refine Matrix.exists_vecMul_eq_zero_iff.1 ⟨_, hne, ?_⟩
  funext j
  have h1 : δ j t = ∑ i, c i * δ j (g i) := by

    rw [← (δ j).liftKaehlerDifferential_comp_D t, hsum, map_sum]
    simp [hg]
  have h2 : residue A (δ j t) = 0 :=
    (residue_eq_zero_iff _).2 ((Ideal.span_singleton_le_iff_mem _).2 ht (hδ j))

  rw [h1, map_sum] at h2
  simpa [Matrix.vecMul, dotProduct] using h2

theorem derivation_mem_span_of_prod {k A : Type} [CommRing k] [CommRing A] [IsRegularLocalRing A] [Algebra k A] {n : ℕ}
    (f : Fin n → A) (hf : ReciprocityTheory.AnForm.R.FinalTheorems.Rsp A n f) (J : Finset (Fin n)) {j : Fin n} (hj : j ∈ J)
    (δ : Derivation k A A) (hδ : δ (∏ i ∈ J, f i) ∈ Ideal.span {∏ i ∈ J, f i}) : δ (f j) ∈ Ideal.span {f j} := by
  classical
  have hD : IsDomain A := ReciprocityTheory.AnForm.R.isDomain_of_isRegularLocalRing
  have hp := ReciprocityTheory.AnForm.R.prime_of_regular_params f hf.1 hf.2
  rw [Ideal.mem_span_singleton] at hδ ⊢
  rw [← Finset.mul_prod_erase J f hj, Derivation.leibniz, smul_eq_mul, smul_eq_mul] at hδ
  have h1 : f j ∣ (∏ i ∈ J.erase j, f i) * δ (f j) :=
    (dvd_add_right (dvd_mul_right _ _)).1 ((dvd_mul_right _ _).trans hδ)
  refine ((hp j).dvd_or_dvd h1).resolve_left fun h2 => ?_
  obtain ⟨i, hi, h3⟩ := (hp j).exists_mem_finset_dvd h2
  exact (ReciprocityTheory.AnForm.R.regular_params_spec f hf.1 hf.2).2 j i (Finset.ne_of_mem_erase hi).symm
    ((hp j).associated_of_dvd (hp i) h3)

theorem D_notMem_smul_top {k A : Type} [CommRing k] [CommRing A] [IsLocalRing A] [Algebra k A]
    [Algebra.FormallySmooth k (ResidueField A)] {t : A} (ht : t ∈ maximalIdeal A) (ht2 : t ∉ maximalIdeal A ^ 2) :
    KaehlerDifferential.D k A t ∉ (maximalIdeal A) • (⊤ : Submodule A Ω[A⁄k]) := by
  intro hm
  have h := GlobalTheory.AdaptedFrame.linearIndependent_tmul_D (k := k) (fun _ : Unit => t) (fun _ => ht)
    (linearIndependent_unique_iff.2 (by
      intro h0
      exact ht2 ((Ideal.toCotangent_eq_zero _ _).1 h0)))
  refine h.ne_zero () ?_
  generalize KaehlerDifferential.D k A t = w at hm
  refine Submodule.smul_induction_on hm (fun r hr w _ => ?_) (fun x y hx hy => ?_)
  · rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_one, ResidueField.algebraMap_eq,
      (residue_eq_zero_iff _).2 hr, TensorProduct.zero_tmul]
  · rw [TensorProduct.tmul_add, hx, hy, add_zero]

theorem derivation_mem_map {k R A : Type} [CommRing k] [CommRing R] [CommRing A] [Algebra k A] (φ : R →+* A)
    (I : Ideal R) (d : R → R) (hd : ∀ r ∈ I, d r ∈ I) (δ : Derivation k A A) (hδ : ∀ r, δ (φ r) = φ (d r))
    {a : A} (ha : a ∈ I.map φ) : δ a ∈ I.map φ := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨r, hr, rfl⟩ := hx
    rw [hδ]
    exact Ideal.mem_map_of_mem _ (hd r hr)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x hx0 hx =>
    rw [smul_eq_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact add_mem (Ideal.mul_mem_left _ _ hx) (Ideal.mul_mem_right _ _ hx0)

theorem exists_boundary_param : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), ∀ [IsIntegral (X₀ TF.Y Z)] [SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z)] (x : X₀ TF.Y Z) (U : TF.Y.X.affineOpens), ∀ (hx : (barComp TF.Y Z).ι x ∈ U.1) (b : Module.Basis (Fin Dw.dim) Γ(TF.Y.X, U.1) (LogKS.logDer TF.Y.s (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl) U)), letI := (GlobalTheory.LogKSDiv.stalkAlg TF Z x).toAlgebra; ∀ δ : Fin Dw.dim → Derivation c.F ((X₀ TF.Y Z).presheaf.stalk x) ((X₀ TF.Y Z).presheaf.stalk x), (∀ j r, δ j (GlobalTheory.LogKSDiv.stalkHom TF Z x U hx r) = GlobalTheory.LogKSDiv.stalkHom TF Z x U hx ((b j).1 r)) → x ∉ (j₀ TF.Y Z).opensRange → ∃ t ∈ IsLocalRing.maximalIdeal ((X₀ TF.Y Z).presheaf.stalk x), KaehlerDifferential.D c.F ((X₀ TF.Y Z).presheaf.stalk x) t ∉ (IsLocalRing.maximalIdeal ((X₀ TF.Y Z).presheaf.stalk x)) • (⊤ : Submodule ((X₀ TF.Y Z).presheaf.stalk x) Ω[(X₀ TF.Y Z).presheaf.stalk x⁄c.F]) ∧ ∀ j, δ j t ∈ Ideal.span {t} := by
  intro E _ _ _ H Dw l Xo c TF Z _ _ x U hx b δ hδ hn
  letI := (GlobalTheory.LogKSDiv.stalkAlg TF Z x).toAlgebra
  obtain ⟨hreg, n, f, J, hf, ⟨j, hj⟩, hI⟩ := GlobalTheory.T.boundary_componentStalk_regular_boundaryIdeal_prod_params E H Dw l Xo c TF Z x U hx hn
  have hm : f j ∈ maximalIdeal ((X₀ TF.Y Z).presheaf.stalk x) := hf.1 ▸ Ideal.subset_span ⟨j, rfl⟩
  refine ⟨f j, hm, ?_, fun i => ?_⟩
  · obtain ⟨V, hV, hxV, -⟩ := Opens.isBasis_iff_nbhd.1 (X₀ TF.Y Z).isBasis_affineOpens (show x ∈ (⊤ : (X₀ TF.Y Z).Opens) from trivial)
    haveI := GlobalTheory.AdaptedFrame.formallySmooth_residueField (s₀ TF.Y Z) (n := Dw.dim) hV x hxV (by
      ext t
      change ((X₀ TF.Y Z).presheaf.germ ⊤ x trivial).hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX (s₀ TF.Y Z) ⊤ t) =
        ((X₀ TF.Y Z).presheaf.germ V x hxV).hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX (s₀ TF.Y Z) V t)
      rw [← GlobalTheory.TopForm.resG_comp_algX (s₀ TF.Y Z) (le_top : V ≤ ⊤), RingHom.comp_apply, germ_resG])
    exact D_notMem_smul_top hm ((ReciprocityTheory.AnForm.R.regular_params_spec f hf.1 hf.2).1 j)
  · refine derivation_mem_span_of_prod f hf J hj (δ i) ?_
    rw [← hI]
    refine derivation_mem_map _ _ (b i).1 (b i).2.2 (δ i) (hδ i) ?_
    rw [hI]
    exact Ideal.subset_span rfl

theorem local_topPair : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), ∀ [IsIntegral (X₀ TF.Y Z)] [SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z)] (x : X₀ TF.Y Z) (U : TF.Y.X.affineOpens), U.1 ≤ barComp TF.Y Z → (barComp TF.Y Z).ι x ∈ U.1 → ∀ (ρ : Γ(TF.Y.X, U.1) →+* (X₀ TF.Y Z).functionField), spMap ρ ≫ LogKS.chart U = GlobalTheory.LogKSDiv.genPt TF Z ≫ (barComp TF.Y Z).ι → ∀ (b : Module.Basis (Fin Dw.dim) Γ(TF.Y.X, U.1) (LogKS.logDer TF.Y.s (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl) U)) (D : Fin Dw.dim → GlobalTheory.LogKSDiv.GenDer TF Z), (letI := (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)).toAlgebra; ∀ j r, (show Derivation c.F (X₀ TF.Y Z).functionField (X₀ TF.Y Z).functionField from D j) (ρ r) = ρ ((b j).1 r)) → ∀ (U' : (X₀ TF.Y Z).Opens) (ω : TopForm.FormsOn (s₀ TF.Y Z) Dw.dim U'), TopForm.IsFrame ω → ∀ hx : x ∈ U', RegAt x (GlobalTheory.LogKSDiv.topPair (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)) D (formOf U' (gen_mem hx) ω)) ∧ (UnitAt x (GlobalTheory.LogKSDiv.topPair (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)) D (formOf U' (gen_mem hx) ω)) ↔ x ∈ (j₀ TF.Y Z).opensRange) := by
  intro E _ _ _ H Dw l Xo c TF Z _ _ x U hU hxU ρ hρ b D hD U' ω hω hx
  have h1 := chartRestr_eq_germ E H Dw l Xo c TF Z x U hU hxU ρ hρ
  obtain ⟨δ, hδK, hδR⟩ := GlobalTheory.T.exists_componentStalkDerivation_of_functionField_extension E H Dw l Xo c TF Z x U hU hxU ρ h1 (fun j => (b j).1) D hD
  obtain ⟨g, bΩ, u, hg, hu, hform⟩ := frame_eq_unit_smul_dForm E H Dw l Xo c TF Z x U' ω hω hx
  letI := (stalkAlg TF Z x).toAlgebra
  have key : topPair (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)) D (formOf U' (gen_mem hx) ω) =
      algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField
        (u * (Matrix.of fun i j => δ j (g i)).det) := by
    rw [hform, LinearMap.map_smul, topPair_dForm, smul_eq_mul, map_mul, RingHom.map_det]
    congr 2
    ext i j
    exact hδK j (g i)
  refine ⟨⟨_, key.symm⟩, fun hU' => ?_, fun hr => ?_⟩
  · by_contra hn
    obtain ⟨t, htm, htd, htδ⟩ := exists_boundary_param E H Dw l Xo c TF Z x U hxU b δ hδR hn
    have hz := det_mem_maximalIdeal c.F _ g bΩ hg δ t htm htd htδ
    refine (zeroAt_iff.1 ⟨_, Ideal.mul_mem_left _ u hz, key.symm⟩).2 hU'
  · have hs := GlobalTheory.T.span_logDer_germs' E H Dw l Xo c TF Z x U hU hxU b δ hδR hr
    exact ⟨_, hu.mul (isUnit_det_of_span_eq_top c.F _ g bΩ hg δ hs), key.symm⟩

end GlobalTheory.LogKSDiv
end
end
end
