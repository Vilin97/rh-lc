module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBaseFrame
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitMkOfFormallyUnramified
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfComp
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsChartOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBaseFrame
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
public import Mathlib.RingTheory.Kaehler.Basic
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoordinatesExtendingRegularParameters
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafEqSpanOnBasicOpensOfStalkPrincipal
import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogDerivationDetEqUnitMulProdNormalCrossingsStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FlatBCSec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAffineOpenFinitePresentationStalkKaehlerFr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SncStalkRegularParametersFromAffineOpenStatement
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenTopFormFrameOfStalkKaehlerBasis

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

namespace GlobalTheory.FrameSpread

open GlobalTheory.TopForm

theorem exists_basicOpen_isFrame_dOn : ∀ (k : Type) [Field k] (X : Scheme.{0}) (p : X ⟶ Sp k) (n : ℕ) [SmoothOfRelativeDimension n p] (U : X.affineOpens) (x₀ : X) (hx : x₀ ∈ U.1) (x : Fin n → Γ(X, U.1)), (letI := ((X.presheaf.germ U.1 x₀ hx).hom.comp (algX p U.1)).toAlgebra; ∃ bs : Module.Basis (Fin n) (X.presheaf.stalk x₀) Ω[X.presheaf.stalk x₀⁄k], ∀ i, bs i = KaehlerDifferential.D k (X.presheaf.stalk x₀) ((X.presheaf.germ U.1 x₀ hx).hom (x i))) → ∃ s : Γ(X, U.1), x₀ ∈ X.basicOpen s ∧ GlobalTheory.TopForm.IsFrame (GlobalTheory.TopForm.dOn p fun i => resG X (X.basicOpen_le s) (x i)) := by
  intro k _ X p n _ U x₀ hx x hbs
  obtain ⟨V, ω, hxV, hω⟩ := TopForm.exists_isFrame p n x₀
  obtain ⟨s, hsV, hxs⟩ := U.2.exists_basicOpen_le ⟨x₀, hxV⟩ hx
  have hWU : X.basicOpen s ≤ U.1 := X.basicOpen_le s
  have hWaff : IsAffineOpen (X.basicOpen s) := U.2.basicOpen s
  have hωW := hω.res hWaff hsV
  set η : FormsOn p n (X.basicOpen s) := TopForm.dOn p (fun i => resG X hWU (x i)) with hη
  set J : Γ(X, X.basicOpen s) := hωW.gen.repr η with hJdef
  have hJ : J • TopForm.resForm hsV ω = η := hωW.gen.repr_smul η
  obtain ⟨bs, hbs⟩ := hbs
  set ρ : Γ(X, X.basicOpen s) →+* X.presheaf.stalk x₀ := (X.presheaf.germ (X.basicOpen s) x₀ hxs).hom with hρ
  have hgerm : ∀ a : Γ(X, U.1), ρ (resG X hWU a) = (X.presheaf.germ U.1 x₀ hx).hom a := fun a => by
    have := TopCat.Presheaf.germ_res X.presheaf (homOfLE hWU) x₀ hxs
    exact congrArg (fun φ => (ConcreteCategory.hom φ) a) this
  have hρα : ρ.comp (algX p (X.basicOpen s)) = (X.presheaf.germ U.1 x₀ hx).hom.comp (algX p U.1) := by
    rw [← resG_comp_algX p hWU]
    ext a
    exact hgerm _
  have hfe : letI := ρ.toAlgebra; Algebra.FormallyEtale Γ(X, X.basicOpen s) (X.presheaf.stalk x₀) := by
    letI := ρ.toAlgebra
    haveI := hWaff.isLocalization_stalk ⟨x₀, hxs⟩
    exact Algebra.FormallyEtale.of_isLocalization (hWaff.primeIdealOf ⟨x₀, hxs⟩).asIdeal.primeCompl
  have h1 : IsFreeGen (X.presheaf.stalk x₀) (TopForm.formMap n ρ hρα (TopForm.resForm hsV ω)) := by
    letI := (algX p (X.basicOpen s)).toAlgebra
    letI := ((X.presheaf.germ U.1 x₀ hx).hom.comp (algX p U.1)).toAlgebra
    letI := ρ.toAlgebra
    haveI : IsScalarTower k Γ(X, X.basicOpen s) (X.presheaf.stalk x₀) :=
      IsScalarTower.of_algebraMap_eq' hρα.symm
    haveI : Algebra.FormallyEtale Γ(X, X.basicOpen s) (X.presheaf.stalk x₀) := hfe
    exact hωW.gen.of_isBaseChange (isBaseChange_exteriorPower
      (KaehlerDifferential.isBaseChange_of_formallyEtale k Γ(X, X.basicOpen s) (X.presheaf.stalk x₀)) n)
  have h2 : IsFreeGen (X.presheaf.stalk x₀)
      (dForm ((X.presheaf.germ U.1 x₀ hx).hom.comp (algX p U.1))
        (fun i => (X.presheaf.germ U.1 x₀ hx).hom (x i))) :=
    isFreeGen_dForm _ bs hbs
  have h3 : TopForm.formMap n ρ hρα η = ρ J • TopForm.formMap n ρ hρα (TopForm.resForm hsV ω) := by
    rw [← hJ, map_smulₛₗ]
  have h4 : TopForm.formMap n ρ hρα η = dForm ((X.presheaf.germ U.1 x₀ hx).hom.comp (algX p U.1))
      (fun i => (X.presheaf.germ U.1 x₀ hx).hom (x i)) := by
    rw [hη, dOn, formMap_dForm]
    simp only [hgerm]
  have hu : IsUnit (ρ J) := h1.smul_iff.1 (h3 ▸ h4 ▸ h2)
  have hxJ : x₀ ∈ X.basicOpen J := (X.mem_basicOpen J x₀ hxs).2 hu
  obtain ⟨t, htJ, hxt⟩ := U.2.exists_basicOpen_le ⟨x₀, hxJ⟩ hx
  refine ⟨t, hxt, ?_⟩
  have hJW : X.basicOpen J ≤ X.basicOpen s := X.basicOpen_le J
  have hte : X.basicOpen t ≤ X.basicOpen s := htJ.trans hJW
  have hframe := hωW.res (U.2.basicOpen t) hte
  have e : TopForm.dOn p (fun i => resG X (X.basicOpen_le t) (x i)) =
      resG X hte J • TopForm.resForm hte (TopForm.resForm hsV ω) := by
    rw [← resForm_smul, hJ, hη, resForm_dOn]
    simp only [resG_resG]
  rw [e]
  refine ⟨U.2.basicOpen t, hframe.gen.smul_iff.2 ?_⟩
  have hu' : IsUnit (resG X hJW J) := X.toRingedSpace.isUnit_res_basicOpen J
  have := hu'.map (resG X htJ)
  rwa [resG_resG] at this

end GlobalTheory.FrameSpread
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenTopFormFrameOfStalkKaehlerBasisStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

theorem _root_.GlobalTheory.T.exists_basicOpen_topFormFrame_of_stalkKaehlerBasis : ∀ (k : Type) [Field k] (X : Scheme.{0}) (p : X ⟶ Sp k) (n : ℕ) [SmoothOfRelativeDimension n p] (U : X.affineOpens) (x₀ : X) (hx : x₀ ∈ U.1) (x : Fin n → Γ(X, U.1)), (letI := ((X.presheaf.germ U.1 x₀ hx).hom.comp (algX p U.1)).toAlgebra; ∃ bs : Module.Basis (Fin n) (X.presheaf.stalk x₀) Ω[X.presheaf.stalk x₀⁄k], ∀ i, bs i = KaehlerDifferential.D k (X.presheaf.stalk x₀) ((X.presheaf.germ U.1 x₀ hx).hom (x i))) → ∃ s : Γ(X, U.1), x₀ ∈ X.basicOpen s ∧ GlobalTheory.TopForm.IsFrame (GlobalTheory.TopForm.dOn p fun i => resG X (X.basicOpen_le s) (x i)) := by
  first | exact @GlobalTheory.FrameSpread.exists_basicOpen_isFrame_dOn | exact GlobalTheory.FrameSpread.exists_basicOpen_isFrame_dOn | (intros; apply GlobalTheory.FrameSpread.exists_basicOpen_isFrame_dOn <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoordinatesExtendingRegularParametersStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

theorem _root_.GlobalTheory.T.exists_coordinates_extending_regular_parameters : ∀ (F A R : Type) [Field F] [CharZero F] [CommRing A] [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsRegularLocalRing R] [Algebra F A] [Algebra A R] [Algebra F R] [IsScalarTower F A R] (P : Ideal A) [P.IsPrime] [IsLocalization.AtPrime R P] (n : ℕ) [Module.Free R Ω[R⁄F]] [Module.Finite R Ω[R⁄F]], Module.finrank R Ω[R⁄F] = n → ∀ (m : ℕ) (a : Fin m → A), ReciprocityTheory.AnForm.R.FinalTheorems.Rsp R m (fun i => algebraMap A R (a i)) → ∃ (x : Fin n → A) (e : Fin m ↪ Fin n), (∀ j, x (e j) = a j) ∧ ∃ bs : Module.Basis (Fin n) R Ω[R⁄F], ∀ i, bs i = KaehlerDifferential.D F R (algebraMap A R (x i)) := by
  first | exact @GlobalTheory.exists_coords_extending_regularParams | exact GlobalTheory.exists_coords_extending_regularParams | (intros; apply GlobalTheory.exists_coords_extending_regularParams <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafEqSpanOnBasicOpensOfStalkPrincipalStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

theorem _root_.GlobalTheory.T.idealSheaf_eq_span_on_basicOpens_of_stalk_principal : ∀ (X : Scheme.{0}) (I : X.IdealSheafData) (U : X.affineOpens) (x₀ : X) (hx : x₀ ∈ U.1) (d : Γ(X, U.1)), IsNoetherianRing Γ(X, U.1) → (I.ideal U).map (X.presheaf.germ U.1 x₀ hx).hom = Ideal.span {(X.presheaf.germ U.1 x₀ hx).hom d} → ∃ s : Γ(X, U.1), x₀ ∈ X.basicOpen s ∧ ∀ t : Γ(X, U.1), X.basicOpen t ≤ X.basicOpen s → I.ideal (X.affineBasicOpen t) = Ideal.span {resG X (X.basicOpen_le t) d} := by
  first | exact @GlobalTheory.IdealSpread.ideal_eq_span_of_germ | exact GlobalTheory.IdealSpread.ideal_eq_span_of_germ | (intros; apply GlobalTheory.IdealSpread.ideal_eq_span_of_germ <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAffineOpenFinitePresentationStalkKaehlerFrStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

theorem _root_.GlobalTheory.T.smooth_affineOpen_finitePresentation_stalkKaehler_free_rank : ∀ (k : Type) [Field k] (X : Scheme.{0}) (p : X ⟶ Sp k) (n : ℕ) [SmoothOfRelativeDimension n p] (U : X.affineOpens) (x : X) (hx : x ∈ U.1), letI := (algX p U.1).toAlgebra; letI := ((X.presheaf.germ U.1 x hx).hom.comp (algX p U.1)).toAlgebra; Algebra.FinitePresentation k Γ(X, U.1) ∧ Module.Free (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄k] ∧ Module.Finite (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄k] ∧ Module.finrank (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄k] = n := by
  first | exact @GlobalTheory.SmoothStalk.smooth_stalk | exact GlobalTheory.SmoothStalk.smooth_stalk | (intros; apply GlobalTheory.SmoothStalk.smooth_stalk <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoordinatesLogVectorFieldsDeterminant

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option autoImplicit false

theorem GlobalTheory.LogPole.exists_coord_logDet : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (U : TF.Y.X.affineOpens) (b : Module.Basis (Fin Dw.dim) Γ(TF.Y.X, U.1) (LogKS.logDer TF.Y.s (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl) U)) (x₀ : TF.Y.X), x₀ ∈ U.1 → ∃ (x : Fin Dw.dim → Γ(TF.Y.X, U.1)) (U' : TF.Y.X.affineOpens) (hU' : U'.1 ≤ U.1), x₀ ∈ U'.1 ∧ TopForm.IsFrame (TopForm.dOn TF.Y.s fun i => resG TF.Y.X hU' (x i)) ∧ (LogKS.boundary TF.Y).ideal U' = Ideal.span {resG TF.Y.X hU' (logDet (fun j => (b j).1) x)} := by
  intro E _ _ _ H Dw l Xo c TF U b x₀ hx₀
  classical
  have hres : ∀ (V W : TF.Y.X.Opens) (hW : IsAffineOpen W) (h : W ≤ V) (hVU : V ≤ U.1)
      (f : Fin Dw.dim → Γ(TF.Y.X, U.1)), TopForm.IsFrame (TopForm.dOn TF.Y.s fun i => resG TF.Y.X hVU (f i)) →
      TopForm.IsFrame (TopForm.dOn TF.Y.s fun i => resG TF.Y.X (h.trans hVU) (f i)) := by
    intro V W hW h hVU f hf
    have h' := hf.res hW h
    rw [TopForm.resForm_dOn] at h'
    simpa only [LB.resG_resG] using h'
  obtain ⟨hreg, m, a, J, hRsp, hIa⟩ := GlobalTheory.T.snc_stalk_regularParameters_from_affineOpen TF.Y.X (LogKS.boundary TF.Y) TF.snc U x₀ hx₀
  haveI := TF.smooth
  obtain ⟨hfp, hfree, hfin, hrank⟩ := GlobalTheory.T.smooth_affineOpen_finitePresentation_stalkKaehler_free_rank c.F TF.Y.X TF.Y.s Dw.dim U x₀ hx₀
  letI : Algebra c.F Γ(TF.Y.X, U.1) := (algX TF.Y.s U.1).toAlgebra
  letI : Algebra Γ(TF.Y.X, U.1) (TF.Y.X.presheaf.stalk x₀) :=
    TopCat.Presheaf.algebra_section_stalk TF.Y.X.presheaf ⟨x₀, hx₀⟩
  letI : Algebra c.F (TF.Y.X.presheaf.stalk x₀) :=
    ((TF.Y.X.presheaf.germ U.1 x₀ hx₀).hom.comp (algX TF.Y.s U.1)).toAlgebra
  haveI : IsScalarTower c.F Γ(TF.Y.X, U.1) (TF.Y.X.presheaf.stalk x₀) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI hloc := U.2.isLocalization_stalk ⟨x₀, hx₀⟩
  haveI : IsNoetherianRing Γ(TF.Y.X, U.1) := Algebra.FiniteType.isNoetherianRing c.F _
  haveI : IsNoetherianRing (TF.Y.X.presheaf.stalk x₀) :=
    IsLocalization.isNoetherianRing (U.2.primeIdealOf ⟨x₀, hx₀⟩).asIdeal.primeCompl _ inferInstance
  have h3 := GlobalTheory.T.exists_coordinates_extending_regular_parameters c.F Γ(TF.Y.X, U.1) (TF.Y.X.presheaf.stalk x₀)
    (U.2.primeIdealOf ⟨x₀, hx₀⟩).asIdeal Dw.dim hrank m a hRsp
  obtain ⟨x, e, hxe, bs, hbs⟩ := h3
  have hxe' : (fun j => x (e j)) = a := funext hxe
  have hI : ((LogKS.boundary TF.Y).ideal U).map (algebraMap Γ(TF.Y.X, U.1) (TF.Y.X.presheaf.stalk x₀)) =
      Ideal.span {algebraMap Γ(TF.Y.X, U.1) (TF.Y.X.presheaf.stalk x₀) (∏ j ∈ J, x (e j))} := by
    simp only [hxe]; exact hIa
  have hspan : ∀ D : Derivation ℤ Γ(TF.Y.X, U.1) Γ(TF.Y.X, U.1),
      (∀ c', D (algebraMap c.F Γ(TF.Y.X, U.1) c') = 0) → (∀ f ∈ (LogKS.boundary TF.Y).ideal U, D f ∈ (LogKS.boundary TF.Y).ideal U) →
      ∃ cf : Fin Dw.dim → Γ(TF.Y.X, U.1), D = ∑ j, cf j • (b j).1 := by
    intro D h0 h1
    let D' : LogKS.logDer TF.Y.s (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl) U := ⟨D, h0, h1⟩
    refine ⟨b.repr D', ?_⟩
    have := congrArg Subtype.val (b.sum_repr D')
    rw [Submodule.coe_sum] at this
    exact this.symm
  have h4 := GlobalTheory.T.logDerivation_det_eq_unit_mul_prod_normalCrossings c.F Γ(TF.Y.X, U.1) (TF.Y.X.presheaf.stalk x₀) (U.2.primeIdealOf ⟨x₀, hx₀⟩).asIdeal
    Dw.dim m x e J (by simp only [hxe]; exact hRsp) ⟨bs, hbs⟩ ((LogKS.boundary TF.Y).ideal U) hI
    (fun j => (b j).1) (fun j c' => (b j).2.1 c') (fun j => (b j).2.2) hspan
  obtain ⟨u, hu⟩ := h4
  have hd : ((LogKS.boundary TF.Y).ideal U).map (TF.Y.X.presheaf.germ U.1 x₀ hx₀).hom =
      Ideal.span {(TF.Y.X.presheaf.germ U.1 x₀ hx₀).hom (logDet (fun j => (b j).1) x)} := by
    change ((LogKS.boundary TF.Y).ideal U).map (algebraMap Γ(TF.Y.X, U.1) (TF.Y.X.presheaf.stalk x₀)) =
      Ideal.span {algebraMap Γ(TF.Y.X, U.1) (TF.Y.X.presheaf.stalk x₀) (logDet (fun j => (b j).1) x)}
    exact hI.trans ((Ideal.span_singleton_mul_left_unit u.isUnit _).symm.trans (congrArg (fun y => Ideal.span {y}) hu.symm))
  have h5 := GlobalTheory.T.idealSheaf_eq_span_on_basicOpens_of_stalk_principal TF.Y.X (LogKS.boundary TF.Y) U x₀ hx₀ _ inferInstance hd
  obtain ⟨s₂, hs₂, hid⟩ := h5
  have h2 := GlobalTheory.T.exists_basicOpen_topFormFrame_of_stalkKaehlerBasis c.F TF.Y.X TF.Y.s Dw.dim U x₀ hx₀ x ⟨bs, hbs⟩
  obtain ⟨s₁, hs₁, hfr⟩ := h2
  have hle₁ : TF.Y.X.basicOpen (s₁ * s₂) ≤ TF.Y.X.basicOpen s₁ := by
    rw [Scheme.basicOpen_mul]; exact inf_le_left
  have hle₂ : TF.Y.X.basicOpen (s₁ * s₂) ≤ TF.Y.X.basicOpen s₂ := by
    rw [Scheme.basicOpen_mul]; exact inf_le_right
  refine ⟨x, TF.Y.X.affineBasicOpen (s₁ * s₂), TF.Y.X.basicOpen_le _, ?_, ?_, hid _ hle₂⟩
  · show x₀ ∈ TF.Y.X.basicOpen (s₁ * s₂)
    rw [Scheme.basicOpen_mul]; exact ⟨hs₁, hs₂⟩
  · exact hres _ _ (U.2.basicOpen (s₁ * s₂)) hle₁ _ x hfr
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoordinatesLogVectorFieldsDeterminantStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

theorem _root_.GlobalTheory.T.exists_coordinates_logVectorFields_determinant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (U : TF.Y.X.affineOpens) (b : Module.Basis (Fin Dw.dim) Γ(TF.Y.X, U.1) (LogKS.logDer TF.Y.s (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl) U)) (x₀ : TF.Y.X), x₀ ∈ U.1 → ∃ (x : Fin Dw.dim → Γ(TF.Y.X, U.1)) (U' : TF.Y.X.affineOpens) (hU' : U'.1 ≤ U.1), x₀ ∈ U'.1 ∧ TopForm.IsFrame (TopForm.dOn TF.Y.s fun i => resG TF.Y.X hU' (x i)) ∧ (LogKS.boundary TF.Y).ideal U' = Ideal.span {resG TF.Y.X hU' (logDet (fun j => (b j).1) x)} := by
  first | exact @GlobalTheory.LogPole.exists_coord_logDet | exact GlobalTheory.LogPole.exists_coord_logDet | (intros; apply GlobalTheory.LogPole.exists_coord_logDet <;> assumption)
end
end
