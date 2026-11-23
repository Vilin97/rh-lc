module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.PAdicSplitting.InfLifts
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CharpolyFromTrace.GoodLiftCHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CharpolyFromTrace.IneNorm
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.UnrField
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.NumberField
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.InflMatch
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.TypeOfLblHolds
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PStableOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PSuppIne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeRhamDescends
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JumpsDescend
import Mathlib.Tactic.Linter.Style
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RestrictsSelf
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
public import Development.AutomorphicArithmetic.Foundations.Convolution.Cbcc
public import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalGlobalCompatibility.TemperedLocalGlobal.WeilGroupRestriction.NotRealComplex
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.PAdicSplitting.PMixedOf
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InePolLpTwOfMemIne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupercuspidalSupportTwistNuCharacters
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ArtEx
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.PAdicSplitting.PToTor
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsModelOfMem
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GaloisRestrictionWdCompatible
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RestrictsLpDimMono0CharPol
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RestrictsWdPst
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsBridge
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.RecTExists

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.Closed

section

@[expose] public section

namespace UpperTheory.Gal.InertialTypesAlt

theorem suppBC_outright : SuppBC := suppBC_holds L.inflMatch

end UpperTheory.Gal.InertialTypesAlt
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.PAdicSplitting.PDrDesc

section

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL GlobalTheory.DeRhamOfPlainTorus ValuativeRel
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.ToralGalois.R2

theorem UpperTheory.Gal.ToralGalois.R2.drDesc :
    DRDesc := by
  intro E Ω _ _ _ _ _ _ l _ ι n π r hr w hall P AI hT A hA O _ _ _ Bw hj
  obtain ⟨X, PM, u, h', hinf, hcl⟩ := hall A hA
  obtain ⟨O', _, _, _, Bw', hj', hjj, hdesc⟩ :=
    GlobalTheory.DRDescent.deRham_descends E X.K Ω A w u hA h' l P AI hT n r hr O Bw hj
  obtain ⟨hdR, hjump⟩ := hcl P AI hT A h' O' Bw' hj'
  refine ⟨hdesc hdR, ?_⟩
  intro τ LL' τ' hind J hJ
  obtain ⟨φ, hφ⟩ := IntermediateField.exists_algHom_of_splits
    (fun s : Om l => ⟨Algebra.IsIntegral.isIntegral s, IsAlgClosed.splits _⟩)
    ((IntermediateField.val LL'.1).comp τ')
  have hφx : ∀ x : E, φ (Bw.j (algebraMap E Ω x)) = τ x := by
    intro x
    have := congrArg (fun f => f ⟨Bw.j (algebraMap E Ω x), Bw.j_E x⟩) hφ
    simp only [AlgHom.comp_apply, IntermediateField.val_mk] at this
    rw [this, hind x]
    rfl
  let LL'' : FinExt l := ⟨Bw'.Kw.1.map φ, inferInstance⟩
  let τ'' : ↥Bw'.Kw.1 →ₐ[ℚ_[l]] ↥LL''.1 := (IntermediateField.equivMap Bw'.Kw.1 φ).toAlgHom
  let τL : X.K →+* Om l := φ.toRingHom.comp (Bw'.j.comp (algebraMap X.K Ω))
  have hτL : τL.comp (algebraMap E X.K) = τ := by
    ext x
    show φ (Bw'.j (algebraMap X.K Ω (algebraMap E X.K x))) = τ x
    rw [← IsScalarTower.algebraMap_apply E X.K Ω, hjj, hφx]
  have hind' : IsInduced Bw' τL τ'' := fun x => rfl
  have hJ' : J.map (fun n : ℤ => (n : ℂ)) =
      ((CG.mk PM).infChar (ι.toRingHom.comp τL)).map (fun z => ((n : ℂ) - 1) / 2 - z) := by
    rw [hinf, RingHom.comp_assoc, hτL, hJ]
  exact GlobalTheory.JumpsDescend.jumps_descend E X.K Ω A w u hA h' l P AI hT n r hr O Bw O' Bw' hj hj' hjj τ τL hτL J
    (hjump τL LL'' τ'' hind' J hJ')
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.PAdicSplitting.PInfLifts

section

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL GlobalTheory.DeRhamOfPlainTorus ValuativeRel
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.ToralGalois.R2

theorem UpperTheory.Gal.ToralGalois.R2.infLifts :
    InfStep → InfLifts := by
  intro hS E Ω _ _ _ _ _ _ n hn π Y hY
  induction hY with
  | refl =>
    intro τ
    exact congrArg (CG.mk π).infChar (RingHom.comp_id τ).symm
  | @tail Y Z _ hs ih =>
    intro τ
    obtain ⟨alg, tow, hG, hP, hW⟩ := hs
    have hcomp : (algebraMap Y.K Z.K).comp (algebraMap E Y.K) = algebraMap E Z.K := by
      ext x
      apply (algebraMap Z.K Ω).injective
      rw [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply Y.K Z.K Ω,
        ← IsScalarTower.algebraMap_apply E Y.K Ω, ← IsScalarTower.algebraMap_apply E Z.K Ω]
    rw [hS Y.K Z.K hP n hn Y.π Z.π hW τ, ih (τ.comp (algebraMap Y.K Z.K)), RingHom.comp_assoc, hcomp]
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteOrderTwists

section

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RoadU.FinTwist

open GlobalTheory.ContraPair GlobalTheory.HeightCounting.Blocks

end GlobalTheory.RoadU.FinTwist

namespace GlobalTheory.RoadU.FinTwist

open GlobalTheory.ContraPair GlobalTheory.HeightCounting.Blocks

theorem isAlg_zero {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] {κ : HChar K} {m : ℕ} (hm : 0 < m)
    (h : κ ^ m = 1) : κ.IsAlg 0 := fun k => isAlgPos_zero_of_orderDvd hm h k fun φ => by
  have h := IsTotallyComplex.complexEmbedding_not_isReal (Complex.ofRealHom.comp φ)
  refine absurd ?_ h
  rw [ComplexEmbedding.isReal_iff]
  ext x
  simp

theorem infChar_twist {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] {n : ℕ} (P : CuspSub K n) {κ : HChar K}
    (hκ : κ.IsAlg 0) (τ : K →+* ℂ) : (CG.mk (P.twist κ)).infChar τ = (CG.mk P).infChar τ := by
  have e := ((ParLaws.hasInfChar_infChar (CG.mk P) τ).twist κ).infChar_eq
  rw [CG.twist_mk] at e
  rw [e, (InfType.expo_of_infType K κ).1 0 hκ τ]
  simp

end GlobalTheory.RoadU.FinTwist
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.PAdicSplitting.PInfStep

section

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL GlobalTheory.DeRhamOfPlainTorus ValuativeRel
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.ToralGalois.R2

theorem UpperTheory.Gal.ToralGalois.R2.infStep :
    UpperTheory.Gal.InertialTypesAlt.StableOf → InfStep := by
  intro hS K M _ _ _ _ _ _ _ _ hp n hn π P hw τ
  obtain ⟨hconj, -⟩ := hS K M hp n hn π P hw
  have hK : IsTotallyComplex K := inferInstance
  obtain ⟨-, hD, hF⟩ := UpperTheory.ConvolutionTheory.cbcc K M hp hK n hn
  obtain ⟨Q, hQw, hQinf, -⟩ := hD (.cx P) hconj
  cases Q with
  | re Q => exact (PositivityTheory.Pf1.CLGD.K.LKW.not_real_complex K inferInstance hK).elim
  | cx π₁ =>
    obtain ⟨η, hη, hi⟩ := (hF (.cx π) (.cx P) hconj hw).2 (.cx π₁) hQw
    have hP := GlobalTheory.CuspRep.ParLaws.hasInfChar_infChar (CG.mk P) τ
    have h2 : π₁.HasInfChar (τ.comp (algebraMap K M)) ((CG.mk P).infChar τ) := hQinf τ _ hP
    have h3 : (CG.mk π₁).infChar (τ.comp (algebraMap K M)) = (CG.mk P).infChar τ :=
      CG.HasInfChar.infChar_eq h2
    have h4 : CG.mk (π.twist η) = CG.mk π₁ := Quotient.sound hi
    have h5 : (CG.mk (π.twist η)).infChar (τ.comp (algebraMap K M)) =
        (CG.mk π).infChar (τ.comp (algebraMap K M)) := by
      rcases hη with rfl | hη
      · exact GlobalTheory.RoadU.FinTwist.infChar_twist π
          (GlobalTheory.RoadU.FinTwist.isAlg_zero (m := 1) one_pos (pow_one _)) _
      · exact GlobalTheory.RoadU.FinTwist.infChar_twist π
          (GlobalTheory.RoadU.FinTwist.isAlg_zero hp.pos hη.2.1) _
    rw [← h3, ← h4, h5]
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.PAdicSplitting.PRecChars

section

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL GlobalTheory.DeRhamOfPlainTorus ValuativeRel
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.ToralGalois.R2

theorem UpperTheory.Gal.ToralGalois.R2.recChars :
    UpperTheory.Gal.InertialTypesAlt.SuppIne → RecChars := by
  intro hSI M Ω _ _ _ _ _ A u h n T ξ hξ hsup
  haveI : CharZero (u.adicCompletion M) := charZero_of_injective_algebraMap (algebraMap M _).injective
  have hsupx : HasSupport (IrrGL.of T.ρ T.smooth T.irred).rep (chars ξ hξ) :=
    hsup.of_equiv (IrrGL.equivOf T.ρ T.smooth T.irred)
  have hnu := GlobalTheory.RoadU.TwistSupp.supp_nu_chars (u.adicCompletion M) (IrrGL.of T.ρ T.smooth T.irred) n ξ
    (fun j => ξ j * absPow _ (((1 - (n : ℝ)) / 2 : ℝ) : ℂ))
    hξ (fun j => (hξ j).mul (GlobalTheory.LocGL.isSmoothChar_absPow _)) (((1 - (n : ℝ)) / 2 : ℝ) : ℂ) (fun _ => rfl)
  refine ⟨fun hun => ⟨_, hnu.1.1 hsupx, fun y hy => ?_, hnu.2.1 hun⟩, fun rc hrc a ha t => ?_⟩
  · obtain ⟨j, -, rfl⟩ := Multiset.mem_map.1 hy
    rfl
  · have hSI' := hSI M Ω A u h rc hrc _ _ hsupx t
    obtain ⟨a₀, ha₀, L⟩ := hrc
    obtain rfl : a₀ = a := (UpperTheory.Zero.LLC.artEx M Ω A u h).unique ha₀ ha
    have e : algNorm T = (IrrGL.of T.ρ T.smooth T.irred).nu (((1 - (n : ℝ)) / 2 : ℝ) : ℂ) := rfl
    have h1 : ∀ j, (rc (IrrGL.ofChar (ξ j) (hξ j))).inePol (t : G M Ω) = X - C ((ξ j (a₀ (ineIncl h t)) : ℂˣ) : ℂ) := by
      intro j
      rw [WD.inePol_of_mem_Ine _ t.2, L.one, WD.lpOfChar, WD.charPol_mk, WDRep.ofChars_ρ, charpoly_diagEnd]
      simp
    rw [← WD.inePol_of_mem_Ine _ t.2, e, L.nu, GlobalTheory.RoadU.DepthZeroRec.inePol_lpTw_of_mem_Ine _ _ t.2, hSI', chars,
      Multiset.map_map]
    exact congrArg Multiset.prod (Multiset.map_congr rfl fun j _ => h1 j)
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.PAdicSplitting.R2g

section

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL GlobalTheory.DeRhamOfPlainTorus ValuativeRel
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.ToralGalois.R2

theorem UpperTheory.Gal.ToralGalois.R2.r2g :
    MixedOf → ToTor → DRDesc → UpperTheory.Zero.LLC.RecTExists → GlobalTheory.DeRhamOfPlainTorus.R1 → LocalGlobalCompatAtIwahoriFixedPlaces := by
  intro hMix hTor hDR hRec hR1 E Ω _ _ _ _ _ _ l _ ι n hn π χ hπ r hr w σ hσ hfix hcase A h rc hrc hm0
  rcases hcase with hpt | ⟨hQ, hap⟩
  · obtain ⟨haway, habove⟩ := hR1 E Ω l ι n hn π χ hπ r hr w σ hσ hpt
    refine ⟨fun hl => ?_, fun hl => ?_⟩
    · obtain ⟨hm, he⟩ := haway hl A h
      exact ⟨hm, fun t => by rw [he rc hrc]⟩
    · obtain ⟨hd, hb⟩ := habove hl
      refine ⟨hd, fun Q AI hT O _ _ _ Bw hj => ?_⟩
      obtain ⟨h1, h2, h3⟩ := hb Q AI hT A h O Bw hj
      exact ⟨h1, h2, fun t => h3 rc hrc _⟩
  · have hmix := hMix E Ω n π w σ hσ hfix hap A h rc hrc hm0
    obtain ⟨X, P, χ', u, h', T, rc', hP, hW, hinf, hTc, hPT, hrc', hine⟩ :=
      hTor E Ω l ι n hn π χ hπ r hr w σ hσ hQ hmix A h rc hrc
    obtain ⟨haway, habove⟩ := hR1 X.K Ω l ι n hn P χ' hP (resTo X.K r) hW u T hTc hPT
    refine ⟨fun hl => ?_, fun hl => ?_⟩
    · have hl' : ((l : ℕ) : 𝓞 X.K) ∉ u.asIdeal := by
        intro hm
        apply hl
        rw [← h]
        rw [← h'] at hm
        simpa using hm
      obtain ⟨hm', he⟩ := haway hl' A h'
      have hres := GlobalTheory.AboveL.wdOf_restricts E X.K Ω A w u h h' l ι n r hl hl' hr.1
      obtain ⟨-, hmono, hcp⟩ := GlobalTheory.AboveL.restricts_lpDim_mono0_charPol E X.K Ω A w u h h' _ _ hres
      refine ⟨hmono.mp hm', fun t => ?_⟩
      obtain ⟨t', hz, hc⟩ := hine t
      rw [← hcp (ineIncl h t) (ineIncl h' t') (fun z => by simpa [coe_ineIncl] using hz z), he rc' hrc', hc]
    · have hl' : ((l : ℕ) : 𝓞 X.K) ∈ u.asIdeal := by
        rw [← h] at hl
        rw [← h']
        simpa using hl
      obtain ⟨-, hb⟩ := habove hl'
      refine ⟨?_, fun Q AI hT O _ _ _ Bw hj => ?_⟩
      · refine hDR E Ω l ι n π r hr.1 w fun A' hA' => ?_
        obtain ⟨rc₁, hrc₁⟩ := hRec E Ω A' w hA'
        obtain ⟨X₁, P₁, χ₁, u₁, h₁, T₁, rc₁', hP₁, hW₁, hinf₁, hTc₁, hPT₁, -, -⟩ :=
          hTor E Ω l ι n hn π χ hπ r hr w σ hσ hQ hmix A' hA' rc₁ hrc₁
        have hl₁ : ((l : ℕ) : 𝓞 X₁.K) ∈ u₁.asIdeal := by
          rw [← hA'] at hl
          rw [← h₁]
          simpa using hl
        exact ⟨X₁, P₁, u₁, h₁, hinf₁,
          ((hR1 X₁.K Ω l ι n hn P₁ χ₁ hP₁ (resTo X₁.K r) hW₁ u₁ T₁ hTc₁ hPT₁).2 hl₁).1⟩
      · obtain ⟨LL₀, Bw₀, hjj₀, -, -⟩ := GlobalTheory.AboveLRes.exists_bridge (L := X.K) Bw hj Bw.LL
        have hj₀ : GlobalTheory.Pst.Induces Bw₀ := fun x => by rw [hjj₀]; exact hj x
        have hp₀ := (hb Q AI hT A h' _ Bw₀ hj₀).1
        have hpst : IsPstAt Q Bw (r.comp (Dec (F := E) A).subtype) :=
          GlobalTheory.AboveLRes.isPstAt_of_resTo E X.K Ω A l Q AI hT n r hr.1 O _ Bw Bw₀ hj hj₀ hp₀
        obtain ⟨O', _, _, _, Bw', hj', -, hres⟩ :=
          GlobalTheory.AboveLRes.wdAt_resTo E X.K Ω A w u h h' l ι Q AI hT n r O Bw hj hpst
        obtain ⟨-, hmono, hcp⟩ := GlobalTheory.AboveL.restricts_lpDim_mono0_charPol E X.K Ω A w u h h' _ _ hres
        obtain ⟨-, hm', hc'⟩ := hb Q AI hT A h' O' Bw' hj'
        refine ⟨hpst, hmono.mp hm', fun t => ?_⟩
        obtain ⟨t', hz, hc⟩ := hine t
        rw [← hcp (ineIncl h t) (ineIncl h' t') (fun z => by simpa [coe_ineIncl] using hz z), hc' rc' hrc', hc]
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.PAdicSplitting.LocalGlobalCompatAtIwahoriFixedOfUnlinked

section

@[expose] public section

namespace UpperTheory.Gal.ToralGalois.R2

theorem toTor_holds : ToTor :=
  toTor UpperTheory.Gal.InertialTypesAlt.suppBC_outright UpperTheory.Gal.UnramifiedFromSplittingCriterion.unrField_holds UpperTheory.Gal.NearKilling.allLift_holds UpperTheory.Gal.NearKilling.ineNorm
    (infLifts (infStep UpperTheory.Gal.InertialTypesAlt.stableOf)) (recChars UpperTheory.Gal.InertialTypesAlt.suppIne) UpperTheory.Zero.LLC.recTExists

theorem localGlobalCompatAtIwahoriFixed_of_unlinked : GlobalTheory.DeRhamOfPlainTorus.R1 → LocalGlobalCompatAtIwahoriFixedPlaces := r2g mixedOf toTor_holds drDesc UpperTheory.Zero.LLC.recTExists

end UpperTheory.Gal.ToralGalois.R2
end
end
