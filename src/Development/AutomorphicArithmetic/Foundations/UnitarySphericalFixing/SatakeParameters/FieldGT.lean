module

public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.AbsCentral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodIrrGLTransportAlongFieldIsoStatement
public import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceOverTransportRingIso
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsReadingLaws
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoeffRingsHaveRootsOfUnity
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import ReciprocityTheory.Automorphisms.InstMainA
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsTransport
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsTheRecOfIsRecLit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalCongruenceFixedVectorsNeBotTransportStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChevalleyUnits
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousRingEquivLocalFieldPreservesValuationStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLanglandsDataTransportLocalFieldIsoStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalArtinExistsHolds
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalArtinMapUniqueTransportPlaceIso
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalArtinMapUniqueTransportPlaceIsoStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceOverTransportRingIso
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceOverTransportRingIsoStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceOverTransportRingIsoSymmStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TransportIrrGLBijectiveDegreeCharZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TransportIrrGLBijectiveDegreeCharZeroStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TransportKeepsCuspidalTwistsCharacters
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TransportKeepsCuspidalTwistsCharactersStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlobalArtinReciprocityHolds
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.RecTUnique
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTameWDOfWdRel

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LocLanglands GlobalTheory.WeilDeligne GlobalTheory.LocGL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TameTransport

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
  {A : ValuationSubring Ω} {E' Ω' : Type} [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω']
  {A' : ValuationSubring Ω'} {φ : Ω ≃+* Ω'}

theorem val_lt_val_iff (hm : ∀ z, φ z ∈ A' ↔ z ∈ A) (a b : Ω) (hb : b ≠ 0) :
    A'.valuation (φ a) < A'.valuation (φ b) ↔ A.valuation a < A.valuation b := by
  have hb' : φ b ≠ 0 := (map_ne_zero φ).mpr hb
  have h1 : A'.valuation (φ b) ≠ 0 := by simpa using hb'
  have h2 : A.valuation b ≠ 0 := by simpa using hb
  have e1 : A'.valuation (φ a) < A'.valuation (φ b) ↔ A'.valuation (φ (a / b)) < 1 := by
    rw [map_div₀, map_div₀, div_lt_one₀ (zero_lt_iff.mpr h1)]
  have e2 : A.valuation a < A.valuation b ↔ A.valuation (a / b) < 1 := by
    rw [map_div₀, div_lt_one₀ (zero_lt_iff.mpr h2)]
  rw [e1, e2, GlobalTheory.WeilTransport.val_lt_one_iff hm]

theorem isWild_of_rel (hm : ∀ z, φ z ∈ A' ↔ z ∈ A) {σ : G E Ω} {σ' : G E' Ω'}
    (hrel : ∀ z, φ (σ z) = σ' (φ z)) (hσ : Formalism.MainNotions.BlochKatoReduction.IsWild A σ) : Formalism.MainNotions.BlochKatoReduction.IsWild A' σ' := by
  obtain ⟨⟨hdec, hin⟩, hw⟩ := hσ
  refine ⟨⟨(GlobalTheory.WeilTransport.mem_Dec_iff hm hrel).mpr hdec, fun x hx => ?_⟩, fun x hx => ?_⟩
  · obtain ⟨z, rfl⟩ := φ.surjective x
    rw [GlobalTheory.WeilTransport.val_le_one_iff hm] at hx
    rw [← hrel, ← map_sub, GlobalTheory.WeilTransport.val_lt_one_iff hm]
    exact hin z hx
  · obtain ⟨z, rfl⟩ := φ.surjective x
    have hz : z ≠ 0 := by rintro rfl; exact hx (map_zero φ)
    rw [← hrel, ← map_sub, val_lt_val_iff hm _ _ hz]
    exact hw z hz

end GlobalTheory.TameTransport
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceIsoCompatibleLocalLanglandsFour

section

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.LocLanglands.FieldCompat GlobalTheory.LocLanglands.TransportGL GlobalTheory.TheRecTransport

namespace GlobalTheory.LawsTTransport

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {E' Ω' : Type} [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω']
  {A' : ValuationSubring Ω'} {w' : HeightOneSpectrum (𝓞 E')} {h' : IsPlaceOver A' w'}

theorem eig_of_wdRel {φ : Ω ≃+* Ω'} {y : WD h} {y' : WD h'} (H : WDRel φ y y') {σ : Weil h} {σ' : Weil h'}
    (hσ : WeilRel φ σ σ') : y.eig σ = y'.eig σ' := by
  obtain ⟨n, b, b', e1, e2, -, hb⟩ := H
  rw [← e1, ← e2, WD.eig, WD.eig, WD.charPol_mk, WD.charPol_mk, hb σ _ hσ]

end GlobalTheory.LawsTTransport
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableHopfOrderSubgroupRestriction

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LocLanglands GlobalTheory.WeilDeligne GlobalTheory.LocGL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TypeLawTransport

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {E' Ω' : Type} [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω']
  {A' : ValuationSubring Ω'} {w' : HeightOneSpectrum (𝓞 E')} {h' : IsPlaceOver A' w'}
  {φ : Ω ≃+* Ω'} {j : E →+* E'} {i : w.adicCompletion E ≃+* w'.adicCompletion E'}

theorem monodromy_vanishing_iff_of_weil_deligne_rel {y : WD h} {y' : WD h'} (H : WDRel φ y y') : y.mono0 ↔ y'.mono0 := by
  obtain ⟨n, b, b', rfl, rfl, hN, -⟩ := H
  rw [WD.monodromyZero_ofWeilDeligneRepClass_iff, WD.monodromyZero_ofWeilDeligneRepClass_iff, hN]

theorem inePol_transport (P : PlaceIso A w A' w' φ j i) {y : WD h} {y' : WD h'} (H : WDRel φ y y')
    {σ : G E Ω} {σ' : G E' Ω'} (hr : ∀ z, φ (σ z) = σ' (φ z)) : y.inePol σ = y'.inePol σ' := by
  obtain ⟨c, -, -, hq, -⟩ := GlobalTheory.WeilTransport.weil_equiv E Ω A w h E' Ω' A' w' h' φ j i P
  have hmem : σ' ∈ Weil h' ↔ σ ∈ Weil h := by
    rw [mem_Weil, mem_Weil, hq]
    exact exists_congr fun a => exists_congr fun b => GlobalTheory.WeilTransport.actsAs_iff P.mem hr _ a b
  obtain ⟨n, b, b', rfl, rfl, -, hb⟩ := H
  by_cases hσ : σ ∈ Weil h
  · have hσ' := hmem.2 hσ
    rw [WD.inePol_of_mem _ hσ, WD.inePol_of_mem _ hσ', WD.charPol_mk, WD.charPol_mk, hb ⟨σ, hσ⟩ ⟨σ', hσ'⟩ hr]
  · have hσ' : σ' ∉ Weil h' := fun h1 => hσ (hmem.1 h1)
    rw [WD.inePol_of_not_mem _ hσ, WD.inePol_of_not_mem _ hσ']

end GlobalTheory.TypeLawTransport

end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.FieldGT

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.LocLanglands.FieldCompat GlobalTheory.LocLanglands.TransportGL GlobalTheory.TheRecTransport GlobalTheory.TypeLawTransport

namespace UpperTheory.One.M.FieldTr

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {E' Ω' : Type} [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω']
  {A' : ValuationSubring Ω'} {w' : HeightOneSpectrum (𝓞 E')} {h' : IsPlaceOver A' w'}
  {φ : Ω ≃+* Ω'} {j : E →+* E'} {i : w.adicCompletion E ≃+* w'.adicCompletion E'}

private theorem tame_fwd (P : PlaceIso A w A' w' φ j i) {y : WD h} {y' : WD h'} (hrel : WDRel φ y y')
    (hy : IsTameWD y) : IsTameWD y' := by
  obtain ⟨n, b, b', hb, hb', -, hρ⟩ := hrel
  obtain ⟨m, a, ha, hwild⟩ := hy
  obtain ⟨e, he, -⟩ := GlobalTheory.WeilDeligne.WD.mk_eq_mk.mp (ha.trans hb.symm)
  obtain ⟨c, hc, -⟩ := GlobalTheory.T.place_over_transport_ring_iso E Ω A w h E' Ω' A' w' h' φ j i P
  refine ⟨n, b', hb', fun σ' hσ' => ?_⟩
  have hr : WeilRel φ (c.symm σ') σ' := (hc (c.symm σ') σ').mpr (by simp)
  have hm : ∀ z, φ.symm z ∈ A ↔ z ∈ A' := fun z => by
    rw [← P.mem, RingEquiv.apply_symm_apply]
  have hσ : Formalism.MainNotions.BlochKatoReduction.IsWild A ((c.symm σ' : Weil h) : G E Ω) :=
    GlobalTheory.TameTransport.isWild_of_rel (φ := φ.symm) hm (fun z => φ.injective (by
      rw [RingEquiv.apply_symm_apply, hr, RingEquiv.apply_symm_apply])) hσ'
  rw [← hρ _ σ' hr]
  refine LinearMap.ext fun v => ?_
  obtain ⟨u, rfl⟩ := e.surjective v
  rw [← he, hwild _ hσ]
  rfl



private theorem typeLaw_fwd (P : PlaceIso A w A' w' φ j i) (rc : IrrGL (k := w.adicCompletion E) → WD h)
    (rc' : IrrGL (k := w'.adicCompletion E') → WD h') (hrel : ∀ x x', RepRel i x x' → WDRel φ (rc x) (rc' x'))
    (hT : UpperTheory.Zero.LLC.TypeLaw h rc) : UpperTheory.Zero.LLC.TypeLaw h' rc' := by
  intro E'' _ _ _ _ _ _ g _ w'' h'' ii hii n hn hg hnorm a'' ha'' K _ _ red hred hker θ hθ τ hτ hτc σ' hσ'
  letI iE : Algebra E E'' := ((algebraMap E' E'').comp j).toAlgebra
  letI iΩ : Algebra E'' Ω := ((φ.symm : Ω' →+* Ω).comp (algebraMap E'' Ω')).toAlgebra
  haveI : IsScalarTower E E'' Ω := IsScalarTower.of_algebraMap_eq fun x => by
    show algebraMap E Ω x = φ.symm (algebraMap E'' Ω' (algebraMap E' E'' (j x)))
    rw [← IsScalarTower.algebraMap_apply, ← P.ext, RingEquiv.symm_apply_apply]
  let ψ : Ω' ≃ₐ[E''] Ω := AlgEquiv.ofRingEquiv (f := φ.symm) fun _ => rfl
  haveI : Algebra.IsAlgebraic E'' Ω' := IsAlgClosure.isAlgebraic
  haveI : IsAlgClosure E'' Ω := ⟨IsAlgClosure.isAlgClosed E, ψ.isAlgebraic⟩
  have hm : ∀ z, φ.symm z ∈ A ↔ z ∈ A' := fun z => by
    rw [← P.mem, RingEquiv.apply_symm_apply]
  have h₃ : IsPlaceOver A w'' := fun x => by
    show A.valuation (φ.symm (algebraMap E'' Ω' (x : E''))) < 1 ↔ _
    rw [GlobalTheory.WeilTransport.val_lt_one_iff hm]
    exact h'' x
  haveI := charZero_compl w
  haveI := charZero_compl w'
  have hs : Continuous i.symm := (GlobalTheory.T.continuous_ringEquiv_localField_preserves_valuation _ _ i P.cont).1
  have hcont : Continuous (ii.trans i.symm) := hs.comp hii
  obtain ⟨T, hT1, -⟩ := GlobalTheory.transport_irrGL_bijective _ _ i.symm hs
  obtain ⟨σ₀, e, h2, he⟩ := exists_of_repRel σ' ((hT1 _ _).2 rfl)
  have hR' : RepRel i.symm (cls σ') (cls σ₀) := h2 ▸ (hT1 _ _).2 rfl
  have hR : RepRel i (cls σ₀) (cls σ') := repRel_symm hR'
  have W := hrel _ _ hR
  have hinf : GlobalTheory.SerSys.TameGen.Inflates (σ₀.ρ.comp (Matrix.GeneralLinearGroup.map (ii.trans i.symm).toRingHom)) τ := by
    obtain ⟨f, hf0, hf⟩ := hσ'
    refine ⟨e.toLinearMap ∘ₗ f, fun h0 => hf0 ?_, fun k v => ?_⟩
    · ext v
      have := congrArg (fun F => F v) h0
      simpa using this
    · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, MonoidHom.comp_apply] at hf ⊢
      rw [hf, he]
      rfl
  obtain ⟨a₃, ha₃⟩ := GlobalTheory.localArtinExists_holds E'' Ω A w'' h₃
  obtain ⟨hm0, hp⟩ := hT E'' g w'' h₃ (ii.trans i.symm) hcont n hn hg hnorm a₃ ha₃ K red hred hker θ hθ τ hτ hτc σ₀ hinf
  refine ⟨(monodromy_vanishing_iff_of_weil_deligne_rel W).1 hm0, fun t x z hxz hv => ?_⟩
  have hfix : ∀ y : E'', GlobalTheory.WeilTransport.conj φ.symm (t : G E'' Ω').toRingEquiv (algebraMap E'' Ω y) =
      algebraMap E'' Ω y := fun y => by
    show φ.symm ((t : G E'' Ω') (φ.symm.symm (φ.symm (algebraMap E'' Ω' y)))) = φ.symm (algebraMap E'' Ω' y)
    rw [RingEquiv.symm_apply_apply, AlgEquiv.commutes]
  let t₁ : G E'' Ω := GlobalTheory.WeilTransport.conjAlg φ.symm (t : G E'' Ω') hfix
  have hrt : ∀ z, φ.symm ((t : G E'' Ω') z) = t₁ (φ.symm z) := fun z => by
    rw [GlobalTheory.WeilTransport.conjAlg_apply, RingEquiv.symm_apply_apply]
  have ht₁ : t₁ ∈ Ine (F := E'') A := by
    rw [← actsAs_zero_iff (q := 1), GlobalTheory.WeilTransport.actsAs_iff hm hrt, actsAs_zero_iff]
    exact t.2
  have P'' : PlaceIso A' w'' A w'' φ.symm (RingHom.id E'') (RingEquiv.refl (w''.adicCompletion E'')) :=
    ⟨hm, fun _ => rfl, continuous_id, fun _ => rfl⟩
  have hart := GlobalTheory.LocLanglands.isLocalArtin_transport GlobalTheory.globalArtinReciprocity_holds
    GlobalTheory.Published.chevalleyUnits' E'' Ω' A' w'' h'' E'' Ω A w'' h₃ φ.symm (RingHom.id E'')
    (RingEquiv.refl _) P'' a'' a₃ ha'' ha₃ (ineIncl h'' t) (ineIncl h₃ ⟨t₁, ht₁⟩) hrt
  have hv' : Valued.v ((a₃ (ineIncl h₃ ⟨t₁, ht₁⟩) : w''.adicCompletion E'') -
      algebraMap E'' (w''.adicCompletion E'') (x : E'')) < 1 := by
    rw [hart]
    exact hv
  rw [← hp ⟨t₁, ht₁⟩ x z hxz hv']
  refine (inePol_transport P W fun z => ?_).symm
  have := hrt (φ z)
  rw [RingEquiv.symm_apply_apply] at this
  show φ (t₁ z) = (t : G E'' Ω') (φ z)
  rw [← this, RingEquiv.apply_symm_apply]



private theorem isRecT_fwd (P : PlaceIso A w A' w' φ j i) (rc : IrrGL (k := w.adicCompletion E) → WD h)
    (H : UpperTheory.Zero.LLC.IsRecT h rc) (a' : Weil h' →* (w'.adicCompletion E')ˣ) (ha' : IsLocalArtin h' a') :
    ∃ rc' : IrrGL (k := w'.adicCompletion E') → WD h', UpperTheory.Zero.LLC.IsRecT h' rc' ∧
      ∀ x x', RepRel i x x' → WDRel φ (rc x) (rc' x') := by
  have h3 := P.cont
  have := charZero_compl w
  have := charZero_compl w'
  have hs : Continuous i.symm := (GlobalTheory.T.continuous_ringEquiv_localField_preserves_valuation _ _ i h3).1
  obtain ⟨T, hT, hTd⟩ := GlobalTheory.T.transportIrrGL_bijective_degree_charZero _ _ i h3
  obtain ⟨hcu, hch⟩ := GlobalTheory.T.transport_keeps_cuspidal_twists_characters _ _ i h3
  obtain ⟨S, hS, hSd, hS0, hSs, hSc, hSt, hSp, hSi, hSo⟩ := GlobalTheory.T.place_over_transport_ring_iso_symm E Ω A w h E' Ω' A' w' h' φ j i P
  obtain ⟨c, hc, -⟩ := GlobalTheory.T.place_over_transport_ring_iso E Ω A w h E' Ω' A' w' h' φ j i P
  obtain ⟨a, ha, L⟩ := H
  have hart := GlobalTheory.T.localArtinMap_unique_transport_placeIso GlobalTheory.globalArtinReciprocity_holds GlobalTheory.Published.chevalleyUnits'
    E Ω A w h E' Ω' A' w' h' φ j i P a a' ha ha'
  obtain ⟨rc', key⟩ : ∃ rc' : IrrGL (k := w'.adicCompletion E') → WD h', ∀ x', rc' x' = S (rc (T.symm x')) :=
    ⟨_, fun _ => rfl⟩
  have hRS : ∀ x x', RepRel i x x' → rc' x' = S (rc x) := fun x x' r => by
    rw [key, ← (hT _ _).1 r, T.symm_apply_apply]
  have hR : ∀ x x', RepRel i x x' → WDRel φ (rc x) (rc' x') := fun x x' r => (hS _ _).2 (hRS x x' r).symm
  have hrel : ∀ x', RepRel i (T.symm x') x' := fun x' => (hT _ _).2 (T.apply_symm_apply x')
  have hcusp : ∀ x', (T.symm x').IsCusp ↔ x'.IsCusp := fun x' => (hcu _ _ (hrel x')).1
  have hG : ∀ x x', RepRel i x x' → (UpperTheory.Zero.LLC.Good x ↔ UpperTheory.Zero.LLC.Good x') := fun x x' hx =>
    ⟨GlobalTheory.T.good_irrGL_transport_along_fieldIso _ _ i h3 x x' hx, GlobalTheory.T.good_irrGL_transport_along_fieldIso _ _ i.symm hs x' x (repRel_symm hx)⟩
  have hwd : ∀ y, WDRel φ y (S y) := fun y => (hS _ _).2 rfl
  have hσ : ∀ σ', WeilRel φ (c.symm σ') σ' := fun σ' => (hc _ _).2 (c.apply_symm_apply σ')
  have hv : ∀ (ω : (w'.adicCompletion E')ˣ →* ℂˣ) (z : (w.adicCompletion E)ˣ),
      (ω.comp (Units.map i.symm.symm.toRingHom.toMonoidHom)) z = ω (Units.map i.toRingHom.toMonoidHom z) :=
    fun ω z => rfl
  have heig : ∀ x' σ', (rc' x').eig σ' = (rc (T.symm x')).eig (c.symm σ') := fun x' σ' => by
    rw [hRS _ _ (hrel x')]
    exact (GlobalTheory.LawsTTransport.eig_of_wdRel (hwd _) (hσ σ')).symm
  have hcent : ∀ (x' : IrrGL (k := w'.adicCompletion E')) ω, HasCentralChar x'.rep ω →
      HasCentralChar (T.symm x').rep (ω.comp (Units.map i.symm.symm.toRingHom.toMonoidHom)) :=
    fun x' ω hω => central_transport i.symm (repRel_symm (hrel x')) hω
  refine ⟨rc', ⟨a', ha', ⟨fun x' => ?_, fun χ' hχ' => ?_, fun l x' hx => ?_, fun x' hx => ?_, fun x' s => ?_,
    fun x' ω hω σ' => ?_, fun x' χ hχ hg => ?_, fun x' ω hg hω σ' => ?_, fun n π π' hg ⟨u₀⟩ => ?_,
    fun x' y' hg e => ?_, fun x' hg hf => ?_, typeLaw_fwd P rc rc' hR L.type⟩⟩, hR⟩
  · rw [key, hSd, L.dim, ← hTd, T.apply_symm_apply]
  · have hχ := isSmoothChar_comp i h3 hχ'
    have R := hch _ hχ χ' hχ' (fun _ => rfl)
    rw [key, ← (hT _ _).1 R, T.symm_apply_apply, L.one]
    refine hSo _ _ _ _ fun σ σ' hσ => ?_
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MonoidHom.comp_apply, hart σ σ' hσ]
  · let f : Segment (w'.adicCompletion E') → Segment (w.adicCompletion E) := fun Δ =>
      Segment.ofFirst (T.symm Δ.first) ((hcusp _).2 Δ.isCusp_first) Δ.len Δ.len_pos
    have hl := GlobalTheory.T.isLanglandsData_transport_localFieldIso _ _ i.symm hs l (l.map f) x' (T.symm x')
      (by rw [List.forall₂_map_right_iff, List.forall₂_same]; exact fun Δ _ => ⟨repRel_symm (hrel _), rfl⟩)
      (repRel_symm (hrel x')) hx
    rw [key, L.langlands _ _ hl]
    clear hl hx
    induction l with
    | nil => exact hS0
    | cons Δ l ih =>
      simp only [segSum, sumList, List.map_cons, List.foldr_cons] at ih ⊢
      rw [hSs, ih, hSc, hSt, hSp, show (f Δ).first = T.symm Δ.first from rfl,
        show (f Δ).len = Δ.len from rfl, ← key]
  · rw [key, hSi]
    exact L.cusp _ ((hcusp x').2 hx)
  · have R : RepRel i ((T.symm x').nu s) (x'.nu s) := (hcu _ _ (hrel x')).2 s
    rw [key, ← (hT _ _).1 R, T.symm_apply_apply, L.nu, hSt, ← key]
  · rw [heig, L.absCentral _ _ (hcent x' ω hω) (c.symm σ'), hart _ _ (hσ σ'), hv]
  · have hχ0 := isSmoothChar_comp i h3 hχ
    have htw : ∀ x x', RepRel i x x' → RepRel i (x.tw _ hχ0) (x'.tw χ hχ) := by
      rintro x x' ⟨n, π, π', e, rfl, rfl, he⟩
      exact repRel_tw i π π' e he _ hχ0 χ hχ (fun _ => rfl)
    rw [hRS _ _ (htw _ _ (hrel x')), L.twist _ _ _ ((hG _ _ (hrel x')).2 hg), hSc, ← hRS _ _ (hrel x'),
      ← hRS _ _ (hch _ hχ0 χ hχ (fun _ => rfl))]
  · rw [heig, L.central _ _ ((hG _ _ (hrel x')).2 hg) (hcent x' ω hω) (c.symm σ'), hart _ _ (hσ σ'), hv]
  · obtain ⟨π₀, e, h1, he⟩ := exists_of_repRel π (repRel_symm (hrel (cls π)))
    obtain ⟨π₀', u, h2, hu⟩ := exists_of_repRel π' (repRel_symm (hrel (cls π')))
    have r1 : RepRel i (cls π₀) (cls π) := h1 ▸ hrel (cls π)
    have r2 : RepRel i (cls π₀') (cls π') := h2 ▸ hrel (cls π')
    rw [hRS _ _ r2, hRS _ _ r1, ← equiv_lpDual P S hS,
      L.dual n π₀ π₀' ((hG _ _ r1).2 hg) (contra_transport i.symm hs h3 π π' π₀ π₀' e he u hu u₀)]
  · have e2 : rc (T.symm x') = rc (T.symm y') := by
      apply S.injective
      rw [← hRS _ _ (hrel x'), ← hRS _ _ (hrel y'), e]
    exact T.symm.injective (L.inj _ _ ((hG _ _ (hrel y')).2 hg) e2)
  · have hx' := repRel_symm (hrel x')
    exact tame_fwd P (hR _ _ (hrel x')) (L.depth _ (GlobalTheory.T.good_irrGL_transport_along_fieldIso _ _ i.symm hs _ _ hx' hg)
      (GlobalTheory.T.principalCongruence_fixedVectors_ne_bot_transport _ _ i.symm hs _ _ hx' hf))

end UpperTheory.One.M.FieldTr

open UpperTheory.One.M.FieldTr in
theorem UpperTheory.One.M.fieldGT :
    UpperTheory.One.M.FieldGT := by
  intro E Ω _ _ _ _ _ A w h E' Ω' _ _ _ _ _ A' w' h' rc rc' H H' φ j i h1 h2 h3 h4 n π π' e he hg
  have P : PlaceIso A w A' w' φ j i := ⟨h1, h2, h3, h4⟩
  have := charZero_compl w
  have := charZero_compl w'
  obtain ⟨a', ha', -⟩ := id H'
  obtain ⟨rc'', hrec, hR⟩ := isRecT_fwd P rc H a' ha'
  have hr : RepRel i (cls π) (cls π') := ⟨n, π, π', e, rfl, rfl, he⟩
  have hg' := GlobalTheory.T.good_irrGL_transport_along_fieldIso _ _ i h3 _ _ hr hg
  have W := hR _ _ hr
  rw [UpperTheory.Zero.LLC.recTUnique E' Ω' A' w' h' rc'' rc' hrec H' _ hg'] at W
  obtain ⟨a, ha, L⟩ := H
  exact exists_of_wdRel W (L.dim _)
end
end
end
