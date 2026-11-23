module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.WeightsConjBis
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LimWU4OfLimWU3
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.HodgeTrAt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.TLiftK
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BaseChangeDescent.BcBackOffT
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.ClosedPhiHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CongruenceOddLevel.CongFinOddOfLvLac
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.ToCoreK
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineInputs.CoreAllOfRowStarCoreInp
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineInputs.InputsOf
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
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.PAdicSplitting.LocalGlobalCompatAtIwahoriFixedPlaces
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.WeightsConjAlt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsGenericOfIsLocComp
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NontrivialTwJacquetOfSurjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspRepSatakeIffLocalComponentSatakeStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIsWeight
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalContragredientMonomial
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalLetter
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.NeutralLocalFields.Reciprocity
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.InertCharpoly.CharPolOfInert
import GroundTheory.LocalFields.PadicLogSeries
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.MainFin
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.GaloisCompatUnlinkedSupportOfSpherical
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.PAdicSplitting.LocalGlobalCompatAtIwahoriFixedOfUnlinked
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TraceLimits.LimFinOddOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.LadicWeightEmbeddingOverPlace

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineInputs.CoreAllOfRowStarCore

section

@[expose] public section

theorem UpperTheory.Gal.Int.Inp.coreAll_of_core : GlobalTheory.RoadU.Core → GlobalTheory.RoadU.CoreAll :=
  UpperTheory.Gal.Int.Inp.coreAll_of_core_inp UpperTheory.Gal.Int.Inp.inp_holds
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValuationNatCastLtOneOfInduces

section

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.GalCut
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.GalCut

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [IsCMField E] {l : ℕ} [Fact l.Prime] {a : ℕ}


omit [IsAlgClosure E Ω] [IsCMField E] in
theorem norm_natCast_om_lt_one : ‖((l : ℕ) : Om l)‖ < 1 := by
  have h := PadicAlgCl.norm_extends l ((l : ℕ) : ℚ_[l])
  rw [map_natCast] at h
  rw [h]
  exact Padic.norm_p_lt_one


omit [NumberField E] [IsAlgClosure E Ω] [IsCMField E] in
theorem valuation_natCast_lt_one_of_induces {A : ValuationSubring Ω} {O : Type} [CommRing O] [Algebra ℤ_[l] O]
    [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw) :
    A.valuation ((l : ℕ) : Ω) < 1 := by
  have hn : ‖Bw.j ((l : ℕ) : Ω)‖ < 1 := by rw [map_natCast]; exact norm_natCast_om_lt_one
  have hl0 : ((l : ℕ) : Ω) ≠ 0 := by
    intro h0
    have h1 := congrArg Bw.j h0
    rw [map_natCast, map_zero] at h1
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) h1
  have hmem : ((l : ℕ) : Ω) ∈ A := (hj _).2 hn.le
  have hinv : ((l : ℕ) : Ω)⁻¹ ∉ A := by
    intro hm
    have h1 := (hj _).1 hm
    rw [map_inv₀, norm_inv] at h1
    have hpos : 0 < ‖Bw.j ((l : ℕ) : Ω)‖ := norm_pos_iff.2 ((_root_.map_ne_zero _).2 hl0)
    have := (one_lt_inv₀ hpos).2 hn
    linarith
  refine lt_of_le_of_ne ((A.valuation_le_one_iff _).2 hmem) fun h1 => hinv ?_
  rw [← A.valuation_le_one_iff, map_inv₀, h1, inv_one]


omit [IsAlgClosure E Ω] [IsCMField E] in
theorem mem_of_induces {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} (hA : IsPlaceOver A w) {O : Type} [CommRing O]
    [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw) :
    ((l : ℕ) : 𝓞 E) ∈ w.asIdeal := by
  refine (hA _).1 ?_
  have h := valuation_natCast_lt_one_of_induces Bw hj
  simpa [map_natCast] using h

end GlobalTheory.GalCut
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.InertCharpoly.GaloisLocalGlobalOfLocalGlobalCompatibility

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.DeRhamOfPlainTorus
open UpperTheory.Zero.LLC UpperTheory.GalStar UpperTheory.GalS UpperTheory.Gal.ToralGalois.R2

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.Int.Row

abbrev PlaceClass : Type 1 := ∀ (E : Type) [Field E] [NumberField E], HeightOneSpectrum (𝓞 E) → ℕ → Prop

def LocalGlobalCompatibilityAtPlaceClass (Q : PlaceClass) : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n → ∀ (π : CuspSub E n) (χ : HChar (maximalRealSubfield E)),
    InScope .all l π χ → ∀ r : G E Ω →* GL (Fin n) (Qbar l), Weak π ι r →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin n) (w.adicCompletion E))), π.IsLocComp w σ →
      fixed σ.ρ (KOne (w.adicCompletion E) (Fin n)) ≠ ⊥ → Q E w n → IsQg w → Apart (algNorm σ) →
    ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w) (rc : IrrGL (k := w.adicCompletion E) → WD h), IsRecT h rc →
      (rc (algNorm σ)).mono0 →
      (∀ hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal, (wdOf h hl ι r).mono0 ∧
        ∀ t : Ine (F := E) A, (wdOf h hl ι r).charPol (ineIncl h t) = (rc (algNorm σ)).charPol (ineIncl h t)) ∧
      (((l : ℕ) : 𝓞 E) ∈ w.asIdeal → ClauseAt .dR π ι r w ∧
        ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
        ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
          (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : GlobalTheory.Pst.Induces Bw),
          IsPstAt P Bw (r.comp (Dec (F := E) A).subtype) ∧ (wdAt P ι Bw h hj (r.comp (Dec (F := E) A).subtype)).mono0 ∧
          ∀ t : Ine (F := E) A,
            (wdAt P ι Bw h hj (r.comp (Dec (F := E) A).subtype)).charPol (ineIncl h t) = (rc (algNorm σ)).charPol (ineIncl h t))

theorem localGlobalAtPlaceClass_of_localGlobal (H : LocalGlobalCompatAtIwahoriFixedPlaces) (Q : PlaceClass) : LocalGlobalCompatibilityAtPlaceClass Q := fun E Ω _ _ _ _ _ _ l _ ι n hn π χ hI r hW w σ hσ hf _ q g =>
  H E Ω l ι n hn π χ hI r hW w σ hσ hf (Or.inr ⟨q, g⟩)

section Local

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem charPol_of_ine {x y : WD h} (k : ∀ t : Ine (F := E) A, x.charPol (ineIncl h t) = y.charPol (ineIncl h t))
    (g : Weil h) (hg : deg g = 0) : x.charPol g = y.charPol g := by
  obtain ⟨t, e⟩ := exists_eq_zpow_mul deg_frob g
  rw [hg, zpow_zero, one_mul] at e
  rw [e, k]

theorem dim_of_ine {x y : WD h} (k : ∀ t : Ine (F := E) A, x.charPol (ineIncl h t) = y.charPol (ineIncl h t)) :
    x.lpDim = y.lpDim := by
  rw [← WD.charPol_natDegree x (ineIncl h 1), k, WD.charPol_natDegree]

variable [IsCMField E] {a : ℕ} {π : CuspSub E a} {σ : SmIrr (GL (Fin a) (w.adicCompletion E))}
  {rc : IrrGL (k := w.adicCompletion E) → WD h}

theorem generic_algNorm (hσ : π.IsLocComp w σ) : IsGeneric (algNorm σ).rep :=
  (isGeneric_congr (IrrGL.twEquiv _ _ (isSmoothChar_absPow _))).1 ((isGeneric_twist_iff _).2
    ((isGeneric_congr (IrrGL.equivOf σ.ρ σ.smooth σ.irred)).1 (GlobalTheory.CuspRep.Generic.isGeneric_of_isLocComp E a π w σ hσ)))

theorem guard_tame (ha : 1 ≤ a) (hσ : π.IsLocComp w σ) (hrc : IsRecT h rc) (hq : IsQp w) (ht : TmW (rc (algNorm σ)))
    (hs : Sqf (rc (algNorm σ))) (hm : (rc (algNorm σ)).mono0) :
    fixed σ.ρ (KOne (w.adicCompletion E) (Fin a)) ≠ ⊥ ∧ Apart (algNorm σ) := by
  obtain ⟨h1, h2⟩ := mixed_of_tame hq hrc (generic_algNorm hσ) ht hs hm
  exact ⟨GlobalTheory.WeakTheRep.fixed_ne_bot_of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred).symm
    (dz_of_nu (x := IrrGL.of σ.ρ σ.smooth σ.irred) ha _ h1), fun s k => (h2 s k).2⟩

theorem exists_hasSat (hσ : π.IsLocComp w σ) (hs : SmGL.IsSpherical σ.ρ) : ∃ B, (CG.mk π).HasSat w B := by
  obtain ⟨k1, k2⟩ := GlobalTheory.T.cuspRep_satake_iff_localComponent_satake E a π w σ hσ
  obtain ⟨B, hB⟩ := GlobalTheory.SatInd.exists_hasSatGL_of_isIrreducible σ.smooth σ.irred (k2.1 hs)
  exact ⟨B, (k1 B).2 hB⟩

end Local

def Cmp {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w} (q : Prop) (x y : WD h) : Prop :=
  x.lpDim = y.lpDim ∧ (Tor y → y.mono0 → x = y) ∧
    (q → IsQp w → TmW y → Sqf y → y.mono0 → x.mono0 ∧ ∀ g : ↥(Weil h), deg g = 0 → x.charPol g = y.charPol g)

section Global

variable {Q : PlaceClass} {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ} {a : ℕ} {π : CuspSub E a} {χ : HChar (maximalRealSubfield E)}
  {r : G E Ω →* GL (Fin a) (Qbar l)} {w : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω} {h : IsPlaceOver A w}
  {σ : SmIrr (GL (Fin a) (w.adicCompletion E))} {rc : IrrGL (k := w.adicCompletion E) → WD h}

theorem away (H1 : R1) (H2 : LocalGlobalCompatibilityAtPlaceClass Q) (ha : 1 ≤ a) (hI : InScope .all l π χ) (hW : Weak π ι r)
    (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (hrc : IsRecT h rc) (hσ : π.IsLocComp w σ) :
    Cmp (Q E w a) (wdOf h hl ι r) (rc (algNorm σ)) := by
  refine ⟨?_, fun ht hm => ?_, fun q hq ht hs hm => ?_⟩
  · obtain ⟨_, _, L⟩ := hrc
    rw [lpDim_wdOf, Fintype.card_fin, L.dim]
    rfl
  · exact ((H1 E Ω l ι a ha π χ hI r hW w σ hσ (plainTor_of_tor hrc (generic_algNorm hσ) ht hm)).1 hl A h).2 rc hrc
  · obtain ⟨g1, g2⟩ := guard_tame ha hσ hrc hq ht hs hm
    have k := (H2 E Ω l ι a ha π χ hI r hW w σ hσ g1 q hq g2 A h rc hrc hm).1 hl
    exact ⟨k.1, charPol_of_ine k.2⟩

theorem above (H1 : R1) (H2 : LocalGlobalCompatibilityAtPlaceClass Q) (ha : 1 ≤ a) (hI : InScope .all l π χ) (hW : Weak π ι r)
    {P : LocPrime l} {AI : LocAinf l P} (T : Nonempty (LocTied l P AI))
    {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw)
    (hrc : IsRecT h rc) (hσ : π.IsLocComp w σ)
    (g : (Q E w a ∧ IsQp w ∧ TmW (rc (algNorm σ)) ∧ Sqf (rc (algNorm σ))) ∨ Tor (rc (algNorm σ))) (hm : (rc (algNorm σ)).mono0) :
    ClauseAt .dR π ι r w ∧ IsPstAt P Bw (r.comp (Dec (F := E) A).subtype) ∧
      Away (wdAt P ι Bw h hj (r.comp (Dec (F := E) A).subtype)) (rc (algNorm σ)) := by
  have hl := mem_of_induces h Bw hj
  by_cases ht : Tor (rc (algNorm σ))
  · obtain ⟨k1, k2⟩ := (H1 E Ω l ι a ha π χ hI r hW w σ hσ (plainTor_of_tor hrc (generic_algNorm hσ) ht hm)).2 hl
    obtain ⟨k3, k4, k5⟩ := k2 P AI T A h O Bw hj
    have e := GlobalTheory.WeakTheRep.eq_of_mono0_charPol _ _ k4 hm (k5 rc hrc)
    exact ⟨k1, k3, by rw [e], fun _ _ => e, fun _ _ _ _ => ⟨k4, fun g _ => k5 rc hrc g⟩⟩
  · obtain ⟨q, hq, h1, h2⟩ := g.resolve_right ht
    obtain ⟨g1, g2⟩ := guard_tame ha hσ hrc hq h1 h2 hm
    obtain ⟨k1, k2⟩ := (H2 E Ω l ι a ha π χ hI r hW w σ hσ g1 q hq g2 A h rc hrc hm).2 hl
    obtain ⟨k3, k4, k5⟩ := k2 P AI T O Bw hj
    exact ⟨k1, k3, dim_of_ine k5, fun t => absurd t ht, fun _ _ _ _ => ⟨k4, charPol_of_ine k5⟩⟩

theorem exists_weights (ha : 1 ≤ a) (hI : InScope .all l π χ) (ι : Qbar l ≃+* ℂ) :
    ∃ (wt : ℤ) (HT : (E →+* Qbar l) → Multiset ℤ),
      (∀ τ : E →+* Qbar l, (HT τ).map (fun n : ℤ => (n : ℂ)) =
        ((CG.mk π).infChar (ι.toRingHom.comp τ)).map fun z => ((a : ℂ) - 1) / 2 - z) ∧
      ∀ τ : E →+* Qbar l, HT (τ.comp (IsCMField.complexConj E).toRingEquiv.toRingHom) = (HT τ).map (wt - ·) := by
  obtain ⟨wt, hwt⟩ := GlobalTheory.PolarizedWeight.exists_isWeight E l a ha π χ hI
  have ex : ∀ τ : E →+* Qbar l, ∃ J : Multiset ℤ, J.map (fun n : ℤ => (n : ℂ)) =
      ((CG.mk π).infChar (ι.toRingHom.comp τ)).map fun z => ((a : ℂ) - 1) / 2 - z := fun τ => by
    haveI : CanLift ℂ ℤ (fun n : ℤ => (n : ℂ)) (fun z => ∃ n : ℤ, (n : ℂ) = z) := ⟨fun _ k => k⟩
    refine (Multiset.canLift (fun n : ℤ => (n : ℂ)) (fun z => ∃ n : ℤ, (n : ℂ) = z)).prf _ fun y hy => ?_
    obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.1 hy
    obtain ⟨n, hn⟩ := (hI.1 (ι.toRingHom.comp τ)).2 z hz
    exact ⟨-n, by rw [hn]; push_cast; ring⟩
  choose HT hHT using ex
  refine ⟨wt, HT, hHT, fun τ => Multiset.map_injective (Int.cast_injective (α := ℂ)) ?_⟩
  have k := hwt (ι.toRingHom.comp τ)
  have e := congrArg (Multiset.map fun y : ℂ => (wt : ℂ) - y) (hHT τ)
  rw [hHT, ← RingHom.comp_assoc, k]
  simp only [Multiset.map_map, Function.comp_def] at e ⊢
  push_cast
  rw [e]
  exact Multiset.map_congr rfl fun z _ => by ring

theorem crys (C : CoreAll) (ha : 1 ≤ a) (hI : InScope .all l π χ) (hW : Weak π ι r) (hσ : π.IsLocComp w σ)
    (hs : SmGL.IsSpherical σ.ρ) : ClauseAt .crys π ι r w ∧ ClauseAt .dR π ι r w := by
  obtain ⟨B, hB⟩ := exists_hasSat hσ hs
  exact ⟨C.2 .crys E Ω l ι a ha π χ hI r hW w trivial B hB, C.2 .dR E Ω l ι a ha π χ hI r hW w trivial B hB⟩

end Global

theorem galoisLocalGlobal_of_placeClassCompatibility (C : CoreAll) (H1 : R1) (H2 : LocalGlobalCompatibilityAtPlaceClass fun _ _ _ _ _ => True) :
    Row0 (fun h rc => IsRecT h rc) := fun E Ω _ _ _ _ _ _ l _ ι a ha π χ hr hp => by
  have hI : InScope .all l π χ := ⟨hr, hp, trivial⟩
  obtain ⟨r, hW⟩ := C.1 E Ω l ι a ha π χ hI
  obtain ⟨wt, HT, w1, w2⟩ := exists_weights ha hI ι
  refine ⟨r, wt, HT, hW.1, hW.2.1, fun w hl A h rc hrc σ hσ => ?_, w1, w2, fun P AI T w A h O _ _ _ Bw hj =>
    ⟨fun σ hσ hs => ?_, fun σ hσ rc hrc g hm => ?_⟩⟩
  · have k := away H1 H2 ha hI hW hl hrc hσ
    exact ⟨k.1, k.2.1, k.2.2 trivial⟩
  · obtain ⟨k1, k2⟩ := crys C ha hI hW hσ hs
    have k3 := k2 P AI T A h O Bw hj
    exact ⟨k1 P AI T A h O Bw hj σ hσ hs, k3.1, fun τ LL' τ' hτ => k3.2 τ LL' τ' hτ _ (w1 τ)⟩
  · obtain ⟨k1, k2, k4⟩ := above H1 H2 ha hI hW T Bw hj hrc hσ (g.imp (fun q => ⟨trivial, q⟩) id) hm
    have k3 := k1 P AI T A h O Bw hj
    exact ⟨k3.1, k2, fun τ LL' τ' hτ => k3.2 τ LL' τ' hτ _ (w1 τ), k4⟩

theorem galoisLocalGlobal_of_localGlobalCompatibility (C : CoreAll) (H1 : R1) (H2 : LocalGlobalCompatAtIwahoriFixedPlaces) : Row0 (fun h rc => IsRecT h rc) :=
  galoisLocalGlobal_of_placeClassCompatibility C H1 (localGlobalAtPlaceClass_of_localGlobal H2 _)

end UpperTheory.Gal.Int.Row
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.Development

section

@[expose] public section

namespace UpperTheory.Gal.Int

open GlobalTheory.CongL

def recT : UpperTheory.GalStar.RecNotion := fun h rc => UpperTheory.Zero.LLC.IsRecT h rc

theorem coreAll_of (seed : SeedFinOdd) (cong : CongFinOdd) (up : UpperTheory.TP.TLiftK) : GlobalTheory.RoadU.CoreAll :=
  UpperTheory.Gal.Int.Inp.coreAll_of_core
    (UpperTheory.Gal.Int.Core.toCoreK up UpperTheory.Gal.ClosedPhiFromClosedTrace.congPhi_holds UpperTheory.Gal.Desc.descOffT (UpperTheory.Gal.Lim.limFinOdd_of seed cong))

theorem rest (h : GlobalTheory.RoadU.CoreAll) : UpperTheory.GalStar.Row0 recT := by
  have hspherical := UpperTheory.Gal.ToralGalois.galoisCompat_unlinkedSupport_of_spherical h
  exact UpperTheory.Gal.Int.Row.galoisLocalGlobal_of_localGlobalCompatibility h hspherical
    (UpperTheory.Gal.ToralGalois.R2.localGlobalCompatAtIwahoriFixed_of_unlinked hspherical)

theorem galoisLocalGlobal_of_geometry_lift (geo : UpperTheory.Gal.Int.Geo.GeoOne) (up : UpperTheory.TP.TLiftK) : UpperTheory.GalStar.Row0 recT :=
  rest (coreAll_of (UpperTheory.Gal.Int.Div.seedFinOdd_of_geoOne geo) (UpperTheory.Gal.Int.Cong.congFinOdd_of_ex UpperTheory.Gal.Wt.wtLacEx_holds) up)

theorem galoisLocalGlobalStrong_of_geometry_lift (geo : UpperTheory.Gal.Int.Geo.GeoOne) (up : UpperTheory.TP.TLiftK) : UpperTheory.GalStar.Row0b recT :=
  UpperTheory.GalStar.Row0.row0b recT (galoisLocalGlobal_of_geometry_lift geo up)

end UpperTheory.Gal.Int
end
end
