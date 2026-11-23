module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeightsConj
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CGTrueT
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlocksUnique
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPadicAlgClRingEquivComplexCompEqOfCountabl
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.UnrRecOfHasSat
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRecTLocRecT
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocParTwistAbsPow
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.UnrRecOfHasSat
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
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReadsCusp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FillPreservesIdempotent

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsRep

section

@[expose] public section



section
noncomputable section
namespace GlobalTheory.HeightCounting.Blocks
open NumberField IsDedekindDomain Polynomial Filter
section Polar
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp GlobalTheory.ThetaPull GlobalTheory.UnitaryBC Formalism.L2.Host Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleMap continuous_ideleMap ideleMap_principalIdele continuous_adeleMap)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne in
theorem exists_rep_alt_alt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL)
    (hG : _root_.UpperTheory.GalS.CuspUAlt) (Ω : Type) [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ}
    [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (ha : 1 ≤ a) (π : CG E a) (hc : π.IsCsd) (s : ℝ)
    (hr : ∀ τ, (π.infChar τ).Nodup ∧ ∀ z ∈ π.infChar τ, ∃ m : ℤ, z + (s : ℂ) = (m : ℂ) + ((a : ℂ) - 1) / 2) :
    ∃ r : G E Ω →* GL (Fin a) (Qbar l), Continuous (fun g => (r g : Matrix (Fin a) (Fin a) (Qbar l))) ∧
      ∀ (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w),
        UpperTheory.GalS.Aw (wdOf h hl ι r) (((_root_.GlobalTheory.CuspRep.ParLawsT.locParT hL π h).lpTw s).lpTw ((1 - (a : ℝ)) / 2)) := by
  have hν := GlobalTheory.HeckeGal.Model.absPow_isAbsPow E s
  have hr' : (π.twist (GlobalTheory.HeckeGal.Model.absPow E s)).IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
    rw [((ParLaws.hasInfChar_infChar π τ).twist _).infChar_eq, (InfType.expo_of_infType E _).2.1 s hν τ]
    refine ⟨(hr τ).1.map (add_left_injective _), fun z hz => ?_⟩
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hz
    exact (hr τ).2 y hy
  induction π using Quotient.inductionOn with | _ π =>
  obtain ⟨r, wt, HT, H⟩ := hG E Ω l ι a ha _ _ hr' (isPolarized_twist_absPow hc s)
  refine ⟨r, Units.continuous_val.comp H.cont, fun w hl A h => ?_⟩
  have k := H.aw_locPar hL hF hl h
  have e := _root_.GlobalTheory.HeightCounting.Blocks.local_parameter_twist_abs_pow hL hF (CG.mk π) hν h
  exact (congrArg (fun x : WD h => UpperTheory.GalS.Aw (wdOf h hl ι r) (x.lpTw ((1 - (a : ℝ)) / 2))) e).mp k
end Polar
section True
end True
end GlobalTheory.HeightCounting.Blocks
namespace GlobalTheory.HeightCounting
end GlobalTheory.HeightCounting
section
namespace GlobalTheory.GalAllPlaces
end GlobalTheory.GalAllPlaces
end
section
namespace GlobalTheory.CsdTwistGal
end GlobalTheory.CsdTwistGal
namespace GlobalTheory.TempSatGal
end GlobalTheory.TempSatGal
end
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspFam

section

@[expose] public section



section
noncomputable section
namespace GlobalTheory.HeightCounting.Blocks
open NumberField IsDedekindDomain Polynomial Filter
section Polar
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp GlobalTheory.ThetaPull GlobalTheory.UnitaryBC Formalism.L2.Host Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleMap continuous_ideleMap ideleMap_principalIdele continuous_adeleMap)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}
end Polar
section True
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.RowPar GlobalTheory.RowTie GlobalTheory.CuspRep GlobalTheory.WeilDeligne
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) {D : D7} {T : WDTie D.nd D.naut}
  (C : _root_.GlobalTheory.HeightCounting.CGTrueT hL D T)
include hF C in
theorem cuspFam_alt_alt (hG : _root_.UpperTheory.GalS.CuspUAlt) {l : ℕ} [hp : Fact l.Prime] (ι : Qbar l ≃+* ℂ) :
    CuspFam D.naut ι := by
  intro a ha π hc s hs
  have := host_isCMField D.host
  obtain ⟨r, h1, h3⟩ := _root_.GlobalTheory.HeightCounting.Blocks.exists_rep_alt_alt hL hF hG D.nd.Om ι ha (C.e a π).1 ((C.csd a π).1 hc) s fun τ => by
    have := hs τ
    rwa [C.inf] at this
  have hfin : ∀ᶠ w : PlE D.host in cofinite, ((l : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := by
    have h0 : Ideal.span {((l : ℕ) : 𝓞 D.host.E)} ≠ 0 := by simpa using hp.out.ne_zero
    have hf : {v : PlE D.host | ((l : ℕ) : 𝓞 D.host.E) ∈ v.asIdeal}.Finite :=
      (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.2 hv
    exact hf.eventually_cofinite_notMem
  refine ⟨fun z σ => (r σ : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.eval z, fun z => ?_, ?_⟩
  · simp only [Matrix.eval_charpoly]
    exact (continuous_const.sub h1).matrix_det
  · filter_upwards [hfin, D.naut.locG_unr_ae π] with w hl hu B σ hB hσ z
    have hu' := (D.naut.unr_tw _ (s + (1 - (a : ℝ)) / 2)).2 hu
    have e : T.e w (D.naut.lpTw (D.naut.locG π w) (s + (1 - (a : ℝ)) / 2)) = wdOf (D.nd.plOm.2 w) hl ι r := by
      have hu2 := (T.unr w _).1 hu'
      rw [← D.naut.lpTw_add, T.tw, T.tw, C.loc] at hu2 ⊢
      exact ((h3 w hl _ _).eq_unr hu2).symm
    rw [galPol, T.frobEig w _ hu', e, ← frobEig_wdOf hl ι h1 (e ▸ (T.unr w _).1 hu') hB hσ]
    exact (eval_map_apply ι.toRingHom _).symm
end True
end GlobalTheory.HeightCounting.Blocks
namespace GlobalTheory.HeightCounting
end GlobalTheory.HeightCounting
section
namespace GlobalTheory.GalAllPlaces
end GlobalTheory.GalAllPlaces
end
section
namespace GlobalTheory.CsdTwistGal
end GlobalTheory.CsdTwistGal
namespace GlobalTheory.TempSatGal
end GlobalTheory.TempSatGal
end
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BlocksUnique

section

@[expose] public section



section
noncomputable section
namespace GlobalTheory.HeightCounting.Blocks
open NumberField IsDedekindDomain Polynomial Filter
section Satake
open GlobalTheory.LFun GlobalTheory.PRep GlobalTheory.CuspRep Formalism.UG
variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {n : ℕ}
variable [_root_.NumberField.IsTotallyComplex E]
end Satake
section Local
open GlobalTheory.CuspRep GlobalTheory.CuspRep.ParLaws GlobalTheory.WeilDeligne GlobalTheory.LocLanglands Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {a : ℕ}
variable [_root_.NumberField.IsTotallyComplex E] (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL)
end Local
section Polar
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp GlobalTheory.ThetaPull GlobalTheory.UnitaryBC Formalism.L2.Host Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleMap continuous_ideleMap ideleMap_principalIdele continuous_adeleMap)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}
end Polar
section Record
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.RowPar GlobalTheory.RowTie
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N} {l : ℕ} [Fact l.Prime]
variable {ι : Qbar l ≃+* ℂ}
end Record
section True
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.RowPar GlobalTheory.RowTie GlobalTheory.CuspRep GlobalTheory.WeilDeligne
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) {D : D7} {T : WDTie D.nd D.naut}
  (C : _root_.GlobalTheory.HeightCounting.CGTrueT hL D T)
end True
end GlobalTheory.HeightCounting.Blocks
namespace GlobalTheory.HeightCounting
open Formalism.BasicNotions GlobalTheory.CuspRep Blocks
theorem CGTrueT.blocksUnique (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL)
    (hG : _root_.UpperTheory.GalS.CuspUAlt) (hJ : GlobalTheory.Published.JacquetShalikaRigidity)
    (hC : GlobalTheory.Published.ChebotarevDegreeOne) {D : D7} {T : GlobalTheory.RowTie.WDTie D.nd D.naut} (C : _root_.GlobalTheory.HeightCounting.CGTrueT hL D T) :
    BlocksUnique D := by
  intro Sig Sig' h _ _ e
  have := host_isCMField D.host
  haveI : Fact (Nat.Prime 2) := Nat.fact_prime_two
  obtain ⟨ι⟩ := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex 2
  have h1 := fun p hp => h p (List.mem_append_left Sig' hp)
  have h2 := fun p hp => h p (List.mem_append_right Sig hp)
  exact Multiset.coe_eq_coe.2 ((perm_of_split hC (GlobalTheory.RowPar.isobaricRigid_of_jacquetShalika hJ (_root_.GlobalTheory.HeightCounting.Blocks.readsCusp_alt hF C))
    (_root_.GlobalTheory.HeightCounting.Blocks.cuspFam_alt_alt hF C hG (l := 2) ι) (fun p hp => ⟨(h1 p hp).1, (h1 p hp).2.1⟩) (fun p hp => ⟨(h2 p hp).1, (h2 p hp).2.1⟩)
    ⟨fun p hp => (h1 p hp).2.2.1, fun p hp => (h1 p hp).2.2.2⟩ ⟨fun p hp => (h2 p hp).2.2.1, fun p hp => (h2 p hp).2.2.2⟩
    (Filter.Eventually.of_forall e)).map _)
end GlobalTheory.HeightCounting
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BlocksUniqueOfCgTrue

section

@[expose] public section



section
noncomputable section
namespace GlobalTheory.HeightCounting.Blocks
open NumberField IsDedekindDomain Polynomial Filter
section Satake
open GlobalTheory.LFun GlobalTheory.PRep GlobalTheory.CuspRep Formalism.UG
variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {n : ℕ}
variable [_root_.NumberField.IsTotallyComplex E]
end Satake
section Local
open GlobalTheory.CuspRep GlobalTheory.CuspRep.ParLaws GlobalTheory.WeilDeligne GlobalTheory.LocLanglands Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {a : ℕ}
variable [_root_.NumberField.IsTotallyComplex E] (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL)
end Local
section Polar
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp GlobalTheory.ThetaPull GlobalTheory.UnitaryBC Formalism.L2.Host Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleMap continuous_ideleMap ideleMap_principalIdele continuous_adeleMap)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}
end Polar
section Record
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.RowPar GlobalTheory.RowTie
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N} {l : ℕ} [Fact l.Prime]
variable {ι : Qbar l ≃+* ℂ}
end Record
section True
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.RowPar GlobalTheory.RowTie GlobalTheory.CuspRep GlobalTheory.WeilDeligne
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) {D : D7} {T : WDTie D.nd D.naut}
  (C : _root_.GlobalTheory.HeightCounting.CGTrueT hL D T)
end True
end GlobalTheory.HeightCounting.Blocks
namespace GlobalTheory.HeightCounting
open Formalism.BasicNotions GlobalTheory.CuspRep Blocks
theorem blocksUnique_of_cgTrue_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, GlobalTheory.Published.AutomorphicFormsFiniteGL →
    _root_.UpperTheory.GalS.CuspUAlt → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.JacquetShalika →
    GlobalTheory.Published.ChebotarevDegreeOne → ∀ (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut), _root_.GlobalTheory.HeightCounting.CGTrueT hL D T → BlocksUnique D :=
  fun hL hF hG _ hJ hC _ _ C => C.blocksUnique hL hF hG hJ.1 hC
end GlobalTheory.HeightCounting
end
end
end
end
