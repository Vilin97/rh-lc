module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BoundAtTwoThreeFamilyFon
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleParametersOfLargeScale
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
public import Development.AutomorphicArithmetic.CyclotomicBounds.CyclotomicOrders.NuHost
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWachFunctorComparisonOfBhattScholzeStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAssembly
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PsiAtPsiAt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualAbsIrredGoodPointOfResidualIrred
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpecialPrimesSmallAlongFamilyStatement
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DecompositionInvariantsCondition
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Mathlib.RingTheory.DedekindDomain.Factorization

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChosenTwistAnnihilatesSelmerGroups

section

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLink

theorem twist_kills_selmer : ∀ (D : D7) (C : NChoice D) (I : TwIn D) (ρ : FamilyRepresentationConstants.RhoFam D), NChTie D C → TwGoodAt D C I →
    KillingConditions.SignatureChoiceCondition ρ C → KillingConditions.KillAt ρ := by
  intro D C I ρ hT hG hA i hi
  have hw : D.what₂.muAt (D.nd.w i) ≠ D.what₂.mu0 := hi
  obtain ⟨-, hg⟩ := hG (D.nd.w i) hw
  obtain ⟨hA1, hA2⟩ := hA i hi
  obtain ⟨-, -, -, ⟨epsT, hT0, hTs, hTle⟩, -, hD⟩ := hg
  have hl : D.ntw.l (C.twI (D.nd.w i)) = D.nd.l i := by rw [← hT.twOf_eq]; exact D.ntw.twOf_l i
  have heps : twEps D (C.twI (D.nd.w i)) = Formalism.MainNotions.TwistedPlaces.epsL (D.nd.l i) := by
    rw [twEps, Formalism.MainNotions.TwistedPlaces.epsL, hl, one_div]
  refine ⟨fun π hπ => ?_, ?_⟩
  · obtain ⟨s, hs, hfin, hle⟩ := hA1 π hπ
    have h1 := hTle s hs
    have hsum : epsT s ≤ twEps D (C.twI (D.nd.w i)) :=
      le_trans (Finset.single_le_sum (fun s _ => hT0 s) ((Formalism.MainNotions.BlochKatoReduction.Gen.mem_SigG _ _ s).2 hs)) hTs
    have h0 : 0 ≤ (Formalism.MainNotions.BlochKatoReduction.Gen.nu D.ntw (C.twI (D.nd.w i)) : ℝ) + epsT s :=
      add_nonneg (Nat.cast_nonneg _) (hT0 s)
    have h2 := le_trans hle h1
    refine ⟨hfin (ne_top_of_le_ne_top ENNReal.ofReal_ne_top h1), ?_⟩
    rw [ENNReal.ofReal_le_ofReal_iff h0] at h2
    rw [← heps]
    rw [UpperTheory.KStar.nu_eq_nuL, hl] at h2
    linarith
  · rw [← heps]
    exact le_trans (mul_le_mul_of_nonneg_left hA2 (Nat.cast_nonneg _)) hD

end GlobalTheory.NLink
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChosenTwistAnnihilatesSelmerGroupsStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

theorem _root_.GlobalTheory.T.chosenTwist_annihilates_selmerGroups : ∀ (D : D7) (C : NChoice D) (I : TwIn D) (ρ : FamilyRepresentationConstants.RhoFam D), NChTie D C → TwGoodAt D C I → KillingConditions.SignatureChoiceCondition ρ C → KillingConditions.KillAt ρ := by
  first | exact @GlobalTheory.NLink.twist_kills_selmer | exact GlobalTheory.NLink.twist_kills_selmer | (intros; apply GlobalTheory.NLink.twist_kills_selmer <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsContinuousComplementFamily

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.PtCore

namespace GlobalTheory.PtCore

theorem exists_continuous_complementFamily {D : D7} (h : GlobalTheory.IndefiniteRowSideFullHecke.BlockRepresentationsSemisimple.Complement_at D) (i : D.nd.Loc)
    (r : D.nd.X i → (Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (hr : GoodR D.nd i r) :
    ∃ ρ : D.nd.X i → (Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.r) (D.nd.O i)),
      (∀ π, Continuous
        (fun g => ((ρ π g : GL (Fin D.R.r) (D.nd.O i)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)))) ∧
      ∀ π ∈ D.nd.Z i, GlobalTheory.IndefiniteRowSideFullHecke.BlockRepresentationsSemisimple.IsComplement D.nd i (r π) (ρ π) := by
  have key : ∀ π : D.nd.X i, ∃ ρ : Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.r) (D.nd.O i),
      Continuous (fun g => ((ρ g : GL (Fin D.R.r) (D.nd.O i)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i))) ∧
      (π ∈ D.nd.Z i → GlobalTheory.IndefiniteRowSideFullHecke.BlockRepresentationsSemisimple.IsComplement D.nd i (r π) ρ) := by
    intro π
    by_cases hπ : π ∈ D.nd.Z i
    · obtain ⟨ρ, hρ⟩ := h i π hπ (r π) (hr π)
      exact ⟨ρ, hρ.cont, fun _ => hρ⟩
    · exact ⟨1, continuous_const, fun h' => absurd h' hπ⟩
  choose ρ h1 h2 using key
  exact ⟨ρ, h1, h2⟩

theorem exists_ptFam : GlobalTheory.TwSys.Cheb → ∀ (D : D7), GlobalTheory.BlockComplement.GaloisRepsCusp D →
    (∀ i, ∃ r, GoodR D.nd i r) → ∃ r ρ, PtFam D r ρ := by
  intro hC D hG hr
  choose r hr using hr
  choose ρ h1 h2 using fun i =>
    exists_continuous_complementFamily (GlobalTheory.BlockComplement.complement_at hC D hG) i (r i) (hr i)
  exact ⟨r, ρ, hr, h1, h2⟩

end GlobalTheory.PtCore
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisRepsCuspidal

section

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

noncomputable section

namespace GlobalTheory.GaloisFromAdm

theorem placesOver_finite (D : D7) (l : ℕ) (hl : l ≠ 0) : (placesOver D.host.E l).Finite := by
  have h0 : Ideal.span {((l : ℕ) : 𝓞 D.host.E)} ≠ 0 := by
    simpa using hl
  exact (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.2 hv

end GlobalTheory.GaloisFromAdm

end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MainAltAltAltTer

section

@[expose] public section



section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
noncomputable section
namespace GlobalTheory.GaloisFromAdm
theorem main_alt_alt_alt : ∀ D : D7, _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D → GlobalTheory.BlockComplement.GaloisRepsCusp D := by
  intro D h i a ha π hc hr
  obtain ⟨ρ, hcont, hss, haway, -⟩ := (_root_.UpperTheory.GalS.weak' h i).1 a ha π hc hr
  refine ⟨ρ, hcont, hss, ?_⟩
  have hfin := placesOver_finite D (D.nd.l i) (Fact.out : (D.nd.l i).Prime).ne_zero
  filter_upwards [D.naut.locG_unr_ae π, hfin.eventually_cofinite_notMem] with w hu hw B φ hB hφ
  rw [D.naut.wdOf_frob i ρ w hw hcont (by rw [(haway w hw).eq_of_unr ((D.naut.unr_tw _ _).2 hu)]; exact (D.naut.unr_tw _ _).2 hu) B φ hB hφ,
    (haway w hw).eq_of_unr ((D.naut.unr_tw _ _).2 hu)]
  rfl
end GlobalTheory.GaloisFromAdm
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GaloisRepsCuspidal

section

@[expose] public section



section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

theorem _root_.GlobalTheory.T.galoisRepsCusp_of_adm2 : ∀ D : D7, _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D → GlobalTheory.BlockComplement.GaloisRepsCusp D := by
  first | exact @_root_.GlobalTheory.GaloisFromAdm.main_alt_alt_alt | exact _root_.GlobalTheory.GaloisFromAdm.main_alt_alt_alt | (intros; apply _root_.GlobalTheory.GaloisFromAdm.main_alt_alt_alt <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsHubData

section

@[expose] public section



section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
namespace GlobalTheory.HubX
theorem exists_canonical_hubData_with_bounds : GlobalTheory.TwSys.Cheb → ∀ (D : D7) (L : SizeData₂ D) (HW : HWOf D.loc) (R : KillingConditions.RowK), _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D → _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → ∀ (e' : FamilyRepresentationConstants.RFam D → FamilyRepresentationConstants.RhoFam D → D.nd.Loc → HeightOneSpectrum (𝓞 D.host.E) → ℕ) (exc : FamilyRepresentationConstants.RhoFam D → Finset ℕ) (I : TwIn D), ∃ X : KillingConditions.HubData D, GlobalTheory.HubX.Canon L HW R X ∧ X.e' = e' X.r X.ρ ∧ X.exc = exc X.ρ ∧ X.I = I ∧ (∀ i, GoodR D.nd i (X.r i)) ∧ (0 ≤ L.etaSz → (X.eta : ℝ) ≤ 2 * L.etaSz) ∧ ∀ i, GlobalTheory.HubLoc.cBnum (D.nd.l i) ⌊2 * L.sc.b⌋₊ D.R.t (4 * D.R.n * D.R.nV) ≤ X.cB i := by
  intro hC D L HW R h2 h41 e' exc I
  obtain ⟨r, ρ, h⟩ := GlobalTheory.PtCore.exists_ptFam hC D (_root_.GlobalTheory.T.galoisRepsCusp_of_adm2 D h2) (fun i => (h41 i).1.2)
  have hc := canon_ourX L HW R r ρ (e' r ρ) (exc ρ) I h
  refine ⟨ourX L HW R r ρ (e' r ρ) (exc ρ) I, hc, rfl, rfl, rfl, hc.fam.good, ?_, ?_⟩
  · intro hL
    rw [hc.eta]
    have := Nat.floor_le hL
    linarith
  · intro i
    rw [hc.cB]
    exact le_refl _
end GlobalTheory.HubX
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsSetupLarge

section

@[expose] public section



section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
namespace GlobalTheory.NLink
theorem exists_setup_large_alt : Hypotheses₂ → ∀ {eps : ℝ} (Fm : FamP eps), ∀ (C C₂ : ℝ) (CT : ℕ), TwGood Fm → _root_.GlobalTheory.NLink.FactsFAlt Fm C CT → ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x), TwistedPlaces.ShaFinOdd (Fm.D x i) → ∀ exc : Finset ℕ, ∃ (HW : HWOf (Fm.D x i).loc) (F : FonOf (Fm.D x i).loc (Fm.D x i).locA HW) (_ : CmpOf (Fm.D x i).loc (Fm.D x i).locA HW F) (X : KillingConditions.HubData (Fm.D x i)), X.exc = exc ∧ _root_.Formalism.MainNotions.AdmissibleParameterJ.AdmJAlt (Fm.L x i) ∧ _root_.GlobalTheory.NLink.SetupAlt (Fm.L x i) (Fm.ex x hx i).nch HW X C₂ := by
  intro hP eps Fm C C₂ CT hTw hF
  obtain ⟨i0⟩ := Fm.Ix_zero
  have he : 0 < eps := Fm.L_eps 0 i0 ▸ (Fm.L 0 i0).sc.eps_pos
  obtain ⟨xa, hxa⟩ := GlobalTheory.HTW.admissibleParameters_of_large_scale eps (Fm.PK.getD 7 0) he
  obtain ⟨xb, hxb⟩ := GlobalTheory.T.specialPrimes_small_along_family Fm 1 le_rfl
  obtain ⟨xc, hxc⟩ := hTw
  refine ⟨max xa (max xb xc), fun x hx hx1 i hsha exc => ?_⟩
  have hxa' : xa ≤ x := le_trans (le_max_left _ _) hx
  have hxb' : xb ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hxc' : xc ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  obtain ⟨-, N0, S, hgood⟩ := hxc x hxc' hx1 i
  obtain ⟨hfa, -⟩ := hF x hx1 i
  obtain ⟨HW, F, ⟨Cm⟩⟩ := GlobalTheory.T.exists_wachFunctor_comparison_of_bhattScholze hP.bs (Fm.D x i)
  have hCLw : (Fm.params x hx1 i).CLw ≤ Fm.PK.getD 7 0 := by
    rw [← Fm.params_K x hx1 i]
    exact le_refl _
  have hsx : xa ≤ (Fm.L x i).sc.x := by rw [Fm.L_x x i hx1]; exact hxa'
  obtain ⟨hpar, hpar67⟩ := hxa (Fm.D x i) (Fm.L x i) (Fm.params x hx1 i) (Fm.L_eps x i) hCLw hsx
  obtain ⟨X, hcan, -, hexc, hI, -⟩ := _root_.GlobalTheory.HubX.exists_canonical_hubData_with_bounds GlobalTheory.Published.cheb_holds (Fm.D x i) (Fm.L x i) HW (rowC C₂)
    hfa.adm.1.1.2.2.2.1 hfa.Conclusion1.1 (fun _ _ _ _ => 0) (fun _ => exc) ⟨twE Fm x hx1 i, N0, S⟩
  obtain ⟨-, hbig, hsplit, -⟩ := hxb x hxb' hx1 i
  have hrow : GlobalTheory.PtCore.GoodPtRow (Fm.D x i) :=
    GlobalTheory.Proof.LocalGlobalAssembly.main _ hfa.adm.1.1.1 hfa.Conclusion1.2.2 hfa.Conclusion2.2.2
  have h6 := GlobalTheory.JointSix.main GlobalTheory.Published.cheb_holds (Fm.D x i) (Fm.ex x hx1 i).nch X.r X.ρ hcan.fam hfa.nct hfa.trip
    hfa.same hrow (GlobalTheory.PtCore.residualAbsIrredGoodPoint_of_residualIrred _ hfa.rhoBar)
  have hkill : KillingConditions.KillAt X.ρ := GlobalTheory.T.chosenTwist_annihilates_selmerGroups (Fm.D x i) (Fm.ex x hx1 i).nch X.I X.ρ hfa.nct (hI ▸ hgood) h6
  exact ⟨HW, F, Cm, X, hexc, hfa.admJ _ hpar, ⟨hfa, hcan, hpar, hpar67, hbig, hsplit, hkill, hsha⟩⟩
end GlobalTheory.NLink
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsSetupLargeStatement

section

@[expose] public section



section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

theorem _root_.GlobalTheory.T.exists_hubData_admJ_setup : Hypotheses₂ → ∀ {eps : ℝ} (Fm : FamP eps), ∀ (C C₂ : ℝ) (CT : ℕ), TwGood Fm → _root_.GlobalTheory.NLink.FactsFAlt Fm C CT → ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x), TwistedPlaces.ShaFinOdd (Fm.D x i) → ∀ exc : Finset ℕ, ∃ (HW : HWOf (Fm.D x i).loc) (F : FonOf (Fm.D x i).loc (Fm.D x i).locA HW) (_ : CmpOf (Fm.D x i).loc (Fm.D x i).locA HW F) (X : KillingConditions.HubData (Fm.D x i)), X.exc = exc ∧ _root_.Formalism.MainNotions.AdmissibleParameterJ.AdmJAlt (Fm.L x i) ∧ _root_.GlobalTheory.NLink.SetupAlt (Fm.L x i) (Fm.ex x hx i).nch HW X C₂ := by
  first | exact @_root_.GlobalTheory.NLink.exists_setup_large_alt | exact _root_.GlobalTheory.NLink.exists_setup_large_alt | (intros; apply _root_.GlobalTheory.NLink.exists_setup_large_alt <;> assumption)
end
end
end
