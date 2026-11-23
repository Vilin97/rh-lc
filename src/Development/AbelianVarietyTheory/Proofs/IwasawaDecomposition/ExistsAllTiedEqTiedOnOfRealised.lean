module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSplittingCharacterSelf
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicWeilRepresentationWithRulesExists
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
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterInfinityExponentGroupLaws
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasChr
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsDetRoot
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsInfFamFamily
public import Formalism.LocalToGlobal.BesselHermitianTheta.MinfDensity
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGrpDataMapHaar
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyFockModelUnitaryDualPairStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPlaceStdParamIsParam
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRealisedE
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsThetaChrTied
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankOrth
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueIsStdChar
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoordSymm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsWeilDatumOOfRankEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToTWsmallZero
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GelfConstSmul
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasureLeOfCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PetIntOfCuspRapidDecay
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumNormEmb
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToTWsmallZero
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.BlattnerShiftsSignedParameters
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.IsTypeAtCentral
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsWeilOnOfCoord
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumEqTraceOriented
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicWeilRepresentationWithRulesExistsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.adelicWeilRepresentation_with_rules_exists : GlobalTheory.Published.WeilRepresentationUnitaryPair → ∀ D : D7, WeilEx D := by
  first | exact @GlobalTheory.Mem.WeilExists.weilEx_of_weilRepresentation | exact GlobalTheory.Mem.WeilExists.weilEx_of_weilRepresentation | (intros; apply GlobalTheory.Mem.WeilExists.weilEx_of_weilRepresentation <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqualRankSplittingCharsAdmissibleMulRight

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.WeilEqRank

variable {D : D7}

theorem equalRankSplittingCharsAdmissible_mul_right {V W : HSp D} {χ χ' ν : IdC D} (h : AdmE V W χ χ') (hν : IsHC D ν) (h0 : ResEta D ν 0) :
    AdmE V W χ (χ' * ν) :=
  ⟨h.1, h.2.1, (GlobalTheory.Mem.HeckeExp.hcSubgroup D).mul_mem (show χ' ∈ GlobalTheory.Mem.HeckeExp.hcSubgroup D from h.2.2.1)
    (show ν ∈ GlobalTheory.Mem.HeckeExp.hcSubgroup D from hν), h.2.2.2.1, resEta_mul h.2.2.2.2 h0⟩

theorem equalRankSplittingCharsAdmissible_mul_left {V W : HSp D} {χ χ' ν : IdC D} (h : AdmE V W χ χ') (hν : IsHC D ν) (h0 : ResEta D ν 0) :
    AdmE V W (χ * ν) χ' :=
  ⟨h.1, (GlobalTheory.Mem.HeckeExp.hcSubgroup D).mul_mem (show χ ∈ GlobalTheory.Mem.HeckeExp.hcSubgroup D from h.2.1)
    (show ν ∈ GlobalTheory.Mem.HeckeExp.hcSubgroup D from hν), h.2.2.1, resEta_mul h.2.2.2.1 h0, h.2.2.2.2⟩

theorem exists_weilFun_eqRank : ∀ D : D7, WeilEx D → WeilOnEqEx D → WeilTwEq D → ∀ ψ, IsStdChar D ψ (-1) →
    ∃ Wf : WeilFun D ψ, Wf.EqRank := by
  classical
  intro D h1 h2 h3 ψ hψ
  obtain ⟨W₀⟩ := h1 ψ hψ
  have key : ∀ (V W : HSp D) (χ χ' : IdC D), ∃ om : GA D V × GA D W →* Module.End ℂ (ThS ψ V W),
      (V.rank ≠ W.rank → om = W₀.om V W χ χ') ∧ (AdmE V W χ χ' → IsWeilOn ψ V W χ χ' om) := fun V W χ χ' => by
    by_cases h : AdmE V W χ χ'
    · obtain ⟨om, hom⟩ := h2 ψ hψ V W χ χ' h
      exact ⟨om, fun hne => absurd h.1 hne, fun _ => hom⟩
    · exact ⟨W₀.om V W χ χ', fun _ => rfl, fun k => absurd k h⟩
  choose om hne heq using key
  refine ⟨⟨om, fun V W χ χ' ha => ?_, fun V W χ χ' ha => ?_, fun V W χ χ' ha => ?_, fun V W χ χ' ha => ?_,
    fun V W χ χ' ha => ?_, fun V W χ χ' ν ha => ?_, fun V W χ χ' ν ha => ?_, fun V W χ χ' ha => ?_,
    fun V W χ χ' ha => ?_⟩, heq, fun V W χ χ' ν ha hν h0 => ?_, fun V W χ χ' ν ha hν h0 => ?_⟩
  · rw [hne V W χ χ' ha.1]; exact W₀.om_heis V W χ χ' ha
  · rw [hne V W χ χ' ha.1]; exact W₀.om_aut V W χ χ' ha
  · rw [hne V W χ χ' ha.1]; exact W₀.om_cont V W χ χ' ha
  · rw [hne V W χ χ' ha.1]; exact W₀.om_unit V W χ χ' ha
  · rw [hne V W χ χ' ha.1]; exact W₀.om_split V W χ χ' ha
  · rw [hne V W χ χ' ha.1, hne V W χ (χ' * ν) ha.1]; exact W₀.twW V W χ χ' ν ha
  · rw [hne V W χ χ' ha.1, hne V W (χ * ν) χ' ha.1]; exact W₀.twV V W χ χ' ν ha
  · rw [hne V W χ χ' ha.1, hne W V χ' χ ha.1.symm]; exact W₀.om_swap V W χ χ' ha
  · rw [hne V W χ χ' ha.1]; exact W₀.om_unr V W χ χ' ha
  · exact (h3 ψ hψ V W χ χ' ν ha hν h0 _ (heq V W χ χ' ha)).1 _ (heq V W χ (χ' * ν) (equalRankSplittingCharsAdmissible_mul_right ha hν h0))
  · exact (h3 ψ hψ V W χ χ' ν ha hν h0 _ (heq V W χ χ' ha)).2 _ (heq V W (χ * ν) χ' (equalRankSplittingCharsAdmissible_mul_left ha hν h0))

end GlobalTheory.Mem.WeilEqRank

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRealPlaceRecordTied

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem exists_realPlace_record_tied :
    (∀ (p q : ℕ) (T : GrpData p q) (lam : Ix p q → ℚ), IsParam lam → ∃ R : DSRep T, HasParam R lam) →
    ∀ D : D7, ∃ A : ProvA, ProvisionCompatibility D A := by
  intro H D
  classical
  choose grp hgrp using fun p q : ℕ =>
    GlobalTheory.DetSqrtCover.exists_grpData_map_haar p q (D.cd.cd p q) (D.cd.haar p q)
  have key : ∀ (p q : ℕ) (lam : Ix p q → ℚ), ∃ R : DSRep (grp p q),
      IsParam lam → HasParam R lam := by
    intro p q lam
    by_cases h : IsParam lam
    · obtain ⟨R, hR⟩ := H p q (grp p q) lam h
      exact ⟨R, fun _ => hR⟩
    · obtain ⟨R, -⟩ := H p q (grp p q) _ (realPlaceStdParam_isParam p q)
      exact ⟨R, fun h' => absurd h' h⟩
  choose ds hds using key
  exact ⟨⟨grp, fun p q r s => Classical.choice (GlobalTheory.T.nonempty_fockModel_unitary_dual_pair p q r s _ _ _), ds⟩,
    ⟨hgrp, fun p q lam h => by first | exact hds p q lam h | exact fun _ => hds p q lam h⟩⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTow

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

namespace GlobalTheory.TowerSpaces

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_tow : ∀ D : D7, ∃ Tw : Tow D, (∀ j, j < D.R.m → HEq (Tw.iXYs D.R.t j) (D.sp.iXY j)) ∧
    HEq (Tw.iYXm D.R.t) (D.sp.iX'.comp D.sp.eYm.symm.toLinearMap) := by
  intro D
  obtain ⟨Tw⟩ := nonempty_tow (GlobalTheory.WittLow.wittLowEx D)
  exact ⟨Tw, Tw.iXYs_rec, Tw.iYXm_rec⟩

end GlobalTheory.TowerSpaces
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftAutEq

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Lift

theorem liftAutEq : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, LiftAutEq D := by
  intro hP D θ hθ ψ hψ V W χ χ' ha om hom μ 𝓕 hq Φ F hF
  obtain ⟨omO, H, e⟩ := GlobalTheory.Mem.WeilOriented.exists_isWeilDatumO_of_rank_eq D ψ hψ V W χ χ' om ha hom
  obtain ⟨E, -, -, hE, -, -, -, h7, -⟩ := GlobalTheory.OrientedCoord.exists_coord D V W ha.1.le
  have hf := (h7 ψ Φ.1).2 (mem_ThS.1 Φ.2)
  simp only [hE] at hf
  have e' : ∀ g h, (om (g, h) Φ).1 0 = thKer ψ V W omO ⟨fun x => Φ.1 (toTWsmall V W x), hf⟩ g h := fun g h => by
    have := congrFun (e (g, h) Φ) 0
    rw [toTWsmall_zero] at this
    exact this.symm
  simp only [e']
  exact (isKerSys_thKer hθ hψ (GlobalTheory.Ker.isWeak_of_datum H) H.om_cont).lift hP hθ hq hF _

end GlobalTheory.Mem.Lift
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypAddOfDiscreteSeries

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.TypeSum in
theorem GlobalTheory.TypeSum.typAdd_of_discreteSeries : ∀ D : D7, (∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam → ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.MainNotions.S.IsDS ε lam σ) → (∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam → ∀ (H H' : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')), Formalism.MainNotions.S.IsDS ε lam σ → Formalism.MainNotions.S.IsDS ε lam σ' → ∃ U : H ≃ₗᵢ[ℂ] H', ∀ g ∈ Formalism.MainNotions.S.UJset ε, ∀ v, U (σ g v) = σ' g (U v)) → TypAdd D := by
  intro D hex huniq θ hθ V hV τ S hS
  obtain ⟨lam₀, ε₀, hE₀, hP₀, hp, hq⟩ := hS
  refine ⟨(GlobalTheory.TypeAtTest.isTypeAt_zero θ V).2 ?_, fun φ φ' _ _ h h' => ?_⟩
  · obtain ⟨H, i1, i2, σ, hσ⟩ := hex _ ε₀ lam₀ hP₀
    obtain ⟨P, h1, h2⟩ := GlobalTheory.Published.exists_frame_of_hasSignature (hV (tauE D τ)) ε₀ hp hq
    exact ⟨H, i1, i2, σ, lam₀, ε₀, P, hE₀, hσ, h1, h2⟩
  obtain ⟨H, i1, i2, σ, lam, ε, P, hE, hσ, hP, hG, hx⟩ := h
  obtain ⟨H', j1, j2, σ', lam', ε', P', hE', hσ', hP', hG', hx'⟩ := h'
  obtain ⟨rfl, rfl⟩ := GlobalTheory.SignedParTest.isEnum_unique hE hE₀
  obtain ⟨rfl, rfl⟩ := GlobalTheory.SignedParTest.isEnum_unique hE' hE₀
  obtain ⟨U, hU⟩ := huniq _ _ _ hP₀ H' H σ' σ hσ' hσ
  refine ⟨H, i1, i2, σ, _, _, P, hE, hσ, hP, hG, fun x => ?_⟩
  exact hasTypeAll_iff.1 (hasTypeAll_add_of_equiv hσ.2.2.1 U hU hP hP' hG hG'
    (f := fun g => φ (x * atTau θ V τ g)) (f' := fun g => φ' (x * atTau θ V τ g))
    (hasTypeAll_iff.2 (hx x)) (hasTypeAll_iff.2 (hx' x)))
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilOnEqExOfKnownTheorem

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.OrientedCoord GlobalTheory.Mem.WeilTransport
open scoped TensorProduct

namespace GlobalTheory.Mem.WeilEqRank

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem isCoord_coord (S T : HSp D) (hr : S.rank ≤ T.rank) : IsCoord S T S T (coord S T) := {
  cont := continuous_coord S T
  cont' := continuous_coord_symm S T
  sympl := symplOH_eq S T hr
  rat x := by
    constructor
    · rintro ⟨γ, rfl⟩
      exact ⟨(γ * S.gram⁻¹)ᵀ, (coord_ratW S T γ).symm⟩
    · rintro ⟨γ, hγ⟩
      have hγ' : ratW S T γ = coord S T x := hγ
      refine ⟨γᵀ * S.gram, ?_⟩
      change ratW T S _ = x
      rw [← coord_symm_ratW, hγ', AddEquiv.symm_apply_apply]
  inf x := ⟨coord_map_zero S T _ x, fun h => by
    simpa only [AddEquiv.symm_apply_apply] using coord_symm_map_zero S T _ _ h⟩
  fin x := ⟨coord_map_zero S T _ x, fun h => by
    simpa only [AddEquiv.symm_apply_apply] using coord_symm_map_zero S T _ _ h⟩
  part a x h i j := by
    show a * ∑ k, x j k * incA D (S.gram⁻¹ k i) = ∑ k, x j k * incA D (S.gram⁻¹ k i)
    simp only [Finset.mul_sum, ← mul_assoc, h] }

theorem weilOnEqEx_of_weilRepresentation : GlobalTheory.Published.WeilRepresentationUnitaryPair → ∀ D : D7, WeilOnEqEx D := by
  intro hP D ψ hψ V W χ χ' ⟨hr, h1, h2, h3, h4⟩
  obtain ⟨om, H⟩ := hP D ψ V W χ χ' hψ h1.1 h2.1 h3 h4
  refine exists_isWeilOn_of_coord (isCoord_coord V W hr.le) H (MonoidHom.id _) continuous_id
    (fun g h x => (GlobalTheory.OrientedSmall.bridgeSmall D V W hr.le).2 g h x) (fun _ a _ b => ⟨a, b⟩)
    fun e g h hg hh x y hx hy => ⟨x, y, hg, hh, hx, hy, ?_⟩
  unfold splitFacO splitFac
  rw [if_pos hr.le]

end GlobalTheory.Mem.WeilEqRank

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAllTiedEqTiedOnOfRealised

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Th

theorem exists_allTied_eqTied_on_of_realised {D : D7} (ht : TypAdd D)
    (hW : ∀ ψ, IsStdChar D ψ (-1) → ∃ Wf : WeilFun D ψ, Wf.EqRank) (hT : Nonempty (Tow D)) (hX : RealisedExE D)
    (hA : ∃ A : ProvA, ProvisionCompatibility D A) (C : Formalism.L2.Host.CharFrame D) (xi : D.what₂.Tup → Formalism.L2.Host.HChar D.host.E)
    (U : Set D.what₂.Tup) (hr : RealTied D) (hR : (∀ θ : InfF D, IsInfFam θ → ∀ ψ, IsStdChar D ψ (-1) → ∀ Wf : WeilFun D ψ, ∃ Rc : RecFun D θ ψ, Rc.ChrIs C xi ∧ Rc.IoTie Wf ∧ ∀ μ ∈ U, ∀ j, j ≤ D.R.m → ∀ x y : D.what₂.Mult μ j, GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt (D.sp.Y j) (Rc.mY μ j * Rc.petC (D.sp.Y j)) (fun h => star ((Rc.row μ j x).1 h) * (Rc.row μ j y).1 h) (inner ℂ x y))) :
    ∃ X : ThetaX D, X.TieIo ∧ (∀ μ ∈ U, ∀ j, j ≤ D.R.m → ∀ x y : D.what₂.Mult μ j,
      X.petY μ j ((X.rowAF μ j x : X.cusp _) : X.AF _) (X.rowAF μ j y) = inner ℂ x y) ∧
      ∃ (A : ProvA) (a : AllTied D X A), WeilThetaCompatibility a.W ∧
      ∀ (nch : NChoice D) (Tp : Formalism.L2.Host.TupTied D C nch), Tp.xi = xi →
        ∃ H : Formalism.L2.Host.ThetaChrTied D C nch Tp X, ∀ c, Formalism.IndefR.Links.ChrEq (a.T.eChr c) (H.eChr c) := by
  obtain ⟨θ, hθ⟩ := GlobalTheory.Member.exists_isInfFam_family D
  obtain ⟨ψ, hψ, -⟩ := GlobalTheory.StdAdelicChar.existsUnique_isStdChar D (-1) (Or.inr rfl)
  obtain ⟨Wf, hE⟩ := hW ψ hψ
  obtain ⟨Tw⟩ := hT
  obtain ⟨Rc, hc, hio, hi⟩ := hR θ hθ ψ hψ Wf
  obtain ⟨X, T, W, B, rfl, h⟩ := hX θ hθ ψ hψ Wf hE Tw Rc
  obtain ⟨A, hA⟩ := hA
  obtain ⟨K, -⟩ := h.kfin
  refine ⟨X, h.tieIo hio, fun μ hμ j hj x y => ?_, A, ⟨T, h.afTiedSm, h.typTied ht, W, h.weilUnrTied, K, h.phiUp, B, hr, hA⟩,
    h.eqTied, fun nch Tp e => ?_⟩
  · obtain ⟨⟨m, hm⟩, h2⟩ := hi μ hμ j hj x y
    have e := T.pet _ (D.sp.Y_sig j) m.1 m.2 hm (X.rowAF μ j x) (X.rowAF μ j y)
    unfold ThetaX.petY
    rw [e, (h2 m hm).2, h.row, h.row, h.mY, ← h.petC_eq]
    simp only [ThetaTied.petC, Complex.ofReal_mul, mul_assoc]
  · exact GlobalTheory.TowerCharRead.exists_thetaChrTied D C nch Tp X T (e ▸ h.chrRead hc)

theorem exists_allTied_eqTied_on : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.CuspRapidDecay → (∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam → ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.MainNotions.S.IsDS ε lam σ) → (∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam → ∀ (H H' : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')), Formalism.MainNotions.S.IsDS ε lam σ → Formalism.MainNotions.S.IsDS ε lam σ' → ∃ U : H ≃ₗᵢ[ℂ] H', ∀ g ∈ Formalism.MainNotions.S.UJset ε, ∀ v, U (σ g v) = σ' g (U v)) → (∀ (p q : ℕ) (T : GrpData p q) (lam : Ix p q → ℚ), IsParam lam → ∃ R : DSRep T, HasParam R lam) → ∀ (D : D7) (C : Formalism.L2.Host.CharFrame D) (xi : D.what₂.Tup → Formalism.L2.Host.HChar D.host.E) (U : Set D.what₂.Tup), RealTied D → (∀ θ : InfF D, IsInfFam θ → ∀ ψ, IsStdChar D ψ (-1) → ∀ Wf : WeilFun D ψ, ∃ Rc : RecFun D θ ψ, Rc.ChrIs C xi ∧ Rc.IoTie Wf ∧ ∀ μ ∈ U, ∀ j, j ≤ D.R.m → ∀ x y : D.what₂.Mult μ j, GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt (D.sp.Y j) (Rc.mY μ j * Rc.petC (D.sp.Y j)) (fun h => star ((Rc.row μ j x).1 h) * (Rc.row μ j y).1 h) (inner ℂ x y)) → ∃ X : ThetaX D, X.TieIo ∧ (∀ μ ∈ U, ∀ j, j ≤ D.R.m → ∀ x y : D.what₂.Mult μ j, X.petY μ j ((X.rowAF μ j x : X.cusp _) : X.AF _) (X.rowAF μ j y) = inner ℂ x y) ∧ ∃ (A : ProvA) (a : AllTied D X A), WeilThetaCompatibility a.W ∧ ∀ (nch : NChoice D) (Tp : Formalism.L2.Host.TupTied D C nch), Tp.xi = xi → ∃ H : Formalism.L2.Host.ThetaChrTied D C nch Tp X, ∀ c, Formalism.IndefR.Links.ChrEq (a.T.eChr c) (H.eChr c) := by
  intro hW hC hex huniq hds D C xi U hr hR
  exact exists_allTied_eqTied_on_of_realised (GlobalTheory.TypeSum.typAdd_of_discreteSeries D hex huniq)
    (GlobalTheory.Mem.WeilEqRank.exists_weilFun_eqRank D (GlobalTheory.T.adelicWeilRepresentation_with_rules_exists hW D) (GlobalTheory.Mem.WeilEqRank.weilOnEqEx_of_weilRepresentation hW D)
      (GlobalTheory.Mem.WeilTwist.weilTwEq D))
    ((GlobalTheory.TowerSpaces.exists_tow D).elim fun Tw _ => ⟨Tw⟩)
    (GlobalTheory.Mem.TrueRecordEq.exists_realisedE D (petInt_of_cuspRapidDecay hC D) (GlobalTheory.Mem.TopIntegrand.topInt hC D)
      (GlobalTheory.Mem.BesselIntegrable.besInt hC D) (GlobalTheory.Mem.Lift.liftAut hC D) (GlobalTheory.Mem.Lift.liftAutEq hC D))
    (GlobalTheory.exists_realPlace_record_tied hds D) C xi U hr hR

end GlobalTheory.Mem.Th
end
end
