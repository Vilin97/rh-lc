module

public import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BoundAtTwoThreeFamilyFon
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BoundAtPointAllLocalisationsOfObjectConditionsAlStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonPlacePartLocalBoundLeMiddleRangeStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitCaseBoundAtPointOfAdmittedItemsStatement
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
public import Development.AutomorphicArithmetic.CyclotomicBounds.SmallFacts
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
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsFurtherBis
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsFurtherRestStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SetPointGood
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SplitPrimeHyps

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StarInequalityRowsADOfGlobalTheorems

section

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLink

theorem starAD_of_global : ∀ (D : D7) (L : SizeData₂ D) (HW : HWOf D.loc) (X : KillingConditions.HubData D) (R : KillingConditions.RowK),
    KillingConditions.DataAD L HW X R → KillingConditions.StepAD L X → TruncatedSeriesCountingIdentities.IntegralityFromMetric D →
    (∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
      (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i) (ep : Bool) (e' : ℕ)
      (c0 : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ), EmbeddingTypes.admitted i r ρ π dc ep e' c0 cB →
      (D.nd.l i ≠ D.host.g 0 → D.nd.l i ≠ D.host.g 1 → π ∈ D.nd.Z i → TruncatedSeriesCountingIdentities.admG2 i r ρ π) →
      EmbeddingTypes.aux₃ i r ρ π dc ep e' c0 cB) →
    (∀ i, D.nd.l i ∉ TwistedPlaces.gset D → ∀ π ∈ D.nd.Zgood i, TruncatedSeriesCountingIdentities.admG2 i (X.r i) (X.ρ i) π) →
    KillingConditions.KillAt X.ρ → TwistedPlaces.ShaFinOdd D →
    KillingConditions.StarAD L X := by
  classical
  intro D L HW X R hD hS h09 h78 hG2 hK hSha
  intro i hTw hg hR π hπ
  have hl : (D.nd.l i).Prime := (D.nd.lPrime i).out
  have hR' := hR
  obtain ⟨h23, hqd, -⟩ := hR'
  have hsm : D.nd.l i ∉ D.host.small := fun h => h23 (Or.inl h)
  have hl2 : D.nd.l i ≠ 2 := UpperTheory.Small.ne_two D.host hsm
  have hl3 : D.nd.l i ≠ 3 := fun h => h23 (Or.inr h)
  have hlq : D.nd.l i ≠ D.host.q := fun h => hqd (Or.inl h)
  have hld : D.nd.l i ≠ D.host.d := fun h => hqd (Or.inr h)
  have hg0 : D.nd.l i ≠ D.host.g 0 := fun h => hg (by simp [TwistedPlaces.gset, h])
  have hg1 : D.nd.l i ≠ D.host.g 1 := fun h => hg (by simp [TwistedPlaces.gset, h])
  have hZ : π ∈ D.nd.Z i := (D.Z_tie i π).2 ((D.Zgood_tie i π).1 hπ).1
  obtain ⟨hK1, hK2⟩ := hK i hTw
  obtain ⟨hFin, -⟩ := hK1 π hπ
  have hodd : Odd (D.nd.l i) := hl.odd_of_ne_two hl2
  have hShaT : ∀ e ∈ Finset.Ioo 0 D.R.t, GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ) < ⊤ := by
    intro e he
    rw [Finset.mem_Ioo] at he
    exact lt_top_iff_ne_top.2 (@hSha (D.nd.l i) (D.nd.lPrime i) e he.1 he.2)
  have hIco : Finset.Ico 1 D.R.t = Finset.Ioo 0 D.R.t := by
    ext e; simp only [Finset.mem_Ico, Finset.mem_Ioo]; omega
  have hVV : TwistedPlaces.VVr D (D.nd.l i) = ((∑ e ∈ Finset.Ioo 0 D.R.t, D.what₂.shaLen (D.nd.l i) e : ℚ) : ℝ) := by
    unfold TwistedPlaces.VVr
    simp only [Rows.Data.VV, hIco]
  have hcls : TwistedPlaces.SplitK D (D.nd.l i) ∨ TwistedPlaces.InertK D (D.nd.l i) := by
    unfold TwistedPlaces.SplitK TwistedPlaces.InertK Host.cls primeClass
    simp only [hsm, hlq, hld, if_false]
    split_ifs <;> simp
  rcases hcls with hsp | hin
  ·
    obtain ⟨ep, hdecl, hram, hAdm⟩ := hS.a78 i hTw hg hR hsp
    have hA := hAdm π hπ
    have hL : EmbeddingTypes.hypL i := ⟨hl.two_le, Or.inl hsp, fun _ => hram, hg0, hg1⟩
    have hzeta : ∀ v ∈ D.nd.Q i, D.nd.zeta i v ≠ 1 := fun v hv => (hA.2.2.2.2.2.1 v (Or.inr hv)).2.2.1 hv
    obtain ⟨-, -, hB⟩ := h78 i (X.r i) (X.ρ i) π (X.dc i) ep (X.eS i) (X.c0 i) (X.cB i) hA
      (fun _ _ _ => hG2 i hg π hπ) hL hdecl hZ
    have hT := hB hFin hShaT hzeta
    have hpl : (↑((X.dc i).row ∪ (X.dc i).col) : Set _) = placesOver D.host.E (D.nd.l i) := by
      ext v
      rw [Finset.coe_union, Set.mem_union, Finset.mem_coe, Finset.mem_coe]
      exact (X.dc i).cover v
    have hsum : TwistedPlaces.sumOver D (D.nd.l i) (X.len0 i π) =
        ((∑ u ∈ (X.dc i).col, (2 * (N.locDeg D.host.E u : ℚ) * D.R.m + 1) * (X.eS i : ℚ) : ℚ) : ℝ) := by
      unfold TwistedPlaces.sumOver
      rw [← hpl, finsum_mem_coe_finset]
      rw [Finset.sum_congr rfl fun w _ => hD.len0S i hsp π w]
      rw [← Rat.cast_sum]
      congr 1
      simp only [lenA]
      rw [Finset.sum_ite_mem, Finset.union_inter_cancel_right]
    have hBB := hD.error_bound_split_eq i hsp π
    have hcol : (∑ u ∈ (X.dc i).col,
        ((X.eS i : ℚ) + (N.locDeg D.host.E u : ℚ) * D.R.m * ((X.eS i : ℚ) + D.nd.vdel i) + 2 * D.nd.vdel i +
          Br.h0W i u (X.ρ i) π + (N.locDeg D.host.E u : ℚ) * D.R.m * (X.eS i : ℚ) + D.R.r * (X.c0 i u : ℚ))) =
        (∑ u ∈ (X.dc i).col, (2 * (N.locDeg D.host.E u : ℚ) * D.R.m + 1) * (X.eS i : ℚ)) +
        ∑ u ∈ (X.dc i).col, ((N.locDeg D.host.E u : ℚ) * D.R.m * D.nd.vdel i + 2 * D.nd.vdel i +
          Br.h0W i u (X.ρ i) π + D.R.r * (X.c0 i u : ℚ)) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun u _ => by ring
    unfold EmbeddingTypes.boundSplit at hT
    rw [hcol] at hT
    have hT' := (Rat.cast_le (K := ℝ)).2 hT
    rw [hsum, hBB, hVV]
    unfold localErrorBoundPlaces TwistedPlaces.vhE
    push_cast at hT' hK2 ⊢
    linarith
  ·
    have hA := hS.a09 i hTw hg hR hin π hπ
    have hT := h09 i (X.r i) (X.ρ i) π (X.dc i) (X.lenRow i) (X.e' i) (X.cB i) (hS.goodR i) hA hg0 hg1 hZ hFin hShaT
    have hcol := hD.col i hin
    have hrow : (↑(X.dc i).row : Set _) = placesOver D.host.E (D.nd.l i) := by
      ext v
      have := (X.dc i).cover v
      rw [hcol] at this
      simpa using this
    have hsum : TwistedPlaces.sumOver D (D.nd.l i) (X.len0 i π) = ((∑ w ∈ (X.dc i).row, X.lenRow i w : ℚ) : ℝ) := by
      unfold TwistedPlaces.sumOver
      rw [← hrow, finsum_mem_coe_finset, Rat.cast_sum]
      exact Finset.sum_congr rfl fun w _ => hD.len0I i hin π w
    have hW : ∑ w ∈ (X.dc i).row ∪ (X.dc i).col, TruncatedSeriesCountingIdentities.lenW i (X.ρ i) π (X.dc i) (X.lenRow i) (X.e' i) w =
        ∑ w ∈ (X.dc i).row, X.lenRow i w := by
      rw [hcol, Finset.union_empty]
      refine Finset.sum_congr rfl fun w _ => ?_
      simp [TruncatedSeriesCountingIdentities.lenW, hcol]
    rw [hW] at hT
    have hT' := (Rat.cast_le (K := ℝ)).2 hT
    rw [hsum, hD.error_bound_inert_eq i hin π, hVV]
    unfold KillingConditions.localErrorBoundDecomposition TwistedPlaces.vhE
    push_cast at hT' hK2 ⊢
    linarith

end GlobalTheory.NLink
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StarInequalityRowsADOfGlobalTheoremsStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

theorem _root_.GlobalTheory.T.starInequality_rowsAD_of_global_theorems : ∀ (D : D7) (L : SizeData₂ D) (HW : HWOf D.loc) (X : KillingConditions.HubData D) (R : KillingConditions.RowK), KillingConditions.DataAD L HW X R → KillingConditions.StepAD L X → TruncatedSeriesCountingIdentities.IntegralityFromMetric D → (∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i) (ep : Bool) (e' : ℕ) (c0 : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ), EmbeddingTypes.admitted i r ρ π dc ep e' c0 cB → (D.nd.l i ≠ D.host.g 0 → D.nd.l i ≠ D.host.g 1 → π ∈ D.nd.Z i → TruncatedSeriesCountingIdentities.admG2 i r ρ π) → EmbeddingTypes.aux₃ i r ρ π dc ep e' c0 cB) → (∀ i, D.nd.l i ∉ TwistedPlaces.gset D → ∀ π ∈ D.nd.Zgood i, TruncatedSeriesCountingIdentities.admG2 i (X.r i) (X.ρ i) π) → KillingConditions.KillAt X.ρ → TwistedPlaces.ShaFinOdd D → KillingConditions.StarAD L X := by
  first | exact @GlobalTheory.NLink.starAD_of_global | exact GlobalTheory.NLink.starAD_of_global | (intros; apply GlobalTheory.NLink.starAD_of_global <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsFurtherBisStatement

section

@[expose] public section



section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

theorem _root_.GlobalTheory.T.adm_at_inert_of_range : Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ), _root_.GlobalTheory.NLink.SetupAlt L nch HW X C₂ → 1 ≤ C₂ → WachCoordinates.Conclusion2 D C₂ → KillingConditions.JointParametersHubConditions L HW X (rowC C₂) → ∀ i, TwistedPlaces.TwLoc D i → D.nd.l i ∉ TwistedPlaces.gset D → KillingConditions.RangeAD L X.exc (D.nd.l i) → TwistedPlaces.InertK D (D.nd.l i) → ∀ π ∈ D.nd.Zgood i, TruncatedSeriesCountingIdentities.admitted i (X.r i) (X.ρ i) π (X.dc i) (X.lenRow i) (X.e' i) (X.cB i) := by
  first | exact @_root_.GlobalTheory.NLink.InertStep.main_alt_alt | exact _root_.GlobalTheory.NLink.InertStep.main_alt_alt | (intros; apply _root_.GlobalTheory.NLink.InertStep.main_alt_alt <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SplitPrimeHypsStatement

section

@[expose] public section



section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

theorem _root_.GlobalTheory.T.unramified_places_declared' : Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ), _root_.GlobalTheory.NLink.SetupAlt L nch HW X C₂ → ∀ i, TwistedPlaces.TwLoc D i → D.nd.l i ∉ TwistedPlaces.gset D → KillingConditions.RangeAD L X.exc (D.nd.l i) → TwistedPlaces.SplitK D (D.nd.l i) → ∃ ep, EmbeddingTypes.hypDecl i (X.dc i) ep ∧ (∀ v ∈ placesOver D.host.E (D.nd.l i), v.asIdeal.ramificationIdx ℤ = 1) ∧ ∀ π ∈ D.nd.Zgood i, EmbeddingTypes.admitted i (X.r i) (X.ρ i) π (X.dc i) ep (X.eS i) (X.c0 i) (X.cB i) := by
  first | exact @_root_.GlobalTheory.NLink.splitPrime_hyps_alt | exact _root_.GlobalTheory.NLink.splitPrime_hyps_alt | (intros; apply _root_.GlobalTheory.NLink.splitPrime_hyps_alt <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowsADInSetting

section

@[expose] public section



section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
namespace GlobalTheory.NLink
theorem rowsAD_in_setting_alt : Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc)
    (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ),
    _root_.GlobalTheory.NLink.SetupAlt L nch HW X C₂ → 1 ≤ C₂ → WachCoordinates.Conclusion2 D C₂ → KillingConditions.JointParametersHubConditions L HW X (rowC C₂) →
    KillingConditions.StarAD L X ∧ KillingConditions.BBLe L X 7200 := by
  intro hP D L P nch HW F Cm X C₂ hS hC hp2 hBCD
  have hstep : KillingConditions.StepAD L X :=
    { a09 := _root_.GlobalTheory.T.adm_at_inert_of_range hP D L P nch HW F Cm X C₂ hS hC hp2 hBCD
      a78 := _root_.GlobalTheory.T.unramified_places_declared' hP D L P nch HW F Cm X C₂ hS
      goodR := hS.canon.fam.good }
  have hst1 : TruncatedSeriesCountingIdentities.IntegralityFromMetric D := GlobalTheory.T.integralityFromMetric_of_designConditionAll hP.artin hP.bk hP.tate hP.euler D hS.facts.duties.2.2.1
  have h78 := GlobalTheory.T.splitCase_bound_at_point_of_admitted_items_alt hP.artin hP.tate hP.euler D
  have hG2 : ∀ i, D.nd.l i ∉ TwistedPlaces.gset D → ∀ π ∈ D.nd.Zgood i, TruncatedSeriesCountingIdentities.admG2 i (X.r i) (X.ρ i) π :=
    fun i hi π hπ => (_root_.GlobalTheory.T.set_pt_of_setup_not_twisted hP D L P nch HW F Cm X C₂ hS i hi π hπ).2.1
  refine ⟨GlobalTheory.T.starInequality_rowsAD_of_global_theorems D L HW X (rowC C₂) hS.canon.data hstep hst1 h78 hG2 hS.kill hS.sha, ?_⟩
  have h := GlobalTheory.T.nonPlacePart_localBound_le_middleRange D L P HW X (rowC C₂) 120 (by norm_num) hS.canon.data
    (_root_.GlobalTheory.T.invariantsBoundNonsplit_of_setup hP D L P nch HW F Cm X C₂ hS)
  have e : (60 : ℝ) * 120 = 7200 := by norm_num
  rwa [e] at h
end GlobalTheory.NLink
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowsADInSettingStatement

section

@[expose] public section



section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

theorem _root_.GlobalTheory.T.star_ad_and_bb_le_of_joint_cond : Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ), _root_.GlobalTheory.NLink.SetupAlt L nch HW X C₂ → 1 ≤ C₂ → WachCoordinates.Conclusion2 D C₂ → KillingConditions.JointParametersHubConditions L HW X (rowC C₂) → KillingConditions.StarAD L X ∧ KillingConditions.BBLe L X 7200 := by
  first | exact @_root_.GlobalTheory.NLink.rowsAD_in_setting_alt | exact _root_.GlobalTheory.NLink.rowsAD_in_setting_alt | (intros; apply _root_.GlobalTheory.NLink.rowsAD_in_setting_alt <;> assumption)
end
end
end
