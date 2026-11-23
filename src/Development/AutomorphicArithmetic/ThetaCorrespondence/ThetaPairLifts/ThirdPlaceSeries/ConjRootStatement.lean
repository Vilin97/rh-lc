module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvOfRoot
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SeriesRatSOf
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowAtOfRatStep
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.Algebraic.Defs
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsRingEquivComplexCompEq
public import Formalism.LocalRingCardinality.DataHost
public import Mathlib.Algebra.AlgebraicCard
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.IndefiniteTreeX
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExpAlgAlt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExpAlgOfSerAlg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgebraicOfSmallInt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToRatHyp0
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSeriesOfReciprocityHypotheses
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationLawsCentralMovedReadingsStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.InGeoGeoHalf
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LowAtHolds
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RatHyp0AtPoint
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwAdm
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Definitions.Divisors.OfCore
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullHeckeRealDatMovedReadings
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ScaleRootOfPrintStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExpConjStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjRootOfExp

section

@[expose] public section

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
open scoped TensorProduct


attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn.Exp

theorem exists_aut_alg {K : Type} [Field K] (e e' : K →+* ℂ) :
    ∃ τ : ℂ ≃+* ℂ, ∀ a : K, IsAlgebraic ℚ (e a) → τ (e a) = e' a := by
  let k : Subfield K := (algebraicClosure ℚ ℂ).toSubfield.comap e
  have hk : ∀ a : K, a ∈ k ↔ IsAlgebraic ℚ (e a) := fun a => mem_algebraicClosure_iff
  haveI : Countable {x : ℂ | IsAlgebraic ℚ x} := (Algebraic.countable ℚ ℂ).to_subtype
  haveI : Countable k :=
    Function.Injective.countable (f := fun a : k => (⟨e a, (hk a).1 a.2⟩ : {x : ℂ | IsAlgebraic ℚ x}))
      (fun a b hab => Subtype.ext (e.injective (congrArg Subtype.val hab)))
  obtain ⟨τ, hτ⟩ := GlobalTheory.CompRat.exists_ringEquiv_complex_comp_eq k (e.comp k.subtype) (e'.comp k.subtype)
  exact ⟨τ, fun a ha => hτ ⟨a, (hk a).2 ha⟩⟩

end GlobalTheory.BigOn.Exp
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PointCases

section

@[expose] public section



section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.SerRefCore
open scoped TensorProduct


attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.SerRefPt
section Core
variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m}
end Core
end GlobalTheory.SerRefPt
namespace GlobalTheory.SerRefPt
open GlobalTheory.RealGeo GlobalTheory.Unframe GlobalTheory.UnframePt

theorem fw_eq_zero_or_exists_norm_algComb (hP : GlobalTheory.Published.CuspRapidDecay) (hA : GlobalTheory.Published.GlobalArtinReciprocity) (hRF : GlobalTheory.Published.RayClassFieldSt)
    (hS : GlobalTheory.SerStd.SeriesRatS) {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) (p : Pt Fm x hx i) (hR : p.PointConditions')
    (hM : More p) (t : (Fm.D x i).ntw.Tw) (j : Fin (Fm.D x i).R.m) (h0 : RatHyp0 p.T p.R (F2 p) p.κ p.v₀ p.O t j)
    (ρ : Setup (Fm.D x i).ntw) (hρ : ρ.Good) (b : Bool) (h : RealPin p.R p.cG ρ) :
    (∀ y ∈ (p.R.FW j).WK, y = 0) ∨ ∃ ν, IsNorm p.R p.v₀ (ρ.B t j b) ν ∧ ∀ s g P, ρ.IsDatum t j b s g P →
      P ∈ ρ.lat t j b (smallInt (Fm.D x i)) g → AlgComb p.nexp p.v₀ j (ν • ρ.theta t j b g P) := by
  obtain ⟨c', w, hw, hfr, B', hv⟩ := exists_framed_half hP h0.size (GlobalTheory.Core5.of_core h0.core) (geoHalf p) h0.unif
    (_root_.GlobalTheory.UnframePt.inGeo_geoHalf_of_ratHyp0 hP Fm x hx i p hR hM t j h0)
  letI iA : Algebra (setCE p.T c').Q.c.F (Fm.D x i).what₂.LL := p.alg
  have hV' : (setCE p.T c').V ((j : ℕ) + 1) (setCE p.T c').σ₀ = Wc (Fm.D x i) j :=
    B'.fw.laws.spaceW _ ⟨Nat.le_add_left _ _, j.2⟩ _ (setCE p.T c').toCore.good_σ₀
  have hU' : (fullHeckeRealDatMovedReadings p.R w).toRealDat.LUnif := GlobalTheory.T.uniformisationLaws_centralMovedReadings p.R.toRealDat w hw h0.unif
  have hG : (fullHeckeRealDatMovedReadings p.R w).toRealDat.IsGrp (F2 p) :=
    ⟨h0.core.grp.red_R, h0.core.grp.red_L, h0.core.grp.levels, h0.core.grp.record, h0.core.grp.chiW⟩
  have c := h0.core
  have hF : (fullHeckeRealDatMovedReadings p.R w).toRealDat.IsFam := { c.fam with }
  have hMo : (fullHeckeRealDatMovedReadings p.R w).toRealDat.IsModels := { c.models with }
  have hCh : (fullHeckeRealDatMovedReadings p.R w).toRealDat.IsChain := { c.chain with }
  have hTh : (fullHeckeRealDatMovedReadings p.R w).toRealDat.IsThP := { c.thP with }
  have hC : GlobalTheory.Hk3.Core (fullHeckeRealDatMovedReadings p.R w).toRealDat (F2 p) := ⟨c.lev, hG, hF, hMo, hCh, hTh⟩
  have hph : (fun k => cj (twAt (Fm.D x i).what₂.embLL p.P.A3.A.v0) ((fullHeckeRealDatMovedReadings p.R w).phs k)) = fun _ => (1 : ℂ) :=
    funext fun k => by
      show cj (twAt (Fm.D x i).what₂.embLL p.P.A3.A.v0) (p.R.phs k) = 1
      rw [p.phsOne k, map_one]
  have hRat : RatHyp (setCE p.T c') (fullHeckeRealDatMovedReadings p.R w) (F2 p) B'.κ B'.v₀ B'.O t j hV' := by
    refine ⟨h0.size, h0.host, h0.std, B'.fw.laws, hC, hU', ⟨B'.fw⟩,
      ⟨B'.fw.laws, B'.fw.alg_eq, B'.fw.kap, B'.fw.hv₀, B'.fw.chiR, B'.fw.x0⟩, h0.io, h0.guard, h0.fin, B'.pins j, ?_,
      hfr j hV', h0.galois, h0.small, h0.inUse, h0.low⟩
    rw [hph]
    exact B'.phase j hU'
  have hpin' : RealPin (fullHeckeRealDatMovedReadings p.R w) p.cG ρ :=
    ⟨h.psi, h.inf, h.cartT, h.onbS, h.onbT, h.latS, h.latT, h.frS, h.frT, h.vac, h.Pg, h.grp, h.mu0, h.eta, h.delta, h.deltaPl,
      h.ap, h.am⟩
  have hsp : (Fm.D x i).host.cls (Fm.D x i).host.pde = PrimeClass.splitK ∧
      (Fm.D x i).host.cls (Fm.D x i).host.pde' = PrimeClass.splitK :=
    ⟨(Fm.params x hx i).level_split _ (Fm.D x i).host.pde_level.1, (Fm.params x hx i).level_split _ (Fm.D x i).host.pde_level.2⟩
  have H := core_cases (T := setCE p.T c') (Rl := fullHeckeRealDatMovedReadings p.R w) hA hRF hS (GlobalTheory.UnframeForms.movedYS p.nexp w) hρ b hpin' hRat hsp
  rw [hv] at H
  rcases H with H | ⟨ν, hN, H⟩
  · exact Or.inl H
  · exact Or.inr ⟨ν, hN, fun s g P hd hl => algComb_of_moved p.nexp w p.v₀ j (H s g P hd hl)⟩
theorem serRef_of_reciprocity_ray_class : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt →
    GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → _root_.GlobalTheory.BigOn.Exp.SerRefAlt := by
  intro hP hA hRF hS
  have hL := _root_.GlobalTheory.BigOn.Exp.lowAt_holds_alt
  have hT := _root_.GlobalTheory.BigOn.Exp.twAdm_alt
  unfold _root_.GlobalTheory.BigOn.Exp.LowerBoundAtPlace at hL
  unfold _root_.GlobalTheory.BigOn.Exp.TwAdmAlt at hT
  unfold _root_.GlobalTheory.BigOn.Exp.SerRefAlt
  refine (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and hL hT).imp fun Fm x hx i p hp hM w _ j h => ?_
  intro ρ hρ ν hpin hN hR0
  refine ⟨ν, hN, hR0, fun s g P hd hl => ?_⟩
  rcases _root_.GlobalTheory.SerRefPt.fw_eq_zero_or_exists_norm_algComb hP hA hRF (GlobalTheory.SerStd.seriesRatS_of hS) Fm x hx i p hp hM _ j
    (_root_.GlobalTheory.BigOn.Exp.ratHyp0_at_point_alt Fm x hx i p hp hM _ h.2.2.2 h.1 j) ρ hρ _ hpin with H | ⟨ν₁, hN₁, H⟩
  · have h0 := theta_eq_zero p.nexp p.v₀ hρ _ j _ H hR0 hd
    have h1 : AlgComb p.nexp p.v₀ j (ν • ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) g P) := by
      rw [h0, smul_zero]
      exact AlgComb.zero
    exact h1
  · obtain ⟨ζ, hζ, e⟩ := exists_root_of_isNorm p.R p.v₀ _ hN₁ hN
    have h1 : AlgComb p.nexp p.v₀ j (ν • ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) g P) := by
      rw [e, mul_smul]
      exact (H s g P hd hl).smul hζ
    exact h1
end GlobalTheory.SerRefPt
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PointCasesStatement

section

@[expose] public section



section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp

theorem _root_.GlobalTheory.T.series_ref_of_decay_artin_ray_seriesRat : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → _root_.GlobalTheory.BigOn.Exp.SerRefAlt := by
  first | exact @_root_.GlobalTheory.SerRefPt.serRef_of_reciprocity_ray_class | exact _root_.GlobalTheory.SerRefPt.serRef_of_reciprocity_ray_class | (intros; apply _root_.GlobalTheory.SerRefPt.serRef_of_reciprocity_ray_class <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExpAlgAltAlt

section

@[expose] public section



section
set_option autoImplicit false
noncomputable section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
namespace GlobalTheory.BigOn.Exp
theorem expAlg_alt : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt →
    GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → _root_.GlobalTheory.BigOn.Exp.ExpAlgAlt := fun h1 h2 h3 h4 =>
  _root_.GlobalTheory.BigOn.Exp.expAlg_of_serAlg_alt (_root_.GlobalTheory.BigOn.Exp.serAlg_of_serRef_scaleRoot (_root_.GlobalTheory.T.series_ref_of_decay_artin_ray_seriesRat h1 h2 h3 h4) (_root_.GlobalTheory.T.scale_root_of_reciprocity_inputs h1 h2 h3 h4))
end GlobalTheory.BigOn.Exp
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExpAlgStatement

section

@[expose] public section



section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp

theorem _root_.GlobalTheory.T.expAlg_of_cusp_decay_and_reciprocity : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.SerStd.SeriesRatS → _root_.GlobalTheory.BigOn.Exp.ExpAlgAlt := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.expAlg_alt | exact _root_.GlobalTheory.BigOn.Exp.expAlg_alt | (intros; apply _root_.GlobalTheory.BigOn.Exp.expAlg_alt <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ConjRoot

section

@[expose] public section



section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
open scoped TensorProduct


attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BigOn.Exp
theorem conjRoot_alt : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.SerStd.SeriesRatS → _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ (ρ ρ' : Setup (Fm.D x i).ntw) (hρ : ρ.Good) (hρ' : ρ'.Good) (ν ν' : ℂ),
  RealPin p.R p.cG ρ → ρ.LevelOf (Fm.D x i).nexp → RealPin p.R p.cG ρ' → SameBut ρ ρ' →
  IsNorm p.R p.v₀ (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ν →
  IsNorm p.R p.v₀ (ρ'.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ν' →
  RatBase (rdAt p w j hρ ν) → RatBase (rdAt p w j hρ' ν') →
  ∀ s h P, ρ.IsDatum ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) s h P →
    P ∈ ρ.lat ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) (smallInt (Fm.D x i)) h →
    ∀ f, rdAt p w j hρ ν f = ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) h P →
      ∃ c : ℂ, (∃ n : ℕ, n ≠ 0 ∧ c ^ n = 1) ∧
        rdAt p w j hρ' ν f = c • ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) h P := by
  intro p1 p2 p3 p4
  have hA := _root_.GlobalTheory.T.expAlg_of_cusp_decay_and_reciprocity p1 p2 p3 p4
  have hB := _root_.GlobalTheory.T.real_datum_rational_normalization_alt p1 p2 p3 p4
  unfold _root_.GlobalTheory.BigOn.Exp.ExpAlgAlt at hA
  unfold _root_.GlobalTheory.BigOn.Exp.TwistConditions _root_.GlobalTheory.BigOn.AtPtsAlt at *
  refine (Formalism.MainNotions.Closed.and hA hB).imp fun Fm CH _ h => ?_
  obtain ⟨x0, hx0⟩ := h.1.and h.2
  refine ⟨x0, fun x hx hle i p hp hm w hw j ρ ρ' hρ hρ' ν ν' hpin hlev hpin' hSB hN hN' hR0 hR0' s h P hd hP f hf => ?_⟩
  obtain ⟨a1, a2⟩ := hx0 x hx hle i p hp
  obtain ⟨n, a, g, hfe, halg⟩ := a1 hm w hw j ρ hρ ν hpin hN hR0 s h P hd hP f hf
  obtain ⟨τ, hτ⟩ := exists_aut_alg (ρ.e ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.sd w))
    (ρ'.e ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.sd w))
  have hfix : ∀ y, τ (Formalism.L2.Host.embLL0 (Fm.D x i) y) = Formalism.L2.Host.embLL0 (Fm.D x i) y := by
    intro y
    have h1 := hρ.e_LL0 ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.sd w) y
    have h2 := hρ'.e_LL0 ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.sd w) y
    have hy : IsAlgebraic ℚ (Formalism.L2.Host.embLL0 (Fm.D x i) y) :=
      ((Algebra.IsAlgebraic.isAlgebraic y).algHom (Formalism.L2.Host.embLL0 (Fm.D x i)).toRatAlgHom)
    rw [← h1] at hy ⊢
    rw [hτ _ hy, h2, h1]
  obtain ⟨c, hc, hsum⟩ := a2 hm w hw j ρ hρ ν hpin hlev hN hR0 s h P hd hP f hf n a g hfe τ hfix
  refine ⟨c, hc, ?_⟩
  rw [← hf]
  have key : ∀ (ρ₀ : Setup (Fm.D x i).ntw) (hρ₀ : ρ₀.Good), rdAt p w j hρ₀ ν f =
      ν⁻¹ • ∑ k, ρ₀.e ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.sd w) (a k) • evW p.nexp p.v₀ j (g k).val := by
    intro ρ₀ hρ₀
    change ν⁻¹ • evK p.nexp p.v₀ hρ₀ _ j _ (p.nexp.eF _ _ _ (Nat.le_add_left _ _) j.2 f) = _

    rw [hfe, map_sum]
    rfl
  rw [key ρ' hρ', key ρ hρ, smul_comm, ← hsum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hτ _ (halg k)]
end GlobalTheory.BigOn.Exp
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ConjRootStatement

section

@[expose] public section



section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
open scoped TensorProduct

theorem _root_.GlobalTheory.T.norm_ratio_realization_same_dual_alt : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.SerStd.SeriesRatS → _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ (ρ ρ' : Setup (Fm.D x i).ntw) (hρ : ρ.Good) (hρ' : ρ'.Good) (ν ν' : ℂ),
  RealPin p.R p.cG ρ → ρ.LevelOf (Fm.D x i).nexp → RealPin p.R p.cG ρ' → SameBut ρ ρ' →
  IsNorm p.R p.v₀ (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ν →
  IsNorm p.R p.v₀ (ρ'.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ν' →
  RatBase (rdAt p w j hρ ν) → RatBase (rdAt p w j hρ' ν') →
  ∀ s h P, ρ.IsDatum ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) s h P →
    P ∈ ρ.lat ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) (smallInt (Fm.D x i)) h →
    ∀ f, rdAt p w j hρ ν f = ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) h P →
      ∃ c : ℂ, (∃ n : ℕ, n ≠ 0 ∧ c ^ n = 1) ∧
        rdAt p w j hρ' ν f = c • ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) h P := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.conjRoot_alt | exact _root_.GlobalTheory.BigOn.Exp.conjRoot_alt | (intros; apply _root_.GlobalTheory.BigOn.Exp.conjRoot_alt <;> assumption)
end
end
end
