module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LatticeHasSmallGenerators
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SeriesRatSOf
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvOfRoot
import Formalism.SharpRestriction.LevelLetterCocycles.CommutingEndomorphismPreservesInvariants
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LatSmallGenStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReadInj
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowAtOfRatStep
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ConjRootStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ScaleRootAltBis
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Formalism.LocalRingCardinality.DataHost
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsKsFormOfAlgebraicFormsIso
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndependentRowsMap
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ScaleRootOfPrintStatement
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateBaseOfReciprocity

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

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (w : D.what₂.places.Pl) (j : Fin D.R.m)

theorem baseLat_le
    (hinj : ∀ (ρ : Setup D.ntw) (hρ : ρ.Good) (ν : ℂ), ν ≠ 0 → Function.Injective (rdAt p w j hρ ν))
    (hgen : ∀ (ρ : Setup D.ntw), ρ.Good → RealPin p.R p.cG ρ → ∀ (h : GA D (Vc D j)) (P : PolF D (Wc D j).rank (Vc D j).rank),
      P ∈ ρ.lat (ex.nch.twI w) j (ex.nch.sd w) (ρ.eO (ex.nch.twI w) (ex.nch.sd w)).range h →
      P ∈ Submodule.span (ρ.eO (ex.nch.twI w) (ex.nch.sd w)).range
        (ρ.lat (ex.nch.twI w) j (ex.nch.sd w) (smallInt D) h : Set (PolF D (Wc D j).rank (Vc D j).rank)))
    (hunit : ∀ (ρ ρ' : Setup D.ntw) (hρ : ρ.Good) (hρ' : ρ'.Good) (ν ν' : ℂ),
      RealPin p.R p.cG ρ → ρ.LevelOf D.nexp → RealPin p.R p.cG ρ' → SameBut ρ ρ' →
      IsNorm p.R p.v₀ (ρ.B (ex.nch.twI w) j (ex.nch.sd w)) ν → IsNorm p.R p.v₀ (ρ'.B (ex.nch.twI w) j (ex.nch.sd w)) ν' →
      RatBase (rdAt p w j hρ ν) → RatBase (rdAt p w j hρ' ν') →
      ∀ s h P, ρ.IsDatum (ex.nch.twI w) j (ex.nch.sd w) s h P → P ∈ ρ.lat (ex.nch.twI w) j (ex.nch.sd w) (smallInt D) h →
        ∀ f f', rdAt p w j hρ ν f = ρ.theta (ex.nch.twI w) j (ex.nch.sd w) h P →
          rdAt p w j hρ' ν' f' = ρ.theta (ex.nch.twI w) j (ex.nch.sd w) h P →
          ∃ u : FractionRing (D.ntw.O (ex.nch.twI w)), (∃ n : ℕ, n ≠ 0 ∧ u ^ n = 1) ∧ f' = u • f)
    (ρ ρ' : Setup D.ntw) (hρ : ρ.Good) (hρ' : ρ'.Good) (ν ν' : ℂ) (hp : RealPin p.R p.cG ρ) (hL : ρ.LevelOf D.nexp) (hp' : RealPin p.R p.cG ρ')
    (hS : SameBut ρ ρ') (hN : IsNorm p.R p.v₀ (ρ.B (ex.nch.twI w) j (ex.nch.sd w)) ν)
    (hN' : IsNorm p.R p.v₀ (ρ'.B (ex.nch.twI w) j (ex.nch.sd w)) ν')
    (hR : RatBase (rdAt p w j hρ ν)) (hR' : RatBase (rdAt p w j hρ' ν')) :
    baseLat p w j hρ ν ≤ baseLat p w j hρ' ν' := by
  have hbad := hS.2.2.1
  have hB := hS.2.2.2.1
  have hom := hS.2.2.2.2
  have hth : ∀ h P, ρ'.theta (ex.nch.twI w) j (ex.nch.sd w) h P = ρ.theta (ex.nch.twI w) j (ex.nch.sd w) h P := by
    intro h P
    simp only [Setup.theta, hB, hom]
  have hlat : ∀ O h, ρ'.lat (ex.nch.twI w) j (ex.nch.sd w) O h = ρ.lat (ex.nch.twI w) j (ex.nch.sd w) O h := by
    intro O h
    simp only [Setup.lat, hB]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, ⟨s, h, P, hd, hf⟩, rfl⟩
  have key : ∀ Q ∈ Submodule.span (ρ.eO (ex.nch.twI w) (ex.nch.sd w)).range
      (ρ.lat (ex.nch.twI w) j (ex.nch.sd w) (smallInt D) h : Set (PolF D (Wc D j).rank (Vc D j).rank)),
      ∃ g, rdAt p w j hρ ν g = ρ.theta (ex.nch.twI w) j (ex.nch.sd w) h Q ∧
        ((1 : FractionRing (ex.nch.Oe w)) ⊗ₜ[D.ntw.O (ex.nch.twI w)] g) ∈ baseLat p w j hρ' ν' := by
    intro Q hQ
    induction hQ using Submodule.span_induction with
    | mem Q hQ =>
      have hd1 : ρ.IsDatum (ex.nch.twI w) j (ex.nch.sd w) s h Q :=
        ⟨hd.split, hd.off, hd.fin, hd.supp, lat_mono ρ _ j _ (smallInt_le hρ _ _) h hQ⟩
      have hd2 : ρ'.IsDatum (ex.nch.twI w) j (ex.nch.sd w) s h Q :=
        ⟨hd.split, by rw [hbad]; exact hd.off, hd.fin, hd.supp,
          lat_mono ρ' _ j _ (smallInt_le hρ' _ _) h (by rw [hlat]; exact hQ)⟩
      obtain ⟨g, hg⟩ := hR s h Q hd1
      obtain ⟨g', hg'⟩ := hR' s h Q hd2
      rw [hth] at hg'
      obtain ⟨u, ⟨n, hn, hu⟩, hgu⟩ := hunit ρ ρ' hρ hρ' ν ν' hp hL hp' hS hN hN' hR hR' s h Q hd1 hQ g g' hg hg'
      obtain ⟨o, ho⟩ := exists_inv_of_root u n hn hu
      have hu0 : u ≠ 0 := by
        rintro rfl
        rw [zero_pow hn] at hu
        exact zero_ne_one hu
      have hgo : g = o • g' := by
        rw [← algebraMap_smul (FractionRing (D.ntw.O (ex.nch.twI w))) o g', ho, hgu, smul_smul, inv_mul_cancel₀ hu0, one_smul]
      refine ⟨g, hg, ?_⟩
      rw [hgo, TensorProduct.tmul_smul]
      refine Submodule.smul_of_tower_mem _ o (Submodule.subset_span ⟨g', ⟨s, h, Q, hd2, ?_⟩, rfl⟩)
      rw [hg', hth]
    | zero =>
      refine ⟨0, ?_, by rw [TensorProduct.tmul_zero]; exact zero_mem _⟩
      rw [map_zero]
      exact (map_zero _).symm
    | add Q1 Q2 _ _ h1 h2 =>
      obtain ⟨g1, e1, m1⟩ := h1
      obtain ⟨g2, e2, m2⟩ := h2
      refine ⟨g1 + g2, ?_, by rw [TensorProduct.tmul_add]; exact add_mem m1 m2⟩
      rw [map_add (f := _), e1, e2]
      exact (map_add _ _ _).symm
    | smul a Q _ h1 =>
      obtain ⟨g1, e1, m1⟩ := h1
      obtain ⟨o, ho⟩ := a.2
      refine ⟨o • g1, ?_, by rw [TensorProduct.tmul_smul]; exact Submodule.smul_of_tower_mem _ o m1⟩
      rw [rd_smul, e1]
      change _ = (ρ.B (ex.nch.twI w) j (ex.nch.sd w)).theta (ρ.om (ex.nch.twI w) j (ex.nch.sd w) 1) h ((a : ℂ) • Q)
      rw [map_smul, ← ho]
  obtain ⟨g, hg, hm⟩ := key P (hgen ρ hρ hp h P hd.mem)
  have : f = g := hinj ρ hρ ν hN.1 (hf.trans hg.symm)
  rw [this]
  exact hm

end Point

end GlobalTheory.BigOn.Exp
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoordOfIndep

section

@[expose] public section

open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links

set_option autoImplicit false

noncomputable section




namespace GlobalTheory.BigOn.Exp

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_coord_of_indep {K V W : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module ℂ W]
    (e : K →+* ℂ) (rd : V →ₛₗ[e] W)
    (hF : ∀ (n : ℕ) (v : Fin n → V), LinearIndependent K v → LinearIndependent ℂ fun c => rd (v c))
    {μ : ℂ} {f f' : V} (hf : f ≠ 0) (h : rd f' = μ • rd f) : ∃ u : K, e u = μ := by
  have hrf : rd f ≠ 0 := (hF 1 (fun _ => f) (linearIndependent_unique_iff.2 hf)).ne_zero 0
  by_cases hli : LinearIndependent K ![f, f']
  · have h2 := hF 2 _ hli
    have h2' : LinearIndependent ℂ ![rd f, rd f'] := by
      convert h2 using 1
      funext c
      fin_cases c <;> rfl
    have := (LinearIndependent.pair_iff.1 h2') (-μ) 1 (by rw [h, one_smul, neg_smul, neg_add_cancel])
    exact absurd this.2 one_ne_zero
  · rw [LinearIndependent.pair_iff] at hli
    push_neg at hli
    obtain ⟨s, t, hst, hne⟩ := hli
    have ht : t ≠ 0 := by
      intro ht0
      rw [ht0, zero_smul, add_zero] at hst
      exact hne ((smul_eq_zero.1 hst).resolve_right hf) ht0
    have hf' : f' = (-(s / t)) • f := by
      have : t • f' = -(s • f) := eq_neg_of_add_eq_zero_right hst
      calc f' = t⁻¹ • (t • f') := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
        _ = _ := by rw [this, smul_neg, smul_smul, ← neg_smul, div_eq_inv_mul]
    refine ⟨-(s / t), ?_⟩
    have h3 : e (-(s / t)) • rd f = μ • rd f := by rw [← h, hf', map_smulₛₗ]
    exact smul_left_injective ℂ hrf h3

end GlobalTheory.BigOn.Exp
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoordRange

section

@[expose] public section



section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
set_option autoImplicit false
noncomputable section


namespace GlobalTheory.BigOn.Exp
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem coordRange_alt : _root_.GlobalTheory.BigOn.Exp.CoordinateRangeCondition := by
  unfold _root_.GlobalTheory.BigOn.Exp.CoordinateRangeCondition _root_.GlobalTheory.BigOn.Exp.TwistConditions _root_.GlobalTheory.BigOn.AtPtsAlt
  refine ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH _ _ =>
    ⟨0, fun x hx _ i p hr hm w _ j ρ hρ ν μ hν f f' hf hff => ?_⟩⟩⟩
  obtain ⟨Z⟩ := hm.2.2.series
  have hU : p.R.toRealDat.LUnif := hr.prim.unif
  have hW : p.R.toRealDat.models_HW := p.charW.base.models.HW
  have hK : (p.Sx.A ((j : ℕ) + 1)).IsKsForm := GlobalTheory.isKsForm_of_formsIso _ _ (p.nexp.fi j) (p.fw.ks j)
  exact exists_coord_of_indep _ _
    (GlobalTheory.SeriesTie.realRd_faithful _ _ _ _ _ _ _ p.R p.cG p.Sx p.nexp p.v₀ ρ hρ _ j _ ν hν hU hW (Z.vec j) hK) hf hff
end GlobalTheory.BigOn.Exp
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SeriesUnit

section

@[expose] public section



section
set_option autoImplicit false
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
open scoped TensorProduct
namespace GlobalTheory.BigOn.Exp
theorem seriesUnit_alt : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.SerStd.SeriesRatS → _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ (ρ ρ' : Setup (Fm.D x i).ntw) (hρ : ρ.Good) (hρ' : ρ'.Good) (ν ν' : ℂ),
  RealPin p.R p.cG ρ → ρ.LevelOf (Fm.D x i).nexp → RealPin p.R p.cG ρ' → SameBut ρ ρ' →
  IsNorm p.R p.v₀ (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ν →
  IsNorm p.R p.v₀ (ρ'.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ν' →
  RatBase (rdAt p w j hρ ν) → RatBase (rdAt p w j hρ' ν') →
  ∀ s h P, ρ.IsDatum ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) s h P →
    P ∈ ρ.lat ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) (smallInt (Fm.D x i)) h →
    ∀ f f', rdAt p w j hρ ν f = ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) h P →
      rdAt p w j hρ' ν' f' = ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) h P →
      ∃ u : FractionRing ((Fm.D x i).ntw.O ((Fm.ex x hx i).nch.twI w)), (∃ n : ℕ, n ≠ 0 ∧ u ^ n = 1) ∧ f' = u • f := by
  intro h1 h2 h3 h4
  have hI := _root_.GlobalTheory.BigOn.Exp.readInj_alt
  have hS := _root_.GlobalTheory.T.scale_root_of_reciprocity_inputs h1 h2 h3 h4
  have hC := _root_.GlobalTheory.T.norm_ratio_realization_same_dual_alt h1 h2 h3 h4
  have hR := _root_.GlobalTheory.BigOn.Exp.coordRange_alt
  unfold _root_.GlobalTheory.BigOn.Exp.ReadInjAlt at hI
  unfold _root_.GlobalTheory.BigOn.Exp.ScaleRootAltBis at hS
  unfold _root_.GlobalTheory.BigOn.Exp.CoordinateRangeCondition at hR
  unfold _root_.GlobalTheory.BigOn.Exp.TwistConditions _root_.GlobalTheory.BigOn.AtPtsAlt at hI hS hC hR ⊢
  refine Closed.imp (Closed.and (Closed.and (Closed.and hI hS) hC) hR) ?_
  intro eps Fm CH _ h
  obtain ⟨x0, hx0⟩ := _root_.GlobalTheory.BigTop.EventuallyAtPoints.and (_root_.GlobalTheory.BigTop.EventuallyAtPoints.and (_root_.GlobalTheory.BigTop.EventuallyAtPoints.and h.1.1.1 h.1.1.2) h.1.2) h.2
  refine ⟨x0, ?_⟩
  intro x hx hle i p hp hm w hw j ρ ρ' hρ hρ' ν ν' hpin hlev hpin' hSB hN hN' hR0 hR0' s h P hd hP f f' hf hf'
  obtain ⟨⟨⟨a1, a2⟩, a3⟩, a4⟩ := hx0 x hx hle i p hp
  have hν : ν ≠ 0 := hN.1
  have hν' : ν' ≠ 0 := hN'.1
  have inj' := a1 hm w hw j ρ' hρ' ν hν
  have inj := a1 hm w hw j ρ hρ ν hν
  by_cases hf0 : f = 0
  · subst hf0
    have h0 : rdAt p w j hρ' ν' f' = rdAt p w j hρ' ν' 0 := by
      rw [hf', ← hf, map_zero, map_zero]
    have := a1 hm w hw j ρ' hρ' ν' hν' h0
    exact ⟨1, ⟨1, one_ne_zero, one_pow 1⟩, by rw [this, smul_zero]⟩
  · have hθ : ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) h P ≠ 0 := by
      intro h0
      apply hf0
      apply inj
      rw [hf, h0, map_zero]
    obtain ⟨n, hn, hnn⟩ := a2 hm w hw j ρ ρ' hρ hρ' ν ν' hpin hpin' hSB hN hN' hR0 hR0' s h P hd hP hθ
    obtain ⟨c, ⟨m, hm0, hcm⟩, hc⟩ := a3 hm w hw j ρ ρ' hρ hρ' ν ν' hpin hlev hpin' hSB hN hN' hR0 hR0' s h P hd hP f hf
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_pow hm0] at hcm
      exact zero_ne_one hcm
    have hap := fun ν₁ g =>
      realRd_apply p.nexp p.v₀ hρ' ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) ν₁ g
    have key : rdAt p w j hρ' ν f' = (ν' * ν⁻¹ * c⁻¹) • rdAt p w j hρ' ν f := by
      rw [hc, ← hf', smul_smul]
      have e1 := hap ν f'
      have e2 := hap ν' f'
      simp only [rdAt]
      rw [e1, e2, smul_smul]
      congr 1
      field_simp
    obtain ⟨u, hu⟩ := a4 hm w hw j ρ' hρ' ν _ hν f f' hf0 key
    refine ⟨u, ⟨n * m, mul_ne_zero hn hm0, ?_⟩, ?_⟩
    · apply (ρ'.e ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.sd w)).injective
      rw [map_pow, map_one, hu, mul_pow, mul_pow, pow_mul ν', hnn, ← pow_mul, inv_pow, inv_pow,
        mul_inv_cancel₀ (pow_ne_zero _ hν), mul_comm n m, pow_mul c, hcm]
      simp
    · apply inj'
      rw [key, map_smulₛₗ, hu]
end GlobalTheory.BigOn.Exp
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SeriesUnitStatement

section

@[expose] public section



section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
open scoped TensorProduct

theorem _root_.GlobalTheory.T.norm_ratio_realization_same_alt : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.SerStd.SeriesRatS → _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ (ρ ρ' : Setup (Fm.D x i).ntw) (hρ : ρ.Good) (hρ' : ρ'.Good) (ν ν' : ℂ),
  RealPin p.R p.cG ρ → ρ.LevelOf (Fm.D x i).nexp → RealPin p.R p.cG ρ' → SameBut ρ ρ' →
  IsNorm p.R p.v₀ (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ν →
  IsNorm p.R p.v₀ (ρ'.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ν' →
  RatBase (rdAt p w j hρ ν) → RatBase (rdAt p w j hρ' ν') →
  ∀ s h P, ρ.IsDatum ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) s h P →
    P ∈ ρ.lat ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) (smallInt (Fm.D x i)) h →
    ∀ f f', rdAt p w j hρ ν f = ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) h P →
      rdAt p w j hρ' ν' f' = ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) h P →
      ∃ u : FractionRing ((Fm.D x i).ntw.O ((Fm.ex x hx i).nch.twI w)), (∃ n : ℕ, n ≠ 0 ∧ u ^ n = 1) ∧ f' = u • f := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.seriesUnit_alt | exact _root_.GlobalTheory.BigOn.Exp.seriesUnit_alt | (intros; apply _root_.GlobalTheory.BigOn.Exp.seriesUnit_alt <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ConjBaseOfSteps

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
section Point
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (w : D.what₂.places.Pl) (j : Fin D.R.m)
end Point
def SeriesUnitLAlt : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ (ρ ρ' : Setup (Fm.D x i).ntw) (hρ : ρ.Good) (hρ' : ρ'.Good) (ν ν' : ℂ),
  RealPin p.R p.cG ρ → ρ.LevelOf (Fm.D x i).nexp → RealPin p.R p.cG ρ' → SameBut ρ ρ' →
  IsNorm p.R p.v₀ (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ν →
  IsNorm p.R p.v₀ (ρ'.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ν' →
  RatBase (rdAt p w j hρ ν) → RatBase (rdAt p w j hρ' ν') →
  ∀ s h P, ρ.IsDatum ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) s h P →
    P ∈ ρ.lat ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) (smallInt (Fm.D x i)) h →
    ∀ f f', rdAt p w j hρ ν f = ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) h P →
      rdAt p w j hρ' ν' f' = ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) h P →
      ∃ u : FractionRing ((Fm.D x i).ntw.O ((Fm.ex x hx i).nch.twI w)), (∃ n : ℕ, n ≠ 0 ∧ u ^ n = 1) ∧ f' = u • f
theorem conjBase_of_readInj_latSmallGen_seriesUnit (hI : _root_.GlobalTheory.BigOn.Exp.ReadInjAlt) (hG : _root_.GlobalTheory.BigOn.Exp.LatticeHasSmallGenerators) (hU : _root_.GlobalTheory.BigOn.Exp.SeriesUnitLAlt) : _root_.GlobalTheory.BigOn.Exp.ConjugateBase := by
  unfold _root_.GlobalTheory.BigOn.Exp.ConjugateBase _root_.GlobalTheory.BigOn.Exp.ReadInjAlt _root_.GlobalTheory.BigOn.Exp.LatticeHasSmallGenerators _root_.GlobalTheory.BigOn.Exp.SeriesUnitLAlt _root_.GlobalTheory.BigOn.Exp.TwistConditions _root_.GlobalTheory.BigOn.AtPtsAlt at *
  refine ((Formalism.MainNotions.Closed.and hI hG).and hU).imp fun Fm CH _ h => ?_
  obtain ⟨x0, hx0⟩ := (h.1.1.and h.1.2).and h.2
  refine ⟨x0, fun x hx hle i p hp hm w hw j ρ ρ' hρ hρ' ν ν' hpin hS hN hR hF => ?_⟩
  obtain ⟨⟨a1, a2⟩, a3⟩ := hx0 x hx hle i p hp
  have hL : ρ.LevelOf (Fm.D x i).nexp := levelOf_of_sameBut hm.2.2 hρ' hρ hF.1.1 hpin hS.symm hF.2.2.2
  exact le_antisymm
    (baseLat_le p w j (a1 hm w hw j) (a2 hm w hw j) (a3 hm w hw j) ρ ρ' hρ hρ' ν ν' hpin hL hF.1.1 hS hN hF.2.1 hR.1 hF.2.2.1.1)
    (baseLat_le p w j (a1 hm w hw j) (a2 hm w hw j) (a3 hm w hw j) ρ' ρ hρ' hρ ν' ν hF.1.1 hF.2.2.2 hpin hS.symm hF.2.1 hN hF.2.2.1.1 hR.1)
theorem conjBase_of_cusp_decay_and_reciprocity : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt →
    GlobalTheory.SerStd.SeriesRatS → _root_.GlobalTheory.BigOn.Exp.ConjugateBase := fun h1 h2 h3 h4 =>
  _root_.GlobalTheory.BigOn.Exp.conjBase_of_readInj_latSmallGen_seriesUnit _root_.GlobalTheory.BigOn.Exp.readInj_alt _root_.GlobalTheory.T.latSmallGen' (_root_.GlobalTheory.T.norm_ratio_realization_same_alt h1 h2 h3 h4)
end GlobalTheory.BigOn.Exp
end
end
end
end
