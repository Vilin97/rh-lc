module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameCoord
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLieRepresentationEigenLatticesStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLatticeFgAndSpanEqTopRingOfIntegersStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedSpanEigenVectorMemEigenSublatticeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieBasisCompletionInSpanLieLatticeStatement
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Formalism.LocalToGlobal.ProjectiveLattices.IsCombAt
public import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsLieBasisBaseChange
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramedPointCoordinatesMemSpanEigenLatticeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramedPointGenericFibreCoordinatesEqFrameStatement
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLetterIntegralInIntegralEigenbasis
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsLieBasisIffIsUnitDet
public import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
public import Formalism.LocalToGlobal.ProjectiveLattices.SatLeaves
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieBasisFibreOverCompletionFractionField

section

@[expose] public section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.Frames

noncomputable section

open Limits

namespace GlobalTheory.LieLatGen

theorem exists_isLieBasis_fibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (K : Type) [Field K] [NumberField K] (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) (T : CDVR) (iK : K →+* T.Fr) (t' : SAB H (Sp T.Fr)) (n' : SABMap t' t₀ (spMap iK)), ∃ v' : Fin F.P₀.g → (epsR T.Fr ⟶ t'.G), IsLieBasis v' ∧ ∀ k, (v' k).left ≫ n'.φ ≫ m2.φ = spMap (Formalism.L2.Pj.dualMap iK) ≫ (F.v k).left ≫ F.φ := by
  intro E _ _ _ H K _ _ B t₀ m2 F T iK t' n'
  have hF : IsGrpPullback F.P₀.A B.t.G (spMap (algebraMap (𝓞 K) K)) F.φ := F.fib.2.1
  have hm : IsGrpPullback t₀.G B.t.G (spMap (algebraMap (𝓞 K) K)) m2.φ := m2.cart
  have hn : IsGrpPullback t'.G t₀.G (spMap iK) n'.φ := n'.cart
  have hc : IsGrpPullback t'.G B.t.G (spMap iK ≫ spMap (algebraMap (𝓞 K) K)) (n'.φ ≫ m2.φ) := hn.comp hm
  have w : (n'.φ ≫ m2.φ) ≫ B.t.G.hom = (t'.G.hom ≫ spMap iK) ≫ spMap (algebraMap (𝓞 K) K) := by
    rw [hc.1.w, Category.assoc]
  have hq : IsGrpPullback t'.G F.P₀.A (spMap iK) (hF.1.lift _ _ w) :=
    IsGrpPullback.cancel hF (hc.congr rfl (hF.1.lift_fst _ _ w).symm) (hF.1.lift_snd _ _ w)
  have := F.P₀.isAb.comm
  obtain ⟨v', hb, hv'⟩ := GlobalTheory.exists_isLieBasis_baseChange K T.Fr iK _ _ _ hq F.P₀.isAb.smooth _ F.v F.basis
  refine ⟨v', hb, fun k => ?_⟩
  rw [← hF.1.lift_fst _ _ w, ← Category.assoc, hv' k, Category.assoc]
  rfl

end GlobalTheory.LieLatGen
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieBasisFibreOverCompletionFractionFieldStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.Frames

theorem _root_.GlobalTheory.T.exists_lieBasis_fibre_over_completion_fraction_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (K : Type) [Field K] [NumberField K] (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) (T : CDVR) (iK : K →+* T.Fr) (t' : SAB H (Sp T.Fr)) (n' : SABMap t' t₀ (spMap iK)), ∃ v' : Fin F.P₀.g → (epsR T.Fr ⟶ t'.G), IsLieBasis v' ∧ ∀ k, (v' k).left ≫ n'.φ ≫ m2.φ = spMap (Formalism.L2.Pj.dualMap iK) ≫ (F.v k).left ≫ F.φ := by
  first | exact @GlobalTheory.LieLatGen.exists_isLieBasis_fibre | exact GlobalTheory.LieLatGen.exists_isLieBasis_fibre | (intros; apply GlobalTheory.LieLatGen.exists_isLieBasis_fibre <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreIntegralTangentInSpanLieBasis

section

@[expose] public section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.Frames
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory GlobalTheory.CM GlobalTheory.LamT
namespace GlobalTheory.PtDeg.LieModel

theorem isGrpPullback_self {S : Scheme.{0}} (G : Over S) [GrpObj G] : IsGrpPullback G G (𝟙 S) (𝟙 G.left) := by
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  exact (mul_left_congr (G := G) (Category.comp_id T.hom) x₀ y₀ x y (hx.trans (Category.comp_id _))
    (hy.trans (Category.comp_id _))).trans (Category.comp_id _).symm

theorem dualMap_id (R : Type) [CommRing R] : dualMap (RingHom.id R) = RingHom.id (DualNumber R) := by
  apply RingHom.ext
  intro x
  ext <;> simp [dualMap]

theorem spMap_dualMap_id (R : Type) [CommRing R] : spMap (dualMap (RingHom.id R)) = 𝟙 _ := by
  rw [dualMap_id]; exact Spec.map_id _

theorem spMap_comp_two {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp]
  rfl

theorem spMap_id' (R : Type) [CommRing R] : spMap (RingHom.id R) = 𝟙 _ := Spec.map_id _

theorem generic_coords_in_span : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (K : Type) [Field K] [NumberField K] (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) (T : CDVR) (iK : K →+* T.Fr) (ρV : 𝓞 K →+* T.V), (algebraMap T.V T.Fr).comp ρV = iK.comp (algebraMap (𝓞 K) K) → ∀ (G : GlobalTheory.CM.PAT H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (n : SABMap G.t B.t (spMap ρV)) (n' : SABMap t' t₀ (spMap iK)) (m2' : SABMap t' G.t (spMap (algebraMap T.V T.Fr))), m2'.φ ≫ n.φ = n'.φ ≫ m2.φ → ∀ (v' : Fin F.P₀.g → (epsR T.Fr ⟶ t'.G)), IsLieBasis v' → (∀ k, (v' k).left ≫ n'.φ ≫ m2.φ = spMap (Formalism.L2.Pj.dualMap iK) ≫ (F.v k).left ≫ F.φ) → ∀ (vV : Fin F.P₀.g → (epsR T.V ⟶ G.t.G)) (M : Fin F.P₀.g → Fin F.P₀.g → K), IsLieBasis vV → (∀ k, ∃ w : epsR K ⟶ F.P₀.A, IsLieComb (M k) F.v w ∧ spMap (Formalism.L2.Pj.dualMap (algebraMap T.V T.Fr)) ≫ (vV k).left ≫ n.φ = spMap (Formalism.L2.Pj.dualMap iK) ≫ w.left ≫ F.φ) → ∀ (ub : epsOver T.V T.V ⟶ G.t.G) (u'' : Sp (DualNumber T.Fr) ⟶ t'.G.left), IsTan ub → u'' ≫ m2'.φ = spMap (Formalism.L2.Pj.dualMap (algebraMap T.V T.Fr)) ≫ ub.left → ∃ (a : Fin F.P₀.g → T.V) (w'' : epsR T.Fr ⟶ t'.G), w''.left = u'' ∧ IsLieComb (∑ k, algebraMap T.V T.Fr (a k) • fun l => iK (M k l)) v' w'' := by
  intro E _ _ _ H K _ _ B t₀ m2 F T iK ρV hρV G t' n n' m2' h2 v' hv' hv'φ vV M hvV hM ub u'' hub hu''

  let ub' : epsR T.V ⟶ G.t.G := Over.homMk ub.left (Over.w ub)
  have hub' : IsTangent ub' := by
    unfold IsTangent
    refine hub.trans ?_
    have e : (1 : ptOver T.V T.V ⟶ G.t.G) = toUnit _ ≫ η[G.t.G] := rfl
    rw [e, Over.comp_left]
    have e2 : (toUnit (ptOver T.V T.V)).left = 𝟙 (Sp T.V) := by
      have := Over.w (toUnit (ptOver T.V T.V))
      exact ((Category.comp_id _).symm.trans this).trans (Spec.map_id _)
    rw [e2]
    exact Category.id_comp _
  obtain ⟨a, ha, -⟩ := hvV.2 ub' hub'

  have hw'' : u'' ≫ t'.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) := by
    apply spMap_frac_cancel (V := T.V)
    rw [Category.assoc, ← m2'.cart.1.w, ← Category.assoc, hu'', Category.assoc, Over.w ub]
    show spMap (dualMap (algebraMap T.V T.Fr)) ≫ spMap (algebraMap T.V (DualNumber T.V)) = _
    exact (spMap_comp_two _ _).trans ((congrArg spMap (dualMap_alg _)).trans (spMap_comp_two _ _).symm)

  have hsq : ∀ k, (spMap (dualMap (algebraMap T.V T.Fr)) ≫ (vV k).left) ≫ G.t.G.hom =
      spMap (algebraMap T.Fr (DualNumber T.Fr)) ≫ spMap (algebraMap T.V T.Fr) := fun k => by
    rw [Category.assoc, Over.w (vV k)]
    exact (spMap_comp_two _ _).trans ((congrArg spMap (dualMap_alg _)).trans (spMap_comp_two _ _).symm)
  let g : Fin F.P₀.g → (epsR T.Fr ⟶ t'.G) := fun k =>
    Over.homMk (m2'.cart.1.lift _ _ (hsq k)) (m2'.cart.1.lift_snd _ _ _)
  have hg1 : ∀ k, (g k).left ≫ m2'.φ = spMap (dualMap (algebraMap T.V T.Fr)) ≫ (vV k).left :=
    fun k => m2'.cart.1.lift_fst _ _ _
  have hB : IsGrpPullback t'.G B.t.G (spMap iK ≫ spMap (algebraMap (𝓞 K) K)) (n'.φ ≫ m2.φ) :=
    n'.cart.comp m2.cart
  have hT' := LieComb.lieComb_algebra T.Fr t'.G _ v' hv'.1
  have hgk : ∀ k, IsLieComb (fun l => iK (M k l)) v' (g k) := by
    intro k
    obtain ⟨wk, hwk, hwkeq⟩ := hM k
    obtain ⟨w₁, hw₁, -⟩ := hT'.1 (fun l => iK (M k l))
    have hf : spMap (RingHom.id T.Fr) ≫ (spMap iK ≫ spMap (algebraMap (𝓞 K) K)) =
        spMap iK ≫ spMap (algebraMap (𝓞 K) K) := by rw [spMap_id', Category.id_comp]
    have hm := LetterInt.comb_match hB F.fib.2.1 (RingHom.id T.Fr) iK hf
      (fun i => by rw [spMap_dualMap_id, Category.id_comp]; exact hv'φ i) (fun _ => rfl) hw₁ hwk
    rw [spMap_dualMap_id, Category.id_comp] at hm
    have he : w₁ = g k := by
      refine Over.OverMorphism.ext (hB.1.hom_ext ?_ ((Over.w w₁).trans (Over.w (g k)).symm))
      rw [hm, ← hwkeq, ← h2, ← Category.assoc (g k).left, hg1, Category.assoc]
    exact he ▸ hw₁

  have hgt : ∀ k, IsTangent (g k) := fun k => hT'.2.1 _ _ (hgk k)
  obtain ⟨w, hw, -⟩ := (LieComb.lieComb_algebra T.Fr t'.G _ g hgt).1 (fun k => algebraMap T.V T.Fr (a k))
  have hcomb := hT'.2.2.1 _ (fun k l => iK (M k l)) g _ w hgk hw
  have hf2 : spMap (algebraMap T.V T.Fr) ≫ 𝟙 (Sp T.V) = spMap (RingHom.id T.Fr) ≫ spMap (algebraMap T.V T.Fr) := by
    rw [spMap_id', Category.id_comp, Category.comp_id]
  have hm2 := LetterInt.comb_match (isGrpPullback_self G.t.G) m2'.cart (algebraMap T.V T.Fr) (RingHom.id T.Fr) hf2
    (v₁ := vV) (v₂ := g) (fun i => by rw [spMap_dualMap_id, Category.id_comp, Category.comp_id, hg1])
    (c₁ := a) (c₂ := fun k => algebraMap T.V T.Fr (a k)) (fun _ => rfl) ha hw
  rw [spMap_dualMap_id, Category.id_comp, Category.comp_id] at hm2
  have hleft : w.left = u'' := by
    refine m2'.cart.1.hom_ext ?_ ((Over.w w).trans hw''.symm)
    rw [← hm2, hu'']
    rfl
  exact ⟨a, w, hleft, hcomb⟩

end GlobalTheory.PtDeg.LieModel
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreIntegralTangentInSpanLieBasisStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.Frames

theorem _root_.GlobalTheory.T.genericFibre_integral_tangent_in_span_lieBasis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (K : Type) [Field K] [NumberField K] (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) (T : CDVR) (iK : K →+* T.Fr) (ρV : 𝓞 K →+* T.V), (algebraMap T.V T.Fr).comp ρV = iK.comp (algebraMap (𝓞 K) K) → ∀ (G : GlobalTheory.CM.PAT H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (n : SABMap G.t B.t (spMap ρV)) (n' : SABMap t' t₀ (spMap iK)) (m2' : SABMap t' G.t (spMap (algebraMap T.V T.Fr))), m2'.φ ≫ n.φ = n'.φ ≫ m2.φ → ∀ (v' : Fin F.P₀.g → (epsR T.Fr ⟶ t'.G)), IsLieBasis v' → (∀ k, (v' k).left ≫ n'.φ ≫ m2.φ = spMap (Formalism.L2.Pj.dualMap iK) ≫ (F.v k).left ≫ F.φ) → ∀ (vV : Fin F.P₀.g → (epsR T.V ⟶ G.t.G)) (M : Fin F.P₀.g → Fin F.P₀.g → K), IsLieBasis vV → (∀ k, ∃ w : epsR K ⟶ F.P₀.A, IsLieComb (M k) F.v w ∧ spMap (Formalism.L2.Pj.dualMap (algebraMap T.V T.Fr)) ≫ (vV k).left ≫ n.φ = spMap (Formalism.L2.Pj.dualMap iK) ≫ w.left ≫ F.φ) → ∀ (ub : epsOver T.V T.V ⟶ G.t.G) (u'' : Sp (DualNumber T.Fr) ⟶ t'.G.left), IsTan ub → u'' ≫ m2'.φ = spMap (Formalism.L2.Pj.dualMap (algebraMap T.V T.Fr)) ≫ ub.left → ∃ (a : Fin F.P₀.g → T.V) (w'' : epsR T.Fr ⟶ t'.G), w''.left = u'' ∧ IsLieComb (∑ k, algebraMap T.V T.Fr (a k) • fun l => iK (M k l)) v' w'' := by
  first | exact @GlobalTheory.PtDeg.LieModel.generic_coords_in_span | exact GlobalTheory.PtDeg.LieModel.generic_coords_in_span | (intros; apply GlobalTheory.PtDeg.LieModel.generic_coords_in_span <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmPointIntegralFrameMemSpanEigenLattice

section

@[expose] public section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.Frames

theorem GlobalTheory.PtDeg.intFrame_mem_span_eigLat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K) (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m1 : SABMap t₀ Xo.univ.t y.x) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) (ρ : E →+* ℂ) (tt : 𝓞 E →+* 𝓞 K), (∀ a, ((tt a : 𝓞 K) : K) = algebraMap c.F K (embK c ρ a)) → ∀ (u : Fin (Dw.mult ρ) → Fin F.P₀.g → K), GlobalTheory.PtDeg.FrameCoord y m1 m2 F ρ u → ∀ (𝔓 : HeightOneSpectrum (𝓞 K)) (T : CDVR) (iK : K →+* T.Fr), (∀ z : K, iK z ∈ Set.range (algebraMap T.V T.Fr) ↔ 𝔓.valuation K z ≤ 1) → ∀ (ρV : 𝓞 K →+* T.V), (algebraMap T.V T.Fr).comp ρV = iK.comp (algebraMap (𝓞 K) K) → letI := (iK.comp (algebraMap c.F K)).toAlgebra; ∀ (yT : FrPt Xo c T.Fr), FrMap ({ iK with commutes' := fun _ => rfl } : K →ₐ[c.F] T.Fr) y yT → ∀ (G : GlobalTheory.CM.PAT H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (n : SABMap G.t B.t (spMap ρV)) (n' : SABMap t' t₀ (spMap iK)) (m1' : SABMap t' Xo.univ.t yT.x) (m2' : SABMap t' G.t (spMap (algebraMap T.V T.Fr))), m1'.φ = n'.φ ≫ m1.φ → m2'.φ ≫ n.φ = n'.φ ≫ m2.φ → ∀ (C : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) T.Fr) (a : T.Fr) (y' : FrPt Xo c T.Fr), FrChg C a yT y' → GlobalTheory.LamT.LieInt T (iK.comp (algebraMap c.F K)) m1' m2' y'.u → (∀ i, (∑ j, C ρ i j • fun k => iK (u j k)) ∈ Submodule.span T.V ((fun (v : Fin F.P₀.g → K) k => iK (v k)) '' (F.eigLat B.t.act tt : Set (Fin F.P₀.g → K)))) := by
  intro E _ _ _ H Dw l Xo c K _ _ _ y B t₀ m1 m2 F ρ tt htt u hu 𝔓 T iK hiK ρV hρV
  letI := (iK.comp (algebraMap c.F K)).toAlgebra
  intro yT hyT G t' n n' m1' m2' h1 h2 C a y' hchg hint i
  obtain ⟨v', hv', hv'φ⟩ := GlobalTheory.T.exists_lieBasis_fibre_over_completion_fraction_field E H K B t₀ m2 F T iK t' n'
  obtain ⟨vV, hvV, hvVM⟩ := GlobalTheory.T.exists_lieBasis_completion_in_span_lieLattice E H K B F 𝔓 T iK hiK ρV hρV G n
  choose M w hMw hMn hMspan using hvVM
  obtain ⟨ub, hubT, -, -, hubu⟩ := hint
  obtain ⟨u', hu'1, hu'2⟩ := hubu ρ i
  obtain ⟨av, w₁, hw₁, hw₁c⟩ := GlobalTheory.T.genericFibre_integral_tangent_in_span_lieBasis E H K B t₀ m2 F T iK ρV hρV G t' n n' m2' h2 v' hv' hv'φ vV M hvV
    (fun k => ⟨w k, hMw k, hMn k⟩) (ub ρ i) u' (hubT ρ i) hu'2
  have hbase : u' ≫ t'.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) := by
    rw [← hw₁]; exact Over.w w₁
  obtain ⟨w₂, hw₂, hw₂c⟩ := GlobalTheory.T.framedPoint_genericFibre_coordinates_eq_frame E H Dw l Xo c K y B t₀ m1 m2 F ρ u hu T iK yT hyT t' n' m1' h1 v' hv'
    hv'φ C a y' hchg i u' hbase hu'1
  obtain rfl : w₁ = w₂ := Over.OverMorphism.ext (hw₁.trans hw₂.symm)
  have htan : IsTangent w₁ :=
    (GlobalTheory.LieComb.lieComb_algebra T.Fr t'.G _ v' hv'.1).2.1 _ _ hw₁c
  have heq := (hv'.2 w₁ htan).unique hw₁c hw₂c
  have hWlie : (∑ j, C ρ i j • fun k => iK (u j k)) ∈ Submodule.span T.V
      ((fun (v : Fin F.P₀.g → K) k => iK (v k)) '' (F.lieLat : Set (Fin F.P₀.g → K))) := by
    rw [← heq]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [algebraMap_smul]
    exact Submodule.smul_mem _ _ (hMspan k)
  obtain ⟨r', -, hr'⟩ := GlobalTheory.T.exists_lieRepresentation_eigenLattices K B.pol F (𝓞 E) B.t.act
  have hueig : ∀ j a, r' a (u j) = ((tt a : 𝓞 K) : K) • u j := by
    intro j a
    have := ((hr' tt (u j)).2).1 (GlobalTheory.T.framedPoint_coordinates_mem_span_eigenLattice E H Dw l Xo c K y B t₀ m1 m2 F ρ tt htt u hu j) a
    rw [this, ← algebraMap_smul K (tt a) (u j)]
  have hx := GlobalTheory.T.completed_span_eigen_vector_mem_eigen_sublattice K F.P₀.g F.lieLat (𝓞 E) (fun a => LinearMap.toMatrix' (r' a))
    (fun a => ((tt a : 𝓞 K) : K)) 𝔓 T iK hiK (GlobalTheory.T.lieLattice_fg_and_span_eq_top_ringOfIntegers K B.pol F).1 _ hWlie (fun a => by
      rw [Matrix.mulVec_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Matrix.mulVec_smul, smul_comm]
      congr 1
      funext k
      rw [show (fun k => iK (u j k)) = iK ∘ u j from rfl, ← RingHom.map_mulVec, LinearMap.toMatrix'_mulVec, hueig j a]
      simp)
  refine Submodule.span_mono ?_ hx
  rintro _ ⟨c', ⟨hc1, hc2⟩, rfl⟩
  refine ⟨c', (hr' tt c').1.2 ⟨hc1, fun a => ?_⟩, rfl⟩
  have := hc2 a
  rw [LinearMap.toMatrix'_mulVec] at this
  rw [this, ← algebraMap_smul K (tt a) c']
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmPointIntegralFrameMemSpanEigenLatticeStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.Frames

theorem _root_.GlobalTheory.T.cm_point_integral_frame_mem_span_eigen_lattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K) (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m1 : SABMap t₀ Xo.univ.t y.x) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) (ρ : E →+* ℂ) (tt : 𝓞 E →+* 𝓞 K), (∀ a, ((tt a : 𝓞 K) : K) = algebraMap c.F K (embK c ρ a)) → ∀ (u : Fin (Dw.mult ρ) → Fin F.P₀.g → K), GlobalTheory.PtDeg.FrameCoord y m1 m2 F ρ u → ∀ (𝔓 : HeightOneSpectrum (𝓞 K)) (T : CDVR) (iK : K →+* T.Fr), (∀ z : K, iK z ∈ Set.range (algebraMap T.V T.Fr) ↔ 𝔓.valuation K z ≤ 1) → ∀ (ρV : 𝓞 K →+* T.V), (algebraMap T.V T.Fr).comp ρV = iK.comp (algebraMap (𝓞 K) K) → letI := (iK.comp (algebraMap c.F K)).toAlgebra; ∀ (yT : FrPt Xo c T.Fr), FrMap ({ iK with commutes' := fun _ => rfl } : K →ₐ[c.F] T.Fr) y yT → ∀ (G : GlobalTheory.CM.PAT H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (n : SABMap G.t B.t (spMap ρV)) (n' : SABMap t' t₀ (spMap iK)) (m1' : SABMap t' Xo.univ.t yT.x) (m2' : SABMap t' G.t (spMap (algebraMap T.V T.Fr))), m1'.φ = n'.φ ≫ m1.φ → m2'.φ ≫ n.φ = n'.φ ≫ m2.φ → ∀ (C : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) T.Fr) (a : T.Fr) (y' : FrPt Xo c T.Fr), FrChg C a yT y' → GlobalTheory.LamT.LieInt T (iK.comp (algebraMap c.F K)) m1' m2' y'.u → (∀ i, (∑ j, C ρ i j • fun k => iK (u j k)) ∈ Submodule.span T.V ((fun (v : Fin F.P₀.g → K) k => iK (v k)) '' (F.eigLat B.t.act tt : Set (Fin F.P₀.g → K)))) := by
  first | exact @GlobalTheory.PtDeg.intFrame_mem_span_eigLat | exact GlobalTheory.PtDeg.intFrame_mem_span_eigLat | (intros; apply GlobalTheory.PtDeg.intFrame_mem_span_eigLat <;> assumption)
end
end
