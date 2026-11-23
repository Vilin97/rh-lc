module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.CstSmoothOfEtSide
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.HodgeTateSpectral.HTSpecGood
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.HtBijOfParts
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.SpecOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtSideGoodHolds
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.TowerRallisLemma
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.BlowBC
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.BlowOfBl
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FinCover
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.BlowUpOff
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.BlowUpSmooth
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.CrossOfRel
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.ExSmooth
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.ProjProd
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
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
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.BlowOfBl
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsExtraAlt
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IntegralityNearIdentity.IsIntegralOfNormLe
import Mathlib.RingTheory.RegularLocalRing.Defs
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.ProjProd
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.SubstXZero
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CommRingSections.IsCovPr
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CoverRefinementHodge.FinalC
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.HodgeTateComparisonSmoothProjective
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.HtBijOf

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.BlowUpTop

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor UpperTheory.Gal.DifferentialFormSections
open FunctorialResolution.Blowup

theorem UpperTheory.Gal.KunnethLefschetz.G.blTop :
    UpperTheory.Gal.KunnethLefschetz.G.BlowUpTop := by
  intro R _ _ Z d _ hZ
  have hprop := (UpperTheory.Gal.KunnethLefschetz.G.projProd R (Over.hom Z) (Over.hom Z) hZ).2.2
  haveI : IsSeparated (Over.hom Z) := inferInstance
  haveI : LocallyOfFiniteType (Over.hom Z) := inferInstance
  have hXX : IsProjOver (Over.hom (UpperTheory.Gal.KunnethLefschetz.G.XX Z)) :=
    (UpperTheory.Gal.KunnethLefschetz.G.projProd R (Over.hom Z) (Over.hom Z) hZ).1 hZ
  obtain ⟨Y, πl, hπ⟩ := exists_isBlowupAlongIdealSheaf (UpperTheory.Gal.KunnethLefschetz.G.XX Z).left
    (Scheme.Hom.ker (Over.Hom.left (UpperTheory.Gal.KunnethLefschetz.G.dg Z)))
  let W : Sch R := Over.mk (πl ≫ Over.hom (UpperTheory.Gal.KunnethLefschetz.G.XX Z))
  let π : W ⟶ UpperTheory.Gal.KunnethLefschetz.G.XX Z := Over.homMk πl rfl
  have hBl : UpperTheory.Gal.KunnethLefschetz.G.IsBl π := hπ
  have hW : IsProjOver (Over.hom W) := by
    obtain ⟨M, f, h, hci⟩ :=
      UpperTheory.Gal.KunnethLefschetz.G.blEmb R (Over.hom (UpperTheory.Gal.KunnethLefschetz.G.XX Z)) hXX _ πl hπ
    have hstr : IsProjOver (PSpace.str R M) := ⟨M, 𝟙 _, inferInstance, by simp⟩
    have hP := (UpperTheory.Gal.KunnethLefschetz.G.projProd R (Over.hom (UpperTheory.Gal.KunnethLefschetz.G.XX Z))
      (PSpace.str R M) hXX).1 hstr
    have h2 := (UpperTheory.Gal.KunnethLefschetz.G.projProd R _ (πl ≫ Over.hom (UpperTheory.Gal.KunnethLefschetz.G.XX Z)) hP).2.1 _ hci
    rw [pullback.lift_fst_assoc] at h2
    exact h2
  have hoff := UpperTheory.Gal.KunnethLefschetz.G.blOff R π hBl
  have hEx : IsProjOver (Over.hom (UpperTheory.Gal.KunnethLefschetz.G.Ex π)) := by
    have h2 := (UpperTheory.Gal.KunnethLefschetz.G.projProd R (Over.hom W) (Over.hom (UpperTheory.Gal.KunnethLefschetz.G.Ex π)) hW).2.1
      _ hoff.2.1
    rwa [Over.w] at h2
  have hsm := UpperTheory.Gal.KunnethLefschetz.G.blSmooth R (d + 1) π hBl
  have hex := UpperTheory.Gal.KunnethLefschetz.G.exSmooth R d π hBl
  refine ⟨W, π, hBl, hXX, hW, hEx, ?_, hsm.2, ?_⟩
  · haveI : SmoothOfRelativeDimension (d + 1) (pullback.fst (Over.hom Z) (Over.hom Z)) :=
      MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension (d + 1))
        (self := smoothOfRelativeDimension_isStableUnderBaseChange (d + 1))
        (IsPullback.of_hasPullback (Over.hom Z) (Over.hom Z)).flip inferInstance
    show SmoothOfRelativeDimension (d + 1 + (d + 1))
      (pullback.fst (Over.hom Z) (Over.hom Z) ≫ Over.hom Z)
    infer_instance
  · haveI := hex.1
    rw [← Over.w (UpperTheory.Gal.KunnethLefschetz.G.exG π)]
    infer_instance
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.IntegralityNearIdentity.EqOneOfNear

section

@[expose] public section

namespace UpperTheory.V.Lib.Small

theorem norm_le_one_of_isIntegral (l : ℕ) [Fact l.Prime] (x : PadicAlgCl l) (hx : IsIntegral ℤ_[l] x) : ‖x‖ ≤ 1 :=
  _root_.UpperTheory.Reformulated.B.S6.norm_le_one_of_isIntegral l x hx

end UpperTheory.V.Lib.Small
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.OKDvr

section

@[expose] public section

theorem UpperTheory.Gal.KunnethLefschetz.G.oKDvr :
    UpperTheory.Gal.KunnethLefschetz.G.OKDvr := by
  intro l _ K _
  have hK : (CrystallineSemistableComparison.OK l K) = (integralClosure ℤ_[l] K).toSubring := by
    ext x
    constructor
    · intro hx
      have h1 : ‖(x : PadicAlgCl l)‖ ≤ 1 := hx
      have h2 : IsIntegral ℤ_[l] (x : PadicAlgCl l) := UpperTheory.V.Lib.Small.isIntegral_of_norm_le h1
      exact (isIntegral_algHom_iff (K.val.restrictScalars ℤ_[l]) Subtype.val_injective).1 h2
    · intro hx
      have h2 : IsIntegral ℤ_[l] (x : PadicAlgCl l) := IsIntegral.map (K.val.restrictScalars ℤ_[l]) hx
      exact UpperTheory.V.Lib.Small.norm_le_one_of_isIntegral l _ h2
  rw [hK]
  exact (IsIntegralClosure.isNoetherianRing ℤ_[l] ℚ_[l] K (integralClosure ℤ_[l] K))
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.SqCore

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry UpperTheory.Gal.DifferentialFormSections ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Onto

theorem UpperTheory.Gal.KunnethLefschetz.G.sqCore (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K]
    (M : Model l K) (d : ℕ) (hM : M.Sm) (hd : SmoothOfRelativeDimension (d + 1) M.p) : ∃ S : Sq M (d + 1), Etale S.D.f := by
  obtain ⟨⟨hproj, ϖ, hϖ, -⟩, -⟩ := hM
  haveI : IsNoetherianRing (OK l K) := oKDvr l K
  let Z : Sch (OK l K) := Over.mk M.p
  haveI : SmoothOfRelativeDimension (d + 1) Z.hom := hd
  obtain ⟨W, π, hbl, hXp, hWp, -, hXs, hWs, -⟩ := blTop (OK l K) Z d hproj
  haveI : IsProper Z.hom := ((projProd (OK l K) Z.hom Z.hom hproj).2.2)
  obtain ⟨D, het, ⟨B⟩⟩ := blowOfBl (OK l K) (d + 1) π hbl
  let P : Model l K := ⟨(XX Z).left, (XX Z).hom⟩
  let Y : Model l K := ⟨W.left, W.hom⟩
  have hΔ : (dg Z).left ≫ P.p = M.p := Over.w (dg Z)
  have hπ : π.left ≫ P.p = Y.p := Over.w π
  haveI : Smooth P.p := SmoothOfRelativeDimension.smooth (d + 1 + (d + 1)) P.p
  haveI : Smooth Y.p := SmoothOfRelativeDimension.smooth (d + 1 + (d + 1)) Y.p
  have hP : P.Sm := ⟨⟨hXp, ϖ, hϖ, smSst _ ϖ P.p⟩, inferInstance⟩
  have hY : Y.Sm := ⟨⟨hWp, ϖ, hϖ, smSst _ ϖ Y.p⟩, inferInstance⟩
  have sq₀ : IsPullback (pullback.fst P.p (Spec.map (CommRingCat.ofHom (OK l K).subtype))) P.q P.p
      (Spec.map (CommRingCat.ofHom (OK l K).subtype)) := IsPullback.of_hasPullback _ _
  have sqΔ : IsPullback (pullback.fst M.p (Spec.map (CommRingCat.ofHom (OK l K).subtype)))
      (Model.genMap (M := M) (N := P) (dg Z).left hΔ) (dg Z).left
      (pullback.fst P.p (Spec.map (CommRingCat.ofHom (OK l K).subtype))) := by
    refine IsPullback.of_bot ?_ (pullback.lift_fst _ _ _).symm sq₀
    rw [Model.genMap_q, hΔ]
    exact IsPullback.of_hasPullback _ _
  have sqπ : IsPullback (pullback.fst Y.p (Spec.map (CommRingCat.ofHom (OK l K).subtype)))
      (Model.genMap (M := Y) (N := P) π.left hπ) π.left
      (pullback.fst P.p (Spec.map (CommRingCat.ofHom (OK l K).subtype))) := by
    refine IsPullback.of_bot ?_ (pullback.lift_fst _ _ _).symm sq₀
    rw [Model.genMap_q, hπ]
    exact IsPullback.of_hasPullback _ _
  exact ⟨{
    P := P, Y := Y, p₁ := (p1 Z).left, p₂ := (p2 Z).left, Δ := (dg Z).left, π := π.left
    h₁ := Over.w (p1 Z), h₂ := Over.w (p2 Z), hΔ := hΔ, hπ := hπ
    Δ₁ := pullback.diagonal_fst _, Δ₂ := pullback.diagonal_snd _
    prod := IsPullback.of_hasPullback _ _
    smP := hP, smY := hY, D := D, loc := B.loc
    blow := blowBC (OK l K) K (OK l K).subtype (XX Z).hom (dg Z).left π.left D (d + 1) P.q _ _ _ _ _ sq₀ sqΔ sqπ ⟨B⟩ }, het⟩

theorem UpperTheory.Gal.KunnethLefschetz.G.sqEx3 : CrystallineSemistableComparison.Onto.SqEx3 := fun l _ K _ M d _ h1 h2 => UpperTheory.Gal.KunnethLefschetz.G.sqCore l K M d h1 h2
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.ClosedHT

section

@[expose] public section

namespace UpperTheory.Gal.Seam.HT

open UpperTheory.Gal.Seam

open CrystallineSemistableComparison UpperTheory.Gal.KunnethLefschetz

theorem etSideS : EtSideS := fun l _ K _ => Top.etSide_sm_holds l K

theorem hodgeTate_comparison_smooth_projective : CrystallineSemistableComparison.HT.HodgeTateMapExists := CrystallineSemistableComparison.HT.hodgeTate_of_etale_side etSideS

theorem htBij : Onto.HTBij := Onto.htBij_of hodgeTate_comparison_smooth_projective G.sqEx3 Top.diagEt3_holds Top.etFin_holds

theorem htSpecGood : HTSpecB.HTSpecGood := Spec.htSpecGood_of htBij CrystallineSemistableComparison.Om.Nt2F.hodge_iso_natural_cech Top.etFin_holds

end UpperTheory.Gal.Seam.HT
end
end
