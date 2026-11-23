module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LocalIntegralGL
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.GoodIdempotentBadPlaces
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Formalism.LocalRingCardinality.DataHost
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.LocalToGlobal.Divisibility.DefGroup
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Formalism.LocalRingCardinality.DataHost
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelAndTwistPlacesSplitDistinct
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasureToRealEqMass
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelLeStabilizerSelfDualLatticeFrame
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelVectorSquareNormEqProdLocalVolumesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InnerProductFormula
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexLevelSelfDualStabilizerEqProdLocal
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.CardGLDivParabolicIndexFiniteField

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)

namespace GlobalTheory.Twist.GLIndexLoc

theorem card_GL_real_eq (κ : Type) [Field κ] [Finite κ] (n : ℕ) :
    (Nat.card (GL (Fin n) κ) : ℝ) =
      (Nat.card κ : ℝ) ^ (n ^ 2) * ∏ i ∈ Finset.Ioc 0 n, (1 - ((Nat.card κ : ℝ) ^ i)⁻¹) := by
  haveI := Fintype.ofFinite κ
  have hq1 : 1 ≤ Nat.card κ := Nat.one_le_iff_ne_zero.mpr (Nat.card_pos).ne'
  have hq0 : (Nat.card κ : ℝ) ≠ 0 := by positivity
  rw [Matrix.card_GL_field, Nat.cast_prod, ← Nat.card_eq_fintype_card]
  rw [Fin.prod_univ_eq_prod_range (fun i => ((Nat.card κ ^ n - Nat.card κ ^ i : ℕ) : ℝ)) n]
  rw [← Finset.prod_range_reflect]
  have hIoc : Finset.Ioc 0 n = (Finset.range n).map ⟨(· + 1), add_left_injective 1⟩ := by
    ext x
    simp only [Finset.mem_Ioc, Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨x - 1, by omega, by omega⟩
    · rintro ⟨y, hy, rfl⟩; omega
  rw [hIoc, Finset.prod_map, sq, pow_mul,
    show ((Nat.card κ : ℝ) ^ n) ^ n = ∏ _j ∈ Finset.range n, (Nat.card κ : ℝ) ^ n by simp,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun j hj => ?_)
  have hj' : j < n := Finset.mem_range.mp hj
  have hle : Nat.card κ ^ (n - 1 - j) ≤ Nat.card κ ^ n := Nat.pow_le_pow_right hq1 (by omega)
  simp only [Function.Embedding.coeFn_mk]
  rw [Nat.cast_sub hle, Nat.cast_pow, Nat.cast_pow, mul_sub, mul_one]
  congr 1
  have hsplit : (Nat.card κ : ℝ) ^ n = (Nat.card κ : ℝ) ^ (n - 1 - j) * (Nat.card κ : ℝ) ^ (j + 1) := by
    rw [← pow_add]; congr 1; omega
  rw [hsplit, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hq0), mul_one]

theorem index_loc : ∀ (κ : Type) [Field κ] [Finite κ] (n r t : ℕ), n = r + t → (Nat.card (GL (Fin n) κ) : ℝ) / ((Nat.card (GL (Fin t) κ) : ℝ) * (Nat.card κ : ℝ) ^ (r * t)) * ((Nat.card κ : ℝ) ^ (r ^ 2 + r * t))⁻¹ = ∏ i ∈ Finset.Ioc t n, (1 - ((Nat.card κ : ℝ) ^ i)⁻¹) := by
  intro κ _ _ n r t hn
  haveI := Fintype.ofFinite κ
  have hq2 : (2 : ℝ) ≤ Nat.card κ := by
    have := Fintype.one_lt_card (α := κ)
    rw [← Nat.card_eq_fintype_card] at this
    exact_mod_cast this
  have hq0 : (Nat.card κ : ℝ) ≠ 0 := by positivity
  have hP : ∏ i ∈ Finset.Ioc 0 t, (1 - ((Nat.card κ : ℝ) ^ i)⁻¹) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr (fun i hi => ?_)
    have hi1 : 1 ≤ i := (Finset.mem_Ioc.mp hi).1
    have : (2 : ℝ) ≤ (Nat.card κ : ℝ) ^ i :=
      le_trans hq2 (le_self_pow₀ (by linarith) (by omega))
    have : ((Nat.card κ : ℝ) ^ i)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
    linarith
  rw [card_GL_real_eq, card_GL_real_eq,
    ← Finset.prod_Ioc_consecutive _ (Nat.zero_le t) (show t ≤ n by omega)]
  have hpow : (Nat.card κ : ℝ) ^ (n ^ 2) =
      (Nat.card κ : ℝ) ^ (t ^ 2) * (Nat.card κ : ℝ) ^ (r * t) * (Nat.card κ : ℝ) ^ (r ^ 2 + r * t) := by
    rw [← pow_add, ← pow_add]; congr 1; subst hn; ring
  rw [hpow]
  generalize ∏ i ∈ Finset.Ioc 0 t, (1 - ((Nat.card κ : ℝ) ^ i)⁻¹) = P at hP ⊢
  generalize ∏ i ∈ Finset.Ioc t n, (1 - ((Nat.card κ : ℝ) ^ i)⁻¹) = Q
  have h1 : (Nat.card κ : ℝ) ^ (t ^ 2) ≠ 0 := pow_ne_zero _ hq0
  have h2 : (Nat.card κ : ℝ) ^ (r * t) ≠ 0 := pow_ne_zero _ hq0
  have h3 : (Nat.card κ : ℝ) ^ (r ^ 2 + r * t) ≠ 0 := pow_ne_zero _ hq0
  field_simp

end GlobalTheory.Twist.GLIndexLoc
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.CardGLDivParabolicIndexFiniteFieldStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)


theorem _root_.GlobalTheory.T.card_GL_div_parabolic_index_finiteField : ∀ (κ : Type) [Field κ] [Finite κ] (n r t : ℕ), n = r + t → (Nat.card (GL (Fin n) κ) : ℝ) / ((Nat.card (GL (Fin t) κ) : ℝ) * (Nat.card κ : ℝ) ^ (r * t)) * ((Nat.card κ : ℝ) ^ (r ^ 2 + r * t))⁻¹ = ∏ i ∈ Finset.Ioc t n, (1 - ((Nat.card κ : ℝ) ^ i)⁻¹) := by
  first | exact @GlobalTheory.Twist.GLIndexLoc.index_loc | exact GlobalTheory.Twist.GLIndexLoc.index_loc | (intros; apply GlobalTheory.Twist.GLIndexLoc.index_loc <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelAndTwistPlacesSplitDistinctStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)
open Classical


theorem _root_.GlobalTheory.T.levelAndTwistPlaces_split_distinct : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ t : T, Disjoint R.Pg (R.Q t) ∧ Set.InjOn (fun PP : Pl D.host.E => (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) ↑(R.Pg ∪ R.Q t) ∧ ∀ PP ∈ R.Pg ∪ R.Q t, (Ideal.primesOver ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)).asIdeal (𝓞 D.host.E)).ncard = 2 ∧ Nat.card (kP PP) = Ideal.absNorm ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)).asIdeal := by
  first | exact @GlobalTheory.TwistTypePlaces.places_split | exact GlobalTheory.TwistTypePlaces.places_split | (intros; apply GlobalTheory.TwistTypePlaces.places_split <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelLeStabilizerSelfDualLatticeFrameStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)


theorem _root_.GlobalTheory.T.level_le_stabilizer_selfDual_lattice_frame : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank), Formalism.IndefR.Lev.IsBaseFrame V β Λ 1 → Formalism.L2.DIV.lev D.sp.cm V.gram β L ≤ GlobalTheory.Mass.Levels.latLev V := by
  first | exact @GlobalTheory.LevelInLatStab.lev_le_latLev | exact GlobalTheory.LevelInLatStab.lev_le_latLev | (intros; apply GlobalTheory.LevelInLatStab.lev_le_latLev <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexLevelSelfDualStabilizerEqProdLocalStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)


theorem _root_.GlobalTheory.T.relIndex_level_selfDual_stabilizer_eq_prod_local : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (i : Fin D.R.m) (t : T) (P : LevelP R.Pg D.R.r ℂ) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Hl : ∀ PP : ↥R.Pg, Subgroup (GL (Fin D.R.r) (kP PP.1))) (cl : ∀ PP : ↥R.Pg, Hl PP →* ℂˣ), GlobalTheory.Hk3.Core R F → P = LevelP.ofLocal Hl cl → (((GlobalTheory.AdelicScalar.levV R i t P m).relIndex (GlobalTheory.Mass.Levels.latLev (Vc D i)) : ℕ) : ℝ) = (∏ PP ∈ R.Pg.attach, (Nat.card (GL (Fin (Vc D i).rank) (kP PP.1)) : ℝ) / ((Nat.card (Hl PP) : ℝ) * (Nat.card (GL (Fin D.R.t) (kP PP.1)) : ℝ) * (Nat.card (kP PP.1) : ℝ) ^ (D.R.r * D.R.t))) * ∏ PP ∈ R.Q t, (Nat.card (GL (Fin (Vc D i).rank) (kP PP)) : ℝ) / ((Nat.card (GL (Fin D.R.r) (kP PP)) : ℝ) * (Nat.card (GL (Fin D.R.t) (kP PP)) : ℝ) * (Nat.card (kP PP) : ℝ) ^ (D.R.r * D.R.t)) := by
  first | exact @GlobalTheory.ParIndex.relIndex_levV_latLev | exact GlobalTheory.ParIndex.relIndex_levV_latLev | (intros; apply GlobalTheory.ParIndex.relIndex_levV_latLev <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLevelIndexMulSchwartzNormFormula

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)

namespace GlobalTheory.LevelIndex

theorem levelIndexNormC : GlobalTheory.IndefiniteRowSideFullHecke.LocalIntegralGL.LocalIntegralSingleBlock → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.PlaceModels D → LevelIndexNormC R F := by
  intro hLoc D G _ _ Pl0 T A Ks _ _ _ R F hPM
  intro i t σ s P cμ cη m ω BW f₀ f c io hd
  classical
  have hC : Hk3.Core R F := hd.1
  obtain ⟨Hl, cl, hP⟩ := hd.2.2.2.1
  refine ⟨?_, fun μ 𝓧 hμ => ?_⟩
  · obtain ⟨c0, hc0⟩ := hC.lev.βV i
    rw [one_pow] at hc0
    exact GlobalTheory.T.level_le_stabilizer_selfDual_lattice_frame D (Vc D i) _ _ _ hc0
  · have hn := GlobalTheory.T.levelVector_squareNorm_eq_prod_localVolumes hLoc R F hPM i t σ s P cμ cη m ω BW f₀ f c io hd Hl cl hP μ 𝓧 hμ
    rw [GlobalTheory.T.relIndex_level_selfDual_stabilizer_eq_prod_local R F i t P m Hl cl hC hP, hn]
    obtain ⟨hdis, hinj, hsp⟩ := GlobalTheory.T.levelAndTwistPlaces_split_distinct R F hC t
    have hrank : (Vc D i).rank = D.R.nV := D.sp.V_rank _ (Nat.le_add_left _ _) i.2
    have hrt : (Vc D i).rank = D.R.r + D.R.t := D.sp.V_rank _ (Nat.le_add_left _ _) i.2
    have key : ∀ PP ∈ R.Pg ∪ R.Q t, (dLoc D ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)))⁻¹ =
        (Nat.card (GL (Fin (Vc D i).rank) (kP PP)) : ℝ) / ((Nat.card (GL (Fin D.R.t) (kP PP)) : ℝ) *
          (Nat.card (kP PP) : ℝ) ^ (D.R.r * D.R.t)) * ((Nat.card (kP PP) : ℝ) ^ (D.R.r ^ 2 + D.R.r * D.R.t))⁻¹ := by
      intro PP hPP
      obtain ⟨h2, hq⟩ := hsp PP hPP
      haveI : Fact PP.asIdeal.IsMaximal := ⟨PP.isMaximal⟩
      letI : Field (kP PP) := Ideal.Quotient.field _
      rw [GlobalTheory.T.card_GL_div_parabolic_index_finiteField (kP PP) _ D.R.r D.R.t hrt, hrank]
      unfold dLoc quadTerm quadSign
      rw [if_pos h2, ← Finset.prod_inv_distrib]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [inv_inv, hq]
      simp
    have hcard : ∀ PP : Pl D.host.E, ∀ n : ℕ, (Nat.card (GL (Fin n) (kP PP)) : ℝ) ≠ 0 := fun PP n => by
      have : Finite (GL (Fin n) (kP PP)) := inferInstance
      exact_mod_cast (Nat.card_pos (α := GL (Fin n) (kP PP))).ne'
    have hHl : ∀ PP, (Nat.card (Hl PP) : ℝ) ≠ 0 := fun PP => by
      exact_mod_cast (Nat.card_pos (α := Hl PP)).ne'
    have hq0 : ∀ PP : Pl D.host.E, (Nat.card (kP PP) : ℝ) ≠ 0 := fun PP => by
      exact_mod_cast (Nat.card_pos (α := kP PP)).ne'
    unfold finS
    rw [Finset.prod_image hinj, Finset.prod_union hdis, ← Finset.prod_attach R.Pg, mul_mul_mul_comm,
      ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    congr 1
    · refine Finset.prod_congr rfl fun PP _ => ?_
      rw [key PP.1 (Finset.mem_union_left _ PP.2)]
      field_simp [hHl PP, hcard PP.1, hq0 PP.1]
    · refine Finset.prod_congr rfl fun PP hPP => ?_
      rw [key PP (Finset.mem_union_right _ hPP)]
      field_simp [hcard PP, hq0 PP]

end GlobalTheory.LevelIndex

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLevelIndexMulSchwartzNormFormulaStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaLevelIndex_mul_schwartzNorm_formula : GlobalTheory.IndefiniteRowSideFullHecke.LocalIntegralGL.LocalIntegralSingleBlock → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.PlaceModels D → LevelIndexNormC R F := by
  first | exact @GlobalTheory.LevelIndex.levelIndexNormC | exact GlobalTheory.LevelIndex.levelIndexNormC | (intros; apply GlobalTheory.LevelIndex.levelIndexNormC <;> assumption)
end
end
