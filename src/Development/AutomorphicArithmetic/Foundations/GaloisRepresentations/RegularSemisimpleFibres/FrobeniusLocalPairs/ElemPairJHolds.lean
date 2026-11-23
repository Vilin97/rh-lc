module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IntersectionFamilySymmetric
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.ElemPairJ
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.NumberField
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.MatchSmulAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.BrMain
public import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.MatchOne
public import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.BallSub
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.ElemLocOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.NormDiag
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.QuotFubiniHolds
public import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.RootEx
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
import Mathlib.Tactic.ENatToNat
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
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.OneField
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.ScalarCover
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.StrictMap
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.StrictNear
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.VolRatio
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.ElemTest
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.MatchSmul
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.NormDiag
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.NormTriv
import GroundTheory.GlobalFields.NormResidueSymbol.FunctorialFinite
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.GelfandKazhdanReal
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.CharZeroAdicCompletion
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.ElemPairJ
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.FinAct
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.FinTrace
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.FrobFacts
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.InflFacts
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.InflTrace
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.RamOne

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.NormOpen

section

@[expose] public section

open ValuativeRel UpperTheory.ConvolutionTheory.Loc

theorem UpperTheory.Gal.InertialTypesAlt.L.normOpen :
    UpperTheory.Gal.InertialTypesAlt.L.NormOpen := by
  intro k E _ _ _ _ _ _ _ _ _ _ _ _ _ σ _ r hr0 hr1
  have hc : Continuous (algebraMap k E) := (UpperTheory.V.Z.Tf.Orb.extCont_holds k E).1
  have hS : {z : E | valuation E (z - 1) < r} ∈ nhds (algebraMap k E 1) := by
    rw [map_one]
    exact (IsValuativeTopology.hasBasis_nhds' (1 : E)).mem_of_mem hr0.ne'
  obtain ⟨γ, hγ0, hγ⟩ :=
    (IsValuativeTopology.hasBasis_nhds' (1 : k)).mem_iff.mp (hc.continuousAt.preimage_mem_nhds hS)
  set d := Module.finrank k E with hd
  have hdpos : 0 < d := Module.finrank_pos
  have hdk : (d : k) ≠ 0 := Nat.cast_ne_zero.mpr hdpos.ne'
  set δ := valuation k (d : k) with hδ
  have hδ0 : δ ≠ 0 := by simpa [hδ] using hdk
  have hδ1 : δ ≤ 1 := by
    rw [hδ]
    clear hδ hδ0 hdk hdpos hd
    induction d with
    | zero => simp
    | succ n ih =>
      push_cast
      exact ((valuation k).map_add _ _).trans (max_le ih (by simp))
  obtain ⟨t, ht0, ht1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
  set ε := valuation k t with hεdef
  set μ := min γ δ
  have hμ0 : 0 < μ := lt_min (zero_lt_iff.mpr hγ0) (zero_lt_iff.mpr hδ0)
  have hε0 : 0 < ε := zero_lt_iff.mpr (by simpa [hεdef] using ht0)
  set r₂ := μ * ε
  have hr₂0 : 0 < r₂ := mul_pos hμ0 hε0
  have hr₂μ : r₂ < μ := by
    calc r₂ = μ * ε := rfl
      _ < μ * 1 := mul_lt_mul_of_pos_left ht1 hμ0
      _ = μ := mul_one μ
  have hr₂γ : r₂ < γ := hr₂μ.trans_le (min_le_left _ _)
  have hr₂δ : r₂ < δ := hr₂μ.trans_le (min_le_right _ _)
  have hr₀r₂ : r₂ * δ ≤ r₂ := by
    calc r₂ * δ ≤ r₂ * 1 := mul_le_mul_of_nonneg_left hδ1 zero_le'
      _ = r₂ := mul_one r₂
  refine ⟨r₂ * δ, mul_pos hr₂0 (zero_lt_iff.mpr hδ0), hr₀r₂.trans_lt (hr₂δ.trans_le hδ1), ?_⟩
  intro x hx
  have hmem : ∀ y : k, valuation k (y - 1) ≤ r₂ → valuation E (algebraMap k E y - 1) ≤ r := by
    intro y hy
    exact le_of_lt (hγ (lt_of_le_of_lt hy hr₂γ))
  refine ⟨hmem x (hx.trans hr₀r₂), ?_⟩
  have hg : Matrix.GeneralLinearGroup.scalar (Fin 1) x ∈ UpperTheory.ConvolutionTheory.Loc.ball 1 (r₂ * δ) := by
    intro i j
    rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
    simpa [Matrix.GeneralLinearGroup.scalar] using hx
  obtain ⟨u, ⟨hu, hud⟩, -⟩ := UpperTheory.ConvolutionTheory.Loc.rootEx k 1 d r₂ hr₂δ _ hg
  have hpow : ∀ (M : Matrix (Fin 1) (Fin 1) k) (m : ℕ), (M ^ m) 0 0 = (M 0 0) ^ m := by
    intro M m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, Matrix.mul_apply, Fin.sum_univ_one, ih, pow_succ]
  have hw : ((u : Matrix (Fin 1) (Fin 1) k) 0 0) ^ d = (x : k) := by
    have := congrArg (fun g : GL (Fin 1) k => (g : Matrix (Fin 1) (Fin 1) k) 0 0) hud
    simp only [Units.val_pow_eq_pow_val] at this
    rw [← hpow, this]
    simp [Matrix.GeneralLinearGroup.scalar]
  have hw1 : valuation k ((u : Matrix (Fin 1) (Fin 1) k) 0 0 - 1) ≤ r₂ := by
    simpa using hu 0 0
  have hw0 : (u : Matrix (Fin 1) (Fin 1) k) 0 0 ≠ 0 := by
    intro h
    rw [h, zero_pow hdpos.ne'] at hw
    exact x.ne_zero hw.symm
  refine ⟨Units.mk0 (algebraMap k E ((u : Matrix (Fin 1) (Fin 1) k) 0 0))
    ((map_ne_zero (algebraMap k E)).mpr hw0), hmem _ hw1, ?_⟩
  rw [Units.val_mk0, Algebra.norm_algebraMap, ← hd, hw]
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.ElemLoc

section

@[expose] public section

open UpperTheory.Gal.InertialTypesAlt.L in
theorem UpperTheory.Gal.InertialTypesAlt.L.elemLoc :
    UpperTheory.Gal.InertialTypesAlt.L.ElemLoc := elemLoc_of suppE oneField reps normOpen normDiag align volRatio
  (fun E _ _ _ _ n r h0 h1 => UpperTheory.ConvolutionTheory.Loc.ballSub E n r h0 h1)
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.NormLoc

section

@[expose] public section

noncomputable section

open MeasureTheory NumberField IsDedekindDomain ValuativeRel Matrix GroundTheory.Global GroundTheory.Global.SemiLocal
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets PositivityTheory.Rg.Tf.Loc UpperTheory.ConvolutionTheory.Loc
open GlobalTheory.SmGL hiding iwahori
open PositivityTheory.Rg.Tf.Geo (incFin galFin)
open UpperTheory.V.Published UpperTheory.CBC
open scoped Classical

open GroundTheory.Global.AdeleBaseChange in
theorem UpperTheory.Gal.InertialTypesAlt.L.normLoc :
    UpperTheory.Gal.InertialTypesAlt.L.NormLoc := by
  intro F E _ _ _ _ _ _ _ _ σ hσ hp v w hw i1 i2 i3 i4 hmap η hη u
  obtain ⟨w0, hw0⟩ := w
  obtain rfl : below F w0 = v := (below_eq_iff w0 v).2 hw0
  have h2 := ideleNorm_finiteEmbedding (K := F) w0 u
  have h3 := UpperTheory.Gal.InertialTypesAlt.G.normTriv F E η hη (IdeleGroup.finiteEmbedding w0 u)
  rw [h2] at h3
  have hi : i1 = GroundTheory.Global.SemiLocal.algebraCompletion (below F w0) w0 := by
    apply Algebra.algebra_ext
    intro r
    exact (hmap r).symm
  subst hi
  exact h3
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.ElemPair

section

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain ValuativeRel Matrix GroundTheory.Global GroundTheory.Global.SemiLocal
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets PositivityTheory.Rg.Tf.Loc UpperTheory.ConvolutionTheory.Loc
open GlobalTheory.SmGL hiding iwahori
open PositivityTheory.Rg.Tf.Geo (incFin galFin)
open UpperTheory.V.Published UpperTheory.CBC
open UpperTheory.Gal.InertialTypesAlt.L

theorem UpperTheory.Gal.InertialTypesAlt.L.elemPair :
    UpperTheory.Gal.InertialTypesAlt.L.ElemPair := by
  intro F E _ _ _ _ _ _ _ _ σ hσ hp v w hw inst8 _ _ _ hmap n r hr0 hr1
  obtain ⟨x0, _, _, _, s, hs, hfin, hinc, hgal, -⟩ :=
    UpperTheory.V.Z.Tf.Orb.placeData_holds F E σ hσ v w hw
  have hx : x0 = inst8 := Algebra.algebra_ext _ _ fun a => (hinc a).symm.trans (hmap a)
  subst hx
  obtain ⟨⟨mE0, bE, mF0, bF, mE, mF, hmE, hmF, h1, h2⟩, hone⟩ := UpperTheory.ConvolutionTheory.GM.matchOne F E σ n v
  letI : MeasurableSpace (GL (Fin n) (HeightOneSpectrum.adicCompletion E w.1)) := borel _
  haveI : BorelSpace (GL (Fin n) (HeightOneSpectrum.adicCompletion E w.1)) := ⟨rfl⟩
  obtain ⟨hμE, k2⟩ :=
    UpperTheory.V.Z.Tf.Orb.placeOfLocal_holds F E σ hσ v w hw s hs hfin hinc hgal n mE mF hmE hmF
  obtain ⟨r₀, hr₀0, hr₀1, hr₀⟩ := UpperTheory.Gal.InertialTypesAlt.L.elemLoc _ _ s hs n _ mF hμE hmF r hr0 hr1
  refine ⟨r₀, hr₀0, hr₀1, fun r' hr' hr'0 => ?_⟩
  obtain ⟨hsurj, c, hc0, hc⟩ := hr₀ r' hr' hr'0
  refine ⟨hsurj, c, hc0, fun t ht => ?_⟩
  have hr'1 : r' < 1 := lt_of_le_of_lt hr' hr₀1
  have hT1 := UpperTheory.Gal.InertialTypesAlt.L.elemTest _ n r hr0 hr1 {t} isCompact_singleton
  have hcpt := ((UpperTheory.Gal.InertialTypesAlt.L.normDiag _ _ s hs n).2.2 r hr1 t ht).2
  have hT2 := UpperTheory.Gal.InertialTypesAlt.L.elemTest _ n r' hr'0 hr'1 _ hcpt
  refine ⟨hT1.2.2.1, hT2.2.2.1, ?_, ?_⟩
  · apply UpperTheory.Gal.InertialTypesAlt.L.matchSmul F E σ n v _ (by exact_mod_cast hc0.ne')
    apply hone mE mF hmE hmF h1 h2
    exact k2 _ hT1.2.2.2.1 _ (Submodule.smul_mem _ _ hT2.2.2.2.1) (hc t ht)
  · intro g hg η hη
    obtain ⟨t', ⟨u, -, rfl⟩, x, hx, hdet⟩ := hT2.2.2.2.2 g hg
    obtain ⟨y, -, hy⟩ := hsurj x hx
    have hy' : x = Units.map (Algebra.norm (HeightOneSpectrum.adicCompletion F v)) y := Units.ext hy
    have hprod : (∏ i, nrmT (HeightOneSpectrum.adicCompletion F v) (t * u) i) =
        Units.map (Algebra.norm (HeightOneSpectrum.adicCompletion F v)) (∏ i, (t * u) i) := by
      simp only [nrmT, map_prod]
    rw [hdet, hprod, hy', ← map_mul]
    exact UpperTheory.Gal.InertialTypesAlt.L.normLoc F E σ hσ hp v w hw hmap η hη _
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.ElemPairJHolds

section

@[expose] public section

namespace UpperTheory.Gal.InertialTypesAlt.L

theorem elemPairJ_holds : UpperTheory.Gal.Join.ElemPairJ := elemPairJ elemPair

theorem finTrace_holds (h : GlobalTheory.DZA.InflMatching) (h₁ : G.VarEx) (h₂ : G.VarTrace) (h₃ : G.NormInt) : FinTrace :=
  finTrace resEx finAct inflFacts frobFacts (inflTrace h h₁ h₂ h₃)

end UpperTheory.Gal.InertialTypesAlt.L
end
end
