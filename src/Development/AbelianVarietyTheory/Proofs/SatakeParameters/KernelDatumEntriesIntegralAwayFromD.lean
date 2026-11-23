module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaZJetsThree
public import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
public import Formalism.SharpRestriction.Divisibility.OrbitPlaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CombOfTied
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralJetsNormalisedThetaCombinationsAwayDStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralJetsRealPlaceLocalBasesStatement
public import Formalism.SharpRestriction.Divisibility.ProductZerothFirstParts
public import Formalism.GaussJetBounds.StatementN
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

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.KvalGeZeroOfIntegralJets

section

@[expose] public section

open Formalism.MainNotions Classical

namespace GlobalTheory.Proof.kvalGe_zero_of_integral_jets

theorem kvalGe_zero : ∀ (Lt : Type) [Fintype Lt] [DecidableEq Lt] (N0 N1 l : ℕ) [Fact l.Prime]
    (nu : Lt → YoungDiagram) (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]),
    Formalism.DworkPowerSeriesWeights.JetsIntegral Th → product_zeroth_first_parts.KvalGe N0 N1 l nu Th 0 := by
  intro Lt _ _ N0 N1 l _ nu Th hTh I m
  rw [neg_zero, Real.rpow_zero]
  unfold product_zeroth_first_parts.applyAt0
  rw [MvPolynomial.coeff_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun μ _ => ?_
  rw [MvPolynomial.coeff_monomial]
  split_ifs
  · rw [mul_assoc, norm_mul]
    refine mul_le_one₀ (IsUltrametricDist.norm_intCast_le_one ℂ_[l] _) (norm_nonneg _) ?_
    have h := hTh (Finsupp.sumFinsuppEquivProdFinsupp μ).2
    unfold Formalism.DworkPowerSeriesWeights.mfact at h
    simpa [Finsupp.prod, Nat.cast_prod] using h
  · simp

end GlobalTheory.Proof.kvalGe_zero_of_integral_jets
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.KvalGeZeroOfIntegralJetsStatement

section

@[expose] public section

open Formalism.MainNotions Classical

theorem _root_.GlobalTheory.T.kvalGe_zero_of_integral_jets : ∀ (Lt : Type) [Fintype Lt] [DecidableEq Lt] (N0 N1 l : ℕ) [Fact l.Prime] (nu : Lt → YoungDiagram) (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]), Formalism.DworkPowerSeriesWeights.JetsIntegral Th → product_zeroth_first_parts.KvalGe N0 N1 l nu Th 0 := by
  first | exact @GlobalTheory.Proof.kvalGe_zero_of_integral_jets.kvalGe_zero | exact GlobalTheory.Proof.kvalGe_zero_of_integral_jets.kvalGe_zero | (intros; apply GlobalTheory.Proof.kvalGe_zero_of_integral_jets.kvalGe_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelDatumEntriesIntegralAwayFromD

section

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Classical

namespace GlobalTheory.Ggeo.AdmEntInt

theorem mod_three_eq_two_of_jacobiSym_neg_eq_one (d : ℕ) (h : jacobiSym (-(d : ℤ)) 3 = 1) : d % 3 = 2 := by
  rw [jacobiSym.mod_left] at h
  simp only [Nat.cast_ofNat] at h
  have : (-(d : ℤ)) % 3 = 0 ∨ (-(d : ℤ)) % 3 = 1 ∨ (-(d : ℤ)) % 3 = 2 := by omega
  rcases this with h0 | h0 | h0 <;> rw [h0] at h
  · norm_num at h
  · omega
  · norm_num at h

end GlobalTheory.Ggeo.AdmEntInt

theorem GlobalTheory.Ggeo.AdmEntInt.kernelDatum_entries_integral_away_from_d : GlobalTheory.ThLoc.Inputs → ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), t.Hyp → 3 ≤ D.host.splitBound → ∀ ep be sg, OrbitPlaces.JetIntegralityBis (OrbitPlaces.ofKer (nuRowOK D) t.ent ep be sg) Y := by
  intro hIn D L hT Gi Gl K Y cX ex t hHyp h3 ep be sg
  intro u μ w hlf hd i hi _heven c c'
  have hlf' : LevFree Y u μ w := hlf
  obtain ⟨hAdm, hComb⟩ := GlobalTheory.Ggeo.KerComb.comb_of_tied hIn.algT D L hT Gi Gl K Y cX ex t hHyp u μ w hlf' i hi c c'
  have hd3 : D.what₂.places.resChar w = 3 → D.host.d % 3 = 2 := fun _ =>
    GlobalTheory.Ggeo.AdmEntInt.mod_three_eq_two_of_jacobiSym_neg_eq_one _ (D.host.split_small 3 Nat.prime_three (by norm_num) h3)
  have hJ := GlobalTheory.T.integralJets_normalisedThetaCombinations_away_d hIn D t.cc t.δ t.cc_ok t.δ_ok t.B t.χ t.χ_ok t.X t.seam t.seam_ok _ _ _ _ hAdm
    (D.what₂.places.resChar w) (t.ent.lam w) hd hd3 _ hComb
  let T := t.kf u μ w hlf'
  have hB := T.B_bas i hi.le c
  have hB' := T.B_bas (i + 1) hi c'
  have hK := GlobalTheory.T.integral_jets_realPlace_local_bases D (t.O u μ).dgen (t.O u μ).dgen_gen _ _ _ _ hAdm (D.what₂.places.resChar w) (t.ent.lam w)
    (T.B i c) (T.B (i + 1) c') (fun τ => T.c0 i c c' τ * TaylorLogMetric.lamC (t.ent.lam w) ((t.O u μ).dgen τ)) hB hB'
    (fun τ => by rw [norm_mul, T.unitAbs_eq_one, one_mul]) _ hJ
  rw [← T.th i hi c c'] at hK
  exact GlobalTheory.T.kvalGe_zero_of_integral_jets _ _ _ _ _ _ hK
end
end
