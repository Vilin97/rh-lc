module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsChainPols
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHasLocalSmall
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensorGiven
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsClearingIntegersPrincipalDatumHost
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridFirstColumnSpaceRankSignatureSelfDual
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatIntegrandFlippedTensorLocallyConstantCompact
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StepVecCongr
public import Development.AbelianVarietyTheory.Definitions.Divisors.MoveArgsOneTranspose
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIdemSumSubOfSubsetAndOrthogonalStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemCompletedHomLatticeIffIntegralOnUnitHalfStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RankCol
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
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSBHalfGivenFnDown
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaAtExtDat
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePlacesNotPairwiseConjugate
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
import Mathlib.Tactic.Linter.Style
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StepVecCongr
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistCosetFunctionIsLocalVector
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistFlipStartHighestVector

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.GivenFnEqExtDat

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun GlobalTheory.ChainCol
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open Classical

noncomputable section

namespace GlobalTheory.ChainColRead



theorem givenFn_eq_extDat : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (B : Frames G) {μ₀ : T}, L.Is μ₀ → L.Pg ⊆ G.pl.W0 → ∀ (t : T) (j : ℕ), j + 1 < D.R.m → ∀ (Φ : G.Datum) (e e' : AE D), IsIdemSum e (locPl G t) → IsIdemSum e' (L.Pg ∪ L.Q t) → (∀ w ∈ locPl G t, w ∉ L.Pg ∪ L.Q t → ((∀ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) ≤ 1) ∧ ∃ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) = 1)) → ∀ x : WO (G.pS (.mu t 0 j)) (G.pT (.mu t 0 j)), GlobalTheory.FlipStart.givenFn B t Φ e (.down t 0 j) x = extDat e e' (latO (G.pS (.mu t 0 j)) (G.pT (.mu t 0 j)) (G.latS (.mu t 0 j) : Set _) (G.latT (.mu t 0 j) : Set _) fun _ => True) (stepDat (G.pS (.mu t 0 j)) (G.pT (.mu t 0 j)) (colFrame L j) (colFrame L (j + 1)) (colDat L t j) (L.chi (j + 1)) (L.xiR t) (L.Q t) e') x := by
  intro D T L sc G B μ₀ hL hPg t j hj1 Φ e e' he he' hAA x
  have hj : j < D.R.m := by omega
  have hsub : L.Pg ∪ L.Q t ⊆ locPl G t := by
    intro w hw
    rcases Finset.mem_union.1 hw with h | h
    · exact Finset.mem_union_left _ (hPg h)
    · exact Finset.mem_union_right _ h
  obtain ⟨he₁, -⟩ := GlobalTheory.T.isIdemSum_sub_of_subset_and_orthogonal he he' hsub
  have h1 := GlobalTheory.PlaceDatum.idemSum_mul_self he'
  have h2 := GlobalTheory.PlaceDatum.idemSum_mul_self he₁
  obtain ⟨-, c1, c0⟩ := GlobalTheory.FunObj.Comparison₂.cpt_idemSum he'
  obtain ⟨-, d1, -⟩ := GlobalTheory.FunObj.Comparison₂.cpt_idemSum he₁
  have ha := GlobalTheory.FlipTop.rank_col G hj.le
  have hb := GlobalTheory.FlipTop.rank_col G hj
  unfold GlobalTheory.FlipStart.givenFn extDat
  by_cases hx : IsHalf e x
  swap
  · rw [if_neg hx, if_neg fun h => hx h.1]
  rw [if_pos hx]
  set N := GlobalTheory.FunObj.Comparison₂.fr (B.β 0 (j + 1)) (B.β 0 j) (x.map (toEAf D)) with hN
  have hfr : ∀ a : AE D, GlobalTheory.FunObj.Comparison₂.fr (B.β 0 (j + 1)) (B.β 0 j) ((x.map (a * ·)).map (toEAf D)) = toEAf D a • N := by
    intro a
    rw [hN, ← GlobalTheory.FunObj.Comparison₂.fr_smul]
    congr 1
    ext p q
    simp [Matrix.map_apply, Matrix.smul_apply, RingHom.map_mul]
  have hcomp : ∀ (a : AE D) (w : Pl D.host.E), cpt (D := D) w (toEAf D a) = 1 →
      (GlobalTheory.FunObj.Comparison₂.fr (B.β 0 (j + 1)) (B.β 0 j) ((x.map (a * ·)).map (toEAf D))).map (cpt (D := D) w) = N.map (cpt (D := D) w) := by
    intro a w hw
    rw [hfr]
    ext p q
    simp [Matrix.map_apply, Matrix.smul_apply, RingHom.map_mul, hw]
  have hsubm : ∀ w : Pl D.host.E, GlobalTheory.StepData.IntM ((N.map (cpt (D := D) w)).submatrix (GlobalTheory.FunObj.Comparison₂.ixOf G t w hb)
      (GlobalTheory.FunObj.Comparison₂.ixOf G t w ha)) ↔ GlobalTheory.StepData.IntM (N.map (cpt (D := D) w)) := fun w =>
    ⟨fun h i l => by simpa using h ((GlobalTheory.FunObj.Comparison₂.ixOf G t w hb).symm i) ((GlobalTheory.FunObj.Comparison₂.ixOf G t w ha).symm l),
      fun h i l => h _ _⟩
  have hR : ∀ w, givenDatum t w B Φ (edgeOf (.down t 0 j)) (locArg B t w (.down t 0 j) x) =
      stepFn L t w j ((N.map (cpt (D := D) w)).submatrix (GlobalTheory.FunObj.Comparison₂.ixOf G t w hb) (GlobalTheory.FunObj.Comparison₂.ixOf G t w ha)) := by
    intro w
    have hla : locArg B t w (.down t 0 j) x = B.coord t w (X := (0, j + 1)) (Y := (0, j)) ⟨Nat.zero_le _, hj⟩
        ⟨Nat.zero_le _, hj.le⟩ ((x.map (toEAf D)).map (cpt (D := D) w)) := by
      rw [Matrix.map_map]
      exact dif_pos ⟨Nat.zero_le _, hj⟩
    rw [hla]
    exact GlobalTheory.FunObj.Comparison₂.givenDatum_theta_coord B t w Φ hj ha hb (x.map (toEAf D))
  rw [Finset.prod_congr rfl fun w _ => hR w, ← Finset.prod_sdiff hsub]
  have hout : ∀ w ∈ locPl G t \ (L.Pg ∪ L.Q t), stepFn L t w j ((N.map (cpt (D := D) w)).submatrix
      (GlobalTheory.FunObj.Comparison₂.ixOf G t w hb) (GlobalTheory.FunObj.Comparison₂.ixOf G t w ha)) =
      if GlobalTheory.StepData.IntM (N.map (cpt (D := D) w)) then 1 else 0 := by
    intro w hw
    obtain ⟨-, hw2⟩ := Finset.mem_sdiff.1 hw
    have hP : w ∉ L.Pg := fun h => hw2 (Finset.mem_union_left _ h)
    have hQ : w ∉ L.Q t := fun h => hw2 (Finset.mem_union_right _ h)
    unfold stepFn
    rw [if_neg hP, if_neg hQ, Set.indicator_apply]
    exact if_congr (hsubm w) rfl rfl
  rw [Finset.prod_congr rfl hout, Finset.prod_boole]

  have hx1 : IsHalf (e - e') (x.map ((e - e') * ·)) := fun p q => by
    simp only [Matrix.map_apply, ← mul_assoc, h2]
  have hS : IsSelfDualC (G.pS (.mu t 0 j)) (G.latS (.mu t 0 j)) := (colY_isV D T L μ₀ hL j hj.le).sd
  have hT : IsSelfDualC (G.pT (.mu t 0 j)) (G.latT (.mu t 0 j)) := (colY_isV D T L μ₀ hL (j + 1) hj).sd
  have hAA' : ∀ w ∈ locPl G t \ (L.Pg ∪ L.Q t), ((∀ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) ≤ 1) ∧
      ∃ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) = 1) := fun w hw =>
    hAA w (Finset.mem_sdiff.1 hw).1 (Finset.mem_sdiff.1 hw).2
  have hlat := GlobalTheory.T.mem_completedHomLattice_iff_integral_on_unit_half hS hT (B.isFrame_β hL (Nat.zero_le _) hj.le) (B.isFrame_β hL (Nat.zero_le _) hj) he₁ hAA'
    (x.map ((e - e') * ·)) hx1
  have k1 : x.map ((e - e') * ·) ∈ latO (G.pS (.mu t 0 j)) (G.pT (.mu t 0 j)) (G.latS (.mu t 0 j) : Set _)
      (G.latT (.mu t 0 j) : Set _) (fun _ => True) ↔
      ∀ w ∈ locPl G t \ (L.Pg ∪ L.Q t), GlobalTheory.StepData.IntM (N.map (cpt (D := D) w)) := by
    rw [hlat]
    exact forall₂_congr fun w hw => by rw [hcomp _ w (d1 w hw)]

  have hint : IsIntM (toEAf D e' • N) ↔ ∀ w ∈ L.Pg ∪ L.Q t, GlobalTheory.StepData.IntM (N.map (cpt (D := D) w)) := by
    constructor
    · intro h w hw i l
      have := (mem_OA_iff _).1 (h i l) w
      rw [Matrix.smul_apply, smul_eq_mul, RingHom.map_mul, c1 w hw, one_mul] at this
      exact (GlobalTheory.FunObj.Comparison₂.vEq w).le_one_iff_le_one.2 this
    · intro h i l
      refine (mem_OA_iff _).2 fun w => ?_
      rw [Matrix.smul_apply, smul_eq_mul, RingHom.map_mul]
      by_cases hw : w ∈ L.Pg ∪ L.Q t
      · rw [c1 w hw, one_mul]
        exact (GlobalTheory.FunObj.Comparison₂.vEq w).le_one_iff_le_one.1 (h w hw i l)
      · rw [c0 w hw, zero_mul]
        exact zero_mem _
  have hx0 : IsHalf e' (x.map (e' * ·)) := fun p q => by
    simp only [Matrix.map_apply, ← mul_assoc, h1]
  have hfrO : frMapO (G.pS (.mu t 0 j)) (G.pT (.mu t 0 j)) (colFrame L j) (colFrame L (j + 1)) (x.map (e' * ·)) =
      toEAf D e' • N := hfr e'
  have k0 : stepDat (G.pS (.mu t 0 j)) (G.pT (.mu t 0 j)) (colFrame L j) (colFrame L (j + 1)) (colDat L t j)
      (L.chi (j + 1)) (L.xiR t) (L.Q t) e' (x.map (e' * ·)) = ∏ w ∈ L.Pg ∪ L.Q t, stepFn L t w j
      ((N.map (cpt (D := D) w)).submatrix (GlobalTheory.FunObj.Comparison₂.ixOf G t w hb) (GlobalTheory.FunObj.Comparison₂.ixOf G t w ha)) := by
    unfold stepDat
    rw [hfrO]
    by_cases H : ∀ w ∈ L.Pg ∪ L.Q t, GlobalTheory.StepData.IntM (N.map (cpt (D := D) w))
    · rw [if_pos ⟨hx0, hint.2 H⟩]
      have key := GlobalTheory.FunObj.Comparison₂.omega_eq_prod_stepFn G t hL hj ha hb (r_le_colY L j) (toEAf D e' • N) (hint.2 H)
      refine key.trans (Finset.prod_congr rfl fun w hw => ?_)
      have e1 : (toEAf D e' • N).map (cpt (D := D) w) = N.map (cpt (D := D) w) := by
        rw [← hfr e']; exact hcomp e' w (c1 w hw)
      rw [e1]
    · rw [if_neg fun h => H (hint.1 h.2)]
      push_neg at H
      obtain ⟨w, hw, hn⟩ := H
      refine (Finset.prod_eq_zero hw ?_).symm
      by_contra h0
      exact hn ((hsubm w).1 (GlobalTheory.FunObj.LocTest.intM_of_stepFn t w j h0))
  rw [k0]
  by_cases hl : ∀ w ∈ locPl G t \ (L.Pg ∪ L.Q t), GlobalTheory.StepData.IntM (N.map (cpt (D := D) w))
  · rw [if_pos hl, one_mul, if_pos ⟨hx, k1.2 hl⟩]
  · rw [if_neg hl, zero_mul, if_neg fun h => hl (k1.1 h.2)]

end GlobalTheory.ChainColRead

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelPlacesSubsetChosenPlaces

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun GlobalTheory.ChainCol
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open Classical

namespace GlobalTheory.LevelPlacesChosen

theorem levelPlaces_subset_chosenPlaces : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {μ₀ : T},
    L.Is μ₀ → L.Pg ⊆ G.pl.W0 := by
  intro D T L sc G μ₀ hμ P hP
  obtain ⟨k, hk⟩ := (hμ.Pg P).1 hP
  have hK : P.under (𝓞 D.host.K) = L.C.P.pb k := hk
  have hgE : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := by
    have h1 : ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ (P.under (𝓞 D.host.K)).asIdeal := by
      rw [hK]; exact L.C.P.pb_over k
    have h2 : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ P.asIdeal := h1
    rwa [map_natCast] at h2
  have hgF : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ (P.under (𝓞 D.host.F)).asIdeal := by
    show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ P.asIdeal
    rw [map_natCast]; exact hgE
  have hS1 : P.under (𝓞 D.host.F) ∈ S1 D := by
    rw [S1_mem_OmF]
    fin_cases k
    · exact Or.inl hgF
    · exact Or.inr (Or.inl hgF)
  have hS0 : P.under (𝓞 D.host.F) ∈ insert G.pl.v0 (S1 D) := Finset.mem_insert_of_mem hS1
  have hwPg : G.pl.w (P.under (𝓞 D.host.F)) ∈ L.Pg := G.pl.w_g _ k hgF
  have hover : (G.pl.w (P.under (𝓞 D.host.F))).under (𝓞 D.host.F) = P.under (𝓞 D.host.F) := G.pl.w_over _ hS0
  have heq : G.pl.w (P.under (𝓞 D.host.F)) = P := by
    rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq hover with h | h
    · exact h
    · exact absurd ((GlobalTheory.GoodPrimes.isConjPl_iff).2 h)
        (GlobalTheory.TypePlaces.not_isConjPl L.C.P L.Pg hμ.Pg P hP _ hwPg)
  unfold Places.W0
  exact Finset.mem_image.2 ⟨_, hS0, heq⟩

end GlobalTheory.LevelPlacesChosen
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalVectorDownEdgeInterior

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.ChainCol

noncomputable section

namespace GlobalTheory.ChainCol

attribute [local instance] Formalism.BasicNotions.Host.cmStar



theorem locVec_col {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A} {large₂ : SizeData₂ D}
    (s : HidaSetting large₂ R F) (ch : Choice R) (hch : ch.Is) (t : T) (j : Fin D.R.m) (g : Sch ch.G (.down t 0 j))
    (hj : (j : ℕ) + 1 < D.R.m) (hg : HEq g (R.vY t j)) (e : AE D) (he : IsIdemSum e (locPl ch.G t)) (Φ : ch.G.Datum) :
    IsLocVec ch.W (.mu t 0 j) e (ch.rm.vT 0 j) (((1 : ℂˣ) : ℂ) • GlobalTheory.FlipStart.givenFn ch.S.B t Φ e (.down t 0 j)) g := by
  classical
  have hL : R.toLevCh.Is A.μ0 := s.core.lev
  have hv := s.core.chain.vY t j hj
  have hvac := hch.vac.1 j hj
  have hw := hch.weil
  obtain ⟨hX1, hX2⟩ := lsp_heq (colY_lt R.toLevCh (j.2 : (j : ℕ) < D.R.m))
  obtain ⟨hY1, hY2⟩ := lsp_heq (colY_lt R.toLevCh hj)
  have hv' : IsStepVecOf R.ψ R.θ (columnBlock R.toLevCh j).sp (columnBlock R.toLevCh (j + 1)).sp (ch.W.cart (.grid 0 j))
      (ch.W.cart (.grid 0 (j + 1))) (columnBlock R.toLevCh j).lat (columnBlock R.toLevCh (j + 1)).lat (colFrame R.toLevCh j)
      (colFrame R.toLevCh (j + 1)) (colDat R.toLevCh t j) (R.chi (j + 1)) (R.Q t) (R.xiR t) (ch.rm.vT 0 j) g :=
    stepVec_congr hX1.symm hY1.symm (hw.cartY j j.2).symm (hw.cartY (j + 1) hj).symm hX2.symm hY2.symm
      (colFrame_lt R.toLevCh j.2).symm (colFrame_lt R.toLevCh hj).symm
      (datY_heq (congrArg (fun V : HSp D => V.rank) hX1.symm) _ _ _ _ _ _ _ _ _ _ _) hvac.symm hg.symm hv
  obtain ⟨hf₀, e', he', hθ'⟩ := hv'
  have hsd := fun k (hk : k ≤ D.R.m) => (colY_isV D T R.toLevCh A.μ0 hL k hk).sd
  have hPg := GlobalTheory.LevelPlacesChosen.levelPlaces_subset_chosenPlaces ch.G hL
  have h1 := GlobalTheory.ExtDatTheta.isThetaAt_extDat (hsd j j.2.le) (hsd (j + 1) hj.le) hf₀ he he' ?_ hθ'
  swap
  · intro x hx
    unfold locPl
    rcases Finset.mem_union.1 hx with h | h
    · exact Finset.mem_union.2 (Or.inl (hPg h))
    · exact Finset.mem_union.2 (Or.inr h)
  have hAA : ∀ w ∈ locPl ch.G t, w ∉ R.toLevCh.Pg ∪ R.toLevCh.Q t →
      ((∀ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) ≤ 1) ∧
        ∃ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) = 1) := by
    intro w hw _
    have hb := GlobalTheory.FunObj.Good.badInt_notMem hL (GlobalTheory.FlipIntegrand.pde_ne_q_of_setting s) (hch.guard t) hw
    have h2q := fun h => hb (GlobalTheory.HalfCompare.mem_of_dvd h (Dvd.intro _ rfl))
    have hN := fun h => hb (GlobalTheory.HalfCompare.mem_of_dvd h (Dvd.intro_left _ rfl))
    refine ⟨fun a ha => ?_, ⟨_, GlobalTheory.HostClear.absNorm_mem_AA D, ?_⟩⟩
    · rw [GlobalTheory.FunObj.Good.valued_alg]
      exact GlobalTheory.FunObj.Good.valuation_le_one_of_mem h2q (Or.inl ha)
    · rw [GlobalTheory.FunObj.Good.valued_alg]
      exact GlobalTheory.FunObj.Good.valuation_nat hN
  have h3 := funext (GlobalTheory.ChainColRead.givenFn_eq_extDat ch.G ch.S.B hL hPg t j hj Φ e e' he he' hAA)
  refine ⟨?_, ?_⟩
  · rw [Units.val_one, one_smul]
    exact GlobalTheory.FlipStart.ColSB.isSBHalf_givenFn_down ch.G ch.S.B hL t j j.2 Φ e he
  · rw [Units.val_one, one_smul, h3, hw.ψ]
    exact h1

end GlobalTheory.ChainCol
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistChainColumnInnerSuccEq

section

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.ChainCol
noncomputable section
namespace GlobalTheory.ChainCol
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem chainColumn_inner_succ : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ {R} ch => ∀ (t : T) (j : Fin D.R.m) (g : Sch ch.G (.down t 0 j)), (j : ℕ) + 1 < D.R.m → HEq g (R.vY t j) → ∃ c : ℂˣ, c ∈ xiVals R.toLevCh t ∧ ∀ e : AE D, IsIdemSum e (locPl ch.G t) → ∀ Φ : ch.G.Datum, IsLocVec ch.W (.mu t 0 j) e (ch.rm.vT 0 j) ((c : ℂ) • GlobalTheory.FlipStart.givenFn ch.S.B t Φ e (.down t 0 j)) g := by
  intro _
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch _ => ?_⟩⟩
  intro t j g hj hg
  exact ⟨1, one_mem _, fun e he Φ => locVec_col s ch hch t j g hj hg e he Φ⟩
end GlobalTheory.ChainCol
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.twist_chainColumn_inner_succ_eq : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ {R} ch => ∀ (t : T) (j : Fin D.R.m) (g : Sch ch.G (.down t 0 j)), (j : ℕ) + 1 < D.R.m → HEq g (R.vY t j) → ∃ c : ℂˣ, c ∈ xiVals R.toLevCh t ∧ ∀ e : AE D, IsIdemSum e (locPl ch.G t) → ∀ Φ : ch.G.Datum, IsLocVec ch.W (.mu t 0 j) e (ch.rm.vT 0 j) ((c : ℂ) • GlobalTheory.FlipStart.givenFn ch.S.B t Φ e (.down t 0 j)) g := by
  first | exact @_root_.GlobalTheory.ChainCol.chainColumn_inner_succ | exact _root_.GlobalTheory.ChainCol.chainColumn_inner_succ | (intros; apply _root_.GlobalTheory.ChainCol.chainColumn_inner_succ <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedThetaFirstOccurrenceFiniteSwappedPair

section

@[expose] public section

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
theorem GlobalTheory.FlipStart.theta_first_occurrence_finite_swapped_pair : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ {R} ch => ∀ (t : T) (f : ∀ j : Fin D.R.m, Sch ch.G (.down t 0 j)), GlobalTheory.FlipStart.ChainVecs ch t f → ∃ z : ℂˣ, z ∈ xiVals R.toLevCh t ∧ ∀ Φ : ch.G.Datum, RepFin ch.S.B ch.rm t (givenPath t D.R.m) (Finsupp.single (GlobalTheory.FlipStart.givenFin ch.W t f Φ) (z : ℂ)) (fun w => (givenStage t w ch.S.B Φ).tensor) := by
  intro hP
  obtain ⟨C, h⟩ := Big.and (Big.and (_root_.GlobalTheory.T.twist_chainColumn_inner_succ_eq hP) (_root_.GlobalTheory.T.twist_flipStart_highestVector hP)) (_root_.GlobalTheory.T.twist_coset_function_isLocalVector hP)
  refine ⟨C, fun ε CF hC => ?_⟩
  obtain ⟨x₀, h⟩ := h ε CF hC
  refine ⟨x₀, fun D large₂ he hx Γ _ _ Pl0 T A Ks _ _ _ R F s ch hi ha => ?_⟩
  obtain ⟨⟨hc1, hc2⟩, hr⟩ := h D large₂ he hx Γ Pl0 T A Ks R F s ch hi ha
  intro t f hf
  have hc : ∀ j : Fin D.R.m, ∃ c : ℂˣ, c ∈ xiVals R.toLevCh t ∧ ∀ e : AE D, IsIdemSum e (locPl ch.G t) →
      ∀ Φ : ch.G.Datum, IsLocVec ch.W (.mu t 0 j) e (ch.rm.vT 0 j) ((c : ℂ) • GlobalTheory.FlipStart.givenFn ch.S.B t Φ e (.down t 0 j)) (f j) := by
    intro j
    by_cases hj : (j : ℕ) + 1 < D.R.m
    · exact hc1 t j (f j) hj ((hf j).1 hj)
    · have hj' : (j : ℕ) + 1 = D.R.m := by have := j.2; omega
      exact hc2 t j (f j) hj' ((hf j).2 hj')
  choose c hcx hcv using hc
  obtain ⟨e, he⟩ := GlobalTheory.FunObj.LocTensor.exists_idemSum_locPl s.core.lev ch.G t
  refine ⟨(∏ j, c j)⁻¹, Subgroup.inv_mem _ (Subgroup.prod_mem _ fun j _ => hcx j), fun Φ => ?_⟩
  refine GlobalTheory.FlipStart.repFin_of ch.W ch.S.B ch.rm t f Φ e he (fun j => (c j : ℂ)) _ ?_ (fun j => hcv j e he Φ) (hr t e he Φ)
  rw [← Units.coe_prod, ← Units.val_mul, inv_mul_cancel, Units.val_one]
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.twisted_theta_first_occurrence_finite_swapped_pair : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ {R} ch => ∀ (t : T) (f : ∀ j : Fin D.R.m, Sch ch.G (.down t 0 j)), GlobalTheory.FlipStart.ChainVecs ch t f → ∃ z : ℂˣ, z ∈ xiVals R.toLevCh t ∧ ∀ Φ : ch.G.Datum, RepFin ch.S.B ch.rm t (givenPath t D.R.m) (Finsupp.single (GlobalTheory.FlipStart.givenFin ch.W t f Φ) (z : ℂ)) (fun w => (givenStage t w ch.S.B Φ).tensor) := by
  first | exact @_root_.GlobalTheory.FlipStart.theta_first_occurrence_finite_swapped_pair | exact _root_.GlobalTheory.FlipStart.theta_first_occurrence_finite_swapped_pair | (intros; apply _root_.GlobalTheory.FlipStart.theta_first_occurrence_finite_swapped_pair <;> assumption)
end
end
end
