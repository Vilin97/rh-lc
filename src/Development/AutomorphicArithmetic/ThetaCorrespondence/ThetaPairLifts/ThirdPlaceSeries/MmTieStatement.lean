module

public import Development.AbelianVarietyTheory.Definitions.Divisors.TieTest
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SettingAtPoint
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LeafInfinitePlaceBound
public import Development.AbelianVarietyTheory.Counterexamples.DegenerateExamples.TreeLeafParameterArithmeticOfBounds
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotLeafMMZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PtFieldMain
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.SlopeE
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSelfDualE
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefGramSelfDualAfterFieldEmbedding
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MaxSlopeDualSumWeylLatticesLe
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MaxSlopeSumWeylAndDualWeylLatticesLe
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefGramSelfDualAfterFieldEmbeddingStatement

section

@[expose] public section

open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

theorem _root_.GlobalTheory.T.defGram_selfDual_after_field_embedding : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [StarRing K] (cE : E →+* E), (∀ (φ : E →+* ℂ) (x : E), φ (cE x) = starRingEnd ℂ (φ x)) → ∀ (ι : Type) (emb : ι → E →+* K), (∀ τ x, star (emb τ x) = emb τ (cE x)) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), (∀ φ : E →+* ℂ, (J.map φ).PosDef) → ∀ τ, IsDefGram (gramK emb J τ) ∧ IsDefGram (gramKd emb J τ) ∧ ∀ L : Submodule (𝓞 E) (Fin n → E), IsSelfDualE cE J L → IsSelfDualK (gramK emb J τ) (tauLat emb τ L) ∧ IsSelfDualK (gramKd emb J τ) (dualFr (tauLat emb τ L)) := by
  first | exact @GlobalTheory.TestLat.defGram_selfDual_of_embedding | exact GlobalTheory.TestLat.defGram_selfDual_of_embedding | (intros; apply GlobalTheory.TestLat.defGram_selfDual_of_embedding <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.MaxSlopeDualSumWeylLatticesLeStatement

section

@[expose] public section

open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

theorem _root_.GlobalTheory.T.maxSlope_dual_sum_weyl_lattices_le : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (v₀ : InfinitePlace K), IsConjAt v₀ → ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (R : ℝ), 1 ≤ R → SpreadLe lam R → ∀ (G : ι → Matrix (Fin n) (Fin n) K), (∀ τ, IsDefGram (G τ)) → ∀ (C : Type) [Nonempty C] (M : C → ι → Submodule (𝓞 K) (Fin n → K)), (∀ c τ, IsSelfDualK (G τ) (M c τ)) → ∀ (N : ℕ) (e : Fin N ≃ C × VVIdx lam) (X : InfinitePlace K → Matrix (Fin N) (Fin N) ℂ), IsMetric ((sumGram lam e G)⁻¹)ᵀ X → TestLatticeCondition N X (dualFr (sumLat lam e fun c => delK lam (M c))) (bound (Fintype.card ι) n R) := by
  first | exact @GlobalTheory.TestLat.testLatticeCondition_dualFr_sumLat_delK | exact GlobalTheory.TestLat.testLatticeCondition_dualFr_sumLat_delK | (intros; apply GlobalTheory.TestLat.testLatticeCondition_dualFr_sumLat_delK <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.MaxSlopeSumWeylAndDualWeylLatticesLeStatement

section

@[expose] public section

open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

theorem _root_.GlobalTheory.T.maxSlope_sum_weyl_and_dualWeyl_lattices_le : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (v₀ : InfinitePlace K), IsConjAt v₀ → ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (R : ℝ), 1 ≤ R → SpreadLe lam R → ∀ (G : ι → Matrix (Fin n) (Fin n) K), (∀ τ, IsDefGram (G τ)) → ∀ (C : Type) [Nonempty C] (M : C → ι → Submodule (𝓞 K) (Fin n → K)), (∀ c τ, IsSelfDualK (G τ) (M c τ)) → ∀ (N : ℕ) (e : Fin N ≃ C × VVIdx lam) (X : InfinitePlace K → Matrix (Fin N) (Fin N) ℂ), IsMetric (sumGram lam e G) X → TestLatticeCondition N X (sumLat lam e fun c => nabK lam (M c)) (bound (Fintype.card ι) n R) ∧ TestLatticeCondition N X (sumLat lam e fun c => delK lam (M c)) (bound (Fintype.card ι) n R) := by
  first | exact @GlobalTheory.TestLat.testLatticeCondition_sumLat_nabK_and_delK | exact GlobalTheory.TestLat.testLatticeCondition_sumLat_nabK_and_delK | (intros; apply GlobalTheory.TestLat.testLatticeCondition_sumLat_nabK_and_delK <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlopeEHolds

section

@[expose] public section

open NumberField
open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

namespace GlobalTheory.TestLat

theorem slopeK_holds : SlopeK := by
  intro K _ _ _ _ v₀ hv ι _ n lam R hR hs G hG C _ M hM N e X
  exact ⟨GlobalTheory.T.maxSlope_sum_weyl_and_dualWeyl_lattices_le K v₀ hv ι n lam R hR hs G hG C M hM N e X,
    GlobalTheory.T.maxSlope_dual_sum_weyl_lattices_le K v₀ hv ι n lam R hR hs G hG C M hM N e X⟩

theorem slopeE_holds : SlopeE := by
  intro E K _ _ _ _ _ _ v₀ hv cE hcE ι _ emb hemb n lam R hR hs J hJ C _ L hL N e X
  have h := GlobalTheory.T.defGram_selfDual_after_field_embedding E K cE hcE ι emb hemb n J hJ
  have h1 := slopeK_holds K v₀ hv ι n lam R hR hs (gramK emb J) (fun τ => (h τ).1) C
    (fun c τ => tauLat emb τ (L c)) (fun c τ => ((h τ).2.2 (L c) (hL c)).1) N e X
  have h2 := slopeK_holds K v₀ hv ι n lam R hR hs (gramKd emb J) (fun τ => (h τ).2.1) C
    (fun c τ => dualFr (tauLat emb τ (L c))) (fun c τ => ((h τ).2.2 (L c) (hL c)).2) N e X
  exact ⟨h1.2, fun hm => (h1.1 hm).1, h2.2, fun hm => (h2.1 hm).1⟩

theorem slope_holds : GlobalTheory.TestLat.SlopeK ∧ GlobalTheory.TestLat.SlopeE := ⟨slopeK_holds, slopeE_holds⟩

end GlobalTheory.TestLat
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicityAtFittedPoints

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest

namespace GlobalTheory.BigTop.Fun.LeafMMTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Spread

open GlobalTheory.SignedHC

variable (D : D7) (C : ℝ) (τ : D.what₂.Tau)

theorem weightX_zero_bounds {x : ℚ} (hx : x ∈ (num D C τ).weightX 0) :
    ((num D C τ).v D.R.k : ℚ) - 1 / 2 ≤ x ∧ x ≤ (num D C τ).a 0 := by
  have hk : 2 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have hg : (0 : ℚ) ≤ (num D C τ).ga := by positivity
  have v_le_two {i : ℕ} (h1 : 2 ≤ i) (h2 : i ≤ D.R.k) :
      ((num D C τ).v i : ℚ) ≤ (num D C τ).v 2 := by
    rcases h1.eq_or_lt with rfl | h
    · exact le_rfl
    · exact_mod_cast ((num D C τ).v_anti 2 i le_rfl h h2).le
  have a_le {i j : ℕ} (h : i ≤ j) : (num D C τ).a j ≤ (num D C τ).a i := by
    rcases h.eq_or_lt with rfl | h
    · exact le_rfl
    · linarith [a_add_le (G := num D C τ) h]
  have hvk := v_le_two hk le_rfl
  have ham : (num D C τ).a (num D C τ).m = (num D C τ).v 2 + (num D C τ).ga + 1 / 2 := (num D C τ).a_m
  have hlow : ∀ i, i ≤ D.R.m → ((num D C τ).v D.R.k : ℚ) - 1 / 2 ≤ (num D C τ).a i := fun i hi => by
    have := a_le hi
    have e : (num D C τ).m = D.R.m := rfl
    rw [e] at ham
    linarith
  have h0 : ((num D C τ).v 2 : ℚ) + 1 / 2 ≤ (num D C τ).a 0 := by
    have h1 := a_le (Nat.zero_le D.R.m)
    have e : (num D C τ).m = D.R.m := rfl
    rw [e] at ham
    linarith
  rcases GridData.mem_weightX.1 hx with h | h | ⟨i, h1, h2, h⟩ | ⟨l, h1, h2, -⟩
  · obtain ⟨i, hi, rfl⟩ := GridData.mem_tops.1 h
    exact ⟨hlow i hi, a_le (Nat.zero_le i)⟩
  · obtain ⟨i, h1, h2, rfl⟩ := GridData.mem_cloudHalf.1 h
    have hi := v_le_two h1 h2
    have hik : ((num D C τ).v D.R.k : ℚ) ≤ (num D C τ).v i := by
      rcases h2.eq_or_lt with e | e
      · rw [e]; exact le_rfl
      · exact_mod_cast ((num D C τ).v_anti i D.R.k h1 e le_rfl).le
    simp only [GridData.vHalf]
    constructor <;> linarith
  · have hb := blockC'_between (num_nearMid D C τ) (odd_sLen D).pos (sLen_lt_gap D C) h1 h2 h
    have hp := (num D C τ).a_pred h1
    have hq := a_le (Nat.zero_le (i - 1))
    exact ⟨(hlow i h2).trans hb.1.le, by linarith [hb.2]⟩
  · omega

theorem La_sub_le (i j : Fin (rankP D D.R.m)) :
    (((La D C τ).w i - (La D C τ).w j : ℤ) : ℚ) ≤
      (((num D C τ).v 2 - (num D C τ).v D.R.k : ℤ) : ℚ) + 1 + ((D.R.m : ℚ) + 1) * (gap D C : ℚ) + (rankP D D.R.m : ℚ) := by
  push_cast
  rw [La_cast, La_cast]
  simp only [highestWeight]
  have hi := weightX_zero_bounds D C τ (descEnum_mem _ (card_weight D C τ) i)
  have hj := weightX_zero_bounds D C τ (descEnum_mem _ (card_weight D C τ) j)
  have ea : (num D C τ).a 0 = (num D C τ).v 2 + 1 / 2 + ((D.R.m : ℚ) + 1 - ((0 : ℕ) : ℚ)) * (gap D C : ℚ) := rfl
  have hi' : ((i : ℕ) : ℚ) ≤ (rankP D D.R.m : ℚ) := by exact_mod_cast i.2.le
  have hj' : (0 : ℚ) ≤ ((j : ℕ) : ℚ) := by positivity
  rw [ea] at hi hj
  push_cast at hi hj
  linarith [hi.1, hi.2, hj.1, hj.2]

end Spread

section Leaf

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem np_eq {p : PtAt ex Csz} {CF : ℝ} (d : FunIn p CF) : ((rankP D D.R.m : ℕ) : ℝ) = d.O.np := by
  have hm := D.R.two_le_m
  have e1 : D.R.r + 6 - 1 = D.R.k + D.R.m + 4 := by unfold Ranks.r; omega
  have e2 : D.R.r + 1 = D.R.k + D.R.m := by unfold Ranks.r; omega
  have e : rankP D D.R.m = (D.R.k + D.R.m) + D.R.m * (D.R.k + D.R.m + 4) := by
    unfold rankP nRk sLen
    rw [e1, e2]
  rw [e]
  show _ = ((D.R.k : ℝ) + D.R.m - 1 + 1) + D.R.m * (((D.R.k : ℝ) + D.R.m - 1) + 5)
  push_cast
  ring

theorem leafMM_of_test {p : PtAt ex Csz} {CF : ℝ} (d : FunIn p CF) (a : SlopeTestRemainingChoices p d.G d.W d.n) (h : TieTest d a) {C : ℝ}
    (hC : 1 ≤ C) : Formalism.L2.Indef.Tree.LeafMM d.O C := by
  obtain ⟨v₀, hv⟩ := (GlobalTheory.ptField_main D).2.1
  have hga : (gap D 1 : ℝ) ≤ d.O.ga C := by
    rw [← GlobalTheory.BigTop.Fun.Model.ga_eq d 1]
    exact_mod_cast GlobalTheory.SizeLeafCheck.ga_mono _ hC
  have hm0 : (0 : ℝ) ≤ (D.R.m : ℝ) + 1 := by positivity
  have hRp : d.O.Rp C = ((D.R.m : ℝ) + 1) * ((d.O.ga C : ℝ) + 1) + d.O.Lc + d.O.np := rfl
  have hnp : (0 : ℝ) ≤ d.O.np := by rw [← np_eq d]; positivity
  have hR1 : 1 ≤ d.O.Rp C := by
    rw [hRp]
    have : (1 : ℝ) ≤ ((D.R.m : ℝ) + 1) * ((d.O.ga C : ℝ) + 1) := by
      have h1 : (1 : ℝ) ≤ (D.R.m : ℝ) + 1 := by linarith [(Nat.cast_nonneg D.R.m : (0 : ℝ) ≤ D.R.m)]
      have h2 : (1 : ℝ) ≤ (d.O.ga C : ℝ) + 1 := by linarith [(Nat.cast_nonneg (d.O.ga C) : (0 : ℝ) ≤ d.O.ga C)]
      nlinarith
    have : (0 : ℝ) ≤ d.O.Lc := Nat.cast_nonneg _
    linarith
  have hSp : GlobalTheory.TestLat.SpreadLe (LaP d.G) (d.O.Rp C) := by
    intro τ i j
    show (((La D 1 τ).w (Fin.cast (rank_Xp d.G) i) - (La D 1 τ).w (Fin.cast (rank_Xp d.G) j) : ℤ) : ℝ) ≤ _
    have hq := La_sub_le D 1 τ (Fin.cast (rank_Xp d.G) i) (Fin.cast (rank_Xp d.G) j)
    have hr := (Rat.cast_le (K := ℝ)).2 hq
    push_cast at hr
    have hL : ((num D 1 τ).v 2 - (num D 1 τ).v D.R.k).toNat ≤ cloudLen D :=
      Finset.le_sup (f := fun τ => ((GlobalTheory.SignedHC.GridData.ofHCParam (D.hc τ) 0 0 0).v 2 -
        (GlobalTheory.SignedHC.GridData.ofHCParam (D.hc τ) 0 0 0).v D.R.k).toNat) (Finset.mem_univ τ)
    have hL' : (((num D 1 τ).v 2 : ℝ) - (num D 1 τ).v D.R.k) ≤ d.O.Lc := by
      rw [GlobalTheory.BigTop.Fun.Model.Lc_eq d]
      have h1 := Int.self_le_toNat ((num D 1 τ).v 2 - (num D 1 τ).v D.R.k)
      have h2 : (((num D 1 τ).v 2 - (num D 1 τ).v D.R.k : ℤ) : ℝ) ≤ (((num D 1 τ).v 2 - (num D 1 τ).v D.R.k).toNat : ℤ) := by
        exact_mod_cast h1
      have h3 : ((((num D 1 τ).v 2 - (num D 1 τ).v D.R.k).toNat : ℕ) : ℝ) ≤ (cloudLen D : ℝ) := by exact_mod_cast hL
      push_cast at h2
      linarith
    have hmul := mul_le_mul_of_nonneg_left (by linarith : (gap D 1 : ℝ) + 1 ≤ (d.O.ga C : ℝ) + 1) hm0
    have hexp : ((D.R.m : ℝ) + 1) * ((gap D 1 : ℝ) + 1) = ((D.R.m : ℝ) + 1) * (gap D 1 : ℝ) + ((D.R.m : ℝ) + 1) := by ring
    have hm1 : (0 : ℝ) ≤ (D.R.m : ℝ) := Nat.cast_nonneg _
    rw [hRp, ← np_eq d]
    push_cast
    linarith
  obtain ⟨h1, h2, h3, h4⟩ := IsTestLat.gridTestLattice_largestSlope_bound GlobalTheory.TestLat.slope_holds.2 hv hR1 hSp h
  refine ⟨h1, h2, h3, h4.trans (le_of_eq ?_)⟩
  unfold GlobalTheory.TestLat.bound Formalism.L2.Indef.Tree.FunData.EMM
  rw [rank_Xp, np_eq d, D.what₂.card_Tau]
  rfl

end Leaf

end GlobalTheory.BigTop.Fun.LeafMMTie
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MmTie

section

@[expose] public section



section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest
namespace GlobalTheory.BigTop.Fun.LeafMMTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Spread
open GlobalTheory.SignedHC
variable (D : D7) (C : ℝ) (τ : D.what₂.Tau)
end Spread
section Leaf
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}
end Leaf
theorem mm_tie_alt : _root_.GlobalTheory.BigTop.Fun.SettingAtPoint → _root_.GlobalTheory.BigTop.Fun.LeafMinimalMass @GlobalTheory.BigTop.Fun.Comparison₂ := fun h =>
  ⟨0, fun _ _ => h.imp fun _ _ _ _ _ => ⟨1, fun _ hC => _root_.GlobalTheory.BigTop.EventuallyAtPoints.of_forall fun _ _ _ _ _ d hd =>
    let ⟨_, a, ha⟩ := hd
    leafMM_of_test d a ha.test hC⟩⟩
end GlobalTheory.BigTop.Fun.LeafMMTie
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MmTieStatement

section

@[expose] public section



section

theorem _root_.GlobalTheory.T.leafMinimalMass_of_setAt : _root_.GlobalTheory.BigTop.Fun.SettingAtPoint → _root_.GlobalTheory.BigTop.Fun.LeafMinimalMass @GlobalTheory.BigTop.Fun.Comparison₂ := by
  first | exact @_root_.GlobalTheory.BigTop.Fun.LeafMMTie.mm_tie_alt | exact _root_.GlobalTheory.BigTop.Fun.LeafMMTie.mm_tie_alt | (intros; apply _root_.GlobalTheory.BigTop.Fun.LeafMMTie.mm_tie_alt <;> assumption)
end
end
end
