module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RowsPtAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CollSBound
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyPacketOfEquivalentStatement
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.MinkowskiDividesFactorialOfBound
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.FamilyGenusBoundOfSiegelRatio
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VanishingGramTermsBoundParams
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ParametersTermRelations
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TermTieOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CorankSumsBoundWithExpLossStatement
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LoopsCut
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.GammaFixedOfHypotheses
public import Formalism.SharpRestriction.CuspSpanNormBounds.ThresholdCubicInequalitySignPattern

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CorankSizeHypothesisExplicitConstantSiegelMass

section

@[expose] public section

open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Deg
theorem xiSizes_explicit : Formalism.HermitianLatticesTheory.SiegelMassRatio → ∀ C : ℝ, 408 * (Real.exp 1 * Real.pi) ≤ C → ∀ (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A : ℝ), 1 ≤ Cl → Cnt.Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A → Formalism.HermitianLatticeCounting.LatticeSumBounds.XiHyp C D.R.k (2 * D.R.rS + 2) D.R.f large₂.sc.b D.host.v (Cnt.NT D u) (BridgeLemma.XiB D large₂ u C) := by
  intro hS C hC D large₂ u u' C' Cl Cg cb Cu cT CT C0 A hCl hH
  have he : (1 : ℝ) ≤ Real.exp 1 * Real.pi := by
    have h1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    have h2 : (3 : ℝ) ≤ Real.pi := Real.pi_gt_three.le
    nlinarith
  have hmax : max 1 (1 / Cl) ≤ 1 := max_le le_rfl (by rw [div_le_one (by linarith)]; exact hCl)
  have hM2 := Formalism.MainNotions.BridgeLemma₂.plane_mass_bound_parameters D large₂ u u' C' Cl Cg cb Cu cT CT C0 A 8
    (le_trans (mul_le_mul_of_nonneg_left hmax (by norm_num)) (by norm_num))
  have hX := Formalism.MainNotions.BridgeLemma.first_bound_of_mass_ratio D large₂ u u' C' Cl Cg cb Cu cT CT C0 A 8 408
    (Formalism.MainNotions.BridgeLemma.lattice_count_first_of_siegel hS D) hM2 (by norm_num) le_rfl hCl
  have hCX : |(408 : ℝ)| * max 1 |Real.exp 1 * Real.pi| ≤ C := by
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 408), abs_of_pos (by positivity), max_eq_right he]; exact hC
  have hXi := Formalism.MainNotions.BridgeLemma.xiHyp_of_stX D large₂ hH hX hCX (by linarith)
  rw [← Formalism.MainNotions.BridgeLemma.d_m_eq D]
  exact hXi
end GlobalTheory.Core.Deg
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CorankSizeHypothesisExplicitConstantSiegelMassStatement

section

@[expose] public section

open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.corankSizeHypothesis_explicitConstant_siegelMass : Formalism.HermitianLatticesTheory.SiegelMassRatio → ∀ C : ℝ, 408 * (Real.exp 1 * Real.pi) ≤ C → ∀ (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A : ℝ), 1 ≤ Cl → Cnt.Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A → Formalism.HermitianLatticeCounting.LatticeSumBounds.XiHyp C D.R.k (2 * D.R.rS + 2) D.R.f large₂.sc.b D.host.v (Cnt.NT D u) (BridgeLemma.XiB D large₂ u C) := by
  first | exact @GlobalTheory.Core.Deg.xiSizes_explicit | exact GlobalTheory.Core.Deg.xiSizes_explicit | (intros; apply GlobalTheory.Core.Deg.xiSizes_explicit <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PairAbsCorankGeTwoLeSumCorankClasses

section

@[expose] public section

open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Deg

theorem pairAbs_big_le_sum_classes : ∀ (τ Rw I H H₁ : Type) [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (X : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (k : ℕ) (B : ℕ → ℝ), X.AbsConv → (∀ p ∈ X.big X.nzSet, X.s0 p.1 p.2 ≤ k) → (∀ s, 2 ≤ s → s ≤ k → Formalism.L2.SG.LoopsCut.ClassLe X (Formalism.L2.SG.LoopsCut.bigS X s) (B s)) → X.pairAbs (X.big X.nzSet) ≤ ∑ s ∈ Finset.Icc 2 k, B s := by
  intro τ Rw I H H₁ _ _ _ _ _ X k B hA hk hS
  have hG : 0 ≤ X.Gam1 := hA.2.2.le
  have hv : Summable (fun t => ‖X.vec t‖) := hA.2.1
  have hcov : X.big X.nzSet ⊆
      (⋃ s ∈ Finset.Icc 2 k, Formalism.L2.SG.LoopsCut.bigS X s) ∪ (∅ : Set (τ × τ)) := by
    intro p hp
    left
    exact Set.mem_iUnion₂.2 ⟨X.s0 p.1 p.2, Finset.mem_Icc.2 ⟨hp.2, hk p hp⟩, ⟨hp.1, rfl⟩⟩
  have hc := Formalism.L2.SG.LoopsCut.ampSum_cover X hv (Finset.Icc 2 k) (Formalism.L2.SG.LoopsCut.bigS X) ∅
    (X.big X.nzSet) hcov
  have h0 : Formalism.L2.SG.RowsOther.ampSum X (∅ : Set (τ × τ)) = 0 := by
    unfold Formalism.L2.SG.RowsOther.ampSum; simp
  rw [h0, add_zero] at hc
  calc X.pairAbs (X.big X.nzSet)
      ≤ X.Gam1 * Formalism.L2.SG.RowsOther.ampSum X (X.big X.nzSet) :=
        Formalism.L2.SG.RowsOther.pairAbs_le_ampSum X hG _ (Formalism.L2.SG.LoopsCut.amp_summable X hv _)
    _ ≤ X.Gam1 * ∑ s ∈ Finset.Icc 2 k, Formalism.L2.SG.RowsOther.ampSum X (Formalism.L2.SG.LoopsCut.bigS X s) :=
        mul_le_mul_of_nonneg_left hc hG
    _ = ∑ s ∈ Finset.Icc 2 k, X.Gam1 * Formalism.L2.SG.RowsOther.ampSum X (Formalism.L2.SG.LoopsCut.bigS X s) :=
        Finset.mul_sum _ _ _
    _ ≤ ∑ s ∈ Finset.Icc 2 k, B s :=
        Finset.sum_le_sum fun s hs => hS s (Finset.mem_Icc.1 hs).1 (Finset.mem_Icc.1 hs).2

end GlobalTheory.Core.Deg
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PairAbsCorankGeTwoLeSumCorankClassesStatement

section

@[expose] public section

open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.pairAbs_corank_ge_two_le_sum_corankClasses : ∀ (τ Rw I H H₁ : Type) [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (X : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (k : ℕ) (B : ℕ → ℝ), X.AbsConv → (∀ p ∈ X.big X.nzSet, X.s0 p.1 p.2 ≤ k) → (∀ s, 2 ≤ s → s ≤ k → Formalism.L2.SG.LoopsCut.ClassLe X (Formalism.L2.SG.LoopsCut.bigS X s) (B s)) → X.pairAbs (X.big X.nzSet) ≤ ∑ s ∈ Finset.Icc 2 k, B s := by
  first | exact @GlobalTheory.Core.Deg.pairAbs_big_le_sum_classes | exact GlobalTheory.Core.Deg.pairAbs_big_le_sum_classes | (intros; apply GlobalTheory.Core.Deg.pairAbs_big_le_sum_classes <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CollisionAbsSumBoundOfTwoRowBounds

section

@[expose] public section

open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Deg

theorem collS_of_rowBounds : Formalism.HermitianLatticesTheory.SiegelMassRatio → ∀ CT C : ℝ, 408 * (Real.exp 1 * Real.pi) ≤ C → CT ≤ C → ∃ thr : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (sOf hF)) (u : D.what₂.Word) (T : TermTie D) (Z : LoopTie D large₂ T u u 1) (C' Cl Cg cb Cu cT C0 : ℝ), thr ≤ C' → thr ≤ Cl → Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 → ConcTie X Y → (Y.tO u u).AbsConv → TieAt hF hI large₂ u T Z → UnitaryVolumeMass.FormAt D u → BridgeLemma.RowsND T Z C → BridgeLemma.RowsDeg T Z C → CollS Y u := by
  intro hS CT C hC hCT
  have he : (1 : ℝ) ≤ Real.exp 1 * Real.pi := by
    have h1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    have h2 : (3 : ℝ) ≤ Real.pi := Real.pi_gt_three.le
    nlinarith
  have hC1 : (1 : ℝ) ≤ C := by nlinarith
  obtain ⟨K₀, hK⟩ := GlobalTheory.T.corankSums_bound_with_expLoss C hC1
  refine ⟨max K₀ 4, ?_⟩
  intro D large₂ X Y hF hI u T Z C' Cl Cg cb Cu cT C0 hC' hCl hH hCc hAbs hTie hFo hn hd
  have hK₀ : K₀ ≤ C' := le_trans (le_max_left _ _) hC'
  have hC'1 : (1 : ℝ) ≤ C' := by linarith [le_max_right K₀ 4]
  have hCl4 : (4 : ℝ) ≤ Cl := le_trans (le_max_right _ _) hCl
  have hHy := Formalism.MainNotions.count_hypotheses_diagonal_words D large₂ C' Cl Cg cb Cu cT CT C0 1 hH.2.1 hH.1 hH.2.2 (by linarith) hC'1 le_rfl u
  have hXi := GlobalTheory.T.corankSizeHypothesis_explicitConstant_siegelMass hS C hC D large₂ u u C' Cl Cg cb Cu cT CT C0 1 (by linarith) hHy
  have hP := Formalism.L2.SG.LoopsCut.params_at hH X u hCl4 hCT hC1 hK₀
  have hb := Formalism.MainNotions.BridgeLemma.d_two_le_b D large₂
  have hP1 : Formalism.HermitianLatticeCounting.LatticeSumBounds.Params C K₀ D.R.k (2 * D.R.rS + 2) D.R.f large₂.sc.b (X.B.g : ℝ) D.host.v
      (Cnt.NT D u) 1 := by
    obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, _, _⟩ := hP
    refine ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, le_rfl, ?_⟩
    apply Real.one_le_exp
    have hl : 0 ≤ Real.log large₂.sc.b := Real.log_nonneg (by linarith)
    have hC0 : (0 : ℝ) ≤ C := by linarith
    positivity
  have hGam0 : 0 ≤ GamS D large₂ := (Real.exp_pos _).le
  have hGam8 : GamS D large₂ ≤ Real.exp ((D.R.k : ℝ) / 8) := by
    unfold GamS
    apply Real.exp_le_exp.2
    have h1 : 8 * large₂.CGam ≤ C' := hH.1.1
    have h2 : C' * (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L ≤ D.R.k := hH.1.2.1
    have hL := Formalism.MainNotions.BridgeLemma.d_one_le_L D large₂
    have hM : 0 ≤ (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L := by positivity
    nlinarith
  obtain ⟨hND, hDG⟩ := hK D.R.k (2 * D.R.rS + 2) D.R.f large₂.sc.b (X.B.g : ℝ) D.host.v (Cnt.NT D u) (GamS D large₂)
    (BridgeLemma.XiB D large₂ u C) hP1 hXi hGam0 hGam8
  obtain ⟨hJ, hW, hFC, _, _, _, _⟩ := hTie
  have hG := Formalism.L2.SG.LoopTieOf.gammaFixed_of_hypotheses Y hH
  have hm := Formalism.MainNotions.BridgeLemma.d_m_eq D
  have hg : (X.B.g : ℝ) = gg D := by rw [X.g_eq]; unfold gg; push_cast; ring
  have hcls : ∀ s, 2 ≤ s → s ≤ D.R.k → Formalism.L2.SG.LoopsCut.ClassLe (Y.tO u u) (Formalism.L2.SG.LoopsCut.bigS (Y.tO u u) s)
      ((fun s : ℕ => (D.duS u : ℝ) *
        (Formalism.HermitianLatticeCounting.LatticeSumBounds.ndRow C D.R.k (2 * D.R.rS + 2) D.R.f s large₂.sc.b (X.B.g : ℝ) D.host.v (GamS D large₂)
                  (BridgeLemma.XiB D large₂ u C) * BridgeLemma.rDD D u +
          Formalism.HermitianLatticeCounting.LatticeSumBounds.degRow C D.R.k (2 * D.R.rS + 2) D.R.f s large₂.sc.b (X.B.g : ℝ) D.host.v (GamS D large₂)
            (BridgeLemma.XiB D large₂ u C))) s) := by
    intro s h2 hk
    have base := Formalism.L2.SG.LoopTieOf.gam_mul_le hG Z hFo
      (Formalism.L2.SG.LoopTieOf.classS_le T hJ hW hFC Z C hn hd s h2 hk)
    rw [hm, ← hg] at base
    exact base
  have habs := GlobalTheory.T.pairAbs_corank_ge_two_le_sum_corankClasses _ _ _ _ _ (Y.tO u u) D.R.k _ hAbs
    (fun p _ => Formalism.L2.SG.LoopsCut.corank_le_k Y u u p.1 p.2) hcls
  have hdd : ddC X Y u u = (D.duS u : ℝ) * BridgeLemma.rDD D u := Formalism.L2.SG.LoopTieOf.ddC_eq hCc u u
  have hdu : duC X Y u = (D.duS u : ℝ) := hCc.2.2.1 u
  have hdr0 : 0 ≤ (D.duS u : ℝ) * BridgeLemma.rDD D u := hdd ▸ dd_nonneg hCc u u
  have hd0 : (0 : ℝ) ≤ (D.duS u : ℝ) := Nat.cast_nonneg _
  have hgg : ((X.B.g : ℕ) : ℝ) = (D.host.g 0 : ℝ) * (D.host.g 1 : ℝ) := by rw [X.g_eq]; push_cast; ring
  unfold CollS
  rw [hdd, hdu]
  set d : ℝ := (D.duS u : ℝ) with hdef
  set r : ℝ := BridgeLemma.rDD D u with hrdef
  set N := fun s : ℕ => Formalism.HermitianLatticeCounting.LatticeSumBounds.ndRow C D.R.k (2 * D.R.rS + 2) D.R.f s large₂.sc.b (X.B.g : ℝ) D.host.v (GamS D large₂)
    (BridgeLemma.XiB D large₂ u C) with hN
  set G := fun s : ℕ => Formalism.HermitianLatticeCounting.LatticeSumBounds.degRow C D.R.k (2 * D.R.rS + 2) D.R.f s large₂.sc.b (X.B.g : ℝ) D.host.v (GamS D large₂)
    (BridgeLemma.XiB D large₂ u C) with hGd
  have hsum : ∑ s ∈ Finset.Icc 2 D.R.k, d * (N s * r + G s) =
      d * r * ∑ s ∈ Finset.Icc 2 D.R.k, N s + d * ∑ s ∈ Finset.Icc 2 D.R.k, G s := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun s _ => by ring
  calc _ ≤ ∑ s ∈ Finset.Icc 2 D.R.k, d * (N s * r + G s) := habs
    _ = d * r * ∑ s ∈ Finset.Icc 2 D.R.k, N s + d * ∑ s ∈ Finset.Icc 2 D.R.k, G s := hsum
    _ ≤ d * r * (√(X.B.g : ℝ))⁻¹ ^ (D.R.k * D.R.f) +
        d * Real.exp (-((D.R.k : ℝ) * D.R.f * Real.log D.R.k) / 2) :=
      add_le_add (mul_le_mul_of_nonneg_left hND hdr0) (mul_le_mul_of_nonneg_left hDG hd0)
    _ = _ := by rw [hgg]; ring

end GlobalTheory.Core.Deg
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CollisionAbsSumBoundOfTwoRowBoundsStatement

section

@[expose] public section

open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.collisionAbsSum_bound_of_two_rowBounds : Formalism.HermitianLatticesTheory.SiegelMassRatio → ∀ CT C : ℝ, 408 * (Real.exp 1 * Real.pi) ≤ C → CT ≤ C → ∃ thr : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (sOf hF)) (u : D.what₂.Word) (T : TermTie D) (Z : LoopTie D large₂ T u u 1) (C' Cl Cg cb Cu cT C0 : ℝ), thr ≤ C' → thr ≤ Cl → Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 → ConcTie X Y → (Y.tO u u).AbsConv → TieAt hF hI large₂ u T Z → UnitaryVolumeMass.FormAt D u → BridgeLemma.RowsND T Z C → BridgeLemma.RowsDeg T Z C → CollS Y u := by
  first | exact @GlobalTheory.Core.Deg.collS_of_rowBounds | exact GlobalTheory.Core.Deg.collS_of_rowBounds | (intros; apply GlobalTheory.Core.Deg.collS_of_rowBounds <;> assumption)
end
end
