module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsScaleWithBoundedGamma
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistedBundle
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotInhAbsOfGamLe
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdmissibleRanksAllMembers
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CollisionTypingsCompare
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RealTiedSetDiv
public import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.TypePrimesOfLevel
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
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
public import Formalism.LocalRingCardinality.DataKerI
import Formalism.LocalToGlobal.Columns.GenericUnipotentCharacter
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AdmissibleRanksOfMassStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HypLAtPointsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RankMuOfBundleStatement
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SetUnipotentTranslate
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Mathlib.Tactic.Linter.Style
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ValSizesAtStatement
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ColumnStabilizerTrivialLocal

section

@[expose] public section

noncomputable section

namespace GlobalTheory.Proof.ColumnStabilizerTrivialLocal

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col
open GlobalTheory.IndefiniteRowSideFullHecke

section Generic

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n n' : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

end Generic

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem typePrimesLarge_iff (D : D7) :
    UnipotentLevelStabilisers.TypePrimesLarge D ↔ ∀ i, 2 * D.R.f * D.R.k < D.host.g i - 1 :=
  forall_congr' fun i => by omega

theorem gBig_of_large (h : UnipotentLevelStabilisers.TypePrimesLarge D) : Formalism.MainNotions.StandardLattice.GBig D :=
  ⟨0, (typePrimesLarge_iff D).mp h 0⟩

variable {Dx : DivX D} {Tw : TwForms D} (E : KerEnt D Dx Tw)

end GlobalTheory.Proof.ColumnStabilizerTrivialLocal
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AdmissibleRanksAtMember

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.MemberRanks
theorem admissible_ranks_at_member_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL),
    GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ D _ _ _ => Formalism.MainNotions.LocalBesselAndTopKernel.FamilyMidVolume D) := by
  intro hL p
  refine GlobalTheory.Fc.RowE.of_all fun κ K β c b h0 h1 h2 => ?_
  obtain ⟨hv, -⟩ :=
    GlobalTheory.Fc.built_val _root_.GlobalTheory.Fc.BundleCondition (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) κ β.D β.O c b (GlobalTheory.Fc.Built.intro h0 h1 h2)
  exact columnRowRanks_admissible_of_massFormula β.D β.O.lev b.R.T.cols (dstar_mass K β.X β.c.isOver β.c.dsig_eq)
    (GlobalTheory.Proof.ColumnStabilizerTrivialLocal.gBig_of_large (typePrimesLarge_of_val β.O.L hv)) (fun u => GlobalTheory.CollCompare.splits_level β.D u)
end GlobalTheory.MemberRanks
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AdmissibleRanksAtMemberStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.familyMidVolume_at_linked : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ D _ _ _ => Formalism.MainNotions.LocalBesselAndTopKernel.FamilyMidVolume D) := by
  first | exact @_root_.GlobalTheory.MemberRanks.admissible_ranks_at_member_alt | exact _root_.GlobalTheory.MemberRanks.admissible_ranks_at_member_alt | (intros; apply _root_.GlobalTheory.MemberRanks.admissible_ranks_at_member_alt <;> assumption)
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LargeGapAllMembers

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Rk.GapAt

theorem poly_bound {M k m f r L T n t N : ℝ} (hM : 1 ≤ M) (hk1 : 1 ≤ k) (hk : k ≤ M) (hm1 : 1 ≤ m) (hm : m ≤ M)
    (hf0 : 0 ≤ f) (hf : f ≤ M) (hr0 : 0 ≤ r) (hr : r ≤ M) (hL0 : 0 ≤ L) (hL : L ≤ M) (hT : T ≤ M) (hn0 : 0 ≤ n)
    (hn : n ≤ 10 * r * (f + f ^ 2 * (k - 1) ^ 3 * L ^ 2 / m) + 8) (ht0 : 0 ≤ t) (ht : t ≤ 8 * f * r + 4 + T * n)
    (hN : N = k + m * (t + 1)) : 4 * N ^ 3 + 2 * t + 6 ≤ 300000 * M ^ 30 := by
  have hM0 : 0 ≤ M := by linarith
  have hk' : 0 ≤ k - 1 := by linarith
  have hk'' : k - 1 ≤ M := by linarith
  have pw : ∀ a b : ℕ, a ≤ b → M ^ a ≤ M ^ b := fun a b h => pow_le_pow_right₀ hM h
  have h1 : f ^ 2 * (k - 1) ^ 3 * L ^ 2 / m ≤ M ^ 7 := by
    calc f ^ 2 * (k - 1) ^ 3 * L ^ 2 / m ≤ f ^ 2 * (k - 1) ^ 3 * L ^ 2 := div_le_self (by positivity) hm1
      _ ≤ M ^ 2 * M ^ 3 * M ^ 2 := by gcongr
      _ = M ^ 7 := by ring
  have h10 : 0 ≤ f ^ 2 * (k - 1) ^ 3 * L ^ 2 / m := by
    have : 0 ≤ m := by linarith
    positivity
  have h2 : n ≤ 28 * M ^ 8 := by
    have a1 : f ≤ M ^ 7 := by have := pw 1 7 (by norm_num); rw [pow_one] at this; linarith
    have a2 : r * (f + f ^ 2 * (k - 1) ^ 3 * L ^ 2 / m) ≤ M * (2 * M ^ 7) :=
      mul_le_mul hr (by linarith) (by linarith) hM0
    have a3 : M * (2 * M ^ 7) = 2 * M ^ 8 := by ring
    have a4 := pw 0 8 (by norm_num)
    rw [pow_zero] at a4
    rw [mul_assoc] at hn
    linarith
  have h3 : t ≤ 40 * M ^ 9 := by
    have a1 : f * r ≤ M * M := mul_le_mul hf hr hr0 hM0
    have a2 : T * n ≤ M * (28 * M ^ 8) := mul_le_mul hT h2 hn0 hM0
    have a3 : M * (28 * M ^ 8) = 28 * M ^ 9 := by ring
    have a4 := pw 0 9 (by norm_num)
    have a5 := pw 2 9 (by norm_num)
    rw [pow_zero] at a4
    rw [pow_two] at a5
    rw [mul_assoc] at ht
    linarith
  have h4 : N ≤ 42 * M ^ 10 := by
    have a4 := pw 0 9 (by norm_num)
    rw [pow_zero] at a4
    have a1 : m * (t + 1) ≤ M * (41 * M ^ 9) := mul_le_mul hm (by linarith) (by linarith) hM0
    have a3 : M * (41 * M ^ 9) = 41 * M ^ 10 := by ring
    have a5 := pw 1 10 (by norm_num)
    rw [pow_one] at a5
    linarith
  have hN0 : 0 ≤ N := by
    rw [hN]
    have : 0 ≤ m * (t + 1) := mul_nonneg (by linarith) (by linarith)
    linarith
  have h5 : N ^ 3 ≤ 74088 * M ^ 30 := by
    calc N ^ 3 ≤ (42 * M ^ 10) ^ 3 := pow_le_pow_left₀ hN0 h4 3
      _ = 74088 * M ^ 30 := by ring
  have a4 := pw 0 30 (by norm_num)
  have a5 := pw 9 30 (by norm_num)
  rw [pow_zero] at a4
  linarith

theorem rank_bound (s : Scale) (R : Ranks) (h : RankVal s R) :
    4 * ((R.N R.m : ℕ) : ℝ) ^ 3 + 2 * R.t + 6 ≤ 300000 * (4 * s.x ^ (377 : ℝ)) ^ 30 := by
  obtain ⟨-, -, ⟨-, hk⟩, ht⟩ := h
  have hx := s.one_lt_alt.le
  have e0 := s.eps_pos
  have e1 := s.eps_lt
  have hY : 1 ≤ s.x ^ (377 : ℝ) := Real.one_le_rpow hx (by norm_num)
  have hk2 : (R.k : ℝ) ≤ 2 * s.x ^ (377 : ℝ) := by
    have := Real.rpow_le_rpow_of_exponent_le hx (show 9 / 2 + 10 * s.eps ≤ (377 : ℝ) by linarith)
    linarith
  have hL : s.L ≤ s.x ^ (377 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx (show s.eps ≤ (377 : ℝ) by linarith)
  have hL0 : 0 ≤ s.L := Real.rpow_nonneg (by linarith) _
  have n1 := R.two_le_m
  have n2 := R.m_add_three_le_k
  have hm1 : (1 : ℝ) ≤ R.m := by exact_mod_cast (show 1 ≤ R.m by omega)
  have hk1 : (1 : ℝ) ≤ R.k := by exact_mod_cast (show 1 ≤ R.k by omega)
  have hmk : (R.m : ℝ) ≤ R.k := by exact_mod_cast (show R.m ≤ R.k by omega)
  have hfk : (R.f : ℝ) ≤ R.k := by exact_mod_cast (show R.f ≤ R.k from R.f_le_k)
  have hrk : (R.r : ℝ) ≤ 2 * R.k := by
    exact_mod_cast (show R.r ≤ 2 * R.k by unfold Ranks.r; omega)
  have hT : (TOv s : ℝ) ≤ 4 * s.x ^ (377 : ℝ) := by
    have := Nat.ceil_lt_add_one (show 0 ≤ s.x ^ (377 : ℝ) by linarith)
    unfold TOv
    linarith
  have hn : (nWv R s : ℝ) ≤ 10 * (R.r : ℝ) * ((R.f : ℝ) + (R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 * s.L ^ 2 / R.m) + 8 := by
    have hk' : (0 : ℝ) ≤ (R.k : ℝ) - 1 := by linarith
    have := Nat.ceil_lt_add_one
      (show 0 ≤ 10 * (R.r : ℝ) * ((R.f : ℝ) + (R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 * s.L ^ 2 / R.m) / 8 by positivity)
    unfold nWv
    push_cast
    linarith
  have ht' : (R.t : ℝ) ≤ 8 * (R.f : ℝ) * R.r + 4 + (TOv s : ℝ) * nWv R s := by
    exact_mod_cast (show R.t ≤ 8 * R.f * R.r + 4 + TOv s * nWv R s by omega)
  refine poly_bound (by linarith) hk1 (by linarith) hm1 (by linarith) (Nat.cast_nonneg _) (by linarith) (Nat.cast_nonneg _)
    (by linarith) hL0 (by linarith) hT (Nat.cast_nonneg _) hn (Nat.cast_nonneg _) ht' ?_
  unfold Ranks.N
  push_cast
  rfl

theorem nodeGap_of_val {C : FC} {cD ch : ℝ} {D : D7} {L : SizeData₂ D} (h : Val C cD ch L) : D.NodeGap (h0v L.sc ch : ℝ) := by
  intro u τ j hj
  obtain ⟨b1, hb, -⟩ := h.hc.2.2.1
  rw [D.hcW_b u τ, (hb τ _).1, (hb τ _).1]
  push_cast
  exact le_of_eq (by ring)

theorem bigGap_of_val {C : FC} {cD ch : ℝ} {D : D7} {L : SizeData₂ D} (h : Val C cD ch L) (hch : 11311 ≤ ch)
    (hx : 300000 * 4 ^ 30 ≤ L.sc.x) : BigGap D := by
  refine (nodeGap_of_val h).mono ((rank_bound L.sc D.R h.ranks).trans ?_)
  have h1 := L.sc.one_lt_alt
  have h0 : 0 < L.sc.x := by linarith
  have e1 : (L.sc.x ^ (377 : ℝ)) ^ 30 = L.sc.x ^ (11310 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul h0.le]; norm_num
  have e2 : L.sc.x * L.sc.x ^ (11310 : ℝ) ≤ L.sc.x ^ ch := by
    rw [mul_comm, ← Real.rpow_add_one h0.ne']
    exact Real.rpow_le_rpow_of_exponent_le h1.le (by linarith)
  have e3 : 0 ≤ L.sc.x ^ (11310 : ℝ) := Real.rpow_nonneg h0.le _
  have e4 := mul_le_mul_of_nonneg_right hx e3
  have e5 := Nat.le_ceil (L.sc.x ^ ch)
  have e6 : (0 : ℝ) ≤ (⌈L.sc.x ^ ch⌉₊ : ℝ) := Nat.cast_nonneg _
  rw [mul_pow, e1, ← mul_assoc]
  unfold h0v
  push_cast
  linarith

end GlobalTheory.Core.Rk.GapAt

end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowEBigGap

section

@[expose] public section



section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Core.Rk.GapAt
theorem rowE_bigGap_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL),
    GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ D _ _ _ => GlobalTheory.Core.Rk.BigGap D) := by
  intro hL p
  refine ⟨1, one_pos, fun _ _ _ _ _ _ _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun _ _ _ _ => ⟨0, fun _ _ =>
    ⟨11311, fun ch hch _ => ⟨300000 * 4 ^ 30, fun K hK hx β _ _ _ _ => ?_⟩⟩⟩⟩⟩
  show BigGap β.X.toD7
  refine bigGap_of_val β.val ?_ ?_
  · rw [hK.2.2.1]; exact hch
  · rw [β.sc]; exact hx
end GlobalTheory.Core.Rk.GapAt
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowEBigGapStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.bigGap_of_isGoodE_isLinked : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ D _ _ _ => GlobalTheory.Core.Rk.BigGap D) := by
  first | exact @_root_.GlobalTheory.Core.Rk.GapAt.rowE_bigGap_alt | exact _root_.GlobalTheory.Core.Rk.GapAt.rowE_bigGap_alt | (intros; apply _root_.GlobalTheory.Core.Rk.GapAt.rowE_bigGap_alt <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MemberSizes

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.Fam.MemberSizes
variable (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL)
theorem ties_at_alt : GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ D _ _ _ => Formalism.BasicNotions.Ties D) :=
  RowE.of_all fun _ _ β _ _ _ _ _ => β.p.pt.xa.ties
theorem linked_scale_ge_H_and_cgam_eq (H : Formalism.MainNotions.Inhab.FC → ℝ) : GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun κ _ O _ _ =>
    H κ.C ≤ O.L.sc.L ∧ O.L.CGam = κ.C.CGam ∧ 1 ≤ κ.C.CGam) := by
  refine ⟨1, one_pos, fun eps C8 C5 c6 Cb he _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun C hC _ _ =>
    ⟨0, fun cD _ => ⟨0, fun ch _ _ => ⟨max 1 (max (H C) 1 ^ eps⁻¹), fun K hK hx β _ c b _ => ?_⟩⟩⟩⟩⟩
  have hG : 1 ≤ C.CGam := hC.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _ (by simp [Inhab.FC.cMid])
  have hs : β.O.L.sc = K.s := β.sc
  have hc : β.O.L.CGam = C.CGam := β.val.CGam_eq.trans (congrArg Inhab.FC.CGam hK.1)
  refine ⟨?_, hc, hG⟩
  show H C ≤ β.O.L.sc.x ^ β.O.L.sc.eps
  rw [hs, hK.2.2.2.1]
  have h1 : 0 ≤ max (H C) 1 := le_trans zero_le_one (le_max_right _ _)
  calc H C ≤ max (H C) 1 := le_max_left _ _
    _ = (max (H C) 1 ^ eps⁻¹) ^ eps := (Real.rpow_inv_rpow h1 he.ne').symm
    _ ≤ K.s.x ^ eps := Real.rpow_le_rpow (Real.rpow_nonneg h1 _) (le_trans (le_max_right _ _) hx) he.le
theorem parameters_scale_rank_gap_bounds (F G H : ℝ → ℝ → ℝ) : GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ D O _ _ =>
    ∃ C' Cl Cg CT : ℝ, F Cg CT ≤ C' ∧ G Cg CT ≤ Cl ∧ H Cg CT ≤ O.L.sc.L ∧
      GlobalTheory.Core.Rk.HD D O.L.sc.L C' Cl Cg (1 / 4) 3 (1 / 2) CT ∧ GlobalTheory.Core.Rk.IsScaleWithBoundedGamma D O.L.sc.L C' ∧
      (∀ u, GlobalTheory.Core.Rk.RankMu D u) ∧ GlobalTheory.Core.Rk.BigGap D ∧ 1 ≤ D.R.rS) := by
  have h := (((((((_root_.GlobalTheory.Fam.MemberSizes.ties_at_alt hL p).and (_root_.GlobalTheory.T.familyMidVolume_at_linked hL p)).and (_root_.GlobalTheory.T.degHypL_all_linked_good_members hL p (fun C => F (C.P.CYL + 1) C.CTu) (fun C => G (C.P.CYL + 1) C.CTu))).and (_root_.GlobalTheory.T.dataNW_all_linked_good_members hL p)).and (_root_.GlobalTheory.T.type_frame_all_members' hL p)).and (_root_.GlobalTheory.T.rankMu_all_linked_members hL p)).and (_root_.GlobalTheory.T.bigGap_of_isGoodE_isLinked hL p)).and (_root_.GlobalTheory.Fam.MemberSizes.linked_scale_ge_H_and_cgam_eq hL p (fun C => H (C.P.CYL + 1) C.CTu))
  refine RowE.imp h ?_
  intro κ K β c b _ _ _ H0
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8, h9, h10⟩ := H0
  have hm : max (G (κ.C.P.CYL + 1) κ.C.CTu) 40 ≤ (β.D.R.m : ℝ) :=
    h3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨max (F (κ.C.P.CYL + 1) κ.C.CTu) (8 * κ.C.CGam), max (G (κ.C.P.CYL + 1) κ.C.CTu) 40, κ.C.P.CYL + 1, κ.C.CTu,
    le_max_left _ _, le_max_left _ _, h8, ⟨h1, h2, h3, h4, h5⟩, ⟨β.O.L, rfl, h9 ▸ le_max_right _ _, h9 ▸ h10⟩, h6, h7, ?_⟩
  have h40 : (40 : ℝ) ≤ β.D.R.m := le_trans (le_max_right _ _) hm
  have : 40 ≤ β.D.R.m := by exact_mod_cast h40
  show 1 ≤ β.D.R.m / 2 - 1
  omega
theorem parameters_scale_size_bounds_of_member : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) (F G H : ℝ → ℝ → ℝ),
    GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ D O _ _ => ∃ C' Cl Cg CT : ℝ, F Cg CT ≤ C' ∧ G Cg CT ≤ Cl ∧
      H Cg CT ≤ O.L.sc.L ∧ GlobalTheory.Core.Rk.HD D O.L.sc.L C' Cl Cg (1 / 4) 3 (1 / 2) CT ∧ GlobalTheory.Core.Rk.IsScaleWithBoundedGamma D O.L.sc.L C' ∧
      (∀ u, GlobalTheory.Core.Rk.RankMu D u) ∧ GlobalTheory.Core.Rk.BigGap D ∧ 1 ≤ D.R.rS) :=
  fun hL p F G H => _root_.GlobalTheory.Fam.MemberSizes.parameters_scale_rank_gap_bounds hL p F G H
end GlobalTheory.Fam.MemberSizes
end
end
end
end
