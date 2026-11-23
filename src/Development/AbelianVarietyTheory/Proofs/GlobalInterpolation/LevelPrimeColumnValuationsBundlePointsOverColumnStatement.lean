module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AndLeft
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LevelPrimeColumnValuationsAtBundlePoints
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EFirstGeOfULastNonpos
public import Formalism.LocalToGlobal.GroupLattices.AdmissibleAtGeneratorPlaces
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw
public import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LevelChainSharpColumnValuationOwnChainIff
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MoveStep
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FivePointLawsTrueChains
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SharpBoundStabilityLatticeColumnChain
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FormsStable
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TwistedChainInitialLatticeCompatibleTrueColumns
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.KerIsTerm
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MoveStep
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.KerIsTerm
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PropertyAtConstructedPointsOfTrueColumnsViewStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ColumnWeightTwisted

section

@[expose] public section

open Formalism.BasicNotions GlobalTheory.LvT

namespace GlobalTheory.Proof.ColumnWeightTwisted

theorem exists_int_m_mul_EatT (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl) :
    ∃ k : ℤ, (D.R.m : ℝ) * EatT D u w = (k : ℝ) := by
  unfold EatT
  split_ifs
  · obtain ⟨a, ha⟩ := D.R.m_even
    obtain ⟨b, hb⟩ := D.R.t_odd
    refine ⟨(D.R.m : ℤ) * (2 * (∑ τ : D.what₂.Tau, (Wtau D u τ : ℤ)) + (D.R.f : ℤ) * (D.R.N D.R.m : ℤ)) +
      ((topsOf D.host D.eTau).card : ℤ) * ((b : ℤ) + 1) * ((D.R.m : ℤ) + 1) * a, ?_⟩
    have ha' : (D.R.m : ℝ) = a + a := by exact_mod_cast ha
    have hb' : (D.R.t : ℝ) = 2 * b + 1 := by exact_mod_cast hb
    unfold Formalism.MainNotions.G.Nm
    push_cast
    rw [hb', ha']
    ring
  · exact ⟨0, by simp⟩

theorem colGeTw_of_tupleChainSharpColumnValuation : ∀ (D : D7) (T : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup), TupleChainSharpColumnValuation T u μ → ∀ w : D.what₂.places.Pl, D.what₂.places.resChar w = (D.mem u).A.T → ∀ x ∈ LT.Nlam D u w, Formalism.MainNotions.WeilJacquetShalikaLaw.ColGeTw T u μ w x (-((D.R.m : ℝ) * EatT D u w)) := by
  intro D T u μ h w hw x hx
  obtain ⟨k, hk⟩ := exists_int_m_mul_EatT D u w
  obtain ⟨c, hc⟩ := D.what₂.places.val_surj w ((D.what₂.places.ramIdx w : ℤ) * k)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [AddValuation.map_zero] at hc
    exact WithTop.top_ne_coe hc
  obtain ⟨y, hy, e⟩ := h w hw c _ hc (by rw [hk]; push_cast; exact le_rfl) x hx
  have hv : vAdd (D.plEq w) c = (D.what₂.places.ramIdx w : ℤ) * k := by
    rw [D.val_eq w _ hc0] at hc
    exact_mod_cast hc
  have hvi : vAdd (D.plEq w) c⁻¹ = - vAdd (D.plEq w) c := by
    unfold vAdd
    rw [map_inv₀, WithZero.log_inv]
  refine ⟨c⁻¹ • y, ?_, c⁻¹, y, hy, rfl, Or.inr ?_⟩
  · rw [LinearMap.map_smulₛₗ, e, smul_smul, ← map_mul, inv_mul_cancel₀ hc0, map_one, one_smul]
  · rw [hvi, hv, hk]
    unfold DV.ur
    push_cast
    exact le_of_eq (by ring)

end GlobalTheory.Proof.ColumnWeightTwisted
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FivePointLawsTrueChainsStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built GlobalTheory.LvT.Built.TrueLaws

theorem _root_.GlobalTheory.T.fivePointLaws_trueChains :
    ∀ (B : GlobalTheory.Mem.Base) (X : PreX B.toPre) (I : TC B X), I.Ok → I.JetsIn →
    ∀ (l : I.Laws) (l0 : I.Law0 l) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι),
      ∃ Bd : Built.Dat (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) u,
        Bd.ch = tw (I.tw l l0 Z) u a ∧
        (∀ i, i ≤ (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.m →
          letI : NumberField Bd.E := Bd.nE
          Nonempty (Split (Bd.J.A i) Bd.J.T)) ∧ Bd.Sees ∧
        (∀ i, i < (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.m →
          ∃ k : Bd.Ker i, Dat.KerEq k ∧ Dat.KerDil k ∧ Dat.KerUK k ∧ Dat.KerBar k ∧ Dat.KerP k) ∧
        Bd = dat I l Z u a := by
  exact GlobalTheory.LvT.Built.TrueLaws.laws_true_fam
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TupleChainSharpColumnValuationOfTwisted

section

@[expose] public section

open Formalism.BasicNotions Classical NumberField GlobalTheory.LvT
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)

noncomputable section
namespace GlobalTheory.LvT.TwSharp

variable {D : D7} {u : D.what₂.Word}

theorem weight_eq (X Y : Ch D u) (j : ℕ) (hj : j ≤ D.R.m) (τ : D.what₂.Tau) (a : Fin (D.R.N j)) :
    (X.fm.lam j τ).w a = (Y.fm.lam j τ).w a := by
  have h := (X.fm.lam_eq j hj τ a).trans (Y.fm.lam_eq j hj τ a).symm
  exact_mod_cast h

theorem weightSup_eq (X Y : Ch D u) (τ : D.what₂.Tau) : TauWeight X τ = TauWeight Y τ := by
  unfold TauWeight
  refine Finset.sup_congr rfl fun i hi => Finset.sup_congr rfl fun a _ => ?_
  rw [weight_eq X Y i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) τ a]

theorem exponent_eq (X Y : Ch D u) : ETpi X = ETpi Y := by
  unfold ETpi Wt; simp only [weightSup_eq X Y]

theorem tupleChainSharpColumnValuation_of_twisted : ∀ (D : D7) (u : D.what₂.Word) (Tw : TwForms D) (μ : D.what₂.Tup),
    Step0Tie Tw u μ → Conclusion5Sharp (tw Tw u μ) → TupleChainSharpColumnValuation Tw u μ := by
  intro D u Tw μ hT h w hw c n hc hn x hx
  have hw' : OverT (tw Tw u μ) w := hw.trans (Tw.A_T u μ).symm
  have hown : ET (own D u) w = EatT D u w := rfl
  have hE : ET (tw Tw u μ) w = EatT D u w := by
    rw [← hown]; unfold ET
    rw [exponent_eq (tw Tw u μ) (own D u)]
    show (if (Tw.fm u μ).seenP w = true then _ else _) = _
    rw [(hT w hw).1]
  obtain ⟨y, hy, e⟩ := h w hw' c n hc (hE ▸ hn) (Tw.e0 u μ x) ((hT w hw).2 x hx)
  refine ⟨y, hy, e.trans ?_⟩
  show _ • (D.chTw u μ).col ((Tw.fm u μ).emb 0 (Tw.e0 u μ x)) = _
  rw [Tw.embed_mul_block_embedding]

end GlobalTheory.LvT.TwSharp
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TwistedChainInitialLatticeCompatibleTrueColumnsStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built GlobalTheory.LvT.Built.TrueLaws

theorem _root_.GlobalTheory.T.twistedChain_initialLattice_compatible_trueColumns : ∀ (B : GlobalTheory.Mem.Base) (X : PreX B.toPre) (I : TC B X), I.Ok → ∀ (l : I.Laws) (l0 : I.Law0 l) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι), Step0Tie (I.tw l l0 Z) u a := by
  first | exact @GlobalTheory.LvT.TrueStep0.step0Tie_trueCols | exact GlobalTheory.LvT.TrueStep0.step0Tie_trueCols | (intros; apply GlobalTheory.LvT.TrueStep0.step0Tie_trueCols <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TrueColumnsRowSharpBounds

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built GlobalTheory.LvT.Built.TrueLaws

noncomputable section
namespace GlobalTheory.LvT.Built.TrueCols

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X}

theorem trueColumns_chain_last_step_sharp_bound (h : I.Ok) (hJ : I.JetsIn) (hS : GlobalTheory.LvT.WtSign.BaseSigns B) (l : I.Laws) (l0 : I.Law0 l)
    (Z : TC.Later B (I.cols l)) (u : (I.rec7 l Z).what₂.Word) (a : I.ι) : Conclusion5Sharp (tw (I.tw l l0 Z) u a) := by
  obtain ⟨Bd, hch, hsp, hse, hk, hBd⟩ := GlobalTheory.T.fivePointLaws_trueChains B X I h hJ l l0 Z u a
  have hT : Module.finrank ℚ Bd.E * (I.rec7 l Z).R.N (I.rec7 l Z).R.m + 1 < Bd.J.T := by
    subst hBd
    show Module.finrank ℚ B.host.E * B.R.N B.R.m + 1 < B.T u
    have h1 := X.a_gt
    have h2 := X.T_gt u
    have hf : Module.finrank ℚ B.host.E = 2 * B.R.f := by
      rw [B.host.finrank_cmField, Formalism.BasicNotions.Ranks.f, Formalism.BasicNotions.Ranks.n]
      ring
    rw [hf]
    have h3 : ((2 * B.R.f * B.R.N B.R.m + 1 : ℕ) : ℝ) < (B.T u : ℝ) := lt_trans h1 h2
    exact_mod_cast h3
  have hW : TwColumn.WtSigns Bd.ch :=
    (GlobalTheory.LvT.WtSign.wtSigns_assemble_iff B (I.cols l) Z.W Z.V Z.S Z.N Z.G u Bd.ch).2 hS
  have := (GlobalTheory.LvT.Built.Assemble.sharpBound_stability_latticeColumnChain (I.rec7 l Z) u Bd hsp hse hk hT hW).1
  rwa [hch] at this

theorem row_true : ∀ (B : GlobalTheory.Mem.Base) (X : PreX B.toPre) (I : TC B X), I.Ok → I.JetsIn → GlobalTheory.LvT.WtSign.BaseSigns B →
    ∀ (l : I.Laws) (l0 : I.Law0 l) (Z : TC.Later B (I.cols l)) (Dx : DivX (I.rec7 l Z)) (u : (I.rec7 l Z).what₂.Word),
      Formalism.MainNotions.product_first_zeroth_parts.Conclusion5Sharp (I.rec7 l Z) u ∧ ∀ w : (I.rec7 l Z).what₂.places.Pl,
        (I.rec7 l Z).what₂.places.resChar w = ((I.rec7 l Z).mem u).A.T → ∀ μ, Formalism.MainNotions.LocalQuadraticParts.UsedT (I.rec7 l Z) μ →
        μ ≠ (I.rec7 l Z).what₂.mu0 → (I.rec7 l Z).what₂.places.resChar w ∉ Dx.Qp μ → ∀ x ∈ LT.Nlam (I.rec7 l Z) u w,
        Formalism.MainNotions.WeilJacquetShalikaLaw.ColGeTw (I.tw l l0 Z) u μ w x (-(((I.rec7 l Z).R.m : ℝ) * EatT (I.rec7 l Z) u w)) := by
  intro B X I h hJ hS l l0 Z Dx u
  refine ⟨?_, fun w hw μ _ _ _ x hx => ?_⟩
  · have h0 := trueColumns_chain_last_step_sharp_bound h hJ hS l l0 Z u I.mu0
    rw [← own_eq I l l0 Z u] at h0
    exact (levelChainSharpColumnValuation_ownChain_iff (I.rec7 l Z) u).1 h0
  · have hTw : TupleChainSharpColumnValuation (I.tw l l0 Z) u μ :=
      TwSharp.tupleChainSharpColumnValuation_of_twisted (I.rec7 l Z) u (I.tw l l0 Z) μ (GlobalTheory.T.twistedChain_initialLattice_compatible_trueColumns B X I h l l0 Z u μ)
        (trueColumns_chain_last_step_sharp_bound h hJ hS l l0 Z u μ)
    exact GlobalTheory.Proof.ColumnWeightTwisted.colGeTw_of_tupleChainSharpColumnValuation (I.rec7 l Z) (I.tw l l0 Z) u μ hTw w hw x hx

end GlobalTheory.LvT.Built.TrueCols
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TrueColumnsRowSharpBoundsStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built GlobalTheory.LvT.Built.TrueLaws

theorem _root_.GlobalTheory.T.trueColumns_row_sharp_bounds : ∀ (B : GlobalTheory.Mem.Base) (X : PreX B.toPre) (I : TC B X), I.Ok → I.JetsIn → GlobalTheory.LvT.WtSign.BaseSigns B → ∀ (l : I.Laws) (l0 : I.Law0 l) (Z : TC.Later B (I.cols l)) (Dx : DivX (I.rec7 l Z)) (u : (I.rec7 l Z).what₂.Word), Formalism.MainNotions.product_first_zeroth_parts.Conclusion5Sharp (I.rec7 l Z) u ∧ ∀ w : (I.rec7 l Z).what₂.places.Pl, (I.rec7 l Z).what₂.places.resChar w = ((I.rec7 l Z).mem u).A.T → ∀ μ, Formalism.MainNotions.LocalQuadraticParts.UsedT (I.rec7 l Z) μ → μ ≠ (I.rec7 l Z).what₂.mu0 → (I.rec7 l Z).what₂.places.resChar w ∉ Dx.Qp μ → ∀ x ∈ LT.Nlam (I.rec7 l Z) u w, Formalism.MainNotions.WeilJacquetShalikaLaw.ColGeTw (I.tw l l0 Z) u μ w x (-(((I.rec7 l Z).R.m : ℝ) * EatT (I.rec7 l Z) u w)) := by
  first | exact @GlobalTheory.LvT.Built.TrueCols.row_true | exact GlobalTheory.LvT.Built.TrueCols.row_true | (intros; apply GlobalTheory.LvT.Built.TrueCols.row_true <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ClosingTrueCols

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LvT.Built.TrueCols

theorem closing_true_cols : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ColIn.JetsIn I → GlobalTheory.LvT.WtSign.BaseSigns B → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (Y : DivX (I.rec7 l Z)) (u : (I.rec7 l Z).what₂.Word), Formalism.MainNotions.product_first_zeroth_parts.Conclusion5Sharp (I.rec7 l Z) u ∧ Formalism.L2.G.Adm2InU.TwistedColumnBoundAtT Y (I.tw l l0 Z) u := by
  intro B X I hOk hJ hS l Z l0 Y u
  exact GlobalTheory.T.trueColumns_row_sharp_bounds B X I hOk hJ hS l l0 Z Y u
end GlobalTheory.LvT.Built.TrueCols
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelPrimeColumnValuationsBundlePointsOverColumn

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Fc.Cv NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fc.Cv

theorem row_level_valuations : ∀ (Q : V4.Slot), OverCols Q → ∀ (Bd : BdT) (Lk : LkT Bd), AllBundlePointProperties.LevelPrimeColumnValuationsAtBundlePoints Q Lk := by
  intro Q hQ Bd Lk
  refine Row0.row (H := EvC fun D O => ∀ u, Formalism.MainNotions.product_first_zeroth_parts.Conclusion5Sharp D u ∧ Formalism.L2.G.Adm2InU.TwistedColumnBoundAtT O.X O.ex.tw u)
    (validForConstructedPointClasses_eventuallyWorkingClass (EvP.of_all fun _ K _ β hβ => ?_)) Lk
  refine GlobalTheory.T.property_at_constructedPoints_of_trueColumnsView (fun D O => ∀ u, Formalism.MainNotions.product_first_zeroth_parts.Conclusion5Sharp D u ∧ Formalism.L2.G.Adm2InU.TwistedColumnBoundAtT O.X O.ex.tw u) ?_ K β
    (hQ _ _ _ _ _ hβ)
  intro B f T w Z O nch hv hs _ u
  rw [hv.tw_eq]
  exact GlobalTheory.LvT.Built.TrueCols.closing_true_cols w.I w.ok hv.jets hs w.l Z w.l0 O.X u

end GlobalTheory.Fc.Cv
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelPrimeColumnValuationsBundlePointsOverColumnStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Fc.Cv NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.levelPrimeColumnValuations_bundlePoints_overColumns : ∀ (Q : V4.Slot), OverCols Q → ∀ (Bd : BdT) (Lk : LkT Bd), AllBundlePointProperties.LevelPrimeColumnValuationsAtBundlePoints Q Lk := by
  first | exact @GlobalTheory.Fc.Cv.row_level_valuations | exact GlobalTheory.Fc.Cv.row_level_valuations | (intros; apply GlobalTheory.Fc.Cv.row_level_valuations <;> assumption)
end
end
