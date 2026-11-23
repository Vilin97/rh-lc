module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PerRowC
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PairBdNonneg
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdaptedNormalFormNormsMinorsEqLabelProofStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BaseLatticeConstructionHoldsStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DefiniteQuotientModelExistsStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdaptedNormalFormRelevantTermProofStatement
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowsMeanC
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscNResNeZero
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsCMFieldOfStar
public import Formalism.SharpRestriction.CuspSpanNormBounds.KappaEndpoints
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
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsometricEmbeddedDatumPairsEncardIsometrySmulStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ParameterSizeConstraintsStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsStarStableIdealAbsorbingMinors
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RelevantSetZeroGNotIdentity
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowLatticeTermAdaptedNormalFormStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowsMeanBoundOfGenusMeanStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumPairBdMulDatBdLe
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermPairsRowLatticeCountedViaEmbeddingsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermsOverRowCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryHostFieldArithmeticConditionsProofStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeightedTermPairsSumLeViaRowsGenusMeans
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenusMeanEmbeddedPairsLeMassMulPairBound

section

@[expose] public section

open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.RowsConc GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PairsRow

theorem main : GlobalTheory.Mass.MaxMass → Formalism.HermitianLatticesTheory.SiegelMassRatio → HostC → LatticeNormalizationCondition →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Std D large₂ →
    ∀ (W : Submodule D.host.E (VS D).V) (HW : Formalism.HermitianLatticeCounting.S6.HermSpace D.host.E W), GlobalTheory.DegAsm.IsEmb (F0 X u) HW W.subtype →
    Module.finrank D.host.E W = D.R.k → GlobalTheory.Mass.PD HW.B.flip → ∀ Λ ∈ Y.what₂ u, ∀ x x' : ℕ, 1 ≤ x → 1 ≤ x' →
      GlobalTheory.Mass.orbSum (Formalism.HermitianLatticesTheory.isom HW.B.flip) (Formalism.HermitianLatticesTheory.genus HW.B.flip (GlobalTheory.DegAsm.lat0 (F0 X u) W.subtype Λ))
                   (fun L => (((GlobalTheory.DegCnt.Trip HW (gS D) L D.R.rS x x').encard : ℕ∞) : ℝ≥0∞)) ≤
        ENNReal.ofReal (Formalism.HermitianLatticesTheory.mass HW.B.flip (GlobalTheory.DegAsm.lat0 (F0 X u) W.subtype Λ) *
          GlobalTheory.DegAsm.pairBd D.host.E D.R.k (gS D) D.R.rS (Tu D u) x x') := by
  intro hMax hSi hHost hLat D large₂ X Y u hStd W HW hEmb hk hpd Λ hΛ x x' hx hx'
  obtain ⟨hK, -, -, hv1, -, -, -, -, -, -, -, hg, hT⟩ := hHost D large₂ hStd
  have hv : 1 ≤ Formalism.HermitianLatticesTheory.vInv D.host.E := by
    rw [(hHost D large₂ hStd).2.2.1]; exact hv1
  obtain ⟨hTp, hTP⟩ := hT u
  obtain ⟨hI, he⟩ := hLat D large₂ X Y u hStd W HW hEmb Λ hΛ
  have hk3 : 3 ≤ Module.finrank D.host.E W := by
    rw [hk]; have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have : FiniteDimensional D.host.E W := Module.finite_of_finrank_pos (by omega)
  have h := GlobalTheory.DegCnt.PairMean.main Formalism.MainNotions.KappaEndpoints.mk_core hMax hSi D.host.E W HW hK
    (GlobalTheory.OrthoLattice.hasOrtho D.host.E hK) hv hpd hk3 (Tu D u) (GlobalTheory.DegAsm.lat0 (F0 X u) W.subtype Λ) _ hTp hTP hI he rfl
    _ rfl (gS D) D.R.rS x x' _ hg hx hx' rfl
  rw [hk] at h
  refine h.trans (le_of_eq ?_)
  unfold GlobalTheory.DegAsm.pairBd
  simp only [mul_assoc]

end GlobalTheory.PairsRow
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenusMeanEmbeddedPairsLeMassMulPairBoundStatement

section

@[expose] public section

open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.RowsConc GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.genusMean_embeddedPairs_le_mass_mul_pairBound : GlobalTheory.Mass.MaxMass → Formalism.HermitianLatticesTheory.SiegelMassRatio → HostC → LatticeNormalizationCondition →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Std D large₂ →
    ∀ (W : Submodule D.host.E (VS D).V) (HW : Formalism.HermitianLatticeCounting.S6.HermSpace D.host.E W), GlobalTheory.DegAsm.IsEmb (F0 X u) HW W.subtype →
    Module.finrank D.host.E W = D.R.k → GlobalTheory.Mass.PD HW.B.flip → ∀ Λ ∈ Y.what₂ u, ∀ x x' : ℕ, 1 ≤ x → 1 ≤ x' →
      GlobalTheory.Mass.orbSum (Formalism.HermitianLatticesTheory.isom HW.B.flip) (Formalism.HermitianLatticesTheory.genus HW.B.flip (GlobalTheory.DegAsm.lat0 (F0 X u) W.subtype Λ))
                   (fun L => (((GlobalTheory.DegCnt.Trip HW (gS D) L D.R.rS x x').encard : ℕ∞) : ℝ≥0∞)) ≤
        ENNReal.ofReal (Formalism.HermitianLatticesTheory.mass HW.B.flip (GlobalTheory.DegAsm.lat0 (F0 X u) W.subtype Λ) *
          GlobalTheory.DegAsm.pairBd D.host.E D.R.k (gS D) D.R.rS (Tu D u) x x') := by
  first | exact @GlobalTheory.PairsRow.main | exact GlobalTheory.PairsRow.main | (intros; apply GlobalTheory.PairsRow.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelevantTermNormsGeOneAndBounded

section

@[expose] public section

open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.RowsConc GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TypeAsm.PairsLab

theorem norms_of_relevant : ∀ (Cg cb Cw cT CT C0 CH C' Cl : ℝ), 0 ≤ CH → ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X)
    (u : D.what₂.Word), HostC → NFExC → LabC → TermC → Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 →
    ∀ t ∈ relSet Y u, 1 ≤ k2Del D (jT t) (labT t) ∧ 1 ≤ DbL D (jT t) (labT t) ∧
      k2Del D (jT t) (labT t) ≤ Hb large₂.sc.b (2 * (CH + 1)) D.R.m D.R.f * k2S D (H1C large₂ CH) (jT t) (labT t) ^ 2 ∧
      DbL D (jT t) (labT t) ≤ (Hb large₂.sc.b (2 * (CH + 1)) D.R.m D.R.f * k2S D (H1C large₂ CH) (jT t) (labT t) ^ 2) ^ D.R.rS := by
  intro Cg cb Cw cT CT C0 CH C' Cl hCH D large₂ X Y u hHost hNF hLab hTerm hH t ht
  have hS : Std D large₂ := ⟨C', Cl, Cg, cb, Cw, cT, CT, C0, hH⟩
  obtain ⟨hK, -, -, -, -, -, -, -, -, -, -, hg, -⟩ := hHost D large₂ hS
  obtain ⟨N, hN, hNj, hNT⟩ := hNF D large₂ X Y u hS t ht
  have hT : N.IsTerm (gS D) t.lam := hTerm D large₂ X Y u hS t N hN
  obtain ⟨-, -, hDel, hDb, -⟩ := hLab D large₂ X Y u hS t N hN
  obtain ⟨𝔠, -, hDb1, hDel1, -⟩ := GlobalTheory.DegCnt.Absorb.exists_absorbing_ideal D.host.E (VS D).V (HV D) hK D.R.rS N (gS D)
    t.lam (by omega) hT
  have hPF : PFHost D := PFHost_of_data D hH.1.2.1
  have hC : 2 * (CH + 1) ≤ 2 * (CH + 1) := le_rfl
  have hup := (delta_pos_le_height_sq hPF large₂ hCH hC t ht).2
  have hb := two_le_scale_b D large₂
  have hHb : (1 : ℝ) ≤ Hb large₂.sc.b (2 * (CH + 1)) D.R.m D.R.f := by
    unfold Hb
    exact Real.one_le_rpow (by linarith) (by positivity)
  have hS1 := one_le_sigma_product (D := D) (H1C large₂ CH) (jT t) (labT t)
  have hA : (1 : ℝ) ≤ Hb large₂.sc.b (2 * (CH + 1)) D.R.m D.R.f * k2S D (H1C large₂ CH) (jT t) (labT t) ^ 2 :=
    one_le_mul_of_one_le_of_one_le hHb (one_le_pow₀ hS1)
  refine ⟨hDel ▸ hDel1, hDb ▸ hDb1, hup, ?_⟩
  have hcard : (k2ends D (jT t) (labT t)).card ≤ D.R.rS := by
    unfold k2ends
    refine (Finset.card_filter_le _ _).trans ?_
    rw [Nat.card_Icc]
    unfold jT
    omega
  calc DbL D (jT t) (labT t)
      ≤ ∏ _l ∈ k2ends D (jT t) (labT t),
          Hb large₂.sc.b (2 * (CH + 1)) D.R.m D.R.f * k2S D (H1C large₂ CH) (jT t) (labT t) ^ 2 := by
        unfold DbL
        refine Finset.prod_le_prod₀ (fun l _ => ?_) (fun l hl => localNorm_le_height_sq hPF large₂ hCH hC t l hl)
        unfold Nloc
        exact_mod_cast FractionalIdeal.absNorm_nonneg _
    _ = _ ^ (k2ends D (jT t) (labT t)).card := Finset.prod_const _
    _ ≤ _ := pow_le_pow_right₀ hA hcard

end GlobalTheory.TypeAsm.PairsLab
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelevantTermNormsGeOneAndBoundedStatement

section

@[expose] public section

open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.RowsConc GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.relevantTerm_norms_ge_one_and_bounded : ∀ (Cg cb Cw cT CT C0 CH C' Cl : ℝ), 0 ≤ CH → ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X)
    (u : D.what₂.Word), HostC → NFExC → LabC → TermC → Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 →
    ∀ t ∈ relSet Y u, 1 ≤ k2Del D (jT t) (labT t) ∧ 1 ≤ DbL D (jT t) (labT t) ∧
      k2Del D (jT t) (labT t) ≤ Hb large₂.sc.b (2 * (CH + 1)) D.R.m D.R.f * k2S D (H1C large₂ CH) (jT t) (labT t) ^ 2 ∧
      DbL D (jT t) (labT t) ≤ (Hb large₂.sc.b (2 * (CH + 1)) D.R.m D.R.f * k2S D (H1C large₂ CH) (jT t) (labT t) ^ 2) ^ D.R.rS := by
  first | exact @GlobalTheory.TypeAsm.PairsLab.norms_of_relevant | exact GlobalTheory.TypeAsm.PairsLab.norms_of_relevant | (intros; apply GlobalTheory.TypeAsm.PairsLab.norms_of_relevant <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeightedTermPairsSumLeViaRowsGenusMeansStatement

section

@[expose] public section

open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.RowsConc GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.weightedTermPairs_sum_le_via_rows_genusMeans : ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Std D large₂ → CompatC → PerRowC →
    RowsMeanC → ∀ (W : Submodule D.host.E (VS D).V) (HW : Formalism.HermitianLatticeCounting.S6.HermSpace D.host.E W),
    GlobalTheory.DegAsm.IsEmb (F0 X u) HW W.subtype →
    (∀ (s : Formalism.HermitianLatticesTheory.isom HW.B.flip) (M : Submodule (𝓞 D.host.E) W) (x x' : ℕ),
      (GlobalTheory.DegCnt.Trip HW (gS D) (s • M) D.R.rS x x').encard = (GlobalTheory.DegCnt.Trip HW (gS D) M D.R.rS x x').encard) →
    ∀ B : ℕ → ℕ → ℝ, (∀ x x', 0 ≤ B x x') →
    (∀ Λ ∈ Y.what₂ u, ∀ x x' : ℕ, 1 ≤ x → 1 ≤ x' →
      GlobalTheory.Mass.orbSum (Formalism.HermitianLatticesTheory.isom HW.B.flip) (Formalism.HermitianLatticesTheory.genus HW.B.flip (GlobalTheory.DegAsm.lat0 (F0 X u) W.subtype Λ))
                   (fun L => (((GlobalTheory.DegCnt.Trip HW (gS D) L D.R.rS x x').encard : ℕ∞) : ℝ≥0∞)) ≤
        ENNReal.ofReal (Formalism.HermitianLatticesTheory.mass HW.B.flip (GlobalTheory.DegAsm.lat0 (F0 X u) W.subtype Λ) * B x x')) →
    ∀ (j' j'' : ℕ) (δ' δ'' : ℕ → D.host.E) (S : Finset (GTu Y u × GTu Y u)),
    (∀ p ∈ S, p ∈ (Y.tO u u).allPairs (relSet Y u) ∧ jT p.1 = j' ∧ jT p.2 = j'' ∧ labT p.1 = δ' ∧ labT p.2 = δ'') →
    ENNReal.ofReal (∑ p ∈ S, (Formalism.L2.SG.TermOp.wt p.1 * Formalism.L2.SG.TermOp.wt p.2) * (omT p.1 * omT p.2)) ≤
      ∑ x ∈ Finset.Icc 1 ⌊k2Del D j' δ'⌋₊, ∑ x' ∈ Finset.Icc 1 ⌊k2Del D j'' δ''⌋₊,
        ENNReal.ofReal (GlobalTheory.DegAsm.datBd D.host.E D.R.k D.R.rS (k2Del D j' δ') (DbL D j' δ') (NT D u) x *
          GlobalTheory.DegAsm.datBd D.host.E D.R.k D.R.rS (k2Del D j'' δ'') (DbL D j'' δ'') (NT D u) x') *
        ENNReal.ofReal (massC Y u * B x x') := by
  first | exact @GlobalTheory.TypeAsm.PairsSum.pairs_sum_le | exact GlobalTheory.TypeAsm.PairsSum.pairs_sum_le | (intros; apply GlobalTheory.TypeAsm.PairsSum.pairs_sum_le <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermPairCountBoundOfSiegelMassRatios

section

@[expose] public section

noncomputable section
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.RowsConc
namespace GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace PairsPf

theorem massC_nonneg {D : D7} {X : HidaSetting D} (Y : Full X) (u : D.what₂.Word) : 0 ≤ massC Y u := by
  show 0 ≤ ∑ Λ ∈ Y.what₂ u, wRow D (X.Fu u) Λ
  exact Finset.sum_nonneg fun Λ _ => inv_nonneg.mpr (Nat.cast_nonneg _)

theorem datBd_nonneg (K : Type) [Field K] [NumberField K] [StarRing K] (k r : ℕ) (Del Db NT x : ℝ) (hD : 0 ≤ Del)
    (hDb : 0 ≤ Db) (hN : 0 ≤ NT) (hx : 0 ≤ x) : 0 ≤ GlobalTheory.DegAsm.datBd K k r Del Db NT x := by
  unfold GlobalTheory.DegAsm.datBd
  positivity

theorem termPairBoundFactor_nonneg {D : D7} (large₂ : SizeData₂ D) (CH Ch Cp : ℝ) (j : ℕ) (δ : ℕ → D.host.E) : 0 ≤ k2e large₂ CH Ch Cp j δ := by
  have hb : 0 < large₂.sc.b := Real.exp_pos _
  have h1 : 0 ≤ k2Del D j δ := Rat.cast_nonneg.mpr (FractionalIdeal.absNorm_nonneg _)
  have h2 : 0 ≤ Hb large₂.sc.b Ch D.R.m D.R.f := Real.rpow_nonneg hb.le _
  have h3 : 0 ≤ k2S D (H1C large₂ CH) j δ := by
    unfold k2S k2sg
    exact Finset.prod_nonneg fun τ _ => le_trans zero_le_one ((Finset.le_fold_max 1).2 (Or.inl le_rfl))
  unfold k2e
  exact mul_nonneg (mul_nonneg (Real.rpow_nonneg h1 _) (Real.rpow_nonneg h2 _)) (Real.rpow_nonneg h3 _)
private lemma le_mul_sum_sum_of_ofReal_le_ennreal_sum (s s' : Finset ℕ) (f P : ℕ → ℕ → ℝ) (c L : ℝ) (hf : ∀ x x', 0 ≤ f x x')
    (hP : ∀ x x', 0 ≤ P x x') (hc : 0 ≤ c)
    (h : ENNReal.ofReal L ≤ ∑ x ∈ s, ∑ x' ∈ s', ENNReal.ofReal (f x x') * ENNReal.ofReal (c * P x x')) :
    L ≤ c * ∑ x ∈ s, ∑ x' ∈ s', P x x' * f x x' := by
  have hnn : ∀ x x', 0 ≤ f x x' * (c * P x x') := fun x x' => mul_nonneg (hf x x') (mul_nonneg hc (hP x x'))
  have e : ∑ x ∈ s, ∑ x' ∈ s', ENNReal.ofReal (f x x') * ENNReal.ofReal (c * P x x') =
      ENNReal.ofReal (∑ x ∈ s, ∑ x' ∈ s', f x x' * (c * P x x')) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun x _ => Finset.sum_nonneg fun x' _ => hnn x x')]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [ENNReal.ofReal_sum_of_nonneg (fun x' _ => hnn x x')]
    refine Finset.sum_congr rfl fun x' _ => ?_
    rw [ENNReal.ofReal_mul (hf x x')]
  rw [e] at h
  have h' := (ENNReal.ofReal_le_ofReal_iff (Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun x' _ => hnn x x')).1 h
  refine le_trans h' (le_of_eq ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x' _ => ?_
  ring

end PairsPf

open PairsPf in
theorem pair_count_bound_of_siegel_mass : GlobalTheory.Mass.MaxMass → Formalism.HermitianLatticesTheory.SiegelMassRatio → PairsP := by
  intro hMM hSR
  unfold PairsP
  intro Cg cb Cw cT CT C0 CH hCH

  obtain ⟨Ca, hCa1, hCaH, hCaT⟩ : ∃ Ca : ℝ, 1 ≤ Ca ∧ 2 * (CH + 1) ≤ Ca ∧ CT ≤ Ca :=
    ⟨max 1 (max (2 * (CH + 1)) CT), le_max_left _ _, le_trans (le_max_left _ _) (le_max_right _ _),
      le_trans (le_max_right _ _) (le_max_right _ _)⟩
  obtain ⟨Ch, Cl', hCh, hsum⟩ := GlobalTheory.DegAsm.sum_pairBd_mul_datBd_le Ca hCa1
  refine ⟨Ch, 16, hCh, by norm_num, 1, max 1 Cl', ?_⟩
  intro C' Cl hC' hCl D large₂ X Y u hK2 _
  have hStd : GlobalTheory.TypeAsm.Std D large₂ :=
    show ∃ C' Cl Cg cb Cw cT CT C0 : ℝ, Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 from
      ⟨C', Cl, Cg, cb, Cw, cT, CT, C0, hK2⟩
  have hHost : HostC := GlobalTheory.T.unitaryHostFieldArithmeticConditions
  have hfD : Formalism.HermitianLatticesTheory.fDeg D.host.E = D.R.f := (hHost D large₂ hStd).2.2.2.2.1
  have hCl1 : 1 ≤ Cl := le_trans (le_max_left _ _) hCl
  have hClCl : Cl' ≤ Cl := le_trans (le_max_right _ _) hCl
  obtain ⟨hrk, hm, hClm, hm4, hm5, hClk, hlog, hb2, hv1, hvb, hg, hTu⟩ :=
    GlobalTheory.T.parameter_size_constraints Ca Cg cb Cw cT CT C0 C' Cl D large₂ hHost hK2 hC' hCl1 hCaT
  have hlb : 0 ≤ (D.R.m : ℝ) ^ 2 * Real.log large₂.sc.b := mul_nonneg (by positivity) (Real.log_nonneg (by linarith))
  have hClm' : Cl' ≤ (D.R.m : ℝ) := le_trans hClCl hClm
  have hClk' : Cl' * ((D.R.m : ℝ) ^ 2 * Real.log large₂.sc.b) ≤ D.R.k :=
    le_trans (mul_le_mul_of_nonneg_right hClCl hlb) hClk

  have hHb : Hb large₂.sc.b (2 * (CH + 1)) D.R.m D.R.f ≤
      large₂.sc.b ^ (Ca * (D.R.m : ℝ) ^ 2 * Formalism.HermitianLatticesTheory.fDeg D.host.E) := by
    show large₂.sc.b ^ (2 * (CH + 1) * (D.R.m : ℝ) ^ 2 * D.R.f) ≤ _
    rw [hfD]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by gcongr)
  have hHb0 : 0 ≤ Hb large₂.sc.b (2 * (CH + 1)) D.R.m D.R.f := Real.rpow_nonneg (by linarith) _
  have hNT : NT D u = ((Tu D u : ℕ) : ℝ) ^ Formalism.HermitianLatticesTheory.fDeg D.host.E := by
    rw [hfD]
    rfl
  have hNT0 : 0 ≤ NT D u := by
    rw [hNT]
    positivity
  have hk2e : ∀ (j : ℕ) (δ : ℕ → D.host.E), k2e large₂ CH Ch 16 j δ =
      k2Del D j δ ^ ((D.R.k : ℝ) / 2) * (large₂.sc.b ^ (Ch * (D.R.m : ℝ) ^ 2 * Formalism.HermitianLatticesTheory.fDeg D.host.E)) ^ (Ch * (D.R.rS : ℝ) ^ 4) *
        k2S D (H1C large₂ CH) j δ ^ (16 * (D.R.k : ℝ)) := by
    intro j δ
    rw [hfD]
    rfl
  unfold PairsAt
  intro j' _ j'' _ δ' δ'' S hS
  rcases S.eq_empty_or_nonempty with rfl | ⟨p, hp⟩
  · rw [Finset.sum_empty]
    exact mul_nonneg (massC_nonneg Y u) (mul_nonneg (termPairBoundFactor_nonneg large₂ CH Ch 16 j' δ') (termPairBoundFactor_nonneg large₂ CH Ch 16 j'' δ''))
  obtain ⟨hpp, hj1, hj2, hl1, hl2⟩ := hS p hp
  obtain ⟨hr1, hr2, -⟩ := hpp
  have hF := GlobalTheory.T.relevantTerm_norms_ge_one_and_bounded Cg cb Cw cT CT C0 CH C' Cl hCH D large₂ X Y u hHost GlobalTheory.T.exists_adaptedNormalForm_relevantTerm GlobalTheory.T.adaptedNormalForm_normsMinors_eq_label GlobalTheory.T.rowLattice_term_adaptedNormalForm hK2
  obtain ⟨hD1, hDb1, hDle, hDble⟩ := hF p.1 hr1
  obtain ⟨hD1', hDb1', hDle', hDble'⟩ := hF p.2 hr2
  rw [hj1, hl1] at hD1 hDb1 hDle hDble
  rw [hj2, hl2] at hD1' hDb1' hDle' hDble'
  have hS1 : 1 ≤ k2S D (H1C large₂ CH) j' δ' := by
    unfold k2S k2sg
    exact Finset.prod_induction _ (fun x : ℝ => 1 ≤ x) (fun a b ha hb => one_le_mul_of_one_le_of_one_le ha hb) le_rfl
      (fun τ _ => (Finset.le_fold_max 1).2 (Or.inl le_rfl))
  have hS1' : 1 ≤ k2S D (H1C large₂ CH) j'' δ'' := by
    unfold k2S k2sg
    exact Finset.prod_induction _ (fun x : ℝ => 1 ≤ x) (fun a b ha hb => one_le_mul_of_one_le_of_one_le ha hb) le_rfl
      (fun τ _ => (Finset.le_fold_max 1).2 (Or.inl le_rfl))

  have hDA := le_trans hDle (mul_le_mul_of_nonneg_right hHb (sq_nonneg _))
  have hDA' := le_trans hDle' (mul_le_mul_of_nonneg_right hHb (sq_nonneg _))
  have hDbA := le_trans hDble (pow_le_pow_left₀ (mul_nonneg hHb0 (sq_nonneg _)) (mul_le_mul_of_nonneg_right hHb (sq_nonneg _)) _)
  have hDbA' := le_trans hDble' (pow_le_pow_left₀ (mul_nonneg hHb0 (sq_nonneg _)) (mul_le_mul_of_nonneg_right hHb (sq_nonneg _)) _)
  have hbound := hsum D.host.E D.R.k D.R.rS D.R.m (gS D) (Tu D u) large₂.sc.b (k2Del D j' δ') (k2Del D j'' δ'')
    (DbL D j' δ') (DbL D j'' δ'') (k2S D (H1C large₂ CH) j' δ') (k2S D (H1C large₂ CH) j'' δ'') hrk hm hClm' hm4 hm5 hClk'
    hlog hb2 hv1 hvb hg (hTu u).1 (hTu u).2 hS1 hS1' hD1 hD1' hDb1 hDb1' hDA hDA' hDbA hDbA'

  obtain ⟨W, HW, hemb, hrkW, hPD⟩ := GlobalTheory.T.definite_quotient_model_exists D large₂ X u hStd
  have hI := GlobalTheory.T.weightedTermPairs_sum_le_via_rows_genusMeans D large₂ X Y u hStd GlobalTheory.T.termsOverRow_compatible GlobalTheory.T.termPairs_rowLattice_counted_via_embeddings GlobalTheory.T.rowsMeanC_holds W HW hemb
    (fun s M x x' => GlobalTheory.T.isometricEmbeddedDatumPairs_encard_isometry_smul _ _ HW (gS D) D.R.rS x x' s M)
    (fun x x' => GlobalTheory.DegAsm.pairBd D.host.E D.R.k (gS D) D.R.rS (Tu D u) x x')
    (fun x x' => GlobalTheory.DegAsm.pairBd_nonneg _ _ _ _ _ _ _)
    (fun Λ hΛ x x' hx hx' => GlobalTheory.T.genusMean_embeddedPairs_le_mass_mul_pairBound hMM hSR hHost GlobalTheory.T.base_lattice_construction_holds D large₂ X Y u hStd W HW hemb hrkW hPD Λ hΛ x x' hx hx')
    j' j'' δ' δ'' S hS
  rw [hNT] at hI
  have hstep := le_mul_sum_sum_of_ofReal_le_ennreal_sum _ _
    (fun x x' => GlobalTheory.DegAsm.datBd D.host.E D.R.k D.R.rS (k2Del D j' δ') (DbL D j' δ')
        (((Tu D u : ℕ) : ℝ) ^ Formalism.HermitianLatticesTheory.fDeg D.host.E) x *
      GlobalTheory.DegAsm.datBd D.host.E D.R.k D.R.rS (k2Del D j'' δ'') (DbL D j'' δ'')
        (((Tu D u : ℕ) : ℝ) ^ Formalism.HermitianLatticesTheory.fDeg D.host.E) x')
    (fun x x' => GlobalTheory.DegAsm.pairBd D.host.E D.R.k (gS D) D.R.rS (Tu D u) x x') (massC Y u) _
    (fun x x' => mul_nonneg (datBd_nonneg _ _ _ _ _ _ _ (by linarith) (by linarith) (by positivity) (Nat.cast_nonneg _))
      (datBd_nonneg _ _ _ _ _ _ _ (by linarith) (by linarith) (by positivity) (Nat.cast_nonneg _)))
    (fun x x' => GlobalTheory.DegAsm.pairBd_nonneg _ _ _ _ _ _ _) (massC_nonneg Y u) hI
  refine le_trans hstep ?_
  rw [hk2e, hk2e]
  exact mul_le_mul_of_nonneg_left hbound (massC_nonneg Y u)

end GlobalTheory.TypeAsm
end
end
end
