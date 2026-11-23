module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EpsVEqOne
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsDblClosed
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatContrIntIndicator
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapBesselToFourierJacobiLocalModel
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapFourierJacobiToBesselLocalModel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapsPreserveSchwartzBruhatAndSurjective
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapsSatisfyFlatLawsFinitePlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaMapsConvergeThetaFunctions
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationTwoVariableModelAndLineExte
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergInvariantFactorsContraction
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineContractionSplitPlaceLocalModel
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SliceColMem
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumLocalModelFormula
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
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
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagGenDiag
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealLineOfPeriodsOnLine
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowBesZeroE
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceDoubleStepFlatContractionExpand

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.DblStepLoc

theorem contr_flat_expand : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), GlobalTheory.SplitWeil.IsUnitVol ν → ∀ (p : GlobalTheory.LocMod.Place D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ψk : AddChar k Circle), p.IsChar ψ ψk → GlobalTheory.SplitWeil.HasConductor ψk 1 → ∀ (σ : ℕ) (B : GlobalTheory.Unf.BesLev D (σ + 1)) (J : GlobalTheory.Unf.JacLev D (σ + 1)) (B' : GlobalTheory.Unf.BesLev D σ) (n₀ : Type) [Fintype n₀] [DecidableEq n₀] (n₁ : Type) [Fintype n₁] [DecidableEq n₁] (n₂ : Type) [Fintype n₂] [DecidableEq n₂] (c : ℕ) (F : GlobalTheory.LocMod.Dbl p B J B' n₀ n₁ n₂ c) (s₁ : GlobalTheory.Unf.StepBF ψ B J) (s₂ : GlobalTheory.Unf.StepFB ψ J B') (l : GlobalTheory.Unf.Link B B'.L B'.ζ) (vL : GlobalTheory.Unf.VolM D B'.L.rank J.W₀.rank) T₁ T₂, p.IsModel ψ F.G₀ F.G₁ T₁ → p.IsModel ψ F.G₁ F.G₂ T₂ → ∀ Φ₁ Φ₂ O₁ O₂, GlobalTheory.LocMod.IsOne O₁ → GlobalTheory.LocMod.IsOne O₂ → ∀ (I : Type) (S : Finset I) (x : I → ℂ) (Ξ₁ : I → GlobalTheory.SplitWeil.SB (Matrix n₁ n₀ k)) (Ξ₂ : I → GlobalTheory.SplitWeil.SB (Matrix n₂ n₁ k)) (c₁ : I → WO B.A J.W₀ →₀ ℂ) (c₂ : I → WO J.W₀ B'.A →₀ ℂ), (∀ i ∈ S, p.IsCombAt ψ F.F₀ F.F₁ (c₁ i) (Ξ₁ i).1 ∧ p.IsCombAt ψ F.F₁ F.F₂ (c₂ i) (Ξ₂ i).1) → (∀ q, GlobalTheory.LocFlat.contr ψk ν (GlobalTheory.LocFlat.flCol ψk ν (σ + 1 + 1) Φ₁.1) (GlobalTheory.LocFlat.flRow ψk ν (σ + 1) Φ₂.1) q = ∑ i ∈ S, x i * ((Ξ₁ i).1 q.1 * (Ξ₂ i).1 q.2)) → GlobalTheory.Unf.contr l J.W₀ vL (GlobalTheory.Unf.flatBF s₁ (T₁ Φ₁)) (GlobalTheory.Unf.flatFB s₂ (T₂ Φ₂)) = ∑ i ∈ S, x i • biComb ψ B.A J.W₀ B'.A (c₁ i) (c₂ i) (GlobalTheory.Unf.contr l J.W₀ vL (GlobalTheory.Unf.flatBF s₁ (T₁ O₁)) (GlobalTheory.Unf.flatFB s₂ (T₂ O₂))) := by
  intro D k _ _ _ _ _ _ ν hν p ψ hstd ψk hchar hcond σ B J B' n₀ _ _ n₁ _ _ n₂ _ _ c F s₁ s₂ l vL T₁ T₂ hT₁ hT₂
    Φ₁ Φ₂ O₁ O₂ hO₁ hO₂ I S x Ξ₁ Ξ₂ c₁ c₂ hcomb hcontr
  have hcσ : c = 2 * σ := by have := F.bes.1; omega
  have hBF := GlobalTheory.FlatBFLoc.flatBF_of_laws D (GlobalTheory.Unf.Flat.flatLaw D) (GlobalTheory.FinPl.flatLaws_all D) (GlobalTheory.LocOm.omLoc D)
  have hFB := GlobalTheory.LocMod.flatFB_holds D (GlobalTheory.Unf.Flat.flatLaw D) (GlobalTheory.FinPl.flatLaws_all D) (GlobalTheory.LocOm.omLoc D)
  have hCL := GlobalTheory.ContrLocProof.contrLoc D GlobalTheory.LocFlat.contrFactor
  have hψc : Continuous ψk := hcond.continuous
  obtain ⟨C₀, hC₀⟩ := GlobalTheory.LocMod.GValProof.core_of_bes p B F.s F.F₀ F.G₀ F.bes
  obtain ⟨C₂, hC₂⟩ := GlobalTheory.LocMod.GValProof.core_of_bes p B' (F.s * p.xi) F.F₂ F.G₂ F.bes'
  have hjac : p.IsJacFrame J F.s (-p.xi ^ 2 * p.hz B') F.F₁ F.G₁ := by
    rw [← GlobalTheory.LocMod.GValProof.hz_link p B B' l]; exact F.jac
  obtain ⟨U₁, hU₁, hU₁e⟩ := hBF k p ν hν.1 ψ ψk hchar (σ + 1) B J s₁ F.s F.s_ne _ _ (c + 1 + 1) F.F₀ C₀ F.G₀ F.F₁ F.G₁
    hC₀ F.bes F.jac T₁ hT₁
  obtain ⟨U₂, hU₂, hU₂e⟩ := hFB k p ν hν.1 ψ ψk hchar σ J B' s₂ F.s F.s_ne _ _ (c + 1) F.F₁ F.G₁ F.F₂ C₂ F.G₂
    hjac hC₂ F.bes' T₂ hT₂
  obtain ⟨Λ, hΛ, hΛe⟩ := hCL k p ν hν.1 ψ hstd ψk hchar (σ + 1) σ B B' l J.W₀ vL F.s F.s_ne _ _ _ F.F₀ C₀ F.F₁ F.F₂ C₂
    hC₀ hC₂ U₁ U₂ hU₁ hU₂
  have hfl := GlobalTheory.LocFlat.flat_SB_onto k ψk ν hψc hν.1
  have m₁ := fun Φ : GlobalTheory.SplitWeil.SB _ =>
    ((hfl n₁ n₀ (c + 1 + 1) (σ + 1 + 1) (by omega)).1 (by omega)).1 Φ.1 Φ.2
  have m₂ := fun Φ : GlobalTheory.SplitWeil.SB _ =>
    ((hfl n₂ n₁ (c + 1) (σ + 1) (by omega)).2 (by omega)).1 Φ.1 Φ.2
  let Ψ₁ : GlobalTheory.SplitWeil.SB _ := ⟨_, m₁ Φ₁⟩
  let Ψ₂ : GlobalTheory.SplitWeil.SB _ := ⟨_, m₂ Φ₂⟩
  let P₁ : GlobalTheory.SplitWeil.SB _ := ⟨_, m₁ O₁⟩
  let P₂ : GlobalTheory.SplitWeil.SB _ := ⟨_, m₂ O₂⟩
  rw [hU₁e Φ₁ Ψ₁ rfl, hU₂e Φ₂ Ψ₂ rfl, hU₁e O₁ P₁ rfl, hU₂e O₂ P₂ rfl]
  obtain ⟨Ξ, hΞ, e1⟩ := hΛe Ψ₁ Ψ₂
  obtain ⟨ΞO, hΞO, e2⟩ := hΛe P₁ P₂
  rw [e1, e2]
  have hun := GlobalTheory.LocFlat.flat_contr_intIndicator k ψk ν hcond hν
  let Q₁ : GlobalTheory.SplitWeil.SB (Matrix n₁ n₀ k) := ⟨_, GlobalTheory.LocMod.GValProof.one_mem_SB _ _⟩
  let Q₂ : GlobalTheory.SplitWeil.SB (Matrix n₂ n₁ k) := ⟨_, GlobalTheory.LocMod.GValProof.one_mem_SB _ _⟩
  have hP₁ : P₁.1 = Set.indicator {x : Matrix n₁ (n₀ ⊕ Unit) k | ∀ r q, x r q ∈ (ValuativeRel.valuation k).integer}
      fun _ => 1 := by
    simp only [P₁]
    rw [hO₁, (hun n₁ n₀ n₀ (c + 1 + 1) (σ + 1 + 1)).1, if_neg (by omega)]
  have hP₂ : P₂.1 = Set.indicator {x : Matrix (n₂ ⊕ Unit) n₁ k | ∀ r q, x r q ∈ (ValuativeRel.valuation k).integer}
      fun _ => 1 := by
    simp only [P₂]
    rw [hO₂, (hun n₂ n₁ n₀ (c + 1) (σ + 1)).2.1 (by omega) (by omega)]
  have hΞO' : ∀ q, ΞO.1 q = Q₁.1 q.1 * Q₂.1 q.2 := by
    intro q
    rw [hΞO, hP₁, hP₂]
    exact (hun n₁ n₀ n₂ 0 0).2.2 q
  let Pr : I → GlobalTheory.SplitWeil.SB (Matrix n₁ n₀ k × Matrix n₂ n₁ k) := fun i => GlobalTheory.LocFlat.CFac.prodSB (Ξ₁ i) (Ξ₂ i)
  have hPr : ∀ i q, (Pr i).1 q = (Ξ₁ i).1 q.1 * (Ξ₂ i).1 q.2 := fun i q => rfl
  have hΞs : Ξ = ∑ i ∈ S, x i • Pr i := by
    apply Subtype.ext
    funext q
    rw [hΞ]
    refine (hcontr q).trans ?_
    rw [Submodule.coe_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, hPr]

  rw [hΞs, map_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [map_smul]
  congr 1
  exact (GlobalTheory.BiComb.comb_bimodel_and_line D k p ψ _ _ _).1 B.A J.W₀ B'.A F.F₀ F.F₁ F.F₂ Λ (c₁ i) (c₂ i) (Ξ₁ i) Q₁ (Ξ₂ i) Q₂
    (Pr i) ΞO hΛ (hcomb i hi).1 (hcomb i hi).2 rfl rfl (hPr i) hΞO'

end GlobalTheory.DblStepLoc
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceDoubleStepFlatContractionExpandStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.splitPlace_doubleStep_flatContraction_expand : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), GlobalTheory.SplitWeil.IsUnitVol ν → ∀ (p : GlobalTheory.LocMod.Place D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ψk : AddChar k Circle), p.IsChar ψ ψk → GlobalTheory.SplitWeil.HasConductor ψk 1 → ∀ (σ : ℕ) (B : GlobalTheory.Unf.BesLev D (σ + 1)) (J : GlobalTheory.Unf.JacLev D (σ + 1)) (B' : GlobalTheory.Unf.BesLev D σ) (n₀ : Type) [Fintype n₀] [DecidableEq n₀] (n₁ : Type) [Fintype n₁] [DecidableEq n₁] (n₂ : Type) [Fintype n₂] [DecidableEq n₂] (c : ℕ) (F : GlobalTheory.LocMod.Dbl p B J B' n₀ n₁ n₂ c) (s₁ : GlobalTheory.Unf.StepBF ψ B J) (s₂ : GlobalTheory.Unf.StepFB ψ J B') (l : GlobalTheory.Unf.Link B B'.L B'.ζ) (vL : GlobalTheory.Unf.VolM D B'.L.rank J.W₀.rank) T₁ T₂, p.IsModel ψ F.G₀ F.G₁ T₁ → p.IsModel ψ F.G₁ F.G₂ T₂ → ∀ Φ₁ Φ₂ O₁ O₂, GlobalTheory.LocMod.IsOne O₁ → GlobalTheory.LocMod.IsOne O₂ → ∀ (I : Type) (S : Finset I) (x : I → ℂ) (Ξ₁ : I → GlobalTheory.SplitWeil.SB (Matrix n₁ n₀ k)) (Ξ₂ : I → GlobalTheory.SplitWeil.SB (Matrix n₂ n₁ k)) (c₁ : I → WO B.A J.W₀ →₀ ℂ) (c₂ : I → WO J.W₀ B'.A →₀ ℂ), (∀ i ∈ S, p.IsCombAt ψ F.F₀ F.F₁ (c₁ i) (Ξ₁ i).1 ∧ p.IsCombAt ψ F.F₁ F.F₂ (c₂ i) (Ξ₂ i).1) → (∀ q, GlobalTheory.LocFlat.contr ψk ν (GlobalTheory.LocFlat.flCol ψk ν (σ + 1 + 1) Φ₁.1) (GlobalTheory.LocFlat.flRow ψk ν (σ + 1) Φ₂.1) q = ∑ i ∈ S, x i * ((Ξ₁ i).1 q.1 * (Ξ₂ i).1 q.2)) → GlobalTheory.Unf.contr l J.W₀ vL (GlobalTheory.Unf.flatBF s₁ (T₁ Φ₁)) (GlobalTheory.Unf.flatFB s₂ (T₂ Φ₂)) = ∑ i ∈ S, x i • biComb ψ B.A J.W₀ B'.A (c₁ i) (c₂ i) (GlobalTheory.Unf.contr l J.W₀ vL (GlobalTheory.Unf.flatBF s₁ (T₁ O₁)) (GlobalTheory.Unf.flatFB s₂ (T₂ O₂))) := by
  first | exact @GlobalTheory.DblStepLoc.contr_flat_expand | exact GlobalTheory.DblStepLoc.contr_flat_expand | (intros; apply GlobalTheory.DblStepLoc.contr_flat_expand <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatDictionaryDoubleStepAtPlace

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

namespace GlobalTheory.FlatPlace

theorem dblP_big : Big fun ch => ChrP ch → ArrP ch → LocP ch → BesP ch → JacP ch → DblP ch := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch _ => ?_⟩⟩
  intro hChr hArr hLoc hBes hJac
  intro t w hw p hp β r r₀ h hpts M hM φ v f hvf j hje hj
  have hstd : IsStdChar D ch.W.ψ (-1) := by rw [hch.weil.ψ]; exact s.std
  obtain ⟨hψ, hcond, -⟩ := hChr t w hw p hp
  have hm := D.R.m_even
  have hj' : j + 2 * ((D.R.m - 4 - j) / 2 + 1) + 2 = D.R.m := by
    obtain ⟨a, ha⟩ := hm; obtain ⟨b, hb⟩ := hje; omega
  have hj2 : j + 1 + 1 + 2 * ((D.R.m - 4 - j) / 2) + 2 = D.R.m := by omega
  have h0 : ¬ j + 2 * 0 + 2 = D.R.m := by omega
  have hL := hLoc t w hw p hp β r r₀ h hpts
  have t0 : topRank (locGrid ch.G t w) j + D.R.m = (locGrid ch.G t w).rank (D.R.m, j) + j + 1 :=
    topRank_add (G := locGrid ch.G t w) one_le_sLen j
  have t1 : topRank (locGrid ch.G t w) (j + 1) + D.R.m = (locGrid ch.G t w).rank (D.R.m, j + 1) + (j + 1) + 1 :=
    topRank_add (G := locGrid ch.G t w) one_le_sLen (j + 1)
  have t2 : topRank (locGrid ch.G t w) (j + 1 + 1) + D.R.m = (locGrid ch.G t w).rank (D.R.m, j + 1 + 1) + (j + 1 + 1) + 1 :=
    topRank_add (G := locGrid ch.G t w) one_le_sLen (j + 1 + 1)
  have hc0 : topRank (locGrid ch.G t w) j + (2 * ((D.R.m - 4 - j) / 2) + 1 + 1 + 1) = (locGrid ch.G t w).rank (D.R.m, j) := by
    omega
  have hc1 : topRank (locGrid ch.G t w) (j + 1) + (2 * ((D.R.m - 4 - j) / 2) + 1 + 1) =
      (locGrid ch.G t w).rank (D.R.m, j + 1) := by
    omega
  have hc2 : topRank (locGrid ch.G t w) (j + 1 + 1) + (2 * ((D.R.m - 4 - j) / 2) + 1) =
      (locGrid ch.G t w).rank (D.R.m, j + 1 + 1) := by
    omega
  have hodd : Odd (j + 1) := hje.add_one
  have hev2 : Even (j + 1 + 1) := hodd.add_one

  obtain ⟨T₁, hT₁, hO₁, Φ₁, hΦ₁, hTΦ₁⟩ := hArr t w hw p hp φ j (by omega) (v ⟨j, by omega⟩) (f ⟨j, by omega⟩)
    (hvf ⟨j, by omega⟩) (epsV ch.G t w) ((repsAt ch.G t w).elt β) (fun X => epsV_mem (G := ch.G) t w X)
    (h j * r₀ j) ((r₀ j)⁻¹ * r j) (h (j + 1) * r₀ (j + 1)) ((r₀ (j + 1))⁻¹ * r (j + 1))
    (hL j (by omega)).1 (hL (j + 1) (by omega)).1
    (Fin (topRank (locGrid ch.G t w) j) ⊕ Fin (2 * ((D.R.m - 4 - j) / 2) + 1 + 1 + 1))
    (Fin (topRank (locGrid ch.G t w) (j + 1)) ⊕ Fin (2 * ((D.R.m - 4 - j) / 2) + 1 + 1)) (frame hc0) (frame hc1)
  obtain ⟨T₂, hT₂, hO₂, Φ₂, hΦ₂, hTΦ₂⟩ := hArr t w hw p hp φ (j + 1) (by omega) (v ⟨j + 1, by omega⟩) (f ⟨j + 1, by omega⟩)
    (hvf ⟨j + 1, by omega⟩) (epsV ch.G t w) ((repsAt ch.G t w).elt β) (fun X => epsV_mem (G := ch.G) t w X)
    (h (j + 1) * r₀ (j + 1)) ((r₀ (j + 1))⁻¹ * r (j + 1)) (h (j + 1 + 1) * r₀ (j + 1 + 1))
    ((r₀ (j + 1 + 1))⁻¹ * r (j + 1 + 1))
    (hL (j + 1) (by omega)).1 (hL (j + 1 + 1) (by omega)).1
    (Fin (topRank (locGrid ch.G t w) (j + 1)) ⊕ Fin (2 * ((D.R.m - 4 - j) / 2) + 1 + 1))
    (Fin (topRank (locGrid ch.G t w) (j + 1 + 1)) ⊕ Fin (2 * ((D.R.m - 4 - j) / 2) + 1)) (frame hc1) (frame hc2)

  have hB0 := hBes t w hw p hp M hM j ((D.R.m - 4 - j) / 2 + 1) hj' (GlobalTheory.Unf.Inhab.nonempty_volN _).some
    (h j * r₀ j) ((hL j (by omega)).2.1 hje) _ hc0
  have hJ1 := hJac t w hw p hp M hM j ((D.R.m - 4 - j) / 2 + 1) hj' (GlobalTheory.Unf.Inhab.nonempty_volN _).some
    (h (j + 1) * r₀ (j + 1)) (Or.inr ((hL (j + 1) (by omega)).2.2 hodd)) _ hc1
  have hB2 := hBes t w hw p hp M hM (j + 1 + 1) ((D.R.m - 4 - j) / 2) hj2 (GlobalTheory.Unf.Inhab.nonempty_volN _).some
    (h (j + 1 + 1) * r₀ (j + 1 + 1)) ((hL (j + 1 + 1) (by omega)).2.1 hev2) _ hc2
  intro I S x Ξ₁ Ξ₂ c₁ c₂ hc
  have hxi := Witness.xi_ne p
  have es : (p.xi ^ ((D.R.m - 4 - j) / 2 + 1))⁻¹ * p.xi = (p.xi ^ ((D.R.m - 4 - j) / 2))⁻¹ := by
    rw [pow_succ, mul_inv, mul_assoc, inv_mul_cancel₀ hxi, mul_one]
  let Fd : GlobalTheory.LocMod.Dbl p (besAt ch.G hM j ((D.R.m - 4 - j) / 2 + 1) hj' (GlobalTheory.Unf.Inhab.nonempty_volN _).some)
      (jacAt ch.G hM (j + 1) ((D.R.m - 4 - j) / 2 + 1) (by omega))
      (besAt ch.G hM (j + 1 + 1) ((D.R.m - 4 - j) / 2) hj2 (GlobalTheory.Unf.Inhab.nonempty_volN _).some)
      (Fin (topRank (locGrid ch.G t w) j)) (Fin (topRank (locGrid ch.G t w) (j + 1)))
      (Fin (topRank (locGrid ch.G t w) (j + 1 + 1))) (2 * ((D.R.m - 4 - j) / 2)) :=
    ⟨_, inv_ne_zero (pow_ne_zero _ hxi), _, _, _, _, _, _, hB0, hJ1, es ▸ hB2⟩

  obtain ⟨O₁, hOne₁, -⟩ := GlobalTheory.LocMod.PinModel.exists_isOne (k := Kw w)
    (Y := Fin (topRank (locGrid ch.G t w) (j + 1)) ⊕ Fin (2 * ((D.R.m - 4 - j) / 2) + 1 + 1))
    (Y' := Fin (topRank (locGrid ch.G t w) j) ⊕ Fin (2 * ((D.R.m - 4 - j) / 2) + 1 + 1 + 1))
  obtain ⟨O₂, hOne₂, -⟩ := GlobalTheory.LocMod.PinModel.exists_isOne (k := Kw w)
    (Y := Fin (topRank (locGrid ch.G t w) (j + 1 + 1)) ⊕ Fin (2 * ((D.R.m - 4 - j) / 2) + 1))
    (Y' := Fin (topRank (locGrid ch.G t w) (j + 1)) ⊕ Fin (2 * ((D.R.m - 4 - j) / 2) + 1 + 1))
  have hv1 : ch.W.om (.mu t D.R.m j) ((h * r₀) j, (h * r₀) (j + 1)) (v ⟨j, by omega⟩) = T₁ O₁ := (hO₁ O₁ hOne₁).symm
  have hv2 : ch.W.om (.mu t D.R.m (j + 1)) ((h * r₀) (j + 1), (h * r₀) (j + 1 + 1)) (v ⟨j + 1, by omega⟩) = T₂ O₂ :=
    (hO₂ O₂ hOne₂).symm
  have hf1 : ch.W.om (.mu t D.R.m j) ((h * r) j, (h * r) (j + 1)) (f ⟨j, by omega⟩) = T₁ Φ₁ := by
    rw [hTΦ₁]; simp only [Pi.mul_apply, mul_assoc, mul_inv_cancel_left]
  have hf2 : ch.W.om (.mu t D.R.m (j + 1)) ((h * r) (j + 1), (h * r) (j + 1 + 1)) (f ⟨j + 1, by omega⟩) = T₂ Φ₂ := by
    rw [hTΦ₂]; simp only [Pi.mul_apply, mul_assoc, mul_inv_cancel_left]
  have E : ∀ (Φ : SchDown ch.G t) (g : Pts ch.G), conAt ch.W hM Φ g j =
      GlobalTheory.Unf.contr (linkAt hM j _ hj' (GlobalTheory.Unf.Inhab.nonempty_volN _).some (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some)
        (ch.G.V (.top (j + 1))) ((GlobalTheory.Unf.Inhab.nonempty_volM D _ _).some)
        (GlobalTheory.Unf.flatBF (B := besAt ch.G hM j _ hj' (GlobalTheory.Unf.Inhab.nonempty_volN _).some)
          (J := jacAt ch.G hM (j + 1) ((D.R.m - 4 - j) / 2 + 1) (by omega))
          (stepAt ch.G ch.W t hM j (by omega) (besDecAt ch.G j _ hj')
            (rowJac ch.G (j + 1) (by omega) ((D.R.m - 4 - j) / 2 + 1) (by omega)))
          (ch.W.om (.mu t D.R.m j) (g j, g (j + 1)) (Φ ⟨j, by omega⟩)))
        (GlobalTheory.Unf.flatFB (J := jacAt ch.G hM (j + 1) ((D.R.m - 4 - j) / 2 + 1) (by omega))
          (B := besAt ch.G hM (j + 1 + 1) ((D.R.m - 4 - j) / 2) (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some)
          (stepAt ch.G ch.W t hM (j + 1) (by omega) (rowJac ch.G (j + 1) (by omega) ((D.R.m - 4 - j) / 2 + 1) (by omega))
            (besDecAt ch.G (j + 1 + 1) ((D.R.m - 4 - j) / 2) (by omega)))
          (ch.W.om (.mu t D.R.m (j + 1)) (g (j + 1), g (j + 1 + 1)) (Φ ⟨j + 1, by omega⟩))) := by
    intro Φ g
    unfold conAt
    rw [dite_eq_right h0]
    exact dif_pos hj'
  rw [E v (h * r₀), E f (h * r)]
  rw [hv1, hv2, hf1, hf2]
  have hz : ∀ (S' : Finset I), (∀ q₁ q₂, ∑ i ∈ S', x i * ((Ξ₁ i).1 q₁ * (Ξ₂ i).1 q₂) = 0) → ∀ q,
      GlobalTheory.LocFlat.contr (psiAt ch.W w) (unitVol w) (GlobalTheory.LocFlat.flCol (psiAt ch.W w) (unitVol w) ((D.R.m - 4 - j) / 2 + 1 + 1)
        (0 : SB (Matrix (Fin (topRank (locGrid ch.G t w) (j + 1)) ⊕ Fin (2 * ((D.R.m - 4 - j) / 2) + 1 + 1))
          (Fin (topRank (locGrid ch.G t w) j) ⊕ Fin (2 * ((D.R.m - 4 - j) / 2) + 1 + 1 + 1)) (Kw w))).1)
        (GlobalTheory.LocFlat.flRow (psiAt ch.W w) (unitVol w) ((D.R.m - 4 - j) / 2 + 1) Φ₂.1) q =
        ∑ i ∈ S', x i * ((Ξ₁ i).1 q.1 * (Ξ₂ i).1 q.2) := by
    intro S' hS' q
    rw [hS' q.1 q.2]
    simp [GlobalTheory.LocFlat.contr, GlobalTheory.LocFlat.flCol, GlobalTheory.RootEx.opE, GlobalTheory.StepData.hat]
  refine ⟨fun hvan => ?_, fun hq => ?_⟩
  · refine Eq.trans (GlobalTheory.T.splitPlace_doubleStep_flatContraction_expand D (Kw w) (unitVol w) (isUnitVol_unitVol w) p ch.W.ψ hstd (psiAt ch.W w) hψ hcond
      ((D.R.m - 4 - j) / 2) _ _ _ _ _ _ _ Fd _ _ _ _ T₁ T₂ hT₁ hT₂ 0 Φ₂ O₁ O₂ hOne₁ hOne₂ I S x Ξ₁ Ξ₂ c₁ c₂ hc (hz S hvan)).symm ?_
    exact (GlobalTheory.T.splitPlace_doubleStep_flatContraction_expand D (Kw w) (unitVol w) (isUnitVol_unitVol w) p ch.W.ψ hstd (psiAt ch.W w) hψ hcond ((D.R.m - 4 - j) / 2)
      _ _ _ _ _ _ _ Fd _ _ _ _ T₁ T₂ hT₁ hT₂ 0 Φ₂ O₁ O₂ hOne₁ hOne₂ I ∅ x Ξ₁ Ξ₂ c₁ c₂ (by simp)
      (hz ∅ fun _ _ => Finset.sum_empty)).trans Finset.sum_empty
  · have hloc : ∀ q, GlobalTheory.LocFlat.contr (psiAt ch.W w) (unitVol w)
        (GlobalTheory.LocFlat.flCol (psiAt ch.W w) (unitVol w) ((D.R.m - 4 - j) / 2 + 1 + 1) Φ₁.1)
        (GlobalTheory.LocFlat.flRow (psiAt ch.W w) (unitVol w) ((D.R.m - 4 - j) / 2 + 1) Φ₂.1) q =
        ∑ i ∈ S, x i * ((Ξ₁ i).1 q.1 * (Ξ₂ i).1 q.2) := by
      intro q
      rw [← hq q, show Φ₁.1 = _ from funext hΦ₁, show Φ₂.1 = _ from funext hΦ₂]
      unfold facAt locA
      rw [dite_eq_right (show ¬ j + 2 * 0 + 2 = (locGrid ch.G t w).m from h0),
        dif_pos (show j + 2 * (((locGrid ch.G t w).m - 4 - j) / 2 + 1) + 2 = (locGrid ch.G t w).m from hj')]
      rfl
    exact GlobalTheory.T.splitPlace_doubleStep_flatContraction_expand D (Kw w) (unitVol w) (isUnitVol_unitVol w) p ch.W.ψ hstd (psiAt ch.W w) hψ hcond ((D.R.m - 4 - j) / 2)
      _ _ _ _ _ _ _ Fd _ _ _ _ T₁ T₂ hT₁ hT₂ Φ₁ Φ₂ O₁ O₂ hOne₁ hOne₂ I S x Ξ₁ Ξ₂ c₁ c₂ hc hloc

end GlobalTheory.FlatPlace
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatDictionaryDoubleStepAtPlaceStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil


theorem _root_.GlobalTheory.T.flatDictionary_doubleStep_at_place : Big fun ch => ChrP ch → ArrP ch → LocP ch → BesP ch → JacP ch → DblP ch := by
  first | exact @GlobalTheory.FlatPlace.dblP_big | exact GlobalTheory.FlatPlace.dblP_big | (intros; apply GlobalTheory.FlatPlace.dblP_big <;> assumption)
end
end
