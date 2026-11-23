module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EpsVEqOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIsModelChg
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntIndFromCols
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.T2SpaceMatrixOfIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationTwoVariableModelAndLineExte
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceDoubleStepKernelLocalModels
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagGenDiag
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealLineOfPeriodsOnLine
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowBesZeroE
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastTwoStepsLocalModelExtendByZeroTopStepStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastTwoStepsLocalModelFlatMapFourierJacobiStepStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastTwoStepsTopVertexFrameAtPlaceStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TopOrthAtEmb
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastBiExpand

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open ValuativeRel GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod in

theorem GlobalTheory.LastSeeSawGen.lastBi_expand : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), GlobalTheory.SplitWeil.IsUnitVol ν → ∀ (p : GlobalTheory.LocMod.Place D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ψk : AddChar k Circle), p.IsChar ψ ψk → GlobalTheory.SplitWeil.HasConductor ψk 1 → ∀ (ρ : ℕ) (B : GlobalTheory.Unf.BesLev D ρ) (W X T L'' : HSp D) (o'' : OrthDec X T L'') (τ : Matrix (Fin B.L.rank) (Fin L''.rank) D.host.E), L''.rank = 1 → τᴴ * (B.L.gram * τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram → ∀ (a : k) (z₀ : Fin L''.rank → k), a ≠ 0 → τ.map p.pr *ᵥ z₀ = (-(p.xi * a)) • (fun i => p.pr (B.ζ i)) → ∀ (n : Type) [Fintype n] [DecidableEq n] (n' : Type) [Fintype n'] [DecidableEq n'] (Z : Type) [Fintype Z] [DecidableEq Z] (FA : GlobalTheory.LocMod.Frame k B.A.rank n') (F₀ : GlobalTheory.LocMod.Frame k B.V₀.rank (n' ⊕ Unit)) (FS : GlobalTheory.LocMod.Frame k W.rank n) (FT : GlobalTheory.LocMod.Frame k T.rank Z) (FX : GlobalTheory.LocMod.Frame k X.rank (Z ⊕ Unit)), p.IsCoreFrame B a FA F₀ → FX.β = fromCols (o''.iA.map p.pr * FT.β) (Matrix.of fun r _ => (o''.iB.map p.pr *ᵥ z₀) r) → ∀ T₁ T₂, p.IsModel ψ F₀ FS T₁ → p.IsModel ψ FS FT T₂ → ∀ Φ₁ Φ₂ O₁ O₂, GlobalTheory.LocMod.IsOne O₁ → GlobalTheory.LocMod.IsOne O₂ → ∀ (I : Type) (S : Finset I) (x : I → ℂ) (Ξ₁ : I → GlobalTheory.SplitWeil.SB (Matrix n n' k)) (Ξ₂ : I → GlobalTheory.SplitWeil.SB (Matrix (Z ⊕ Unit) n k)) (c₁ : I → WO B.A W →₀ ℂ) (c₂ : I → WO W X →₀ ℂ), (∀ i ∈ S, p.IsCombAt ψ FA FS (c₁ i) (Ξ₁ i).1 ∧ p.IsCombAt ψ FS FX (c₂ i) (Ξ₂ i).1) → (∀ (y : Matrix n n' k) (y' : Matrix (Z ⊕ Unit) n k), Φ₂.1 y'.toRows₁ * GlobalTheory.StepData.hat ψk ν (-1) (fun u => Φ₁.1 (fromCols y (Matrix.of fun r _ => u r))) (y' (Sum.inr ())) = ∑ i ∈ S, x i * ((Ξ₁ i).1 y * (Ξ₂ i).1 y')) → GlobalTheory.FinPl.lastBi B.o o'' τ (T₁ Φ₁) (T₂ Φ₂) = ∑ i ∈ S, x i • biComb ψ B.A W X (c₁ i) (c₂ i) (GlobalTheory.FinPl.lastBi B.o o'' τ (T₁ O₁) (T₂ O₂)) := by
  classical
  intro D k _ _ _ _ _ _ ν hν p ψ hstd ψk hchar hcond ρ B W X T L'' o'' τ hL hτ a z₀ ha hz n _ _ n' _ _ Z _ _
    FA F₀ FS FT FX hcore hFX T₁ T₂ hT₁ hT₂ Φ₁ Φ₂ O₁ O₂ hO₁ hO₂ I S x Ξ₁ Ξ₂ c₁ c₂ hc hrel
  have := hν.1
  obtain ⟨Λ, hΛ, hK⟩ := GlobalTheory.LastKerLoc.lastLoc D k p ν hν.1 ψ hstd ψk hchar ρ B W X T L'' o'' τ hL hτ a z₀ ha hz
    n n' Z FA F₀ FS FT FX hcore hFX T₁ T₂ hT₁ hT₂
  obtain ⟨Ξ, hΞ, hΞK⟩ := hK Φ₁ Φ₂
  obtain ⟨Ξ', hΞ', hΞ'K⟩ := hK O₁ O₂
  have hv1 : valuation k (-1 : k) = 1 := by simp
  haveI : T2Space (Matrix n n' k) := GlobalTheory.FinPl.Comm.t2Space_matrix_of_isNonarchimedeanLocalField
  haveI : T2Space (Matrix (Z ⊕ Unit) n k) := GlobalTheory.FinPl.Comm.t2Space_matrix_of_isNonarchimedeanLocalField
  let P : I → SB (Matrix n n' k × Matrix (Z ⊕ Unit) n k) := fun i =>
    ⟨fun q => (Ξ₁ i).1 q.1 * (Ξ₂ i).1 q.2,
      GlobalTheory.FinPl.Comm.prod_mem_SB (Ξ₁ i).2 (Ξ₂ i).2 continuous_fst continuous_snd continuous_id fun _ => rfl⟩
  let O₁' : SB (Matrix n n' k) := ⟨_, GlobalTheory.LastTwoSteps.intInd_mem_SB _ _⟩
  let O₂' : SB (Matrix (Z ⊕ Unit) n k) := ⟨_, GlobalTheory.LastTwoSteps.intInd_mem_SB _ _⟩
  have hone : ∀ q, Ξ'.1 q = O₁'.1 q.1 * O₂'.1 q.2 := fun q => by
    rw [hΞ' q, hO₂]
    have e : (fun y => O₁.1 (fromCols q.1 (Matrix.of fun r _ => y r))) = fun y =>
        Set.indicator {x : Matrix n n' k | ∀ r q, x r q ∈ 𝒪[k]}
          (fun _ => (1 : ℂ)) q.1 * cosetInd (box _ (1 : kˣ)) (Submodule.Quotient.mk 0) y := by
      funext y
      rw [hO₁]
      exact GlobalTheory.LastTwoSteps.intInd_fromCols q.1 y
    rw [e, GlobalTheory.LastTwoSteps.hat_const_mul, GlobalTheory.LastTwoSteps.hat_int hcond hν hv1]
    simp only [O₁', O₂']
    rw [GlobalTheory.LastTwoSteps.intInd_rows q.2]
    ring
  have hsum : Ξ = ∑ i ∈ S, x i • P i := by
    apply Subtype.ext
    funext q
    rw [hΞ q, hrel q.1 q.2, Submodule.coe_sum, Finset.sum_apply]
    rfl
  have key : ∀ i ∈ S, Λ (P i) = biComb ψ B.A W X (c₁ i) (c₂ i) (Λ Ξ') := fun i hi =>
    (GlobalTheory.BiComb.comb_bimodel_and_line D k p ψ n n' (Z ⊕ Unit)).1 B.A W X FA FS FX Λ (c₁ i) (c₂ i) (Ξ₁ i) O₁'
      (Ξ₂ i) O₂' (P i) Ξ' hΛ (hc i hi).1 (hc i hi).2 rfl rfl (fun _ => rfl) hone
  have e1 : GlobalTheory.FinPl.lastBi B.o o'' τ (T₁ Φ₁) (T₂ Φ₂) = Λ Ξ := funext fun u => hΞK u
  have e2 : GlobalTheory.FinPl.lastBi B.o o'' τ (T₁ O₁) (T₂ O₂) = Λ Ξ' := funext fun u => hΞ'K u

  rw [e1, e2, hsum, map_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [map_smul, key i hi]
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatDictionaryLastTwoStepsAtPlace

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

noncomputable section

namespace GlobalTheory.LastPlace

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}


open ValuativeRel in
theorem combAt_renumber {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) {S T' : HSp D} {Y Y' Z : Type} [Fintype Y] [DecidableEq Y] [Fintype Y']
    [DecidableEq Y'] [Fintype Z] [DecidableEq Z] (FS : Frame k S.rank Y') (F : Frame k T'.rank Y) (FX : Frame k T'.rank Z)
    (e : Z ≃ Y) (he : ∀ r z, FX.β r z = F.β r (e z)) (c : WO S T' →₀ ℂ) (Ξ : Matrix Y Y' k → ℂ) :
    p.IsCombAt ψ FS F c Ξ → p.IsCombAt ψ FS FX c (fun x => Ξ (x.submatrix e.symm id)) := by
  rintro ⟨hsupp, hc⟩
  refine ⟨hsupp, fun Tm hTm Φ₀ Φ hΦ₀ hΦ => ?_⟩
  haveI : T2Space (Matrix Y Y' k) := GlobalTheory.FinPl.Comm.t2Space_matrix_of_isNonarchimedeanLocalField
  have hc1 : Continuous fun y : Matrix Y Y' k => y.submatrix e id :=
    continuous_pi fun a => continuous_pi fun b => (continuous_apply b).comp (continuous_apply (e a))
  have hc2 : Continuous fun x : Matrix Z Y' k => x.submatrix e.symm id :=
    continuous_pi fun a => continuous_pi fun b => (continuous_apply b).comp (continuous_apply (e.symm a))
  let re : SB (Matrix Z Y' k) → SB (Matrix Y Y' k) := fun Ψ =>
    ⟨fun y => Ψ.1 (y.submatrix e id), GlobalTheory.FinPl.Comm.comp_mem_SB Ψ.2 hc1 hc2 (fun y => by ext a b; simp)⟩
  obtain ⟨Tm', hTm', hchg⟩ := GlobalTheory.LocMod.Place.exists_isModel_chg D k p Z Y' S T' FS FX Y Y' FS F ψ Tm hTm
  have hP : F.γ * FX.β = (F.γ * F.β).submatrix id e := by
    ext y z
    simp only [Matrix.mul_apply, Matrix.submatrix_apply, id, he]
  have hre : ∀ (Ψ : SB (Matrix Z Y' k)), Tm' (re Ψ) = Tm Ψ := fun Ψ => hchg Ψ (re Ψ) fun x => by
    change Ψ.1 x = Ψ.1 ((F.γ * FX.β * x * (FS.γ * FS.β)).submatrix e id)
    have hx : (F.γ * FX.β * x * (FS.γ * FS.β)).submatrix e id = x := by
      rw [hP, F.γβ, FS.γβ, Matrix.mul_one]
      funext a b
      simp [Matrix.mul_apply, Matrix.one_apply]
    rw [hx]
  have h1 : IsOne (re Φ₀) := by
    unfold IsOne
    funext y
    change Φ₀.1 (y.submatrix e id) = _
    rw [hΦ₀]
    by_cases hy : ∀ r q, y r q ∈ 𝒪[k]
    · rw [Set.indicator_of_mem (show y ∈ {x : Matrix Y Y' k | ∀ r q, x r q ∈ 𝒪[k]} from hy), Set.indicator_of_mem (show y.submatrix e id ∈ {x : Matrix Z Y' k | ∀ r q, x r q ∈ 𝒪[k]} from
        fun r q => hy (e r) q)]
    · rw [Set.indicator_of_notMem (show y ∉ {x : Matrix Y Y' k | ∀ r q, x r q ∈ 𝒪[k]} from hy), Set.indicator_of_notMem (show y.submatrix e id ∉ {x : Matrix Z Y' k | ∀ r q, x r q ∈ 𝒪[k]} from
        fun h => hy fun r q => by simpa using h (e.symm r) q)]
  have h2 : (re Φ).1 = Ξ := by
    funext y
    change Φ.1 (y.submatrix e id) = Ξ y
    rw [hΦ]
    simp
  rw [← hre Φ, ← hre Φ₀]
  exact hc Tm' hTm' (re Φ₀) (re Φ) h1 h2

end GlobalTheory.LastPlace


open GlobalTheory.LastPlace in

theorem GlobalTheory.FlatPlace.lastStep_eventually : Big fun ch => ChrP ch → ArrP ch → LocP ch → BesP ch → JacP ch → LastP ch := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch _ => ?_⟩⟩
  classical
  intro hChr hArr hLoc hBes hJac t w hw p hp β r r₀ h hpts M hM φ v f hvf j hj
  have hj0 : j + 2 * 0 + 2 = D.R.m := by omega
  have hm : (locGrid ch.G t w).m = D.R.m := rfl
  have hA1 := topRank_add (G := locGrid ch.G t w) one_le_sLen (j + 1)
  have hA0 := topRank_add (G := locGrid ch.G t w) one_le_sLen j
  have hA2 := topRank_add (G := locGrid ch.G t w) one_le_sLen (j + 1 + 1)
  have hAm := topRank_add (G := locGrid ch.G t w) one_le_sLen D.R.m
  rw [hm] at hA1 hA0 hA2 hAm
  have h₁ : topRank (locGrid ch.G t w) (j + 1) + 0 = (locGrid ch.G t w).rank (D.R.m, j + 1) := by omega
  have h₂ : topRank (locGrid ch.G t w) j + (0 + 1) = (locGrid ch.G t w).rank (D.R.m, j) := by omega
  have h₃ : (locGrid ch.G t w).rank (D.R.m, j + 1 + 1) = (locGrid ch.G t w).rank (D.R.m, D.R.m) := by
    rw [show j + 1 + 1 = D.R.m by omega]
  have h₄ : (locGrid ch.G t w).rank (D.R.m, j + 1) = topRank (locGrid ch.G t w) (j + 1) := by omega
  obtain ⟨hchar, hcond, -⟩ := hChr t w hw p hp
  obtain ⟨F₀, T₁, hcore, hT₁, hT₁O, Φ₁, hΦ₁, hT₁Φ⟩ := GlobalTheory.T.lastTwoSteps_localModel_flatMap_fourierJacobiStep ch hChr hArr hLoc hBes hJac t w hw p hp β r r₀ h hpts M hM φ v f
    hvf j hj0 (GlobalTheory.Unf.Inhab.nonempty_volN _).some h₁ h₂
  obtain ⟨T₂, hT₂, hT₂O, Φ₂, hΦ₂, hT₂Φ⟩ := GlobalTheory.T.lastTwoSteps_localModel_extendByZero_topStep ch hChr hArr hJac t w hw p hp β M hM φ v f hvf j hj0 h₃ h₄
  obtain ⟨e, he1, he2, FX, hFX, hFXe⟩ := GlobalTheory.T.lastTwoSteps_topVertex_frame_at_place ch t w hw p hp j hj
  intro I S x Ξ₁ Ξ₂ c₁ c₂ hc
  haveI : T2Space (Matrix (Fin ((locGrid ch.G t w).rank (D.R.m, D.R.m)) ⊕ Unit) (Fin (topRank (locGrid ch.G t w) (j + 1))) (Kw w)) :=
    GlobalTheory.FinPl.Comm.t2Space_matrix_of_isNonarchimedeanLocalField
  let Ξ₂' : I → SB (Matrix (Fin ((locGrid ch.G t w).rank (D.R.m, D.R.m)) ⊕ Unit) (Fin (topRank (locGrid ch.G t w) (j + 1))) (Kw w)) :=
    fun i => ⟨fun y => (Ξ₂ i).1 (y.submatrix e.symm id),
      GlobalTheory.FinPl.Comm.comp_mem_SB (Ξ₂ i).2 (p := fun y => y.submatrix e.symm id) (s := fun y => y.submatrix e id)
        (continuous_pi fun a => continuous_pi fun b => (continuous_apply b).comp (continuous_apply (e.symm a)))
        (continuous_pi fun a => continuous_pi fun b => (continuous_apply b).comp (continuous_apply (e a)))
        (fun y => by ext a b; simp)⟩
  have hΞ₂' : ∀ i y, (Ξ₂' i).1 y = (Ξ₂ i).1 (y.submatrix e.symm id) := fun _ _ => rfl
  let O₁ : SB (Matrix (Fin (topRank (locGrid ch.G t w) (j + 1))) (Fin (topRank (locGrid ch.G t w) j) ⊕ Unit) (Kw w)) :=
    ⟨_, GlobalTheory.LastTwoSteps.intInd_mem_SB _ _⟩
  let O₂ : SB (Matrix (Fin ((locGrid ch.G t w).rank (D.R.m, D.R.m))) (Fin (topRank (locGrid ch.G t w) (j + 1))) (Kw w)) :=
    ⟨_, GlobalTheory.LastTwoSteps.intInd_mem_SB _ _⟩
  have hO₁ : IsOne O₁ := rfl
  have hO₂ : IsOne O₂ := rfl
  have hL : (pLine D).rank = 1 := rfl
  have ha : ((p.xi ^ 0)⁻¹ : Kw w) ≠ 0 := by simp
  have hz : (lastTau (D := D)).map p.pr *ᵥ (fun _ => (1 : Kw w)) =
      (-(p.xi * (p.xi ^ 0)⁻¹)) • fun i => p.pr ((besAt ch.G hM j 0 hj0 (GlobalTheory.Unf.Inhab.nonempty_volN _).some).ζ i) := by
    funext i
    simp [lastTau, mulVec, dotProduct, besAt, Place.xi, Place.pr, hL]
    exact (mul_one _).symm
  have key := fun (S' : Finset I) (Ψ₂ : SB (Matrix (Fin ((locGrid ch.G t w).rank (D.R.m, D.R.m))) (Fin (topRank (locGrid ch.G t w) (j + 1))) (Kw w))) =>
    GlobalTheory.LastSeeSawGen.lastBi_expand D (Kw w) (unitVol w) (isUnitVol_unitVol w) p ch.W.ψ ch.W.ψ_std (psiAt ch.W w) hchar hcond 0
      (besAt ch.G hM j 0 hj0 (GlobalTheory.Unf.Inhab.nonempty_volN _).some) (ch.G.V (.top (j + 1))) (ch.G.V (.top (j + 1 + 1)))
      (ch.G.V (.grid D.R.m D.R.m)) (pLine D) (topOrthAt ch.G (show D.R.m = j + 1 + 1 by omega)) lastTau hL
      GlobalTheory.RowChain.LastSeeSawStep.lastTau_gram ((p.xi ^ 0)⁻¹) (fun _ => 1) ha hz _ _ _ (frTop ch.S.toGridChoice t w j (by omega)) F₀
      (frTop ch.S.toGridChoice t w (j + 1) (by omega)) (frRow ch.S.B t w D.R.m le_rfl) FX hcore hFX T₁ T₂ hT₁ hT₂ Φ₁ Ψ₂ O₁ O₂
      hO₁ hO₂ I S' x Ξ₁ Ξ₂' c₁ c₂
  have hc' : ∀ i ∈ S, p.IsCombAt ch.W.ψ (frTop ch.S.toGridChoice t w j (by omega)) (frTop ch.S.toGridChoice t w (j + 1) (by omega))
      (c₁ i) (Ξ₁ i).1 ∧ p.IsCombAt ch.W.ψ (frTop ch.S.toGridChoice t w (j + 1) (by omega)) FX (c₂ i) (Ξ₂' i).1 :=
    fun i hi => ⟨(hc i hi).1, combAt_renumber p ch.W.ψ _ _ FX e hFXe _ _ (hc i hi).2⟩
  have hsymm : ∀ a : Fin ((locGrid ch.G t w).rank (D.R.m, j + 1 + 1)),
      e.symm (Fin.castLE (by omega) a) = Sum.inl (Fin.cast h₃ a) := fun a => by
    rw [Equiv.symm_apply_eq]; ext; rw [he1]; rfl
  have hsymm' : e.symm (topLast (locGrid ch.G t w) (j + 1 + 1)) = Sum.inr () := by
    rw [Equiv.symm_apply_eq]; ext; rw [he2]; rfl
  unfold facAt locA conAt
  rw [dite_eq_left hj0, dite_eq_left hj0]
  unfold lastDat
  rw [← hT₁O O₁ hO₁, ← hT₂O O₂ hO₂]
  refine ⟨fun hrel => ?_, fun hexp => ?_⟩
  · have e1 := key S 0 hc' (fun y y' => by
      rw [Submodule.coe_zero, Pi.zero_apply, zero_mul]
      exact (hrel y (y'.submatrix e.symm id)).symm)
    have e2 := key ∅ 0 (fun i hi => absurd hi (Finset.notMem_empty i)) (fun y y' => by
      rw [Submodule.coe_zero, Pi.zero_apply, zero_mul, Finset.sum_empty])
    rw [Finset.sum_empty] at e2
    exact e1.symm.trans e2
  · rw [← hT₁Φ, ← hT₂Φ]
    refine key S Φ₂ hc' fun y y' => ?_
    rw [hΦ₂, hΦ₁]
    refine Eq.trans ?_ (hexp (y, y'.submatrix e.symm id))
    rw [dite_eq_left (show j + 2 * 0 + 2 = (locGrid ch.G t w).m from hj0)]
    have hy : y'.toRows₁.submatrix (Fin.cast h₃) (Fin.cast h₄) = (y'.submatrix e.symm id).submatrix
        (Fin.castLE (show (locGrid ch.G t w).rank ((locGrid ch.G t w).m, j + 1 + 1) ≤ _ by simp only [hm]; omega))
        (Fin.cast (show (locGrid ch.G t w).rank ((locGrid ch.G t w).m, j + 1) = _ by simp only [hm]; omega)) := by
      funext a b
      simp only [Matrix.submatrix_apply, Matrix.toRows₁_apply, id]
      exact congrArg (fun z => y' z (Fin.cast h₄ b)) (hsymm a).symm
    have hy' : (y'.submatrix e.symm id) (topLast (locGrid ch.G t w) (j + 1 + 1)) = y' (Sum.inr ()) := by
      funext b
      simp only [Matrix.submatrix_apply, id]
      rw [hsymm']
    simp only
    rw [hy, hy']
    rfl

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatDictionaryLastTwoStepsAtPlaceStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil


theorem _root_.GlobalTheory.T.flatDictionary_lastTwoSteps_at_place : Big fun ch => ChrP ch → ArrP ch → LocP ch → BesP ch → JacP ch → LastP ch := by
  first | exact @GlobalTheory.FlatPlace.lastStep_eventually | exact GlobalTheory.FlatPlace.lastStep_eventually | (intros; apply GlobalTheory.FlatPlace.lastStep_eventually <;> assumption)
end
end
