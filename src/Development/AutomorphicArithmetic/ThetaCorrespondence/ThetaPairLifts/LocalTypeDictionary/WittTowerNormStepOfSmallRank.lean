module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialHeckeLFunctionSquareEqPrimitiveStatement
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
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
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaStepFactorRatioUnitGaussSumQuotientStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseFits
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTowerStageRankFactorization
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaneSplit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneSplitSelfDualHermitianComplement
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualLatticeHasRigidification
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsSmallTripleOfWeilVacuum
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaTowerStageNormFactorization
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TowerStageSuccessorCoefficients
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.StageTriangleFactorStepSecond

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SqStep

theorem gbig_three {Q₁ Q₂ Q₃ Q : GP} (h₁ : GBig Q₁) (h₂ : GBig Q₂) (h₃ : GBig Q₃)
    (H : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) (μ₀ : T) (C x b : ℝ),
      Q₁ G μ₀ C x b → Q₂ G μ₀ C x b → Q₃ G μ₀ C x b → Q G μ₀ C x b) : GBig Q := by
  obtain ⟨F₁, h₁⟩ := h₁
  obtain ⟨F₂, h₂⟩ := h₂
  obtain ⟨F₃, h₃⟩ := h₃
  refine ⟨max F₁ (max F₂ F₃), fun ε CF hCF => ?_⟩
  obtain ⟨C₁, x₁, k₁⟩ := h₁ ε CF (le_trans (le_max_left _ _) hCF)
  obtain ⟨C₂, x₂, k₂⟩ := h₂ ε CF (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hCF)
  obtain ⟨C₃, x₃, k₃⟩ := h₃ ε CF (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hCF)
  refine ⟨max C₁ (max C₂ C₃), max x₁ (max x₂ x₃), fun C hC D large₂ he hx hR T Lc μ₀ hL G => H G μ₀ C _ _ ?_ ?_ ?_⟩
  · exact k₁ C (le_trans (le_max_left _ _) hC) D large₂ he (le_trans (le_max_left _ _) hx) hR T Lc μ₀ hL G
  · exact k₂ C (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hC) D large₂ he
      (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx) hR T Lc μ₀ hL G
  · exact k₃ C (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hC) D large₂ he
      (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx) hR T Lc μ₀ hL G

end GlobalTheory.SqStep

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneSplitSelfDualHermitianComplementStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.hyperbolicPlane_split_selfDual_hermitian_complement : ∀ (D : D7) (S : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (q : ℕ),
    IsSelfDualC S Λ → NegIdx S (q + 1) → q + 2 ≤ S.rank → 3 ≤ S.rank →
    ∃ (S₁ : HSp D) (Λ₁ : Submodule (𝓞 D.host.E) (Fin S₁.rank → D.host.E)) (ι : S₁.V →ₗ[D.host.E] S.V) (x y : S.V),
      GlobalTheory.SqStepK.PlaneSplit S S₁ Λ Λ₁ ι x y ∧ S₁.SigOK ∧ IsSelfDualC S₁ Λ₁ ∧ NegIdx S₁ q := by
  first | exact @GlobalTheory.PlaneComplement.plane_split_complement | exact GlobalTheory.PlaneComplement.plane_split_complement | (intros; apply GlobalTheory.PlaneComplement.plane_split_complement <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.QuadraticTowerStepStageInduction

section

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.SqStepK.PiLocalization₂
theorem quadratic_tower_step_base_stage : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW),
      GlobalTheory.SqTower.IsStageC W i j p (q + 1) X → ∃ (B' WW₁ : HSp D) (Y : Tri T A B' WW₁),
        GlobalTheory.SqTower.IsStageC W i j p q Y ∧ GlobalTheory.SqStepK.IsStepB X Y := by
  intro hP _ _
  refine ⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ _ _ _ T Lc μ₀ _ G => ?_⟩⟩
  intro W S hψ hN i j p q A A' WW X hX
  obtain ⟨hp, hq, hrA, hrA', hnA, hnA', hnW, hXI⟩ := hX
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have hrk := hXI.rank
  have hb1 : 2 * qq D j + 3 ≤ rankV D i j := by
    simp only [rankV, qq, Formalism.BasicNotions.Ranks.r]; omega
  have hb2 : 2 * pp D j ≤ rankV D (i + 1) (j + 1) := by
    simp only [rankV, pp, Formalism.BasicNotions.Ranks.r]; omega
  obtain ⟨B', Λ₁, ι, x, y, hs, hsig, hsd, hneg⟩ := GlobalTheory.T.hyperbolicPlane_split_selfDual_hermitian_complement D A' X.rA'.Λ q hXI.rigA'.1 hnA' (by omega) (by omega)
  obtain ⟨WW₁, ΛW, ι', x', y', hs', hsig', hsd', hneg'⟩ :=
    GlobalTheory.T.hyperbolicPlane_split_selfDual_hermitian_complement D WW X.rW.Λ (p + q) hXI.rigW.1 (by simpa only [add_assoc] using hnW) (by omega) (by omega)
  obtain ⟨rB, eB, hB⟩ := GlobalTheory.RigExists.exists_rig D B' Λ₁ hsig hsd
  obtain ⟨rW, eW, hW⟩ := GlobalTheory.RigExists.exists_rig D WW₁ ΛW hsig' hsd'
  obtain ⟨Y, e1, e2, e3, hY⟩ := _root_.GlobalTheory.T.exists_small_triple_of_weil_vacuum hP D T A A' WW B' WW₁ X W.ψ W.θ _ _ _ _ rB rW W.θ_is hXI hB hW
    (by have := hs.1; omega) (by have := hs'.1; omega)
  refine ⟨B', WW₁, Y, ⟨hp, by omega, hrA, by have := hs.1; omega, hnA, hneg, hneg', hY⟩, e1, ⟨ι, x, y, ?_⟩, ⟨ι', x', y', ?_⟩⟩
  · rw [e2, eB]; exact hs
  · rw [e3, eW]; exact hs'
end GlobalTheory.SqStepK.PiLocalization₂
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.quadratic_tower_step_stage_induction : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW),
      GlobalTheory.SqTower.IsStageC W i j p (q + 1) X → ∃ (B' WW₁ : HSp D) (Y : Tri T A B' WW₁),
        GlobalTheory.SqTower.IsStageC W i j p q Y ∧ GlobalTheory.SqStepK.IsStepB X Y := by
  first | exact @_root_.GlobalTheory.SqStepK.PiLocalization₂.quadratic_tower_step_base_stage | exact _root_.GlobalTheory.SqStepK.PiLocalization₂.quadratic_tower_step_base_stage | (intros; apply _root_.GlobalTheory.SqStepK.PiLocalization₂.quadratic_tower_step_base_stage <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SeesawFirstReductionLevel

section

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.SqStepK
section Values
open GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
end Values
theorem seesaw_first_reduction : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW) (lam : T → ℂ) (e : ℕ),
      GlobalTheory.SqTower.IsStageC W i j p (q + 1) X → Factor X W.ψ W.θ lam → A.rank = A'.rank + 2 * e →
      ∃ (B B' WW₁ : HSp D) (Y : Tri T B B' WW₁) (c : T → ℂ), GlobalTheory.SqTower.IsStageC W i j p q Y ∧ Y.IsConst W.ψ W.θ c ∧
        (∀ t, c t ≠ 0) ∧ ∀ t, ∃ (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (e₁ e₂ s : ℤˣ)
          (𝔟 𝔠 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E), GlobalTheory.SqStep.BaseFits G W i j t Bs ∧
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.stepFac Bs (GlobalTheory.SqStep.chs G i j t) e₁ e₂ s 𝔟 𝔠 (-(e : ℤ)) ≠ 0 ∧
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.stepFac Bs (GlobalTheory.SqStep.chs G i j μ₀) e₁ e₂ s 𝔟 𝔠 (-(e : ℤ)) ≠ 0 ∧
          GlobalTheory.LFun.charL (GlobalTheory.SqStep.chs G i j t).ν (G.pl.S0 : Set (HeightOneSpectrum (𝓞 D.host.F))) ((e + 1 : ℕ) : ℂ) ≠ 0 ∧
          GlobalTheory.LFun.charL (GlobalTheory.SqStep.chs G i j μ₀).ν (G.pl.S0 : Set (HeightOneSpectrum (𝓞 D.host.F))) ((e + 1 : ℕ) : ℂ) ≠ 0 ∧
          lam t * GlobalTheory.LFun.charL (GlobalTheory.SqStep.chs G i j t).ν (G.pl.S0 : Set (HeightOneSpectrum (𝓞 D.host.F))) ((e + 1 : ℕ) : ℂ) *
              GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.stepFac Bs (GlobalTheory.SqStep.chs G i j t) e₁ e₂ s 𝔟 𝔠 (-(e : ℤ)) * c μ₀ =
            lam μ₀ * GlobalTheory.LFun.charL (GlobalTheory.SqStep.chs G i j μ₀).ν (G.pl.S0 : Set (HeightOneSpectrum (𝓞 D.host.F))) ((e + 1 : ℕ) : ℂ) *
              GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.stepFac Bs (GlobalTheory.SqStep.chs G i j μ₀) e₁ e₂ s 𝔟 𝔠 (-(e : ℤ)) * c t := by
  intro hP hK hM
  obtain ⟨e₁, e₂, s, hSB⟩ := hK.2.1
  refine gbig_three_is (_root_.GlobalTheory.T.quadratic_tower_step_stage_induction hP hK hM) (_root_.GlobalTheory.T.tower_stage_successor_coefficients_alt hP hK hM) (_root_.GlobalTheory.T.exists_factor_of_isStageC hP hK hM) ?_
  intro D T Lc sc G μ₀ C x b hL hy hd hf W S hψ hN i j p q A A' WW X lam e hX hF he
  obtain ⟨B', WW₁, Y, hY, hst⟩ := hy W S hψ hN i j p q A A' WW X hX
  obtain ⟨c, hc⟩ := hf W S hψ hN i j p q A B' WW₁ Y hY
  haveI : Nonempty T := ⟨μ₀⟩
  refine ⟨A, B', WW₁, Y, c, hY, hc.isConst, hc.1, fun t => ?_⟩
  obtain ⟨Bs, bb, Γ, Γ₁, H, H', R, R₁, d, d₁, k, k₁, hfit, hb, hV, hp, hq, hH, hH', hd0, hd10, hk⟩ :=
    hd W S hψ hN i j p q A A' WW B' WW₁ X Y lam c e hX hY hst hF hc he t
  obtain ⟨C₀, hC₀, hstep⟩ := hSB D.host.F D.host.E D.sp.cm.sig Bs A.rank bb Γ Γ₁ H H' R R₁ hV hp hq hH hH'
  have hE : (A.rank - (bb + 2)) / 2 = e := by omega
  have key : ∀ t' ∈ ({t, μ₀} : Set T),
      d * (((GlobalTheory.SqStep.chs G i j t').ν k / (GlobalTheory.SqStep.chs G i j μ₀).ν k : Circle) : ℂ) * lam t' *
      GlobalTheory.LFun.charL (GlobalTheory.SqStep.chs G i j t').ν (G.pl.S0 : Set (HeightOneSpectrum (𝓞 D.host.F))) ((e + 1 : ℕ) : ℂ) *
      (C₀ * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.stepFac Bs (GlobalTheory.SqStep.chs G i j t') e₁ e₂ s H.𝔟 H'.𝔟 (-(e : ℤ))) =
      d₁ * (((GlobalTheory.SqStep.chs G i j t').ν k₁ / (GlobalTheory.SqStep.chs G i j μ₀).ν k₁ : Circle) : ℂ) * c t' := by
    intro t' ht'
    obtain ⟨⟨om, om', Rf, hm, hκ⟩, ⟨om₁, om₁', Rf₁, hm₁, hκ₁⟩⟩ := hk t' ht'
    obtain ⟨u, hu1, hu2⟩ := hstep _ om om' Rf om₁ om₁' Rf₁ hm hm₁ _ _ hκ hκ₁
    rw [hE] at hu1 hu2
    have e1 : (((e : ℕ) : ℂ) + 1) = ((e + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [e1] at hu2
    change _ * GlobalTheory.LFun.charL _ (G.pl.S0 : Set (HeightOneSpectrum (𝓞 D.host.F))) _ = _ at hu2
    rw [hu2, mul_right_comm, hu1, one_mul]
  have good : ∀ t' ∈ ({t, μ₀} : Set T), GlobalTheory.LFun.IsHecke D.host.F D.host.E (GlobalTheory.SqStep.chs G i j t').ν ∧
      ∀ᶠ w in Filter.cofinite, GlobalTheory.LFun.UnrAt (GlobalTheory.SqStep.chs G i j t').ν w := by
    intro t' ht'
    obtain ⟨⟨om, om', Rf, hm, -⟩, -⟩ := hk t' ht'
    exact nu_good hm.triple.chars
  obtain ⟨gt, ut⟩ := good t (by simp)
  obtain ⟨gμ, uμ⟩ := good μ₀ (by simp)
  obtain ⟨n, hn, hv⟩ := val_quot_pow G hL W S hN i j t
  obtain ⟨𝔟, r, hr, st, sμ⟩ := exists_stepFac_twist Bs (X := GlobalTheory.SqStep.chs G i j t) (Y := GlobalTheory.SqStep.chs G i j μ₀)
    ⟨gt.1.div' gμ.1, fun y => by simp only [MonoidHom.div_apply, gt.2 y, gμ.2 y, div_one]⟩
    ((ut.and uμ).mono fun w hw => by rw [div_eq_mul_inv]; exact hw.1.mul hw.2.inv) hn hv e₁ e₂ s H.𝔟 H'.𝔟 (-(e : ℤ)) (k / k₁)
  have kt := key t (by simp)
  have kμ := key μ₀ (by simp)
  rw [div_self', div_self', Circle.coe_one, mul_one, mul_one] at kμ
  have ek : (((GlobalTheory.SqStep.chs G i j t).ν k / (GlobalTheory.SqStep.chs G i j μ₀).ν k : Circle) : ℂ) =
      (((GlobalTheory.SqStep.chs G i j t).ν (k / k₁) / (GlobalTheory.SqStep.chs G i j μ₀).ν (k / k₁) : Circle) : ℂ) *
        (((GlobalTheory.SqStep.chs G i j t).ν k₁ / (GlobalTheory.SqStep.chs G i j μ₀).ν k₁ : Circle) : ℂ) := by
    rw [← Circle.coe_mul, div_mul_div_comm, ← map_mul, ← map_mul, div_mul_cancel]
  rw [ek] at kt
  have z₀ := Circle.coe_ne_zero ((GlobalTheory.SqStep.chs G i j t).ν (k / k₁) / (GlobalTheory.SqStep.chs G i j μ₀).ν (k / k₁))
  have z₁ := Circle.coe_ne_zero ((GlobalTheory.SqStep.chs G i j t).ν k₁ / (GlobalTheory.SqStep.chs G i j μ₀).ν k₁)
  have nt := mul_ne_zero (mul_ne_zero hd10 z₁) (hc.1 t)
  have nμ : d₁ * c μ₀ ≠ 0 := mul_ne_zero hd10 (hc.1 μ₀)
  rw [← kt] at nt
  rw [← kμ] at nμ
  refine ⟨Bs, e₁, e₂, s, 𝔟, H'.𝔟, hfit, ?_, ?_, right_ne_zero_of_mul (left_ne_zero_of_mul nt),
    right_ne_zero_of_mul (left_ne_zero_of_mul nμ), ?_⟩
  · rw [st]
    exact mul_ne_zero (mul_ne_zero z₀ hr) (right_ne_zero_of_mul (right_ne_zero_of_mul nt))
  · rw [sμ]
    exact mul_ne_zero hr (right_ne_zero_of_mul (right_ne_zero_of_mul nμ))
  · rw [st, sμ]
    refine mul_left_cancel₀ (mul_ne_zero (mul_ne_zero hd0 hC₀) z₁) ?_
    linear_combination (r * c μ₀) * kt -
      (r * c t * (((GlobalTheory.SqStep.chs G i j t).ν k₁ / (GlobalTheory.SqStep.chs G i j μ₀).ν k₁ : Circle) : ℂ)) * kμ
end GlobalTheory.SqStepK
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem _root_.GlobalTheory.T.seesaw_first_reduction_level : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW) (lam : T → ℂ) (e : ℕ),
      GlobalTheory.SqTower.IsStageC W i j p (q + 1) X → Factor X W.ψ W.θ lam → A.rank = A'.rank + 2 * e →
      ∃ (B B' WW₁ : HSp D) (Y : Tri T B B' WW₁) (c : T → ℂ), GlobalTheory.SqTower.IsStageC W i j p q Y ∧ Y.IsConst W.ψ W.θ c ∧
        (∀ t, c t ≠ 0) ∧ ∀ t, ∃ (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (e₁ e₂ s : ℤˣ)
          (𝔟 𝔠 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E), GlobalTheory.SqStep.BaseFits G W i j t Bs ∧
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.stepFac Bs (GlobalTheory.SqStep.chs G i j t) e₁ e₂ s 𝔟 𝔠 (-(e : ℤ)) ≠ 0 ∧
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.stepFac Bs (GlobalTheory.SqStep.chs G i j μ₀) e₁ e₂ s 𝔟 𝔠 (-(e : ℤ)) ≠ 0 ∧
          GlobalTheory.LFun.charL (GlobalTheory.SqStep.chs G i j t).ν (G.pl.S0 : Set (HeightOneSpectrum (𝓞 D.host.F))) ((e + 1 : ℕ) : ℂ) ≠ 0 ∧
          GlobalTheory.LFun.charL (GlobalTheory.SqStep.chs G i j μ₀).ν (G.pl.S0 : Set (HeightOneSpectrum (𝓞 D.host.F))) ((e + 1 : ℕ) : ℂ) ≠ 0 ∧
          lam t * GlobalTheory.LFun.charL (GlobalTheory.SqStep.chs G i j t).ν (G.pl.S0 : Set (HeightOneSpectrum (𝓞 D.host.F))) ((e + 1 : ℕ) : ℂ) *
              GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.stepFac Bs (GlobalTheory.SqStep.chs G i j t) e₁ e₂ s 𝔟 𝔠 (-(e : ℤ)) * c μ₀ =
            lam μ₀ * GlobalTheory.LFun.charL (GlobalTheory.SqStep.chs G i j μ₀).ν (G.pl.S0 : Set (HeightOneSpectrum (𝓞 D.host.F))) ((e + 1 : ℕ) : ℂ) *
              GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.stepFac Bs (GlobalTheory.SqStep.chs G i j μ₀) e₁ e₂ s 𝔟 𝔠 (-(e : ℤ)) * c t := by
  first | exact @_root_.GlobalTheory.SqStepK.seesaw_first_reduction | exact _root_.GlobalTheory.SqStepK.seesaw_first_reduction | (intros; apply _root_.GlobalTheory.SqStepK.seesaw_first_reduction <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.WittTowerNormStepOfSmallRank

section

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.SqStep
theorem theta_tower_norm_step_small_rank : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW) (lam : T → ℂ) (e : ℕ) (Lf : T → ℂ → ℂ),
      GlobalTheory.SqTower.IsStageC W i j p (q + 1) X → Factor X W.ψ W.θ lam → A.rank = A'.rank + 2 * e →
      (∀ t, IsHeckeL (nuH G t i j) (Lf t)) → ∃ (B B' WW₁ : HSp D) (Y : Tri T B B' WW₁) (c y : T → ℂ),
        GlobalTheory.SqTower.IsStageC W i j p q Y ∧ Y.IsConst W.ψ W.θ c ∧
        (∀ t, y t ≠ 0 ∧ lam t * Lf t ((e + 1 : ℕ) : ℂ) = y t * c t) ∧ ∀ t, GlobalTheory.Square.StepRatio D.what₂.embLL (Qn G t) G.pl.S0 (condExp G.pl) (fun v => Ideal.absNorm v.asIdeal) (y t) (y μ₀) := by
  intro hP hK hM
  refine gbig_three (_root_.GlobalTheory.T.seesaw_first_reduction_level hP hK hM) GlobalTheory.T.thetaStepFactor_ratio_unit_gaussSumQuotient GlobalTheory.T.partialHeckeLFunction_square_eq_primitive ?_
  intro D T Lc sc G μ₀ C x b hk ha hl W S hψ hN i j p q A A' WW X lam e Lf hX hF he hLf
  obtain ⟨B, B', WW₁, Y, c, hY, hc, hc0, H⟩ := hk W S hψ hN i j p q A A' WW X lam e hX hF he
  have he1 : 1 ≤ e := by
    obtain ⟨h1, h2, a1, a2, -⟩ := hX
    have e2 : rankV D (↑i + 1) (↑j + 1) = rankV D ↑i ↑j + D.R.t + sLen D := by simp only [rankV]; ring
    have h3 := D.R.three_m_lt_t
    have hpp : pp D j ≤ D.R.m := by unfold pp; omega
    have hqq : qq D j ≤ D.R.m := by unfold qq; omega
    omega
  have hLeq : ∀ t, GlobalTheory.LFun.charL (chs G i j t).ν (G.pl.S0 : Set (HeightOneSpectrum (𝓞 D.host.F))) ((e + 1 : ℕ) : ℂ) =
      Lf t ((e + 1 : ℕ) : ℂ) := fun t => hl i j t (e + 1) (Lf t) (by omega) (hLf t)
  refine ⟨B, B', WW₁, Y, c, fun t => lam t * Lf t ((e + 1 : ℕ) : ℂ) / c t, hY, hc, fun t => ⟨?_, ?_⟩, fun t => ?_⟩
  · obtain ⟨Bs, e₁, e₂, s, 𝔟, 𝔠, -, -, -, hL0, -, -⟩ := H t
    rw [hLeq t] at hL0
    exact div_ne_zero (mul_ne_zero (hF.1 t) hL0) (hc0 t)
  · rw [div_mul_cancel₀ _ (hc0 t)]
  · obtain ⟨Bs, e₁, e₂, s, 𝔟, 𝔠, hfit, hsf, hsf0, -, -, heq⟩ := H t
    rw [hLeq t, hLeq μ₀] at heq
    obtain ⟨bb, g, g', hb, hg, e3⟩ := ha W S hψ hN i j t Bs e₁ e₂ s 𝔟 𝔠 (-(e : ℤ)) hfit hsf
    refine ⟨bb, g, g', hb, hg, ?_⟩
    have h0 := hc0 μ₀
    have ht := hc0 t
    rw [e3] at heq
    have key := mul_right_cancel₀ hsf (show (lam t * Lf t ((e + 1 : ℕ) : ℂ) * c μ₀) * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.stepFac Bs (chs G i j t) e₁ e₂ s 𝔟 𝔠 (-(e : ℤ)) =
      (D.what₂.embLL (bb * ∏ v ∈ G.pl.S0, ((g v : D.what₂.LL) / (g' v : D.what₂.LL))) * (lam μ₀ * Lf μ₀ ((e + 1 : ℕ) : ℂ)) * c t) *
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.stepFac Bs (chs G i j t) e₁ e₂ s 𝔟 𝔠 (-(e : ℤ)) by linear_combination heq)
    field_simp
    linear_combination key
end GlobalTheory.SqStep
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem _root_.GlobalTheory.T.witt_tower_norm_step_of_small_rank : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW) (lam : T → ℂ) (e : ℕ) (Lf : T → ℂ → ℂ),
      GlobalTheory.SqTower.IsStageC W i j p (q + 1) X → Factor X W.ψ W.θ lam → A.rank = A'.rank + 2 * e →
      (∀ t, IsHeckeL (nuH G t i j) (Lf t)) → ∃ (B B' WW₁ : HSp D) (Y : Tri T B B' WW₁) (c y : T → ℂ),
        GlobalTheory.SqTower.IsStageC W i j p q Y ∧ Y.IsConst W.ψ W.θ c ∧
        (∀ t, y t ≠ 0 ∧ lam t * Lf t ((e + 1 : ℕ) : ℂ) = y t * c t) ∧ ∀ t, GlobalTheory.Square.StepRatio D.what₂.embLL (Qn G t) G.pl.S0 (condExp G.pl) (fun v => Ideal.absNorm v.asIdeal) (y t) (y μ₀) := by
  first | exact @_root_.GlobalTheory.SqStep.theta_tower_norm_step_small_rank | exact _root_.GlobalTheory.SqStep.theta_tower_norm_step_small_rank | (intros; apply _root_.GlobalTheory.SqStep.theta_tower_norm_step_small_rank <;> assumption)
end
end
end
