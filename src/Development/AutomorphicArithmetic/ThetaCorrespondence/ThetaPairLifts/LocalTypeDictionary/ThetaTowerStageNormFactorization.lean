module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.AuxiliaryPrimeNeTypePrime
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsThetaFunOOfIsVacO
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtYAndItYOfPair
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedWeilRepresentationConvergence
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaSmallRankStageHolds
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaStageKernelCharacterization
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaStageLiftExists

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorOfStageTriangle

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

namespace GlobalTheory.StageFactor

open MeasureTheory

variable {D : D7} {T : Type} {A A' WW : HSp D}

theorem ker_add_smul (X : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (t : T)
    (P Q : PolF D WW.rank A.rank) (c : ℂ) (h : GA D WW) :
    X.ker ψ θ t (P + c • Q) h = fun g => X.ker ψ θ t P h g + c * X.ker ψ θ t Q h g := by
  funext g
  simp [Tri.ker, thetaKO, map_add (f := _), map_smul]

def linI (X : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (t : T)
    (hint : ∀ P h, IntegrableOn (X.ker ψ θ t P h) X.fd X.m) : PolF D WW.rank A.rank →ₗ[ℂ] (GA D WW → ℂ) where
  toFun P := X.I ψ θ t P
  map_add' P Q := by
    funext h
    have e := ker_add_smul X ψ θ t P Q 1 h
    simp only [one_smul, one_mul] at e
    simp only [Tri.I, Pi.add_apply, e]
    exact integral_add (hint P h) (hint Q h)
  map_smul' c Q := by
    funext h
    have e := ker_add_smul X ψ θ t 0 Q c h
    simp only [zero_add] at e
    have e0 : X.ker ψ θ t 0 h = 0 := by funext g; simp [Tri.ker, thetaKO]
    simp only [Tri.I, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, e, e0, Pi.zero_apply, zero_add]
    exact integral_const_mul c _

theorem linI_apply (X : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (t : T)
    (hint : ∀ P h, IntegrableOn (X.ker ψ θ t P h) X.fd X.m) (P : PolF D WW.rank A.rank) :
    linI X ψ θ t hint P = X.I ψ θ t P := rfl

theorem factor_of_parts (X : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (hint : ∀ t P h, IntegrableOn (X.ker ψ θ t P h) X.fd X.m)
    (hker : ∀ t t' P, X.I ψ θ t P = 0 → X.I ψ θ t' P = 0)
    (lam : T → ℂ) (s : PolF D WW.rank A'.rank →ₗ[ℂ] PolF D WW.rank A.rank) (hlam : ∀ t, lam t ≠ 0)
    (hs : ∀ t P', (∀ h, IntegrableOn (X.ker' ψ θ t P' h) X.fd' X.m') → X.I ψ θ t (s P') = lam t • X.I' ψ θ t P')
    (hconv : ∃ P', (∀ t h, IntegrableOn (X.ker' ψ θ t P' h) X.fd' X.m') ∧ ∀ t, X.I' ψ θ t P' ≠ 0) :
    Factor X ψ θ lam := by
  rcases isEmpty_or_nonempty T with hT | ⟨⟨t₀⟩⟩
  · refine ⟨hlam, ModuleCat.of ℂ ℂ, MvPolynomial.lcoeff ℂ 0, MvPolynomial.lcoeff ℂ 0, fun _ => 0,
      fun z => ⟨MvPolynomial.C z, by simp⟩, fun t => hT.elim t, fun t => hT.elim t, fun t => hT.elim t,
      fun t => hT.elim t, 1, by simp, fun t => hT.elim t⟩
  · let K : Submodule ℂ (PolF D WW.rank A.rank) := LinearMap.ker (linI X ψ θ t₀ (hint t₀))
    have hK : ∀ t, LinearMap.ker (linI X ψ θ t (hint t)) = K := fun t => by
      ext P
      simp only [K, LinearMap.mem_ker, linI_apply]
      exact ⟨hker t t₀ P, hker t₀ t P⟩
    let Jb : T → ((PolF D WW.rank A.rank ⧸ K) →ₗ[ℂ] (GA D WW → ℂ)) := fun t =>
      K.liftQ (linI X ψ θ t (hint t)) (hK t).ge
    have hJb : ∀ t, Function.Injective (Jb t) := fun t => by
      rw [← LinearMap.ker_eq_bot]
      exact Submodule.ker_liftQ_eq_bot _ _ _ (hK t).le
    refine ⟨hlam, ModuleCat.of ℂ (PolF D WW.rank A.rank ⧸ K), K.mkQ, K.mkQ ∘ₗ s, fun t => (lam t)⁻¹ • Jb t,
      K.mkQ_surjective, fun t => ?_, hint, fun t P => ?_, fun t P' hP' => ?_, ?_⟩
    · intro x y hxy
      exact hJb t (smul_right_injective _ (inv_ne_zero (hlam t)) hxy)
    · show X.I ψ θ t P = lam t • ((lam t)⁻¹ • Jb t (K.mkQ P))
      rw [smul_smul, mul_inv_cancel₀ (hlam t), one_smul]
      rfl
    · show X.I' ψ θ t P' = (lam t)⁻¹ • Jb t (K.mkQ (s P'))
      have : Jb t (K.mkQ (s P')) = X.I ψ θ t (s P') := rfl
      rw [this, hs t P' hP', smul_smul, inv_mul_cancel₀ (hlam t), one_smul]
    · obtain ⟨P', hc, hne⟩ := hconv
      refine ⟨P', fun h0 => hne t₀ ?_, hc⟩
      have h1 : s P' ∈ K := (Submodule.Quotient.mk_eq_zero K).1 h0
      have h2 : X.I ψ θ t₀ (s P') = 0 := h1
      rw [hs t₀ P' (hc t₀)] at h2
      exact (smul_eq_zero.1 h2).resolve_left (hlam t₀)

end GlobalTheory.StageFactor

open GlobalTheory.StageFactor

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.StageTriangleKernelIntegrable

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

namespace GlobalTheory.StageConv

theorem m_le_of_size {D : D7} {large₂ : SizeData₂ D} (h : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂) : D.R.m ≤ D.R.r + 1 := by
  have h4 : D.R.m ^ 4 ≤ D.R.f := h.2.2.1
  have hm : 44 ≤ D.R.m := h.2.2.2.1
  have hfm : D.R.f * D.R.m ≤ (D.R.r + 1) ^ 3 := h.2.2.2.2.2.2.1
  by_contra hc
  push_neg at hc
  have h1 : (D.R.r + 1) ^ 3 < D.R.m ^ 3 := Nat.pow_lt_pow_left hc (by norm_num)
  have h2 : D.R.m ^ 3 ≤ D.R.m ^ 4 * D.R.m := by
    calc D.R.m ^ 3 ≤ D.R.m ^ 5 := Nat.pow_le_pow_right (by omega) (by norm_num)
      _ = D.R.m ^ 4 * D.R.m := by ring
  have h3 : D.R.m ^ 4 * D.R.m ≤ D.R.f * D.R.m := Nat.mul_le_mul_right _ h4
  omega

theorem rank_lt {D : D7} {i j : Fin D.R.m} {p q : ℕ} {A A' WW : HSp D} (hmr : D.R.m ≤ D.R.r + 1)
    (hp : p ≤ pp D j) (hq : q ≤ qq D j) (hA : A.rank + 2 * pp D j = rankV D (i + 1) (j + 1) + 2 * p)
    (hA' : A'.rank + 2 * qq D j = rankV D i j + 2 * q) (hd : A.rank + A'.rank = WW.rank) :
    WW.rank < 2 * (A.rank - p) := by
  have e1 : rankV D ((i : ℕ) + 1) ((j : ℕ) + 1) = rankV D i j + D.R.t + sLen D := by
    simp only [rankV]; ring
  have hpp : 2 * pp D j ≤ D.R.m - 1 := by
    simp only [pp]; have := j.2; omega
  have hs : sLen D = D.R.r + 6 := rfl
  rw [e1] at hA
  omega

end GlobalTheory.StageConv
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaIntegralStageConvergent

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
namespace GlobalTheory.StageConv
theorem theta_stage_converges : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j p q X →
      ∀ t P h, MeasureTheory.IntegrableOn (X.ker W.ψ W.θ t P h) X.fd X.m := by
  intro hP _ _
  have hW := _root_.GlobalTheory.T.twisted_theta_integral_converges hP.siegelSetUnitary hP
  refine ⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ _ _ hRec T Lc μ₀ _ G => ?_⟩⟩
  intro W S _ _ i j p q A A' WW X hX t P h
  obtain ⟨hp, hq, hA, hA', hnA, _, _, hXi⟩ := hX
  obtain ⟨τ⟩ : Nonempty D.what₂.Tau := ⟨D.eTau.symm (Classical.arbitrary _)⟩
  have hrank : WW.rank < 2 * (A.rank - p) := rank_lt (m_le_of_size hRec.size) hp hq hA hA' hXi.rank
  have hf :=
    GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt W.ψ_std W.θ_is (hXi.fst t) (GlobalTheory.OneMapRef.isThetaFunO_of_isVacO hXi.isVac)
  have hΦ := GlobalTheory.Chain.InnerSteps.theta_pureTensorO (S := GlobalTheory.Grid.neg A) (T := WW) W.ψ_std W.θ_is (fun τ => -X.rA.s τ) X.rA.B X.rW.s X.rW.B hf P
  obtain ⟨N, C', hint⟩ := hW D W.ψ W.θ W.θ_is true A WW _ _ (X.ω t) (hXi.weil t) p ⟨τ, hnA τ⟩ hrank X.m X.fd hXi.meas _ hΦ
  exact (hint h).1
end GlobalTheory.StageConv
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

theorem _root_.GlobalTheory.T.theta_integral_stage_convergent : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j p q X →
      ∀ t P h, MeasureTheory.IntegrableOn (X.ker W.ψ W.θ t P h) X.fd X.m := by
  first | exact @_root_.GlobalTheory.StageConv.theta_stage_converges | exact _root_.GlobalTheory.StageConv.theta_stage_converges | (intros; apply _root_.GlobalTheory.StageConv.theta_stage_converges <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaTowerStageNormFactorization

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
namespace GlobalTheory.StageFactor
open MeasureTheory
variable {D : D7} {T : Type} {A A' WW : HSp D}
end GlobalTheory.StageFactor
open GlobalTheory.StageFactor
theorem GlobalTheory.StageFactor.theta_tower_stage_norm_factorization : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j p q X →
      ∃ lam : T → ℂ, Factor X W.ψ W.θ lam := by
  intro hP hK hL
  obtain ⟨c, hc⟩ := GlobalTheory.SqTop.Model.gBig_and (GlobalTheory.SqTop.Model.gBig_and (_root_.GlobalTheory.T.theta_integral_stage_convergent hP hK hL) (_root_.GlobalTheory.T.theta_stage_kernel_characterization hP hK hL))
    (GlobalTheory.SqTop.Model.gBig_and (_root_.GlobalTheory.T.theta_stage_liftable hP hK hL) (_root_.GlobalTheory.T.theta_small_rank_stage_holds hP hK hL))
  refine ⟨c, fun ε CF hCF => ?_⟩
  obtain ⟨C0, x0, h⟩ := hc ε CF hCF
  refine ⟨C0, x0, fun C hC D large₂ a b r T Lc μ hL G W S hW hN i j p q A A' WW X hX => ?_⟩
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h C hC D large₂ a b r T Lc μ hL G
  obtain ⟨lam, s, hlam, hs⟩ := h3 W S hW hN i j p q A A' WW X hX
  exact ⟨lam, factor_of_parts X W.ψ W.θ (h1 W S hW hN i j p q A A' WW X hX) (h2 W S hW hN i j p q A A' WW X hX) lam s hlam hs
    (h4 W S hW hN i j p q A A' WW X hX)⟩
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

theorem _root_.GlobalTheory.T.exists_factor_of_isStageC : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j p q X →
      ∃ lam : T → ℂ, Factor X W.ψ W.θ lam := by
  first | exact @_root_.GlobalTheory.StageFactor.theta_tower_stage_norm_factorization | exact _root_.GlobalTheory.StageFactor.theta_tower_stage_norm_factorization | (intros; apply _root_.GlobalTheory.StageFactor.theta_tower_stage_norm_factorization <;> assumption)
end
end
end
