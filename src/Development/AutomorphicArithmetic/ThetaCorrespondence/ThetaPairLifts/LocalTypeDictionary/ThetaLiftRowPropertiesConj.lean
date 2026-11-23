module

public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.StepUnfold
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestRationalSumsOfFiniteSumsMeaningfulStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ConstK
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.RowSumOfHyp
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaPairLiftCuspidalOfHypotheses
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodCorankConvergesColumnStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedBaseChangeLiftExists
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedJetSuccEqAssembly
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedLiftFlipInvariant
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HcFiniteAndSchurMult
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ActEqTranslate
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftSchurMultiplierCompatibility
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedThetaIntegralUnfolding

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestLiftFormulaPrincipalLevel

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames

namespace GlobalTheory.RowClaim.FormulaTwo

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

variable {D : D7} {T : Type}

theorem mem_xiVals {L : LevCh D T} {t : T} {n : ℕ} (hn : (L.xiH t).OrderDvd n) (hL : LocIn D.what₂.embLL (L.xiH t))
    {z : ℂˣ} (hz : z ∈ xiVals L t) : z ^ n = 1 ∧ (z : ℂ) ∈ Set.range D.what₂.embLL := by
  induction hz using Subgroup.closure_induction with
  | mem z hz =>
    obtain ⟨w, x, rfl⟩ := hz
    refine ⟨?_, hL w x⟩
    have : ((L.xiH t) ^ n).loc w x = 1 := by rw [show (L.xiH t) ^ n = 1 from hn]; rfl
    exact this
  | one => exact ⟨one_pow _, 1, by simp⟩
  | mul a b _ _ ha hb =>
    obtain ⟨x, hx⟩ := ha.2
    obtain ⟨y, hy⟩ := hb.2
    exact ⟨by rw [mul_pow, ha.1, hb.1, one_mul], x * y, by simp [hx, hy]⟩
  | inv a _ ha =>
    obtain ⟨x, hx⟩ := ha.2
    exact ⟨by rw [inv_pow, ha.1, inv_one], x⁻¹, by simp [hx]⟩

theorem Bplus_smul_form {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G) (c : ℂ) (φ : Fn G (.top 0))
    (F : Fn G (.grid D.R.m 0)) : Bplus W M φ (c • F) = c * Bplus W M φ F := by
  simpa using Bplus_smul W M 1 c φ F

theorem scalar_calc {e z z' c p b s u κ v w : ℂ} (he : e = z * z') (hz : z ≠ 0) (hz' : z' ≠ 0) (hc : c ≠ 0)
    (h1 : p = (z * c)⁻¹ * b) (h2 : b = z'⁻¹ * s * u) (h3 : u = κ * v) (h4 : w = s * v) : e * c * p = κ * w := by
  subst he h1 h2 h3 h4
  field_simp

variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}



theorem formulaAt_steps (hL : R.toLevCh.Is A.μ0) (hC : R.IsChain) (ch : Choice R) (hP : ProjAt ch) (hF : FlipAt ch)
    (hU : UnfoldAt ch) (hJ : JetsAt ch) (hc : ∀ i j t, ch.c i j t ≠ 0) (hS : ∀ t a, ch.S.SumOK t (ch.Phi a))
    (hK : ch.FieldOK) : ∃ κ ze, FormulaAt ch κ ze := by
  obtain ⟨τi, z, hF⟩ := hF
  obtain ⟨σ, z', hU⟩ := hU τi
  obtain ⟨hM, hJ⟩ := hJ
  obtain ⟨κ, hJ⟩ := hJ σ
  have key : ∀ t, ∃ e : D.what₂.LL, D.what₂.embLL e = (z t : ℂ) * z' t ∧ ∃ n : ℕ, 0 < n ∧ e ^ n = 1 := fun t => by
    obtain ⟨n, hn, ho⟩ := hL.xi_fin t
    obtain ⟨h1, e, he⟩ := mem_xiVals ho (hK.chars.xi t) (mul_mem (hF t).1 (hU t).1)
    refine ⟨e, he, n, hn, D.what₂.embLL.injective ?_⟩
    rw [map_pow, he, map_one, ← Units.val_pow_eq_pow_val, h1, Units.val_one]
  choose ze hze hzn using key
  refine ⟨κ, ze, hzn, fun t x hx a => ?_⟩
  obtain ⟨τ, hτ, hfl⟩ := (hF t).2 (ch.Phi a)
  obtain ⟨M, hMt⟩ := exists_vol ch.G hL t
  choose Mβ hMβ using hM t (ch.Phi a)
  have hex : ∀ β ∈ ch.S.supp t (ch.Phi a), ch.S.IsExpansion t (ch.Phi a) β
      (Classical.epsilon (ch.S.IsExpansion t (ch.Phi a) β)) := fun β hβ => Classical.epsilon_spec ((hS t a).ex β hβ)
  have e1 : psiK ch a (R.Th t (R.jX t x)) =
      Bplus ch.W ch.M (colFn ch a) (thetaChi ch.W ch.M ch.ρ (ch.Phi a) (ch.cv.lift t (R.jX t x))) := by
    exact congrArg (fun u => Bplus ch.W ch.M (colFn ch a) (thetaChi ch.W ch.M ch.ρ (ch.Phi a) u))
      ((form_Th ch hC t _).trans (hP t x hx))
  have e2 := (hU t).2 a τ hτ M hMt Mβ (fun β => Classical.epsilon (ch.S.IsExpansion t (ch.Phi a) β))
    (fun β hβ => ⟨hMβ β, hex β hβ⟩) (R.jX t x)
  have e3 : (∑ᶠ β ∈ ch.S.supp t (ch.Phi a), (∏ w, ((ch.S.term t (ch.Phi a) β w).coef : ℂ)) *
      defTot t ch.S.toGridChoice (Mβ β) σ (Classical.epsilon (ch.S.IsExpansion t (ch.Phi a) β)) (colFn ch a)
        (formTop ch t (R.jX t x))) = κ * ch.S.vCore t (ch.Phi a) (psiC (ch.Psi a)) (ch.S.formC t (R.jX t x)) := by
    rw [(hS t a).vCore_eq _ hex, finsum_mem_eq_finite_toFinset_sum _ (hS t a).fin, Finset.mul_sum]
    refine Finset.sum_congr rfl fun β hβ => ?_
    have hβ' := (Set.Finite.mem_toFinset _).1 hβ
    exact (congrArg (HMul.hMul _) (hJ t a β hβ' (Mβ β) _ (hMβ β) (hex β hβ') (R.jX t x))).trans (mul_left_comm _ _ _)
  have e4 : vK ch t x a = ch.S.sAA * ch.S.vCore t (ch.Phi a) (psiC (ch.Psi a)) (ch.S.formC t (R.jX t x)) := rfl
  have hct : cTot ch t ≠ 0 := (cTot_ne_zero_iff ch t).2 fun i j => hc i j t
  have e5 := congrArg (Bplus ch.W ch.M (colFn ch a)) (hfl M hMt (R.jX t x)).2
  exact scalar_calc (hze t) (z t).ne_zero (z' t).ne_zero hct (e1.trans (e5.trans (Bplus_smul_form _ _ _ _ _))) e2 e3 e4

theorem formula2K (hP : StepProj) (hF : StepFlip) (hU : StepUnfold) (hJ : StepJets) (hc : ConstK) (hS : SumOKK) :
    Formula2K := by
  obtain ⟨C0, H⟩ := ((((hP.and hF).and hU).and hJ).and hc).and hS
  refine ⟨C0, fun ε CF h => ?_⟩
  obtain ⟨x₀, H⟩ := H ε CF h
  refine ⟨x₀, fun D large₂ e hx Γ _ _ Pl0 T A Ks _ _ _ R F s ch i j hK => ?_⟩
  obtain ⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, f⟩, g⟩ := H D large₂ e hx Γ Pl0 T A Ks R F s ch i j
  exact formulaAt_steps s.core.lev s.core.chain ch a b c d (fun i j t => (f i j t).2) g hK

end GlobalTheory.RowClaim.FormulaTwo

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestLiftFormulaPrincipalLevelStatement

section

@[expose] public section

open GlobalTheory.RowClaim

theorem _root_.GlobalTheory.T.rowTestLiftFormula_principalLevel : StepProj → StepFlip → StepUnfold → StepJets → ConstK → SumOKK → Formula2K := by
  first | exact @GlobalTheory.RowClaim.FormulaTwo.formula2K | exact GlobalTheory.RowClaim.FormulaTwo.formula2K | (intros; apply GlobalTheory.RowClaim.FormulaTwo.formula2K <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedThetaLiftAutomorphicOfConvergent

section

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory
theorem twisted_theta_lift_automorphic_of_convergent : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → ∀ {D : D7} (large₂ : SizeData₂ D)
    {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A},
    HidaSetting large₂ R F → ∀ (ch : Choice R), ch.Is → ∀ (CF : ℝ), ch.AtScale CF large₂.sc.b → ∀ (a : Fin ch.n) (u : R.HE.H),
    ThetaConv ch.W ch.M ch.ρ (ch.Phi a) (ch.form u) ∧
      IsAutFun (ch.G.V (.grid D.R.m 0)) (thetaChi ch.W ch.M ch.ρ (ch.Phi a) (ch.form u)) :=
  fun hP hL _ large₂ _ _ _ _ _ _ _ _ _ _ _ _ hS ch hch CF hsc a u => _root_.GlobalTheory.T.twisted_base_change_lift_exists hP hL large₂ hS ch hch.toIsBase CF hsc a u
end GlobalTheory
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.twisted_theta_lift_automorphic : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → ∀ {D : D7} (large₂ : SizeData₂ D)
    {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A},
    HidaSetting large₂ R F → ∀ (ch : Choice R), ch.Is → ∀ (CF : ℝ), ch.AtScale CF large₂.sc.b → ∀ (a : Fin ch.n) (u : R.HE.H),
    ThetaConv ch.W ch.M ch.ρ (ch.Phi a) (ch.form u) ∧
      IsAutFun (ch.G.V (.grid D.R.m 0)) (thetaChi ch.W ch.M ch.ρ (ch.Phi a) (ch.form u)) := by
  first | exact @_root_.GlobalTheory.twisted_theta_lift_automorphic_of_convergent | exact _root_.GlobalTheory.twisted_theta_lift_automorphic_of_convergent | (intros; apply _root_.GlobalTheory.twisted_theta_lift_automorphic_of_convergent <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedCharactersLinearlyIndependent

section

@[expose] public section

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim MeasureTheory
namespace GlobalTheory.RowTest
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem twist_linear_independence_test (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hL : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal) : GlobalTheory.RowClaim.LinK := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hch hsc a u => ?_⟩⟩
  obtain ⟨h1, h2⟩ := _root_.GlobalTheory.T.twisted_theta_lift_automorphic hP hL large₂ hS ch hch CF hsc a u
  exact ⟨h1, GlobalTheory.T.besselPeriodCorank_converges_column ch.W ch.M hch.vol ch.ξ _ (col_mem ch a) _ h2⟩
end GlobalTheory.RowTest
end
end

section

theorem _root_.GlobalTheory.T.twisted_characters_linearly_independent : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.RowClaim.LinK := by
  first | exact @_root_.GlobalTheory.RowTest.twist_linear_independence_test | exact _root_.GlobalTheory.RowTest.twist_linear_independence_test | (intros; apply _root_.GlobalTheory.RowTest.twist_linear_independence_test <;> assumption)
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProjectionOfFunctorialityAdopted

section

@[expose] public section

namespace ThetaProjectionIdempotent
section
open GlobalTheory.RowClaim

namespace CompanionTheory.Member.ThetaDownProjection

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
open GlobalTheory.ChainEquiv
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks]
  [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}

theorem thDn_act (hP : GlobalTheory.Published.CuspRapidDecay) (hC : GlobalTheory.Hk3.Core R F) (t : T0) (g : G) (x : (A.fam.R t).S.Forms)
    (v : SmT (R.MY 0)) :
    R.thDn t (R.jX t ((A.fam.R t).r g x)) v = actL _ (R.βY 0) (R.dat0 R.triv) (R.eG g) (R.thDn t (R.jX t x) v) := by
  have hS : ∀ t j, j < D.R.m → SchurMult R.θ (R.MY j) (levS _ (R.βY j) (R.datYt t j R.triv))
      (levChi _ (R.βY j) (R.datYt t j R.triv)) (R.νY t j) (R.fdY t j) :=
    fun t j _ => @GlobalTheory.MultFinite.schurMult D R.θ _ _ (R.MY j) (levS _ (R.βY j) (R.datYt t j R.triv))
      (levChi _ (R.βY j) (R.datYt t j R.triv)) hP (R.νY t j) (R.fdY t j)
  refine (GlobalTheory.FormAction.act_eq_translate R hC.grp.red_R hC.models.jX t g x).elim fun κ hκ => ?_
  have hrel : Rel R t (R.eG g) 0 (thCC t (R.jX t x)) (thCC t (R.jX t ((A.fam.R t).r g x))) :=
    rel_dnFrom hC.lev hC.models.inf hC.models.νY hC.models.νY' hC.chain hS t (R.eG g) (D.R.m - 1)
      (by have := D.R.two_le_m; omega) _ _
      (rel_ioX hC.lev hC.models.inf hC.models.νY hC.models.νY' hC.chain hC.models.νX hC.models.cX hC.models.HX hS t
        (R.eG g) κ hκ.1 _ _ hκ.2)
  exact act_of_rel hC.lev t _ _ _ hrel v

theorem sum_act {K V H M W G : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup H] [Module ℂ H]
    [AddCommGroup M] [Module ℂ M] [AddCommGroup W] [Module ℂ W] [Fintype G] {σ : K →+* ℂ} (j : V →ₛₗ[σ] H)
    (Θ : H →ₗ[ℂ] M →ₗ[ℂ] W) (r : G → Module.End K V) (a : G → W →ₗ[ℂ] W) (c : G → K) (x : V) (v : M)
    (h : ∀ g, Θ (j (r g x)) v = a g (Θ (j x) v)) :
    Θ (j ((∑ g, c g • r g) x)) v = (∑ g, σ (c g) • a g) (Θ (j x) v) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smulₛₗ, RingHom.id_apply, h]

theorem heckeProjector_fixes_heckeEigenVector (hC : GlobalTheory.Hk3.Core R F) (y : R.HE.H) (f : (R.MY 0).Vec) : R.e0 (R.HE.e y f) = R.HE.e y f := by
  have h1 : R.HE.e y ∈ R.EEat R.triv := by
    rw [← hC.models.HE.2.1]
    exact LinearMap.mem_range_self _ y
  have h2 : postOn (R.MY 0) R.e0 (R.HE.e y) - R.HE.e y = 0 := h1.2
  have h3 := congrArg (fun u : MMap (R.MY 0) => u f) (sub_eq_zero.1 h2)
  exact (postOn_apply _ _ _ _).symm.trans h3

theorem idem_ind {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (e : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ))
    (u : SmT M →ₗ[ℂ] (GA D V → ℂ))
    (h : ∀ f : M.Vec, e (e (u (PiTensorProduct.tprod ℂ f))) = e (u (PiTensorProduct.tprod ℂ f))) (v : SmT M) :
    e (e (u v)) = e (u v) := by
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r f => rw [map_smul, map_smul, map_smul]; exact congrArg (fun z => r • z) (h f)
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), map_add (f := _), ha, hb]


set_option maxHeartbeats 1000000 in
theorem heckeProjector_idempotent_compositeLift (hC : GlobalTheory.Hk3.Core R F) (t : T0) (y : (R.HX t).H) (v : SmT (R.MY 0)) :
    R.e0 (R.e0 (R.thDn t y v)) = R.e0 (R.thDn t y v) := by
  rw [thDn_eq]
  refine idem_ind (R.MY 0) R.e0 _ (fun f => ?_) v
  have h5 := e_Th hC.chain.Th t y f
  exact (congrArg R.e0 h5).symm.trans ((heckeProjector_fixes_heckeEigenVector hC (R.Th t y) f).trans h5)

set_option maxHeartbeats 1000000 in
theorem proj_thDn (hP : GlobalTheory.Published.CuspRapidDecay) (hC : GlobalTheory.Hk3.Core R F) (t : T0) (x : A.fam.amb.FR t)
    (hx : x ∈ (A.fam.R t).goodF A.fam.X) (v : SmT (R.MY 0)) :
    R.e0 (R.thDn t (R.jX t x) v) = R.thDn t (R.jX t x) v := by
  obtain ⟨y, hy⟩ := hx
  rw [goodAt, level_idempotent_bot, mul_one] at hy
  have h : R.thDn t (R.jX t x) v = R.e0 (R.thDn t (R.jX t y) v) := by
    rw [← hy]
    exact sum_act (R.jX t) (R.thDn t) (fun g => (A.fam.R t).r g) _ (fun g => (idemOf A.X).coeff g) y v
      fun g => thDn_act hP hC t g y v
  rw [h]
  exact heckeProjector_idempotent_compositeLift hC t _ v

end CompanionTheory.Member.ThetaDownProjection

end

end ThetaProjectionIdempotent
section
open GlobalTheory.RowClaim

end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedPeriodIdentityLocal

section

@[expose] public section

section
namespace ThetaProjectionIdempotent
section
open GlobalTheory.RowClaim
namespace CompanionTheory.Member.ThetaDownProjection
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
open GlobalTheory.ChainEquiv
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks]
  [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}
end CompanionTheory.Member.ThetaDownProjection
theorem CompanionTheory.Member.twisted_period_identity_local : _root_.GlobalTheory.FunPr.ThetaLocalInputs → StepProj := by
  intro hP
  refine ⟨0, fun ε CF _ => ⟨0, ?_⟩⟩
  intro D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch _ _ t x hx
  rw [← ch.cv.thDn_w s.core.chain]
  exact CompanionTheory.Member.ThetaDownProjection.proj_thDn hP.cuspRapidDecay s.core t x hx _
end
end ThetaProjectionIdempotent
section
open GlobalTheory.RowClaim
theorem _root_.GlobalTheory.Adopt.twisted_period_identity : _root_.GlobalTheory.FunPr.ThetaLocalInputs → StepProj := by
  first | exact @_root_.ThetaProjectionIdempotent.CompanionTheory.Member.twisted_period_identity_local | exact _root_.ThetaProjectionIdempotent.CompanionTheory.Member.twisted_period_identity_local | (intros; apply _root_.ThetaProjectionIdempotent.CompanionTheory.Member.twisted_period_identity_local <;> assumption)
end
end

section
open GlobalTheory.RowClaim

theorem _root_.GlobalTheory.T.twisted_period_identity : _root_.GlobalTheory.FunPr.ThetaLocalInputs → StepProj := by
  first | exact @_root_.GlobalTheory.Adopt.twisted_period_identity | exact _root_.GlobalTheory.Adopt.twisted_period_identity | (intros; apply _root_.GlobalTheory.Adopt.twisted_period_identity <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaLiftRowPropertiesConj

section

@[expose] public section

section
namespace GlobalTheory.RowClaim.Join
theorem thetaLift_row_properties_conj : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GlobalTheory.SquareSt.WeilConvergence → GlobalTheory.SquareSt.LocalMatching → GlobalTheory.SquareSt.ThetaIntegralsAgree → GlobalTheory.RowClaim.SumOKK ∧ GlobalTheory.RowClaim.ConstK ∧ GlobalTheory.RowClaim.LinK ∧ GlobalTheory.RowClaim.Formula2K ∧ GlobalTheory.RowClaim.SumRatK := by
  intro P K L s1 s2 s3
  have c := _root_.GlobalTheory.ConstNZ.constK_alt P K L s1 s2 s3
  have cusp := _root_.GlobalTheory.T.twisted_thetaLift_cuspidal P
  have sum := _root_.GlobalTheory.T.sumOKK_of_theta_local_inputs P
  exact ⟨sum, c, _root_.GlobalTheory.T.twisted_characters_linearly_independent P cusp,
    GlobalTheory.T.rowTestLiftFormula_principalLevel (_root_.GlobalTheory.T.twisted_period_identity P) (_root_.GlobalTheory.T.twisted_lift_flip_invariant P cusp s1 K c) (_root_.GlobalTheory.T.twisted_theta_integral_unfolds P cusp sum)
      (_root_.GlobalTheory.T.twisted_jets_assemble P sum) c sum,
    GlobalTheory.T.rowTestRationalSums_of_finiteSumsMeaningful sum⟩
end GlobalTheory.RowClaim.Join
end

section

theorem _root_.GlobalTheory.T.thetaLift_row_properties : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GlobalTheory.SquareSt.WeilConvergence → GlobalTheory.SquareSt.LocalMatching → GlobalTheory.SquareSt.ThetaIntegralsAgree → GlobalTheory.RowClaim.SumOKK ∧ GlobalTheory.RowClaim.ConstK ∧ GlobalTheory.RowClaim.LinK ∧ GlobalTheory.RowClaim.Formula2K ∧ GlobalTheory.RowClaim.SumRatK := by
  first | exact @_root_.GlobalTheory.RowClaim.Join.thetaLift_row_properties_conj | exact _root_.GlobalTheory.RowClaim.Join.thetaLift_row_properties_conj | (intros; apply _root_.GlobalTheory.RowClaim.Join.thetaLift_row_properties_conj <;> assumption)
end
end
end
