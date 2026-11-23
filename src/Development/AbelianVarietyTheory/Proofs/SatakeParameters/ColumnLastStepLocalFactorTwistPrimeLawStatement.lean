module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.XiTopEqProd
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
public import Formalism.LocalToGlobal.Columns.XtPhiTopGCongr
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartFramesMulAdeleAtBadPrime
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
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.XiTopEqProd
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CouplingCosetRepresentativesCongrAtTwistPrimeStatement
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DatumPeriodicMulLatticeFinal
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntAtFormOfMemStdAt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepDatumLawK1DepthTwiceM
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepDatumTwistPrimeInvariantCongruentFrames
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BlkDetEqDB
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Data.Nat.Choose.Multinomial
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TopLevelDatumTransformAtTwistPrimeUnderLevelsStatement
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
import Formalism.LocalToGlobal.Columns.ChainInst
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.TopLawQ
import Mathlib.RingTheory.Coalgebra.CoassocSimps

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartFramesMulAdeleAtBadPrimeStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.chartFrames_mul_adele_at_badPrime : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
  ∀ (j : ℕ) (hj : j ≤ D.R.m) (β : (St j hj).Ch) (x x₁ : UA D j hj)
    (κ : GL (Fin (D.R.N j)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (p p₁ : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) j), x₁.1 = x.1 * κ →
    IsPtAd A a j hj β x p → IsPtAd A a j hj β x₁ p₁ →
    ∀ (P : SB t μ) (dep : SB t μ → ℕ) (g : Sp t.X.E (D.R.N j) ≃ₗ[t.X.E] Sp t.X.E (D.R.N j)),
      1 ≤ dep P → dep P ≤ (t.cst μ).D P → g ∈ GLint t.X.E (D.R.N j) P.1 →
      InFrame t.seam (A.fb j hj β) dep P κ g →
      (frsF t.sel (t.tup μ) p₁ P).trans ((frsF t.sel (t.tup μ) p P).symm.trans g.symm) ∈ GLint t.X.E (D.R.N j) P.1 ∧
      ∀ w ∈ stdAt t.X.E (D.R.N j) P.1, ((qOf P.1 : t.X.E) ^ dep P)⁻¹ •
        ((frsF t.sel (t.tup μ) p₁ P).trans ((frsF t.sel (t.tup μ) p P).symm.trans g.symm) w - w) ∈ stdAt t.X.E (D.R.N j) P.1) := by
  first | exact @GlobalTheory.FrameMove.frames_mul | exact GlobalTheory.FrameMove.frames_mul | (intros; apply GlobalTheory.FrameMove.frames_mul <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepDatumFixedCongruentFrameChangeTwistPrime

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TopStep GlobalTheory.TopLaw GlobalTheory.TopFrameQ

namespace GlobalTheory.TopFrameQM

section Main

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (cst : LocCst X (rowSG Pr sel mu))

theorem topDat_frames_qM {m2 : ℕ} (hm : R.m = m2 + 2) (hc : cst.Ok) (P : rowSG Pr sel mu) (hP : P.1 ∉ Pr.vGs)
    (hD : 2 * cst.M ≤ cst.D P)
    (κ : Sp X.E (R.N (m2 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1)))
    (κ' : Sp X.E (R.N (m2 + 1 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1 + 1)))
    (hκ : κ ∈ GLint X.E _ P.1)
    (hκc : ∀ w ∈ stdAt X.E _ P.1, ((qOf P.1 : X.E) ^ cst.D P)⁻¹ • (κ w - w) ∈ stdAt X.E _ P.1)
    (hκ' : κ' ∈ GLint X.E _ P.1)
    (hκ'c : ∀ w ∈ stdAt X.E _ P.1, ((qOf P.1 : X.E) ^ (2 * cst.M))⁻¹ • (κ' w - w) ∈ stdAt X.E _ P.1)
    (y : HomE X.E (R.N (m2 + 1)) (R.N (m2 + 1 + 1))) (y'' : Sp X.E (R.N (m2 + 1)))
    (hy'' : ∀ l, IntAt P.1 ((qOf P.1 : X.E) ^ cst.M * y'' l)) :
    topDat Ch sel mu cst (m2 + 1) P (κ'.symm.toLinearMap ∘ₗ y ∘ₗ κ.toLinearMap) (κ.symm y'') =
      topDat Ch sel mu cst (m2 + 1) P y y'' := by
  have hM1 : 1 ≤ cst.M := hc.M_pos
  have hMD : cst.M + 1 ≤ cst.D P := by omega
  have hMD' : cst.M + 1 ≤ 2 * cst.M := by omega
  have hq : (qOf P.1 : X.E) ≠ 0 := qOf_ne_zero
  have hκ's : κ'.symm ∈ GLint X.E _ P.1 := (GLint X.E _ P.1).inv_mem hκ'
  have hκs : κ.symm ∈ GLint X.E _ P.1 := (GLint X.E _ P.1).inv_mem hκ
  have hκ'sc := cong_symm hκ' hκ'c
  by_cases hg : ∀ j, abelian₂ P.1 (R.N (m2 + 1 + 1)) cst.M (y (Pi.single j 1))
  · unfold topDat
    congr 1
    · unfold PhiTopG
      rw [if_neg hP]
      have hc0 : cOf R (m2 + 1) = 0 := cOf_topB hm
      have hw : ∀ w ∈ stdAt X.E (R.N (m2 + 1)) P.1, ∀ l : Fin (R.N (m2 + 1 + 1)), l.1 + 1 < R.N (m2 + 1 + 1) →
          IntAt P.1 ((κ'.symm (y (κ w)) - y w) l / (qOf P.1 : X.E)) := by
        intro w hw l hl
        have hu := abelian₂.of_basis y hg (glint_mem (⟨κ, hκ⟩ : GLint X.E _ P.1) hw)
        have d1 := mem_stdAt.1 (abelian₂.move hκ's hκ'sc hMD' hu).2 l
        have e1 := intAt_inv_pow_le (a := 1) (by omega) d1
        have hu' : ((qOf P.1 : X.E) ^ cst.D P)⁻¹ • (κ w - w) ∈ stdAt X.E _ P.1 := hκc w hw
        have hyu := (abelian₂.of_basis y hg hu').2 l hl
        rw [map_smul, map_sub, Pi.smul_apply, smul_eq_mul] at hyu
        have e2 := intAt_inv_pow_le (a := 1) (by omega) hyu
        rw [pow_one] at e1 e2
        have e3 := e1.add e2
        rw [← add_div] at e3
        convert e3 using 2
        simp only [Pi.sub_apply]
        ring
      have key := fun z hz => GlobalTheory.TopInv.PhiQ_add (K := X.K) (GlobalTheory.TopInv.qOf_mem P.1) hq
        (resChar (mu : Chr X.F X.E X.K) P.1) R.k R.r (cOf R (m2 + 1)) (R.N (m2 + 1)) (R.N (m2 + 1 + 1) - 1) hc0
        (prXpG X.E (R.N (m2 + 1 + 1)) ∘ₗ y ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) z hz
      refine (congrArg _ (add_sub_cancel _ _)).symm.trans (key _ ?_)
      intro s l
      have hws : (LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1))) (Pi.single s (1 : X.E)) : Sp X.E _) ∈
          stdAt X.E (R.N (m2 + 1)) P.1 :=
        mem_stdAt.2 fun a => GlobalTheory.TopInv.single_int s (Fin.castAdd _ a)
      have := hw _ hws ⟨l.1, by omega⟩ (by show l.1 + 1 < _; omega)
      exact this
    · have h1 := ftY_comp_glint sel mu cst hc P (fun _ => hD) ⟨κ, hκ⟩
          (atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ κ'.symm.toLinearMap ∘ₗ y) y'' (κ.symm y'')
          (fun h => absurd h hP) (fun _ => hy'') (fun h => absurd h hP)
          (fun _ => by
            show ((qOf P.1 : X.E) ^ cst.M)⁻¹ • (κ (κ.symm y'') - y'') ∈ _
            rw [LinearEquiv.apply_symm_apply, sub_self, smul_zero]
            exact zero_mem _)
      refine h1.trans ?_
      have hy''s : ((qOf P.1 : X.E) ^ cst.M) • y'' ∈ stdAt X.E _ P.1 :=
        mem_stdAt.2 fun l => by simpa only [Pi.smul_apply, smul_eq_mul] using hy'' l
      have hδ : ∀ i, IntAt P.1 (((qOf P.1 : X.E) ^ cst.M)⁻¹ *
          ((atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ κ'.symm.toLinearMap ∘ₗ y) -
            atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ y) (Pi.single i 1)) := by
        intro i
        have d1 := mem_stdAt.1 (abelian₂.move hκ's hκ'sc (v := y (Pi.single i 1)) hMD' (hg i)).2
        have e1 : ∀ l, IntAt P.1 ((κ'.symm (y (Pi.single i 1)) - y (Pi.single i 1)) l / (qOf P.1 : X.E) ^ cst.M) :=
          fun l => intAt_inv_pow_le (by omega) (d1 l)
        have e2 := GlobalTheory.TopInv.atNL_int (R.N (m2 + 1 + 1) - 1) _ _ e1
        rw [inv_mul_eq_div]
        convert e2 using 2
        simp only [LinearMap.sub_apply, LinearMap.comp_apply, map_sub]
        rfl
      have h2 := GlobalTheory.ftY_pert_qM sel mu cst hc P hP hD (atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ y)
        _ y'' hδ hy''s
      rw [add_sub_cancel] at h2
      exact h2
  · have h0 : topDat Ch sel mu cst (m2 + 1) P y y'' = 0 := by
      by_contra hne
      exact hg (lam_of_topDat_ne Ch sel mu cst _ P hP y y'' hne)
    rw [h0]
    by_contra hne
    apply hg
    have h1 := lam_of_topDat_ne Ch sel mu cst _ P hP _ _ hne
    have h2 := lam_comp hκs hκ' hκ'c hMD' _ h1
    intro j
    have := h2 j
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using this

end Main

end GlobalTheory.TopFrameQM
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepDatumFixedCongruentFrameChangeTwistPrimeStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.lastStepDatum_fixed_congruentFrameChange_twistPrime : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (cst : LocCst X (rowSG Pr sel mu)) {m2 : ℕ}, R.m = m2 + 2 → cst.Ok → ∀ (P : rowSG Pr sel mu), P.1 ∉ Pr.vGs →
  2 * cst.M ≤ cst.D P →
  ∀ (κ : Sp X.E (R.N (m2 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1)))
    (κ' : Sp X.E (R.N (m2 + 1 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1 + 1))),
  κ ∈ GLint X.E (R.N (m2 + 1)) P.1 →
  (∀ w ∈ stdAt X.E (R.N (m2 + 1)) P.1, ((qOf P.1 : X.E) ^ cst.D P)⁻¹ • (κ w - w) ∈ stdAt X.E (R.N (m2 + 1)) P.1) →
  κ' ∈ GLint X.E (R.N (m2 + 1 + 1)) P.1 →
  (∀ w ∈ stdAt X.E (R.N (m2 + 1 + 1)) P.1, ((qOf P.1 : X.E) ^ (2 * cst.M))⁻¹ • (κ' w - w) ∈ stdAt X.E (R.N (m2 + 1 + 1)) P.1) →
  ∀ (y : HomE X.E (R.N (m2 + 1)) (R.N (m2 + 1 + 1))) (y'' : Sp X.E (R.N (m2 + 1))),
  (∀ l, IntAt P.1 ((qOf P.1 : X.E) ^ cst.M * y'' l)) →
  topDat Ch sel mu cst (m2 + 1) P (κ'.symm.toLinearMap ∘ₗ y ∘ₗ κ.toLinearMap) (κ.symm y'') =
    topDat Ch sel mu cst (m2 + 1) P y y'' := by
  intro X Pr R Ch sel S mu cst m2 hm hc P hP hD κ κ' hκ hκc hκ' hκ'c y y'' hy''
  exact GlobalTheory.TopFrameQM.topDat_frames_qM Ch sel mu cst hm hc P hP hD κ κ' hκ hκc hκ' hκ'c y y'' hy''
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.TopRankLevelMemIntegralGLAtTwistPrime

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TopLevInt

theorem mem_GLint_of_topLev : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (cst : LocCst X (rowSG Pr sel mu)) (j : ℕ) (P : rowSG Pr sel mu), P.1 ∉ Pr.vGs →
  ∀ (g : Sp X.E (R.N j) ≃ₗ[X.E] Sp X.E (R.N j)) (z : X.K), TopLev Ch sel mu cst j P g z → g ∈ GLint X.E (R.N j) P.1 := by
  intro X Pr R Ch sel S mu cst j P hP g z hT
  obtain ⟨g', hg', hpr, hat, -⟩ := hT
  unfold rowLevTop at hg'
  rw [if_neg hP] at hg'
  have hst : g' ∈ stabL X.E _ (stdAt X.E _ P.1) := (Subgroup.mem_inf.1 hg').1
  show ∀ x, g x ∈ stdAt X.E (R.N j) P.1 ↔ x ∈ stdAt X.E (R.N j) P.1
  intro x
  have h1 : prXpG X.E (R.N j) (g x) = g' (prXpG X.E (R.N j) x) := LinearMap.congr_fun hpr x
  have h2 : atNL X.E (R.N j) (R.N j - 1) (g x) = atNL X.E (R.N j) (R.N j - 1) x := LinearMap.congr_fun hat x
  have h3 := hst (prXpG X.E (R.N j) x)
  rw [ciMem_stdAt, ciMem_stdAt] at h3 ⊢
  rw [xt_split j (g x), xt_split j x, h1, h2, h3]

end GlobalTheory.TopLevInt
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.TopRankLevelMemIntegralGLAtTwistPrimeStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.topRankLevel_mem_integralGL_at_twist_prime : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (cst : LocCst X (rowSG Pr sel mu)) (j : ℕ) (P : rowSG Pr sel mu), P.1 ∉ Pr.vGs →
  ∀ (g : Sp X.E (R.N j) ≃ₗ[X.E] Sp X.E (R.N j)) (z : X.K), TopLev Ch sel mu cst j P g z → g ∈ GLint X.E (R.N j) P.1 := by
  first | exact @GlobalTheory.TopLevInt.mem_GLint_of_topLev | exact GlobalTheory.TopLevInt.mem_GLint_of_topLev | (intros; apply GlobalTheory.TopLevInt.mem_GLint_of_topLev <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ColumnLastStepLocalFactorTwistPrimeLaw

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.TwTopQ

theorem topF_eq {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) {u : Pr.Word} (i : ℕ) (P : rowSG Pr sel mu) (p : ChPt (R := R) sel mu u i) (Y : Set (Sp X.E (R.N i)))
    (p' : ChPt (R := R) sel mu u (i + 1)) (x : HomE X.E (R.N i) (R.N (i + 1))) :
  topF Ch sel mu cst i P p Y p' x = topDat Ch sel mu cst i P (inFr (frsF sel mu p P) (frsF sel mu p' P) x) ((frsF sel mu p P).symm (repY Y)) := rfl

theorem locq_twist : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
  ∀ (hi : t.m2 + 1 + 1 ≤ D.R.m) (β : (St (t.m2 + 1) (Nat.le_of_succ_le hi)).Ch) (β' : (St (t.m2 + 1 + 1) hi).Ch)
    (x x₁ : UA D (t.m2 + 1) (Nat.le_of_succ_le hi)) (x' x₁' : UA D (t.m2 + 1 + 1) hi)
    (κ : ((St (t.m2 + 1) (Nat.le_of_succ_le hi)).K β).lev.U) (κ' : ((St (t.m2 + 1 + 1) hi).K β').lev.U),
    x₁.1 = x.1 * κ.1 → x₁'.1 = x'.1 * κ'.1 →
    ∀ p p' p₁ p₁', IsPtAd A a (t.m2 + 1) (Nat.le_of_succ_le hi) β x p → IsPtAd A a (t.m2 + 1 + 1) hi β' x' p' →
      IsPtAd A a (t.m2 + 1) (Nat.le_of_succ_le hi) β x₁ p₁ → IsPtAd A a (t.m2 + 1 + 1) hi β' x₁' p₁' →
    ∀ (P : SB t μ), P.1 ∉ t.Pr.vGs → ∀ g z g' z', A.cplRel β P g z →
      InFrame t.seam (A.fb (t.m2 + 1) (Nat.le_of_succ_le hi) β) (t.cst μ).D P κ.1 g →
      TopLev t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1 + 1) P g' z' →
      InFrame t.seam (A.fb (t.m2 + 1 + 1) hi β') (topDep t.sel (t.tup μ) (t.cst μ)) P κ'.1 g' →
    ∀ Z, z' * topF t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P p₁ (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p₁) p₁' Z *
        rhoS t.Ch t.sel (t.tup μ) (t.m2 + 1) P ((LinearEquiv.det g : t.X.Eˣ) : t.X.E) *
        rhoT t.Ch t.sel (t.tup μ) (t.m2 + 1) P ((LinearEquiv.det g' : t.X.Eˣ) : t.X.E) =
      z * topF t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P p (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p) p' Z) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPin hTie hi β β' x x₁ x' x₁' κ κ' hx hx' p p' p₁ p₁' hp hp' hp₁ hp₁' P hP g z g' z' hcpl hfr htop hfr' Z
  have hok := t.idx_ok μ
  have hc := hok.cst_ok
  have hD := hok.depthQ P hP
  have hM := hc.M_pos
  have hX : t.X.Ok := hPin.fields.ok
  have hU := qUnif_of t.sel (t.tup μ) hX t.pr_ok hPin.sel
  have hgI : g ∈ GLint t.X.E _ P.1 :=
    hok.int (t.m2 + 1) (A.ib (t.m2 + 1) (cpl_lt t μ) β) P ((exists_midLev_iff _ _ _ _ _ _ _ _).1 ⟨z, hcpl.1⟩)
  have hg'I : g' ∈ GLint t.X.E _ P.1 := GlobalTheory.T.topRankLevel_mem_integralGL_at_twist_prime _ _ _ _ _ P hP g' z' htop
  have hdep : topDep t.sel (t.tup μ) (t.cst μ) P = 2 * (t.cst μ).M := if_neg hP
  obtain ⟨hk, hkc⟩ := GlobalTheory.T.chartFrames_mul_adele_at_badPrime A dtU a hPin hTie (t.m2 + 1) (Nat.le_of_succ_le hi) β x x₁ κ.1 p p₁ hx hp hp₁ P (t.cst μ).D g
    (hc.D_pos P) le_rfl hgI hfr
  obtain ⟨hk', hkc'⟩ := GlobalTheory.T.chartFrames_mul_adele_at_badPrime A dtU a hPin hTie (t.m2 + 1 + 1) hi β' x' x₁' κ'.1 p' p₁' hx' hp' hp₁' P
    (topDep t.sel (t.tup μ) (t.cst μ)) g' (by rw [hdep]; omega) (by rw [hdep]; exact hD) hg'I hfr'
  rw [hdep] at hkc'
  have hy0 : y0At A (t.m2 + 1) (Nat.le_of_succ_le hi) β P = A.y0 β P := by
    unfold y0At
    rw [dite_eq_left rfl]
  obtain ⟨hW0, hV1, hW⟩ := GlobalTheory.T.couplingCoset_representatives_congr_at_twistPrime A dtU a hPin hTie (Nat.le_of_succ_le hi) β P hP p p₁ g
    ((frsF t.sel (t.tup μ) p₁ P).trans ((frsF t.sel (t.tup μ) p P).symm.trans g.symm)) hgI (by rw [hy0]; exact hcpl.2) hk hkc
    (fun w => by simp)
  rw [topF_eq, topF_eq]
  have e1 : inFr (frsF t.sel (t.tup μ) p₁ P) (frsF t.sel (t.tup μ) p₁' P) Z =
      ((frsF t.sel (t.tup μ) p₁' P).trans ((frsF t.sel (t.tup μ) p' P).symm.trans g'.symm)).symm.toLinearMap ∘ₗ
        (g'.symm.toLinearMap ∘ₗ inFr (frsF t.sel (t.tup μ) p P) (frsF t.sel (t.tup μ) p' P) Z ∘ₗ g.toLinearMap) ∘ₗ
        ((frsF t.sel (t.tup μ) p₁ P).trans ((frsF t.sel (t.tup μ) p P).symm.trans g.symm)).toLinearMap := by
    refine LinearMap.ext fun w => ?_
    simp [inFr, LinearEquiv.trans_symm]
  have e2 : (frsF t.sel (t.tup μ) p₁ P).symm (repY (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p₁)) =
      ((frsF t.sel (t.tup μ) p₁ P).trans ((frsF t.sel (t.tup μ) p P).symm.trans g.symm)).symm
        (g.symm ((frsF t.sel (t.tup μ) p P).symm (repY (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p₁)))) := by
    simp [LinearEquiv.trans_symm]
  have hy'' : ∀ l, IntAt P.1 (((qOf P.1 : t.X.E) ^ (t.cst μ).M) *
      g.symm ((frsF t.sel (t.tup μ) p P).symm (repY (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p₁))) l) := by
    have h1 := (hk _).2 hV1
    rw [map_smul] at h1
    have e3 : ((frsF t.sel (t.tup μ) p₁ P).trans ((frsF t.sel (t.tup μ) p P).symm.trans g.symm))
        ((frsF t.sel (t.tup μ) p₁ P).symm (repY (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p₁))) =
        g.symm ((frsF t.sel (t.tup μ) p P).symm (repY (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p₁))) := by
      simp
    rw [e3] at h1
    intro l
    simpa using (ciMem_stdAt _ _).1 h1 l
  rw [e1, e2, GlobalTheory.T.lastStepDatum_fixed_congruentFrameChange_twistPrime t.Ch t.sel (t.tup μ) (t.cst μ) (m_eq t μ) hc P hP hD _ _ hk hkc hk' hkc' _ _ hy'']
  exact GlobalTheory.T.topLevelDatum_transform_at_twist_prime_under_levels t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) hok hU (A.ib (t.m2 + 1) (cpl_lt t μ) β) P hP g z hcpl.1 g' z' htop _ _ _ hW hW0

end GlobalTheory.TwTopQ
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ColumnLastStepLocalFactorTwistPrimeLawStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.columnLastStep_localFactor_twist_prime_law : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
  ∀ (hi : t.m2 + 1 + 1 ≤ D.R.m) (β : (St (t.m2 + 1) (Nat.le_of_succ_le hi)).Ch) (β' : (St (t.m2 + 1 + 1) hi).Ch)
    (x x₁ : UA D (t.m2 + 1) (Nat.le_of_succ_le hi)) (x' x₁' : UA D (t.m2 + 1 + 1) hi)
    (κ : ((St (t.m2 + 1) (Nat.le_of_succ_le hi)).K β).lev.U) (κ' : ((St (t.m2 + 1 + 1) hi).K β').lev.U),
    x₁.1 = x.1 * κ.1 → x₁'.1 = x'.1 * κ'.1 →
    ∀ p p' p₁ p₁', IsPtAd A a (t.m2 + 1) (Nat.le_of_succ_le hi) β x p → IsPtAd A a (t.m2 + 1 + 1) hi β' x' p' →
      IsPtAd A a (t.m2 + 1) (Nat.le_of_succ_le hi) β x₁ p₁ → IsPtAd A a (t.m2 + 1 + 1) hi β' x₁' p₁' →
    ∀ (P : SB t μ), P.1 ∉ t.Pr.vGs → ∀ g z g' z', A.cplRel β P g z →
      InFrame t.seam (A.fb (t.m2 + 1) (Nat.le_of_succ_le hi) β) (t.cst μ).D P κ.1 g →
      TopLev t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1 + 1) P g' z' →
      InFrame t.seam (A.fb (t.m2 + 1 + 1) hi β') (topDep t.sel (t.tup μ) (t.cst μ)) P κ'.1 g' →
    ∀ Z, z' * topF t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P p₁ (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p₁) p₁' Z *
        rhoS t.Ch t.sel (t.tup μ) (t.m2 + 1) P ((LinearEquiv.det g : t.X.Eˣ) : t.X.E) *
        rhoT t.Ch t.sel (t.tup μ) (t.m2 + 1) P ((LinearEquiv.det g' : t.X.Eˣ) : t.X.E) =
      z * topF t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P p (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p) p' Z) := by
  first | exact @GlobalTheory.TwTopQ.locq_twist | exact GlobalTheory.TwTopQ.locq_twist | (intros; apply GlobalTheory.TwTopQ.locq_twist <;> assumption)
end
end
