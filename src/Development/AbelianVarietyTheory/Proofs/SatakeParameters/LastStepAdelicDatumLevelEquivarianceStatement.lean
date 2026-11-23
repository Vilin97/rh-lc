module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.XiTopEqProd
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicLatAtRep
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartFunctionalEqOfAgreeBadPlacesAllSteps
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointRightTranslateByLevelCoupledStep
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatAdXMulLev
import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocBases
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.XiTopEqProd
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ColumnLastStepLocalFactorTwistPrimeLawStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepCharacterAtLevelDetMulLocalCharactersStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepLocalFactorLevelValuesTypePrime

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartDatumLevelPrimeInvariantMulLevel

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.PhiTLev



theorem deco_mul_lev : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    ∀ (j : ℕ) (hj : j ≤ D.R.m) (β : (St j hj).Ch) (x x₁ : UA D j hj) (κ : ((St j hj).K β).lev.U) p p₁,
      x₁.1 = x.1 * κ.1 → IsPtAd A a j hj β x p → IsPtAd A a j hj β x₁ p₁ →
      p₁.deco.1.N = p.deco.1.N ∧ ∀ P : t.Pr.vT (t.word u), ∀ y ∈ p.deco.1.at P.1, p₁.deco.1.f P y = p.deco.1.f P y) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a _hPins hTie j hj β x x₁ κ p p₁ hx hp hp₁
  have hL : latCo D.sp (gramN D j hj) (A.crd j hj) a x₁.1 ((St j hj).K β).lev.Lb =
      latCo D.sp (gramN D j hj) (A.crd j hj) a x.1 ((St j hj).K β).lev.Lb := by
    unfold latCo
    rw [hx, Formalism.MainNotions.G.KAat.latAd_stab _ _ _ (hatStab_of_lev _ κ)]
  have hN : p₁.deco.1.N = p.deco.1.N := by
    have h := congrArg (latBack t.seam) ((hp₁.lat.trans hL).trans hp.lat.symm)
    rwa [latBack_seam_lat, latBack_seam_lat] at h
  refine ⟨hN, fun P => ?_⟩
  obtain ⟨v, hov, hTv, -⟩ := FnlAwayCpl.exists_place hTie P
  have hat : p₁.deco.1.at P.1 = p.deco.1.at P.1 := by
    show Formalism.HermitianLatticesTheory.localization₂ _ p₁.deco.1.N = Formalism.HermitianLatticesTheory.localization₂ _ p.deco.1.N
    rw [hN]
  refine FnlAwayCpl.f_eq_on_at p.deco.2 p₁.deco.2 P hat fun w hw hw₁ => ?_
  have H := GlobalTheory.CplPt.funMoved_mul_lev t.seam _ P v (hTv j hj) _ _ _ κ (hp.fnl P v (hTv j hj) hov)
  have e : ratA D.host.F (A.crd j hj) * x₁.1 = ratA D.host.F (A.crd j hj) * x.1 * κ.1 := by
    rw [hx, mul_assoc]
  rw [← e] at H
  have hu₁ : (fun l => t.seam.iE (w l)) ∈ latCo D.sp (gramN D j hj) (A.crd j hj) a x₁.1 ((St j hj).K β).lev.Lb := by
    rw [← hp₁.lat]
    exact Submodule.subset_span ⟨w, hw₁, rfl⟩
  obtain ⟨z, hz⟩ := FnlAwayCpl.exists_latS_pullV D.sp (gramN D j hj) (A.crd j hj) a x₁.1 x₁.2
    (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_gramN_det D j hj) ((St j hj).K β).lev.Lb ((St j hj).K β).lev.Lb_fin
    ((St j hj).K β).lev.Lb_span ((St j hj).K β).lev.Lb_int v _ hu₁
  rw [hp₁.fnl P v (hTv j hj) hov w hw₁ z hz, H w hw z hz]



theorem phiT_mul_lev : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
  ∀ (i : ℕ) (hi : i + 1 ≤ D.R.m) (β : (St i (Nat.le_of_succ_le hi)).Ch) (β' : (St (i + 1) hi).Ch)
    (x x₁ : UA D i (Nat.le_of_succ_le hi)) (x' x₁' : UA D (i + 1) hi)
    (κ : ((St i (Nat.le_of_succ_le hi)).K β).lev.U) (κ' : ((St (i + 1) hi).K β').lev.U),
    x₁.1 = x.1 * κ.1 → x₁'.1 = x'.1 * κ'.1 →
    ∀ p p' p₁ p₁', IsPtAd A a i (Nat.le_of_succ_le hi) β x p → IsPtAd A a (i + 1) hi β' x' p' →
      IsPtAd A a i (Nat.le_of_succ_le hi) β x₁ p₁ → IsPtAd A a (i + 1) hi β' x₁' p₁' →
      ∀ z, phiT t.X.K p₁.deco.1 p₁'.deco.1 z = phiT t.X.K p.deco.1 p'.deco.1 z) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPins hTie i hi β β' x x₁ x' x₁' κ κ' hx hx' p p' p₁ p₁' hp hp' hp₁ hp₁' z
  obtain ⟨hN, hf⟩ := deco_mul_lev A dtU a hPins hTie i (Nat.le_of_succ_le hi) β x x₁ κ p p₁ hx hp hp₁
  obtain ⟨hN', hf'⟩ := deco_mul_lev A dtU a hPins hTie (i + 1) hi β' x' x₁' κ' p' p₁' hx' hp' hp₁'
  unfold phiT
  refine @if_congr _ _ _ (_) (_) _ _ _ _ ?_ rfl rfl
  refine forall_congr' fun P => ?_
  simp only [Deco.at, hN, hN']
  refine forall₂_congr fun y hy => and_congr_right fun hzy => ?_
  rw [hf P y hy, hf' P (z y) hzy]

end GlobalTheory.TwV.PhiTLev
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartDatumLevelPrimeInvariantMulLevelStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.chartDatum_levelPrime_invariant_mul_level : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
  ∀ (i : ℕ) (hi : i + 1 ≤ D.R.m) (β : (St i (Nat.le_of_succ_le hi)).Ch) (β' : (St (i + 1) hi).Ch)
    (x x₁ : UA D i (Nat.le_of_succ_le hi)) (x' x₁' : UA D (i + 1) hi)
    (κ : ((St i (Nat.le_of_succ_le hi)).K β).lev.U) (κ' : ((St (i + 1) hi).K β').lev.U),
    x₁.1 = x.1 * κ.1 → x₁'.1 = x'.1 * κ'.1 →
    ∀ p p' p₁ p₁', IsPtAd A a i (Nat.le_of_succ_le hi) β x p → IsPtAd A a (i + 1) hi β' x' p' →
      IsPtAd A a i (Nat.le_of_succ_le hi) β x₁ p₁ → IsPtAd A a (i + 1) hi β' x₁' p₁' →
      ∀ z, phiT t.X.K p₁.deco.1 p₁'.deco.1 z = phiT t.X.K p.deco.1 p'.deco.1 z) := by
  first | exact @GlobalTheory.TwV.PhiTLev.phiT_mul_lev | exact GlobalTheory.TwV.PhiTLev.phiT_mul_lev | (intros; apply GlobalTheory.TwV.PhiTLev.phiT_mul_lev <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepLocalFactorLevelValuesTypePrimeStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.lastStep_localFactor_levelValues_typePrime : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
  ∀ (hi : t.m2 + 1 + 1 ≤ D.R.m) (β : (St (t.m2 + 1) (Nat.le_of_succ_le hi)).Ch) (β' : (St (t.m2 + 1 + 1) hi).Ch)
    (x x₁ : UA D (t.m2 + 1) (Nat.le_of_succ_le hi)) (x' x₁' : UA D (t.m2 + 1 + 1) hi)
    (κ : ((St (t.m2 + 1) (Nat.le_of_succ_le hi)).K β).lev.U) (κ' : ((St (t.m2 + 1 + 1) hi).K β').lev.U),
    x₁.1 = x.1 * κ.1 → x₁'.1 = x'.1 * κ'.1 →
    ∀ p p' p₁ p₁', IsPtAd A a (t.m2 + 1) (Nat.le_of_succ_le hi) β x p → IsPtAd A a (t.m2 + 1 + 1) hi β' x' p' →
      IsPtAd A a (t.m2 + 1) (Nat.le_of_succ_le hi) β x₁ p₁ → IsPtAd A a (t.m2 + 1 + 1) hi β' x₁' p₁' →
    ∀ (P : SB t μ), P.1 ∈ t.Pr.vGs → ∀ g z g' z', A.cplRel β P g z →
      InFrame t.seam (A.fb (t.m2 + 1) (Nat.le_of_succ_le hi) β) (t.cst μ).D P κ.1 g →
      TopLev t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1 + 1) P g' z' →
      InFrame t.seam (A.fb (t.m2 + 1 + 1) hi β') (topDep t.sel (t.tup μ) (t.cst μ)) P κ'.1 g' →
    ∀ Z, z' * topF t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P p₁ (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p₁) p₁' Z *
        rhoS t.Ch t.sel (t.tup μ) (t.m2 + 1) P ((LinearEquiv.det g : t.X.Eˣ) : t.X.E) *
        rhoT t.Ch t.sel (t.tup μ) (t.m2 + 1) P ((LinearEquiv.det g' : t.X.Eˣ) : t.X.E) =
      z * topF t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P p (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p) p' Z) := by
  first | exact @GlobalTheory.TwTop.locAt_vG | exact GlobalTheory.TwTop.locAt_vG | (intros; apply GlobalTheory.TwTop.locAt_vG <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepAdelicDatumLevelEquivariance

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV

namespace GlobalTheory.TwTop

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem locAt : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
  ∀ (hi : t.m2 + 1 + 1 ≤ D.R.m) (β : (St (t.m2 + 1) (Nat.le_of_succ_le hi)).Ch) (β' : (St (t.m2 + 1 + 1) hi).Ch)
    (x x₁ : UA D (t.m2 + 1) (Nat.le_of_succ_le hi)) (x' x₁' : UA D (t.m2 + 1 + 1) hi)
    (κ : ((St (t.m2 + 1) (Nat.le_of_succ_le hi)).K β).lev.U) (κ' : ((St (t.m2 + 1 + 1) hi).K β').lev.U),
    x₁.1 = x.1 * κ.1 → x₁'.1 = x'.1 * κ'.1 →
    ∀ p p' p₁ p₁', IsPtAd A a (t.m2 + 1) (Nat.le_of_succ_le hi) β x p → IsPtAd A a (t.m2 + 1 + 1) hi β' x' p' →
      IsPtAd A a (t.m2 + 1) (Nat.le_of_succ_le hi) β x₁ p₁ → IsPtAd A a (t.m2 + 1 + 1) hi β' x₁' p₁' →
    ∀ (P : SB t μ) g z g' z', A.cplRel β P g z →
      InFrame t.seam (A.fb (t.m2 + 1) (Nat.le_of_succ_le hi) β) (t.cst μ).D P κ.1 g →
      TopLev t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1 + 1) P g' z' →
      InFrame t.seam (A.fb (t.m2 + 1 + 1) hi β') (topDep t.sel (t.tup μ) (t.cst μ)) P κ'.1 g' →
    ∀ Z, z' * topF t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P p₁ (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p₁) p₁' Z *
        rhoS t.Ch t.sel (t.tup μ) (t.m2 + 1) P ((LinearEquiv.det g : t.X.Eˣ) : t.X.E) *
        rhoT t.Ch t.sel (t.tup μ) (t.m2 + 1) P ((LinearEquiv.det g' : t.X.Eˣ) : t.X.E) =
      z * topF t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P p (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p) p' Z) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPin hTie hi β β' x x₁ x' x₁' κ κ' hx hx' p p' p₁ p₁' hp hp' hp₁ hp₁' P
  by_cases hP : P.1 ∈ t.Pr.vGs
  · exact GlobalTheory.T.lastStep_localFactor_levelValues_typePrime A dtU a hPin hTie hi β β' x x₁ x' x₁' κ κ' hx hx' p p' p₁ p₁' hp hp' hp₁ hp₁' P hP
  · exact GlobalTheory.T.columnLastStep_localFactor_twist_prime_law A dtU a hPin hTie hi β β' x x₁ x' x₁' κ κ' hx hx' p p' p₁ p₁' hp hp' hp₁ hp₁' P hP

end GlobalTheory.TwTop

namespace GlobalTheory.TwTop

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem levAt_top : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => PtEx A a → MuLaw t u μ dtU →
    ∀ i hi, i = t.m2 + 1 → PtAway A a i hi → LevAt A dtU a i hi) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPin hTie hEx hMu i hi hieq _hAway
  subst hieq
  intro β β' x x' x₁ x₁' κ κ' hx hx' z
  have key : ∀ p p' p₁ p₁', IsPtAd A a (t.m2 + 1) (Nat.le_of_succ_le hi) β x p → IsPtAd A a (t.m2 + 1 + 1) hi β' x' p' →
      IsPtAd A a (t.m2 + 1) (Nat.le_of_succ_le hi) β x₁ p₁ → IsPtAd A a (t.m2 + 1 + 1) hi β' x₁' p₁' → ∀ Z,
      muOf t u μ dtU (t.m2 + 1 + 1) (Matrix.GeneralLinearGroup.det κ'.1) * ((((St (t.m2 + 1) _).K β).lev.chi κ : ℂˣ) : ℂ) *
          t.seam.σ₀ (xiPt A (t.m2 + 1) hi β β' p₁ p₁' Z) =
        muOf t u μ dtU (t.m2 + 1 + 1) (Matrix.GeneralLinearGroup.det κ.1) * ((((St (t.m2 + 1 + 1) hi).K β').lev.chi κ' : ℂˣ) : ℂ) *
          t.seam.σ₀ (xiPt A (t.m2 + 1) hi β β' p p' Z) := by
    intro p p' p₁ p₁' hp hp' hp₁ hp₁' Z
    have hxi : ∀ q q', xiPt A (t.m2 + 1) hi β β' q q' Z =
        _root_.Formalism.L2.Col.XiTop t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) q (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β q) q' Z := by
      intro q q'
      unfold xiPt
      rw [dite_eq_right (by omega), if_neg (by omega)]
    have e1 := hxi p₁ p₁'
    have e2 := hxi p p'
    have e3 := GlobalTheory.T.chartDatum_levelPrime_invariant_mul_level A dtU a hPin hTie (t.m2 + 1) hi β β' x x₁ x' x₁' κ κ' hx hx' p p' p₁ p₁' hp hp' hp₁ hp₁' Z
    simp only [e1, e2, xiTop_eq_prod, e3]
    have hC := hTie.levCpl β
    have hT2 := hTie.levTop β'
    have hLe := hC.1
    have hChi := hC.2.2
    have hLe' := hT2.1
    have hChi' := hT2.2
    have hU := (((St (t.m2 + 1) (Nat.le_of_succ_le hi)).K β).lev.U_eq κ.1).1 κ.2
    have hU' := (((St (t.m2 + 1 + 1) hi).K β').lev.U_eq κ'.1).1 κ'.2
    have hov : ∀ P : SB t μ, IsOver (HeightOneSpectrum.under (𝓞 D.host.F) (seamP t.seam P.1)) (seamP t.seam P.1) := by
      intro P
      unfold IsOver
      rw [HeightOneSpectrum.under_asIdeal]
    choose g zz hg using fun P : SB t μ => hLe P _ (hov P) κ.1 hU.1 (hU.2 _)
    choose g' zz' hg' using fun P : SB t μ => hLe' P _ (hov P) κ'.1 hU'.1 (hU'.2 _)
    have c1 := hChi κ g zz hg
    have c2 := hChi' κ' g' zz' hg'
    have hm := GlobalTheory.T.lastStepCharacter_at_levelDet_mul_localCharacters A dtU a hPin hTie hMu hi β β' κ κ' g zz g' zz' hg hg'
    have hprod : (∏ P, zz' P) * (∏ P, topF t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P p₁
          (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p₁) p₁' Z) *
        (∏ P, rhoS t.Ch t.sel (t.tup μ) (t.m2 + 1) P ((LinearEquiv.det (g P) : t.X.Eˣ) : t.X.E) *
          rhoT t.Ch t.sel (t.tup μ) (t.m2 + 1) P ((LinearEquiv.det (g' P) : t.X.Eˣ) : t.X.E)) =
        (∏ P, zz P) * ∏ P, topF t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P p
          (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p) p' Z := by
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun P _ => ?_
      rw [← locAt A dtU a hPin hTie hi β β' x x₁ x' x₁' κ κ' hx hx' p p' p₁ p₁' hp hp' hp₁ hp₁' P (g P) (zz P) (g' P) (zz' P)
        (hg P).1 (hg P).2 (hg' P).1 (hg' P).2 Z]
      ring
    have e := congrArg t.seam.σ₀ hprod
    simp only [map_mul] at e ⊢
    have hA : t.seam.σ₀ (∏ P, zz P) ≠ 0 := right_ne_zero_of_mul_eq_one c1
    have hB : t.seam.σ₀ (∏ P, zz' P) ≠ 0 := right_ne_zero_of_mul_eq_one c2
    apply mul_right_cancel₀ (mul_ne_zero hA hB)
    linear_combination
      (-(((((St (t.m2 + 1) _).K β).lev.chi κ : ℂˣ) : ℂ) * t.seam.σ₀ (phiT t.X.K p.deco.1 p'.deco.1 Z) *
        t.seam.σ₀ (∏ P, topF t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P p₁ (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p₁) p₁' Z) *
        t.seam.σ₀ (∏ P, zz P) * t.seam.σ₀ (∏ P, zz' P))) * hm +
      (muOf t u μ dtU (t.m2 + 1 + 1) (Matrix.GeneralLinearGroup.det κ.1) * t.seam.σ₀ (phiT t.X.K p.deco.1 p'.deco.1 Z) *
        t.seam.σ₀ (∏ P, zz' P) *
        t.seam.σ₀ (∏ P, topF t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P p₁ (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p₁) p₁' Z) *
        t.seam.σ₀ (∏ P, rhoS t.Ch t.sel (t.tup μ) (t.m2 + 1) P ((LinearEquiv.det (g P) : t.X.Eˣ) : t.X.E) *
          rhoT t.Ch t.sel (t.tup μ) (t.m2 + 1) P ((LinearEquiv.det (g' P) : t.X.Eˣ) : t.X.E))) * c1 +
      (muOf t u μ dtU (t.m2 + 1 + 1) (Matrix.GeneralLinearGroup.det κ.1) * t.seam.σ₀ (phiT t.X.K p.deco.1 p'.deco.1 Z)) * e -
      (muOf t u μ dtU (t.m2 + 1 + 1) (Matrix.GeneralLinearGroup.det κ.1) * t.seam.σ₀ (phiT t.X.K p.deco.1 p'.deco.1 Z) *
        t.seam.σ₀ (∏ P, topF t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P p (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p) p' Z) *
        t.seam.σ₀ (∏ P, zz P)) * c2
  have h₁ : (∃ p, IsPtAd A a (t.m2 + 1) (Nat.le_of_succ_le hi) β x₁ p) ∧ ∃ p', IsPtAd A a (t.m2 + 1 + 1) hi β' x₁' p' :=
    ⟨hEx _ _ β x₁, hEx _ _ β' x₁'⟩
  have h₀ : (∃ p, IsPtAd A a (t.m2 + 1) (Nat.le_of_succ_le hi) β x p) ∧ ∃ p', IsPtAd A a (t.m2 + 1 + 1) hi β' x' p' :=
    ⟨hEx _ _ β x, hEx _ _ β' x'⟩
  unfold xiAd
  rw [dite_eq_left h₁, dite_eq_left h₀]
  exact key _ _ _ _ h₀.1.choose_spec h₀.2.choose_spec h₁.1.choose_spec h₁.2.choose_spec _

end GlobalTheory.TwTop

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepAdelicDatumLevelEquivarianceStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

theorem _root_.GlobalTheory.T.lastStep_adelicDatum_level_equivariance : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => PtEx A a → MuLaw t u μ dtU → ∀ i hi, i = t.m2 + 1 → PtAway A a i hi → LevAt A dtU a i hi) := by
  first | exact @GlobalTheory.TwTop.levAt_top | exact GlobalTheory.TwTop.levAt_top | (intros; apply GlobalTheory.TwTop.levAt_top <;> assumption)
end
end
