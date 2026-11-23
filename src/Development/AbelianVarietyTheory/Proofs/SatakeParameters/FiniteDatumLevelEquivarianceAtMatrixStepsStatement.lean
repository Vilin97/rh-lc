module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.XiEntryInvariant
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemLatBack
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicLatAtRep
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointRightTranslateByLevelCoupledStep
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatAdXMulLev
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PulledLatticeVectorMemDualBaseLatticeCompletionStatement
public import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocBases
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
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelMovedPointFramesMatrixStepsStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MuCharacterDetLevelEqLocalTameProductStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointMulLevelSameDecoration

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.LevDeco
open scoped TensorProduct

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}

theorem exists_basePlace_contains_every_chartLevelPrime {A : AdData t u μ St} {dtU : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm →* D.Dt} {a : 𝓞 D.host.E} (H : AdTie A dtU a)
    (j : ℕ) (hj : j ≤ D.R.m) (P : t.Pr.vT (t.word u)) :
    ∃ v : HeightOneSpectrum (𝓞 D.host.F), ∃ h : (((St j hj).T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal, IsOver v (seamP t.seam P.1) := by
  classical
  have hpi : t.Pr.piT (t.word u) ∈ P.1.asIdeal := by
    have h := P.2
    unfold Formalism.L2.Col.Primes.vT Formalism.L2.Col.divs at h
    split_ifs at h with hf
    · simpa using h
    · simp at h
  have hT : ((t.Pr.T (t.word u) : ℕ) : 𝓞 t.X.E) ∈ P.1.asIdeal := by
    rw [← t.pr_ok.piT_norm]
    exact Ideal.mul_mem_right _ _ hpi
  have hTQ : (((St j hj).T : ℕ) : 𝓞 D.host.E) ∈ (seamP t.seam P.1).asIdeal := by
    rw [H.T_eq j hj, ← t.T_rec u, ← map_natCast (RingOfIntegers.mapRingEquiv t.seam.iE), mem_seamP]
    exact hT
  have hT0 : (((St j hj).T : ℕ) : 𝓞 D.host.F) ≠ 0 := by
    rw [H.T_eq j hj, ← t.T_rec u]
    exact Nat.cast_ne_zero.2 (t.pr_ok.T_prime _).ne_zero
  have hmem : (((St j hj).T : ℕ) : 𝓞 D.host.F) ∈ (seamP t.seam P.1).asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) := by
    rw [Ideal.mem_comap, map_natCast]
    exact hTQ
  let v : HeightOneSpectrum (𝓞 D.host.F) := ⟨(seamP t.seam P.1).asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)),
    Ideal.IsPrime.comap _, fun h => hT0 (by rw [h] at hmem; exact (Ideal.mem_bot.1 hmem))⟩
  exact ⟨v, hmem, rfl⟩

theorem N_eq_latAdX {A : AdData t u μ St} {a : 𝓞 D.host.E} {j : ℕ} {hj : j ≤ D.R.m} {β : (St j hj).Ch} {y : UA D j hj}
    {q : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) j} (hq : IsPtAd A a j hj β y q) : q.deco.1.N = latAdX A a j hj β y.1 := by
  show _ = latBack t.seam (latCo D.sp (gramN D j hj) (A.crd j hj) a y.1 ((St j hj).K β).lev.Lb)
  rw [← hq.lat, latBack_seam_lat]

theorem ptAd_mul_lev_deco : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    ∀ j (hj : j ≤ D.R.m) (β : (St j hj).Ch) (x x₁ : UA D j hj) (κ : ((St j hj).K β).lev.U), x₁.1 = x.1 * κ.1 →
    ∀ p p₁, IsPtAd A a j hj β x p → IsPtAd A a j hj β x₁ p₁ →
      p₁.deco.1.N = p.deco.1.N ∧ ∀ P w, p₁.deco.1.f P w = p.deco.1.f P w) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a _ H j hj β x x₁ κ hx p p₁ hp hp₁
  have hN : p₁.deco.1.N = p.deco.1.N := by
    rw [N_eq_latAdX hp₁, N_eq_latAdX hp, hx, latAdX_mul_lev]
  refine ⟨hN, fun P w => ?_⟩
  obtain ⟨v, hTv, hov⟩ := exists_basePlace_contains_every_chartLevelPrime H j hj P
  by_cases hw : w ∈ p.deco.1.at P.1
  · have hw₁ : w ∈ p₁.deco.1.at P.1 := by simpa only [Deco.at, hN] using hw
    obtain ⟨s, hs, hsw⟩ := (mem_locP _ _ _).1 hw
    have h2 : s • w ∈ p₁.deco.1.N := hN ▸ hsw
    have hy : (fun b => t.seam.iE ((s • w) b)) ∈ latCo D.sp (gramN D j hj) (A.crd j hj) a x₁.1 ((St j hj).K β).lev.Lb := by
      rw [← hp₁.lat]
      exact Submodule.subset_span ⟨_, h2, rfl⟩
    let z : latS (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v)
        (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D j hj) ((St j hj).K β).lev.Lb)) :=
      ⟨_, GlobalTheory.T.pulledLatticeVector_mem_dualBaseLatticeCompletion D.sp (gramN D j hj) (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_gramN_det D j hj) (A.crd j hj) a x₁.1 x₁.2
        _ ((St j hj).K β).lev.Lb_fin ((St j hj).K β).lev.Lb_span ((St j hj).K β).lev.Lb_int v _ hy⟩
    have H1 := GlobalTheory.CplPt.funMoved_mul_lev t.seam ((St j hj).K β).lev P v hTv _ _ p.deco.1 κ (hp.fnl P v hTv hov)
    rw [mul_assoc, ← hx] at H1
    have e1 := H1 _ hsw z rfl
    have e2 := hp₁.fnl P v hTv hov _ h2 z rfl
    have e3 : p₁.deco.1.f P (s • w) = p.deco.1.f P (s • w) := e2.trans e1.symm
    rw [p₁.deco.2.f_smul P _ w hw₁, p.deco.2.f_smul P _ w hw] at e3
    haveI hP := P.1.isPrime
    have hu : Ideal.Quotient.mk P.1.asIdeal s ≠ 0 := by
      rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
      exact hs
    exact mul_left_cancel₀ hu e3
  · have hw₁ : w ∉ p₁.deco.1.at P.1 := by simpa only [Deco.at, hN] using hw
    rw [p₁.deco.2.f_off P w hw₁, p.deco.2.f_off P w hw]

end GlobalTheory.TwV.LevDeco

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointMulLevelSameDecorationStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

theorem _root_.GlobalTheory.T.chartPoint_mul_level_same_decoration : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    ∀ j (hj : j ≤ D.R.m) (β : (St j hj).Ch) (x x₁ : UA D j hj) (κ : ((St j hj).K β).lev.U), x₁.1 = x.1 * κ.1 →
    ∀ p p₁, IsPtAd A a j hj β x p → IsPtAd A a j hj β x₁ p₁ →
      p₁.deco.1.N = p.deco.1.N ∧ ∀ P w, p₁.deco.1.f P w = p.deco.1.f P w) := by
  first | exact @GlobalTheory.TwV.LevDeco.ptAd_mul_lev_deco | exact GlobalTheory.TwV.LevDeco.ptAd_mul_lev_deco | (intros; apply GlobalTheory.TwV.LevDeco.ptAd_mul_lev_deco <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDatumLevelEquivarianceAtMatrixSteps

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV



theorem levAt_mat : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    PtEx A a → MuLaw t u μ dtU → ∀ i hi, i < t.m2 → PtAway A a i hi → LevAt A dtU a i hi) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPin hTie hEx hMu i hi him _ β β' x x' x₁ x₁' κ κ' e1 e1' z
  have hm := m_eq t μ
  have hi0 : i < D.R.m := by omega
  have hi1 : i + 1 < D.R.m := by omega
  have H0 : (∃ p, IsPtAd A a i (Nat.le_of_succ_le hi) β x p) ∧ ∃ p', IsPtAd A a (i + 1) hi β' x' p' :=
    ⟨hEx _ _ _ _, hEx _ _ _ _⟩
  have H1 : (∃ p, IsPtAd A a i (Nat.le_of_succ_le hi) β x₁ p) ∧ ∃ p', IsPtAd A a (i + 1) hi β' x₁' p' :=
    ⟨hEx _ _ _ _, hEx _ _ _ _⟩
  unfold xiAd
  rw [dite_eq_left H0, dite_eq_left H1]
  have hp := H0.1.choose_spec
  have hp' := H0.2.choose_spec
  have hq := H1.1.choose_spec
  have hq' := H1.2.choose_spec
  generalize H0.1.choose = p at hp ⊢
  generalize H0.2.choose = p' at hp' ⊢
  generalize H1.1.choose = q at hq ⊢
  generalize H1.2.choose = q' at hq' ⊢
  unfold xiPt
  rw [dite_eq_left him, dite_eq_left him]
  obtain ⟨k, c, hk, hc, hχ, hd⟩ := GlobalTheory.T.levelMoved_point_frames_matrixSteps A dtU a hPin hTie i hi0 him.le β x x₁ κ e1 p q hp hq
  obtain ⟨k', c', hk', hc', hχ', hd'⟩ := GlobalTheory.T.levelMoved_point_frames_matrixSteps A dtU a hPin hTie (i + 1) hi1 him β' x' x₁' κ' e1' p' q' hp' hq'
  obtain ⟨hN, hf⟩ := GlobalTheory.T.chartPoint_mul_level_same_decoration A dtU a hPin hTie i (Nat.le_of_succ_le hi) β x x₁ κ e1 p q hp hq
  obtain ⟨hN', hf'⟩ := GlobalTheory.T.chartPoint_mul_level_same_decoration A dtU a hPin hTie (i + 1) hi β' x' x₁' κ' e1' p' q' hp' hq'
  obtain ⟨hmu, -⟩ := GlobalTheory.T.muCharacter_det_level_eq_local_tame_product A dtU a hPin hTie hMu i hi0 i (Nat.le_of_succ_le hi) β κ _ hd
  obtain ⟨-, hmu'⟩ := GlobalTheory.T.muCharacter_det_level_eq_local_tame_product A dtU a hPin hTie hMu i hi0 (i + 1) hi β' κ' _ hd'
  have core : ∀ W, muOf t u μ dtU (i + 1) (Matrix.GeneralLinearGroup.det κ'.1) * ((((St i (Nat.le_of_succ_le hi)).K β).lev.chi κ : ℂˣ) : ℂ) *
      t.seam.σ₀ (XiEntry t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) i (A.ib i hi β) (A.ib (i + 1) hi1 β') q q' W) =
      muOf t u μ dtU (i + 1) (Matrix.GeneralLinearGroup.det κ.1) * ((((St (i + 1) hi).K β').lev.chi κ' : ℂˣ) : ℂ) *
      t.seam.σ₀ (XiEntry t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) i (A.ib i hi β) (A.ib (i + 1) hi1 β') p p' W) := by
    intro W
    have e0 : phiT t.X.K q.deco.1 q'.deco.1 W = phiT t.X.K p.deco.1 p'.deco.1 W := by
      unfold phiT
      refine @if_congr _ _ _ (_) (_) _ _ _ _ ?_ rfl rfl
      simp only [Deco.at, hN, hN', hf, hf']
    have law := GlobalTheory.MatLaw.xiEntry_law hPin.fields.ok t.pr_ok hPin.sel (t.idx_ok μ) him
      (γ := 1) (γ' := 1) (p := p) (q := q) (p' := p') (q' := q') (κ := k) (κ' := k') (a := c) (a' := c')
      (fun P => by rw [hk P, OneMemClass.coe_one, one_mul]) (fun P => by rw [hk' P, OneMemClass.coe_one, one_mul]) hc hc' W
      (by exact e0)
    have hW : ((1 : UF t.X.E (D.R.N (i + 1))).1.toLinearMap ∘ₗ W ∘ₗ (1 : UF t.X.E (D.R.N i)).1.symm.toLinearMap) = W :=
      LinearMap.ext fun v => rfl
    rw [hW, Finset.prod_mul_distrib] at law
    have law' := congrArg t.seam.σ₀ law
    simp only [map_mul, Units.val_mul, Pi.inv_apply] at law'
    have hCC : t.seam.σ₀ (((∏ P, c P : t.X.Kˣ)) : t.X.K) * t.seam.σ₀ ((((∏ P, c P)⁻¹ : t.X.Kˣ)) : t.X.K) = 1 := by
      rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
    linear_combination (-(t.seam.σ₀ (∏ P, rhoT t.Ch t.sel (t.tup μ) i P ((LinearEquiv.det ((k' P)⁻¹).1 : t.X.Eˣ) : t.X.E)) *
        t.seam.σ₀ (((∏ P, c P : t.X.Kˣ)) : t.X.K) * t.seam.σ₀ (XiEntry t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) i (A.ib i hi β) (A.ib (i + 1) hi1 β') q q' W))) * hmu
      + (muOf t u μ dtU (i + 1) (Matrix.GeneralLinearGroup.det κ.1) * t.seam.σ₀ (((∏ P, c P : t.X.Kˣ)) : t.X.K)) * law'
      + (muOf t u μ dtU (i + 1) (Matrix.GeneralLinearGroup.det κ.1) * t.seam.σ₀ (((∏ P, c' P : t.X.Kˣ)) : t.X.K) *
        t.seam.σ₀ (XiEntry t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) i (A.ib i hi β) (A.ib (i + 1) hi1 β') p p' W)) * hCC
      + (((((St i (Nat.le_of_succ_le hi)).K β).lev.chi κ : ℂˣ) : ℂ) *
        t.seam.σ₀ (XiEntry t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) i (A.ib i hi β) (A.ib (i + 1) hi1 β') q q' W)) * hmu'
      + (t.seam.σ₀ (∏ P, rhoT t.Ch t.sel (t.tup μ) i P ((LinearEquiv.det ((k' P)⁻¹).1 : t.X.Eˣ) : t.X.E)) *
        t.seam.σ₀ (XiEntry t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) i (A.ib i hi β) (A.ib (i + 1) hi1 β') q q' W)) * hχ
      - (muOf t u μ dtU (i + 1) (Matrix.GeneralLinearGroup.det κ.1) *
        t.seam.σ₀ (XiEntry t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) i (A.ib i hi β) (A.ib (i + 1) hi1 β') p p' W)) * hχ'
  exact core _

end GlobalTheory.TwV

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDatumLevelEquivarianceAtMatrixStepsStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

theorem _root_.GlobalTheory.T.finiteDatum_levelEquivariance_at_matrixSteps : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => PtEx A a → MuLaw t u μ dtU → ∀ i hi, i < t.m2 → PtAway A a i hi → LevAt A dtU a i hi) := by
  first | exact @GlobalTheory.TwV.levAt_mat | exact GlobalTheory.TwV.levAt_mat | (intros; apply GlobalTheory.TwV.levAt_mat <;> assumption)
end
end
