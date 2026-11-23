module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmulCompSmul
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FirstCoupledKernelEquivariantCosets
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointRightTranslateByLevelCoupledStep
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatAdXMulLev
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsChartPointFramesMovedByLevelStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DetInvMulFrameReadingCongruentOneModNorm
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MuCharacterDetLevelEqLocalTameProductStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartBasePointAdelicRightMulLevel

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

noncomputable section

namespace GlobalTheory.PtMove

attribute [local instance] Formalism.BasicNotions.Host.cmStar



theorem isPtAd_mul_lev : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
  ∀ (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (κ : ((St i hi).K β).lev.U) (x x₁ : UA D i hi)
    (p q : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) i) (k : SB t μ → (Sp t.X.E (D.R.N i) ≃ₗ[t.X.E] Sp t.X.E (D.R.N i))),
    x₁.1 = x.1 * κ.1 → IsPtAd A a i hi β x p → q.deco.1.N = p.deco.1.N → q.deco.1.f = p.deco.1.f →
    (∀ P, frsF t.sel (t.tup μ) q P = frsF t.sel (t.tup μ) p P * k P) → (∀ P, k P ∈ GLint t.X.E (D.R.N i) P.1) →
    (∀ P, InFrame t.seam (A.fb i hi β) (t.cst μ).D P κ.1 (k P)) → IsPtAd A a i hi β x₁ q) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a _ _ i hi β κ x x₁ p q k hx hp hN hf hfr hk hin
  refine ⟨?_, ?_, ?_⟩
  · rw [hN, hp.lat]
    unfold latCo
    rw [hx, Formalism.MainNotions.G.KAat.latAd_stab x.1 κ.1 _ (hatStab_of_lev _ κ)]
  · intro P
    have e1 : ratA D.host.F (A.crd i hi) * x₁.1 * ratA D.host.F (A.fb i hi β P) =
        (ratA D.host.F (A.crd i hi) * x.1 * ratA D.host.F (A.fb i hi β P)) *
          ((ratA D.host.F (A.fb i hi β P))⁻¹ * κ.1 * ratA D.host.F (A.fb i hi β P)) := by
      rw [hx]; group
    rw [e1, hfr P, map_mul (seamGL t.seam)]
    exact GlobalTheory.CplPt.nearAt_mul_int _ (hp.frame P) (hin P) (GlobalTheory.CplPt.seamGL_int t.seam ⟨k P, hk P⟩)
  · intro P v h hv
    have H := GlobalTheory.CplPt.funMoved_mul_lev t.seam _ P v h (iotaOf A i hi β P v h) (ratA D.host.F (A.crd i hi) * x.1) p.deco.1 κ (hp.fnl P v h hv)
    have e : ratA D.host.F (A.crd i hi) * x₁.1 = ratA D.host.F (A.crd i hi) * x.1 * κ.1 := by rw [hx, mul_assoc]
    rw [e]
    intro w hw z hz
    have H2 := H w (hN ▸ hw) z hz
    rw [hf]
    exact H2

end GlobalTheory.PtMove

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartBasePointAdelicRightMulLevelStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

theorem _root_.GlobalTheory.T.chart_base_point_adelic_right_mul_level : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
  ∀ (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (κ : ((St i hi).K β).lev.U) (x x₁ : UA D i hi)
    (p q : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) i) (k : SB t μ → (Sp t.X.E (D.R.N i) ≃ₗ[t.X.E] Sp t.X.E (D.R.N i))),
    x₁.1 = x.1 * κ.1 → IsPtAd A a i hi β x p → q.deco.1.N = p.deco.1.N → q.deco.1.f = p.deco.1.f →
    (∀ P, frsF t.sel (t.tup μ) q P = frsF t.sel (t.tup μ) p P * k P) → (∀ P, k P ∈ GLint t.X.E (D.R.N i) P.1) →
    (∀ P, InFrame t.seam (A.fb i hi β) (t.cst μ).D P κ.1 (k P)) → IsPtAd A a i hi β x₁ q) := by
  first | exact @GlobalTheory.PtMove.isPtAd_mul_lev | exact GlobalTheory.PtMove.isPtAd_mul_lev | (intros; apply GlobalTheory.PtMove.isPtAd_mul_lev <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.FirstCoupledStepCharacterAtLevelDetMulTameValues

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

theorem GlobalTheory.SrcMuDet.muOf_levelDet_mul_sigma_prod_rhoS_eq_one : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => MuLaw t u μ dtU →
  ∀ (hi : t.m2 < D.R.m) (β : (St t.m2 hi.le).Ch) (κ : ((St t.m2 hi.le).K β).lev.U)
    (g : SB t μ → (Sp t.X.E (D.R.N t.m2) ≃ₗ[t.X.E] Sp t.X.E (D.R.N t.m2))) (z : SB t μ → t.X.K),
    (∀ P, A.midRel t.m2 hi β P (g P) (z P) ∧ InFrame t.seam (A.fb t.m2 hi.le β) (t.cst μ).D P κ.1 (g P)) →
    muOf t u μ dtU (t.m2 + 1) (Matrix.GeneralLinearGroup.det κ.1) *
      t.seam.σ₀ (∏ P : SB t μ, rhoS t.Ch t.sel (t.tup μ) t.m2 P ((LinearEquiv.det (g P) : t.X.Eˣ) : t.X.E)) = 1) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPin hTie hMu hi β κ g z hg
  exact (GlobalTheory.T.muCharacter_det_level_eq_local_tame_product A dtU a hPin hTie hMu t.m2 hi t.m2 hi.le β κ
    (fun P => ((LinearEquiv.det (g P) : t.X.Eˣ) : t.X.E))
    (fun P => GlobalTheory.FramesDet.det_inFrame t.seam _ _ ((t.idx_ok μ).cst_ok.D_pos P) (hg P).2)).1
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.FirstCoupledStepCharacterAtLevelDetMulTameValuesStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

theorem _root_.GlobalTheory.T.firstCoupledStepCharacter_at_levelDet_mul_tameValues : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => MuLaw t u μ dtU →
  ∀ (hi : t.m2 < D.R.m) (β : (St t.m2 hi.le).Ch) (κ : ((St t.m2 hi.le).K β).lev.U)
    (g : SB t μ → (Sp t.X.E (D.R.N t.m2) ≃ₗ[t.X.E] Sp t.X.E (D.R.N t.m2))) (z : SB t μ → t.X.K),
    (∀ P, A.midRel t.m2 hi β P (g P) (z P) ∧ InFrame t.seam (A.fb t.m2 hi.le β) (t.cst μ).D P κ.1 (g P)) →
    muOf t u μ dtU (t.m2 + 1) (Matrix.GeneralLinearGroup.det κ.1) *
      t.seam.σ₀ (∏ P : SB t μ, rhoS t.Ch t.sel (t.tup μ) t.m2 P ((LinearEquiv.det (g P) : t.X.Eˣ) : t.X.E)) = 1) := by
  first | exact @GlobalTheory.SrcMuDet.muOf_levelDet_mul_sigma_prod_rhoS_eq_one | exact GlobalTheory.SrcMuDet.muOf_levelDet_mul_sigma_prod_rhoS_eq_one | (intros; apply GlobalTheory.SrcMuDet.muOf_levelDet_mul_sigma_prod_rhoS_eq_one <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.FirstCoupledStepLevelLocalElementsValues

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

noncomputable section

namespace GlobalTheory.TwV

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem levSrc_localData : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
  ∀ (hi : t.m2 < D.R.m) (β : (St t.m2 hi.le).Ch) (κ : ((St t.m2 hi.le).K β).lev.U),
    ∃ (g : SB t μ → (Sp t.X.E (D.R.N t.m2) ≃ₗ[t.X.E] Sp t.X.E (D.R.N t.m2))) (z : SB t μ → t.X.K),
      (∀ P, A.midRel t.m2 hi β P (g P) (z P) ∧ InFrame t.seam (A.fb t.m2 hi.le β) (t.cst μ).D P κ.1 (g P)) ∧
      ((((St t.m2 hi.le).K β).lev.chi κ : ℂˣ) : ℂ) * t.seam.σ₀ (∏ P, z P) = 1) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a _hPins hTie hi β κ
  obtain ⟨hLe, -, hChi⟩ := hTie.levMid t.m2 hi le_rfl β
  have hκ := (((St t.m2 hi.le).K β).lev.U_eq κ.1).1 κ.2
  have key : ∀ P : SB t μ, ∃ g z, A.midRel t.m2 hi β P g z ∧
      InFrame t.seam (A.fb t.m2 hi.le β) (t.cst μ).D P κ.1 g := by
    intro P
    refine hLe P (HeightOneSpectrum.under (𝓞 D.host.F) (seamP t.seam P.1)) ?_ κ.1 hκ.1 (hκ.2 _)
    unfold IsOver
    rw [HeightOneSpectrum.under_asIdeal]
  choose g z hgz using key
  exact ⟨g, z, hgz, hChi κ g z hgz⟩

end GlobalTheory.TwV
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.FirstCoupledStepLevelLocalElementsValuesStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

theorem _root_.GlobalTheory.T.firstCoupledStep_level_local_elements_values : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
  ∀ (hi : t.m2 < D.R.m) (β : (St t.m2 hi.le).Ch) (κ : ((St t.m2 hi.le).K β).lev.U),
    ∃ (g : SB t μ → (Sp t.X.E (D.R.N t.m2) ≃ₗ[t.X.E] Sp t.X.E (D.R.N t.m2))) (z : SB t μ → t.X.K),
      (∀ P, A.midRel t.m2 hi β P (g P) (z P) ∧ InFrame t.seam (A.fb t.m2 hi.le β) (t.cst μ).D P κ.1 (g P)) ∧
      ((((St t.m2 hi.le).K β).lev.chi κ : ℂˣ) : ℂ) * t.seam.σ₀ (∏ P, z P) = 1) := by
  first | exact @GlobalTheory.TwV.levSrc_localData | exact GlobalTheory.TwV.levSrc_localData | (intros; apply GlobalTheory.TwV.levSrc_localData <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.FirstCoupledStepAdelicDatumSourceLevelLaw

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

namespace GlobalTheory.LevSrcCpl

section Local
variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
  {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {m2 : ℕ}


open GlobalTheory.TopLaw GlobalTheory.CoupledLaw in
theorem firstCoupledDatum_source_level_law {u : Pr.Word} (hX : X.Ok) (hPr : Pr.Ok) (hL : L.Ok Ch sel mu cst G m2) {al : L.β m2}
    {p q : ChPt (R := R) sel mu u m2} (p' : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1))))
    {κ : GLQ X.E (R.N m2) (rowSG Pr sel mu)} {c : rowSG Pr sel mu → X.Kˣ}
    (hκ : ∀ P, frsF sel mu q P = frsF sel mu p P * ((κ P)⁻¹).1)
    (ha : ∀ P, LevAt (L.levG m2 al) (L.levQ m2 al) P (κ P) (c P))
    (hN : q.deco.1.N = p.deco.1.N) (hf : q.deco.1.f = p.deco.1.f) (x : HomE X.E (R.N m2) (R.N (m2 + 1))) :
    XiCpl1 Ch sel mu cst L m2 al q p' Y x * ∏ P : rowSG Pr sel mu, rhoS Ch sel mu m2 P ((LinearEquiv.det ((κ P)⁻¹).1 : X.Eˣ) : X.E) =
      (((∏ P, c P)⁻¹ : X.Kˣ) : X.K) * XiCpl1 Ch sel mu cst L m2 al p p' Y x := by
  have e0 : phiT X.K q.deco.1 p'.deco.1 x = phiT X.K p.deco.1 p'.deco.1 x := by
    unfold phiT Deco.at
    rw [hN, hf]
  unfold XiCpl1
  rw [e0, mul_assoc, mul_left_comm _ (phiT _ _ _ _), ← Finset.prod_mul_distrib, ← Finset.prod_inv_distrib, Units.coe_prod,
    ← Finset.prod_mul_distrib]
  refine congrArg _ (Finset.prod_congr rfl fun P _ => ?_)
  have e1 : inFr (frsF sel mu q P) (frsF sel mu p' P) x =
      inFr (frsF sel mu p P) (frsF sel mu p' P) x ∘ₗ ((κ P)⁻¹).1.toLinearMap := by
    rw [hκ]
    rfl
  rw [e1]
  exact psiAt_source hX hPr hL (ha P).inv _ _

end Local
end GlobalTheory.LevSrcCpl

namespace GlobalTheory.LevSrcCpl
attribute [local instance] Formalism.BasicNotions.Host.cmStar



theorem levSrc_cpl : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => PtEx A a → MuLaw t u μ dtU → ∀ i hi, i = t.m2 → PtAway A a i hi →
  ∀ β β' (x x₁ : UA D i (Nat.le_of_succ_le hi)) (x' : UA D (i + 1) hi) (κ : ((St i (Nat.le_of_succ_le hi)).K β).lev.U) p p' p₁,
    x₁.1 = x.1 * κ.1 → IsPtAd A a i (Nat.le_of_succ_le hi) β x p → IsPtAd A a (i + 1) hi β' x' p' →
    IsPtAd A a i (Nat.le_of_succ_le hi) β x₁ p₁ → ∀ w,
    ((((St i (Nat.le_of_succ_le hi)).K β).lev.chi κ : ℂˣ) : ℂ) * t.seam.σ₀ (xiPt A i hi β β' p₁ p' w) =
      muOf t u μ dtU (i + 1) (Matrix.GeneralLinearGroup.det κ.1) * t.seam.σ₀ (xiPt A i hi β β' p p' w)) := by
  unfold GlobalTheory.TwV.UnderTie
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPins hTie _hEx hMu i hi hi2 hAway β β' x x₁ x' κ p p' p₁ hx hp hp' hp₁ w
  subst hi2
  have hlt : t.m2 < D.R.m := hi
  obtain ⟨g, z, hgz, hchi⟩ := GlobalTheory.T.firstCoupledStep_level_local_elements_values A dtU a hPins hTie hlt β κ
  obtain ⟨q, κP, c, hfr, hlev, hN, hf, hcz, hrho, hin⟩ := GlobalTheory.T.exists_chart_point_frames_moved_by_level A dtU a hPins hTie hlt β κ p g z hgz
  have hq : IsPtAd A a t.m2 hlt.le β x₁ q :=
    GlobalTheory.T.chart_base_point_adelic_right_mul_level A dtU a hPins hTie t.m2 hlt.le β κ x x₁ p q (fun P => ((κP P)⁻¹).1) hx hp hN hf hfr (fun P => ((κP P)⁻¹).2) hin
  have hD := GlobalTheory.T.firstCoupledStepCharacter_at_levelDet_mul_tameValues A dtU a hPins hTie hMu hlt β κ g z hgz
  have eA : xiPt A t.m2 hi β β' p₁ p' w = xiPt A t.m2 hi β β' q p' w :=
    congrFun (hAway β β' x₁ x' x₁ x' q p' p₁ p' hq hp' hp₁ hp' (fun _ _ => ⟨rfl, rfl⟩)) w
  rw [eA]
  unfold xiPt
  rw [dite_eq_right (lt_irrefl _), if_pos rfl, dite_eq_right (lt_irrefl _), if_pos rfl]
  have hsrc := firstCoupledDatum_source_level_law (G := t.glob) (cst := t.cst μ) (Ch := t.Ch) hPins.fields.ok t.pr_ok (t.idx_ok μ) (al := A.ib t.m2 hlt β) p'
    (cosetOf A (t.m2 + 1) hi β' p') hfr hlev hN hf w
  have hprod : ((∏ P, c P : t.X.Kˣ) : t.X.K) * ∏ P, z P = 1 := by
    rw [Units.coe_prod, ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun P _ => hcz P
  simp_rw [hrho] at hsrc
  have e4 := congrArg t.seam.σ₀ hsrc
  have e2 := congrArg t.seam.σ₀ hprod
  have e3 : t.seam.σ₀ (((∏ P, c P)⁻¹ : t.X.Kˣ) : t.X.K) * t.seam.σ₀ ((∏ P, c P : t.X.Kˣ) : t.X.K) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  rw [map_mul, map_mul] at e4
  rw [map_mul, map_one] at e2
  linear_combination (t.seam.σ₀ (XiCpl1 t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) t.m2 (A.ib t.m2 hlt β) q p' (cosetOf A (t.m2 + 1) hi β' p') w) *
      t.seam.σ₀ ((∏ P, c P : t.X.Kˣ) : t.X.K)) * hchi
    - (t.seam.σ₀ (XiCpl1 t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) t.m2 (A.ib t.m2 hlt β) q p' (cosetOf A (t.m2 + 1) hi β' p') w) *
      ((((St t.m2 hlt.le).K β).lev.chi κ : ℂˣ) : ℂ)) * e2
    - (t.seam.σ₀ ((∏ P, c P : t.X.Kˣ) : t.X.K) *
      t.seam.σ₀ (XiCpl1 t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) t.m2 (A.ib t.m2 hlt β) q p' (cosetOf A (t.m2 + 1) hi β' p') w)) * hD
    + (muOf t u μ dtU (t.m2 + 1) (Matrix.GeneralLinearGroup.det κ.1) *
      t.seam.σ₀ (XiCpl1 t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) t.m2 (A.ib t.m2 hlt β) p p' (cosetOf A (t.m2 + 1) hi β' p') w)) * e3
    + (muOf t u μ dtU (t.m2 + 1) (Matrix.GeneralLinearGroup.det κ.1) * t.seam.σ₀ ((∏ P, c P : t.X.Kˣ) : t.X.K)) * e4

end GlobalTheory.LevSrcCpl
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.FirstCoupledStepAdelicDatumSourceLevelLawStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

theorem _root_.GlobalTheory.T.firstCoupledStep_adelicDatum_source_level_law : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => PtEx A a → MuLaw t u μ dtU → ∀ i hi, i = t.m2 → PtAway A a i hi →
  ∀ β β' (x x₁ : UA D i (Nat.le_of_succ_le hi)) (x' : UA D (i + 1) hi) (κ : ((St i (Nat.le_of_succ_le hi)).K β).lev.U) p p' p₁,
    x₁.1 = x.1 * κ.1 → IsPtAd A a i (Nat.le_of_succ_le hi) β x p → IsPtAd A a (i + 1) hi β' x' p' →
    IsPtAd A a i (Nat.le_of_succ_le hi) β x₁ p₁ → ∀ w,
    ((((St i (Nat.le_of_succ_le hi)).K β).lev.chi κ : ℂˣ) : ℂ) * t.seam.σ₀ (xiPt A i hi β β' p₁ p' w) =
      muOf t u μ dtU (i + 1) (Matrix.GeneralLinearGroup.det κ.1) * t.seam.σ₀ (xiPt A i hi β β' p p' w)) := by
  first | exact @GlobalTheory.LevSrcCpl.levSrc_cpl | exact GlobalTheory.LevSrcCpl.levSrc_cpl | (intros; apply GlobalTheory.LevSrcCpl.levSrc_cpl <;> assumption)
end
end
