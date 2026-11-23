module

public import Development.AbelianVarietyTheory.Definitions.Jets.BasicLiftAll
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BigCellVectorNormEqRadialValueNormStatement
public import Development.AbelianVarietyTheory.Definitions.Jets.SameFns
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsRadialPartPolyDiffOperatorClosed
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellValues
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WordOperatorRadialPointwiseBoundStatement
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactSupportFacts
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelsOfBuiltSetting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.QNFAsm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadJFExists
public import Formalism.HermitianCurvature.StatementTop
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIsMulGOfSmoothLog

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
open scoped ContDiff

namespace GlobalTheory.HatNF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem mulG_normSq_contDiff : ContDiff ℝ ∞ (fun w : ℂ => Complex.normSq w) := by
  have h : (fun w : ℂ => Complex.normSq w) = fun w => w.re * w.re + w.im * w.im := by
    funext w; exact Complex.normSq_apply w
  rw [h]
  exact (Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff)

theorem mulG_ld_contDiffOn {φ : ℝ → ℝ} (hφ : LE.SmoothLog φ) (q : ℕ) :
    ContDiffOn ℝ ∞ (LE.ld q φ) (Set.Ioi 0) := by
  have h1 : ContDiff ℝ ∞ (iteratedDeriv q (fun u : ℝ => φ (Real.exp u))) := by
    rw [iteratedDeriv_eq_iterate]
    exact ContDiff.iterate_deriv q hφ
  exact h1.comp_contDiffOn (Real.contDiffOn_log.mono fun x hx => by simpa using (ne_of_gt hx))

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem mulG_gR_contDiff (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) :
    ContDiff ℝ ∞ (fun x : (Fin P.r → ℂ) × Q.Mx P.k P.r => gR P Bs x.1 x.2) := by
  unfold gR Q.GGl
  refine ContDiff.mul (mulG_normSq_contDiff.comp ?_) (ContDiff.sub (mulG_normSq_contDiff.comp ?_) contDiff_const)
  · exact contDiff_prod fun a _ => Formalism.FourierDecayAlt.P.Qx5.coord_contDiff a
  · exact (Formalism.FourierDecayAlt.P.Qx5.zetaL_contDiff _ _ _ _ _).comp contDiff_snd

theorem mulG_gR_pos (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) {x : (Fin P.r → ℂ) × Q.Mx P.k P.r}
    (hx : x ∈ Formalism.FourierDecayAlt.P.Qx5.OpR P.k P.r Bs.z Bs.z') : 0 < gR P Bs x.1 x.2 :=
  mul_pos (Complex.normSq_pos.2 (Finset.prod_ne_zero_iff.2 fun a _ => hx.1 a)) hx.2

theorem mulG_mem (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) {φ : ℝ → ℝ} (hφ : LE.SmoothLog φ) (q : ℕ)
    {Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)} (hΦ : Φ ∈ Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') :
    (fun c g => ((LE.ld q φ (gR P Bs c g) : ℝ) : ℂ) • Φ c g) ∈ Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π' := by
  refine Formalism.FourierDecayAlt.P.Qx5.smul_mem (a := fun x => ((LE.ld q φ (gR P Bs x.1 x.2) : ℝ) : ℂ)) ?_ ?_ hΦ
  · refine Complex.ofRealCLM.contDiff.comp_contDiffOn ?_
    exact (mulG_ld_contDiffOn hφ q).comp (mulG_gR_contDiff P Bs).contDiffOn fun x hx => mulG_gR_pos P Bs hx
  · intro x _ h hh h' hh'
    simp only [gR, Formalism.FourierDecayAlt.P.Qx5.GG_inv hh hh']

theorem exists_isMulG_of_smoothLog (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) {φ : ℝ → ℝ} (hφ : LE.SmoothLog φ) :
    ∃ W : ℕ → Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'), IsMulG P Bs φ W := by
  refine ⟨fun q =>
    { toFun := fun Φ => ⟨_, mulG_mem P Bs hφ q Φ.2⟩
      map_add' := fun Φ Ψ => ?_
      map_smul' := fun s Φ => ?_ }, fun q Φ c g => rfl⟩
  · apply Subtype.ext
    funext c g
    simp only [Submodule.coe_add, Pi.add_apply, smul_add]
  · apply Subtype.ext
    funext c g
    simp only [Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply]
    exact smul_comm _ _ _

theorem mulG_exists : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r)) (L : LevelData (RA P Bs) P.r) (st : Start (RA P Bs)) (l0 : ℕ) (d : Q.NFData P (RA P Bs)), P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 → IsNF X d → ∀ φ : ℝ → ℝ, LE.SmoothLog φ → ∃ W : ℕ → Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'), IsMulG P Bs φ W :=
  fun _ _ _ _ _ _ _ _ P Bs _ _ _ _ _ _ _ _ _ hφ => exists_isMulG_of_smoothLog P Bs hφ

end GlobalTheory.HatNF
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsRadialPartPolyDiffOperatorClosedStatement

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

theorem _root_.GlobalTheory.T.polyLift_one_mono_mul : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq), PolyLift P Bs 0 0 1 ∧ (∀ o o' κ κ' a, o ≤ o' → κ ≤ κ' → PolyLift P Bs o κ a → PolyLift P Bs o' κ' a) ∧ ∀ o₁ κ₁ o₂ κ₂ a b, PolyLift P Bs o₁ κ₁ a → PolyLift P Bs o₂ κ₂ b → PolyLift P Bs (o₁ + o₂) (κ₁ + κ₂) (a * b) := by
  first | exact @GlobalTheory.HatNF.polyLift_closed | exact GlobalTheory.HatNF.polyLift_closed | (intros; apply GlobalTheory.HatNF.polyLift_closed <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.RadialPictureSmulCutoffGMultiplier

section

@[expose] public section

namespace GlobalTheory.HatNF

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory

noncomputable section

theorem jf_mulG {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (φ : ℝ → ℝ) (f : B.Mat k r → (Wq →L[ℂ] Wp))
    (g : B.Mat k r) : B.JF Bs (mulG Bs φ f) g = ((φ (Gf k r Bs.z Bs.z' g) : ℝ) : ℂ) • B.JF Bs f g := by
  show ∫ p, JF.xiP Bs p • B.rho Bs p (mulG Bs φ f) g ∂Bs.μSS =
    ((φ (Gf k r Bs.z Bs.z' g) : ℝ) : ℂ) • ∫ p, JF.xiP Bs p • B.rho Bs p f g ∂Bs.μSS
  rw [← integral_smul]
  refine integral_congr_ae ?_
  filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS Bs] with p hp
  simp only [B.rho, mulG, Formalism.FourierDecayAlt.P.JCx1.needs.gf_sgs Bs hp]
  rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_comm]


attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
theorem cptCoef_mulG {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) {f : B.Mat k r → (Wq →L[ℂ] Wp)} (hf : KB.CptCoef Bs f) :
    KB.CptCoef Bs (mulG Bs φ f) := by
  obtain ⟨hs, ⟨R, hR⟩, ⟨δ, hδ, hG⟩⟩ := hf
  have hne : ∀ g, mulG Bs φ f g ≠ 0 → f g ≠ 0 := fun g h h0 => h (by simp [mulG, h0])
  have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun g : B.Mat k r => ((φ (Gf k r Bs.z Bs.z' g) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hφ.comp (Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf Bs.z Bs.z'))
  exact ⟨Formalism.FourierDecayAlt.P.JCx2.pd_smooth_smul hc hs, ⟨R, fun g hg h => hR g hg (hne g h)⟩,
    ⟨δ, hδ, fun g hg h => hG g hg (hne g h)⟩⟩

theorem radial_mulG : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq), ∀ (φ : ℝ → ℝ) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), (ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → LE.SmoothLog φ ∧ (KB.CptCoef Bs f → KB.CptCoef Bs (mulG Bs φ f))) ∧ ∀ (W : ℕ → Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'), IsMulG P Bs φ W → Top.IsRadOf P Bs Φ f → Top.IsRadOf P Bs (W 0 Φ) (mulG Bs φ f) := by
  intro Wp Wq _ _ _ _ _ _ P Bs φ f
  refine ⟨fun hφ => ⟨hφ.comp Real.contDiff_exp, fun hf => cptCoef_mulG Bs hφ hf⟩, ?_⟩
  intro W Φ hW hΦ x hx
  have hcell := Formalism.FourierDecayAlt.P.big_cell_values P.k P.r Wp Wq Bs x hx
  have hpos : 0 < gR P Bs x.1 x.2 := by
    have := hcell.1.2.1
    rw [hcell.2.2.2] at this
    exact this
  have hld : LE.ld 0 φ (gR P Bs x.1 x.2) = φ (gR P Bs x.1 x.2) := by
    simp only [LE.ld, iteratedDeriv_zero, Real.exp_log hpos]
  rw [hW 0 Φ x.1 x.2, hΦ x hx]
  simp only [Q.resG]
  rw [jf_mulG, hcell.2.2.2, hld, smul_comm]
  rfl

end

end GlobalTheory.HatNF
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.RadialPictureSmulCutoffGMultiplierStatement

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

theorem _root_.GlobalTheory.T.radial_picture_smul_cutoff_G_multiplier : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq), ∀ (φ : ℝ → ℝ) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), (ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → LE.SmoothLog φ ∧ (KB.CptCoef Bs f → KB.CptCoef Bs (mulG Bs φ f))) ∧ ∀ (W : ℕ → Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'), IsMulG P Bs φ W → Top.IsRadOf P Bs Φ f → Top.IsRadOf P Bs (W 0 Φ) (mulG Bs φ f) := by
  first | exact @GlobalTheory.HatNF.radial_mulG | exact GlobalTheory.HatNF.radial_mulG | (intros; apply GlobalTheory.HatNF.radial_mulG <;> assumption)
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.TLPlanAsm

section

@[expose] public section

namespace Formalism.FourierDecayAlt.TL

open Finset MeasureTheory Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr

noncomputable section

open Classical

theorem act_e1Vec {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] {z z' : Fin (2 * r + k + 1) → ℂ}
    {π : Q.Mx k r → (Wp →L[ℂ] Wp)} {π' : Q.Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]
    (M : Wd.SlopeTestRemainingChoices S (Q.Pr (Q.RadSp k r z z' π π'))) (Φ : Q.RadSp k r z z' π π') (e : Wd.Ix S) :
    P5.act M (Top.firstStateVector Φ) e = (M e e1).1 Φ := by
  unfold P5.act Top.firstStateVector
  rw [Finset.sum_eq_single (fun _ => 0)]
  · simp only [if_true]
    rfl
  · intro b _ hb
    rw [if_neg hb, map_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

end

end Formalism.FourierDecayAlt.TL
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.WordBoundCompactSupportCoefficients

section

@[expose] public section

namespace GlobalTheory.HatNF

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

theorem polyLift_listProd {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (Bs : B.RealPlaceData P.k P.r Wp Wq) (o κ : ℕ) (H : List (RA P Bs)) (hH : ∀ h ∈ H, PolyLift P Bs o κ h) :
    PolyLift P Bs (H.length * o) (H.length * κ) H.prod := by
  obtain ⟨h1, -, hmul⟩ := GlobalTheory.T.polyLift_one_mono_mul Wp Wq P Bs
  induction H with
  | nil => simpa using h1
  | cons a H ih =>
    have := hmul _ _ _ _ _ _ (hH a (by simp)) (ih fun h hh => hH h (by simp [hh]))
    rw [List.prod_cons, List.length_cons, Nat.succ_mul, Nat.succ_mul, add_comm _ o, add_comm _ κ]
    exact this

theorem wordBound_cptCoef : ∀ a : ℕ → ℕ, BasicLiftAll a → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (w : List C.Letter), KB.CutWord P p.l0 w → ∃ (C : ℝ) (J : ℕ) (Θs : List (B.DiffOp P.k P.r Wp Wq)), WordBound p (a P.r) w C J Θs (fun φ f => ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ ∧ KB.CptCoef p.T.base f) := by
  intro a ha Wp Wq _ _ _ _ _ _ P p w hw
  obtain ⟨X, μ, L, st, hD, hL⟩ := p.hΘ
  obtain ⟨d, hd⟩ := Formalism.FourierDecayAlt.P.normal_form_actual Wp Wq P _ _ _ _ p.hP X
  have hNF : IsNF (Bs := p.T.base) X d := hd
  have hok := Formalism.FourierDecayAlt.P.JCTx5.wordOK_of P _ _ _ _ st p.l0 hD.1.1 p.hl.1 p.hl.2.1 hD.2.2.2.2.1 hD.2.2.2.2.2.1 w
    hw.1 hw.2
  have hl : (D.positionted w).length = w.length := by simp [D.positionted]
  obtain ⟨C, J, Ts, hC, hTs, hB⟩ := GlobalTheory.T.wordOperator_radial_pointwise_bound Wp Wq P p.T.base X μ L st p.l0 d hD hNF (Fin w.length) _ (a P.r)
    (ha Wp Wq P p.T.base X μ L st p.l0 d hD hNF) (D.positionted w) hok.1
  rw [hl] at hTs hB
  have hlift : ∀ H : List (RA P p.T.base), ∃ Θ : B.DiffOp P.k P.r Wp Wq, H ∈ Ts →
      Formalism.FourierDecayAlt.P.CutMP.PolyOp (w.length * (2 * P.r + P.k + 1))
        (w.length * (8 * (P.r + 1) * (2 * P.r + P.k + 1))) Θ ∧ TL.RadIs P p.T.base Θ H.prod.1 := by
    intro H
    by_cases hH : H ∈ Ts
    · obtain ⟨Θ, hΘ⟩ := polyLift_listProd P p.T.base _ _ H (hTs H hH).2
      rw [(hTs H hH).1] at hΘ
      exact ⟨Θ, fun _ => hΘ⟩
    · obtain ⟨Θ, -⟩ := (GlobalTheory.T.polyLift_one_mono_mul Wp Wq P p.T.base).1
      exact ⟨Θ, fun h => absurd h hH⟩
  choose lf hlf using hlift
  refine ⟨C, J, Ts.map lf, hC, ?_, ?_⟩
  · intro Θ hΘ
    obtain ⟨H, hH, rfl⟩ := List.mem_map.1 hΘ
    exact (hlf H hH).1
  · rintro φ f ⟨hφ, hf⟩ e c hc hG
    obtain ⟨hm1, hm2⟩ := GlobalTheory.T.radial_picture_smul_cutoff_G_multiplier Wp Wq P p.T.base φ f
    obtain ⟨hsl, hcpt⟩ := hm1 hφ
    obtain ⟨W, hW⟩ := mulG_exists Wp Wq P p.T.base X μ L st p.l0 d hD hNF φ hsl
    obtain ⟨⟨ε, hε, hN⟩, -⟩ := Formalism.FourierDecayAlt.P.compact_support_facts P.k P.r Wp Wq p.T.base f hf
    obtain ⟨Φ, hΦ⟩ := Formalism.FourierDecayAlt.P5.radJFExists Wp Wq P _ _ _ _ p.T.base f p.hP rfl rfl rfl rfl
      ⟨hN.2.1, ε, hε, hN.2.2⟩
    have hΦ' : Top.IsRadOf P p.T.base Φ f := hΦ
    have hrad := hL w hw _ (hcpt hf) _ (hm2 W Φ hW hΦ') e
    rw [TL.act_e1Vec] at hrad
    obtain ⟨x, hx, hg, hdd, lam, hlam, hV⟩ := GlobalTheory.T.bigCellVector_norm_eq_radialValue_norm Wp Wq P p c hc hG
    have hb := hB φ W hsl hW Φ e x hx
    rw [hg, hdd] at hb
    have hs : ((Ts.map lf).map fun Θ => ‖B.hsVec (p.V (B.opApply Θ f) (TBB.bigPt P.r c))‖).sum =
        lam * (Ts.map fun H => nv (H.prod.1 Φ) x).sum := by
      rw [List.map_map, ← List.sum_map_mul_left]
      congr 1
      refine List.map_congr_left fun H hH => ?_
      exact hV _ _ ((hlf H hH).2 f hf Φ hΦ')
    rw [hV _ _ hrad, hs]
    have := mul_le_mul_of_nonneg_left hb hlam.le
    refine le_trans (le_of_eq rfl) (this.trans (le_of_eq ?_))
    ring

end GlobalTheory.HatNF
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.WordBoundCompactSupportCoefficientsStatement

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

theorem _root_.GlobalTheory.T.wordBound_compactSupportCoefficients : ∀ a : ℕ → ℕ, BasicLiftAll a → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (w : List C.Letter), KB.CutWord P p.l0 w → ∃ (C : ℝ) (J : ℕ) (Θs : List (B.DiffOp P.k P.r Wp Wq)), WordBound p (a P.r) w C J Θs (fun φ f => ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ ∧ KB.CptCoef p.T.base f) := by
  first | exact @GlobalTheory.HatNF.wordBound_cptCoef | exact GlobalTheory.HatNF.wordBound_cptCoef | (intros; apply GlobalTheory.HatNF.wordBound_cptCoef <;> assumption)
end
end
