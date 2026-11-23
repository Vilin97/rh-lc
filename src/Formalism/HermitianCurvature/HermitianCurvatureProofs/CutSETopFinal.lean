module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDIdentSpec
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSOpR
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRAsm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpMBeta
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpMConseq
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpMContPf
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpMStepAPf
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpMTop
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDRInvFinal
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDRStepA
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDRStepB
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDRvStepB
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatPolyOK
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WCellMemOmPlus
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
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDCCLower
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSPolyProp
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSOpX
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSRhR
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsAdmissibleSplittingCharPairMulTwist
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeylCellConjTransposeMulApply
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSETopR
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SpectralCompositionZero

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSOpRGrp

section

@[expose] public section

open MeasureTheory
open scoped Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

def RDSNicePoly : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (o κ : ℕ)
    (Θ : B.DiffOp k r Wp Wq), CutMP.PolyOp o κ Θ →
      ∀ F : B.Mat k r → (Wq →L[ℂ] Wp), NiceAll D F → NiceAll D (B.opApply Θ F) ∧ NiceAll D (B.opAdj Θ F)

section swap

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

end swap

theorem opProp1_of_poly (hN : RDSNicePoly) {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (D : B.RealPlaceData k r Wp Wq) {o κ : ℕ} {Θ : B.DiffOp k r Wp Wq} (hP : CutMP.PolyOp o κ Θ)
    (hC : B.Commutes D (B.GPos D) Θ) : OpProp1 D Θ := by
  obtain ⟨hS, hG, -⟩ := CutMP.polynomial_decay_admissible k r Wp Wq o κ Θ hP
  refine ⟨hS _, hC, fun ε _ => ⟨κ, Nat.cast_nonneg _, fun T hT => ?_⟩, fun F hF => hN k r Wp Wq D o κ Θ hP F hF⟩
  obtain ⟨-, -, hb⟩ := hG κ le_rfl T hT
  obtain ⟨C₁, hC₁⟩ := hb (B.opOrder Θ + 5)
  exact ⟨C₁, fun u v hu hv hl g hg _ => hC₁ u v hu hv hl g hg⟩

section ffl

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq]
  [NormedSpace ℂ Wq] {z z' : Fin (2 * r + k + 1) → ℂ} {π : Q.Mx k r → (Wp →L[ℂ] Wp)} {π' : Q.Mx k r → (Wq →L[ℂ] Wq)}

theorem ffl_mono {D₁ D₂ : Set (Q.Mx k r)} (h : ∀ g ∈ Q.Glev k r 0, g ∈ D₂ → g ∈ D₁) {J : Q.Mx k r → (Wq →L[ℂ] Wp)}
    (hJ : J ∈ Q.FFl k r z z' π π' 0 D₁) : J ∈ Q.FFl k r z z' π π' 0 D₂ := by
  obtain ⟨h1, h2, h3, h4⟩ := hJ
  refine ⟨fun g₀ hg₀ => h1 g₀ ⟨hg₀.1, h g₀ hg₀.1 hg₀.2⟩, fun g hg n hn => h2 g ⟨hg.1, h g hg.1 hg.2⟩ n hn,
    fun g hg n hn => h3 g ⟨hg.1, h g hg.1 hg.2⟩ n hn, fun g hg u hu u' hu' => h4 g ⟨hg.1, h g hg.1 hg.2⟩ u hu u' hu'⟩

end ffl

theorem rDSOpRGrp_of_nice (hN : RDSNicePoly) : RDSOpRGrp := by
  intro Wp Wq _ _ _ _ _ _ k r D Y σ
  obtain ⟨ε, hε⟩ := CutMP.jDRRadP_of_steps CutMP.residue_first_move_holds CutMP.residue_second_move_holds k r
  obtain ⟨Θ, hP, hO, hR⟩ := CutMP.ri_real (Wp := Wp) (Wq := Wq) D.z D.z' Y (σ * ε)
  have hComm : B.Commutes D (B.GPos D) Θ := by
    intro p hp F hF g hg
    rw [hO] at hF
    have hgG : g ∈ B.GV k r := hg.1
    have hsg : B.sgs p g ∈ B.GV k r := Formalism.FourierDecayAlt.P.B6.conj_product_mem_unitary_group D hp hgG
    rw [hR _ _ (Formalism.FourierDecayAlt.P.B5.ckOn_rho D hp hF) g hgG hgG]
    have e2 : B.rho D p (B.opApply Θ F) g =
        B.rho D p (fun x => (σ * ε) • CutMP.rhatOp k r D.z D.z' Y F x) g := by
      simp only [B.rho]
      rw [hR _ _ hF _ hsg hsg]
    rw [e2, CutMP.inverse_function_positive_holds k r Wp Wq D Y p hp F hF g hg]
    simp only [B.rho, ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp]
  refine ⟨Θ, opProp1_of_poly hN D hP hComm, ?_⟩
  intro J hJ x hx
  have hJ' : J ∈ Q.FFl k r D.z D.z' D.π D.π' 0 (Q.OmPlus k r D.z D.z') :=
    ffl_mono (D₁ := JF.Om k r D.z D.z') (D₂ := Q.OmPlus k r D.z D.z')
      (fun g hg hgO => ⟨by simpa [Q.Glev] using hg.1, hgO⟩) hJ
  have hDom := Formalism.FourierDecayAlt.P.JCx2.rma_isDom_omPlus (k := k) (r := r) D.z_mem D.z'_mem
  have hcell : Q.wCell k r (Fin.last r) x.1 * x.2 ∈ Q.OmPlus k r D.z D.z' :=
    Formalism.FourierDecayAlt.P5.Rad.wCell_mem_omPlus D.z_mem D.z'_mem hx.1 hx.2.1 hx.2.2
  have key := hε Wp Wq D.z D.z' D.π D.π' (Q.OmPlus k r D.z D.z') Y D.z_mem D.z'_mem hDom J hJ' x.1 hx.1 x.2
    hx.2.1 hcell
  rw [← key]
  have hW0 : Q.wCell k r (Fin.last r) x.1 * x.2 ∈ Q.Glev k r 0 :=
    Formalism.FourierDecayAlt.P.Qx3.glev_mul (Formalism.FourierDecayAlt.P.Qx3.wlist_glev hx.1 _)
      (Formalism.FourierDecayAlt.P.Qx3.glev_mono (Fin.zero_le _) hx.2.1)
  have hWG : Q.wCell k r (Fin.last r) x.1 * x.2 ∈ B.GV k r := by simpa [Q.Glev] using hW0.1
  have hCk : B.CkOn ((r + k : ℕ) : ℕ∞) (Q.Glev k r 0 ∩ JF.Om k r D.z D.z') J := by
    intro g₀ hg₀
    obtain ⟨U', F', hU', hg₀U, hc, he⟩ := hJ.1 g₀ hg₀
    refine ⟨U', F', hU', hg₀U, hc.of_le (by exact_mod_cast le_top), fun y hy hyG => he y hy ?_⟩
    simpa [Q.Glev] using hyG
  simp only [Q.resG]
  rw [hR _ J hCk _ ⟨hW0, hWG, hcell⟩ hWG, smul_smul, smul_smul, smul_smul]
  congr 1
  ring

theorem rDSOpRvGrp_of_nice (hN : RDSNicePoly) : RDSOpRvGrp := by
  intro Wp Wq _ _ _ _ _ _ k r D Y σ
  obtain ⟨ε, hε⟩ := CutMP.jDRRadM_of_parts CutMP.mirror_residue_beta_holds CutMP.mirror_residue_top_holds CutMP.GrpMA.mirror_residue_first_move
    CutMP.mirror_residue_second_move (CutMP.jDRvConseq_of CutMP.mirror_residue_continuity) k r
  obtain ⟨Θ, hP, hO, hR⟩ := CutMP.rim_real (Wp := Wp) (Wq := Wq) D.z D.z' Y (σ * ε)
  have hComm : B.Commutes D (B.GPos D) Θ := by
    intro p hp F hF g hg
    rw [hO] at hF
    have hgG : g ∈ B.GV k r := hg.1
    have hsg : B.sgs p g ∈ B.GV k r := Formalism.FourierDecayAlt.P.B6.conj_product_mem_unitary_group D hp hgG
    rw [hR _ _ (Formalism.FourierDecayAlt.P.B5.ckOn_rho D hp hF) g hgG hgG]
    have e2 : B.rho D p (B.opApply Θ F) g =
        B.rho D p (fun x => (σ * ε) • CutMP.rvhatOp k r D.z D.z' Y F x) g := by
      simp only [B.rho]
      rw [hR _ _ hF _ hsg hsg]
    rw [e2, CutMP.inverse_function_minus_holds k r Wp Wq D Y p hp F hF g hg]
    simp only [B.rho, ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp]
  refine ⟨Θ, opProp1_of_poly hN D hP hComm, ?_⟩
  intro J hJ x hx
  have hJ' : J ∈ Q.FFl k r D.z D.z' D.π D.π' 0 (Q.OmPlus k r D.z D.z') :=
    ffl_mono (D₁ := JF.Om k r D.z D.z') (D₂ := Q.OmPlus k r D.z D.z')
      (fun g hg hgO => ⟨by simpa [Q.Glev] using hg.1, hgO⟩) hJ
  have hDom := Formalism.FourierDecayAlt.P.JCx2.rma_isDom_omPlus (k := k) (r := r) D.z_mem D.z'_mem
  have hcell : Q.wCell k r (Fin.last r) x.1 * x.2 ∈ Q.OmPlus k r D.z D.z' :=
    Formalism.FourierDecayAlt.P5.Rad.wCell_mem_omPlus D.z_mem D.z'_mem hx.1 hx.2.1 hx.2.2
  have key := hε Wp Wq D.z D.z' D.π D.π' (Q.OmPlus k r D.z D.z') Y D.z_mem D.z'_mem hDom J hJ' x.1 hx.1 x.2
    hx.2.1 hcell
  rw [← key]
  have hW0 : Q.wCell k r (Fin.last r) x.1 * x.2 ∈ Q.Glev k r 0 :=
    Formalism.FourierDecayAlt.P.Qx3.glev_mul (Formalism.FourierDecayAlt.P.Qx3.wlist_glev hx.1 _)
      (Formalism.FourierDecayAlt.P.Qx3.glev_mono (Fin.zero_le _) hx.2.1)
  have hWG : Q.wCell k r (Fin.last r) x.1 * x.2 ∈ B.GV k r := by simpa [Q.Glev] using hW0.1
  have hCk : B.CkOn ((r + k : ℕ) : ℕ∞) (Q.Glev k r 0 ∩ JF.Om k r D.z D.z') J := by
    intro g₀ hg₀
    obtain ⟨U', F', hU', hg₀U, hc, he⟩ := hJ.1 g₀ hg₀
    refine ⟨U', F', hU', hg₀U, hc.of_le (by exact_mod_cast le_top), fun y hy hyG => he y hy ?_⟩
    simpa [Q.Glev] using hyG
  simp only [Q.resG]
  rw [hR _ J hCk _ ⟨hW0, hWG, hcell⟩ hWG, smul_smul, smul_smul, smul_smul]
  congr 1
  ring

end Formalism.FourierDecayAlt.P.CutSE
end
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSNicePoly

section

@[expose] public section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

theorem spectral_nice_polynomial : RDSNicePoly := by
  intro k r Wp Wq _ _ _ _ _ _ D o κ Θ hΘ F hF
  obtain ⟨-, hGl, -⟩ := CutMP.polynomial_decay_admissible k r Wp Wq o κ Θ hΘ
  have hG : CutMP.GlobCoef Θ (κ : ℝ) := hGl κ le_rfl
  have hκ : (0 : ℝ) ≤ κ := Nat.cast_nonneg κ
  obtain ⟨ε, hε, hFck, hFcc, hFs⟩ := hF
  have hO : IsOpen {g : B.Mat k r | Gf k r D.z D.z' g < ε} := isOpen_lt (Gf_cont _ _) continuous_const
  have hz : ∀ g ∈ B.GV k r, g ∈ {g : B.Mat k r | Gf k r D.z D.z' g < ε} → F g = 0 := by
    intro g hg hgO
    by_contra hne
    exact absurd hgO (not_lt.2 (hFs g hg hne))
  refine ⟨⟨ε, hε, ?_, ?_, ?_⟩, ⟨ε, hε, ?_, ?_, ?_⟩⟩
  · exact (CutMP.class_lower_decay_holds k r Wp Wq Θ κ 0 hκ hG F hFck (fun m => hFcc _ m)).1
  · intro A' m'
    have h := (CutMP.class_lower_decay_holds k r Wp Wq Θ κ (A' + κ) hκ hG F hFck (fun m => hFcc _ m)).2 m'
    rwa [add_sub_cancel_right] at h
  · intro g hg hne
    by_contra hlt
    exact hne (rdsp_opApply_vanish Θ hO hz g hg (not_le.1 hlt))
  · exact (rdsp_opAdj_cc Θ κ hG F hFck 0 (fun m => hFcc _ m)).1
  · intro A' m'
    exact (rdsp_opAdj_cc Θ κ hG F hFck A' (fun m => hFcc _ m)).2 m'
  · intro g hg hne
    by_contra hlt
    exact hne (rdsp_opAdj_vanish Θ hO hz g hg (not_le.1 hlt))

end Formalism.FourierDecayAlt.P.CutSE
end
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSOpRGrpFinal

section

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutSE

theorem spectral_right_group_action : RDSOpRGrp := rDSOpRGrp_of_nice spectral_nice_polynomial

theorem spectral_adjoint_right_group : RDSOpRvGrp := rDSOpRvGrp_of_nice spectral_nice_polynomial

end Formalism.FourierDecayAlt.P.CutSE
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSRhvR

section

@[expose] public section

open MeasureTheory
open scoped Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

namespace RhvRPf

open RhRPf

theorem pbOp_loc {r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (l : Fin r)
    {f₁ f₂ : (Fin r → ℂ) → E} (h : ∀ c ∈ OmX r, f₁ c = f₂ c) {c : Fin r → ℂ} (hc : c ∈ OmX r) :
    pbOp l f₁ c = pbOp l f₂ c := by
  have hev : f₁ =ᶠ[nhds c] f₂ := by
    filter_upwards [(Formalism.FourierDecayAlt.P.Qx3.isOpen_OmX r).mem_nhds hc] with c' hc' using h c' hc'
  simp only [pbOp, wirtBar, if_pos hc, hev.fderiv_eq]

theorem vABs_loc {r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (Y : ℂ) :
    ∀ (i : ℕ) (f₁ f₂ : (Fin r → ℂ) → E), (∀ c ∈ OmX r, f₁ c = f₂ c) →
      ∀ c ∈ OmX r, (vABs r Y i).1 f₁ c = (vABs r Y i).1 f₂ c ∧ (vABs r Y i).2 f₁ c = (vABs r Y i).2 f₂ c
  | 0, f₁, f₂, h, c, hc => ⟨h c hc, rfl⟩
  | i + 1, f₁, f₂, h, c, hc => by
    by_cases hi : i < r
    · simp only [vABs, dif_pos hi]
      have hsub : ∀ c' ∈ OmX r, (Y • f₁ - pbOp ⟨i, hi⟩ f₁) c' = (Y • f₂ - pbOp ⟨i, hi⟩ f₂) c' := by
        intro c' hc'
        simp only [Pi.sub_apply, Pi.smul_apply]
        rw [h c' hc', pbOp_loc _ h hc']
      have hcb : ∀ c' ∈ OmX r, cbOp ⟨i, hi⟩ f₁ c' = cbOp ⟨i, hi⟩ f₂ c' := by
        intro c' hc'
        simp only [cbOp]
        rw [h c' hc']
      have hcbi : ∀ c' ∈ OmX r, cbiOp ⟨i, hi⟩ f₁ c' = cbiOp ⟨i, hi⟩ f₂ c' := by
        intro c' hc'
        simp only [cbiOp]
        rw [h c' hc']
      refine ⟨?_, ?_⟩
      · simp only [Pi.sub_apply]
        rw [(vABs_loc Y i _ _ hsub c hc).1, (vABs_loc Y i _ _ hcb c hc).2]
      · exact (vABs_loc Y i _ _ hcbi c hc).1
    · simp only [vABs, dif_neg hi]
      exact vABs_loc Y i f₁ f₂ h c hc

def rowP {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ} (L : R.LevelData A r) (Y : ℂ) (n : ℕ) :
    Matrix (Fin 2) (Fin 2) A :=
  ((List.ofFn fun l => (L.Tvl Y l)ᵀ).take n).prod

theorem partialProduct_succ {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ} (L : R.LevelData A r) (Y : ℂ) (n : ℕ) (h : n < r) :
    rowP L Y (n + 1) = rowP L Y n * (L.Tvl Y ⟨n, h⟩)ᵀ := by
  unfold rowP
  rw [List.take_add_one, List.prod_append]
  have e : (List.ofFn fun l => (L.Tvl Y l)ᵀ)[n]? = some ((L.Tvl Y ⟨n, h⟩)ᵀ) := by simp [h]
  rw [e]
  simp

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem rowSide_chain (X : ActualOps k r z z' π π') (L : R.LevelData (Pr (RadSp k r z z' π π')) r)
    (hL : IsActualLevel X L) (Y : ℂ) :
    ∀ n, n ≤ r → ∀ (Ψ : RadSp k r z z' π π'), ∀ x ∈ DomR k r z z',
      (((rowP L Y n 0 0).1 Ψ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 =
          crd (vABs r Y n).1 (Ψ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 ∧
        (((rowP L Y n 0 1).1 Ψ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 =
          crd (vABs r Y n).2 (Ψ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2
  | 0, _, Ψ, x, _ => by
    have e : rowP L Y 0 = 1 := by simp [rowP]
    rw [e]
    refine ⟨rfl, ?_⟩
    simp [vABs, crd]
    rfl
  | n + 1, hn, Ψ, x, hx => by
    have h : n < r := by omega
    have ih := rowSide_chain X L hL Y n (by omega)
    have ev : vABs (E := Wq →L[ℂ] Wp) r Y (n + 1) =
        (fun f => (vABs r Y n).1 (Y • f - pbOp ⟨n, h⟩ f) - (vABs r Y n).2 (cbOp ⟨n, h⟩ f),
          fun f => (vABs r Y n).1 (cbiOp ⟨n, h⟩ f)) := by
      show (if h : n < r then _ else _) = _
      rw [dif_pos h]
    have e00 : rowP L Y (n + 1) 0 0 =
        rowP L Y n 0 0 * (algebraMap ℂ _ Y - L.pb ⟨n, h⟩) + rowP L Y n 0 1 * (-L.cb ⟨n, h⟩) := by
      rw [partialProduct_succ L Y n h]
      simp [Matrix.mul_apply, Fin.sum_univ_two, R.LevelData.Tvl]
    have e01 : rowP L Y (n + 1) 0 1 = rowP L Y n 0 0 * L.cbi ⟨n, h⟩ := by
      rw [partialProduct_succ L Y n h]
      simp [Matrix.mul_apply, Fin.sum_univ_two, R.LevelData.Tvl]
    have hpb : JCx2.rma_fst _ (L.pb ⟨n, h⟩) = X.op ⟨n, h⟩ 3 := by rw [hL.2.1]; rfl
    have hcb : JCx2.rma_fst _ (L.cb ⟨n, h⟩) = X.op ⟨n, h⟩ 4 := by rw [hL.2.2.2.2.1]; rfl
    have hcbi : (L.cbi ⟨n, h⟩).1 = X.op ⟨n, h⟩ 5 := by rw [hL.2.2.2.2.2.1]; rfl
    refine ⟨?_, ?_⟩
    · have h1 : (((rowP L Y (n + 1) 0 0).1 Ψ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 =
          (((rowP L Y n 0 0).1 (Y • Ψ - X.op ⟨n, h⟩ 3 Ψ) : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 -
            (((rowP L Y n 0 1).1 (X.op ⟨n, h⟩ 4 Ψ) : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 := by
        change (JCx2.rma_fst _ (rowP L Y (n + 1) 0 0) Ψ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 = _
        rw [e00]
        simp only [map_add, map_mul, map_sub, map_neg, AlgHom.commutes, LinearMap.add_apply,
          LinearMap.sub_apply, LinearMap.neg_apply, mul_apply_eq_comp, Module.algebraMap_end_apply,
          hpb, hcb, ← sub_eq_add_neg, Submodule.coe_sub, Pi.sub_apply]
        rfl
      rw [h1, (ih _ x hx).1, (ih _ x hx).2, ev]
      simp only [Submodule.coe_sub, Submodule.coe_smul, X.op_apply]
      rfl
    · have h1 : (((rowP L Y (n + 1) 0 1).1 Ψ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 =
          (((rowP L Y n 0 0).1 (X.op ⟨n, h⟩ 5 Ψ) : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 := by
        rw [e01, fst_mul_apply, hcbi]
      rw [h1, (ih _ x hx).1, ev]
      simp only [X.op_apply]
      rfl

end RhvRPf

open RhRPf RhvRPf in
theorem spectral_adjoint_rho_action : RDSRhvR := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 hD hl1 hl2 hr Y hY
  obtain ⟨_, _, hL, hQQ, -⟩ := hD
  refine ⟨M.sgn P l0, ?_⟩
  intro J hJ Φ hΦ x hx
  have hT : (L.Tvprod Y)ᵀ = rowP L Y P.r := by
    rw [Formalism.FourierDecayAlt.P.MAx3.Q.Tvprod_transpose L Y, rowP, List.take_of_length_le (by simp)]
  have eA : L.Avr Y = rowP L Y P.r 0 0 := by rw [← hT]; rfl
  have eB : L.Bvr Y = rowP L Y P.r 0 1 := by rw [← hT]; rfl
  have hch := rowSide_chain X L hL Y P.r le_rfl
  have hA : ∀ y ∈ Glev P.k P.r (Fin.last P.r) ∩ Qx8.Dp P.k P.r z z',
      (((L.Avr Y).1 Φ : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 y =
        crd (Q.cmp (vABs P.r Y P.r) 0) (resG P.k P.r (Fin.last P.r) J) x.1 y := by
    intro y hy
    have hxy : (x.1, y) ∈ DomR P.k P.r z z' := ⟨hx.1, hy.1, hy.2⟩
    rw [eA, (hch Φ (x.1, y) hxy).1]
    simp only [crd, Q.cmp, if_true]
    exact (vABs_loc Y P.r _ _ (fun c' hc' => hΦ (c', y) ⟨hc', hy.1, hy.2⟩) x.1 hx.1).1
  have hB : ∀ y ∈ Glev P.k P.r (Fin.last P.r) ∩ Qx8.Dp P.k P.r z z',
      (((L.Bvr Y).1 Φ : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 y =
        crd (Q.cmp (vABs P.r Y P.r) 1) (resG P.k P.r (Fin.last P.r) J) x.1 y := by
    intro y hy
    have hxy : (x.1, y) ∈ DomR P.k P.r z z' := ⟨hx.1, hy.1, hy.2⟩
    rw [eB, (hch Φ (x.1, y) hxy).2]
    simp only [crd, Q.cmp, if_neg (show (1 : Fin 2) ≠ 0 by decide)]
    exact (vABs_loc Y P.r _ _ (fun c' hc' => hΦ (c', y) ⟨hc', hy.1, hy.2⟩) x.1 hx.1).2
  have e1 : (((RhvR L st Y).1 Φ : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 =
      (((L.Dr).1 ((st.QQ Y 0 1).1 ((L.Avr Y).1 Φ) + (st.QQ Y 1 1).1 ((L.Bvr Y).1 Φ)) :
        RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 := rfl
  rw [e1, dr_apply X L hL, st_fst X st l0 hQQ, st_fst X st l0 hQQ]
  simp only [CutMP.dMul, CutMP.rhvGrp, Submodule.coe_add, Pi.add_apply, LinearMap.smul_apply,
    Submodule.coe_smul, Pi.smul_apply, QL, grp]
  rw [X.t_apply Y 0 1 _ x hx, X.t_apply Y 1 1 _ x hx,
    t_slice_congr X Y 0 1 _ _ x hx hA, t_slice_congr X Y 1 1 _ _ x hx hB]
  simp only [smul_add, smul_comm (CutMP.drF P.r x.1) (M.sgn P l0)]

end Formalism.FourierDecayAlt.P.CutSE
end
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSETopFinal

section

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutSE

theorem spectral_operator_R : RDSOpR := rDSOpR_of_parts spectral_right_group_action spectral_operator_X spectral_right_rho_action spectral_composition_zero

theorem spectral_operator_R_adjoint : RDSOpRv := rDSOpRv_of_parts spectral_adjoint_right_group spectral_operator_X spectral_adjoint_rho_action spectral_composition_zero

theorem actual_compact_theorem : Formalism.FourierDecayAlt.P5.ThmPActualCpt := thmPActualCpt_of_R spectral_operator_R spectral_operator_R_adjoint

end Formalism.FourierDecayAlt.P.CutSE
end
end
