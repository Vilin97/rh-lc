module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SmoothOnHOfLoc
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegrableCsmul
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyZeroNear
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSetting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RaisingCompactSupport
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbSplitPt
public import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyContinuousOn
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TopFirstOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CoeffOfValues

section

@[expose] public section

open MeasureTheory Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.VandermondePolynomialIntegral

section vand

variable {E : Type*} [AddCommGroup E] [Module ℂ E]

def vN (d : ℕ) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ := Matrix.vandermonde fun m : Fin (d + 1) => ((m : ℕ) : ℂ)

theorem vN_det (d : ℕ) : IsUnit (vN d).det := by
  rw [isUnit_iff_ne_zero, vN, Matrix.det_vandermonde_ne_zero_iff]
  intro a b h
  have h' : ((a : ℕ) : ℂ) = ((b : ℕ) : ℂ) := h
  exact Fin.ext (by exact_mod_cast h')

theorem coeff_of_values (d : ℕ) (c : Fin (d + 1) → E) (n : Fin (d + 1)) :
    ∑ m, (vN d)⁻¹ n m • ∑ n' : Fin (d + 1), ((((m : ℕ) : ℝ) : ℂ) ^ (n' : ℕ)) • c n' = c n := by
  have hinv : (vN d)⁻¹ * vN d = 1 := Matrix.nonsing_inv_mul _ (vN_det d)
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  have e : ∀ n' : Fin (d + 1), ∑ m, ((vN d)⁻¹ n m * (((m : ℕ) : ℝ) : ℂ) ^ (n' : ℕ)) • c n' =
      ((vN d)⁻¹ * vN d) n n' • c n' := by
    intro n'
    rw [← Finset.sum_smul, Matrix.mul_apply]
    congr 1
  simp_rw [e, hinv, Matrix.one_apply, ite_smul, one_smul, zero_smul]
  simp

end vand

variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem poly_integral (μ : Measure X) (d : ℕ) (I : ℝ → X → E) (T : X → E) (hI : ∀ y, Integrable (I y) μ)
    (hP : ∀ᵐ x ∂μ, ∃ c : Fin (d + 1) → E, c (Fin.last d) = T x ∧ ∀ y : ℝ, I y x = ∑ n : Fin (d + 1), ((y : ℂ) ^ (n : ℕ)) • c n) :
    ∃ c : Fin (d + 1) → E, c (Fin.last d) = ∫ x, T x ∂μ ∧
      ∀ y : ℝ, ∫ x, I y x ∂μ = ∑ n : Fin (d + 1), ((y : ℂ) ^ (n : ℕ)) • c n := by
  set W := (vN d)⁻¹ with hW

  set C : Fin (d + 1) → X → E := fun n x => ∑ m, W n m • I ((m : ℕ) : ℝ) x with hC
  have hCint : ∀ n, Integrable (C n) μ := fun n =>
    integrable_finsetSum _ fun m _ => (hI _).smul (W n m)

  have hae : ∀ᵐ x ∂μ, (∀ y : ℝ, I y x = ∑ n : Fin (d + 1), ((y : ℂ) ^ (n : ℕ)) • C n x) ∧ C (Fin.last d) x = T x := by
    filter_upwards [hP] with x ⟨c, hc, hcx⟩
    have hCc : ∀ n, C n x = c n := by
      intro n
      rw [hC]
      simp only
      simp_rw [hcx]
      have := coeff_of_values d c n
      simpa [hW] using this
    refine ⟨fun y => ?_, by rw [hCc, hc]⟩
    rw [hcx y]
    simp_rw [hCc]
  refine ⟨fun n => ∫ x, C n x ∂μ, ?_, fun y => ?_⟩
  · exact integral_congr_ae (hae.mono fun x hx => hx.2)
  · rw [integral_congr_ae (hae.mono fun x hx => hx.1 y)]
    have := integral_finsetSum (μ := μ) Finset.univ (f := fun (n : Fin (d + 1)) x => ((y : ℂ) ^ (n : ℕ)) • C n x)
      (fun n _ => (hCint n).smul _)
    rw [this]
    apply Finset.sum_congr rfl
    intro n _
    rw [integral_smul]

end Formalism.FourierDecayAlt.P.VandermondePolynomialIntegral
end
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.VecVSplit

section

@[expose] public section

open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.VandermondePolynomialIntegral

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem vecV_split [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq)
    (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r) (q : C.LPt)
    (h : D.IsLocPt q (r + 1) ∧ 0 < D.ptG (Tz k r Bs.z * Tz k r Bs.z') r q)
    (h' : ∃ γ ∈ B.GV k r, Zhat k r Bs.z Bs.z' γ = D.ptMatN q (r + 1) ∧ D.IsDFrame Bs ν' m₀ γ) :
    ∃ θL : Mt k r × Mt k r → ℝ, ∀ F : B.Mat k r → (Wq →L[ℂ] Wp), KB.CptCoef Bs F →
      Integrable (lint Bs h'.choose θL F) (Bs.μW.prod Bs.μN) ∧
        D.vecV Bs ν' m₀ F q = ∫ x, lint Bs h'.choose θL F x ∂(Bs.μW.prod Bs.μN) := by
  obtain ⟨c₃, hc₃⟩ := orbJ_domL
  set A : ℝ := max 0 (c₃ * ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) + 1)) with hAdef
  have hγ := h'.choose_spec.1
  have hZ := h'.choose_spec.2.1
  have hGq := Formalism.FourierDecayAlt.P.ptG_spec k r Bs.z Bs.z' q h'.choose h.1 hZ
  have hpos : 0 < Gf k r Bs.z Bs.z' h'.choose := hGq ▸ h.2
  obtain ⟨hmono, hd⟩ := Formalism.FourierDecayAlt.P.Dx2.VV.ptMatN_monoP' q (r + 1) h.1.2 h.1.1
  have hrel := Formalism.FourierDecayAlt.P.relevant_points_holds k r Wp Wq Bs q h'.choose h.1 hγ hZ
  have hZm := hZ.trans hmono
  obtain ⟨θ, maj, hθ, hθL, hθp, hmaj, hdom⟩ := hc₃ k r Wp Wq Bs h'.choose _ _ A hγ hd hZm hpos (le_max_right _ _)
  have hG : Formalism.FourierDecayAlt.P.Dx2.Rad.Good Bs h'.choose _ _ :=
    ⟨Formalism.FourierDecayAlt.P.Dx2.Rad.exists_rho Bs hγ hpos hd hZm, Formalism.FourierDecayAlt.P.Dx2.Rad.u_inj Bs hγ hpos hd hZm,
      fun ρ hρ => Formalism.FourierDecayAlt.P.Dx2.Rad.u_lstg Bs hγ hpos hd hZm hρ⟩
  have hR := Formalism.FourierDecayAlt.P.Dx2.Rad.haar_good Bs hγ hd hG
  refine ⟨fun x => θ (x, 0), fun F hF => ?_⟩
  obtain ⟨cF, hcF0, hb⟩ := Formalism.FourierDecayAlt.P.PBN.gN_bound Bs hF A (le_max_left _ _)
  have hbnd : ∀ᵐ p ∂Bs.μSS, θ p * ‖F (B.sgs p h'.choose)‖ ≤ cF * maj p :=
    hdom F cF hcF0 (fun p hp => hb _ (Formalism.FourierDecayAlt.P.B7.sgs_mem Bs hp hγ))
  have hFc : ContinuousOn F (B.GV k r) := Formalism.FourierDecayAlt.P.B5.ckOn_continuousOn hF.1
  have hm : AEStronglyMeasurable (D.orbIntegrand Bs h'.choose F) Bs.μSS :=
    Formalism.FourierDecayAlt.P.PBE.integrand_aesm' Bs (U := B.GV k r) (fun p hp => Formalism.FourierDecayAlt.P.B7.sgs_mem Bs hp hγ) hFc
  have hi : Integrable (fun p => θ p • D.orbIntegrand Bs h'.choose F p) Bs.μSS := by
    refine Integrable.mono' (hmaj.const_mul cF) (hθ.1.aestronglyMeasurable.smul hm) ?_
    filter_upwards [hbnd, Formalism.FourierDecayAlt.P.Dx2.OrbJ.ae_inSS Bs] with p hp hs
    rw [norm_smul, Real.norm_of_nonneg (hθ.2.1 p)]
    unfold D.orbIntegrand
    rw [norm_smul, Formalism.FourierDecayAlt.P.B7.norm_xi, one_mul]
    exact (mul_le_mul_of_nonneg_left (Formalism.FourierDecayAlt.P.B7.norm_rho_le Bs hs F h'.choose) (hθ.2.1 p)).trans hp
  have hR' := inner_int Bs h'.choose hγ θ hθL hθp maj hmaj cF hFc hbnd
  obtain ⟨hint, heq⟩ := fub Bs h'.choose θ hθL F hi hR'
  refine ⟨hint, ?_⟩
  unfold D.vecV
  rw [dite_eq_left h, dite_eq_left h']
  have hex : ∃ θ', D.IsNormCut Bs h'.choose (D.muR Bs h'.choose (h.1.2 ▸ D.ptPerm q)) θ' ∧
      Integrable (fun p => θ' p • D.orbIntegrand Bs h'.choose F p) Bs.μSS := ⟨θ, hθ, hi⟩
  unfold D.orbJ
  rw [dite_eq_left hex]
  refine (Formalism.FourierDecayAlt.P.orbital_integral_indep_choice k r Wp Wq Bs h'.choose _ hrel hR F _ θ hex.choose_spec.1 hθ
    hex.choose_spec.2 hi).trans heq

end Formalism.FourierDecayAlt.P.VandermondePolynomialIntegral
end
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.PolyTopOf

section

@[expose] public section

open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.VandermondePolynomialIntegral

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem ae_left {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) :
    ∀ᵐ x ∂(Bs.μW.prod Bs.μN), (Matrix.of x.1 : B.Mat k r) ∈ UWset k r Bs.z ∧
      (Matrix.of x.2 : B.Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r := by
  have := Formalism.FourierDecayAlt.P.B6.haar_sigmaFinite Bs.haarN
  have a1 : ∀ᵐ x ∂(Bs.μW.prod Bs.μN), (Matrix.of x.1 : B.Mat k r) ∈ UWset k r Bs.z :=
    Measure.quasiMeasurePreserving_fst.ae (Formalism.FourierDecayAlt.P.B6.haar_ae Bs.haarW)
  have a2 : ∀ᵐ x ∂(Bs.μW.prod Bs.μN), (Matrix.of x.2 : B.Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r :=
    Measure.quasiMeasurePreserving_snd.ae (Formalism.FourierDecayAlt.P.B6.haar_ae Bs.haarN)
  filter_upwards [a1, a2] with x h1 h2 using ⟨h1, h2⟩

theorem polyTop_of (hKA : KrAA) : PBN.PolyTop := by
  intro Wp Wq _ _ _ _ _ _ P p G s h t hs hq hG
  set q : C.LPt := h ++ [(s, t)] with hqdef
  set Bs := p.T.base with hBs
  by_cases hpos : D.IsLocPt q (P.r + 1) ∧ 0 < D.ptG (Tz P.k P.r Bs.z * Tz P.k P.r Bs.z') P.r q
  · by_cases h' : ∃ γ ∈ B.GV P.k P.r, Zhat P.k P.r Bs.z Bs.z' γ = D.ptMatN q (P.r + 1) ∧ D.IsDFrame Bs p.ν' p.m₀ γ
    · obtain ⟨θL, hsplit⟩ := vecV_split Bs p.ν' p.m₀ q hpos h'
      have hγ := h'.choose_spec.1
      have hZ := h'.choose_spec.2.1
      have hGq := Formalism.FourierDecayAlt.P.ptG_spec P.k P.r Bs.z Bs.z' q h'.choose hpos.1 hZ
      have hposG : 0 < Gf P.k P.r Bs.z Bs.z' h'.choose := hGq ▸ hpos.2
      set κ : ℂ := (-1) ^ (s - 1) / t with hκ
      have hA : ∀ y : ℝ, KB.CptCoef Bs (PBN.aaTop Bs y G) := fun y => Formalism.FourierDecayAlt.P.raising_compact_support P.k P.r Wp Wq Bs G y hG
      obtain ⟨c, hc, hcy⟩ := poly_integral (Bs.μW.prod Bs.μN) (D.ptSize h)
        (fun y x => lint Bs h'.choose θL (PBN.aaTop Bs y G) x) (fun x => κ • lint Bs h'.choose θL G x)
        (fun y => (hsplit _ (hA y)).1)
        (by
          filter_upwards [ae_left Bs] with x hx
          obtain ⟨c, hc, hcy⟩ := pt_poly hKA Bs hG h s t hs hq hγ hZ hposG hx
          set a : ℂ := ((θL x : ℝ) : ℂ) * psi P.k P.r Bs.z cStd (Matrix.of x.2) with ha
          set L := ContinuousLinearMap.compL ℂ Wq Wp Wp (Bs.π (Matrix.of x.1)) with hL
          refine ⟨fun n => a • L (c n), ?_, fun y => ?_⟩
          · simp only
            rw [hc, map_smul, smul_comm]
            rfl
          · show a • L (PBG.Kr Bs (PBN.aaTop Bs y G) _) = _

            rw [hcy y, map_sum, Finset.smul_sum]
            apply Finset.sum_congr rfl
            intro n _
            rw [map_smul, smul_comm])
      refine ⟨c, ?_, fun y => ?_⟩
      · rw [hc, integral_smul, ← (hsplit G hG).2]
        rfl
      · show D.vecV Bs p.ν' p.m₀ (PBN.aaTop Bs y G) q = _
        rw [(hsplit _ (hA y)).2, hcy y]
    · refine ⟨fun _ => 0, ?_, fun y => ?_⟩
      · show (0 : Wq →L[ℂ] Wp) = _ • D.vecV Bs p.ν' p.m₀ G q
        unfold D.vecV
        rw [dite_eq_left hpos, dite_eq_right h', smul_zero]
      · show D.vecV Bs p.ν' p.m₀ _ q = _
        unfold D.vecV
        rw [dite_eq_left hpos, dite_eq_right h']
        simp
  · refine ⟨fun _ => 0, ?_, fun y => ?_⟩
    · show (0 : Wq →L[ℂ] Wp) = _ • D.vecV Bs p.ν' p.m₀ G q
      unfold D.vecV
      rw [dite_eq_right hpos, smul_zero]
    · show D.vecV Bs p.ν' p.m₀ _ q = _
      unfold D.vecV
      rw [dite_eq_right hpos]
      simp

end Formalism.FourierDecayAlt.P.VandermondePolynomialIntegral
end
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.RaisingLoweringRelations

section

@[expose] public section

noncomputable section

namespace Formalism.FourierDecayAlt.P.VandermondePolynomialIntegral

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

theorem raising_lowering_relations : KrAA := by
  intro k r Wp Wq _ _ _ _ _ _ Bs F hF u x hx
  obtain ⟨hs, ⟨R, hR⟩, -⟩ := hF
  exact (PBG.kr_AA_cpt Bs hs (Formalism.FourierDecayAlt.P.PBE.isCompact_gN_le k r R)
    (fun g hg hgC => by
      by_contra hne
      exact hgC (hR g hg hne)) r le_rfl u 0 hx).1

end Formalism.FourierDecayAlt.P.VandermondePolynomialIntegral

namespace Formalism.FourierDecayAlt.P

theorem polynomial_top : PBN.PolyTop := VandermondePolynomialIntegral.polyTop_of VandermondePolynomialIntegral.raising_lowering_relations

end Formalism.FourierDecayAlt.P
end
end
end
