module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopDomPtw
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFLeibAsm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFLeib
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutoffIteratedFDerivBounded
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HomogeneityNaturalDegree
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFLeibExp
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFLeibOps
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSetting
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyContinuousOn
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFLeibBd

section

@[expose] public section

open Matrix MeasureTheory Filter Topology
open scoped ContDiff ComplexConjugate ENNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section bd

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem nfLeibBd_term (Bs : B.RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → B.Mat k r → C6.EndH Wp Wq)
    (hfib : ∀ j, C6.FibBound Bs (fib j)) {o κ : ℕ} {Dop : B.DiffOp k r Wp Wq} (hIn : C6.InDDPlus Bs fib ∅ o κ Dop)
    (T' : B.DTerm k r Wp Wq) (hT' : LeibTerm Bs Dop T') {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (F : B.Mat k r → (Wq →L[ℂ] Wp)) (A b : ℝ), B.CCle A o F b →
      ∀ g ∈ B.GV k r, ε ≤ Gf k r Bs.z Bs.z' g →
        ‖T'.coef g (B.Rw T'.word F g)‖ ≤
          K * b * B.gN g ^ ((κ : ℝ) + 3 * ((r : ℝ) + 1) * o + (2 * (r : ℝ) + 2) * o - A) := by
  obtain ⟨T, hT, Pc, j, hPc, hsub, hco'⟩ := hT'
  obtain ⟨Pp, a, bb, c, es, hP, hab, hlen, hlie, hco⟩ := hIn.2.2 T hT
  set S : Set (B.Mat k r) := {g | g ∈ B.GV k r ∧ ε ≤ Gf k r Bs.z Bs.z' g} with hSdef
  set c₀ : ℝ := min ε (ε ^ 2) with hc₀
  have hc₀p : 0 < c₀ := lt_min hε (by positivity)
  have hSD : ∀ g ∈ S, ∀ l, (l ∈ (∅ : Finset (Fin (r + 2))) ∨ l = Fin.last (r + 1)) →
      c₀ ≤ Complex.normSq (Dmin k r Bs.z Bs.z' g l) := by
    intro g hg l hl
    rcases hl with hl | rfl
    · simp at hl
    · have := Formalism.FourierDecayAlt.P.gram_function_last_minor k r Bs.z Bs.z' Bs.T_pos.le Bs.T'_pos.le g ε hg.2
      exact (min_le_left _ _).trans this
  have hSGf : ∀ g ∈ S, c₀ ≤ Complex.normSq ((Gf k r Bs.z Bs.z' g : ℝ) : ℂ) := by
    intro g hg
    rw [Complex.normSq_ofReal]
    have h1 := hg.2
    have : ε ^ 2 ≤ Gf k r Bs.z Bs.z' g * Gf k r Bs.z Bs.z' g := by nlinarith
    exact (min_le_right _ _).trans this
  have hcU := P.AdmissibleLieWords.ubl_coefP Bs fib hfib ∅ Pp a bb c es hP hab hlie hε (fun g hg => hg) hc₀p hSD hSGf 0
  obtain ⟨⟨Cc, hCc0, hUB⟩, -⟩ := hcU
  set fo := (es.map fun e => e.2.length).sum with hfo
  obtain ⟨CP, hCP0, hCP⟩ := hPc.2 [] (fun x hx => by simp at hx)
  set D : ℕ := (2 * r + 2) * T.word.length with hD
  set cw : ℝ := (T'.word.map P.BetaSesquilinearity.nz).prod with hcw
  have hcw0 : 0 ≤ cw := List.prod_nonneg fun x hx => by
    obtain ⟨X, _, rfl⟩ := List.mem_map.1 hx; exact (P.BetaSesquilinearity.nz_pos X).le
  refine ⟨CP * ε⁻¹ ^ j * Cc * cw, by positivity, fun F A b hF g hg hgε => ?_⟩
  have hgS : g ∈ S := ⟨hg, hgε⟩
  have hgp := P.BetaSesquilinearity.gN_pos hg
  have hg1 := P.BetaSesquilinearity.gN_ge_one hg
  have hGpos : 0 < Gf k r Bs.z Bs.z' g := lt_of_lt_of_le hε hgε
  have hgd : g ∈ C6.domL Bs ∅ := ⟨hg, hGpos, fun l hl => by simp at hl⟩
  have hAdm0 : PI.UnitaryCorollaryDerivatives.CRH.admitted (k := k) (r := r) 0 [] := ⟨[], [], by simp, by simp, by simp, by simp [P.BetaSesquilinearity.wL, P.BetaSesquilinearity.wR]⟩
  have hc1 : ‖T.coef g‖ ≤ Cc * B.gN g ^ (κ + 3 * (r + 1) * fo + 3 * (r + 1) * 0) := by
    have h := hUB [] hAdm0 g hgS
    have e : P.BetaSesquilinearity.Dw [] (fun g => (Pp g * C6.monoM Bs a bb c g) • C6.Epart fib es g) g =
        (Pp g * C6.monoM Bs a bb c g) • C6.Epart fib es g := rfl
    rw [e] at h
    rw [hco g hgd]
    simpa using h
  have hb0 : 0 ≤ b := by
    have h := hF.2 [] [] (by simp) (by simp) (by simp) g hg
    exact le_trans (by positivity) h
  have hc2 : ‖B.Rw T'.word F g‖ ≤ cw * (b * B.gN g ^ (-A)) := by
    rw [P.BetaSesquilinearity.Rw_scale]
    simp only
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hcw0]
    apply mul_le_mul_of_nonneg_left _ hcw0
    have hunit : ∀ X ∈ T'.word.map P.BetaSesquilinearity.nrm, B.unitLie k r X := fun X hX => by
      obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX; exact P.BetaSesquilinearity.nrm_unit (T'.word_lie Y hY)
    have hl' : T'.word.length ≤ T.word.length := hsub.length_le
    have h := hF.2 [] (T'.word.map P.BetaSesquilinearity.nrm) (by simp) hunit (by simp; omega) g hg
    have e : B.dLR [] (T'.word.map P.BetaSesquilinearity.nrm) F g = B.Rw (T'.word.map P.BetaSesquilinearity.nrm) F g := rfl
    rw [e] at h
    have hpw : 0 < B.gN g ^ A := Real.rpow_pos_of_pos hgp _
    rw [Real.rpow_neg hgp.le, ← div_eq_mul_inv, le_div_iff₀ hpw, mul_comm]
    exact h
  have hc3 : ‖Pc g‖ ≤ CP * B.gN g ^ D := by
    have := hCP g hg
    simpa [P.B4.W_nil] using this
  have hc4 : ‖(((Gf k r Bs.z Bs.z' g : ℝ) : ℂ))⁻¹ ^ j‖ ≤ ε⁻¹ ^ j := by
    rw [norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hGpos]
    exact pow_le_pow_left₀ (by positivity) (inv_anti₀ hε hgε) j
  have hfo' : fo ≤ o := by omega
  have hwo : T.word.length ≤ o := by omega
  rw [hco' g hgd, ContinuousLinearMap.smul_apply, norm_smul, norm_mul]
  calc ‖Pc g‖ * ‖(((Gf k r Bs.z Bs.z' g : ℝ) : ℂ))⁻¹ ^ j‖ * ‖T.coef g (B.Rw T'.word F g)‖
      ≤ (CP * B.gN g ^ D) * ε⁻¹ ^ j * (‖T.coef g‖ * ‖B.Rw T'.word F g‖) := by
        gcongr
        exact (T.coef g).le_opNorm _
    _ ≤ (CP * B.gN g ^ D) * ε⁻¹ ^ j *
          ((Cc * B.gN g ^ (κ + 3 * (r + 1) * fo + 3 * (r + 1) * 0)) * (cw * (b * B.gN g ^ (-A)))) := by
        gcongr
    _ = CP * ε⁻¹ ^ j * Cc * cw * b *
          (B.gN g ^ (((D + (κ + 3 * (r + 1) * fo) : ℕ) : ℝ)) * B.gN g ^ (-A)) := by
        rw [Real.rpow_natCast]; ring_nf
    _ = CP * ε⁻¹ ^ j * Cc * cw * b * B.gN g ^ (((D + (κ + 3 * (r + 1) * fo) : ℕ) : ℝ) - A) := by
        rw [← Real.rpow_add hgp, sub_eq_add_neg]
    _ ≤ CP * ε⁻¹ ^ j * Cc * cw * b *
          B.gN g ^ ((κ : ℝ) + 3 * ((r : ℝ) + 1) * o + (2 * (r : ℝ) + 2) * o - A) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Real.rpow_le_rpow_of_exponent_le hg1
        have h3 : (3 * (r + 1) * fo : ℕ) ≤ 3 * (r + 1) * o := Nat.mul_le_mul_left _ hfo'
        have h4 : ((3 * (r + 1) * fo : ℕ) : ℝ) ≤ ((3 * (r + 1) * o : ℕ) : ℝ) := by exact_mod_cast h3
        have h5 : (D : ℝ) ≤ ((2 * r + 2) * o : ℕ) := by
          rw [hD]; exact_mod_cast Nat.mul_le_mul_left _ hwo
        push_cast at h4 h5 ⊢
        linarith

theorem leibniz_bound_holds : NFLeibBd := by
  unfold NFLeibBd
  intro k r Wp Wq _ _ _ _ _ Bs nf fib o κ Dop hfib hIn L hL ε hε
  induction L with
  | nil =>
    refine ⟨0, le_refl _, ?_⟩
    intro F A b hF g hg hεg
    simp [B.opApply]
  | cons T L ih =>
    obtain ⟨K₁, hK₁, h₁⟩ := nfLeibBd_term Bs fib hfib hIn T (hL T (by simp)) hε
    obtain ⟨K₂, hK₂, h₂⟩ := ih (fun T' hT' => hL T' (by simp [hT']))
    refine ⟨K₁ + K₂, add_nonneg hK₁ hK₂, ?_⟩
    intro F A b hF g hg hεg
    have e1 := h₁ F A b hF g hg hεg
    have e2 := h₂ F A b hF g hg hεg
    have hs : B.opApply (T :: L) F g = T.coef g (B.Rw T.word F g) + B.opApply L F g := by
      simp [B.opApply]
    rw [hs]
    calc _ ≤ ‖T.coef g (B.Rw T.word F g)‖ + ‖B.opApply L F g‖ := norm_add_le _ _
      _ ≤ _ := add_le_add e1 e2
      _ = _ := by ring

end bd

end Formalism.FourierDecayAlt.P.CutBP
end
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFLeibVLin

section

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

theorem nfVLin_comp_sum {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] {ι : Type} (s : Finset ι) (a : Wp →L[ℂ] Wp) (b : Wq →L[ℂ] Wq) (c : ι → ℂ)
    (f : ι → Wq →L[ℂ] Wp) :
    a.comp ((∑ i ∈ s, c i • f i).comp b) = ∑ i ∈ s, c i • a.comp ((f i).comp b) := by
  ext x

  simp [ContinuousLinearMap.sum_apply, map_sum, map_smul]

theorem vector_linearity_holds : NFVLin := by
  obtain ⟨c₃, hc₃⟩ := Formalism.FourierDecayAlt.P.PBE.orbJ_dom
  refine ⟨c₃, ?_⟩
  intro k r Wp Wq _ _ _ _ _ _ Bs ν' m₀ Q c H Hq A hA hcont hdec hH pt hpt hGPoint
  unfold D.vecV
  have h : D.IsLocPt pt (r + 1) ∧ 0 < D.ptG (Tz k r Bs.z * Tz k r Bs.z') r pt := ⟨hpt, hGPoint⟩
  simp only [dif_pos h]
  by_cases h' : ∃ γ ∈ B.GV k r, Zhat k r Bs.z Bs.z' γ = D.ptMatN pt (r + 1) ∧ D.IsDFrame Bs ν' m₀ γ
  · simp only [dif_pos h']
    have hγ := h'.choose_spec.1
    have hZ := h'.choose_spec.2.1
    have hGq := Formalism.FourierDecayAlt.P.ptG_spec k r Bs.z Bs.z' pt h'.choose h.1 hZ
    have hpos : 0 < Gf k r Bs.z Bs.z' h'.choose := hGq ▸ h.2
    have hGeq : D.ptG (Tz k r Bs.z * Tz k r Bs.z') r pt = Gf k r Bs.z Bs.z' h'.choose := by
      rw [hGq]
    obtain ⟨hmono, hd⟩ := Formalism.FourierDecayAlt.P.Dx2.VV.ptMatN_monoP' pt (r + 1) h.1.2 h.1.1
    have hrel := Formalism.FourierDecayAlt.P.relevant_points_holds k r Wp Wq Bs pt h'.choose h.1 hγ hZ
    have horb : ∀ p, Bs.inSS p → B.sgs p h'.choose ∈ B.GPos Bs := fun p hp =>
      ⟨Formalism.FourierDecayAlt.P.B7.sgs_mem Bs hp hγ, by rw [Formalism.FourierDecayAlt.P.JCx1.needs.gf_sgs Bs hp]; exact hpos⟩
    have hZm := hZ.trans hmono
    obtain ⟨θ, maj, hθ, hmaj, hdom⟩ := hc₃ k r Wp Wq Bs h'.choose _ _ A hγ hd hZm hpos hA
    have hG : Formalism.FourierDecayAlt.P.Dx2.Rad.Good Bs h'.choose _ _ :=
      ⟨Formalism.FourierDecayAlt.P.Dx2.Rad.exists_rho Bs hγ hpos hd hZm, Formalism.FourierDecayAlt.P.Dx2.Rad.u_inj Bs hγ hpos hd hZm,
        fun ρ hρ => Formalism.FourierDecayAlt.P.Dx2.Rad.u_lstg Bs hγ hpos hd hZm hρ⟩
    have hR := Formalism.FourierDecayAlt.P.Dx2.Rad.haar_good Bs hγ hd hG

    have hEq : ∀ G : B.Mat k r → (Wq →L[ℂ] Wp),
        Integrable (fun p => θ p • D.orbIntegrand Bs h'.choose G p) Bs.μSS →
        D.orbJ Bs h'.choose (D.muR Bs h'.choose (h.1.2 ▸ D.ptPerm pt)) G =
          ∫ p, θ p • D.orbIntegrand Bs h'.choose G p ∂Bs.μSS := by
      intro G hi
      have hex : ∃ θ', D.IsNormCut Bs h'.choose (D.muR Bs h'.choose (h.1.2 ▸ D.ptPerm pt)) θ' ∧
          Integrable (fun p => θ' p • D.orbIntegrand Bs h'.choose G p) Bs.μSS := ⟨θ, hθ, hi⟩
      unfold D.orbJ
      rw [dif_pos hex]
      exact Formalism.FourierDecayAlt.P.orbital_integral_indep_choice k r Wp Wq Bs h'.choose _ hrel hR G _ θ hex.choose_spec.1 hθ
        hex.choose_spec.2 hi

    have hiq : ∀ q, Integrable (fun p => θ p • D.orbIntegrand Bs h'.choose (Hq q) p) Bs.μSS := by
      intro q
      obtain ⟨C, hC⟩ := hdec q (Gf k r Bs.z Bs.z' h'.choose) hpos
      have hm : AEStronglyMeasurable (D.orbIntegrand Bs h'.choose (Hq q)) Bs.μSS :=
        Formalism.FourierDecayAlt.P.PBE.integrand_aesm' Bs horb (hcont q)
      refine Integrable.mono' (hmaj.const_mul (max C 0)) (hθ.1.aestronglyMeasurable.smul hm) ?_
      refine hdom (Hq q) (max C 0) (le_max_right _ _) fun p hp => ?_
      have hs := horb p hp
      refine (hC _ hs.1 (by rw [Formalism.FourierDecayAlt.P.JCx1.needs.gf_sgs Bs hp])).trans ?_
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (Real.sqrt_nonneg _) _)

    have hae : (fun p => θ p • D.orbIntegrand Bs h'.choose H p) =ᵐ[Bs.μSS]
        fun p => ∑ q, c q (Gf k r Bs.z Bs.z' h'.choose) • (θ p • D.orbIntegrand Bs h'.choose (Hq q) p) := by
      filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS Bs] with p hp
      have hs := horb p hp
      simp only [D.orbIntegrand, B.rho]
      rw [hH _ hs, Formalism.FourierDecayAlt.P.JCx1.needs.gf_sgs Bs hp, nfVLin_comp_sum, Finset.smul_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [smul_comm (B.xiTau Bs (1, 1) p), smul_comm (θ p)]
    have hiH : Integrable (fun p => θ p • D.orbIntegrand Bs h'.choose H p) Bs.μSS :=
      (integrable_finsetSum _ fun q _ => (hiq q).smul (c q (Gf k r Bs.z Bs.z' h'.choose))).congr hae.symm
    have hint : ∀ q ∈ (Finset.univ : Finset (Fin (Q + 1))), Integrable
        (fun a => c q (Gf k r Bs.z Bs.z' h'.choose) • (θ a • D.orbIntegrand Bs h'.choose (Hq q) a)) Bs.μSS :=
      fun q _ => (hiq q).smul (c q (Gf k r Bs.z Bs.z' h'.choose))
    rw [hEq H hiH, integral_congr_ae hae, integral_finsetSum Finset.univ hint, hGeq]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [integral_smul, hEq (Hq q) (hiq q)]
  · simp only [dif_neg h', smul_zero, Finset.sum_const_zero]

end

end Formalism.FourierDecayAlt.P.CutBP
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFLeibMain

section

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutBP

theorem leibniz_vector_estimate_holds : NFLeibV :=
  nfLeibV_of (nfLeibOps_of leibniz_expansion_holds) leibniz_bound_holds vector_linearity_holds

end Formalism.FourierDecayAlt.P.CutBP
end
end
