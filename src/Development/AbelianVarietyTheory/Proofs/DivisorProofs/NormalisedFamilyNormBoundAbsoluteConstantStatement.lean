module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SignedLogMeans
public import Formalism.LocalToGlobal.GlobalTheory.GL3.PFamily
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ExistsPowPrincipalFractionalIdeal
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaZeroMeanLogNormConjugatesOfWeberStatement
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.PeriodLatticeAgreement
public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.EpsteinZeta.DedekindFactorK
public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.EpsteinZeta.Jacobi
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ThetaWeberStatement
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Tactic.NormNum.Parity
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedFamilyEqTensorPowerVacuumStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumNormConjCmPointsAllEmbeddings
import Formalism.LocalToGlobal.GlobalTheory.GL3.PStdOK

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LatticeDiscriminantEqWeierstrassDiscr

section

@[expose] public section

noncomputable section

namespace GlobalTheory.LatticePeriodEtaProof

open Formalism.MainNotions.TaylorLogMetric GlobalTheory.IndefiniteRowSideFullHecke.PeriodLatticeAgreement
open scoped UpperHalfPlane

theorem lattice_discriminant_eq_weierstrass_discr (Λ : AddSubgroup ℂ) : discr Λ = Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.discr Λ := rfl

theorem latt_eq_closure (ω₁ τ : ℂ) : latt ω₁ τ = AddSubgroup.closure {ω₁, ω₁ * τ} := by
  ext w
  rw [mem_latt, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.jac_mem_closure]
  constructor
  · rintro ⟨m, n, rfl⟩
    exact ⟨![n, m], by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; ring⟩
  · rintro ⟨v, rfl⟩
    exact ⟨v 1, v 0, by ring⟩

theorem discrEta : DiscrEta := by
  intro ω₁ τ h
  rw [lattice_discriminant_eq_weierstrass_discr, latt_eq_closure]
  exact Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.jac_discr ω₁ τ h τ.2

theorem im_conj_mul (ω τ : ℂ) (m n m' n' : ℤ) :
    ((starRingEnd ℂ) (ω * ((m : ℂ) + (n : ℂ) * τ)) * (ω * ((m' : ℂ) + (n' : ℂ) * τ))).im =
      ‖ω‖ ^ 2 * τ.im * ((m * n' - n * m' : ℤ) : ℝ) := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [Complex.mul_im, Complex.mul_re]
  ring

theorem areaEq : AreaEq := by
  intro ω₁ τ h
  have hy : 0 < τ.im := τ.2
  have hω : 0 < ‖ω₁‖ := norm_pos_iff.2 h
  have hc : 0 < ‖ω₁‖ ^ 2 * τ.im := by positivity
  unfold area
  apply IsLeast.csInf_eq
  refine ⟨⟨hc, ω₁ * ((1 : ℤ) + ((0 : ℤ) : ℂ) * (τ : ℂ)), ⟨1, 0, rfl⟩,
    ω₁ * (((0 : ℤ) : ℂ) + ((1 : ℤ) : ℂ) * (τ : ℂ)), ⟨0, 1, rfl⟩, ?_⟩, ?_⟩
  · rw [im_conj_mul]
    norm_num [UpperHalfPlane.coe_im, abs_of_pos hy]
  · rintro a ⟨ha, w₁, ⟨m, n, rfl⟩, w₂, ⟨m', n', rfl⟩, rfl⟩
    rw [im_conj_mul] at ha ⊢
    simp only [UpperHalfPlane.coe_im] at ha ⊢
    rw [abs_mul, abs_of_pos hc]
    have hd : (m * n' - n * m' : ℤ) ≠ 0 := by
      rintro h0
      rw [h0] at ha
      simp at ha
    have h1 : (1 : ℝ) ≤ |((m * n' - n * m' : ℤ) : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hd
    nlinarith

theorem periodEta : PeriodEta := by
  intro ω₁ τ h
  have hω : 0 < ‖ω₁‖ := norm_pos_iff.2 h
  have hπ : 0 < Real.pi := Real.pi_pos
  unfold period
  rw [discrEta ω₁ τ h, areaEq ω₁ τ h]
  have e : ‖(2 * (Real.pi : ℂ) / ω₁) ^ 12 * ModularForm.eta (τ : ℂ) ^ 24‖ =
      ((2 * Real.pi / ‖ω₁‖) ^ 2 * ‖ModularForm.eta (τ : ℂ)‖ ^ 4) ^ 6 := by
    rw [norm_mul, norm_pow, norm_pow, norm_div, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hπ.le]
    norm_num
    ring
  have hx : 0 ≤ (2 * Real.pi / ‖ω₁‖) ^ 2 * ‖ModularForm.eta (τ : ℂ)‖ ^ 4 := by positivity
  rw [e, show ((1 : ℝ) / 6) = ((6 : ℕ) : ℝ)⁻¹ by norm_num, Real.pow_rpow_inv_natCast hx (by norm_num)]
  field_simp
  ring

theorem discrScale : DiscrScale := by
  intro ω₁ τ c h hc
  rw [scale_latt, discrEta _ τ (mul_ne_zero hc h), discrEta ω₁ τ h]
  rw [zpow_neg, show (12 : ℤ) = ((12 : ℕ) : ℤ) from rfl, zpow_natCast]
  field_simp

theorem hasSum_G (L : PeriodPair) {n : ℕ} (hn : 2 < n) :
    HasSum (fun w : {w : ℂ // w ∈ L.lattice.toAddSubgroup ∧ w ≠ 0} => 1 / (w : ℂ) ^ n) (L.G n) := by
  have h := L.hasSum_sumInvPow 0 hn
  simp only [sub_zero, PeriodPair.sumInvPow_zero] at h
  have h1 : HasSum (((L.lattice : Set ℂ)).indicator (fun w : ℂ => 1 / w ^ n)) (L.G n) := by
    rw [← hasSum_subtype_iff_indicator]
    simp only [one_div]
    exact h
  have h2 : ((L.lattice : Set ℂ)).indicator (fun w : ℂ => 1 / w ^ n) =
      ({w : ℂ | w ∈ L.lattice.toAddSubgroup ∧ w ≠ 0}).indicator (fun w : ℂ => 1 / w ^ n) := by
    ext w
    by_cases hw : w = 0
    · subst hw
      simp [Set.indicator, zero_pow (by omega : n ≠ 0)]
    · classical
      have e : (w ∈ (L.lattice : Set ℂ)) ↔ (w ∈ L.lattice.toAddSubgroup ∧ w ≠ 0) :=
        ⟨fun h => ⟨h, hw⟩, fun h => h.1⟩
      simp only [Set.indicator]
      exact if_congr e rfl rfl
  rw [h2, ← hasSum_subtype_iff_indicator] at h1
  exact h1

theorem agreePeriodPair : AgreePeriodPair := by
  intro L
  have hk : ∀ k : ℕ, 2 ≤ k →
      (Summable (fun w : {w : ℂ // w ∈ L.lattice.toAddSubgroup ∧ w ≠ 0} => 1 / (w : ℂ) ^ (2 * k)) ∧
      eisG L.lattice.toAddSubgroup k = L.G (2 * k)) := by
    intro k hk
    have h := hasSum_G L (n := 2 * k) (by omega)
    exact ⟨h.summable, h.tsum_eq⟩
  refine ⟨hk, ?_, ?_⟩
  · rw [g2, PeriodPair.g₂, (hk 2 le_rfl).2]
  · rw [g3, PeriodPair.g₃, (hk 3 (by norm_num)).2]

theorem latticePeriodEta : LatticePeriodEta :=
  ⟨discrEta, areaEq, periodEta, discrScale, agreePeriodPair⟩

end GlobalTheory.LatticePeriodEtaProof
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LatticePeriodEtaObj

section

@[expose] public section

noncomputable section

namespace GlobalTheory.LatticePeriodEtaObj

theorem latticePeriodEta_obj : GlobalTheory.IndefiniteRowSideFullHecke.PeriodLatticeAgreement.LatticePeriodEta :=
  GlobalTheory.LatticePeriodEtaProof.latticePeriodEta

end GlobalTheory.LatticePeriodEtaObj
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaZeroMeanLogLeConstMul

section

@[expose] public section

open Formalism.BasicNotions

namespace GlobalTheory.Theta0MeanLeC

theorem theta0MeanLeC : ∃ C : ℝ, 0 ≤ C ∧ ∀ D : Formalism.BasicNotions.D7, GlobalTheory.IndefiniteRowSideFullHecke.SignedLogMeans.MeanLeC C D :=
  (GlobalTheory.T.thetaZero_mean_log_norm_conjugates_of_weber GlobalTheory.LatticePeriodEtaObj.latticePeriodEta_obj GlobalTheory.ThetaWeberObj.thetaWeberStatement).1.2.2

end GlobalTheory.Theta0MeanLeC
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaZeroMeanLogLeConstMulStatement

section

@[expose] public section

open Formalism.BasicNotions

theorem _root_.GlobalTheory.T.exists_thetaZeroMeanLogLeConstMul : ∃ C : ℝ, 0 ≤ C ∧ ∀ D : Formalism.BasicNotions.D7, GlobalTheory.IndefiniteRowSideFullHecke.SignedLogMeans.MeanLeC C D := by
  first | exact @GlobalTheory.Theta0MeanLeC.theta0MeanLeC | exact GlobalTheory.Theta0MeanLeC.theta0MeanLeC | (intros; apply GlobalTheory.Theta0MeanLeC.theta0MeanLeC <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedFamilyNormBoundAbsoluteConstant

section

@[expose] public section

noncomputable section
namespace GlobalTheory.ColNorms.FamilyBound
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity GlobalTheory.ColNorms

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

theorem genusOne_meanSquare_forms_agree (Λ : AddSubgroup ℂ) (G : ℂ → ℂ) : StandardLatticesGL3.nrm1Sq Λ G = GL3Theta.normSq1 Λ G :=
  (GlobalTheory.Glob.normSq1_eq_nrm1Sq Λ G).symm

theorem conj_normSq (B : Base D cc δ) (χ : IdE D → ℂ) (hc : StandardLatticesGL3.Crv D cc δ) (ht : StandardLatticesGL3.natTie D cc δ (B.eNat χ))
    {N N' : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (hA : admitted D N N' L L') (M : IntermediateField ℚ ℂ) (hD : DataIn D (tor0 D cc δ) M)
    (hcoef : CoefIn D (B.eNat χ N N' L L') M) (ρ : M →ₐ[ℚ] ℂ) {t : ℂ}
    (hT : GL3Theta.IsTwoTorsionPointUnkilled D (lamConj M ρ (lamOf D cc δ)) t) :
    normSq D (torConj D (tor0 D cc δ) M ρ) (La D (torConj D (tor0 D cc δ) M ρ) L L') (fnConj D M ρ (B.eNat χ N N' L L')) =
      GL3Theta.normSq1 (lamConj M ρ (lamOf D cc δ)) (GL3Theta.th0 (lamConj M ρ (lamOf D cc δ)) t) ^ (fF D * N * N') := by
  rw [(GlobalTheory.ConjNorm.useNorm_all D cc δ hc _ B.t0 N N' L L' (StandardLatticesGL3.admissible_self_dual_even hA).1 (StandardLatticesGL3.admissible_self_dual_even hA).2.1 (StandardLatticesGL3.admissible_self_dual_even hA).2.2 _
    (ht _ B.t0 N N' L L' hA) M ρ hD hcoef t hT).1, genusOne_meanSquare_forms_agree]

theorem conj_indep (B : Base D cc δ) (χ : IdE D → ℂ) (hc : StandardLatticesGL3.Crv D cc δ) (ht : StandardLatticesGL3.natTie D cc δ (B.eNat χ)) :
    ThetaNormConjugateIndependent D (tor0 D cc δ) (B.eNat χ) := by
  intro N N' L₁ L₁' L₂ L₂' a₁ a₂ M _ hD c₁ c₂ ρ
  have : NumberField M := NumberField.mk
  obtain ⟨t, hT⟩ := GlobalTheory.Glob.exists_isThetaZero hc hD ρ
  rw [conj_normSq B χ hc ht a₁ M hD c₁ ρ hT, conj_normSq B χ hc ht a₂ M hD c₂ ρ hT]

theorem mean_le_of {C : ℝ} (hC : GlobalTheory.IndefiniteRowSideFullHecke.SignedLogMeans.MeanLeC C D) (B : Base D cc δ) (χ : IdE D → ℂ) (hc : StandardLatticesGL3.Crv D cc δ)
    (ht : StandardLatticesGL3.natTie D cc δ (B.eNat χ)) : ThetaMeanBound D (tor0 D cc δ) C (B.eNat χ) := by
  intro Lsc hL N N' L L' hA M _ hD hcoef
  have : NumberField M := NumberField.mk
  have hex : ∀ ρ : M →ₐ[ℚ] ℂ, ∃ t, GL3Theta.IsTwoTorsionPointUnkilled D (lamConj M ρ (lamOf D cc δ)) t := fun ρ => GlobalTheory.Glob.exists_isThetaZero hc hD ρ
  choose t hT using hex
  have hm := hC cc δ M t ⟨hc.1, hc.2, hD, hT⟩ Lsc hL
  have key : meanLogNormSq D (tor0 D cc δ) L L' M (B.eNat χ N N' L L') =
      ((fF D * N * N' : ℕ) : ℝ) * GlobalTheory.IndefiniteRowSideFullHecke.SignedLogMeans.meanLog M (lamOf D cc δ) t := by
    unfold meanLogNormSq GlobalTheory.IndefiniteRowSideFullHecke.SignedLogMeans.meanLog GlobalTheory.IndefiniteRowSideFullHecke.SignedLogMeans.conjNormSq
    simp_rw [fun ρ => conj_normSq B χ hc ht hA M hD hcoef ρ (hT ρ), Real.log_pow]
    rw [← Finset.mul_sum, mul_div_assoc]
    rfl
  rw [key]
  calc ((fF D * N * N' : ℕ) : ℝ) * GlobalTheory.IndefiniteRowSideFullHecke.SignedLogMeans.meanLog M (lamOf D cc δ) t
      ≤ ((fF D * N * N' : ℕ) : ℝ) * (C * Lsc) := mul_le_mul_of_nonneg_left hm (by positivity)
    _ = C * (fF D : ℝ) * (N : ℝ) * (N' : ℝ) * Lsc := by push_cast; ring

theorem familyNorms_of (hT : FamilyTie) (hM : ∃ C : ℝ, 0 ≤ C ∧ ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.SignedLogMeans.MeanLeC C D) : FamilyNorms := by
  obtain ⟨C, -, hC⟩ := hM
  refine ⟨C, fun D cc δ B χ h1 h2 hcc hδ hχ hY => ?_⟩
  have ht := hT D cc δ B χ h1 h2 hcc hδ hχ hY
  have hc : StandardLatticesGL3.Crv D cc δ := ⟨hcc, hδ⟩
  have h14 := theta_link_holds D cc hcc δ hδ B (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.stdOK B hcc hδ) χ hχ
  exact ⟨h14.1, mean_le_of (hC D) B χ hc ht, conj_indep B χ hc ht, h14.2⟩

theorem familyNorms : FamilyNorms := familyNorms_of GlobalTheory.T.normalisedFamily_eq_tensorPower_vacuum GlobalTheory.T.exists_thetaZeroMeanLogLeConstMul

end GlobalTheory.ColNorms.FamilyBound
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedFamilyNormBoundAbsoluteConstantStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.normalisedFamily_normBound_absoluteConstant : GlobalTheory.ColNorms.FamilyNorms := by
  first | exact @GlobalTheory.ColNorms.FamilyBound.familyNorms | exact GlobalTheory.ColNorms.FamilyBound.familyNorms | (intros; apply GlobalTheory.ColNorms.FamilyBound.familyNorms <;> assumption)
end
end
