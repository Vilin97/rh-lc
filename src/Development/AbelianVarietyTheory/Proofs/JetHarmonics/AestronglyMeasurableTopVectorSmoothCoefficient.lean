module

public import Development.AbelianVarietyTheory.Definitions.Jets.ImportsAlt
public import Formalism.HermitianCurvature.StatementTBB
public import Formalism.HermitianCurvature.StatementB
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdjointnessPolynomiallyBounded
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
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
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactCoefficientAppend
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSetting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.VectorVanishesBigCell
import Mathlib.Tactic.Linter.Style
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DensityConstantOfParts
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsContinuousFrameSectionStatement
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces
public import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.JfBetaAdjCOfLemmaBNorm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyContinuousOn
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLemB
import Formalism.HermitianCurvature.HermitianCurvatureProofs.VectorVanishesBigCell

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.AestronglyMeasurableBesselFunctionContinuousFami

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

namespace GlobalTheory


set_option synthInstance.maxSize 2000 in
theorem besselJ_family_aestronglyMeasurable : ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (α : Type) [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α] [SecondCountableTopology α] (μ : Measure α) [SFinite μ] (U : Set α) (γ : α → B.Mat k r) (V : Set (B.Mat k r)) (H : B.Mat k r → (Wq →L[ℂ] Wp)), IsOpen U → ContinuousOn γ U → (∀ x ∈ U, ∀ q, Bs.inSS q → B.sgs q (γ x) ∈ V) → ContinuousOn H V → AEStronglyMeasurable (fun x => B.JF Bs H (γ x)) (μ.restrict U) := by
  intro k r Wp Wq _ _ _ _ _ _ Bs α _ _ _ _ μ _ U γ V H hU hγ hV hH
  set S : Set (B.SS k r) := {p | Bs.inSS p} with hS
  have hWc := (P.weyl_subgroup_closed k r Bs.z).closed
  have hWc' := (P.weyl_subgroup_closed k r Bs.z').closed
  have hNc := (P.unipotent_radical_closed k r).closed
  have hSc : IsClosed S := by
    have e : S = (fun p : B.SS k r => (p.1.1 : B.Mat k r)) ⁻¹' (UWset k r Bs.z) ∩
        ((fun p : B.SS k r => (p.1.2 : B.Mat k r)) ⁻¹' (Nset k r) ∩
          ((fun p : B.SS k r => (p.2.1 : B.Mat k r)) ⁻¹' (UWset k r Bs.z') ∩
            (fun p : B.SS k r => (p.2.2 : B.Mat k r)) ⁻¹' (Nset k r))) := by
      ext p; rfl
    rw [e]
    exact (hWc.preimage continuous_fst.fst).inter ((hNc.preimage continuous_fst.snd).inter
      ((hWc'.preimage continuous_snd.fst).inter (hNc.preimage continuous_snd.snd)))
  have hxi : Continuous fun p : B.SS k r => B.xiTau Bs (1, 1) p :=
    (P.B7.continuous_xi Bs).comp (by fun_prop : Continuous fun p : B.SS k r => (((1 : ℝ), (1 : ℝ)), p))
  have hπ : ContinuousOn (fun p : B.SS k r => Bs.π (Matrix.of p.1.1)) S :=
    Bs.π_cont.comp (continuous_fst.fst).continuousOn (fun p hp => hp.1)
  have hinv1 : ContinuousOn (fun p : B.SS k r => (Matrix.of p.1.1 : B.Mat k r)⁻¹) S :=
    (P.B6.inv_continuousOn k r).comp (continuous_fst.fst).continuousOn (fun p hp => hp.1.1)
  have hinv2 : ContinuousOn (fun p : B.SS k r => (Matrix.of p.1.2 : B.Mat k r)⁻¹) S :=
    (P.B6.inv_continuousOn k r).comp (continuous_fst.snd).continuousOn (fun p hp => hp.2.1.1)
  have hinv3 : ContinuousOn (fun p : B.SS k r => (Matrix.of p.2.1 : B.Mat k r)⁻¹) S :=
    (P.B6.inv_continuousOn k r).comp (continuous_snd.fst).continuousOn (fun p hp => hp.2.2.1.1)
  have hπ' : ContinuousOn (fun p : B.SS k r => Bs.π' (Matrix.of p.2.1 : B.Mat k r)⁻¹) S :=
    Bs.π'_cont.comp hinv3 (fun p hp => Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv hp.2.2.1)
  have hc4 : ContinuousOn (fun p : B.SS k r => (Matrix.of p.2.2 : B.Mat k r)) S :=
    (continuous_snd.snd).continuousOn
  have hc5 : ContinuousOn (fun p : B.SS k r => (Matrix.of p.2.1 : B.Mat k r)) S :=
    (continuous_snd.fst).continuousOn
  have up : ∀ {β : Type} [TopologicalSpace β] {f : B.SS k r → β}, ContinuousOn f S →
      ContinuousOn (fun y : α × B.SS k r => f y.2) (U ×ˢ S) :=
    fun hf => hf.comp continuous_snd.continuousOn (fun y hy => hy.2)
  have hγ' : ContinuousOn (fun y : α × B.SS k r => γ y.1) (U ×ˢ S) :=
    hγ.comp continuous_fst.continuousOn (fun y hy => hy.1)
  have hsgs : ContinuousOn (fun y : α × B.SS k r => B.sgs y.2 (γ y.1)) (U ×ˢ S) :=
    (((((up hinv1).mul (up hinv2)).mul hγ').mul (up hc4)).mul (up hc5))
  have hFs : ContinuousOn (fun y : α × B.SS k r => H (B.sgs y.2 (γ y.1))) (U ×ˢ S) :=
    hH.comp hsgs (fun y hy => hV y.1 hy.1 y.2 hy.2)
  have hcont : ContinuousOn (fun y : α × B.SS k r => D.orbIntegrand Bs (γ y.1) H y.2) (U ×ˢ S) := by
    unfold D.orbIntegrand B.rho
    exact (up hxi.continuousOn).smul ((up hπ).clm_comp (hFs.clm_comp (up hπ')))
  have hW : SigmaFinite Bs.μW := P.Dx2.MN.sigma_of_haar Bs.haarW
  have hW' : SigmaFinite Bs.μW' := P.Dx2.MN.sigma_of_haar Bs.haarW'
  have hN : SigmaFinite Bs.μN := P.Dx2.MN.sigma_of_haar Bs.haarN
  have hsf : SFinite Bs.μSS := by unfold B.RealPlaceData.μSS; infer_instance
  have h1 := hcont.aestronglyMeasurable (μ := μ.prod Bs.μSS) (hU.measurableSet.prod hSc.measurableSet)
  have hae : ∀ᵐ p ∂Bs.μSS, p ∈ S := P.Dx2.OrbJ.ae_inSS Bs
  rw [← Measure.prod_restrict, Measure.restrict_eq_self_of_ae_mem hae] at h1
  have h2 := h1.integral_prod_right'
  have e : (fun x => B.JF Bs H (γ x)) = fun x => ∫ p, D.orbIntegrand Bs (γ x) H p ∂Bs.μSS := by
    funext x
    rw [← P.bessel_function_trivial_index k r Wp Wq Bs H (γ x)]
    rfl
  rw [e]
  exact h2

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.AestronglyMeasurableBesselFunctionContinuousFamiStatement

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

theorem _root_.GlobalTheory.T.aestronglyMeasurable_besselFunction_continuousFamily : ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (α : Type) [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α] [SecondCountableTopology α] (μ : Measure α) [SFinite μ] (U : Set α) (γ : α → B.Mat k r) (V : Set (B.Mat k r)) (H : B.Mat k r → (Wq →L[ℂ] Wp)), IsOpen U → ContinuousOn γ U → (∀ x ∈ U, ∀ q, Bs.inSS q → B.sgs q (γ x) ∈ V) → ContinuousOn H V → AEStronglyMeasurable (fun x => B.JF Bs H (γ x)) (μ.restrict U) := by
  first | exact @GlobalTheory.besselJ_family_aestronglyMeasurable | exact GlobalTheory.besselJ_family_aestronglyMeasurable | (intros; apply GlobalTheory.besselJ_family_aestronglyMeasurable <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselBigCellPointVectorEqBessel

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

namespace GlobalTheory

theorem vec_bigPt_eq_bessel : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (c : Fin (P.r + 1) → ℂ), (¬ ((∀ a, c a ≠ 0) ∧ TBB.TTp p < Complex.normSq (c (Fin.last P.r))) → p.V H (TBB.bigPt P.r c) = 0) ∧ (((∀ a, c a ≠ 0) ∧ TBB.TTp p < Complex.normSq (c (Fin.last P.r))) → 0 < TBB.Gp p (TBB.bigPt P.r c) ∧ ∀ γ ∈ B.GV P.k P.r, Zhat P.k P.r p.T.base.z p.T.base.z' γ = D.ptMatN (TBB.bigPt P.r c) (P.r + 1) → D.IsDFrame p.T.base p.ν' p.m₀ γ → γ ∈ B.GPos p.T.base ∧ p.V H (TBB.bigPt P.r c) = B.JF p.T.base H γ) := by
  intro Wp Wq _ _ _ _ _ _ P p H c
  refine ⟨fun hn => ?_, fun ⟨hd, hlt⟩ => ?_⟩
  · show D.vecV p.T.base p.ν' p.m₀ H (TBB.bigPt P.r c) = 0
    unfold D.vecV
    rw [dite_eq_right]
    rintro ⟨hl, hG⟩
    refine hn ⟨fun a => ?_, Formalism.FourierDecayAlt.P.PBM.zeta_big _ c hG⟩
    exact (hl.1 (1, c a) (List.mem_ofFn.2 ⟨a, rfl⟩)).2
  · have hc : ∀ a : Fin P.r, c a.castSucc ≠ 0 := fun a => hd _
    have hG : 0 < D.ptG (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') P.r
        (Formalism.FourierDecayAlt.P.PBJ.bigPt c) := by
      unfold D.ptG
      rw [Formalism.FourierDecayAlt.P.PBM.ptMatN_bigPt_head, Formalism.FourierDecayAlt.P.PBJ.Dens.ptMatN_bigPt, Formalism.FourierDecayAlt.P.PBM.hMat_one,
        Matrix.det_diagonal, Matrix.det_diagonal, Fin.prod_univ_castSucc, Complex.normSq_mul]
      have hp : 0 < Complex.normSq (∏ i : Fin P.r, c i.castSucc) :=
        Complex.normSq_pos.2 (Finset.prod_ne_zero_iff.2 fun a _ => hc a)
      have hlt' : Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z' < Complex.normSq (c (Fin.last P.r)) := hlt
      nlinarith [mul_lt_mul_of_pos_left hlt' hp]
    have hl : D.IsLocPt (Formalism.FourierDecayAlt.P.PBJ.bigPt c) (P.r + 1) := Formalism.FourierDecayAlt.P.PBJ.Dens.isLocPt_bigPt c hd
    refine ⟨hG, fun γ hγ hZ hD => ?_⟩
    have hZ' : Zhat P.k P.r p.T.base.z p.T.base.z' γ = D.ptMatN (Formalism.FourierDecayAlt.P.PBJ.bigPt c) (P.r + 1) := hZ
    have hpos : 0 < Gf P.k P.r p.T.base.z p.T.base.z' γ := by
      rw [← Formalism.FourierDecayAlt.P.ptG_spec P.k P.r _ _ (Formalism.FourierDecayAlt.P.PBJ.bigPt c) _ hl hZ']; exact hG
    refine ⟨⟨hγ, hpos⟩, ?_⟩
    show D.vecV p.T.base p.ν' p.m₀ H (Formalism.FourierDecayAlt.P.PBJ.bigPt c) = _
    rw [Formalism.FourierDecayAlt.P.isotropic_vectors_linear_indep P.k P.r Wp Wq p.T.base p.ν' p.m₀ H _ hl γ p.hF hG hγ hZ' hD]
    have hw : (hl.2 ▸ D.ptPerm (Formalism.FourierDecayAlt.P.PBJ.bigPt c) : Equiv.Perm (Fin (P.r + 1))) = 1 :=
      Formalism.FourierDecayAlt.P.PBM.cast_perm_eq_one _ _ (Formalism.FourierDecayAlt.P.PBM.ptPerm_bigPt c hd)
    obtain ⟨hmono, hnz⟩ := Formalism.FourierDecayAlt.P.Dx2.VV.ptMatN_monoP' (Formalism.FourierDecayAlt.P.PBJ.bigPt c) (P.r + 1) hl.2 hl.1
    rw [hw] at hmono
    rw [hw, Formalism.FourierDecayAlt.P.PBM.orbJ_one_eq p.T.base hγ hpos hnz (hZ'.trans hmono) H]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselBigCellPointVectorEqBesselStatement

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

theorem _root_.GlobalTheory.T.besselBigCellPoint_vector_eq_bessel : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (c : Fin (P.r + 1) → ℂ), (¬ ((∀ a, c a ≠ 0) ∧ TBB.TTp p < Complex.normSq (c (Fin.last P.r))) → p.V H (TBB.bigPt P.r c) = 0) ∧ (((∀ a, c a ≠ 0) ∧ TBB.TTp p < Complex.normSq (c (Fin.last P.r))) → 0 < TBB.Gp p (TBB.bigPt P.r c) ∧ ∀ γ ∈ B.GV P.k P.r, Zhat P.k P.r p.T.base.z p.T.base.z' γ = D.ptMatN (TBB.bigPt P.r c) (P.r + 1) → D.IsDFrame p.T.base p.ν' p.m₀ γ → γ ∈ B.GPos p.T.base ∧ p.V H (TBB.bigPt P.r c) = B.JF p.T.base H γ) := by
  first | exact @GlobalTheory.vec_bigPt_eq_bessel | exact GlobalTheory.vec_bigPt_eq_bessel | (intros; apply GlobalTheory.vec_bigPt_eq_bessel <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.BigCellVectorAestronglyMeasurable

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

namespace GlobalTheory

theorem bigCell_vector_aestronglyMeasurable :
    ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
      [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
      (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), ContinuousOn H (B.GPos p.T.base) →
      AEStronglyMeasurable (fun c : Fin (P.r + 1) → ℂ => p.V H (TBB.bigPt P.r c)) volume := by
  intro Wp Wq _ _ _ _ _ _ P p H hH
  classical
  obtain ⟨γ, hγc, hγ⟩ := GlobalTheory.T.exists_continuous_frame_section' P.k P.r Wp Wq p.T.base p.ν' p.m₀ p.hF
  set U : Set (Fin (P.r + 1) → ℂ) := {c | (∀ a, c a ≠ 0) ∧
    Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z' < Complex.normSq (c (Fin.last P.r))} with hU
  have hUo : IsOpen U := by
    have h1 : IsOpen {c : Fin (P.r + 1) → ℂ | ∀ a, c a ≠ 0} := by
      rw [Set.ofPred_forall]
      exact isOpen_iInter_of_finite fun a => isOpen_ne_fun (continuous_apply a) continuous_const
    have h2 : IsOpen {c : Fin (P.r + 1) → ℂ |
        Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z' < Complex.normSq (c (Fin.last P.r))} :=
      isOpen_lt continuous_const (Complex.continuous_normSq.comp (continuous_apply _))
    exact h1.inter h2
  have key : ∀ c ∈ U, γ c ∈ B.GPos p.T.base ∧ p.V H (TBB.bigPt P.r c) = B.JF p.T.base H (γ c) := by
    intro c hc
    obtain ⟨g1, g2, g3⟩ := hγ c hc.1 hc.2
    exact ((GlobalTheory.T.besselBigCellPoint_vector_eq_bessel Wp Wq P p H c).2 hc).2 (γ c) g1 g2 g3
  have hm : AEStronglyMeasurable (fun c => B.JF p.T.base H (γ c)) (volume.restrict U) := by
    refine GlobalTheory.T.aestronglyMeasurable_besselFunction_continuousFamily P.k P.r Wp Wq p.T.base _ volume U γ (B.GPos p.T.base) H hUo hγc ?_ hH
    intro c hc q hq
    have h := (key c hc).1
    exact ⟨Formalism.FourierDecayAlt.P.B7.sgs_mem _ hq h.1, by
      rw [Formalism.FourierDecayAlt.P.JCx1.needs.gf_sgs _ hq]; exact h.2⟩
  have he : (fun c : Fin (P.r + 1) → ℂ => p.V H (TBB.bigPt P.r c)) =
      U.indicator (fun c => B.JF p.T.base H (γ c)) := by
    funext c
    by_cases hc : c ∈ U
    · rw [Set.indicator_of_mem hc]; exact (key c hc).2
    · rw [Set.indicator_of_notMem hc]; exact (GlobalTheory.T.besselBigCellPoint_vector_eq_bessel Wp Wq P p H c).1 hc
  rw [he]
  exact (aestronglyMeasurable_indicator_iff hUo.measurableSet).2 hm

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.LiftedWordContinuousOnGPos

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

namespace GlobalTheory

theorem liftedWord_continuousOn_GPos : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (Cb : ℝ) (w : List C.Letter) (e : Wd.Ix (Fin w.length)) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CutWord P p.l0 w → B.CkOn ⊤ (B.GV P.k P.r) F → ContinuousOn (p.Θ.Θ w e F) (B.GPos p.T.base) := by
  intro Wp Wq _ _ _ _ _ _ P0 p Cb w e F hDD hw hF
  obtain ⟨nf, fib, o, κ, Dop, -, hIn, -, -, hEq⟩ := hDD w hw e
  have hsub : B.GPos p.T.base ⊆ C6.domL p.T.base ∅ :=
    fun g hg => ⟨hg.1, hg.2, fun l hl => by simp at hl⟩
  have hGPG : B.GPos p.T.base ⊆ B.GV P0.k P0.r := fun g hg => hg.1
  have hcont : ContinuousOn (B.opApply Dop F) (B.GPos p.T.base) := by
    apply Formalism.FourierDecayAlt.P.PBE.opApply_continuousOn
    intro T hT
    have h1 : ContinuousOn T.coef (B.GPos p.T.base) :=
      (Formalism.FourierDecayAlt.P.PBE.ckOn_continuousOn' (UU := C6.domL p.T.base ∅) (fun g hg => hg.1) (hIn.1 T hT).1).mono hsub
    have h2 : ContinuousOn (B.Rw T.word F) (B.GPos p.T.base) :=
      (Formalism.FourierDecayAlt.P.B5.ckOn_continuousOn (Formalism.FourierDecayAlt.P.JFxG.ckOn_Rw_top hF T.word T.word_lie)).mono hGPG
    exact h1.clm_apply h2
  exact hcont.congr (fun g hg => hEq F g (hsub hg))

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.AestronglyMeasurableTopVectorSmoothCoefficient

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.TopVec Filter Topology MeasureTheory

namespace GlobalTheory.TopVec

theorem aesm_pi_of_finite {α ι E : Type} [MeasurableSpace α] {μ : Measure α} [Finite ι] [NormedAddCommGroup E]
    (f : α → ι → E) (hf : ∀ i, AEStronglyMeasurable (fun a => f a i) μ) : AEStronglyMeasurable f μ := by
  classical
  have := Fintype.ofFinite ι
  have e : f = fun a => ∑ i, (Pi.single i (f a i) : ι → E) := by
    funext a; rw [Finset.univ_sum_single]
  rw [e]
  refine Finset.aestronglyMeasurable_fun_sum _ fun i _ => ?_
  exact (continuous_single (A := fun _ : ι => E) i).comp_aestronglyMeasurable (hf i)

theorem measurable_nPt_bigPt (k r : ℕ) (TT : ℝ) :
    Measurable fun c : Fin (r + 1) → ℂ => TBB.nPt k r TT (TBB.bigPt r c) := by
  have e : (fun c : Fin (r + 1) → ℂ => TBB.nPt k r TT (TBB.bigPt r c)) = fun c =>
      ∏ i : Fin (r + 1), (if 1 + (i : ℕ) = r + 1 then (‖c (Fin.last r)‖ ^ 2 - TT) ^ (k - 1)
        else ‖c i‖ ^ (2 * (C.Mlev k r (1 + (i : ℕ)) - 2))) := by
    funext c
    unfold TBB.nPt D.ptGG
    rw [Formalism.FourierDecayAlt.P.CutBP.ptLast_bigPt, Complex.normSq_eq_norm_sq]
    unfold TBB.bigPt
    rw [Formalism.FourierDecayAlt.P.CutBP.level_product_of_constant_weights]
  rw [e]
  refine Finset.measurable_prod _ fun i _ => ?_
  split_ifs
  · fun_prop
  · exact ((measurable_pi_apply i).norm).pow_const _

theorem measurable_wPt_bigPt (r : ℕ) (TT : ℝ) :
    Measurable fun c : Fin (r + 1) → ℂ => Top.wPt TT r (TBB.bigPt r c) := by
  have e : (fun c : Fin (r + 1) → ℂ => Top.wPt TT r (TBB.bigPt r c)) = fun c =>
      ‖∏ i, c i‖ ^ 2 / (‖∏ i, c i‖ ^ 2 - TT * ‖∏ i : Fin r, c i.castSucc‖ ^ 2) := by
    funext c
    show Top.wPt TT r (Formalism.FourierDecayAlt.P.PBJ.bigPt c) = _
    unfold Top.wPt D.ptG
    rw [Formalism.FourierDecayAlt.P.PBM.ptMatN_bigPt_head, Formalism.FourierDecayAlt.P.PBJ.Dens.ptMatN_bigPt, Formalism.FourierDecayAlt.P.PBM.hMat_one,
      Matrix.det_diagonal, Matrix.det_diagonal, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  rw [e]
  refine Measurable.div ?_ ?_
  · exact (by fun_prop : Continuous fun c : Fin (r + 1) → ℂ => ‖∏ i, c i‖ ^ 2).measurable
  · exact (by fun_prop : Continuous fun c : Fin (r + 1) → ℂ =>
      ‖∏ i, c i‖ ^ 2 - TT * ‖∏ i : Fin r, c i.castSucc‖ ^ 2).measurable

theorem aestronglyMeasurable_tv : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (P : M.Par) (p : KB.Pl P Wp Wq) (Cb : ℝ) (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter),
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CutWord P p.l0 w → B.CkOn ⊤ (B.GV P.k P.r) H →
    AEStronglyMeasurable (tv p H w) volume := by
  intro Wp Wq _ _ _ _ _ _ P p Cb H w hD hw hH
  unfold tv
  refine (PiLp.continuous_toLp 2 _).comp_aestronglyMeasurable (aesm_pi_of_finite _ fun x => ?_)
  have hV := GlobalTheory.bigCell_vector_aestronglyMeasurable Wp Wq P p _ (GlobalTheory.liftedWord_continuousOn_GPos Wp Wq P p Cb w x.1 H hD hw hH)
  have hc : Continuous fun X : Wq →L[ℂ] Wp => B.hsVec ((p.TP.E x.2).comp X) := by
    unfold B.hsVec
    refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
    exact (p.TP.E x.2).continuous.comp
      (ContinuousLinearMap.apply ℂ Wp (stdOrthonormalBasis ℂ Wq i)).continuous
  refine AEStronglyMeasurable.smul (f := fun c : Fin (P.r + 1) → ℂ =>
    ((Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c)) *
        Top.dH P p.l0 (TBB.TTp p) w (TBB.bigPt P.r c) x.1 x.2 : ℝ) : ℂ)) ?_ (hc.comp_aestronglyMeasurable hV)
  refine (Complex.measurable_ofReal.comp ?_).aestronglyMeasurable
  refine (measurable_nPt_bigPt _ _ _).sqrt.mul ?_
  unfold Top.dH
  exact (((measurable_wPt_bigPt _ _).pow_const _).mul_const _).sqrt

end GlobalTheory.TopVec
end
end
