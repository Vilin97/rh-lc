module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.YGSlice
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SlicesFiniteRegularityBuilt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitTailEstimates
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralConvergesAbs
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WirtingerIntegrationByParts
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelsOfBuiltSetting
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SliceOmBlock
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixOneZero
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSetting
import Mathlib.Algebra.Order.Star.Int
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixMul
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegrableBlockIntegrand

section

@[expose] public section

namespace Formalism.FourierDecayAlt.P.FormNormSumIdentities

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.G MeasureTheory Filter

noncomputable section

section om

variable {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]

theorem maxpow_le_onepow {x y a : ℝ} (hy : 0 ≤ y) (hxy : y ≤ x) (ha : 0 ≤ a) :
    (1 + x) ^ (-a) ≤ (max 1 y) ^ (-a) := by
  refine Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le one_pos (le_max_left _ _)) ?_ (by linarith)
  exact max_le (by linarith) (by linarith)

theorem continuous_lowRow (n : ℕ) : Continuous (fun a : Fin n → ℂ => lowRow a) := by
  unfold lowRow
  exact P.G7.continuous_blk continuous_const continuous_const continuous_id continuous_const

theorem continuous_blkU (n : ℕ) :
    Continuous (fun p : (UT n → ℂ) × (Fin n → ℂ) => blk (upper p.1) p.2 0 1) :=
  P.G7.continuous_blk (P.Dx2.SL.cont_upper.comp continuous_fst) continuous_snd continuous_const continuous_const

theorem continuous_orbM (n : ℕ) (t c : ℂ) : Continuous (orbM n t c) := by
  unfold orbM
  refine Continuous.matrix_mul (Continuous.matrix_mul ((continuous_lowRow n).comp continuous_fst) continuous_const) ?_
  exact (continuous_blkU n).comp (continuous_snd)

theorem integrable_blockIntegrand (β : ℂ) (m : ℕ) (Φ : Mat (m + 2) → V) (t c : ℂ) (ht : t ≠ 0) (K a : ℝ)
    (ha : ((m : ℝ) + 1) * ((m : ℝ) + 4) < a) (hc : ∀ p, ContinuousAt Φ (orbM (m + 1) t c p))
    (hb : ∀ p, ‖Φ (orbM (m + 1) t c p)‖ ≤ K * (1 + ‖orbM (m + 1) t c p‖) ^ (-a)) :
    Integrable (blockIntegrand β (m + 1) Φ t c) (muBlock β (m + 1)) := by
  have ha0 : 0 ≤ a := le_trans (by positivity) ha.le
  have hK : 0 ≤ K := by
    have h := hb 0
    by_contra hn
    have : K * (1 + ‖orbM (m + 1) t c 0‖) ^ (-a) < 0 :=
      mul_neg_of_neg_of_pos (lt_of_not_ge hn) (Real.rpow_pos_of_pos (by positivity) _)
    linarith [norm_nonneg (Φ (orbM (m + 1) t c 0))]
  have hpt : ∀ p : BlockCoord (m + 1),
      ‖blockIntegrand β (m + 1) Φ t c p‖ ≤ K * (max 1 ‖coordMap (m + 1) t p‖) ^ (-a) := by
    intro p
    rw [P.OrbitTailEstimates.norm_blockIntegrand]
    refine (hb p).trans (mul_le_mul_of_nonneg_left ?_ hK)
    exact maxpow_le_onepow (norm_nonneg _) (P.OrbitTailEstimates.norm_coordMap_le (m + 1) t c p) ha0
  obtain ⟨k, hk⟩ := P.G7.muBlock_eq β (m + 1)
  have i3 : BorelSpace (BlockCoord (m + 1)) := inferInstance
  have j1 : (volume : Measure ((UT (m + 1) → ℂ) × (Fin (m + 1) → ℂ))).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  have j2 : (volume : Measure (BlockCoord (m + 1))).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  have hfr : (Module.finrank ℝ (BlockCoord (m + 1)) : ℝ) < a := by
    rw [P.OrbitTailEstimates.finrank_block_cast]; exact ha
  have hI : Integrable (fun q : BlockCoord (m + 1) => (max 1 ‖q‖) ^ (-a)) (muBlock β (m + 1)) := by
    rw [hk]; exact (P.OrbitTailEstimates.integrable_maxpow volume a hfr).smul_measure_nnreal
  have hJ := P.G7.jacobian (m + 1) β t ht
  have hI' : Integrable (fun p : BlockCoord (m + 1) => (max 1 ‖coordMap (m + 1) t p‖) ^ (-a))
      (muBlock β (m + 1)) := by
    have h2 : Integrable (fun q : BlockCoord (m + 1) => (max 1 ‖q‖) ^ (-a))
        (Measure.map (coordMap (m + 1) t) (muBlock β (m + 1))) := hJ ▸ hI.smul_measure_nnreal
    exact (P.G7.embedding_coordMap _ t ht).integrable_map_iff.1 h2
  have hcont : Continuous (blockIntegrand β (m + 1) Φ t c) := by
    unfold blockIntegrand
    refine Continuous.smul ?_ ?_
    · have h1 : Continuous fun p : BlockCoord (m + 1) => G.subSum (lowRow p.1) := by
        unfold G.subSum
        exact continuous_finsetSum _ fun i _ =>
          (continuous_apply _).comp ((continuous_apply _).comp ((continuous_lowRow (m + 1)).comp continuous_fst))
      have h2 : Continuous fun p : BlockCoord (m + 1) => G.superSum (blk (upper p.2.1) p.2.2 0 1) := by
        unfold G.superSum
        exact continuous_finsetSum _ fun i _ =>
          (continuous_apply _).comp ((continuous_apply _).comp ((continuous_blkU (m + 1)).comp continuous_snd))
      exact ((P.G7.continuous_psi β).comp h1).mul ((P.G7.continuous_psi β).comp h2)
    · exact continuous_iff_continuousAt.2 fun p => (hc p).comp (continuous_orbM (m + 1) t c).continuousAt
  exact (hI'.const_mul K).mono' hcont.aestronglyMeasurable (Eventually.of_forall hpt)

theorem integrable_longIntegrand (n : ℕ) (Φ : Mat (n + 1) → V) (z : ℂ) (hz : z ≠ 0) (K a : ℝ)
    (ha : (Module.finrank ℝ (UT (n + 1) → ℂ) : ℝ) < a)
    (hc : ∀ v, ContinuousAt Φ (P.JCTx6.Pos.Zv n z v))
    (hb : ∀ v, ‖Φ (P.JCTx6.Pos.Zv n z v)‖ ≤ K * (1 + ‖P.JCTx6.Pos.Zv n z v‖) ^ (-a)) :
    Integrable (fun v : UT (n + 1) → ℂ => psi U.betaU (superSum (upper v)) • Φ (P.JCTx6.Pos.Zv n z v))
      (muPi U.betaU (UT (n + 1))) := by
  have ha0 : 0 ≤ a := le_trans (Nat.cast_nonneg _) ha.le
  have hK : 0 ≤ K := by
    have h := hb 0
    by_contra hn
    have : K * (1 + ‖P.JCTx6.Pos.Zv n z 0‖) ^ (-a) < 0 :=
      mul_neg_of_neg_of_pos (lt_of_not_ge hn) (Real.rpow_pos_of_pos (by positivity) _)
    linarith [norm_nonneg (Φ (P.JCTx6.Pos.Zv n z 0))]
  have hZc : Continuous (fun v : UT (n + 1) → ℂ => P.JCTx6.Pos.Zv n z v) := by
    show Continuous (fun v : UT (n + 1) → ℂ =>
      ((ptLong (n + 1) z * upper v : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) : Mat (n + 1)))
    exact continuous_const.matrix_mul P.Dx2.SL.cont_upper
  have hΦc : Continuous (fun v : UT (n + 1) → ℂ => Φ (P.JCTx6.Pos.Zv n z v)) :=
    continuous_iff_continuousAt.2 fun v => (hc v).comp hZc.continuousAt
  have hψc : Continuous (fun v : UT (n + 1) → ℂ => psi U.betaU (superSum (upper v))) := by
    have h1 : Continuous fun v : UT (n + 1) → ℂ => superSum (upper v) := by
      unfold superSum
      exact continuous_finsetSum _ fun i _ =>
        (continuous_apply _).comp ((continuous_apply _).comp P.Dx2.SL.cont_upper)
    exact (P.G7.continuous_psi _).comp h1
  have hbound : ∀ v : UT (n + 1) → ℂ, ‖psi U.betaU (superSum (upper v)) • Φ (P.JCTx6.Pos.Zv n z v)‖ ≤
      K * (min 1 ‖z‖) ^ (-a) * (1 + ‖v‖) ^ (-a) := by
    intro v
    rw [norm_smul, P.WirtingerIntegrationByParts.norm_psi, one_mul]
    refine (hb v).trans ?_
    have := mul_le_mul_of_nonneg_left (P.JCTx6.Pos.Zv_decay n hz v ha0) hK
    rw [← mul_assoc] at this
    exact this
  rw [P.Dx2.SL.muPi_betaU]
  apply Integrable.smul_measure_nnreal
  exact ((integrable_one_add_norm ha).const_mul (K * (min 1 ‖z‖) ^ (-a))).mono'
    (hψc.smul hΦc).aestronglyMeasurable (Eventually.of_forall hbound)

theorem clm_omBlock [CompleteSpace V] [CompleteSpace W] (L : V →L[ℂ] W) (β : ℂ) (n : ℕ) (Φ : Mat (n + 1) → V)
    (t c : ℂ) (hI : Integrable (blockIntegrand β n Φ t c) (muBlock β n)) :
    L (OmBlock β n Φ t c) = OmBlock β n (fun Z => L (Φ Z)) t c := by
  unfold OmBlock
  rw [← L.integral_comp_comm hI]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp only [blockIntegrand, L.map_smul]

theorem clm_omLong [CompleteSpace V] [CompleteSpace W] (L : V →L[ℂ] W) (β : ℂ) (n : ℕ) (Φ : Mat (n + 1) → V)
    (z : ℂ) (hI : Integrable (fun v : UT (n + 1) → ℂ => psi β (superSum (upper v)) • Φ (ptLong (n + 1) z * upper v))
      (muPi β (UT (n + 1)))) :
    L (OmLong β n Φ z) = OmLong β n (fun Z => L (Φ Z)) z := by
  unfold OmLong
  rw [← L.integral_comp_comm hI]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [L.map_smul]

end om

end

end Formalism.FourierDecayAlt.P.FormNormSumIdentities
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.SliceOrbitalBlock

section

@[expose] public section

open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.FormNormSumIdentities.GlobalTheory

open Formalism.FourierDecayAlt.P.PBJ

section core

variable {k ρ ph m : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem coreQ (σh : Equiv.Perm (Fin ph)) (dh : Fin ph → ℂ) (σb : Equiv.Perm (Fin m)) (db : Fin m → ℂ)
    (z z' : Fin (2 * (ph + m + ρ) + k + 1) → ℂ) (F : B.Mat k (ph + m + ρ) → E) (γ : B.Mat k ρ)
    (hint : Integrable (fun ξ : U.Xi k (ph + m) 0 ρ (Fub.sigQ σh σb) =>
        U.psiStar (p := ph + m) (s := 0) k ρ (Fub.sigQ σh σb) z z' ξ •
          F (U.gaXi (p := ph + m) (s := 0) k ρ (Fub.sigQ σh σb) (Fub.dQ dh db) ξ (fun a => a.elim0) γ))
      (U.muXi k (ph + m) 0 ρ (Fub.sigQ σh σb))) :
    U.PhiFun (p := ph + m) (s := 0) k ρ (Fub.sigQ σh σb) (Fub.dQ dh db) z z' F (fun a => a.elim0) γ =
      U.PhiTop (p := m) (s := 0) U.betaU σb db
        (fun Z => U.PhiFun (p := ph) (s := m) k ρ σh dh z z' F Z γ) (fun x => x.elim0) := by
  set RR := U.RC k (ph + m) ρ × U.RC k (ph + m) ρ
  have sR := Dx2.SL.sigma_RC k (ph + m) ρ
  set μR : Measure RR := (U.muRC k (ph + m) ρ).prod (U.muRC k (ph + m) ρ)
  have s1 := Fub.sfXiH ph m σh
  have s2 := Fub.sfXiH m 0 σb
  have s3 : SFinite (U.muXiH (ph + m) 0 (Fub.sigQ σh σb)) := Fub.sfXiH (ph + m) 0 (Fub.sigQ σh σb)
  let g : RR × (U.XiH ph m σh × U.XiH m 0 σb) → E := fun y =>
    U.psiH U.betaU σb y.2.2 •
      (U.psiStar (p := ph) (s := m) k ρ σh z z' (y.1, y.2.1) • F (U.gaXi (p := ph) (s := m) k ρ σh dh (y.1, y.2.1)
        (Matrix.of.symm (U.ZjH (p := m) (s := 0) σb db y.2.2 (fun x => x.elim0))) γ))
  let Φ : U.Xi k (ph + m) 0 ρ (Fub.sigQ σh σb) ≃ᵐ RR × (U.XiH ph m σh × U.XiH m 0 σb) :=
    MeasurableEquiv.prodCongr (MeasurableEquiv.refl RR) (Fub.xiE σh σb)
  have hΦ : MeasurePreserving Φ (U.muXi k (ph + m) 0 ρ (Fub.sigQ σh σb)) (μR.prod (volume.prod volume)) :=
    (MeasurePreserving.id μR).prod (Fub.xiE_mp σh σb)
  have hfg : (fun ξ : U.Xi k (ph + m) 0 ρ (Fub.sigQ σh σb) =>
      U.psiStar (p := ph + m) (s := 0) k ρ (Fub.sigQ σh σb) z z' ξ •
        F (U.gaXi (p := ph + m) (s := 0) k ρ (Fub.sigQ σh σb) (Fub.dQ dh db) ξ (fun a => a.elim0) γ)) = g ∘ Φ := by
    funext ξ
    obtain ⟨x, ⟨a0, b0⟩, v, u⟩ := ξ
    rw [Function.comp_apply]
    rw [show Φ (x, ((a0, b0), v, u)) = (x, Fub.xiE σh σb ((a0, b0), v, u)) from rfl, Fub.xiE_apply]
    simp only [g, U.psiStar, U.gaXi, U.ZjH, Dx2.SL.zj_zero, Fub.zj_split, Equiv.apply_symm_apply]
    rw [Fub.psiH_split σh σb U.betaU a0 b0 (Dx2.SL.uniqueT m).toInhabited.default v u, smul_smul]
    congr 1
    have e1 : Formalism.QuantumDeterminants.psi k (ph + m + 0 + ρ) z cStd (U.Rn k (ph + m + 0) ρ x.1) =
        Formalism.QuantumDeterminants.psi k (ph + m + ρ) z cStd (U.Rn k (ph + m) ρ x.1) := rfl
    have e2 : Formalism.QuantumDeterminants.psi k (ph + m + 0 + ρ) z' cStd (U.Rn k (ph + m + 0) ρ x.2) =
        Formalism.QuantumDeterminants.psi k (ph + m + ρ) z' cStd (U.Rn k (ph + m) ρ x.2) := rfl
    rw [e1, e2]
    ring
  have hg : Integrable g (μR.prod (volume.prod volume)) := by
    have := hint; rw [hfg] at this
    exact (hΦ.integrable_comp_emb Φ.measurableEmbedding).mp this
  have hL : U.PhiFun (p := ph + m) (s := 0) k ρ (Fub.sigQ σh σb) (Fub.dQ dh db) z z' F (fun a => a.elim0) γ =
      ∫ y, g y ∂(μR.prod (volume.prod volume)) := by
    unfold U.PhiFun
    rw [hfg]
    exact hΦ.integral_comp' g
  have hA : MeasurePreserving (MeasurableEquiv.prodAssoc : (RR × U.XiH ph m σh) × U.XiH m 0 σb ≃ᵐ _)
      ((μR.prod volume).prod volume) (μR.prod (volume.prod volume)) := Dx2.SL.assoc_mp μR volume volume
  let g' : (RR × U.XiH ph m σh) × U.XiH m 0 σb → E := fun w => g (w.1.1, (w.1.2, w.2))
  have eg : g ∘ (MeasurableEquiv.prodAssoc : (RR × U.XiH ph m σh) × U.XiH m 0 σb ≃ᵐ _) = g' := rfl
  have hg' : Integrable g' ((μR.prod volume).prod volume) := by
    rw [← eg]; exact (hA.integrable_comp_emb MeasurableEquiv.prodAssoc.measurableEmbedding).mpr hg
  have hA' : ∫ y, g y ∂(μR.prod (volume.prod volume)) = ∫ w, g' w ∂((μR.prod volume).prod volume) :=
    (hA.integral_comp' g).symm
  rw [hL, hA', MeasureTheory.integral_prod_symm g' hg']
  unfold U.PhiTop
  rw [show U.muXiH m 0 σb = volume from rfl]
  congr 1
  funext η
  change (∫ x, U.psiH U.betaU σb η • _ ∂(μR.prod volume)) = _
  rw [integral_smul]
  rfl

end core

section wrap

theorem partner_two (h : C.LPt) (n : ℕ) (t c : ℂ) (a : ℕ) (ha : a < D.ptSize h + (n + 1 + 1)) :
    D.ptPartner (h ++ [(n + 1, t), (1, c)]) a =
      if a < D.ptSize h then D.ptPartner h a else if a < D.ptSize h + (n + 1) then D.ptSize h + (n - (a - D.ptSize h))
        else a := by
  rw [show h ++ [(n + 1, t), (1, c)] = (h ++ [(n + 1, t)]) ++ [(1, c)] by simp]
  rw [Dx2.SL.partner_append 1 c (h ++ [(n + 1, t)]) a (by rw [Dx2.SL.ptSize_append]; omega), Dx2.SL.ptSize_append]
  by_cases h1 : a < D.ptSize h + (n + 1)
  · rw [if_pos h1, Dx2.SL.partner_append (n + 1) t h a h1]
    by_cases h2 : a < D.ptSize h
    · rw [if_pos h2, if_pos h2]
    · rw [if_neg h2, if_neg h2, if_pos h1]; omega
  · rw [if_neg h1, if_neg (by omega), if_neg h1]; omega

theorem scal_two (h : C.LPt) (n : ℕ) (t c : ℂ) (a : ℕ) (ha : a < D.ptSize h + (n + 1 + 1)) :
    D.ptScal (h ++ [(n + 1, t), (1, c)]) a =
      if a < D.ptSize h then D.ptScal h a else if a < D.ptSize h + (n + 1) then t else c := by
  rw [show h ++ [(n + 1, t), (1, c)] = (h ++ [(n + 1, t)]) ++ [(1, c)] by simp]
  rw [Dx2.SL.scal_append 1 c (h ++ [(n + 1, t)]) a (by rw [Dx2.SL.ptSize_append]; omega), Dx2.SL.ptSize_append]
  by_cases h1 : a < D.ptSize h + (n + 1)
  · rw [if_pos h1, Dx2.SL.scal_append (n + 1) t h a h1]
    by_cases h2 : a < D.ptSize h
    · rw [if_pos h2, if_pos h2]
    · rw [if_neg h2, if_neg h2, if_pos h1]
  · rw [if_neg h1, if_neg (by omega), if_neg h1]

theorem kapB_mul (n : ℕ) :
    kapB n * ((Real.toNNReal (‖U.betaU‖ / (2 * Real.pi)) ^ (Fintype.card (Fin (n + 1)) +
        (Fintype.card (G.UT (n + 1)) + Fintype.card (Fin (n + 1)))) : NNReal) : ℝ) = 1 := by
  rw [Dx2.SL.norm_betaU, show (2 : ℝ) / (2 * Real.pi) = 1 / Real.pi by field_simp, Dx2.SL.card_UT' n,
    Fintype.card_fin]
  have hp : (0 : ℝ) < Real.pi := Real.pi_pos
  have hN : (n + 1) * (n + 4) / 2 = n + 1 + ((n + 1) * n / 2 + (n + 1)) := by
    have h2 : 2 ∣ (n + 1) * n := (Nat.even_mul_pred_self (n + 1)).two_dvd
    obtain ⟨q, hq⟩ := h2
    have e : (n + 1) * (n + 4) = 2 * (q + 2 * (n + 1)) := by nlinarith
    rw [e, hq]; omega
  unfold kapB
  rw [NNReal.coe_pow, Real.coe_toNNReal _ (by positivity), hN, ← mul_pow, mul_one_div_cancel hp.ne', one_pow]

end wrap

section final

theorem sliceOmBlock : SliceOmBlock := by
  intro k r E _ _ _ z z' F h p n t c hp hle γ hloc hint
  subst hp
  have hP : D.ptSize (h ++ [(n + 1, t), (1, c)]) = D.ptSize h + (n + 1 + 1) := ptSize_two h n t c
  have hlocH : D.IsLocPt h (D.ptSize h) := ⟨fun b hb => hloc.1 b (List.mem_append_left _ hb), rfl⟩
  have hspec := (Formalism.FourierDecayAlt.P.ptPerm_spec _ _ hloc).1
  have hspec' := (Formalism.FourierDecayAlt.P.ptPerm_spec _ _ hlocH).1
  set ph := D.ptSize h with hph
  have hσ : ∀ a : Fin (D.ptSize (h ++ [(n + 1, t), (1, c)])),
      ((Fub.sigQ (D.ptPerm h) (Om.σB (n + 1))) (Fin.cast hP a)).val =
        (D.ptPerm (h ++ [(n + 1, t), (1, c)]) a).val := by
    intro a
    have ha : a.val < ph + (n + 1 + 1) := by have := a.isLt; omega
    rw [hspec a, partner_two h n t c a.val ha]
    by_cases h1 : a.val < ph
    · rw [if_pos h1]
      have e : Fin.cast hP a = Fin.castAdd (n + 1 + 1) ⟨a.val, h1⟩ := Fin.ext rfl
      rw [e, Fub.sigQ_castAdd]
      exact hspec' ⟨a.val, h1⟩
    · rw [if_neg h1]
      have e : Fin.cast hP a = Fin.natAdd ph ⟨a.val - ph, by omega⟩ := Fin.ext (by simp; omega)
      rw [e, Fub.sigQ_natAdd, Fin.val_natAdd]
      by_cases h2 : a.val < ph + (n + 1)
      · rw [if_pos h2]
        have e2 : (⟨a.val - ph, by omega⟩ : Fin (n + 1 + 1)) = Fin.castAdd 1 ⟨a.val - ph, by omega⟩ := Fin.ext rfl
        rw [e2, Om.σB, Fub.sigQ_castAdd, Fin.val_castAdd]
        simp only [Fin.revPerm_apply, Fin.val_rev]
        omega
      · rw [if_neg h2]
        have e2 : (⟨a.val - ph, by omega⟩ : Fin (n + 1 + 1)) = Fin.natAdd (n + 1) (0 : Fin 1) :=
          Fin.ext (by simp; omega)
        rw [e2, Om.σB, Fub.sigQ_natAdd, Fin.val_natAdd]
        simp
        omega
  have hd : ∀ a : Fin (D.ptSize (h ++ [(n + 1, t), (1, c)])),
      Fub.dQ (D.ptDiag h) (Fub.dQ (fun _ : Fin (n + 1) => t) (fun _ : Fin 1 => c)) (Fin.cast hP a) =
        D.ptDiag (h ++ [(n + 1, t), (1, c)]) a := by
    intro a
    have ha : a.val < ph + (n + 1 + 1) := by have := a.isLt; omega
    simp only [D.ptDiag]
    rw [scal_two h n t c a.val ha]
    by_cases h1 : a.val < ph
    · rw [if_pos h1]
      have e : Fin.cast hP a = Fin.castAdd (n + 1 + 1) ⟨a.val, h1⟩ := Fin.ext rfl
      rw [e, Fub.dQ, Fin.addCases_left]; rfl
    · rw [if_neg h1]
      have e : Fin.cast hP a = Fin.natAdd ph ⟨a.val - ph, by omega⟩ := Fin.ext (by simp; omega)
      rw [e, Fub.dQ, Fin.addCases_right]
      by_cases h2 : a.val < ph + (n + 1)
      · rw [if_pos h2]
        have e2 : (⟨a.val - ph, by omega⟩ : Fin (n + 1 + 1)) = Fin.castAdd 1 ⟨a.val - ph, by omega⟩ := Fin.ext rfl
        rw [e2, Fub.dQ, Fin.addCases_left]
      · rw [if_neg h2]
        have e2 : (⟨a.val - ph, by omega⟩ : Fin (n + 1 + 1)) = Fin.natAdd (n + 1) (0 : Fin 1) :=
          Fin.ext (by simp; omega)
        rw [e2, Fub.dQ, Fin.addCases_right]
  obtain ⟨hT1, hT2⟩ := Dx2.SL.phi_transport (k := k) (ρ := r - D.ptSize (h ++ [(n + 1, t), (1, c)])) hP _ _ hσ _ _ hd
    (D.castV (by omega) z) (D.castV (by omega) z') (D.castF (by omega) F) γ
  have hc := coreQ (k := k) (ρ := r - D.ptSize (h ++ [(n + 1, t), (1, c)])) (D.ptPerm h) (D.ptDiag h) (Om.σB (n + 1))
    (Fub.dQ (fun _ : Fin (n + 1) => t) (fun _ : Fin 1 => c)) _ _ _ γ (hT1 hint)
  unfold D.sliceAt
  rw [dite_eq_left hle, hT2, hc, Om.omBlock_eq, smul_smul, ← Complex.ofReal_mul]
  rw [kapB_mul n, Complex.ofReal_one, one_smul]
  simp only [Dx2.SL.castV_castV, Dx2.SL.castF_castF]

end final

end Formalism.FourierDecayAlt.P.FormNormSumIdentities.GlobalTheory

theorem Formalism.FourierDecayAlt.P.slice_orbital_block : Formalism.FourierDecayAlt.P.FormNormSumIdentities.SliceOmBlock := Formalism.FourierDecayAlt.P.FormNormSumIdentities.GlobalTheory.sliceOmBlock
end
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.SliceGermPoints

section

@[expose] public section

namespace Formalism.FourierDecayAlt.P.FormNormSumIdentities

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.G MeasureTheory

noncomputable section

section tr

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem phiFun_tr {k p s ρ ρ' r : ℕ} (hρ : ρ = ρ') (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ)
    (z z' : Fin (2 * r + k + 1) → ℂ) (F : B.Mat k r → E) (e : r = p + s + ρ) (e' : r = p + s + ρ')
    (Z : G.Mat s) (γ : B.Mat k ρ) :
    U.PhiFun k ρ' σ d (D.castV e' z) (D.castV e' z') (D.castF e'.symm F) Z (D.castM hρ γ) =
      U.PhiFun k ρ σ d (D.castV e z) (D.castV e z') (D.castF e.symm F) Z γ := by
  subst hρ
  rw [Formalism.FourierDecayAlt.P.JCTx5.castM_rfl]

end tr

theorem finrank_UT_lt (m : ℕ) (a : ℝ) (ha : ((m : ℝ) + 1) * ((m : ℝ) + 4) < a) :
    (Module.finrank ℝ (UT (m + 1 + 1) → ℂ) : ℝ) < a := by
  have h1 : Module.finrank ℝ (UT (m + 1 + 1) → ℂ) = Fintype.card (UT (m + 1 + 1)) * 2 := by
    rw [Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex]
  have h2 := Formalism.FourierDecayAlt.P.Dx2.SL.card_UT (m + 1 + 1)
  have h3 : ((Fintype.card (UT (m + 1 + 1)) * 2 : ℕ) : ℝ) = ((m : ℝ) + 2) * ((m : ℝ) + 1) := by
    have : Fintype.card (UT (m + 1 + 1)) * 2 = (m + 2) * (m + 1) := by
      rw [mul_comm, h2, show m + 1 + 1 - 1 = m + 1 by omega]
    rw [this]; push_cast; ring
  rw [h1, h3]
  nlinarith

end

end Formalism.FourierDecayAlt.P.FormNormSumIdentities

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.G MeasureTheory Formalism.FourierDecayAlt.P.FormNormSumIdentities

theorem slice_germ_points : Formalism.FourierDecayAlt.P.FormNormSumIdentities.YGSlice := by
  intro k r E _ _ _ z z' F h' m ρ e1 V _ _ _ Φ L γ Kc K a hh' hKc ha hΦ hL q hq hint
  have hW : (G.wMat (m + 1)).det ≠ 0 := (Formalism.FourierDecayAlt.P.Ux3.wMat_det (m + 1)).ne_zero
  rcases q with ⟨t, c⟩ | w0
  · obtain ⟨ht, hcK⟩ := hq
    have hc0 : c ≠ 0 := by
      rintro rfl; apply hKc; simpa using hcK
    have hne : ∀ p, G.detM (G.orbM (m + 1) t c p) ≠ 0 := by
      intro p; rw [Formalism.FourierDecayAlt.P.OrbitTailEstimates.detM_orbM]
      exact mul_ne_zero hW (fun h0 => hKc (h0 ▸ hcK))
    have himg : ∀ p, G.detM (G.orbM (m + 1) t c p) ∈ (fun D => (G.wMat (m + 1)).det * D) '' Kc :=
      fun p => ⟨c * t ^ (m + 1), hcK, (Formalism.FourierDecayAlt.P.OrbitTailEstimates.detM_orbM _ _ _ _).symm⟩
    have hI := integrable_blockIntegrand U.betaU m Φ t c ht K a ha (fun p => (hΦ _ (hne p)).1)
      (fun p => (hΦ _ (hne p)).2)
    show L (((kapB m : ℝ) : ℂ) • G.OmBlock U.betaU (m + 1) Φ t c) = _
    rw [L.map_smul, clm_omBlock L U.betaU (m + 1) Φ t c hI]
    have hloc : D.IsLocPt (ptG h' m (Sum.inl (t, c))) (D.ptSize (ptG h' m (Sum.inl (t, c)))) := by
      refine ⟨fun b hb => ?_, rfl⟩
      simp only [ptG, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with hb | hb | hb
      · exact hh'.1 b hb
      · subst hb; exact ⟨by omega, ht⟩
      · subst hb; exact ⟨le_rfl, hc0⟩
    have hle : D.ptSize (ptG h' m (Sum.inl (t, c))) ≤ r := by rw [ptSize_ptG]; omega
    have hSB := Formalism.FourierDecayAlt.P.slice_orbital_block k r E z z' F h' (ptG h' m (Sum.inl (t, c))) m t c rfl hle
      (D.castM (by rw [ptSize_ptG]; omega) γ) hloc hint
    rw [hSB]
    congr 1
    unfold G.OmBlock
    congr 1
    funext p
    unfold G.blockIntegrand
    congr 1
    have hp := hL _ (hne p) (himg p)
    simp only [G.orbM] at hp
    exact hp.trans (phiFun_tr (by rw [ptSize_ptG]; omega) _ _ z z' F _ _ _ γ).symm
  · obtain ⟨D0, hDK, hz⟩ := hq
    have hz0 : w0 ≠ 0 := by
      rintro rfl
      apply hKc
      have : (0 : ℂ) = (-1) ^ (m + 3) * D0 := by simpa using hz
      have h1 : D0 = 0 := by
        rcases mul_eq_zero.1 this.symm with h | h
        · exact absurd h (pow_ne_zero _ (by norm_num))
        · exact h
      exact h1 ▸ hDK
    have hne : ∀ v, G.detM (Formalism.FourierDecayAlt.P.JCTx6.Pos.Zv (m + 1) w0 v) ≠ 0 := by
      intro v
      have := Formalism.FourierDecayAlt.P.OrbitTailEstimates.detM_longM m w0 D0 hz v
      show G.detM (Formalism.FourierDecayAlt.P.OrbitTailEstimates.longM (m + 1 + 1) w0 v) ≠ 0
      rw [this]
      exact mul_ne_zero hW (fun h0 => hKc (h0 ▸ hDK))
    have himg : ∀ v, G.detM (Formalism.FourierDecayAlt.P.JCTx6.Pos.Zv (m + 1) w0 v) ∈ (fun D => (G.wMat (m + 1)).det * D) '' Kc :=
      fun v => ⟨D0, hDK, (Formalism.FourierDecayAlt.P.OrbitTailEstimates.detM_longM m w0 D0 hz v).symm⟩
    have hI := integrable_longIntegrand (m + 1) Φ w0 hz0 K a (finrank_UT_lt m a ha)
      (fun v => (hΦ _ (hne v)).1) (fun v => (hΦ _ (hne v)).2)
    show L (((Real.pi ^ ((m + 2) * (m + 1) / 2) : ℝ) : ℂ) • G.OmLong U.betaU (m + 1) Φ w0) = _
    rw [L.map_smul, clm_omLong L U.betaU (m + 1) Φ w0 hI]
    have hloc : D.IsLocPt (ptG h' m (Sum.inr w0)) (D.ptSize (ptG h' m (Sum.inr w0))) := by
      refine ⟨fun b hb => ?_, rfl⟩
      simp only [ptG, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with hb | hb
      · exact hh'.1 b hb
      · subst hb; exact ⟨by omega, hz0⟩
    have hle : D.ptSize (ptG h' m (Sum.inr w0)) ≤ r := by rw [ptSize_ptG]; omega
    have hSO := Formalism.FourierDecayAlt.P.slice_measure_identity k r E z z' F h' (ptG h' m (Sum.inr w0)) (m + 1) w0 rfl hle
      (D.castM (by rw [ptSize_ptG]; omega) γ) hloc hint
    rw [hSO]
    congr 1
    unfold G.OmLong
    congr 1
    funext v
    congr 1
    have hp := hL _ (hne v) (himg v)
    exact hp.trans (phiFun_tr (by rw [ptSize_ptG]; omega) _ _ z z' F _ _ _ γ).symm

end Formalism.FourierDecayAlt.P
end
end
