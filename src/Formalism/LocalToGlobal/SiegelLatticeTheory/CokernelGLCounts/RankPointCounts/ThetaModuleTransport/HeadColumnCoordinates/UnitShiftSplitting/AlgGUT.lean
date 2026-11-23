module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.CoordU
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.ThetaMbeG
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.LocCntUG
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.GraphTransport4
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.SharpSpanCounting.DlRSwapZero
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumAGram
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.CompOfMemR
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.CoordGHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.SharpSpanCounting.GraphTransport
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.DecompU
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumA
public import Formalism.SharpRestriction.CuspSpanNormBounds.LinQRawRange
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.SharpSpanCounting.Common
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.ExistsUnitShift
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.LocCntUGOf

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.CoordGU

section

@[expose] public section

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

namespace Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUG

section Parts

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)
variable {r : ℕ}

theorem unit_gramCU {f f' : Fin (r + 1) → V} {T T' : F}
    (hF : Formalism.MainNotions.ThinScalesBound.FrameK H f T) (hF' : Formalism.MainNotions.ThinScalesBound.FrameK H f' T')
    (hD1 : IsUnit (H.Dl f f' (r + 1))) (hGd : IsUnit (H.Gdet f f' T T')) :
    IsUnit (gramC (M.L.cj : E →+* E) (H.Zhat f f') (algebraMap F E T) (algebraMap F E T')).det := by
  rw [gramC_eq H f f' T T' hF hF', Matrix.det_transpose]
  obtain ⟨s, hs, hdet⟩ := gram_det H f f' T T' hF hF' hD1
  have hsu : IsUnit s := ⟨⟨s, s, hs, hs⟩, rfl⟩
  have : (H.gram (Sum.elim f f')).det = H.Gdet f f' T T' * s := by
    rw [← hdet, mul_assoc, hs, mul_one]
  rw [this]
  exact hGd.mul hsu

theorem unit_gramHU {g : SplitG M.L} (hs : M.split = some g) {t : Term V M r}
    (hF : Formalism.MainNotions.ThinScalesBound.FrameK H t.f t.T) (hF' : Formalism.MainNotions.ThinScalesBound.FrameK H t.f' t.T')
    (hD1 : IsUnit (H.Dl t.f t.f' (r + 1))) (hGd : IsUnit (H.Gdet t.f t.f' t.T t.T')) :
    IsUnit (gramH H (H.MMfam t)).det := by
  set qi := algebraMap F E ((g.q : F)⁻¹) with hqi
  let B : Matrix (Ix r) (Ix r) E := Matrix.fromBlocks 1 0 (-qi • (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E))
    (qi • (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E))
  have hfam : H.MMfam t = fun i => ∑ j, B i j • Sum.elim t.f t.f' j := by
    rw [mmfam_some H hs]
    funext i
    rcases i with a | a
    · simp [B, Fintype.sum_sum_type, Matrix.one_apply]
    · simp [B, Fintype.sum_sum_type, Matrix.one_apply, sub_eq_add_neg, add_comm, neg_smul]
      rfl
  have hqu : IsUnit qi := by
    refine ⟨⟨qi, algebraMap F E (g.q : F), qi_mul_q g, ?_⟩, rfl⟩
    rw [mul_comm]; exact qi_mul_q g
  have hB : IsUnit B.det := by
    simp only [B]
    rw [Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, one_mul, Matrix.det_smul, Matrix.det_one, mul_one]
    exact hqu.pow _
  have hV : gramH H (Sum.elim t.f t.f') = gramC (M.L.cj : E →+* E) (H.Zhat t.f t.f')
      (algebraMap F E t.T) (algebraMap F E t.T') := by
    rw [gramC_eq H _ _ _ _ hF hF']
    ext i j; rfl
  have hG := unit_gramCU H hF hF' hD1 hGd
  rw [hfam, gramH_comb, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hV]
  have hBc : IsUnit (B.map M.L.cj).det := by
    have : (B.map M.L.cj).det = M.L.cj B.det := by
      rw [show (B.map M.L.cj) = (M.L.cj : E →+* E).mapMatrix B from rfl, ← RingHom.map_det]; rfl
    rw [this]; exact hB.map _
  exact (hB.mul hG).mul hBc

theorem gdet_eq (f f' : Fin (r + 1) → V) (T T' : F) :
    H.Gdet f f' T T' = H.Dl f f' (r + 1) * M.L.cj (H.Dl f f' (r + 1)) -
      algebraMap F E (T * T') * (H.Dl f f' r * M.L.cj (H.Dl f f' r)) := rfl

theorem gdet_swap (f f' : Fin (r + 1) → V) (T T' : F) : H.Gdet f' f T' T = H.Gdet f f' T T' := by
  rw [gdet_eq, gdet_eq, dl_swap_full, dl_swap_r, M.L.cj_cj, M.L.cj_cj, mul_comm T' T]
  ring

theorem gamR_sepU {g : SplitG M.L} {t₁ : Term V M r} {f₂ f₂' : Fin (r + 1) → V}
    (hg₁ : GoodG H g t₁) (hg₂ : GoodG H g (⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ : Term V M r))
    (hG₁ : IsUnit (H.Gdet t₁.f t₁.f' t₁.T t₁.T')) (hG₂ : IsUnit (H.Gdet f₂ f₂' t₁.T t₁.T'))
    (hrel : H.Dl t₁.f t₁.f' r * H.Dl f₂ f₂' (r + 1) = H.Dl f₂ f₂' r * H.Dl t₁.f t₁.f' (r + 1))
    (φ : H.Wb t₁.f ≃ₗ[E] H.Wb f₂) (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb f₂')
    (hz : φ (H.mkW t₁.f ⟨_, z_mem H t₁.f t₁.T hg₁.2.1⟩) = H.mkW f₂ ⟨_, z_mem H f₂ t₁.T hg₂.2.1⟩)
    (ho : φ (H.mkW t₁.f ⟨_, omP_mem H t₁.f t₁.f' hg₁.2.2.2.1⟩) =
      H.mkW f₂ ⟨_, omP_mem H f₂ f₂' hg₂.2.2.2.1⟩)
    (hz' : φ' (H.mkW t₁.f' ⟨_, z_mem H t₁.f' t₁.T' hg₁.2.2.1⟩) =
      H.mkW f₂' ⟨_, z_mem H f₂' t₁.T' hg₂.2.2.1⟩)
    (ho' : φ' (H.mkW t₁.f' ⟨_, omP_mem H t₁.f' t₁.f (unit_swap H t₁.f t₁.f' hg₁.2.2.2.1)⟩) =
      H.mkW f₂' ⟨_, omP_mem H f₂' f₂ (unit_swap H f₂ f₂' hg₂.2.2.2.1)⟩) :
    ∀ p ∈ GamR H t₁ (algebraMap F E (g.q : F)),
      ∀ p₂ ∈ GamR H (⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ : Term V M r) (algebraMap F E (g.q : F)),
      PcG H hg₂ p₂.2.2.1 = PcG H hg₁ p.2.2.1 → PcG' H hg₂ p₂.2.2.2 = PcG' H hg₁ p.2.2.2 →
      p₂.2.2.1 = φ p.2.2.1 ∧ p₂.2.2.2 = φ' p.2.2.2 := by
  rintro _ ⟨u₁, u₁', u₁'', hu₁, hu₁', -, rfl⟩ _ ⟨u₂, u₂', u₂'', hu₂, hu₂', -, rfl⟩ hc hc'
  simp only [PcG, PcG', coordW_mk, Prod.mk.injEq] at hc hc'
  have hν := nu_eq H t₁.f t₁.f' f₂ f₂' t₁.T' hg₁.2.2.1 hg₂.2.2.1 hg₁.2.2.2.1 hg₂.2.2.2.1 hrel
  have hrel' : H.Dl t₁.f' t₁.f r * H.Dl f₂' f₂ (r + 1) = H.Dl f₂' f₂ r * H.Dl t₁.f' t₁.f (r + 1) := by
    rw [dl_swap_r H t₁.f t₁.f', dl_swap_full H f₂ f₂', dl_swap_r H f₂ f₂', dl_swap_full H t₁.f t₁.f',
      ← map_mul, ← map_mul, hrel]
  have hν' := nu_eq H t₁.f' t₁.f f₂' f₂ t₁.T hg₁.2.1 hg₂.2.1 (unit_swap H _ _ hg₁.2.2.2.1)
    (unit_swap H _ _ hg₂.2.2.2.1) hrel'
  constructor
  · exact mkW_transport H hg₁.2.1 hg₁.2.2.1 hg₂.2.1 hg₂.2.2.1 hg₁.2.2.2.1 hg₂.2.2.2.1
      (by rw [← gdet_eq]; exact hG₁) (by rw [← gdet_eq]; exact hG₂) hν φ hz ho ⟨u₁, hu₁⟩
      (mem_span_of_sharpG H hg₁ u₁) ⟨u₂, hu₂⟩ (mem_span_of_sharpG H hg₂ u₂) hc.1 hc.2
  · exact mkW_transport H hg₁.2.2.1 hg₁.2.1 hg₂.2.2.1 hg₂.2.1 (unit_swap H _ _ hg₁.2.2.2.1)
      (unit_swap H _ _ hg₂.2.2.2.1)
      (by rw [← gdet_eq, gdet_swap]; exact hG₁) (by rw [← gdet_eq, gdet_swap]; exact hG₂) hν' φ' hz' ho'
      ⟨u₁', hu₁'⟩ (by rw [span_swap]; exact mem_span_of_sharpG H hg₁ u₁') ⟨u₂', hu₂'⟩
      (by rw [span_swap]; exact mem_span_of_sharpG H hg₂ u₂') hc'.2 hc'.1

end Parts

theorem coordGU_holds : CoordGU := by
  intro F _ _ _ E _ _ _ _ M g hs r n V _ _ H hn t₁ f₂ f₂' φ φ' hyp hD hU2 hR
  have hF₁ : Formalism.MainNotions.ThinScalesBound.FrameK H t₁.f t₁.T := ⟨hyp.1.1.2.1.2.1, hyp.1.1.2.1.2.2.1⟩
  have hF₁' : Formalism.MainNotions.ThinScalesBound.FrameK H t₁.f' t₁.T' := ⟨hyp.1.1.2.2.1.2.1, hyp.1.1.2.2.1.2.2.1⟩
  have hT : t₁.T ∈ 𝒪[F] := hyp.1.1.2.1.2.2.2.1
  have hrel : H.Dl t₁.f t₁.f' r * H.Dl f₂ f₂' (r + 1) = H.Dl f₂ f₂' r * H.Dl t₁.f t₁.f' (r + 1) :=
    hyp.2.2.2.1.2.2.2.2.2
  have hG₁ : IsUnit (H.Gdet t₁.f t₁.f' t₁.T t₁.T') := by
    have hG : H.Gdet t₁.f t₁.f' t₁.T t₁.T' ≠ 0 := hyp.1.1.2.2.2.2.1
    apply isUnit_of_cj_fixed g _ hG
    rw [gdet_eq]
    simp only [map_sub, map_mul, M.L.cj_cj, M.L.cj.commutes]
    ring
  have hG₂ : IsUnit (H.Gdet f₂ f₂' t₁.T t₁.T') := by
    have key := gdet_rel (M := M) (H.Dl t₁.f t₁.f' (r + 1)) (H.Dl t₁.f t₁.f' r) (H.Dl f₂ f₂' (r + 1))
      (H.Dl f₂ f₂' r) (algebraMap F E (t₁.T * t₁.T')) hrel
    have hB : IsUnit (H.Dl f₂ f₂' (r + 1) * M.L.cj (H.Dl f₂ f₂' (r + 1))) := hU2.mul (hU2.map M.L.cj)
    have : IsUnit (H.Gdet f₂ f₂' t₁.T t₁.T' *
        (H.Dl t₁.f t₁.f' (r + 1) * M.L.cj (H.Dl t₁.f t₁.f' (r + 1)))) := by
      rw [gdet_eq, key]; exact hB.mul (by rw [← gdet_eq]; exact hG₁)
    exact isUnit_of_mul_isUnit_left this
  have hg₁ : GoodG H g t₁ := ⟨hs, hF₁, hF₁', dl_succ_unit hyp,
    unit_gramHU H hs hF₁ hF₁' (dl_succ_unit hyp) hG₁⟩
  have hg₂ : GoodG H g (⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ : Term V M r) :=
    ⟨hs, hyp.2.1, hyp.2.2.1, hU2, unit_gramHU H hs hyp.2.1 hyp.2.2.1 hU2 hG₂⟩
  have hTT := (hyp.1.1.2.2.2.2.2 g hs).2.1
  have hI := hyp.2.2.2.1
  have hmm : MMInt H (⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ : Term V M r) := mmInt_G H hg₂ hT hTT hR
  have eZ := sends_one H φ _ _ (z_mem H t₁.f t₁.T hF₁) (z_mem H f₂ t₁.T hyp.2.1) hyp.2.2.2.2.1
  have eZ' := sends_one H φ' _ _ (z_mem H t₁.f' t₁.T' hF₁') (z_mem H f₂' t₁.T' hyp.2.2.1)
    hyp.2.2.2.2.2
  have eO := sends_omP H φ hg₁.2.2.2.1 hU2 hI.2.2.2.1
  have eO' := sends_omP' H φ' hg₁.2.2.2.1 hU2 hI.2.2.2.2.1
  have hGam := fun θ : DDt H t₁ ≃ₗ[M.L.O] DDt H (⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ : Term V M r) =>
    graph_transport4 (PsiG H hg₁).toEquiv (PsiG H hg₂).toEquiv θ.toEquiv φ φ' (PcG H hg₁) (PcG H hg₂)
      (PcG' H hg₁) (PcG' H hg₂) (GamR H t₁ (algebraMap F E (g.q : F))) (GamR H _ (algebraMap F E (g.q : F)))
      _ _ (gamR_image H hg₁) (gamR_image H hg₂)
      (coordW_comp H φ hI.1 _ _ _ _ _ _ _ _ eZ eO)
      (coordW_comp H φ' hI.2.1 _ _ _ _ _ _ _ _ eO' eZ')
      (gamR_sepU H hg₁ hg₂ hG₁ hG₂ hrel φ φ' eZ eO eZ' eO')
  have key : ∀ θ : DDt H t₁ ≃ₗ[M.L.O] DDt H (⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ : Term V M r),
      θ ∈ Theta H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ φ φ' ↔
        (PsiG H hg₁).symm.trans (θ.trans (PsiG H hg₂)) ∈
          ThetaGC M.L.O (M.L.cj : E →+* E) (algebraMap F E (g.q : F)) (algebraMap F E ((g.q : F)⁻¹))
            (H.Zhat t₁.f t₁.f') (H.Zhat f₂ f₂') (algebraMap F E t₁.T) (algebraMap F E t₁.T') := by
    intro θ
    constructor
    · rintro ⟨_, _, hD', _, hG⟩
      exact ⟨(isomD_iffG H hg₁ hg₂ θ).1 hD', (hGam θ).1 (hG g hs)⟩
    · rintro ⟨hD', hG⟩
      refine ⟨hU2, hmm, (isomD_iffG H hg₁ hg₂ θ).2 hD', fun h => ?_, fun g' hg' => ?_⟩
      · rw [hs] at h; cases h
      · rw [hs] at hg'
        cases hg'
        exact (hGam θ).2 hG
  refine Nat.card_congr
    { toFun := fun θ => ⟨(PsiG H hg₁).symm.trans (θ.1.trans (PsiG H hg₂)), (key θ.1).1 θ.2⟩
      invFun := fun θc => ⟨(PsiG H hg₁).trans (θc.1.trans (PsiG H hg₂).symm), (key _).2 (by
        convert θc.2 using 1
        ext x
        simp)⟩
      left_inv := fun θ => by
        apply Subtype.ext; apply LinearEquiv.ext; intro x; simp
      right_inv := fun θc => by
        apply Subtype.ext; apply LinearEquiv.ext; intro x; simp }

end Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUG
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.DlUnitOfHead

section

@[expose] public section

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUG

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

theorem isUnit_comp (g : SplitG M.L) {y : E} (hy : IsUnit y) : (g.e y).1 ≠ 0 ∧ (g.e y).2 ≠ 0 := by
  have h := hy.map g.e
  rw [Prod.isUnit_iff] at h
  exact ⟨h.1.ne_zero, h.2.ne_zero⟩

theorem head_zz_comp {g : SplitG M.L} (hs : M.split = some g) {r : ℕ}
    (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) :
    (g.e ((HermSp.ZZplusOf M Zh T T').submatrix Fin.castSucc Fin.castSucc).det).1 =
        ((g.q : F)⁻¹) ^ r * (g.e (Zh.submatrix Fin.castSucc Fin.castSucc).det).1 ∧
      (g.e ((HermSp.ZZplusOf M Zh T T').submatrix Fin.castSucc Fin.castSucc).det).2 =
        (-(g.q : F)⁻¹) ^ r * (g.e (Zh.submatrix Fin.castSucc Fin.castSucc).det).2 := by
  let f1 : E →+* F := (RingHom.fst F F).comp g.e.toRingEquiv.toRingHom
  let f2 : E →+* F := (RingHom.snd F F).comp g.e.toRingEquiv.toRingHom
  have hd1 : ∀ A : Matrix (Fin r) (Fin r) E, (g.e A.det).1 = (A.map f1).det := fun A => by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    rfl
  have hd2 : ∀ A : Matrix (Fin r) (Fin r) E, (g.e A.det).2 = (A.map f2).det := fun A => by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    rfl
  have hS1 : ((HermSp.ZZplusOf M Zh T T').submatrix Fin.castSucc Fin.castSucc).map f1 =
      ((g.q : F)⁻¹) • (Zh.submatrix Fin.castSucc Fin.castSucc).map f1 := by
    ext i j
    simp [HermSp.ZZplusOf, hs, f1, Fin.castSucc_ne_last, div_eq_inv_mul]
  have hS2 : ((HermSp.ZZplusOf M Zh T T').submatrix Fin.castSucc Fin.castSucc).map f2 =
      (-(g.q : F)⁻¹) • ((Zh.submatrix Fin.castSucc Fin.castSucc).map f2).transpose := by
    ext i j
    simp [HermSp.ZZplusOf, hs, f2, Fin.castSucc_ne_last, div_eq_inv_mul]
  refine ⟨?_, ?_⟩
  · rw [hd1, hS1, Matrix.det_smul, Fintype.card_fin, hd1]
  · rw [hd2, hS2, Matrix.det_smul, Fintype.card_fin, Matrix.det_transpose, hd2]

theorem dl_unit_of_head {g : SplitG M.L} (hs : M.split = some g) (H : HermSp M V) {r : ℕ}
    (f f' : Fin (r + 1) → V) (T T' : F)
    (hu : IsUnit ((HermSp.ZZplusOf M (H.Zhat f f') T T').submatrix Fin.castSucc Fin.castSucc).det) :
    IsUnit (H.Dl f f' r) := by
  have hDl : H.Dl f f' r = ((H.Zhat f f').submatrix Fin.castSucc Fin.castSucc).det := by
    unfold HermSp.Dl
    rw [dite_eq_left (Nat.le_succ r)]
    rfl
  obtain ⟨h1, h2⟩ := isUnit_comp g hu
  rw [(head_zz_comp hs (H.Zhat f f') T T').1] at h1
  rw [(head_zz_comp hs (H.Zhat f f') T T').2] at h2
  have h1' : (g.e (H.Dl f f' r)).1 ≠ 0 := by
    rw [hDl]
    exact right_ne_zero_of_mul h1
  have h2' : (g.e (H.Dl f f' r)).2 ≠ 0 := by
    rw [hDl]
    exact right_ne_zero_of_mul h2
  have hU : IsUnit (g.e (H.Dl f f' r)) :=
    Prod.isUnit_iff.2 ⟨isUnit_iff_ne_zero.2 h1', isUnit_iff_ne_zero.2 h2'⟩
  have h3 := hU.map g.e.symm
  simpa using h3

end Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUG
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.AlgGUT

section

@[expose] public section

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

namespace Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUG

section StepsT

def AlgGUT : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) (g : SplitG M.L), M.split = some g →
  ∀ (r : ℕ) (T T' : F), (∃ u v : 𝒪[F], (u : F) * T = 1 ∧ (v : F) * T' = 1) →
    (∃ c : 𝒪[F], T - T' = (g.q : F) ^ 2 * c) →
  ∀ (Zh₁ Zh₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) M.R),
    Z₁.map M.R.subtype = HermSp.ZZplusOf M Zh₁ T T' → Z₂.map M.R.subtype = HermSp.ZZplusOf M Zh₂ T T' →
    IsUnit Zh₁.det → IsUnit Zh₂.det →
    IsUnit (Zh₁.submatrix Fin.castSucc Fin.castSucc).det → IsUnit (Zh₂.submatrix Fin.castSucc Fin.castSucc).det →
    Zh₁.det * (Zh₂.submatrix Fin.castSucc Fin.castSucc).det =
      Zh₂.det * (Zh₁.submatrix Fin.castSucc Fin.castSucc).det →
    IsUnit (Zh₁.det * M.L.cj Zh₁.det - algebraMap F E (T * T') *
      ((Zh₁.submatrix Fin.castSucc Fin.castSucc).det * M.L.cj (Zh₁.submatrix Fin.castSucc Fin.castSucc).det)) →
    IsUnit (Zh₂.det * M.L.cj Zh₂.det - algebraMap F E (T * T') *
      ((Zh₂.submatrix Fin.castSucc Fin.castSucc).det * M.L.cj (Zh₂.submatrix Fin.castSucc Fin.castSucc).det)) →
    T ∈ 𝒪[F] →
    Nat.card (ThetaGC M.L.O (M.L.cj : E →+* E) (algebraMap F E (g.q : F))
        (algebraMap F E ((g.q : F)⁻¹)) Zh₁ Zh₂ (algebraMap F E T) (algebraMap F E T')) =
      Nat.card (IsoMbe Z₁ Z₂)

end StepsT

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

theorem thetaMbeG_of_coordT (h1 : CoordGU) (h2 : AlgGUT) (M : Model F E) (r n : ℕ) : ThetaMbeG M r n := by
  intro hmode V _ _ H hn t₁ f₂ f₂' φ φ' hyp hD Z₁ Z₂ e₁ e₂ hu₂
  obtain ⟨g, hs⟩ := Option.isSome_iff_exists.1 hmode
  have hg := hyp.1
  have hr2 : IsUnit (H.Dl f₂ f₂' r) := by
    apply dl_unit_of_head hs H f₂ f₂' t₁.T t₁.T'
    have : headDet M Z₂ = ((HermSp.ZZplusOf M (H.Zhat f₂ f₂') t₁.T t₁.T').submatrix Fin.castSucc
        Fin.castSucc).det := by
      unfold headDet; rw [e₂]
    rw [← this]; exact hu₂
  have hrel : H.Dl t₁.f t₁.f' r * H.Dl f₂ f₂' (r + 1) = H.Dl f₂ f₂' r * H.Dl t₁.f t₁.f' (r + 1) :=
    hyp.2.2.2.1.2.2.2.2.2
  have hunit : IsUnit (H.Dl f₂ f₂' (r + 1)) := by
    have : IsUnit (H.Dl t₁.f t₁.f' r * H.Dl f₂ f₂' (r + 1)) := by rw [hrel]; exact hr2.mul (dl_succ_unit hyp)
    exact isUnit_of_mul_isUnit_right this
  have hzz : ∀ a b, HermSp.ZZplusOf M (H.Zhat f₂ f₂') t₁.T t₁.T' a b ∈ M.R := by
    intro a b
    have := (Z₂ a b).2
    rw [show ((Z₂ a b : M.R) : E) = HermSp.ZZplusOf M (H.Zhat f₂ f₂') t₁.T t₁.T' a b from
      congrFun (congrFun e₂ a) b] at this
    exact this
  have hG1 : IsUnit (H.Dl t₁.f t₁.f' (r + 1) * M.L.cj (H.Dl t₁.f t₁.f' (r + 1)) - algebraMap F E (t₁.T * t₁.T') *
      (H.Dl t₁.f t₁.f' r * M.L.cj (H.Dl t₁.f t₁.f' r))) := by
    have hG : H.Gdet t₁.f t₁.f' t₁.T t₁.T' ≠ 0 := hg.1.2.2.2.2.1
    unfold HermSp.Gdet HermSp.normE at hG
    apply isUnit_of_cj_fixed g _ hG
    simp only [map_sub, map_mul, M.L.cj_cj, cj_alg]
    ring
  rw [h1 F E M g hs r n V H hn t₁ f₂ f₂' φ φ' hyp hD hunit hzz]
  refine h2 F E M g hs r t₁.T t₁.T' (hg.1.2.2.2.2.2 g hs).1 (hg.1.2.2.2.2.2 g hs).2.1 _ _ Z₁ Z₂ e₁ e₂
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ hyp.1.1.2.1.2.2.2.1
  · rw [← dl_full]; exact dl_succ_unit hyp
  · rw [← dl_full]; exact hunit
  · rw [← dl_eq_det]; exact hD
  · rw [← dl_eq_det]; exact hr2
  · rw [← dl_full, ← dl_full, ← dl_eq_det, ← dl_eq_det]
    linear_combination hrel.symm
  · rw [← dl_full, ← dl_eq_det]
    exact hG1
  · rw [← dl_full, ← dl_eq_det]
    have key := gdet_rel (M := M) (H.Dl t₁.f t₁.f' (r + 1)) (H.Dl t₁.f t₁.f' r) (H.Dl f₂ f₂' (r + 1))
      (H.Dl f₂ f₂' r) (algebraMap F E (t₁.T * t₁.T')) hrel
    have hA : IsUnit (H.Dl t₁.f t₁.f' (r + 1) * M.L.cj (H.Dl t₁.f t₁.f' (r + 1))) :=
      (dl_succ_unit hyp).mul ((dl_succ_unit hyp).map M.L.cj)
    have hB : IsUnit (H.Dl f₂ f₂' (r + 1) * M.L.cj (H.Dl f₂ f₂' (r + 1))) := hunit.mul (hunit.map M.L.cj)
    have : IsUnit ((H.Dl f₂ f₂' (r + 1) * M.L.cj (H.Dl f₂ f₂' (r + 1)) - algebraMap F E (t₁.T * t₁.T') *
        (H.Dl f₂ f₂' r * M.L.cj (H.Dl f₂ f₂' r))) * (H.Dl t₁.f t₁.f' (r + 1) * M.L.cj (H.Dl t₁.f t₁.f' (r + 1)))) := by
      rw [key]; exact hB.mul hG1
    exact isUnit_of_mul_isUnit_left this

theorem locCntUG_of_algGUT (h : AlgGUT) : Formalism.L2.SG.LocalCountModules.LocCntUG.LocCntUG :=
  locCntUG_of (fun _ _ _ _ _ _ _ _ _ M _ r n => thetaMbeG_of_coordT coordGU_holds h M r n)

end Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUG
end
end
end
