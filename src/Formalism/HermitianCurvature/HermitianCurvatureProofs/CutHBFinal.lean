module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PbWords
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHB2
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CornerMatrixBlockThreeMul
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHBPts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyZeroNear
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UpperMinorOfLevelPoint
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.VLetZeroNear
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
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHBPts
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LettersPassPartialBessel
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OneVariableLettersUnderIntegral
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsOpenDomP
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellZetaMinors
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CornerBlockActionInvariant
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelsOfBuiltSetting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixMul
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UwClosedSubgroup
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.Linter.Style
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ProperLeftVariablesDomain
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PointLevelZeroEqEmbedding
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Side0PosOf

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHBSupp

section

@[expose] public section

open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutHB

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.LevelPointCoordinates Formalism.FourierDecayAlt.P.PBQ

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def ProperDomP : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (j : ℕ) (hj : j ≤ P.r) (Cs : Set (B.Mat P.k P.r)), IsCompact Cs →
    PartialBesselProperness.Proper (p.T.bs j) p.T.base (by omega : j + (P.r - j) = P.r) Cs (domP P.k P.r j p.T.base.z p.T.base.z')

theorem zxH_rfl (h : C.LPt) (v : XH h) : zxH h (D.ptSize h) rfl v = LeftFubiniLemmas.lhOf (D.ptPerm h) v *
    U.hMat (D.ptPerm h) (D.ptDiag h) := by
  first
  | rfl
  | simp [zxH]

theorem supp_of (hW : PartialBesselProperness.PbWords) (hP : ProperDomP) : Supp := by
  intro Wp Wq _ _ _ _ _ _ P p F j hj w h hh γ hF hw hγ hΩ K _ hK0
  obtain ⟨hh1, hh2⟩ := hh
  subst hh2
  have hhh : D.IsLocPt h (D.ptSize h) := ⟨hh1, rfl⟩
  obtain ⟨R, hR⟩ := hF.2.1
  set Cs : Set (B.Mat P.k P.r) := {g | B.gN g ≤ R} with hCs
  have hCc : IsCompact Cs := Formalism.FourierDecayAlt.P.PBE.isCompact_gN_le P.k P.r R
  have e : D.ptSize h + (P.r - D.ptSize h) = P.r := by omega
  have hd : ∀ i, D.ptDiag h i ≠ 0 := ptDiag_ne hhh

  have hR1 : ∀ ew : Wd.Ix (Fin w.length), ∃ R1 : ℝ, ∀ v : XH h, R1 < ‖v‖ → ∀ g ∈ B.GV P.k P.r,
      U.Zh P.k (D.ptSize h) (P.r - D.ptSize h) (D.castM e.symm g) =
        LeftFubiniLemmas.lhOf (D.ptPerm h) v * U.hMat (D.ptPerm h) (D.ptDiag h) →
      pbF (p.T.bs (D.ptSize h)) p.T.base e
        (D.uwG P.k P.r p.T.base.z p.T.base.z' F (D.ptSize h) (by omega) w ew) g = 0 := by
    intro ew
    refine pb_head_support (p.T.bs (D.ptSize h)) p.T.base e (D.ptPerm h) (D.ptDiag h) hd _ Cs hCc ?_
    intro g hg hgC
    by_contra hne
    exact hgC (Formalism.FourierDecayAlt.P.PBG.uwG_supp p.T.base.z p.T.base.z' F R hR (D.ptSize h) (by omega) w ew g hg hne)
  choose R1 hR1 using hR1
  refine ⟨⋃ ew, Metric.closedBall (0 : XH h) (R1 ew), isCompact_iUnion fun ew => isCompact_closedBall _ _,
    fun v hv τ hτK ew => ?_⟩
  have hτ : τ ≠ 0 := hK0 hτK
  have hvR : R1 ew < ‖v‖ := by
    by_contra hle
    have hle : ‖v‖ ≤ R1 ew := not_lt.mp hle
    exact hv (Set.mem_iUnion.2 ⟨ew, by rw [Metric.mem_closedBall, dist_zero_right]; exact hle⟩)
  have hpt := pts Wp Wq P p (D.ptSize h) hj h hhh γ hγ hΩ v
  have hyD := hpt.2 τ hτ
  have hyG := x0_GV hj hpt.1 hτ hγ
  have hz : p.T.base.z = D.castV e (liftVec P.k (D.ptSize h) (P.r - D.ptSize h) (p.T.bs (D.ptSize h)).z) :=
    (p.T.z_lev (D.ptSize h) (by omega)).symm
  have hPW := hW P.k (D.ptSize h) (P.r - D.ptSize h) P.r Wp Wq (p.T.bs (D.ptSize h)) p.T.base e hz (D.ptSize h)
    (by omega) F Cs (fun g hg _ => hF.1 g hg) hCc
    (fun g hg hgC => by
      by_contra hne
      exact hgC (hR g hg hne))
    (domP P.k P.r (D.ptSize h) p.T.base.z p.T.base.z') (isOpen_domP _ _ _ _ _)
    (fun g hg => hg.1 ⟨D.ptSize h, by omega⟩ (show D.ptSize h ≤ D.ptSize h from le_rfl) (show D.ptSize h ≤ P.r by omega))
    (hP Wp Wq P p (D.ptSize h) (by omega) Cs hCc) w ew _ hyD hyG
  unfold phf
  unfold pbT
  rw [hPW]
  refine hR1 ew v hvR _ hyG ?_
  rw [leading_block_of_base_point hj _ τ γ e.symm, zxH_rfl]

end Formalism.FourierDecayAlt.P.CutHB
end
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.RulesOnPbT

section

@[expose] public section

open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBQ

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

section nl

variable {k : ℕ}

def cL {j ρ : ℕ} (a : Fin j → ℂ) : Fin (2 * ρ + k + 1) → Fin j → ℂ :=
  fun v α => if v.val = 2 * ρ + k then a (Fin.rev α) else 0

theorem nL_apply {j ρ : ℕ} (hρ : 1 ≤ ρ) (a : Fin j → ℂ) (p q : Fin (2 * (j + ρ) + k + 1)) :
    LevelPointCoordinates.nL k (j + ρ) j (by omega) a p q =
      (if p = q then 1 else 0) +
        (if h : p.val = j + 2 * ρ + k ∧ j + 2 * ρ + k + 1 ≤ q.val then a ⟨2 * (j + ρ) + k - q.val, by omega⟩ else 0) -
        (if h : p.val < j ∧ q.val = j then conj (a ⟨p.val, h.1⟩) else 0) := by
  have hS1 : (∑ c : Fin j, if esI k (j + ρ) ⟨j, by omega⟩ = p ∧ esI k (j + ρ) ⟨c.val, by omega⟩ = q then a c else 0) =
      (if h : p.val = j + 2 * ρ + k ∧ j + 2 * ρ + k + 1 ≤ q.val then a ⟨2 * (j + ρ) + k - q.val, by omega⟩ else 0) := by
    split_ifs with h
    · rw [Finset.sum_eq_single ⟨2 * (j + ρ) + k - q.val, by omega⟩]
      · rw [if_pos]
        constructor <;> apply Fin.ext <;> simp [esI] <;> omega
      · intro b _ hb
        rw [if_neg]
        rintro ⟨_, h2⟩
        apply hb
        apply Fin.ext
        have := congrArg Fin.val h2
        simp [esI] at this
        simp
        omega
      · simp
    · refine Finset.sum_eq_zero fun b _ => ?_
      rw [if_neg]
      rintro ⟨h1, h2⟩
      apply h
      have e1 := congrArg Fin.val h1
      have e2 := congrArg Fin.val h2
      simp [esI] at e1 e2
      have := b.isLt
      omega
  have hS2 : (∑ c : Fin j, if eI k (j + ρ) ⟨c.val, by omega⟩ = p ∧ eI k (j + ρ) ⟨j, by omega⟩ = q then
      conj (a c) else 0) = (if h : p.val < j ∧ q.val = j then conj (a ⟨p.val, h.1⟩) else 0) := by
    split_ifs with h
    · rw [Finset.sum_eq_single ⟨p.val, h.1⟩]
      · rw [if_pos]
        constructor <;> apply Fin.ext <;> simp [eI] <;> omega
      · intro b _ hb
        rw [if_neg]
        rintro ⟨h1, _⟩
        apply hb
        apply Fin.ext
        have := congrArg Fin.val h1
        simp [eI] at this
        simp
        omega
      · simp
    · refine Finset.sum_eq_zero fun b _ => ?_
      rw [if_neg]
      rintro ⟨h1, h2⟩
      apply h
      have e1 := congrArg Fin.val h1
      have e2 := congrArg Fin.val h2
      simp [eI] at e1 e2
      have := b.isLt
      omega
  unfold LevelPointCoordinates.nL
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.sum_apply, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib]
  rw [hS1, hS2]
  ring

theorem skewOf_zero {j : ℕ} : U.skewOf (0 : (G.UT j → ℂ) × (Fin j → ℝ)) = 0 := by
  ext a b
  simp [U.skewOf, G.strictUpper]

theorem hpk_last {ρ : ℕ} (hρ : 1 ≤ ρ) (v : Fin (2 * ρ + k + 1)) :
    Hpk k ρ ⟨2 * ρ + k, by omega⟩ v = if v.val = 0 then 1 else 0 := by
  unfold Hpk
  have hv := v.isLt
  simp only [Fin.ext_iff, Fin.val_mk]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem cL_last {j ρ : ℕ} (a : Fin j → ℂ) (v : Fin (2 * ρ + k + 1)) (α : Fin j) :
    (cL (k := k) (ρ := ρ) a) v α = if v.val = 2 * ρ + k then a (Fin.rev α) else 0 := rfl

theorem cHc_zero {j ρ : ℕ} (hρ : 1 ≤ ρ) (a : Fin j → ℂ) :
    (Matrix.of (cL (k := k) (ρ := ρ) a))ᴴ * Hpk k ρ * Matrix.of (cL (k := k) (ρ := ρ) a) = 0 := by
  ext β γ
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, cL_last, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun v _ => ?_
  by_cases hv : v.val = 2 * ρ + k
  · rw [if_pos hv, Finset.sum_eq_single v]
    · have h := hpk_last (k := k) hρ v
      rw [show (⟨2 * ρ + k, by omega⟩ : Fin (2 * ρ + k + 1)) = v from Fin.ext hv.symm] at h
      rw [h, if_neg (show ¬ (v.val = 0) by omega)]
      simp
    · intro u _ hu
      by_cases hu' : u.val = 2 * ρ + k
      · exact absurd (Fin.ext (hu'.trans hv.symm)) hu
      · simp [hu']
    · simp
  · simp [hv]

theorem wcH_apply {j ρ : ℕ} (hρ : 1 ≤ ρ) (a : Fin j → ℂ) (α : Fin j) (v : Fin (2 * ρ + k + 1)) :
    (G.wMat j * (Matrix.of (cL (k := k) (ρ := ρ) a))ᴴ * Hpk k ρ) α v = if v.val = 0 then conj (a α) else 0 := by
  rw [Matrix.mul_assoc, Matrix.mul_apply, Finset.sum_eq_single α.rev]
  · rw [show G.wMat j α α.rev = 1 by simp [G.wMat], one_mul, Matrix.mul_apply,
      Finset.sum_eq_single ⟨2 * ρ + k, by omega⟩]
    · rw [hpk_last hρ, Matrix.conjTranspose_apply, Matrix.of_apply, cL_last, if_pos rfl, Fin.rev_rev]
      split_ifs <;> simp
    · intro u _ hu
      rw [Matrix.conjTranspose_apply, Matrix.of_apply, cL_last, if_neg (fun h => hu (Fin.ext h))]
      simp
    · simp
  · intro β _ hβ
    rw [show G.wMat j α β = 0 by simp [G.wMat]; exact fun h => hβ h, zero_mul]
  · simp

theorem nL_eq {j ρ : ℕ} (hρ : 1 ≤ ρ) (a : Fin j → ℂ) :
    LevelPointCoordinates.nL k (j + ρ) j (by omega) a = U.Rn k j ρ (cL a, 0) := by
  ext p q
  obtain ⟨x, rfl⟩ := (U.eB k j ρ).surjective p
  obtain ⟨y, rfl⟩ := (U.eB k j ρ).surjective q
  rw [nL_apply hρ, Ux3.rn_eq, Ux3.block3_apply]
  simp only [cHc_zero hρ, skewOf_zero, smul_zero, add_zero, Matrix.mul_zero]
  have v1 := @Ux3.block_index_first_val k j ρ
  have v2 := @Ux3.block_index_middle_val k j ρ
  have v3 := @Ux3.block_index_last_val k j ρ
  rcases x with ((α | u) | α) <;> rcases y with ((β | v) | β) <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inl,
      Matrix.fromCols_apply_inr, Matrix.zero_apply, Matrix.one_apply, Matrix.neg_apply, Matrix.of_apply,
      EmbeddingLike.apply_eq_iff_eq, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, if_false, v1, v2, v3]
  · have := α.isLt; have := β.isLt
    rw [dite_eq_right (by omega), dite_eq_right (by omega)]; ring
  · have := α.isLt; have := v.isLt
    rw [wcH_apply hρ, dite_eq_right (by omega)]
    by_cases hv : v.val = 0
    · rw [dite_eq_left ⟨α.isLt, by omega⟩, if_pos hv]; simp
    · rw [dite_eq_right (by omega), if_neg hv]; simp
  · have := α.isLt; have := β.isLt
    rw [dite_eq_right (by omega), dite_eq_right (by omega)]; ring
  · have := u.isLt; have := β.isLt
    rw [dite_eq_right (by omega), dite_eq_right (by omega)]; ring
  · have := u.isLt; have := v.isLt
    rw [dite_eq_right (by omega), dite_eq_right (by omega)]; ring
  · have := u.isLt; have := β.isLt
    rw [cL_last, dite_eq_right (show ¬(j + u.val < j ∧ j + (2 * ρ + k + 1) + β.val = j) by omega)]
    by_cases hu : u.val = 2 * ρ + k
    · rw [dite_eq_left (show j + u.val = j + 2 * ρ + k ∧ j + 2 * ρ + k + 1 ≤ j + (2 * ρ + k + 1) + β.val by omega),
        if_pos hu]
      have e : (⟨2 * (j + ρ) + k - (j + (2 * ρ + k + 1) + β.val), by omega⟩ : Fin j) = β.rev :=
        Fin.ext (by simp [Fin.rev]; omega)
      rw [e]; ring
    · rw [dite_eq_right (show ¬(j + u.val = j + 2 * ρ + k ∧ j + 2 * ρ + k + 1 ≤ j + (2 * ρ + k + 1) + β.val) by omega),
        if_neg hu]; ring
  · have := α.isLt; have := β.isLt
    rw [dite_eq_right (by omega), dite_eq_right (by omega)]; ring
  · have := α.isLt; have := v.isLt
    rw [dite_eq_right (by omega), dite_eq_right (by omega)]; ring
  · have := α.isLt; have := β.isLt
    rw [dite_eq_right (by omega), dite_eq_right (by omega)]; ring

end nl

section tower

variable {k : ℕ}

theorem nL_castM {r j : ℕ} (hj : j + 1 ≤ r) (a : Fin j → ℂ) :
    LevelPointCoordinates.nL k r j hj a = D.castM (by omega : j + (r - j) = r) (U.Rn k j (r - j) (cL a, 0)) := by
  have key : ∀ (ρ r' : ℕ) (e : j + ρ = r') (hj' : j + 1 ≤ r'),
      LevelPointCoordinates.nL k r' j hj' a = D.castM e (U.Rn k j ρ (cL a, 0)) := by
    intro ρ r' e hj'
    subst e
    rw [Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl]
    exact nL_eq (by omega) a
  exact key (r - j) r (by omega) hj

theorem nL_mem {r j : ℕ} (hj : j + 1 ≤ r) (a : Fin j → ℂ) : LevelPointCoordinates.nL k r j hj a ∈ Nset k r := by
  rw [nL_castM hj a]
  exact PBH.castM_N _ (LeftFubiniLemmas.rn_nset _)

theorem psi_castM {j ρ r : ℕ} (e : j + ρ = r) (zj : Fin (2 * ρ + k + 1) → ℂ) (z : Fin (2 * r + k + 1) → ℂ)
    (hz : D.castV e (liftVec k j ρ zj) = z) (c : ℂ) (M : B.Mat k (j + ρ)) :
    psi k r z c (D.castM e M) = psi k (j + ρ) (liftVec k j ρ zj) c M := by
  subst e
  rw [Formalism.FourierDecayAlt.P.JCTx5.castV_rfl] at hz
  subst hz
  rw [Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl]

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem domP_sgs {r : ℕ} (Bs : B.RealPlaceData k r Wp Wq) (j : ℕ) {pp : B.SS k r} (hp : Bs.inSS pp) {g : Q.Mx k r}
    (hg : g ∈ domP k r j Bs.z Bs.z') : B.sgs pp g ∈ domP k r j Bs.z Bs.z' :=
  ⟨fun l h1 h2 => by rw [Formalism.FourierDecayAlt.P.BigCellZetaMinors.dmin_sgs Bs hp]; exact hg.1 l h1 h2,
    by unfold Gf; rw [Formalism.FourierDecayAlt.P.BigCellZetaMinors.dmin_sgs Bs hp, Formalism.FourierDecayAlt.P.BigCellZetaMinors.dmin_sgs Bs hp]; exact hg.2⟩

theorem minorDomain_mul_unipotent {r : ℕ} (Bs : B.RealPlaceData k r Wp Wq) (j : ℕ) {g : Q.Mx k r}
    (hg : g ∈ domP k r j Bs.z Bs.z') {m : Q.Mx k r} (hm : m ∈ Nset k r) : g * m ∈ domP k r j Bs.z Bs.z' := by
  have hp : Bs.inSS ((Matrix.of.symm 1, Matrix.of.symm 1), (Matrix.of.symm 1, Matrix.of.symm m)) :=
    ⟨Formalism.FourierDecayAlt.P.BigCellZetaMinors.one_uw _, Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_one, Formalism.FourierDecayAlt.P.BigCellZetaMinors.one_uw _, hm⟩
  have hs : B.sgs ((Matrix.of.symm 1, Matrix.of.symm 1), (Matrix.of.symm 1, Matrix.of.symm m)) g = g * m := by
    simp only [B.sgs, Equiv.apply_symm_apply, inv_one, one_mul, mul_one]
  rw [← hs]
  exact domP_sgs Bs j hp hg

theorem domP_N_mul {r : ℕ} (Bs : B.RealPlaceData k r Wp Wq) (j : ℕ) {g : Q.Mx k r}
    (hg : g ∈ domP k r j Bs.z Bs.z') {m : Q.Mx k r} (hm : m ∈ Nset k r) : m * g ∈ domP k r j Bs.z Bs.z' := by
  have hmi : m⁻¹ ∈ Nset k r := Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_inv hm
  have hp : Bs.inSS ((Matrix.of.symm 1, Matrix.of.symm m⁻¹), (Matrix.of.symm 1, Matrix.of.symm 1)) :=
    ⟨Formalism.FourierDecayAlt.P.BigCellZetaMinors.one_uw _, hmi, Formalism.FourierDecayAlt.P.BigCellZetaMinors.one_uw _, Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_one⟩
  have hu : IsUnit m.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hm.1
  have hs : B.sgs ((Matrix.of.symm 1, Matrix.of.symm m⁻¹), (Matrix.of.symm 1, Matrix.of.symm 1)) g = m * g := by
    simp only [B.sgs, Equiv.apply_symm_apply, inv_one, one_mul, mul_one,
      Matrix.nonsing_inv_nonsing_inv _ hu]
  rw [← hs]
  exact domP_sgs Bs j hp hg

variable [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

end tower

end Formalism.FourierDecayAlt.P.PBQ
end
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.RulesEq

section

@[expose] public section

open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.PBQ

theorem rules_eq : CutHB.RulesEq := by
  intro Wp Wq _ _ _ _ _ _ P p F j hj _hF
  refine ⟨fun g hg m hm => ⟨minorDomain_mul_unipotent p.T.base j hg.2 hm, ?_⟩,
    fun g hg a => ⟨domP_N_mul p.T.base j hg.2 (nL_mem hj a), ?_⟩⟩
  · exact pbF_right _ _ _ F g m hm
  · show pbF (p.T.bs j) p.T.base _ F (LevelPointCoordinates.nL P.k P.r j hj a * g) =
      psi P.k P.r p.T.base.z cStd (LevelPointCoordinates.nL P.k P.r j hj a) • pbF (p.T.bs j) p.T.base _ F g
    rw [nL_castM hj a, pbF_left_rn p.T.base _ (p.T.bs j).z_mem F (cL a, 0) g,
      psi_castM _ (p.T.bs j).z p.T.base.z (p.T.z_lev j (by omega))]

end Formalism.FourierDecayAlt.P
end
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.SideZeroOfLocalProperness

section

@[expose] public section

namespace Formalism.FourierDecayAlt.P.SliceIntegralLemmas

open Formalism.FourierDecayAlt

theorem side_zero_of_local_properness (hPr : ProperLeftVariablesDomain) : CutHB.Side0 :=
  CutHB.side_zero_of_positive_and_zero (side0Pos_of'' hPr) (side0Zero_of Formalism.FourierDecayAlt.P.letters_pass_partial_bessel hPr CutHB.pts)

end Formalism.FourierDecayAlt.P.SliceIntegralLemmas

namespace Formalism.FourierDecayAlt.P

end Formalism.FourierDecayAlt.P
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHBFinal

section

@[expose] public section

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutHB

theorem headBridge_of_rest (hPr : ProperDomP) (hW : WordSmooth) (h1 : Side1) : LevelPointCoordinates.HeadBridge :=
  headBridge_of Formalism.FourierDecayAlt.P.rules_eq hW pts curveSmooth (supp_of Formalism.FourierDecayAlt.P.letters_pass_partial_bessel hPr)
    (Formalism.FourierDecayAlt.P.SliceIntegralLemmas.side_zero_of_local_properness hPr) h1 Formalism.FourierDecayAlt.P.one_variable_letters_under_integral

end Formalism.FourierDecayAlt.P.CutHB
end
end
end
