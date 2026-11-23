module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXPbSuppHyp
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEX2
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegrableCsmul
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellInversePair
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellZetaMinors
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CornerBlockActionInvariant
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CornerMatrixBlockThreeMul
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsCompactCutoffCoefficient
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LeftFubiniNormalizedTower
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelsOfBuiltSetting
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RdVZeroOfVanish
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SlicesFiniteRegularityBuilt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UwClosedSubgroup
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
import Mathlib.Topology.Sheaves.Init
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CornerBZero
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXPbSuppOrbit

section

@[expose] public section

open Matrix MeasureTheory Filter Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutEXPbSupp

section gen

variable {k p ρ n : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem exists_orbit (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k n Wp Wq) (e : p + ρ = n)
    (H : B.Mat k n → (Wq →L[ℂ] Wp)) (g0 : B.Mat k n) (h : PBQ.pbF Bj B0 e H g0 ≠ 0) :
    ∃ x, PBQ.GoodP Bj x ∧ ∃ ξ : Mt k n × Mt k n, PBG.InR B0 ξ ∧
      H (D.castM e (PBQ.sP Bj x) * g0 * Matrix.of ξ.2 * Matrix.of ξ.1) ≠ 0 := by
  by_contra hno
  push Not at hno
  apply h
  unfold PBQ.pbF
  rw [← integral_zero (PBQ.XP k p ρ) (Wq →L[ℂ] Wp)]
  refine integral_congr_ae ?_
  filter_upwards [PBQ.ae_goodP (p := p) Bj] with x hx
  show PBQ.pbI Bj B0 e H g0 x = 0
  unfold PBQ.pbI
  have hK : PBG.Kr B0 H (D.castM e (PBQ.sP Bj x) * g0) = 0 := by
    unfold PBG.Kr
    rw [← integral_zero (Mt k n × Mt k n) (Wq →L[ℂ] Wp)]
    refine integral_congr_ae ?_
    filter_upwards [PBG.ae_inR B0] with ξ hξ
    show _ = 0
    rw [hno x hx ξ hξ, ContinuousLinearMap.zero_comp, smul_zero]
  rw [hK, ContinuousLinearMap.comp_zero, smul_zero]

theorem norm_entry_le_gN (g : B.Mat k n) (i j : Fin (2 * n + k + 1)) : ‖g i j‖ ≤ B.gN g := by
  unfold B.gN
  rw [Complex.norm_def]
  refine Real.sqrt_le_sqrt ?_
  calc Complex.normSq (g i j) ≤ ∑ j', Complex.normSq (g i j') :=
        Finset.single_le_sum (f := fun j' => Complex.normSq (g i j')) (fun _ _ => Complex.normSq_nonneg _)
          (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', Complex.normSq (g i' j') :=
        Finset.single_le_sum (f := fun i' => ∑ j', Complex.normSq (g i' j'))
          (fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ i)

theorem orbit_gen (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k n Wp Wq) (e : p + ρ = n)
    (hz : B0.z = D.castV e (liftVec k p ρ Bj.z))
    (Z : Matrix (Fin p) (Fin p) ℂ) (μ : B.Mat k ρ) (hZ : Z.det ≠ 0) (hμ : μ ∈ B.GV k ρ)
    (x : PBQ.XP k p ρ) (hx : PBQ.GoodP Bj x) (ξ : Mt k n × Mt k n) (hξ : PBG.InR B0 ξ) (g : B.Mat k n)
    (hg : g = D.castM e (PBQ.sP Bj x) * D.castM e (U.mMap k p ρ Z μ) * Matrix.of ξ.2 * Matrix.of ξ.1) :
    g ∈ B.GV k n ∧ (∃ u : Matrix (Fin p) (Fin p) ℂ, Formalism.DoubleCosetMeasures.IsUpUni u ∧ ∀ a b, ‖(Z * u) a b‖ ≤ B.gN g) ∧
      (∀ l, Dmin k n B0.z B0.z' g l = Dmin k n B0.z B0.z' (D.castM e (U.mMap k p ρ Z μ)) l) ∧
      Gf k n B0.z B0.z' g = Gf k n B0.z B0.z' (D.castM e (U.mMap k p ρ Z μ)) := by
  subst e
  simp only [Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl] at hg ⊢
  rw [Formalism.FourierDecayAlt.P.JCTx5.castV_rfl] at hz
  have hm : U.mMap k p ρ Z μ ∈ B.GV k (p + ρ) := (Formalism.FourierDecayAlt.P.slice_membership k p ρ).1 Z μ hZ hμ
  refine ⟨?_, ?_, ?_⟩
  · rw [hg]
    exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (PartialBesselProperness.sP_GV Bj x) hm) hξ.2.1)
      hξ.1.1
  · refine ⟨G.upper (fun q : G.UT p => (Matrix.of ξ.2 : B.Mat k (p + ρ)) ⟨q.1.1.val, by omega⟩ ⟨q.1.2.val, by omega⟩),
      LeftFubiniLemmas.upper_isUpUni _, fun a b => ?_⟩
    have hZh : U.Zh k p ρ g = Z * G.upper (fun q : G.UT p =>
        (Matrix.of ξ.2 : B.Mat k (p + ρ)) ⟨q.1.1.val, by omega⟩ ⟨q.1.2.val, by omega⟩) := by
      have e0 := Formalism.FourierDecayAlt.P.hat_z_on_slice k p ρ 0 0 Z μ
      rw [LeftFubiniLemmas.rn_zero, inv_one, Matrix.one_mul, Matrix.mul_one] at e0
      rw [hg, PBQ.zh_mul_UW _ _ _ hξ.1, LeftFubiniLemmas.zh_mul_N _ _ hξ.2, PBQ.zh_sP_mul, e0,
        PBQ.nblk_upper _ hξ.2]
    rw [← hZh]
    exact norm_entry_le_gN g _ _
  · obtain ⟨h, hh, m, hmN, hs⟩ := PartialBesselProperness.leftFactor_mem Bj x
    rw [← hz] at hh
    have hhu : IsUnit h.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hh.1
    have hmu : IsUnit m.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hmN.1
    set pp : B.SS k (p + ρ) := ((Matrix.of.symm h⁻¹, Matrix.of.symm m⁻¹), ξ) with hpp
    have hin : B0.inSS pp := ⟨Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hh, Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_inv hmN, hξ.1, hξ.2⟩
    have hsg : B.sgs pp (U.mMap k p ρ Z μ) = g := by
      rw [hg, hs]
      simp only [B.sgs, hpp]
      change (h⁻¹)⁻¹ * (m⁻¹)⁻¹ * U.mMap k p ρ Z μ * Matrix.of ξ.2 * Matrix.of ξ.1 = _
      rw [Matrix.nonsing_inv_nonsing_inv _ hhu, Matrix.nonsing_inv_nonsing_inv _ hmu]
    refine ⟨fun l => ?_, ?_⟩
    · rw [← hsg]; exact Formalism.FourierDecayAlt.P.BigCellZetaMinors.dmin_sgs B0 hin _ l
    · rw [← hsg]; exact Formalism.FourierDecayAlt.P.JCx1.needs.gf_sgs B0 hin _

end gen

theorem gf_castM {k a b : ℕ} (e : a = b) (z z' : Fin (2 * b + k + 1) → ℂ) (g : B.Mat k a) :
    Gf k b z z' (D.castM e g) = Gf k a (D.castV e.symm z) (D.castV e.symm z') g := by
  subst e
  rw [Formalism.FourierDecayAlt.P.JCTx5.castM_rfl, Formalism.FourierDecayAlt.P.JCTx5.castV_rfl, Formalism.FourierDecayAlt.P.JCTx5.castV_rfl]

theorem castV_castV' {k a b c : ℕ} (h1 : a = b) (h2 : b = c) (v : Fin (2 * a + k + 1) → ℂ) :
    D.castV h2 (D.castV h1 v) = D.castV (h1.trans h2) v := by
  subst h1 h2; rfl

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem lowV_top {P : M.Par} (p : KB.Pl P Wp Wq) (e : P.r + (P.r - P.r) = P.r) :
    U.lowV P.k P.r (P.r - P.r) (D.castV e.symm p.T.base.z) = (p.T.bs P.r).z ∧
      U.lowV P.k P.r (P.r - P.r) (D.castV e.symm p.T.base.z') = (p.T.bs P.r).z' := by
  unfold D.LevTower.base
  rw [← p.T.z_lev P.r le_rfl, ← p.T.z'_lev P.r le_rfl, castV_castV', castV_castV']
  exact ⟨Formalism.FourierDecayAlt.P.JCTx6.Link2.lowV_liftVec rfl _ _, Formalism.FourierDecayAlt.P.JCTx6.Link2.lowV_liftVec rfl _ _⟩

theorem orbit_point {P : M.Par} (p : KB.Pl P Wp Wq) (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (Z : Matrix (Fin P.r) (Fin P.r) ℂ) (μ : B.Mat P.k (P.r - P.r)) (hZ : Z.det ≠ 0)
    (hμ : μ ∈ Q.Glev P.k (P.r - P.r) (Fin.last _)) (h : CutEX.pbTop p G Z μ ≠ 0) :
    ∃ g ∈ B.GV P.k P.r, G g ≠ 0 ∧ ∃ u : Matrix (Fin P.r) (Fin P.r) ℂ, Formalism.DoubleCosetMeasures.IsUpUni u ∧
      (∀ a b, ‖(Z * u) a b‖ ≤ B.gN g) ∧ Dmin P.k P.r p.T.base.z p.T.base.z' g ⟨P.r, by omega⟩ = Z.det ∧
      Gf P.k P.r p.T.base.z p.T.base.z' g =
        Complex.normSq Z.det * Gf P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' μ := by
  have e : P.r + (P.r - P.r) = P.r := by omega
  have hμGV : μ ∈ B.GV P.k (P.r - P.r) := hμ.1
  unfold CutEX.pbTop PBQ.pbT at h
  obtain ⟨x, hx, ξ, hξ, hG⟩ := exists_orbit _ _ _ _ _ h
  have hz : p.T.base.z = D.castV e (liftVec P.k P.r (P.r - P.r) (p.T.bs P.r).z) := (p.T.z_lev P.r le_rfl).symm
  obtain ⟨hGV, ⟨u, hu, hb⟩, hD, hGf⟩ := orbit_gen (p.T.bs P.r) p.T.base e hz Z μ hZ hμGV x hx ξ hξ _ rfl
  refine ⟨_, hGV, hG, u, hu, hb, ?_, ?_⟩
  · rw [hD]
    rw [Formalism.FourierDecayAlt.P.PBI.dmin_castM e _ _ _ P.r (by omega) (by omega), Formalism.FourierDecayAlt.P.hat_z_minimum_degree P.k P.r (P.r - P.r)]
    have e0 := Formalism.FourierDecayAlt.P.hat_z_on_slice P.k P.r (P.r - P.r) 0 0 Z μ
    rw [Formalism.FourierDecayAlt.P.LeftFubiniLemmas.rn_zero, inv_one, Matrix.one_mul, Matrix.mul_one] at e0
    unfold U.DjU
    rw [e0]
  · rw [hGf, gf_castM e]
    have hz0 := Formalism.FourierDecayAlt.P.PBH.inWb_castV e.symm p.T.base.z_mem
    have hz0' := Formalism.FourierDecayAlt.P.PBH.inWb_castV e.symm p.T.base.z'_mem
    have hG0 := Formalism.FourierDecayAlt.P.level_function_slice P.k P.r (P.r - P.r) _ _ hz0 hz0' 0 0 Z μ
    rw [Formalism.FourierDecayAlt.P.LeftFubiniLemmas.rn_zero, inv_one, Matrix.one_mul, Matrix.mul_one] at hG0
    obtain ⟨hl1, hl2⟩ := lowV_top p e
    rw [hG0, hl1, hl2]

end Formalism.FourierDecayAlt.P.CutEXPbSupp
end
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXPbSupp2

section

@[expose] public section

open Matrix MeasureTheory Filter Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutEXPbSupp

theorem hpk_zero (k : ℕ) : Hpk k 0 = diagonal (dS (2 * 0 + k)) := by
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  simp only [Hpk, diagonal_apply, dS, Fin.ext_iff, Fin.val_last]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem tz_sum (k : ℕ) (z : Fin (2 * 0 + k + 1) → ℂ) :
    ∑ i : Fin (2 * 0 + k), ‖z i.castSucc‖ ^ 2 = ‖z (Fin.last _)‖ ^ 2 - Tz k 0 z := by
  have e : ∀ w : ℂ, (starRingEnd ℂ w * w).re = ‖w‖ ^ 2 := by
    intro w
    rw [Complex.conj_mul']
    norm_cast
  unfold Tz herm
  rw [hpk_zero]
  simp only [Matrix.mulVec_diagonal, dotProduct, Fin.sum_univ_castSucc, Pi.star_apply, Complex.star_def]
  have h1 : ∀ i : Fin (2 * 0 + k), dS (2 * 0 + k) i.castSucc = 1 := fun i => by
    unfold dS
    rw [if_neg (Fin.castSucc_lt_last i).ne]
  have h2 : dS (2 * 0 + k) (Fin.last (2 * 0 + k)) = -1 := by
    unfold dS
    rw [if_pos rfl]
  simp only [h1, h2, one_mul, neg_one_mul, mul_neg, Complex.add_re, Complex.neg_re, Complex.re_sum, e]
  ring

theorem gf_eq_GGl (k ρ : ℕ) (hρ : ρ = 0) (z z' : Fin (2 * ρ + k + 1) → ℂ) (g : B.Mat k ρ) :
    Gf k ρ z z' g = Q.GGl k ρ z z' g := by
  subst hρ
  unfold Gf Q.GGl Dmin
  rw [Matrix.det_fin_zero, Matrix.det_fin_one]
  simp only [Complex.normSq_one, mul_one]
  rfl

theorem mu_bound (k ρ : ℕ) (hρ : ρ = 0) (z z' : Fin (2 * ρ + k + 1) → ℂ) (hT : 0 < Tz k ρ z) (hT' : 0 < Tz k ρ z')
    (μ : B.Mat k ρ) (hμ : μ ∈ Q.Glev k ρ (Fin.last ρ)) (i j : Fin (2 * ρ + k + 1)) :
    ‖μ i j‖ * (Tz k ρ z * Tz k ρ z') ≤ 4 * ‖z ⟨2 * ρ + k, by omega⟩‖ * ‖z' ⟨2 * ρ + k, by omega⟩‖ *
      ‖Q.zetaL k ρ z z' (Fin.last ρ) μ‖ := by
  subst hρ
  have hU : μᴴ * diagonal (dS (2 * 0 + k)) * μ = diagonal (dS (2 * 0 + k)) := by
    have h := hμ.1
    rw [hpk_zero] at h
    exact h
  have hζ : Q.zetaL k 0 z z' (Fin.last 0) μ = star z ⬝ᵥ (diagonal (dS (2 * 0 + k)) *ᵥ (μ *ᵥ z')) := by
    unfold Q.zetaL herm
    rw [hpk_zero]
    simp [fvec]
  rw [hζ]
  exact entry_bound μ hU z z' _ _ hT hT' (tz_sum k z) (tz_sum k z') i j

end Formalism.FourierDecayAlt.P.CutEXPbSupp

namespace Formalism.FourierDecayAlt.P

open CutEX CutEXPbSupp

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
theorem pullback_support : CutEX.PbSupp := by
  intro Wp Wq _ _ _ _ _ _ P p G hG
  obtain ⟨⟨_, ⟨R, hR⟩, ⟨ε, hε, hεG⟩⟩, K0, hK0c, h0K0, hK0⟩ := hG

  obtain ⟨δ, hδ, hδK⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ w ∈ K0, δ ≤ ‖w‖ := by
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hK0c.isClosed.isOpen_compl 0 h0K0
    refine ⟨δ, hδ, fun w hw => ?_⟩
    by_contra hlt
    push Not at hlt
    exact hball (by simpa [Metric.mem_ball, dist_zero_right] using hlt) hw

  obtain ⟨M1, hM1⟩ := hK0c.isBounded.exists_norm_le
  set M0 : ℝ := max M1 1 with hM0
  have hM0pos : 0 < M0 := lt_of_lt_of_le one_pos (le_max_right _ _)

  set SR : Set (B.Mat P.k P.r) := Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Metric.closedBall (0 : ℂ) R
    with hSRdef
  have hSR : IsCompact SR := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  obtain ⟨Cg, hCg⟩ := hSR.exists_bound_of_continuousOn
    (f := fun g : B.Mat P.k P.r => Gf P.k P.r p.T.base.z p.T.base.z' g)
    (Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf p.T.base.z p.T.base.z').continuous.continuousOn

  set zr := (p.T.bs P.r).z with hzr
  set zr' := (p.T.bs P.r).z' with hzr'
  have hT : 0 < Tz P.k (P.r - P.r) zr := (p.T.bs P.r).T_pos
  have hT' : 0 < Tz P.k (P.r - P.r) zr' := (p.T.bs P.r).T'_pos
  set TT : ℝ := Tz P.k (P.r - P.r) zr * Tz P.k (P.r - P.r) zr' with hTT
  have hTTpos : 0 < TT := mul_pos hT hT'
  set Zb : ℝ := Real.sqrt (Cg / δ ^ 2 + TT) with hZb
  set Bμ : ℝ := 4 * ‖zr ⟨2 * (P.r - P.r) + P.k, by omega⟩‖ * ‖zr' ⟨2 * (P.r - P.r) + P.k, by omega⟩‖ * Zb / TT
    with hBμ
  set c : ℝ := ε / M0 ^ 2 with hc
  have hcpos : 0 < c := div_pos hε (by positivity)
  set Bset : Set (Mt P.k (P.r - P.r)) :=
    Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Metric.closedBall (0 : ℂ) Bμ with hBset
  set Aset : Set (Fin P.r → Fin P.r → ℂ) :=
    Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Metric.closedBall (0 : ℂ) R with hAset
  have hA : IsCompact Aset := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have hB : IsCompact Bset := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  refine ⟨(Aset ×ˢ Bset) ∩ ((fun q : (Fin P.r → Fin P.r → ℂ) × Mt P.k (P.r - P.r) => (Matrix.of q.1).det) ⁻¹' K0) ∩
      ((fun q : (Fin P.r → Fin P.r → ℂ) × Mt P.k (P.r - P.r) => (Matrix.of q.2 : B.Mat P.k (P.r - P.r))) ⁻¹'
        Q.Glev P.k (P.r - P.r) (Fin.last _)) ∩
      {q | c ≤ Q.GGl P.k (P.r - P.r) zr zr' (Matrix.of q.2)}, ?_, ?_, ?_⟩
  · refine (((hA.prod hB).inter_right ?_).inter_right ?_).inter_right ?_
    · exact hK0c.isClosed.preimage (Continuous.matrix_det continuous_fst)
    · exact (Formalism.FourierDecayAlt.P.JCTx5.glev_closed _ _ _).preimage continuous_snd
    · exact isClosed_le continuous_const ((Formalism.FourierDecayAlt.P.Qx8.GGl_cont _ _ _ _).comp continuous_snd)
  · rintro q ⟨⟨⟨_, hq1⟩, _⟩, hq3⟩
    refine ⟨fun h0 => h0K0 ?_, lt_of_lt_of_le hcpos hq3⟩
    have : (Matrix.of q.1).det ∈ K0 := hq1
    rwa [h0] at this
  · intro q hdet hμ hpb
    obtain ⟨g, hg, hGg, u, hu, hb, hD, hGf⟩ := CutEXPbSupp.orbit_point p G (Matrix.of q.1) (Matrix.of q.2) hdet hμ hpb
    have hgR : B.gN g ≤ R := hR g hg hGg
    have hDK : (Matrix.of q.1).det ∈ K0 := hD ▸ hK0 g hg hGg
    have hdetδ : δ ≤ ‖(Matrix.of q.1).det‖ := hδK _ hDK
    have hdetM : ‖(Matrix.of q.1).det‖ ≤ M0 := (hM1 _ hDK).trans (le_max_left _ _)
    have hGε : ε ≤ Gf P.k P.r p.T.base.z p.T.base.z' g := hεG g hg hGg
    have hgSR : g ∈ SR := by
      rw [hSRdef]
      exact fun a _ b _ => by
        rw [Metric.mem_closedBall, dist_zero_right]; exact (CutEXPbSupp.norm_entry_le_gN g a b).trans hgR
    have hGC : Gf P.k P.r p.T.base.z p.T.base.z' g ≤ Cg := (le_abs_self _).trans (hCg g hgSR)
    set Gr := Gf P.k (P.r - P.r) zr zr' (Matrix.of q.2) with hGr
    have hns : Complex.normSq (Matrix.of q.1).det = ‖(Matrix.of q.1).det‖ ^ 2 := Complex.normSq_eq_norm_sq _
    have hGr_pos : 0 < Gr := by
      by_contra hle
      push Not at hle
      have : Gf P.k P.r p.T.base.z p.T.base.z' g ≤ 0 := by
        rw [hGf]; exact mul_nonpos_of_nonneg_of_nonpos (Complex.normSq_nonneg _) hle
      linarith
    have hGGl : Q.GGl P.k (P.r - P.r) zr zr' (Matrix.of q.2) = Gr :=
      (CutEXPbSupp.gf_eq_GGl P.k (P.r - P.r) (Nat.sub_self _) zr zr' _).symm
    have hδ2 : δ ^ 2 ≤ Complex.normSq (Matrix.of q.1).det := by
      rw [hns]; exact pow_le_pow_left₀ hδ.le hdetδ 2
    have hM2 : Complex.normSq (Matrix.of q.1).det ≤ M0 ^ 2 := by
      rw [hns]; exact pow_le_pow_left₀ (norm_nonneg _) hdetM 2
    have hGr_up : Gr ≤ Cg / δ ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      calc Gr * δ ^ 2 ≤ Gr * Complex.normSq (Matrix.of q.1).det := mul_le_mul_of_nonneg_left hδ2 hGr_pos.le
        _ = Gf P.k P.r p.T.base.z p.T.base.z' g := by rw [hGf, mul_comm]
        _ ≤ Cg := hGC
    have hGr_lo : c ≤ Gr := by
      rw [hc, div_le_iff₀ (by positivity)]
      calc ε ≤ Gf P.k P.r p.T.base.z p.T.base.z' g := hGε
        _ = Complex.normSq (Matrix.of q.1).det * Gr := hGf
        _ ≤ M0 ^ 2 * Gr := mul_le_mul_of_nonneg_right hM2 hGr_pos.le
        _ = Gr * M0 ^ 2 := mul_comm _ _
    have hζ : ‖Q.zetaL P.k (P.r - P.r) zr zr' (Fin.last _) (Matrix.of q.2)‖ ≤ Zb := by
      rw [Complex.norm_def, hZb]
      refine Real.sqrt_le_sqrt ?_
      have e : Q.GGl P.k (P.r - P.r) zr zr' (Matrix.of q.2) =
          Complex.normSq (Q.zetaL P.k (P.r - P.r) zr zr' (Fin.last _) (Matrix.of q.2)) - TT := rfl
      linarith
    refine ⟨u, hu, ⟨⟨⟨?_, ?_⟩, hμ⟩, ?_⟩⟩
    · refine ⟨?_, ?_⟩
      · simp only [hAset, Set.mem_univ_pi, Metric.mem_closedBall, dist_zero_right]
        exact fun a b => (hb a b).trans hgR
      · simp only [hBset, Set.mem_univ_pi, Metric.mem_closedBall, dist_zero_right]
        intro a b
        have hm := CutEXPbSupp.mu_bound P.k (P.r - P.r) (Nat.sub_self _) zr zr' hT hT' (Matrix.of q.2) hμ a b
        rw [hBμ, le_div_iff₀ hTTpos]
        refine hm.trans ?_
        exact mul_le_mul_of_nonneg_left hζ (by positivity)
    · show (Matrix.of (Matrix.of.symm (Matrix.of q.1 * u))).det ∈ K0
      rw [Equiv.apply_symm_apply, Matrix.det_mul, Formalism.DoubleCosetMeasures.isUpUni_det ℂ hu, mul_one]
      exact hDK
    · show c ≤ Q.GGl P.k (P.r - P.r) zr zr' (Matrix.of q.2)
      rw [hGGl]; exact hGr_lo

end Formalism.FourierDecayAlt.P
end
end
end
