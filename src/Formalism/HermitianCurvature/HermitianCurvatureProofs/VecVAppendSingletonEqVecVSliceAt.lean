module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.MulVecBvecApply
public import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdjugateBlockSingleLastColumn
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BlkUUMapMuPRn
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactCoefficientAppend
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSetting
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CptCoefContSupp
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LowerParabolicCoordinates
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChiLIntegrable
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegrableUnipotentNormRpowNeg
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SliceContOn
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.OuterInt

section

@[expose] public section

open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBM

section outer

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]



theorem outer_int (S : B.RealPlaceData k r Wp Wq) (hN : S.μN = D.muN k r) (hW1 : S.μW Set.univ = 1)
    (hW1' : S.μW' Set.univ = 1) (z0 z0' : Fin (2 * 0 + k + 1) → ℂ)
    (hz : S.z = liftVec k r 0 z0) (hz' : S.z' = liftVec k r 0 z0')
    (σ : Equiv.Perm (Fin r)) (d : Fin r → ℂ) (hd : ∀ a, d a ≠ 0) (γ0 : B.Mat k 0) (hγ0 : γ0 ∈ B.GV k 0)
    (hrel : C6.IsRelevant S (U.mMap k r 0 (U.hMat σ d) γ0)) (F : B.Mat k r → (Wq →L[ℂ] Wp))
    (hFc : ContinuousOn F (B.GV k r)) (M : ℝ) (Bs : Set (U.Xi k r 0 0 σ)) (hBs : MeasurableSet Bs)
    (hBsf : U.muXi k r 0 0 σ Bs < ⊤)
    (hdom : ∀ (ξ : U.Xi k r 0 0 σ) (γ : B.Mat k 0), γ ∈ B.GV k 0 →
      ‖F (U.gaXi k 0 σ d ξ (fun a => a.elim0) γ)‖ ≤ Bs.indicator (fun _ => M) ξ) :
    Integrable (fun p => theta0 S.z σ.symm p • D.orbIntegrand S (U.mMap k r 0 (U.hMat σ d) γ0) F p) S.μSS ∧
      ∫ p, theta0 S.z σ.symm p • D.orbIntegrand S (U.mMap k r 0 (U.hMat σ d) γ0) F p ∂S.μSS =
        ∫ x, conjL S x.1 x.2 (U.PhiFun (s := 0) k 0 σ d S.z S.z' F (fun a => a.elim0)
          ((midB r 0 (Matrix.of x.1))⁻¹ * γ0 * midB r 0 (Matrix.of x.2))) ∂(S.μW.prod S.μW') := by
  have : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
  have hsW : SigmaFinite S.μW := Dx2.OrbJ.sigmaF S.haarW
  have hsW' : SigmaFinite S.μW' := Dx2.OrbJ.sigmaF S.haarW'
  have hfW : IsFiniteMeasure S.μW := ⟨by rw [hW1]; exact ENNReal.one_lt_top⟩
  have hfW' : IsFiniteMeasure S.μW' := ⟨by rw [hW1']; exact ENNReal.one_lt_top⟩
  set γ := U.mMap k r 0 (U.hMat σ d) γ0 with hγ
  have hγG : γ ∈ B.GV k r := by
    have := (Formalism.FourierDecayAlt.P.slice_membership k r 0).1 (U.hMat σ d) γ0 (hMat_det_ne σ d hd) hγ0
    exact this
  set f : B.SS k r → (Wq →L[ℂ] Wp) := fun p => theta0 S.z σ.symm p • D.orbIntegrand S γ F p with hf
  have hfm : AEStronglyMeasurable f S.μSS :=
    (theta0_meas S.z σ.symm).aestronglyMeasurable.smul (Dx3.integrand_aesm S hγG hFc)

  have hSS := muSS_eq S hN
  set P := (S.μW.prod (QN k r)).prod (S.μW'.prod (QN k r)) with hP
  have hfm' : AEStronglyMeasurable f (P.map (TN k r)) := by rw [← hSS]; exact hfm
  have hTm : AEMeasurable (TN k r) P := TN_meas.aemeasurable
  set P2 := (S.μW.prod S.μW').prod ((QN k r).prod (QN k r)) with hP2
  have hsw := Dx2.SL.measurePreserving_prod_middle_swap S.μW (QN k r) S.μW' (QN k r)
  set G2 : (Mt k r × Mt k r) × ((U.RC k r 0 × (G.UT r → ℂ)) × (U.RC k r 0 × (G.UT r → ℂ))) → (Wq →L[ℂ] Wp) :=
    fun x => f (TN k r ((x.1.1, x.2.1), (x.1.2, x.2.2))) with hG2
  have hG2e : G2 = (f ∘ TN k r) ∘ (Dx2.SL.swap4 (α := Mt k r) (β := U.RC k r 0 × (G.UT r → ℂ)) (γ := Mt k r)
      (δ := U.RC k r 0 × (G.UT r → ℂ))).symm := by
    funext x; rfl
  have hfTm : AEStronglyMeasurable (f ∘ TN k r) P := hfm'.comp_aemeasurable hTm
  have hG2m : AEStronglyMeasurable G2 P2 := by
    rw [hG2e]
    exact hfTm.comp_measurePreserving (hsw.symm _)

  have hae : ∀ᵐ x ∂(S.μW.prod S.μW'), Matrix.of x.1 ∈ UWset k r S.z ∧ Matrix.of x.2 ∈ UWset k r S.z' := by
    have b1 := (Measure.quasiMeasurePreserving_fst (μ := S.μW) (ν := S.μW')).ae (Dx2.OrbJ.ae_mem S.haarW)
    have b2 := (Measure.quasiMeasurePreserving_snd (μ := S.μW) (ν := S.μW')).ae (Dx2.OrbJ.ae_mem S.haarW')
    filter_upwards [b1, b2] with x h1 h2 using ⟨h1, h2⟩
  have hin := fun x : Mt k r × Mt k r => fun hx : Matrix.of x.1 ∈ UWset k r S.z ∧ Matrix.of x.2 ∈ UWset k r S.z' =>
    inner_int S z0 z0' hz hz' σ d hd γ0 hγ0 hrel F hFc M Bs hBs hBsf hdom x.1 x.2 hx.1 hx.2
  have hG2i : Integrable G2 P2 := by
    rw [integrable_prod_iff hG2m]
    refine ⟨?_, ?_⟩
    · filter_upwards [hae] with x hx using (hin x hx).1
    · refine Integrable.of_bound hG2m.norm.integral_prod_right' (M * (U.muXi k r 0 0 σ Bs).toReal) ?_
      filter_upwards [hae] with x hx
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      exact (hin x hx).2.2

  have hfTi : Integrable (f ∘ TN k r) P := by
    have := (hsw.symm _).integrable_comp_emb (MeasurableEquiv.measurableEmbedding _) (g := f ∘ TN k r)
    rw [← this, ← hG2e]; exact hG2i
  refine ⟨?_, ?_⟩
  · rw [hSS]; exact (integrable_map_measure hfm' hTm).2 hfTi
  · rw [hSS, integral_map hTm hfm']
    have e := (hsw.symm _).integral_comp' (f ∘ TN k r)
    change ∫ x, (f ∘ TN k r) x ∂P = _
    rw [← e]
    change ∫ x, G2 x ∂P2 = _
    rw [hP2, integral_prod G2 hG2i]
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx using (hin x hx).2.1

theorem orbJ_mMap (S : B.RealPlaceData k r Wp Wq) (hN : S.μN = D.muN k r) (hW1 : S.μW Set.univ = 1)
    (hW1' : S.μW' Set.univ = 1) (z0 z0' : Fin (2 * 0 + k + 1) → ℂ)
    (hz : S.z = liftVec k r 0 z0) (hz' : S.z' = liftVec k r 0 z0')
    (σ : Equiv.Perm (Fin r)) (d : Fin r → ℂ) (hd : ∀ a, d a ≠ 0) (γ0 : B.Mat k 0) (hγ0 : γ0 ∈ B.GV k 0)
    (hrel : C6.IsRelevant S (U.mMap k r 0 (U.hMat σ d) γ0))
    (w : Equiv.Perm (Fin (r + 1))) (dd : Fin (r + 1) → ℂ) (hdd : ∀ a, dd a ≠ 0)
    (hZw : Zhat k r S.z S.z' (U.mMap k r 0 (U.hMat σ d) γ0) = C2.monoP w dd)
    (hw : ∀ a : Fin r, w.symm a.castSucc = (σ a).castSucc)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) (hFc : ContinuousOn F (B.GV k r)) (hr : 1 ≤ r) (R : ℝ)
    (hFs : ∀ g ∈ B.GV k r, F g ≠ 0 → B.gN g ≤ R) :
    D.orbJ S (U.mMap k r 0 (U.hMat σ d) γ0) (D.muR S (U.mMap k r 0 (U.hMat σ d) γ0) w) F =
      ∫ x, conjL S x.1 x.2 (U.PhiFun (s := 0) k 0 σ d S.z S.z' F (fun a => a.elim0)
        ((midB r 0 (Matrix.of x.1))⁻¹ * γ0 * midB r 0 (Matrix.of x.2))) ∂(S.μW.prod S.μW') := by
  obtain ⟨M, Bs, hBs, hBsf, hdom⟩ := slice_dom k r hr σ d hd F hFc R hFs
  obtain ⟨hint, heq⟩ := outer_int S hN hW1 hW1' z0 z0' hz hz' σ d hd γ0 hγ0 hrel F hFc M Bs hBs hBsf hdom
  have hγG : U.mMap k r 0 (U.hMat σ d) γ0 ∈ B.GV k r :=
    (Formalism.FourierDecayAlt.P.slice_membership k r 0).1 (U.hMat σ d) γ0 (hMat_det_ne σ d hd) hγ0
  have hw' : ∀ a : Fin r, w.symm a.castSucc = (σ.symm.symm a).castSucc := by simpa using hw
  have hnc := theta0_normCut S hγG hdd hZw σ.symm hw'
  have hex : ∃ θ, D.IsNormCut S (U.mMap k r 0 (U.hMat σ d) γ0) (D.muR S (U.mMap k r 0 (U.hMat σ d) γ0) w) θ ∧
      Integrable (fun p => θ p • D.orbIntegrand S (U.mMap k r 0 (U.hMat σ d) γ0) F p) S.μSS :=
    ⟨_, hnc, hint⟩
  unfold D.orbJ
  rw [dite_eq_left hex, Formalism.FourierDecayAlt.P.orbital_integral_indep_choice k r Wp Wq S _ _ hrel
    (Formalism.FourierDecayAlt.P.radial_measure_is_haar k r Wp Wq S _ w dd hγG hdd hZw) F hex.choose _ hex.choose_spec.1 hnc
    hex.choose_spec.2 hint, heq]

end outer

end Formalism.FourierDecayAlt.P.PBM
end
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.VecVAppendSingletonEqVecVSliceAt

section

@[expose] public section

open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBM

section helpers

variable {k : ℕ}

theorem cast_cancel (a : ℕ) (h1 : a = 0) (h2 : 0 = a) (γ : B.Mat k 0) : h1 ▸ D.castM h2 γ = γ := by
  subst h1; exact Dx2.MN.castM_rfl γ

theorem phiFun_tr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (R j ρ' : ℕ) (hj : j = R) (hρ : ρ' = 0)
    (σ : Equiv.Perm (Fin j)) (d : Fin j → ℂ) (z z' : Fin (2 * R + k + 1) → ℂ) (F : B.Mat k R → E)
    (e1 : R = j + 0 + ρ') (e2 : j + 0 + ρ' = R) (γ : B.Mat k ρ') :
    U.PhiFun (s := 0) k ρ' σ d (D.castV e1 z) (D.castV e1 z') (D.castF e2 F) (fun a => a.elim0) γ =
      U.PhiFun (s := 0) k 0 (hj ▸ σ) (hj ▸ d) z z' F (fun a => a.elim0) (hρ ▸ γ) := by
  subst hj; subst hρ
  have h1 : D.castV e1 z = z := Dx2.Tower.castV_rfl z
  have h2 : D.castV e1 z' = z' := Dx2.Tower.castV_rfl z'
  have h3 : D.castF e2 F = F := by funext g; exact congrArg F (Dx2.MN.castM_rfl g)
  rw [h1, h2, h3]

theorem ptMatN_one (ζ : ℂ) : D.ptMatN [(1, ζ)] (0 + 1) = Matrix.of fun _ _ => ζ := by
  ext a b
  have ha : a.val = 0 := by have := a.isLt; omega
  have hb : b.val = 0 := by have := b.isLt; omega
  simp [D.ptMatN, D.ptEntry, ha, hb]

theorem ptMatN_append_head (h : C.LPt) (ζ : ℂ) (R : ℕ) (hR : D.ptSize h = R) :
    D.ptMatN (h ++ [(1, ζ)]) R = D.ptMatN h R := by
  ext a b
  simp only [D.ptMatN, ptEntry_append, hR, a.isLt, b.isLt, and_self, if_true]

theorem isLocPt_app (h : C.LPt) (R : ℕ) (hh : D.IsLocPt h R) (ζ : ℂ) (hζ : ζ ≠ 0) :
    D.IsLocPt (h ++ [(1, ζ)]) (R + 1) := by
  refine ⟨fun b hb => ?_, CompactCoefficientAppend.ptSize_app h R hh ζ⟩
  rcases List.mem_append.1 hb with hb | hb
  · exact hh.1 b hb
  · simp at hb; subst hb; exact ⟨le_refl _, hζ⟩

theorem Tz_lift (R : ℕ) (v : Fin (2 * 0 + k + 1) → ℂ) : Tz k (R + 0) (liftVec k R 0 v) = Tz k 0 v := by
  unfold Tz; rw [herm_lift]

end helpers

section master

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem lev_inv {k R : ℕ} (y : B.Mat k 0) (hy : IsUnit y.det) : ιLev k R 0 y⁻¹ = (ιLev k R 0 y)⁻¹ := by
  refine (Matrix.inv_eq_left_inv ?_).symm
  rw [← Dx2.Tower.lev_mul, Matrix.nonsing_inv_mul _ hy, Dx2.Tower.lev_one]



theorem vecV_append_singleton_eq_vecV_sliceAt (k R ρ : ℕ) (hρ : ρ = 0) (e : R + ρ = R) (S : B.RealPlaceData k R Wp Wq) (S0 : B.RealPlaceData k ρ Wp Wq)
    (hzL : D.castV e (liftVec k R ρ S0.z) = S.z) (hzL' : D.castV e (liftVec k R ρ S0.z') = S.z')
    (hπ : ∀ y, S0.π y = S.π (D.castM e (ιLev k R ρ y))) (hπ' : ∀ y, S0.π' y = S.π' (D.castM e (ιLev k R ρ y)))
    (hN : S.μN = D.muN k R) (hW1 : S.μW Set.univ = 1) (hW1' : S.μW' Set.univ = 1)
    (hW01 : S0.μW Set.univ = 1) (hW01' : S0.μW' Set.univ = 1) (hN0 : S0.μN = D.muN k ρ)
    (ν' : Fin (2 * R + k + 1) → ℂ) (m₀ : B.Mat k R) (ν'r : Fin (2 * ρ + k + 1) → ℂ) (m₀r : B.Mat k ρ)
    (hν : D.castV e (liftVec k R ρ ν'r) = ν') (hm : D.castM e (ιLev k R ρ m₀r) = m₀)
    (hFb : D.IsBaseFrame S ν' m₀) (hF0 : D.IsBaseFrame S0 ν'r m₀r)
    (h : C.LPt) (hh : D.IsLocPt h R) (ζ : ℂ) (hζ : ζ ≠ 0)
    (F : B.Mat k R → (Wq →L[ℂ] Wp)) (hF : KB.CptCoef S F) (hR : 1 ≤ R) (e' : ρ = R - D.ptSize h) :
    D.vecV S ν' m₀ F (h ++ [(1, ζ)]) = D.vecV S0 ν'r m₀r (D.castF e' (D.sliceAt k R S.z S.z' F h)) [(1, ζ)] := by
  subst hρ
  have hzS : S.z = liftVec k R 0 S0.z := by rw [← hzL]; exact (Dx2.Tower.castV_rfl _).symm
  have hzS' : S.z' = liftVec k R 0 S0.z' := by rw [← hzL']; exact (Dx2.Tower.castV_rfl _).symm
  have hνS : ν' = liftVec k R 0 ν'r := by rw [← hν]; exact Dx2.Tower.castV_rfl _
  have hmS : m₀ = ιLev k R 0 m₀r := by rw [← hm]; exact Dx2.MN.castM_rfl _
  have hT : Tz k R S.z = Tz k 0 S0.z := by rw [hzS]; exact Tz_lift R S0.z
  have hT' : Tz k R S.z' = Tz k 0 S0.z' := by rw [hzS']; exact Tz_lift R S0.z'
  obtain ⟨hZh, hdR, hQmono, hdd, hw⟩ := CompactCoefficientAppend.perm_app h R hh ζ hζ
  set σR := hh.2 ▸ D.ptPerm h with hσR
  set dR := hh.2 ▸ D.ptDiag h with hdRdef
  set Z := U.hMat σR dR with hZdef
  have hZu : IsUnit Z.det := by rw [hZdef, hMat_monoP]; exact C2x2.isUnit_det_monomialMatrix _ _ hdR
  have hq := isLocPt_app h R hh ζ hζ
  have hG : D.ptG (Tz k R S.z * Tz k R S.z') R (h ++ [(1, ζ)]) =
      Complex.normSq (D.ptMatN h R).det * (Complex.normSq ζ - Tz k R S.z * Tz k R S.z') := by
    unfold D.ptG
    rw [ptMatN_append_one h ζ R hh.2, det_extendOne, ptMatN_append_head h ζ R hh.2, Complex.normSq_mul]
    ring
  have hdetpos : 0 < Complex.normSq (D.ptMatN h R).det := by
    rw [← hZh]; exact Complex.normSq_pos.2 hZu.ne_zero
  by_cases hζT : Complex.normSq ζ ≤ Tz k R S.z * Tz k R S.z'
  · have hL : D.vecV S ν' m₀ F (h ++ [(1, ζ)]) = 0 := by
      unfold D.vecV
      rw [dite_eq_right]
      rintro ⟨_, hpos⟩
      rw [hG] at hpos
      nlinarith
    rw [hL, vector_level_zero_degenerate rfl S0 ν'r m₀r _ ζ (by rw [← hT, ← hT']; exact hζT)]
  push_neg at hζT
  have hζT0 : Tz k 0 S0.z * Tz k 0 S0.z' < Complex.normSq ζ := by rw [← hT, ← hT']; exact hζT
  obtain ⟨γ0, hγ0G, hZ0, hD0⟩ := exists_frame_level_zero rfl S0 ν'r m₀r hF0 ζ hζT0
  rw [vector_level_zero_eq_jacquet rfl S0 ν'r m₀r hF0 _ ζ hζT0 γ0 hγ0G hZ0 hD0, jacquet_integral_level_zero rfl S0 hN0 _ γ0]
  have hZ0' : Zhat k 0 S0.z S0.z' γ0 = Matrix.of fun _ _ => ζ := by rw [hZ0, ptMatN_one]
  have hγG : U.mMap k R 0 Z γ0 ∈ B.GV k R := (Formalism.FourierDecayAlt.P.slice_membership k R 0).1 Z γ0 hZu.ne_zero hγ0G
  have hZhat : Zhat k R S.z S.z' (U.mMap k R 0 Z γ0) = D.ptMatN (h ++ [(1, ζ)]) (R + 1) := by
    have h1 := zhat_mMap (j := R) S.z S.z' S.z_mem S.z'_mem Z γ0
    refine h1.trans ?_
    rw [hzS, hzS', lowV_liftVec, lowV_liftVec, hZ0', ptMatN_append_one h ζ R hh.2, hZh]
  have hDγ : D.IsDFrame S ν' m₀ (U.mMap k R 0 Z γ0) := by
    rw [hνS, hmS]
    exact dFrame_mMap S S0 hzS hzS' ν'r m₀r Z hZu γ0 (gv_unit hγ0G) ζ hζ hZ0' hD0
  have hpos : 0 < D.ptG (Tz k R S.z * Tz k R S.z') R (h ++ [(1, ζ)]) := by
    rw [hG]; exact mul_pos hdetpos (by linarith)
  rw [Formalism.FourierDecayAlt.P.isotropic_vectors_linear_indep k R Wp Wq S ν' m₀ F _ hq _ hFb hpos hγG hZhat hDγ]
  have hrel := Formalism.FourierDecayAlt.P.relevant_points_holds k R Wp Wq S _ _ hq hγG hZhat
  obtain ⟨hFc, Rb, hFs⟩ := CompactCoefficientAppend.cptCoef_cont_supp S F hF
  have hZw : Zhat k R S.z S.z' (U.mMap k R 0 Z γ0) =
      C2.monoP (hq.2 ▸ D.ptPerm (h ++ [(1, ζ)])) (hq.2 ▸ D.ptDiag (h ++ [(1, ζ)])) := by
    rw [hZhat]; exact hQmono
  rw [orbJ_mMap S hN hW1 hW1' S0.z S0.z' hzS hzS' σR dR hdR γ0 hγ0G hrel _ _ hdd hZw hw F hFc hR Rb hFs]

  have hsW0 : SigmaFinite S0.μW := Dx2.OrbJ.sigmaF S0.haarW
  have hsW0' : SigmaFinite S0.μW' := Dx2.OrbJ.sigmaF S0.haarW'
  have hH := haar_lev R 0 e S0.z S.z hzL S.μW S0.μW S.haarW S0.haarW hW1 hW01
  have hH' := haar_lev R 0 e S0.z' S.z' hzL' S.μW' S0.μW' S.haarW' S0.haarW' hW1' hW01'
  rw [hH, hH', Measure.map_prod_map _ _ (levMt_cont R 0 e).measurable (levMt_cont R 0 e).measurable,
    ((levMt_emb R 0 e).prodMap (levMt_emb R 0 e)).integral_map]
  have hae : ∀ᵐ y ∂(S0.μW.prod S0.μW'), Matrix.of y.1 ∈ UWset k 0 S0.z ∧ Matrix.of y.2 ∈ UWset k 0 S0.z' := by
    have b1 := (Measure.quasiMeasurePreserving_fst (μ := S0.μW) (ν := S0.μW')).ae (Dx2.OrbJ.ae_mem S0.haarW)
    have b2 := (Measure.quasiMeasurePreserving_snd (μ := S0.μW) (ν := S0.μW')).ae (Dx2.OrbJ.ae_mem S0.haarW')
    filter_upwards [b1, b2] with x h1 h2 using ⟨h1, h2⟩
  refine integral_congr_ae ?_
  filter_upwards [hae] with y hy
  obtain ⟨y1, y2⟩ := y
  have hlev : ∀ x : Mt k 0, Matrix.of (levMt R 0 e x) = ιLev k R 0 (Matrix.of x) := by
    intro x; simp only [levMt, Equiv.apply_symm_apply]; exact Dx2.MN.castM_rfl _
  simp only [Prod.map_apply, conjL_apply, hlev, midB_lev]
  have hy2u : IsUnit (Matrix.of y2).det := gv_unit hy.2.1
  rw [← lev_inv _ hy2u, hπ (Matrix.of y1), hπ' (Matrix.of y2)⁻¹, Dx2.MN.castM_rfl, Dx2.MN.castM_rfl]
  congr 2

  show _ = D.sliceAt k R S.z S.z' F h (D.castM e' ((Matrix.of y1)⁻¹ * γ0 * Matrix.of y2))
  unfold D.sliceAt
  rw [dite_eq_left (by rw [hh.2]), phiFun_tr R (D.ptSize h) (R - D.ptSize h) hh.2 (by rw [hh.2]; simp),
    cast_cancel]

end master

end Formalism.FourierDecayAlt.P.PBM
end
end
end
