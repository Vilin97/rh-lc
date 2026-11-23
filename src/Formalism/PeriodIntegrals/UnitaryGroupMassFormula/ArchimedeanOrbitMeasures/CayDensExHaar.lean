module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.CayDensExCayK
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.CayDensExCayS
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.CayDensExLHU
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.CayDensExOm
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.CayDensExTop
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.CayleyInverseMeasurable
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ContinuousAdelicGL2Det
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.CayDensExHua
public import Mathlib.Analysis.Matrix.Normed
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.HuaInvOfTauDeriv
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.CayDensExCayH
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.CayDensExTop
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.HasFDerivAtTauR

section

@[expose] public section

noncomputable section

namespace HcInf

open HcS.BasicNotions Matrix Filter Topology

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

section Deriv

variable {P Q : ℕ}

local notation "Mat" => Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ

def tauR (H X : Mat) : Mat :=
  (1 + 1) - (4 : ℂ) • (((1 + 1) - X) * Ring.inverse (H * ((1 + 1) + X) + ((1 + 1) - X)))

theorem smul_four (Z : Mat) : (4 : ℂ) • Z = (1 + 1 + 1 + 1) * Z := by
  rw [show (4 : ℂ) = 1 + 1 + 1 + 1 by norm_num, add_smul, add_smul, add_smul, one_smul, add_mul, add_mul,
    add_mul, one_mul]

theorem key_alg (H X Y Ni K : Mat)
    (hNi : Ni * (H * ((1 + 1) + X) + ((1 + 1) - X)) = 1) (hK : ((1 + 1) - X) * K = 1) :
    Y + ((1 + 1) - X) * Ni * (H * Y - Y) =
      (1 + 1 + 1 + 1) * (((1 + 1) - X) * Ni * H * K * Y) := by
  set S := (1 + 1 : Mat) - X with hS
  have hX : (1 + 1 : Mat) + X = (1 + 1 + 1 + 1) - S := by
    rw [hS]
    noncomm_ring
  have e1 : S * Ni * (H * ((1 + 1) + X) + S) * K = 1 := by
    rw [mul_assoc S Ni, hNi, mul_one, hK]
  rw [hX] at e1
  have e2 : S * Ni * (H * ((1 + 1 + 1 + 1) - S) + S) * K =
      (1 + 1 + 1 + 1) * (S * Ni * H * K) - S * Ni * H * (S * K) + S * Ni * (S * K) := by
    noncomm_ring
  rw [e2, hK, mul_one, mul_one] at e1
  have e3 : (1 + 1 + 1 + 1) * (S * Ni * H * K) = 1 + S * Ni * H - S * Ni := by
    calc (1 + 1 + 1 + 1) * (S * Ni * H * K)
        = ((1 + 1 + 1 + 1) * (S * Ni * H * K) - S * Ni * H + S * Ni) + S * Ni * H - S * Ni := by abel
      _ = 1 + S * Ni * H - S * Ni := by rw [e1]
  calc Y + S * Ni * (H * Y - Y) = (1 + S * Ni * H - S * Ni) * Y := by noncomm_ring
    _ = (1 + 1 + 1 + 1) * (S * Ni * H * K) * Y := by rw [e3]
    _ = (1 + 1 + 1 + 1) * (S * Ni * H * K * Y) := by noncomm_ring

theorem hasFDerivAt_tauR (H X : Mat) (hN : IsUnit (H * ((1 + 1) + X) + ((1 + 1) - X)).det)
    (hS : IsUnit ((1 + 1) - X).det) :
    HasFDerivAt (tauR H) (ContinuousLinearMap.mulLeftRight ℝ Mat
      ((4 : ℂ) • (((1 + 1) - X) * (H * ((1 + 1) + X) + ((1 + 1) - X))⁻¹ * H * ((1 + 1) - X)⁻¹))
      ((4 : ℂ) • (H * ((1 + 1) + X) + ((1 + 1) - X))⁻¹)) X := by
  obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det _).2 hN
  have hA : HasFDerivAt (fun Z : Mat => (1 + 1) - Z) (-ContinuousLinearMap.id ℝ Mat) X :=
    (hasFDerivAt_id X).const_sub _
  have hB := (((hasFDerivAt_const (1 + 1 : Mat) X).add (hasFDerivAt_id X)).const_mul H).add hA
  have hI : HasFDerivAt Ring.inverse (-ContinuousLinearMap.mulLeftRight ℝ Mat ↑u⁻¹ ↑u⁻¹)
      (H * ((1 + 1) + X) + ((1 + 1) - X)) := by
    rw [← hu]; exact hasFDerivAt_ringInverse u
  have hC := hI.comp X hB
  have hD := ((hA.mul' hC).const_smul (4 : ℂ)).const_sub (1 + 1 : Mat)
  have hE : HasFDerivAt (tauR H) _ X := hD
  have hinv : (↑u⁻¹ : Mat) = (H * ((1 + 1) + X) + ((1 + 1) - X))⁻¹ := by
    rw [Matrix.nonsing_inv_eq_ringInverse, ← hu, Ring.inverse_unit]
  refine hE.congr_fderiv (ContinuousLinearMap.ext fun Y => ?_)
  have hNi := Matrix.nonsing_inv_mul _ hN
  have hK := Matrix.mul_nonsing_inv _ hS
  have k := key_alg H X Y _ _ hNi hK
  change -((4 : ℂ) • (((1 + 1) - X) * (-(Units.val u⁻¹ * (H * (0 + Y) + -Y) * Units.val u⁻¹)) +
      (-Y) * Ring.inverse (H * ((1 + 1) + X) + ((1 + 1) - X)))) =
    (4 : ℂ) • (((1 + 1) - X) * (H * ((1 + 1) + X) + ((1 + 1) - X))⁻¹ * H * ((1 + 1) - X)⁻¹) * Y *
      ((4 : ℂ) • (H * ((1 + 1) + X) + ((1 + 1) - X))⁻¹)
  rw [hinv, ← Matrix.nonsing_inv_eq_ringInverse, smul_four, smul_four, smul_four, zero_add]
  calc _ = (1 + 1 + 1 + 1) * ((Y + ((1 + 1) - X) * (H * ((1 + 1) + X) + ((1 + 1) - X))⁻¹ * (H * Y - Y)) *
          (H * ((1 + 1) + X) + ((1 + 1) - X))⁻¹) := by noncomm_ring
    _ = (1 + 1 + 1 + 1) * (((1 + 1 + 1 + 1) * (((1 + 1) - X) * (H * ((1 + 1) + X) + ((1 + 1) - X))⁻¹ *
          H * ((1 + 1) - X)⁻¹ * Y)) * (H * ((1 + 1) + X) + ((1 + 1) - X))⁻¹) := by rw [k]
    _ = _ := by noncomm_ring

end Deriv

section Sub

variable {P Q : ℕ}

local notation "Mat" => Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ

theorem tauDeriv_at (h : UpqT P Q) (x : lieU P Q) (hx : x ∈ D0 P Q)
    (hn : IsUnit (nH h (x : Mat)).det) :
    ∃ f' : lieU P Q →L[ℝ] lieU P Q,
      (∀ Y : lieU P Q, ((f' Y : lieU P Q) : Mat) = chA h (x : Mat) * (Y : Mat) * chB h (x : Mat)) ∧
      HasFDerivAt (tauL h) f' x := by
  set ι : lieU P Q →L[ℝ] Mat := (lieU P Q).subtypeL with hι
  set L : Mat →L[ℝ] Mat :=
    ContinuousLinearMap.mulLeftRight ℝ Mat (chA h (x : Mat)) (chB h (x : Mat)) with hL
  have hM : HasFDerivAt (tauR (UpqT.mat h)) L (ι x) := hasFDerivAt_tauR (UpqT.mat h) (x : Mat) hn hx
  have c1 : Continuous fun y : lieU P Q => (1 + 1) - ι y := continuous_const.sub ι.continuous
  have c2 : Continuous fun y : lieU P Q => UpqT.mat h * ((1 + 1) + ι y) + ((1 + 1) - ι y) :=
    (continuous_const.mul (continuous_const.add ι.continuous)).add (continuous_const.sub ι.continuous)
  have hev : ∀ᶠ y in 𝓝 x, IsUnit ((1 + 1) - ι y) ∧
      IsUnit (UpqT.mat h * ((1 + 1) + ι y) + ((1 + 1) - ι y)) := by
    filter_upwards [c1.continuousAt.preimage_mem_nhds
        (Units.isOpen.mem_nhds ((Matrix.isUnit_iff_isUnit_det _).2 hx)),
      c2.continuousAt.preimage_mem_nhds
        (Units.isOpen.mem_nhds ((Matrix.isUnit_iff_isUnit_det _).2 hn))] with y h1 h2
    exact ⟨h1, h2⟩
  have heq : (fun y : lieU P Q => ((tauL h y : lieU P Q) : Mat)) =ᶠ[𝓝 x]
      (tauR (UpqT.mat h) ∘ ι) := by
    filter_upwards [hev] with y hy
    have hyD : y ∈ D0 P Q := (Matrix.isUnit_iff_isUnit_det _).1 hy.1
    have hyN : IsUnit (nH h (y : Mat)).det := (Matrix.isUnit_iff_isUnit_det _).1 hy.2
    have hu : IsUnit (UpqT.mat (h * cayF P Q y) + 1).det := by
      have e := hyN
      rw [nH_eq h y hyD, det_mul] at e
      exact isUnit_of_mul_isUnit_left e
    rw [tauL_val h y hyD hu, Matrix.nonsing_inv_eq_ringInverse]
    rfl
  have hF : HasFDerivAt (fun y : lieU P Q => ((tauL h y : lieU P Q) : Mat)) (L.comp ι) x :=
    (HasFDerivAt.comp x hM ι.hasFDerivAt).congr_of_eventuallyEq heq
  have hclosed : IsClosed ((lieU P Q : Set Mat)) := (lieU P Q).isClosed_of_finiteDimensional
  have hmem : ∀ Y, (L.comp ι) Y ∈ lieU P Q := by
    intro Y
    exact hclosed.mem_of_tendsto (hF.lim_real Y) (Eventually.of_forall fun c =>
      (lieU P Q).smul_mem c ((lieU P Q).sub_mem (tauL h _).2 (tauL h x).2))
  refine ⟨(L.comp ι).codRestrict (lieU P Q) hmem, fun Y => ?_, ?_⟩
  · have hLY : L (ι Y) = chA h (x : Mat) * ι Y * chB h (x : Mat) :=
      ContinuousLinearMap.mulLeftRight_apply _ _ _ _ _
    exact hLY
  · have hF' := hasFDerivAt_iff_isLittleO_nhds_zero.1 hF
    refine hasFDerivAt_iff_isLittleO_nhds_zero.2 ?_
    rw [← Asymptotics.isLittleO_norm_left] at hF' ⊢
    refine hF'.congr_left fun k => ?_
    rfl

end Sub

theorem tau_derivative : TauDeriv := fun _ _ h x hx hn => tauDeriv_at h x hx hn

end HcInf
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PreimageSubsetImage

section

@[expose] public section

noncomputable section

namespace HcInf

open HcS.BasicNotions Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal

instance instT2SpaceUnitaryPQ (P Q : ℕ) : T2Space (UpqT P Q) := (isClosedEmbedding_mat P Q).isEmbedding.t2Space

section SlopeTestRemainingChoices

variable {P Q : ℕ}

theorem continuousOn_cayInv : ContinuousOn (cayInv P Q) (cayS (D0 P Q)) := by
  have e : cayInv P Q = fun g => ⟨cayCand P Q g, cayCand_mem P Q g⟩ :=
    funext (cayInv_eq P Q)
  rw [e]
  refine Topology.IsInducing.subtypeVal.continuousOn_iff.2 ?_
  show ContinuousOn (cayCand P Q) (cayS (D0 P Q))
  intro g hg
  have hdet : IsUnit (g.mat + 1).det := by
    rw [cayley_domain_eq] at hg
    exact hg
  unfold cayCand
  have hc : ContinuousAt (fun g : UpqT P Q => g.mat) g := continuous_mat.continuousAt
  have hinv : ContinuousAt (fun g : UpqT P Q => (g.mat + 1)⁻¹) g := by
    have hdet_cont : ContinuousAt Ring.inverse (g.mat + 1).det := by
      obtain ⟨u, hu⟩ := hdet
      rw [← hu]
      exact NormedRing.inverse_continuousAt u
    have hadd : ContinuousAt (fun x : UpqT P Q => x.mat + 1) g :=
      hc.add continuousAt_const
    exact (continuousAt_matrix_inv (g.mat + 1) hdet_cont).comp
      (f := fun x : UpqT P Q => x.mat + 1) (x := g) hadd
  exact ((continuousAt_const.mul hinv).mul (hc.sub continuousAt_const)).continuousWithinAt

theorem betaH_apply (lam : Measure (lieU P Q)) (S : Set (UpqT P Q)) (hS : MeasurableSet S) :
    betaH P Q lam S = ∫⁻ X in cayF P Q ⁻¹' S ∩ D0 P Q, rhoH P Q X ∂lam := by
  unfold betaH
  rw [Measure.map_apply measurable_cayF hS, withDensity_apply _ (measurable_cayF hS),
    Measure.restrict_restrict (measurable_cayF hS)]

theorem preimage_subset_image (S : Set (UpqT P Q)) :
    cayF P Q ⁻¹' S ∩ D0 P Q ⊆ cayInv P Q '' S := by
  rintro X ⟨hXS, hXD⟩
  exact ⟨cayF P Q X, hXS, cayInv_cayF X hXD⟩

end SlopeTestRemainingChoices

end HcInf
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.CayDensExHaar

section

@[expose] public section

noncomputable section

namespace HcHDC

open HcInf HcS.BasicNotions Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal

theorem cayDensU (P Q : ℕ) (m : Measure (UpqT P Q)) [hm : m.IsHaarMeasure] (lam : Measure (lieU P Q))
    [hlam : lam.IsAddHaarMeasure] :
    ∃ D ∈ 𝓝 (0 : lieU P Q), MeasurableSet D ∧ ∃ f : lieU P Q → ℝ≥0∞, Measurable f ∧ ContinuousAt f 0 ∧
      f 0 ≠ 0 ∧ f 0 ≠ ⊤ ∧ (m.restrict (cayS D)).map (cayInv P Q) = (lam.restrict D).withDensity f := by

  have hW : IsOpen (cayS (D0 P Q)) := isOpen_cayley_domain (P := P) (Q := Q)
  have h00 : (0 : lieU P Q) ∈ D0 P Q := zero_mem_cayley_domain (P := P) (Q := Q)
  have h1W : (1 : UpqT P Q) ∈ cayS (D0 P Q) := by
    have h := cayF_spec (P := P) (Q := Q) 0 h00
    rw [cayF_zero (P := P) (Q := Q)] at h
    exact ⟨0, h00, h⟩
  have hHua : HuaInv := huaInv_of_tauDeriv tau_derivative
  have hinv : ∀ (h : UpqT P Q) (S : Set (UpqT P Q)), MeasurableSet S → S ⊆ cayS (D0 P Q) →
      (fun g => h * g) '' S ⊆ cayS (D0 P Q) →
      betaH P Q lam ((fun g => h * g) '' S) = betaH P Q lam S :=
    fun h S hS hSW hhSW => hHua P Q lam hlam h S hS hSW hhSW

  have hcpt : ∀ K, IsCompact K → K ⊆ cayS (D0 P Q) → betaH P Q lam K ≠ ⊤ := by
    intro K hK hKW
    have hKm : MeasurableSet K := hK.isClosed.measurableSet
    have hCc : IsCompact (insert (0 : lieU P Q) (cayInv P Q '' K)) :=
      (hK.image_of_continuousOn ((continuousOn_cayInv (P := P) (Q := Q)).mono hKW)).insert 0
    have hC0 : insert (0 : lieU P Q) (cayInv P Q '' K) ⊆ D0 P Q := by
      rintro X (rfl | ⟨g, hg, rfl⟩)
      · exact h00
      · obtain ⟨Y, hY, hrel⟩ := hKW hg
        rw [cayley_inverse_iff P Q g Y hrel]
        exact hY
    obtain ⟨x0, -, hmax⟩ := hCc.exists_isMaxOn ⟨0, Set.mem_insert _ _⟩
      (fun x hx => (continuousAt_rhoH (P := P) (Q := Q) x (hC0 hx)).continuousWithinAt)
    have hS'm : MeasurableSet (cayF P Q ⁻¹' K ∩ D0 P Q) :=
      (measurable_cayF (P := P) (Q := Q) hKm).inter (isOpen_cell_domain (P := P) (Q := Q)).measurableSet
    have hS'C : cayF P Q ⁻¹' K ∩ D0 P Q ⊆ insert (0 : lieU P Q) (cayInv P Q '' K) :=
      fun X hX => Set.mem_insert_of_mem _ (preimage_subset_image (P := P) (Q := Q) K hX)
    rw [betaH_apply (P := P) (Q := Q) lam K hKm]
    apply ne_of_lt
    calc ∫⁻ X in cayF P Q ⁻¹' K ∩ D0 P Q, rhoH P Q X ∂lam
        ≤ ∫⁻ _ in cayF P Q ⁻¹' K ∩ D0 P Q, rhoH P Q x0 ∂lam := by
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem hS'm] with X hX
          exact isMaxOn_iff.1 hmax X (hS'C hX)
      _ = rhoH P Q x0 * lam (cayF P Q ⁻¹' K ∩ D0 P Q) := setLIntegral_const _ _
      _ < ⊤ := ENNReal.mul_lt_top (lt_top_iff_ne_top.2 ENNReal.ofReal_ne_top)
          ((measure_mono hS'C).trans_lt hCc.measure_lt_top)

  have hne : betaH P Q lam (cayS (D0 P Q)) ≠ 0 := by
    rw [betaH_apply (P := P) (Q := Q) lam _ hW.measurableSet]
    have hpre : cayF P Q ⁻¹' cayS (D0 P Q) ∩ D0 P Q = D0 P Q :=
      Set.inter_eq_right.2 (fun X hX => ⟨X, hX, cayF_spec (P := P) (Q := Q) X hX⟩)
    rw [hpre]
    have hpos : 0 < lam (D0 P Q) := (isOpen_cell_domain (P := P) (Q := Q)).measure_pos lam ⟨0, h00⟩
    intro h0
    rw [lintegral_eq_zero_iff (measurable_rhoH (P := P) (Q := Q))] at h0
    have hF : ∀ᵐ x ∂(lam.restrict (D0 P Q)), False := by
      filter_upwards [h0, ae_restrict_mem (isOpen_cell_domain (P := P) (Q := Q)).measurableSet]
        with x hx hxD
      exact rhoH_pos (P := P) (Q := Q) x hxD hx
    rw [ae_iff] at hF
    simp only [not_false_eq_true, Set.ofPred_true, Measure.restrict_apply_univ] at hF
    exact hpos.ne' hF
  obtain ⟨t, ht0, httop, W', hW'1, hW'W, hβW'⟩ :=
    local_haar_unique (UpqT P Q) m hm (betaH P Q lam) (cayS (D0 P Q)) hW h1W hinv hcpt hne
  obtain ⟨V, hVW', hVo, h1V⟩ := mem_nhds_iff.1 hW'1
  have hβV : (betaH P Q lam).restrict V = t • m.restrict V := by
    have h := congrArg (fun μ : Measure (UpqT P Q) => μ.restrict V) hβW'
    simp only [Measure.restrict_restrict_of_subset hVW', Measure.restrict_smul] at h
    exact h
  have key : ∀ S ⊆ V, betaH P Q lam S = t * m S := by
    intro S hSV
    have h := congrArg (fun μ : Measure (UpqT P Q) => μ S) hβV
    simp only [smul_apply, Measure.restrict_apply' hVo.measurableSet,
      Set.inter_eq_left.2 hSV, smul_eq_mul] at h
    exact h

  set D : Set (lieU P Q) := D0 P Q ∩ cayF P Q ⁻¹' V with hDdef
  have hDnhds : D ∈ 𝓝 (0 : lieU P Q) := by
    have hc : ContinuousAt (cayF P Q) 0 :=
      (continuousOn_cayF (P := P) (Q := Q)).continuousAt
        ((isOpen_cell_domain (P := P) (Q := Q)).mem_nhds h00)
    have hV0 : V ∈ 𝓝 (cayF P Q 0) := by
      rw [cayF_zero (P := P) (Q := Q)]
      exact hVo.mem_nhds h1V
    exact Filter.inter_mem ((isOpen_cell_domain (P := P) (Q := Q)).mem_nhds h00) (hc.preimage_mem_nhds hV0)
  have hDmeas : MeasurableSet D :=
    (isOpen_cell_domain (P := P) (Q := Q)).measurableSet.inter
      (measurable_cayF (P := P) (Q := Q) hVo.measurableSet)
  have hcayS : cayS D = cayS (D0 P Q) ∩ cayInv P Q ⁻¹' D := by
    ext g
    constructor
    · rintro ⟨X, hXD, hrel⟩
      refine ⟨⟨X, hXD.1, hrel⟩, ?_⟩
      show cayInv P Q g ∈ D
      rw [cayley_inverse_iff P Q g X hrel]
      exact hXD
    · rintro ⟨⟨X, -, hrel⟩, hgD⟩
      have hgX := cayley_inverse_iff P Q g X hrel
      refine ⟨X, ?_, hrel⟩
      rw [← hgX]
      exact hgD
  refine ⟨D, hDnhds, hDmeas, fun X => t⁻¹ * rhoH P Q X,
    (measurable_rhoH (P := P) (Q := Q)).const_mul _, ?_, ?_, ?_, ?_⟩
  · exact (ENNReal.continuous_const_mul (ENNReal.inv_ne_top.2 ht0)).continuousAt.comp
      (continuousAt_rhoH (P := P) (Q := Q) 0 h00)
  · exact mul_ne_zero (ENNReal.inv_ne_zero.2 httop) (rhoH_pos (P := P) (Q := Q) 0 h00)
  · exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 ht0) ENNReal.ofReal_ne_top
  · ext A hA
    have hSV : cayInv P Q ⁻¹' A ∩ cayS D ⊆ V := by
      rintro g ⟨-, X, hXD, hrel⟩
      rw [← cayF_eq_of (P := P) (Q := Q) g X hrel]
      exact hXD.2
    have hSmeas : MeasurableSet (cayInv P Q ⁻¹' A ∩ cayS D) := by
      rw [hcayS]
      exact (cayley_inverse_measurable P Q hA).inter (hW.measurableSet.inter (cayley_inverse_measurable P Q hDmeas))
    have hpre : cayF P Q ⁻¹' (cayInv P Q ⁻¹' A ∩ cayS D) ∩ D0 P Q = A ∩ D := by
      ext X
      constructor
      · rintro ⟨⟨hXA, Y, hYD, hrel⟩, hX0⟩
        have h1 : cayInv P Q (cayF P Q X) = X := cayInv_cayF (P := P) (Q := Q) X hX0
        have h2 : cayInv P Q (cayF P Q X) = Y := cayley_inverse_iff P Q _ Y hrel
        have hXY : X = Y := h1.symm.trans h2
        refine ⟨?_, by rw [hXY]; exact hYD⟩
        have hA' : cayInv P Q (cayF P Q X) ∈ A := hXA
        rwa [h1] at hA'
      · rintro ⟨hXA, hXD⟩
        refine ⟨⟨?_, X, hXD, cayF_spec (P := P) (Q := Q) X hXD.1⟩, hXD.1⟩
        show cayInv P Q (cayF P Q X) ∈ A
        rw [cayInv_cayF (P := P) (Q := Q) X hXD.1]
        exact hXA
    have hβS : betaH P Q lam (cayInv P Q ⁻¹' A ∩ cayS D) = ∫⁻ X in A ∩ D, rhoH P Q X ∂lam := by
      rw [betaH_apply (P := P) (Q := Q) lam _ hSmeas, hpre]
    rw [Measure.map_apply (cayley_inverse_measurable P Q) hA, Measure.restrict_apply (cayley_inverse_measurable P Q hA),
      withDensity_apply _ hA, Measure.restrict_restrict hA]
    calc m (cayInv P Q ⁻¹' A ∩ cayS D)
        = t⁻¹ * (t * m (cayInv P Q ⁻¹' A ∩ cayS D)) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel ht0 httop, one_mul]
      _ = t⁻¹ * ∫⁻ X in A ∩ D, rhoH P Q X ∂lam := by rw [← key _ hSV, hβS]
      _ = ∫⁻ X in A ∩ D, t⁻¹ * rhoH P Q X ∂lam :=
          (lintegral_const_mul _ (measurable_rhoH (P := P) (Q := Q))).symm

end HcHDC
end
end
end
