module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugatePlaceBoundedMatrixFromConjugateHalfHomL
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHomLatticeIffIntegralMatrixSplitChart
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DegreeOnePrimeReductionSplitPlaceDictionary
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceAdjointMatrixHomLatticeBoundedConjugatStatement
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjPartMemCompletedSelfDualLatticeIffSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceColumnMemCompletedLatticeIffFrameIntegStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitProjAdeleComponentChartProperties
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugatePlaceBoundedMatrixFromConjugateHalfHomL
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceHomLatticeEntriesBoundedByIdealValuatiStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugatePlaceBoundedMatrixFromConjugateHalfHomLStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.conjugatePlaceBoundedMatrix_from_conjugateHalfHomLattice : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (v : FinPl D) (φ : SplitProj D v) (e : AE D), IsIdemOf φ e → ∀ a : D.host.E, a ∈ D.host.AA → a ≠ 0 → ∀ y : Matrix (Fin S.rank) (Fin T.rank) (Fv D.host.F v), (∀ i j, Valued.v (y i j) ≤ Valued.v (rdQ φ (star a))) → ∃ u, u ∈ latO S T ΛS ΛT (fun _ => True) ∧ IsHalf (cA D e) u ∧ adjCo φ S T (frCo φ βS) (frCo φ βT) u = y := by
  first | exact @GlobalTheory.ConjHalfOnto.conj_half_onto | exact GlobalTheory.ConjHalfOnto.conj_half_onto | (intros; apply GlobalTheory.ConjHalfOnto.conj_half_onto <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMaxValuationIdealSplitPlaceAndConjugate

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SplitIdealMax

theorem exists_max_of_int (D : D7) {v : FinPl D} (g : D.host.E →+* Fv D.host.F v)
    (hg : ∀ o : 𝓞 D.host.E, Valued.v (g (o : D.host.E)) ≤ 1) :
    ∃ a : D.host.E, a ∈ D.host.AA ∧ a ≠ 0 ∧ ∀ a' : D.host.E, a' ∈ D.host.AA → Valued.v (g a') ≤ Valued.v (g a) := by
  have hfg : (D.host.AA : Submodule (𝓞 D.host.E) D.host.E).FG :=
    FractionalIdeal.fg_of_isUnit _ (Ne.isUnit (GlobalTheory.SplitHomLattice.ideal_ne_zero D))
  obtain ⟨s, hs⟩ := hfg
  have hne : s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    rw [Finset.coe_empty, Submodule.span_empty] at hs
    exact GlobalTheory.SplitHomLattice.ideal_ne_zero D (FractionalIdeal.coeToSubmodule_eq_bot.1 hs.symm)
  obtain ⟨a₀, ha₀, hmax⟩ := s.exists_max_image (fun a => Valued.v (g a)) hne
  have hle : ∀ a ∈ (D.host.AA : Submodule (𝓞 D.host.E) D.host.E), Valued.v (g a) ≤ Valued.v (g a₀) := by
    intro a ha
    rw [← hs] at ha
    induction ha using Submodule.span_induction with
    | mem a ha => exact hmax a ha
    | zero => simp only [map_zero, zero_le]
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact Valuation.map_add_le _ hx hy
    | smul o x _ hx =>
      rw [show o • x = (o : D.host.E) * x from rfl, map_mul, Valuation.map_mul]
      exact (mul_le_of_le_one_left' (hg o)).trans hx
  have hmem : a₀ ∈ D.host.AA := by
    show a₀ ∈ (D.host.AA : Submodule (𝓞 D.host.E) D.host.E)
    rw [← hs]; exact Submodule.subset_span ha₀
  have h0 : a₀ ≠ 0 := by
    rintro rfl
    apply GlobalTheory.SplitHomLattice.ideal_ne_zero D
    rw [FractionalIdeal.eq_zero_iff]
    intro a ha
    have := hle a ha
    rw [map_zero, map_zero, le_zero_iff, map_eq_zero] at this
    exact (map_eq_zero g).1 this
  exact ⟨a₀, hmem, h0, fun a' ha' => hle a' ha'⟩

theorem star_int (D : D7) (o : 𝓞 D.host.E) : IsIntegral ℤ (star (o : D.host.E)) :=
  (o.2).map (starRingEnd D.host.E).toIntAlgHom

end GlobalTheory.SplitIdealMax

open GlobalTheory.SplitIdealMax in
theorem GlobalTheory.SplitIdealMax.exists_max_both : ∀ (D : D7) (v : FinPl D) (φ : SplitProj D v) (e : AE D), IsIdemOf φ e → (∃ a : D.host.E, a ∈ D.host.AA ∧ a ≠ 0 ∧ ∀ a' : D.host.E, a' ∈ D.host.AA → Valued.v (rdQ φ a') ≤ Valued.v (rdQ φ a)) ∧ (∃ a : D.host.E, a ∈ D.host.AA ∧ a ≠ 0 ∧ ∀ a' : D.host.E, a' ∈ D.host.AA → Valued.v (rdQ φ (star a')) ≤ Valued.v (rdQ φ (star a))) := by
  intro D v φ _ _
  refine ⟨exists_max_of_int D (GlobalTheory.PlaceRed.rdQh φ) fun o => GlobalTheory.PlaceRed.rdQ_int φ o,
    exists_max_of_int D ((GlobalTheory.PlaceRed.rdQh φ).comp (starRingEnd D.host.E)) fun o =>
      GlobalTheory.PlaceRed.rdQ_int φ ⟨star (o : D.host.E), star_int D o⟩⟩
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMaxValuationIdealSplitPlaceAndConjugateStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_max_valuation_ideal_splitPlace_and_conjugate : ∀ (D : D7) (v : FinPl D) (φ : SplitProj D v) (e : AE D), IsIdemOf φ e → (∃ a : D.host.E, a ∈ D.host.AA ∧ a ≠ 0 ∧ ∀ a' : D.host.E, a' ∈ D.host.AA → Valued.v (rdQ φ a') ≤ Valued.v (rdQ φ a)) ∧ (∃ a : D.host.E, a ∈ D.host.AA ∧ a ≠ 0 ∧ ∀ a' : D.host.E, a' ∈ D.host.AA → Valued.v (rdQ φ (star a')) ≤ Valued.v (rdQ φ (star a))) := by
  first | exact @GlobalTheory.SplitIdealMax.exists_max_both | exact GlobalTheory.SplitIdealMax.exists_max_both | (intros; apply GlobalTheory.SplitIdealMax.exists_max_both <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceBoundedMatrixFromHalfHomLattice

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section




namespace GlobalTheory.SplitHomOnto

open GlobalTheory.SplitHomLattice GlobalTheory.LatticeStable

variable {D : D7}

theorem rk_mem_latHat (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) {a : D.host.E} (ha : a ∈ D.host.AA)
    {s : Fin S.rank → Af D.host.F ⊗[D.host.F] D.host.E}
    (hs : s ∈ latHat D.host.F D.host.E (ΛS : Set (Fin S.rank → D.host.E)))
    {t : Fin T.rank → Af D.host.F ⊗[D.host.F] D.host.E}
    (ht : t ∈ latHat D.host.F D.host.E (ΛT : Set (Fin T.rank → D.host.E))) :
    rk S T a s t ∈ latO S T ΛS ΛT fun _ => True := by
  apply _root_.GlobalTheory.ConjHalfOnto.rk_mem_lat <;> assumption

theorem honto : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (v : FinPl D) (φ : SplitProj D v) (e : AE D), IsIdemOf φ e → ∀ a : D.host.E, a ∈ D.host.AA → a ≠ 0 → ∀ y : Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v), (∀ i j, Valued.v (y i j) ≤ Valued.v (rdQ φ a)) → ∃ u, u ∈ latO S T ΛS ΛT (fun _ => True) ∧ IsHalf e u ∧ mapCo φ S T (frCo φ βS) (frCo φ βT) u = y := by
  intro D S T ΛS ΛT βS βT hSd hTd hfS hfT v φ e he a haA ha0 y hy
  obtain ⟨hπ, -, hQ, -, -⟩ := GlobalTheory.SplitProjChart.chart_rdA D v φ e he
  have hsi : IsSplitIdem D e := he.1
  set π : AE D →+* Fv D.host.F v := rdA φ with hπdef
  set c : Fv D.host.F v := π (incA D a) with hc
  have hc0 : c ≠ 0 := by
    intro h
    exact ha0 ((π.comp (incA D)).injective (by rw [RingHom.comp_apply, map_zero]; exact h))
  set BS : GL (Fin S.rank) (Fv D.host.F v) := frCo φ βS with hBS
  set BT : GL (Fin T.rank) (Fv D.host.F v) := frCo φ βT with hBT
  set G : Matrix (Fin S.rank) (Fin S.rank) (Fv D.host.F v) := S.gram.map (rdQ φ) with hG
  have hGπ : G = S.gram.map fun x => π (incA D x) := Matrix.ext fun i j => (hQ _).symm
  have hGu : IsUnit G.det := by
    have := (GlobalTheory.LatVac.gram_det_isUnit S).map (π.comp (incA D))
    rw [RingHom.map_det] at this
    rw [hGπ]; exact this
  choose σ hσ using hπ.1
  set Y : Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v) := c⁻¹ • y with hY
  have hYi : ∀ i j, Valued.v (Y i j) ≤ 1 := by
    intro i j
    have hy' := hy i j
    rw [← hQ] at hy'
    rw [hY, Matrix.smul_apply, smul_eq_mul, Valuation.map_mul, map_inv₀, hc]
    exact inv_mul_le_one_of_le₀ hy' zero_le
  set X : Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v) := BT.1 * Y with hX
  set Z : Matrix (Fin S.rank) (Fin S.rank) (Fv D.host.F v) := (BS⁻¹).1 * G⁻¹ with hZ
  have hZ1 : Z * (G * BS.1) = 1 := by
    rw [hZ, Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hGu, ← Units.val_mul, inv_mul_cancel,
      Units.val_one]
  have hs : ∀ j, (fun k => finPart D (cA D e * cA D (σ (Z j k)))) ∈
      latHat D.host.F D.host.E (ΛS : Set (Fin S.rank → D.host.E)) := by
    intro j
    refine (GlobalTheory.T.conjPart_mem_completedSelfDualLattice_iff_splitPlace D S ΛS βS hSd hfS v φ e he fun k => cA D (σ (Z j k))).2 fun l => ?_
    have h1 : (fun i => rdA φ (cA D (cA D (σ (Z j i))))) = fun k => Z j k := by
      funext k; rw [GlobalTheory.DualPairCheck.cA_cA]; exact hσ _
    rw [h1]
    have : ((fun k => Z j k) ᵥ* (S.gram.map (rdQ φ) * (frCo φ βS).1)) l = (Z * (G * BS.1)) j l := rfl
    rw [this, hZ1, Matrix.one_apply]
    split_ifs <;> simp
  have ht : ∀ j, (fun k => finPart D (e * σ (X k j))) ∈
      latHat D.host.F D.host.E (ΛT : Set (Fin T.rank → D.host.E)) := by
    intro j
    refine (GlobalTheory.T.splitPlace_column_mem_completedLattice_iff_frame_integral D T ΛT βT hTd hfT v φ e he fun k => σ (X k j)).2 fun i => ?_
    have h1 : (fun k => rdA φ (σ (X k j))) = fun k => X k j := funext fun k => hσ _
    rw [h1]
    have : (((frCo φ βT)⁻¹ : GL (Fin T.rank) (Fv D.host.F v)).1 *ᵥ fun k => X k j) i = ((BT⁻¹).1 * X) i j := rfl
    rw [this, hX, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
    exact hYi i j
  set u₀ : WO S T := ∑ j, rk S T a (fun k => finPart D (cA D e * cA D (σ (Z j k))))
    (fun k => finPart D (e * σ (X k j))) with hu₀
  have hu₀m : u₀ ∈ latO S T ΛS ΛT fun _ => True :=
    sum_mem fun j _ => rk_mem_latHat S T ΛS ΛT haA (hs j) (ht j)
  refine ⟨e • u₀, smul_mem_latO D S T _ _ _ e (idem_int hsi) _ hu₀m, fun i j => ?_, ?_⟩
  · rw [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, hsi.1]
  · have hmap : (e • u₀).map π = c • (X * (Z * G)) := by
      refine Matrix.ext fun i l => ?_

      rw [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, RingHom.map_mul, pi_idem hsi hπ, one_mul, hu₀,
      Matrix.sum_apply, map_sum, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [pi_rk hsi hπ S T a (fun k => cA D (σ (Z j k))) (fun k => σ (X k j)) i l]
      simp only [GlobalTheory.DualPairCheck.cA_cA, hσ]
      simp only [Matrix.mul_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hGπ, Matrix.map_apply]
      ring
    have hZG : Z * G = (BS⁻¹).1 := by rw [hZ, Matrix.nonsing_inv_mul_cancel_right _ _ hGu]
    have hXZG : c • (X * (Z * G)) = BT.1 * y * (BS⁻¹).1 := by
      rw [hZG, hX, hY, Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_inv_cancel₀ hc0,
        one_smul]
    show (BT⁻¹).1 * ((e • u₀).map π) * BS.1 = y
    rw [hmap, hXZG, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mul, Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]

end GlobalTheory.SplitHomOnto
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceBoundedMatrixFromHalfHomLatticeStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.splitPlaceBoundedMatrix_from_halfHomLattice : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (v : FinPl D) (φ : SplitProj D v) (e : AE D), IsIdemOf φ e → ∀ a : D.host.E, a ∈ D.host.AA → a ≠ 0 → ∀ y : Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v), (∀ i j, Valued.v (y i j) ≤ Valued.v (rdQ φ a)) → ∃ u, u ∈ latO S T ΛS ΛT (fun _ => True) ∧ IsHalf e u ∧ mapCo φ S T (frCo φ βS) (frCo φ βT) u = y := by
  first | exact @GlobalTheory.SplitHomOnto.honto | exact GlobalTheory.SplitHomOnto.honto | (intros; apply GlobalTheory.SplitHomOnto.honto <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceThetaLatticeHalvesSelfDualFrames

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitLatticeHalves

theorem splitLattice : ∀ D : D7, SplitLattice D := by
  intro D S T ΛS ΛT βS βT hS hT hfS hfT v φ e he
  obtain ⟨⟨a, haA, ha0, hmax⟩, ⟨b, hbA, hb0, hbmax⟩⟩ := GlobalTheory.T.exists_max_valuation_ideal_splitPlace_and_conjugate D v φ e he
  refine ⟨⟨a, haA, ha0, hmax, Set.ext fun y => ⟨?_, fun hy => ?_⟩⟩,
    ⟨b, hbA, hb0, hbmax, Set.ext fun y => ⟨?_, fun hy => ?_⟩⟩⟩
  · rintro ⟨t, ⟨ht, -⟩, rfl⟩
    exact GlobalTheory.T.splitPlaceHomLattice_entries_bounded_by_idealValuation D S T ΛS ΛT βS βT hS hT hfS hfT v φ e he a hmax t ht
  · obtain ⟨u, hu, hh, rfl⟩ := GlobalTheory.T.splitPlaceBoundedMatrix_from_halfHomLattice D S T ΛS ΛT βS βT hS hT hfS hfT v φ e he a haA ha0 y hy
    exact ⟨u, ⟨hu, hh⟩, rfl⟩
  · rintro ⟨t, ⟨ht, -⟩, rfl⟩
    exact GlobalTheory.T.splitPlaceAdjointMatrix_homLattice_bounded_conjugateIdeal D S T ΛS ΛT βS βT hS hT hfS hfT v φ e he b hbmax t ht
  · obtain ⟨u, hu, hh, rfl⟩ := GlobalTheory.T.conjugatePlaceBoundedMatrix_from_conjugateHalfHomLattice D S T ΛS ΛT βS βT hS hT hfS hfT v φ e he b hbA hb0 y hy
    exact ⟨u, ⟨hu, hh⟩, rfl⟩

end GlobalTheory.SplitLatticeHalves
end
end
