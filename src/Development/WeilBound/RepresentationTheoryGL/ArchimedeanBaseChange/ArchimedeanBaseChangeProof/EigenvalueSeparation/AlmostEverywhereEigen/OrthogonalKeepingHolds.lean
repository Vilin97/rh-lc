module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.OneStepOf
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.FaceMapCompSuccAboveCastSucc
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.DualityDiagonalClassOfAffineProperBaseChange
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.PositiveMeasureNorms.AeZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.PositiveMeasureNorms.Convcont
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.PositiveMeasureNorms.Desint
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.PositiveMeasureNorms.Eigae
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.GelfandDuality
public import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.PositiveMeasureNorms.Imports
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.PositiveMeasureNorms.Jointrep
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.PositiveMeasureNorms.Locint
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.PositiveMeasureNorms.MulLeWeightedSquares
import Mathlib.Topology.Separation.CompletelyRegular
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.VecClose
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.PositiveMeasureNorms.Smooth
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.PositiveMeasureNorms.Speciso
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.PositiveMeasureNorms.Specmeas
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.PositiveMeasureNorms.Unfold
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.PositiveMeasureNorms.Weakae
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelRowsColumnsSquareIntegrable

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.PositiveMeasureNorms.Aeeq

section

@[expose] public section

open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2
namespace PositivityTheory.Rg.BcB.E2.P

open MeasureTheory
open scoped Pointwise

theorem aeeq : AeEq := by
  intro X u u' hu hu' hi hi' hae
  have : MeasurableConstSMul X.Γ X.G := ⟨fun γ => measurable_const_mul (γ : X.G)⟩
  have : SMulInvariantMeasure X.Γ X.G X.μ := ⟨fun γ s _ => measure_preimage_mul _ γ.1 s⟩
  set A : Set X.G := {x | u x ≠ u' x} with hA
  have hAo : IsOpen A := isOpen_ne_fun hu hu'
  have hAF : X.μ (A ∩ X.F) = 0 := by
    have h1 : X.ν A = 0 := ae_iff.1 hae
    rw [Ctx.ν, Measure.restrict_apply hAo.measurableSet] at h1
    exact h1
  have hinv : ∀ γ : X.Γ, γ • A = A := by
    intro γ
    ext x
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    show u (((γ⁻¹ : X.Γ) : X.G) * x) ≠ u' (((γ⁻¹ : X.Γ) : X.G) * x) ↔ u x ≠ u' x
    rw [hi _ (γ⁻¹).2, hi' _ (γ⁻¹).2]
  have hμA : X.μ A = 0 := X.fd.measure_zero_of_invariant A hinv hAF
  have hAe : A = ∅ := (hAo.measure_eq_zero_iff X.μ).1 hμA
  funext x
  by_contra h
  have hx : x ∈ A := h
  rw [hAe] at hx
  exact hx

end PositivityTheory.Rg.BcB.E2.P
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.PositiveMeasureNorms.Gelf

section

@[expose] public section

open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2
namespace PositivityTheory.Rg.BcB.E2.P

theorem gelf : Gelf := by
  intro K _ _ _ B _ _ _ _ R
  let A0 : StarSubalgebra ℂ (K →L[ℂ] K) := R.range
  have hc : ∀ x y : A0, x * y = y * x := by
    rintro ⟨x, b, rfl⟩ ⟨y, c, rfl⟩
    apply Subtype.ext
    change R b * R c = R c * R b
    rw [← map_mul, ← map_mul, mul_comm]
  let A : StarSubalgebra ℂ (K →L[ℂ] K) := A0.topologicalClosure
  have : IsClosed (A : Set (K →L[ℂ] K)) := A0.isClosed_topologicalClosure
  let cr : CommRing A := A0.commRingTopologicalClosure hc
  let _ : CommCStarAlgebra A :=
    { (inferInstance : CStarAlgebra A) with mul_comm := cr.mul_comm }
  let G := gelfandStarTransform A
  have hmem : ∀ b, R b ∈ A := fun b => A0.le_topologicalClosure ⟨b, rfl⟩
  refine ⟨WeakDual.characterSpace ℂ A, inferInstance, inferInstance, inferInstance,
    A.subtype.comp G.symm.toStarAlgHom, G.toStarAlgHom.comp (R.codRestrict A hmem), ?_, ?_⟩
  · intro f
    have h1 : ‖G (G.symm f)‖ = ‖G.symm f‖ := (gelfandTransform_isometry A).norm_map_of_map_zero (map_zero _) _
    rw [G.apply_symm_apply] at h1
    rw [h1]
    rfl
  · intro b
    change ((G.symm (G ⟨R b, hmem b⟩) : A) : K →L[ℂ] K) = R b
    rw [G.symm_apply_apply]

end PositivityTheory.Rg.BcB.E2.P
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.PositiveMeasureNorms.Hssep

section

@[expose] public section

open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2
namespace PositivityTheory.Rg.BcB.E2.P

open MeasureTheory

theorem hssep : HsSep := by
  intro X ι _
  haveI : Fact ((1 : ENNReal) ≤ 2) := ⟨by norm_num⟩
  haveI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  haveI : SFinite X.ν := by unfold Ctx.ν; infer_instance
  haveI : IsSeparable X.ν := inferInstance
  haveI : SecondCountableTopology (Lp ℂ 2 X.ν) := inferInstance
  infer_instance

end PositivityTheory.Rg.BcB.E2.P
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.PositiveMeasureNorms.Nonzero

section

@[expose] public section

open MeasureTheory
open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2

namespace PositivityTheory.Rg.BcB.E2.P

theorem nonzero : NonZero := by
  intro X S _ ν _ F f hF hf h0
  have hmeas : MeasurableSet {p : X.G × S | f p.1 p.2 = 0} :=
    (measurableSet_singleton (0 : ℂ)).preimage hf.1
  have h1 : ∀ᵐ x ∂X.μ, ∀ᵐ s ∂ν, f x s = 0 :=
    (Measure.ae_ae_comm (μ := X.μ) (ν := ν) (p := fun x s => f x s = 0) hmeas).2 h0
  have h2 : F =ᵐ[X.μ] (0 : X.G → Lp ℂ 2 ν) := by
    filter_upwards [h1] with x hx
    have : (F x : S → ℂ) =ᵐ[ν] 0 := by
      filter_upwards [(hf.2 x).symm, hx, Lp.coeFn_zero ℂ 2 ν] with s h1 h2 h3
      rw [h1, h2]; rfl
    simpa using (Lp.eq_zero_iff_ae_eq_zero).2 this
  exact (Continuous.ae_eq_iff_eq X.μ hF continuous_const).1 h2

end PositivityTheory.Rg.BcB.E2.P
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.PositiveMeasureNorms.Rowseig

section

@[expose] public section

open MeasureTheory
open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2

namespace PositivityTheory.Rg.BcB.E2.P

theorem rowseig : AeEq → Unfold → RowsEig := by
  intro hAe hUn X ι _ Φ T T₁ k u u' hΦ hT hk heq x i
  have wc : ∀ j, Continuous fun y => inner ℂ (k j y) u := fun j => (hk.cont j).inner continuous_const
  have winv : ∀ j, ∀ γ ∈ X.Γ, ∀ y, (fun y => inner ℂ (k j y) u) (γ * y) = (fun y => inner ℂ (k j y) u) y :=
    fun j γ hγ y => by simp only [hk.inv j γ hγ y]
  have hLc : Continuous fun x => ∑ j, ∫ y, Φ i j y * inner ℂ (k j (x * y)) u ∂X.μ :=
    continuous_finsetSum _ fun j _ => (hUn X (Φ i j) _ (hΦ i j) (wc j) (winv j)).2
  have hRc : Continuous fun x => inner ℂ (k i x) u' := (hk.cont i).inner continuous_const
  have hLinv : ∀ γ ∈ X.Γ, ∀ x, (fun x => ∑ j, ∫ y, Φ i j y * inner ℂ (k j (x * y)) u ∂X.μ) (γ * x)
      = (fun x => ∑ j, ∫ y, Φ i j y * inner ℂ (k j (x * y)) u ∂X.μ) x := by
    intro γ hγ x
    refine Finset.sum_congr rfl fun j _ => integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [mul_assoc, hk.inv j γ hγ]
  have hRinv : ∀ γ ∈ X.Γ, ∀ x, (fun x => inner ℂ (k i x) u') (γ * x) = (fun x => inner ℂ (k i x) u') x :=
    fun γ hγ x => by simp only [hk.inv i γ hγ x]
  have h3 : (fun x => ∑ j, ∫ y, Φ i j y * inner ℂ (k j (x * y)) u ∂X.μ)
      = fun x => ∑ j, ∫ y, ker X.Γ (Φ i j) x y * (T₁ u j : X.G → ℂ) y ∂X.ν := by
    funext x
    refine Finset.sum_congr rfl fun j _ => ?_
    have e1 := (hUn X (Φ i j) _ (hΦ i j) (wc j) (winv j)).1 x
    refine e1.symm.trans (integral_congr_ae ((hk.rep u j).mono fun y hy => ?_))
    simp only [hy]
  have hae : (fun x => ∑ j, ∫ y, Φ i j y * inner ℂ (k j (x * y)) u ∂X.μ) =ᵐ[X.ν]
      fun x => inner ℂ (k i x) u' := by
    rw [h3]
    have h1 := hT (T₁ u) i
    rw [heq] at h1
    exact h1.symm.trans (hk.rep u' i)
  exact congrFun (hAe X _ _ hLc hRc hLinv hRinv hae) x

end PositivityTheory.Rg.BcB.E2.P
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.PositiveMeasureNorms.Rowsex

section

@[expose] public section

open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2
open MeasureTheory

namespace PositivityTheory.Rg.BcB.E2.P

theorem rowsex : KerBasic → VecEx → VecNorm → VecInner → RowsEx := by
  intro hK hE hN hI X ι _ Φ T hΦ hT
  have hΨ : ∀ i j, Tst ((fun i j => adj (Φ j i)) i j : X.G → ℂ) := fun i j => (hK X (Φ j i) (hΦ j i)).2.2.2.1
  obtain ⟨k', hc, hv⟩ := hE X ι (fun i j => adj (Φ j i)) hΨ
  obtain ⟨C, Ω, hC, hΩ, hb⟩ := hN X ι (fun i j => adj (Φ j i)) hΨ
  refine ⟨fun i x => k' x i, ⟨hc, ?_, ?_, ⟨C, Ω, hC, hΩ, fun i x => hb x i _ (hv x i)⟩⟩⟩
  · intro i γ hγ x
    refine PiLp.ext fun l => Lp.ext ?_
    filter_upwards [hv (γ * x) i l, hv x i l] with z h1 h2
    rw [h1, h2]
    exact ((hK X _ (hΨ l i)).2.2.1 γ hγ z x).2
  · intro u i
    filter_upwards [hT u i] with x hx
    rw [hx]
    exact ((hI X ι Φ x i (k' x i) u hΦ).2 (hv x i)).symm

end PositivityTheory.Rg.BcB.E2.P
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.PositiveMeasureNorms.Tonelli

section

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2

namespace PositivityTheory.Rg.BcB.E2.P.Tonelli

theorem enorm_sq {S : Type} [MeasurableSpace S] {ν : Measure S} (g : Lp ℂ 2 ν) :
    ‖g‖ₑ ^ 2 = ∫⁻ s, ‖(g : S → ℂ) s‖ₑ ^ 2 ∂ν := by
  rw [Lp.enorm_def, eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
    ← ENNReal.rpow_two, ← ENNReal.rpow_mul]
  · norm_num
  · exact Lp.aestronglyMeasurable g

end PositivityTheory.Rg.BcB.E2.P.Tonelli

namespace PositivityTheory.Rg.BcB.E2.P

theorem tonelli : Tonelli := by
  intro Y S _ _ m _ ν _ F f W hf hW hfin
  have hmeas : Measurable (Function.uncurry fun y s => W y * ‖f y s‖ₑ ^ 2) :=
    (hW.comp measurable_fst).mul (hf.1.enorm.pow_const 2)
  refine ae_lt_top hmeas.lintegral_prod_left' ?_
  rw [← lintegral_lintegral_swap hmeas.aemeasurable]
  refine ne_of_eq_of_ne (lintegral_congr fun y => ?_) hfin
  have hy : Measurable fun s => f y s := hf.1.comp measurable_prodMk_left
  rw [lintegral_const_mul _ (hy.enorm.pow_const 2), Tonelli.enorm_sq]
  congr 1
  exact lintegral_congr_ae ((hf.2 y).mono fun s hs => by simp only [hs])

end PositivityTheory.Rg.BcB.E2.P
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.OrthogonalKeepingHolds

section

@[expose] public section

namespace PositivityTheory.Rg.BcB.E2

open E1

theorem spec_holds : Spec := P.spec P.gelf P.point P.specmeas P.speciso

theorem desint_holds : Desint :=
  P.desint P.jointrep P.tonelli P.weakae (P.eigae P.weakae) (P.locint P.tonelli) P.nonzero (P.smooth P.convcont)

theorem fData_holds : FData :=
  P.fdata (P.rowsex kerBasic vecEx vecNorm vecInner) (P.rowseig P.aeeq (P.unfold kerBasic P.convcont))

theorem oneStep_holds : OneStep := oneStep_of spec_holds fData_holds desint_holds P.hssep

theorem orthogonal_keeping_holds : E.OrthogonalKeepingOperator := orthogonal_keeping_of_estimate oneStep_holds

theorem proper_base_change : E.E2 := duality_diagonalClass_of_affineProperBaseChange orthogonal_keeping_holds

end PositivityTheory.Rg.BcB.E2
end
end
