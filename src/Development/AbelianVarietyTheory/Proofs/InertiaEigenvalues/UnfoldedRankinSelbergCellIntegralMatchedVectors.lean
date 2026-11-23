module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadNatZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurDir
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
public import Development.AbelianVarietyTheory.Definitions.Divisors.NAInterSupSSubset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhitMulLocGLDiagPowOfFixed
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CellLintegral
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousGlobalWhittakerCoefficientGLAdeles
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormRapidKernelSmoothSpanSmoothCuspidalBound
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantProj
public import GroundTheory.AutomorphicForms.GL2.GJMatrixAdelic
public import GroundTheory.GlobalFields.TateThesis.GaussianSchwartz
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsValLastRowEqOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinsuppVanishingOnEquivComplProd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsOpenAdelicUnipotentTimesIntegralOutsideSet
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralUnipotentCellPosLtTopContinuous
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergCellIntegralFinitePartNonnegStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SuperDiagBlockGL
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocFacOfNeg
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EulerProductRankinSelbergGLnGLmDirichletSeries
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasProdLocalRankinSelbergFactorSelfOfEulerProduc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProdTsumEqTsumIndicatorEnnreal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TsumSchurSquareCellProductEqEulerProduct
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFourierGaussLattice

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff

noncomputable section

namespace GlobalTheory.FourierCell

open GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open scoped nonZeroDivisors SchwartzMap

variable {E : Type} [Field E] [NumberField E]

theorem finId_val (u : (Af E)ˣ) :
    ((finId E u : (Ad E)ˣ) : Ad E) = ((1, (u : Af E)) : InfiniteAdeleRing E × Af E) := by
  change (1 - sFin E 1 + sFin E (u : Af E) : Ad E) = _
  refine Prod.ext ?_ ?_
  · change (1 : InfiniteAdeleRing E) - 0 + 0 = 1
    simp
  · change (1 : Af E) - 1 + (u : Af E) = u
    simp

theorem mem_one_iff (x : Af E) :
    x ∈ idealFiniteAdeles (1 : (FractionalIdeal (𝓞 E)⁰ E)ˣ) ↔ ∀ v, Valued.v (pLoc E v x) ≤ 1 := by
  simp only [mem_idealFiniteAdeles, Units.val_one, FractionalIdeal.count_one, neg_zero, WithZero.exp_zero]
  rfl

theorem val_zpow_unif {w : HeightOneSpectrum (𝓞 E)} {ϖ : w.adicCompletion E} (h : IsUnifV E w ϖ) (n : ℤ) :
    Valued.v (ϖ ^ n) = ((Multiplicative.ofAdd (-n) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  rw [map_zpow₀, h, ← WithZero.coe_zpow, ← ofAdd_zsmul]
  simp

theorem ofAdd_le_one_iff (n : ℤ) :
    ((Multiplicative.ofAdd n : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ≤ 1 ↔ n ≤ 0 := by
  rw [← WithZero.coe_one, WithZero.coe_le_coe, ← ofAdd_zero, Multiplicative.ofAdd_le]

theorem exists_fourier_gauss_lattice : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (y₀ : Fin (m + 1) → Ad E),
    (∀ w ∉ S, ∀ j, pLoc E w (pFin E (y₀ j)) ∈ w.adicCompletionIntegers E) →
    ∃ F ∈ GroundTheory.Automorphic.GJMatrix.schwartzBruhatPi (K := E) (ι := Fin (m + 1)),
      Continuous (GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F) ∧
      (∀ y, 0 ≤ (GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F y).re ∧
        (GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F y).im = 0) ∧
      0 < (GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F y₀).re ∧
      ∀ (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
      ∀ a : HeightOneSpectrum (𝓞 E) →₀ ℤ, (∀ v ∈ S, a v = 0) →
      ∀ y : Fin (m + 1) → Ad E,
        (∀ w ∉ S, (∀ j, pLoc E w (pFin E (y j)) ∈ w.adicCompletionIntegers E) ∧
          ∃ j, Valued.v (pLoc E w (pFin E (y j))) = 1) →
        ((∀ w, 0 ≤ a w) → GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F
            (fun j => ((finId E (GlobalTheory.CellDec.adl ϖ a) : (Ad E)ˣ) : Ad E) * y j) =
          GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F y) ∧
        ((∃ w, a w < 0) → GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F
            (fun j => ((finId E (GlobalTheory.CellDec.adl ϖ a) : (Ad E)ˣ) : Ad E) * y j) = 0) := by
  intro E _ _ _ m S y₀ hy₀
  classical
  let φ : 𝓢(Fin (m + 1) → NumberField.mixedEmbedding.mixedSpace E, ℂ) :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (toEuclidean (E := Fin (m + 1) → NumberField.mixedEmbedding.mixedSpace E))
      (GroundTheory.Global.gaussianSchwartz _)
  have hφ : ∀ x, φ x = ((Real.exp (-Real.pi * ‖toEuclidean x‖ ^ 2) : ℝ) : ℂ) := fun x => by
    simp [φ, SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
  let g : (Fin (m + 1) → Af E) → ℂ := finiteTensor fun j => cosetIndicator 1 (pFin E (y₀ j))
  have hg : g ∈ finiteSchwartzBruhatPi E :=
    finiteTensor_mem fun j => cosetIndicator_mem_finiteSchwartzBruhat _ _
  let G := schwartzBruhatTensorPi φ g
  have hG : G ∈ schwartzBruhatPi (K := E) (ι := Fin (m + 1)) := schwartzBruhatTensorPi_mem φ hg
  have hG1 := adelicFourierPi_mem_schwartzBruhatPi hG
  have hG2 := adelicFourierPi_mem_schwartzBruhatPi hG1
  have hG3 := adelicFourierPi_mem_schwartzBruhatPi hG2
  have hFG : adelicFourierPi E (adelicFourierPi E (adelicFourierPi E (adelicFourierPi E G))) = G := by
    rw [adelicFourierPi_adelicFourierPi hG2, adelicFourierPi_adelicFourierPi hG]
    funext x
    simp
  have hGv : ∀ y, G y = φ (infPartPi y) *
      if ∀ j v, Valued.v (pLoc E v (pFin E (y j)) - pLoc E v (pFin E (y₀ j))) ≤ 1 then 1 else 0 := by
    intro y
    simp only [G, g, schwartzBruhatTensorPi, finiteTensor, cosetIndicator_apply, Finset.prod_boole,
      Finset.mem_univ, true_implies, mem_one_iff, map_sub]
    rfl
  refine ⟨adelicFourierPi E (adelicFourierPi E (adelicFourierPi E G)), hG3, ?_, ?_, ?_, ?_⟩
  · rw [hFG]; exact continuous_of_mem_schwartzBruhatPi hG
  · intro y
    rw [hFG, hGv, hφ]
    split_ifs
    · rw [mul_one]
      exact ⟨by rw [Complex.ofReal_re]; exact (Real.exp_pos _).le, Complex.ofReal_im _⟩
    · rw [mul_zero]
      exact ⟨le_refl _, rfl⟩
  · rw [hFG, hGv, hφ, if_pos (fun j v => by simp)]
    rw [mul_one, Complex.ofReal_re]
    exact Real.exp_pos _
  · intro ϖ hϖ a ha y hy
    have hFy : ∀ z, adelicFourierPi E (adelicFourierPi E (adelicFourierPi E (adelicFourierPi E G))) z = G z :=
      fun z => by rw [hFG]
    have hinf : infPartPi (fun j => ((finId E (GlobalTheory.CellDec.adl ϖ a) : (Ad E)ˣ) : Ad E) * y j) = infPartPi y := by
      funext j
      simp only [infPartPi, finId_val]
      congr 1
      change (1 : InfiniteAdeleRing E) * (y j).1 = (y j).1
      exact one_mul _
    have hfin : ∀ j v, pLoc E v (pFin E (((finId E (GlobalTheory.CellDec.adl ϖ a) : (Ad E)ˣ) : Ad E) * y j)) =
        ((ϖ v : v.adicCompletion E) ^ a v) * pLoc E v (pFin E (y j)) := by
      intro j v
      rw [map_mul, map_mul, finId_val]
      change ((ϖ v ^ a v : (v.adicCompletion E)ˣ) : v.adicCompletion E) * _ = _
      rw [Units.val_zpow_eq_zpow_val]
    have hint : ∀ w ∉ S, ∀ j, Valued.v (pLoc E w (pFin E (y₀ j))) ≤ 1 := fun w hw j => by
      simpa [HeightOneSpectrum.mem_adicCompletionIntegers] using hy₀ w hw j
    constructor
    · intro hpos
      rw [hFy, hFy, hGv, hGv, hinf]
      congr 1
      refine if_congr ?_ rfl rfl
      refine forall_congr' fun j => forall_congr' fun v => ?_
      rw [hfin]
      by_cases hv : v ∈ S
      · rw [ha v hv, zpow_zero, one_mul]
      · have h1 := hint v hv j
        have h2 : Valued.v (pLoc E v (pFin E (y j))) ≤ 1 := by
          simpa [HeightOneSpectrum.mem_adicCompletionIntegers] using (hy v hv).1 j
        have h3 : Valued.v ((ϖ v : v.adicCompletion E) ^ a v) ≤ 1 := by
          rw [val_zpow_unif (hϖ v), ofAdd_le_one_iff]
          linarith [hpos v]
        have key : ∀ t, Valued.v t ≤ 1 → Valued.v (t - pLoc E v (pFin E (y₀ j))) ≤ 1 :=
          fun t ht => (Valuation.map_sub _ _ _).trans (max_le ht h1)
        exact iff_of_true (key _ (by rw [map_mul]; exact mul_le_one' h3 h2)) (key _ h2)
    · rintro ⟨w, hw⟩
      rw [hFy, hGv, if_neg, mul_zero]
      intro hP
      have hwS : w ∉ S := fun h => by rw [ha w h] at hw; exact lt_irrefl _ hw
      obtain ⟨j, hj⟩ := (hy w hwS).2
      have h1 := hint w hwS j
      have h := hP j w
      rw [hfin] at h
      have ht : Valued.v ((ϖ w : w.adicCompletion E) ^ a w * pLoc E w (pFin E (y j))) ≤ 1 := by
        have h4 := Valuation.map_add Valued.v
          ((ϖ w : w.adicCompletion E) ^ a w * pLoc E w (pFin E (y j)) - pLoc E w (pFin E (y₀ j)))
          (pLoc E w (pFin E (y₀ j)))
        rw [sub_add_cancel] at h4
        exact h4.trans (max_le h h1)
      rw [map_mul, hj, mul_one, val_zpow_unif (hϖ w), ofAdd_le_one_iff] at ht
      omega

end GlobalTheory.FourierCell
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TsumPadTermNeTop

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff

noncomputable section
namespace GlobalTheory.RSCellEul

open GlobalTheory.RSnmEul GlobalTheory.RSnmUnf

theorem term_le_locFac {m k : ℕ} (h : m + 1 ≤ k) (q : ℕ) (a : Fin k → ℂ) (x : ℝ) (v : Fin (m + 1) → ℤ) :
    (if (∀ i, 0 ≤ v i) ∧ Antitone v then
          ENNReal.ofReal (‖GlobalTheory.JSW.schurAt (GlobalTheory.RSnmUnf.padNat (n := k) fun i => (v i).toNat) a‖ ^ 2 *
            (q : ℝ) ^ (-(((∑ i, (v i).toNat : ℕ) : ℝ) * x))) else 0) ≤
      GlobalTheory.RSCell.locFac q a x (padInt h v) := by
  split_ifs with hv
  · have hv' := padInt_valid h hv
    rw [GlobalTheory.RSCell.locFac, if_pos ⟨hv'.2, hv'.1⟩, toNat_padInt h v, sum_padNat h]
  · exact bot_le

theorem term_zero {m k : ℕ} (q : ℕ) (a : Fin k → ℂ) (x : ℝ) :
    (if (∀ i, 0 ≤ (0 : Fin (m + 1) → ℤ) i) ∧ Antitone (0 : Fin (m + 1) → ℤ) then
          ENNReal.ofReal (‖GlobalTheory.JSW.schurAt (GlobalTheory.RSnmUnf.padNat (n := k) fun i => ((0 : Fin (m + 1) → ℤ) i).toNat) a‖ ^ 2 *
            (q : ℝ) ^ (-(((∑ i, ((0 : Fin (m + 1) → ℤ) i).toNat : ℕ) : ℝ) * x))) else 0) = 1 := by
  have h0 : (fun i : Fin (m + 1) => ((0 : Fin (m + 1) → ℤ) i).toNat) = 0 := funext fun _ => rfl
  rw [if_pos ⟨fun _ => le_rfl, fun _ _ _ => le_rfl⟩, h0, padNat_zero]
  rw [show (0 : Fin k → ℕ) = fun _ => 0 from rfl, GlobalTheory.RSPole.EulerPole.schurAt_const_zero]
  simp

theorem tprod_le_of_one_le {I : Type} (f g : I → ℝ≥0∞) (hf : ∀ i, 1 ≤ f i) (hfg : ∀ i, f i ≤ g i) :
    ∏' i, f i ≤ ∏' i, g i := by
  have hg : ∀ i, 1 ≤ g i := fun i => (hf i).trans (hfg i)
  rw [(GlobalTheory.RSPole.EulerPole.hasProd_of_one_le f hf).tprod_eq, (GlobalTheory.RSPole.EulerPole.hasProd_of_one_le g hg).tprod_eq]
  exact iSup_mono fun s => Finset.prod_le_prod' fun i _ => hfg i

theorem tsum_padTerm_ne_top : ∀ (E : Type) [Field E] [NumberField E] (m k : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))), m + 1 ≤ k →
    ∀ (α : HeightOneSpectrum (𝓞 E) → Fin k → ℂ) (x : ℝ),
    GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ S} => Ideal.absNorm w.1.asIdeal) (fun w i => α w.1 i) x ≠ ⊤ →
    ∑' l : GlobalTheory.CellDec.abelian₂ E (m + 1) S, (l.1.prod fun w v => if (∀ i, 0 ≤ v i) ∧ Antitone v then
          ENNReal.ofReal (‖GlobalTheory.JSW.schurAt (GlobalTheory.RSnmUnf.padNat (n := k) fun i => (v i).toNat) (α w)‖ ^ 2 *
            (Ideal.absNorm w.asIdeal : ℝ) ^ (-(((∑ i, (v i).toNat : ℕ) : ℝ) * x))) else 0) ≠ ⊤ := by
  intro E _ _ m k S hmk α x hfin
  classical
  let g : HeightOneSpectrum (𝓞 E) → (Fin (m + 1) → ℤ) → ℝ≥0∞ := fun w v =>
    if (∀ i, 0 ≤ v i) ∧ Antitone v then
      ENNReal.ofReal (‖GlobalTheory.JSW.schurAt (GlobalTheory.RSnmUnf.padNat (n := k) fun i => (v i).toNat) (α w)‖ ^ 2 *
        (Ideal.absNorm w.asIdeal : ℝ) ^ (-(((∑ i, (v i).toNat : ℕ) : ℝ) * x))) else 0
  show ∑' l : GlobalTheory.CellDec.abelian₂ E (m + 1) S, l.1.prod g ≠ ⊤
  have hg0 : ∀ w, g w 0 = 1 := fun w => term_zero _ _ _
  obtain ⟨e, he⟩ := GlobalTheory.finsupp_vanishing_on_equiv_compl_prod S (m + 1)
  let f : {w : HeightOneSpectrum (𝓞 E) // w ∉ S} → (Fin (m + 1) → ℤ) → ℝ≥0∞ := fun i v => g i.1 v
  have h1 : ∑' l : GlobalTheory.CellDec.abelian₂ E (m + 1) S, l.1.prod g = ∑' l' : {w : HeightOneSpectrum (𝓞 E) // w ∉ S} →₀ (Fin (m + 1) → ℤ), l'.prod f := by
    rw [← e.tsum_eq]; exact tsum_congr fun l => (he ℝ≥0∞ g hg0 l).symm
  rw [h1, (GlobalTheory.EulerSum.euler_product_intVec_ennreal (m + 1) f fun i => hg0 i.1).2]
  refine ne_top_of_le_ne_top hfin ?_
  rw [GlobalTheory.RSPole.eulD]
  refine tprod_le_of_one_le _ _ (fun i => ?_) (fun i => ?_)
  · exact le_of_eq_of_le (hg0 i.1).symm (ENNReal.le_tsum (f := f i) 0)
  · rw [GlobalTheory.RSCellSum.schurDir_eq_tsum_locFac]
    calc ∑' v, f i v ≤ ∑' v, GlobalTheory.RSCell.locFac (Ideal.absNorm i.1.asIdeal) (α i.1) x (padInt hmk v) :=
          ENNReal.tsum_le_tsum fun v => term_le_locFac hmk _ _ _ v
      _ ≤ _ := ENNReal.tsum_comp_le_tsum_of_injective (padInt_injective hmk) _

end GlobalTheory.RSCellEul
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldedRankinSelbergCellIntegralMatchedVectors

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff

namespace GlobalTheory.RSnmCells

theorem rsTermNM_zero (q : ℕ) {n m : ℕ} (α : Fin n → ℂ) (β : Fin m → ℂ) (x : ℝ) :
    GlobalTheory.RSnmUnf.rsTermNM q α β x 0 = 1 := by
  have h1 : (GlobalTheory.RSnmUnf.padNat (n := n) fun i : Fin m => ((0 : Fin m → ℤ) i).toNat) = fun _ => 0 := by
    funext i; simp [GlobalTheory.RSnmUnf.padNat]
  have h2 : (fun i : Fin m => ((0 : Fin m → ℤ) i).toNat) = fun _ => 0 := by funext i; simp
  rw [GlobalTheory.RSnmUnf.rsTermNM, if_pos ⟨fun i => le_rfl, antitone_const⟩, h1, h2]
  simp [GlobalTheory.JSW.schurAt, GlobalTheory.JSW.schur_zero]

set_option synthInstance.maxHeartbeats 400000 in
theorem unfolded_cells_eq : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))),
    (∀ w ∉ S, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w (x * y))) : ℂ) = 1) ↔ x ∈ Ov E w) →
    ∀ (π : CuspSub E (m + r + 1 + 1)) (π' : CuspSub E (m + 1)), π.IsUnitary → π'.IsUnitary →
    ∀ (α : HeightOneSpectrum (𝓞 E) → Fin (m + r + 1 + 1) → ℂˣ) (β : HeightOneSpectrum (𝓞 E) → Fin (m + 1) → ℂˣ)
      (φ : GA E (m + r + 1 + 1) → ℂ) (φ' : GA E (m + 1) → ℂ) (κ : GA E (m + 1) → ℝ),
      φ ∈ GlobalTheory.JSW.mspanR π → φ' ∈ GlobalTheory.JSW.mspanR π' →
      (∃ U : Subgroup (GL (Fin (m + r + 1 + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + r + 1 + 1)) (Af E))) ∧
        ∀ u ∈ U, ∀ g, φ (g * finGL E (m + r + 1 + 1) u) = φ g) →
      (∀ w ∉ S, ∀ k ∈ KGL w (n := (m + r + 1 + 1)), ∀ g,
        φ (g * finGL E (m + r + 1 + 1) (locGL E (m + r + 1 + 1) w k)) = φ g) →
      (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧
        ∀ u ∈ U, ∀ g, φ' (g * finGL E (m + 1) u) = φ' g) →
      (∀ w ∉ S, ∀ k ∈ KGL w (n := (m + 1)), ∀ g, φ' (g * finGL E (m + 1) (locGL E (m + 1) w k)) = φ' g) →
      (∀ (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
        ∀ l : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℕ), (∀ w ∈ l.support, w ∉ S) →
        ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S,
          GlobalTheory.JSW.whit φ' (h * GlobalTheory.JSW.tl ϖ l) =
            (∏ w ∈ l.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (β w i : ℂ)) (l w)) * GlobalTheory.JSW.whit φ' h) →
      (∀ (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
        ∀ l : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℕ), (∀ w ∈ l.support, w ∉ S) →
        ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S,
          GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) (h * GlobalTheory.JSW.tl ϖ l)) =
            (∏ w ∈ l.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (α w i : ℂ)) (GlobalTheory.RSnmUnf.padNat (l w))) *
              GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h)) →
      (∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h) = (κ h : ℂ) * GlobalTheory.JSW.whit φ' h) →
      Continuous κ → (∀ h, 0 ≤ κ h) → (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ h, κ (u * h) = κ h) →
      (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, κ h ≠ 0 →
        ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * h ∈ C) →
      (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧
        ∀ u ∈ U, ∀ h, κ (h * finGL E (m + 1) u) = κ h) →
      (∃ h₀ ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, 0 < κ h₀ ∧ GlobalTheory.JSW.whit φ' h₀ ≠ 0) →
    ∃ F ∈ GroundTheory.Automorphic.GJMatrix.schwartzBruhatPi (K := E) (ι := Fin (m + 1)),
    ∀ (μ : Measure (GA E (m + 1))) [μ.IsHaarMeasure] (𝓕₀ : Set (GA E (m + 1))),
      IsFundamentalDomain (GlobalTheory.CellDec.NE E (m + 1)) 𝓕₀ μ →
      ∃ f t : GA E (m + 1) → ℝ, Measurable f ∧ Measurable t ∧ (∀ g, 0 ≤ f g) ∧ IntegrableOn f 𝓕₀ μ ∧
        0 < ∫ g in 𝓕₀, f g ∂μ ∧ (∃ R : ℝ, ∀ g, f g ≠ 0 → |t g| ≤ R) ∧
        ∀ x : ℝ, 1 < x →
          GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ S} => Ideal.absNorm w.1.asIdeal)
            (fun w i => (α w.1 i : ℂ)) x ≠ ⊤ →
          GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ S} => Ideal.absNorm w.1.asIdeal)
            (fun w i => (β w.1 i : ℂ)) x ≠ ⊤ →
          (∫⁻ h in 𝓕₀, ‖GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h)‖ₑ ^ 2 * ‖GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow h)‖ₑ * ENNReal.ofReal (GlobalTheory.RSnm.detAbs h ^ (x - ((r : ℝ) + 1))) ∂μ ≠ ⊤) ∧ (∫⁻ h in 𝓕₀, ‖GlobalTheory.JSW.whit φ' h‖ₑ ^ 2 * ‖GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow h)‖ₑ * ENNReal.ofReal (GlobalTheory.RSnm.detAbs h ^ x) ∂μ ≠ ⊤) ∧
          ∫ g in 𝓕₀, GlobalTheory.RSnmUnf.uIntNM (by omega : m + 1 ≤ m + r + 1 + 1) F φ φ' x g ∂μ =
            (∫ g in 𝓕₀, (f g : ℂ) * Complex.exp (x * t g) ∂μ) *
              ∑' l : {w : HeightOneSpectrum (𝓞 E) // w ∉ S} →₀ (Fin (m + 1) → ℤ),
                l.prod fun w v => GlobalTheory.RSnmUnf.rsTermNM (Ideal.absNorm w.1.asIdeal) (fun i => (α w.1 i : ℂ))
                  (fun i => (β w.1 i : ℂ)) x v := by
  intro E _ _ _ m r S hψ π π' hπ hπ' α β φ φ' κ hφ hφ' hU hK hU' hK' hshβ hshα hmatch hκc hκ0 hκN hκC hκU h₀
  classical
  have hϖex : ∀ w : HeightOneSpectrum (𝓞 E), ∃ ϖ : (w.adicCompletion E)ˣ, IsUnifV E w (ϖ : w.adicCompletion E) := by
    intro w
    obtain ⟨ϖ, hϖ⟩ : ∃ ϖ, IsUnifV E w ϖ := ⟨_, Formalism.L2.Host.unif_spec w⟩
    refine ⟨Units.mk0 ϖ fun h => ?_, hϖ⟩
    rw [IsUnifV, h] at hϖ
    simp at hϖ
  choose ϖ hϖ using hϖex
  have hreg : ∀ {a : ℕ} {ρ : CuspSub E a}, ρ.IsUnitary → ∀ F ∈ GlobalTheory.JSW.mspanR ρ, GlobalTheory.JSW.IsBCC F := by
    intro a ρ hρ F hF
    obtain ⟨ψ, rfl, h⟩ := GlobalTheory.JSW.mspanR_words GlobalTheory.CuspOrth.cuspFormsBounded hρ F hF
    have h0 := (h []).2
    rwa [GlobalTheory.JSW.word_nil] at h0
  have hc := hreg hπ φ hφ
  have hc' := hreg hπ' φ' hφ'
  have hW : ∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + r + 1 + 1)), ∀ g, GlobalTheory.JSW.whit φ (u * g) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ g :=
    fun u hu g => GlobalTheory.JSW.WhitModel.whit_mul hc.cont (fun γ g => hc.left γ g) hu g
  have hW' : ∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, GlobalTheory.JSW.whit φ' (u * g) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ' g :=
    fun u hu g => GlobalTheory.JSW.WhitModel.whit_mul hc'.cont (fun γ g => hc'.left γ g) hu g
  have hWc := GlobalTheory.JSW.WhitCont.continuous_whit E _ φ hc.cont hc.bdd
  have hWc' := GlobalTheory.JSW.WhitCont.continuous_whit E _ φ' hc'.cont hc'.bdd
  have hRI : ∀ {a : ℕ} (Φ : GA E a → ℂ), (∃ U : Subgroup (GL (Fin a) (Af E)), IsOpen (U : Set (GL (Fin a) (Af E))) ∧
        ∀ u ∈ U, ∀ g, Φ (g * finGL E a u) = Φ g) →
      (∀ w ∉ S, ∀ k ∈ KGL w (n := a), ∀ g, Φ (g * finGL E a (locGL E a w k)) = Φ g) →
      ∀ k : GL (Fin a) (Af E), (∀ v, Matrix.GeneralLinearGroup.map (pLoc E v) k ∈ KGL v (n := a)) →
      (∀ v ∈ S, Matrix.GeneralLinearGroup.map (pLoc E v) k = 1) → ∀ g, GlobalTheory.JSW.whit Φ (g * finGL E a k) = GlobalTheory.JSW.whit Φ g := by
    intro a Φ ⟨U, hUo, hUi⟩ hKi k hk1 hk2 g
    let stab : Subgroup (GL (Fin a) (Af E)) :=
      { carrier := {k | ∀ g, Φ (g * finGL E a k) = Φ g}
        mul_mem' := fun {a' c} ha hc g => by rw [map_mul, ← mul_assoc, hc, ha]
        one_mem' := fun g => by rw [map_one, mul_one]
        inv_mem' := fun {a'} ha g => by
          rw [← ha (g * finGL E a a'⁻¹), mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one] }
    let V : Subgroup (GL (Fin a) (Af E)) := U ⊔ Subgroup.closure
      {k | ∃ w ∉ S, ∃ k' ∈ KGL w (n := a), locGL E a w k' = k}
    have hVle : V ≤ stab := by
      refine sup_le (fun k hk => hUi k hk) (Subgroup.closure_le _ |>.2 ?_)
      rintro _ ⟨w, hw, k, hk, rfl⟩
      exact hKi w hw k hk
    have hVo : IsOpen (V : Set (GL (Fin a) (Af E))) := Subgroup.isOpen_mono (le_sup_left : U ≤ V) hUo
    have hVK : ∀ w ∉ S, ∀ k ∈ KGL w (n := a), locGL E a w k ∈ V := fun w hw k hk =>
      (le_sup_right : Subgroup.closure _ ≤ V) (Subgroup.subset_closure ⟨w, hw, k, hk, rfl⟩)
    obtain ⟨J, -, -, hJV⟩ := GlobalTheory.RSLocalPart.exists_levelAt_subset S V hVo hVK
    have hkJ : k ∈ GlobalTheory.RSLocalPart.levelAt a S J := by
      refine ⟨hk1, fun v hv i j => ?_⟩
      have e1 := congrArg (fun M : GL (Fin a) (v.adicCompletion E) => (M : Matrix (Fin a) (Fin a) (v.adicCompletion E)) i j) (hk2 v hv)
      have e2 : ((k.val - 1) i j) v = 0 := by
        have e1' : pLoc E v (k.val i j) = (1 : Matrix (Fin a) (Fin a) (v.adicCompletion E)) i j := by simpa using e1
        change pLoc E v (k.val i j - (1 : Matrix (Fin a) (Fin a) (Af E)) i j) = 0
        rw [map_sub, e1', Matrix.one_apply, Matrix.one_apply]
        split_ifs <;> simp
      rw [e2, map_zero]
      exact zero_le'
    have e : (fun z => Φ (z * finGL E a k)) = Φ := funext fun z => hVle (hJV hkJ) z
    rw [GlobalTheory.JSW.whit_mul_right, e]
  have hWK := hRI φ hU hK
  have hWK' := hRI φ' hU' hK'
  obtain ⟨h₀, hh₀, hκ₀, hW₀⟩ := h₀
  have hint : ∀ w ∉ S, ∀ j, pLoc E w (pFin E (GlobalTheory.ZEul.lastRow h₀ j)) ∈ w.adicCompletionIntegers E := by
    intro w hw j
    have e1 := congrArg (fun M : GL (Fin (m + 1)) (w.adicCompletion E) => (M : Matrix (Fin (m + 1)) (Fin (m + 1)) (w.adicCompletion E)) (Fin.last m) j) (hh₀ w hw)
    have e2 : pLoc E w (pFin E (GlobalTheory.ZEul.lastRow h₀ j)) = (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) (w.adicCompletion E)) (Fin.last m) j := by
      simpa [GlobalTheory.ZEul.lastRow] using e1
    rw [e2, Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  obtain ⟨F, hFSB, hFc, hFr, hFpos, hFsc⟩ := GlobalTheory.FourierCell.exists_fourier_gauss_lattice E m S (GlobalTheory.ZEul.lastRow h₀) hint
  refine ⟨F, hFSB, ?_⟩
  intro μ _ 𝓕₀ h𝓕
  obtain ⟨f, t, hfm, htm, hf0, hfi, hfpos, hR, hfC, hfu, hdet, hDA, hDB⟩ := GlobalTheory.T.rankinSelberg_cell_integral_finite_part_nonneg E m r S φ φ' κ F hWc hWc' hW hW'
    hWK hWK' hmatch hκc hκ0 hκC ⟨h₀, hh₀, hκ₀, hW₀, hFpos⟩ hFc hFr μ 𝓕₀ h𝓕
  refine ⟨f, t, hfm, htm, hf0, hfi, hfpos, hR, ?_⟩
  intro x hx hdα hdβ

  have ev := GlobalTheory.CellEvalNM.uIntNM_cell_eval E m r S hψ ϖ hϖ α β φ φ' F hW hW' hWK hWK' (hshβ ϖ hϖ) (hshα ϖ hϖ)
    (fun a ha y hy => hFsc ϖ hϖ a ha y hy) x
  obtain ⟨hWbc, hFlc, hmeas, hinv, hbd⟩ := GlobalTheory.RSnmUnfProps.uIntNM_props E m r S φ φ' F hWc hWc' hW hW' hFc
  have hC0 : MeasurableSet (GlobalTheory.CellDec.C0 E (m + 1) S) := (GlobalTheory.CellDec.isOpen_adelicUnipotentTimesIntegralOutsideSet E (m + 1) S).measurableSet
  set I : ℂ := ∫ g in 𝓕₀, (f g : ℂ) * Complex.exp (x * t g) ∂μ with hI
  have hIC : ∫ g in 𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) S, (f g : ℂ) * Complex.exp (x * t g) ∂μ = I := by
    rw [hI, Set.inter_comm, ← Measure.restrict_restrict hC0, ← integral_indicator hC0]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    by_cases hg : g ∈ GlobalTheory.CellDec.C0 E (m + 1) S
    · rw [Set.indicator_of_mem hg]
    · rw [Set.indicator_of_notMem hg]; simp [hfC g hg]
  have hs : NullMeasurableSet (𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) S) μ :=
    h𝓕.nullMeasurableSet.inter hC0.nullMeasurableSet

  have hlinD : ∀ (D : GA E (m + 1) → ℝ≥0∞) (c : GlobalTheory.CellDec.abelian₂ E (m + 1) S → ℝ≥0∞), Measurable D →
      (∀ u ∈ GlobalTheory.CellDec.NA E (m + 1), ∀ g, D (u * g) = D g) →
      (∀ g ∈ GlobalTheory.CellDec.C0 E (m + 1) S, ∀ l, ENNReal.ofReal (GlobalTheory.CellDec.dinv (m + 1) l.1) *
        D (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) = c l * D g) →
      ∫⁻ g in 𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) S, D g ∂μ ≠ ⊤ → (∑' l, c l) ≠ ⊤ → ∫⁻ g in 𝓕₀, D g ∂μ ≠ ⊤ := by
    intro D c hDm hDi hDc hD hc
    rw [GlobalTheory.CellDec.cell_lintegral μ S ϖ hϖ 𝓕₀ h𝓕 D hDm hDi]
    have : ∀ l : GlobalTheory.CellDec.abelian₂ E (m + 1) S, ENNReal.ofReal (GlobalTheory.CellDec.dinv (m + 1) l.1) *
        ∫⁻ g in 𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) S, D (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) ∂μ =
        c l * ∫⁻ g in 𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) S, D g ∂μ := by
      intro l
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      rw [← lintegral_const_mul'' _ hDm.aemeasurable]
      exact lintegral_congr_ae ((ae_restrict_mem₀ hs).mono fun g hg => hDc g hg.2 l)
    simp_rw [this, ENNReal.tsum_mul_right]
    exact ENNReal.mul_ne_top hc hD
  have hen : ∀ {a b : ℂ}, ‖a‖ = ‖b‖ → ‖a‖ₑ = ‖b‖ₑ := fun h => by
    rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, h]
  have hmD : ∀ s : ℝ, Measurable fun g : GA E (m + 1) =>
      ‖GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) g)‖ₑ ^ 2 *
        ‖GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow g)‖ₑ * ENNReal.ofReal (GlobalTheory.RSnm.detAbs g ^ s) :=
    fun s => ((hWbc.measurable.enorm.pow_const 2).mul hFlc.measurable.enorm).mul
      (ENNReal.measurable_ofReal.comp (GlobalTheory.RSnm.continuous_detAbs.measurable.pow_const s))
  have hmD' : ∀ s : ℝ, Measurable fun g : GA E (m + 1) =>
      ‖GlobalTheory.JSW.whit φ' g‖ₑ ^ 2 *
        ‖GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow g)‖ₑ * ENNReal.ofReal (GlobalTheory.RSnm.detAbs g ^ s) :=
    fun s => ((hWc'.measurable.enorm.pow_const 2).mul hFlc.measurable.enorm).mul
      (ENNReal.measurable_ofReal.comp (GlobalTheory.RSnm.continuous_detAbs.measurable.pow_const s))
  have LA := hlinD _ _ (hmD _) (fun u hu g => by
      obtain ⟨h1, -, h3, h4, -⟩ := hinv u hu g
      rw [hen h1, h3, h4]) (fun g hg l => (ev g hg l).2.1) (hDA x)
    (GlobalTheory.RSCellEul.tsum_padTerm_ne_top E m (m + r + 1 + 1) S (by omega) (fun w i => (α w i : ℂ)) x hdα)
  have LB := hlinD _ _ (hmD' _) (fun u hu g => by
      obtain ⟨-, h2, h3, h4, -⟩ := hinv u hu g
      rw [hen h2, h3, h4]) (fun g hg l => (ev g hg l).2.2) (hDB π' hπ' hφ' hFSB x hx)
    (GlobalTheory.RSCellEul.tsum_padTerm_ne_top E m (m + 1) S le_rfl (fun w i => (β w i : ℂ)) x hdβ)
  refine ⟨LA, LB, ?_⟩

  have hDtr : ∀ (a b : ℂ) (s : ℝ) (g : GA E (m + 1)), (‖a‖ₑ ^ 2 * ‖b‖ₑ * ENNReal.ofReal (GlobalTheory.RSnm.detAbs g ^ s)).toReal =
      ‖a‖ ^ 2 * ‖b‖ * GlobalTheory.RSnm.detAbs g ^ s := by
    intro a b s g
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow, toReal_enorm, toReal_enorm,
      ENNReal.toReal_ofReal (Real.rpow_nonneg (GlobalTheory.RSnm.detAbs_pos g).le _)]
  have iA := integrable_toReal_of_lintegral_ne_top (hmD (x - ((r : ℝ) + 1))).aemeasurable LA
  have iB := integrable_toReal_of_lintegral_ne_top (hmD' x).aemeasurable LB
  have i12 : Integrable (GlobalTheory.RSnmUnf.uIntNM (by omega : m + 1 ≤ m + r + 1 + 1) F φ φ' x) (μ.restrict 𝓕₀) :=
    Integrable.mono' ((iA.add iB).div_const 2) (hmeas x).aestronglyMeasurable
      (Filter.Eventually.of_forall fun g => by
        simp only [Pi.add_apply, hDtr]
        exact hbd x g)
  have hl : ∀ l : GlobalTheory.CellDec.abelian₂ E (m + 1) S, (GlobalTheory.CellDec.dinv (m + 1) l.1 : ℂ) *
      ∫ g in 𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) S,
        GlobalTheory.RSnmUnf.uIntNM (by omega : m + 1 ≤ m + r + 1 + 1) F φ φ' x (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) ∂μ =
      (l.1.prod fun w v => GlobalTheory.RSnmUnf.rsTermNM (Ideal.absNorm w.asIdeal) (fun i => (α w i : ℂ))
        (fun i => (β w i : ℂ)) x v) * I := by
    intro l
    rw [← integral_const_mul, ← hIC, ← integral_const_mul]
    refine integral_congr_ae ((ae_restrict_mem₀ hs).mono fun g hg => ?_)
    dsimp only
    rw [(ev g hg.2 l).1, hfu g hg.2, hdet, mul_assoc]
  have h := (GlobalTheory.CellDec.cell_integral μ S ϖ hϖ 𝓕₀ h𝓕 _ (hmeas x) i12 (fun u hu g => (hinv u hu g).2.2.2.2 x)).2
  simp_rw [hl] at h
  rw [← h.tsum_eq, tsum_mul_right, mul_comm]
  obtain ⟨e, he⟩ := GlobalTheory.finsupp_vanishing_on_equiv_compl_prod S (m + 1)
  congr 1
  rw [← e.tsum_eq]
  exact tsum_congr fun l => (he ℂ (fun w v => GlobalTheory.RSnmUnf.rsTermNM (Ideal.absNorm w.asIdeal) (fun i => (α w i : ℂ))
    (fun i => (β w i : ℂ)) x v) (fun i => rsTermNM_zero _ _ _ _) l).symm

end GlobalTheory.RSnmCells
end
end
