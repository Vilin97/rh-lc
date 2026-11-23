module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.LefRho
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.SymZeroCommFrame
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.AdjugateDifferentiability.DifferentiableMt
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.EigLocal
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
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.ConjugateTransposeDerivatives.CfSandwich
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.ConjugateTransposeDerivatives.HasDerivAtConjTranspose
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.ConjugateTransposeDerivatives.TraceSingleMulSingle
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.ContractionDerivatives.ContractLeftMap
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.ContractionDerivatives.DerTop
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.ContractionDerivatives.ToLinSmulOne
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.CxDataOf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.DeterminantPowerSmoothness.GtCharZero
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.HaarGramPositivity.EpowMulOfKill
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.HaarGramPositivity.SwapLawsOf
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.InverseLineDerivatives.RmAnti
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.EigOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContDiffOnChartInv
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Tactic.TypeStar

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.AdjugateDifferentiability.EpowCongr

section

@[expose] public section

noncomputable section

open Matrix

namespace PositivityTheory.RgBcC.Cxf

open PositivityTheory.RgTw (Mat)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem isOpen_GLs : IsOpen (GLs n) := isOpen_ne_fun continuous_id.matrix_det continuous_const

theorem rd_congr {U : Set (Mat n)} (hU : IsOpen U) {f f' : Mat n → V} (h : ∀ x ∈ U, f x = f' x) (X : Mat n) :
    ∀ x ∈ U, Rd X f x = Rd X f' x := by
  intro x hx
  unfold Rd
  rw [Filter.EventuallyEq.fderiv_eq (Filter.eventuallyEq_of_mem (hU.mem_nhds hx) h)]

theorem eu_congr {U : Set (Mat n)} (hU : IsOpen U) {f f' : Mat n → V} (h : ∀ x ∈ U, f x = f' x) (s : Bool) (a b : Fin n) :
    ∀ x ∈ U, Eu s a b f x = Eu s a b f' x := by
  intro x hx
  simp only [Eu, Pi.smul_apply, Pi.add_apply]
  rw [rd_congr hU h (single a b 1) x hx, rd_congr hU h (single a b Complex.I) x hx]

theorem epow_congr {U : Set (Mat n)} (hU : IsOpen U) {f f' : Mat n → V} (h : ∀ x ∈ U, f x = f' x) (s : Bool) :
    ∀ (m : ℕ) (a b : Fin n), ∀ x ∈ U, Epow s m a b f x = Epow s m a b f' x := by
  intro m
  induction m with
  | zero =>
    intro a b x hx
    simp only [Epow.eq_1]
    by_cases hab : a = b <;> simp [hab, h x hx]
  | succ m ih =>
    intro a b x hx
    simp only [Epow.eq_2]
    rw [Finset.sum_apply, Finset.sum_apply]
    exact Finset.sum_congr rfl fun c _ => eu_congr hU (fun y hy => ih c b y hy) s a c x hx

theorem gel_congr {U : Set (Mat n)} (hU : IsOpen U) {f f' : Mat n → V} (h : ∀ x ∈ U, f x = f' x) (s : Bool) (m : ℕ) :
    ∀ x ∈ U, gel s m f x = gel s m f' x := by
  intro x hx
  simp only [gel]
  rw [Finset.sum_apply, Finset.sum_apply]
  exact Finset.sum_congr rfl fun a _ => epow_congr hU h s m a a x hx

end PositivityTheory.RgBcC.Cxf

namespace PositivityTheory.RgBcC

open Cxf in
theorem eigLocal : EigLocal := by
  intro n χ V _ _ f f' h hf s m g hg
  rw [← h g hg, ← gel_congr isOpen_GLs h s m g hg]
  exact hf s m g hg

end PositivityTheory.RgBcC
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.KroneckerSmoothness.FrameInvMulSymZero

section

@[expose] public section

noncomputable section

open Matrix
open scoped Kronecker ContDiff ComplexConjugate

namespace PositivityTheory.RgBcC.Cxh

open PositivityTheory.RgTw (Mat hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {lam : Fin n → ℤ}

theorem frame_inv_mul_sym_zero (hu : IsUnit (sqQ lam)) (hG : GamMul) (x : Mat n) :
    lefFr n lam x⁻¹ * lefS n lam 0 =
      cjL lam (gamM (0 : Matrix (Md n) (Md n) ℂ) ⊗ₖ rhoW lam x⁻¹) := by
  have hmul : ∀ A B : Matrix (Ix n lam) (Ix n lam) ℂ, cjL lam A * cjL lam B = cjL lam (A * B) := by
    intro A B
    have hc : clm lam (A * B) = clm lam A * clm lam B := map_mul Matrix.toEuclideanCLM A B
    have hi : Ring.inverse (sqQ lam) * sqQ lam = 1 := Ring.inverse_mul_cancel _ hu
    change sqQ lam * (clm lam A * Ring.inverse (sqQ lam)) * (sqQ lam * (clm lam B * Ring.inverse (sqQ lam))) =
      sqQ lam * (clm lam (A * B) * Ring.inverse (sqQ lam))
    rw [hc]
    simp only [mul_assoc]
    rw [← mul_assoc (Ring.inverse (sqQ lam)) (sqQ lam), hi, one_mul]
  have h0 : lefS n lam 0 = cjL lam (gamM (0 : Matrix (Md n) (Md n) ℂ) ⊗ₖ (1 : Matrix (Jd n lam × Jd n lam) (Jd n lam × Jd n lam) ℂ)) := by
    simp only [lefS, Complex.ofReal_zero, zero_smul]
  rw [h0, lefFr, fr0, hmul, ← Matrix.mul_kronecker_mul, ← (hG n).2, mul_zero, Matrix.mul_one]

theorem clm_entry (M : Matrix (Ix n lam) (Ix n lam) ℂ) (u : EV n lam) (r : Ix n lam) :
    (clm lam M u) r = ∑ c, M r c * u c := by
  have h : (clm lam M u).ofLp = M *ᵥ u.ofLp := by
    rw [clm, ← ContinuousLinearMap.coe_coe, Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
    rfl
  change (clm lam M u).ofLp r = _
  rw [h]
  rfl

theorem clm_apply' (M : Matrix (Ix n lam) (Ix n lam) ℂ) (u : EV n lam) :
    clm lam M u = ∑ i : Ix n lam × Ix n lam, (M i.1 i.2 * u i.2) • EuclideanSpace.single i.1 (1 : ℂ) := by
  rw [Fintype.sum_prod_type (f := fun i : Ix n lam × Ix n lam => (M i.1 i.2 * u i.2) • EuclideanSpace.single i.1 (1 : ℂ))]
  ext r
  rw [clm_entry]
  simp [Finset.sum_apply, Pi.single_apply]

theorem mem_GLs_inv' {x : Mat n} (hx : x ∈ GLs n) : x⁻¹ ∈ GLs n := by
  simp only [GLs, Set.mem_ofPred_eq] at hx ⊢
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  exact inv_ne_zero hx

theorem mem_GLs_conjInv {x : Mat n} (hx : x ∈ GLs n) : (x⁻¹)ᴴ ∈ GLs n := by
  have h := mem_GLs_inv' hx
  simp only [GLs, Set.mem_ofPred_eq] at h ⊢
  rw [Matrix.det_conjTranspose]
  exact star_ne_zero.2 h

theorem contDiff_conjT : ContDiff ℝ ∞ (fun y : Mat n => yᴴ) := by
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  exact Complex.conjCLE.contDiff.comp ((contDiff_apply ℝ (fun _ => ℂ) i).comp (contDiff_apply ℝ (fun _ => (Fin n → ℂ)) j))

theorem contDiffOn_theta : ContDiffOn ℝ ∞ (fun y : Mat n => (y⁻¹)ᴴ) (GLs n) :=
  contDiff_conjT.comp_contDiffOn GlobalTheory.CompanionTheory.MatInv.contDiffOn_inv

theorem contDiffOn_entry {J : Type} [Fintype J] [DecidableEq J] {f : Mat n → Matrix J J ℂ} (hf : ContDiffOn ℝ ∞ f (GLs n))
    (a b : J) : ContDiffOn ℝ ∞ (fun x => (f x * (1 : Matrix J J ℂ) : Matrix J J ℂ) a b) (GLs n) := by
  simp only [Matrix.mul_one]
  exact ((contDiff_apply ℝ (fun _ => ℂ) b).comp (contDiff_apply ℝ (fun _ => (J → ℂ)) a)).comp_contDiffOn hf

end PositivityTheory.RgBcC.Cxh

namespace PositivityTheory.RgBcC

open Cxh
open PositivityTheory.RgTw (Mat hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace


theorem eigOf : EigOf := by
  intro hAvg hG hRm hHol hAnti hProd hLoc n lam hlam w
  obtain ⟨hu, -, -, -, -⟩ := hAvg n lam
  obtain ⟨hR1, hRmul, hRc⟩ := hRm n lam
  let G0 : Matrix (Finset (Md n)) (Finset (Md n)) ℂ := gamM (0 : Matrix (Md n) (Md n) ℂ)
  let hh : Ix n lam × Ix n lam → Mat n → ℂ := fun i x =>
    (Rm lam x * 1 : Matrix (Jd n lam) (Jd n lam) ℂ) i.2.2.1 i.1.2.1
  let aa : Ix n lam × Ix n lam → Mat n → ℂ := fun i x =>
    (Rm lam x⁻¹ᴴ * 1 : Matrix (Jd n lam) (Jd n lam) ℂ) i.2.2.2 i.1.2.2
  let vv : Ix n lam × Ix n lam → EV n lam := fun i =>
    (G0 i.1.1 i.2.1 * (Ring.inverse (sqQ lam) w) i.2) • sqQ lam (EuclideanSpace.single i.1 (1 : ℂ))
  have hE := hProd n (infOf lam) (Ix n lam × Ix n lam) (EV n lam) hh aa vv
    (fun i => contDiffOn_entry (f := Rm lam) hRc _ _)
    (fun i => contDiffOn_entry (f := fun x => Rm lam x⁻¹ᴴ)
      (hRc.comp contDiffOn_theta (fun x hx => mem_GLs_conjInv hx)) _ _)
    (fun i g hg => hHol n lam hlam 1 _ _ g hg)
    (fun i g hg => hAnti n lam hlam 1 _ _ g hg)
  refine hLoc n (infOf lam) (EV n lam) _ _ ?_ hE
  intro x hx
  have hdx : IsUnit (det x) := isUnit_iff_ne_zero.2 hx
  have hdx' : IsUnit (det x⁻¹) := isUnit_iff_ne_zero.2 (mem_GLs_inv' hx)
  have hinv : (Rm lam x⁻¹)⁻¹ = Rm lam x := by
    apply Matrix.inv_eq_left_inv
    rw [← hRmul x x⁻¹ hdx hdx', Matrix.mul_nonsing_inv x hdx, hR1]
  symm
  rw [← ContinuousLinearMap.mul_apply, frame_inv_mul_sym_zero hu hG]
  change (sqQ lam * (clm lam (gamM (0 : Matrix (Md n) (Md n) ℂ) ⊗ₖ rhoW lam x⁻¹) * Ring.inverse (sqQ lam))) w = _

  rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, clm_apply', map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul]
  simp only [vv, smul_smul]
  congr 1
  simp only [hh, aa, G0, rhoW, Matrix.kroneckerMap_apply, Matrix.transpose_apply, Matrix.mul_one, hinv]
  ring
end RgBcC
end PositivityTheory
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.KroneckerSmoothness.SumKronLeft

section

@[expose] public section

noncomputable section

open Matrix
open scoped Kronecker ContDiff ComplexConjugate

namespace PositivityTheory.RgBcC.Cxh

open PositivityTheory.RgTw (Mat hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {lam : Fin n → ℤ}

def cjC (lam : Fin n → ℤ) : Matrix (Ix n lam) (Ix n lam) ℂ →L[ℝ] (EV n lam →L[ℂ] EV n lam) :=
  LinearMap.toContinuousLinearMap ((cjL lam).restrictScalars ℝ)

theorem fderiv_lefFr (hd : DifferentiableAt ℝ (fr0 lam) (1 : Mat n)) (X : Mat n) :
    fderiv ℝ (lefFr n lam) 1 X = cjL lam (fderiv ℝ (fr0 lam) 1 X) := by
  have h : lefFr n lam = (cjC lam) ∘ fr0 lam := rfl
  have h2 := ((cjC lam).hasFDerivAt.comp (1 : Mat n) hd.hasFDerivAt).fderiv
  rw [h]
  exact congrFun (congrArg DFunLike.coe h2) X

theorem sum_kron_left {ι κ μ : Type*} [Fintype κ] [Fintype μ] (s : Finset ι) (A : ι → Matrix κ κ ℂ)
    (B : Matrix μ μ ℂ) : (∑ i ∈ s, A i) ⊗ₖ B = ∑ i ∈ s, A i ⊗ₖ B := by
  ext a b
  simp [kroneckerMap_apply, Matrix.sum_apply, Finset.sum_mul]

theorem kron_neg' {κ μ : Type*} (A : Matrix κ κ ℂ) (B : Matrix μ μ ℂ) : A ⊗ₖ (-B) = -(A ⊗ₖ B) := by
  ext a b; simp [kroneckerMap_apply]

theorem zero_kron {κ μ : Type*} (B : Matrix μ μ ℂ) : (0 : Matrix κ κ ℂ) ⊗ₖ B = 0 := by
  ext a b; simp [kroneckerMap_apply]

theorem hb_eq (p : Fin n × Fin n) : hb p = hbM (finProdFinEquiv p) := by
  simp [hbM]

end PositivityTheory.RgBcC.Cxh

namespace PositivityTheory.RgBcC

open Cxh
open PositivityTheory.RgTw (Mat hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace


theorem tdOf : TDOf := by
  intro hAvg hOr hSw hFr hWd n lam
  obtain ⟨hu, -, -, -, -⟩ := hAvg n lam
  obtain ⟨-, -, -, hsw, -⟩ := hSw n lam
  obtain ⟨hd, hfr⟩ := hFr n lam
  have hmul : ∀ A B : Matrix (Ix n lam) (Ix n lam) ℂ, cjL lam A * cjL lam B = cjL lam (A * B) := by
    intro A B
    have hc : clm lam (A * B) = clm lam A * clm lam B := map_mul Matrix.toEuclideanCLM A B
    have hi : Ring.inverse (sqQ lam) * sqQ lam = 1 := Ring.inverse_mul_cancel _ hu
    change sqQ lam * (clm lam A * Ring.inverse (sqQ lam)) * (sqQ lam * (clm lam B * Ring.inverse (sqQ lam))) =
      sqQ lam * (clm lam (A * B) * Ring.inverse (sqQ lam))
    rw [hc]
    simp only [mul_assoc]
    rw [← mul_assoc (Ring.inverse (sqQ lam)) (sqQ lam), hi, one_mul]
  have hherm : ∀ p : Fin n × Fin n, (hb p).IsHermitian := fun p => by
    rw [hb_eq]
    exact (hOr n).2 _
  let C : Fin n × Fin n → Matrix (Finset (Md n)) (Finset (Md n)) ℂ := fun p => creL n (cf n (hb p))
  let G : Fin n × Fin n → Matrix (Finset (Md n)) (Finset (Md n)) ℂ := fun p =>
    fderiv ℝ (fun x : Mat n => gamM (Mt x⁻¹)ᵀ) 1 (hb p)
  let R : Fin n × Fin n → Matrix (Jd n lam × Jd n lam) (Jd n lam × Jd n lam) ℂ := fun p =>
    fderiv ℝ (rhoW lam) 1 (hb p)
  have hw : ∑ p, C p * G p = 0 := hWd n
  have e1 : ∀ p, lefε n lam (hb p) * fderiv ℝ (lefFr n lam) 1 (hb p) =
      cjL lam ((C p * G p) ⊗ₖ (1 : Matrix (Jd n lam × Jd n lam) (Jd n lam × Jd n lam) ℂ) + C p ⊗ₖ R p) := by
    intro p
    rw [fderiv_lefFr hd, hfr _ (hherm p)]
    change cjL lam (C p ⊗ₖ (1 : Matrix (Jd n lam × Jd n lam) (Jd n lam × Jd n lam) ℂ)) *
      cjL lam (G p ⊗ₖ (1 : Matrix (Jd n lam × Jd n lam) (Jd n lam × Jd n lam) ℂ) +
        (1 : Matrix (Finset (Md n)) (Finset (Md n)) ℂ) ⊗ₖ R p) = _
    rw [hmul, Matrix.mul_add, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
    simp only [Matrix.mul_one, Matrix.one_mul]
  have hS : ∑ p, lefε n lam (hb p) * fderiv ℝ (lefFr n lam) 1 (hb p) = cjL lam (∑ p, C p ⊗ₖ R p) := by

    rw [Finset.sum_congr rfl (fun p _ => e1 p), ← map_sum, Finset.sum_add_distrib, ← sum_kron_left, hw,
    zero_kron, zero_add]
  rw [hS]
  change cjL lam ((1 : Matrix (Finset (Md n)) (Finset (Md n)) ℂ) ⊗ₖ swapJ lam) * _ =
    -(_ * cjL lam ((1 : Matrix (Finset (Md n)) (Finset (Md n)) ℂ) ⊗ₖ swapJ lam))
  rw [hmul, hmul, ← map_neg]
  refine congrArg (cjL lam) ?_
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    show swapJ lam * R p = -(R p * swapJ lam) from hsw _ (hherm p), Matrix.one_mul, Matrix.mul_one, kron_neg']
end RgBcC
end PositivityTheory
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.CxDataModel

section

@[expose] public section

namespace PositivityTheory.RgBcC

theorem cxData_model {n : ℕ} (lam : Fin n → ℤ) (hlam : Antitone lam) :
    CxData lam (lefE n lam) (lefFr n lam) (lefε n lam) (lefι n lam) (lefS n lam) (lefΓ n lam) (lefT n lam) := by
  have hsw : SwapLaws := swapLaws_of rmLaws
  have hfd : MatrixFrechetDerivativeAtZero := fr0Der_of gamDer gamMul mtLaws rmLaws
  exact cxData_of cfPair mtLaws gamMul car gamCre gamScal number rmLaws rmChar avg fr0Laws hsw
    (tdOf avg hbOrtho hsw hfd (wedgeDer_of gamDer))
    (eigOf avg gamMul rmLaws rmHol rmAnti eigProd eigLocal) lam hlam

theorem cxEx_model : CxEx := fun n lam hlam =>
  ⟨lefE n lam, lefFr n lam, lefε n lam, lefι n lam, lefS n lam, lefΓ n lam, lefT n lam, cxData_model lam hlam⟩

end PositivityTheory.RgBcC
end
end
