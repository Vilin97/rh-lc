module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.LefRho
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.SymZeroCommFrame
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.SwapLaws
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.FrameZeroApply
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
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.ConjugateTransposeDerivatives.HasDerivAtConjTranspose
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.SymZeroCommFrameMatrix
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic.TypeStar
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.SymZeroCommFrameMatrix
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.TraceGammaZeroEqOne

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.InvCancelRight

section

@[expose] public section

noncomputable section

open Matrix
open scoped Kronecker ContDiff ComplexConjugate

namespace PositivityTheory.RgBcC

open PositivityTheory.RgTw (Mat hb)

variable {n : ℕ} {lam : Fin n → ℤ}

theorem cj_smul_one (hu : IsUnit (sqQ lam)) (c : ℂ) : cjL lam (c • (1 : Matrix (Ix n lam) (Ix n lam) ℂ)) = c • 1 := by
  rw [map_smul, cj_one hu]

theorem herm_conj {x H : Mat n} (hH : H.IsHermitian) : (x * H * xᴴ).IsHermitian := by
  exact Matrix.isHermitian_mul_mul_conjTranspose x hH

theorem herm_conj' {x H : Mat n} (hH : H.IsHermitian) : (xᴴ * H * x).IsHermitian := by
  exact Matrix.isHermitian_conjTranspose_mul_mul x hH

theorem car_f (hu : IsUnit (sqQ lam)) (hB : Car) (hP : CfPair) (H H' : Mat n) (hH : H.IsHermitian)
    (hH' : H'.IsHermitian) : lefε n lam H * lefι n lam H' + lefι n lam H' * lefε n lam H = (H * H').trace • 1 := by
  rw [lefε_apply, lefι_apply, cj_mul hu, cj_mul hu, ← map_add (f := _), ← mul_kronecker_mul, ← mul_kronecker_mul, mul_one,
    ← add_kronecker, add_comm (creL n (cf n H) * annL n (cf n H')), hB n (cf n H) (cf n H')]
  have e : cf n H' ⬝ᵥ cf n H = (H * H').trace := by
    rw [← hP n H H' hH hH', dotProduct]
    exact Finset.sum_congr rfl fun m _ => mul_comm _ _
  rw [e, smul_kronecker, one_kronecker_one, cj_smul_one hu]

theorem inv_cancel_left' {x : Mat n} (hx : x ∈ GLs n) : x⁻¹ * x = 1 :=
  Matrix.nonsing_inv_mul x (isUnit_iff_ne_zero.mpr hx)

theorem inv_cancel_right' {x : Mat n} (hx : x ∈ GLs n) : x * x⁻¹ = 1 :=
  Matrix.mul_nonsing_inv x (isUnit_iff_ne_zero.mpr hx)

theorem frι_f (hu : IsUnit (sqQ lam)) (hC : GamCre) (hM : MtLaws) (x : Mat n) (hx : x ∈ GLs n) (H : Mat n)
    (hH : H.IsHermitian) : lefFr n lam x * lefι n lam H = lefι n lam (x * H * xᴴ) * lefFr n lam x := by
  rw [lefFr_apply, lefι_apply, lefι_apply, cj_mul hu, cj_mul hu, frame_zero_apply, ← mul_kronecker_mul, ← mul_kronecker_mul,
    mul_one, one_mul]
  congr 2
  rw [(hC n _ 0 (cf n (x * H * xᴴ))).2, transpose_transpose, (hM n).2.2.1 x⁻¹ _ (herm_conj hH)]
  have h1 := inv_cancel_left' hx
  have h2 : xᴴ * x⁻¹ᴴ = 1 := by rw [← conjTranspose_mul, h1, conjTranspose_one]
  have key : x⁻¹ * (x * H * xᴴ) * x⁻¹ᴴ = H := by
    calc x⁻¹ * (x * H * xᴴ) * x⁻¹ᴴ = (x⁻¹ * x) * H * (xᴴ * x⁻¹ᴴ) := by simp only [mul_assoc]
      _ = H := by rw [h1, h2, one_mul, mul_one]
  rw [key]

theorem frε_f (hu : IsUnit (sqQ lam)) (hC : GamCre) (hM : MtLaws) (x : Mat n) (hx : x ∈ GLs n) (H : Mat n)
    (hH : H.IsHermitian) : lefε n lam H * lefFr n lam x = lefFr n lam x * lefε n lam (xᴴ * H * x) := by
  rw [lefFr_apply, lefε_apply, lefε_apply, cj_mul hu, cj_mul hu, frame_zero_apply, ← mul_kronecker_mul, ← mul_kronecker_mul,
    mul_one, one_mul]
  congr 2
  rw [(hC n _ (cf n (xᴴ * H * x)) 0).1, (hM n).2.2.2 x⁻¹ _ (herm_conj' hH)]
  have h1 := inv_cancel_right' hx
  have h2 : x⁻¹ᴴ * xᴴ = 1 := by rw [← conjTranspose_mul, h1, conjTranspose_one]
  have key : x⁻¹ᴴ * (xᴴ * H * x) * x⁻¹ = H := by
    calc x⁻¹ᴴ * (xᴴ * H * x) * x⁻¹ = (x⁻¹ᴴ * xᴴ) * H * (x * x⁻¹) := by simp only [mul_assoc]
      _ = H := by rw [h1, h2, one_mul, mul_one]
  rw [key]

end PositivityTheory.RgBcC
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.KronConjTranspose

section

@[expose] public section

noncomputable section

open Matrix
open scoped Kronecker ContDiff ComplexConjugate

namespace PositivityTheory.RgBcC

open PositivityTheory.RgTw (Mat hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {lam : Fin n → ℤ}

theorem kron_conjTranspose' {ι₁ ι₂ : Type*} (A : Matrix ι₁ ι₁ ℂ) (B : Matrix ι₂ ι₂ ℂ) : (A ⊗ₖ B)ᴴ = Aᴴ ⊗ₖ Bᴴ := by
  ext i j; simp [kroneckerMap_apply, conjTranspose_apply, mul_comm]

theorem U_mem (hS : SwapLaws) :
    ((1 : Matrix (Finset (Md n)) (Finset (Md n)) ℂ) ⊗ₖ swapJ lam) ∈ Matrix.unitaryGroup (Ix n lam) ℂ := by
  have h := (hS n lam).2.1
  rw [Matrix.mem_unitaryGroup_iff] at h ⊢
  rw [Matrix.star_eq_conjTranspose, kron_conjTranspose', conjTranspose_one, ← mul_kronecker_mul, mul_one,
    ← Matrix.star_eq_conjTranspose, h, one_kronecker_one]

theorem Tiso_f (hu : IsUnit (sqQ lam)) (hA : Avg) (hS : SwapLaws) (v : EV n lam) : ‖lefT n lam v‖ = ‖v‖ := by
  set U := (1 : Matrix (Finset (Md n)) (Finset (Md n)) ℂ) ⊗ₖ swapJ lam
  have hU := U_mem (lam := lam) hS
  have hc : ∀ k : Matrix.unitaryGroup (Fin n) ℂ, U * fr0 lam k.1 = fr0 lam k.1 * U := by
    intro k
    rw [frame_zero_apply, ← mul_kronecker_mul, ← mul_kronecker_mul, one_mul, mul_one, swap_rhoW_k hu hS k]
  have hcomm := (hA n lam).2.2.2.2 U hU hc
  have e : lefT n lam = clm lam U := by
    rw [lefT_apply, cjL_apply, ← hcomm, mul_assoc, Ring.mul_inverse_cancel _ hu, mul_one]
  rw [e]
  apply ContinuousLinearMap.norm_map_of_mem_unitary
  rw [Unitary.mem_iff]
  have hs : star (clm lam U) = clm lam (star U) := (map_star _ U).symm
  rw [hs, ← clm_mul', ← clm_mul', Unitary.star_mul_self_of_mem hU, Unitary.mul_star_self_of_mem hU, clm_one']
  exact ⟨rfl, rfl⟩

theorem smooth_f (hF : MatrixFrechetDerivativeAtZeroLaws) : ContDiffOn ℝ ∞ (lefFr n lam) (GLs n) := by
  have h := ((cjL lam).restrictScalars ℝ).toContinuousLinearMap.contDiff.comp_contDiffOn (hF n lam).2.2
  exact h

theorem one_f (hu : IsUnit (sqQ lam)) (hF : MatrixFrechetDerivativeAtZeroLaws) : lefFr n lam 1 = 1 := by
  rw [lefFr_apply, (hF n lam).1, cj_one hu]

theorem mul_f (hu : IsUnit (sqQ lam)) (hF : MatrixFrechetDerivativeAtZeroLaws) (x : Mat n) (hx : x ∈ GLs n) (y : Mat n) (hy : y ∈ GLs n) :
    lefFr n lam (x * y) = lefFr n lam x * lefFr n lam y := by
  rw [lefFr_apply, lefFr_apply, lefFr_apply, cj_mul hu,
    (hF n lam).2.1 x y (isUnit_iff_ne_zero.mpr hx) (isUnit_iff_ne_zero.mpr hy)]

theorem lefS_diag (hScal : GamScal) (s : ℝ) : lefS n lam s =
    cjL lam (krL n lam (Matrix.diagonal fun A : Finset (Md n) => (s : ℂ) ^ A.card)) := by
  rw [lefS_apply, hScal n]; rfl

theorem Ssmooth_f (hScal : GamScal) : ContDiff ℝ ∞ (lefS n lam) := by
  have e : lefS n lam = fun s : ℝ => (((cjL lam ∘ₗ krL n lam).restrictScalars ℝ).toContinuousLinearMap)
      (Matrix.diagonal fun A : Finset (Md n) => (s : ℂ) ^ A.card) := by
    funext s; rw [lefS_diag hScal]; rfl
  rw [e]
  refine ContinuousLinearMap.contDiff _ |>.comp ?_
  refine contDiff_pi.2 fun A => contDiff_pi.2 fun B => ?_
  by_cases h : A = B
  · subst h; simp only [diagonal_apply_eq]; exact (Complex.ofRealCLM.contDiff).pow _
  · simp only [diagonal_apply_ne _ h]; exact contDiff_const

theorem hasDerivAt_diagPow (s : ℝ) : HasDerivAt (fun s : ℝ => (Matrix.diagonal fun A : Finset (Md n) => (s : ℂ) ^ A.card))
    (Matrix.diagonal fun A : Finset (Md n) => (A.card : ℂ) * (s : ℂ) ^ (A.card - 1)) s := by
  refine hasDerivAt_pi.2 fun A => hasDerivAt_pi.2 fun B => ?_
  by_cases h : A = B
  · subst h; simp only [diagonal_apply_eq]
    exact (hasDerivAt_pow A.card (s : ℂ)).comp_ofReal
  · simp only [diagonal_apply_ne _ h]; exact hasDerivAt_const _ _

theorem Sder_f (hu : IsUnit (sqQ lam)) (hScal : GamScal) (hN : Number) (s : ℝ) :
    deriv (lefS n lam) s = ∑ p, lefε n lam (hb p) * lefS n lam s * lefι n lam (hb p) := by
  set L := (((cjL lam ∘ₗ krL n lam).restrictScalars ℝ).toContinuousLinearMap)
  have e : lefS n lam = fun s : ℝ => L (Matrix.diagonal fun A : Finset (Md n) => (s : ℂ) ^ A.card) := by
    funext s; rw [lefS_diag hScal]; rfl
  have hd : HasDerivAt (lefS n lam) (L (Matrix.diagonal fun A : Finset (Md n) => (A.card : ℂ) * (s : ℂ) ^ (A.card - 1))) s := by
    rw [e]; exact L.hasFDerivAt.comp_hasDerivAt s (hasDerivAt_diagPow s)
  rw [hd.deriv]
  have hcf : ∀ p : Fin n × Fin n, cf n (hb p) = Pi.single (finProdFinEquiv p) 1 := fun p => by
    have := Cxa.cf_hbM (n := n) (finProdFinEquiv p)
    simpa [hbM] using this
  have key : ∑ p : Fin n × Fin n, creL n (cf n (hb p)) * gamM ((s : ℂ) • (1 : Matrix (Md n) (Md n) ℂ)) *
      annL n (cf n (hb p)) = Matrix.diagonal fun A : Finset (Md n) => (A.card : ℂ) * (s : ℂ) ^ (A.card - 1) := by
    rw [← hN n (s : ℂ)]
    exact Fintype.sum_equiv finProdFinEquiv _ _ (fun p => by rw [hcf p])
  calc L (Matrix.diagonal fun A : Finset (Md n) => (A.card : ℂ) * (s : ℂ) ^ (A.card - 1))
      = cjL lam (krL n lam (∑ p : Fin n × Fin n, creL n (cf n (hb p)) * gamM ((s : ℂ) • (1 : Matrix (Md n) (Md n) ℂ)) *
          annL n (cf n (hb p)))) := by rw [key]; rfl
    _ = ∑ p : Fin n × Fin n, cjL lam (krL n lam (creL n (cf n (hb p)) * gamM ((s : ℂ) • (1 : Matrix (Md n) (Md n) ℂ)) *
          annL n (cf n (hb p)))) := by rw [map_sum, map_sum]
    _ = ∑ p, lefε n lam (hb p) * lefS n lam s * lefι n lam (hb p) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [lefε_apply, lefι_apply, lefS_apply, cj_mul hu, cj_mul hu, ← mul_kronecker_mul, ← mul_kronecker_mul,
          mul_one, mul_one]
        rfl

end PositivityTheory.RgBcC
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.CxDataOf

section

@[expose] public section

noncomputable section

open Matrix
open scoped Kronecker ContDiff ComplexConjugate

namespace PositivityTheory.RgBcC

open PositivityTheory.RgTw (Mat hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem cxData_of (hCP : CfPair) (hM : MtLaws) (hG : GamMul) (hB : Car) (hC : GamCre) (hScal : GamScal) (hN : Number)
    (hRL : RmLaws) (hRC : RmChar) (hA : Avg) (hF : MatrixFrechetDerivativeAtZeroLaws) (hS : SwapLaws)
    (hTD : ∀ (n : ℕ) (lam : Fin n → ℤ), lefT n lam * (∑ p, lefε n lam (hb p) * fderiv ℝ (lefFr n lam) 1 (hb p)) =
      -((∑ p, lefε n lam (hb p) * fderiv ℝ (lefFr n lam) 1 (hb p)) * lefT n lam))
    (hEig : ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ w : EV n lam,
      IsEig (infOf lam) fun x => lefFr n lam x⁻¹ (lefS n lam 0 w))
    {n : ℕ} (lam : Fin n → ℤ) (hlam : Antitone lam) :
    CxData lam (lefE n lam) (lefFr n lam) (lefε n lam) (lefι n lam) (lefS n lam) (lefΓ n lam) (lefT n lam) := by
  have hQ : IsUnit (sqQ lam) := (hA n lam).1
  exact
    { smooth := smooth_f hF
      one := one_f hQ hF
      mul := mul_f hQ hF
      onK := fun k => rfl
      car := car_f hQ hB hCP
      frι := frι_f hQ hC hM
      frε := frε_f hQ hC hM
      Γsq := Γsq_f hQ hG
      Γε := Γε_f hQ hG hC
      Γι := Γι_f hQ hG hC
      ΓFr := fun x _ => ΓFr_f hQ hG x
      ΓT := ΓT_f hQ hG
      Tsq := Tsq_f hQ hS
      Tiso := Tiso_f hQ hA hS
      TK := TK_f hQ hS
      Tε := Tε_f hQ hS
      Tι := Tι_f hQ hS
      TD := hTD n lam
      Ssmooth := Ssmooth_f hScal
      S1 := sym_one_eq_one hQ hG
      Sε := Sε_f hQ hG hC
      Sder := Sder_f hQ hScal hN
      SΓ := SΓ_f hQ hG
      S0sq := S0sq_f hQ hG
      S0Γ := S0Γ_f hQ hG
      sym_zero_comm_frame := fun x _ => sym_zero_comm_frame_matrix hQ hG x
      time_comm_sym_zero := time_comm_sym_zero_matrix hQ hG
      S0θ := S0θ_f hQ hS hG
      eig := hEig n lam hlam
      char := char_f hQ hG hScal hS hRL hRC hlam }

end PositivityTheory.RgBcC
end
end
end
