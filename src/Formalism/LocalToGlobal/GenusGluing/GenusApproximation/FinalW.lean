module

public import Formalism.LocalToGlobal.GenusGluing.GenusApproximation.FactsW
import Formalism.LocalToGlobal.Columns.AdelicLemmas
public import Formalism.LocalToGlobal.GenusGluing.GenusApproximation.GenusApproximationProofs.GlueSmulSame
public import Formalism.LocalToGlobal.GenusGluing.GenusApproximation.GenusApproximationProofs.IdempotentCalculationHolds
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsApprox
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalToGlobal.GenusGluing.GenusApproximation.GenusApproximationProofs.Cayley
import Mathlib.Tactic.TypeStar
public import Formalism.LocalToGlobal.GenusGluing.GenusApproximation.GenusApproximationProofs.EvaluationNeZeroHolds
public import Formalism.LocalToGlobal.GenusGluing.GenusApproximation.LocalAdelicEquivHolds

-- Source module: Formalism.LocalToGlobal.GenusGluing.GenusApproximation.GenusApproximationProofs.ApproximationAdelicHolds

section

@[expose] public section

noncomputable section

namespace Formalism.L2.GenusGluing.Gen

open NumberField IsDedekindDomain Matrix Formalism.L2.Col
open scoped TensorProduct

theorem approximationAdelic_holds : ApproxA := by
  intro F E _ _ _ _ _ D hD u
  obtain ⟨d, hd, hdu⟩ := Formalism.UG.P.levelaf_denom (F := F) (E := E) u
  obtain ⟨b0, t, ht, heq⟩ :=
    Formalism.UG.P.csGlob_approx Formalism.UG.P.integral_adele_approximation_holds (d * D) (mul_ne_zero hd hD) _ hdu
  have hlevel (a : 𝓞 F) : Formalism.UG.P.levelafC E a = iA F E (algebraMap (𝓞 F) E a) := by
    have h := Formalism.UG.P.csGlob_tmul_int (F := F) (E := E) (1 : E) a
    rw [mul_one] at h
    exact h
  rw [hlevel, hlevel] at heq
  have hdE : algebraMap (𝓞 F) E d ≠ 0 := by
    intro h0
    apply hd
    exact (FaithfulSMul.algebraMap_injective (𝓞 F) E) (by rw [h0, map_zero])
  have hinv : iA F E (algebraMap (𝓞 F) E d)⁻¹ * iA F E (algebraMap (𝓞 F) E d) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hdE, map_one]
  refine ⟨(algebraMap (𝓞 F) E d)⁻¹ * algebraMap (𝓞 E) E b0, t, ht, ?_⟩
  calc u = iA F E (algebraMap (𝓞 F) E d)⁻¹ * (iA F E (algebraMap (𝓞 F) E d) * u) := by
        rw [← mul_assoc, hinv, one_mul]
    _ = iA F E (algebraMap (𝓞 F) E d)⁻¹ * (iA F E (algebraMap (𝓞 E) E b0) +
          iA F E (algebraMap (𝓞 F) E d) * iA F E (algebraMap (𝓞 F) E D) * t) := by
        rw [heq, map_mul (algebraMap (𝓞 F) E) d D, map_mul (iA F E)]
    _ = _ := by
        rw [mul_add, ← mul_assoc, ← mul_assoc, hinv, one_mul, map_mul]

theorem unitNearOne_holds : UnitNear := by
  intro F E _ _ _ _ _ _ hc v π hπ n s hs
  classical
  set S := Formalism.L2.Herm.intAf F E with hS
  let st : Matrix (Fin n) (Fin n) S := Matrix.of fun i j => ⟨s i j, hs i j⟩
  let et : S := Formalism.L2.DIV.adS F E (Formalism.L2.DIV.idemAd (fun w => w = v))
  let pt : S := Formalism.L2.DIV.oToS F E (algebraMap (𝓞 F) (𝓞 E) π)
  let Mt : Matrix (Fin n) (Fin n) S := et • (1 - pt • st) + (1 - et) • (1 : Matrix (Fin n) (Fin n) S)
  have hMt : IsUnit Mt := by
    refine Formalism.L2.DIV.isUnit_matrix_of_resS hc Mt fun PP => ?_
    have h1 : Mt.map (Formalism.L2.DIV.resS F PP) = 1 := by
      by_cases hw : Formalism.L2.DIV.underPl F PP = v
      · have he : Formalism.L2.DIV.resS F PP et = 1 :=
          Formalism.L2.DIV.resS_idemAd_pos PP (Formalism.L2.DIV.underPl F PP) rfl hw
        have hp : Formalism.L2.DIV.resS F PP pt = 0 := by
          show Formalism.L2.DIV.resS F PP (Formalism.L2.DIV.oToS F E (algebraMap (𝓞 F) (𝓞 E) π)) = 0
          rw [Formalism.L2.DIV.resS_oToS, Ideal.Quotient.eq_zero_iff_mem]
          have : π ∈ (Formalism.L2.DIV.underPl F PP).asIdeal := by rw [hw]; exact hπ
          exact this
        ext i j
        by_cases hij : i = j <;>
          simp [Mt, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply,
            he, hp, hij]
      · have he : Formalism.L2.DIV.resS F PP et = 0 :=
          Formalism.L2.DIV.resS_idemAd_neg PP (Formalism.L2.DIV.underPl F PP) rfl hw
        ext i j
        by_cases hij : i = j <;>
          simp [Mt, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply,
            he, hij]
    rw [h1, Matrix.det_one]
    exact one_ne_zero
  obtain ⟨U, hU⟩ := hMt
  set e := eAt E v with he_def
  have hee : e * e = e := by
    rw [he_def, show eAt E v = eP E (fun w => w = v) from rfl, (idempotentCalculation_holds F E).2.1]
    exact eP_congr (fun u => and_self_iff)
  have het : ((et : S) : E ⊗[F] Formalism.L2.Herm.Af F) = e := rfl
  have hpt : ((pt : S) : E ⊗[F] Formalism.L2.Herm.Af F) = iA F E (algebraMap (𝓞 F) E π) := by
    show algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) π) ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F) = _
    rw [← IsScalarTower.algebraMap_apply]
    rfl
  let φ := (S.subtype).mapMatrix (m := Fin n)
  refine ⟨((U⁻¹ : (Matrix (Fin n) (Fin n) S)ˣ) : Matrix (Fin n) (Fin n) S).map S.subtype,
    fun i j => (((U⁻¹ : (Matrix (Fin n) (Fin n) S)ˣ) : Matrix (Fin n) (Fin n) S) i j).2, ?_⟩
  have hMR : Mt * ((U⁻¹ : (Matrix (Fin n) (Fin n) S)ˣ) : Matrix (Fin n) (Fin n) S) = 1 := by
    rw [← hU]; exact U.mul_inv
  set_option synthInstance.maxHeartbeats 200000 in
  have hφ : φ Mt = glueM e (1 - iA F E (algebraMap (𝓞 F) E π) • s) := by
    change Mt.map S.subtype = _
    ext i j
    by_cases hij : i = j <;>
      simp [Mt, glueM, st, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply,
        het, hpt, hij]
  have h2 := congrArg φ hMR
  rw [map_mul, map_one, hφ] at h2
  rw [← glue_smul_same hee]
  exact congrArg (fun M => e • M) h2

theorem integralAtInverse_holds : IntAtInv := by
  intro F E _ _ _ _ _ _ hc n v y hy hI
  have hJ : (1 : Matrix (Fin n) (Fin n) E).map (Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F)) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  have hy' : Formalism.UG.cT (Formalism.UG.sigR hc.sig (Formalism.L2.Herm.Af F))
      ((y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *
      ((1 : Matrix (Fin n) (Fin n) E).map (Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F))) *
      ((y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
      ((1 : Matrix (Fin n) (Fin n) E).map (Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F))) := hy
  rw [hJ, Matrix.mul_one] at hy'
  have hinv : (((y⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
      Formalism.UG.cT (Formalism.UG.sigR hc.sig (Formalism.L2.Herm.Af F))
        ((y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :=
    Units.inv_eq_of_mul_eq_one_left hy'
  have hσ : Formalism.UG.sigR hc.sig (Formalism.L2.Herm.Af F) (eAt E v) = eAt E v := sigR_eP hc _
  intro i j
  rw [hinv]
  show eAt E v * Formalism.UG.sigR hc.sig (Formalism.L2.Herm.Af F)
    (((y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) j i) ∈ _
  have hm := (Formalism.L2.DIV.sigS hc ⟨_, hI j i⟩).2
  rw [Formalism.L2.DIV.sigS_coe, map_mul, hσ] at hm
  exact hm

end Formalism.L2.GenusGluing.Gen
end
end
end

-- Source module: Formalism.LocalToGlobal.GenusGluing.GenusApproximation.GenusApproximationProofs.DetAddDiagonalCons

section

@[expose] public section

noncomputable section

namespace Formalism.L2.GenusGluing.Gen

open NumberField IsDedekindDomain Matrix Formalism.L2.Col
open scoped TensorProduct

theorem det_add_diagonal_cons {A : Type*} [CommRing A] {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) A) (a : A) (d : Fin n → A) :
    (M + diagonal (Fin.cons a d : Fin (n + 1) → A)).det =
      (M.submatrix Fin.succ Fin.succ + diagonal d).det * a +
        (M + diagonal (Fin.cons 0 d : Fin (n + 1) → A)).det := by
  set N := M + diagonal (Fin.cons 0 d : Fin (n + 1) → A) with hN
  have h1 : M + diagonal (Fin.cons a d : Fin (n + 1) → A) =
      N.updateRow 0 (N 0 + a • Pi.single 0 1) := by
    ext i j
    refine Fin.cases ?_ ?_ i
    · by_cases hj : j = 0
      · subst hj; simp [N]
      · simp [N, hj, Ne.symm hj]
    · intro i
      simp [N, Matrix.diagonal_apply]
  have h2 : (N.updateRow 0 (Pi.single 0 1)).det = (M.submatrix Fin.succ Fin.succ + diagonal d).det := by
    rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
    have hz : ∀ k : Fin n, (N.updateRow 0 (Pi.single 0 1)) 0 k.succ = 0 := by
      intro k; simp [Fin.succ_ne_zero]
    simp only [hz, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
    simp only [Matrix.updateRow_self, Pi.single_eq_same, Fin.val_zero, pow_zero, one_mul,
      Fin.succAbove_zero]
    congr 1
    ext i j
    simp [N, Matrix.diagonal_apply]
  rw [h1, Matrix.det_updateRow_add, Matrix.det_updateRow_smul, Matrix.updateRow_eq_self, h2]
  ring

theorem shiftDiag_of (hS : ShiftOne) : ShiftDiag := by
  intro F E _ _ _ _ _ _ hc v n
  induction n with
  | zero =>
    intro M
    refine ⟨Fin.elim0, fun i => i.elim0, 1, ?_⟩
    simp [Matrix.det_isEmpty]
  | succ n ih =>
    intro M
    obtain ⟨t', ht', w', hw'⟩ := ih (M.submatrix Fin.succ Fin.succ)
    obtain ⟨t0, ht0, w, hw⟩ := hS F E hc v _
      ((M + diagonal (Fin.cons 0 (fun i => iA F E (t' i)) : Fin (n + 1) → _)).det) ⟨w', hw'⟩
    refine ⟨Fin.cons t0 t', ?_, w, ?_⟩
    · intro i
      refine Fin.cases ?_ ?_ i
      · simpa using ht0
      · intro i; simpa using ht' i
    · have hf : (fun i => iA F E ((Fin.cons t0 t' : Fin (n + 1) → E) i)) =
          (Fin.cons (iA F E t0) (fun i => iA F E (t' i)) : Fin (n + 1) → _) := by
        funext i
        refine Fin.cases ?_ ?_ i
        · simp
        · intro i; simp
      rw [hf, det_add_diagonal_cons]
      exact hw

end Formalism.L2.GenusGluing.Gen
end
end
end

-- Source module: Formalism.LocalToGlobal.GenusGluing.GenusApproximation.GenusApproximationProofs.WeakApproxAllOf

section

@[expose] public section

noncomputable section

namespace Formalism.L2.GenusGluing.Gen

open NumberField IsDedekindDomain Matrix Formalism.L2.Col
open scoped TensorProduct

section At

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem intAt_congr {n : ℕ} (v : HeightOneSpectrum (𝓞 F))
    {Y Y' : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (h : eAt E v • Y = eAt E v • Y') :
    IntAt v Y ↔ IntAt v Y' := by
  have h' : ∀ i j, eAt E v * Y i j = eAt E v * Y' i j := fun i j => by
    have := congrFun (congrFun h i) j
    simpa only [Matrix.smul_apply, smul_eq_mul] using this
  unfold IntAt
  simp only [h']

theorem weakApproxU_at (hSD : ShiftDiag) (hCS : CayleyStep) (hII : IntAtInv) (hc : Formalism.BasicNotions.CMData F E) (n : ℕ)
    (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (hx : x ∈ UAd hc n) (v : HeightOneSpectrum (𝓞 F)) :
    ∃ γ ∈ URat hc n,
      IntAt v (((Formalism.UG.bc (iA F E) γ)⁻¹ * x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :
        Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) ∧
      IntAt v ((x⁻¹ * Formalism.UG.bc (iA F E) γ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :
        Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
  classical
  have he : eAt E v * eAt E v = eAt E v := by
    have h := (idempotentCalculation_holds F E).2.1 (fun w => w = v) (fun w => w = v)
    exact h.trans (eP_congr (fun u => and_self_iff))
  have hσe : Formalism.UG.sigR hc.sig (Formalism.L2.Herm.Af F) (eAt E v) = eAt E v := sigR_eP hc _
  obtain ⟨t, ht, w, hw⟩ := hSD F E hc v n (x : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
  have hts : ∀ i, t i * star (t i) = 1 := fun i => by rw [mul_comm]; exact ht i

  let γ0 : GL (Fin n) E :=
    { val := Matrix.diagonal t
      inv := Matrix.diagonal (fun i => star (t i))
      val_inv := by rw [Matrix.diagonal_mul_diagonal]; simp only [hts, Matrix.diagonal_one]
      inv_val := by rw [Matrix.diagonal_mul_diagonal]; simp only [ht, Matrix.diagonal_one] }
  have hγ0 : γ0 ∈ URat hc n := by
    show Formalism.UG.cT _ (Matrix.diagonal t) * 1 * Matrix.diagonal t = 1
    rw [Matrix.mul_one]
    unfold Formalism.UG.cT
    rw [Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
    have h1 : ∀ i, ((hc.sig : E →ₐ[F] E) : E →+* E) (t i) * t i = 1 := fun i => ht i
    simp only [h1, Matrix.diagonal_one]
  set g0 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F) := Formalism.UG.bc (iA F E) γ0 with hg0
  have hg0v : (g0 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = Matrix.diagonal fun i => iA F E (t i) := by
    rw [hg0]
    show (Matrix.diagonal t).map (iA F E) = _
    exact Matrix.diagonal_map (map_zero _)
  have hg0A : g0 ∈ UAd hc n := (ratIn hc n ⟨γ0, hγ0⟩).2
  rw [← hg0v] at hw

  set x1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F) := g0⁻¹ * x with hx1
  have hx1A : x1 ∈ UAd hc n := mul_mem (inv_mem hg0A) hx
  have hJ : (1 : Matrix (Fin n) (Fin n) E).map (Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F)) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  have hx1U : x1 ∈ Formalism.UG.UJ (Formalism.UG.sigR hc.sig (Formalism.L2.Herm.Af F))
      (1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
    have h := hx1A
    change _ ∈ Formalism.UG.UJ (Formalism.UG.sigR hc.sig (Formalism.L2.Herm.Af F))
      ((1 : Matrix (Fin n) (Fin n) E).map (Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F))) at h
    rwa [hJ] at h
  set x2 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F) := glueU he x1 with hx2
  have hx2A : x2 ∈ UAd hc n := by
    change _ ∈ Formalism.UG.UJ (Formalism.UG.sigR hc.sig (Formalism.L2.Herm.Af F))
      ((1 : Matrix (Fin n) (Fin n) E).map (Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F)))
    rw [hJ]
    exact glueU_mem _ he hσe hx1U

  set P : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F) :=
    (x : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) + (g0 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) with hP
  set B : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F) :=
    w • (Matrix.adjugate P * (g0 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) with hB
  have h1x : (1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) + (x1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
      ((g0⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) * P := by
    rw [hx1, Units.val_mul, hP, Matrix.mul_add, Units.inv_mul, add_comm]
  have hxB : ((1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) + (x1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) * B =
      (w * P.det) • (1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
    rw [h1x, hB]
    calc ((g0⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) * P *
          (w • (Matrix.adjugate P * (g0 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))))
        = w • (((g0⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *
            (P * Matrix.adjugate P) * (g0 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) := by
          rw [Matrix.mul_smul]; simp only [Matrix.mul_assoc]
      _ = w • (((g0⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *
            (P.det • (1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) *
            (g0 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) := by rw [Matrix.mul_adjugate]
      _ = (w * P.det) • (1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
          rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Units.inv_mul, smul_smul]
  have heB : eAt E v • (((1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) +
      (x1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) * B) =
      eAt E v • (1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
    rw [hxB, smul_smul, mul_comm w, hw]
  have hglue1 : glueM (eAt E v) (((1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) +
      (x1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) * B) = 1 := by
    unfold glueM
    rw [heB, ← add_smul, add_sub_cancel, one_smul]
  set c : E ⊗[F] Formalism.L2.Herm.Af F := iA F E (2⁻¹ : E) with hcdef
  have h2c : (2 : E ⊗[F] Formalism.L2.Herm.Af F) * c = 1 := by
    rw [hcdef, ← map_ofNat (iA F E) 2, ← map_mul, mul_inv_cancel₀ two_ne_zero, map_one]
  set s : E ⊗[F] Formalism.L2.Herm.Af F := eAt E v + 2 * (1 - eAt E v) with hs
  set s' : E ⊗[F] Formalism.L2.Herm.Af F := eAt E v + c * (1 - eAt E v) with hs'
  have hss : s * s' = 1 := by
    rw [hs, hs']
    linear_combination (-c) * he + (1 - eAt E v) ^ 2 * h2c
  have h1x2 : (1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) + (x2 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
      s • glueM (eAt E v) ((1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) +
        (x1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) := by
    rw [hx2, glueU_val, hs]
    ext i j
    simp only [glueM, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    linear_combination ((x1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) i j) * he
  have hright : ((1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) + (x2 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) *
      (s' • glueM (eAt E v) B) = 1 := by
    rw [h1x2, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hss, one_smul, glueM_mul he, hglue1]
  have hx2u : IsUnit ((1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) +
      (x2 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) :=
    ⟨⟨_, _, hright, mul_eq_one_comm.mp hright⟩, rfl⟩

  obtain ⟨γ1, hγ1, hI1⟩ := hCS F E hc n v x2 hx2A hx2u
  have hI1' : IntAt v ((x1⁻¹ * Formalism.UG.bc (iA F E) γ1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :
      Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
    refine (intAt_congr v ?_).1 hI1
    rw [Units.val_mul, Units.val_mul]
    exact glue_smul_same he _ _
  have hγ : γ0 * γ1 ∈ URat hc n := mul_mem hγ0 hγ1
  have hprod : x1⁻¹ * Formalism.UG.bc (iA F E) γ1 = x⁻¹ * Formalism.UG.bc (iA F E) (γ0 * γ1) := by
    rw [hx1, map_mul, _root_.mul_inv_rev, inv_inv, mul_assoc]
  rw [hprod] at hI1'
  refine ⟨γ0 * γ1, hγ, ?_, hI1'⟩
  have hyA : x⁻¹ * Formalism.UG.bc (iA F E) (γ0 * γ1) ∈ UAd hc n :=
    mul_mem (inv_mem hx) (ratIn hc n ⟨γ0 * γ1, hγ⟩).2
  have hinv : (Formalism.UG.bc (iA F E) (γ0 * γ1))⁻¹ * x = (x⁻¹ * Formalism.UG.bc (iA F E) (γ0 * γ1))⁻¹ := by
    rw [_root_.mul_inv_rev, inv_inv]
  rw [hinv]
  exact hII F E hc n v _ hyA hI1'

end At

theorem weakApproxAll_of : ShiftDiag → CayleyStep → IntAtInv → WeakApproxAll := by
  intro hSD hCS hII F E _ _ _ _ _ _ hc n x hx v
  exact weakApproxU_at hSD hCS hII hc n x hx v

end Formalism.L2.GenusGluing.Gen
end
end
end

-- Source module: Formalism.LocalToGlobal.GenusGluing.GenusApproximation.FinalW

section

@[expose] public section

noncomputable section

namespace Formalism.L2.GenusGluing.Gen

open NumberField IsDedekindDomain Matrix Formalism.L2.Col
open scoped TensorProduct

theorem shiftDiagonal_holds : ShiftDiag := shiftDiag_of shiftOne_holds

theorem cayleyApproximation_holds : CayleyStep := cayleyStep_of evaluationNeZero_holds approximationAdelic_holds unitNearOne_holds

theorem weakApproximationAll_holds : WeakApproxAll := weakApproxAll_of shiftDiagonal_holds cayleyApproximation_holds integralAtInverse_holds

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem weakApproximation_unitary (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) : WeakApproxU hc n := weakApproximationAll_holds F E hc n

theorem unimodGenus_iff (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) : UnimodGenusLoc E n ↔ UnimodGenus hc n :=
  localAdelicEquiv_holds F E hc n (weakApproximation_unitary hc n)

end Formalism.L2.GenusGluing.Gen
end
end
end
