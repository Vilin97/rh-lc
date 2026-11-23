module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalDegreeUpperC
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FormalDegreeCompactDualIff
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.VolUFactProdMulLe
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Real.Pi.Bounds
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TwistedLevelValues
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalDegreeUpperC
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InnerProductFormula
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InnerProductFormula
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowestKTypeCoefficientsSqIntegrable
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CdScaleIsTrueScale
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSignatureBlocksOfVectorAndFrame
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftModelParameterDecreasingHalfIntegralWidthStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftRowsAntitoneSignatureRankStatement
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardMeasureUnitaryPQEqVolumeSmulCompactDual

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalDegreeDivVolumeUnitaryGroupLogBound

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

namespace GlobalTheory.LowRow

theorem volU_ge_inv_pow_of_formalDeg (r : ℕ) (hr : 1 ≤ r) :
    (((r : ℝ) ^ r)⁻¹) ^ r ≤ ReciprocityTheory.ChartRestriction.DS.volU r := by
  unfold ReciprocityTheory.ChartRestriction.DS.volU
  have hrpos : (0 : ℝ) < (r : ℝ) ^ r := by positivity
  rw [show (((r : ℝ) ^ r)⁻¹) ^ r = ∏ _i ∈ Finset.range r, ((r : ℝ) ^ r)⁻¹ by
    rw [Finset.prod_const, Finset.card_range]]
  apply Finset.prod_le_prod₀
  · intro i _; positivity
  · intro i hi
    have hi' : i < r := Finset.mem_range.mp hi
    have hfac : (i.factorial : ℝ) ≤ (r : ℝ) ^ r := by
      have h1 : i.factorial ≤ r.factorial := Nat.factorial_le hi'.le
      have h2 : r.factorial ≤ r ^ r := Nat.factorial_le_pow r
      exact_mod_cast h1.trans h2
    have hfpos : (0 : ℝ) < (i.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos i
    have hpi : (1 : ℝ) ≤ 2 * Real.pi ^ (i + 1) := by
      have : (1 : ℝ) ≤ Real.pi ^ (i + 1) := one_le_pow₀ (by linarith [Real.pi_gt_three])
      linarith
    calc ((r : ℝ) ^ r)⁻¹ ≤ (i.factorial : ℝ)⁻¹ := inv_anti₀ hfpos hfac
      _ = 1 / (i.factorial : ℝ) := by rw [one_div]
      _ ≤ 2 * Real.pi ^ (i + 1) / (i.factorial : ℝ) := by gcongr

theorem formalDeg_div_volU_log_bound : ∀ (r n : ℕ) (d : ℝ) (lam : Fin r → ℝ), 1 ≤ r → 3 ≤ n → 0 ≤ d → StrictAnti lam → (∀ a b, |lam a - lam b| ≤ d + n + 3) → 0 < ReciprocityTheory.ChartRestriction.DS.volU r ∧ 0 < (∏ a : Fin r, ∏ b ∈ Finset.univ.filter (fun b : Fin r => a < b), |lam a - lam b|) / (∏ a : Fin r, ∏ b ∈ Finset.univ.filter (fun b : Fin r => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ))) ∧ Real.log ((∏ a : Fin r, ∏ b ∈ Finset.univ.filter (fun b : Fin r => a < b), |lam a - lam b|) / (∏ a : Fin r, ∏ b ∈ Finset.univ.filter (fun b : Fin r => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ))) / ReciprocityTheory.ChartRestriction.DS.volU r) ≤ 2 + (r : ℝ) ^ 2 * Real.log (2 * Real.sqrt 2 * (r : ℝ) ^ 2 * n * (d + 2)) := by
  intro r n d lam hr hn hd hlam hbd
  set P : ℝ := ∏ a : Fin r, ∏ b ∈ Finset.univ.filter (fun b : Fin r => a < b), |lam a - lam b| with hPdef
  set D : ℝ := ∏ a : Fin r, ∏ b ∈ Finset.univ.filter (fun b : Fin r => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) with hDdef
  set V : ℝ := ReciprocityTheory.ChartRestriction.DS.volU r with hVdef
  set M : ℝ := d + n + 3 with hMdef
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hM1 : (1 : ℝ) ≤ M := by rw [hMdef]; linarith
  have hVlow := volU_ge_inv_pow_of_formalDeg r hr
  have hVpos : 0 < V := lt_of_lt_of_le (by positivity) hVlow
  have hPpos : 0 < P := by
    apply Finset.prod_pos
    intro a _
    apply Finset.prod_pos
    intro b hb
    have hab : a < b := (Finset.mem_filter.mp hb).2
    exact abs_pos.mpr (sub_ne_zero.mpr (hlam hab).ne')
  have hD1 : 1 ≤ D := by
    have : (∏ _a : Fin r, ∏ _b ∈ Finset.univ.filter (fun b : Fin r => _a < b), (1 : ℝ)) ≤ D := by
      apply Finset.prod_le_prod₀
      · intro a _; positivity
      · intro a _
        apply Finset.prod_le_prod₀
        · intro b _; positivity
        · intro b hb
          have hab : a < b := (Finset.mem_filter.mp hb).2
          have : (a : ℕ) + 1 ≤ (b : ℕ) := hab
          have : ((a : ℕ) : ℝ) + 1 ≤ ((b : ℕ) : ℝ) := by exact_mod_cast this
          linarith
    simpa using this
  have hDpos : 0 < D := lt_of_lt_of_le one_pos hD1
  have hPle : P ≤ M ^ (r * r) := by
    have : P ≤ ∏ _a : Fin r, M ^ r := by
      apply Finset.prod_le_prod₀
      · intro a _; exact Finset.prod_nonneg (fun b _ => abs_nonneg _)
      · intro a _
        calc (∏ b ∈ Finset.univ.filter (fun b : Fin r => a < b), |lam a - lam b|)
            ≤ ∏ _b ∈ Finset.univ.filter (fun b : Fin r => a < b), M :=
              Finset.prod_le_prod₀ (fun b _ => abs_nonneg _) (fun b _ => hbd a b)
          _ = M ^ (Finset.univ.filter (fun b : Fin r => a < b)).card := Finset.prod_const _
          _ ≤ M ^ r := by
              apply pow_le_pow_right₀ hM1
              calc (Finset.univ.filter (fun b : Fin r => a < b)).card ≤ (Finset.univ : Finset (Fin r)).card :=
                    Finset.card_filter_le _ _
                _ = r := by simp
    calc P ≤ ∏ _a : Fin r, M ^ r := this
      _ = M ^ (r * r) := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
  have hVinv : V⁻¹ ≤ (r : ℝ) ^ (r * r) := by
    have h := inv_anti₀ (by positivity) hVlow
    rw [inv_pow, inv_inv, ← pow_mul] at h
    exact h
  have hQpos : 0 < P / D / V := by positivity
  have hQle : P / D / V ≤ (M * r) ^ (r * r) := by
    calc P / D / V ≤ P / V := by
          gcongr
          exact div_le_self hPpos.le hD1
      _ = P * V⁻¹ := div_eq_mul_inv _ _
      _ ≤ M ^ (r * r) * (r : ℝ) ^ (r * r) := by
          apply mul_le_mul hPle hVinv (by positivity) (by positivity)
      _ = (M * r) ^ (r * r) := (mul_pow _ _ _).symm
  refine ⟨hVpos, div_pos hPpos hDpos, ?_⟩
  have hsq : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
  have hMn : M ≤ n * (d + 2) := by
    rw [hMdef]; nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ n - 1) hd]
  have hr2 : (r : ℝ) ≤ 2 * Real.sqrt 2 * (r : ℝ) ^ 2 := by nlinarith
  have hX : M * r ≤ 2 * Real.sqrt 2 * (r : ℝ) ^ 2 * n * (d + 2) := by
    calc M * r ≤ (n * (d + 2)) * (2 * Real.sqrt 2 * (r : ℝ) ^ 2) :=
          mul_le_mul hMn hr2 (by positivity) (by positivity)
      _ = 2 * Real.sqrt 2 * (r : ℝ) ^ 2 * n * (d + 2) := by ring
  have hMr : 0 < M * r := by positivity
  calc Real.log (P / D / V) ≤ Real.log ((M * r) ^ (r * r)) := Real.log_le_log hQpos hQle
    _ = ((r * r : ℕ) : ℝ) * Real.log (M * r) := Real.log_pow _ _
    _ = (r : ℝ) ^ 2 * Real.log (M * r) := by push_cast; ring
    _ ≤ (r : ℝ) ^ 2 * Real.log (2 * Real.sqrt 2 * (r : ℝ) ^ 2 * n * (d + 2)) := by
        gcongr
    _ ≤ 2 + (r : ℝ) ^ 2 * Real.log (2 * Real.sqrt 2 * (r : ℝ) ^ 2 * n * (d + 2)) := by linarith

end GlobalTheory.LowRow
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalDegreeDivVolumeUnitaryGroupLogBoundStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

theorem _root_.GlobalTheory.T.formalDegree_div_volume_unitaryGroup_log_bound : ∀ (r n : ℕ) (d : ℝ) (lam : Fin r → ℝ), 1 ≤ r → 3 ≤ n → 0 ≤ d → StrictAnti lam → (∀ a b, |lam a - lam b| ≤ d + n + 3) → 0 < ReciprocityTheory.ChartRestriction.DS.volU r ∧ 0 < (∏ a : Fin r, ∏ b ∈ Finset.univ.filter (fun b : Fin r => a < b), |lam a - lam b|) / (∏ a : Fin r, ∏ b ∈ Finset.univ.filter (fun b : Fin r => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ))) ∧ Real.log ((∏ a : Fin r, ∏ b ∈ Finset.univ.filter (fun b : Fin r => a < b), |lam a - lam b|) / (∏ a : Fin r, ∏ b ∈ Finset.univ.filter (fun b : Fin r => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ))) / ReciprocityTheory.ChartRestriction.DS.volU r) ≤ 2 + (r : ℝ) ^ 2 * Real.log (2 * Real.sqrt 2 * (r : ℝ) ^ 2 * n * (d + 2)) := by
  first | exact @GlobalTheory.LowRow.formalDeg_div_volU_log_bound | exact GlobalTheory.LowRow.formalDeg_div_volU_log_bound | (intros; apply GlobalTheory.LowRow.formalDeg_div_volU_log_bound <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvIntegralSqDiscreteSeriesCoefficientCompactDua

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

noncomputable section

namespace GlobalTheory.LowRow.CompactDualCoef

open GlobalTheory.RealCoefSq GlobalTheory.Mem.Vol.Scale GlobalTheory.Mem.Vol GlobalTheory.AdelicScalar

section Perm

variable {p q n : ℕ} {ε : Fin n → Bool}

def permFrame (e : Fin p ⊕ Fin q ≃ Fin n) : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ :=
  (1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).submatrix id e.symm

theorem mul_permFrame (e : Fin p ⊕ Fin q ≃ Fin n) (X : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) :
    X * permFrame e = X.submatrix id e.symm := by
  ext i j
  simp [permFrame, Matrix.mul_apply, Matrix.one_apply]

theorem permFrame_conjTranspose_mul (e : Fin p ⊕ Fin q ≃ Fin n) (Y : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ) :
    (permFrame e)ᴴ * Y = Y.submatrix e.symm id := by
  ext i j
  simp [permFrame, Matrix.mul_apply, Matrix.one_apply, Matrix.conjTranspose_apply]

theorem permFrame_herm {e : Fin p ⊕ Fin q ≃ Fin n} (h : Sorts ε e) :
    (permFrame e)ᴴ * Formalism.UG.Jpq p q * permFrame e = Formalism.REAL.Jm ε := by
  rw [Matrix.mul_assoc, mul_permFrame, permFrame_conjTranspose_mul, ← h.reindex_Jpq, Matrix.reindex_apply,
    Matrix.submatrix_submatrix]
  rfl

theorem frameInv_permFrame {e : Fin p ⊕ Fin q ≃ Fin n} (h : Sorts ε e)
    (X : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) :
    frameInv ε (permFrame e) * X * permFrame e = Matrix.reindex e e X := by
  have : frameInv ε (permFrame e) * X * permFrame e =
      Formalism.REAL.Jm ε * ((permFrame e)ᴴ * (Formalism.UG.Jpq p q * X * permFrame e)) := by
    simp only [frameInv, Matrix.mul_assoc]
  rw [this, mul_permFrame, permFrame_conjTranspose_mul, Matrix.submatrix_submatrix,
    show (e.symm ∘ id : Fin n → Fin p ⊕ Fin q) = e.symm from rfl,
    show (id ∘ e.symm : Fin n → Fin p ⊕ Fin q) = e.symm from rfl,
    ← Matrix.submatrix_mul_equiv (Formalism.UG.Jpq p q) X e.symm e.symm e.symm,
    ← Matrix.reindex_apply, h.reindex_Jpq, ← Matrix.mul_assoc, Formalism.REAL.Jm_mul_self, Matrix.one_mul,
    Matrix.reindex_apply]

end Perm

theorem map_frameEquiv_cd (cd : CDHaar) {p q n : ℕ} {ε : Fin n → Bool} (B : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ)
    (hB : Bᴴ * Formalism.UG.Jpq p q * B = Formalism.REAL.Jm ε) (hn : p + q = n) :
    (cd.cd p q).map (frameEquiv B hB hn) = (trueScale cd n ε : ENNReal) • Formalism.REAL.muG ε := by
  classical
  let e₀ : Fin p ⊕ Fin q ≃ Fin n := finSumFinEquiv.trans (finCongr hn)
  let ε₀ : Fin n → Bool := fun i => (e₀.symm i).isLeft
  have h₀ : Sorts ε₀ e₀ := ⟨fun i => by simp [ε₀], fun j => by simp [ε₀]⟩
  have hC : (B.submatrix e₀.symm id)ᴴ * Formalism.REAL.Jm ε₀ * B.submatrix e₀.symm id = Formalism.REAL.Jm ε := by
    rw [← h₀.reindex_Jpq, Matrix.reindex_apply, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_mul_equiv, hB]
    rfl
  have hcount : Nat.card {a // ε a = true} = p := (GlobalTheory.SignCount.card_true_eq _ hC).symm.trans h₀.card_true
  obtain ⟨P, Q, e, he⟩ := exists_sorts ε
  have hP : P = p := he.card_true.symm.trans hcount
  have hQ : Q = q := by have := Sorts.add_eq e; omega
  subst hP hQ
  have hBp := permFrame_herm he
  have hfun : (frameEquiv (permFrame e) hBp hn : UpqT P Q → Formalism.REAL.UJ ε) = he.equiv := funext fun b =>
    umat_injective (by rw [umat_frameEquiv, frameInv_permFrame he, he.umat_equiv])
  have hmap0 : (cd.cd P Q).map (frameEquiv (permFrame e) hBp hn) =
      (trueScale cd n ε : ENNReal) • Formalism.REAL.muG ε := by
    rw [hfun]
    ext A hA
    rw [Measure.map_apply he.measurable_equiv hA, ← he.set_eq]
    exact (cdScaleIs_trueScale cd n ε P Q e he.1 he.2 A hA).symm
  exact map_frameEquiv hBp hB hn (cd.cd P Q) _ hmap0

end GlobalTheory.LowRow.CompactDualCoef

namespace GlobalTheory.LowRow.CompactDualCoef

open GlobalTheory.RealCoefSq GlobalTheory.Mem.Vol.Scale GlobalTheory.Mem.Vol GlobalTheory.AdelicScalar

theorem inv_integral_coef_sq : GlobalTheory.Published.FormalDegreeCompactDual → ∀ (cd : CDHaar) {D : D7} (W : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel W S) (Fr : Frames W), IsFrames W Fr → (∀ ρ, (W.sig (tauE D ρ)).1 + (W.sig (tauE D ρ)).2 = W.rank) → ∀ ρ, StrictAnti (M.lam ρ) → (∀ a, ∃ z : ℤ, M.lam ρ a - ((W.rank : ℝ) - 1) / 2 = (z : ℝ)) → ∀ w : M.H ρ, ‖w‖ = 1 → Integrable (fun b : Upq W ρ => ‖⟪w, M.rep ρ (realMat W Fr ρ b) w⟫_ℂ‖ ^ 2) (cd.cd _ _) ∧ (∫ b : Upq W ρ, ‖⟪w, M.rep ρ (realMat W Fr ρ b) w⟫_ℂ‖ ^ 2 ∂(cd.cd _ _))⁻¹ = (∏ a : Fin W.rank, ∏ b ∈ Finset.univ.filter (fun b : Fin W.rank => a < b), |M.lam ρ a - M.lam ρ b|) / ∏ a : Fin W.rank, ∏ b ∈ Finset.univ.filter (fun b : Fin W.rank => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) := by
  intro hHC cd D W S M Fr hFr hsig ρ hanti hhalf w hw
  classical
  haveI : BorelSpace (Upq W ρ) := ⟨rfl⟩
  have hn := hsig ρ
  have hmap := map_frameEquiv_cd cd _ (frame_herm M hFr ρ) hn
  have hme : MeasurableEmbedding (frameEquiv _ (frame_herm M hFr ρ) hn) :=
    (frameEquiv _ (frame_herm M hFr ρ) hn).toHomeomorph.measurableEmbedding
  have hk : (fun b : Upq W ρ => ‖⟪w, M.rep ρ (realMat W Fr ρ b) w⟫_ℂ‖ ^ 2) =
      (fun g : Formalism.REAL.UJ (M.ε ρ) => ‖⟪w, M.σ ρ (umat g) w⟫_ℂ‖ ^ 2) ∘ frameEquiv _ (frame_herm M hFr ρ) hn :=
    funext fun b => by simp only [Function.comp_apply, rep_realMat M hFr ρ hn b]
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw
  have hpr := hHC cd (trueScale cd) (cdScaleIs_trueScale cd) W.rank (M.ε ρ) (M.lam ρ) ⟨hanti, hhalf⟩ (M.H ρ)
    (M.σ ρ) w (M.ds ρ) hw0
  rw [hw, one_pow, one_div] at hpr
  have hpos : 0 < (∏ a : Fin W.rank, ∏ b ∈ Finset.univ.filter (fun b : Fin W.rank => a < b), |M.lam ρ a - M.lam ρ b|) /
      ∏ a : Fin W.rank, ∏ b ∈ Finset.univ.filter (fun b : Fin W.rank => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) := by
    refine div_pos (Finset.prod_pos fun a _ => Finset.prod_pos fun b hb => ?_)
      (Finset.prod_pos fun a _ => Finset.prod_pos fun b hb => ?_)
    · exact abs_pos.2 (sub_ne_zero.2 (hanti.injective.ne (ne_of_lt (Finset.mem_filter.1 hb).2)))
    · have := (Finset.mem_filter.1 hb).2
      exact sub_pos.2 (by exact_mod_cast this)
  have hint : Integrable (fun g : Formalism.REAL.UJ (M.ε ρ) => ‖⟪w, M.σ ρ (umat g) w⟫_ℂ‖ ^ 2)
      ((trueScale cd W.rank (M.ε ρ) : ENNReal) • Formalism.REAL.muG (M.ε ρ)) := by
    by_contra hni
    rw [integral_undef hni, _root_.inv_zero] at hpr
    exact hpos.ne hpr
  rw [← hmap] at hint
  rw [hk]
  refine ⟨hme.integrable_map_iff.1 hint, ?_⟩
  rw [show (∫ b, ((fun g : Formalism.REAL.UJ (M.ε ρ) => ‖⟪w, M.σ ρ (umat g) w⟫_ℂ‖ ^ 2) ∘
      frameEquiv _ (frame_herm M hFr ρ) hn) b ∂(cd.cd _ _)) =
      ∫ g, ‖⟪w, M.σ ρ (umat g) w⟫_ℂ‖ ^ 2 ∂((trueScale cd W.rank (M.ε ρ) : ENNReal) • Formalism.REAL.muG (M.ε ρ)) by
    rw [← hmap, hme.integral_map]; rfl]
  exact hpr

end GlobalTheory.LowRow.CompactDualCoef
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvIntegralSqDiscreteSeriesCoefficientCompactDuaStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

theorem _root_.GlobalTheory.T.inv_integral_sq_discreteSeries_coefficient_compactDual : GlobalTheory.Published.FormalDegreeCompactDual → ∀ (cd : CDHaar) {D : D7} (W : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel W S) (Fr : Frames W), IsFrames W Fr → (∀ ρ, (W.sig (tauE D ρ)).1 + (W.sig (tauE D ρ)).2 = W.rank) → ∀ ρ, StrictAnti (M.lam ρ) → (∀ a, ∃ z : ℤ, M.lam ρ a - ((W.rank : ℝ) - 1) / 2 = (z : ℝ)) → ∀ w : M.H ρ, ‖w‖ = 1 → Integrable (fun b : Upq W ρ => ‖⟪w, M.rep ρ (realMat W Fr ρ b) w⟫_ℂ‖ ^ 2) (cd.cd _ _) ∧ (∫ b : Upq W ρ, ‖⟪w, M.rep ρ (realMat W Fr ρ b) w⟫_ℂ‖ ^ 2 ∂(cd.cd _ _))⁻¹ = (∏ a : Fin W.rank, ∏ b ∈ Finset.univ.filter (fun b : Fin W.rank => a < b), |M.lam ρ a - M.lam ρ b|) / ∏ a : Fin W.rank, ∏ b ∈ Finset.univ.filter (fun b : Fin W.rank => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) := by
  first | exact @GlobalTheory.LowRow.CompactDualCoef.inv_integral_coef_sq | exact GlobalTheory.LowRow.CompactDualCoef.inv_integral_coef_sq | (intros; apply GlobalTheory.LowRow.CompactDualCoef.inv_integral_coef_sq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardMeasureUnitaryPQEqVolumeSmulCompactDualStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

theorem _root_.GlobalTheory.T.standardMeasure_unitaryPQ_eq_volume_smul_compactDual : ∀ (cd : CDHaar) (p q : ℕ) (m : Measure (UpqT p q)), Lev.IsMinf m → m = ENNReal.ofReal (ReciprocityTheory.ChartRestriction.DS.volU (p + q)) • cd.cd p q := by
  first | exact @GlobalTheory.LowRow.CompactDualScale.isMinf_eq_volU_smul_cd | exact GlobalTheory.LowRow.CompactDualScale.isMinf_eq_volU_smul_cd | (intros; apply GlobalTheory.LowRow.CompactDualScale.isMinf_eq_volU_smul_cd <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalDegreeRealPlaceUpperBoundOfHarishChandra

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

namespace GlobalTheory.LowRow

theorem formalDegreeUpperC_of_hypotheses : GlobalTheory.Published.FormalDegreeCompactDual → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), FormalDegreeUpperC R F := by
  intro hp D G _ _ Pl0 T A Ks _ _ _ R F
  intro i t σ s P cμ cη m ω BW f₀ f c io hL
  obtain ⟨hcore, -, hσ, -⟩ := hL
  have h5 : GlobalTheory.Core5 R F := ⟨hcore.lev, hcore.grp, hcore.fam, hcore.models, hcore.thP⟩
  intro Fr hFr ρ mR hmR e he
  dsimp only
  obtain ⟨hanti, hhalf, hwid⟩ := GlobalTheory.T.liftModelParameter_decreasing_halfIntegral_width R F h5 i σ s hσ ρ
  have hsig : ∀ ρ', ((Wc D i).sig (tauE D ρ')).1 + ((Wc D i).sig (tauE D ρ')).2 = (Wc D i).rank :=
    fun ρ' => (GlobalTheory.T.liftRows_antitone_signature_rank D i σ ρ').2.2.1
  have hrk : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have h1 : 1 ≤ (Wc D i).rank := by
    rw [hrk]; have := D.R.m_add_three_le_k; have := D.R.two_le_m
    simp only [Formalism.BasicNotions.Ranks.r]; omega
  have h3 : 3 ≤ D.R.nV := by
    have := D.R.m_add_three_le_k; have := D.R.two_le_m; have := D.R.three_m_lt_t
    simp only [Formalism.BasicNotions.Ranks.nV, Formalism.BasicNotions.Ranks.r]; omega
  obtain ⟨hint, hinv⟩ := GlobalTheory.T.inv_integral_sq_discreteSeries_coefficient_compactDual hp D.cd (Wc D i) _ (R.MW i σ) Fr hFr hsig ρ hanti hhalf _ he
  have hm := GlobalTheory.T.standardMeasure_unitaryPQ_eq_volume_smul_compactDual D.cd _ _ mR hmR
  rw [hsig ρ] at hm
  obtain ⟨hvol, hQpos, hlog⟩ := GlobalTheory.T.formalDegree_div_volume_unitaryGroup_log_bound (Wc D i).rank D.R.nV (degAt D i σ ρ) ((R.MW i σ).lam ρ) h1 h3
    (by positivity) hanti hwid
  have e1 : (((Wc D i).rank : ℕ) : ℝ) = (D.R.r : ℝ) := by exact_mod_cast hrk
  rw [e1] at hlog
  subst hm
  refine ⟨hint.smul_measure ENNReal.ofReal_ne_top, ?_, ?_⟩
  · rw [integral_smul_measure, ENNReal.toReal_ofReal hvol.le, smul_eq_mul]
    refine mul_pos hvol ?_
    have : 0 < (∫ b : Upq (Wc D i) ρ, ‖⟪((e : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ),
        (R.MW i σ).rep ρ (realMat (Wc D i) Fr ρ b) ((e : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ)⟫_ℂ‖ ^ 2 ∂(D.cd.cd _ _))⁻¹ := by
      rw [hinv]; exact hQpos
    exact inv_pos.mp this
  · rw [integral_smul_measure, ENNReal.toReal_ofReal hvol.le, smul_eq_mul, mul_inv, hinv, mul_comm, ← div_eq_mul_inv]
    exact hlog

end GlobalTheory.LowRow
end
end
