module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RkLe
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EvalStdFramesEqDetPowerMulBlockValue
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ModelPartitionSizeExtensionFirstLastRowsStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ModelPolynomialOddDegreeOfRealisesFramePolyStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.OperatorMatricesAtComplexPointStatement
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealPlaceBlockWeightLastEntryConsecutiveLevelsStatement
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.NumeratorDivDenominatorAtComplexPoint

section

@[expose] public section

noncomputable section

namespace GlobalTheory.TwV.DelA

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)

theorem pow_toNat_split {K : Type} [Field K] {a : K} (ha : a ≠ 0) (e : ℤ) :
    a ^ e.toNat = a ^ (-e).toNat * a ^ e := by
  have h := Int.toNat_sub_toNat_neg e
  calc a ^ e.toNat = a ^ (-e).toNat * a ^ ((e.toNat : ℤ) - ((-e).toNat : ℤ)) := by
        rw [zpow_sub₀ ha, zpow_natCast, zpow_natCast]
        field_simp
    _ = _ := by rw [h]

theorem zT_det_ne {n : ℕ} (f : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (hf : ∀ τ, (f τ).det ≠ 0) (τ : D.what₂.Tau) :
    (zT X D pos f τ).det ≠ 0 := by
  unfold zT
  split_ifs
  · have h1 : (((f τ)⁻¹).transpose.submatrix id Fin.rev).det
        = ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) : ℤˣ) : ℤ) * (((f τ)⁻¹).transpose).det := by
      exact Matrix.det_permute' (Fin.revPerm : Equiv.Perm (Fin n)) (((f τ)⁻¹).transpose)
    rw [h1, Matrix.det_transpose, Matrix.det_nonsing_inv]
    refine mul_ne_zero (by simp) ?_
    rw [Ring.inverse_eq_inv']
    exact inv_ne_zero (hf τ)
  · exact hf τ

theorem det_rev_transpose {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    (A.transpose.submatrix Fin.rev id).det = sgRev n * A.det := by
  have : (A.transpose.submatrix Fin.rev id).det = _ := Matrix.det_permute (Fin.revPerm : Equiv.Perm (Fin n)) A.transpose
  rw [this, Matrix.det_transpose, sgRev]

theorem evD_det {Kc : Type} [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) {j : ℕ} (hN : RankTie X D j)
    (d : D.what₂.Tau → Matrix (Fin (D.R.N j)) (Fin (D.R.N (j + 1))) ℂ)
    (f' : D.what₂.Tau → Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) ℂ) {n : Type} [Fintype n] [DecidableEq n]
    (M : Matrix n n (DA X Kc j)) : evD X D pos ι hN d f' M.det = (M.map (evD X D pos ι hN d f')).det :=
  RingHom.map_det _ M

theorem det_map_cast {Kc : Type} [Field Kc] (ι : ℂ →+* Kc) {a b : ℕ} (h : a = b) (B : Matrix (Fin b) (Fin b) ℂ) :
    ((B.map ι).submatrix (Fin.cast h) (Fin.cast h)).det = ι B.det := by
  have : ((B.map ι).submatrix (Fin.cast h) (Fin.cast h)).det = (B.map ι).det :=
    Matrix.det_submatrix_equiv_self (finCongr h) (B.map ι)
  rw [this, RingHom.map_det]
  rfl

theorem evD_numD_denD : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (j : ℕ) (hN : RankTie X D j) (d : D.what₂.Tau → Matrix (Fin (D.R.N j)) (Fin (D.R.N (j + 1))) ℂ) (f' : D.what₂.Tau → Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) ℂ), (∀ τ, (f' τ).det ≠ 0) → (∀ τ, (dfr X D hN d f' τ).det ≠ 0) → evD X D pos ι hN d f' (numD X Kc j) = evD X D pos ι hN d f' (denD X Kc j) * ι (∏ τ, if IsOddPos (pos.symm τ).2 then (zT X D pos f' τ).det ^ (cT1 X D pos j τ - szT X D pos j τ) * ((zT X D pos f' τ).det ^ (D.R.N j) * sgRev (D.R.N j) * (dfr X D hN d f' τ).det) ^ (cT1 X D pos j τ - (D.R.N j : ℤ) * cT1 X D pos j τ + szT X D pos j τ) else (dfr X D hN d f' τ).det ^ (X.nuv (pos.symm τ).1 (j + 1) (pos.symm τ).2 (NN X.G.P.m X.t j)).toNat) := by
  intro p _ X D pos Kc _ _ ι j hN d f' hf hd
  classical
  have key := GlobalTheory.T.operatorMatrices_at_complexPoint X D pos Kc ι j hN d f' hf hd
  have e : ∀ G : D.what₂.Tau → ℂ, ∏ τ, G τ = ∏ v, ∏ s, G (pos ⟨v, s⟩) := fun G => by
    rw [← Equiv.prod_comp pos G, Fintype.prod_sigma]
  rw [e, map_prod]
  unfold numD denD
  simp only [map_prod]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun s _ => ?_
  simp only [cT1, szT]
  rw [Equiv.symm_apply_apply]
  obtain ⟨k1, k2, k3⟩ := key v s
  by_cases hs : IsOddPos s
  · simp only [if_pos hs]
    have hY : evD X D pos ι hN d f' (YtMat X Kc j v s).det
        = ι ((zT X D pos f' (pos ⟨v, s⟩)).det ^ D.R.N j * sgRev (D.R.N j) * (dfr X D hN d f' (pos ⟨v, s⟩)).det) := by
      rw [evD_det, k3 hs, Matrix.det_smul, det_map_cast, det_rev_transpose, Fintype.card_fin,
        show NN X.G.P.m X.t j = D.R.N j from hN.1.symm]
      simp only [map_mul, map_pow]
      ring
    have ha : ι (zT X D pos f' (pos ⟨v, s⟩)).det ≠ 0 := (map_ne_zero ι).2 (zT_det_ne X D pos f' hf _)
    have hb : ι ((zT X D pos f' (pos ⟨v, s⟩)).det ^ D.R.N j * sgRev (D.R.N j) * (dfr X D hN d f' (pos ⟨v, s⟩)).det) ≠ 0 := by
      refine (map_ne_zero ι).2 (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (zT_det_ne X D pos f' hf _)) ?_) (hd _))
      simp [sgRev]
    rw [map_mul ι ((zT X D pos f' (pos ⟨v, s⟩)).det ^ _), map_zpow₀, map_zpow₀]
    rw [map_mul (evD X D pos ι hN d f'), map_mul (evD X D pos ι hN d f'), map_pow (evD X D pos ι hN d f'),
      map_pow (evD X D pos ι hN d f'), map_pow (evD X D pos ι hN d f'), map_pow (evD X D pos ι hN d f'), k1, hY,
      pow_toNat_split ha (exY X j v s), pow_toNat_split hb (exT X j v s)]
    have h1 : exY X j v s = cMu X j v s - szMu X j v s := rfl
    have h2 : exT X j v s = cMu X j v s - (D.R.N j : ℤ) * cMu X j v s + szMu X j v s := by
      rw [exT, show NN X.G.P.m X.t j = D.R.N j from hN.1.symm]
    rw [h1, h2]
    ring
  · simp only [if_neg hs]
    rw [map_one, one_mul, map_pow (evD X D pos ι hN d f'), evD_det, k2 hs, det_map_cast, map_pow]

end GlobalTheory.TwV.DelA
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.NumeratorDivDenominatorAtComplexPointStatement

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.numerator_div_denominator_at_complex_point : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (j : ℕ) (hN : RankTie X D j) (d : D.what₂.Tau → Matrix (Fin (D.R.N j)) (Fin (D.R.N (j + 1))) ℂ) (f' : D.what₂.Tau → Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) ℂ), (∀ τ, (f' τ).det ≠ 0) → (∀ τ, (dfr X D hN d f' τ).det ≠ 0) → evD X D pos ι hN d f' (numD X Kc j) = evD X D pos ι hN d f' (denD X Kc j) * ι (∏ τ, if IsOddPos (pos.symm τ).2 then (zT X D pos f' τ).det ^ (cT1 X D pos j τ - szT X D pos j τ) * ((zT X D pos f' τ).det ^ (D.R.N j) * sgRev (D.R.N j) * (dfr X D hN d f' τ).det) ^ (cT1 X D pos j τ - (D.R.N j : ℤ) * cT1 X D pos j τ + szT X D pos j τ) else (dfr X D hN d f' τ).det ^ (X.nuv (pos.symm τ).1 (j + 1) (pos.symm τ).2 (NN X.G.P.m X.t j)).toNat) := by
  first | exact @GlobalTheory.TwV.DelA.evD_numD_denD | exact GlobalTheory.TwV.DelA.evD_numD_denD | (intros; apply GlobalTheory.TwV.DelA.evD_numD_denD <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.SubstitutedValueAtComplexPointOddBlocks

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.DelA

theorem adjugate_transpose_rev {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (h : A.det ≠ 0) :
    (A.transpose.submatrix Fin.rev id).adjugate = (sgRev n * A.det) • (A⁻¹.transpose.submatrix id Fin.rev) := by
  have hB : (A.transpose.submatrix Fin.rev id).det = sgRev n * A.det := by
    show (A.transpose.submatrix (Fin.revPerm : Equiv.Perm (Fin n)) id).det = _
    rw [Matrix.det_permute, Matrix.det_transpose, sgRev]
  have hI : (A.transpose.submatrix Fin.rev id)⁻¹ = A⁻¹.transpose.submatrix id Fin.rev := by
    show (A.transpose.submatrix (Fin.revPerm : Equiv.Perm (Fin n)) (Equiv.refl _))⁻¹ = _
    rw [Matrix.inv_submatrix_equiv, Matrix.transpose_nonsing_inv]
    rfl
  have hne : (A.transpose.submatrix Fin.rev id).det ≠ 0 := by
    rw [hB]
    refine mul_ne_zero ?_ h
    unfold sgRev
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n))) with h1 | h1 <;> rw [h1] <;> norm_num
  rw [← hI, ← hB, Matrix.inv_def, smul_smul, Ring.inverse_eq_inv', mul_inv_cancel₀ hne, one_smul]

end GlobalTheory.TwV.DelA

namespace GlobalTheory.TwV.DelA

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)

theorem posJ_blkJ (j : ℕ) (x : Σ v : Fin (X.Fl.Pj j).nV, Fin ((X.Fl.Pj j).n' v) × (Fin ((X.Fl.Pj j).m + 1) × Fin ((X.Fl.Pj j).m + 1))) :
    posJ X D pos j ⟨x.1, x.2.1⟩ = pos (blkJ X j x) := by
  cases j <;> rfl

theorem levelIndex_row_val_eq (j : ℕ) (x : Σ v : Fin (X.Fl.Pj j).nV, Fin ((X.Fl.Pj j).n' v) × (Fin ((X.Fl.Pj j).m + 1) × Fin ((X.Fl.Pj j).m + 1))) :
    ((idxJ X j x).2.2.1 : ℕ) = x.2.2.1 := by
  cases j <;> rfl

theorem levelIndex_col_val_eq (j : ℕ) (x : Σ v : Fin (X.Fl.Pj j).nV, Fin ((X.Fl.Pj j).n' v) × (Fin ((X.Fl.Pj j).m + 1) × Fin ((X.Fl.Pj j).m + 1))) :
    ((idxJ X j x).2.2.2 : ℕ) = x.2.2.2 := by
  cases j <;> rfl

def kOdd {j : ℕ} (hN : RankTie X D j) (d : D.what₂.Tau → Matrix (Fin (D.R.N j)) (Fin (D.R.N (j + 1))) ℂ)
    (f' : D.what₂.Tau → Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) ℂ) (τ : D.what₂.Tau) : ℂ :=
  (zT X D pos f' τ).det ^ ((D.R.N j : ℤ) - 1) * sgRev (D.R.N j) * (dfr X D hN d f' τ).det

theorem evD_ySub (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) {j : ℕ} (hN : RankTie X D j)
    (d : D.what₂.Tau → Matrix (Fin (D.R.N j)) (Fin (D.R.N (j + 1))) ℂ)
    (f' : D.what₂.Tau → Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) ℂ)
    (hf : ∀ τ, (f' τ).det ≠ 0) (hd : ∀ τ, (dfr X D hN d f' τ).det ≠ 0) (v : X.Pl) (s : Fin (X.G.P.n' v))
    (a t : Fin (NN X.G.P.m X.t j)) :
    evD X D pos ι hN d f' (ySub X Kc j v s a t) =
      (if IsOddPos s then ι (kOdd X D pos hN d f' (pos ⟨v, s⟩)) else 1) *
        ι (zT X D pos (dfr X D hN d f') (pos ⟨v, s⟩) (Fin.cast hN.1.symm a) (Fin.cast hN.1.symm t)) := by
  obtain ⟨_, hE, hO⟩ := GlobalTheory.T.operatorMatrices_at_complexPoint X D pos Kc ι j hN d f' hf hd v s
  have hsym : IsOddPos (pos.symm (pos ⟨v, s⟩)).2 ↔ IsOddPos s := by
    have hb : ∀ b : (Σ v : X.Pl, Fin (X.G.P.n' v)), b = ⟨v, s⟩ → (IsOddPos b.2 ↔ IsOddPos s) := by
      rintro _ rfl; exact Iff.rfl
    exact hb _ (Equiv.symm_apply_apply _ _)
  by_cases ho : IsOddPos s
  · rw [if_pos ho, ySub_odd X Kc j v s ho]
    have h1 := RingHom.map_adjugate (evD X D pos ι hN d f') (YtMat X Kc j v s)
    simp only [RingHom.mapMatrix_apply] at h1
    have h2 := congrFun (congrFun h1 a) t
    rw [Matrix.map_apply] at h2
    rw [h2, hO ho, Matrix.adjugate_smul, Fintype.card_fin,
      show (Fin.cast hN.1.symm : Fin (NN X.G.P.m X.t j) → Fin (D.R.N j)) = ⇑(finCongr hN.1.symm) from rfl,
      Matrix.adjugate_submatrix_equiv_self]
    have h3 := RingHom.map_adjugate ι ((dfr X D hN d f' (pos ⟨v, s⟩)).transpose.submatrix Fin.rev id)
    simp only [RingHom.mapMatrix_apply] at h3
    rw [← h3, adjugate_transpose_rev _ (hd _)]
    have hz : zT X D pos (dfr X D hN d f') (pos ⟨v, s⟩) = ((dfr X D hN d f' (pos ⟨v, s⟩))⁻¹).transpose.submatrix id Fin.rev := by
      unfold zT; rw [if_pos (hsym.2 ho)]
    have hpos : 1 ≤ D.R.N j := by have := rkS X D hN; omega
    have he : ((D.R.N j : ℤ) - 1) = ((NN X.G.P.m X.t j - 1 : ℕ) : ℤ) := by
      rw [← hN.1]; push_cast [Nat.cast_sub hpos]; ring
    rw [hz, kOdd, he, zpow_natCast]
    simp only [Matrix.smul_apply, Matrix.submatrix_apply, Matrix.map_apply, smul_eq_mul, map_mul, map_pow, mul_assoc]
  · rw [if_neg ho, one_mul]
    have h0 : ySub X Kc j v s = dyMat X Kc j v s := by unfold ySub; rw [if_neg ho]
    have hz : zT X D pos (dfr X D hN d f') (pos ⟨v, s⟩) = dfr X D hN d f' (pos ⟨v, s⟩) := by
      unfold zT; rw [if_neg (fun h => ho (hsym.1 h))]
    have h2 := congrFun (congrFun (hE ho) a) t
    rw [Matrix.map_apply] at h2
    rw [h0, h2, hz]
    rfl

end GlobalTheory.TwV.DelA

namespace GlobalTheory.TwV.DelA

theorem evD_subD : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (j : ℕ) (hN : RankTie X D j) (Gc : XR (X.Pj j) ℂ) (G : (X.Pj j).Xsp), MvPolynomial.map (algebraMap X.G.Kf Kc) G = MvPolynomial.map ι Gc → OddDeg X j G → ∀ (d : D.what₂.Tau → Matrix (Fin (D.R.N j)) (Fin (D.R.N (j + 1))) ℂ) (f' : D.what₂.Tau → Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) ℂ), (∀ τ, (f' τ).det ≠ 0) → (∀ τ, (dfr X D hN d f' τ).det ≠ 0) → evD X D pos ι hN d f' (subD X Kc j G) = ι ((∏ τ, if IsOddPos (pos.symm τ).2 then ((zT X D pos f' τ).det ^ ((D.R.N j : ℤ) - 1) * sgRev (D.R.N j) * (dfr X D hN d f' τ).det) ^ ((D.R.N j : ℤ) * cT1 X D pos j τ - szT X D pos j τ) else 1) * valZ X D pos j (rkS X D hN) Gc (dfr X D hN d f')) := by
  intro p _ X D pos Kc _ _ ι j hN Gc G hG hO d f' hf hd
  let g : Var (X.Pj j) → ℂ := fun y => zT X D pos (dfr X D hN d f') (posJ X D pos j ⟨y.1, y.2.1⟩)
    (Fin.cast (rkS X D hN) y.2.2.1) (Fin.cast (rkS X D hN) y.2.2.2)
  let φ : (X.Pj j).Xsp →+* Kc := (evD X D pos ι hN d f').comp (subD X Kc j : (X.Pj j).Xsp →+* DA X Kc j)
  let ψ : (X.Pj j).Xsp →+* Kc := MvPolynomial.eval₂Hom (algebraMap X.G.Kf Kc) (fun y => ι (g y))
  have hR : ι (valZ X D pos j (rkS X D hN) Gc (dfr X D hN d f')) = ψ G := by
    show ι (MvPolynomial.eval g Gc) = MvPolynomial.eval₂ (algebraMap X.G.Kf Kc) (fun y => ι (g y)) G
    rw [MvPolynomial.eval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_comp_left, RingHom.comp_id,
      ← MvPolynomial.eval_map, ← hG, MvPolynomial.eval_map]
    rfl
  have hC : ∀ a, φ (MvPolynomial.C a) = ψ (MvPolynomial.C a) := by
    intro a
    show evD X D pos ι hN d f' (subD X Kc j (MvPolynomial.C a)) = MvPolynomial.eval₂ _ _ (MvPolynomial.C a)
    rw [MvPolynomial.eval₂_C, ← MvPolynomial.algebraMap_eq, AlgHom.commutes, MvPolynomial.algebraMap_apply,
      MvPolynomial.algebraMap_apply]
    simp [evD]
  have hX : ∀ x, φ (MvPolynomial.X x) =
      (if IsOddPos (blkJ X j x).2 then ι (kOdd X D pos hN d f' (pos (blkJ X j x))) else 1) * ψ (MvPolynomial.X x) := by
    intro x
    show evD X D pos ι hN d f' (subD X Kc j (MvPolynomial.X x)) = _ * MvPolynomial.eval₂ _ _ (MvPolynomial.X x)
    rw [subD_X, MvPolynomial.eval₂_X, evD_ySub X D pos Kc ι hN d f' hf hd]
    congr 2
    show _ = zT X D pos (dfr X D hN d f') (posJ X D pos j ⟨x.1, x.2.1⟩) _ _
    rw [posJ_blkJ]
    congr 1 <;> ext <;> simp [levelIndex_row_val_eq, levelIndex_col_val_eq]
  have key := ringHom_scale φ ψ
    (fun x => if IsOddPos (blkJ X j x).2 then ι (kOdd X D pos hN d f' (pos (blkJ X j x))) else 1) hC hX
    (ι (∏ τ, if IsOddPos (pos.symm τ).2 then ((zT X D pos f' τ).det ^ ((D.R.N j : ℤ) - 1) * sgRev (D.R.N j) * (dfr X D hN d f' τ).det) ^ ((D.R.N j : ℤ) * cT1 X D pos j τ - szT X D pos j τ) else 1)) G ?_
  · rw [map_mul, hR]
    exact key
  · intro m hm
    let H : (Σ v : X.Pl, Fin (X.G.P.n' v)) → ℂ := fun b =>
      if IsOddPos b.2 then kOdd X D pos hN d f' (pos b) ^ ((D.R.N j : ℤ) * cMu X j b.1 b.2 - szMu X j b.1 b.2) else 1
    have hF : ∀ τ, (if IsOddPos (pos.symm τ).2 then ((zT X D pos f' τ).det ^ ((D.R.N j : ℤ) - 1) * sgRev (D.R.N j) * (dfr X D hN d f' τ).det) ^ ((D.R.N j : ℤ) * cT1 X D pos j τ - szT X D pos j τ) else 1) = H (pos.symm τ) := by
      intro τ
      simp only [H, cT1, szT, Equiv.apply_symm_apply]
      rfl
    rw [Finset.prod_congr rfl (fun τ _ => hF τ), Fintype.prod_equiv pos.symm (fun τ => H (pos.symm τ)) H (fun _ => rfl),
      map_prod, ← Finset.prod_fiberwise Finset.univ (blkJ X j)]
    refine Finset.prod_congr rfl fun b _ => ?_
    have h2 : ∏ x ∈ Finset.univ.filter (fun x => blkJ X j x = b),
        (if IsOddPos (blkJ X j x).2 then ι (kOdd X D pos hN d f' (pos (blkJ X j x))) else 1) ^ m x =
        (if IsOddPos b.2 then ι (kOdd X D pos hN d f' (pos b)) else 1) ^
          (∑ x ∈ Finset.univ.filter (fun x => blkJ X j x = b), m x) := by
      rw [← Finset.prod_pow_eq_pow_sum]
      refine Finset.prod_congr rfl fun x hx => ?_
      rw [(Finset.mem_filter.1 hx).2]
    rw [h2]
    by_cases hb : IsOddPos b.2
    · simp only [H]
      rw [if_pos hb, if_pos hb, hN.1, ← hO m hm b hb, zpow_natCast, map_pow]
    · simp only [H]
      rw [if_neg hb, if_neg hb, one_pow, map_one]

end GlobalTheory.TwV.DelA
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.SubstitutedValueAtComplexPointOddBlocksStatement

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.substituted_value_at_complex_point_oddBlocks : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (j : ℕ) (hN : RankTie X D j) (Gc : XR (X.Pj j) ℂ) (G : (X.Pj j).Xsp), MvPolynomial.map (algebraMap X.G.Kf Kc) G = MvPolynomial.map ι Gc → OddDeg X j G → ∀ (d : D.what₂.Tau → Matrix (Fin (D.R.N j)) (Fin (D.R.N (j + 1))) ℂ) (f' : D.what₂.Tau → Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) ℂ), (∀ τ, (f' τ).det ≠ 0) → (∀ τ, (dfr X D hN d f' τ).det ≠ 0) → evD X D pos ι hN d f' (subD X Kc j G) = ι ((∏ τ, if IsOddPos (pos.symm τ).2 then ((zT X D pos f' τ).det ^ ((D.R.N j : ℤ) - 1) * sgRev (D.R.N j) * (dfr X D hN d f' τ).det) ^ ((D.R.N j : ℤ) * cT1 X D pos j τ - szT X D pos j τ) else 1) * valZ X D pos j (rkS X D hN) Gc (dfr X D hN d f')) := by
  first | exact @GlobalTheory.TwV.DelA.evD_subD | exact GlobalTheory.TwV.DelA.evD_subD | (intros; apply GlobalTheory.TwV.DelA.evD_subD <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.OperatorIdentityLeftSideComplexPoint

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.TwV.DelA

theorem leftSide_odd_grp {M : Type} [CommGroup M] (u e d d' e' : M) (n : ℕ) (c s w : ℤ) (hu : u = e' * d'⁻¹) (he : e * e = 1) :
    (u ^ ((n : ℤ) - 1) * e * d) ^ ((n : ℤ) * c - s) * (u ^ (c - s) * (u ^ n * e * d) ^ (c - (n : ℤ) * c + s)) * u ^ (w - c) * d ^ (-w)
      = (e * e') ^ w * d' ^ (-w) * (e * d⁻¹) ^ (w - c) := by
  subst hu
  apply Additive.ofMul.injective
  have he' : Additive.ofMul e + Additive.ofMul e = 0 := by rw [← ofMul_mul, he]; rfl
  simp only [ofMul_mul, ofMul_zpow, ofMul_pow, ofMul_inv]
  linear_combination (norm := module) (c - w) • he'

theorem leftSide_odd (u e d d' e' : ℂ) (n : ℕ) (c s w : ℤ) (hd : d ≠ 0) (hd' : d' ≠ 0) (he : e * e = 1) (he' : e' * e' = 1)
    (hu : u = e' * d'⁻¹) :
    (u ^ ((n : ℤ) - 1) * e * d) ^ ((n : ℤ) * c - s) * (u ^ (c - s) * (u ^ n * e * d) ^ (c - (n : ℤ) * c + s)) * u ^ (w - c) * d ^ (-w)
      = (e * e') ^ w * d' ^ (-w) * (e * d⁻¹) ^ (w - c) := by
  have he0 : e ≠ 0 := left_ne_zero_of_mul_eq_one he
  have he0' : e' ≠ 0 := left_ne_zero_of_mul_eq_one he'
  have h := leftSide_odd_grp (Units.mk0 e' he0' * (Units.mk0 d' hd')⁻¹) (Units.mk0 e he0) (Units.mk0 d hd) (Units.mk0 d' hd')
    (Units.mk0 e' he0') n c s w rfl (Units.ext (by simpa using he))
  have h2 := congrArg Units.val h
  simp only [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, Units.val_mk0] at h2
  subst hu
  exact h2

theorem leftSide_sgRev_sq (n : ℕ) : sgRev n * sgRev n = 1 := by
  unfold sgRev
  rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
  simp

theorem leftSide_det_zT_odd {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) {n : ℕ}
    (f : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (τ : D.what₂.Tau) (h : IsOddPos (pos.symm τ).2) :
    (zT X D pos f τ).det = sgRev n * ((f τ).det)⁻¹ := by
  unfold zT
  rw [if_pos h]
  have := Matrix.det_permute' (Fin.revPerm : Equiv.Perm (Fin n)) ((f τ)⁻¹).transpose
  rw [show (⇑(Fin.revPerm : Equiv.Perm (Fin n))) = Fin.rev from rfl] at this
  rw [this, Matrix.det_transpose, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  rfl

theorem leftSide_zT_even {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) {n : ℕ}
    (f : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (τ : D.what₂.Tau) (h : ¬ IsOddPos (pos.symm τ).2) :
    zT X D pos f τ = f τ := by
  unfold zT; rw [if_neg h]

end GlobalTheory.TwV.DelA
end

namespace GlobalTheory.TwV.DelA

theorem leftSide_at_point : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (j : ℕ) (hN : RankTie X D j) (ν : D.what₂.Tau → Fin (D.R.N j) → ℕ), NuIs X D pos j ν → ∀ (Q : MvPolynomial (GL3Theta.FrV D (D.R.N j)) ℂ), Q ∈ WtPol ℂ ν → ∀ (Gc : XR (X.Pj j) ℂ) (G : (X.Pj j).Xsp), Realises X D pos j (rkS X D hN) (wT X D pos j) Q Gc → MvPolynomial.map (algebraMap X.G.Kf Kc) G = MvPolynomial.map ι Gc → ∀ (d : D.what₂.Tau → Matrix (Fin (D.R.N j)) (Fin (D.R.N (j + 1))) ℂ) (f' : D.what₂.Tau → Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) ℂ), (∀ τ, (f' τ).det ≠ 0) → (∀ τ, (dfr X D hN d f' τ).det ≠ 0) → evD X D pos ι hN d f' (subD X Kc j G * numD X Kc j) * ι (∏ τ, (zT X D pos f' τ).det ^ eT X D pos (j + 1) τ) = evD X D pos ι hN d f' (denD X Kc j) * ι (sgO X D pos j * (∏ τ, (f' τ).det ^ (-(wT X D pos j τ))) * GL3Theta.evFr D Q (dfr X D hN d f')) := by
  intro p _ X D pos Kc _ _ ι j hN ν hν Q hQ Gc G hR hG d f' hf' hdf
  have hodd := GlobalTheory.T.modelPolynomial_oddDegree_of_realisesFramePoly X D pos Kc ι j hN ν hν Q hQ Gc G hR hG
  have hsub := GlobalTheory.T.substituted_value_at_complex_point_oddBlocks X D pos Kc ι j hN Gc G hG hodd d f' hf' hdf
  have hnum := GlobalTheory.T.numerator_div_denominator_at_complex_point X D pos Kc ι j hN d f' hf' hdf
  have hex := GlobalTheory.T.realPlaceBlockWeightLastEntry_consecutive_levels X D pos j
  have hnn := (GlobalTheory.T.modelPartition_size_extension_firstLast_rows X D pos j hN ν hν).2.2.2.2
  have hR' := hR ⟨dfr X D hN d f', fun τ => (hdf τ).isUnit⟩
  have hR2 := (ev1_eq_prod_det_pow_mul_valZ X D pos j (rkS X D hN) Gc ⟨dfr X D hN d f', fun τ => (hdf τ).isUnit⟩).symm.trans hR'
  clear hR'
  simp only at hR2
  rw [map_mul, hsub, hnum]
  have gen : ∀ (x y z : ℂ) (E : Kc), ι x * (E * ι y) * ι z = E * ι (x * y * z) := by
    intro x y z E; simp only [map_mul]; ring
  rw [gen]
  congr 2
  have hW : (∏ τ, (dfr X D hN d f' τ).det ^ (-(wT X D pos j τ))) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun τ _ => zpow_ne_zero _ (hdf τ)
  have key : ∀ A V B P' S W' q Pj Wf : ℂ, Wf ≠ 0 → A * B * P' * Wf = S * W' * Pj → Pj * V = Wf * q →
      A * V * B * P' = S * W' * q := by
    intro A V B P' S W' q Pj Wf hWf hK hP
    apply mul_right_cancel₀ hWf
    linear_combination V * hK + S * W' * hP
  refine key _ _ _ _ _ _ _ _ _ hW ?_ hR2
  unfold sgO
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  obtain ⟨h1, h2⟩ := hex τ
  by_cases ho : IsOddPos (pos.symm τ).2
  · simp only [if_pos ho] at h1 h2 ⊢
    rw [h1, h2, leftSide_det_zT_odd X D pos f' τ ho, leftSide_det_zT_odd X D pos (dfr X D hN d f') τ ho]
    exact leftSide_odd _ _ _ _ _ _ _ _ _ (hdf τ) (hf' τ) (leftSide_sgRev_sq _) (leftSide_sgRev_sq _) rfl
  · simp only [if_neg ho] at h1 h2 ⊢
    rw [h1, h2, leftSide_zT_even X D pos f' τ ho, leftSide_zT_even X D pos (dfr X D hN d f') τ ho, ← zpow_natCast,
      Int.toNat_of_nonneg (hnn τ), zpow_sub₀ (hdf τ)]
    simp only [zpow_neg]
    ring

end GlobalTheory.TwV.DelA
end
end
