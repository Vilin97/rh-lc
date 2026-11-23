module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RealAt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EquivFrameBTheta
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChangedFrameRationalUnitaryStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EvalBasisCoordsAgainstBlockAction
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FramePolynomialsWeightRealisedNextLevelStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteModelStageWeightsEqChainWeightsStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteValuesAtPointIffRealisesInStdCoordsStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ModelPartitionSizeExtensionFirstLastRows
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PosTieAt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TargetFrameMapEqComplexBlockActionScalarStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DetRationalUnitaryOrthonormalChangeMatricesStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepCharacterDetRationalIsometryStatement
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
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.SecondKernelProjection
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.TargetStepScalarEq

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

theorem half_rank_cast (R : Ranks) (j : ℕ) : (((R.N j / 2 : ℕ) : ℤ) : ℚ) = (R.N j : ℚ) / 2 := by
  obtain ⟨a, ha⟩ : Even (R.N j) := R.k_even.add (R.t_odd.add_one.mul_left j)
  have h1 : R.N j / 2 = a := by omega
  rw [h1, ha]
  push_cast
  ring

theorem target_scalar : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S =>
    ∀ (d : Dec J std) j (hj : j + 1 ≤ D.R.m) (La' : (sysS H X std).Lt (j + 1)),
      dPow (mM d (j + 1) hj La').1 (fun τ => -(wT (sysS H X std) D (hT.gat_pos u w hg) j τ)) * sPt d (j + 1) hj La' =
        d.uT S j La' * kT J j hj La'.1) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S d j hj La'
  have hjm : j < D.R.m := hj
  have hW := (GlobalTheory.T.kernelSite_modelStageWeights_eq_chainWeights S j hjm ⟨La'.1⟩).dv
  obtain ⟨e, he, hmu⟩ := GlobalTheory.T.stepCharacter_det_rationalIsometry S j hjm
  have hG := GlobalTheory.T.det_rational_unitary_orthonormalChange_matrices S (j + 1) hj
  set γ := d.gam (j + 1) hj La' with hγ
  have hmem : γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D (j + 1) hj) := d.mem (j + 1) hj La'
  have hmuγ := hmu (j + 1) hj γ hmem
  have hgd := (hG.2 γ hmem).1
  have hq0 : (gMat J (j + 1) hj 1).det ≠ 0 := left_ne_zero_of_mul_eq_one hG.1
  have hdm : (mM d (j + 1) hj La').1.det * γ.1.det = (uB J (j + 1) hj La'.1).1.det := by
    have h1 : (γ⁻¹).1.det * γ.1.det = 1 := by
      rw [← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]
    simp only [mM, uB, Units.val_mul, Matrix.det_mul]
    linear_combination ((J.A.crd (j + 1) hj).1.det * (bAt J (j + 1) hj La'.1).1.det) * h1
  have hsd : ∀ τ, (D.chTw u μ).sDiv j τ = e τ - ((D.R.N j / 2 : ℕ) : ℤ) := fun τ => by
    apply Int.cast_injective (α := ℚ)
    rw [(D.chTw u μ).sDiv_eq j hjm τ, Int.cast_sub, D.hcW_e, he τ, half_rank_cast]
    simp only [sExp, Nat.add_sub_cancel]
  simp only [dPow, sPt, Dec.uT, dif_pos hj, kT, hW, hsd]
  rw [← hγ, hmuγ, hgd]
  have hP : ∀ τ x, TaylorLogMetric.embT D τ x = embT D τ x := fun _ _ => rfl
  simp only [hP, map_mul]
  rw [← Finset.prod_zpow]
  have hb : ∀ τ, embT D τ (uB J (j + 1) hj La'.1).1.det ≠ 0 := fun τ => by
    rw [map_ne_zero, ← Matrix.GeneralLinearGroup.val_det_apply]
    exact Units.ne_zero _
  have hg0 : ∀ τ, embT D τ γ.1.det ≠ 0 := fun τ => by
    rw [map_ne_zero, ← Matrix.GeneralLinearGroup.val_det_apply]
    exact Units.ne_zero _
  have hq : ∀ τ, embT D τ (gMat J (j + 1) hj 1).det ≠ 0 := fun τ => by
    rw [map_ne_zero]
    exact hq0
  have hm : ∀ τ, embT D τ (mM d (j + 1) hj La').1.det = embT D τ (uB J (j + 1) hj La'.1).1.det / embT D τ γ.1.det := fun τ => by
    rw [eq_div_iff (hg0 τ), ← map_mul, hdm]
  simp only [hm]
  set n : ℤ := ((D.R.N j / 2 : ℕ) : ℤ)
  set c : ℤ := cTw D (j + 1)
  have key : ∀ τ, (embT D τ (uB J (j + 1) hj La'.1).1.det / embT D τ γ.1.det) ^ (-(e τ - n - c)) *
      embT D τ (uB J (j + 1) hj La'.1).1.det ^ (-c) =
      embT D τ γ.1.det ^ e τ * (embT D τ γ.1.det * embT D τ (gMat J (j + 1) hj 1).det) ^ (-(n + c)) *
        (embT D τ (uB J (j + 1) hj La'.1).1.det ^ (-(e τ - n)) * embT D τ (gMat J (j + 1) hj 1).det ^ (n + c)) := fun τ => by
    have h1 := hb τ
    have h2 := hg0 τ
    have h3 := hq τ
    simp only [div_zpow, mul_zpow, zpow_neg, zpow_sub₀ h1, zpow_sub₀ h2, zpow_add₀ h1, zpow_add₀ h2, zpow_add₀ h3]
    field_simp
  have hprod := Finset.prod_congr rfl (fun τ (_ : τ ∈ Finset.univ) => key τ)
  simp only [Finset.prod_mul_distrib] at hprod
  linear_combination (d.chi (j + 1) hj La' * ((D.chiD ((t.O u μ).dt (j + 1) (clsAt X H (j + 1) La'.1 La'.2)) : ℂˣ) : ℂ) ^ c) * hprod

end GlobalTheory.TwV.DelA
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.TargetStepScalarEqStatement

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.targetStep_scalar_eq : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ (d : Dec J std) j (hj : j + 1 ≤ D.R.m) (La' : (sysS H X std).Lt (j + 1)), dPow (mM d (j + 1) hj La').1 (fun τ => -(wT (sysS H X std) D (hT.gat_pos u w hg) j τ)) * sPt d (j + 1) hj La' = d.uT S j La' * kT J j hj La'.1) := by
  first | exact @GlobalTheory.TwV.DelA.target_scalar | exact GlobalTheory.TwV.DelA.target_scalar | (intros; apply GlobalTheory.TwV.DelA.target_scalar <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.TransportedFramePolynomialComplexValuesAtPoint

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.DelA

theorem actC_actC_inv {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (i : ℕ) {n : ℕ}
    (h : (X.Pj i).m + 1 = n) (M : GL (Fin n) D.host.E) (V : XR (X.Pj i) ℂ) :
    actC X D pos i h M (actC X D pos i h M⁻¹ V) = V := by
  let z : Frames (fun _ : D.what₂.Tau => (1 : Matrix (Fin n) (Fin n) ℂ)) := ⟨fun _ => 1, fun _ => by simp⟩
  let f : Fr1 D n := ⟨fun τ => (atR D (M * (1 : GL (Fin n) D.host.E)⁻¹) τ : Matrix (Fin n) (Fin n) ℂ) * z.1 τ, fun τ => by
    show IsUnit ((atR D (M * (1 : GL (Fin n) D.host.E)⁻¹) τ : Matrix (Fin n) (Fin n) ℂ) * 1).det
    rw [mul_one]
    exact (Matrix.GeneralLinearGroup.det (atR D (M * (1 : GL (Fin n) D.host.E)⁻¹) τ)).isUnit⟩
  exact (evC_crdB_actC X D pos i h (fun _ => 1) 1 M V z f (fun _ => rfl)).2

theorem embT_det_ne_zero (D : D7) {n : ℕ} (M : GL (Fin n) D.host.E) (τ : D.what₂.Tau) : embT D τ M.1.det ≠ 0 := by
  have h0 : M.1.det ≠ 0 := by
    have := (Matrix.GeneralLinearGroup.det M).ne_zero
    simpa using this
  exact (map_ne_zero _).2 h0

theorem transported_frame_realAt : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos → ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → letI := wittFractionAlgebraCp (D.what₂.places.resChar w); letI := algKfC S.E.toCEmb; ∀ (d : Dec J std) j (hj : j + 1 ≤ D.R.m) (h : ((sysS H X std).Pj (j + 1)).m + 1 = D.R.N (j + 1)) (La' : (sysS H X std).Lt (j + 1)) (φ : (D.chTw u μ).cls (j + 1) → (D.chTw u μ).Y (j + 1) → ℂ) (P : MvPolynomial (GL3Theta.FrV D (D.R.N (j + 1))) ℂ), P ∈ WtPol ℂ (extNu (D.R.N (j + 1)) (Formalism.L2.Ker.nuT D u j)) → (∀ y, φ (clsAt X H (j + 1) La'.1 La'.2) y = (∏ τ, (D.chTw u μ).de (j + 1) y τ ^ (D.chTw u μ).sDiv j τ)⁻¹ * frPoly (t.O u μ) (j + 1) P y) → ∃ V : XR ((sysS H X std).Pj (j + 1)) ℂ, RealAt d (j + 1) hj h La' φ V ∧ MvPolynomial.map ι V = scT d S ι j La'.1 La'.2 • GlobalTheory.FrameB.tauV ℂ_[D.what₂.places.resChar w] d.fd2 (ltC S.g S.hLT) j La' (phi0 (sysS H X std) D (hT.gat_pos u w hg) ι j P)) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hPos ι hι
  intro d j hj h La' φ P hP hφ
  have hWt := GlobalTheory.T.kernelSite_modelStageWeights_eq_chainWeights S j (by omega) ⟨La'.1⟩
  obtain ⟨-, -, -, hle, -⟩ := size_first_last_rows (sysS H X std) D (hT.gat_pos u w hg) j hWt.rk (nuT D u j) hWt.nu
  have hR : Realises (sysS H X std) D (hT.gat_pos u w hg) (j + 1) h (wT (sysS H X std) D (hT.gat_pos u w hg) j) P
      (phiC (sysS H X std) D (hT.gat_pos u w hg) (j + 1) h (wT (sysS H X std) D (hT.gat_pos u w hg) j) P) := by
    obtain ⟨R0, hR0⟩ := GlobalTheory.T.frame_polynomials_weight_realised_next_level (sysS H X std) D (hT.gat_pos u w hg) j h _ hle P hP
    exact selOf_mem (relPhi (sysS H X std) D (hT.gat_pos u w hg) (j + 1) h _) P ⟨(P, R0), hR0, rfl⟩
  refine ⟨sPt d (j + 1) hj La' • actC (sysS H X std) D (hT.gat_pos u w hg) (j + 1) h (mM d (j + 1) hj La')⁻¹
    (phiC (sysS H X std) D (hT.gat_pos u w hg) (j + 1) h (wT (sysS H X std) D (hT.gat_pos u w hg) j) P), ?_, ?_⟩
  · rw [GlobalTheory.T.kernelSite_valuesAtPoint_iff_realisesInStdCoords S d (j + 1) hj h La' (fun τ => (D.chTw u μ).sDiv j τ) φ P hφ, map_smul, actC_actC_inv]
    have hw : (fun τ => (D.chTw u μ).sDiv j τ - cTw D (j + 1)) = wT (sysS H X std) D (hT.gat_pos u w hg) j :=
      funext fun τ => (hWt.dv τ).symm
    rw [hw]
    intro f
    have h1 := hR f
    simp only [GL3Theta.evFr, map_smul, Pi.smul_apply, smul_eq_mul, MvPolynomial.smul_eval] at h1 ⊢
    rw [h1]
    ring
  · letI := wittFractionAlgebraCp (D.what₂.places.resChar w)
    letI := algKfC S.E.toCEmb
    have hPT := (posTie_at S hPos ι hι).1
    have hFr := GlobalTheory.T.changedFrame_rational_unitary S d (j + 1) hj h La'
    have hτ := GlobalTheory.T.targetFrameMap_eq_complexBlockAction_scalar (sysS H X std) D (hT.gat_pos u w hg) ℂ_[D.what₂.places.resChar w] ι (J.rho std) hPT d.fd2
      (ltC S.g S.hLT) (ltC_ne_zero _ _) j hWt.rk La' (mM d (j + 1) hj La') hFr.1 hFr.2.1 (nuT D u j) hWt.nu P hP
    have h45 := GlobalTheory.T.targetStep_scalar_eq S d j hj La'
    have hprod : dPow (mM d (j + 1) hj La').1 (fun τ => -(wT (sysS H X std) D (hT.gat_pos u w hg) j τ)) *
        ∏ τ, embT D τ (mM d (j + 1) hj La').1.det ^ wT (sysS H X std) D (hT.gat_pos u w hg) j τ = 1 := by
      unfold dPow
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_eq_one fun τ _ => ?_
      rw [zpow_neg, inv_mul_cancel₀ (zpow_ne_zero _ (embT_det_ne_zero D _ τ))]
    have hc := ltC_ne_zero S.g S.hLT
    have key : ι (sPt d (j + 1) hj La') = scT d S ι j La'.1 La'.2 * (ltC S.g S.hLT ^ (∑ τ, szT (sysS H X std) D (hT.gat_pos u w hg) j τ) *
        ι (∏ τ, embT D τ (mM d (j + 1) hj La').1.det ^ wT (sysS H X std) D (hT.gat_pos u w hg) j τ)) := by
      rw [scT, dite_eq_left hj]
      have e1 : sPt d (j + 1) hj La' = d.uT S j (La'.1, La'.2) * kT J j hj La'.1 *
          ∏ τ, embT D τ (mM d (j + 1) hj La').1.det ^ wT (sysS H X std) D (hT.gat_pos u w hg) j τ := by
        rw [← h45, mul_comm (dPow _ _) (sPt _ _ _ _), mul_assoc, hprod, mul_one]
      rw [e1, map_mul, zpow_neg]
      field_simp
    rw [hτ, smul_smul, ← key, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul]

end GlobalTheory.TwV.DelA

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.TransportedFramePolynomialComplexValuesAtPointStatement

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.transportedFramePolynomial_complex_values_at_point : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos → ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → letI := wittFractionAlgebraCp (D.what₂.places.resChar w); letI := algKfC S.E.toCEmb; ∀ (d : Dec J std) j (hj : j + 1 ≤ D.R.m) (h : ((sysS H X std).Pj (j + 1)).m + 1 = D.R.N (j + 1)) (La' : (sysS H X std).Lt (j + 1)) (φ : (D.chTw u μ).cls (j + 1) → (D.chTw u μ).Y (j + 1) → ℂ) (P : MvPolynomial (GL3Theta.FrV D (D.R.N (j + 1))) ℂ), P ∈ WtPol ℂ (extNu (D.R.N (j + 1)) (Formalism.L2.Ker.nuT D u j)) → (∀ y, φ (clsAt X H (j + 1) La'.1 La'.2) y = (∏ τ, (D.chTw u μ).de (j + 1) y τ ^ (D.chTw u μ).sDiv j τ)⁻¹ * frPoly (t.O u μ) (j + 1) P y) → ∃ V : XR ((sysS H X std).Pj (j + 1)) ℂ, RealAt d (j + 1) hj h La' φ V ∧ MvPolynomial.map ι V = scT d S ι j La'.1 La'.2 • GlobalTheory.FrameB.tauV ℂ_[D.what₂.places.resChar w] d.fd2 (ltC S.g S.hLT) j La' (phi0 (sysS H X std) D (hT.gat_pos u w hg) ι j P)) := by
  first | exact @GlobalTheory.TwV.DelA.transported_frame_realAt | exact GlobalTheory.TwV.DelA.transported_frame_realAt | (intros; apply GlobalTheory.TwV.DelA.transported_frame_realAt <;> assumption)
end
end
