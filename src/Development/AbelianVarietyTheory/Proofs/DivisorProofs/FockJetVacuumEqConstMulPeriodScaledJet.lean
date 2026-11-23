module

public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Formalism.LocalToGlobal.ProjectiveLattices.CuspidalL2Subspace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockJetGaussianEntireOriginGridFrames
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPureTensorAtOriginEqThetaSeries
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrPt
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ApplyAddInfRat
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDualStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsThetaAtOfVac
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableFockVacuumGaussianDefinitePair
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacuumRealRestrictionSatisfiesStandardThetaLawStatement
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AdelicWeilVacuumFixedAndTranslatesSpan
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpaceSelfDualPairAtMostLine
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumTranslateConjugateJetBound
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.L2NormFundamentalDomain

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockJetGaussianEntireOriginGridFramesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.fockJet_gaussianEntire_origin_gridFrames : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GlobalTheory.ChiGrid.GridData L sc} (W : G.Weil) {U : Set T} (N : GlobalTheory.FunObj.Std G U) (t : T) (j : ℕ), j + 1 ≤ D.R.m → ∀ (F : WO (G.pS (.top t j)) (G.pT (.top t j)) → ℂ) (Θ : Formalism.MainNotions.TaylorLogMetric.VC D (G.pS (.top t j)).rank (G.pT (.top t j)).rank → ℂ), Differentiable ℂ Θ → (∀ w : WO (G.pS (.top t j)) (G.pT (.top t j)), w.map (finPart D) = 0 → F w = Complex.exp (-((Real.pi * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, ((‖((N.frC (.top (j + 1)) τ)⁻¹ * compAt W.θ τ w * N.frC (.top j) τ) a b‖ ^ 2 : ℝ) : ℂ)) * Θ (fun τ => (N.frC (.top (j + 1)) τ)⁻¹ * compAt W.θ τ w * N.frC (.top j) τ)) → ∀ k : FVar D (G.pT (.top t j)).rank (G.pS (.top t j)).rank →₀ ℕ, GlobalTheory.FunObj.fockIn W N.frC (.top t j) F (MvPolynomial.monomial k 1) 0 = (((Real.sqrt (2 * Real.pi * Formalism.L2.Pj.xiR D) : ℝ) : ℂ)⁻¹) ^ (k.sum fun _ n => n) * Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) Θ := by
  first | exact @GlobalTheory.FockJetOrigin.fockIn_gauss_zero | exact GlobalTheory.FockJetOrigin.fockIn_gauss_zero | (intros; apply GlobalTheory.FockJetOrigin.fockIn_gauss_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefinitePairUnitVacuumRealPointNeZero

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.VacRealForm

open GlobalTheory.FockCompare

theorem vacuum_real_ne_zero : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GlobalTheory.ChiGrid.GridData L sc} (W : G.Weil) {U : Set T} (N : GlobalTheory.FunObj.Std G U) (σ : (D.what₂.Tau → ℂ) →+ AE D), GlobalTheory.FockCompare.Chart W.θ σ → ∀ (t : T) (j : ℕ), j + 1 ≤ D.R.m → ∀ f, IsVacO W.ψ W.θ _ _ (G.cartS W.cart (.top t j)) (G.onT W.cart (.top t j)) (N.latS (.top t j) : Set _) (N.latT (.top t j) : Set _) f → ∃ z : GlobalTheory.FockCompare.RW (G.pT (.top t j)) (G.pS (.top t j)), f (GlobalTheory.FockCompare.iotaW σ (G.pT (.top t j)) (G.pS (.top t j)) z) ≠ 0 := by
  classical
  intro D T L sc G W U N σ h t j hj f hf
  by_contra hcon
  push_neg at hcon
  have hψ := hf.1
  have hS : IsSelfDualC (G.pS (.top t j)) (N.latS (.top t j)) :=
    N.selfDual (X := .top j) (show j ≤ D.R.m by omega)
  have hT : IsSelfDualC (G.pT (.top t j)) (N.latT (.top t j)) :=
    N.selfDual (X := .top (j + 1)) (show j + 1 ≤ D.R.m by omega)
  obtain ⟨-, h2, h3⟩ := GlobalTheory.T.self_dual_lattice_pairing_dual D W.ψ _ _ _ _ hψ hS hT
  have hinf := fun u => GlobalTheory.VacUnique.latO_inf (u := u) (G.pS (.top t j)) (G.pT (.top t j))
    ((N.latS (.top t j) : Set _)) ((N.latT (.top t j) : Set _)) fun _ => True
  choose ε _ hε2 using h3 f hf.2.lat
  have e : f = 0 := by
    funext w
    obtain ⟨γ, z, u, hu, rfl⟩ := GlobalTheory.VacUnique.exists_decomp h h2 w
    rw [hf.2.theta.quasi, GlobalTheory.VacUnique.apply_real_add h hψ (hinf u hu) (hε2 u hu f hf.2.lat), hcon z]
    simp
  obtain ⟨⟨p, hp⟩, hn⟩ := hf.2.norm
  have n1 := hn p hp
  rw [e] at n1
  simp [nrm2] at n1

end GlobalTheory.VacRealForm

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefinitePairUnitVacuumRealPointNeZeroStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.definite_pair_unit_vacuum_real_point_ne_zero : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GlobalTheory.ChiGrid.GridData L sc} (W : G.Weil) {U : Set T} (N : GlobalTheory.FunObj.Std G U) (σ : (D.what₂.Tau → ℂ) →+ AE D), GlobalTheory.FockCompare.Chart W.θ σ → ∀ (t : T) (j : ℕ), j + 1 ≤ D.R.m → ∀ f, IsVacO W.ψ W.θ _ _ (G.cartS W.cart (.top t j)) (G.onT W.cart (.top t j)) (N.latS (.top t j) : Set _) (N.latT (.top t j) : Set _) f → ∃ z : GlobalTheory.FockCompare.RW (G.pT (.top t j)) (G.pS (.top t j)), f (GlobalTheory.FockCompare.iotaW σ (G.pT (.top t j)) (G.pS (.top t j)) z) ≠ 0 := by
  first | exact @GlobalTheory.VacRealForm.vacuum_real_ne_zero | exact GlobalTheory.VacRealForm.vacuum_real_ne_zero | (intros; apply GlobalTheory.VacRealForm.vacuum_real_ne_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableFockVacuumGaussianDefinitePairStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.differentiable_fockVacuum_gaussian_definitePair : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GlobalTheory.ChiGrid.GridData L sc} (W : G.Weil) {U : Set T} (N : GlobalTheory.FunObj.Std G U) (σ : (D.what₂.Tau → ℂ) →+ AE D), GlobalTheory.FockCompare.Chart W.θ σ → ∀ (t : T) (j : ℕ), j + 1 ≤ D.R.m → ∀ f, IsVacO W.ψ W.θ _ _ (G.cartS W.cart (.top t j)) (G.onT W.cart (.top t j)) (N.latS (.top t j) : Set _) (N.latT (.top t j) : Set _) f → Differentiable ℂ (GlobalTheory.VacRealForm.gZ σ (G.pS (.top t j)) (G.pT (.top t j)) (N.frC (.top j)) (N.frC (.top (j + 1))) f) := by
  first | exact @GlobalTheory.VacRealForm.differentiable_gZ_top | exact GlobalTheory.VacRealForm.differentiable_gZ_top | (intros; apply GlobalTheory.VacRealForm.differentiable_gZ_top <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacuumRealRestrictionGaussianMulTheta

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.FockCompare GlobalTheory.VacRealForm

namespace GlobalTheory.VacRealForm

theorem vacuum_real_form : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GlobalTheory.ChiGrid.GridData L sc} (W : G.Weil) {U : Set T} (N : GlobalTheory.FunObj.Std G U) (δ : ℂ), Formalism.MainNotions.StandardLatticesGL3.Crv D D.host.ccK δ → δ ≠ 0 → ∀ (t : T) (j : ℕ), j + 1 ≤ D.R.m → ∀ f, IsVacO W.ψ W.θ _ _ (G.cartS W.cart (.top t j)) (G.onT W.cart (.top t j)) (N.latS (.top t j) : Set _) (N.latT (.top t j) : Set _) f → ∃ θ : Formalism.MainNotions.TaylorLogMetric.VC D (G.pS (.top t j)).rank (G.pT (.top t j)).rank → ℂ, θ ∈ Formalism.MainNotions.TaylorLogMetric.Th D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (Formalism.MainNotions.StandardLatticesGL3.stdL D _) (Formalism.MainNotions.StandardLatticesGL3.stdL D _) ∧ θ ≠ 0 ∧ ∀ w : WO (G.pS (.top t j)) (G.pT (.top t j)), w.map (finPart D) = 0 → f w = Complex.exp (-((Real.pi * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, ((‖((N.frC (.top (j + 1)) τ)⁻¹ * compAt W.θ τ w * N.frC (.top j) τ) a b‖ ^ 2 : ℝ) : ℂ)) * θ (δ • (fun τ => (N.frC (.top (j + 1)) τ)⁻¹ * compAt W.θ τ w * N.frC (.top j) τ)) := by
  intro D T L sc G W U N δ hC hδ t j hj f hf
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hf.2.inf
  have hU : ∀ X τ, IsUnit (N.frC X τ).det := fun X τ => by
    show IsUnit ((tauE D τ).mapMatrix (N.fr X).1).det
    rw [← RingHom.map_det]
    exact (Matrix.isUnits_det_units (N.fr X)).map _
  have hs : ∀ Z : D.what₂.Tau → Fin (G.pT (.top t j)).rank → Fin (G.pS (.top t j)).rank → ℂ, δ⁻¹ • δ • Z = Z :=
    fun Z => inv_smul_smul₀ hδ Z
  refine ⟨thY σ (G.pS (.top t j)) (G.pT (.top t j)) (N.frC (.top j)) (N.frC (.top (j + 1))) f δ,
    ⟨?_, ?_⟩, ?_, ?_⟩
  · exact (GlobalTheory.T.differentiable_fockVacuum_gaussian_definitePair W N σ hσ t j hj f hf).comp (differentiable_id.const_smul δ⁻¹)
  · exact GlobalTheory.T.vacuum_realRestriction_satisfies_standardThetaLaw W N σ δ hσ hC hδ t j hj f hf
  · obtain ⟨z, hz⟩ := GlobalTheory.T.definite_pair_unit_vacuum_real_point_ne_zero W N σ hσ t j hj f hf
    intro h0
    apply hz
    have e : thY σ (G.pS (.top t j)) (G.pT (.top t j)) (N.frC (.top j)) (N.frC (.top (j + 1))) f δ
        (δ • fun τ => ((N.frC (.top (j + 1)) τ)⁻¹ * Matrix.of (z τ) * N.frC (.top j) τ : Matrix _ _ ℂ)) = 0 :=
      congrFun h0 _
    unfold thY gZ at e
    erw [hs] at e
    rw [mul_eq_zero] at e
    rcases e with e | e
    · convert e using 3
      funext τ
      simp only [frPt, Matrix.of_apply]
      rw [show Matrix.of ((N.frC (.top (j + 1)) τ)⁻¹ * Matrix.of (z τ) * N.frC (.top j) τ) =
        (N.frC (.top (j + 1)) τ)⁻¹ * Matrix.of (z τ) * N.frC (.top j) τ from rfl,
        ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hU _ τ), Matrix.one_mul, Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ (hU _ τ), Matrix.mul_one]
      rfl
    · exact absurd e (Complex.exp_ne_zero _)
  · intro w hw
    unfold thY gZ
    erw [hs]
    have e1 : frPt (N.frC (.top j)) (N.frC (.top (j + 1)))
        (fun τ => ((N.frC (.top (j + 1)) τ)⁻¹ * compAt W.θ τ w * N.frC (.top j) τ : Matrix _ _ ℂ)) =
        piW W.θ (G.pT (.top t j)) (G.pS (.top t j)) w := by
      funext τ
      simp only [frPt]
      rw [show Matrix.of ((N.frC (.top (j + 1)) τ)⁻¹ * compAt W.θ τ w * N.frC (.top j) τ) =
        (N.frC (.top (j + 1)) τ)⁻¹ * compAt W.θ τ w * N.frC (.top j) τ from rfl,
        ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hU _ τ), Matrix.one_mul, Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ (hU _ τ), Matrix.mul_one]
      rfl
    rw [e1, hσ.iota_pi hw, ← mul_assoc, mul_comm _ (f w), mul_assoc, ← Complex.exp_add]
    have e2 : -((Real.pi * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b,
        ((‖((N.frC (.top (j + 1)) τ)⁻¹ * compAt W.θ τ w * N.frC (.top j) τ) a b‖ ^ 2 : ℝ) : ℂ) +
        ((Real.pi * Formalism.L2.Pj.xiR D * sqSum (fun τ => ((N.frC (.top (j + 1)) τ)⁻¹ * compAt W.θ τ w * N.frC (.top j) τ : Matrix _ _ ℂ)) : ℝ) : ℂ) = 0 := by
      simp only [sqSum]
      push_cast
      ring
    rw [e2, Complex.exp_zero, mul_one]

end GlobalTheory.VacRealForm
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacuumRealRestrictionGaussianMulThetaStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.vacuum_real_restriction_gaussian_mul_theta : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GlobalTheory.ChiGrid.GridData L sc} (W : G.Weil) {U : Set T} (N : GlobalTheory.FunObj.Std G U) (δ : ℂ), Formalism.MainNotions.StandardLatticesGL3.Crv D D.host.ccK δ → δ ≠ 0 → ∀ (t : T) (j : ℕ), j + 1 ≤ D.R.m → ∀ f, IsVacO W.ψ W.θ _ _ (G.cartS W.cart (.top t j)) (G.onT W.cart (.top t j)) (N.latS (.top t j) : Set _) (N.latT (.top t j) : Set _) f → ∃ θ : Formalism.MainNotions.TaylorLogMetric.VC D (G.pS (.top t j)).rank (G.pT (.top t j)).rank → ℂ, θ ∈ Formalism.MainNotions.TaylorLogMetric.Th D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (Formalism.MainNotions.StandardLatticesGL3.stdL D _) (Formalism.MainNotions.StandardLatticesGL3.stdL D _) ∧ θ ≠ 0 ∧ ∀ w : WO (G.pS (.top t j)) (G.pT (.top t j)), w.map (finPart D) = 0 → f w = Complex.exp (-((Real.pi * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, ((‖((N.frC (.top (j + 1)) τ)⁻¹ * compAt W.θ τ w * N.frC (.top j) τ) a b‖ ^ 2 : ℝ) : ℂ)) * θ (δ • (fun τ => (N.frC (.top (j + 1)) τ)⁻¹ * compAt W.θ τ w * N.frC (.top j) τ)) := by
  first | exact @GlobalTheory.VacRealForm.vacuum_real_form | exact GlobalTheory.VacRealForm.vacuum_real_form | (intros; apply GlobalTheory.VacRealForm.vacuum_real_form <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockJetVacuumEqConstMulPeriodScaledJet

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FunObj.TopJet

open Formalism.MainNotions.TaylorLogMetric in
theorem applyAt0_monomial (D : D7) {N N' : ℕ} (k : Formalism.MainNotions.GL3Theta.Idx D N N' →₀ ℕ) (G : VC D N N' → ℂ) :
    Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) G = (k.prod fun _ n => (n.factorial : ℂ)) * Formalism.MainNotions.TaylorLogMetric.taylor D G k := by
  classical
  unfold Formalism.MainNotions.GL3Theta.applyAt0
  rw [MvPolynomial.support_monomial, if_neg one_ne_zero, Finset.sum_singleton, MvPolynomial.coeff_monomial, if_pos rfl,
    one_mul]

open Formalism.MainNotions.TaylorLogMetric in
theorem taylor_comp_smul (D : D7) {N N' : ℕ} (G : VC D N N' → ℂ) (hG : Differentiable ℂ G) (a : ℂ) (α : Mono D N N') :
    Formalism.MainNotions.TaylorLogMetric.taylor D (fun z => G (a • z)) α = a ^ (α.sum fun _ n => n) * Formalism.MainNotions.TaylorLogMetric.taylor D G α := by
  unfold Formalism.MainNotions.TaylorLogMetric.taylor
  have key := iteratedFDeriv_comp_const_smul (𝕜 := ℂ) (i := Multiset.card (Finsupp.toMultiset α)) (f := G) a ((ReciprocityTheory.ChartRestriction.G.I2.contDiff_of_diff hG).of_le (by exact_mod_cast le_top))
  rw [key]
  simp only [smul_zero, ContinuousMultilinearMap.smul_apply, smul_eq_mul, mul_div_assoc]
  congr 2
  exact Finsupp.card_toMultiset α

open Formalism.MainNotions.TaylorLogMetric in
theorem taylor_const_smul (D : D7) {N N' : ℕ} (G : VC D N N' → ℂ) (hG : Differentiable ℂ G) (c : ℂ) (α : Mono D N N') :
    Formalism.MainNotions.TaylorLogMetric.taylor D (c • G) α = c * Formalism.MainNotions.TaylorLogMetric.taylor D G α := by
  unfold Formalism.MainNotions.TaylorLogMetric.taylor
  have key := iteratedFDeriv_const_smul_apply (𝕜 := ℂ) (i := Multiset.card (Finsupp.toMultiset α)) (f := G) (x := 0) (a := c) (((ReciprocityTheory.ChartRestriction.G.I2.contDiff_of_diff hG).of_le (by exact_mod_cast le_top)).contDiffAt)
  rw [key, ContinuousMultilinearMap.smul_apply, smul_eq_mul,
    mul_div_assoc]

theorem fockIn_vacuum_eq : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GlobalTheory.ChiGrid.GridData L sc} (W : G.Weil) {U : Set T} (N : GlobalTheory.FunObj.Std G U) (δ t0 : ℂ), Formalism.MainNotions.StandardLatticesGL3.Crv D D.host.ccK δ → δ ≠ 0 → Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (Formalism.MainNotions.TaylorLogMetric.lamOf D D.host.ccK δ) t0 → ∀ (t : T) (j : ℕ), j + 1 ≤ D.R.m → ∀ e0 : Formalism.MainNotions.TaylorLogMetric.VC D (G.pS (.top t j)).rank (G.pT (.top t j)).rank → ℂ, Formalism.MainNotions.StandardLatticesGL3.oddE0 D D.host.ccK δ t0 _ _ e0 → ∀ f, IsVacO W.ψ W.θ _ _ (G.cartS W.cart (.top t j)) (G.onT W.cart (.top t j)) (N.latS (.top t j) : Set _) (N.latT (.top t j) : Set _) f → ∃ c : ℂˣ, ∀ k : FVar D (G.pT (.top t j)).rank (G.pS (.top t j)).rank →₀ ℕ, GlobalTheory.FunObj.fockIn W N.frC (.top t j) f (MvPolynomial.monomial k 1) 0 = c * ((k.prod fun v n => GlobalTheory.FunObj.period δ v.1 ^ n) * Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) e0) := by
  intro D T L sc G W U N δ t0 hC hδ hT t j hj e0 he0 f hf
  obtain ⟨θ, hθTh, hθ0, hreal⟩ := GlobalTheory.T.vacuum_real_restriction_gaussian_mul_theta W N δ hC hδ t j hj f hf
  have hG1 := (GlobalTheory.InducedType.induced_type D).1
  have he0ne : e0 ≠ 0 := by
    intro h
    have h1 := he0.2.2.1
    rw [h] at h1
    simp only [Formalism.MainNotions.TaylorLogMetric.normSq, Pi.zero_apply, norm_zero] at h1
    have h2 := h1.symm
    simp at h2
    exact GlobalTheory.ConjJet.thetaZeroNormSq_ne_zero_cmLattice D hG1 _ δ t0 hC hT h2.1
  obtain ⟨c, hc⟩ := (GlobalTheory.ThetaLine.theta_line D hG1 _ δ hC _ _ _
    (Or.inr ⟨_, _, GlobalTheory.FinWeil.Vacuum.sd_std D _, GlobalTheory.FinWeil.Vacuum.sd_std D _, rfl⟩)).1 θ hθTh e0 he0.1 he0ne
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hθ0 (by rw [hc, zero_smul])
  refine ⟨Units.mk0 c hc0, fun k => ?_⟩
  have hdiff : Differentiable ℂ (fun z => θ (δ • z)) := hθTh.1.comp (differentiable_id.const_smul δ)
  rw [GlobalTheory.T.fockJet_gaussianEntire_origin_gridFrames W N t j hj f (fun z => θ (δ • z)) hdiff hreal k, applyAt0_monomial, applyAt0_monomial,
    taylor_comp_smul D θ hθTh.1, hc, taylor_const_smul D e0 he0.1.1]
  have hper : ∀ τ : D.what₂.Tau, GlobalTheory.FunObj.period δ τ = δ * (((Real.sqrt (2 * Real.pi * Formalism.L2.Pj.xiR D) : ℝ) : ℂ)⁻¹) := by
    intro τ
    rw [GlobalTheory.FunObj.period, GlobalTheory.AdTh.Fock.norm_embedding_hostFormConstant_eq, div_eq_mul_inv]
  have hprod : (k.prod fun v n => GlobalTheory.FunObj.period δ v.1 ^ n) =
      (δ * (((Real.sqrt (2 * Real.pi * Formalism.L2.Pj.xiR D) : ℝ) : ℂ)⁻¹)) ^ (k.sum fun _ n => n) := by
    simp only [hper, Finsupp.prod, Finsupp.sum]
    exact Finset.prod_pow_eq_pow_sum _ _ _
  rw [hprod, Units.val_mk0, mul_pow]
  ring

end GlobalTheory.FunObj.TopJet
end
end
