module

public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RaisingLoweringOperators
public import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ActOfMemGfC
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasDerivAtFockVectorTargetLieOneParam
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaLiftInfinityTypesAtRealPlace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieActionFockOperatorsScalarsTrace
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.InfinityTypes
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ParamsEx
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HoweDualityCompactPairPolynomialFockAllRealPlaceStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RealPointsActFockByRealComponentsBasisStatement
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedSmooth
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryRealPointsStructureRealPlaces
public import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
import Mathlib.Tactic.ReduceModChar
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.IndefiniteReal.PartsOrth
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TranslateMemCoefLatFn

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasDerivAtFockVectorsTargetLieRealPlace

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.ExportSeries GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes

namespace GlobalTheory.FockLieW

theorem hasDerivAt_fockVector : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T), ∀ (τ : D.what₂.Tau), ∃ κ : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ → ℂ, ∀ Y ∈ lieAt (Wc D i) τ, ∀ (P : PolF D (Wc D i).rank (Vc D i).rank) (z : WO (Vc D i) (Wc D i)), HasDerivAt (fun s : ℝ => R.ωP i t (1, oneP R.θ (Wc D i) τ Y s) (R.ptP i t P) z) (R.ptP i t (GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ (fun _ : Fin (Vc D i).rank => true) ((R.MW i (sg0 D A)).ε τ) ((R.MW i (sg0 D A)).fr τ * Y * ((R.MW i (sg0 D A)).fr τ)⁻¹) P + κ Y • P) z) 0 := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG _ i t τ
  have hC := hG.core
  have hB := hC.models.BV i
  set AV := GlobalTheory.FockDerivP.frONB (R.BV i) hB with hAV
  set BW := GlobalTheory.ChainFr.Fr.ofModel (R.MW i (sg0 D A)) with hBW
  have hcA := GlobalTheory.FockDerivP.frONB_cart (R.BV i) hB
  have hoA := GlobalTheory.FockDerivP.frONB_onb (R.BV i) hB
  obtain ⟨hf, hv, -⟩ := GlobalTheory.CoefActIo.thetaVector_laws (i := i) hC t
  have hvac : GlobalTheory.ChainFr.IsVacF R.ψ R.θ AV BW (R.vP i t) := by
    refine ⟨hf, fun ρ => ?_⟩
    rw [hcA]
    exact hv ρ
  have hI := GlobalTheory.PairInfTypes.infTypesAt D T R.toLevCh A.μ0 hC.lev i t τ
  have hAll := GlobalTheory.LieScalar.lieFockAll D (Vc D i) (Wc D i) AV BW R.θ R.ψ _ _ (R.ωP i t) (R.vP i t) τ _ _
    hC.models.inf (hC.thP.ωP i t) hI.chiV hI.chiW hvac
  have hpt : GlobalTheory.ChainFr.ptF R.ψ R.θ AV BW (R.vP i t) = R.ptP i t := by
    unfold GlobalTheory.ChainFr.ptF RealDat.ptP
    rw [hcA, hoA]
    rfl
  refine ⟨fun Y => ((-eS D i τ : ℚ) : ℂ) * Y.trace, fun Y hY P z => ?_⟩
  have h := hAll.2 Y hY P z
  rw [hpt] at h
  exact h

end GlobalTheory.FockLieW

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasDerivAtFockVectorsTargetLieRealPlaceStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

theorem _root_.GlobalTheory.T.hasDerivAt_fockVectors_targetLie_realPlace : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T), ∀ (τ : D.what₂.Tau), ∃ κ : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ → ℂ, ∀ Y ∈ lieAt (Wc D i) τ, ∀ (P : PolF D (Wc D i).rank (Vc D i).rank) (z : WO (Vc D i) (Wc D i)), HasDerivAt (fun s : ℝ => R.ωP i t (1, oneP R.θ (Wc D i) τ Y s) (R.ptP i t P) z) (R.ptP i t (GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ (fun _ : Fin (Vc D i).rank => true) ((R.MW i (sg0 D A)).ε τ) ((R.MW i (sg0 D A)).fr τ * Y * ((R.MW i (sg0 D A)).fr τ)⁻¹) P + κ Y • P) z) 0 := by
  first | exact @GlobalTheory.FockLieW.hasDerivAt_fockVector | exact GlobalTheory.FockLieW.hasDerivAt_fockVector | (intros; apply GlobalTheory.FockLieW.hasDerivAt_fockVector <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanConjUnitaryLieAlgebraRealPlaceEqTop

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

namespace GlobalTheory.LieSpanConj

theorem exists_decomp {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (hd : H.det ≠ 0)
    (Z : Matrix (Fin n) (Fin n) ℂ) :
    ∃ X Y : Matrix (Fin n) (Fin n) ℂ, Xᴴ * H + H * X = 0 ∧ Yᴴ * H + H * Y = 0 ∧
      Z = X + Complex.I • Y := by
  have hu : IsUnit H.det := isUnit_iff_ne_zero.2 hd
  set Zb : Matrix (Fin n) (Fin n) ℂ := -(H⁻¹ * Zᴴ * H) with hZb
  have hA : Zbᴴ * H = -(H * Z) := by
    rw [hZb, conjTranspose_neg, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
      conjTranspose_nonsing_inv, hH, neg_mul, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu,
      Matrix.mul_one]
  have hB : H * Zb = -(Zᴴ * H) := by
    rw [hZb, Matrix.mul_neg, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]
  refine ⟨(1 / 2 : ℂ) • (Z + Zb), (-(Complex.I / 2)) • (Z - Zb), ?_, ?_, ?_⟩
  · rw [conjTranspose_smul, conjTranspose_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add,
      hA, hB]
    have : star (1 / 2 : ℂ) = 1 / 2 := by simp
    rw [this, ← smul_add]
    rw [show Zᴴ * H + -(H * Z) + (H * Z + -(Zᴴ * H)) = 0 by abel, smul_zero]
  · rw [conjTranspose_smul, conjTranspose_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub,
      hA, hB]
    have : star (-(Complex.I / 2)) = Complex.I / 2 := by
      simp [Complex.conj_I]
      ring
    rw [this]
    rw [show Zᴴ * H - -(H * Z) = H * Z + Zᴴ * H by abel, show H * Z - -(Zᴴ * H) = H * Z + Zᴴ * H by abel]
    rw [← add_smul]
    simp
  · rw [smul_smul, smul_add, smul_sub]
    have h1 : Complex.I * -(Complex.I / 2) = 1 / 2 := by
      have := Complex.I_sq
      linear_combination (-(1 / 2 : ℂ)) * this
    rw [h1]
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring

theorem span_conj_lieAt_eq_top : ∀ (D : D7) (V : HSp D) (τ : D.what₂.Tau) (Fm : Matrix (Fin V.rank) (Fin V.rank) ℂ),
    IsUnit Fm → Submodule.span ℂ {Z : Matrix (Fin V.rank) (Fin V.rank) ℂ | ∃ Y ∈ lieAt V τ, Z = Fm * Y * Fm⁻¹} = ⊤ := by
  intro D V τ Fm hF
  have hFd : IsUnit Fm.det := (Matrix.isUnit_iff_isUnit_det Fm).1 hF
  have hd : (gramAt D V τ).det ≠ 0 := by
    rw [gramAt, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero _).2 (Formalism.L2.Theta.gram_det_ne V)
  rw [eq_top_iff]
  intro Z' _
  obtain ⟨X, Y, hX, hY, hZ⟩ :=
    GlobalTheory.LieSpanConj.exists_decomp (gramAt D V τ) (SmoothForms.RealPts.gramAt_herm V τ) hd (Fm⁻¹ * Z' * Fm)
  have hmX : Fm * X * Fm⁻¹ ∈ Submodule.span ℂ {Z : Matrix (Fin V.rank) (Fin V.rank) ℂ | ∃ Y ∈ lieAt V τ, Z = Fm * Y * Fm⁻¹} :=
    Submodule.subset_span ⟨X, hX, rfl⟩
  have hmY : Fm * Y * Fm⁻¹ ∈ Submodule.span ℂ {Z : Matrix (Fin V.rank) (Fin V.rank) ℂ | ∃ Y ∈ lieAt V τ, Z = Fm * Y * Fm⁻¹} :=
    Submodule.subset_span ⟨Y, hY, rfl⟩
  have hZ' : Z' = Fm * X * Fm⁻¹ + Complex.I • (Fm * Y * Fm⁻¹) := by
    have : Z' = Fm * (Fm⁻¹ * Z' * Fm) * Fm⁻¹ := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hFd, Matrix.one_mul, Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ hFd, Matrix.mul_one]
    rw [this, hZ, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  rw [hZ']
  exact Submodule.add_mem _ hmX (Submodule.smul_mem _ _ hmY)

end GlobalTheory.LieSpanConj
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanConjUnitaryLieAlgebraRealPlaceEqTopStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

theorem _root_.GlobalTheory.T.span_conj_unitaryLieAlgebra_realPlace_eq_top : ∀ (D : D7) (V : HSp D) (τ : D.what₂.Tau) (Fm : Matrix (Fin V.rank) (Fin V.rank) ℂ), IsUnit Fm → Submodule.span ℂ {Z : Matrix (Fin V.rank) (Fin V.rank) ℂ | ∃ Y ∈ lieAt V τ, Z = Fm * Y * Fm⁻¹} = ⊤ := by
  first | exact @GlobalTheory.LieSpanConj.span_conj_lieAt_eq_top | exact GlobalTheory.LieSpanConj.span_conj_lieAt_eq_top | (intros; apply GlobalTheory.LieSpanConj.span_conj_lieAt_eq_top <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HoweDualityCompactPairRealPlacesIrreducible

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

noncomputable section

namespace GlobalTheory.HoweIrrCompact

section FockLin
variable {D : D7} {a b : ℕ} (τ : D.what₂.Tau) (ε : Fin a → Bool) (ε' : Fin b → Bool)

theorem fockT_zero : GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ ε ε' (0 : Matrix (Fin b) (Fin b) ℂ) = 0 := by
  simp [GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT]

theorem fockT_add (Y Y' : Matrix (Fin b) (Fin b) ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ ε ε' (Y + Y') = GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ ε ε' Y + GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ ε ε' Y' := by
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT, Matrix.add_apply, add_smul, Finset.sum_add_distrib]

theorem fockT_smul (c : ℂ) (Y : Matrix (Fin b) (Fin b) ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ ε ε' (c • Y) = c • GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ ε ε' Y := by
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT, Matrix.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

end FockLin

theorem howe_irr : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (M : Submodule ℂ ((R.cV i).W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank)), (∀ ψ ∈ M, (∀ u ∈ GinfC (Vc D i), ∀ w', R.ptP i t (ψ ((R.cV i).ρ u w')) = R.ωP i t (u, 1) (R.ptP i t (ψ w')))) → (∀ ψ ∈ M, ∀ (τ : D.what₂.Tau) (Y : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ), Y ∈ lieAt (Wc D i) τ → ∀ ψ' : ((R.cV i).W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank), (∀ w z, HasDerivAt (fun s : ℝ => R.ωP i t (1, oneP R.θ (Wc D i) τ Y s) (R.ptP i t (ψ w)) z) (R.ptP i t (ψ' w) z) 0) → ψ' ∈ M) → M ≠ ⊥ → ∀ φ : ((R.cV i).W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank), (∀ u ∈ GinfC (Vc D i), ∀ w', R.ptP i t (φ ((R.cV i).ρ u w')) = R.ωP i t (u, 1) (R.ptP i t (φ w'))) → φ ∈ M := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG hFull i t M hMeq hMlie hM0 φ hφ
  classical
  have hC := hG.core
  obtain ⟨-, -, hinj⟩ := GlobalTheory.CoefActIo.thetaVector_laws (i := i) hC t
  obtain ⟨w, BS, r, hact, hU, hsurj, hε⟩ := GlobalTheory.T.realPoints_act_fock_by_realComponents_basis D G Pl0 T A Ks R F hG hFull i t
  set ρ' : ↥(GinfC (Vc D i)) →* Module.End ℂ (R.cV i).W := (R.cV i).ρ.comp (GinfC (Vc D i)).subtype with hρ'
  have eqv : ∀ ψ : (R.cV i).W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank,
      (∀ u ∈ GinfC (Vc D i), ∀ w', R.ptP i t (ψ ((R.cV i).ρ u w')) = R.ωP i t (u, 1) (R.ptP i t (ψ w'))) →
      ∀ (k : ↥(GinfC (Vc D i))) (w' : (R.cV i).W), ψ (ρ' k w') = GlobalTheory.ExportSeries.fockGL (Wc D i).rank w BS (r k) (ψ w') := by
    intro ψ hψ k w'
    apply hinj
    rw [← hact k (ψ w')]
    exact hψ k k.2 w'
  have hirr : ∀ U : Submodule ℂ (R.cV i).W, (∀ k, U.map (ρ' k) ≤ U) → U = ⊥ ∨ U = ⊤ := by
    intro U hUk
    refine (hC.models.cV i).2.2.2.2 U fun h => ?_
    have e := GlobalTheory.AutMult.toInf_mul_toFin (V := Vc D i) h
    have h1 : (R.cV i).ρ h = ρ' (GlobalTheory.AutMult.toInf (Vc D i) h) := by
      calc (R.cV i).ρ h = (R.cV i).ρ ((GlobalTheory.AutMult.toInf (Vc D i) h : GA D (Vc D i)) * GlobalTheory.AutMult.toFin (Vc D i) h) := by rw [e]
        _ = ρ' (GlobalTheory.AutMult.toInf (Vc D i) h) := by
          rw [map_mul, (hC.models.cV i).1 _ (GlobalTheory.AutMult.toFin (Vc D i) h).2, mul_one]
          rfl
    rw [h1]
    exact hUk _
  have hlie : ∀ ψ ∈ M, ∀ (τ : D.what₂.Tau) (Z : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ),
      GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ (fun _ : Fin (Vc D i).rank => true) (fun j : Fin (Wc D i).rank => decide ((j : ℕ) < w.p τ)) Z ∘ₗ ψ ∈ M := by
    intro ψ hψ τ
    obtain ⟨κ, hκ⟩ := GlobalTheory.T.hasDerivAt_fockVectors_targetLie_realPlace D G Pl0 T A Ks R F hG hFull i t τ
    have hε' : (R.MW i (sg0 D A)).ε τ = fun j : Fin (Wc D i).rank => decide ((j : ℕ) < w.p τ) := funext (hε τ)
    set fr := (R.MW i (sg0 D A)).fr τ with hfr
    have base : ∀ Y ∈ lieAt (Wc D i) τ,
        GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ (fun _ : Fin (Vc D i).rank => true) ((R.MW i (sg0 D A)).ε τ) (fr * Y * fr⁻¹) ∘ₗ ψ ∈ M := by
      intro Y hY
      have h1 : (GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ (fun _ : Fin (Vc D i).rank => true) ((R.MW i (sg0 D A)).ε τ) (fr * Y * fr⁻¹) + κ Y • (1 : Module.End ℂ (PolF D (Wc D i).rank (Vc D i).rank))) ∘ₗ ψ ∈ M :=
        hMlie ψ hψ τ Y hY _ fun w' z => by
          simpa using hκ Y hY (ψ w') z
      have h2 : κ Y • ψ ∈ M := M.smul_mem _ hψ
      have h3 := M.sub_mem h1 h2
      convert h3 using 1
      ext x
      simp
    have hsp := GlobalTheory.T.span_conj_unitaryLieAlgebra_realPlace_eq_top D (Wc D i) τ fr ((R.MW i (sg0 D A)).fr_unit τ)
    intro Z
    have hZ : Z ∈ Submodule.span ℂ {Z : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ | ∃ Y ∈ lieAt (Wc D i) τ, Z = fr * Y * fr⁻¹} := by
      rw [hsp]; exact Submodule.mem_top
    rw [← hε']
    induction hZ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨Y, hY, rfl⟩ := hx
      exact base Y hY
    | zero =>
      rw [fockT_zero, LinearMap.zero_comp]; exact M.zero_mem
    | add x y _ _ hx hy =>
      rw [fockT_add, LinearMap.add_comp]; exact M.add_mem hx hy
    | smul c x _ hx =>
      rw [fockT_smul, LinearMap.smul_comp]; exact M.smul_mem c hx
  exact GlobalTheory.T.howeDuality_compactPair_polynomialFock_allRealPlaces D (Vc D i).rank (Wc D i).rank w BS ↥(GinfC (Vc D i)) r hU hsurj (R.cV i).W ρ' hirr M
    (fun ψ hψ => eqv ψ (hMeq ψ hψ)) hlie hM0 φ (eqv φ hφ)

end GlobalTheory.HoweIrrCompact
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HoweDualityCompactPairRealPlacesIrreducibleStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

theorem _root_.GlobalTheory.T.howeDuality_compactPair_realPlaces_irreducible : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (M : Submodule ℂ ((R.cV i).W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank)), (∀ ψ ∈ M, (∀ u ∈ GinfC (Vc D i), ∀ w', R.ptP i t (ψ ((R.cV i).ρ u w')) = R.ωP i t (u, 1) (R.ptP i t (ψ w')))) → (∀ ψ ∈ M, ∀ (τ : D.what₂.Tau) (Y : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ), Y ∈ lieAt (Wc D i) τ → ∀ ψ' : ((R.cV i).W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank), (∀ w z, HasDerivAt (fun s : ℝ => R.ωP i t (1, oneP R.θ (Wc D i) τ Y s) (R.ptP i t (ψ w)) z) (R.ptP i t (ψ' w) z) 0) → ψ' ∈ M) → M ≠ ⊥ → ∀ φ : ((R.cV i).W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank), (∀ u ∈ GinfC (Vc D i), ∀ w', R.ptP i t (φ ((R.cV i).ρ u w')) = R.ωP i t (u, 1) (R.ptP i t (φ w'))) → φ ∈ M := by
  first | exact @GlobalTheory.HoweIrrCompact.howe_irr | exact GlobalTheory.HoweIrrCompact.howe_irr | (intros; apply GlobalTheory.HoweIrrCompact.howe_irr <;> assumption)
end
end
