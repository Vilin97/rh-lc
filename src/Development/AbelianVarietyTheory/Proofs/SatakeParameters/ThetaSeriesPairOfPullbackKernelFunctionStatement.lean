module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Reframe
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelThetaAdmissibleLattices
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Reframe
import Formalism.LocalToGlobal.InertKernelTheory.DelPolOfTies
import Formalism.LocalToGlobal.InertKernelTheory.SecondKernelEntrywiseLastLevel
import Formalism.LocalToGlobal.InertKernelTheory.StatementInt
import Formalism.LocalToGlobal.InertKernelTheory.SubBSplit
import Formalism.LocalToGlobal.InertKernelTheory.TieSerPin
import Formalism.SharpRestriction.GrowthBounds.ChartComparison.NrmAMemAdForms
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IteratedFDerivConstSmulOfNe
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PullbackThenFrameSubstitutionEqChangedFramesStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TaylorDirLinear
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.MemAnalyticAtZeroOfEventuallyDifferentiableAt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TaylorCoeffConjugateSeries
import Mathlib.Tactic.Basify

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.DifferentiableOfUnitaryMatrixPullbackDifferentia

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.TwU.XbEntire

theorem entire_of_pull : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {a b : ℕ} (e : Matrix (Fin a) (Fin a) D.host.E) (e' : Matrix (Fin b) (Fin b) D.host.E) (Θ K : TaylorLogMetric.VC D a b → ℂ) (s : ℂ), e * star e = 1 → e' * star e' = 1 → s ≠ 0 → Differentiable ℂ K → (∀ z, K z = s * TaylorLogMetric.pull D (TaylorLogMetric.tor0 D cc δ) e e' Θ z) → Differentiable ℂ Θ := by
  intro D cc δ a b e e' Θ K s he he' hs hK hKΘ
  have hinv : ∀ z, Θ z = s⁻¹ * K (Formalism.L2.KerInert.PullbackComparison.tPullL cc δ (star e) (star e') z) := by
    intro z
    rw [hKΘ, ← mul_assoc, inv_mul_cancel₀ hs, one_mul, Formalism.L2.KerInert.PullbackComparison.tPullL_apply]
    show Θ z = Θ (Formalism.L2.KerInert.tPull D (TaylorLogMetric.tor0 D cc δ) e e'
      (Formalism.L2.KerInert.tPull D (TaylorLogMetric.tor0 D cc δ) (star e) (star e') z))
    rw [GlobalTheory.TwU.KerMove.tPull_tPull, mul_eq_one_comm.1 he, mul_eq_one_comm.1 he', GlobalTheory.TwU.KerMove.tPull_one]
  have hf : Θ = fun z => s⁻¹ * K (Formalism.L2.KerInert.PullbackComparison.tPullL cc δ (star e) (star e') z) := funext hinv
  rw [hf]
  exact ((hK.comp (Formalism.L2.KerInert.PullbackComparison.tPullL cc δ (star e) (star e')).differentiable).const_mul _)

end GlobalTheory.TwU.XbEntire
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.DifferentiableOfUnitaryMatrixPullbackDifferentiaStatement

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.differentiable_of_unitary_matrixPullback_differentiable : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {a b : ℕ} (e : Matrix (Fin a) (Fin a) D.host.E) (e' : Matrix (Fin b) (Fin b) D.host.E) (Θ K : TaylorLogMetric.VC D a b → ℂ) (s : ℂ), e * star e = 1 → e' * star e' = 1 → s ≠ 0 → Differentiable ℂ K → (∀ z, K z = s * TaylorLogMetric.pull D (TaylorLogMetric.tor0 D cc δ) e e' Θ z) → Differentiable ℂ Θ := by
  first | exact @GlobalTheory.TwU.XbEntire.entire_of_pull | exact GlobalTheory.TwU.XbEntire.entire_of_pull | (intros; apply GlobalTheory.TwU.XbEntire.entire_of_pull <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.PadicSeriesAlgebraicMultipleViaPlaceExtension

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.SerMap

theorem iteratedFDeriv_smul_of_ne {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
    [NormedSpace ℂ F] (c : ℂ) (hc : c ≠ 0) (f : E → F) (n : ℕ) :
    iteratedFDeriv ℂ n (fun y => c • f y) = c • iteratedFDeriv ℂ n f := by
  let _ : Invertible c := invertibleOfNonzero hc
  induction n with
  | zero =>
    ext x m
    simp [iteratedFDeriv_zero_apply]
  | succ n ih =>
    rw [iteratedFDeriv_succ_eq_comp_left, iteratedFDeriv_succ_eq_comp_left, ih]
    funext x
    simp only [Function.comp_apply]
    rw [fderiv_const_smul_of_invertible c, map_smul]
    rfl

theorem taylor_mul (D : D7) {N N' : ℕ} (c : ℂ) (G : TaylorLogMetric.VC D N N' → ℂ) (α : TaylorLogMetric.Mono D N N') :
    TaylorLogMetric.taylor D (fun z => c * G z) α = c * TaylorLogMetric.taylor D G α := by
  by_cases hc : c = 0
  · subst hc
    simp only [zero_mul]
    unfold TaylorLogMetric.taylor
    simp
  · unfold TaylorLogMetric.taylor
    have h := iteratedFDeriv_smul_of_ne c hc G (Multiset.card α.toMultiset)
    simp only [smul_eq_mul] at h
    rw [h, Pi.smul_apply, ContinuousMultilinearMap.smul_apply, smul_eq_mul, mul_div_assoc]

theorem padicSeries_const_mul : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (ι : ℂ →+* ℂ_[p]),
    (∀ z : TaylorLogMetric.Qbar, ι z = lam z) → ∀ {a b : ℕ} (K G : TaylorLogMetric.VC D a b → ℂ) (s s' : ℂ), s ∈ TaylorLogMetric.Qbar →
    TaylorLogMetric.CoefIn D K TaylorLogMetric.Qbar → (∀ z, K z = s' * G z) →
    serP lam (fun z => s * K z) = ι (s * s') • MvPowerSeries.map ι (tay G) := by
  intro D p _ lam ι hι a b K G s s' hs hK hKG
  ext α
  have hKt : TaylorLogMetric.taylor D K α = s' * TaylorLogMetric.taylor D G α := by
    have : K = fun z => s' * G z := funext hKG
    rw [this, taylor_mul]
  have hmem : s * TaylorLogMetric.taylor D K α ∈ TaylorLogMetric.Qbar := TaylorLogMetric.Qbar.mul_mem hs (hK α)
  show TaylorLogMetric.lamC lam (TaylorLogMetric.taylor D (fun z => s * K z) α) = _
  rw [taylor_mul, MvPowerSeries.coeff_smul, MvPowerSeries.coeff_map]
  unfold TaylorLogMetric.lamC
  rw [dite_eq_left hmem, ← hι ⟨_, hmem⟩]
  show ι (s * TaylorLogMetric.taylor D K α) = _
  rw [hKt, ← mul_assoc, map_mul]
  rfl

end GlobalTheory.TwV.SerMap
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.PadicSeriesAlgebraicMultipleViaPlaceExtensionStatement

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.padicSeries_algebraic_multiple_via_place_extension : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (ι : ℂ →+* ℂ_[p]), (∀ z : TaylorLogMetric.Qbar, ι z = lam z) → ∀ {a b : ℕ} (K G : TaylorLogMetric.VC D a b → ℂ) (s s' : ℂ), s ∈ TaylorLogMetric.Qbar → TaylorLogMetric.CoefIn D K TaylorLogMetric.Qbar → (∀ z, K z = s' * G z) → serP lam (fun z => s * K z) = ι (s * s') • MvPowerSeries.map ι (tay G) := by
  first | exact @GlobalTheory.TwV.SerMap.padicSeries_const_mul | exact GlobalTheory.TwV.SerMap.padicSeries_const_mul | (intros; apply GlobalTheory.TwV.SerMap.padicSeries_const_mul <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.TaylorSeriesMatrixPullbackEqLinearSubstitution

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelB

theorem pull_eq_linear (D : D7) (T : TaylorLogMetric.Tor D) (hT : ∀ τ, T.emb τ = TaylorLogMetric.embT D τ) {a b : ℕ}
    (e : Matrix (Fin a) (Fin a) D.host.E) (e' : Matrix (Fin b) (Fin b) D.host.E) (Θ : TaylorLogMetric.VC D a b → ℂ) :
    TaylorLogMetric.pull D T e e' Θ = fun z => Θ (fun τ i j =>
      ∑ x : D.what₂.Tau × Fin b × Fin a, pullMat e e' (τ, i, j) x * z x.1 x.2.1 x.2.2) := by
  funext z
  unfold TaylorLogMetric.pull
  congr 1
  funext τ i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply, Matrix.of_apply, hT,
    Fintype.sum_prod_type, pullMat]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_mul]
  rw [Finset.sum_comm]
  rw [Fintype.sum_eq_single τ (fun x hx => by simp [Ne.symm hx])]
  simp only [if_true]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [← Complex.star_def]
  ring

end GlobalTheory.TwV.DelB

namespace GlobalTheory.TwV.DelB

theorem tay_eq_taylorDir (D : D7) {a b : ℕ} (G : TaylorLogMetric.VC D a b → ℂ) :
    tay G = taylorDir (Formalism.MainNotions.TaylorLogMetric.coordV D) G := by
  ext α
  exact GlobalTheory.ConjSeries.taylor_eq_coeff D G α

theorem tay_pull_linSub : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {a b : ℕ} (e : Matrix (Fin a) (Fin a) D.host.E) (e' : Matrix (Fin b) (Fin b) D.host.E) (Θ : TaylorLogMetric.VC D a b → ℂ), Differentiable ℂ Θ → tay (TaylorLogMetric.pull D (TaylorLogMetric.tor0 D cc δ) e e' Θ) = linSub (pullMat e e') (tay Θ) := by
  intro D cc δ a b e e' Θ hΘ
  rw [pull_eq_linear D (TaylorLogMetric.tor0 D cc δ) (fun _ => rfl) e e' Θ, tay_eq_taylorDir, tay_eq_taylorDir, linSub]
  exact GlobalTheory.PSerLin.taylorDir_linear D Θ (pullMat e e') hΘ

end GlobalTheory.TwV.DelB
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.TaylorSeriesMatrixPullbackEqLinearSubstitutionStatement

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.taylorSeries_matrixPullback_eq_linear_substitution : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {a b : ℕ} (e : Matrix (Fin a) (Fin a) D.host.E) (e' : Matrix (Fin b) (Fin b) D.host.E) (Θ : TaylorLogMetric.VC D a b → ℂ), Differentiable ℂ Θ → tay (TaylorLogMetric.pull D (TaylorLogMetric.tor0 D cc δ) e e' Θ) = linSub (pullMat e e') (tay Θ) := by
  first | exact @GlobalTheory.TwV.DelB.tay_pull_linSub | exact GlobalTheory.TwV.DelB.tay_pull_linSub | (intros; apply GlobalTheory.TwV.DelB.tay_pull_linSub <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaSeriesPairOfPullbackKernelFunction

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.TwV.DelB

theorem linSub_smul' {σ R : Type} [Fintype σ] [CommRing R] (B : σ → σ → R) (a : R) (f : MvPowerSeries σ R) :
    linSub B (a • f) = a • linSub B f := by
  rw [MvPowerSeries.smul_eq_C_mul, MvPowerSeries.smul_eq_C_mul, GlobalTheory.TwU.LawAll.linSub_C_mul']

theorem map_linSub' {σ R S : Type} [Fintype σ] [CommRing R] [CommRing S] (h : R →+* S) (B : σ → σ → R)
    (f : MvPowerSeries σ R) :
    MvPowerSeries.map h (linSub B f) = linSub (fun x y => h (B x y)) (MvPowerSeries.map h f) := by
  unfold linSub
  exact GlobalTheory.PSerLin.map_subst_linear h B f

theorem frecG_pull : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (X : Sys p) (E : CEmb X.G) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (fd : FData X D) (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (ι : ℂ →+* ℂ_[p]), (∀ z : TaylorLogMetric.Qbar, ι z = lam z) → ∀ (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v), LamPos X E pos lam ρ → ∀ (e : ∀ j, X.Lt j → Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) D.host.E) (c : ℂ_[p]) (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)), e j La * star (e j La) = 1 → e (j + 1) La' * star (e (j + 1) La') = 1 → ∀ {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ) (Ξ₀ : ∀ j, X.Lt j → X.Lt (j + 1) → Formalism.L2.Col.HomE D.host.E ((X.Pj j).m + 1) ((X.Pj (j + 1)).m + 1) → ℂ) (muT : ℕ → (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)ˣ → ℂ), PairOK X fd B χ SS cl Ξ₀ muT ρ → j < X.mm → (X.Pj j).IsLatTup La.2 → (X.Pj (j + 1)).IsLatTup La'.2 → ∀ (s : ℂ) (Θ : TaylorLogMetric.VC D ((X.Pj j).m + 1) ((X.Pj (j + 1)).m + 1) → ℂ), s ≠ 0 → (∀ z, kerTh B χ SS cl (fd.kerN j La) (fd.kerN (j + 1) La') (xiM X fd Ξ₀ j La La') z = s * TaylorLogMetric.pull D B.tor (e j La) (e (j + 1) La') Θ z) → FrecG E pos fd B χ lam SS cl Ξ₀ muT c j La La' = linSub (fun x y => c * subBG E pos (reframe fd ρ e) j La La' x y) ((pPow X j La La' * ι (scal0 X fd χ muT j La La' * (Base.chiFac χ _ _ (fd.kerN j La) (fd.kerN (j + 1) La'))⁻¹ * s)) • MvPowerSeries.map ι (tay Θ)) := by
  intro D p _ X E pos fd lam ι hι ρ hρ e c j La La' he he' cc δ B χ SS cl Ξ₀ muT hok hj hL hL' s Θ hs hK
  obtain ⟨-, -, hdiff, hcoef, hsc, hcf, hcf0, hfr⟩ := hok j hj La La' hL hL'
  have hΘ : Differentiable ℂ Θ :=
    GlobalTheory.T.differentiable_of_unitary_matrixPullback_differentiable D cc δ (e j La) (e (j + 1) La') Θ _ s he he' hs hdiff hK
  have hsc' : scal0 X fd χ muT j La La' * (Base.chiFac χ _ _ (fd.kerN j La) (fd.kerN (j + 1) La'))⁻¹ ∈ TaylorLogMetric.Qbar :=
    TaylorLogMetric.Qbar.mul_mem hsc (TaylorLogMetric.Qbar.inv_mem hcf)
  have hser := GlobalTheory.T.padicSeries_algebraic_multiple_via_place_extension D p lam ι hι _ _ _ s hsc' hcoef hK
  have htay := GlobalTheory.T.taylorSeries_matrixPullback_eq_linear_substitution D cc δ (e j La) (e (j + 1) La') Θ hΘ
  have hsub := GlobalTheory.T.pullback_then_frame_substitution_eq_changed_frames D p X E pos fd lam ι hι ρ hρ e c j La La' he he' (fun v => ⟨(hfr v).1, (hfr v).2.1⟩)
  rw [frecG_eq, hser]
  change linSub _ (_ • _ • MvPowerSeries.map ι (tay (TaylorLogMetric.pull D (TaylorLogMetric.tor0 D cc δ) (e j La) (e (j + 1) La') Θ))) = _
  rw [htay, map_linSub', ← linSub_smul', ← linSub_smul', GlobalTheory.TwU.LawAll.linSub_linSub', smul_smul]
  congr 1
  funext x y
  exact hsub x y

end GlobalTheory.TwV.DelB
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaSeriesPairOfPullbackKernelFunctionStatement

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaSeriesPair_of_pullbackKernelFunction : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (X : Sys p) (E : CEmb X.G) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (fd : FData X D) (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (ι : ℂ →+* ℂ_[p]), (∀ z : TaylorLogMetric.Qbar, ι z = lam z) → ∀ (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v), LamPos X E pos lam ρ → ∀ (e : ∀ j, X.Lt j → Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) D.host.E) (c : ℂ_[p]) (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)), e j La * star (e j La) = 1 → e (j + 1) La' * star (e (j + 1) La') = 1 → ∀ {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ) (Ξ₀ : ∀ j, X.Lt j → X.Lt (j + 1) → Formalism.L2.Col.HomE D.host.E ((X.Pj j).m + 1) ((X.Pj (j + 1)).m + 1) → ℂ) (muT : ℕ → (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)ˣ → ℂ), PairOK X fd B χ SS cl Ξ₀ muT ρ → j < X.mm → (X.Pj j).IsLatTup La.2 → (X.Pj (j + 1)).IsLatTup La'.2 → ∀ (s : ℂ) (Θ : TaylorLogMetric.VC D ((X.Pj j).m + 1) ((X.Pj (j + 1)).m + 1) → ℂ), s ≠ 0 → (∀ z, kerTh B χ SS cl (fd.kerN j La) (fd.kerN (j + 1) La') (xiM X fd Ξ₀ j La La') z = s * TaylorLogMetric.pull D B.tor (e j La) (e (j + 1) La') Θ z) → FrecG E pos fd B χ lam SS cl Ξ₀ muT c j La La' = linSub (fun x y => c * subBG E pos (reframe fd ρ e) j La La' x y) ((pPow X j La La' * ι (scal0 X fd χ muT j La La' * (Base.chiFac χ _ _ (fd.kerN j La) (fd.kerN (j + 1) La'))⁻¹ * s)) • MvPowerSeries.map ι (tay Θ)) := by
  first | exact @GlobalTheory.TwV.DelB.frecG_pull | exact GlobalTheory.TwV.DelB.frecG_pull | (intros; apply GlobalTheory.TwV.DelB.frecG_pull <;> assumption)
end
end
