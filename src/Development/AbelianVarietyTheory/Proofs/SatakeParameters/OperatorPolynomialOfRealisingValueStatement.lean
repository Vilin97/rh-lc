module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RkLe
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.OperatorIdentityLeftSideComplexPoint
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
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SymbolFramePolynomialEqZeroOfGenericVanishStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EvalStdFramesEqDetPowerMulBlockValue
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FramePolynomialsWeightRealisedNextLevelStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ModelPartitionSizeExtensionFirstLastRowsStatement
public import Formalism.LocalToGlobal.InertKernelTheory.KernelDifferenceOfFrame
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.OperatorPolynomialCoeffsWeightExtendedByZero
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Realises
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.IsComplRatCompl
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.WittFractionToCpAlgebraMap
import Formalism.LocalToGlobal.InertKernelTheory.DelPolOfTies
import Formalism.LocalToGlobal.InertKernelTheory.ProjRSurj
import Formalism.LocalToGlobal.InertKernelTheory.SubBSplit
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.LtCNeZero
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.SecondKernelProjection
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ModelPolynomialOddDegreeOfRealisesFramePolyStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.OperatorIdentityLeftSideComplexPointStatement

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.operatorIdentity_leftSide_complexPoint : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (j : ℕ) (hN : RankTie X D j) (ν : D.what₂.Tau → Fin (D.R.N j) → ℕ), NuIs X D pos j ν → ∀ (Q : MvPolynomial (GL3Theta.FrV D (D.R.N j)) ℂ), Q ∈ WtPol ℂ ν → ∀ (Gc : XR (X.Pj j) ℂ) (G : (X.Pj j).Xsp), Realises X D pos j (rkS X D hN) (wT X D pos j) Q Gc → MvPolynomial.map (algebraMap X.G.Kf Kc) G = MvPolynomial.map ι Gc → ∀ (d : D.what₂.Tau → Matrix (Fin (D.R.N j)) (Fin (D.R.N (j + 1))) ℂ) (f' : D.what₂.Tau → Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) ℂ), (∀ τ, (f' τ).det ≠ 0) → (∀ τ, (dfr X D hN d f' τ).det ≠ 0) → evD X D pos ι hN d f' (subD X Kc j G * numD X Kc j) * ι (∏ τ, (zT X D pos f' τ).det ^ eT X D pos (j + 1) τ) = evD X D pos ι hN d f' (denD X Kc j) * ι (sgO X D pos j * (∏ τ, (f' τ).det ^ (-(wT X D pos j τ))) * GL3Theta.evFr D Q (dfr X D hN d f')) := by
  first | exact @GlobalTheory.TwV.DelA.leftSide_at_point | exact GlobalTheory.TwV.DelA.leftSide_at_point | (intros; apply GlobalTheory.TwV.DelA.leftSide_at_point <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.OperatorPolynomialCoeffsWeightExtendedByZeroStatement

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.operatorPolynomial_coeffs_weight_extended_by_zero : ∀ (D : D7) {N N' : ℕ}, N ≤ N' → ∀ (s : D.what₂.Tau → ℂ) (ν : D.what₂.Tau → Fin N → ℕ) (Q : MvPolynomial (GL3Theta.FrV D N) ℂ), Q ∈ WtPol ℂ ν → (∀ α, AddMonoidAlgebra.coeff (polDY D s Q (N' := N')) α ∈ WtPol ℂ (extNu N' ν)) ∧ ∀ Θ : TaylorLogMetric.VC D N N' → ℂ, framePol D s Q Θ ∈ WtPol ℂ (extNu N' ν) := by
  first | exact @GlobalTheory.TwV.DelA.wt_polDY_framePol | exact GlobalTheory.TwV.DelA.wt_polDY_framePol | (intros; apply GlobalTheory.TwV.DelA.wt_polDY_framePol <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.TransportedPolynomialComplexPointEvaluation

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.TwV.DelA

open MvPolynomial

theorem transpC_eval_aeval {σ κ : Type} (x : κ → ℂ) (g : σ → MvPolynomial κ ℂ) (Q : MvPolynomial σ ℂ) :
    eval x (aeval g Q) = eval (fun i => eval x (g i)) Q := by
  induction Q using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq, map_add (f := _)]
  | mul_X p v hp => rw [map_mul, map_mul, hp, map_mul, aeval_X, eval_X]

theorem transpC_map_eval {σ Kc : Type} [CommRing Kc] (ι : ℂ →+* Kc) (x : σ → ℂ) (R : MvPolynomial σ ℂ) :
    eval (fun i => ι (x i)) (map ι R) = ι (eval x R) := by
  induction R using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq, map_add (f := _), map_add (f := _)]
  | mul_X p v hp => rw [map_mul, map_mul, hp, map_mul, map_X, eval_X, eval_X, map_mul]

theorem transpC_hom_aeval {σ ι' κ : Type} (φ : MvPolynomial ι' (MvPolynomial κ ℂ) →+* ℂ) (hφ : ∀ c, φ (C (C c)) = c)
    (g : σ → MvPolynomial ι' (MvPolynomial κ ℂ)) (Q : MvPolynomial σ ℂ) :
    φ (aeval g Q) = eval (fun i => φ (g i)) Q := by
  induction Q using MvPolynomial.induction_on with
  | C c => simp [MvPolynomial.algebraMap_apply, hφ]
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq, map_add (f := _)]
  | mul_X p v hp => rw [map_mul, map_mul, hp, map_mul, aeval_X, eval_X]

theorem evFr_scalar_of_wtPol (D : D7) {N : ℕ} (ν : D.what₂.Tau → Fin N → ℕ) (Q : MvPolynomial (GL3Theta.FrV D N) ℂ)
    (hQ : Q ∈ WtPol ℂ ν) (s : D.what₂.Tau → ℂ) (hs : ∀ τ, s τ ≠ 0) (y : D.what₂.Tau → Matrix (Fin N) (Fin N) ℂ) :
    GL3Theta.evFr D Q (fun τ => s τ • y τ) = (∏ τ, ∏ r, s τ ^ ν τ r) * GL3Theta.evFr D Q y := by
  have hB : IsBor (fun τ => s τ • (1 : Matrix (Fin N) (Fin N) ℂ)) := fun τ =>
    ⟨fun r c hcr => by simp [Matrix.one_apply_ne hcr.ne'], fun r => by simp [hs τ]⟩
  have h1 : colSub (fun τ => s τ • (1 : Matrix (Fin N) (Fin N) ℂ)) Q = _ := hQ _ hB
  have h2 := congrArg (eval (fun k : GL3Theta.FrV D N => y k.1 k.2.1 k.2.2)) h1
  simp only [colSub, transpC_eval_aeval, smul_eval] at h2
  have h3 : (∏ τ, ∏ r, (s τ • (1 : Matrix (Fin N) (Fin N) ℂ)) r r ^ ν τ r) = ∏ τ, ∏ r, s τ ^ ν τ r := by simp
  rw [h3] at h2
  unfold GL3Theta.evFr
  rw [← h2]
  refine congrArg (fun x => eval x Q) ?_
  funext k
  simp [Matrix.smul_apply, Matrix.one_apply, mul_comm]

theorem transpC_polDY_eval (D : D7) {N N' : ℕ} (hle : N ≤ N') (s : D.what₂.Tau → ℂ) (Q : MvPolynomial (GL3Theta.FrV D N) ℂ)
    (d : D.what₂.Tau → Matrix (Fin N) (Fin N') ℂ) (f' : D.what₂.Tau → Matrix (Fin N') (Fin N') ℂ) :
    MvPolynomial.eval₂Hom (MvPolynomial.eval (fun k : GL3Theta.FrV D N' => f' k.1 k.2.1 k.2.2)) (fun k : GL3Theta.Idx D N N' => d k.1 k.2.2 k.2.1)
        (polDY D s Q (N' := N')) =
      GL3Theta.evFr D Q (fun τ => s τ • (d τ * f' τ).submatrix id (Fin.castLE hle)) := by
  unfold polDY
  rw [transpC_hom_aeval _ (fun c => by simp)]
  unfold GL3Theta.evFr
  refine congrArg (fun x => MvPolynomial.eval x Q) ?_
  funext k
  have hk : ((k.2.2 : Fin N) : ℕ) < N' := lt_of_lt_of_le k.2.2.2 hle
  simp [dfr, Matrix.mul_apply, Finset.mul_sum, hk]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [mul_assoc, mul_comm (f' k.1 b _)]
  rfl

theorem evD_trDY_polDY : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (j : ℕ) (hN : RankTie X D j) (ν : D.what₂.Tau → Fin (D.R.N j) → ℕ), NuIs X D pos j ν → ∀ (Q : MvPolynomial (GL3Theta.FrV D (D.R.N j)) ℂ), Q ∈ WtPol ℂ ν → ∀ (s : D.what₂.Tau → ℂ), (∀ τ, s τ ≠ 0) → ∀ (d : D.what₂.Tau → Matrix (Fin (D.R.N j)) (Fin (D.R.N (j + 1))) ℂ) (f' : D.what₂.Tau → Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) ℂ), (∀ τ, (f' τ).det ≠ 0) → evD X D pos ι hN d f' (trDY X Kc j D (eIdx X D pos j hN) (phi0 X D pos ι j) (polDY D s Q (N' := D.R.N (j + 1)))) * ι (∏ τ, (zT X D pos f' τ).det ^ eT X D pos (j + 1) τ) = ι ((∏ τ, (f' τ).det ^ (-(wT X D pos j τ))) * (∏ τ, s τ ^ szT X D pos j τ) * GL3Theta.evFr D Q (dfr X D hN d f')) := by
  intro p _ X D pos Kc _ _ ι j hN ν hν Q hQ s hs d f' hf
  classical
  have h' := rkT X D hN
  obtain ⟨-, hsz, -, hle, -⟩ := GlobalTheory.T.modelPartition_size_extension_firstLast_rows X D pos j hN ν hν
  have hco := (GlobalTheory.T.operatorPolynomial_coeffs_weight_extended_by_zero D (rk_le X D hN) s ν Q hQ).1
  have hreal : ∀ α, Realises X D pos (j + 1) h' (wT X D pos j) (AddMonoidAlgebra.coeff (polDY D s Q (N' := D.R.N (j + 1))) α)
      (phiC X D pos (j + 1) h' (wT X D pos j) (AddMonoidAlgebra.coeff (polDY D s Q (N' := D.R.N (j + 1))) α)) := by
    intro α
    obtain ⟨R, hR⟩ := GlobalTheory.T.frame_polynomials_weight_realised_next_level X D pos j h' (extNu _ ν) hle _ (hco α)
    exact selOf_mem (relPhi X D pos (j + 1) h' (wT X D pos j)) _ (Submodule.mem_map.2 ⟨(_, R), hR, rfl⟩)
  let F : Fr1 D (D.R.N (j + 1)) := ⟨f', fun τ => isUnit_iff_ne_zero.2 (hf τ)⟩
  have hval : ∀ α, (∏ τ, (zT X D pos f' τ).det ^ eT X D pos (j + 1) τ) *
      valZ X D pos (j + 1) h' (phiC X D pos (j + 1) h' (wT X D pos j) (AddMonoidAlgebra.coeff (polDY D s Q (N' := D.R.N (j + 1))) α)) f' =
      (∏ τ, (f' τ).det ^ (-(wT X D pos j τ))) * GL3Theta.evFr D (AddMonoidAlgebra.coeff (polDY D s Q (N' := D.R.N (j + 1))) α) f' := by
    intro α
    have := hreal α F
    rw [ev1_eq_prod_det_pow_mul_valZ] at this
    exact this
  have hD : evD X D pos ι hN d f' (trDY X Kc j D (eIdx X D pos j hN) (phi0 X D pos ι j) (polDY D s Q (N' := D.R.N (j + 1)))) =
      ι (∑ α ∈ (polDY D s Q (N' := D.R.N (j + 1))).support,
        valZ X D pos (j + 1) h' (phiC X D pos (j + 1) h' (wT X D pos j) (AddMonoidAlgebra.coeff (polDY D s Q (N' := D.R.N (j + 1))) α)) f' *
          ∏ k ∈ α.support, d k.1 k.2.2 k.2.1 ^ α k) := by
    unfold trDY

    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    unfold evD
    rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_monomial,
      Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
    unfold phi0
    rw [dite_eq_left h', map_mul, map_prod]
    congr 1
    · unfold valZ
      exact transpC_map_eval ι _ _
    · unfold Finsupp.prod
      refine Finset.prod_congr rfl fun k _ => ?_
      simp [eIdx, map_pow]
  have hP : ∑ α ∈ (polDY D s Q (N' := D.R.N (j + 1))).support,
        GL3Theta.evFr D (AddMonoidAlgebra.coeff (polDY D s Q (N' := D.R.N (j + 1))) α) f' * ∏ k ∈ α.support, d k.1 k.2.2 k.2.1 ^ α k =
      (∏ τ, s τ ^ szT X D pos j τ) * GL3Theta.evFr D Q (dfr X D hN d f') := by
    let φ : MvPolynomial (GL3Theta.Idx D (D.R.N j) (D.R.N (j + 1))) (MvPolynomial (GL3Theta.FrV D (D.R.N (j + 1))) ℂ) →+* ℂ :=
      MvPolynomial.eval₂Hom (MvPolynomial.eval (fun k : GL3Theta.FrV D (D.R.N (j + 1)) => f' k.1 k.2.1 k.2.2))
        (fun k => d k.1 k.2.2 k.2.1)
    have e1 : φ (polDY D s Q (N' := D.R.N (j + 1))) = ∑ α ∈ (polDY D s Q (N' := D.R.N (j + 1))).support,
        GL3Theta.evFr D (AddMonoidAlgebra.coeff (polDY D s Q (N' := D.R.N (j + 1))) α) f' * ∏ k ∈ α.support, d k.1 k.2.2 k.2.1 ^ α k := by
      rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq]
      rfl
    have e2 : φ (polDY D s Q (N' := D.R.N (j + 1))) = GL3Theta.evFr D Q (fun τ => s τ • dfr X D hN d f' τ) :=
      transpC_polDY_eval D (rk_le X D hN) s Q d f'
    have e3 : ∀ τ, ∏ r, s τ ^ ν τ r = s τ ^ szT X D pos j τ := by
      intro τ
      rw [hsz τ, Finset.prod_pow_eq_pow_sum, ← Nat.cast_sum, zpow_natCast]
    rw [← e1, e2, evFr_scalar_of_wtPol D ν Q hQ s hs]
    simp only [e3]
  rw [hD, ← map_mul]
  congr 1
  rw [Finset.sum_mul]
  calc _ = ∑ α ∈ (polDY D s Q (N' := D.R.N (j + 1))).support, (∏ τ, (f' τ).det ^ (-(wT X D pos j τ))) *
        (GL3Theta.evFr D (AddMonoidAlgebra.coeff (polDY D s Q (N' := D.R.N (j + 1))) α) f' * ∏ k ∈ α.support, d k.1 k.2.2 k.2.1 ^ α k) := by
        refine Finset.sum_congr rfl fun α _ => ?_
        rw [← mul_assoc, ← hval α]
        ring
    _ = _ := by rw [← Finset.mul_sum, hP, mul_assoc]

end GlobalTheory.TwV.DelA

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.TransportedPolynomialComplexPointEvaluationStatement

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.transportedPolynomial_complexPoint_evaluation : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (j : ℕ) (hN : RankTie X D j) (ν : D.what₂.Tau → Fin (D.R.N j) → ℕ), NuIs X D pos j ν → ∀ (Q : MvPolynomial (GL3Theta.FrV D (D.R.N j)) ℂ), Q ∈ WtPol ℂ ν → ∀ (s : D.what₂.Tau → ℂ), (∀ τ, s τ ≠ 0) → ∀ (d : D.what₂.Tau → Matrix (Fin (D.R.N j)) (Fin (D.R.N (j + 1))) ℂ) (f' : D.what₂.Tau → Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) ℂ), (∀ τ, (f' τ).det ≠ 0) → evD X D pos ι hN d f' (trDY X Kc j D (eIdx X D pos j hN) (phi0 X D pos ι j) (polDY D s Q (N' := D.R.N (j + 1)))) * ι (∏ τ, (zT X D pos f' τ).det ^ eT X D pos (j + 1) τ) = ι ((∏ τ, (f' τ).det ^ (-(wT X D pos j τ))) * (∏ τ, s τ ^ szT X D pos j τ) * GL3Theta.evFr D Q (dfr X D hN d f')) := by
  first | exact @GlobalTheory.TwV.DelA.evD_trDY_polDY | exact GlobalTheory.TwV.DelA.evD_trDY_polDY | (intros; apply GlobalTheory.TwV.DelA.evD_trDY_polDY <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.DetTwistedFrameOperatorIdentityDenominator

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

theorem det_zT_ne_zero {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)
    {n : ℕ} (f : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (hf : ∀ τ, (f τ).det ≠ 0) (τ : D.what₂.Tau) :
    (zT X D pos f τ).det ≠ 0 := by
  unfold zT
  split_ifs
  · have hu : IsUnit (f τ).det := isUnit_iff_ne_zero.mpr (hf τ)
    have e : ((f τ)⁻¹).transpose.submatrix id Fin.rev = ((f τ)⁻¹).transpose.submatrix id (Fin.revPerm : Equiv.Perm (Fin n)) := rfl
    rw [e, Matrix.det_permute', Matrix.det_transpose]
    refine mul_ne_zero (by simp [Units.ne_zero]) ?_
    intro h0
    have := Matrix.det_nonsing_inv_mul_det (f τ) hu
    rw [h0, zero_mul] at this
    exact zero_ne_one this
  · exact hf τ

theorem opId_denom : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (j : ℕ) (hN : RankTie X D j) (ν : D.what₂.Tau → Fin (D.R.N j) → ℕ), NuIs X D pos j ν → ∀ (Q : MvPolynomial (GL3Theta.FrV D (D.R.N j)) ℂ), Q ∈ WtPol ℂ ν → ∀ (Gc : XR (X.Pj j) ℂ) (G : (X.Pj j).Xsp), Realises X D pos j (rkS X D hN) (wT X D pos j) Q Gc → MvPolynomial.map (algebraMap X.G.Kf Kc) G = MvPolynomial.map ι Gc → ∀ (s : D.what₂.Tau → ℂ), (∀ τ, s τ ≠ 0) → subD X Kc j G * numD X Kc j = denD X Kc j * (cD X Kc j (ι (cOp X D pos j s)) * trDY X Kc j D (eIdx X D pos j hN) (phi0 X D pos ι j) (polDY D s Q (N' := D.R.N (j + 1)))) := by
  intro p _ X D pos Kc _ _ ι j hN ν hν Q hQ Gc G hR hG s hs
  apply sub_eq_zero.mp
  apply GlobalTheory.T.symbolFramePolynomial_eq_zero_of_generic_vanish X D pos Kc ι j hN
  intro d f' hf hdf
  have hZ : ι (∏ τ, (zT X D pos f' τ).det ^ eT X D pos (j + 1) τ) ≠ 0 := by
    rw [map_ne_zero]
    exact Finset.prod_ne_zero_iff.mpr fun τ _ => zpow_ne_zero _ (det_zT_ne_zero X D pos f' hf τ)
  have hL := GlobalTheory.T.operatorIdentity_leftSide_complexPoint X D pos Kc ι j hN ν hν Q hQ Gc G hR hG d f' hf hdf
  have hRr := GlobalTheory.T.transportedPolynomial_complexPoint_evaluation X D pos Kc ι j hN ν hν Q hQ s hs d f' hf
  have hc : evD X D pos ι hN d f' (cD X Kc j (ι (cOp X D pos j s))) = ι (cOp X D pos j s) := by
    simp [evD, cD]
  have hS : (∏ τ, s τ ^ (-(szT X D pos j τ))) * ∏ τ, s τ ^ szT X D pos j τ = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun τ _ => by rw [zpow_neg, inv_mul_cancel₀ (zpow_ne_zero _ (hs τ))]
  rw [map_sub, sub_eq_zero]
  apply mul_right_cancel₀ hZ
  rw [hL, (evD X D pos ι hN d f').map_mul (denD X Kc j), (evD X D pos ι hN d f').map_mul (cD X Kc j _), hc, mul_assoc ((evD X D pos ι hN d f') (denD X Kc j)), mul_assoc (ι (cOp X D pos j s)), hRr, ← ι.map_mul]
  congr 2
  unfold cOp
  linear_combination (-(sgO X D pos j * (∏ τ, (f' τ).det ^ (-(wT X D pos j τ))) * GL3Theta.evFr D Q (dfr X D hN d f'))) * hS

end GlobalTheory.TwV.DelA
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.DetTwistedFrameOperatorIdentityDenominatorStatement

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.detTwistedFrame_operatorIdentity_denominator : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (j : ℕ) (hN : RankTie X D j) (ν : D.what₂.Tau → Fin (D.R.N j) → ℕ), NuIs X D pos j ν → ∀ (Q : MvPolynomial (GL3Theta.FrV D (D.R.N j)) ℂ), Q ∈ WtPol ℂ ν → ∀ (Gc : XR (X.Pj j) ℂ) (G : (X.Pj j).Xsp), Realises X D pos j (rkS X D hN) (wT X D pos j) Q Gc → MvPolynomial.map (algebraMap X.G.Kf Kc) G = MvPolynomial.map ι Gc → ∀ (s : D.what₂.Tau → ℂ), (∀ τ, s τ ≠ 0) → subD X Kc j G * numD X Kc j = denD X Kc j * (cD X Kc j (ι (cOp X D pos j s)) * trDY X Kc j D (eIdx X D pos j hN) (phi0 X D pos ι j) (polDY D s Q (N' := D.R.N (j + 1)))) := by
  first | exact @GlobalTheory.TwV.DelA.opId_denom | exact GlobalTheory.TwV.DelA.opId_denom | (intros; apply GlobalTheory.TwV.DelA.opId_denom <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.OperatorPolynomialOfRealisingValue

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

theorem trDY_smul {p : ℕ} [Fact p.Prime] (X : Sys p) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (j : ℕ) (D : D7)
    {N N' : ℕ} {ι : ℂ →+* Kc} (e : GL3Theta.Idx D N N' → X.ZA j)
    (Φ₀ : MvPolynomial (GL3Theta.FrV D N') ℂ →ₛₗ[ι] XspC (X.Pj (j + 1)) Kc)
    (R : MvPolynomial (GL3Theta.Idx D N N') (MvPolynomial (GL3Theta.FrV D N') ℂ)) (r : ℂ) :
    trDY X Kc j D e Φ₀ (r • R) = ι r • trDY X Kc j D e Φ₀ R := by
  unfold trDY
  rw [Finset.smul_sum, Finset.sum_subset MvPolynomial.support_smul]
  · refine Finset.sum_congr rfl fun α _ => ?_
    rw [MvPolynomial.coeff_smul, LinearMap.map_smulₛₗ, MvPolynomial.smul_monomial]
  · intro α _ h
    rw [MvPolynomial.notMem_support_iff.1 h, map_zero, MvPolynomial.monomial_zero]

theorem polDY_smul (D : D7) {N N' : ℕ} (s : D.what₂.Tau → ℂ) (Q : MvPolynomial (GL3Theta.FrV D N) ℂ) (r : ℂ) :
    polDY D s (r • Q) (N' := N') = r • polDY D s Q (N' := N') := by
  unfold polDY
  exact map_smul _ r Q

theorem polDel_realises : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (j : ℕ) (hN : RankTie X D j) (ν : D.what₂.Tau → Fin (D.R.N j) → ℕ), NuIs X D pos j ν → ∀ (Q : MvPolynomial (GL3Theta.FrV D (D.R.N j)) ℂ), Q ∈ WtPol ℂ ν → ∀ (r : ℂ) (Gc : XR (X.Pj j) ℂ) (G : (X.Pj j).Xsp), Realises X D pos j (rkS X D hN) (wT X D pos j) (r • Q) Gc → MvPolynomial.map (algebraMap X.G.Kf Kc) G = MvPolynomial.map ι Gc → ∀ (s : D.what₂.Tau → ℂ), (∀ τ, s τ ≠ 0) → GoodG X Kc j G ∧ OddDeg X j G ∧ ∀ n, AddMonoidAlgebra.coeff (polDel X Kc j G) n = ι (r * cOp X D pos j s) • AddMonoidAlgebra.coeff (trDY X Kc j D (eIdx X D pos j hN) (phi0 X D pos ι j) (polDY D s Q (N' := D.R.N (j + 1)))) n := by
  intro p _ X D pos Kc _ _ ι j hN ν hν Q hQ r Gc G hR hG s hs
  have hQr : r • Q ∈ WtPol ℂ ν := Submodule.smul_mem _ r hQ
  have hop := GlobalTheory.T.detTwistedFrame_operatorIdentity_denominator X D pos Kc ι j hN ν hν (r • Q) hQr Gc G hR hG s hs
  refine ⟨⟨_, hop⟩, GlobalTheory.T.modelPolynomial_oddDegree_of_realisesFramePoly X D pos Kc ι j hN ν hν (r • Q) hQr Gc G hR hG, fun n => ?_⟩
  rw [polDel_eq X Kc j G _ hop, polDY_smul, trDY_smul, Formalism.L2.G.Pend.cD, RingHom.comp_apply,
    MvPolynomial.coeff_C_mul, ← Algebra.smul_def, MvPolynomial.coeff_smul, smul_smul, map_mul, mul_comm]

end GlobalTheory.TwV.DelA
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.OperatorPolynomialOfRealisingValueStatement

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.operatorPolynomial_of_realising_value : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (j : ℕ) (hN : RankTie X D j) (ν : D.what₂.Tau → Fin (D.R.N j) → ℕ), NuIs X D pos j ν → ∀ (Q : MvPolynomial (GL3Theta.FrV D (D.R.N j)) ℂ), Q ∈ WtPol ℂ ν → ∀ (r : ℂ) (Gc : XR (X.Pj j) ℂ) (G : (X.Pj j).Xsp), Realises X D pos j (rkS X D hN) (wT X D pos j) (r • Q) Gc → MvPolynomial.map (algebraMap X.G.Kf Kc) G = MvPolynomial.map ι Gc → ∀ (s : D.what₂.Tau → ℂ), (∀ τ, s τ ≠ 0) → GoodG X Kc j G ∧ OddDeg X j G ∧ ∀ n, AddMonoidAlgebra.coeff (polDel X Kc j G) n = ι (r * cOp X D pos j s) • AddMonoidAlgebra.coeff (trDY X Kc j D (eIdx X D pos j hN) (phi0 X D pos ι j) (polDY D s Q (N' := D.R.N (j + 1)))) n := by
  first | exact @GlobalTheory.TwV.DelA.polDel_realises | exact GlobalTheory.TwV.DelA.polDel_realises | (intros; apply GlobalTheory.TwV.DelA.polDel_realises <;> assumption)
end
end
