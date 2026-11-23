module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAlgebraicDatumThetaTransformEqStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPureTensorO
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasDerivAtHeisenbergOpArchimedeanSumRealPlacesStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasDerivAtThetaSumArchimedeanHeisenbergLineStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergDerivativeMemFockAlgebraicThetaVectors
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchrodingerThetaDatumHeisenbergOrientedStatement
import Mathlib.RingTheory.PiTensorProduct
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSchrodingerThetaDatumAddAdelicSchwartz
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPlaceHeisenbergDerivThetaTransformAlgebraicD
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaTransformGaussianVacuumIsFiniteDatumStatement
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergDerivativeMemFockAlgebraicThetaVectorsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

theorem _root_.GlobalTheory.T.heisenberg_derivative_mem_fockAlgebraicThetaVectors : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X), ∀ f ∈ algF ψ θ ε A B, ∀ (τ : D.what₂.Tau) (z : Matrix (Fin X.rank) (Fin S.rank) ℂ),
      dRho (heisO ψ (sgn ε S) X) θ τ z f ∈ algF ψ θ ε A B := by
  first | exact @GlobalTheory.SquareComm.dRho_mem_algF | exact GlobalTheory.SquareComm.dRho_mem_algF | (intros; apply GlobalTheory.SquareComm.dRho_mem_algF <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAlgebraicVectorThetaTransformHeisenbergDer

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.SquareAgree.SchDeriv

theorem exists_mem_algF_deriv : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X) {d : ℕ} (e : Fin X.rank ≃ Fin d)
      (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig → Bs.ψ = ψ →
    ∀ (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (r s r' s' : ℕ)
      (hJ : Vs.J = (if ε then 1 else -1 : D.host.E) • S.gram) (hJW : Ws.J = D.host.xi0 • reindex e e X.gramᵀ),
      Vs.IsHerm D.sp.cm.sig Bs r s → Ws.IsSkew D.sp.cm.sig Bs r' s' →
      (∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) ∧ Vs.θ w = (if ε then 1 else -1 : ℂ) • A.cart τ ∧
        Ws.θ w = (reindex e e (B.cart τ)).map (starRingEnd ℂ)) →
    ∀ M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Vs Ws, M.IsGood Bs.ψ →
    ∀ cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X,
      (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
      ∀ (g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin S.rank × Fin d)) (φ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (Fin S.rank × Fin d → v.adicCompletion D.host.F) → ℂ),
        (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
        ∀ f ∈ algF ψ θ ε A B, IsDatum M ψ cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ) f →
        ∀ u : Matrix (Fin S.rank) (Fin d) (AE D), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) u →
        ∀ g₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin S.rank × Fin d),
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (M.heisLine Bs.ψ u) g g₁ →
        ∃ f₁ ∈ algF ψ θ ε A B, IsDatum M ψ cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g₁ φ) f₁ := by
  intro D ψ θ hθ ε S X A B d e Bs hBs hψB Vs Ws r s r' s' hJ hJW hV hW hemb M hM cS hcS g φ hφ hvac f hf hD u hu g₁ hg₁
  subst hψB
  have hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd Bs.ψ := hBs.std
  have hψ : IsStdChar D Bs.ψ (-1) := GlobalTheory.StdCharFromIsStd.isStdChar_of_isStd D Bs.ψ hstd
  have hth : ∀ Φ ∈ algF Bs.ψ θ ε A B, IsThetaFunO Bs.ψ (sgn ε S) X Φ := by
    intro Φ hΦ
    induction hΦ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, P, hf, rfl⟩ := hx
      exact GlobalTheory.GalLift.Vec.theta_pureTensorO hψ hθ _ _ _ _ hf.1 P
    | zero => exact GlobalTheory.OrientedHeis.theta_zero
    | add x y _ _ hx hy => exact GlobalTheory.OrientedHeis.theta_add hx hy
    | smul c x _ hx => exact GlobalTheory.OrientedHeis.theta_smul c hx
  have hsm : ∀ (a : AF D.host.F) (v : Matrix (Fin S.rank) (Fin d) (AE D)), cS (a • v) = a • cS v := by
    intro a v
    rw [hcS, hcS]
    ext i j
    simp only [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.smul_apply, Finset.smul_sum,
      smul_mul_assoc, id]
  have hAt : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (cS u) := by
    intro a ha
    rw [← hsm, hu a ha, map_zero]
  refine ⟨∑ τ, dRho (heisO Bs.ψ (sgn ε S) X) θ τ (compAt θ τ (cS u)) f,
    Submodule.sum_mem _ fun τ _ => GlobalTheory.T.heisenberg_derivative_mem_fockAlgebraicThetaVectors D Bs.ψ θ hψ hθ ε S X A B f hf τ _, ?_, fun u' => ?_⟩
  · exact GlobalTheory.TensUniq.pure_mem_schA g₁ φ hφ ((hvac.and hM.std).mono fun v hv => hv.1.trans hv.2)
  · have h2 := GlobalTheory.T.hasDerivAt_thetaSum_archimedeanHeisenbergLine M Bs.ψ hstd hM u hu g g₁ φ hφ hvac hg₁ u'
    have h3 := GlobalTheory.T.hasDerivAt_heisenbergOp_archimedean_sum_realPlaces D Bs.ψ θ hψ hθ (sgn ε S) X f (hth f hf) (cS u) hAt (cS u')
    have heq : (fun t : ℝ => GlobalTheory.WeilM.thetaSum D.host.F (M.co.rho Bs.ψ u' (M.heisLine Bs.ψ u t (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ)))) =
        fun t : ℝ => heisO Bs.ψ (sgn ε S) X (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • cS u) f (cS u') := by
      funext t
      have h4 := (GlobalTheory.T.schrodingerThetaDatum_heisenberg_oriented D Bs.ψ θ hθ ε S X A B e Bs hBs rfl Vs Ws r s r' s' hJ hJW hV hW hemb M hM cS hcS
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ) f hD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u)).2 u'
      rw [hsm] at h4
      exact h4
    rw [heq] at h2
    rw [h2.unique h3, Finset.sum_apply]

end GlobalTheory.SquareAgree.SchDeriv

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAlgebraicVectorThetaTransformHeisenbergDerStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

theorem _root_.GlobalTheory.T.exists_algebraicVector_thetaTransform_heisenbergDerivative : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X) {d : ℕ} (e : Fin X.rank ≃ Fin d)
      (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig → Bs.ψ = ψ →
    ∀ (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (r s r' s' : ℕ)
      (hJ : Vs.J = (if ε then 1 else -1 : D.host.E) • S.gram) (hJW : Ws.J = D.host.xi0 • reindex e e X.gramᵀ),
      Vs.IsHerm D.sp.cm.sig Bs r s → Ws.IsSkew D.sp.cm.sig Bs r' s' →
      (∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) ∧ Vs.θ w = (if ε then 1 else -1 : ℂ) • A.cart τ ∧
        Ws.θ w = (reindex e e (B.cart τ)).map (starRingEnd ℂ)) →
    ∀ M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Vs Ws, M.IsGood Bs.ψ →
    ∀ cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X,
      (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
      ∀ (g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin S.rank × Fin d)) (φ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (Fin S.rank × Fin d → v.adicCompletion D.host.F) → ℂ),
        (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
        ∀ f ∈ algF ψ θ ε A B, IsDatum M ψ cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ) f →
        ∀ u : Matrix (Fin S.rank) (Fin d) (AE D), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) u →
        ∀ g₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin S.rank × Fin d),
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (M.heisLine Bs.ψ u) g g₁ →
        ∃ f₁ ∈ algF ψ θ ε A B, IsDatum M ψ cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g₁ φ) f₁ := by
  first | exact @GlobalTheory.SquareAgree.SchDeriv.exists_mem_algF_deriv | exact GlobalTheory.SquareAgree.SchDeriv.exists_mem_algF_deriv | (intros; apply GlobalTheory.SquareAgree.SchDeriv.exists_mem_algF_deriv <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSchrodingerThetaDatumAddAdelicSchwartzStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

theorem _root_.GlobalTheory.T.isSchrodingerThetaDatum_add_adelicSchwartz : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd)
    (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → ∀ {Z : Type} [AddCommGroup Z]
    (crd : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → Z) (Φ Φ' : (Fin n × Fin d → AF F) → ℂ) (f f' : Z → ℂ),
    IsDatum M ψ crd Φ f → IsDatum M ψ crd Φ' f' → IsDatum M ψ crd (Φ + Φ') (f + f') := by
  first | exact @GlobalTheory.SquareAgree.isDatum_add | exact GlobalTheory.SquareAgree.isDatum_add | (intros; apply GlobalTheory.SquareAgree.isDatum_add <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPlaceHeisenbergDerivThetaTransformAlgebraicDStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

theorem _root_.GlobalTheory.T.realPlaceHeisenbergDeriv_thetaTransform_algebraicDatum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X) {d : ℕ} (e : Fin X.rank ≃ Fin d)
      (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig → Bs.ψ = ψ →
    ∀ (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (r s r' s' : ℕ)
      (hJ : Vs.J = (if ε then 1 else -1 : D.host.E) • S.gram) (hJW : Ws.J = D.host.xi0 • reindex e e X.gramᵀ),
      Vs.IsHerm D.sp.cm.sig Bs r s → Ws.IsSkew D.sp.cm.sig Bs r' s' →
      (∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) ∧ Vs.θ w = (if ε then 1 else -1 : ℂ) • A.cart τ ∧
        Ws.θ w = (reindex e e (B.cart τ)).map (starRingEnd ℂ)) →
    ∀ M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Vs Ws, M.IsGood Bs.ψ →
    ∀ cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X,
      (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
      ∀ ΦD ∈ algD M Bs.ψ Bs.emb, ∀ f : WO S X → ℂ, IsDatum M ψ cS ΦD f → ∀ (τ : D.what₂.Tau) (z : Matrix (Fin X.rank) (Fin S.rank) ℂ),
        ∃ ΦD' ∈ algD M Bs.ψ Bs.emb, IsDatum M ψ cS ΦD' (dRho (heisO ψ (sgn ε S) X) θ τ z f) := by
  first | exact @GlobalTheory.SquareAgree.HeisDeriv.heisDeriv_algD | exact GlobalTheory.SquareAgree.HeisDeriv.heisDeriv_algD | (intros; apply GlobalTheory.SquareAgree.HeisDeriv.heisDeriv_algD <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.AlgebraicVectorsCorrespondSchrodingerThetaMap

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.SquareAgree

theorem isDatum_zero_zero {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd)
    (ψ : AddChar (AF F) ℂ) {Z : Type} (crd : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → Z) :
    IsDatum M ψ crd 0 0 := by
  refine ⟨zero_mem _, fun u => ?_⟩
  simp [GlobalTheory.WeilM.thetaSum, GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr]

theorem isDatum_smul_smul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd)
    (ψ : AddChar (AF F) ℂ) {Z : Type} (crd : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → Z)
    {Φ : (Fin n × Fin d → AF F) → ℂ} {f : Z → ℂ} (h : IsDatum M ψ crd Φ f) (c : ℂ) :
    IsDatum M ψ crd (c • Φ) (c • f) := by
  refine ⟨Submodule.smul_mem _ _ h.1, fun u => ?_⟩
  rw [Pi.smul_apply, ← h.2 u]
  simp only [GlobalTheory.WeilM.thetaSum, GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, Pi.smul_apply, smul_eq_mul]
  rw [← tsum_mul_left]
  exact tsum_congr fun η => mul_left_comm _ _ _

theorem algVec_correspond : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X) {d : ℕ} (e : Fin X.rank ≃ Fin d)
      (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig → Bs.ψ = ψ →
    ∀ (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (r s r' s' : ℕ)
      (hJ : Vs.J = (if ε then 1 else -1 : D.host.E) • S.gram) (hJW : Ws.J = D.host.xi0 • reindex e e X.gramᵀ),
      Vs.IsHerm D.sp.cm.sig Bs r s → Ws.IsSkew D.sp.cm.sig Bs r' s' →
      (∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) ∧ Vs.θ w = (if ε then 1 else -1 : ℂ) • A.cart τ ∧
        Ws.θ w = (reindex e e (B.cart τ)).map (starRingEnd ℂ)) →
    ∀ M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Vs Ws, M.IsGood Bs.ψ →
    ∀ cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X,
      (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
      (∀ Φ ∈ algF ψ θ ε A B, ∃ ΦD ∈ algD M Bs.ψ Bs.emb, IsDatum M ψ cS ΦD Φ) ∧
      ∀ ΦD ∈ algD M Bs.ψ Bs.emb, ∃ Φ ∈ algF ψ θ ε A B, IsDatum M ψ cS ΦD Φ := by
  intro D ψ θ hθ ε S X A B d e Bs hBs hψ Vs Ws r s r' s' hJ hJW hVs hWs hcart M hM cS hcS
  have hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ := hψ ▸ hBs.std
  have hadd : ∀ {Φ Φ' : (Fin S.rank × Fin d → AF D.host.F) → ℂ} {f f' : WO S X → ℂ},
      IsDatum M ψ cS Φ f → IsDatum M ψ cS Φ' f' → IsDatum M ψ cS (Φ + Φ') (f + f') :=
    fun h h' => GlobalTheory.T.isSchrodingerThetaDatum_add_adelicSchwartz M ψ hstd cS _ _ _ _ h h'

  set Aop := aPlusAll (heisO ψ (sgn ε S) X) θ (fun τ => cplxO ((frSgn ε A).cart τ) (B.cart τ)) A.onb B.onb with hAop
  have hfock : ∀ f P, fockF ψ θ ε A B f P = pureTensorL Aop f P := fun f P => rfl
  have step : ∀ g : WO S X → ℂ, (∃ ΦD ∈ algD M Bs.ψ Bs.emb, IsDatum M ψ cS ΦD g) →
      ∀ k, ∃ ΦD ∈ algD M Bs.ψ Bs.emb, IsDatum M ψ cS ΦD (Aop k g) := by
    rintro g ⟨ΦD, hD, hd⟩ k
    obtain ⟨a, ha, h1⟩ := GlobalTheory.T.realPlaceHeisenbergDeriv_thetaTransform_algebraicDatum D ψ θ hθ ε S X A B e Bs hBs hψ Vs Ws r s r' s' hJ hJW hVs hWs hcart M hM cS hcS ΦD hD g hd k.1
      (unitMap (A.onb k.1) (B.onb k.1) k.2.1 k.2.2)
    obtain ⟨b, hb, h2⟩ := GlobalTheory.T.realPlaceHeisenbergDeriv_thetaTransform_algebraicDatum D ψ θ hθ ε S X A B e Bs hBs hψ Vs Ws r s r' s' hJ hJW hVs hWs hcart M hM cS hcS ΦD hD g hd k.1
      (cplxO ((frSgn ε A).cart k.1) (B.cart k.1) (unitMap (A.onb k.1) (B.onb k.1) k.2.1 k.2.2))
    refine ⟨((fockScale D k.1 : ℂ)⁻¹) • (a + (-Complex.I) • b),
      Submodule.smul_mem _ _ (add_mem ha (Submodule.smul_mem _ _ hb)), ?_⟩
    have e1 := isDatum_smul_smul M ψ cS (hadd h1 (isDatum_smul_smul M ψ cS h2 (-Complex.I))) ((fockScale D k.1 : ℂ)⁻¹)
    convert e1 using 1
    simp only [hAop, aPlusAll, aPlus, crea, sub_eq_add_neg, neg_smul]
  have gen : ∀ f, IsFinF ψ θ ε A B f → ∀ P, ∃ ΦD ∈ algD M Bs.ψ Bs.emb, IsDatum M ψ cS ΦD (fockF ψ θ ε A B f P) := by
    intro f hf P
    have h0 := GlobalTheory.T.exists_algebraicDatum_thetaTransform_eq D ψ θ hθ ε S X A B e Bs hBs hψ Vs Ws r s r' s' hJ hJW hVs hWs hcart M hM cS hcS f hf
    have hl : ∀ l : List (FVar D X.rank S.rank), ∃ ΦD ∈ algD M Bs.ψ Bs.emb,
        IsDatum M ψ cS ΦD (l.foldr (fun i g => Aop i g) f) := by
      intro l
      induction l with
      | nil => exact h0
      | cons k l ih => exact step _ ih k
    rw [hfock]
    induction P using MvPolynomial.induction_on' with
    | monomial u a =>
      have em : MvPolynomial.monomial u a = a • MvPolynomial.basisMonomials (FVar D X.rank S.rank) ℂ u := by
        rw [MvPolynomial.coe_basisMonomials, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
      obtain ⟨ΦD, hD, hd⟩ := hl (Multiset.toList (Finsupp.toMultiset u))
      refine ⟨a • ΦD, Submodule.smul_mem _ _ hD, ?_⟩
      rw [em, map_smul]
      unfold pureTensorL
      rw [Module.Basis.constr_basis]
      exact isDatum_smul_smul M ψ cS hd a
    | add p q hp hq =>
      obtain ⟨a, ha, h1⟩ := hp
      obtain ⟨b, hb, h2⟩ := hq
      exact ⟨a + b, add_mem ha hb, by rw [map_add (f := _)]; exact hadd h1 h2⟩
  have fin_mem : ∀ f, IsFinF ψ θ ε A B f → f ∈ algF ψ θ ε A B := by
    intro f hf
    refine Submodule.subset_span ⟨f, 1, hf, ?_⟩
    have e1 : (1 : MvPolynomial (FVar D X.rank S.rank) ℂ) = MvPolynomial.basisMonomials (FVar D X.rank S.rank) ℂ 0 := by
      rw [MvPolynomial.coe_basisMonomials]; rfl
    rw [hfock, e1]
    unfold pureTensorL
    rw [Module.Basis.constr_basis]
    simp [opPow]
  refine ⟨fun Φ hΦ => ?_, fun ΦD hΦD => ?_⟩
  · induction hΦ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, P, hf, rfl⟩ := hx
      exact gen f hf P
    | zero => exact ⟨0, zero_mem _, isDatum_zero_zero M ψ cS⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, h1⟩ := hx
      obtain ⟨b, hb, h2⟩ := hy
      exact ⟨a + b, add_mem ha hb, hadd h1 h2⟩
    | smul c x _ hx =>
      obtain ⟨a, ha, h1⟩ := hx
      exact ⟨c • a, Submodule.smul_mem _ _ ha, isDatum_smul_smul M ψ cS h1 c⟩
  · have pure_add : ∀ (g g' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin S.rank × Fin d)) (φ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (Fin S.rank × Fin d → v.adicCompletion D.host.F) → ℂ),
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (g + g') φ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ + GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g' φ := by
      intro g g' φ; funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, add_mul]
    have pure_smul : ∀ (c : ℂ) (g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin S.rank × Fin d)) (φ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (Fin S.rank × Fin d → v.adicCompletion D.host.F) → ℂ),
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c • g) φ = c • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ := by
      intro c g φ; funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc]
    have pure_zero : ∀ (φ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (Fin S.rank × Fin d → v.adicCompletion D.host.F) → ℂ),
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (0 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin S.rank × Fin d)) φ = 0 := by
      intro φ; funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
    let N : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin S.rank × Fin d)) :=
      { carrier := {g | ∀ (φ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (Fin S.rank × Fin d → v.adicCompletion D.host.F) → ℂ), (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
          ∃ f ∈ algF ψ θ ε A B, IsDatum M ψ cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ) f}
        zero_mem' := fun φ _ _ => ⟨0, zero_mem _, by rw [pure_zero]; exact isDatum_zero_zero M ψ cS⟩
        add_mem' := by
          intro g g' hg hg' φ h1 h2
          obtain ⟨a, ha, d1⟩ := hg φ h1 h2
          obtain ⟨b, hb, d2⟩ := hg' φ h1 h2
          exact ⟨a + b, add_mem ha hb, by rw [pure_add]; exact hadd d1 d2⟩
        smul_mem' := by
          intro c g hg φ h1 h2
          obtain ⟨a, ha, d1⟩ := hg φ h1 h2
          exact ⟨c • a, Submodule.smul_mem _ _ ha, by rw [pure_smul]; exact isDatum_smul_smul M ψ cS d1 c⟩ }
    have hPol : M.Pol Bs.ψ Bs.emb ≤ N := by
      refine sInf_le ⟨fun g₀ hg₀ φ h1 h2 => ?_, fun u hu g hg g₁ hg₁ φ h1 h2 => ?_⟩
      · obtain ⟨f, hf, hd⟩ := GlobalTheory.T.thetaTransform_gaussianVacuum_isFiniteDatum D ψ θ hθ ε S X A B e Bs hBs hψ Vs Ws r s r' s' hJ hJW hVs hWs hcart M hM cS hcS g₀ φ hg₀ h1 h2
        exact ⟨f, fin_mem f hf, hd⟩
      · obtain ⟨f, hf, hd⟩ := hg φ h1 h2
        exact GlobalTheory.T.exists_algebraicVector_thetaTransform_heisenbergDerivative D ψ θ hθ ε S X A B e Bs hBs hψ Vs Ws r s r' s' hJ hJW hVs hWs hcart M hM cS hcS g φ h1 h2 f hf hd u hu g₁ hg₁
    induction hΦD using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, φ, hg, h1, h2, rfl⟩ := hx
      exact hPol hg φ h1 h2
    | zero => exact ⟨0, zero_mem _, isDatum_zero_zero M ψ cS⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, h1⟩ := hx
      obtain ⟨b, hb, h2⟩ := hy
      exact ⟨a + b, add_mem ha hb, hadd h1 h2⟩
    | smul c x _ hx =>
      obtain ⟨a, ha, h1⟩ := hx
      exact ⟨c • a, Submodule.smul_mem _ _ ha, isDatum_smul_smul M ψ cS h1 c⟩

end GlobalTheory.SquareAgree

end
end
end
