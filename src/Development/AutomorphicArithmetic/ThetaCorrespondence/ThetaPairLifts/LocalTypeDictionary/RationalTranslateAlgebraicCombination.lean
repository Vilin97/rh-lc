module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisOSumSmul
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpecialisedUniversalSeriesEqTwistedThetaSeries
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PureTensorLIntertwine
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockJetsUnitVacuumEqScaledThetaJets
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockJetsUnitVacuumEqUnitMulPeriodJets
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacEqJets
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVectorNegHermitianSpaceConjMonomial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVacuumConjOfNegHermitianSpace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormSqMulGaussianLatticeTranslateEqShifted
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalisedThetaFamilyVectorsLatticesThetaZero
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.LatticeBasisExistsHolds
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorNegSpaceFrameChangeConjSubst
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SignedUnitaryGroupCompat
import Mathlib.Tactic.Linter.Style
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.JetsDivPeriodIsAlgebraic
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.MovedVacuumJetAlgebraicCombination
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPointActsOnVacuumByAlgebraicScalarStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumFinitePairVacuumAlgebraicCombinationStatement
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFourierIndexRationalPair

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.MovedJetNZ

open GlobalTheory.Grid (neg ofSgn)

theorem std_eq_colLat_one' {D : D7} {n : ℕ} (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (hL : ∀ y, y ∈ L ↔ ∀ i, ∃ b : 𝓞 D.host.E, (b : D.host.E) = y i) :
    (L : Set (Fin n → D.host.E)) = (colLat (1 : GL (Fin n) D.host.E) : Set _) := by
  ext y
  simp only [SetLike.mem_coe, hL, lc_mem_colLat_one, Submodule.mem_one]

theorem even_bot' {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW} (hX : IsBottomTri W i j X) : Even (A.rank * WW.rank) := by
  refine Even.mul_left ?_ _
  have h1 := hX.rank
  have h2 := hX.rank'
  have h3 := hX.is.rank
  have h4 := SqNum.ranks_exact D i j
  rw [← h3, h1, h2]
  refine ⟨SqNum.halfRank D i j - (D.R.m - (j.1 + 1)) / 2 - (D.R.m - j.1) / 2, ?_⟩
  omega

theorem vac_jet_ne_zero {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW} (hI : ∀ D, GlobalTheory.NormSum.Inp D) (hX : IsBottomTri W i j X) :
    ∃ k : FVar D WW.rank A.rank →₀ ℕ, pureTensorO W.ψ W.θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B X.vac
      (MvPolynomial.monomial k 1) 0 ≠ 0 := by
  classical
  have hIs := hX.is
  have hψ : IsStdChar D W.ψ (-1) := hIs.isVac.1
  have hθ : IsInfFam W.θ := hIs.isVac.2.inf
  set f : WO A WW → ℂ := fun w => starRingEnd ℂ (X.vac w) with hfdef
  have hf0 : IsVacO W.ψ W.θ A WW X.rA.s X.rW.s X.rA.Λ X.rW.Λ f :=
    GlobalTheory.VacConj.isVacO_conj_negSp W.ψ W.θ A WW X.rA.s X.rW.s _ _ X.vac hIs.isVac
  have hf : IsVacO W.ψ W.θ A WW X.rA.s X.rW.s (colLat (1 : GL (Fin A.rank) D.host.E) : Set _)
      (colLat (1 : GL (Fin WW.rank) D.host.E) : Set _) f := by
    rw [← std_eq_colLat_one' X.rA.Λ hX.std.2.1, ← std_eq_colLat_one' X.rW.Λ hX.stdW.2.1]
    exact hf0
  have hS : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (1 : GL (Fin A.rank) D.host.E).1 * A.gram *
      (1 : GL (Fin A.rank) D.host.E).1 = 1 := by
    rw [hX.std.1]
    simp [Formalism.UG.cT]
  have hW : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (1 : GL (Fin WW.rank) D.host.E).1 * WW.gram *
      (1 : GL (Fin WW.rank) D.host.E).1 = 1 := by
    rw [hX.stdW.1]
    simp [Formalism.UG.cT]
  have hcA : ∀ τ, IsCartanInv (gramAt D A τ) (X.rA.s τ) := fun τ => (hIs.rigA.2.2 τ).1
  have hcW : ∀ τ, IsCartanInv (gramAt D WW τ) (X.rW.s τ) := fun τ => (hIs.rigW.2.2 τ).1
  have hBA : (fun τ => (1 : GL (Fin A.rank) D.host.E).1.map (tauE D τ)) = X.rA.B := by
    funext τ
    rw [(hX.std.2.2 τ).2]
    simp
  have hBW : (fun τ => (1 : GL (Fin WW.rank) D.host.E).1.map (tauE D τ)) = X.rW.B := by
    funext τ
    rw [(hX.stdW.2.2 τ).2]
    simp
  obtain ⟨δ, hC, hδ⟩ := GlobalTheory.FunObj.exists_delta D
  obtain ⟨t0, ht0⟩ := ((hI D).t0Ex D.host.ccK δ hC).1
  obtain ⟨e0, he0, he0ne⟩ := GlobalTheory.Vacuum.exists_vacuum D D.host.ccK δ hC t0 ht0 A.rank WW.rank (even_bot' hX)
  obtain ⟨c, hc⟩ := GlobalTheory.FockPos.fock_jets_eq_unit_mul_period_jets W.ψ W.θ A WW X.rA.s X.rW.s 1 1 hS hW hcA hcW δ t0 hC hδ
    ht0 e0 he0 f hf
  obtain ⟨α, hα⟩ := GlobalTheory.NatFamily.exists_taylor_ne D he0.1.1 he0ne
  refine ⟨α, ?_⟩
  change pureTensorO W.ψ W.θ (negSp A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B X.vac (MvPolynomial.monomial α 1) 0 ≠ 0
  rw [GlobalTheory.FockConj.pureTensorO_negSp_monomial W.ψ W.θ A WW X.rA.s X.rW.s X.rA.B X.rW.B X.vac hψ hθ α 0, map_ne_zero,
    ← hBA, ← hBW, hc α, GlobalTheory.FockPos.applyAt0_monomial']
  have hprod : (α.prod fun v n => GlobalTheory.FunObj.period δ v.1 ^ n) ≠ 0 :=
    Finsupp.prod_ne_zero_iff.2 fun v _ => pow_ne_zero _ (GlobalTheory.FunObj.period_ne_zero hδ v.1)
  have hfac : (α.prod fun _ n => (n.factorial : ℂ)) ≠ 0 :=
    Finsupp.prod_ne_zero_iff.2 fun _ _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  exact mul_ne_zero c.ne_zero (mul_ne_zero hprod (mul_ne_zero hfac hα))

end GlobalTheory.MovedJetNZ

end

namespace GlobalTheory.MovedJetNZ

open GlobalTheory.Grid (neg ofSgn)

end GlobalTheory.MovedJetNZ
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.JetOfMovedVacuumNonvanishing

section

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
noncomputable section
namespace GlobalTheory.MovedJetNZ
open GlobalTheory.Grid (neg ofSgn)
end GlobalTheory.MovedJetNZ
end
namespace GlobalTheory.MovedJetNZ
open GlobalTheory.Grid (neg ofSgn)
theorem moved_vacuum_jet_ne_zero : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X → ∀ (t : T), ∀ γ ∈ Formalism.L2.Theta.GQ A, ∀ a ∈ GinfC A, ∀ γ' ∈ Formalism.L2.Theta.GQ WW, ∀ a' ∈ GinfC WW,
      γ * a ∈ GfC A → γ' * a' ∈ GfC WW →
      ∃ k : FVar D WW.rank A.rank →₀ ℕ, pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.ω t (γ, γ') X.vac) (MvPolynomial.monomial k 1) 0 ≠ 0 := by
  intro D T _ L μ₀ sc G W i j A A' WW X _ hI _ hX t γ hγ _ _ γ' hγ' _ _ _ _
  classical
  have hIs := hX.is
  have hψ : IsStdChar D W.ψ (-1) := hIs.isVac.1
  have hθ : IsInfFam W.θ := hIs.isVac.2.inf
  set om' := (X.ω t).toSgn true with hom'
  have hom := hIs.weil t
  have hsA : ∀ τ, X.rA.s τ = 1 := fun τ => (hX.std.2.2 τ).1
  have hsW : ∀ τ, X.rW.s τ = 1 := fun τ => (hX.stdW.2.2 τ).1
  have hBA : ∀ τ, X.rA.B τ = 1 := fun τ => by rw [(hX.std.2.2 τ).2]
  obtain ⟨k₀, hk₀⟩ := vac_jet_ne_zero hI hX
  by_contra hall
  push_neg at hall
  set γs := (ofSgn true A).symm γ with hγs
  have hγsQ : γs ∈ GQ (neg A) :=
    (GlobalTheory.SgnIdent.mem_GQ_sgn true A γs).2 (by rw [hγs, MulEquiv.apply_symm_apply]; exact hγ)
  have hg : X.ω t (γ, γ') X.vac = om' (γs, γ') X.vac := by
    show _ = (X.ω t) ((ofSgn true A) ((ofSgn true A).symm γ), γ') X.vac
    rw [MulEquiv.apply_symm_apply]
  simp only [hg] at hall
  have hvθ : IsThetaFunO W.ψ (neg A) WW X.vac := hIs.isVac.2.theta
  have hgθ : IsThetaFunO W.ψ (neg A) WW (om' (γs, γ') X.vac) := hom.om_pres _ _ hvθ
  have hzero : ∀ P, pureTensorO W.ψ W.θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (om' (γs, γ') X.vac) P 0 = 0 := by
    intro P

    rw [P.as_sum, map_sum, Finset.sum_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    have e : MvPolynomial.monomial k (P.coeff k) = P.coeff k • MvPolynomial.monomial k 1 := by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [e, map_smul, Pi.smul_apply, hall k, smul_zero]
  have hop := GlobalTheory.OrientedHeis.om_pureTensorO D W.ψ W.θ (neg A) WW _ _ om' hom hθ (fun τ => -X.rA.s τ) (fun τ => -X.rA.s τ)
    X.rA.B (fun τ => compAt W.θ τ (Formalism.L2.Theta.mt (neg A) γs) * X.rA.B τ) X.rW.s X.rW.s X.rW.B
    (fun τ => compAt W.θ τ (Formalism.L2.Theta.mt WW γ') * X.rW.B τ) γs γ' (fun τ => by rw [hsA]; simp) (fun τ => by rw [hsW]; simp)
    (fun τ => rfl) (fun τ => rfl) X.vac hvθ (MvPolynomial.monomial k₀ 1)
  have haut := hom.om_aut γs hγsQ γ' hγ' _ hop.1
  apply hk₀
  rw [← haut, hop.2]
  have hBW : ∀ τ, X.rW.B τ = 1 := fun τ => by rw [(hX.stdW.2.2 τ).2]
  have e1 : (fun τ => compAt W.θ τ (Formalism.L2.Theta.mt (neg A) γs) * X.rA.B τ) =
      fun τ => X.rA.B τ * compAt W.θ τ (Formalism.L2.Theta.mt (neg A) γs) := by
    funext τ; rw [hBA, Matrix.mul_one, Matrix.one_mul]
  have e2 : (fun τ => compAt W.θ τ (Formalism.L2.Theta.mt WW γ') * X.rW.B τ) =
      fun τ => X.rW.B τ * compAt W.θ τ (Formalism.L2.Theta.mt WW γ') := by
    funext τ; rw [hBW, Matrix.mul_one, Matrix.one_mul]
  have es : (fun τ => -X.rA.s τ) = fun _ => (-1 : Matrix (Fin A.rank) (Fin A.rank) ℂ) := funext fun τ => by rw [hsA]
  have et : X.rW.s = fun _ => (1 : Matrix (Fin WW.rank) (Fin WW.rank) ℂ) := funext hsW
  rw [e1, e2]
  rw [es, et] at hzero ⊢
  change pureTensorO W.ψ W.θ (negSp A) WW (fun _ => -1) (fun _ => 1) _ _ _ _ _ = _
  rw [GlobalTheory.FockNegSubst.pureTensorO_negSp_subst D W.ψ W.θ A WW hψ hθ _ _ _ _ _ hgθ]
  exact hzero _
end GlobalTheory.MovedJetNZ
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

theorem _root_.GlobalTheory.T.jet_of_moved_vacuum_nonvanishing : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X → ∀ (t : T), ∀ γ ∈ Formalism.L2.Theta.GQ A, ∀ a ∈ GinfC A, ∀ γ' ∈ Formalism.L2.Theta.GQ WW, ∀ a' ∈ GinfC WW,
      γ * a ∈ GfC A → γ' * a' ∈ GfC WW →
      ∃ k : FVar D WW.rank A.rank →₀ ℕ, pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.ω t (γ, γ') X.vac) (MvPolynomial.monomial k 1) 0 ≠ 0 := by
  first | exact @_root_.GlobalTheory.MovedJetNZ.moved_vacuum_jet_ne_zero | exact _root_.GlobalTheory.MovedJetNZ.moved_vacuum_jet_ne_zero | (intros; apply _root_.GlobalTheory.MovedJetNZ.moved_vacuum_jet_ne_zero <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.RationalVacuumEqSmulAlgebraicCombination

section

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
noncomputable section
namespace GlobalTheory.RatVacAlg
theorem rational_vacuum_eq_smul_algebraic_combination : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X → ∀ (t : T), ∀ γ ∈ Formalism.L2.Theta.GQ A, ∀ a ∈ GinfC A, ∀ γ' ∈ Formalism.L2.Theta.GQ WW, ∀ a' ∈ GinfC WW,
      γ * a ∈ GfC A → γ' * a' ∈ GfC WW →
      ∃ (κ : ℂ) (F : WO (GlobalTheory.Grid.neg A) WW → ℂ), GlobalTheory.MovedAlg.IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac F ∧
        X.ω t (γ, γ') X.vac = κ • F := by
  intro D T _ L μ₀ sc G W i j A A' WW X hP hN hL hX t γ hγ a ha γ' hγ' a' ha' hfa hfa'
  have hI := hX.is
  have hom := hI.weil t
  have cS : ∀ τ, IsCartanInv (gramAt D (GlobalTheory.Grid.neg A) τ) (-X.rA.s τ) := fun τ =>
    GlobalTheory.Grid.isCartanInv_sgn true A τ (hI.rigA.2.2 τ).1
  have cT : ∀ τ, IsCartanInv (gramAt D WW τ) (X.rW.s τ) := fun τ => (hI.rigW.2.2 τ).1
  have hsdS : IsSelfDualC (GlobalTheory.Grid.neg A) X.rA.Λ := GlobalTheory.RowTest.isSelfDualC_neg' hI.rigA.1
  have hx : (GlobalTheory.Grid.ofSgn true A).symm (γ * a) ∈ GfC (GlobalTheory.Grid.neg A) := by
    show (GlobalTheory.Grid.ofSgn true A) ((GlobalTheory.Grid.ofSgn true A).symm (γ * a)) ∈ GfC A
    rw [MulEquiv.apply_symm_apply]
    exact hfa
  obtain ⟨κ₁, F, hF, hκ₁⟩ := GlobalTheory.T.weilDatum_finite_pair_vacuum_algebraic_combination hI.isVac hsdS hI.rigW.1 cS cT hom _ hx _ hfa'
  obtain ⟨C, -, hC⟩ := GlobalTheory.T.realPoint_acts_on_vacuum_by_algebraicScalar hX t γ hγ a ha γ' hγ' a' ha' hfa hfa'
  have e1 : X.ω t (γ * a, γ' * a') X.vac = κ₁ • F := hκ₁
  have e2 : X.ω t (γ * a, γ' * a') X.vac = C • X.ω t (γ, γ') X.vac := by
    rw [show ((γ * a, γ' * a') : GA D A × GA D WW) = (γ, γ') * (a, a') from rfl, map_mul, Module.End.mul_apply, hC,
      map_smul]
  have hv : X.vac ≠ 0 := by
    intro h0
    obtain ⟨⟨p, hp⟩, hn⟩ := hI.isVac.2.norm
    have h1 := hn p hp
    simp [h0, nrm2] at h1
  have hC0 : C ≠ 0 := by
    rintro rfl
    apply hv
    have h2 := congrArg (X.ω t (a, a')⁻¹) hC
    rw [zero_smul, map_zero, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at h2
    exact h2
  refine ⟨C⁻¹ * κ₁, F, hF, ?_⟩
  rw [mul_smul, ← e1, e2, smul_smul, inv_mul_cancel₀ hC0, one_smul]
end GlobalTheory.RatVacAlg
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

theorem _root_.GlobalTheory.T.rational_vacuum_algebraic_combination : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X → ∀ (t : T), ∀ γ ∈ Formalism.L2.Theta.GQ A, ∀ a ∈ GinfC A, ∀ γ' ∈ Formalism.L2.Theta.GQ WW, ∀ a' ∈ GinfC WW,
      γ * a ∈ GfC A → γ' * a' ∈ GfC WW →
      ∃ (κ : ℂ) (F : WO (GlobalTheory.Grid.neg A) WW → ℂ), GlobalTheory.MovedAlg.IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac F ∧
        X.ω t (γ, γ') X.vac = κ • F := by
  first | exact @_root_.GlobalTheory.RatVacAlg.rational_vacuum_eq_smul_algebraic_combination | exact _root_.GlobalTheory.RatVacAlg.rational_vacuum_eq_smul_algebraic_combination | (intros; apply _root_.GlobalTheory.RatVacAlg.rational_vacuum_eq_smul_algebraic_combination <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.RationalTranslateAlgebraicCombination

section

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
noncomputable section
namespace GlobalTheory.RatMovedAlg
theorem rational_moved_scalar_algebraic : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X → ∀ (t : T), ∀ γ ∈ Formalism.L2.Theta.GQ A, ∀ a ∈ GinfC A, ∀ γ' ∈ Formalism.L2.Theta.GQ WW, ∀ a' ∈ GinfC WW,
      γ * a ∈ GfC A → γ' * a' ∈ GfC WW →
      ∀ (κ : ℂ) (F : WO (GlobalTheory.Grid.neg A) WW → ℂ), GlobalTheory.MovedAlg.IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac F →
        X.ω t (γ, γ') X.vac = κ • F → IsAlgebraic ℚ κ := by
  intro D T _ L μ₀ sc G W i j A A' WW X hP hI hL hX t γ hγ a ha γ' hγ' a' ha' h1 h2 κ F hF e
  obtain ⟨k, hk⟩ := _root_.GlobalTheory.T.jet_of_moved_vacuum_nonvanishing hP hI hL hX t γ hγ a ha γ' hγ' a' ha' h1 h2
  obtain ⟨Ω, hΩ, hJ⟩ := _root_.GlobalTheory.T.bottom_translate_jets_algebraic hP hI hL hX (Finsupp.mapDomain Prod.fst k)
  obtain ⟨n', c', k', hc', hk', he'⟩ := _root_.GlobalTheory.T.moved_vacuum_jet_algebraic_combination hP hI hL hX t γ hγ a ha γ' hγ' a' ha' h1 h2 k
  have hψ : IsStdChar D W.ψ (-1) := (hX.is.weil t).std
  have hθ : IsInfFam W.θ := hX.is.isVac.2.inf
  have hv : IsThetaFunO W.ψ (GlobalTheory.Grid.neg A) WW X.vac := hX.is.isVac.2.theta
  have h0 : heisO W.ψ (GlobalTheory.Grid.neg A) WW 0 X.vac = X.vac := by
    funext w; simp [heisO, symplOH, symplO, hO]
  have alg : ∀ x : ℂ, IsAlgebraic ℚ x ↔ x ∈ algebraicClosure ℚ ℂ := fun x => (mem_algebraicClosure_iff).symm
  have hg : IsAlgebraic ℚ (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.ω t (γ, γ') X.vac) (MvPolynomial.monomial k 1) 0 / Ω) := by
    rw [he', Finset.sum_div, alg]
    refine sum_mem fun p _ => ?_
    rw [mul_div_assoc]
    refine mul_mem ((alg _).1 (hc' p)) ((alg _).1 ?_)
    have := hJ 0 (by simp) (k' p) (hk' p)
    rwa [h0] at this
  obtain ⟨n, c, w, hc, hw, rfl⟩ := hF
  have hsum : pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (∑ p, c p • heisO W.ψ (GlobalTheory.Grid.neg A) WW (w p) X.vac) (MvPolynomial.monomial k 1) 0 =
      ∑ p, c p * pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (heisO W.ψ (GlobalTheory.Grid.neg A) WW (w p) X.vac) (MvPolynomial.monomial k 1) 0 := by
    rw [GlobalTheory.SpecFac.pureTensorO_sum hψ hθ _ _ _ _ Finset.univ c _
      (fun p _ => GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hv (w p))]
    simp [Finset.sum_apply]
  have hF' : IsAlgebraic ℚ (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (∑ p, c p • heisO W.ψ (GlobalTheory.Grid.neg A) WW (w p) X.vac) (MvPolynomial.monomial k 1) 0 / Ω) := by
    rw [hsum, Finset.sum_div, alg]
    refine sum_mem fun p _ => ?_
    rw [mul_div_assoc]
    exact mul_mem ((alg _).1 (hc p)) ((alg _).1 (hJ (w p) (hw p) k rfl))
  have hsm : pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.ω t (γ, γ') X.vac) (MvPolynomial.monomial k 1) 0 = κ * pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (∑ p, c p • heisO W.ψ (GlobalTheory.Grid.neg A) WW (w p) X.vac) (MvPolynomial.monomial k 1) 0 := by
    rw [e, GlobalTheory.FiniteFock.pureTensorO_smul]; rfl
  have hne : pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (∑ p, c p • heisO W.ψ (GlobalTheory.Grid.neg A) WW (w p) X.vac) (MvPolynomial.monomial k 1) 0 ≠ 0 := by
    intro h0'; rw [h0', mul_zero] at hsm; exact hk hsm
  have hκ : κ = (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.ω t (γ, γ') X.vac) (MvPolynomial.monomial k 1) 0 / Ω) / (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (∑ p, c p • heisO W.ψ (GlobalTheory.Grid.neg A) WW (w p) X.vac) (MvPolynomial.monomial k 1) 0 / Ω) := by
    rw [hsm]; field_simp
  rw [hκ, alg]
  exact div_mem ((alg _).1 hg) ((alg _).1 hF')
theorem rational_translate_algebraic_combination : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X → ∀ (t : T), ∀ γ ∈ Formalism.L2.Theta.GQ A, ∀ a ∈ GinfC A, ∀ γ' ∈ Formalism.L2.Theta.GQ WW, ∀ a' ∈ GinfC WW,
      γ * a ∈ GfC A → γ' * a' ∈ GfC WW →
      ∃ (n : ℕ) (c : Fin n → ℂ) (w : Fin n → WO (GlobalTheory.Grid.neg A) WW), (∀ p, IsAlgebraic ℚ (c p)) ∧
        (∀ p, (w p).map (infPart D) = 0) ∧
        X.ω t (γ, γ') X.vac = ∑ p, c p • heisO W.ψ (GlobalTheory.Grid.neg A) WW (w p) X.vac := by
  intro D T _ L μ₀ sc G W i j A A' WW X hP hI hL hX t γ hγ a ha γ' hγ' a' ha' h1 h2
  obtain ⟨κ, F, hF, e⟩ := _root_.GlobalTheory.T.rational_vacuum_algebraic_combination hP hI hL hX t γ hγ a ha γ' hγ' a' ha' h1 h2
  have hk := _root_.GlobalTheory.RatMovedAlg.rational_moved_scalar_algebraic hP hI hL hX t γ hγ a ha γ' hγ' a' ha' h1 h2 κ F hF e
  obtain ⟨n, c, w, hc, hw, he⟩ := hF.smul hk
  exact ⟨n, c, w, hc, hw, e.trans he⟩
end GlobalTheory.RatMovedAlg
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

theorem _root_.GlobalTheory.T.rationally_moved_vector_algebraic : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X → ∀ (t : T), ∀ γ ∈ Formalism.L2.Theta.GQ A, ∀ a ∈ GinfC A, ∀ γ' ∈ Formalism.L2.Theta.GQ WW, ∀ a' ∈ GinfC WW,
      γ * a ∈ GfC A → γ' * a' ∈ GfC WW →
      ∃ (n : ℕ) (c : Fin n → ℂ) (w : Fin n → WO (GlobalTheory.Grid.neg A) WW), (∀ p, IsAlgebraic ℚ (c p)) ∧
        (∀ p, (w p).map (infPart D) = 0) ∧
        X.ω t (γ, γ') X.vac = ∑ p, c p • heisO W.ψ (GlobalTheory.Grid.neg A) WW (w p) X.vac := by
  first | exact @_root_.GlobalTheory.RatMovedAlg.rational_translate_algebraic_combination | exact _root_.GlobalTheory.RatMovedAlg.rational_translate_algebraic_combination | (intros; apply _root_.GlobalTheory.RatMovedAlg.rational_translate_algebraic_combination <;> assumption)
end
end
end
