module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.DifferentiableOfChar
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CentralEigenThetaIsFockVectorBoundedDegree
public import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
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
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsFinCombSingleZero
public import Formalism.RealPlaceAnalysis.Complexify
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.LocalRingCardinality.DataHost
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisOfRegularForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStableComplBot
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.LiftsCart
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldingLevelsAndStepsHaarMeasuresExist
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorSourceRealPointCommuteHeisenbergComb
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumHeisOPureTensorO
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCoordLatticeOfSelfDualFrame
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OrientedThetaEqFiniteHeisenbergTranslatesVacua
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt

-- Source module: Development.AbelianVarietyTheory.BlockTheory.SiegelEisenstein.UnimodularTower

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChainOnto
open scoped TensorProduct InnerProductSpace ComplexConjugate

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnimodularTower

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev Fn (D : D7) (u : D.what₂.Word) (i : ℕ) : Type := Formalism.MainNotions.product_first_zeroth_parts.Fn D u i

abbrev Fm (D : D7) (u : D.what₂.Word) (i : ℕ) : Submodule ℂ (Fn D u i) := (D.fm u).Fi i

abbrev Ram (D : D7) (u : D.what₂.Word) (i : ℕ) : Submodule ℂ (Fn D u i) := Formalism.MainNotions.product_first_zeroth_parts.MramI D u i

abbrev Eps (D : D7) (u : D.what₂.Word) : Type := ∀ v : (D.mem u).A.vT, ((D.mem u).A.Fv v)ˣ

def colPar (D : D7) (u : D.what₂.Word) (j : ℕ) : D.what₂.Tau → SPar :=
  (TPar.ofWord D u (Ptw D).eta (Ptw D).eta_half).Xpar j

def dcos {V : HSp D} (R : Subgroup (GA D V)) (b : GA D V) (K : Subgroup (GA D V)) : Set (GA D V) :=
  {h | ∃ r ∈ R, ∃ x ∈ GinfC V, ∃ κ ∈ K, h = r * x * b * κ}

structure RowOn (V : HSp D) where
  par : D.what₂.Tau → SPar
  M : DSModel V par
  Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)
  β : GL (Fin V.rank) (Lev.EAf D)
  L : LevDat D.host.E ℂ V.rank
  ν : Measure (GA D V)
  fd : Set (GA D V)

abbrev RowOn.st {V : HSp D} (r : RowOn V) : PiLocalization₂ D := ⟨V, r.par, r.M, r.Λ, r.β, r.L, r.ν, r.fd⟩

structure ColOn (c : Com D) (u : D.what₂.Word) (X : HSp D) (j : ℕ) where
  M : DSModel X (colPar D u j)
  K : Subgroup (GA D X)
  a : Fm D u j →ₗ[ℂ] MultT c.θ M (K : Set (GA D X)) (fun _ => 1)

variable {c : Com D} {u : D.what₂.Word}

structure ColStep {X X' : HSp D} {j : ℕ} (A : ColOn c u X j) (A' : ColOn c u X' (j + 1)) where
  om : Om X X'
  f : WO X X' → ℂ
  it : PolF D X'.rank X.rank →ₗ[ℂ] SmT A.M →ₗ[ℂ] SmT A'.M

section ColStep

variable {X X' : HSp D} {j : ℕ} {A : ColOn c u X j} {A' : ColOn c u X' (j + 1)}

end ColStep

structure Node (c : Com D) (u : D.what₂.Word) (ρ j : ℕ) where
  B : BesLev D ρ
  row : RowOn B.V
  col : ColOn c u B.A j
  b : GA D B.V

structure Dbl {σ j : ℕ} (N : Node c u (σ + 1) j) (N' : Node c u σ (j + 1 + 1)) where
  J : JacLev D (σ + 1)
  row : RowOn J.W
  col : ColOn c u J.W₀ (j + 1)
  b : GA D J.W
  s₁ : StepBF c.ψ N.B J
  s₂ : StepFB c.ψ J N'.B
  l : Link N.B N'.B.L N'.B.ζ
  vL : VolM D N'.B.L.rank J.W₀.rank
  p₁ : ChainOnto.Step c N.row.st row.st
  p₂ : ChainOnto.Step c row.st N'.row.st
  k₁ : ColStep N.col col
  k₂ : ColStep col N'.col
  ε : Eps D u

section Dbl

variable {σ j : ℕ} {N : Node c u (σ + 1) j} {N' : Node c u σ (j + 1 + 1)}

end Dbl

structure Fin2 {j : ℕ} (N : Node c u 0 j) {T : HSp D} (top : RowOn T) where
  t : Last c.ψ T N.B
  row : RowOn t.J.W
  col₁ : ColOn c u t.J.W (j + 1)
  X : HSp D
  L : HSp D
  o : OrthDec X T L
  col₂ : ColOn c u X (j + 1 + 1)
  p₁ : ChainOnto.Step c N.row.st row.st
  p₂ : ChainOnto.Step c row.st top.st
  k₁ : ColStep N.col col₁
  k₂ : ColStep col₁ col₂
  ε : Eps D u
  ι : (D.mem u).P.Mt ≃ₗ[ℂ] top.st.CC c
  br : SmT col₂.M →ₗ[ℂ] SmT top.M →ₗ[ℂ] ℂ

section Fin2

variable {j : ℕ} {N : Node c u 0 j} {T : HSp D} {top : RowOn T}

end Fin2

end GlobalTheory.IndefiniteRowSideFullHecke.UnimodularTower

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalDefiniteSpaceH

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR.Mult Formalism.UG GlobalTheory.SphPar GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefTransfer
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem signs_pos_of_frame_gram_posdef {r : ℕ} (ε : Fin r → Bool) (fr G : Matrix (Fin r) (Fin r) ℂ)
    (h : fr.conjTranspose * Formalism.REAL.Jm ε * fr = G) (hs : Formalism.UG.HasSignature G r 0) :
    ∀ i, ε i = true := by
  obtain ⟨e, P, hP⟩ := hs
  have hcT : Formalism.UG.cT (starRingEnd ℂ) (P : Matrix (Fin r ⊕ Fin 0) (Fin r ⊕ Fin 0) ℂ) =
      (P : Matrix (Fin r ⊕ Fin 0) (Fin r ⊕ Fin 0) ℂ).conjTranspose := by
    ext i j; simp [Formalism.UG.cT, Matrix.conjTranspose_apply]
  have hJ0 : Formalism.UG.Jpq r 0 = 1 := by
    ext i j
    rcases i with i | i
    · rcases j with j | j
      · simp [Formalism.UG.Jpq, Matrix.one_apply]
      · exact j.elim0
    · exact i.elim0
  rw [hcT, hJ0] at hP
  set P' : Matrix (Fin r) (Fin r) ℂ := (P : Matrix (Fin r ⊕ Fin 0) (Fin r ⊕ Fin 0) ℂ).submatrix e e with hP'
  have h1 : P'.conjTranspose * G * P' = 1 := by
    have := congrArg (fun A : Matrix (Fin r ⊕ Fin 0) (Fin r ⊕ Fin 0) ℂ => A.submatrix e e) hP
    simp only [Matrix.reindex_apply] at this
    rw [← Matrix.submatrix_mul_equiv _ _ _ e _, ← Matrix.submatrix_mul_equiv _ _ _ e _] at this
    simpa [Matrix.submatrix_submatrix, Matrix.conjTranspose_submatrix, hP'] using this
  set Q := fr * P' with hQ
  have h2 : (Q.conjTranspose * Formalism.REAL.Jm ε) * Q = 1 := by
    rw [← h1, ← h]; simp only [hQ, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have h3 : Q * (Q.conjTranspose * Formalism.REAL.Jm ε) = 1 := mul_eq_one_comm.mp h2
  have h4 : Q * Q.conjTranspose = Formalism.REAL.Jm ε := by
    have := congrArg (· * Formalism.REAL.Jm ε) h3
    simpa [Matrix.mul_assoc, Formalism.REAL.Jm_mul_self] using this
  intro i
  by_contra hi
  have hi' : ε i = false := by simpa using hi
  have h5 := congrFun (congrFun h4 i) i
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Formalism.REAL.Jm, Matrix.diagonal_apply_eq, hi'] at h5
  have h6 := congrArg Complex.re h5
  simp only [Complex.re_sum, Bool.false_eq_true, if_false, Complex.neg_re, Complex.one_re] at h6
  have h7 : ∀ k, 0 ≤ (Q i k * star (Q i k)).re := by
    intro k
    rw [Complex.star_def, Complex.mul_conj]
    simp [Complex.normSq_nonneg]
  have := Finset.sum_nonneg (fun k (_ : k ∈ Finset.univ) => h7 k)
  linarith

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RepresentsOfLink

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.IndefiniteRowSideFullHecke.UnimodularTower
open GlobalTheory.ChainOnto (Com PiLocalization₂)
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSawCompare

variable {D : D7} {u : D.what₂.Word}

theorem defSp_is {V : HSp D} (hs : V.SigOK) (hp : V.IsPosDef) {S : D.what₂.Tau → SPar} (M : DSModel V S) (x : DefSp V)
    (h1 : x.s = cart M) (h2 : x.B = onb M) (h3 : IsSelfDualC V x.L) : x.Is := by
  have hs' : ∀ τ, Formalism.UG.HasSignature (gramAt D V τ) V.rank 0 := fun τ => by
    have := hs (tauE D τ)
    rw [hp (tauE D τ)] at this
    exact this
  have hJ : ∀ τ, Formalism.REAL.Jm (M.ε τ) = 1 := fun τ => by
    have := signs_pos_of_frame_gram_posdef (M.ε τ) (M.fr τ) _ (M.fr_gram τ) (hs' τ)
    unfold Formalism.REAL.Jm; simp [this]
  have hd := fun τ => (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have hc : ∀ τ, x.s τ = 1 := fun τ => by rw [h1, cart, hJ, Matrix.mul_one, Matrix.nonsing_inv_mul _ (hd τ)]
  refine ⟨hs, Inh.coCpt_of_isDefinite hs fun τ => Or.inl (hp τ), fun τ => ?_, fun τ => Or.inl (hc τ), fun τ => ?_, h3⟩
  · rw [hc]
    exact ⟨by simp, by simp, by simpa using Formalism.IndefR.Fin.Lifts.posDef_of_sig _ (hs' τ)⟩
  · refine ⟨V.rank, fun _ => 1, fun a => Or.inl ⟨rfl, a.2⟩, ?_, by simp [hc]⟩
    rw [h2, onb, ← M.fr_gram τ, hJ, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.conjTranspose_mul,
      Matrix.mul_nonsing_inv _ (hd τ), Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_nonsing_inv _ (hd τ)]
    simp

abbrev Live (D : D7) (u : D.what₂.Word) : Type := ∀ j, Submodule ℂ (Fn D u j)

variable (W : Live D u) {c : Com D}

section Dbl

variable {σ j : ℕ} {N : Node c u (σ + 1) j} {N' : Node c u σ (j + 1 + 1)} (d : Dbl N N')

end Dbl

section Fin2

variable {j : ℕ} {N : Node c u 0 j} {T : HSp D} {top : RowOn T} (e : Fin2 N top)

end Fin2

variable {W}

section Step

variable {X X' : HSp D} {j : ℕ} {A : ColOn c u X j} {A' : ColOn c u X' (j + 1)} {k : ColStep A A'} {vol : Vol X}

end Step

end GlobalTheory.SeeSawCompare

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.CentreEigenThetaFunctionFiniteSumFockPolynomials

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.CenFockGen

open GlobalTheory.SeeSaw

theorem isFockVacAt_heisO_fin {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {θ : InfFam D}
    (hθ : IsInfFam θ) {S T : HSp D} {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (τ : D.what₂.Tau)
    (J : Matrix (Fin T.rank) (Fin S.rank) ℂ → Matrix (Fin T.rank) (Fin S.rank) ℂ) (hv : IsFockVacAt (heisO ψ S T) θ τ J f)
    {u : WO S T} (hu : u.map (infPart D) = 0) : IsFockVacAt (heisO ψ S T) θ τ J (heisO ψ S T u f) := by
  have h := GlobalTheory.FockTranslate.isFockVacAt_sum D ψ θ S T hψ.1 hθ f hf τ J hv Unit Finset.univ (fun _ => u) (fun _ => 1)
    (fun _ _ => hu)
  simpa using h

theorem heisO_pureTensorO_fin {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {θ : InfFam D}
    (hθ : IsInfFam θ) {S T : HSp D} (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) {u : WO S T} (hu : u.map (infPart D) = 0)
    {x : WO S T → ℂ} (hx : IsThetaFunO ψ S T x) (P : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    heisO ψ S T u (pureTensorO ψ θ S T sS sT BS BT x P) = pureTensorO ψ θ S T sS sT BS BT (heisO ψ S T u x) P := by
  classical
  have h := GlobalTheory.FiniteHeisComb.sum_heisO_pureTensorO D ψ θ S T hψ hθ sS BS sT BT (Finsupp.single u 1)
    (fun v hv => by
      rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at hv
      rw [hv]; exact hu) x hx P
  simpa [Finsupp.sum_single_index] using h

theorem comb_smul' {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} (c : WO S T →₀ ℂ) (r : ℂ) (f : WO S T → ℂ) :
    comb ψ S T c (r • f) = r • comb ψ S T c f := by
  funext w
  simp only [comb, heisO, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem theta_comb {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {c : WO S T →₀ ℂ}
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S T (comb ψ S T c f) :=
  Finset.sum_induction _ (IsThetaFunO ψ S T) (fun _ _ => GlobalTheory.OrientedHeis.theta_add) GlobalTheory.OrientedHeis.theta_zero
    fun u _ => GlobalTheory.OrientedHeis.theta_smul _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf u)

theorem exists_defData {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : GlobalTheory.Grid.Node D} {νS νT : ℕ}
    {PS PT : D.what₂.Tau → SPar} (hS : S.Is νS 0 PS) (hT : T.Is νT 0 PT) {a : GlobalTheory.Grid.ArrT S T}
    {χS χT : (AE D)ˣ →* Circle} (ha : a.Is ψ θ false χS χT) :
    ∃ (x : DefSp S.V) (y : DefSp T.V) (k : KerDat S.V T.V), x.Is ∧ y.Is ∧ k.Is ψ θ x y ∧ x.s = cart S.M ∧
      y.s = cart T.M ∧ x.B = onb S.M ∧ y.B = onb T.M ∧ k.om = a.ω ∧ k.vac = a.vac := by
  obtain ⟨vS⟩ := GlobalTheory.Unf.VolExist.nonempty_vol S.V
  obtain ⟨vT⟩ := GlobalTheory.Unf.VolExist.nonempty_vol T.V
  have pS : S.V.IsPosDef := fun τ => by rw [hS.sig τ, hS.rank, Nat.sub_zero]
  have pT : T.V.IsPosDef := fun τ => by rw [hT.sig τ, hT.rank, Nat.sub_zero]
  let x : DefSp S.V := ⟨cart S.M, onb S.M, S.Λ, vS⟩
  let y : DefSp T.V := ⟨cart T.M, onb T.M, T.Λ, vT⟩
  have hx : x.Is := GlobalTheory.SeeSawCompare.defSp_is hS.sigOK pS S.M x rfl rfl
    (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D S.V S.β S.Λ 1 hS.frame)
  have hy : y.Is := GlobalTheory.SeeSawCompare.defSp_is hT.sigOK pT T.M y rfl rfl
    (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D T.V T.β T.Λ 1 hT.frame)
  let k : KerDat S.V T.V := ⟨a.ω, a.vac, 0⟩
  have hk : k.Is ψ θ x y :=
    ⟨⟨χS, χT, (GlobalTheory.Grid.isWeil_false ψ S.V T.V χS χT a.ω).1 ha.weil⟩, ha.vac, fun u hu => (Finsupp.mem_support_iff.1 hu Finsupp.zero_apply).elim⟩
  exact ⟨x, y, k, hx, hy, hk, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem cenFock_fin : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (S T : GlobalTheory.Grid.Node D) (νS νT : ℕ) (PS PT : D.what₂.Tau → SPar), S.Is νS 0 PS → T.Is νT 0 PT → ∀ (a : GlobalTheory.Grid.ArrT S T) (χS χT : (AE D)ˣ →* Circle), a.Is ψ θ false χS χT → ∀ (χ : GA D S.V → ℂ) (f : WO S.V T.V → ℂ), IsThetaFunO ψ S.V T.V f → (∀ z ∈ GinfC S.V, z ∈ Subgroup.center (GA D S.V) → a.ω (z, 1) f = χ z • f) → ∃ (k : ℕ) (g : Fin k → WO S.V T.V → ℂ) (p : Fin k → GlobalTheory.Grid.Pol S T), (∀ l, GlobalTheory.Grid.IsFinVec ψ θ false S T (g l)) ∧ f = ∑ l, GlobalTheory.Grid.fock ψ θ false S T (g l) (p l) := by
  intro D ψ θ hθ S T νS νT PS PT hS hT a χS χT ha χ f hf hχ
  classical
  obtain ⟨x, y, k, hx, hy, hk, hxs, hys, hxB, hyB, hkom, hkvac⟩ := exists_defData hS hT ha
  have hstd : IsStdChar D ψ (-1) := hk.vac.1
  obtain ⟨χS', χT', hW⟩ := hk.weil
  obtain ⟨Wf, -, hWf⟩ := GlobalTheory.SeeSaw.CenFockPf.cenFock D ψ θ hθ S.V T.V x y hx hy k hk χ
  obtain ⟨n, u, c, hu, hc, hlat, hsum⟩ :=
    GlobalTheory.T.orientedTheta_eq_finite_heisenbergTranslates_vacua D ψ θ S.V T.V x.s y.s x.L y.L k.vac hx.sd hy.sd hk.vac f hf
  have hg : ∀ i, ∃ P, comb ψ S.V T.V (c i) f = pureTensorO ψ θ S.V T.V x.s y.s x.B y.B k.vac P := by
    intro i
    have he : ∀ z ∈ GinfC S.V, z ∈ Subgroup.center (GA D S.V) →
        k.om (z, 1) (comb ψ S.V T.V (c i) f) = χ z • comb ψ S.V T.V (c i) f := by
      intro z hz hzc
      rw [GlobalTheory.SeeSaw.RealComm.om_comb D ψ S.V T.V χS' χT' k.om hW z hz (c i) (hc i) f hf, hkom, hχ z hz hzc,
        comb_smul']
    obtain ⟨P, -, hP⟩ := hWf _ (theta_comb hstd hf) (hlat i) he
    exact ⟨P, hP⟩
  choose P hP using hg
  have hvth : IsThetaFunO ψ S.V T.V a.vac := hkvac ▸ hk.vac.2.theta
  refine ⟨n, fun i => heisO ψ S.V T.V (u i) a.vac, P, fun i => ⟨GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hstd hvth (u i),
    fun τ => isFockVacAt_heisO_fin hstd hθ hvth τ _ (ha.vac.2.fock τ) (hu i)⟩, ?_⟩
  refine hsum.trans (Finset.sum_congr rfl fun i _ => ?_)
  rw [hP i, heisO_pureTensorO_fin hstd hθ _ _ _ _ (hu i) hk.vac.2.theta, hxs, hys, hxB, hyB, hkvac]
  rfl

end GlobalTheory.CenFockGen

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.CentreEigenThetaFunctionFiniteSumFockPolynomialsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.centreEigen_thetaFunction_finite_sum_fockPolynomials : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (S T : GlobalTheory.Grid.Node D) (νS νT : ℕ) (PS PT : D.what₂.Tau → SPar), S.Is νS 0 PS → T.Is νT 0 PT → ∀ (a : GlobalTheory.Grid.ArrT S T) (χS χT : (AE D)ˣ →* Circle), a.Is ψ θ false χS χT → ∀ (χ : GA D S.V → ℂ) (f : WO S.V T.V → ℂ), IsThetaFunO ψ S.V T.V f → (∀ z ∈ GinfC S.V, z ∈ Subgroup.center (GA D S.V) → a.ω (z, 1) f = χ z • f) → ∃ (k : ℕ) (g : Fin k → WO S.V T.V → ℂ) (p : Fin k → GlobalTheory.Grid.Pol S T), (∀ l, GlobalTheory.Grid.IsFinVec ψ θ false S T (g l)) ∧ f = ∑ l, GlobalTheory.Grid.fock ψ θ false S T (g l) (p l) := by
  first | exact @GlobalTheory.CenFockGen.cenFock_fin | exact GlobalTheory.CenFockGen.cenFock_fin | (intros; apply GlobalTheory.CenFockGen.cenFock_fin <;> assumption)
end
end
