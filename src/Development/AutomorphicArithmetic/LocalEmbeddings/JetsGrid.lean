module

public import Development.AutomorphicArithmetic.LocalEmbeddings.JetsGlue
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.StepUnfold
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousReGLSymm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacEqJets
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOpenLevelFixingThetaFunction
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsThetaFunOOfThetaAt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtYAndItYOfPair
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DenseOfPolynomialStdGaussianMemSchwartzStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMeasDefOfIsTermVol
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
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
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ClassFunctionSumIntegral
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfOfMulFinOf
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.KerFockMovedReal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastColumnArrowRealAverageFunctionalStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfOfMulFinOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKernelGridRationalLeftInvariant
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.StmtTransInvHolds
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaFunOFockMovedVecTop

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.DefStep
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsOpenCompactLevel)
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.RowClaim

theorem isThetaFunO_fock_movedVec_top {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {U : Set T} (S : GridChoice W U) {j : ℕ} (hj : j < D.R.m)
    (Q : PolF D (G.V (.top (j + 1))).rank (G.V (.top j)).rank) (t : T) (d : FinDatum G t (.top t j))
    (hd : S.Z.HasVec d) :
    IsThetaFunO W.ψ (G.pS (.top t j)) (G.pT (.top t j)) (W.fock (.top t j) (movedVec t S d) Q) := by
  have hr : (Pair.top t j : Pair T).InRange D.R.m := by
    show j + 1 ≤ D.R.m
    omega
  have hω := W.om_is _ hr
  obtain ⟨f, hf⟩ := hd
  have hf0 : IsThetaFunO W.ψ _ _ f :=
    GlobalTheory.VecTheta.isThetaFunO_of_thetaAt W.ψ_std W.θ_is hf ((S.Z.vac_is (.top t j) (show j + 1 ≤ D.R.m by omega)).2.theta)
  have hv : IsThetaFunO W.ψ _ _ (S.Z.vec d) := by
    rw [Normal.vec, FinDatum.vec_eq W hf]
    exact hω.om_pres _ _ hf0
  have hm : IsThetaFunO W.ψ _ _ (movedVec t S d) := hω.om_pres _ _ hv
  exact GlobalTheory.Chain.InnerSteps.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ hm Q

theorem kerA_col_aut_cont : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {μ0 : T}, L.Is μ0 → ∀ (j : ℕ), j < D.R.m →
    ∀ (Q : PolF D (G.V (.top (j + 1))).rank (G.V (.top j)).rank) (t : T), t ∈ U → ∀ (d : FinDatum G t (.top t j)), S.Z.HasVec d →
    (∀ γ ∈ GQ (G.V (.top j)), ∀ g h, W.kerA (.col t j) (W.fock (.top t j) (movedVec t S d) Q) (γ * g) h =
      W.kerA (.col t j) (W.fock (.top t j) (movedVec t S d) Q) g h) ∧
    ∀ z h, Continuous fun k : GinfC (G.V (.top j)) =>
      W.kerA (.col t j) (W.fock (.top t j) (movedVec t S d) Q) (z * k) h := by
  intro D T L sc G W U S μ0 _ j hj Q t _ d hd
  have hr : (Pair.top t j : Pair T).InRange D.R.m := by
    show j + 1 ≤ D.R.m
    omega
  have hω := W.om_is _ hr
  have hF := isThetaFunO_fock_movedVec_top S hj Q t d hd
  refine ⟨fun γ hγ g h => ?_, fun z h => ?_⟩
  · show thetaKO (W.om (.top t j)) (γ * g) h _ = thetaKO (W.om (.top t j)) g h _
    have e : ((γ * g, h) : GA D (G.V (.top j)) × GA D (G.V (.top (j + 1)))) = (γ, 1) * (g, h) := by simp
    unfold thetaKO
    rw [e, map_mul]
    exact hω.om_aut γ hγ 1 (one_mem _) _ (hω.om_pres _ _ hF)
  · show Continuous fun k : GinfC (G.V (.top j)) => thetaKO (W.om (.top t j)) (z * k) h _
    exact (hω.om_cont _ hF 0).comp ((continuous_const.mul continuous_subtype_val).prodMk continuous_const)

end GlobalTheory.RowClaim

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealActionOnVertexWeightContinuous

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.DefStep
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsOpenCompactLevel)
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.RealActCont

theorem realAct_inv_continuous : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (θ : InfFam D), IsInfFam θ →
    ∀ (fr : ∀ X : Node, GL (Fin (G.V X).rank) D.host.E) (X : Node) (Λ : Module.Dual ℂ (VV ℂ (wt G X))) (w : VV ℂ (wt G X)),
    Continuous fun k : GinfC (G.V X) => Λ (realAct θ fr X ((k : GA D (G.V X))⁻¹) w) := by
  intro D T L sc G θ hθ fr X Λ w
  classical
  obtain ⟨hc, -⟩ := GlobalTheory.CoefModel.realGL_laws hθ (G.V X)
  have hG : ∀ _τ : D.what₂.Tau, (1 : Matrix (Fin (G.V X).rank) (Fin (G.V X).rank) ℂ).PosDef := fun _ => Matrix.PosDef.one
  let A : GinfC (G.V X) → D.what₂.Tau → GL (Fin (G.V X).rank) ℂ :=
    fun k => invTrK (realIn θ fr X ((k : GA D (G.V X))⁻¹))
  have hA : ∀ τ, Continuous fun k => (A k τ : Matrix (Fin (G.V X).rank) (Fin (G.V X).rank) ℂ) := by
    intro τ
    have e : ∀ k : GinfC (G.V X), (A k τ : Matrix (Fin (G.V X).rank) (Fin (G.V X).rank) ℂ) =
        Matrix.transpose ((((frGL fr X τ)⁻¹ : GL (Fin (G.V X).rank) ℂ) : Matrix (Fin (G.V X).rank) (Fin (G.V X).rank) ℂ) *
          Formalism.L2.Pj.archM (G.V X) (θ τ) (k : GA D (G.V X)) * (frGL fr X τ : Matrix (Fin (G.V X).rank) (Fin (G.V X).rank) ℂ)) := by
      intro k
      simp only [A, map_inv]
      show ((((realIn θ fr X (k : GA D (G.V X)) τ)⁻¹)⁻¹ : GL (Fin (G.V X).rank) ℂ) : Matrix (Fin (G.V X).rank) (Fin (G.V X).rank) ℂ).transpose = _
      rw [inv_inv]
      simp [realIn, MulAut.conj_apply, GlobalTheory.CoefModel.realGL_coe]
    refine Continuous.congr ?_ fun k => (e k).symm
    exact ((continuous_const.mul ((hc τ).comp continuous_subtype_val)).mul continuous_const).matrix_transpose
  have key := GlobalTheory.CoefModel.continuous_rhoH (wt G X) hG A hA (GlobalTheory.CoefModel.toHilb (wt G X) hG w)
  have hΛ : Continuous (Λ ∘ₗ (GlobalTheory.CoefModel.toHilb (wt G X) hG).symm.toLinearMap) :=
    LinearMap.continuous_of_finiteDimensional _
  refine (hΛ.comp key).congr fun k => ?_
  simp only [Function.comp_apply, GlobalTheory.CoefModel.rhoH_toHilb, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]
  rfl

end GlobalTheory.RealActCont
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealActionOnVertexWeightContinuousStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.DefStep
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsOpenCompactLevel)
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.realActionOnVertexWeight_continuous : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (θ : InfFam D), IsInfFam θ →
    ∀ (fr : ∀ X : Node, GL (Fin (G.V X).rank) D.host.E) (X : Node) (Λ : Module.Dual ℂ (VV ℂ (wt G X))) (w : VV ℂ (wt G X)),
    Continuous fun k : GinfC (G.V X) => Λ (realAct θ fr X ((k : GA D (G.V X))⁻¹) w) := by
  first | exact @GlobalTheory.RealActCont.realAct_inv_continuous | exact GlobalTheory.RealActCont.realAct_inv_continuous | (intros; apply GlobalTheory.RealActCont.realAct_inv_continuous <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.LocalEmbeddings.JetsGrid

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.DefStep
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsOpenCompactLevel IsDefiniteSpace)
open scoped ComplexOrder Topology

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.JetsOne

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem exists_rec {α : ℕ → Type} [∀ n, Zero (α n)] {N : ℕ} {R : ∀ n, n < N → α n → α (n + 1) → Prop}
    (h : ∀ n hn a, ∃ b, R n hn a b) (a : α 0) : ∃ f : ∀ n, α n, f 0 = a ∧ ∀ n hn, R n hn (f n) (f (n + 1)) := by
  choose g hg using h
  refine ⟨fun n => Nat.rec a (fun n b => if hn : n < N then g n hn b else 0) n, rfl, fun n hn => ?_⟩
  have := hg n hn (Nat.rec a (fun n b => if hn : n < N then g n hn b else 0) n)
  simpa only [dif_pos hn] using this

theorem inRange_of_def {p : Pair T} (hp : DefPair D.R.m p) : p.InRange D.R.m := by
  have hn := DefPair.nodes hp
  cases p <;> simp only [DefPair, DefNode] at hp hn <;> simp only [Pair.InRange, Node.InRange] <;> omega

theorem theta_fock (S : GridChoice W U) {t : T} {p : Pair T} (hp : DefPair D.R.m p) (d : FinDatum G t p) (hd : S.Z.HasVec d)
    (Q : PolF D (G.pT p).rank (G.pS p).rank) : IsThetaFunO W.ψ (G.pS p) (G.pT p) (W.fock p (movedVec t S d) Q) := by
  have hω := W.om_is _ (inRange_of_def hp)
  obtain ⟨f, hf⟩ := hd
  have hf0 : IsThetaFunO W.ψ _ _ f := GlobalTheory.VecTheta.isThetaFunO_of_thetaAt W.ψ_std W.θ_is hf ((S.Z.vac_is p hp).2.theta)
  have hv : IsThetaFunO W.ψ _ _ (S.Z.vec d) := by
    rw [Normal.vec, FinDatum.vec_eq W hf]
    exact hω.om_pres _ _ hf0
  have hm : IsThetaFunO W.ψ _ _ (movedVec t S d) := hω.om_pres _ _ hv
  exact GlobalTheory.Chain.InnerSteps.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ hm Q

theorem ker_near (W : G.Weil) {p : Pair T} (hp : p.InRange D.R.m) {f : WO (G.pS p) (G.pT p) → ℂ}
    (hf : IsThetaFunO W.ψ (G.pS p) (G.pT p) f) :
    (∀ᶠ k in 𝓝 (1 : GA D (G.V p.small)), k ∈ GfC _ → ∀ g h, W.ker p f (g * k) h = W.ker p f g h) ∧
      ∀ᶠ k in 𝓝 (1 : GA D (G.V p.big)), k ∈ GfC _ → ∀ g h, W.ker p f g (h * k) = W.ker p f g h := by
  have hω := W.om_is _ hp
  obtain ⟨A, A', hA, hA', e⟩ := GlobalTheory.Mem.ThetaLevel.exists_level D W.ψ hω.std _ _ (W.om p) (GlobalTheory.Ker.isWeak_of_datum hω) hω.om_cont f hf
  have hc : Continuous fun q : GA D (G.V p.small) × GA D (G.V p.big) => G.toPair p q.1 q.2 := by
    cases p
    · exact ((continuous_negGA _).comp continuous_snd).prodMk continuous_fst
    · exact continuous_id
    · exact ((continuous_negGA _).comp continuous_snd).prodMk continuous_fst
    · exact continuous_id
  have h1 : G.toPair p 1 1 = 1 := by cases p <;> simp [GridData.toPair, Prod.ext_iff]
  have hf : ∀ k ∈ GfC (G.V p.small), ∀ k' ∈ GfC (G.V p.big), (G.toPair p k k').1 ∈ GfC _ ∧ (G.toPair p k k').2 ∈ GfC _ :=
    fun k hk k' hk' => by
    cases p
    · exact ⟨GlobalTheory.FockReal.negGA_mem_GfC _ hk', hk⟩
    · exact ⟨hk, hk'⟩
    · exact ⟨GlobalTheory.FockReal.negGA_mem_GfC _ hk', hk⟩
    · exact ⟨hk, hk'⟩
  have key : ∀ k ∈ GfC (G.V p.small), ∀ k' ∈ GfC (G.V p.big), G.toPair p k k' ∈ (A : Set _) ×ˢ (A' : Set _) → ∀ g h,
      W.ker p f (g * k) (h * k') = W.ker p f g h := fun k hk k' hk' hm g h => by
    rw [GlobalTheory.FockReal.ker_mul]
    exact congrArg (fun F => W.ker p F g h) (e _ hm.1 (hf k hk k' hk').1 _ hm.2 (hf k hk k' hk').2)
  have hO : IsOpen ((A : Set (GA D (G.pS p))) ×ˢ (A' : Set (GA D (G.pT p)))) := hA.prod hA'
  have m1 : G.toPair p 1 1 ∈ (A : Set _) ×ˢ (A' : Set _) := by rw [h1]; exact ⟨one_mem _, one_mem _⟩
  constructor
  · filter_upwards [(hO.preimage (hc.comp (continuous_id.prodMk (continuous_const (y := 1))))).mem_nhds (x := 1) m1] with k hk hk' g h
    simpa using key k hk' 1 (one_mem _) hk g h
  · filter_upwards [(hO.preimage (hc.comp ((continuous_const (y := 1)).prodMk continuous_id))).mem_nhds (x := 1) m1] with k hk hk' g h
    simpa using key 1 (one_mem _) k hk' hk g h

theorem scal_ne (S : GridChoice W U) (p : Pair T) : S.Z.scal 1 p ≠ 0 := by
  have hδ : S.Z.δ ≠ 0 := Formalism.MainNotions.Ext.delta_ne_holds D _ D.host.ccK_ne_bot _ S.Z.crv.2
  refine mul_ne_zero (Units.ne_zero _) (Finset.prod_ne_zero_iff.2 fun τ _ => pow_ne_zero _ ((map_ne_zero _).2 ?_))
  exact div_ne_zero one_ne_zero (period_ne_zero hδ τ)

theorem scal_free (S : GridChoice W U) (t t' : T) (j : ℕ) : S.Z.scal 1 (.top t j) = S.Z.scal 1 (.top t' j) := by
  unfold Normal.scal
  rw [(S.Z.free t t' j).2.2]
  rfl

def colComp (S : GridChoice W U) {t : T} (d : PureDat G t) (j : ℕ) (x : FinPt G (.top j)) (y : FinPt G (.top (j + 1))) :
    VV ℂ (wt G (.top j)) →ₗ[ℂ] VV ℂ (wt G (.top (j + 1))) := if h : j < D.R.m then S.Z.kkMap 1 (d.1 ⟨j, h⟩) x y else 0

def rowComp (S : GridChoice W U) {t : T} (d : PureDat G t) (i : ℕ) (x : FinPt G (.grid i D.R.m)) (y : FinPt G (.grid (i + 1) D.R.m)) :
    VV ℂ (wt G (.grid i D.R.m)) →ₗ[ℂ] VV ℂ (wt G (.grid (i + 1) D.R.m)) :=
  if h : i < D.R.m then S.Z.kkMap 1 (d.2 ⟨i, h⟩) x y else 0

def colKer (S : GridChoice W U) (P : PolCol G × PolRow G) {t : T} (d : PureDat G t) (j : ℕ) (g : GA D (G.V (.top j)))
    (h : GA D (G.V (.top (j + 1)))) : ℂ :=
  if hj : j < D.R.m then W.ker (.top t j) (W.fock (.top t j) (movedVec t S (d.1 ⟨j, hj⟩)) (P.1 ⟨j, hj⟩)) g h else 0

def rowKer (S : GridChoice W U) (P : PolCol G × PolRow G) {t : T} (d : PureDat G t) (i : ℕ) (g : GA D (G.V (.grid i D.R.m)))
    (h : GA D (G.V (.grid (i + 1) D.R.m))) : ℂ :=
  if hi : i < D.R.m then W.ker (.chi i D.R.m) (W.fock (.chi i D.R.m) (movedVec t S (d.2 ⟨i, hi⟩)) (P.2 ⟨i, hi⟩)) g h else 0

theorem pathLift_column_eq_kernelLift (M : Vol G) (t : T) (ker : ∀ j, GA D (G.V (.top j)) → GA D (G.V (.top (j + 1))) → ℂ) (φ : Fn G (.top 0)) :
    ∀ (n : ℕ) (f : ∀ j : Fin n, Sch G (.col t j)), (∀ j : Fin n, ∀ g h, ker j g h = W.ker (.top t j) (f j) g h) →
      liftP W M (colPath t n) (colFam t n f) φ =
        liftC (V := fun j => G.V (.top j)) (fun j => M.ν (.top j)) (fun j => M.fd (.top j)) ker φ n
  | 0, _, _ => rfl
  | n + 1, f, hf => by
    funext h
    show liftA W M (.col t n) (f (Fin.last n)) (liftP W M (colPath t n) (colFam t n fun j => f j.castSucc) φ) h = _
    rw [pathLift_column_eq_kernelLift M t ker φ n _ fun j => hf j.castSucc, liftA_apply]
    exact congrArg _ (funext fun g => congrArg (· * _) (hf (Fin.last n) g h).symm)

theorem pathLift_row_eq_kernelLift (M : Vol G) (ker : ∀ i, GA D (G.V (.grid i D.R.m)) → GA D (G.V (.grid (i + 1) D.R.m)) → ℂ)
    (φ : Fn G (.grid 0 D.R.m)) :
    ∀ (n : ℕ) (f : ∀ i : Fin n, Sch G (.right i D.R.m)), (∀ i : Fin n, ∀ g h, ker i g h = W.ker (.chi i D.R.m) (f i) g h) →
      liftP W M (rowPath T D.R.m n) (rowFam D.R.m n f) φ =
        liftC (V := fun i => G.V (.grid i D.R.m)) (fun i => M.ν (.grid i D.R.m)) (fun i => M.fd (.grid i D.R.m)) ker φ n
  | 0, _, _ => rfl
  | n + 1, f, hf => by
    funext h
    show liftA W M (.right n D.R.m) (f (Fin.last n)) (liftP W M (rowPath T D.R.m n) (rowFam D.R.m n fun j => f j.castSucc) φ) h = _
    rw [pathLift_row_eq_kernelLift M ker φ n _ fun j => hf j.castSucc, liftA_apply]
    exact congrArg _ (funext fun g => congrArg (· * _) (hf (Fin.last n) g h).symm)

theorem defPer_eq (S : GridChoice W U) (P : PolCol G × PolRow G) {t : T} (d : PureDat G t) (M : Vol G) (φ : Fn G (.top 0))
    (F : Fn G (.grid 0 D.R.m)) : defPer t S M P d φ F = ∫ h in M.fd (.grid D.R.m D.R.m),
      liftC (V := fun j => G.V (.top j)) (fun j => M.ν (.top j)) (fun j => M.fd (.top j)) (colKer S P d) φ D.R.m
          (stabilizerEmbedding G.sp.topDec h) *
        liftC (V := fun i => G.V (.grid i D.R.m)) (fun i => M.ν (.grid i D.R.m)) (fun i => M.fd (.grid i D.R.m)) (rowKer S P d) F
          D.R.m h ∂M.ν (.grid D.R.m D.R.m) := by
  rw [defPer, pathLift_column_eq_kernelLift M t (colKer S P d) φ _ _ fun j g h => dif_pos j.2, pathLift_row_eq_kernelLift M (rowKer S P d) F _ _ fun j g h => dif_pos j.2]

theorem col_near (S : GridChoice W U) (P : PolCol G × PolRow G) {t : T} (d : PureDat G t) (hd : ∀ j, S.Z.HasVec (d.1 j))
    {F : Fn G (.top 0)} (hF : ∀ᶠ k in 𝓝 (1 : GA D (G.V (.top 0))), k ∈ GfC _ → ∀ g, F (g * k) = F g) :
    NearOK (V := fun j => G.V (.top j)) (colKer S P d) F D.R.m := by
  refine ⟨hF, fun n hn => ?_⟩
  have hp : DefPair D.R.m (.top t n) := hn
  simp only [colKer, dif_pos hn]
  exact ker_near W (inRange_of_def hp) (theta_fock S hp _ (hd ⟨n, hn⟩) _)

theorem row_near (S : GridChoice W U) (P : PolCol G × PolRow G) {t : T} (d : PureDat G t) (hd : ∀ j, S.Z.HasVec (d.2 j))
    {F : Fn G (.grid 0 D.R.m)} (hF : ∀ᶠ k in 𝓝 (1 : GA D (G.V (.grid 0 D.R.m))), k ∈ GfC _ → ∀ g, F (g * k) = F g) :
    NearOK (V := fun j => G.V (.grid j D.R.m)) (rowKer S P d) F D.R.m := by
  refine ⟨hF, fun n hn => ?_⟩
  have hp : DefPair D.R.m (.chi n D.R.m : Pair T) := ⟨hn, rfl⟩
  simp only [rowKer, dif_pos hn]
  exact ker_near W (inRange_of_def hp) (theta_fock S hp _ (hd ⟨n, hn⟩) _)

theorem col_chain (S : GridChoice W U) {μ0 : T} (hL : L.Is μ0) (P : PolCol G × PolRow G) (Λ0 : Module.Dual ℂ (VV ℂ (wt G (.top 0)))) :
    ∃ Λ : ∀ j, Module.Dual ℂ (VV ℂ (wt G (.top j))), Λ 0 = Λ0 ∧ ∀ t ∈ U, ∀ d : PureDat G t, (∀ j, S.Z.HasVec (d.1 j)) →
      ∀ n < D.R.m, ArrowOK (V := fun j => G.V (.top j)) (Mo := fun j => VV ℂ (wt G (.top j))) (colComp S d)
        (fun j => realAct W.θ S.N.fr (.top j)) (colKer S P d) Λ n := by
  obtain ⟨Λ, h0, h⟩ := exists_rec (α := fun j => Module.Dual ℂ (VV ℂ (wt G (.top j)))) (N := D.R.m)
    (R := fun j hj Λ Λ' => ∀ t ∈ U, ∀ d : FinDatum G t (.top t j), S.Z.HasVec d →
      ∀ κ : Measure (GinfC (G.V (.top j))), κ.IsHaarMeasure → IsProbabilityMeasure κ →
      ∀ (x : FinPt G (.top j)) (h : GA D (G.V (.top (j + 1)))) (v : VV ℂ (wt G (.top j))),
        ∫ k, W.ker (.top t j) (W.fock (.top t j) (movedVec t S d) (P.1 ⟨j, hj⟩)) ((x : GA D (G.V (.top j))) * (k : GA D (G.V (.top j)))) h *
            Λ (realAct W.θ S.N.fr (.top j) ((k : GA D (G.V (.top j)))⁻¹) v) ∂κ =
          Λ' (realAct W.θ S.N.fr (.top (j + 1)) h⁻¹ (S.Z.kkMap 1 d x (finOf _ h) v))) (fun j hj Λ => by
      obtain ⟨Λ', h⟩ := GlobalTheory.T.exists_dual_integral_arrowKernel_fock_eq_fockComp_top S hL j hj (P.1 ⟨j, hj⟩) Λ
      refine ⟨(S.Z.scal 1 (.top μ0 j))⁻¹ • Λ', fun t ht d hd κ h1 h2 x g v => (h t ht d hd κ h1 h2 x g v).trans ?_⟩
      rw [Normal.kkMap, LinearMap.smul_apply, LinearMap.smul_apply, map_smul, map_smul, scal_free S t μ0, smul_smul,
        inv_mul_cancel₀ (scal_ne S _), one_smul]) Λ0
  refine ⟨Λ, h0, fun t ht d hd n hn => ?_⟩
  have hp : DefPair D.R.m (.top t n) := hn
  have hθ := theta_fock S hp _ (hd ⟨n, hn⟩) (P.1 ⟨n, hn⟩)
  have hl := GlobalTheory.RowReal.ker_rat_left W _ (inRange_of_def hp) _ hθ
  refine ⟨TermVolDef.isDefiniteSpace_of_isV (node_isV G hL (X := .top n) hn.le), posDef_top G hn.le,
    fun g hg => realAct_fin _ _ _ hg, fun u => GlobalTheory.T.realActionOnVertexWeight_continuous W.θ W.θ_is S.N.fr _ _ u, ?_⟩
  simp only [colKer, colComp, dif_pos hn]
  exact ⟨fun γ hγ g h => by simpa using hl γ hγ 1 (one_mem _) g h, fun γ hγ g h => by simpa using hl 1 (one_mem _) γ hγ g h,
    (kerA_col_aut_cont S hL n hn _ t ht _ (hd ⟨n, hn⟩)).2, h n hn t ht _ (hd ⟨n, hn⟩)⟩

theorem row_chain (S : GridChoice W U) {μ0 : T} (hL : L.Is μ0) (P : PolCol G × PolRow G)
    (Λ0 : Module.Dual ℂ (VV ℂ (wt G (.grid 0 D.R.m)))) :
    ∃ Λ : ∀ j, Module.Dual ℂ (VV ℂ (wt G (.grid j D.R.m))), Λ 0 = Λ0 ∧ ∀ t ∈ U, ∀ d : PureDat G t, (∀ j, S.Z.HasVec (d.2 j)) →
      ∀ n < D.R.m, ArrowOK (V := fun j => G.V (.grid j D.R.m)) (Mo := fun j => VV ℂ (wt G (.grid j D.R.m))) (rowComp S d)
        (fun j => realAct W.θ S.N.fr (.grid j D.R.m)) (rowKer S P d) Λ n := by
  obtain ⟨Λ, h0, h⟩ := exists_rec (α := fun j => Module.Dual ℂ (VV ℂ (wt G (.grid j D.R.m)))) (N := D.R.m)
    (R := fun j hj Λ Λ' => ∀ t ∈ U, ∀ d : FinDatum G t (.chi j D.R.m), S.Z.HasVec d →
      ∀ κ : Measure (GinfC (G.V (.grid j D.R.m))), κ.IsHaarMeasure → IsProbabilityMeasure κ →
      ∀ (x : FinPt G (.grid j D.R.m)) (h : GA D (G.V (.grid (j + 1) D.R.m))) (v : VV ℂ (wt G (.grid j D.R.m))),
        ∫ k, W.ker (.chi j D.R.m) (W.fock (.chi j D.R.m) (movedVec t S d) (P.2 ⟨j, hj⟩))
            ((x : GA D (G.V (.grid j D.R.m))) * (k : GA D (G.V (.grid j D.R.m)))) h *
            Λ (realAct W.θ S.N.fr (.grid j D.R.m) ((k : GA D (G.V (.grid j D.R.m)))⁻¹) v) ∂κ =
          Λ' (realAct W.θ S.N.fr (.grid (j + 1) D.R.m) h⁻¹ (S.Z.kkMap 1 d x (finOf _ h) v))) (fun j hj Λ => by
      obtain ⟨Λ', h⟩ := GlobalTheory.T.lastColumnArrow_realAverage_functional S hL j hj (P.2 ⟨j, hj⟩) Λ
      refine ⟨(S.Z.scal 1 (.chi j D.R.m))⁻¹ • Λ', fun t ht d hd κ h1 h2 x g v => (h t ht d hd κ h1 h2 x g v).trans ?_⟩
      rw [Normal.kkMap, LinearMap.smul_apply, LinearMap.smul_apply, map_smul, map_smul, smul_smul,
        inv_mul_cancel₀ (scal_ne S _), one_smul]) Λ0
  refine ⟨Λ, h0, fun t ht d hd n hn => ?_⟩
  have hp : DefPair D.R.m (.chi n D.R.m : Pair T) := ⟨hn, rfl⟩
  have hθ := theta_fock S hp _ (hd ⟨n, hn⟩) (P.2 ⟨n, hn⟩)
  have hl := GlobalTheory.RowReal.ker_rat_left W _ (inRange_of_def hp) _ hθ
  have hV := node_isV G hL (X := .grid n D.R.m) ⟨hn.le, le_rfl⟩
  have e : Node.neg D.R.m (.grid n D.R.m) = 0 := by simp [Node.neg]
  rw [e] at hV
  refine ⟨TermVolDef.isDefiniteSpace_of_isV hV, posDef_grid hL hn.le,
    fun g hg => realAct_fin _ _ _ hg, fun u => GlobalTheory.T.realActionOnVertexWeight_continuous W.θ W.θ_is S.N.fr _ _ u, ?_⟩
  simp only [rowKer, rowComp, dif_pos hn]
  exact ⟨fun γ hγ g h => by simpa using hl γ hγ 1 (one_mem _) g h, fun γ hγ g h => by simpa using hl 1 (one_mem _) γ hγ g h,
    fun z h => ((W.om_is _ (inRange_of_def hp)).om_cont _ hθ 0).comp
      (continuous_const.prodMk (continuous_const.mul continuous_subtype_val)), h n hn t ht _ (hd ⟨n, hn⟩)⟩

end GlobalTheory.JetsOne

end
end
end
