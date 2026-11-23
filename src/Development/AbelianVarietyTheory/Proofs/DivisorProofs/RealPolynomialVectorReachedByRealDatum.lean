module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLagrModelOfIsLin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerSkewPlaneUniqueDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDerivAtHeisenbergTranslateFockBoxStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDerivAtThetaTransformHeisenbergRealLine
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacuaTripleProportionalToNonzeroStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanSchwartzDatumStableHeisenbergDerivati

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.BigNZ.DatRealStable

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem schr_schr_apply {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (w w' : (κ → R) × (κ → R)) (f : (κ → R) → ℂ) (x : κ → R) :
    GlobalTheory.WeilM.schr ψ w (GlobalTheory.WeilM.schr ψ w' f) x =
      ψ (⅟(2 : R) * (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2)) * GlobalTheory.WeilM.schr ψ (w + w') f x := by
  simp only [GlobalTheory.WeilM.schr, ← mul_assoc, ← AddChar.map_add_eq_mul, add_assoc]
  congr 2
  simp only [Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]
  rw [dotProduct_comm w'.1 w.2]
  first
    | linear_combination (w.1 ⬝ᵥ w'.2) * invOf_mul_self (2 : R)
    | linear_combination (-(w.1 ⬝ᵥ w'.2)) * invOf_mul_self (2 : R)

theorem sum_tensT (W : G.Weil) {X Y : Node} {p : Path T X Y} (a : PolT G p →₀ ℂ) (τ : TotT G p) (g : PureT G p → ℂ) :
    (tensT W a τ).sum (fun d c => c * g d) =
      a.sum fun P c => τ.sum fun d c' => c * c' * g (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) d P) := by
  unfold tensT
  rw [Finsupp.sum_sum_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
  refine Finset.sum_congr rfl fun P _ => ?_
  beta_reduce
  rw [Finsupp.sum_sum_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
  refine Finset.sum_congr rfl fun d _ => ?_
  beta_reduce
  rw [Finsupp.sum_single_index (zero_mul _)]

theorem datum_stable : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (M : Vol G)
    (e : Num G i j) (Bs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
    (om : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (h : IsTripleOf W M t i j e Bs Γ X), IsTriple Bs Γ X om om' → ∀ n Φ τ τ', HasFlip B t ρ i j n Φ τ τ' →
    ∀ φ, IsFinPart Γ.M X.T φ → ∀ (f : SInf D.host.F (Fin (spW G i j).rank × Fin ((spW G i j).rank + (spW₁ G i j).rank))) a, IsDatumA W e Γ (tensT W a τ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) →
    ∀ u, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) u → ∀ f₁ : SInf D.host.F (Fin (spW G i j).rank × Fin ((spW G i j).rank + (spW₁ G i j).rank)), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (Γ.M.heisLine Bs.ψ u) f f₁ →
    ∃ a', IsDatumA W e Γ (tensT W a' τ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₁ φ) := by
  intro D T L sc G μ₀ hL W B ρ t i j M e Bs Γ X om om' h hT n Φ τ τ' hF φ hφ f a ha u hu f₁ h1
  change TotT G (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.routeA t i j) at τ
  have hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd W.ψ := h.ψ ▸ hT.base.std
  have hFr : IsTotallyReal D.host.F := hT.base.cm.1
  have hψc : IsCharAF D.host.F W.ψ := GlobalTheory.StdCharFromIsStd.isCharAF hψ
  have hstd := (hT.geo.hM.std.and (Finset.finite_toSet X.T).compl_mem_cofinite).mono
    fun v hv => (hφ.2 v hv.2).trans hv.1
  have hrest := GlobalTheory.ThK.EvUniqInf.rest_pure f φ hφ.1 hstd
  have hmem1 := GlobalTheory.TensUniq.pure_mem_schA f₁ φ hφ.1 hstd
  have hd : ∀ x, HasDerivAt (fun s : ℝ => Γ.M.co.rho W.ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F s • u)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) x) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₁ φ x) 0 := by
    intro x
    rw [← h.ψ]
    exact h1 _ hrest x
  choose b hb using fun P => GlobalTheory.T.hasDerivAt_heisenbergTranslate_fockBox hL W B ρ t i j M e Bs Γ X om om' h hT n Φ τ τ' hF u hu P
  refine ⟨a.sum fun P c => c • b P, hmem1, fun v => ?_⟩
  have H1 := GlobalTheory.ThetaLineDeriv.hasDerivAt_thetaSum_rho Γ.M.co W.ψ hFr hψc u _ ha.1 _ hmem1 hd v
  set g : PolT G (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.routeA t i j) → PureT G (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.routeA t i j) → _ → ℂ :=
    fun P d => GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.boxA e (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) d P) with hg
  set ph : ℝ → ℂ := fun s => W.ψ (⅟(2 : AF D.host.F) * ((Γ.M.co.e v).1 ⬝ᵥ (Γ.M.co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F s • u)).2 -
        (Γ.M.co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F s • u)).1 ⬝ᵥ (Γ.M.co.e v).2)) with hph
  have e1 : ∀ s : ℝ, GlobalTheory.WeilM.thetaSum D.host.F (Γ.M.co.rho W.ψ v (Γ.M.co.rho W.ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F s • u)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ))) = ∑ P ∈ a.support, ∑ d ∈ τ.support,
        a P * τ d * (ph s * g P d (v + GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F s • u)) := by
    intro s
    have e2 : GlobalTheory.WeilM.thetaSum D.host.F (Γ.M.co.rho W.ψ v (Γ.M.co.rho W.ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F s • u)
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ))) = ph s * GlobalTheory.WeilM.thetaSum D.host.F (Γ.M.co.rho W.ψ
          (v + GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F s • u) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ)) := by
      unfold GlobalTheory.WeilM.thetaSum
      rw [← tsum_mul_left]
      refine tsum_congr fun ξ => ?_
      simp only [GlobalTheory.WeilM.Darboux.rho, map_add (f := _)]
      exact schr_schr_apply W.ψ _ _ _ _
    rw [e2, ha.2, sum_tensT, Finsupp.sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun P _ => ?_
    rw [Finsupp.sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    simp only [hg]
    ring
  have H2 : HasDerivAt (fun s : ℝ => ∑ P ∈ a.support, ∑ d ∈ τ.support,
        a P * τ d * (ph s * g P d (v + GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F s • u)))
      (∑ P ∈ a.support, ∑ d ∈ τ.support, a P * τ d * (b P).sum fun P' c => c * g P' d v) 0 :=
    HasDerivAt.fun_sum fun P _ => HasDerivAt.fun_sum fun d hd => (hb P d hd v).const_mul (a P * τ d)
  rw [← funext e1] at H2
  rw [H1.unique H2, sum_tensT, Finsupp.sum_sum_index (fun _ => by simp) (fun _ _ _ => by simp only [add_mul, Finsupp.sum_add])]
  refine Finset.sum_congr rfl fun P _ => ?_
  beta_reduce
  rw [Finsupp.sum_smul_index' (fun _ => by simp)]
  simp only [Finsupp.sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun P' _ => Finset.sum_congr rfl fun d _ => ?_
  simp only [hg, smul_eq_mul]
  ring

end GlobalTheory.BigNZ.DatRealStable
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanSchwartzDatumStableHeisenbergDerivatiStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw


theorem _root_.GlobalTheory.T.archimedeanSchwartzDatum_stable_heisenbergDerivative : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (M : Vol G)
    (e : Num G i j) (Bs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
    (om : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (h : IsTripleOf W M t i j e Bs Γ X), IsTriple Bs Γ X om om' → ∀ n Φ τ τ', HasFlip B t ρ i j n Φ τ τ' →
    ∀ φ, IsFinPart Γ.M X.T φ → ∀ (f : SInf D.host.F (Fin (spW G i j).rank × Fin ((spW G i j).rank + (spW₁ G i j).rank))) a, IsDatumA W e Γ (tensT W a τ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) →
    ∀ u, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) u → ∀ f₁ : SInf D.host.F (Fin (spW G i j).rank × Fin ((spW G i j).rank + (spW₁ G i j).rank)), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (Γ.M.heisLine Bs.ψ u) f f₁ →
    ∃ a', IsDatumA W e Γ (tensT W a' τ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₁ φ) := by
  first | exact @GlobalTheory.BigNZ.DatRealStable.datum_stable | exact GlobalTheory.BigNZ.DatRealStable.datum_stable | (intros; apply GlobalTheory.BigNZ.DatRealStable.datum_stable <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealPolynomialVectorReachedByRealDatum

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.BigNZ.DatReal

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

section Tens

variable (W : G.Weil) {X Y : Node} {p : Path T X Y}

theorem tensT_zero (τ : TotT G p) : tensT W (0 : PolT G p →₀ ℂ) τ = 0 := Finsupp.sum_zero_index

theorem tensT_add (a b : PolT G p →₀ ℂ) (τ : TotT G p) : tensT W (a + b) τ = tensT W a τ + tensT W b τ := by
  unfold tensT
  refine Finsupp.sum_add_index' (fun P => by simp) (fun P c₁ c₂ => ?_)
  simp only [add_mul, Finsupp.single_add, Finsupp.sum_add]

theorem tensT_smul (c : ℂ) (a : PolT G p →₀ ℂ) (τ : TotT G p) : tensT W (c • a) τ = c • tensT W a τ := by
  unfold tensT
  rw [Finsupp.sum_smul_index' (fun P => by simp), Finsupp.smul_sum]
  refine Finset.sum_congr rfl fun P _ => ?_
  dsimp only
  rw [Finsupp.smul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  dsimp only
  rw [Finsupp.smul_single, smul_eq_mul, smul_eq_mul, mul_assoc]

theorem fock_one (q : Pair T) (f : WO (G.pS q) (G.pT q) → ℂ) : W.fock q f 1 = f := by
  unfold GridData.Weil.fock pureTensorO pureTensorL
  rw [show (1 : MvPolynomial (FVar D (G.pT q).rank (G.pS q).rank) ℂ) = MvPolynomial.basisMonomials _ ℂ 0 by
    rw [MvPolynomial.coe_basisMonomials]; rfl, Module.Basis.constr_basis]
  simp [opPow]

end Tens

section Datum

variable {t : T} {i j : ℕ} (W : G.Weil) (e : Num G i j) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j)

noncomputable def onePol : PolT G (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.routeA t i j) := (((), 1), 1)

theorem tensT_one (τ : TotT G (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.routeA t i j)) : tensT W (Finsupp.single onePol 1) τ = τ := by
  unfold tensT
  rw [Finsupp.sum_single_index (by simp)]
  have hz : ∀ d : PureT G (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.routeA t i j), Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) d onePol = d := by
    rintro ⟨⟨⟨⟩, d₁⟩, d₂⟩
    show (((), W.fock _ d₁ 1), W.fock _ d₂ 1) = (((), d₁), d₂)
    rw [fock_one, fock_one]
  simp only [hz, one_mul]
  exact Finsupp.sum_single τ

theorem isDatumA_zero : IsDatumA W e Γ (0 : TotT G (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.routeA t i j)) 0 := by
  refine ⟨Submodule.zero_mem _, fun u => ?_⟩
  have : Γ.M.co.rho W.ψ u 0 = 0 := by
    funext x; simp [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr]
  rw [this, Finsupp.sum_zero_index]
  simp [GlobalTheory.WeilM.thetaSum]

theorem datumA_add (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd W.ψ) {τ τ' : TotT G (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.routeA t i j)} {Φ Φ'} (h : IsDatumA W e Γ τ Φ)
    (h' : IsDatumA W e Γ τ' Φ') : IsDatumA W e Γ (τ + τ') (Φ + Φ') := by
  refine ⟨add_mem h.1 h'.1, fun u => ?_⟩
  have e1 : Γ.M.co.rho W.ψ u (Φ + Φ') = Γ.M.co.rho W.ψ u Φ + Γ.M.co.rho W.ψ u Φ' := by
    funext x; simp only [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, Pi.add_apply]; ring
  rw [e1, GlobalTheory.WeilM.thetaSum_add _ (GlobalTheory.HeisSchA.rho_mem_schA _ _ hψ _ _ h.1) (GlobalTheory.HeisSchA.rho_mem_schA _ _ hψ _ _ h'.1),
    h.2, h'.2, Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]

theorem datumA_smul (c : ℂ) {τ : TotT G (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.routeA t i j)} {Φ} (h : IsDatumA W e Γ τ Φ) :
    IsDatumA W e Γ (c • τ) (c • Φ) := by
  refine ⟨Submodule.smul_mem _ c h.1, fun u => ?_⟩
  have e1 : Γ.M.co.rho W.ψ u (c • Φ) = c • Γ.M.co.rho W.ψ u Φ := by
    funext x; simp only [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, Pi.smul_apply, smul_eq_mul]; ring
  rw [e1, GlobalTheory.WeilM.thetaSum_smul, h.2, Finsupp.sum_smul_index' (fun _ => zero_mul _), Finsupp.mul_sum]
  simp only [smul_eq_mul, mul_assoc]

end Datum

section Pure

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ)

theorem pure_zero : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (0 : SInf F κ) φ = 0 := by
  funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]

theorem pure_add (f f' : SInf F κ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f + f') φ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ + GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f' φ := by
  funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, add_mul]

theorem pure_smul (c : ℂ) (f : SInf F κ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c • f) φ = c • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ := by
  funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc]

end Pure

theorem datum_real : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (M : Vol G)
    (e : Num G i j) (Bs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
    (om : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (h : IsTripleOf W M t i j e Bs Γ X), IsTriple Bs Γ X om om' → ∀ n Φ τ τ', HasFlip B t ρ i j n Φ τ τ' →
    ∀ φ, IsFinPart Γ.M X.T φ → ∀ f₀, f₀ ≠ 0 → Γ.M.IsGauss Bs.ψ Bs.emb f₀ → IsDatumA W e Γ τ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ φ) →
    ∀ f ∈ Γ.M.Pol Bs.ψ Bs.emb, ∃ a, IsDatumA W e Γ (tensT W a τ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) := by
  intro D T L sc G μ₀ hL W B ρ t i j M e Bs Γ X om om' h hT n Φ τ τ' hF φ hφ f₀ hf₀ hG hD
  have hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd W.ψ := h.ψ ▸ hT.base.std
  change TotT G (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.routeA t i j) at τ
  let N : Submodule ℂ (SInf D.host.F (Fin (spW G i j).rank × Fin ((spW G i j).rank + (spW₁ G i j).rank))) :=
    { carrier := {f | ∃ a, IsDatumA W e Γ (tensT W a τ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ)}
      zero_mem' := ⟨0, by rw [tensT_zero, pure_zero]; exact isDatumA_zero W e Γ⟩
      add_mem' := by
        rintro f f' ⟨a, ha⟩ ⟨a', ha'⟩
        exact ⟨a + a', by rw [tensT_add, pure_add]; exact datumA_add W e Γ hψ ha ha'⟩
      smul_mem' := by
        rintro c f ⟨a, ha⟩
        exact ⟨c • a, by rw [tensT_smul, pure_smul]; exact datumA_smul W e Γ c ha⟩ }
  have h0 : f₀ ∈ N := ⟨Finsupp.single onePol 1, by rw [tensT_one]; exact hD⟩
  have hle : Γ.M.Pol Bs.ψ Bs.emb ≤ N := sInf_le ⟨fun g hg => by
      obtain ⟨c, rfl⟩ := GlobalTheory.T.fockVacua_triple_proportional_to_nonzero Bs Γ X om om' hT f₀ hf₀ hG g hg
      exact N.smul_mem c h0,
    fun u hu f ⟨a, ha⟩ f₁ h1 => GlobalTheory.T.archimedeanSchwartzDatum_stable_heisenbergDerivative hL W B ρ t i j M e Bs Γ X om om' h hT n Φ τ τ' hF φ hφ f a ha u hu f₁ h1⟩
  exact fun f hf => hle hf

end GlobalTheory.BigNZ.DatReal
end
end
