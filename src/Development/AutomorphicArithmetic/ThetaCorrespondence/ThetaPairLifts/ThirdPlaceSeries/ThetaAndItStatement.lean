module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.InverseLevelCardinality
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BiThetaOfVac
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationCommFockPolynomialVectors
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtYAndItYOfPair
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GEqBase
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnesRepresent
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsBicharPairing
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsThetaFunOOfThetaAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtYAndItYOfPair
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelStepVectorEqHeisenbergCombinationVacuum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisOFinsetSum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryChainDescent
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.VacuumMemSpanHeisenbergTranslatesOfNeZeroStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpOfOrder
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCoordLatticeOfSelfDualFrame

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BaseChainTopThetaFunctions

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BaseChainTop

variable {D : D7}

theorem comb_pureTensorO {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} (hψ : IsStdChar D ψ (-1))
    (hθ : IsInfFam θ) (sS sT BS BT) {e : WO S T →₀ ℂ} (he : IsFinComb e) {f₀ : WO S T → ℂ}
    (hf₀ : IsThetaFunO ψ S T f₀) (P) :
    comb ψ S T e (pureTensorO ψ θ S T sS sT BS BT f₀ P) = pureTensorO ψ θ S T sS sT BS BT (comb ψ S T e f₀) P := by
  let q := e.support.equivFin
  have key := (GlobalTheory.FockFiniteHeis.heis_comb_pureTensorO D ψ θ S T hψ hθ sS sT BS BT f₀ hf₀ e.support.card
    (fun i => e (q.symm i).1) (fun i => (q.symm i).1) (fun i => he _ (q.symm i).2) P).1
  have h1 : ∀ g : WO S T → (WO S T → ℂ), ∑ u ∈ e.support, e u • g u = ∑ i, e (q.symm i).1 • g (q.symm i).1 := by
    intro g
    rw [← Finset.sum_coe_sort e.support]
    exact (Equiv.sum_comp q.symm (fun u : e.support => e u.1 • g u.1)).symm
  simp only [comb]
  rw [h1, h1]
  exact key

theorem isItW_of_comb {V W : HSp D} {S S' : D.what₂.Tau → SPar} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
    {M : DSModel V S} {M' : DSModel W S'} {χS χT : (AE D)ˣ →* Circle}
    {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} (hω : IsWeilDatumO ψ V W χS χT ω) (hθ : IsInfFam θ)
    {f g : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) {b : WO V W →₀ ℂ} (hb : IsFinComb b) (hg : comb ψ V W b f = g)
    {It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M}
    (hI : IsItW θ M M' ω (pureTensorO ψ θ V W (cart M) (cart M') (onb M) (onb M') g) It) :
    IsItW θ M M' ω (pureTensorO ψ θ V W (cart M) (cart M') (onb M) (onb M') f) It := by
  have hψ : IsStdChar D ψ (-1) := hω.std
  have hpt : ∀ φ, IsThetaFunO ψ V W (pureTensorO ψ θ V W (cart M) (cart M') (onb M) (onb M') f φ) := fun φ =>
    GlobalTheory.Chain.InnerSteps.theta_pureTensorO hψ hθ _ _ _ _ hf φ
  have hrel : ∀ φ, comb ψ V W b (pureTensorO ψ θ V W (cart M) (cart M') (onb M) (onb M') f φ) =
      pureTensorO ψ θ V W (cart M) (cart M') (onb M) (onb M') g φ := fun φ => by
    rw [← hg]
    exact comb_pureTensorO hψ hθ _ _ _ _ hb hf φ
  have hcomm : ∀ a ∈ GinfC V, ∀ a' ∈ GinfC W, ∀ φ,
      ω (a, a') (pureTensorO ψ θ V W (cart M) (cart M') (onb M) (onb M') g φ) =
        comb ψ V W b (ω (a, a') (pureTensorO ψ θ V W (cart M) (cart M') (onb M) (onb M') f φ)) := fun a ha a' ha' φ => by
    rw [← hrel, GlobalTheory.FrComb.om_comb hω ha ha' hb (hpt φ)]
  refine ⟨hI.ne, hI.bdd, fun τ x hx φ φ' h v => ?_, fun τ X hX φ φ' hd v => ?_, fun τ y hy φ φ' v v' h hv => ?_,
    fun τ X hX φ φ' v v' hd hD => ?_⟩
  · refine hI.eqK τ x hx φ φ' ?_ v
    rw [hcomm _ (Formalism.IndefR.Eqv.Act.atTau_mem θ τ x) 1 (one_mem _) φ, ← h, hrel]
  · refine hI.eqg τ X hX φ φ' (fun z => ?_) v
    have e1 : (fun t : ℝ => ω (oneP θ V τ X t, 1) (pureTensorO ψ θ V W (cart M) (cart M') (onb M) (onb M') g φ) z) =
        fun t => ∑ x ∈ b.support, b x * (ψ (symplOH V W z x) *
          ω (oneP θ V τ X t, 1) (pureTensorO ψ θ V W (cart M) (cart M') (onb M) (onb M') f φ) (z + x)) := funext fun t => by
      rw [hcomm _ (Formalism.IndefR.Eqv.Act.oneP_mem θ τ X t) 1 (one_mem _) φ, GlobalTheory.FrComb.comb_apply]
    rw [e1, ← hrel φ', GlobalTheory.FrComb.comb_apply]
    exact HasDerivAt.fun_sum fun x _ => ((hd (z + x)).const_mul _).const_mul _
  · refine hI.invK τ y hy φ φ' v v' ?_ hv
    rw [hcomm 1 (one_mem _) _ (Formalism.IndefR.Eqv.Act.atTau_mem θ τ y) φ, ← h, hrel]
  · refine hI.invg τ X hX φ φ' v v' (fun z => ?_) hD
    have e1 : (fun t : ℝ => ω (1, oneP θ W τ X t) (pureTensorO ψ θ V W (cart M) (cart M') (onb M) (onb M') g φ) z) =
        fun t => ∑ x ∈ b.support, b x * (ψ (symplOH V W z x) *
          ω (1, oneP θ W τ X t) (pureTensorO ψ θ V W (cart M) (cart M') (onb M) (onb M') f φ) (z + x)) := funext fun t => by
      rw [hcomm 1 (one_mem _) _ (Formalism.IndefR.Eqv.Act.oneP_mem θ τ X t) φ, GlobalTheory.FrComb.comb_apply]
    rw [e1, ← hrel φ', GlobalTheory.FrComb.comb_apply]
    exact HasDerivAt.fun_sum fun x _ => ((hd (z + x)).const_mul _).const_mul _

end GlobalTheory.BaseChainTop

namespace GlobalTheory.BaseChainTop

end GlobalTheory.BaseChainTop
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TopStepVectorTheta

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TopConv

variable {D : D7}

theorem exists_finComb_of_mem_span (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} {f g : WO S T → ℂ}
    (hg : g ∈ Submodule.span ℂ (Set.range fun a : {a : WO S T // a.map (infPart D) = 0} => heisO ψ S T a f)) :
    ∃ b : WO S T →₀ ℂ, IsFinComb b ∧ comb ψ S T b f = g := by
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    refine ⟨Finsupp.single a.1 1, fun u hu => ?_, by rw [GlobalTheory.StepComb.comb_single', one_smul]⟩
    rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hu)]
    exact a.2
  | zero => exact ⟨0, fun u hu => absurd hu (Finsupp.notMem_support_iff.2 rfl), GlobalTheory.StepComb.comb_zero' ψ f⟩
  | add x y _ _ hx hy =>
    obtain ⟨b, hb, rfl⟩ := hx
    obtain ⟨b', hb', rfl⟩ := hy
    exact ⟨b + b', fun u hu => (Finset.mem_union.1 (Finsupp.support_add hu)).elim (hb u) (hb' u),
      GlobalTheory.StepComb.comb_add' ψ b b' f⟩
  | smul a x _ hx =>
    obtain ⟨b, hb, rfl⟩ := hx
    exact ⟨a • b, fun u hu => hb u (Finsupp.support_smul hu), GlobalTheory.StepComb.comb_smul' ψ a b f⟩

theorem isFinComb_comp (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} {b b' : WO S T →₀ ℂ} (hb : IsFinComb b)
    (hb' : IsFinComb b') : ∃ c : WO S T →₀ ℂ, IsFinComb c ∧ ∀ f, comb ψ S T c f = comb ψ S T b (comb ψ S T b' f) := by
  obtain ⟨c, h1, h2⟩ := (GlobalTheory.HeisComb.main D ψ S T).1 b b'
  refine ⟨c, fun w hw => ?_, h2⟩
  obtain ⟨x, hx, y, hy, rfl⟩ := h1 w hw
  ext i j
  have e1 := congrFun (congrFun (hb x hx) i) j
  have e2 := congrFun (congrFun (hb' y hy) i) j
  simp only [Matrix.map_apply, Matrix.zero_apply] at e1 e2 ⊢
  rw [Matrix.add_apply, RingHom.map_add (f := _), e1, e2, add_zero]

end GlobalTheory.TopConv

end

noncomputable section

namespace GlobalTheory.TopConv

theorem comb_mem_span {D : D7} (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} {b : WO S T →₀ ℂ} (hb : IsFinComb b)
    (f : WO S T → ℂ) :
    comb ψ S T b f ∈ Submodule.span ℂ (Set.range fun a : {a : WO S T // a.map (infPart D) = 0} => heisO ψ S T a f) := by
  unfold comb
  exact Submodule.sum_mem _ fun u hu => Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨u, hb u hu⟩, rfl⟩)


end GlobalTheory.TopConv

end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopComb

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.TopConv
variable {D : D7}
end GlobalTheory.TopConv
end
noncomputable section
namespace GlobalTheory.TopConv

theorem top_comb_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m) (v : WO (Yc D (j + 1)) D.sp.X' → ℂ), IsStepVecOf (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D (j + 1)) D.sp.X' (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (cart (_root_.GlobalTheory.Fam.pk_z W).MX) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) (_root_.GlobalTheory.Fam.pk_z W).ΛX ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) (_root_.GlobalTheory.Fam.pk_z W).βX ((_root_.GlobalTheory.Fam.pk_z W).datYt W.P.A3.A.μ0 (j + 1) (_root_.GlobalTheory.Fam.complexLevelStructure W)) ((_root_.GlobalTheory.Fam.pk_z W).chi D.R.m) ((_root_.GlobalTheory.Fam.pk_z W).Q W.P.A3.A.μ0) ((_root_.GlobalTheory.Fam.pk_z W).xiR W.P.A3.A.μ0) (vacT (_root_.GlobalTheory.Fam.pk_z W) j h) v → ∃ b : WO (Yc D (j + 1)) D.sp.X' →₀ ℂ, IsFinComb b ∧ comb (_root_.GlobalTheory.Fam.pk_z W).ψ (Yc D (j + 1)) D.sp.X' b v = Eq.rec (motive := fun n _ => WO (Yc D n) D.sp.X' → ℂ) ((_root_.GlobalTheory.Fam.pk_z W).vX W.P.A3.A.μ0) (idx_top h) := by
  intro D L hT Gi Gl Kc Yd cX ex W hP j h v hv
  have hLev := hP.bot.hyp.2.2.2.1.lev
  obtain ⟨cY, hbY⟩ := hLev.βY (j + 1) (by omega)
  obtain ⟨cX', hbX⟩ := hLev.βX
  have sdY : IsSelfDualC (Yc D (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) :=
    GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hLev.βY (j + 1) (by omega))
  have sdX : IsSelfDualC D.sp.X' (_root_.GlobalTheory.Fam.pk_z W).ΛX := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ hLev.βX
  have hr : (Yc D (j + 1)).rank ≤ D.sp.X'.rank := by
    rw [D.sp.Y_rank _ (min_le_right _ _), D.sp.X'_rank]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (min_le_right _ _)) _
  have key : ∀ n (e : D.R.m - 1 = n), IsStepVecOf (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D n) D.sp.X' (cart ((_root_.GlobalTheory.Fam.pk_z W).MY n)) (cart (_root_.GlobalTheory.Fam.pk_z W).MX)
      ((_root_.GlobalTheory.Fam.pk_z W).ΛY n) (_root_.GlobalTheory.Fam.pk_z W).ΛX ((_root_.GlobalTheory.Fam.pk_z W).βY n) (_root_.GlobalTheory.Fam.pk_z W).βX ((_root_.GlobalTheory.Fam.pk_z W).datYt W.P.A3.A.μ0 n (_root_.GlobalTheory.Fam.pk_z W).triv) ((_root_.GlobalTheory.Fam.pk_z W).chi D.R.m)
      ((_root_.GlobalTheory.Fam.pk_z W).Q W.P.A3.A.μ0) ((_root_.GlobalTheory.Fam.pk_z W).xiR W.P.A3.A.μ0) (Eq.rec (motive := fun n _ => WO (Yc D n) D.sp.X' → ℂ) (_root_.GlobalTheory.Fam.pk_z W).vacX e)
      (Eq.rec (motive := fun n _ => WO (Yc D n) D.sp.X' → ℂ) ((_root_.GlobalTheory.Fam.pk_z W).vX W.P.A3.A.μ0) e) := by
    intro n e
    subst e
    exact W.Q.charW.base.chain.vX _
  have hX := key (j + 1) (idx_top h)
  obtain ⟨d₁, hd₁, e₁⟩ := GlobalTheory.StepComb.exists_comb_of_isStepVecOf _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sdY sdX hbY.1 hbX.1 hX
  obtain ⟨d₂, hd₂, e₂⟩ := GlobalTheory.StepComb.exists_comb_of_isStepVecOf _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sdY sdX hbY.1 hbX.1 hv
  have hv0 : v ≠ 0 := (GlobalTheory.Chain.StepVac.stepVec_vac sdY sdX hr hv).2.1
  have hspan := comb_mem_span (_root_.GlobalTheory.Fam.pk_z W).ψ (GlobalTheory.Fam.VacTheta.isFinComb_of_combAt hd₂) (vacT (_root_.GlobalTheory.Fam.pk_z W) j h)
  rw [← e₂] at hspan
  have hvac := GlobalTheory.T.vacuum_mem_span_heisenbergTranslates_of_ne_zero hv.1 sdY sdX hspan hv0
  obtain ⟨b, hb, hbv⟩ := exists_finComb_of_mem_span _ hvac
  obtain ⟨c, hc, hcc⟩ := isFinComb_comp (_root_.GlobalTheory.Fam.pk_z W).ψ (GlobalTheory.Fam.VacTheta.isFinComb_of_combAt hd₁) hb
  refine ⟨c, hc, ?_⟩
  rw [hcc, hbv]
  exact e₁.symm
end GlobalTheory.TopConv
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopCombStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.top_step_vector_theta_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m) (v : WO (Yc D (j + 1)) D.sp.X' → ℂ), IsStepVecOf (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D (j + 1)) D.sp.X' (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (cart (_root_.GlobalTheory.Fam.pk_z W).MX) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) (_root_.GlobalTheory.Fam.pk_z W).ΛX ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) (_root_.GlobalTheory.Fam.pk_z W).βX ((_root_.GlobalTheory.Fam.pk_z W).datYt W.P.A3.A.μ0 (j + 1) (_root_.GlobalTheory.Fam.complexLevelStructure W)) ((_root_.GlobalTheory.Fam.pk_z W).chi D.R.m) ((_root_.GlobalTheory.Fam.pk_z W).Q W.P.A3.A.μ0) ((_root_.GlobalTheory.Fam.pk_z W).xiR W.P.A3.A.μ0) (vacT (_root_.GlobalTheory.Fam.pk_z W) j h) v → ∃ b : WO (Yc D (j + 1)) D.sp.X' →₀ ℂ, IsFinComb b ∧ comb (_root_.GlobalTheory.Fam.pk_z W).ψ (Yc D (j + 1)) D.sp.X' b v = Eq.rec (motive := fun n _ => WO (Yc D n) D.sp.X' → ℂ) ((_root_.GlobalTheory.Fam.pk_z W).vX W.P.A3.A.μ0) (idx_top h) := by
  first | exact @_root_.GlobalTheory.TopConv.top_comb_alt | exact _root_.GlobalTheory.TopConv.top_comb_alt | (intros; apply _root_.GlobalTheory.TopConv.top_comb_alt <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaAndIt

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.BaseChainTop
variable {D : D7}
end GlobalTheory.BaseChainTop
namespace GlobalTheory.BaseChainTop
theorem theta_and_it_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ j (h : j + 2 * 0 + 2 = D.R.m), (∀ φ, IsThetaFunO (_root_.GlobalTheory.BaseChain.com_z W).ψ (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).V (_root_.GlobalTheory.BaseChain.stageOfSpaceX W).V ((_root_.GlobalTheory.BaseChain.transitionToSpaceX f j h).pt φ)) ∧ IsItW (_root_.GlobalTheory.BaseChain.com_z W).θ (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).M (_root_.GlobalTheory.BaseChain.stageOfSpaceX W).M (_root_.GlobalTheory.BaseChain.transitionToSpaceX f j h).ω (_root_.GlobalTheory.BaseChain.transitionToSpaceX f j h).pt (_root_.GlobalTheory.BaseChain.transitionToSpaceX f j h).It := by
  intro D L hT Gi Gl Kc Yd cX ex W u f hP hR j h
  have hC := Formalism.IndefR.Links.RealDat3.characterisation_of_weak W.Q.charW hP.ex
  have hvT := (hR.row W.P.A3.A.μ0).vT j h
  have hθ : IsInfFam (_root_.GlobalTheory.Fam.pk_z W).θ := hvT.1.2.inf
  have hth : IsThetaFunO (_root_.GlobalTheory.Fam.pk_z W).ψ (Yc D (j + 1)) D.sp.X' ((f.row W.P.A3.A.μ0).vT j h) :=
    GlobalTheory.VecTheta.isThetaFunO_stepVec hvT
  have key : ∀ n (e : D.R.m - 1 = n),
      IsWeilDatumO (_root_.GlobalTheory.Fam.pk_z W).ψ (Yc D n) D.sp.X' (Lift.chrStep ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu W.P.A3.A.μ0) (_root_.GlobalTheory.Fam.pk_z W).eta D.R.m).1
        (Lift.chrStep ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu W.P.A3.A.μ0) (_root_.GlobalTheory.Fam.pk_z W).eta D.R.m).2
        (Eq.rec (motive := fun n _ => Om (Yc D n) D.sp.X') ((_root_.GlobalTheory.Fam.pk_z W).ωX W.P.A3.A.μ0) e) ∧
      IsItW (_root_.GlobalTheory.Fam.pk_z W).θ ((_root_.GlobalTheory.Fam.pk_z W).MY n) (_root_.GlobalTheory.Fam.pk_z W).MX (Eq.rec (motive := fun n _ => Om (Yc D n) D.sp.X') ((_root_.GlobalTheory.Fam.pk_z W).ωX W.P.A3.A.μ0) e)
        (pureTensorO (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D n) D.sp.X' (cart ((_root_.GlobalTheory.Fam.pk_z W).MY n)) (cart (_root_.GlobalTheory.Fam.pk_z W).MX) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY n))
          (onb (_root_.GlobalTheory.Fam.pk_z W).MX) (Eq.rec (motive := fun n _ => WO (Yc D n) D.sp.X' → ℂ) ((_root_.GlobalTheory.Fam.pk_z W).vX W.P.A3.A.μ0) e))
        (Eq.rec (motive := fun n _ => PolF D D.sp.X'.rank (Yc D n).rank →ₗ[ℂ] SmT (_root_.GlobalTheory.Fam.pk_z W).MX →ₗ[ℂ] SmT ((_root_.GlobalTheory.Fam.pk_z W).MY n))
          (_root_.GlobalTheory.Fam.pk_z W).ItX e) := by
    intro n e
    subst e
    exact ⟨hC.chain.ωX _, hC.chain.ItX _⟩
  obtain ⟨hW', hI'⟩ := key (j + 1) (idx_top h)
  obtain ⟨b, hb, hbv⟩ := _root_.GlobalTheory.T.top_step_vector_theta_alt W hP j h _ hvT
  exact ⟨fun φ => GlobalTheory.Chain.InnerSteps.theta_pureTensorO hW'.std hθ _ _ _ _ hth φ, isItW_of_comb hW' hθ hth hb hbv hI'⟩
end GlobalTheory.BaseChainTop
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaAndItStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.base_chain_top_theta_functions_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ j (h : j + 2 * 0 + 2 = D.R.m), (∀ φ, IsThetaFunO (_root_.GlobalTheory.BaseChain.com_z W).ψ (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).V (_root_.GlobalTheory.BaseChain.stageOfSpaceX W).V ((_root_.GlobalTheory.BaseChain.transitionToSpaceX f j h).pt φ)) ∧ IsItW (_root_.GlobalTheory.BaseChain.com_z W).θ (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).M (_root_.GlobalTheory.BaseChain.stageOfSpaceX W).M (_root_.GlobalTheory.BaseChain.transitionToSpaceX f j h).ω (_root_.GlobalTheory.BaseChain.transitionToSpaceX f j h).pt (_root_.GlobalTheory.BaseChain.transitionToSpaceX f j h).It := by
  first | exact @_root_.GlobalTheory.BaseChainTop.theta_and_it_alt | exact _root_.GlobalTheory.BaseChainTop.theta_and_it_alt | (intros; apply _root_.GlobalTheory.BaseChainTop.theta_and_it_alt <;> assumption)
end
end
end
