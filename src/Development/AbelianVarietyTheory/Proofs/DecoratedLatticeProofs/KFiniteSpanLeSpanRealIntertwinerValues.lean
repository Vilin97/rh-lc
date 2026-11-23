module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaSourceAction
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteSupport
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesPureInnerProductsTensorProduct
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SobolevFormEqZeroOnSmoothOfKFiniteDiscreteSeries
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KFiniteVectorsDiscreteSeriesSmoothAbsolutelyIrre
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PiTensorSubmoduleEqTopOfAbsolutelyIrreducibleSta
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealIntertwinerValuesKFiniteStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntegralForm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InclTprodUpdate
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieActionFockOperatorsScalarsTraceStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRealIntertwinerNeZeroKFiniteTensor

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Chain.IoLift.ItNe

open GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace

theorem exists_ne_zero_inclK : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (pt : PolF D W.rank V.rank → (WO V W → ℂ)) (It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M), IsItW θ M M' ω pt It → ∀ h' : GlobalTheory.Chain.IoLift.KSm M', ∃ φ y, It φ (GlobalTheory.Chain.IoLift.inclK h' y) ≠ 0 := by
  classical
  intro hHC D V W S S' M M' θ ω pt It hIt h'
  apply Classical.byContradiction
  intro hcon
  push_neg at hcon
  apply hIt.ne
  have key : ∀ φ (w : ∀ τ, M.H τ) (s : Finset D.what₂.Tau) (v : M'.Vec),
      (∀ τ ∉ s, (v τ : M'.H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M' τ) →
      ellT M w (inclT M (It φ (PiTensorProduct.tprod ℂ v))) = 0 := by
    intro φ w s
    induction s using Finset.induction_on with
    | empty =>
      intro v hv
      have e : PiTensorProduct.tprod ℂ v =
          GlobalTheory.Chain.IoLift.inclK h' (PiTensorProduct.tprod ℂ fun τ => ⟨v τ, hv τ (by simp)⟩) := by
        rw [GlobalTheory.Chain.IoLift.inclK, PiTensorProduct.map_tprod]; rfl
      rw [e, hcon, map_zero, map_zero]
    | insert τ s hτ ih =>
      intro v hv
      obtain ⟨c, hc⟩ := hIt.bdd φ w
      let ℓ₀ : M'.sm τ →ₗ[ℂ] ℂ :=
        (ellT M w ∘ₗ inclT M ∘ₗ It φ) ∘ₗ (PiTensorProduct.tprod ℂ).toLinearMap v τ
      obtain ⟨ℓ, hℓ⟩ := LinearMap.exists_extend ℓ₀
      have hℓv : ∀ y : M'.sm τ, ℓ (y : M'.H τ) =
          ellT M w (inclT M (It φ (PiTensorProduct.tprod ℂ (Function.update v τ y)))) := fun y => by
        have := LinearMap.congr_fun hℓ y
        simpa [ℓ₀, MultilinearMap.toLinearMap_apply] using this
      have hsob : Formalism.L2.Theta.Sobolev₂ (lieAt W τ) (M'.rep τ) ℓ := by
        refine ⟨[[]], c * ∏ ρ ∈ Finset.univ.erase τ, ‖(v ρ : M'.H ρ)‖, by simp, fun u hu => ?_⟩
        have hy : u ∈ M'.sm τ := Submodule.subset_span hu
        have h1 := hc (Function.update v τ ⟨u, hy⟩)
        rw [← hℓv ⟨u, hy⟩] at h1
        have h2 : ∏ ρ, ‖((Function.update v τ ⟨u, hy⟩ ρ : M'.sm ρ) : M'.H ρ)‖ =
            ‖u‖ * ∏ ρ ∈ Finset.univ.erase τ, ‖(v ρ : M'.H ρ)‖ := by
          rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ τ), Function.update_self]
          congr 1
          refine Finset.prod_congr rfl fun ρ hρ => ?_
          rw [Function.update_of_ne (Finset.ne_of_mem_erase hρ)]
        rw [h2] at h1
        simp only [List.map_cons, List.map_nil, List.foldr_nil, List.sum_cons, List.sum_nil, add_zero]
        calc ‖ℓ u‖ ≤ c * (‖u‖ * ∏ ρ ∈ Finset.univ.erase τ, ‖(v ρ : M'.H ρ)‖) := h1
          _ = c * (∏ ρ ∈ Finset.univ.erase τ, ‖(v ρ : M'.H ρ)‖) * ‖u‖ := by ring
      have hk : ∀ u ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M' τ, ℓ u = 0 := by
        intro u hu
        have hy : u ∈ M'.sm τ := h' τ hu
        rw [show u = ((⟨u, hy⟩ : M'.sm τ) : M'.H τ) from rfl, hℓv]
        refine ih _ fun ρ hρ => ?_
        by_cases e : ρ = τ
        · subst e; rw [Function.update_self]; exact hu
        · rw [Function.update_of_ne e]; exact hv ρ (by simp [e, hρ])
      have h0 := GlobalTheory.KFiniteDense.eq_zero_of_kFin hHC D W S' M' τ ℓ hsob hk (v τ) (v τ).2
      rwa [hℓv, Function.update_eq_self] at h0
  refine LinearMap.ext fun φ => LinearMap.ext fun x => ?_
  simp only [LinearMap.zero_apply]
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    rw [map_smul]
    have h0 : It φ (PiTensorProduct.tprod ℂ v) = 0 := by
      refine (tensorLaw D V S M).inj ?_
      rw [map_zero]
      exact (tensorLaw D V S M).sep _ fun w => key φ w Finset.univ v (by simp)
    rw [h0, smul_zero]
  | add a b ha hb => rw [map_add (f := _), ha, hb, add_zero]

end GlobalTheory.Chain.IoLift.ItNe
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRealIntertwinerNeZeroKFiniteTensorStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_realIntertwiner_ne_zero_KFinite_tensor : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (pt : PolF D W.rank V.rank → (WO V W → ℂ)) (It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M), IsItW θ M M' ω pt It → ∀ h' : GlobalTheory.Chain.IoLift.KSm M', ∃ φ y, It φ (GlobalTheory.Chain.IoLift.inclK h' y) ≠ 0 := by
  first | exact @GlobalTheory.Chain.IoLift.ItNe.exists_ne_zero_inclK | exact GlobalTheory.Chain.IoLift.ItNe.exists_ne_zero_inclK | (intros; apply GlobalTheory.Chain.IoLift.ItNe.exists_ne_zero_inclK <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KFiniteVectorsDiscreteSeriesSmoothAbsolutelyIrreStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.kFinite_vectors_discrete_series_smooth_absolutely_irreducible : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau), GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ ≤ M.sm τ ∧ ∃ a : Matrix (Fin V.rank) (Fin V.rank) ℂ → Module.End ℂ (GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ), GlobalTheory.Chain.IoLift.IsKAct M τ a ∧ GlobalTheory.Chain.IoLift.AbsIrr (fun X : lieAt V τ => a X) := by
  first | exact @GlobalTheory.KFinLoc.kFin_smooth_absIrr | exact GlobalTheory.KFinLoc.kFin_smooth_absIrr | (intros; apply GlobalTheory.KFinLoc.kFin_smooth_absIrr <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PiTensorSubmoduleEqTopOfAbsolutelyIrreducibleStaStatement

section

@[expose] public section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.piTensor_submodule_eq_top_of_absolutely_irreducible_stable : ∀ (ι : Type) [Fintype ι] (K : ι → Type) [∀ i, AddCommGroup (K i)] [∀ i, Module ℂ (K i)] (G : ι → Type) (a : ∀ i, G i → Module.End ℂ (K i)), (∀ i, GlobalTheory.Chain.IoLift.AbsIrr (a i)) → ∀ N : Submodule ℂ (PiTensorProduct ℂ K), (∀ i g, ∀ x ∈ N, GlobalTheory.Chain.IoLift.intersection_update_fsHerm_neg_one i (a i g) x ∈ N) → N ≠ ⊥ → N = ⊤ := by
  first | exact @GlobalTheory.TensorIrr.eq_top_of_stable | exact GlobalTheory.TensorIrr.eq_top_of_stable | (intros; apply GlobalTheory.TensorIrr.eq_top_of_stable <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KFiniteSpanLeSpanRealIntertwinerValues

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.ItOnto
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin maxCpt)
open GlobalTheory.Chain.IoLift

theorem kfin_eq {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) :
    GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M τ = kFin M τ := Submodule.span_eq (kFin M τ)

theorem span_le_range {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (h : KSm M) :
    Submodule.span ℂ {w : SmT M | ∃ v : M.Vec, (∀ τ, (v τ : M.H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M τ) ∧
      w = PiTensorProduct.tprod ℂ v} ≤ LinearMap.range (inclK h) := by
  rw [Submodule.span_le]
  rintro _ ⟨v, hv, rfl⟩
  refine ⟨PiTensorProduct.tprod ℂ fun τ => ⟨(v τ : M.H τ), (kfin_eq M τ) ▸ hv τ⟩, ?_⟩
  rw [inclK_tprod]

theorem range_le_span {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (h : KSm M) (y : KT M) :
    inclK h y ∈ Submodule.span ℂ {w : SmT M | ∃ v : M.Vec, (∀ τ, (v τ : M.H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M τ) ∧
      w = PiTensorProduct.tprod ℂ v} := by
  induction y using PiTensorProduct.induction_on with
  | smul_tprod r u =>
    rw [map_smul, inclK_tprod]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, fun τ => (kfin_eq M τ).symm ▸ (u τ).2, rfl⟩)
  | add x y hx hy => rw [map_add]; exact add_mem hx hy

theorem kfinSpan_le_span_it : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (aS aT : D.what₂.Tau → ℚ) (ω : (GA D V × GA D W →* Module.End ℂ (WO V W → ℂ))) (f : WO V W → ℂ) (It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M), IsInfFam θ → IsWeilExp ψ V W aS aT ω → IsVacVec ψ θ M M' f → IsItW θ M M' ω (ptOf ψ θ M M' f) It → (Submodule.span ℂ {w : SmT M | ∃ v : (M).Vec, (∀ τ, (v τ : (M).H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M τ) ∧ w = PiTensorProduct.tprod ℂ v}) ≤ Submodule.span ℂ {w | ∃ P, ∃ v ∈ (Submodule.span ℂ {w : SmT M' | ∃ v : (M').Vec, (∀ τ, (v τ : (M').H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M' τ) ∧ w = PiTensorProduct.tprod ℂ v}), w = It P v} := by
  intro hD hH D V W S S' M M' θ ψ aS aT ω f It hθ hW hf hIt
  choose hs a ha hirr using fun τ => GlobalTheory.T.kFinite_vectors_discrete_series_smooth_absolutely_irreducible hH D V S M τ
  have h : KSm M := hs
  have h' : KSm M' := fun τ => (GlobalTheory.T.kFinite_vectors_discrete_series_smooth_absolutely_irreducible hH D W S' M' τ).1
  have hval := GlobalTheory.T.real_intertwiner_values_kFinite D V W S S' M M' θ ψ aS aT ω f It hθ hW hf hIt
  have inj := inclK_injective h
  obtain ⟨I, hI⟩ : ∃ I : PolF D W.rank V.rank →ₗ[ℂ] KT M' →ₗ[ℂ] KT M,
      ∀ φ y, inclK h (I φ y) = It φ (inclK h' y) := by
    obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ (LinearMap.ker_eq_bot.2 inj)
    refine ⟨(It.compl₂ (inclK h')).compr₂ g, fun φ y => ?_⟩
    obtain ⟨z, hz⟩ := span_le_range M h (hval φ (inclK h' y))
    change inclK h (g (It φ (inclK h' y))) = _
    rw [← hz, ← LinearMap.comp_apply g, hg, LinearMap.id_apply]
  obtain ⟨χS, χT, hω, hexp⟩ := hW
  have hL := fun τ => GlobalTheory.T.lieAction_fockOperators_scalars_trace D V W (Fr.ofModel M) (Fr.ofModel M') θ ψ χS χT ω f τ (aS τ) (aT τ) hθ hω
    (hexp τ).1 (hexp τ).2 (isVacF_of_isVacVec hf)
  have hstep : ∀ τ, ∀ X ∈ lieAt V τ, ∀ φ, ∃ φ', ∀ y, intersection_update_fsHerm_neg_one τ (a τ X) (I φ y) = I φ' y := by
    intro τ X hX φ
    obtain ⟨φ', hd⟩ : ∃ φ', ∀ v, DerT M τ X (It φ v) (It φ' v) := ⟨_, hIt.eqg τ X hX φ _ ((hL τ).1 X hX φ)⟩
    refine ⟨φ', fun y => inj ?_⟩
    have e := hd (inclK h' y)
    rw [← hI] at e
    rw [hI]
    exact derT_unique ((GlobalTheory.Chain.IoLift.FinTensor.kFinTensor D V S M τ h).2.1 _ (ha τ) X hX _) e
  obtain ⟨N, hNd⟩ : ∃ N : Submodule ℂ (KT M), N = Submodule.span ℂ {x | ∃ φ y, I φ y = x} := ⟨_, rfl⟩
  have hN : ∀ τ (X : lieAt V τ), ∀ x ∈ N, intersection_update_fsHerm_neg_one τ (a τ X) x ∈ N := by
    intro τ X x hx
    rw [hNd] at hx ⊢
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨φ, y, rfl⟩ := hx
      obtain ⟨φ', hφ'⟩ := hstep τ X X.2 φ
      exact Submodule.subset_span ⟨φ', y, (hφ' y).symm⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx
  have h0 : N ≠ ⊥ := by
    obtain ⟨φ, y, hne⟩ := GlobalTheory.T.exists_realIntertwiner_ne_zero_KFinite_tensor hH D V W S S' M M' θ ω _ It hIt h'
    intro e
    refine hne ?_
    have : I φ y ∈ N := hNd ▸ Submodule.subset_span ⟨φ, y, rfl⟩
    rw [e, Submodule.mem_bot] at this
    rw [← hI, this, map_zero]
  have htop := GlobalTheory.T.piTensor_submodule_eq_top_of_absolutely_irreducible_stable D.what₂.Tau (fun τ => kFin M τ) (fun τ => lieAt V τ) (fun τ X => a τ X) hirr N hN h0
  intro w hw
  obtain ⟨z, rfl⟩ := span_le_range M h hw
  have hz : z ∈ N := htop ▸ Submodule.mem_top
  rw [hNd] at hz
  clear hw
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨φ, y, rfl⟩ := hx
    exact Submodule.subset_span ⟨φ, inclK h' y, range_le_span M' h' y, (hI φ y)⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

end GlobalTheory.ItOnto
end
end
end
