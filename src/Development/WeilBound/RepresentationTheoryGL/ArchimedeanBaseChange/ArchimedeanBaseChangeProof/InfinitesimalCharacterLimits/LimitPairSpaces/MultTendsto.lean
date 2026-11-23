module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LimitPairSpaces.TensorSpanEqPairSpace
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqOfIsLocCompGL
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinStable
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatAbsoluteCharacter
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
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NodeFunctionLeviDecompositionStatement
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PIndMapB
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PIndMapC
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PIndMapD
import Mathlib.Tactic.Linter.Style
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NodeFunctionLeviDecompositionStatement
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatAbsoluteCharacterStatement

section

@[expose] public section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

theorem _root_.GlobalTheory.T.flat_absolute_character : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ) (w : ℂ), FlatFn (absFn (E := E) N w) := by
  first | exact @GlobalTheory.CompanionTheory.LimV.absFn_flat | exact GlobalTheory.CompanionTheory.LimV.absFn_flat | (intros; apply GlobalTheory.CompanionTheory.LimV.absFn_flat <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatNodeFunction

section

@[expose] public section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.LimV.NodeFlat

theorem flatFn_nodeFn : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {r s : ℕ} (e₁ : GA E r → ℂ) (e₂ : GA E s → ℂ), FlatFn e₁ → FlatFn e₂ → FlatFn (nodeFn e₁ e₂) := by
  intro E _ _ _ r s e₁ e₂ h₁ h₂
  have ap : ∀ (u : BlockIx (r + s) r → Ad E) (m : GA E r × GA E s) (k : Kinf E (r + s))
      (c : GL (Fin (r + s)) (Af E)), c ∈ GlobalTheory.CompanionTheory.LimV.KO E (r + s) →
      nodeFn e₁ e₂ (unip u * lev (Ad E) r s m * cf (r + s) k c) = e₁ m.1 * e₂ m.2 :=
    fun u m k c hc => GlobalTheory.T.node_function_levi_decomposition e₁ e₂ h₁ h₂ u m k c hc
  have hleft : ∀ (v : BlockIx (r + s) r → Ad E) (x : GA E (r + s)),
      nodeFn e₁ e₂ (unip v * x) = nodeFn e₁ e₂ x := by
    intro v x
    obtain ⟨u, m, k, c, hc, rfl⟩ := exists_iw x
    rw [← mul_assoc, ← mul_assoc, ← PositivityTheory.Rg.Rs.InducedTensorMap.D.unip_add', ap _ _ _ _ hc, ap _ _ _ _ hc]
  have hright : ∀ (x : GA E (r + s)) (k' : Kinf E (r + s)), ∀ c' ∈ GlobalTheory.CompanionTheory.LimV.KO E (r + s),
      nodeFn e₁ e₂ (x * cf (r + s) k' c') = nodeFn e₁ e₂ x := by
    intro x k' c' hc'
    obtain ⟨u, m, k, c, hc, rfl⟩ := exists_iw x
    rw [mul_assoc _ (cf (r + s) k c), PositivityTheory.Rg.Rs.InducedTensorMap.cf_mul,
      ap _ _ _ _ ((GlobalTheory.CompanionTheory.LimV.KO E (r + s)).mul_mem hc hc'), ap _ _ _ _ hc]
  have key : ∀ m : GA E r × GA E s,
      ContDiffAt ℝ ∞ (chart (nodeFn e₁ e₂) (lev (Ad E) r s m)) (oneL E (r + s)) := by
    intro m
    obtain ⟨b₁, b₂, κ, u, hb₁, hb₂, hκ, hb₁1, hb₂1, hκ1, hloc⟩ := exists_local E r s
    have c₁ : ContDiffAt ℝ ∞ (fun y => e₁ (m.1 * infGL E r (b₁ y))) (oneL E (r + s)) := by
      have := (contDiffAt_chart h₁.sm m.1 (val_mem_invSet (b₁ (oneL E (r + s))))).comp (oneL E (r + s)) hb₁
      simpa only [Function.comp_def, chart_val] using this
    have c₂ : ContDiffAt ℝ ∞ (fun y => e₂ (m.2 * infGL E s (b₂ y))) (oneL E (r + s)) := by
      have := (contDiffAt_chart h₂.sm m.2 (val_mem_invSet (b₂ (oneL E (r + s))))).comp (oneL E (r + s)) hb₂
      simpa only [Function.comp_def, chart_val] using this
    refine ContDiffAt.congr_of_eventuallyEq (c₁.mul c₂) ?_
    filter_upwards [hloc] with y hy
    have hyw : y = toL (unip (u y) * lev (Cinf E) r s (b₁ y, b₂ y) * Unitary.toUnits (κ y)).val := by
      show y = toL ((unip (u y) * lev (Cinf E) r s (b₁ y, b₂ y)).val * (κ y).1)
      rw [← hy]
      rfl
    conv_lhs => rw [hyw, chart_val]
    obtain ⟨v, hv⟩ := lev_mul_infGL m (u y) (b₁ y) (b₂ y) (κ y)
    rw [hv, ap _ _ _ _ ((GlobalTheory.CompanionTheory.LimV.KO E (r + s)).one_mem)]
  refine ⟨fun x => ?_, hright, ?_⟩
  · obtain ⟨u, m, k, c, hc, rfl⟩ := exists_iw x
    rw [ap _ _ _ _ hc]
    exact mul_ne_zero (h₁.ne _) (h₂.ne _)
  refine GlobalTheory.DiscSMO.mem_Sm_of_one fun x => ?_
  obtain ⟨u, m, k, g, hg, rfl⟩ := exists_iw x
  have e1 : chart (nodeFn e₁ e₂) (unip u * lev (Ad E) r s m * cf (r + s) k g) =
      chart (nodeFn e₁ e₂) (lev (Ad E) r s m * cf (r + s) k g) := by
    funext z
    unfold chart
    split_ifs
    · simp only [mul_assoc]
      exact hleft u _
    · rfl
  rw [e1, cf, infGL_comm, ← mul_assoc]
  refine GlobalTheory.DiscSMO.contDiffAt_chart_mul ?_
  rw [← chart_rt_fin]
  have e2 : (fun x => (fun x => nodeFn e₁ e₂ (x * infGL E (r + s) (Unitary.toUnits k))) (x * finGL E (r + s) g)) =
      nodeFn e₁ e₂ := by
    funext z
    show nodeFn e₁ e₂ (z * finGL E (r + s) g * infGL E (r + s) (Unitary.toUnits k)) = nodeFn e₁ e₂ z
    rw [mul_assoc, ← infGL_comm]
    exact hright z k g hg
  rw [e2]
  exact key m

end GlobalTheory.CompanionTheory.LimV.NodeFlat
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatNodeFunctionStatement

section

@[expose] public section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

theorem _root_.GlobalTheory.T.flat_node_function : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {r s : ℕ} (e₁ : GA E r → ℂ) (e₂ : GA E s → ℂ), FlatFn e₁ → FlatFn e₂ → FlatFn (nodeFn e₁ e₂) := by
  first | exact @GlobalTheory.CompanionTheory.LimV.NodeFlat.flatFn_nodeFn | exact GlobalTheory.CompanionTheory.LimV.NodeFlat.flatFn_nodeFn | (intros; apply GlobalTheory.CompanionTheory.LimV.NodeFlat.flatFn_nodeFn <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TendstoAbsoluteCharacterOne

section

@[expose] public section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.LimV

theorem absFn_tendsto_one : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ) (x : GA E N) (w : ℕ → ℂ), Tendsto w atTop (𝓝 0) → Tendsto (fun k => absFn N (w k) x) atTop (𝓝 1) := by
  intro E _ _ _ N x w hw
  have hL : ∀ t : ℂ, absFn N t x =
      Complex.exp (t * (GlobalTheory.Mem.Chr.CharModel.logNorm E (GeneralLinearGroup.det x) : ℝ)) := by
    intro t
    exact GlobalTheory.Mem.Chr.CharModel.absHom_val E t (GeneralLinearGroup.det x)
  have h0 : Tendsto (fun k => Complex.exp (w k *
      (GlobalTheory.Mem.Chr.CharModel.logNorm E (GeneralLinearGroup.det x) : ℝ))) atTop
      (𝓝 (Complex.exp (0 * (GlobalTheory.Mem.Chr.CharModel.logNorm E (GeneralLinearGroup.det x) : ℝ)))) :=
    (Complex.continuous_exp.tendsto _).comp (hw.mul_const _)
  simpa [hL] using h0

end GlobalTheory.CompanionTheory.LimV
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TendstoAbsoluteCharacterOneStatement

section

@[expose] public section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

theorem _root_.GlobalTheory.T.tendsto_absolute_character_one : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ) (x : GA E N) (w : ℕ → ℂ), Tendsto w atTop (𝓝 0) → Tendsto (fun k => absFn N (w k) x) atTop (𝓝 1) := by
  first | exact @GlobalTheory.CompanionTheory.LimV.absFn_tendsto_one | exact GlobalTheory.CompanionTheory.LimV.absFn_tendsto_one | (intros; apply GlobalTheory.CompanionTheory.LimV.absFn_tendsto_one <;> assumption)
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LimitPairSpaces.MultTendsto

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.LV

open PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.E

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem mul_mem_Sm' {N : ℕ} {f g : GA E N → ℂ} (hf : f ∈ Sm E N) (hg : g ∈ Sm E N) :
    (fun x => f x * g x) ∈ Sm E N := by
  refine GlobalTheory.DiscSMO.mem_Sm_of_one fun x => ?_
  have h0 : oneL E N ∈ invSet E N := by
    have := val_mem_invSet (E := E) (1 : GL (Fin N) (Cinf E))
    rwa [Units.val_one] at this
  refine ((contDiffAt_chart hf x h0).mul (contDiffAt_chart hg x h0)).congr_of_eventuallyEq ?_
  filter_upwards [isOpen_invSet.mem_nhds h0] with y hy
  obtain ⟨u, hu⟩ := hy
  have hy' : y = toL (u : GL (Fin N) (Cinf E)).val := by rw [hu]; rfl
  rw [hy', chart_val, chart_val, chart_val]

theorem mult_flat {N : ℕ} (b : Tr E N) (γ : ℕ → ℂ) : GlobalTheory.CompanionTheory.LimV.FlatFn (mult b γ) := by
  induction b generalizing γ with
  | leaf V z => exact GlobalTheory.T.flat_absolute_character _ _
  | node t₁ t₂ ih₁ ih₂ => exact GlobalTheory.T.flat_node_function _ _ (ih₁ _) (ih₂ _)

theorem mult_rinv {N : ℕ} (b : Tr E N) (γ : ℕ → ℂ) (x : GA E N) (k : Kinf E N) {c : GL (Fin N) (Af E)}
    (hc : c ∈ Cint E N) : mult b γ (x * InducedTensorMap.cf N k c) = mult b γ x :=
  (mult_flat b γ).rinv x k c hc

theorem mult_node {r s : ℕ} (t₁ : Tr E r) (t₂ : Tr E s) (γ : ℕ → ℂ) (u : BlockIx (r + s) r → Ad E)
    (m : GA E r × GA E s) (k : Kinf E (r + s)) {c : GL (Fin (r + s)) (Af E)} (hc : c ∈ Cint E (r + s)) :
    mult (Tr.node t₁ t₂) γ (unip u * lev (Ad E) r s m * InducedTensorMap.cf (r + s) k c) =
      mult t₁ γ m.1 * mult t₂ (fun i => γ (i + t₁.twists.length)) m.2 :=
  GlobalTheory.T.node_function_levi_decomposition _ _ (mult_flat _ _) (mult_flat _ _) u m k c hc

theorem mult_ne {N : ℕ} (b : Tr E N) (γ : ℕ → ℂ) (x : GA E N) : mult b γ x ≠ 0 :=
  (mult_flat b γ).ne x

theorem mult_tendsto {N : ℕ} (b : Tr E N) (γ : ℕ → ℕ → ℂ) (hγ : ∀ i, Tendsto (fun k => γ k i) atTop (𝓝 0))
    (x : GA E N) : Tendsto (fun k => mult b (γ k) x) atTop (𝓝 1) := by
  induction b generalizing γ with
  | leaf V z => exact GlobalTheory.T.tendsto_absolute_character_one _ x (fun k => γ k 0) (hγ 0)
  | node t₁ t₂ ih₁ ih₂ =>
    have h := (ih₁ γ hγ (GlobalTheory.CompanionTheory.LimV.leviOf x).1).mul
      (ih₂ (fun k i => γ k (i + t₁.twists.length)) (fun i => hγ _) (GlobalTheory.CompanionTheory.LimV.leviOf x).2)
    rw [one_mul] at h
    exact h

theorem mult_mem_Sm {N : ℕ} (b : Tr E N) (γ : ℕ → ℂ) : mult b γ ∈ Sm E N :=
  (mult_flat b γ).sm

end PositivityTheory.Rg.BcB.SpectralAccumulation.LV

end
end
end
