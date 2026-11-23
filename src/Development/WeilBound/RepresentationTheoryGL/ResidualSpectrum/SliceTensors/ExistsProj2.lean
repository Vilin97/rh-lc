module

public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.LsProps
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionTensorProductHasFiniteLength
public import Development.WeilBound.CoreStatements.AutomorphicKernels.ResidualSpectrumHilbertSum.ResidualSpectrumTensors.LeviMaps
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFixedOfMemISup
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.ExistsNeZeroOfISup

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.ResidualSpectrumHilbertSum.ResidualSpectrumTensors.MultilinearMemOfSpan

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.RSHS.LocalComponentTwist

open PositivityTheory.RSHS.LeviInductionForms

theorem multilinear_mem_of_span {ι : Type} [Fintype ι] {M : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
    {Y : Type} [AddCommGroup Y] [Module ℂ Y] (P : (∀ i, M i) →ₘₗ[ℂ] Y) (s : ∀ i, Set (M i)) (W : Submodule ℂ Y)
    (h : ∀ x : ∀ i, M i, (∀ i, x i ∈ s i) → P x ∈ W) (x : ∀ i, M i) (hx : ∀ i, x i ∈ Submodule.span ℂ (s i)) :
    P x ∈ W := by
  classical
  have key : ∀ t : Finset ι, ∀ x : ∀ i, M i, (∀ i ∈ t, x i ∈ Submodule.span ℂ (s i)) → (∀ i ∉ t, x i ∈ s i) →
      P x ∈ W := by
    intro t
    induction t using Finset.induction_on with
    | empty => intro x _ h2; exact h x fun i => h2 i (by simp)
    | insert a t ha ih =>
      intro x h1 h2
      have hle : Submodule.span ℂ (s a) ≤ W.comap (P.toLinearMap x a) := by
        refine Submodule.span_le.2 fun y hy => ?_
        change P (Function.update x a y) ∈ W
        refine ih _ (fun i hi => ?_) fun i hi => ?_
        · have hne : i ≠ a := fun e => ha (e ▸ hi)
          rw [Function.update_of_ne hne]
          exact h1 i (Finset.mem_insert_of_mem hi)
        · by_cases e : i = a
          · subst e; rw [Function.update_self]; exact hy
          · rw [Function.update_of_ne e]
            exact h2 i fun hm => (Finset.mem_insert.1 hm).elim e hi
      have h3 : P (Function.update x a (x a)) ∈ W := hle (h1 a (Finset.mem_insert_self a t))
      rwa [Function.update_eq_self] at h3
  exact key Finset.univ x (fun i _ => hx i) fun i hi => absurd (Finset.mem_univ i) hi

def prodMap {ι : Type} [Fintype ι] {G : ι → Type} (S : ∀ i, Submodule ℂ (G i → ℂ)) :
    (∀ i, S i) →ₘₗ[ℂ] ((∀ i, G i) → ℂ) :=
  MultilinearMap.pi fun m => (MultilinearMap.mkPiAlgebra ℂ ι ℂ).compLinearMap
    fun i => (LinearMap.proj (m i) : (G i → ℂ) →ₗ[ℂ] ℂ) ∘ₗ (S i).subtype

theorem prodMap_apply {ι : Type} [Fintype ι] {G : ι → Type} (S : ∀ i, Submodule ℂ (G i → ℂ)) (φ : ∀ i, S i) :
    prodMap S φ = fun m => ∏ i, (φ i).1 (m i) := rfl

theorem span_le_iSup {ι : Type} [Fintype ι] {G Γ X A : ι → Type} [∀ i, Group (G i)] [∀ i, Group (Γ i)]
    [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)] (S : ∀ i, Submodule ℂ (G i → ℂ)) (V : ∀ i, Submodule ℂ (S i))
    (j : ∀ i, Γ i → G i) (ρ : ∀ i, Representation ℂ (Γ i) (X i)) (f : ∀ i, A i → X i →ₗ[ℂ] S i)
    (hf : ∀ i a v, f i a v ∈ V i) (he : ∀ i a g v y, (f i a (ρ i g v)).1 y = (f i a v).1 (y * j i g))
    (hV : ∀ i, V i ≤ ⨆ a, LinearMap.range (f i a)) (T : Submodule ℂ ((∀ i, G i) → ℂ))
    (hT : T = Submodule.span ℂ {F | ∃ φ : ∀ i, V i, F = fun m => ∏ i, (φ i).1.1 (m i)}) :
    T ≤ ⨆ Φ : {Φ : (PiTensorProduct ℂ X) →ₗ[ℂ] ((∀ i, G i) → ℂ) // (∀ v, Φ v ∈ T) ∧
      ∀ g v, Φ (piTensor ρ g v) = fun m => Φ v fun i => m i * j i (g i)}, LinearMap.range Φ.1 := by
  refine hT.le.trans (Submodule.span_le.2 ?_)
  rintro _ ⟨φ, rfl⟩
  refine multilinear_mem_of_span (prodMap S) (fun i => {y | ∃ a v, f i a v = y}) _ (fun x hx => ?_)
    (fun i => (φ i).1) fun i => ?_
  · choose a v hx using hx
    let Φ : (PiTensorProduct ℂ X) →ₗ[ℂ] ((∀ i, G i) → ℂ) :=
      PiTensorProduct.lift ((prodMap S).compLinearMap fun i => f i (a i))
    have hΦ : ∀ u : ∀ i, X i, Φ (PiTensorProduct.tprod ℂ u) = fun m => ∏ i, (f i (a i) (u i)).1 (m i) := fun u => by
      simp only [Φ, PiTensorProduct.lift.tprod]
      rfl
    refine Submodule.mem_iSup_of_mem ⟨Φ, fun t => ?_, fun g t => ?_⟩ ⟨PiTensorProduct.tprod ℂ v, ?_⟩
    · induction t using PiTensorProduct.induction_on with
      | smul_tprod r u =>
        rw [map_smul, hΦ, hT]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨fun i => ⟨f i (a i) (u i), hf i _ _⟩, rfl⟩)
      | add x y h1 h2 =>
        rw [map_add]
        exact add_mem h1 h2
    · induction t using PiTensorProduct.induction_on with
      | smul_tprod r u =>
        rw [map_smul, map_smul, map_smul, piTensor_tprod, hΦ, hΦ]
        funext m
        simp only [Pi.smul_apply, he]
      | add x y h1 h2 => rw [map_add (f := _), map_add (f := _), map_add (f := _), h1, h2]; rfl
    · change Φ _ = _
      rw [hΦ, prodMap_apply]
      simp only [hx]
  · refine (hV i).trans (iSup_le fun a => ?_) (φ i).2
    rintro _ ⟨v, rfl⟩
    exact Submodule.subset_span ⟨a, v, rfl⟩

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ}

theorem tensorForms_le_iSup {c : ℕ} {n : Fin c → ℕ} (π : ∀ i, CuspSub E (n i)) {w : HeightOneSpectrum (𝓞 E)}
    (τ : ∀ i, SmIrr (GL (Fin (n i)) (w.adicCompletion E))) (hτ : ∀ i, (π i).IsLocComp w (τ i)) :
    tensorForms π ≤ ⨆ Φ : LeviMaps (tensorForms π) w (piTensor fun i => (τ i).ρ), LinearMap.range Φ.1 :=
  span_le_iSup (A := fun i => LocSph.Maps (π i) w (τ i)) (fun i => Sm E (n i)) (fun i => (π i).V)
    (fun i g => finGL E (n i) (locGL E (n i) w g)) (fun i => (τ i).ρ) (fun _ a => a.1) (fun _ a => a.2.1)
    (fun _ a g v y => by rw [a.2.2]; rfl) (fun i => (LocSph.iSup_range_eq (π i) w (τ i) (hτ i)).ge) _ rfl

end PositivityTheory.RSHS.LocalComponentTwist

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.ExistsProj2

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.Rs.PLsProj2

theorem proj_fun {Y Γ X : Type} [Group Γ] [AddCommGroup X] [Module ℂ X] (act : Γ → Y → Y)
    (ρ : Representation ℂ Γ X) (hρ : ρ.IsIrreducible) (T : Submodule ℂ (Y → ℂ))
    (hle : T ≤ ⨆ Φ : {Φ : X →ₗ[ℂ] (Y → ℂ) // (∀ v, Φ v ∈ T) ∧ ∀ g v, Φ (ρ g v) = fun m => Φ v (act g m)},
      LinearMap.range Φ.1) (t : Y → ℂ) (ht : t ∈ T) (h0 : t ≠ 0) :
    ∃ p : (Y → ℂ) →ₗ[ℂ] X, p t ≠ 0 ∧ ∀ g, ∀ s ∈ T, p (fun m => s (act g m)) = ρ g (p s) := by
  have key := PLsAbs2.exists_proj (fun g => LinearMap.funLeft ℂ ℂ (act g)) ρ hρ
    (fun Φ : {Φ : X →ₗ[ℂ] (Y → ℂ) // (∀ v, Φ v ∈ T) ∧ ∀ g v, Φ (ρ g v) = fun m => Φ v (act g m)} => Φ.1)
    (fun Φ => Φ.2.2) (hle ht) h0
  obtain ⟨p, hp, he⟩ := key
  exact ⟨p, hp, fun g s hs => he g s (hle hs)⟩

theorem schur {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
    (τ : SmIrr (GL (Fin n) k)) (φ : τ.V →ₗ[ℂ] τ.V) (hφ : ∀ g x, φ (τ.ρ g x) = τ.ρ g (φ x)) :
    ∃ c : ℂ, φ = c • LinearMap.id := by
  obtain ⟨z, hz⟩ := GlobalTheory.LocGL.schur_GL τ.smooth τ.irred ⟨φ, fun g => LinearMap.ext (hφ g)⟩
  exact ⟨z, LinearMap.ext hz⟩

theorem irr {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {c : ℕ}
    {n : Fin c → ℕ} (τ : ∀ i, SmIrr (GL (Fin (n i)) k)) : (piTensor fun i => (τ i).ρ).IsIrreducible :=
  GlobalTheory.ProdFiniteLength.piTensor_isIrreducible_of_schur _ (fun i => (τ i).irred) fun i => schur (τ i)

end PositivityTheory.Rg.Rs.PLsProj2

namespace PositivityTheory.Rg.Rs

theorem existsProj2 : PositivityTheory.RSHS.LS.ExistsProj := fun E _ _ _ _ n π w τ hτ =>
  PLsProj2.proj_fun (Γ := ∀ i, GL (Fin (n i)) (w.adicCompletion E))
    (fun g (m : ∀ i, GA E (n i)) i => m i * finGL E (n i) (locGL E (n i) w (g i)))
    (piTensor fun i => (τ i).ρ) (PLsProj2.irr τ) (tensorForms π) (PositivityTheory.RSHS.LocalComponentTwist.tensorForms_le_iSup π τ hτ)

end PositivityTheory.Rg.Rs

end
end
end
