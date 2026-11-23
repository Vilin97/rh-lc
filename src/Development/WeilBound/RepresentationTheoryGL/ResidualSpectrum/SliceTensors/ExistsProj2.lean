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
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RepresentationTheory.Irreducible
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic.Linter.Style

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

-- Source module: Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.ExistsNeZeroOfISup

section

@[expose] public section

noncomputable section

open scoped MonoidAlgebra

namespace PositivityTheory.Rg.Rs.PLsAbs2

theorem exists_ne_zero_of_iSup {R M S : Type} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup S]
    [Module R S] [IsSimpleModule R S] {ι : Type} (fs : ι → S →ₗ[R] M)
    (htop : ⨆ i, LinearMap.range (fs i) = ⊤) (x : M) (hx : x ≠ 0) : ∃ p : M →ₗ[R] S, p x ≠ 0 := by
  have : IsSemisimpleModule R M := isSemisimpleModule_of_isSemisimpleModule_submodule'
    (fun i => IsSemisimpleModule.of_surjective (fs i).rangeRestrict (fs i).surjective_rangeRestrict) htop
  rcases IsSemisimpleModule.eq_bot_or_exists_simple_le (Submodule.span R {x}) with hC | ⟨A, hAC, hA⟩
  · exact absurd ((Submodule.span_singleton_eq_bot).1 hC) hx
  obtain ⟨h, hh⟩ := IsSemisimpleModule.extension_property A.subtype A.injective_subtype LinearMap.id
  have := hA
  have hA0 : A ≠ ⊥ := ((isSimpleModule_iff_isAtom).1 hA).1
  have hhx : h x ≠ 0 := by
    intro h0
    apply hA0
    have hle : Submodule.span R {x} ≤ LinearMap.ker h := (Submodule.span_singleton_le_iff_mem _ _).2 h0
    refine eq_bot_iff.2 fun a ha => ?_
    have e1 : h a = ⟨a, ha⟩ := LinearMap.congr_fun hh ⟨a, ha⟩
    have e2 : h a = 0 := LinearMap.mem_ker.1 (hle (hAC ha))
    have e3 : (⟨a, ha⟩ : A) = 0 := e1.symm.trans e2
    exact (Submodule.mem_bot R).2 (congrArg Subtype.val e3)
  obtain ⟨i, hi⟩ : ∃ i, h ∘ₗ fs i ≠ 0 := by
    by_contra hc
    push Not at hc
    have hle : (⨆ i, LinearMap.range (fs i)) ≤ LinearMap.ker h := iSup_le fun i => by
      rintro _ ⟨v, rfl⟩
      exact LinearMap.congr_fun (hc i) v
    rw [htop] at hle
    exact hhx (hle Submodule.mem_top)
  let e := LinearEquiv.ofBijective (h ∘ₗ fs i) (LinearMap.bijective_of_ne_zero hi)
  exact ⟨e.symm.toLinearMap ∘ₗ h, fun h0 => hhx (by simpa using congrArg e h0)⟩

theorem exists_proj {Γ M X : Type} [Group Γ] [AddCommGroup M] [Module ℂ M] [AddCommGroup X] [Module ℂ X]
    (σ : Γ → M →ₗ[ℂ] M) (ρ : Representation ℂ Γ X) (hρ : ρ.IsIrreducible) {ι : Type} (Φ : ι → X →ₗ[ℂ] M)
    (hΦ : ∀ i g v, Φ i (ρ g v) = σ g (Φ i v)) {t : M} (ht : t ∈ ⨆ i, LinearMap.range (Φ i)) (h0 : t ≠ 0) :
    ∃ p : M →ₗ[ℂ] X, p t ≠ 0 ∧ ∀ g, ∀ s ∈ ⨆ i, LinearMap.range (Φ i), p (σ g s) = ρ g (p s) := by
  classical
  set T := ⨆ i, LinearMap.range (Φ i) with hTdef
  have hmemΦ : ∀ i v, Φ i v ∈ T := fun i v => Submodule.mem_iSup_of_mem i (LinearMap.mem_range_self (Φ i) v)
  have hgen : ∀ f₁ f₂ : M →ₗ[ℂ] M, (∀ i v, f₁ (Φ i v) = f₂ (Φ i v)) → ∀ s ∈ T, f₁ s = f₂ s := by
    intro f₁ f₂ h s hs
    have hle : T ≤ LinearMap.ker (f₁ - f₂) := iSup_le fun i => by
      rintro _ ⟨v, rfl⟩
      simp [h i v]
    have := hle hs
    rwa [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at this
  have hT : ∀ g, ∀ s ∈ T, σ g s ∈ T := by
    intro g s hs
    have hle : T ≤ T.comap (σ g) := iSup_le fun i => by
      rintro _ ⟨v, rfl⟩
      show σ g (Φ i v) ∈ T
      rw [← hΦ]
      exact hmemΦ i _
    exact hle hs
  let τ : Representation ℂ Γ T :=
    { toFun := fun g => (σ g).restrict (hT g)
      map_one' := LinearMap.ext fun s => Subtype.ext (by
        show σ 1 s.1 = s.1
        exact hgen (σ 1) LinearMap.id (fun i v => by rw [← hΦ, map_one]; rfl) s.1 s.2)
      map_mul' := fun g h => LinearMap.ext fun s => Subtype.ext (by
        show σ (g * h) s.1 = σ g (σ h s.1)
        exact hgen (σ (g * h)) (σ g ∘ₗ σ h) (fun i v => by
          rw [LinearMap.comp_apply, ← hΦ i h v, ← hΦ i g, ← hΦ i (g * h), map_mul, Module.End.mul_apply]) s.1 s.2) }
  let Ψ : ι → Representation.IntertwiningMap ρ τ := fun i =>
    ((Φ i).codRestrict T (hmemΦ i)).intertwiningMap_of_isIntertwiningMap ρ τ (fun g v => Subtype.ext (hΦ i g v))
  let A := Representation.IntertwiningMap.equivLinearMapAsModule ρ τ
  have : IsSimpleModule ℂ[Γ] ρ.asModule := (Representation.irreducible_iff_isSimpleModule_asModule ρ).1 hρ
  have hN : ∀ y ∈ T, ∃ hy : y ∈ T, (show τ.asModule from ⟨y, hy⟩) ∈ ⨆ i, LinearMap.range (A (Ψ i)) :=
    fun y hy => Submodule.iSup_induction (fun i => LinearMap.range (Φ i))
      (motive := fun y => ∃ hy : y ∈ T, (show τ.asModule from ⟨y, hy⟩) ∈ ⨆ i, LinearMap.range (A (Ψ i))) hy
      (fun i x hx => by
        obtain ⟨v, rfl⟩ := hx
        exact ⟨hmemΦ i v, Submodule.mem_iSup_of_mem i (LinearMap.mem_range.2 ⟨v, rfl⟩)⟩)
      ⟨T.zero_mem, Submodule.zero_mem _⟩
      (fun _ _ ⟨ha, h1⟩ ⟨hb, h2⟩ => ⟨T.add_mem ha hb, Submodule.add_mem _ h1 h2⟩)
  have htop : ⨆ i, LinearMap.range (A (Ψ i)) = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨_, hx⟩ := hN (x : T).1 (x : T).2
    exact hx
  obtain ⟨q, hq⟩ := exists_ne_zero_of_iSup (fun i => A (Ψ i)) htop (show τ.asModule from ⟨t, ht⟩)
    (fun e => h0 (congrArg (fun y : T => y.1) e))
  let qI := (Representation.IntertwiningMap.equivLinearMapAsModule τ ρ).symm q
  obtain ⟨p, hp⟩ := LinearMap.exists_extend qI.toLinearMap
  have hpv : ∀ s (hs : s ∈ T), p s = qI.toLinearMap ⟨s, hs⟩ := fun s hs => LinearMap.congr_fun hp ⟨s, hs⟩
  refine ⟨p, ?_, fun g s hs => ?_⟩
  · rw [hpv t ht]
    exact hq
  · rw [hpv _ (hT g s hs), hpv s hs]
    exact LinearMap.congr_fun (qI.isIntertwining' g) ⟨s, hs⟩

end PositivityTheory.Rg.Rs.PLsAbs2

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
