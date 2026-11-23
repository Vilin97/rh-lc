module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.UltraDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchedSupportCompletions
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.FinCompl
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Imports
public import Mathlib.Order.Filter.Ultrafilter.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Order.Filter.Ultrafilter.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.KjMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpecializationMapCompUniversalSection
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PairedDualFirstOrderDualMatrixSpace
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg
public import Mathlib.RingTheory.Ideal.Quotient.Index

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ULimConst

section

@[expose] public section

open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

theorem UpperTheory.V.AlgebraTools.ULim.const_bijective :
    ∀ (R ι : Type) [CommRing R] (U : Ultrafilter ι) (m : Ideal R) (Z : Type) [AddCommGroup Z] [Module R Z], IsAdicComplete m Z →
      (∀ j : ℕ, Finite (Z ⧸ (m ^ j • ⊤ : Submodule R Z))) →
      Function.Bijective fun z : Z => ULim.mk (U : Filter ι) (fun j => m ^ j) (fun _ => Z) fun _ => z := by
  intro R ι _ U m Z _ _ hc hfin
  refine ⟨fun a b hab => ?_, fun x => ?_⟩
  · have h0 : ULim.mk (U : Filter ι) (fun j => m ^ j) (fun _ => Z) (fun _ => a - b) = 0 := by
      have h1 : (fun _ : ι => a - b) = (fun _ : ι => a) - (fun _ : ι => b) := rfl
      rw [h1, map_sub]
      exact sub_eq_zero.2 hab
    rw [ULim.mk_eq_zero] at h0
    refine sub_eq_zero.1 (IsHausdorff.haus hc.toIsHausdorff _ fun j => ?_)
    obtain ⟨_, h⟩ := (h0 j).exists
    exact SModEq.zero.2 h
  · obtain ⟨p, rfl⟩ := ULim.mk_surjective _ _ _ x
    have hz : ∀ j : ℕ, ∃ z : Z, ∀ᶠ i in (U : Filter ι), p i ≡ z [SMOD (m ^ j • ⊤ : Submodule R Z)] := by
      intro j
      haveI := hfin j
      obtain ⟨q, hq⟩ := Ultrafilter.eq_pure_of_finite
        (U.map fun i => (Submodule.Quotient.mk (p i) : Z ⧸ (m ^ j • ⊤ : Submodule R Z)))
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      refine ⟨z, ?_⟩
      have h : ({Submodule.Quotient.mk z} : Set (Z ⧸ (m ^ j • ⊤ : Submodule R Z))) ∈
          U.map fun i => (Submodule.Quotient.mk (p i) : Z ⧸ (m ^ j • ⊤ : Submodule R Z)) := by
        rw [hq]; simp
      exact h
    choose z hz using hz
    obtain ⟨L, hL⟩ := IsPrecomplete.prec hc.toIsPrecomplete (f := z) (fun {j k} hjk => by
      obtain ⟨i, h1, h2⟩ := ((hz j).and (hz k)).exists
      exact h1.symm.trans (h2.mono (Submodule.smul_mono_left (Ideal.pow_le_pow_right hjk))))
    refine ⟨L, ?_⟩
    show ULim.mk _ _ _ _ = _
    rw [← sub_eq_zero, ← map_sub, ULim.mk_eq_zero]
    intro j
    refine (hz j).mono fun i hi => ?_
    exact SModEq.sub_mem.1 (hi.trans (hL j)).symm
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.UlimQuot

section

@[expose] public section

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

theorem UpperTheory.V.Pa.Core.ulimQuot :
    ∀ (R : Type) [CommRing R] (F : Filter ℕ) (I : ℕ → Ideal R) (M M' : ℕ → Type) [∀ N, AddCommGroup (M N)] [∀ N, Module R (M N)] [∀ N, AddCommGroup (M' N)] [∀ N, Module R (M' N)] (ν : ℕ → ℕ) (φ : ∀ N, (M N ⧸ (I (ν N) • ⊤ : Submodule R (M N))) →ₗ[R] (M' N ⧸ (I (ν N) • ⊤ : Submodule R (M' N)))), Antitone I → Tendsto ν F atTop → ∃ Φ : ULim F I M →ₗ[R] ULim F I M', ∀ (p : ∀ N, M N) (p' : ∀ N, M' N), (∀ᶠ N in F, Submodule.Quotient.mk (p' N) = φ N (Submodule.Quotient.mk (p N))) → Φ (ULim.mk F I M p) = ULim.mk F I M' p' := by
  intro R _ F I M M' _ _ _ _ ν φ hI hν
  have hev : ∀ j, ∀ᶠ N in F, I (ν N) ≤ I j := fun j =>
    (tendsto_atTop.1 hν j).mono fun N hN => hI hN
  have he : ∀ {X : Type} [AddCommGroup X] [Module R X] (K J : Ideal R),
      (J • ⊤ : Submodule R (X ⧸ (K • ⊤ : Submodule R X))) =
        (J • ⊤ : Submodule R X).map (K • ⊤ : Submodule R X).mkQ := by
    intro X _ _ K J
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]
  have hlift : ∀ {X : Type} [AddCommGroup X] [Module R X] (K J : Ideal R), K ≤ J → ∀ x : X,
      (Submodule.Quotient.mk x : X ⧸ (K • ⊤ : Submodule R X)) ∈
        (J • ⊤ : Submodule R (X ⧸ (K • ⊤ : Submodule R X))) → x ∈ (J • ⊤ : Submodule R X) := by
    intro X _ _ K J hKJ x hx
    rw [he] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have hd : x - y ∈ (K • ⊤ : Submodule R X) := by
      rw [← Submodule.Quotient.eq]
      exact hyx.symm
    have := Submodule.add_mem _ (Submodule.smul_mono_left hKJ hd) hy
    rwa [sub_add_cancel] at this
  have hmk : ∀ {X : Type} [AddCommGroup X] [Module R X] (K J : Ideal R) (x : X),
      x ∈ (J • ⊤ : Submodule R X) →
        (Submodule.Quotient.mk x : X ⧸ (K • ⊤ : Submodule R X)) ∈
          (J • ⊤ : Submodule R (X ⧸ (K • ⊤ : Submodule R X))) := by
    intro X _ _ K J x hx
    rw [he]
    exact ⟨x, hx, rfl⟩
  have hφ : ∀ N j (z : M N ⧸ (I (ν N) • ⊤ : Submodule R (M N))),
      z ∈ (I j • ⊤ : Submodule R _) → φ N z ∈ (I j • ⊤ : Submodule R _) := by
    intro N j z hz
    have hle : (I j • ⊤ : Submodule R _).map (φ N) ≤ I j • ⊤ := by
      rw [Submodule.map_smul'']
      exact Submodule.smul_mono le_rfl le_top
    exact hle ⟨z, hz, rfl⟩
  let π : (∀ N, M' N) →ₗ[R] ∀ N, (M' N ⧸ (I (ν N) • ⊤ : Submodule R (M' N))) :=
    LinearMap.pi fun N => (Submodule.mkQ _).comp (LinearMap.proj N)
  have hπ : Function.Surjective π := fun q =>
    ⟨fun N => (Submodule.mkQ_surjective _ (q N)).choose,
      funext fun N => (Submodule.mkQ_surjective _ (q N)).choose_spec⟩
  have hker : LinearMap.ker π ≤ LinearMap.ker (ULim.mk F I M') := by
    intro p hp
    rw [LinearMap.mem_ker] at hp ⊢
    rw [ULim.mk_eq_zero]
    intro j
    refine (hev j).mono fun N hN => ?_
    have hpN : p N ∈ (I (ν N) • ⊤ : Submodule R (M' N)) := by
      rw [← Submodule.Quotient.mk_eq_zero]
      exact congrFun hp N
    exact Submodule.smul_mono_left hN hpN
  let φ' : (∀ N, M N) →ₗ[R] ∀ N, (M' N ⧸ (I (ν N) • ⊤ : Submodule R (M' N))) :=
    LinearMap.pi fun N => (φ N).comp ((Submodule.mkQ _).comp (LinearMap.proj N))
  let Φ0 : (∀ N, M N) →ₗ[R] ULim F I M' :=
    ((LinearMap.ker π).liftQ (ULim.mk F I M') hker).comp
      ((π.quotKerEquivOfSurjective hπ).symm.toLinearMap.comp φ')
  have hΦ0 : ∀ p p', π p' = φ' p → Φ0 p = ULim.mk F I M' p' := by
    intro p p' h
    simp only [Φ0, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [← h]
    have hs : (π.quotKerEquivOfSurjective hπ).symm (π p') = Submodule.Quotient.mk p' := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    rw [hs, Submodule.liftQ_apply]
  have hnull : uNull F I M ≤ LinearMap.ker Φ0 := by
    intro p hp
    have hp : ∀ j, ∀ᶠ N in F, p N ∈ (I j • ⊤ : Submodule R (M N)) := hp
    rw [LinearMap.mem_ker]
    obtain ⟨p', hp'⟩ := hπ (φ' p)
    rw [hΦ0 p p' hp', ULim.mk_eq_zero]
    intro j
    refine ((hp j).and (hev j)).mono fun N ⟨h1, h2⟩ => ?_
    apply hlift (I (ν N)) (I j) h2
    have hN : π p' N = φ N (Submodule.Quotient.mk (p N)) := congrFun hp' N
    change π p' N ∈ _
    rw [hN]
    exact hφ N j _ (hmk _ _ _ h1)
  refine ⟨(uNull F I M).liftQ Φ0 hnull, fun p p' h => ?_⟩
  change (uNull F I M).liftQ Φ0 hnull (Submodule.Quotient.mk p) = _
  rw [Submodule.liftQ_apply]
  obtain ⟨q, hq⟩ := hπ (φ' p)
  rw [hΦ0 p q hq, ← sub_eq_zero, ← map_sub, ULim.mk_eq_zero]
  intro j
  refine (h.and (hev j)).mono fun N ⟨h1, h2⟩ => ?_
  apply Submodule.smul_mono_left h2
  rw [← Submodule.Quotient.mk_eq_zero, Pi.sub_apply, Submodule.Quotient.mk_sub, h1]
  have hN : π q N = φ N (Submodule.Quotient.mk (p N)) := congrFun hq N
  exact sub_eq_zero.2 hN
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.ExistsUltraLimitPairOfEventualQuotientMaps

section

@[expose] public section

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem const_bij {R X : Type} [CommRing R] [AddCommGroup X] [Module R X] (U : Ultrafilter ℕ)
    (m : Ideal R) (I : ℕ → Ideal R) (hc : IsAdicComplete m X)
    (hf : ∀ j : ℕ, Finite (X ⧸ (m ^ j • ⊤ : Submodule R X)))
    (hI : ∀ j, (I j • ⊤ : Submodule R X) = m ^ j • ⊤) :
    Function.Bijective
      (ULim.mk (U : Filter ℕ) I (fun _ => X) ∘ₗ LinearMap.pi fun _ : ℕ => (LinearMap.id : X →ₗ[R] X)) := by
  have hb := ULim.const_bijective R ℕ U m X hc hf
  have key : ∀ p q : ℕ → X, ULim.mk (U : Filter ℕ) I (fun _ => X) p = ULim.mk (U : Filter ℕ) I (fun _ => X) q ↔
      ULim.mk (U : Filter ℕ) (fun j => m ^ j) (fun _ => X) p =
        ULim.mk (U : Filter ℕ) (fun j => m ^ j) (fun _ => X) q := by
    intro p q
    rw [← sub_eq_zero, ← map_sub, ULim.mk_eq_zero, ← sub_eq_zero (a := ULim.mk _ _ _ p), ← map_sub,
      ULim.mk_eq_zero]
    simp only [hI]
  refine ⟨fun a b hab => hb.1 ((key (fun _ => a) (fun _ => b)).1 hab), fun x => ?_⟩
  obtain ⟨p, rfl⟩ := ULim.mk_surjective _ _ _ x
  obtain ⟨z, hz⟩ := hb.2 (ULim.mk _ _ _ p)
  exact ⟨z, (key (fun _ => z) p).2 hz⟩

private theorem comp_smul {R : Type} [CommRing R] (F : Filter ℕ) (I : ℕ → Ideal R) (M M' : ℕ → Type)
    [∀ N, AddCommGroup (M N)] [∀ N, Module R (M N)] [∀ N, AddCommGroup (M' N)] [∀ N, Module R (M' N)]
    (ν : ℕ → ℕ) (hν : Tendsto ν F atTop) (hI : Antitone I) (f : R)
    (φ : ∀ N, (M N ⧸ (I (ν N) • ⊤ : Submodule R (M N))) →ₗ[R] (M' N ⧸ (I (ν N) • ⊤ : Submodule R (M' N))))
    (ψ : ∀ N, (M' N ⧸ (I (ν N) • ⊤ : Submodule R (M' N))) →ₗ[R] (M N ⧸ (I (ν N) • ⊤ : Submodule R (M N))))
    (h : ∀ᶠ N in F, ∀ z, ψ N (φ N z) = f • z)
    (Φ : ULim F I M →ₗ[R] ULim F I M') (Ψ : ULim F I M' →ₗ[R] ULim F I M)
    (hΦ : ∀ (p : ∀ N, M N) (p' : ∀ N, M' N), (∀ᶠ N in F, Submodule.Quotient.mk (p' N) =
      φ N (Submodule.Quotient.mk (p N))) → Φ (ULim.mk F I M p) = ULim.mk F I M' p')
    (hΨ : ∀ (p : ∀ N, M' N) (p' : ∀ N, M N), (∀ᶠ N in F, Submodule.Quotient.mk (p' N) =
      ψ N (Submodule.Quotient.mk (p N))) → Ψ (ULim.mk F I M' p) = ULim.mk F I M p') (z : ULim F I M) :
    Ψ (Φ z) = f • z := by
  obtain ⟨p, rfl⟩ := ULim.mk_surjective _ _ _ z
  choose q hq using fun N => Submodule.Quotient.mk_surjective _ (φ N (Submodule.Quotient.mk (p N)))
  rw [hΦ p q (Eventually.of_forall hq), ← map_smul]
  refine hΨ q (f • p) (h.mono fun N hN => ?_)
  rw [hq, hN]
  rfl

theorem UpperTheory.V.Pa.Core.exists_ultraLimit_pair_of_eventual_quotient_maps :
    ∀ (Λ R σ : Type) [CommRing Λ] [IsLocalRing Λ] [CommRing R] [Fintype σ] (s : MvPowerSeries σ Λ →+* R) [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] [Finite (ResidueField Λ)] (U : Ultrafilter ℕ) (f : R) (M : ℕ → Type) [∀ N, AddCommGroup (M N)] [∀ N, Module R (M N)] (X : Type) [AddCommGroup X] [Module R X] [Module Λ X] [Module.Finite Λ X], (U : Filter ℕ) ≤ atTop → (∀ (a : Λ) (x : X), a • x = s (MvPowerSeries.C a) • x) → (∀ a (x : X), s (MvPowerSeries.X a) • x = 0) → (∀ j, ∀ᶠ N in (U : Filter ℕ), ∃ (φ : (X ⧸ ((kjIdeal Λ σ 1 j).map s • ⊤ : Submodule R X)) →ₗ[R] (M N ⧸ ((kjIdeal Λ σ 1 j).map s • ⊤ : Submodule R (M N)))) (ψ : (M N ⧸ ((kjIdeal Λ σ 1 j).map s • ⊤ : Submodule R (M N))) →ₗ[R] (X ⧸ ((kjIdeal Λ σ 1 j).map s • ⊤ : Submodule R X))), (∀ z, φ (ψ z) = f • z) ∧ ∀ z, ψ (φ z) = f • z) → ∃ (Φ : X →ₗ[R] ULim (U : Filter ℕ) (fun j => Ideal.span (Set.range (fun a => s (MvPowerSeries.X a))) ⊔ ((maximalIdeal Λ).map (s.comp MvPowerSeries.C)) ^ j) M) (Ψ : ULim (U : Filter ℕ) (fun j => Ideal.span (Set.range (fun a => s (MvPowerSeries.X a))) ⊔ ((maximalIdeal Λ).map (s.comp MvPowerSeries.C)) ^ j) M →ₗ[R] X), (∀ z, Φ (Ψ z) = f • z) ∧ ∀ z, Ψ (Φ z) = f • z := by
  intro Λ R σ _ _ _ _ s _ _ _ U f M _ _ X _ _ _ _ hU hs hy h
  classical
  letI : Algebra Λ R := (s.comp MvPowerSeries.C).toAlgebra
  haveI : IsScalarTower Λ R X := IsScalarTower.of_algebraMap_smul fun a x => (hs a x).symm
  set m : Ideal R := (maximalIdeal Λ).map (s.comp MvPowerSeries.C) with hm
  set I : ℕ → Ideal R := fun j => Ideal.span (Set.range (fun a => s (MvPowerSeries.X a))) ⊔ m ^ j with hIdef
  have hkj : ∀ j, (kjIdeal Λ σ 1 j).map s = I j := fun j => by rw [kjMap, pow_one]
  have h' : ∀ j, ∀ᶠ N in (U : Filter ℕ), ∃ (φ : (X ⧸ (I j • ⊤ : Submodule R X)) →ₗ[R] (M N ⧸ (I j • ⊤ : Submodule R (M N)))) (ψ : (M N ⧸ (I j • ⊤ : Submodule R (M N))) →ₗ[R] (X ⧸ (I j • ⊤ : Submodule R X))), (∀ z, φ (ψ z) = f • z) ∧ ∀ z, ψ (φ z) = f • z := by
    intro j
    rw [← hkj j]
    exact h j
  obtain ⟨ν, hν, hP⟩ := exists_diag _ hU _ h'
  have hanti : Antitone I := fun a b hab => sup_le_sup_left (Ideal.pow_le_pow_right hab) _
  have hex : ∀ N, ∃ (φ : (X ⧸ (I (ν N) • ⊤ : Submodule R X)) →ₗ[R] (M N ⧸ (I (ν N) • ⊤ : Submodule R (M N)))) (ψ : (M N ⧸ (I (ν N) • ⊤ : Submodule R (M N))) →ₗ[R] (X ⧸ (I (ν N) • ⊤ : Submodule R X))), (∃ (φ : (X ⧸ (I (ν N) • ⊤ : Submodule R X)) →ₗ[R] (M N ⧸ (I (ν N) • ⊤ : Submodule R (M N)))) (ψ : (M N ⧸ (I (ν N) • ⊤ : Submodule R (M N))) →ₗ[R] (X ⧸ (I (ν N) • ⊤ : Submodule R X))), (∀ z, φ (ψ z) = f • z) ∧ ∀ z, ψ (φ z) = f • z) → (∀ z, φ (ψ z) = f • z) ∧ ∀ z, ψ (φ z) = f • z := by
    intro N
    by_cases hN : ∃ (φ : (X ⧸ (I (ν N) • ⊤ : Submodule R X)) →ₗ[R] (M N ⧸ (I (ν N) • ⊤ : Submodule R (M N)))) (ψ : (M N ⧸ (I (ν N) • ⊤ : Submodule R (M N))) →ₗ[R] (X ⧸ (I (ν N) • ⊤ : Submodule R X))), (∀ z, φ (ψ z) = f • z) ∧ ∀ z, ψ (φ z) = f • z
    · obtain ⟨φ, ψ, hh⟩ := hN
      exact ⟨φ, ψ, fun _ => hh⟩
    · exact ⟨0, 0, fun hh => absurd hh hN⟩
  choose φ ψ hφψ using hex
  have hgood := hP.mono fun N hN => hφψ N (hN _ le_rfl)
  obtain ⟨Φ, hΦ⟩ := ulimQuot R U I (fun _ => X) M ν φ hanti hν
  obtain ⟨Ψ, hΨ⟩ := ulimQuot R U I M (fun _ => X) ν ψ hanti hν
  have h1 := comp_smul U I (fun _ => X) M ν hν hanti f φ ψ (hgood.mono fun _ hN => hN.2) Φ Ψ hΦ hΨ
  have h2 := comp_smul U I M (fun _ => X) ν hν hanti f ψ φ (hgood.mono fun _ hN => hN.1) Ψ Φ hΨ hΦ
  have hc : IsAdicComplete m X :=
    (IsAdicComplete.map_algebraMap_iff (S := R) (maximalIdeal Λ) X).2 (AnnihilatorQuotientFinite.finCompl Λ X _)
  have hf : ∀ j : ℕ, Finite (X ⧸ (m ^ j • ⊤ : Submodule R X)) := by
    intro j
    haveI : Finite (Λ ⧸ maximalIdeal Λ) := inferInstanceAs (Finite (ResidueField Λ))
    haveI : Finite (Λ ⧸ maximalIdeal Λ ^ j) := Ideal.finite_quotient_pow (IsNoetherian.noetherian _) j
    haveI : Finite (X ⧸ (maximalIdeal Λ ^ j • ⊤ : Submodule Λ X)) :=
      Submodule.finite_quotient_smul _ Module.Finite.fg_top
    have hle : (maximalIdeal Λ ^ j • ⊤ : Submodule Λ X) ≤ (m ^ j • ⊤ : Submodule R X).restrictScalars Λ := by
      refine Submodule.smul_le.2 fun a ha x _ => ?_
      rw [Submodule.restrictScalars_mem, hs]
      refine Submodule.smul_mem_smul ?_ Submodule.mem_top
      rw [hm, ← Ideal.map_pow]
      exact Ideal.mem_map_of_mem (s.comp MvPowerSeries.C) ha
    haveI : Finite (X ⧸ (m ^ j • ⊤ : Submodule R X).restrictScalars Λ) :=
      Finite.of_surjective _ (Submodule.factor_surjective hle)
    exact Finite.of_equiv _ (Submodule.Quotient.restrictScalarsEquiv Λ _).toEquiv
  have hI : ∀ j, (I j • ⊤ : Submodule R X) = m ^ j • ⊤ := by
    intro j
    have h0 : (Ideal.span (Set.range (fun a => s (MvPowerSeries.X a))) • ⊤ : Submodule R X) = ⊥ := by
      rw [← Submodule.le_annihilator_iff, Ideal.span_le]
      rintro _ ⟨a, rfl⟩
      exact Submodule.mem_annihilator.2 fun x _ => hy a x
    show ((_ ⊔ _ : Ideal R) • ⊤ : Submodule R X) = _
    rw [Submodule.sup_smul, h0, bot_sup_eq]
  let e := LinearEquiv.ofBijective _ (const_bij U m I hc hf hI)
  refine ⟨Φ ∘ₗ e.toLinearMap, e.symm.toLinearMap ∘ₗ Ψ, fun z => ?_, fun z => ?_⟩
  · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    exact h2 z
  · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [h1, map_smul, LinearEquiv.symm_apply_apply]
end
end
