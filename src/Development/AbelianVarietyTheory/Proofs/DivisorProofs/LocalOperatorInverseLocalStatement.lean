module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjLinApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralPointsIndicatorIsVacuum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalOperatorsProductCompatibleStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzFinitePureTensors
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilEigenInjectiveExtends
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilEigenSurjectiveExtends
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
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBijectionRightInverseStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalOperatorsProductExtend

section

@[expose] public section

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DblEval

noncomputable section

namespace GlobalTheory.ArchBij

theorem bijective_arch : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (e : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) (ei : SInf F κ →L[ℂ] SInf F κ)
    (ev : ∀ v : Pl (F := F), ((κ → Fv F v) → ℂ) →ₗ[ℂ] (κ → Fv F v) → ℂ),
    (∀ v, ∀ φ ∈ SB (κ → Fv F v), ev v φ ∈ SB (κ → Fv F v)) →
    (∀ᶠ v in cofinite, ev v (stdInd F κ v) = stdInd F κ v) →
    (∀ (f : SInf F κ) (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ), (∀ v, φ v ∈ SB (κ → Fv F v)) →
      (∀ᶠ v in cofinite, φ v = stdInd F κ v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
    Set.BijOn e (schA F κ : Set ((κ → AF F) → ℂ)) (schA F κ : Set ((κ → AF F) → ℂ)) →
    (∀ v, ev v (stdInd F κ v) ≠ 0) → Function.Bijective ei := by
  intro F _ _ κ _ e ei ev hSB hfix he hbij hne
  have hstdSB : ∀ v, stdInd F κ v ∈ SB (κ → Fv F v) := fun v => GlobalTheory.StdVacuum.indicator_mem_SB v
  have hstd0 : ∀ v, stdInd F κ v ≠ 0 := by
    intro v h0
    have h := congrFun h0 0
    have hm : (0 : κ → Fv F v) ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} :=
      fun i => zero_mem (v.adicCompletionIntegers F)
    simp only [stdInd, Set.indicator_of_mem hm, Pi.one_apply, Pi.zero_apply] at h
    exact one_ne_zero h
  constructor
  · refine (injective_iff_map_eq_zero ei).2 fun f hf => ?_
    have hmem : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (stdInd F κ) ∈ schA F κ :=
      GlobalTheory.TensUniq.pure_mem_schA f (stdInd F κ) hstdSB (Filter.Eventually.of_forall fun _ => rfl)
    have h1 : e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (stdInd F κ)) = e 0 := by
      rw [he f (stdInd F κ) hstdSB (Filter.Eventually.of_forall fun _ => rfl), hf, map_zero]
      funext x
      simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
    have h2 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (stdInd F κ) = 0 :=
      hbij.injOn hmem (schA F κ).zero_mem h1
    exact GlobalTheory.EvInj.eq_zero_of_pure_eq_zero f (stdInd F κ) hstd0 (Filter.Eventually.of_forall fun _ => rfl) h2
  · intro h
    let Φ₁ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ := fun w => ev w (stdInd F κ w)
    have hΦ₁SB : ∀ v, Φ₁ v ∈ SB (κ → Fv F v) := fun v => hSB v _ (hstdSB v)
    have hΦ₁std : ∀ᶠ v in Filter.cofinite,
        Φ₁ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := hfix
    have h₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure h Φ₁ ∈ schA F κ := GlobalTheory.TensUniq.pure_mem_schA h Φ₁ hΦ₁SB hΦ₁std
    obtain ⟨Ψ, hΨ, heΨ⟩ := hbij.surjOn h₁
    obtain ⟨T, m, f, φ, hφSB, hφstd, hsum⟩ := GlobalTheory.SchADecomp.exists_sum_pure F κ Ψ hΨ
    have hvac : ∀ i, ∀ᶠ v in Filter.cofinite, φ i v = stdInd F κ v := fun i =>
      T.eventually_cofinite_notMem.mono fun v hT => hφstd i v hT
    have hid : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure h Φ₁ = ∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei (f i)) fun v => ev v (φ i v) := by

      rw [← heΨ, hsum, map_sum]
      exact Finset.sum_congr rfl fun i _ => he (f i) (φ i) (hφSB i) (hvac i)
    obtain ⟨y, hy⟩ := GlobalTheory.ArchSurj.exists_point_ne_zero Φ₁ hne hΦ₁std
    set c : ℂ := ∏ᶠ v, Φ₁ v (fun j => y j v) with hc
    have hc0 : c ≠ 0 := finprod_induction (fun a : ℂ => a ≠ 0) one_ne_zero (fun _ _ => mul_ne_zero) hy
    set cs : Fin m → ℂ := fun i => ∏ᶠ v, ev v (φ i v) (fun j => y j v) with hcs
    refine ⟨∑ i, (cs i / c) • f i, ?_⟩
    refine DFunLike.ext _ _ fun x => ?_
    let a : κ → AF F := fun j => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x j), y j)
    have hI : (fun j => evI F (a j)) = x := by
      funext j
      exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply (x j)
    have hx : h x * c = ∑ i, ei (f i) x * cs i := by
      have := congrFun hid a
      rw [Finset.sum_apply] at this
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, hI] at this
      exact this

    rw [map_sum]
    have hs : (∑ i, ei ((cs i / c) • f i)) x = ∑ i, (cs i / c) * ei (f i) x := by
      rw [SchwartzMap.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul]; rfl
    rw [hs]
    apply mul_right_cancel₀ hc0
    rw [hx, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp

end GlobalTheory.ArchBij
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalOperatorsProductExtendStatement

section

@[expose] public section

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DblEval

theorem _root_.GlobalTheory.T.bijective_infinite_part_of_restricted_product : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (e : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) (ei : SInf F κ →L[ℂ] SInf F κ)
    (ev : ∀ v : Pl (F := F), ((κ → Fv F v) → ℂ) →ₗ[ℂ] (κ → Fv F v) → ℂ),
    (∀ v, ∀ φ ∈ SB (κ → Fv F v), ev v φ ∈ SB (κ → Fv F v)) →
    (∀ᶠ v in cofinite, ev v (stdInd F κ v) = stdInd F κ v) →
    (∀ (f : SInf F κ) (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ), (∀ v, φ v ∈ SB (κ → Fv F v)) →
      (∀ᶠ v in cofinite, φ v = stdInd F κ v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
    Set.BijOn e (schA F κ : Set ((κ → AF F) → ℂ)) (schA F κ : Set ((κ → AF F) → ℂ)) →
    (∀ v, ev v (stdInd F κ v) ≠ 0) → Function.Bijective ei := by
  first | exact @GlobalTheory.ArchBij.bijective_arch | exact GlobalTheory.ArchBij.bijective_arch | (intros; apply GlobalTheory.ArchBij.bijective_arch <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedTensorLocalOperators

section

@[expose] public section

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DblEval
namespace GlobalTheory.EvKer

theorem ker_trivial : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (e : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) (ei : SInf F κ →L[ℂ] SInf F κ)
    (ev : ∀ v : Pl (F := F), ((κ → Fv F v) → ℂ) →ₗ[ℂ] (κ → Fv F v) → ℂ),
    (∀ v, ∀ φ ∈ SB (κ → Fv F v), ev v φ ∈ SB (κ → Fv F v)) →
    (∀ᶠ v in cofinite, ev v (stdInd F κ v) = stdInd F κ v) →
    (∀ (f : SInf F κ) (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ), (∀ v, φ v ∈ SB (κ → Fv F v)) →
      (∀ᶠ v in cofinite, φ v = stdInd F κ v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
    Set.InjOn e (schA F κ : Set ((κ → AF F) → ℂ)) →
    ∀ v, ∀ ψ ∈ SB (κ → Fv F v), ev v ψ = 0 → ψ = 0 := by
  intro F _ _ κ _ e ei ev hSB hstd hpure hinj v ψ hψ hev
  classical
  by_contra hne
  obtain ⟨f₀, hf₀⟩ := GlobalTheory.TensUniq.exists_sInf_ne_zero F κ
  set φ : ∀ w : Pl (F := F), (κ → Fv F w) → ℂ := Function.update (fun w => stdInd F κ w) v ψ with hφdef
  have hφSB : ∀ w, φ w ∈ SB (κ → Fv F w) := by
    intro w
    by_cases h : w = v
    · subst h; simpa [φ] using hψ
    · simpa [φ, Function.update_of_ne h, stdInd] using GlobalTheory.StdVacuum.indicator_mem_SB (κ := κ) w
  have hφev : ∀ᶠ w in cofinite, φ w = stdInd F κ w := by
    exact (Filter.eventually_cofinite_ne v).mono fun w h => by simp [φ, Function.update_of_ne h]
  have hmem : pure f₀ φ ∈ schA F κ := GlobalTheory.TensUniq.pure_mem_schA f₀ φ hφSB (by simpa [stdInd] using hφev)
  have hcomp : (fun w => ev w (φ w)) = Function.update (fun w => ev w (stdInd F κ w)) v 0 := by
    funext w
    by_cases h : w = v
    · subst h; simp [φ, hev]
    · simp [φ, Function.update_of_ne h]
  have hevstd : ∀ᶠ w in cofinite, (fun w => ev w (stdInd F κ w)) w =
      {x : κ → Fv F w | ∀ i, x i ∈ HeightOneSpectrum.adicCompletionIntegers F w}.indicator 1 := by
    simpa [stdInd] using hstd
  obtain ⟨r, -, hr⟩ := GlobalTheory.PureFactor.exists_rest_factor v (ei f₀) _ hevstd
  have hzero : e (pure f₀ φ) = 0 := by
    rw [hpure f₀ φ hφSB hφev, hcomp, ← hr 0]
    funext x
    simp [tens]
  have h0 : pure f₀ φ = 0 := hinj hmem (Submodule.zero_mem _) (by rw [hzero, map_zero])
  have hall : ∀ w, φ w ≠ 0 := by
    intro w
    by_cases h : w = v
    · subst h; simpa [φ] using hne
    · simp only [φ, Function.update_of_ne h]
      intro h1
      have := congrFun h1 0
      simp [stdInd, Set.indicator, zero_mem] at this
  have := GlobalTheory.EvInj.eq_zero_of_pure_eq_zero f₀ φ hall (by simpa [stdInd] using hφev) h0
  exact hf₀ (by rw [this]; rfl)

end GlobalTheory.EvKer
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedTensorLocalOperatorsStatement

section

@[expose] public section

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DblEval

theorem _root_.GlobalTheory.T.restricted_tensor_local_operators : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (e : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) (ei : SInf F κ →L[ℂ] SInf F κ)
    (ev : ∀ v : Pl (F := F), ((κ → Fv F v) → ℂ) →ₗ[ℂ] (κ → Fv F v) → ℂ),
    (∀ v, ∀ φ ∈ SB (κ → Fv F v), ev v φ ∈ SB (κ → Fv F v)) →
    (∀ᶠ v in cofinite, ev v (stdInd F κ v) = stdInd F κ v) →
    (∀ (f : SInf F κ) (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ), (∀ v, φ v ∈ SB (κ → Fv F v)) →
      (∀ᶠ v in cofinite, φ v = stdInd F κ v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
    Set.InjOn e (schA F κ : Set ((κ → AF F) → ℂ)) →
    ∀ v, ∀ ψ ∈ SB (κ → Fv F v), ev v ψ = 0 → ψ = 0 := by
  first | exact @GlobalTheory.EvKer.ker_trivial | exact GlobalTheory.EvKer.ker_trivial | (intros; apply GlobalTheory.EvKer.ker_trivial <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalOperatorInverseLocal

section

@[expose] public section

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DblEval

noncomputable section

namespace GlobalTheory.LocOpInv

theorem pure_mem {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (f : SInf F κ)
    (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ) (hSB : ∀ v, φ v ∈ SB (κ → Fv F v))
    (hstd : ∀ᶠ v in cofinite, φ v = stdInd F κ v) : pure f φ ∈ schA F κ :=
  GlobalTheory.TensUniq.pure_mem_schA f φ hSB hstd

theorem stdInd_mem_SB_ne {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : Pl (F := F)) :
    stdInd F κ v ∈ SB (κ → Fv F v) ∧ stdInd F κ v ≠ 0 := by
  refine ⟨GlobalTheory.StdVacuum.indicator_mem_SB v, fun h => ?_⟩
  have h0 := congrFun h 0
  rw [stdInd, Set.indicator_of_mem (show (0 : κ → Fv F v) ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F}
    from fun i => zero_mem _)] at h0
  exact one_ne_zero h0

theorem isLocOp_inv : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (e : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)), IsLocOp e →
    Set.BijOn e (schA F κ : Set ((κ → AF F) → ℂ)) (schA F κ : Set ((κ → AF F) → ℂ)) →
    ∃ e' : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ), IsLocOp e' ∧ ∀ Φ ∈ schA F κ, e' (e Φ) = Φ := by
  classical
  intro F _ _ κ _ e he hbij
  obtain ⟨ei, ev, hSB, hstd, hloc⟩ := he
  have hne : ∀ v, ev v (stdInd F κ v) ≠ 0 := fun v h =>
    (stdInd_mem_SB_ne v).2 (GlobalTheory.T.restricted_tensor_local_operators e ei ev hSB hstd hloc hbij.injOn v _ (stdInd_mem_SB_ne v).1 h)
  obtain ⟨S, hS⟩ := GlobalTheory.T.schwartz_bijection_right_inverse _ _ ei (GlobalTheory.T.bijective_infinite_part_of_restricted_product e ei ev hSB hstd hloc hbij hne)

  have hbv : ∀ v, Function.Bijective ((ev v).restrict (p := SB (κ → Fv F v)) (q := SB (κ → Fv F v)) (hSB v)) := by
    intro v
    refine ⟨?_, ?_⟩
    · refine (injective_iff_map_eq_zero _).2 fun ψ hψ => ?_
      exact Subtype.ext (GlobalTheory.T.restricted_tensor_local_operators e ei ev hSB hstd hloc hbij.injOn v ψ.1 ψ.2 (congrArg Subtype.val hψ))
    · intro χ
      obtain ⟨ψ, hψ, h⟩ := GlobalTheory.T.local_operators_product_compatible e ei ev hSB hstd hloc hbij.surjOn hne v χ.1 χ.2
      exact ⟨⟨ψ, hψ⟩, Subtype.ext h⟩
  let Lv : ∀ v, SB (κ → Fv F v) ≃ₗ[ℂ] SB (κ → Fv F v) := fun v => LinearEquiv.ofBijective _ (hbv v)
  have hCv : ∀ v, ∃ C : Submodule ℂ ((κ → Fv F v) → ℂ), IsCompl (SB (κ → Fv F v)) C := fun v =>
    Submodule.exists_isCompl _
  choose Cv hCv using hCv
  let ev' : ∀ v : Pl (F := F), ((κ → Fv F v) → ℂ) →ₗ[ℂ] (κ → Fv F v) → ℂ := fun v =>
    (SB (κ → Fv F v)).subtype ∘ₗ ((Lv v).symm : SB (κ → Fv F v) →ₗ[ℂ] SB (κ → Fv F v)) ∘ₗ
      Submodule.linearProjOfIsCompl _ _ (hCv v)
  have hev'1 : ∀ v, ∀ ψ (hψ : ψ ∈ SB (κ → Fv F v)), ev' v ψ = ((Lv v).symm ⟨ψ, hψ⟩ : SB _) := by
    intro v ψ hψ
    simp only [ev', LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype, LinearEquiv.coe_coe]
    have hp : Submodule.linearProjOfIsCompl _ _ (hCv v) ψ = ⟨ψ, hψ⟩ :=
      Submodule.linearProjOfIsCompl_apply_left (hCv v) ⟨ψ, hψ⟩
    rw [hp]
  have hev'SB : ∀ v, ∀ ψ ∈ SB (κ → Fv F v), ev' v ψ ∈ SB (κ → Fv F v) := fun v ψ hψ => by
    rw [hev'1 v ψ hψ]; exact Subtype.property _
  have hevev' : ∀ v, ∀ ψ ∈ SB (κ → Fv F v), ev v (ev' v ψ) = ψ := by
    intro v ψ hψ
    rw [hev'1 v ψ hψ]
    have := congrArg Subtype.val ((Lv v).apply_symm_apply ⟨ψ, hψ⟩)
    exact this
  have hev'std : ∀ᶠ v in cofinite, ev' v (stdInd F κ v) = stdInd F κ v := by
    filter_upwards [hstd] with v hv
    have h1 := (stdInd_mem_SB_ne (κ := κ) v).1
    rw [hev'1 v _ h1]
    have : (Lv v) ⟨stdInd F κ v, h1⟩ = ⟨stdInd F κ v, h1⟩ := Subtype.ext hv
    rw [← this, LinearEquiv.symm_apply_apply]

  let Le : schA F κ ≃ₗ[ℂ] schA F κ := LinearEquiv.ofBijective ((e.restrict (p := schA F κ) (q := schA F κ)
    fun Φ hΦ => hbij.mapsTo hΦ)) ⟨fun a b h => Subtype.ext (hbij.injOn a.2 b.2 (congrArg Subtype.val h)), fun b => by
      obtain ⟨a, ha, h⟩ := hbij.surjOn b.2
      exact ⟨⟨a, ha⟩, Subtype.ext h⟩⟩
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (schA F κ)
  let e' : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ) :=
    (schA F κ).subtype ∘ₗ (Le.symm : schA F κ →ₗ[ℂ] schA F κ) ∘ₗ Submodule.linearProjOfIsCompl _ _ hC
  have he'e : ∀ Φ ∈ schA F κ, e' (e Φ) = Φ := by
    intro Φ hΦ
    have h1 : e Φ ∈ schA F κ := hbij.mapsTo hΦ
    simp only [e', LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype, LinearEquiv.coe_coe]
    have hp : Submodule.linearProjOfIsCompl _ _ hC (e Φ) = ⟨e Φ, h1⟩ :=
      Submodule.linearProjOfIsCompl_apply_left hC ⟨e Φ, h1⟩
    rw [hp]
    have : Le ⟨Φ, hΦ⟩ = ⟨e Φ, h1⟩ := rfl
    rw [← this, LinearEquiv.symm_apply_apply]
  refine ⟨e', ⟨S, ev', hev'SB, hev'std, fun f φ hφ hφs => ?_⟩, he'e⟩
  have hφ' : ∀ v, ev' v (φ v) ∈ SB (κ → Fv F v) := fun v => hev'SB v _ (hφ v)
  have hφ's : ∀ᶠ v in cofinite, ev' v (φ v) = stdInd F κ v := by
    filter_upwards [hφs, hev'std] with v h1 h2
    rw [h1, h2]
  have hΨ : pure (S f) (fun v => ev' v (φ v)) ∈ schA F κ := pure_mem (S f) _ hφ' hφ's
  have hE : e (pure (S f) fun v => ev' v (φ v)) = pure f φ := by
    rw [hloc _ _ hφ' hφ's, hS]
    congr 1
    funext v
    exact hevev' v _ (hφ v)
  rw [← hE, he'e _ hΨ]

end GlobalTheory.LocOpInv

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalOperatorInverseLocalStatement

section

@[expose] public section

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DblEval

theorem _root_.GlobalTheory.T.local_operator_inverse_local : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (e : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)), IsLocOp e →
    Set.BijOn e (schA F κ : Set ((κ → AF F) → ℂ)) (schA F κ : Set ((κ → AF F) → ℂ)) →
    ∃ e' : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ), IsLocOp e' ∧ ∀ Φ ∈ schA F κ, e' (e Φ) = Φ := by
  first | exact @GlobalTheory.LocOpInv.isLocOp_inv | exact GlobalTheory.LocOpInv.isLocOp_inv | (intros; apply GlobalTheory.LocOpInv.isLocOp_inv <;> assumption)
end
end
