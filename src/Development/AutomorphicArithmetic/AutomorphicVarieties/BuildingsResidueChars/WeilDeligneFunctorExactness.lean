module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.WdDefs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankLetterHomComp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.DpstRightExact
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.WeilDeligneDpstLeftExact
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
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.WeilDeligneFunctorExact

section

@[expose] public section

open TensorProduct Module GlobalTheory.Pst GlobalTheory.Pst.DpstMap in
theorem UpperTheory.weilDeligne_functor_exact :
    UpperTheory.V.Af.Wd.LetterExact := by
  intro LL U D' D D'' F _ _ _ _ _ _ _ _ _ _ m' m m'' τ T S hT hS hex hsurj
  have hS' : Function.Surjective (S.baseChange F) := LinearMap.lTensor_surjective F hsurj
  have hex' : Function.Exact (T.baseChange F) (S.baseChange F) := lTensor_exact F hex hsurj
  have eT : ∀ y, letterLin m' m F τ T hT (letterQ m' F τ y) = letterQ m F τ (T.baseChange F y) := fun _ => rfl
  have eS : ∀ y, letterLin m m'' F τ S hS (letterQ m F τ y) = letterQ m'' F τ (S.baseChange F y) := fun _ => rfl
  have hker : letterKer m'' F τ ≤ (letterKer m F τ).map (S.baseChange F) := iSup_le fun c => by
    rintro _ ⟨y, rfl⟩
    obtain ⟨y, rfl⟩ := hS' y
    refine ⟨_, Submodule.mem_iSup_of_mem c ⟨y, rfl⟩, ?_⟩
    have := LinearMap.congr_fun (congrArg (LinearMap.baseChange F) (hS c)) y
    rw [LinearMap.baseChange_comp, LinearMap.baseChange_comp, LinearMap.comp_apply, LinearMap.comp_apply] at this
    simp [this]
  refine ⟨fun y => ?_, fun y => ?_⟩
  · obtain ⟨y, rfl⟩ := letterQ_surjective m F τ y
    constructor
    · intro h
      rw [eS, ← LinearMap.mem_ker, ker_letterQ] at h
      obtain ⟨z, hz, hzy⟩ := hker h
      obtain ⟨w, hw⟩ := (hex' (y - z)).mp (by rw [map_sub, hzy, sub_self])
      refine ⟨letterQ m' F τ w, ?_⟩
      have hz0 : letterQ m F τ z = 0 := by
        rw [← LinearMap.mem_ker, ker_letterQ]; exact hz
      rw [eT, hw, map_sub, hz0, sub_zero]
    · rintro ⟨w, hw⟩
      obtain ⟨w, rfl⟩ := letterQ_surjective m' F τ w
      rw [← hw, eT, eS, hex'.apply_apply_eq_zero, map_zero]
  · obtain ⟨y, rfl⟩ := letterQ_surjective m'' F τ y
    obtain ⟨y, rfl⟩ := hS' y
    exact ⟨letterQ m F τ y, eS y⟩
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.WeilDeligneFunctorExactness

section

@[expose] public section

open Module

private theorem finrank_add_of_exact {k A B C : Type} [Field k] [AddCommGroup A] [Module k A] [AddCommGroup B]
    [Module k B] [AddCommGroup C] [Module k C] [FiniteDimensional k A] [FiniteDimensional k B] (f : A →ₗ[k] B)
    (p : B →ₗ[k] C) (hp : Function.Surjective p) (hex : Function.Exact f p) :
    finrank k (LinearMap.ker f) + finrank k B = finrank k A + finrank k C := by
  have h1 := LinearMap.finrank_range_add_finrank_ker f
  have h2 := LinearMap.finrank_range_add_finrank_ker p
  rw [LinearMap.range_eq_top.mpr hp, finrank_top, LinearMap.exact_iff.mp hex] at h2
  omega

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Pst GlobalTheory.Pst.DpstMap in
theorem UpperTheory.weil_deligne_functor_exactness :
    UpperTheory.V.Af.Wd.WdExact := by
  intro l _ ι K L V' V V'' _ _ _ _ _ _ _ _ _ _ _ _ _ ρ' ρ ρ'' f p hf hp hfi hps hex hV
  obtain ⟨hV', hV'', hds⟩ := UpperTheory.dpst_right_exact l K L V' V V'' ρ' ρ ρ'' f p hf hp hfi hps hex hV
  obtain ⟨-, hde⟩ := UpperTheory.weilDeligne_dpst_leftExact l (UpperTheory.V.Loc.PP l) K L V' V V'' ρ' ρ ρ'' f p hf hp hfi hex
  haveI : FiniteDimensional ↥L.1 V' := FiniteDimensional.of_injective f hfi
  haveI : FiniteDimensional ↥L.1 V'' := Module.Finite.of_surjective p hps
  have key : Function.Exact (wdLin (UpperTheory.V.Loc.PP l) ι hf) (wdLin (UpperTheory.V.Loc.PP l) ι hp) ∧
      Function.Surjective (wdLin (UpperTheory.V.Loc.PP l) ι hp) :=
    letI := algC ι L
    UpperTheory.weilDeligne_functor_exact _ _ _ _ _ ℂ (mulD (UpperTheory.V.Loc.PP l) ρ') (mulD (UpperTheory.V.Loc.PP l) ρ) (mulD (UpperTheory.V.Loc.PP l) ρ'') (urC ι)
      (dmap (UpperTheory.V.Loc.PP l) hf) (dmap (UpperTheory.V.Loc.PP l) hp) _ _ hde hds
  refine ⟨hV', hV'', ?_, key.2, key.1⟩
  haveI := hV.finite
  haveI := hV'.finite
  have h1 := finrank_add_of_exact _ _ key.2 key.1
  have h2 := finrank_add_of_exact f p hps hex
  rw [LetterDim.finrank_wdSpace l _ ι K L V ρ hV, LetterDim.finrank_wdSpace l _ ι K L V' ρ' hV',
    LetterDim.finrank_wdSpace l _ ι K L V'' ρ'' hV''] at h1
  rw [LinearMap.ker_eq_bot.mpr hfi, finrank_bot] at h2
  rw [← LinearMap.ker_eq_bot, ← Submodule.finrank_eq_zero]
  omega
end
end
