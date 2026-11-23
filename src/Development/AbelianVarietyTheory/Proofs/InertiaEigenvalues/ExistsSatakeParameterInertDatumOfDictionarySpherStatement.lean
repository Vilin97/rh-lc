module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAutLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLevelFullAtInertPlacePrincipalElsewhereStatement
public import Formalism.SatakeDualWeyl.StatementF
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsCharacterEigenvectorOfCommutingRepresentat
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvMemDoubleCosetAndComm
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
import Formalism.AlgebraicWeights.IsAlgWeight
import ReciprocityTheory.Automorphisms.PlaceA
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeFunIAddSmulStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertHeckeOperatorConvolutionEqCompStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertHeckeOperatorMaximalCompactIndicatorEqIdStatement
public import Formalism.AlgebraicWeights.InertDatumExists
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertHeckeOperatorPreservesLevelInvariants
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDoubleCosetsDefiniteUnitaryMaximalLevelStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteInertHeckeSupportCosets
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemMaxCompactOfTrivOutsideLocalIntegral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryDoubleCosetFiniteLeftCosets
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FSatakeA
import Formalism.SatakeDualWeyl.KpqSubgroupCompact

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSatUEigenvector

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.HeckeSatakeEigen

theorem exists_satU_eigenvector : ∀ {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] [CompleteSpace K] (ϖ : K) (σ : K →+* K) (q n : ℕ), Formalism.UG.IsUnramInv ϖ σ q → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (T : (Formalism.UG.GU σ n → ℂ) → Module.End ℂ V), (∀ h₁ ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n), ∀ h₂ ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n), T (h₁ + h₂) = T h₁ + T h₂) → (∀ (c : ℂ), ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n), T (c • h) = c • T h) → T (Formalism.UG.dosetInd ℂ (Formalism.UG.KU σ n) 1) = 1 → (∀ h₁ ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n), ∀ h₂ ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n), T (Formalism.UG.conv (Formalism.UG.KU σ n) h₁ h₂) = T h₁ * T h₂) → ∀ x₀ : V, x₀ ≠ 0 → ∃ α : Fin (n / 2) → ℂ, ∃ x : V, x ≠ 0 ∧ ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n), T h x = Formalism.UG.SatU ϖ q h α • x := by
  intro K _ _ _ ϖ σ q n hU V _ _ _ T hadd hsmul h1 hmul x₀ hx₀
  haveI : Nontrivial V := ⟨⟨x₀, 0, hx₀⟩⟩
  have hcomm : ∀ a b : Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n), T a.1 * T b.1 = T b.1 * T a.1 := by
    intro a b
    rw [← hmul _ a.2 _ b.2, ← hmul _ b.2 _ a.2, GlobalTheory.UnitarySwap.heckeCommU K ϖ σ q n ℂ hU _ a.2 _ b.2]
  obtain ⟨x, hx0, hx⟩ := GlobalTheory.exists_common_eigenvector_of_commute
    (fun b : Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n) => T b.1) hcomm
  choose c hc using hx
  have hinj : Function.Injective fun a : ℂ => a • x := smul_left_injective ℂ hx0
  let l : Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n) →ₗ[ℂ] ℂ :=
    { toFun := c
      map_add' := fun a b => hinj (by
        show c (a + b) • x = (c a + c b) • x
        rw [← hc, add_smul, ← hc, ← hc]
        show T (a.1 + b.1) x = _
        rw [hadd _ a.2 _ b.2]; rfl)
      map_smul' := fun r a => hinj (by
        show c (r • a) • x = (r * c a) • x
        rw [← hc, mul_smul, ← hc]
        show T (r • a.1) x = _
        rw [hsmul r _ a.2]; rfl) }
  have hl1 : l ⟨_, Formalism.UG.Final.DosetIndMem _ _ ℂ 1⟩ = 1 := hinj (by
    show c _ • x = (1 : ℂ) • x
    rw [← hc, one_smul]
    show T (Formalism.UG.dosetInd ℂ _ 1) x = x
    rw [h1]; rfl)
  have hlm : ∀ f f' : Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n),
      l ⟨_, Formalism.UG.Final.HeckeConvMem _ _ ℂ (Formalism.UG.P.isCommensurated_integral_unitary_of_unramified hU n) _ f.2 _ f'.2⟩ = l f * l f' :=
    fun f f' => hinj (by
      show c _ • x = (c f * c f') • x
      rw [← hc]
      show T (Formalism.UG.conv _ f.1 f'.1) x = _
      rw [hmul _ f.2 _ f'.2, Module.End.mul_apply, hc f', map_smul, hc f, smul_smul, mul_comm])
  obtain ⟨α, hα⟩ := GlobalTheory.LFun.SatCompare.exists_satU_eq hU l hl1 hlm
  refine ⟨fun i => (α i : ℂ), x, hx0, fun h hh => ?_⟩
  rw [hc ⟨h, hh⟩]
  congr 1
  exact hα ⟨h, hh⟩

end GlobalTheory.HeckeSatakeEigen
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSatUEigenvectorStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.exists_satU_eigenvector_alt : ∀ {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] [CompleteSpace K] (ϖ : K) (σ : K →+* K) (q n : ℕ), Formalism.UG.IsUnramInv ϖ σ q → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (T : (Formalism.UG.GU σ n → ℂ) → Module.End ℂ V), (∀ h₁ ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n), ∀ h₂ ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n), T (h₁ + h₂) = T h₁ + T h₂) → (∀ (c : ℂ), ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n), T (c • h) = c • T h) → T (Formalism.UG.dosetInd ℂ (Formalism.UG.KU σ n) 1) = 1 → (∀ h₁ ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n), ∀ h₂ ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n), T (Formalism.UG.conv (Formalism.UG.KU σ n) h₁ h₂) = T h₁ * T h₂) → ∀ x₀ : V, x₀ ≠ 0 → ∃ α : Fin (n / 2) → ℂ, ∃ x : V, x ≠ 0 ∧ ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n), T h x = Formalism.UG.SatU ϖ q h α • x := by
  first | exact @GlobalTheory.HeckeSatakeEigen.exists_satU_eigenvector | exact GlobalTheory.HeckeSatakeEigen.exists_satU_eigenvector | (intros; apply GlobalTheory.HeckeSatakeEigen.exists_satU_eigenvector <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertHeckeOperatorPreservesProductLevelInvarianc

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.InertSatInv.heckeFunI_rt_invariant_prod : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (U : Subgroup (GAf L n)), (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) → (∀ κ ∈ U, ∃ a b : GAf L n, κ = a * b ∧ a ∈ Umax L n ∧ TrivOutside {v} a ∧ b ∈ U ∧ ∀ x : GAf L n, TrivOutside {v} x → b * x = x * b) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (h : Formalism.UG.GU Dv.σw n → ℂ), h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n) → ∀ f : GAf L n → W, (∀ κ ∈ U, NG.rt L n κ f = f) → ∀ κ ∈ U, NG.rt L n κ (heckeFunI L n U Dv h f) = heckeFunI L n U Dv h f := by
  intro L _ _ _ n v w Dv U hU hsplit W _ _ h hh f hf κ hκ
  refine GlobalTheory.heckeFunI_rt_invariant L n v w Dv U hU ?_ W h hh f hf κ hκ
  intro u hu
  obtain ⟨a, b, rfl, haM, hat, hbU, hbc⟩ := hsplit u hu
  exact ⟨a, b, rfl, (hU a hat).2 haM, hat, hbU, fun x hx => (hbc x hx).symm⟩
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertHeckeOperatorPreservesProductLevelInvariancStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.inertHeckeOperator_preserves_productLevel_invariance : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (U : Subgroup (GAf L n)), (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) → (∀ κ ∈ U, ∃ a b : GAf L n, κ = a * b ∧ a ∈ Umax L n ∧ TrivOutside {v} a ∧ b ∈ U ∧ ∀ x : GAf L n, TrivOutside {v} x → b * x = x * b) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (h : Formalism.UG.GU Dv.σw n → ℂ), h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n) → ∀ f : GAf L n → W, (∀ κ ∈ U, NG.rt L n κ f = f) → ∀ κ ∈ U, NG.rt L n κ (heckeFunI L n U Dv h f) = heckeFunI L n U Dv h f := by
  exact @GlobalTheory.InertSatInv.heckeFunI_rt_invariant_prod
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSatakeParameterInertDatumOfDictionarySpher

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.SatExist

theorem exists_satAt : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (π : NG.AutRep L n) (U : Submodule ℂ (UA L n → ℂ)), Dict F π U → ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → π.SphAt v → ∀ Dv : InertDatum L n v w, ∃ α, NG.SatAt π Dv α := by
  classical
  intro L _ _ _ n F π U₀ _ v w _ hsph Dv
  obtain ⟨f₀, hf₀S, hf₀0, hf₀K⟩ := hsph
  obtain ⟨-, N, hN, hf₀N⟩ := π.irrS.1.le hf₀S
  obtain ⟨U, hCU, hU, hdec⟩ := GlobalTheory.T.exists_level_full_at_inert_place_principal_elsewhere L n v N hN
  have hdec' : ∀ κ ∈ U, ∃ a b : GAf L n, κ = a * b ∧ a ∈ Umax L n ∧ TrivOutside {v} a ∧ b ∈ U ∧
      ∀ x : GAf L n, TrivOutside {v} x → b * x = x * b := fun κ hκ => by
    obtain ⟨a, b, e, ha, hta, hb, hc⟩ := hdec κ hκ
    exact ⟨a, b, e, ha, hta, hCU b hb, hc⟩
  have hf₀U : ∀ κ ∈ U, NG.rt L n κ f₀ = f₀ := fun κ hκ => by
    obtain ⟨a, b, rfl, ha, hta, hb, -⟩ := hdec κ hκ
    funext g
    show f₀ (g * (a * b)) = f₀ g
    rw [← mul_assoc, hf₀N b hb]
    exact congrFun (hf₀K a ha hta) g
  let V : Submodule ℂ (GAf L n → π.W) :=
    { carrier := {f | f ∈ π.S ∧ ∀ κ ∈ U, NG.rt L n κ f = f}
      add_mem' := fun {f f'} hf hf' => ⟨π.S.add_mem hf.1 hf'.1, fun κ hκ => by
        rw [map_add (f := _), hf.2 κ hκ, hf'.2 κ hκ]⟩
      zero_mem' := ⟨π.S.zero_mem, fun κ _ => map_zero _⟩
      smul_mem' := fun c f hf => ⟨π.S.smul_mem c hf.1, fun κ hκ => by rw [map_smul, hf.2 κ hκ]⟩ }
  haveI : FiniteDimensional ℂ π.W := π.alg.1
  haveI := GlobalTheory.AlgFormsFin.fixedForms_finite L n π.ρ (GlobalTheory.T.finite_doubleCosets_definiteUnitary_maximalLevel L n) hN
  haveI hVfin : FiniteDimensional ℂ V :=
    Submodule.finiteDimensional_of_le (S₂ := GlobalTheory.AlgFormsFin.fixedForms L n π.ρ N) fun f hf =>
      ⟨(π.irrS.1.le hf.1).1, fun κ hκ g => congrFun (hf.2 κ (hCU κ hκ)) g⟩
  have hfin := fun h hh => GlobalTheory.SatInd.CosetFin.finite_inert_support L n v w Dv
    (GlobalTheory.SatInd.DCoset.finite_dcoset Dv.ϖ Dv.σw _ n Dv.unram)
    (GlobalTheory.InertUmax.mem_Umax_of_trivOutside_of_loc_integral L n v w Dv) U hU h hh
  have hsum : ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n),
      ∃ (C : Finset (GAf L n ⧸ U)) (a : GAf L n ⧸ U → ℂ) (x : GAf L n ⧸ U → GAf L n),
        ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (φ : GAf L n → W),
          heckeFunI L n U Dv h φ = ∑ c ∈ C, a c • NG.rt L n (x c) φ := by
    intro h hh
    let hf := hfin h hh
    refine ⟨hf.toFinset,
      fun c => if hc : ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x then
        Dv.hval h (Dv.loc hc.choose) else 0,
      fun c => if hc : ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x then
        hc.choose else 1, fun W _ _ φ => ?_⟩
    funext g
    unfold heckeFunI
    rw [finsum_eq_sum_of_support_subset (s := hf.toFinset)]
    · rw [Finset.sum_apply]
      refine Finset.sum_congr rfl fun c _ => ?_
      by_cases hc : ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x
      · simp only [dif_pos hc]
        rfl
      · simp only [dif_neg hc, zero_smul]
        rfl
    · intro c hc0
      rw [Function.mem_support] at hc0
      by_cases hc : ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x
      · rw [dif_pos hc] at hc0
        rw [Set.Finite.coe_toFinset]
        refine ⟨hc.choose, hc.choose_spec.1, hc.choose_spec.2, fun h0 => hc0 ?_⟩
        rw [h0, zero_smul]
      · exact absurd (dif_neg hc) hc0
  have hmemV : ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n), ∀ f ∈ V, heckeFunI L n U Dv h f ∈ V := by
    intro h hh f hf
    refine ⟨?_, GlobalTheory.T.inertHeckeOperator_preserves_productLevel_invariance L n v w Dv U hU hdec' π.W h hh f hf.2⟩
    obtain ⟨C, a, x, hC⟩ := hsum h hh
    rw [hC]
    exact π.S.sum_mem fun c _ => π.S.smul_mem _ (π.irrS.1.stable _ _ hf.1)
  let T : (Formalism.UG.GU Dv.σw n → ℂ) → Module.End ℂ V := fun h =>
    if hh : h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n) then
      { toFun := fun f => ⟨heckeFunI L n U Dv h f, hmemV h hh f f.2⟩
        map_add' := fun f f' => Subtype.ext (by
          obtain ⟨C, a, x, hC⟩ := hsum h hh
          simp only [Submodule.coe_add, hC, map_add (f := _), smul_add, Finset.sum_add_distrib])
        map_smul' := fun c f => Subtype.ext (by
          obtain ⟨C, a, x, hC⟩ := hsum h hh
          simp only [Submodule.coe_smul, hC, map_smul, RingHom.id_apply, Finset.smul_sum]
          exact Finset.sum_congr rfl fun c' _ => smul_comm _ _ _) }
    else 0
  have hT : ∀ h (hh : h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n)) (f : V),
      ((T h f : V) : GAf L n → π.W) = heckeFunI L n U Dv h f := fun h hh f => by
    simp only [T, dif_pos hh]
    rfl
  have hK := Formalism.UG.P.isCommensurated_integral_unitary_of_unramified Dv.unram n
  obtain ⟨α, x, hx0, hx⟩ := GlobalTheory.T.exists_satU_eigenvector_alt Dv.ϖ Dv.σw _ n Dv.unram V T
    (fun h₁ hh₁ h₂ hh₂ => LinearMap.ext fun f => Subtype.ext (by
      rw [LinearMap.add_apply, Submodule.coe_add, hT (h₁ + h₂) (add_mem hh₁ hh₂) f, hT h₁ hh₁ f, hT h₂ hh₂ f]
      exact (GlobalTheory.T.heckeFunI_add_and_smul L n v w Dv U hU π.W h₁ h₂ hh₁ hh₂ 0 f).1))
    (fun c h hh => LinearMap.ext fun f => Subtype.ext (by
      rw [LinearMap.smul_apply, Submodule.coe_smul, hT (c • h) (Submodule.smul_mem _ c hh) f, hT h hh f]
      exact (GlobalTheory.T.heckeFunI_add_and_smul L n v w Dv U hU π.W h h hh hh c f).2))
    (LinearMap.ext fun f => Subtype.ext (by
      rw [hT _ (Formalism.UG.Final.DosetIndMem _ _ ℂ 1) f]
      exact GlobalTheory.T.inertHeckeOperator_maximalCompact_indicator_eq_id L n v w Dv U hU π.W f f.2.2))
    (fun h₁ hh₁ h₂ hh₂ => LinearMap.ext fun f => Subtype.ext (by
      rw [Module.End.mul_apply, hT _ (Formalism.UG.Final.HeckeConvMem _ _ ℂ hK _ hh₁ _ hh₂) f, hT h₁ hh₁ (T h₂ f), hT h₂ hh₂ f]
      exact GlobalTheory.T.inertHeckeOperator_convolution_eq_comp L n v w Dv U hU π.W h₁ h₂ hh₁ hh₂ f f.2.2))
    ⟨f₀, hf₀S, hf₀U⟩ (fun h => hf₀0 (congrArg Subtype.val h))
  refine ⟨α, x, x.2.1, fun h => hx0 (Subtype.ext h), U, x.2.2, hU, fun h hh => ?_⟩
  have e := congrArg Subtype.val (hx h hh)
  rw [hT h hh] at e
  exact e

end GlobalTheory.SatExist
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSatakeParameterInertDatumOfDictionarySpherStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.exists_satakeParameter_inertDatum_of_dictionary_spherical : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (π : NG.AutRep L n) (U : Submodule ℂ (UA L n → ℂ)), Dict F π U → ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → π.SphAt v → ∀ Dv : InertDatum L n v w, ∃ α, NG.SatAt π Dv α := by
  first | exact @GlobalTheory.SatExist.exists_satAt | exact GlobalTheory.SatExist.exists_satAt | (intros; apply GlobalTheory.SatExist.exists_satAt <;> assumption)
end
end
