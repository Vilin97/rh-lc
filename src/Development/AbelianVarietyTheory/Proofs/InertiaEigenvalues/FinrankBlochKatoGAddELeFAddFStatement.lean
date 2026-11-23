module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CrystallineCocycles
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import CompanionTheory.AutomorphicTheory.PadicCyclotomicFields.GcohTop
public import CompanionTheory.AutomorphicTheory.PadicCyclotomicFields.GcohTopEuler
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoExactAnnihilatorsPeriodDatum
public import Formalism.GaloisCohomology.LocalTateDualityK
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
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamCocycleDimensionCompareStatement
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.TypeStar
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dual.Lemmas
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankH1DualPairStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateDualityDegreeOneContinuousCocyclesStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Mathlib.Tactic.Linter.HaveILetI
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoExactAnnihilatorsPeriodDatumStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.blochKato_exact_annihilators_periodDatum : Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ K : FinExt l, bkACore (P.PD K) := by
  first | exact @GlobalTheory.BlochKatoAnn.bkA_exact_annihilators | exact GlobalTheory.BlochKatoAnn.bkA_exact_annihilators | (intros; apply GlobalTheory.BlochKatoAnn.bkA_exact_annihilators <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankAnnihilatorAdd

section

@[expose] public section

open Module

namespace GlobalTheory.HyodoDef.PairLin

variable {k M M' : Type*} [Field k] [AddCommGroup M] [Module k M] [AddCommGroup M'] [Module k M']
  [FiniteDimensional k M] [FiniteDimensional k M']

theorem finrank_annihilator_add (β : M →ₗ[k] M' →ₗ[k] k) (S : Submodule k M')
    (hS : LinearMap.ker β.flip ≤ S) :
    finrank k (LinearMap.ker (S.subtype.dualMap ∘ₗ β)) + finrank k S
      = finrank k M + finrank k (LinearMap.ker β.flip) := by
  set φ : M →ₗ[k] Dual k S := S.subtype.dualMap ∘ₗ β with hφ
  set ψ : S →ₗ[k] Dual k M := β.flip ∘ₗ S.subtype with hψ
  have hφψ : φ = ψ.dualMap ∘ₗ (Module.evalEquiv k M).toLinearMap := by
    ext a s; rfl
  have hrange : LinearMap.range φ = LinearMap.range ψ.dualMap := by
    rw [hφψ, LinearEquiv.range_comp]
  have h1 := LinearMap.finrank_range_add_finrank_ker φ
  have h2 := LinearMap.finrank_range_add_finrank_ker ψ
  have h3 : finrank k (LinearMap.range φ) = finrank k (LinearMap.range ψ) := by
    rw [hrange, LinearMap.finrank_range_dualMap_eq_finrank_range]
  have h4 : finrank k (LinearMap.ker ψ) = finrank k (LinearMap.ker β.flip) := by
    have : LinearMap.ker ψ = (LinearMap.ker β.flip).comap S.subtype := by
      rw [hψ, LinearMap.ker_comp]
    rw [this]
    exact (Submodule.comapSubtypeEquivOfLe hS).finrank_eq
  omega

theorem finrank_add_le (β : M →ₗ[k] M' →ₗ[k] k) (Ag Af : Submodule k M) (Ae Af' : Submodule k M')
    (hN : ∀ b : M', (∀ a : M, β a b = 0) → b ∈ Ae ⊓ Af')
    (hg : ∀ a ∈ Ag, ∀ b ∈ Ae, β a b = 0)
    (hf : ∀ a : M, a ∈ Af ↔ ∀ b ∈ Af', β a b = 0) :
    finrank k Ag + finrank k Ae ≤ finrank k Af + finrank k Af' := by
  have hker : ∀ b : M', b ∈ LinearMap.ker β.flip → b ∈ Ae ⊓ Af' := by
    intro b hb
    apply hN b
    intro a
    have := LinearMap.congr_fun (LinearMap.mem_ker.mp hb) a
    simpa using this
  have hNe : LinearMap.ker β.flip ≤ Ae := fun b hb => (hker b hb).1
  have hNf : LinearMap.ker β.flip ≤ Af' := fun b hb => (hker b hb).2
  have he := finrank_annihilator_add β Ae hNe
  have hf' := finrank_annihilator_add β Af' hNf
  have hgle : Ag ≤ LinearMap.ker (Ae.subtype.dualMap ∘ₗ β) := by
    intro a ha
    rw [LinearMap.mem_ker]
    ext ⟨b, hb⟩
    simpa using hg a ha b hb
  have hfeq : Af = LinearMap.ker (Af'.subtype.dualMap ∘ₗ β) := by
    ext a
    rw [hf a, LinearMap.mem_ker]
    constructor
    · intro h
      ext ⟨b, hb⟩
      simpa using h b hb
    · intro h b hb
      have := LinearMap.congr_fun h ⟨b, hb⟩
      simpa using this
  have hAg := Submodule.finrank_mono hgle
  rw [hfeq]
  omega

end GlobalTheory.HyodoDef.PairLin
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankBlochKatoGAddELeFAddF

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.HyodoDef GlobalTheory.Pst TensorProduct Module

namespace GlobalTheory.HyodoDef.Count

theorem finrank_blochKato_g_add_e_le_f_add_f_alt : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [ContinuousAdd V] [ContinuousConstSMul ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V) (V' : Type) [AddCommGroup V'] [Module ℚ_[l] V'] [FiniteDimensional ℚ_[l] V'] [TopologicalSpace V'] [IsModuleTopology ℚ_[l] V'] [ContinuousAdd V'] [ContinuousConstSMul ℚ_[l] V'] (ρ' : Representation ℚ_[l] ↥(GK K) V') (m : V →ₗ[ℚ_[l]] V' →ₗ[ℚ_[l]] ℚ_[l]), (∀ v, Continuous fun g => ρ g v) → (∀ y, Continuous fun g => ρ' g y) → IsDR (P.PD K) ρ → IsDR (P.PD K) ρ' → IsDual1 (P.PD K) ρ ρ' m → finrank ℚ_[l] ↥(geometricCocycles (P.PD K) ρ) + finrank ℚ_[l] ↥(crystallineCocycles (P.PD K) ρ') ≤ finrank ℚ_[l] ↥(finiteCocycles (P.PD K) ρ) + finrank ℚ_[l] ↥(finiteCocycles (P.PD K) ρ') := by
  intro l _ P AI hT K V _ _ _ _ _ _ _ ρ V' _ _ _ _ _ _ _ ρ' m hc hc' hdR hdR' hdual
  letI : Module ℤ_[l] V := Module.compHom V (algebraMap ℤ_[l] ℚ_[l])
  haveI : IsScalarTower ℤ_[l] ℚ_[l] V := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  letI : Module ℤ_[l] V' := Module.compHom V' (algebraMap ℤ_[l] ℚ_[l])
  haveI : IsScalarTower ℤ_[l] ℚ_[l] V' := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hO := GlobalTheory.Published.BlochKato.goodO_padicInt (l := l)
  have hTD := CompanionTheory.LocalTateOrthogonality.Gcoh.top_tate
  have hEC := CompanionTheory.LocalTateOrthogonality.Gcoh.top_euler
  let A : GRep ↥(GK K) ℚ_[l] ℚ_[l] ℤ_[l] := { V := V, ρ := ρ, cont := hc }
  let A' : GRep ↥(GK K) ℚ_[l] ℚ_[l] ℤ_[l] := { V := V', ρ := ρ', cont := hc' }
  have hdual' : IsDual1 (P.PD K) ρ' ρ m.flip := by
    obtain ⟨h1, h2, h3, h4⟩ := hdual
    refine ⟨fun g y x => ?_, fun y hy => h3 y hy, fun x hx => h2 x hx, h4.symm⟩
    simp only [LinearMap.flip_apply]
    exact h1 g x y
  obtain ⟨hfin, -⟩ := GlobalTheory.T.finrank_H1_dual_pair hTD hEC l P K ℚ_[l] ℤ_[l] hO A A' m hdual
  obtain ⟨hfin', -⟩ := GlobalTheory.T.finrank_H1_dual_pair hTD hEC l P K ℚ_[l] ℤ_[l] hO A' A m.flip hdual'
  haveI : FiniteDimensional ℚ_[l] (continuousCocycles ρ) := GlobalTheory.BlochKatoAnn.finite_continuous_cocycles_localGaloisRep A hfin
  haveI : FiniteDimensional ℚ_[l] (continuousCocycles ρ') := GlobalTheory.BlochKatoAnn.finite_continuous_cocycles_localGaloisRep A' hfin'
  obtain ⟨β, hβ, -, hr⟩ : ∃ β : ↥(continuousCocycles ρ) →ₗ[ℚ_[l]] ↥(continuousCocycles ρ') →ₗ[ℚ_[l]] ℚ_[l],
      (∀ a b, β a b = 0 ↔ CobL (P.PD K) (cupL ρ' m a.1 b.1)) ∧
      (∀ a, (∀ b, β a b = 0) ↔ a.1 ∈ B1 ρ) ∧ ∀ b, (∀ a, β a b = 0) ↔ b.1 ∈ B1 ρ' :=
    GlobalTheory.T.tateDuality_degreeOne_continuous_cocycles hTD l P K ℚ_[l] ℤ_[l] hO A A' m hdual
  have hann : ∀ a ∈ continuousCocycles ρ, (a ∈ finiteCocycles (P.PD K) ρ ↔
      ∀ b ∈ finiteCocycles (P.PD K) ρ', CobL (P.PD K) (cupL ρ' m a b)) :=
    (GlobalTheory.T.blochKato_exact_annihilators_periodDatum hTD hEC l P AI hT K ℚ_[l] ℤ_[l] hO A A' m hdR hdual).1
  have horth := GlobalTheory.T.de_rham_cocycle_dimension_compare l P AI hT K V ρ V' ρ' m hc hc' hdR' hdual
  have hg : geometricCocycles (P.PD K) ρ ≤ continuousCocycles ρ := fun _ h => h.1
  have he : crystallineCocycles (P.PD K) ρ' ≤ continuousCocycles ρ' := fun _ h => h.1
  have hf : finiteCocycles (P.PD K) ρ ≤ continuousCocycles ρ := fun _ h => h.1
  have hf' : finiteCocycles (P.PD K) ρ' ≤ continuousCocycles ρ' := fun _ h => h.1
  have hBf : B1 ρ' ≤ finiteCocycles (P.PD K) ρ' := GlobalTheory.BlochKatoAnn.B1_le_Z1f (P.PD K) A'
  have hBe : B1 ρ' ≤ crystallineCocycles (P.PD K) ρ' := by
    intro c hcB
    refine ⟨hf' (hBf hcB), ?_⟩
    obtain ⟨x, rfl⟩ := hcB
    refine ⟨x ⊗ₜ[ℚ_[l]] 1, ?_, fun g => ?_⟩
    · simp [φVB]
    · simp [cob, actVB, sub_tmul]
  have key := GlobalTheory.HyodoDef.PairLin.finrank_add_le β
    ((geometricCocycles (P.PD K) ρ).comap (continuousCocycles ρ).subtype) ((finiteCocycles (P.PD K) ρ).comap (continuousCocycles ρ).subtype)
    ((crystallineCocycles (P.PD K) ρ').comap (continuousCocycles ρ').subtype) ((finiteCocycles (P.PD K) ρ').comap (continuousCocycles ρ').subtype)
    (fun b hb => ⟨hBe ((hr b).1 hb), hBf ((hr b).1 hb)⟩)
    (fun a ha b hb => (hβ a b).2 (horth a.1 ha b.1 hb))
    (fun a => by
      rw [Submodule.mem_comap, Submodule.subtype_apply, hann a.1 a.2]
      constructor
      · intro h b hb
        exact (hβ a b).2 (h b.1 hb)
      · intro h b hb
        exact (hβ a ⟨b, hf' hb⟩).1 (h ⟨b, hf' hb⟩ hb))
  rwa [(Submodule.comapSubtypeEquivOfLe hg).finrank_eq,
    (Submodule.comapSubtypeEquivOfLe he).finrank_eq,
    (Submodule.comapSubtypeEquivOfLe hf).finrank_eq,
    (Submodule.comapSubtypeEquivOfLe hf').finrank_eq] at key

end GlobalTheory.HyodoDef.Count
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankBlochKatoGAddELeFAddFStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.HyodoDef GlobalTheory.Pst TensorProduct Module

theorem _root_.GlobalTheory.T.finrank_blochKato_g_add_e_le_f_add_f : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [ContinuousAdd V] [ContinuousConstSMul ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V) (V' : Type) [AddCommGroup V'] [Module ℚ_[l] V'] [FiniteDimensional ℚ_[l] V'] [TopologicalSpace V'] [IsModuleTopology ℚ_[l] V'] [ContinuousAdd V'] [ContinuousConstSMul ℚ_[l] V'] (ρ' : Representation ℚ_[l] ↥(GK K) V') (m : V →ₗ[ℚ_[l]] V' →ₗ[ℚ_[l]] ℚ_[l]), (∀ v, Continuous fun g => ρ g v) → (∀ y, Continuous fun g => ρ' g y) → IsDR (P.PD K) ρ → IsDR (P.PD K) ρ' → IsDual1 (P.PD K) ρ ρ' m → finrank ℚ_[l] ↥(geometricCocycles (P.PD K) ρ) + finrank ℚ_[l] ↥(crystallineCocycles (P.PD K) ρ') ≤ finrank ℚ_[l] ↥(finiteCocycles (P.PD K) ρ) + finrank ℚ_[l] ↥(finiteCocycles (P.PD K) ρ') := by
  first | exact @GlobalTheory.HyodoDef.Count.finrank_blochKato_g_add_e_le_f_add_f_alt | exact GlobalTheory.HyodoDef.Count.finrank_blochKato_g_add_e_le_f_add_f_alt | (intros; apply GlobalTheory.HyodoDef.Count.finrank_blochKato_g_add_e_le_f_add_f_alt <;> assumption)
end
end
