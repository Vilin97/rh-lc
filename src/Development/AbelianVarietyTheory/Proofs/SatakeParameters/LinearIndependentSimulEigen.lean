module

public import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.ClosedAtLConclusionOfMem
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DefiniteUnitaryRealApproxAndFiniteInfiniteSplit
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsConjIsAutFormU
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjugatesAutomorphicFormSpanFiniteDimensionalStatement
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
public import Formalism.ConjugateSelfDual.Statement
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.HaveILetI
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Analysis.CStarAlgebra.Classes

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.DefiniteUnitaryRationalHeckeCommuteComplexAutomo

section

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.CuspRep GlobalTheory.PRep
open scoped Pointwise

noncomputable section

namespace GlobalTheory.EigenConj

theorem opOf_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (σ : ℂ ≃+* ℂ) (t : UA E n →₀ ℂ), (∀ g ∈ t.support, g ∈ finU (E := E) (n := n) ∧ ∃ q : ℚ, t g = q) → ∀ (φ φ' : UA E n → ℂ) (z : ℂ), IsAutFormU φ → IsAutFormU φ' → (∀ g ∈ finU (E := E) (n := n), φ' g = σ (φ g)) → opOf (RU E n) t φ = z • φ → opOf (RU E n) t φ' = σ z • φ' := by
  intro E _ _ _ n σ t ht φ φ' z hφ hφ' hfin heig
  have key : ∀ (f : UA E n → ℂ) (x : UA E n),
      opOf (RU E n) t f x = ∑ g ∈ t.support, t g * f (x * g) := by
    intro f x
    simp only [opOf, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rfl
  have hc1 : Continuous (opOf (RU E n) t φ') := by
    have e : opOf (RU E n) t φ' = fun x => ∑ g ∈ t.support, t g * φ' (x * g) := funext (key φ')
    rw [e]
    exact continuous_finsetSum _ fun g _ =>
      continuous_const.mul (hφ'.cont.comp (continuous_id.mul continuous_const))
  have hc2 : Continuous (σ z • φ') := hφ'.cont.const_smul _
  have hl1 : ∀ γ ∈ ratU E n, ∀ x, opOf (RU E n) t φ' (γ * x) = opOf (RU E n) t φ' x := by
    intro γ hγ x
    rw [key, key]
    simp_rw [mul_assoc, hφ'.left γ hγ]
  have hl2 : ∀ γ ∈ ratU E n, ∀ x, (σ z • φ') (γ * x) = (σ z • φ') x := by
    intro γ hγ x
    simp only [Pi.smul_apply, hφ'.left γ hγ]
  have hfinEq : ∀ h ∈ finU (E := E) (n := n), opOf (RU E n) t φ' h = (σ z • φ') h := by
    intro h hh
    have e := congrFun heig h
    rw [key, Pi.smul_apply, smul_eq_mul] at e
    rw [key, Pi.smul_apply, smul_eq_mul]
    calc ∑ g ∈ t.support, t g * φ' (h * g) = ∑ g ∈ t.support, σ (t g * φ (h * g)) :=
          Finset.sum_congr rfl fun g hg => by
            obtain ⟨hgU, q, hq⟩ := ht g hg
            rw [map_mul, hfin _ ((finU (E := E) (n := n)).mul_mem hh hgU), hq, map_ratCast]
      _ = σ (∑ g ∈ t.support, t g * φ (h * g)) := (map_sum σ _ _).symm
      _ = σ (z * φ h) := by rw [e]
      _ = σ z * φ' h := by rw [map_mul, hfin h hh]
  have hon : Set.EqOn (opOf (RU E n) t φ') (σ z • φ') ((ratU E n : Set (UA E n)) * (finU (E := E) (n := n) : Set (UA E n))) := by
    rintro _ ⟨γ, hγ, g, hg, rfl⟩
    rw [hl1 γ hγ, hl2 γ hγ]
    exact hfinEq g hg
  exact Continuous.ext_on (GlobalTheory.UnitarySplit.dense_and_split E n).1 hc1 hc2 hon

end GlobalTheory.EigenConj
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.DefiniteUnitaryRationalHeckeCommuteComplexAutomoStatement

section

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.CuspRep GlobalTheory.PRep

theorem _root_.GlobalTheory.T.definiteUnitaryRationalHecke_commute_complexAutomorphism : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (σ : ℂ ≃+* ℂ) (t : UA E n →₀ ℂ), (∀ g ∈ t.support, g ∈ finU (E := E) (n := n) ∧ ∃ q : ℚ, t g = q) → ∀ (φ φ' : UA E n → ℂ) (z : ℂ), IsAutFormU φ → IsAutFormU φ' → (∀ g ∈ finU (E := E) (n := n), φ' g = σ (φ g)) → opOf (RU E n) t φ = z • φ → opOf (RU E n) t φ' = σ z • φ' := by
  first | exact @GlobalTheory.EigenConj.opOf_conj | exact GlobalTheory.EigenConj.opOf_conj | (intros; apply GlobalTheory.EigenConj.opOf_conj <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteAutomorphismOrbitMemFiniteExtensionPadic

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.ConjugateSelfDual GlobalTheory.Cong

namespace GlobalTheory

theorem orbit_finite_mem_finite_ext : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (J : Type) (z : J → ℂ),
    (Set.range fun σ : ℂ ≃+* ℂ => fun j => σ (z j)).Finite →
      ∃ L : IntermediateField ℚ_[l] (Qbar l), FiniteDimensional ℚ_[l] L ∧ ∀ j, ι.symm (z j) ∈ L := by
  intro l _ ι J z hfin
  classical
  set O := Set.range fun σ : ℂ ≃+* ℂ => fun j => σ (z j) with hO
  haveI : Finite O := hfin.to_subtype
  set w : J → Qbar l := fun j => ι.symm (z j) with hw
  let K : Finset J → IntermediateField ℚ_[l] (Qbar l) := fun s =>
    IntermediateField.adjoin ℚ_[l] (w '' (s : Set J))
  have hKfin : ∀ s, FiniteDimensional ℚ_[l] (K s) := fun s => by
    haveI : Finite (w '' (s : Set J)) := (s.finite_toSet.image w).to_subtype
    exact IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  have hbound : ∀ s, Module.finrank ℚ_[l] (K s) ≤ Nat.card O := by
    intro s
    haveI := hKfin s
    rw [← AlgHom.card ℚ_[l] (K s) (Qbar l), ← Nat.card_eq_fintype_card]
    let g : (K s →ₐ[ℚ_[l]] Qbar l) → O := fun φ =>
      ⟨fun j => ι (φ.liftNormal (Qbar l) (w j)),
        ι.symm.trans ((AlgEquiv.ofBijective (φ.liftNormal (Qbar l))
          (Algebra.IsAlgebraic.algHom_bijective _)).toRingEquiv.trans ι), rfl⟩
    apply Nat.card_le_card_of_injective g
    intro φ ψ h
    apply IntermediateField.adjoin_algHom_ext
    rintro x ⟨j, hj, rfl⟩
    have h1 := ι.injective (congrFun (congrArg Subtype.val h) j)
    have e1 := AlgHom.liftNormal_commutes φ (Qbar l) ⟨w j, IntermediateField.subset_adjoin _ _ ⟨j, hj, rfl⟩⟩
    have e2 := AlgHom.liftNormal_commutes ψ (Qbar l) ⟨w j, IntermediateField.subset_adjoin _ _ ⟨j, hj, rfl⟩⟩
    simp only [Algebra.algebraMap_self, RingHom.id_apply] at e1 e2
    exact e1.symm.trans (h1.trans e2)
  set R := Set.range fun s : Finset J => Module.finrank ℚ_[l] (K s) with hR
  have hne : R.Nonempty := ⟨_, ∅, rfl⟩
  have hbdd : BddAbove R := ⟨Nat.card O, by rintro _ ⟨s, rfl⟩; exact hbound s⟩
  obtain ⟨s0, hs0⟩ := Nat.sSup_mem hne hbdd
  haveI := hKfin s0
  refine ⟨K s0, inferInstance, fun j => ?_⟩
  have hle : K s0 ≤ K (insert j s0) :=
    IntermediateField.adjoin.mono _ _ _ (Set.image_mono (by simp))
  haveI := hKfin (insert j s0)
  have heq : K s0 = K (insert j s0) := by
    apply IntermediateField.eq_of_le_of_finrank_le hle
    rw [show Module.finrank ℚ_[l] (K s0) = sSup R from hs0]
    exact le_csSup hbdd ⟨insert j s0, rfl⟩
  rw [heq]
  exact IntermediateField.subset_adjoin _ _ ⟨j, by simp, rfl⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteAutomorphismOrbitMemFiniteExtensionPadicStatement

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.ConjugateSelfDual GlobalTheory.Cong

theorem _root_.GlobalTheory.T.finite_automorphism_orbit_mem_finite_extension_padic : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (J : Type) (z : J → ℂ), (Set.range fun σ : ℂ ≃+* ℂ => fun j => σ (z j)).Finite → ∃ L : IntermediateField ℚ_[l] (Qbar l), FiniteDimensional ℚ_[l] L ∧ ∀ j, ι.symm (z j) ∈ L := by
  first | exact @GlobalTheory.orbit_finite_mem_finite_ext | exact GlobalTheory.orbit_finite_mem_finite_ext | (intros; apply GlobalTheory.orbit_finite_mem_finite_ext; all_goals assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.LinearIndependentJointEigenvectors

section

@[expose] public section

namespace GlobalTheory.JointEigenvectorsIndependentSatakeParameters

theorem linearIndependent_jointEigenvectors {J V : Type} [AddCommGroup V] [Module ℂ V]
    (T : J → V →ₗ[ℂ] V) (S : Set (J → ℂ)) (v : S → V)
    (hv : ∀ χ : S, v χ ≠ 0)
    (hT : ∀ (χ : S) (j : J), T j (v χ) = (χ : J → ℂ) j • v χ) :
    LinearIndependent ℂ v := by
  classical
  rw [linearIndependent_iff']
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro g _ i hi
    simp at hi
  | insert a s ha ih =>
    intro g hg
    rw [Finset.sum_insert ha] at hg
    have e1 : ∑ i ∈ s, g i • v i = -(g a • v a) := eq_neg_of_add_eq_zero_right hg
    have hs : ∀ i ∈ s, g i = 0 := by
      intro i hi
      have hne : (i : J → ℂ) ≠ a := fun h => ha (Subtype.ext h ▸ hi)
      obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
      have e2 : ∑ i ∈ s, (g i * (i : J → ℂ) j) • v i = -((g a * (a : J → ℂ) j) • v a) := by
        have := congrArg (T j) e1

        simpa [map_sum, map_smul, hT, smul_smul] using this
      have e3 : ∑ i ∈ s, ((a : J → ℂ) j * g i) • v i = -(((a : J → ℂ) j * g a) • v a) := by
        have := congrArg (fun x => (a : J → ℂ) j • x) e1
        simpa [Finset.smul_sum, smul_smul] using this
      have h2 : ∑ i ∈ s, (g i * ((i : J → ℂ) j - (a : J → ℂ) j)) • v i = 0 := by
        calc ∑ i ∈ s, (g i * ((i : J → ℂ) j - (a : J → ℂ) j)) • v i
            = ∑ i ∈ s, (g i * (i : J → ℂ) j) • v i - ∑ i ∈ s, ((a : J → ℂ) j * g i) • v i := by
              rw [← Finset.sum_sub_distrib]
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [← sub_smul]
              congr 1
              ring
          _ = 0 := by rw [e2, e3, mul_comm ((a : J → ℂ) j) (g a)]; exact sub_self _
      have := ih (fun i => g i * ((i : J → ℂ) j - (a : J → ℂ) j)) h2 i hi
      exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hj)
    have hsum : ∑ i ∈ s, g i • v i = 0 := Finset.sum_eq_zero fun i hi => by rw [hs i hi, zero_smul]
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · rw [hsum, add_zero] at hg
      exact (smul_eq_zero.mp hg).resolve_right (hv _)
    · exact hs i hi

end GlobalTheory.JointEigenvectorsIndependentSatakeParameters
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.LinearIndependentSimulEigen

section

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong
open scoped Pointwise

noncomputable section

namespace GlobalTheory.Cong

theorem linearIndependent_simulEigen {J V : Type} [AddCommGroup V] [Module ℂ V] (T : J → V →ₗ[ℂ] V)
    (S : Set (J → ℂ)) (v : S → V) (hv : ∀ χ, v χ ≠ 0)
    (hT : ∀ (χ : S) j, T j (v χ) = (χ : J → ℂ) j • v χ) : LinearIndependent ℂ v := by
  first
  | exact @_root_.GlobalTheory.JointEigenvectorsIndependentSatakeParameters.linearIndependent_jointEigenvectors
  | exact _root_.GlobalTheory.JointEigenvectorsIndependentSatakeParameters.linearIndependent_jointEigenvectors
  | (apply _root_.GlobalTheory.JointEigenvectorsIndependentSatakeParameters.linearIndependent_jointEigenvectors <;> assumption)
  | (intros; apply _root_.GlobalTheory.JointEigenvectorsIndependentSatakeParameters.linearIndependent_jointEigenvectors <;> assumption)
  | (intros; apply @_root_.GlobalTheory.JointEigenvectorsIndependentSatakeParameters.linearIndependent_jointEigenvectors <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.JointEigenvectorsIndependentSatakeParameters.linearIndependent_jointEigenvectors ..)

def opLin {Γ V : Type} [Group Γ] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ Γ V) (f : Γ →₀ ℂ) :
    V →ₗ[ℂ] V :=
  f.sum fun g c => c • ρ g

theorem opLin_apply {Γ V : Type} [Group Γ] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ Γ V) (f : Γ →₀ ℂ)
    (v : V) : opLin ρ f v = opOf ρ f v := by
  simp [opLin, opOf, Finsupp.sum, LinearMap.sum_apply]

theorem eq_zero_of_finU {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {φ : UA E n → ℂ}
    (hφ : IsAutFormU φ) (h0 : ∀ g ∈ finU (E := E) (n := n), φ g = 0) : φ = 0 := by
  refine Continuous.ext_on (GlobalTheory.UnitarySplit.dense_and_split E n).1 hφ.cont continuous_const ?_
  rintro x ⟨γ, hγ, g, hg, rfl⟩
  simp only [Pi.zero_apply]
  rw [hφ.left γ hγ g]
  exact h0 g hg

theorem finU_holds : FinU := by
  intro E _ _ _ l _ ι a _ w₀ K _ lam J t η ht hact U hU
  obtain ⟨φ, hφU, hφ0, hφK⟩ := hU.fix
  have hφ : IsAutFormU φ := hU.aut.aut φ hφU
  have heig : ∀ j, opOf (RU E a) (t j) φ = η U j • φ := fun j => hact U hU.aut φ hφU hφK j
  obtain ⟨g₀, hg₀, hφg₀⟩ : ∃ g ∈ finU (E := E) (n := a), φ g ≠ 0 := by
    by_contra h
    push_neg at h
    exact hφ0 (eq_zero_of_finU hφ h)
  choose φ' hφ' hφ'eq using fun σ : ℂ ≃+* ℂ => exists_conj_isAutFormU E a σ φ hφ
  obtain ⟨M, hMfin, hM⟩ := GlobalTheory.T.conjugates_automorphicForm_span_finiteDimensional E a φ hφ
  have heig' : ∀ σ j, opOf (RU E a) (t j) (φ' σ) = σ (η U j) • φ' σ := fun σ j =>
    GlobalTheory.T.definiteUnitaryRationalHecke_commute_complexAutomorphism E a σ (t j) (ht j) φ (φ' σ) (η U j) hφ (hφ' σ) (hφ'eq σ) (heig j)
  have hne : ∀ σ, φ' σ ≠ 0 := by
    intro σ h
    have e := hφ'eq σ g₀ hg₀
    rw [h, Pi.zero_apply, eq_comm, map_eq_zero_iff σ σ.injective] at e
    exact hφg₀ e
  have hfin : (Set.range fun σ : ℂ ≃+* ℂ => fun j => σ (η U j)).Finite := by
    set S := Set.range fun σ : ℂ ≃+* ℂ => fun j => σ (η U j) with hS
    have hch : ∀ χ : S, ∃ σ : ℂ ≃+* ℂ, (fun j => σ (η U j)) = (χ : J → ℂ) := fun χ => χ.2
    choose sel hsel using hch
    let v : S → (UA E a → ℂ) := fun χ => φ' (sel χ)
    have hli : LinearIndependent ℂ v := by
      refine linearIndependent_simulEigen (fun j => opLin (RU E a) (t j)) S v (fun χ => hne _) ?_
      intro χ j
      rw [opLin_apply, heig', ← hsel χ]
    let v' : S → M := fun χ => ⟨v χ, hM (sel χ) (φ' (sel χ)) (hφ' _) (hφ'eq _)⟩
    have hli' : LinearIndependent ℂ v' := LinearIndependent.of_comp M.subtype hli
    have : Finite S := hli'.finite
    exact Set.toFinite S
  obtain ⟨L, hL, hLmem⟩ := GlobalTheory.T.finite_automorphism_orbit_mem_finite_extension_padic l ι J (η U) hfin
  exact ⟨⟨L, hL⟩, hLmem⟩

end GlobalTheory.Cong
end
end
end
