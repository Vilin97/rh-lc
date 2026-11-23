module

public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EqOfPowEqOneOfNormSubLt
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoboundaryDeRhamOfCoboundarySemistableStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteDimensionalDstOfIsSstStatement
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankDcrisPhiFixedAddFinrankMonLe
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmSt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonVEqZeroIffExistsCrisInclStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistableCocycleOfFrobeniusMonodromyPair
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankAddLeFinrankRangeAddOfComapLe

section

@[expose] public section

open TensorProduct Module

namespace GlobalTheory

theorem finrank_add_le_finrank_range_add_of_comap_le : ∀ (k : Type) [Field k] (E A M : Type) [AddCommGroup E] [Module k E] [AddCommGroup A] [Module k A] [AddCommGroup M] [Module k M] (π : E →ₗ[k] A) (ν : E →ₗ[k] M) (Z : Submodule k A) (R U : Submodule k M) [FiniteDimensional k ↥(LinearMap.range π)] [FiniteDimensional k ↥U], Z ≤ LinearMap.range π → R ≤ U → U ≤ LinearMap.range ν → (∀ e, π e ∈ Z → ν e ∈ R) → finrank k ↥Z + finrank k ↥U ≤ finrank k ↥(LinearMap.range π) + finrank k ↥R := by
  intro k _ E A M _ _ _ _ _ _ π ν Z R U _ _ hZ hRU hU hmap
  set Q := LinearMap.range π with hQ
  set Z' : Submodule k Q := Z.comap Q.subtype
  set R' : Submodule k U := R.comap U.subtype
  have hZ' : finrank k Z' = finrank k Z := (Submodule.comapSubtypeEquivOfLe hZ).finrank_eq
  have hR' : finrank k R' = finrank k R := (Submodule.comapSubtypeEquivOfLe hRU).finrank_eq
  set K : Submodule k E := U.comap ν
  let g : K →ₗ[k] Q ⧸ Z' := Z'.mkQ ∘ₗ π.rangeRestrict ∘ₗ K.subtype
  let f : K →ₗ[k] U ⧸ R' := R'.mkQ ∘ₗ ((ν ∘ₗ K.subtype).codRestrict U (fun x => x.2))
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨u, rfl⟩ := R'.mkQ_surjective y
    obtain ⟨e, he⟩ := hU u.2
    have heU : ν e ∈ U := he ▸ u.2
    refine ⟨⟨e, heU⟩, ?_⟩
    have hu : ((ν ∘ₗ K.subtype).codRestrict U (fun x => x.2)) ⟨e, heU⟩ = u := Subtype.ext he
    exact congrArg R'.mkQ hu
  have hker : LinearMap.ker g ≤ LinearMap.ker f := by
    intro x hx
    have h0 : Submodule.Quotient.mk (p := Z') (π.rangeRestrict (x : E)) = 0 := LinearMap.mem_ker.mp hx
    have hx' : π (x : E) ∈ Z := (Submodule.Quotient.mk_eq_zero (p := Z')).mp h0
    have hy : ν (x : E) ∈ R := hmap _ hx'
    rw [LinearMap.mem_ker]
    exact (Submodule.Quotient.mk_eq_zero (p := R')
      (x := ((ν ∘ₗ K.subtype).codRestrict U (fun x => x.2)) x)).mpr hy
  let gq := (LinearMap.ker g).liftQ g le_rfl
  let fq := (LinearMap.ker g).liftQ f hker
  have hgq : Function.Injective gq := by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ le_rfl
  have hfq : Function.Surjective fq := by
    intro y
    obtain ⟨x, rfl⟩ := hf y
    exact ⟨Submodule.Quotient.mk x, rfl⟩
  have : Module.Finite k (K ⧸ LinearMap.ker g) := Module.Finite.of_injective gq hgq
  have key : finrank k (U ⧸ R') ≤ finrank k (Q ⧸ Z') :=
    (LinearMap.finrank_le_finrank_of_surjective hfq).trans
      (LinearMap.finrank_le_finrank_of_injective hgq)
  have h1 := Submodule.finrank_quotient_add_finrank R'
  have h2 := Submodule.finrank_quotient_add_finrank Z'
  omega

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankAddLeFinrankRangeAddOfComapLeStatement

section

@[expose] public section

open TensorProduct Module

theorem _root_.GlobalTheory.T.finrank_add_finrank_le_finrank_range_add_finrank : ∀ (k : Type) [Field k] (E A M : Type) [AddCommGroup E] [Module k E] [AddCommGroup A] [Module k A] [AddCommGroup M] [Module k M] (π : E →ₗ[k] A) (ν : E →ₗ[k] M) (Z : Submodule k A) (R U : Submodule k M) [FiniteDimensional k ↥(LinearMap.range π)] [FiniteDimensional k ↥U], Z ≤ LinearMap.range π → R ≤ U → U ≤ LinearMap.range ν → (∀ e, π e ∈ Z → ν e ∈ R) → finrank k ↥Z + finrank k ↥U ≤ finrank k ↥(LinearMap.range π) + finrank k ↥R := by
  first | exact @GlobalTheory.finrank_add_le_finrank_range_add_of_comap_le | exact GlobalTheory.finrank_add_le_finrank_range_add_of_comap_le | (intros; apply GlobalTheory.finrank_add_le_finrank_range_add_of_comap_le <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankDcrisPhiFixedAddFinrankMonLeStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.finrank_dcris_phi_fixed_add_finrank_mon_le_alt : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (V' : Type) [AddCommGroup V'] [Module ℚ_[l] V'] [FiniteDimensional ℚ_[l] V'] (ρ : Representation ℚ_[l] ↥(GK K) V) (ρ' : Representation ℚ_[l] ↥(GK K) V') (m : V →ₗ[ℚ_[l]] V' →ₗ[ℚ_[l]] ℚ_[l]), IsDual1 (P.PD K) ρ ρ' m → IsSst P ρ → finrank ℚ_[l] ↥(Dcris (P.PD K) ρ' ⊓ LinearMap.ker (φVB (P.PD K) (LL := ℚ_[l]) (V := V') - LinearMap.id)) + finrank ℚ_[l] ↥((Dst P ρ).map (monV P ℚ_[l] V)) ≤ finrank ℚ_[l] ↥(Dst P ρ ⊓ ((Dst P ρ).map (monV P ℚ_[l] V)).comap ((l : ℚ_[l]) • phiV P ℚ_[l] V - LinearMap.id)) := by
  first | exact @GlobalTheory.finrank_dcris_phi_fixed_add_finrank_mon_le | exact GlobalTheory.finrank_dcris_phi_fixed_add_finrank_mon_le | (intros; apply GlobalTheory.finrank_dcris_phi_fixed_add_finrank_mon_le <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistableCocycleOfFrobeniusMonodromyPairStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.semistable_cocycle_of_frobenius_monodromy_pair : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [ContinuousAdd V] [ContinuousConstSMul ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), (∀ v : V, Continuous fun g => ρ g v) → ∀ x ∈ Dst P ρ, ∀ y ∈ Dst P ρ, (l : ℚ_[l]) • phiV P ℚ_[l] V x - x = monV P ℚ_[l] V y → ∃ (z : V ⊗[ℚ_[l]] Bst P) (c : ↥(GK K) → V), c ∈ continuousCocycles ρ ∧ (∀ g, c g ⊗ₜ[ℚ_[l]] (1 : Bst P) = stRep P ρ g z - z) ∧ monV P ℚ_[l] V z = x := by
  first | exact @GlobalTheory.semistable_class_of_pair | exact GlobalTheory.semistable_class_of_pair | (intros; apply GlobalTheory.semistable_class_of_pair <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistableCocyclesBetweenBlochKatoAndContinuous

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.PMon

noncomputable def stPairs {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K : FinExt l} {V : Type} [AddCommGroup V]
    [Module ℚ_[l] V] [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul ℚ_[l] V]
    (ρ : Representation ℚ_[l] ↥(GK K) V) : Submodule ℚ_[l] ((↥(GK K) → V) × (V ⊗[ℚ_[l]] Bst P)) where
  carrier := {p | p.1 ∈ continuousCocycles ρ ∧ ∀ g, p.1 g ⊗ₜ[ℚ_[l]] (1 : Bst P) = stRep P ρ g p.2 - p.2}
  zero_mem' := ⟨(continuousCocycles ρ).zero_mem, fun g => by simp⟩
  add_mem' := by
    rintro a b ⟨ha, hx⟩ ⟨hb, hy⟩
    refine ⟨(continuousCocycles ρ).add_mem ha hb, fun g => ?_⟩
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_tmul, hx, hy, map_add (f := _)]
    abel
  smul_mem' := by
    rintro c a ⟨ha, hx⟩
    refine ⟨(continuousCocycles ρ).smul_mem c ha, fun g => ?_⟩
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, map_smul, ← smul_sub, ← hx]
    rfl

theorem exists_stCocycles_lower : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [ContinuousAdd V] [ContinuousConstSMul ℚ_[l] V] (V' : Type) [AddCommGroup V'] [Module ℚ_[l] V'] [FiniteDimensional ℚ_[l] V'] (ρ : Representation ℚ_[l] ↥(GK K) V) (ρ' : Representation ℚ_[l] ↥(GK K) V') (m : V →ₗ[ℚ_[l]] V' →ₗ[ℚ_[l]] ℚ_[l]), (∀ v : V, Continuous fun g => ρ g v) → IsDual1 (P.PD K) ρ ρ' m → IsSst P ρ → Module.Finite ℚ_[l] ↥(continuousCocycles ρ) → ∃ S : Submodule ℚ_[l] (↥(GK K) → V), finiteCocycles (P.PD K) ρ ≤ S ∧ S ≤ continuousCocycles ρ ∧ (∀ c ∈ S, ∃ z : V ⊗[ℚ_[l]] Bst P, ∀ g, c g ⊗ₜ[ℚ_[l]] (1 : Bst P) = stRep P ρ g z - z) ∧ (∀ c ∈ S, ∃ b : V ⊗[ℚ_[l]] P.R.BdR, ∀ g, c g ⊗ₜ[ℚ_[l]] (1 : P.R.BdR) = actVdR (P.PD K) ρ g b - b) ∧ finrank ℚ_[l] ↥(finiteCocycles (P.PD K) ρ) + finrank ℚ_[l] ↥(Dcris (P.PD K) ρ' ⊓ LinearMap.ker (φVB (P.PD K) (LL := ℚ_[l]) (V := V') - LinearMap.id)) ≤ finrank ℚ_[l] ↥S := by
  intro l _ P AI T K V _ _ _ _ _ _ _ V' _ _ _ ρ ρ' m hc hd hs hfin
  let π : ↥(stPairs P ρ) →ₗ[ℚ_[l]] (↥(GK K) → V) := (LinearMap.fst _ _ _).comp (stPairs P ρ).subtype
  let ν : ↥(stPairs P ρ) →ₗ[ℚ_[l]] (V ⊗[ℚ_[l]] Bst P) :=
    (monV P ℚ_[l] V).comp ((LinearMap.snd _ _ _).comp (stPairs P ρ).subtype)
  have hcris : ∀ (c : ↥(GK K) → V) (x : V ⊗[ℚ_[l]] P.R.B),
      (∀ g, c g ⊗ₜ[ℚ_[l]] (1 : P.R.B) = actVB (P.PD K) ρ g x - x) →
      ∀ g, c g ⊗ₜ[ℚ_[l]] (1 : Bst P) = stRep P ρ g (crisIncl P ℚ_[l] V x) - crisIncl P ℚ_[l] V x := by
    intro c x hx g
    rw [stRep_crisIncl, ← map_sub, ← hx, crisIncl_tmul, map_one]
  have h1 : finiteCocycles (P.PD K) ρ ≤ LinearMap.range π := by
    rintro c ⟨hc1, x, hx⟩
    exact ⟨⟨(c, crisIncl P ℚ_[l] V x), hc1, hcris c x hx⟩, rfl⟩
  have h2 : LinearMap.range π ≤ continuousCocycles ρ := by
    rintro _ ⟨e, rfl⟩
    exact e.2.1
  have h3 : ∀ c ∈ LinearMap.range π, ∃ z : V ⊗[ℚ_[l]] Bst P,
      ∀ g, c g ⊗ₜ[ℚ_[l]] (1 : Bst P) = stRep P ρ g z - z := by
    rintro _ ⟨e, rfl⟩
    exact ⟨e.1.2, e.2.2⟩
  refine ⟨LinearMap.range π, h1, h2, h3, fun c hc => ?_, ?_⟩
  · obtain ⟨z, hz⟩ := h3 c hc
    exact GlobalTheory.T.coboundary_deRham_of_coboundary_semistable l P AI T K V ρ c z hz
  have hφ : ∀ y ∈ Dst P ρ, phiV P ℚ_[l] V y ∈ Dst P ρ := fun y hy =>
    (mem_Dst P ρ).mpr fun g => by
      rw [← End.mul_apply, ← phiV_stRep, End.mul_apply, (mem_Dst P ρ).mp hy g]
  have hN : ∀ y ∈ Dst P ρ, monV P ℚ_[l] V y ∈ Dst P ρ := fun y hy =>
    (mem_Dst P ρ).mpr fun g => by
      rw [← End.mul_apply, ← monV_stRep, End.mul_apply, (mem_Dst P ρ).mp hy g]
  haveI := GlobalTheory.T.finiteDimensional_Dst_of_isSst' l P K V ρ hs
  haveI : FiniteDimensional ℚ_[l] ↥(LinearMap.range π) := Submodule.finiteDimensional_of_le h2
  haveI : FiniteDimensional ℚ_[l] ↥(Dst P ρ ⊓ ((Dst P ρ).map (monV P ℚ_[l] V)).comap
      ((l : ℚ_[l]) • phiV P ℚ_[l] V - LinearMap.id)) := Submodule.finiteDimensional_of_le inf_le_left
  have h4 := GlobalTheory.T.finrank_add_finrank_le_finrank_range_add_finrank ℚ_[l] _ _ _ π ν (finiteCocycles (P.PD K) ρ) ((Dst P ρ).map (monV P ℚ_[l] V))
    (Dst P ρ ⊓ ((Dst P ρ).map (monV P ℚ_[l] V)).comap ((l : ℚ_[l]) • phiV P ℚ_[l] V - LinearMap.id)) h1
    (by
      rintro _ ⟨y, hy, rfl⟩
      refine ⟨hN y hy, phiV P ℚ_[l] V y - y, Submodule.sub_mem _ (hφ y hy) hy, ?_⟩
      rw [map_sub, ← End.mul_apply, monV_phiV]
      rfl)
    (by
      rintro x ⟨hx, y, hy, hxy⟩
      obtain ⟨z, c, hc1, hc2, hz⟩ := GlobalTheory.T.semistable_cocycle_of_frobenius_monodromy_pair l P AI T K V ρ hc x hx y hy hxy.symm
      exact ⟨⟨(c, z), hc1, hc2⟩, hz⟩)
    (by
      rintro e ⟨-, x, hx⟩
      refine ⟨e.1.2 - crisIncl P ℚ_[l] V x, (mem_Dst P ρ).mpr fun g => ?_, ?_⟩
      · have := (e.2.2 g).symm.trans (hcris _ x hx g)
        rw [map_sub, sub_eq_sub_iff_sub_eq_sub]
        exact this
      · rw [map_sub, (GlobalTheory.T.monV_eq_zero_iff_mem_range_crisIncl' l P V _).mpr ⟨x, rfl⟩, sub_zero]
        rfl)
  have h5 := GlobalTheory.T.finrank_dcris_phi_fixed_add_finrank_mon_le_alt l P AI T K V V' ρ ρ' m hd hs
  omega

end GlobalTheory.PMon
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistableCocyclesBetweenBlochKatoAndContinuousStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.semistable_cocycles_between_blochKato_and_continuous : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [ContinuousAdd V] [ContinuousConstSMul ℚ_[l] V] (V' : Type) [AddCommGroup V'] [Module ℚ_[l] V'] [FiniteDimensional ℚ_[l] V'] (ρ : Representation ℚ_[l] ↥(GK K) V) (ρ' : Representation ℚ_[l] ↥(GK K) V') (m : V →ₗ[ℚ_[l]] V' →ₗ[ℚ_[l]] ℚ_[l]), (∀ v : V, Continuous fun g => ρ g v) → IsDual1 (P.PD K) ρ ρ' m → IsSst P ρ → Module.Finite ℚ_[l] ↥(continuousCocycles ρ) → ∃ S : Submodule ℚ_[l] (↥(GK K) → V), finiteCocycles (P.PD K) ρ ≤ S ∧ S ≤ continuousCocycles ρ ∧ (∀ c ∈ S, ∃ z : V ⊗[ℚ_[l]] Bst P, ∀ g, c g ⊗ₜ[ℚ_[l]] (1 : Bst P) = stRep P ρ g z - z) ∧ (∀ c ∈ S, ∃ b : V ⊗[ℚ_[l]] P.R.BdR, ∀ g, c g ⊗ₜ[ℚ_[l]] (1 : P.R.BdR) = actVdR (P.PD K) ρ g b - b) ∧ finrank ℚ_[l] ↥(finiteCocycles (P.PD K) ρ) + finrank ℚ_[l] ↥(Dcris (P.PD K) ρ' ⊓ LinearMap.ker (φVB (P.PD K) (LL := ℚ_[l]) (V := V') - LinearMap.id)) ≤ finrank ℚ_[l] ↥S := by
  first | exact @GlobalTheory.PMon.exists_stCocycles_lower | exact GlobalTheory.PMon.exists_stCocycles_lower | (intros; apply GlobalTheory.PMon.exists_stCocycles_lower <;> assumption)
end
end
