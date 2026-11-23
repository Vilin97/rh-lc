module

public import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Formalism.WachLatticeTwists.LatticeDualFibres.StatDualFibreLattice
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.Topology.Algebra.Module.Basic
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Order.CompletePartialOrder
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FactorMemCocyclesPowQuot
import Formalism.WachLatticeTwists.LatticeDualFibres.Statement
import ReciprocityTheory.GaloisValuations.GlobalA
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualLatticeCompactPowSmulNhdsBasisStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCocycleCupNotCoboundaryFiniteLevelStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCompatibleSeqOfFiniteNonempty
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FactorMemCocyclesPowQuot
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteCocyclesQuotientPowSmulModuleStatement
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowMulIntegral

section

@[expose] public section

namespace GlobalTheory.IntegralPowerMultiple

theorem exists_pow_mul_integral {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {ϖ : O} (hϖ : Irreducible ϖ) (c : FractionRing O) :
    ∃ (n : ℕ) (a : O), algebraMap O (FractionRing O) (ϖ ^ n) * c = algebraMap O (FractionRing O) a := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := O) c
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb

  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
  refine ⟨n, ((u⁻¹ : Oˣ) : O) * a, ?_⟩
  have hbK : algebraMap O (FractionRing O) b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have hu' : algebraMap O (FractionRing O) (u : O) * algebraMap O (FractionRing O) ((u⁻¹ : Oˣ) : O) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  rw [hu, map_mul] at hbK
  rw [hu, map_mul, map_mul]
  rw [mul_div_assoc', div_eq_iff hbK]
  linear_combination (-(algebraMap O (FractionRing O) a * algebraMap O (FractionRing O) (ϖ ^ n))) * hu'

theorem exists_pow_smul_mem : ∀ {O : Type} [inst : CommRing O] [inst_1 : IsDomain O] [IsDiscreteValuationRing O] {V : Type} [inst_3 : AddCommGroup V] [inst_4 : Module O V] [inst_5 : Module (FractionRing O) V] [inst_6 : IsScalarTower O (FractionRing O) V] (T : Submodule O V), Formalism.RepresentationBoundsCohomology.LOC.IsLatticeIn T → ∀ (ϖ : O), Irreducible ϖ → ∀ (v : V), ∃ (m : ℕ), ϖ ^ m • v ∈ T := by
  intro O _ _ _ V _ _ _ _ T hT ϖ hϖ v
  have hv : v ∈ Submodule.span (FractionRing O) (T : Set V) := by rw [hT.2]; exact Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨0, by simpa using hx⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨m₁, h₁⟩ := hx
    obtain ⟨m₂, h₂⟩ := hy
    refine ⟨m₁ + m₂, ?_⟩
    rw [smul_add, pow_add]
    refine T.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]
      exact T.smul_mem _ h₁
    · rw [mul_smul]
      exact T.smul_mem _ h₂
  | smul c x _ hx =>
    obtain ⟨m, hm⟩ := hx

    obtain ⟨n, a, ha⟩ := exists_pow_mul_integral hϖ c
    refine ⟨n + m, ?_⟩
    have key : ϖ ^ (n + m) • (c • x) = a • (ϖ ^ m • x) := by
      rw [← algebraMap_smul (FractionRing O) (ϖ ^ (n + m)) (c • x), smul_smul,
        ← algebraMap_smul (FractionRing O) a, ← algebraMap_smul (FractionRing O) (ϖ ^ m) x, smul_smul,
        ← ha, pow_add, map_mul]
      congr 1
      ring
    rw [key]
    exact T.smul_mem a hm

end GlobalTheory.IntegralPowerMultiple
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousQuotientTorsionBounded

section

@[expose] public section

open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal GlobalTheory.LocDualInt
open Formalism.NG (KO)

namespace GlobalTheory.LatticeQuotBound

theorem exists_pow_smul_mem {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {V : Type} [AddCommGroup V] [Module O V] [Module (FractionRing O) V]
    [IsScalarTower O (FractionRing O) V] (T : Submodule O V) (hT : IsLatticeIn T)
    (ϖ : O) (hϖ : Irreducible ϖ) (v : V) : ∃ m : ℕ, ϖ ^ m • v ∈ T := by
  first
  | exact @_root_.GlobalTheory.IntegralPowerMultiple.exists_pow_smul_mem
  | exact _root_.GlobalTheory.IntegralPowerMultiple.exists_pow_smul_mem
  | (apply _root_.GlobalTheory.IntegralPowerMultiple.exists_pow_smul_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralPowerMultiple.exists_pow_smul_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralPowerMultiple.exists_pow_smul_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralPowerMultiple.exists_pow_smul_mem ..)

theorem pow_smul_eq_zero_of_compact : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {V : Type} [AddCommGroup V] [Module O V] [Module (FractionRing O) V] [IsScalarTower O (FractionRing O) V] [TopologicalSpace V] [IsTopologicalAddGroup V] {X : Type} [TopologicalSpace X] [CompactSpace X] (T : Submodule O V), IsLatticeIn T → IsOpen (T : Set V) → ∀ ϖ : O, Irreducible ϖ → ∀ c : X → V ⧸ T, Continuous c → ∃ r : ℕ, ∀ x, ϖ ^ r • c x = 0 := by
  intro O _ _ _ V _ _ _ _ _ _ X _ _ T hT hTo ϖ hϖ c hc
  have hopen : ∀ m : ℕ, IsOpen {q : V ⧸ T | ϖ ^ m • q = 0} := by
    intro m
    have h : IsOpen ((Submodule.Quotient.mk : V → V ⧸ T) ⁻¹' {q : V ⧸ T | ϖ ^ m • q = 0}) := by
      rw [isOpen_iff_forall_mem_open]
      intro v hv
      refine ⟨(fun t => v + t) '' (T : Set V), ?_, isOpenMap_add_left v _ hTo,
        ⟨0, T.zero_mem, add_zero v⟩⟩
      rintro _ ⟨t, ht, rfl⟩
      simp only [Set.mem_preimage, Set.mem_setOf_eq] at hv ⊢
      rw [Submodule.Quotient.mk_add, smul_add, hv, zero_add,
        (Submodule.Quotient.mk_eq_zero T).2 ht, smul_zero]
    exact isOpen_coinduced.mpr h
  have hcover : ∀ x, ∃ m : ℕ, x ∈ c ⁻¹' {q : V ⧸ T | ϖ ^ m • q = 0} := by
    intro x
    obtain ⟨v, hv⟩ := Submodule.Quotient.mk_surjective T (c x)
    obtain ⟨m, hm⟩ := exists_pow_smul_mem T hT ϖ hϖ v
    refine ⟨m, ?_⟩
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    rw [← hv, ← Submodule.Quotient.mk_smul, (Submodule.Quotient.mk_eq_zero T).2 hm]
  have hmono : Monotone (fun m : ℕ => c ⁻¹' {q : V ⧸ T | ϖ ^ m • q = 0}) := by
    intro a b hab x hx
    simp only [Set.mem_preimage, Set.mem_setOf_eq] at hx ⊢
    rw [← Nat.add_sub_cancel' hab, pow_add, mul_comm, mul_smul, hx, smul_zero]
  obtain ⟨m, hm⟩ := isCompact_univ.elim_directed_cover _ (fun m => (hopen m).preimage hc)
    (fun x _ => Set.mem_iUnion.2 (hcover x)) hmono.directed_le
  exact ⟨m, fun x => hm (Set.mem_univ x)⟩

end GlobalTheory.LatticeQuotBound
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousQuotientTorsionBoundedStatement

section

@[expose] public section

open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal GlobalTheory.LocDualInt
open Formalism.NG (KO)

theorem _root_.GlobalTheory.T.continuous_quotient_torsion_bounded : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {V : Type} [AddCommGroup V] [Module O V] [Module (FractionRing O) V] [IsScalarTower O (FractionRing O) V] [TopologicalSpace V] [IsTopologicalAddGroup V] {X : Type} [TopologicalSpace X] [CompactSpace X] (T : Submodule O V), IsLatticeIn T → IsOpen (T : Set V) → ∀ ϖ : O, Irreducible ϖ → ∀ c : X → V ⧸ T, Continuous c → ∃ r : ℕ, ∀ x, ϖ ^ r • c x = 0 := by
  first | exact @GlobalTheory.LatticeQuotBound.pow_smul_eq_zero_of_compact | exact GlobalTheory.LatticeQuotBound.pow_smul_eq_zero_of_compact | (intros; apply GlobalTheory.LatticeQuotBound.pow_smul_eq_zero_of_compact <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsContinuousCocycleLiftOfCompatible

section

@[expose] public section

open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal GlobalTheory.LocDualInt
open Formalism.NG (KO)

noncomputable section

namespace GlobalTheory.CocycleLimit

theorem exists_continuous_cocycle_lift_of_compatible : ∀ {O : Type} [CommRing O] {G : Type} [Group G] [TopologicalSpace G] {M : Type} [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul O M] [T2Space M] [CompactSpace M] (ρ : Representation O G M) (a : O) (r : ℕ), (∀ n : ℕ, IsOpen ((powSub (M := M) a n : Submodule O M) : Set M)) → (∀ U ∈ nhds (0 : M), ∃ n : ℕ, ((powSub (M := M) a n : Submodule O M) : Set M) ⊆ U) → ∀ w : ℕ → G → M, (∀ k, (fun g => (Submodule.Quotient.mk (w k g) : M ⧸ powSub (M := M) a (r + k))) ∈ Z1 (quotRep ρ a (r + k))) → (∀ k g, w (k + 1) g - w k g ∈ powSub (M := M) a (r + k)) → ∃ e ∈ Z1 ρ, ∀ k g, e g - w k g ∈ powSub (M := M) a (r + k) := by
  intro O _ G _ _ M _ _ _ _ _ _ _ ρ a r hopen hbasis w hw hstep
  set N : ℕ → Submodule O M := fun n => powSub (M := M) a n with hN

  have hclosedN : ∀ n, IsClosed ((N n : Submodule O M) : Set M) := fun n =>
    AddSubgroup.isClosed_of_isOpen (N n).toAddSubgroup (hopen n)

  have hex : ∀ g, ∃ x, ∀ k, x - w k g ∈ N (r + k) := by
    intro g
    let C : ℕ → Set M := fun k => {x | x - w k g ∈ N (r + k)}
    have hsub : ∀ k, C (k + 1) ⊆ C k := by
      intro k x hx
      have h1 : x - w (k + 1) g ∈ N (r + k) :=
        powSub_anti a (by omega : r + k ≤ r + (k + 1)) hx
      have h2 := hstep k g
      show x - w k g ∈ N (r + k)
      have : x - w k g = (x - w (k + 1) g) + (w (k + 1) g - w k g) := by abel
      rw [this]; exact (N (r + k)).add_mem h1 h2
    have hne : ∀ k, (C k).Nonempty := fun k => ⟨w k g, by simp [C, (N (r + k)).zero_mem]⟩
    have hcl : ∀ k, IsClosed (C k) := fun k =>
      (hclosedN (r + k)).preimage (continuous_id.sub continuous_const)
    obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C hsub hne
      (hcl 0).isCompact hcl
    exact ⟨x, fun k => Set.mem_iInter.1 hx k⟩
  choose e he using hex

  have hzero : ∀ x : M, (∀ k, x ∈ N (r + k)) → x = 0 := by
    intro x hx
    by_contra hne
    obtain ⟨n, hn⟩ := hbasis ({x}ᶜ) (isOpen_compl_singleton.mem_nhds (Ne.symm hne))
    have : x ∈ N (r + n) := hx n
    exact hn (powSub_anti a (by omega : n ≤ r + n) this) rfl

  have hcoc : ∀ k g h, w k (g * h) - (w k g + ρ g (w k h)) ∈ N (r + k) := by
    intro k g h
    have := (hw k).2 g h
    simp only [quotRep_mk] at this
    rw [← Submodule.Quotient.mk_add] at this
    exact (Submodule.Quotient.eq _).1 this
  refine ⟨e, ⟨?_, ?_⟩, fun k g => he g k⟩
  ·
    rw [continuous_iff_continuousAt]
    intro g0 U hU
    have hV : {y : M | y + e g0 ∈ U} ∈ nhds (0 : M) :=
      (continuous_id.add continuous_const).continuousAt.preimage_mem_nhds (by simpa using hU)
    obtain ⟨n, hn⟩ := hbasis _ hV
    let q : G → M ⧸ powSub (M := M) a (r + n) := fun g => Submodule.Quotient.mk (w n g)
    have hq : Continuous q := (hw n).1
    have hsing : IsOpen ({q g0} : Set (M ⧸ powSub (M := M) a (r + n))) := by
      rw [← (Submodule.isOpenQuotientMap_mkQ (powSub (M := M) a (r + n))).isQuotientMap.isOpen_preimage]
      have : (Submodule.mkQ (powSub (M := M) a (r + n))) ⁻¹' {q g0} =
          (fun y => y - w n g0) ⁻¹' ((N (r + n) : Submodule O M) : Set M) := by
        ext y
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Submodule.mkQ_apply, q,
          SetLike.mem_coe, N]
        exact Submodule.Quotient.eq _
      rw [this]
      exact (hopen (r + n)).preimage (continuous_id.sub continuous_const)
    have hS : q ⁻¹' {q g0} ∈ nhds g0 := (hsing.preimage hq).mem_nhds rfl
    show e ⁻¹' U ∈ nhds g0
    refine Filter.mem_of_superset hS ?_
    intro g hg
    have hg' : w n g - w n g0 ∈ N (r + n) := (Submodule.Quotient.eq _).1 hg
    have hmem : e g - e g0 ∈ N (r + n) := by
      have : e g - e g0 = (e g - w n g) + (w n g - w n g0) - (e g0 - w n g0) := by abel
      rw [this]
      exact (N (r + n)).sub_mem ((N (r + n)).add_mem (he g n) hg') (he g0 n)
    have := hn (powSub_anti a (by omega : n ≤ r + n) hmem)
    simpa using this
  ·
    intro g h
    rw [← sub_eq_zero]
    apply hzero
    intro k
    have : e (g * h) - (e g + ρ g (e h)) =
        (e (g * h) - w k (g * h)) - (e g - w k g) - ρ g (e h - w k h) +
          (w k (g * h) - (w k g + ρ g (w k h))) := by
      rw [map_sub]; abel
    rw [this]
    refine (N (r + k)).add_mem ((N (r + k)).sub_mem ((N (r + k)).sub_mem (he _ k) (he _ k))
      (powSub_stable ρ a _ g _ (he h k))) (hcoc k g h)

end GlobalTheory.CocycleLimit
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsContinuousCocycleLiftOfCompatibleStatement

section

@[expose] public section

open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal GlobalTheory.LocDualInt
open Formalism.NG (KO)

theorem _root_.GlobalTheory.T.exists_continuous_cocycle_lift_of_compatible' : ∀ {O : Type} [CommRing O] {G : Type} [Group G] [TopologicalSpace G] {M : Type} [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul O M] [T2Space M] [CompactSpace M] (ρ : Representation O G M) (a : O) (r : ℕ), (∀ n : ℕ, IsOpen ((powSub (M := M) a n : Submodule O M) : Set M)) → (∀ U ∈ nhds (0 : M), ∃ n : ℕ, ((powSub (M := M) a n : Submodule O M) : Set M) ⊆ U) → ∀ w : ℕ → G → M, (∀ k, (fun g => (Submodule.Quotient.mk (w k g) : M ⧸ powSub (M := M) a (r + k))) ∈ Z1 (quotRep ρ a (r + k))) → (∀ k g, w (k + 1) g - w k g ∈ powSub (M := M) a (r + k)) → ∃ e ∈ Z1 ρ, ∀ k g, e g - w k g ∈ powSub (M := M) a (r + k) := by
  first | exact @GlobalTheory.CocycleLimit.exists_continuous_cocycle_lift_of_compatible | exact GlobalTheory.CocycleLimit.exists_continuous_cocycle_lift_of_compatible | (intros; apply GlobalTheory.CocycleLimit.exists_continuous_cocycle_lift_of_compatible <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralLocalDualityOfLocalTateDuality

section

@[expose] public section

open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal
open Formalism.NG (KO)

noncomputable section

namespace GlobalTheory.LocDualInt

theorem int_iso_of_localTateDuality (hT : Formalism.GaloisCohomology.LocalTateDualityK) : ReciprocityTheory.ChartRestriction.T2.IntIso := by
  intro p _ K O _ _ _ _ _ _ _ VT VT' _ _ _ _ _ _ _ _ _ _ _ _ _ _ G _ _ hK hO hF i D hD hinv x hx
  haveI := hD.t2'
  haveI : IsGalois K (PadicAlgCl p) := inferInstance
  haveI : CompactSpace (Formalism.GaloisCohomology.GK p K) := inferInstance
  haveI : CompactSpace G := i.symm.toHomeomorph.compactSpace
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  induction x using Submodule.Quotient.induction_on with
  | H c => ?_
  by_contra hx0
  have hcB : (c : G → VT ⧸ D.T) ∉ B1 D.ρA := fun h => hx0 ((Submodule.Quotient.mk_eq_zero _).2 h)
  obtain ⟨r, hr⟩ := GlobalTheory.T.continuous_quotient_torsion_bounded D.T hD.lat hD.openT ϖ hϖ (c : G → VT ⧸ D.T) c.2.1
  have hcyc : ∀ (g : G) (n : ℕ) (ζ : PadicAlgCl p), ζ ^ (p ^ n) = 1 → ∃ a : ℕ, (i g) ζ = ζ ^ a ∧
      ((D.ε g : Oˣ) : O) - (a : O) ∈ Ideal.span {(p : O) ^ n} := by
    intro g n ζ hζ
    obtain ⟨a, h1, h2⟩ := hD.cyc (i g) n ζ hζ
    have e : (ReciprocityTheory.ChartRestriction.T2.carry i D.ε) (i g) = D.ε g := by
      change D.ε (i.symm (i g)) = D.ε g
      exact congrArg D.ε (i.symm_apply_apply g)
    rw [e] at h2
    exact ⟨a, h1, h2⟩
  obtain ⟨hcpt, hopen, hbasis⟩ := GlobalTheory.T.dualLattice_compact_powSmul_nhds_basis D hO.compact hF.emb hD.lat hD.perf hD.t2' ϖ hϖ
  haveI := hcpt
  let X : ℕ → Type := fun k => G → ↥D.T' ⧸ powSub (M := ↥D.T') ϖ (r + k)
  let Y : ∀ k, Set (X k) := fun k => {z | z ∈ Z1 (quotRep D.ρTl' ϖ (r + k)) ∧
    cupMod D (c : G → VT ⧸ D.T) ϖ (r + k) z ∉ B2 (twist D.ε (KO O))}
  have hle : ∀ k, r + k ≤ r + (k + 1) := fun k => by omega
  let f : ∀ k, X (k + 1) → X k := fun k z g =>
    Submodule.factor (powSub_anti (M := ↥D.T') ϖ (hle k)) (z g)
  have hfin : ∀ k, (Y k).Finite := fun k =>
    (GlobalTheory.T.finite_cocycles_quotient_pow_smul_of_isOpen hT hK hO.p_mem i D.ρTl' (sub_contAction D.contT' _ D.stT') ϖ hϖ hopen (r + k)).subset
      (fun z hz => hz.1)
  have hne : ∀ k, (Y k).Nonempty := fun k => by
    obtain ⟨z, hz, hz'⟩ := GlobalTheory.T.exists_cocycle_cup_not_coboundary_finiteLevel hT hK hO.ring hO.compact hO.t2 hO.adic hO.p_mem hO.p_ne hF.emb i D
      hcyc hD.lat hD.perf hD.contT hD.openT hD.t2 hD.t2' hD.cs hD.cs' ϖ hϖ c.1 c.2 hcB r hr (r + k)
      (by omega)
    exact ⟨z, hz, hz'⟩
  have hmap : ∀ k, ∀ z ∈ Y (k + 1), f k z ∈ Y k := by
    rintro k z ⟨hz, hnc⟩
    refine ⟨factor_mem_cocycles_pow_quot D.ρTl' ϖ (hle k) hz, ?_⟩
    have e := cupMod_factor D hr (Nat.le_add_right r k) (hle k) z
    show cupMod D (c : G → VT ⧸ D.T) ϖ (r + k)
      (fun g => Submodule.factor (powSub_anti (M := ↥D.T') ϖ (hle k)) (z g)) ∉ _
    rw [e]
    exact hnc
  obtain ⟨s, hs⟩ := GlobalTheory.exists_compatible_seq_of_finite_nonempty X f Y hfin hne hmap
  let w : ℕ → G → ↥D.T' := fun k g => qlift (s k g)
  have hwZ : ∀ k, (fun g => (Submodule.Quotient.mk (w k g) :
      ↥D.T' ⧸ powSub (M := ↥D.T') ϖ (r + k))) ∈ Z1 (quotRep D.ρTl' ϖ (r + k)) := by
    intro k
    have e : (fun g => (Submodule.Quotient.mk (w k g) : ↥D.T' ⧸ powSub (M := ↥D.T') ϖ (r + k))) =
        s k := funext fun g => mk_qlift _
    rw [e]
    exact (hs k).1.1
  have hstep : ∀ k g, w (k + 1) g - w k g ∈ powSub (M := ↥D.T') ϖ (r + k) := by
    intro k g
    apply (Submodule.Quotient.eq _).1
    have e1 : (Submodule.Quotient.mk (w (k + 1) g) : ↥D.T' ⧸ powSub (M := ↥D.T') ϖ (r + k)) =
        f k (s (k + 1)) g := by
      show _ = Submodule.factor (powSub_anti (M := ↥D.T') ϖ (hle k)) (s (k + 1) g)
      conv_rhs => rw [← mk_qlift (s (k + 1) g)]
      rfl
    rw [e1, (hs k).2]
    exact (mk_qlift (s k g)).symm
  obtain ⟨e, he, hew⟩ := GlobalTheory.T.exists_continuous_cocycle_lift_of_compatible' D.ρTl' ϖ r hopen hbasis w hwZ hstep
  have h1 := hx (Submodule.Quotient.mk ⟨e, he⟩)
  have h2 : ((cupCocycleZ1Z1 D.ρA D.ρTl' (twist D.ε (KO O)) (pairKO D.bT D.T) (pairKO_cont D.bT D.contbT D.T) D.pairKO_equiv (sub_contAction D.contT' _ D.stT') c ⟨e, he⟩) : G × G → KO O) ∈ B2 (twist D.ε (KO O)) := by
    have h3 : D.inv (Submodule.Quotient.mk (cupCocycleZ1Z1 D.ρA D.ρTl' (twist D.ε (KO O)) (pairKO D.bT D.T) (pairKO_cont D.bT D.contbT D.T) D.pairKO_equiv (sub_contAction D.contT' _ D.stT') c ⟨e, he⟩)) = D.inv 0 := by
      rw [map_zero]
      exact h1
    have h6 := (Submodule.Quotient.mk_eq_zero _).1 (hinv h3)
    exact h6
  apply (hs 0).1.2
  have h4 : cupMod D (c : G → VT ⧸ D.T) ϖ (r + 0) (s 0) = ((cupCocycleZ1Z1 D.ρA D.ρTl' (twist D.ε (KO O)) (pairKO D.bT D.T) (pairKO_cont D.bT D.contbT D.T) D.pairKO_equiv (sub_contAction D.contT' _ D.stT') c ⟨e, he⟩) : G × G → KO O) := by
    funext q
    refine pairKO_eq_of_sub_mem D (hr q.1) ?_
    rw [← map_sub]
    refine powSub_stable _ ϖ r q.1 _ ?_
    have h5 := hew 0 q.2
    rw [← neg_sub]
    exact Submodule.neg_mem _ h5
  rw [h4]
  exact h2

end GlobalTheory.LocDualInt
end
end
end
