module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TateDefs
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
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CardQuotientPowSubmoduleGrowsFinrank
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsInvariantLatticeOpenEmbedding
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteLevelCyclotomicOfOpenEmbedding
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteLevelOfFiniteLevelMod
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LatticeCochainsFinGenOfFinLevel
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LatticeCohomologyFiniteAndGrowthOfFinGen
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.NonemptyCohomologyRestrictScalarsLinearEquiv
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.RankCohomologyRationalEqRankLattice
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CardCoinvariantsModPowEqModPowCoinvariants

section

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

theorem UpperTheory.card_coinvariants_mod_pow_eq_mod_pow_coinvariants :
    ∀ {l : ℕ} [Fact l.Prime] {G X : Type} [Group G] [AddCommGroup X] [Module ℤ_[l] X] (χ : G →* ℤ_[l]ˣ) (ρ : Representation ℤ_[l] G X) (m : ℕ), Nat.card ((X ⧸ lSub l X m) ⧸ coSub χ (redRep ρ m)) = Nat.card ((X ⧸ coSub χ ρ) ⧸ lSub l (X ⧸ coSub χ ρ) m) := by
  intro l _ G X _ _ _ χ ρ m
  have hq : ∀ g x, UpperTheory.V.Loc.redRep ρ m g ((lSub l X m).mkQ x) = (lSub l X m).mkQ (ρ g x) :=
    fun g x => rfl
  have hC : coSub χ (UpperTheory.V.Loc.redRep ρ m) = (coSub χ ρ).map (lSub l X m).mkQ := by
    unfold coSub
    rw [Submodule.map_span]
    congr 1
    ext y
    constructor
    · rintro ⟨g, x, rfl⟩
      obtain ⟨x, rfl⟩ := (lSub l X m).mkQ_surjective x
      exact ⟨ρ g x - (χ g : ℤ_[l]) • x, ⟨g, x, rfl⟩, by rw [map_sub, map_smul, hq]⟩
    · rintro ⟨_, ⟨g, x, rfl⟩, rfl⟩
      exact ⟨g, (lSub l X m).mkQ x, by rw [map_sub, map_smul, hq]⟩
  have hL : lSub l (X ⧸ coSub χ ρ) m = (lSub l X m).map (coSub χ ρ).mkQ := by
    ext y
    rw [mem_lSub, Submodule.mem_map]
    constructor
    · rintro ⟨z, rfl⟩
      obtain ⟨z, rfl⟩ := (coSub χ ρ).mkQ_surjective z
      exact ⟨(l : ℤ_[l]) ^ m • z, mem_lSub.2 ⟨z, rfl⟩, by simp⟩
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨z, rfl⟩ := mem_lSub.1 hx
      exact ⟨(coSub χ ρ).mkQ z, by simp⟩
  rw [hC, hL]
  exact Nat.card_congr ((Submodule.quotientQuotientEquivQuotientSup _ _).toEquiv.trans
    ((Submodule.quotEquivOfEq _ _ (sup_comm _ _)).toEquiv.trans
      (Submodule.quotientQuotientEquivQuotientSup _ _).symm.toEquiv))
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FinrankCoinvariantsEqFinrankLatticeCoinvariants

section

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

theorem UpperTheory.finrank_coinvariants_eq_finrank_lattice_coinvariants :
    ∀ {l : ℕ} [Fact l.Prime] {G T V : Type} [Group G] [AddCommGroup T] [Module ℤ_[l] T] [AddCommGroup V] [Module ℚ_[l] V] [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V] (χ : G →* ℤ_[l]ˣ) (ρ : Representation ℚ_[l] G V) (ρT : Representation ℤ_[l] G T) (j : T →ₗ[ℤ_[l]] V), Function.Injective j → (∀ g x, j (ρT g x) = ρ g (j x)) → (∀ y : V, ∃ m : ℕ, (l : ℤ_[l]) ^ m • y ∈ LinearMap.range j) → finrank ℚ_[l] (V ⧸ coSub ((Units.map (algebraMap ℤ_[l] ℚ_[l] : ℤ_[l] →* ℚ_[l])).comp χ) ρ) = finrank ℤ_[l] (T ⧸ coSub χ ρT) := by
  intro l _ G T V _ _ _ _ _ _ _ χ ρ ρT j hj hρ hs
  set N := coSub ((Units.map (algebraMap ℤ_[l] ℚ_[l] : ℤ_[l] →* ℚ_[l])).comp χ) ρ with hN
  have hl : ∀ m : ℕ, (l : ℤ_[l]) ^ m ∈ nonZeroDivisors ℤ_[l] := fun m =>
    mem_nonZeroDivisors_of_ne_zero (pow_ne_zero _ (by exact_mod_cast (Fact.out : l.Prime).ne_zero))
  have hgen : ∀ g x, j (ρT g x - ((χ g : ℤ_[l]ˣ) : ℤ_[l]) • x) =
      ρ g (j x) - ((((Units.map (algebraMap ℤ_[l] ℚ_[l] : ℤ_[l] →* ℚ_[l])).comp χ) g : ℚ_[l]ˣ) : ℚ_[l]) • j x := by
    intro g x
    rw [map_sub, hρ, map_smul, ← algebraMap_smul ℚ_[l] ((χ g : ℤ_[l]ˣ) : ℤ_[l]) (j x)]
    rfl
  have hρs : ∀ g (c : ℤ_[l]) (v : V), ρ g (c • v) = c • ρ g v := fun g c v => by
    rw [← algebraMap_smul ℚ_[l] c v, map_smul, algebraMap_smul]
  let q : V →ₗ[ℤ_[l]] (V ⧸ N) := N.mkQ.restrictScalars ℤ_[l]
  have hle : coSub χ ρT ≤ LinearMap.ker (q ∘ₗ j) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, x, rfl⟩
    change N.mkQ (j _) = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hgen]
    exact Submodule.subset_span ⟨g, j x, rfl⟩
  let f : (T ⧸ coSub χ ρT) →ₗ[ℤ_[l]] (V ⧸ N) := (coSub χ ρT).liftQ (q ∘ₗ j) hle
  have key : ∀ v ∈ N, ∃ c ∈ nonZeroDivisors ℤ_[l], c • v ∈ (coSub χ ρT).map j := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨g, x, rfl⟩ := hy
      obtain ⟨m, t, ht⟩ := hs x
      refine ⟨_, hl m, ρT g t - ((χ g : ℤ_[l]ˣ) : ℤ_[l]) • t, Submodule.subset_span ⟨g, t, rfl⟩, ?_⟩
      rw [hgen, ht, hρs, smul_sub, smul_comm]
    | zero => exact ⟨1, one_mem _, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, hc, hx⟩ := hx
      obtain ⟨d, hd, hy⟩ := hy
      refine ⟨c * d, mul_mem hc hd, ?_⟩
      rw [smul_add]
      refine add_mem ?_ ?_
      · rw [mul_comm, mul_smul]; exact Submodule.smul_mem _ _ hx
      · rw [mul_smul]; exact Submodule.smul_mem _ _ hy
    | smul a x _ hx =>
      obtain ⟨c, hc, hx⟩ := hx
      obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj (nonZeroDivisors ℤ_[l]) a
      refine ⟨c * s, mul_mem hc s.2, ?_⟩
      have : (s : ℤ_[l]) • a • x = r • x := by
        rw [← algebraMap_smul ℚ_[l] (s : ℤ_[l]), smul_smul, mul_comm, hrs, algebraMap_smul]
      rw [mul_smul, this, smul_comm]
      exact Submodule.smul_mem _ _ hx
  haveI : IsLocalizedModule (nonZeroDivisors ℤ_[l]) f := by
    refine ⟨(isLocalizedModule_id (nonZeroDivisors ℤ_[l]) (V ⧸ N) ℚ_[l]).map_units, ?_, ?_⟩
    · intro y
      obtain ⟨v, rfl⟩ := N.mkQ_surjective y
      obtain ⟨m, t, ht⟩ := hs v
      refine ⟨⟨Submodule.Quotient.mk t, ⟨_, hl m⟩⟩, ?_⟩
      change (l : ℤ_[l]) ^ m • q v = q (j t)
      rw [ht, map_smul]
    · intro x y h
      obtain ⟨x, rfl⟩ := (coSub χ ρT).mkQ_surjective x
      obtain ⟨y, rfl⟩ := (coSub χ ρT).mkQ_surjective y
      have h' : j x - j y ∈ N := (Submodule.Quotient.eq N).1 h
      obtain ⟨c, hc, t, ht, e⟩ := key _ h'
      rw [← map_sub, ← map_smul] at e
      obtain rfl := hj e
      refine ⟨⟨c, hc⟩, ?_⟩
      change c • (coSub χ ρT).mkQ x = c • (coSub χ ρT).mkQ y
      rw [← map_smul, ← map_smul]
      refine (Submodule.Quotient.eq _).2 ?_
      rw [← smul_sub]; exact ht
  rw [IsLocalization.finrank_eq ℚ_[l] (nonZeroDivisors ℤ_[l]) le_rfl,
    IsLocalizedModule.finrank_eq (nonZeroDivisors ℤ_[l]) f le_rfl]
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TateRat

section

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

private theorem grows_le {l : ℕ} (hl : 1 < l) {a : ℕ → ℕ} {s t : ℕ} (h : Grows l a s) (h' : Grows l a t) :
    s ≤ t := by
  obtain ⟨_, h⟩ := h
  obtain ⟨C, h'⟩ := h'
  have := (Nat.pow_le_pow_iff_right hl).1 ((h (C + 1) C.succ_pos).1.trans (h' (C + 1) C.succ_pos).2)
  by_contra hc
  have : (C + 1) * (t + 1) ≤ (C + 1) * s := Nat.mul_le_mul_left _ (by omega)
  nlinarith

private theorem grows_unique {l : ℕ} (hl : 1 < l) {a b : ℕ → ℕ} {s t : ℕ} (h : Grows l a s) (h' : Grows l b t)
    (e : ∀ m, a m = b m) : s = t := by
  obtain rfl : a = b := funext e
  exact le_antisymm (grows_le hl h h') (grows_le hl h' h)

private theorem grows_mul {l : ℕ} {a b : ℕ → ℕ} {s t : ℕ} (h : Grows l a s) (h' : Grows l b t) :
    Grows l (fun m => a m * b m) (s + t) := by
  obtain ⟨C, h⟩ := h
  obtain ⟨D, h'⟩ := h'
  refine ⟨C + D, fun m hm => ⟨?_, ?_⟩⟩
  · rw [mul_add, pow_add]
    exact Nat.mul_le_mul (h m hm).1 (h' m hm).1
  · rw [show m * (s + t) + (C + D) = (m * s + C) + (m * t + D) by ring, pow_add]
    exact Nat.mul_le_mul (h m hm).2 (h' m hm).2

private theorem grows_pow (l n d : ℕ) : Grows l (fun m => (l ^ (m * n)) ^ d) (d * n) :=
  ⟨0, fun m _ => by
    have : (l ^ (m * n)) ^ d = l ^ (m * (d * n)) := by rw [← pow_mul]; congr 1; ring
    simp [this]⟩

private theorem tate_lattice {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {χ : G →* ℤ_[l]ˣ} {d : ℕ} (hF : FinLevel l G χ d) {n : ℕ}
    (ρ : Representation ℤ_[l] G (Fin n → ℤ_[l])) (h : ContAction ρ) :
    Module.Finite ℤ_[l] (H1 ρ) ∧ Module.Finite ℤ_[l] (H2 ρ) ∧
      finrank ℤ_[l] (H1 ρ) = finrank ℤ_[l] ↥(H0 ρ) + finrank ℤ_[l] (H2 ρ) + d * n ∧
      finrank ℤ_[l] (H2 ρ) = finrank ℤ_[l] ((Fin n → ℤ_[l]) ⧸ coSub χ ρ) := by
  have hl : 1 < l := (Fact.out : l.Prime).one_lt
  have hm := fun m => hF _ (redRep ρ m) (contAction_redRep h m)
  obtain ⟨f1, f2, g0, g1, g2⟩ := UpperTheory.lattice_cohomology_finite_and_growth_of_finGen ρ h (UpperTheory.latticeCochains_finGen_of_finLevel hF ρ h) fun m => ⟨(hm m).1, (hm m).2.1⟩
  refine ⟨f1, f2, grows_unique hl g1 (grows_mul (grows_mul g0 g2) (grows_pow l n d)) fun m => ?_,
    grows_unique hl g2 (UpperTheory.card_quotient_powSubmodule_grows_finrank l _) fun m => ?_⟩
  · rw [(hm m).2.2.2.1, card_quot_lSub]
  · rw [(hm m).2.2.2.2, UpperTheory.card_coinvariants_mod_pow_eq_mod_pow_coinvariants]

private theorem tate_Q {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] {χ : G →* ℤ_[l]ˣ} {d : ℕ} (hF : FinLevel l G χ d)
    {V : Type} [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V]
    [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul ℚ_[l] V]
    (ρ : Representation ℚ_[l] G V) (h : ContAction ρ) :
    Module.Finite ℚ_[l] (H1 ρ) ∧ Module.Finite ℚ_[l] (H2 ρ) ∧
      finrank ℚ_[l] (H1 ρ) = finrank ℚ_[l] ↥(H0 ρ) + finrank ℚ_[l] (H2 ρ) + d * finrank ℚ_[l] V ∧
      finrank ℚ_[l] (H2 ρ) =
        finrank ℚ_[l] (V ⧸ coSub ((Units.map (algebraMap ℤ_[l] ℚ_[l] : ℤ_[l] →* ℚ_[l])).comp χ) ρ) := by
  letI : Module ℤ_[l] V := Module.compHom V (algebraMap ℤ_[l] ℚ_[l])
  haveI : IsScalarTower ℤ_[l] ℚ_[l] V := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  obtain ⟨ρT, j, hT, hj, he, hs⟩ := UpperTheory.exists_invariant_lattice_openEmbedding ρ h
  obtain ⟨r0, r1, r2⟩ := UpperTheory.rank_cohomology_rational_eq_rank_lattice ρ h ρT j hT hj he hs
  obtain ⟨f1, f2, e1, e2⟩ := tate_lattice hF ρT hT
  have q0 : finrank ℚ_[l] ↥(H0 ρ) = finrank ℤ_[l] ↥(H0 ρT) := congrArg Cardinal.toNat r0
  have q1 : finrank ℚ_[l] (H1 ρ) = finrank ℤ_[l] (H1 ρT) := congrArg Cardinal.toNat r1
  have q2 : finrank ℚ_[l] (H2 ρ) = finrank ℤ_[l] (H2 ρT) := congrArg Cardinal.toNat r2
  refine ⟨Module.rank_lt_aleph0_iff.1 (r1 ▸ Module.rank_lt_aleph0 _ _),
    Module.rank_lt_aleph0_iff.1 (r2 ▸ Module.rank_lt_aleph0 _ _), ?_, ?_⟩
  · rw [q0, q1, q2, e1]
  · rw [q2, e2, UpperTheory.finrank_coinvariants_eq_finrank_lattice_coinvariants χ ρ ρT j hj.injective he hs]

private theorem finrank_H0dual {G E V : Type} [Group G] [Field E] [AddCommGroup V] [Module E V]
    [FiniteDimensional E V] (χ : G →* Eˣ) (ρ : Representation E G V) :
    finrank E ↥(H0dual χ ρ) = finrank E (V ⧸ coSub χ ρ) := by
  have : H0dual χ ρ = (coSub χ ρ).dualAnnihilator := by
    ext f
    rw [Submodule.mem_dualAnnihilator]
    constructor
    · intro hf w hw
      refine (Submodule.span_le (p := LinearMap.ker f)).2 ?_ hw
      rintro _ ⟨g, x, rfl⟩
      simp [hf g x]
    · intro hf g x
      have := hf _ (Submodule.subset_span ⟨g, x, rfl⟩)
      simpa [sub_eq_zero] using this
  rw [this, ← (Submodule.dualQuotEquivDualAnnihilator _).finrank_eq, Subspace.dual_finrank_eq]

private theorem coSub_res {Q E G V : Type} [Field Q] [Field E] [Algebra Q E] [Group G] [AddCommGroup V]
    [Module E V] [Module Q V] [IsScalarTower Q E V] (χ : G →* Qˣ) (χ' : G →* Eˣ)
    (hχ : ∀ g, ((χ' g : Eˣ) : E) = algebraMap Q E (χ g : Qˣ)) (ρ : Representation E G V) :
    coSub χ (resCoef Q ρ) = (coSub χ' ρ).restrictScalars Q := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨g, x, rfl⟩
    exact Submodule.subset_span ⟨g, x, by rw [hχ, algebraMap_smul]; rfl⟩
  · intro y hy
    have key : ∀ c : E, c • y ∈ coSub χ (resCoef Q ρ) := by
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨g, x, rfl⟩ := hy
        intro c
        refine Submodule.subset_span ⟨g, c • x, ?_⟩
        change _ = ρ g (c • x) - _
        rw [hχ, algebraMap_smul, smul_sub, map_smul, smul_comm c (χ g : Q)]
      | zero => intro c; simp
      | add a b _ _ ha hb => intro c; rw [smul_add]; exact add_mem (ha c) (hb c)
      | smul a b _ hb => intro c; rw [smul_smul]; exact hb _
    simpa using key 1

theorem UpperTheory.V.Loc.tateRat :
    LocalPublishedTheorems → ∀ {v l : ℕ} [Fact v.Prime] [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ v) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {V : Type} [AddCommGroup V] [Module E V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] E V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul E V] (ρ : Representation E G V), ContAction ρ → Module.Finite E (H1 ρ) ∧ Module.Finite E (H2 ρ) ∧ finrank E (H1 ρ) = finrank E ↥(H0 ρ) + finrank E (H2 ρ) + (if v = l then φ.range.index * finrank E V else 0) ∧ finrank E (H2 ρ) = finrank E ↥(H0dual ((cycA v l E).comp φ) ρ) := by
  intro hP v l _ _ G _ _ _ φ hφ E _ _ _ _ _ V _ _ _ _ _ _ _ _ _ ρ h
  haveI : CompactSpace G := by
    have hc : IsClosed (φ.range : Set (GQ v)) := φ.range.isClosed_of_isOpen hφ.isOpen_range
    exact (⟨hφ.isEmbedding, hc⟩ : IsClosedEmbedding φ).compactSpace
  haveI : ContinuousConstSMul ℚ_[l] V := ⟨fun c => by
    simpa only [algebraMap_smul] using continuous_const_smul (T := V) (algebraMap ℚ_[l] E c)⟩
  haveI : FiniteDimensional E V := Module.Finite.of_restrictScalars_finite ℚ_[l] E V
  obtain ⟨f1, f2, e1, e2⟩ := tate_Q (UpperTheory.finite_level_of_finite_level_mod l G _ _ (UpperTheory.finiteLevel_cyclotomic_of_openEmbedding hP φ hφ)) (resCoef ℚ_[l] ρ) h
  obtain ⟨⟨a0⟩, ⟨a1⟩, ⟨a2⟩, -⟩ := UpperTheory.nonempty_cohomology_restrictScalars_linearEquiv ℚ_[l] ρ
  haveI := Module.Finite.equiv a1
  haveI := Module.Finite.equiv a2
  have hd : 0 < finrank ℚ_[l] E := finrank_pos
  rw [coSub_res ((Units.map (algebraMap ℤ_[l] ℚ_[l] : ℤ_[l] →* ℚ_[l])).comp ((cyc v l).comp φ))
      ((cycA v l E).comp φ)
      (fun g => IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] E ((cyc v l (φ g) : ℤ_[l]ˣ) : ℤ_[l])) ρ,
    (Submodule.Quotient.restrictScalarsEquiv ℚ_[l] _).finrank_eq, a2.finrank_eq,
    ← finrank_mul_finrank ℚ_[l] E (H2 ρ), ← finrank_mul_finrank ℚ_[l] E (V ⧸ _)] at e2
  rw [a0.finrank_eq, a1.finrank_eq, a2.finrank_eq, ← finrank_mul_finrank ℚ_[l] E (H2 ρ),
    ← finrank_mul_finrank ℚ_[l] E (H1 ρ), ← finrank_mul_finrank ℚ_[l] E ↥(H0 ρ),
    ← finrank_mul_finrank ℚ_[l] E V] at e1
  refine ⟨Module.Finite.of_restrictScalars_finite ℚ_[l] E _, Module.Finite.of_restrictScalars_finite ℚ_[l] E _,
    Nat.eq_of_mul_eq_mul_left hd ?_, ?_⟩
  · rw [e1]
    split_ifs <;> ring
  · rw [finrank_H0dual]
    exact Nat.eq_of_mul_eq_mul_left hd e2
end
end
