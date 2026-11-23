module

public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Mathlib.Basic.Finite.Defs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCompatibleSeqOfFiniteNonempty
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
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLimitCocycleOfCompatibleModPowStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTorsionCocycleFiniteLevelLiftStatement
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteLatticeCocyclesModUniformizerPow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TatePairingLatticeQuotientsNondegenerate
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Linter.HaveILetI
public import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCompatibleSeqOfFiniteNonemptyStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.exists_compatible_seq_of_finite_nonempty' : ∀ (X : ℕ → Type) (f : ∀ n, X (n + 1) → X n) (Y : ∀ n, Set (X n)), (∀ n, (Y n).Finite) → (∀ n, (Y n).Nonempty) → (∀ n, ∀ x ∈ Y (n + 1), f n x ∈ Y n) → ∃ s : ∀ n, X n, ∀ n, s n ∈ Y n ∧ f n (s (n + 1)) = s n := by
  first | exact @GlobalTheory.exists_compatible_seq_of_finite_nonempty | exact GlobalTheory.exists_compatible_seq_of_finite_nonempty | (intros; apply GlobalTheory.exists_compatible_seq_of_finite_nonempty <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteLatticeCocyclesModUniformizerPowStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.finite_latticeCocycles_mod_uniformizer_pow : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (ϖ : O), Irreducible ϖ → ∀ (n : ℕ) (hI : StableSub LA (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA.T)), (quotientCocycles LA _ hI : Set (↥(GK K) → ↥LA.T ⧸ (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA.T))).Finite := by
  first | exact @GlobalTheory.CocycleModPow.finite_Z1Q | exact GlobalTheory.CocycleModPow.finite_Z1Q | (intros; apply GlobalTheory.CocycleModPow.finite_Z1Q <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TatePairingLatticeQuotientsNondegenerateStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.tate_pairing_lattice_quotients_nondegenerate : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ L1 : Lattice (O := O) (charRep (cycLL (P.PD K) LL)), L1.T = LinearMap.range (Algebra.linearMap O LL) → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDualLat1 (P.PD K) LA LA' m → ∀ (ϖ : O), Irreducible ϖ → ∀ (r : ℕ) (hI : StableSub LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)) (hI' : StableSub LA' (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA'.T)), (∀ c ∈ quotientCocycles LA _ hI, (∀ c' ∈ quotientCocycles LA' _ hI', CobO (P.PD K) L1 (fun x => (algebraMap O LL ϖ)⁻¹ ^ r * m (Formalism.MainNotions.LocalSituation.liftQ LA _ (c x.1)) (A'.ρ x.1 (Formalism.MainNotions.LocalSituation.liftQ LA' _ (c' x.2))))) → c ∈ BQ LA _ hI) ∧ (∀ c' ∈ quotientCocycles LA' _ hI', (∀ c ∈ quotientCocycles LA _ hI, CobO (P.PD K) L1 (fun x => (algebraMap O LL ϖ)⁻¹ ^ r * m (Formalism.MainNotions.LocalSituation.liftQ LA _ (c x.1)) (A'.ρ x.1 (Formalism.MainNotions.LocalSituation.liftQ LA' _ (c' x.2))))) → c' ∈ BQ LA' _ hI') := by
  first | exact @GlobalTheory.TateFin.tate_pairing_nondegenerate | exact GlobalTheory.TateFin.tate_pairing_nondegenerate | (intros; apply GlobalTheory.TateFin.tate_pairing_nondegenerate <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TorsionCocycleUniformizerPowSmulMem

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section

namespace GlobalTheory.TorsCoc

theorem exists_pow_smul_mem {LL : Type} [Field LL] {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Algebra O LL] [IsFractionRing O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
    (T : Submodule O V) (hT : Submodule.span LL (T : Set V) = ⊤) (ϖ : O) (hϖ : Irreducible ϖ)
    (v : V) : ∃ k : ℕ, ∀ j, k ≤ j → (algebraMap O LL ϖ) ^ j • v ∈ T := by
  have hv : v ∈ Submodule.span LL (T : Set V) := hT ▸ Submodule.mem_top

  have up : ∀ (x : V) (k j : ℕ), k ≤ j → (algebraMap O LL ϖ) ^ k • x ∈ T →
      (algebraMap O LL ϖ) ^ j • x ∈ T := by
    intro x k j hkj hx
    obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hkj
    rw [pow_add, mul_comm, mul_smul, ← map_pow, algebraMap_smul]
    exact T.smul_mem _ hx
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨0, fun j _ => by rw [← map_pow, algebraMap_smul]; exact T.smul_mem _ hx⟩
  | zero => exact ⟨0, fun j _ => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨max a b, fun j hj => by
      rw [smul_add]
      exact T.add_mem (ha j (le_trans (le_max_left _ _) hj)) (hb j (le_trans (le_max_right _ _) hj))⟩
  | smul a x _ hx =>
    obtain ⟨k, hk⟩ := hx
    obtain ⟨b, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := O) a
    have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hs0 hϖ
    refine ⟨n + k, fun j hj => up _ (n + k) j hj ?_⟩
    have key : (algebraMap O LL ϖ) ^ n * (algebraMap O LL b / algebraMap O LL s) =
        algebraMap O LL (b * ((u⁻¹ : Oˣ) : O)) := by
      have hsne : algebraMap O LL s ≠ 0 :=
        IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs
      rw [mul_div_assoc', div_eq_iff hsne, hu]
      simp only [map_mul, map_pow]
      have hu1 : algebraMap O LL ((u⁻¹ : Oˣ) : O) * algebraMap O LL (u : O) = 1 := by
        rw [← map_mul, Units.inv_mul, map_one]
      linear_combination (-(algebraMap O LL b * algebraMap O LL ϖ ^ n)) * hu1
    have e : (algebraMap O LL ϖ) ^ (n + k) • ((algebraMap O LL b / algebraMap O LL s) • x) =
        ((algebraMap O LL ϖ) ^ n * (algebraMap O LL b / algebraMap O LL s)) •
          ((algebraMap O LL ϖ) ^ k • x) := by
      rw [pow_add, mul_smul, mul_smul, smul_comm (algebraMap O LL b / algebraMap O LL s)]
    rw [e, key, algebraMap_smul]
    exact T.smul_mem _ (hk k le_rfl)

theorem cocycle_pow_smul_mem : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL]
    [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL],
    GoodO (Qp := ℚ_[l]) LL O → ∀ (A' : GRep ↥(GK K) ℚ_[l] LL O) (LA' : Lattice (O := O) A'.ρ)
    (ϖ : O), Irreducible ϖ → ∀ c ∈ divisibleCocycles LA', ∃ r : ℕ, ∀ g,
    (algebraMap O LL ϖ) ^ r • liftD LA' (c g) ∈ LA'.T := by
  intro l _ K LL _ _ _ O _ _ hO A' LA' ϖ hϖ c hc
  obtain ⟨⟨hD, hDVR, hFR⟩, -⟩ := hO
  haveI : CompactSpace ↥(GK K) := by
    haveI := K.2
    exact isCompact_iff_compactSpace.1 (InfiniteGalois.fixingSubgroup_isClosed K.1).isCompact
  have hfin : (Set.range c).Finite := hc.1.range_finite
  choose f hf using fun y : A'.V ⧸ LA'.T =>
    exists_pow_smul_mem LA'.T LA'.span ϖ hϖ (liftD LA' y)
  refine ⟨hfin.toFinset.sup f, fun g => hf (c g) _ ?_⟩
  exact Finset.le_sup (f := f) (hfin.mem_toFinset.2 ⟨g, rfl⟩)

end GlobalTheory.TorsCoc
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TorsionCocycleUniformizerPowSmulMemStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.torsionCocycle_uniformizer_pow_smul_mem : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A' : GRep ↥(GK K) ℚ_[l] LL O) (LA' : Lattice (O := O) A'.ρ) (ϖ : O), Irreducible ϖ → ∀ c ∈ divisibleCocycles LA', ∃ r : ℕ, ∀ g, (algebraMap O LL ϖ) ^ r • liftD LA' (c g) ∈ LA'.T := by
  first | exact @GlobalTheory.TorsCoc.cocycle_pow_smul_mem | exact GlobalTheory.TorsCoc.cocycle_pow_smul_mem | (intros; apply GlobalTheory.TorsCoc.cocycle_pow_smul_mem <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeDualPairingCyclotomic

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.TateOrth

section Gen
variable {G : Type} [Group G] {LL : Type} [Field LL] {O : Type} [CommRing O] [Algebra O LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
  {ρ : Representation LL G V}

theorem mem_span_smul_top (L : Lattice (O := O) ρ) (a : O) (x : ↥L.T) :
    x ∈ (Ideal.span {a} • ⊤ : Submodule O ↥L.T) ↔ ∃ y : ↥L.T, x = a • y := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨y, -, rfl⟩; exact ⟨y, rfl⟩
  · rintro ⟨y, rfl⟩; exact ⟨y, Submodule.mem_top, rfl⟩

theorem stable_span_smul_top (L : Lattice (O := O) ρ) (a : O) :
    StableSub L (Ideal.span {a} • ⊤ : Submodule O ↥L.T) := by
  intro g x hx
  rw [mem_span_smul_top] at hx ⊢
  obtain ⟨y, rfl⟩ := hx
  exact ⟨actT L g y, map_smul _ _ _⟩

theorem factor_actQ (L : Lattice (O := O) ρ) {I J : Submodule O ↥L.T} (hI : StableSub L I)
    (hJ : StableSub L J) (hIJ : I ≤ J) (g : G) (x : ↥L.T ⧸ I) :
    Submodule.factor hIJ (actQ L I hI g x) = actQ L J hJ g (Submodule.factor hIJ x) := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective I x
  rfl

theorem factor_mem_Z1Q [TopologicalSpace G] (L : Lattice (O := O) ρ) {I J : Submodule O ↥L.T}
    (hI : StableSub L I) (hJ : StableSub L J) (hIJ : I ≤ J) {z : G → ↥L.T ⧸ I}
    (hz : z ∈ quotientCocycles L I hI) : (fun g => Submodule.factor hIJ (z g)) ∈ quotientCocycles L J hJ := by
  refine ⟨hz.1.comp _, fun g h => ?_⟩
  simp only [hz.2 g h, map_add (f := _), factor_actQ L hI hJ hIJ]

end Gen

theorem mem_BD_of_orthogonal : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ L1 : Lattice (O := O) (charRep (cycLL (P.PD K) LL)), L1.T = LinearMap.range (Algebra.linearMap O LL) → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDualLat1 (P.PD K) LA LA' m → ∀ c ∈ divisibleCocycles LA', (∀ d ∈ latticeCocycles LA, CobO (P.PD K) L1 (cupLD LA' m d c)) → c ∈ BD LA' := by
  intro hT l _ P K LL _ _ _ O _ _ hO L1 hL1 A A' LA LA' m hm c hc horth
  obtain ⟨hDom, hDVR, hFrac⟩ := hO.1
  haveI := hDom; haveI := hDVR; haveI := hFrac
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  set π := algebraMap O LL ϖ with hπdef
  have hπ : π ≠ 0 := by
    intro h
    exact hϖ.ne_zero (IsFractionRing.injective O LL (by rw [← hπdef, h, map_zero]))
  by_contra hcB
  obtain ⟨r, hr⟩ := GlobalTheory.T.torsionCocycle_uniformizer_pow_smul_mem l K LL O hO A' LA' ϖ hϖ c hc
  let I : ℕ → Submodule O ↥LA.T := fun k => Ideal.span {ϖ ^ (r + k)} • ⊤
  have hI : ∀ k, StableSub LA (I k) := fun k => stable_span_smul_top LA _
  let Φ : ∀ k, (↥(GK K) → ↥LA.T ⧸ I k) → ↥(GK K) × ↥(GK K) → LL := fun k z x =>
    m (Formalism.MainNotions.LocalSituation.liftQ LA (I k) (z x.1)) (A'.ρ x.1 (liftD LA' (c x.2)))
  let Y : ∀ k, Set (↥(GK K) → ↥LA.T ⧸ I k) := fun k =>
    {z | z ∈ quotientCocycles LA (I k) (hI k) ∧ ¬ CobO (P.PD K) L1 (Φ k z)}
  have hle : ∀ k, I (k + 1) ≤ I k := fun k =>
    Submodule.smul_mono_left (Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow ϖ (by omega)))
  have hle0 : ∀ k, I k ≤ I 0 := fun k =>
    Submodule.smul_mono_left (Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow ϖ (by omega)))
  let f : ∀ k, (↥(GK K) → ↥LA.T ⧸ I (k + 1)) → (↥(GK K) → ↥LA.T ⧸ I k) := fun k z g =>
    Submodule.factor (hle k) (z g)

  have hmemPow : ∀ (j : ℕ) (x : ↥LA.T), x ∈ (Ideal.span {ϖ ^ j} • ⊤ : Submodule O ↥LA.T) →
      ∃ t ∈ LA.T, (x : A.V) = π ^ j • t := by
    intro j x hx
    obtain ⟨y, rfl⟩ := (mem_span_smul_top LA _ x).1 hx
    exact ⟨y, y.2, by rw [Submodule.coe_smul, hπdef, ← map_pow, algebraMap_smul]⟩
  have hliftMem : ∀ (J : Submodule O ↥LA.T) (x : ↥LA.T ⧸ J), Formalism.MainNotions.LocalSituation.liftQ LA J x ∈ LA.T :=
    fun J x => (Submodule.Quotient.mk_surjective J x).choose.2
  have hspec : ∀ (J : Submodule O ↥LA.T) (x : ↥LA.T ⧸ J), ∃ y : ↥LA.T,
      (y : A.V) = Formalism.MainNotions.LocalSituation.liftQ LA J x ∧ Submodule.Quotient.mk y = x := fun J x =>
    ⟨_, rfl, (Submodule.Quotient.mk_surjective J x).choose_spec⟩
  have hlift2 : ∀ k (x : ↥LA.T ⧸ I k) (y : ↥LA.T), x = Submodule.Quotient.mk y →
      ∃ t ∈ LA.T, Formalism.MainNotions.LocalSituation.liftQ LA (I k) x - (y : A.V) = π ^ (r + k) • t := by
    intro k x y hxy
    obtain ⟨y0, hy0, hmk0⟩ := hspec (I k) x
    have hmem : y0 - y ∈ I k := (Submodule.Quotient.eq _).1 (hmk0.trans hxy)
    obtain ⟨t, ht, he⟩ := hmemPow (r + k) _ hmem
    exact ⟨t, ht, by rw [← hy0, ← he, Submodule.coe_sub]⟩
  have hcong : ∀ (k : ℕ) (a b : A.V) (y : A'.V) (t : A.V), t ∈ LA.T → a - b = π ^ k • t →
      π ^ k • y ∈ LA'.T → m a y - m b y ∈ Set.range (algebraMap O LL) := by
    intro k a b y t ht hab hy
    obtain ⟨e, he⟩ := (hm.2 _).1 hy t ht
    have : m a y - m b y = m t (π ^ k • y) := by
      rw [← LinearMap.sub_apply, ← map_sub, hab, LinearMap.map_smul₂, (m t).map_smul]
    exact ⟨e, by rw [this, he]⟩
  have hcobO : ∀ z z' : ↥(GK K) × ↥(GK K) → LL, (∀ x, z x - z' x ∈ Set.range (algebraMap O LL)) →
      (CobO (P.PD K) L1 z → CobO (P.PD K) L1 z') := by
    intro z z' hzz hz
    have : (fun x => (Submodule.Quotient.mk (z x) : LL ⧸ L1.T)) =
        fun x => Submodule.Quotient.mk (z' x) := by
      funext x
      rw [Submodule.Quotient.eq, hL1]
      obtain ⟨e, he⟩ := hzz x
      exact ⟨e, he⟩
    unfold CobO at hz ⊢
    rwa [← this]
  have hT'pow : ∀ (k : ℕ) (g h : ↥(GK K)), π ^ (r + k) • A'.ρ g (liftD LA' (c h)) ∈ LA'.T := by
    intro k g h
    rw [← map_smul, add_comm, pow_add, mul_smul]
    apply LA'.stable
    rw [hπdef, ← map_pow, algebraMap_smul]
    exact LA'.T.smul_mem _ (hr h)

  have hfin : ∀ k, (Y k).Finite := fun k =>
    (GlobalTheory.T.finite_latticeCocycles_mod_uniformizer_pow hT l K LL O hO A LA ϖ hϖ (r + k) (hI k)).subset (fun z hz => hz.1)
  have hne : ∀ k, (Y k).Nonempty := by
    intro k
    have hI' : StableSub LA' (Ideal.span {ϖ ^ (r + k)} • ⊤ : Submodule O ↥LA'.T) :=
      stable_span_smul_top LA' _
    obtain ⟨c', hc'Z, hc'B, hc'l⟩ :=
      GlobalTheory.T.exists_torsionCocycle_finite_level_lift l K LL O hO A' LA' ϖ hϖ c hc hcB r hr (r + k) (by omega) hI'
    have h2 := (GlobalTheory.T.tate_pairing_lattice_quotients_nondegenerate hT l P K LL O hO L1 hL1 A A' LA LA' m hm ϖ hϖ (r + k) (hI k) hI').2 c' hc'Z
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    apply hc'B
    apply h2
    intro z hz
    have hzY : z ∉ Y k := by rw [hemp]; exact fun h => h
    have hC : CobO (P.PD K) L1 (Φ k z) := by
      by_contra hn; exact hzY ⟨hz, hn⟩
    refine hcobO _ _ ?_ hC
    intro x
    obtain ⟨t, ht, hteq⟩ := hc'l x.2
    obtain ⟨e, he⟩ := (hm.2 _).1 (LA'.stable x.1 t ht) _ (hliftMem (I k) (z x.1))
    refine ⟨-e, ?_⟩
    rw [map_neg, ← he]
    simp only [Φ, hteq, map_add (f := _), map_smul, smul_eq_mul, ← hπdef]
    rw [inv_pow]
    field_simp
    ring
  have hmap : ∀ k, ∀ z ∈ Y (k + 1), f k z ∈ Y k := by
    rintro k z ⟨hz, hnc⟩
    refine ⟨factor_mem_Z1Q LA (hI (k + 1)) (hI k) (hle k) hz, fun hc' => hnc (hcobO _ _ ?_ hc')⟩
    intro x
    obtain ⟨t, ht, hteq⟩ := hlift2 k (f k z x.1) ⟨_, hliftMem (I (k + 1)) (z x.1)⟩ (by
      obtain ⟨y0, hy0, hmk0⟩ := hspec (I (k + 1)) (z x.1)
      have hy : (⟨_, hliftMem (I (k + 1)) (z x.1)⟩ : ↥LA.T) = y0 := Subtype.ext hy0.symm
      rw [hy]
      show Submodule.factor (hle k) (z x.1) = _
      rw [← hmk0]
      rfl)
    exact hcong (r + k) _ _ _ t ht hteq (hT'pow k x.1 x.2)
  obtain ⟨s, hs⟩ := GlobalTheory.T.exists_compatible_seq_of_finite_nonempty' (fun k => ↥(GK K) → ↥LA.T ⧸ I k) f Y hfin hne hmap
  let w : ℕ → ↥(GK K) → ↥LA.T := fun k g => (Submodule.Quotient.mk_surjective (I k) (s k g)).choose
  have hwk : ∀ k g, (Submodule.Quotient.mk (w k g) : ↥LA.T ⧸ I k) = s k g := fun k g =>
    (Submodule.Quotient.mk_surjective (I k) (s k g)).choose_spec
  have hI'I : ∀ k, I k ≤ (Ideal.span {ϖ ^ k} • ⊤ : Submodule O ↥LA.T) := fun k =>
    Submodule.smul_mono_left (Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow ϖ (by omega)))
  have hI' : ∀ n : ℕ, StableSub LA (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA.T) := fun n =>
    stable_span_smul_top LA _
  have hwZ : ∀ n, (fun g => (Submodule.Quotient.mk (w n g) :
      ↥LA.T ⧸ (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA.T))) ∈ quotientCocycles LA _ (hI' n) := by
    intro n
    have := factor_mem_Z1Q LA (hI n) (hI' n) (hI'I n) (hs n).1.1
    convert this using 1
    funext g
    rw [← hwk n g]
    rfl
  have hstep : ∀ k g, w (k + 1) g - w k g ∈ I k := by
    intro k g
    apply (Submodule.Quotient.eq _).1
    rw [hwk k g, ← (hs k).2]
    show _ = Submodule.factor (hle k) (s (k + 1) g)
    rw [← hwk (k + 1) g]
    rfl
  obtain ⟨d, hdZ, hd⟩ := GlobalTheory.T.exists_limit_cocycle_of_compatible_mod_pow l K LL O hO A LA ϖ hϖ hI' w hwZ (fun n g => hI'I n (hstep n g))
  have htele : ∀ n g, w n g - w 0 g ∈ I 0 := by
    intro n g
    induction n with
    | zero => simp
    | succ n ih =>
      have := (I 0).add_mem (hle0 n (hstep n g)) ih
      rwa [sub_add_sub_cancel] at this
  apply (hs 0).1.2
  refine hcobO _ _ ?_ (horth d hdZ)
  intro x
  obtain ⟨t1, ht1, hdt⟩ := hd r x.1
  have he : t1 + (w r x.1 - w 0 x.1) ∈ I 0 := (I 0).add_mem ht1 (htele r x.1)
  obtain ⟨u, hu, hue⟩ := hmemPow (r + 0) _ he
  obtain ⟨t3, ht3, ht3e⟩ := hlift2 0 (s 0 x.1) (w 0 x.1) (hwk 0 x.1).symm
  refine hcong (r + 0) _ _ _ (u - t3) (LA.T.sub_mem hu ht3) ?_ (hT'pow 0 x.1 x.2)
  rw [smul_sub, ← hue, ← ht3e, hdt]
  simp only [Submodule.coe_add, Submodule.coe_sub]
  abel

end GlobalTheory.TateOrth
end
end
