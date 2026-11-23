module

public import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.InhabitedFinite
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.AntitonePowersInDominantMonoidStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CartanDecompositionGlNonarchimedeanStatement
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Topology.Algebra.Group.Defs
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
public import Mathlib.Topology.Compactness.Compact
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CongruenceSubgroupIsCompactStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.EntryMulSubOne
public import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Algebra.Group.Units
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CongruenceSubgroupNormalInMaximalCompactStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CongruenceSubgroupsNeighborhoodBasisStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DominantConjugationPreservesLowerCongruenceStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DominantConjugationPreservesUpperCongruenceStatement
import Mathlib.Tactic.Basify
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsUniformizerNonarchimedeanStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.MatrixNearIdentityInCongruenceSubgroupStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.NearIdentityUpperLowerFactorizationStatement
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CompactSubgroupFiniteOpenCosets

section

@[expose] public section

namespace GlobalTheory.CompanionTheory.CosetCover

theorem exists_finite_coset_cover :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K₀ K : Subgroup G),
      IsCompact (K₀ : Set G) → IsOpen (K : Set G) →
        ∃ (d : ℕ) (c : Fin d → G), (∀ i, c i ∈ K₀) ∧ ∀ g ∈ K₀, ∃ i, ∃ κ ∈ K, g = κ * c i := by
  intro G _ _ _ K₀ K hK₀ hK
  classical
  obtain ⟨t, ht⟩ := hK₀.elim_finite_subcover
    (fun g : K₀ => (fun x => x * (g : G)⁻¹) ⁻¹' (K : Set G))
    (fun g => hK.preimage (continuous_mul_const _))
    (fun g hg => Set.mem_iUnion.2 ⟨⟨g, hg⟩, by simp⟩)
  refine ⟨t.card, fun i => ((t.equivFin.symm i : K₀) : G), fun i => (t.equivFin.symm i : K₀).2,
    fun g hg => ?_⟩
  obtain ⟨a, ha, hga⟩ := Set.mem_iUnion₂.1 (ht hg)
  refine ⟨t.equivFin ⟨a, ha⟩, g * (a : G)⁻¹, hga, ?_⟩
  simp

end GlobalTheory.CompanionTheory.CosetCover
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CompactSubgroupFiniteOpenCosetsStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.compact_subgroup_finite_open_cosets : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K₀ K : Subgroup G), IsCompact (K₀ : Set G) → IsOpen (K : Set G) → ∃ (d : ℕ) (c : Fin d → G), (∀ i, c i ∈ K₀) ∧ ∀ g ∈ K₀, ∃ i, ∃ κ ∈ K, g = κ * c i := by
  first | exact @GlobalTheory.CompanionTheory.CosetCover.exists_finite_coset_cover | exact GlobalTheory.CompanionTheory.CosetCover.exists_finite_coset_cover | (intros; apply GlobalTheory.CompanionTheory.CosetCover.exists_finite_coset_cover <;> assumption)
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CongruenceSubgroupIsOpen

section

@[expose] public section

open Matrix

namespace GlobalTheory.CompanionTheory.CartGL

theorem isOpen_congK : ∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] (n : ℕ) (r : ℝ)
    (h0 : 0 ≤ r) (h1 : r ≤ 1), 0 < r →
    IsOpen (GlobalTheory.CompanionTheory.CartGL.congK L n r h0 h1 : Set (GL (Fin n) L)) := by
  intro L _ _ n r h0 h1 hr
  have hball : IsOpen (Metric.closedBall (0 : L) r) :=
    IsUltrametricDist.isOpen_closedBall _ hr.ne'
  have hval : Continuous fun k : GL (Fin n) L => (k : Matrix (Fin n) (Fin n) L) :=
    Units.continuous_val
  have hinv : Continuous fun k : GL (Fin n) L => ((k⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) :=
    Units.continuous_val.comp continuous_inv
  have hset : (GlobalTheory.CompanionTheory.CartGL.congK L n r h0 h1 : Set (GL (Fin n) L)) =
      ⋂ i : Fin n, ⋂ j : Fin n,
        ((fun k : GL (Fin n) L => ((k : Matrix (Fin n) (Fin n) L) - 1) i j) ⁻¹'
            Metric.closedBall (0 : L) r ∩
          (fun k : GL (Fin n) L =>
            (((k⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) - 1) i j) ⁻¹'
            Metric.closedBall (0 : L) r) := by
    ext k
    simp only [SetLike.mem_coe, mem_congK, Set.mem_iInter, Set.mem_inter_iff, Set.mem_preimage,
      mem_closedBall_zero_iff]
  rw [hset]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => IsOpen.inter ?_ ?_
  · refine hball.preimage ?_
    exact (continuous_apply_apply i j).comp (hval.sub continuous_const)
  · refine hball.preimage ?_
    exact (continuous_apply_apply i j).comp (hinv.sub continuous_const)

end GlobalTheory.CompanionTheory.CartGL
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CongruenceSubgroupIsOpenStatement

section

@[expose] public section

open Matrix

theorem _root_.GlobalTheory.T.congruence_subgroup_is_open : ∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] (n : ℕ) (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1), 0 < r → IsOpen (GlobalTheory.CompanionTheory.CartGL.congK L n r h0 h1 : Set (GL (Fin n) L)) := by
  first | exact @GlobalTheory.CompanionTheory.CartGL.isOpen_congK | exact GlobalTheory.CompanionTheory.CartGL.isOpen_congK | (intros; apply GlobalTheory.CompanionTheory.CartGL.isOpen_congK <;> assumption)
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DominantMonoidElementsAreAntitonePowers

section

@[expose] public section

open Matrix

namespace GlobalTheory.CompanionTheory.CartGL

theorem tExp_antitone (n : ℕ) (i : Fin (n + 2)) : Antitone (tExp n i) := by
  intro j k hjk
  have hjk' : (j : ℕ) ≤ (k : ℕ) := hjk
  unfold tExp
  by_cases h : (i : ℕ) = n + 1
  · simp [h]
  · simp only [h, if_false]
    by_cases hk : (k : ℕ) < i
    · have hj : (j : ℕ) < i := lt_of_le_of_lt hjk' hk
      simp [hj, hk]
    · by_cases hj : (j : ℕ) < i <;> simp [hj, hk]

theorem closure_tGen_antitone (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] (n : ℕ)
    (p : Lˣ) (s : GL (Fin n) L)
    (hs : s ∈ Submonoid.closure (Set.range (tGen p : Fin (n + 2) → GL (Fin n) L))) :
    ∃ a : Fin n → ℤ, Antitone a ∧ s = dPow p a := by
  induction hs using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact ⟨tExp n i, tExp_antitone n i, rfl⟩
  | one => exact ⟨0, fun _ _ _ => le_rfl, (dPow_zero p).symm⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    exact ⟨a + b, ha.add hb, (dPow_add p a b).symm⟩

end GlobalTheory.CompanionTheory.CartGL
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DominantMonoidElementsAreAntitonePowersStatement

section

@[expose] public section

open Matrix

theorem _root_.GlobalTheory.T.dominant_monoid_elements_are_antitone_powers : ∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] (n : ℕ) (p : Lˣ) (s : GL (Fin n) L), s ∈ Submonoid.closure (Set.range (GlobalTheory.CompanionTheory.CartGL.tGen p : Fin (n + 2) → GL (Fin n) L)) → ∃ a : Fin n → ℤ, Antitone a ∧ s = GlobalTheory.CompanionTheory.CartGL.dPow p a := by
  first | exact @GlobalTheory.CompanionTheory.CartGL.closure_tGen_antitone | exact GlobalTheory.CompanionTheory.CartGL.closure_tGen_antitone | (intros; apply GlobalTheory.CompanionTheory.CartGL.closure_tGen_antitone <;> assumption)
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CartanDecompositionGL

section

@[expose] public section

open CompanionTheory.Rg.Fl Matrix
namespace GlobalTheory.CompanionTheory.CartGL

theorem stCartanGL : StCartanGL := by
  unfold CompanionTheory.Rg.Fl.StCartanGL CompanionTheory.Rg.Fl.HasCartan
  intro L _ _ _ n U hU
  obtain ⟨p, hp⟩ := GlobalTheory.T.exists_uniformizer_nonarchimedean L
  have hp1 : ‖(p : L)‖ < 1 := by
    unfold GlobalTheory.CompanionTheory.CartGL.IsUnif at hp
    exact hp.1
  obtain ⟨ε, hε, hεU⟩ := GlobalTheory.T.congruence_subgroups_neighborhood_basis L n (U : Set (GL (Fin n) L)) hU U.one_mem
  obtain ⟨r, hr0, hr1, hrε⟩ : ∃ r : ℝ, 0 < r ∧ r < 1 ∧ r ≤ ε :=
    ⟨min ε (1 / 2), lt_min hε (by norm_num), lt_of_le_of_lt (min_le_right _ _) (by norm_num), min_le_left _ _⟩
  have h0 : 0 ≤ r := hr0.le
  have h1 : r ≤ 1 := hr1.le
  refine ⟨GlobalTheory.CompanionTheory.CartGL.congK L n r h0 h1, fun x hx => hεU r h0 h1 hrε hx,
    GlobalTheory.T.congruence_subgroup_is_open L n r h0 h1 hr0, GlobalTheory.T.congruence_subgroup_is_compact L n r h0 h1, ?_⟩
  obtain ⟨d, c, hc, hcK⟩ := GlobalTheory.T.compact_subgroup_finite_open_cosets (GL (Fin n) L) (GlobalTheory.CompanionTheory.CartGL.congK L n 1 zero_le_one le_rfl)
    (GlobalTheory.CompanionTheory.CartGL.congK L n r h0 h1) (GlobalTheory.T.congruence_subgroup_is_compact L n 1 zero_le_one le_rfl) (GlobalTheory.T.congruence_subgroup_is_open L n r h0 h1 hr0)
  refine ⟨d, n + 2, ?_⟩
  unfold CompanionTheory.Rg.Fl.IsCartan
  refine ⟨c, GlobalTheory.CompanionTheory.CartGL.tGen p, ?_, ?_, ?_, ?_⟩
  · intro i k
    constructor
    · intro hk
      exact GlobalTheory.T.congruence_subgroup_normal_in_maximal_compact L n r h0 h1 (c i) k (hc i) hk
    · intro hk
      have h2 := GlobalTheory.T.congruence_subgroup_normal_in_maximal_compact L n r h0 h1 (c i)⁻¹ _ (Subgroup.inv_mem _ (hc i)) hk
      have e : (c i)⁻¹ * (c i * k * (c i)⁻¹) * (c i)⁻¹⁻¹ = k := by group
      rwa [e] at h2
  · intro i j
    show GlobalTheory.CompanionTheory.CartGL.dPow p (GlobalTheory.CompanionTheory.CartGL.tExp n i) * GlobalTheory.CompanionTheory.CartGL.dPow p (GlobalTheory.CompanionTheory.CartGL.tExp n j) =
      GlobalTheory.CompanionTheory.CartGL.dPow p (GlobalTheory.CompanionTheory.CartGL.tExp n j) * GlobalTheory.CompanionTheory.CartGL.dPow p (GlobalTheory.CompanionTheory.CartGL.tExp n i)
    rw [← GlobalTheory.CompanionTheory.CartGL.dPow_add, ← GlobalTheory.CompanionTheory.CartGL.dPow_add, add_comm]
  · intro g
    obtain ⟨a, ha, k₁, hk₁, k₂, hk₂, rfl⟩ := GlobalTheory.T.cartan_decomposition_gl_nonarchimedean L n p hp g
    obtain ⟨i, κ₁, hκ₁, rfl⟩ := hcK k₁ hk₁
    obtain ⟨j, κ₂, hκ₂, rfl⟩ := hcK k₂ hk₂
    refine ⟨i, j, GlobalTheory.CompanionTheory.CartGL.dPow p a, GlobalTheory.T.antitone_powers_in_dominant_monoid L n p a ha, κ₁, hκ₁, (c j)⁻¹ * κ₂ * c j, ?_, ?_⟩
    · have h2 := GlobalTheory.T.congruence_subgroup_normal_in_maximal_compact L n r h0 h1 (c j)⁻¹ κ₂ (Subgroup.inv_mem _ (hc j)) hκ₂
      rwa [inv_inv] at h2
    · group
  · intro s hs s' hs' k hk
    obtain ⟨a₁, ha₁, rfl⟩ := GlobalTheory.T.dominant_monoid_elements_are_antitone_powers L n p s hs
    obtain ⟨a₂, ha₂, rfl⟩ := GlobalTheory.T.dominant_monoid_elements_are_antitone_powers L n p s' hs'
    have hkA : ∀ i j, ‖((k : Matrix (Fin n) (Fin n) L) - 1) i j‖ ≤ r := fun i j =>
      (GlobalTheory.CompanionTheory.CartGL.mem_congK.mp hk i j).1
    obtain ⟨Um, Wm, hUl, hWu, hUr, hWr, hUW⟩ := GlobalTheory.T.near_identity_upper_lower_factorization L n r h0 hr1 (k : Matrix (Fin n) (Fin n) L) hkA
    obtain ⟨kU, -, hkUv⟩ := GlobalTheory.T.matrix_near_identity_in_congruence_subgroup L n r h0 h1 hr1 Um hUr
    obtain ⟨kW, -, hkWv⟩ := GlobalTheory.T.matrix_near_identity_in_congruence_subgroup L n r h0 h1 hr1 Wm hWr
    have hk_eq : k = kU * kW := Units.ext (by rw [Units.val_mul, hkUv, hkWv, hUW])
    have hA : GlobalTheory.CompanionTheory.CartGL.dPow p a₁ * kU * (GlobalTheory.CompanionTheory.CartGL.dPow p a₁)⁻¹ ∈ GlobalTheory.CompanionTheory.CartGL.congK L n r h0 h1 := by
      have hb := GlobalTheory.T.dominant_conjugation_preserves_upper_congruence L n p hp1 a₁ ha₁ r kU (fun i j hij => by rw [hkUv]; exact hUl i j hij)
        (fun i j => by rw [hkUv]; exact hUr i j)
      obtain ⟨k', hk', hk'v⟩ := GlobalTheory.T.matrix_near_identity_in_congruence_subgroup L n r h0 h1 hr1 _ hb
      rw [← Units.ext hk'v]
      exact hk'
    have hB : (GlobalTheory.CompanionTheory.CartGL.dPow p a₂)⁻¹ * kW * GlobalTheory.CompanionTheory.CartGL.dPow p a₂ ∈ GlobalTheory.CompanionTheory.CartGL.congK L n r h0 h1 := by
      have hb := GlobalTheory.T.dominant_conjugation_preserves_lower_congruence L n p hp1 a₂ ha₂ r kW (fun i j hij => by rw [hkWv]; exact hWu i j hij)
        (fun i j => by rw [hkWv]; exact hWr i j)
      obtain ⟨k', hk', hk'v⟩ := GlobalTheory.T.matrix_near_identity_in_congruence_subgroup L n r h0 h1 hr1 _ hb
      rw [← Units.ext hk'v]
      exact hk'
    refine ⟨_, hA, _, hB, ?_⟩
    rw [hk_eq]
    group

end GlobalTheory.CompanionTheory.CartGL
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CartanDecompositionGLStatement

section

@[expose] public section

open CompanionTheory.Rg.Fl

theorem _root_.GlobalTheory.T.CartanDecompositionGL : StCartanGL := by
  first | exact @GlobalTheory.CompanionTheory.CartGL.stCartanGL | exact GlobalTheory.CompanionTheory.CartGL.stCartanGL | (intros; apply GlobalTheory.CompanionTheory.CartGL.stCartanGL <;> assumption)
end
end
