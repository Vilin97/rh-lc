module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIwasawaDecompositionUpperUnitriangularInte
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasNormGroups
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.NotIsGenericDetRepTwo
import Formalism.ConjugateSelfDual.Statement
import ReciprocityTheory.GaloisValuations.GlobalA
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTorusBoundsOfConsecutiveRatioBoundsStatement
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlCornerEmbeddingUpperUnitriangularSuperDiagonalStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCompactBoundedTorusStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.NotIsGenericDetRepTwo
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WhittakerFunctionalTorusValuationBound
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WhittakerTorusTwKerRootBoundStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIwasawaDecompositionUpperUnitriangularInteStatement

section

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.exists_iwasawa_decomposition_upperUnitriangular_integral : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m : ℕ) (g : GL (Fin m) k), ∃ u ∈ unipB k (Fin m), ∃ t : Fin m → kˣ, ∃ κ ∈ KO k (Fin m), g = u * diagT k (Fin m) t * κ := by
  first | exact @GlobalTheory.SmGL.exists_unipB_mul_diagT_mul_KO | exact GlobalTheory.SmGL.exists_unipB_mul_diagT_mul_KO | (intros; apply GlobalTheory.SmGL.exists_unipB_mul_diagT_mul_KO <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteImageOfIsOpenStabilizer

section

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem finite_image_of_isOpen_stabilizer (G : Type) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (V : Type) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (v : V) (hH : IsOpen {g : G | ρ g v = v})
    (S : Set G) (hS : IsCompact S) : ((fun g => ρ g v) '' S).Finite := by
  obtain ⟨t, ht⟩ := hS.elim_finite_subcover
    (fun s : G => (fun x => s⁻¹ * x) ⁻¹' {g : G | ρ g v = v})
    (fun s => hH.preimage (continuous_const.mul continuous_id))
    (fun x _ => Set.mem_iUnion.2 ⟨x, by simp⟩)
  refine ((t : Set G).toFinite.image (fun g => ρ g v)).subset ?_
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨s, hs, hxs⟩ := Set.mem_iUnion₂.1 (ht hx)
  refine ⟨s, hs, ?_⟩
  have h1 : ρ (s⁻¹ * x) v = v := hxs
  have hx' : x = s * (s⁻¹ * x) := by group
  show ρ s v = ρ x v
  conv_rhs => rw [hx', map_mul, Module.End.mul_apply, h1]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteImageOfIsOpenStabilizerStatement

section

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.finite_image_of_isOpen_stabilizer_alt : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (v : V), IsOpen {g : G | ρ g v = v} → ∀ S : Set G, IsCompact S → ((fun g => ρ g v) '' S).Finite := by
  first | exact @GlobalTheory.finite_image_of_isOpen_stabilizer | exact GlobalTheory.finite_image_of_isOpen_stabilizer | (intros; apply GlobalTheory.finite_image_of_isOpen_stabilizer <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlCornerEmbeddingDiagonalTorusEqSnocOne

section

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands

theorem corner_diagT (R : Type) [CommRing R] (m : ℕ) (t : Fin m → Rˣ) :
    corner (diagT R (Fin m) t) = diagT R (Fin (m + 1)) (Fin.snoc t 1) := by
  apply Units.ext
  change (emb₂ R (stdSum (rfl : m + 1 = m + 1)) (diagT R (Fin m) t, 1) : Matrix (Fin (m + 1)) (Fin (m + 1)) R) = (diagT R (Fin (m + 1)) (Fin.snoc t 1) : Matrix (Fin (m + 1)) (Fin (m + 1)) R)
  rw [val_emb₂, val_diagT, val_diagT]
  ext i j
  obtain ⟨i, rfl⟩ := (stdSum (rfl : m + 1 = m + 1)).surjective i
  obtain ⟨j, rfl⟩ := (stdSum (rfl : m + 1 = m + 1)).surjective j
  have hl : ∀ a : Fin m, stdSum (rfl : m + 1 = m + 1) (Sum.inl a) = Fin.castSucc a := fun a => Fin.ext rfl
  have hr : ∀ a : Fin 1, stdSum (rfl : m + 1 = m + 1) (Sum.inr a) = Fin.last m := fun a => by
    apply Fin.ext; simp [stdSum, Subsingleton.elim a 0]
  simp only [reindex_apply, submatrix_apply, Equiv.symm_apply_apply]
  rcases i with i | i <;> rcases j with j | j
  · rw [hl, hl, fromBlocks_apply₁₁]
    simp only [diagonal_apply, Fin.snoc_castSucc, Fin.castSucc_inj]
  · rw [hl, hr, fromBlocks_apply₁₂, diagonal_apply_ne _ (Fin.castSucc_lt_last i).ne, Matrix.zero_apply]
  · rw [hl, hr, fromBlocks_apply₂₁, diagonal_apply_ne _ (Fin.castSucc_lt_last j).ne', Matrix.zero_apply]
  · rw [hr, hr, fromBlocks_apply₂₂, diagonal_apply_eq, Fin.snoc_last, Subsingleton.elim i j]
    simp

end GlobalTheory.LocLanglands
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlCornerEmbeddingDiagonalTorusEqSnocOneStatement

section

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.glCornerEmbedding_diagonalTorus_eq_snoc_one : ∀ (R : Type) [CommRing R] (m : ℕ) (t : Fin m → Rˣ), corner (diagT R (Fin m) t) = diagT R (Fin (m + 1)) (Fin.snoc t 1) := by
  first | exact @GlobalTheory.LocLanglands.corner_diagT | exact GlobalTheory.LocLanglands.corner_diagT | (intros; apply GlobalTheory.LocLanglands.corner_diagT <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WhittakerFunctionalTorusValuationBoundStatement

section

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.whittaker_functional_torus_valuation_bound : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) k) V), IsSmooth ρ → ∀ l : Module.Dual ℂ V, IsFunctional ψ ρ l → ∀ x : V, ∃ r : kˣ, ∀ (t : Fin n → kˣ) (i j : Fin n), j.val = i.val + 1 → l (ρ (diagT k (Fin n) t) x) ≠ 0 → valuation k ((t i : k) / t j) ≤ valuation k (r : k) := by
  first | exact @GlobalTheory.RootUp.whittaker_torus_root_bound | exact GlobalTheory.RootUp.whittaker_torus_root_bound | (intros; apply GlobalTheory.RootUp.whittaker_torus_root_bound <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RankinSelbergTestFunction

section

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LocLanglands


open scoped Pointwise in
theorem exists_compact_mod_unipB_whittaker : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin (m + 1)) k) V), IsSmooth ρ → (∀ (a b : ℕ) (h : ∑ i, ![a, b] i = m + 1), 0 < a → 0 < b → ∀ x : V, x ∈ twKer ρ (unipRad k (stdBlocks ![a, b] h)) 1) → ∀ l : Module.Dual ℂ V, IsFunctional ψ ρ l → ∀ v : V, ∃ C : Set (GL (Fin m) k), IsCompact C ∧ ∀ g : GL (Fin m) k, l (ρ (corner g) v) ≠ 0 → ∃ u ∈ unipB k (Fin m), ∃ c ∈ C, g = u * c := by
  intro k _ _ _ _ ψ hψc hψ1 m V _ _ ρ hs hJ l hl v
  have hcm : ∀ g h : GL (Fin m) k, corner (g * h) = corner g * corner h := fun g h => by
    simp only [corner]
    rw [← map_mul, Prod.mk_mul_mk, mul_one]
  have hcc : Continuous (corner : GL (Fin m) k → GL (Fin (m + 1)) k) :=
    (continuous_leviEmb k _).comp ((continuous_leviTwo k).comp (continuous_id.prodMk continuous_const))
  have hdc : Continuous (diagT k (Fin m)) :=
    (continuous_leviEmb k _).comp (continuous_leviTorus k (Fin m))
  set X : Set V := (fun g => ρ g v) '' (corner '' (KO k (Fin m) : Set (GL (Fin m) k))) with hX
  have hXf : X.Finite := GlobalTheory.T.finite_image_of_isOpen_stabilizer_alt _ V ρ v (hs v) _ (GlobalTheory.SplitFlip.isCompact_KO.image hcc)
  choose r1 hr1 using GlobalTheory.T.whittaker_functional_torus_valuation_bound k ψ hψc hψ1 (m + 1) V ρ hs l hl
  have hlow : ∀ (x : V) (i : Fin m), ∃ r : kˣ, ∀ t : Fin (m + 1) → kˣ,
      l (ρ (diagT k (Fin (m + 1)) t) x) ≠ 0 → valuation k (r : k) ≤ valuation k ((t i.castSucc : k) / t i.succ) := by
    intro x i
    have hi := i.2
    have h : ∑ j, ![(i : ℕ) + 1, m - i] j = m + 1 := by
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      omega
    exact GlobalTheory.T.whittaker_torus_twKer_rootBound' k ψ hψc (m + 1) V ρ l hl _ _ h i.castSucc i.succ (by simp) (by simp) x
      (hJ _ _ h (Nat.succ_pos _) (by omega) x)
  choose r2 hr2 using hlow
  choose R1 R2 hR using fun x => GlobalTheory.T.exists_torus_bounds_of_consecutive_ratio_bounds k m (fun _ => r1 x) (r2 x)
  refine ⟨⋃ x ∈ X, diagT k (Fin m) '' {t : Fin m → kˣ | ∀ i, valuation k (R2 x : k) ≤ valuation k (t i : k) ∧
      valuation k (t i : k) ≤ valuation k (R1 x : k)} * (KO k (Fin m) : Set (GL (Fin m) k)),
    hXf.isCompact_biUnion fun x _ => ((GlobalTheory.T.isCompact_boundedTorus' k m (R1 x) (R2 x)).image hdc).mul GlobalTheory.SplitFlip.isCompact_KO,
    fun g hg => ?_⟩
  obtain ⟨u, hu, t, κ, hκ, rfl⟩ := GlobalTheory.T.exists_iwasawa_decomposition_upperUnitriangular_integral k m g
  have hcu := GlobalTheory.T.glCornerEmbedding_upperUnitriangular_superDiagonalSum k m u hu
  rw [hcm, hcm, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hl _ hcu.1, GlobalTheory.T.glCornerEmbedding_diagonalTorus_eq_snoc_one] at hg
  have hg' := right_ne_zero_of_mul hg
  have hxX : ρ (corner κ) v ∈ X := ⟨corner κ, ⟨κ, hκ, rfl⟩, rfl⟩
  have hlast : (Fin.snoc t 1 : Fin (m + 1) → kˣ) (Fin.last m) = 1 := Fin.snoc_last _ _
  have hb := hR _ _ hlast (fun i => ⟨hr2 _ i _ hg', hr1 _ _ i.castSucc i.succ (by simp) hg'⟩)
  refine ⟨u, hu, diagT k (Fin m) t * κ, Set.mem_biUnion hxX ⟨_, ⟨t, fun i => ?_, rfl⟩, κ, hκ, rfl⟩,
    mul_assoc _ _ _⟩
  have := hb i.castSucc
  simpa [Fin.snoc_castSucc] using this

end GlobalTheory.LocLanglands
end
end
end
