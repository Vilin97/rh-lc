module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalConverseGL
public import Development.DiscreteGroups.GlobalIrreducibility.LConv
public import Development.DiscreteGroups.GlobalIrreducibility.LConvBig
public import Development.DiscreteGroups.GlobalIrreducibility.LConvComm
public import Development.DiscreteGroups.GlobalIrreducibility.LConvCut
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.MapStdPoly
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.FinOfPI
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Development.DiscreteGroups.GlobalIrreducibility.LConvGen
public import Development.DiscreteGroups.GlobalIrreducibility.LConvGlue
public import Development.DiscreteGroups.GlobalIrreducibility.LConvIrr
public import Development.DiscreteGroups.GlobalIrreducibility.LConvKM
public import Development.DiscreteGroups.GlobalIrreducibility.LConvKir
public import Development.DiscreteGroups.GlobalIrreducibility.LConvSep
public import Development.DiscreteGroups.GlobalIrreducibility.LConvUnif
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Mathlib.Analysis.SpecialFunctions.Bernstein

-- Source module: Development.DiscreteGroups.GlobalIrreducibility.LConvDens

section

@[expose] public section

open scoped InnerProductSpace

noncomputable section

namespace DiscreteGroups.sglob.LConv

open CompanionTheory.D.gk.admitted

theorem irred_of_scalar {G : Type} [Group G] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (π : G →* (H →L[ℂ] H)) (hπ : ∀ g x, ‖π g x‖ = ‖x‖)
    (hsc : ∀ T : H →L[ℂ] H, (∀ g, T * π g = π g * T) → ∃ c : ℂ, T = c • (1 : H →L[ℂ] H))
    (S : Submodule ℂ H) (hcl : IsClosed (S : Set H)) (hS : ∀ g, ∀ v ∈ S, π g v ∈ S) : S = ⊥ ∨ S = ⊤ := by
  have : CompleteSpace S := hcl.completeSpace_coe
  have hcomm : ∀ g, S.starProjection * π g = π g * S.starProjection := by
    intro g
    ext z
    show S.starProjection (π g z) = π g (S.starProjection z)
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    · exact hS g _ (S.starProjection_apply_mem z)
    · intro w hw
      rw [← map_sub, FinOfPIAux.inner_left π hπ]
      exact S.starProjection_inner_eq_zero z _ (hS _ _ hw)
  obtain ⟨c, hc⟩ := hsc _ hcomm
  have hP : ∀ z, S.starProjection z = c • z := fun z => by rw [hc]; rfl
  by_cases h0 : S = ⊥
  · exact Or.inl h0
  · right
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
    have h1 : c • x = x := by rw [← hP, Submodule.starProjection_eq_self_iff.mpr hx]
    have hc1 : c = 1 := by
      have h2 : (c - 1) • x = 0 := by rw [sub_smul, h1, one_smul, sub_self]
      rcases smul_eq_zero.mp h2 with h | h
      · exact sub_eq_zero.mp h
      · exact absurd h hx0
    rw [eq_top_iff]
    intro z _
    have h3 := S.starProjection_apply_mem z
    rwa [hP, hc1, one_smul] at h3

theorem word_eq_mul_prod {R : Type*} [Ring R] (e : R) (he : e * e = e) (l : List R) :
    word e l = e * (l.map fun a => e * a * e).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [word_cons, ih, List.map_cons, List.prod_cons, ← mul_assoc, he]

theorem finiteOfAlt : FiniteOfAlt := by
  intro G _ H _ _ _ π hπ hsc e he d hd
  have h : ∀ g : Fin d → G, stdPoly e (fun i => π (g i)) = 0 := by
    intro g
    have h0 := congrArg (fun X => e * X) (hd g)
    simp only [mul_zero] at h0
    rw [← h0, stdPoly, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [word_eq_mul_prod e he, List.map_ofFn, mul_smul_comm, Int.cast_smul_eq_zsmul, zsmul_eq_mul]
    rfl
  obtain ⟨hfd, -⟩ := finite_rank_of_irreducible_unitary G H π hπ (irred_of_scalar π hπ hsc) e d h
  obtain ⟨s, hs⟩ := (Submodule.fg_iff_finiteDimensional _).mpr hfd
  refine ⟨s, fun x => ?_⟩
  rw [hs]
  exact LinearMap.mem_range_self (e : H →ₗ[ℂ] H) x

end DiscreteGroups.sglob.LConv

end
end
end

-- Source module: Development.DiscreteGroups.GlobalIrreducibility.LConvUnitOf

section

@[expose] public section

noncomputable section

open ValuativeRel

namespace DiscreteGroups.sglob.LConv

theorem countable_quotient_of_isOpen {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [TopologicalSpace.SeparableSpace G] (K : Subgroup G) (hK : IsOpen (K : Set G)) : Countable (G ⧸ K) := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense G
  have : Countable D := hDc.to_subtype
  refine Function.Surjective.countable (f := fun d : D => ((d : G) : G ⧸ K)) fun q => ?_
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  have ho : IsOpen ((fun x => x⁻¹ * g) ⁻¹' (K : Set G)) := hK.preimage (continuous_inv.mul continuous_const)
  obtain ⟨d, hd, hdD⟩ := hDd.inter_open_nonempty _ ho ⟨g, by simp⟩
  exact ⟨⟨d, hdD⟩, QuotientGroup.eq.2 hd⟩

theorem separableSpace_GL (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (m : ℕ) : TopologicalSpace.SeparableSpace (GL (Fin m) k) := by
  have : SecondCountableTopology (GL (Fin m) k) := inferInstance
  infer_instance

theorem unitOfUnif : UnitOfUnif := by
  intro hAlt hFin hUnif k _ _ _ _ m K hKo hKc H _ _ _ π hπ hcomm
  have := separableSpace_GL k m
  obtain ⟨N, hN⟩ := hUnif k m K hKo
  let F : Submodule ℂ H :=
    { carrier := {x | ∀ κ ∈ K, π κ x = x}
      add_mem' := fun {a b} ha hb κ hκ => by rw [map_add (f := _), ha κ hκ, hb κ hκ]
      zero_mem' := fun κ _ => map_zero _
      smul_mem' := fun c x hx κ hκ => by rw [map_smul, hx κ hκ] }
  have hF : IsClosed (F : Set H) := by
    have : (F : Set H) = ⋂ κ ∈ K, {x | π κ x = x} := by
      ext x
      simp only [Set.mem_iInter]
      rfl
    rw [this]
    exact isClosed_biInter fun κ _ => isClosed_eq (π κ).continuous continuous_id
  have : CompleteSpace F := hF.completeSpace_coe
  have h1 : ∀ x, F.starProjection x ∈ F := fun x => F.starProjection_apply_mem x
  have h2 : ∀ x ∈ F, F.starProjection x = x := fun x hx => Submodule.starProjection_eq_self_iff.2 hx
  obtain ⟨s, hs⟩ := hFin _ H π hπ hcomm F.starProjection (by ext x; exact h2 _ (h1 x)) (N ^ 2 + 1)
    (hAlt _ K hKo hKc (countable_quotient_of_isOpen K hKo) N hN H π hπ F.starProjection
      (isSelfAdjoint_starProjection F) h1 h2 _ (Nat.lt_succ_self _))
  exact ⟨s, fun x hx => h2 x hx ▸ hs x⟩

end DiscreteGroups.sglob.LConv

end
end
end

-- Source module: Development.DiscreteGroups.GlobalIrreducibility.LConvFinal

section

@[expose] public section

namespace DiscreteGroups.sglob.LConv

theorem localConverseGL : GlobalTheory.Published.LocalConverseGL :=
  localConverseGL_of_leaves cuspGen kirBump bigCell extremeExists extremeIrred sepOfExtreme commBound unifOfComm
    altIdentity finiteOfAlt unitOfUnif glue

end DiscreteGroups.sglob.LConv
end
end
