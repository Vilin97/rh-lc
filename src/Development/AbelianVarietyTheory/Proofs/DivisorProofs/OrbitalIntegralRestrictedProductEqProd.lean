module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumDoubleCosetEqFinprodLocalSumsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupAverageComponentwiseSubgroupEqProd
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroOfSubsetCpt
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.GroupTheory.Index
public import Mathlib.Order.Filter.Cofinite
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralTwistedConjInvariant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralSummandGoodPlaceIndicator
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupAverageComponentwiseSubgroupEqProdStatement

section

@[expose] public section

open Filter GlobalTheory.BCT
open scoped Classical

theorem _root_.GlobalTheory.T.groupAverage_componentwiseSubgroup_eq_prod : ∀ (ι G : Type) [Group G] (H : ι → Type) [∀ i, Group (H i)] (p : ∀ i, G →* H i) (K : Subgroup G) (KH : ∀ i, Subgroup (H i)) (hK : ∀ x : G, x ∈ K ↔ ∀ i, p i x ∈ KH i) (u : ∀ i, KH i → ℂ), (∀ y : ∀ i, H i, (∀ᶠ i in cofinite, y i ∈ KH i) → ∃ x : G, ∀ i, p i x = y i) → (∀ i, (rStab (u i)).index ≠ 0) → (∀ᶠ i in cofinite, ∀ k, u i k = 1) → avg (fun k : K => ∏ᶠ i, u i ⟨p i k, (hK k).1 k.2 i⟩) = ∏ᶠ i, avg (u i) := by
  first | exact @GlobalTheory.AvgRestr.avg_restrProd | exact GlobalTheory.AvgRestr.avg_restrProd | (intros; apply GlobalTheory.AvgRestr.avg_restrProd <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCompactPartCentralizerIffLocal

section

@[expose] public section

open Filter GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.BCT

theorem mem_cptPart_iff_local (ι G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (H : ι → Type)
    [∀ i, Group (H i)] [∀ i, TopologicalSpace (H i)] [∀ i, IsTopologicalGroup (H i)] [∀ i, T2Space (H i)]
    (p : ∀ i, G →* H i) (KH : ∀ i, Subgroup (H i)) (T : Subgroup G) (TH : ∀ i, Subgroup (H i)) :
    (∀ i, Continuous (p i)) → (∀ x : G, ∀ᶠ i in cofinite, p i x ∈ KH i) →
    (∀ C : ∀ i, Set (H i), (∀ i, IsCompact (C i)) → (∀ᶠ i in cofinite, C i = KH i) →
      IsCompact {x : G | ∀ i, p i x ∈ C i}) →
    (∀ i, IsCompact (KH i : Set (H i))) → (∀ x, x ∈ T ↔ ∀ i, p i x ∈ TH i) →
    (∀ i, ∀ a ∈ TH i, ∀ b ∈ TH i, a * b = b * a) →
    ∀ x, x ∈ cptPart T ↔ x ∈ T ∧ ∀ i, p i x ∈ cptPart (TH i) := by
  intro hp hcof hcpt hKH hT hcomm x
  constructor
  · intro hx
    have hle : cptPart T ≤ T ⊓ ⨅ i, (cptPart (TH i)).comap (p i) := by
      rw [cptPart, Subgroup.closure_le]
      intro t ht
      obtain ⟨htT, htc⟩ := ht
      rw [SetLike.mem_coe, Subgroup.mem_inf, Subgroup.mem_iInf]
      refine ⟨htT, fun i => ?_⟩
      rw [Subgroup.mem_comap]
      refine Subgroup.subset_closure (k := {s | s ∈ TH i ∧ IsCompact (closure (Subgroup.zpowers s : Set (H i)))})
        ⟨(hT t).1 htT i, ?_⟩
      have himc : IsCompact (p i '' closure (Subgroup.zpowers t : Set G)) := htc.image (hp i)
      refine himc.of_isClosed_subset isClosed_closure (closure_minimal ?_ himc.isClosed)
      rintro _ ⟨k, rfl⟩
      exact ⟨t ^ k, subset_closure ⟨k, rfl⟩, by simp⟩
    have := hle hx
    simp only [Subgroup.mem_inf, Subgroup.mem_iInf, Subgroup.mem_comap] at this
    exact this
  · rintro ⟨hxT, hxi⟩
    have hloc : ∀ i, IsCompact (closure (Subgroup.zpowers (p i x) : Set (H i))) := fun i =>
      (GlobalTheory.LocFinU.cptPart_subset_of_comm (TH i) (hcomm i) (hxi i)).2
    set C : ∀ i, Set (H i) := fun i => if p i x ∈ KH i then (KH i : Set (H i))
      else closure (Subgroup.zpowers (p i x) : Set (H i)) with hC
    have hCc : ∀ i, IsCompact (C i) := by
      intro i
      simp only [hC]
      split_ifs
      · exact hKH i
      · exact hloc i
    have hCf : ∀ᶠ i in cofinite, C i = KH i := by
      filter_upwards [hcof x] with i hi
      simp [hC, hi]
    have hS := hcpt C hCc hCf
    have hScl : IsClosed {y : G | ∀ i, p i y ∈ C i} := by
      have : {y : G | ∀ i, p i y ∈ C i} = ⋂ i, p i ⁻¹' C i := by ext; simp
      rw [this]
      exact isClosed_iInter fun i => (hCc i).isClosed.preimage (hp i)
    have hsub : (Subgroup.zpowers x : Set G) ⊆ {y : G | ∀ i, p i y ∈ C i} := by
      rintro _ ⟨k, rfl⟩ i
      simp only [hC, map_zpow]
      split_ifs with h
      · exact (KH i).zpow_mem h k
      · exact subset_closure ⟨k, rfl⟩
    refine Subgroup.subset_closure (k := {s | s ∈ T ∧ IsCompact (closure (Subgroup.zpowers s : Set G))}) ⟨hxT, ?_⟩
    exact hS.of_isClosed_subset isClosed_closure (closure_minimal hsub hScl)

end GlobalTheory.BCT
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCompactPartCentralizerIffLocalStatement

section

@[expose] public section

open Filter GlobalTheory.BCT
open scoped Classical

theorem _root_.GlobalTheory.T.mem_compactPart_centralizer_iff_local : ∀ (ι G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (H : ι → Type) [∀ i, Group (H i)] [∀ i, TopologicalSpace (H i)] [∀ i, IsTopologicalGroup (H i)] [∀ i, T2Space (H i)] (p : ∀ i, G →* H i) (KH : ∀ i, Subgroup (H i)) (T : Subgroup G) (TH : ∀ i, Subgroup (H i)), (∀ i, Continuous (p i)) → (∀ x : G, ∀ᶠ i in cofinite, p i x ∈ KH i) → (∀ C : ∀ i, Set (H i), (∀ i, IsCompact (C i)) → (∀ᶠ i in cofinite, C i = KH i) → IsCompact {x : G | ∀ i, p i x ∈ C i}) → (∀ i, IsCompact (KH i : Set (H i))) → (∀ x, x ∈ T ↔ ∀ i, p i x ∈ TH i) → (∀ i, ∀ a ∈ TH i, ∀ b ∈ TH i, a * b = b * a) → ∀ x, x ∈ cptPart T ↔ x ∈ T ∧ ∀ i, p i x ∈ cptPart (TH i) := by
  first | exact @GlobalTheory.BCT.mem_cptPart_iff_local | exact GlobalTheory.BCT.mem_cptPart_iff_local | (intros; apply GlobalTheory.BCT.mem_cptPart_iff_local <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexInfConjEqFinprodRestrictedProduct

section

@[expose] public section

open Filter
open scoped Classical

namespace GlobalTheory

theorem relIndex_inf_conj_eq_finprod_of_restricted_product
    (ι G : Type) [Group G] (H : ι → Type) [∀ i, Group (H i)] (p : ∀ i, G →* H i)
    (K T C : Subgroup G) (KH TH CH : ∀ i, Subgroup (H i)) (g : G)
    (hglue : ∀ y : ∀ i, H i, (∀ᶠ i in cofinite, y i ∈ KH i) → ∃ x : G, ∀ i, p i x = y i)
    (hcof : ∀ x : G, ∀ᶠ i in cofinite, p i x ∈ KH i)
    (hK : ∀ x : G, x ∈ K ↔ ∀ i, p i x ∈ KH i)
    (hT : ∀ x, x ∈ T ↔ ∀ i, p i x ∈ TH i)
    (hC : ∀ x, x ∈ C ↔ x ∈ T ∧ ∀ i, p i x ∈ CH i)
    (hCT : ∀ i, CH i ≤ TH i)
    (_hloc : ∀ i, TH i ⊓ (KH i).map (MulAut.conj (p i g)).toMonoidHom ≤ CH i ∧
      (TH i ⊓ (KH i).map (MulAut.conj (p i g)).toMonoidHom).relIndex (CH i) ≠ 0)
    (hCK : ∀ᶠ i in cofinite, CH i ≤ KH i) :
    (T ⊓ K.map (MulAut.conj g).toMonoidHom).relIndex C =
      ∏ᶠ i, (TH i ⊓ (KH i).map (MulAut.conj (p i g)).toMonoidHom).relIndex (CH i) := by
  have hfin : {i | ¬ (p i g ∈ KH i ∧ CH i ≤ KH i)}.Finite :=
    Filter.eventually_cofinite.1 ((hcof g).and hCK)
  set S : Finset ι := hfin.toFinset with hS
  have hSn : ∀ i, i ∉ S → p i g ∈ KH i ∧ CH i ≤ KH i := by
    intro i hi
    by_contra h
    exact hi (hfin.mem_toFinset.2 h)
  have hmem : ∀ i (y : H i), y ∈ (KH i).map (MulAut.conj (p i g)).toMonoidHom ↔
      (p i g)⁻¹ * y * p i g ∈ KH i := by
    intro i y
    rw [Subgroup.mem_map_equiv]
    simp
  have hmemG : ∀ x : G, x ∈ K.map (MulAut.conj g).toMonoidHom ↔
      ∀ i, (p i g)⁻¹ * p i x * p i g ∈ KH i := by
    intro x
    rw [Subgroup.mem_map_equiv, hK]
    simp
  have hle : ∀ i, i ∉ S → CH i ≤ TH i ⊓ (KH i).map (MulAut.conj (p i g)).toMonoidHom := by
    intro i hi y hy
    obtain ⟨h1, h2⟩ := hSn i hi
    exact ⟨hCT i hy, (hmem i y).2 (mul_mem (mul_mem (inv_mem h1) (h2 hy)) h1)⟩
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := S)]
  swap
  · intro i hi
    by_contra h
    exact hi (Subgroup.relIndex_eq_one.2 (hle i h))
  let φ : C →* (∀ i : S, CH i) :=
    { toFun := fun x i => ⟨p i x, ((hC x).1 x.2).2 i⟩
      map_one' := by ext i; simp
      map_mul' := by intro x y; ext i; simp }
  have hφ : Function.Surjective φ := by
    intro y
    obtain ⟨x, hx⟩ := hglue (fun i => if h : i ∈ S then (y ⟨i, h⟩ : H i) else 1) (by
      refine Filter.eventually_cofinite.2 (S.finite_toSet.subset ?_)
      intro i hi
      by_contra h
      apply hi
      have h' : i ∉ S := h
      simp [h'])
    have hxC : ∀ i, p i x ∈ CH i := by
      intro i
      rw [hx]
      split_ifs with h
      · exact (y ⟨i, h⟩).2
      · exact one_mem _
    refine ⟨⟨x, (hC x).2 ⟨(hT x).2 fun i => hCT i (hxC i), hxC⟩⟩, ?_⟩
    funext i
    apply Subtype.ext
    show p i x = _
    rw [hx]
    simp
  have hcomap : (T ⊓ K.map (MulAut.conj g).toMonoidHom).subgroupOf C =
      (Subgroup.pi Set.univ (fun i : S =>
        (TH i ⊓ (KH i).map (MulAut.conj (p i g)).toMonoidHom).subgroupOf (CH i))).comap φ := by
    ext x
    have hx := (hC x).1 x.2
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.mem_pi, Subgroup.mem_inf, hmemG]
    constructor
    · rintro ⟨h1, h2⟩ i _
      exact ⟨(hT x).1 h1 i, (hmem i _).2 (h2 i)⟩
    · intro h
      refine ⟨hx.1, fun i => ?_⟩
      by_cases hi : i ∈ S
      · exact (hmem i _).1 (h ⟨i, hi⟩ trivial).2
      · exact (hmem i _).1 (hle i hi (hx.2 i)).2
  have hpi : ∀ L : ∀ i : S, Subgroup (CH i),
      (Subgroup.pi Set.univ L).index = ∏ i, (L i).index := by
    intro L
    simp_rw [Subgroup.index, ← Nat.card_pi]
    refine Nat.card_congr
      ((Quotient.congrRight (fun x y ↦ ?_)).trans (Setoid.piQuotientEquiv _).symm)
    rw [QuotientGroup.leftRel_pi]
  rw [Subgroup.relIndex, hcomap, Subgroup.index_comap_of_surjective _ hφ, hpi,
    ← Finset.prod_coe_sort S]
  rfl

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexInfConjEqFinprodRestrictedProductStatement

section

@[expose] public section

open Filter
open scoped Classical

theorem _root_.GlobalTheory.T.relIndex_inf_conj_eq_finprod_restrictedProduct : ∀ (ι G : Type) [Group G] (H : ι → Type) [∀ i, Group (H i)] (p : ∀ i, G →* H i) (K T C : Subgroup G) (KH TH CH : ∀ i, Subgroup (H i)) (g : G), (∀ y : ∀ i, H i, (∀ᶠ i in cofinite, y i ∈ KH i) → ∃ x : G, ∀ i, p i x = y i) → (∀ x : G, ∀ᶠ i in cofinite, p i x ∈ KH i) → (∀ x : G, x ∈ K ↔ ∀ i, p i x ∈ KH i) → (∀ x, x ∈ T ↔ ∀ i, p i x ∈ TH i) → (∀ x, x ∈ C ↔ x ∈ T ∧ ∀ i, p i x ∈ CH i) → (∀ i, CH i ≤ TH i) → (∀ i, TH i ⊓ (KH i).map (MulAut.conj (p i g)).toMonoidHom ≤ CH i ∧ (TH i ⊓ (KH i).map (MulAut.conj (p i g)).toMonoidHom).relIndex (CH i) ≠ 0) → (∀ᶠ i in cofinite, CH i ≤ KH i) → (T ⊓ K.map (MulAut.conj g).toMonoidHom).relIndex C = ∏ᶠ i, (TH i ⊓ (KH i).map (MulAut.conj (p i g)).toMonoidHom).relIndex (CH i) := by
  first | exact @GlobalTheory.relIndex_inf_conj_eq_finprod_of_restricted_product | exact GlobalTheory.relIndex_inf_conj_eq_finprod_of_restricted_product | (intros; apply GlobalTheory.relIndex_inf_conj_eq_finprod_of_restricted_product <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralSummandGoodPlaceIndicatorStatement

section

@[expose] public section

open Filter GlobalTheory.BCT
open scoped Classical

theorem _root_.GlobalTheory.T.twistedOrbitalIntegralSummand_goodPlace_indicator : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (KH : Subgroup H) (δ : H), δ ∈ KH → cptPart (twCent (MonoidHom.id H) δ) ≤ KH → (∀ g : H, g⁻¹ * δ * g ∈ KH → ∃ t ∈ twCent (MonoidHom.id H) δ, t⁻¹ * g ∈ KH) → ∀ x : H, GlobalTheory.TwOrbConj.summand (MonoidHom.id H) KH δ ((KH : Set H).indicator 1) x = if ∃ t ∈ twCent (MonoidHom.id H) δ, ∃ k ∈ KH, x = t * k then 1 else 0 := by
  first | exact @GlobalTheory.TwOrbGood.summand_goodplace | exact GlobalTheory.TwOrbGood.summand_goodplace | (intros; apply GlobalTheory.TwOrbGood.summand_goodplace <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalIntegralRestrictedProductEqProd

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RestrProd

theorem twOrb_restrProd : ∀ (ι G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (H : ι → Type) [∀ i, Group (H i)] [∀ i, TopologicalSpace (H i)] [∀ i, IsTopologicalGroup (H i)] [∀ i, T2Space (H i)] (p : ∀ i, G →* H i) (K : Subgroup G) (KH : ∀ i, Subgroup (H i)) (δ : G) (f : ∀ i, H i → ℂ), (∀ i, Continuous (p i)) → (∀ x y : G, (∀ i, p i x = p i y) → x = y) → (∀ y : ∀ i, H i, (∀ᶠ i in cofinite, y i ∈ KH i) → ∃ x : G, ∀ i, p i x = y i) → (∀ x : G, ∀ᶠ i in cofinite, p i x ∈ KH i) → (∀ x : G, x ∈ K ↔ ∀ i, p i x ∈ KH i) → (∀ C : ∀ i, Set (H i), (∀ i, IsCompact (C i)) → (∀ᶠ i in cofinite, C i = KH i) → IsCompact {x : G | ∀ i, p i x ∈ C i}) → (∀ i, IsCompact (KH i : Set (H i))) → (∀ i, ∀ a ∈ twCent (MonoidHom.id (H i)) (p i δ), ∀ b ∈ twCent (MonoidHom.id (H i)) (p i δ), a * b = b * a) → (∀ i (x : H i), twCent (MonoidHom.id (H i)) (p i δ) ⊓ (KH i).map (MulAut.conj x).toMonoidHom ≤ cptPart (twCent (MonoidHom.id (H i)) (p i δ)) ∧ (twCent (MonoidHom.id (H i)) (p i δ) ⊓ (KH i).map (MulAut.conj x).toMonoidHom).relIndex (cptPart (twCent (MonoidHom.id (H i)) (p i δ))) ≠ 0) → (∀ i (x : H i), (rStab fun k : KH i => f i ((x * k)⁻¹ * p i δ * (x * k))).index ≠ 0) → (∀ i, {q : DoubleCoset.Quotient (twCent (MonoidHom.id (H i)) (p i δ) : Set (H i)) (KH i : Set (H i)) | ∃ k ∈ KH i, f i ((Quotient.out q * k)⁻¹ * p i δ * (Quotient.out q * k)) ≠ 0}.Finite) → (∀ᶠ i in cofinite, p i δ ∈ KH i ∧ f i = (KH i : Set (H i)).indicator 1 ∧ (∀ g : H i, g⁻¹ * p i δ * g ∈ KH i → ∃ t ∈ twCent (MonoidHom.id (H i)) (p i δ), t⁻¹ * g ∈ KH i) ∧ cptPart (twCent (MonoidHom.id (H i)) (p i δ)) ≤ KH i) → twOrb (MonoidHom.id G) K δ (fun x => ∏ᶠ i, f i (p i x)) = ∏ᶠ i, twOrb (MonoidHom.id (H i)) (KH i) (p i δ) (f i) := by
  intro ι G _ _ _ H _ _ _ _ p K KH δ f hpc hinj hglue hfin hK hcpt hKc hcomm hloc hstab hsupp hgood
  have hT : ∀ x, x ∈ twCent (MonoidHom.id G) δ ↔ ∀ i, p i x ∈ twCent (MonoidHom.id (H i)) (p i δ) := by
    intro x
    simp only [GlobalTheory.TwOrbConj.mem_twCent, MonoidHom.id_apply]
    constructor
    · intro h i
      rw [← map_mul, h, map_mul]
    · intro h
      apply hinj
      intro i
      rw [map_mul, h i, map_mul]
  have hC := GlobalTheory.T.mem_compactPart_centralizer_iff_local ι G H p KH _ _ hpc hfin hcpt hKc hT hcomm
  have hCT : ∀ i, cptPart (twCent (MonoidHom.id (H i)) (p i δ)) ≤ twCent (MonoidHom.id (H i)) (p i δ) :=
    fun i => (Subgroup.closure_le _).2 (fun t ht => ht.1)
  have havg1 : ∀ (M : Type) [Group M], avg (fun _ : M => (1 : ℂ)) = 1 := by
    intro M _
    have hR : rStab (fun _ : M => (1 : ℂ)) = ⊤ := by
      ext k
      simp [GlobalTheory.TwOrbConj.mem_rStab]
    unfold avg
    rw [hR, Subgroup.index_top]
    haveI : Subsingleton (M ⧸ (⊤ : Subgroup M)) := QuotientGroup.subsingleton_quotient_top
    haveI : Unique (M ⧸ (⊤ : Subgroup M)) := uniqueOfSubsingleton (QuotientGroup.mk 1)
    simp [finsum_unique]
  have hs : ∀ g, GlobalTheory.TwOrbConj.summand (MonoidHom.id G) K δ (fun x => ∏ᶠ i, f i (p i x)) g =
      ∏ᶠ i, GlobalTheory.TwOrbConj.summand (MonoidHom.id (H i)) (KH i) (p i δ) (f i) (p i g) := by
    intro g
    have hrel := GlobalTheory.T.relIndex_inf_conj_eq_finprod_restrictedProduct ι G H p K _ _ KH _ _ g hglue hfin hK hT hC hCT (fun i => hloc i (p i g))
      (hgood.mono fun i h => h.2.2.2)
    have hu1 : ∀ᶠ i in cofinite, ∀ k : KH i, f i ((p i g * k)⁻¹ * p i δ * (p i g * k)) = 1 := by
      filter_upwards [hgood, hfin g] with i h hg k
      rw [h.2.1]
      apply Set.indicator_of_mem
      exact (KH i).mul_mem ((KH i).mul_mem ((KH i).inv_mem ((KH i).mul_mem hg k.2)) h.1) ((KH i).mul_mem hg k.2)
    have havg := GlobalTheory.T.groupAverage_componentwiseSubgroup_eq_prod ι G H p K KH hK (fun i k => f i ((p i g * k)⁻¹ * p i δ * (p i g * k))) hglue
      (fun i => hstab i (p i g)) hu1
    have hr1 : ∀ᶠ i in cofinite, (((twCent (MonoidHom.id (H i)) (p i δ) ⊓ (KH i).map (MulAut.conj (p i g)).toMonoidHom).relIndex
        (cptPart (twCent (MonoidHom.id (H i)) (p i δ))) : ℕ) : ℂ) = 1 := by
      filter_upwards [hgood, hfin g] with i h hg
      rw [GlobalTheory.TwOrbConj.map_conj_self _ hg, Subgroup.relIndex_eq_one.2 (le_inf (hCT i) h.2.2.2), Nat.cast_one]
    have ha1 : ∀ᶠ i in cofinite, avg (fun k : KH i => f i ((p i g * k)⁻¹ * p i δ * (p i g * k))) = 1 := by
      filter_upwards [hu1] with i h
      rw [show (fun k : KH i => f i ((p i g * k)⁻¹ * p i δ * (p i g * k))) = fun _ => 1 from funext h]
      exact havg1 _
    have e1 : avg (fun k : K => ∏ᶠ i, f i (p i ((g * ↑k)⁻¹ * δ * (MonoidHom.id G) (g * ↑k)))) =
        ∏ᶠ i, avg (fun k : KH i => f i ((p i g * k)⁻¹ * p i δ * (p i g * k))) := by
      rw [← havg]
      congr 1
      funext k
      simp [map_mul, map_inv]
    unfold GlobalTheory.TwOrbConj.summand
    simp only [MonoidHom.id_apply] at e1 ⊢
    have hN : Function.HasFiniteMulSupport fun i => (twCent (MonoidHom.id (H i)) (p i δ) ⊓
        (KH i).map (MulAut.conj (p i g)).toMonoidHom).relIndex (cptPart (twCent (MonoidHom.id (H i)) (p i δ))) := by
      have : ∀ᶠ i in cofinite, (twCent (MonoidHom.id (H i)) (p i δ) ⊓
          (KH i).map (MulAut.conj (p i g)).toMonoidHom).relIndex (cptPart (twCent (MonoidHom.id (H i)) (p i δ))) = 1 := by
        filter_upwards [hgood, hfin g] with i h hg
        rw [GlobalTheory.TwOrbConj.map_conj_self _ hg, Subgroup.relIndex_eq_one.2 (le_inf (hCT i) h.2.2.2)]
      exact Filter.eventually_cofinite.1 this
    have hcast := map_finprod (Nat.castRingHom ℂ) hN
    simp only [eq_natCast] at hcast
    rw [e1, hrel, hcast, ← finprod_mul_distrib (Filter.eventually_cofinite.1 hr1) (Filter.eventually_cofinite.1 ha1)]
  rw [GlobalTheory.TwOrbConj.twOrb_eq]
  simp only [GlobalTheory.TwOrbConj.twOrb_eq]
  refine GlobalTheory.T.finsum_doubleCoset_eq_finprod_local_sums ι G H p _ K _ KH _ _ hglue hfin hK hT ?_ ?_ ?_ hs
  · intro i t ht k hk x
    exact GlobalTheory.TwOrbConj.summand_rep _ _ _ _ x ht hk
  · intro i
    refine (hsupp i).subset ?_
    intro q hq
    by_contra hcon
    apply hq
    have h0 : (fun k : KH i => f i ((Quotient.out q * k)⁻¹ * p i δ * (MonoidHom.id (H i)) (Quotient.out q * k))) =
        fun _ => 0 := by
      funext k
      by_contra hk
      exact hcon ⟨k, k.2, hk⟩
    unfold GlobalTheory.TwOrbConj.summand
    rw [h0]
    simp [avg]
  · filter_upwards [hgood] with i h x
    rw [h.2.1]
    exact GlobalTheory.T.twistedOrbitalIntegralSummand_goodPlace_indicator (H i) (KH i) (p i δ) h.1 h.2.2.2 h.2.2.1 x

end GlobalTheory.RestrProd
end
end
end
