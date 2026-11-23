module

public import Formalism.SharpRestriction.GrowthBounds.CovariantDegrees
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.OperatorsKillInvariantProjection
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.BinomialPreservesDiagonalStable
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.EquivariantInjectiveOfCyclic
import Formalism.SharpRestriction.GrowthBounds.RootWeights.InvariantProjectionRangeTrivial
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.EquivariantKillsCyclicOfZero
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.CyclicSubmoduleIsSubrepresentation
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.WeightProjectionDiagonalApplyEqSmul
import Formalism.SharpRestriction.GrowthBounds.RootWeights.WeightSpaceEqBotOutsideSupport
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.GrowthBounds.RootWeights.WeightProjectionDiagonalApplyEqSmul

-- Source module: Formalism.SharpRestriction.GrowthBounds.RootWeights.SchurInvariantProjectionTrace

section

@[expose] public section

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem exists_equivariant_cyclic_to_hwv (D : Formalism.BasicNotions.D7) (h2 : adm2 D) {n : ℕ} {K V : Type} [Field K] [CharZero K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (E : GLOps n K V) (hE : IsGLRep E) (lam : Fin n → ℤ)
    (v0 v : V) (hv0 : IsHWV E lam v0) (hv : IsHWV E lam v) (hL : IsSubrepresentation E (cyclicSubmodule E v0)) :
    ∃ φ : cyclicSubmodule E v0 →ₗ[K] V, IsEquivariantMap (restrictRepresentation E _ hL) E φ ∧ φ ⟨v0, self_mem_cyclicSubmodule E v0⟩ = v := by
  have hP := prodRepresentation_isRep E E hE hE
  have hg : IsHWV (prodRepresentation E E) lam (v0, v) := by
    refine ⟨fun h => hv0.1 (congrArg Prod.fst h), (prod_mem_weightSpace_iff E E lam _).2 ⟨hv0.2.1, hv.2.1⟩, fun a b hab => ?_⟩
    rw [prodRepresentation_apply, hv0.2.2 a b hab, hv.2.2 a b hab]; rfl
  have hΓ := cyclicSubmodule_isSubrepresentation (prodRepresentation E E) (v0, v)
  have hEΓ := restrictRepresentation_isRep (prodRepresentation E E) hP _ hΓ
  have hg' := highest_vector_restrict (prodRepresentation E E) _ hΓ lam (v0, v) (self_mem_cyclicSubmodule _ _) hg
  have hcyc := cyclicSubmodule_restrict_eq_top (prodRepresentation E E) (v0, v) hΓ
  let F : cyclicSubmodule (prodRepresentation E E) (v0, v) →ₗ[K] V := (LinearMap.fst K V V) ∘ₗ (Submodule.subtype _)
  let S2 : cyclicSubmodule (prodRepresentation E E) (v0, v) →ₗ[K] V := (LinearMap.snd K V V) ∘ₗ (Submodule.subtype _)
  have hF : IsEquivariantMap (restrictRepresentation (prodRepresentation E E) _ hΓ) E F := fun a b x => rfl
  have hS : IsEquivariantMap (restrictRepresentation (prodRepresentation E E) _ hΓ) E S2 := fun a b x => rfl
  have hker := equivariant_injective_of_cyclic D h2 _ hEΓ E lam _ hg' hcyc F hF hv0.1
  have hinj : Function.Injective F := LinearMap.ker_eq_bot.1 hker
  have hrange : LinearMap.range F = cyclicSubmodule E v0 := by
    have := equivariant_map_cyclicSubmodule _ E F hF ⟨(v0, v), self_mem_cyclicSubmodule _ _⟩
    rw [hcyc, Submodule.map_top] at this
    exact this
  have hmem : ∀ z, F z ∈ cyclicSubmodule E v0 := fun z => by rw [← hrange]; exact ⟨z, rfl⟩
  let e : cyclicSubmodule (prodRepresentation E E) (v0, v) ≃ₗ[K] cyclicSubmodule E v0 :=
    LinearEquiv.ofBijective (F.codRestrict _ hmem)
      ⟨fun x y hxy => hinj (congrArg Subtype.val hxy), fun y => by
        have hy : (y : V) ∈ LinearMap.range F := by rw [hrange]; exact y.2
        obtain ⟨z, hz⟩ := hy
        exact ⟨z, Subtype.ext hz⟩⟩
  have he : ∀ z, ((e z : cyclicSubmodule E v0) : V) = F z := fun z => rfl
  refine ⟨S2 ∘ₗ e.symm.toLinearMap, fun a b y => ?_, ?_⟩
  · obtain ⟨z, rfl⟩ := e.surjective y
    have h1 : restrictRepresentation E _ hL a b (e z) = e (restrictRepresentation (prodRepresentation E E) _ hΓ a b z) := Subtype.ext rfl
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [h1, e.symm_apply_apply, e.symm_apply_apply]
    exact hS a b z
  · have h1 : (⟨v0, self_mem_cyclicSubmodule E v0⟩ : cyclicSubmodule E v0) = e ⟨(v0, v), self_mem_cyclicSubmodule _ _⟩ := Subtype.ext rfl
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [h1, e.symm_apply_apply]
    rfl

def trivialRepresentation (n : ℕ) (K : Type) [Field K] : GLOps n K K := fun _ _ => 0

theorem trivialRepresentation_isRep (n : ℕ) (K : Type) [Field K] : IsGLRep (trivialRepresentation n K) := by
  refine ⟨?_, fun x => ⟨⊤, inferInstance, trivial, fun _ _ _ _ => trivial⟩, ?_⟩
  · intro a b c d
    simp only [trivialRepresentation]
    split_ifs <;> simp
  · rw [eq_top_iff]
    intro x _
    exact Submodule.mem_iSup_of_mem 0 ((mem_weightSp_iff_diagonal_apply _ _ _).2 fun a => by simp [trivialRepresentation])

theorem trivialRep_invariant_projection (n : ℕ) (K : Type) [Field K] [CharZero K] : IsInvProj (trivialRepresentation n K) 1 := by
  refine ⟨fun x _ => rfl, fun mu hmu x hx => ?_⟩
  have hle : isoSub (trivialRepresentation n K) mu ≤ ⊥ := by
    refine Submodule.span_le.2 ?_
    rintro y ⟨u, _, v, hv, _⟩
    exfalso
    obtain ⟨i, hi⟩ : ∃ i, mu i ≠ 0 := by
      by_contra hcon
      exact hmu (funext fun i => by_contra fun h => hcon ⟨i, h⟩)
    have h1 := (mem_weightSp_iff_diagonal_apply _ mu v).1 hv.2.1 i
    simp only [trivialRepresentation, LinearMap.zero_apply] at h1
    rcases smul_eq_zero.1 h1.symm with h | h
    · exact hi (by exact_mod_cast h)
    · exact hv.1 h
  have := hle hx
  rw [Submodule.mem_bot] at this
  rw [this, map_zero]

theorem invariant_projection_equivariant (D : Formalism.BasicNotions.D7) (h2 : adm2 D) {n : ℕ} {K V V' : Type} [Field K] [CharZero K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
    (E : GLOps n K V) (E' : GLOps n K V') (hE : IsGLRep E) (hE' : IsGLRep E')
    (P : Module.End K (V →ₗ[K] V')) (hP : IsInvProj (homRepresentation E E') P) (g : V →ₗ[K] V') : IsEquivariantMap E E' (P g) := by
  intro a b x
  have h := congrArg (fun f : V →ₗ[K] V' => f x)
    (invariant_projection_kills_operators D h2 n K _ (homRepresentation E E') (homRepresentation_isRep E E' hE hE') P hP g a b)
  simp only [homRepresentation_apply, LinearMap.zero_apply] at h
  exact (sub_eq_zero.1 h).symm

theorem schur_invariant_projection_trace (D : Formalism.BasicNotions.D7) (h2 : adm2 D) {n : ℕ} {K L : Type} [Field K] [CharZero K]
    [AddCommGroup L] [Module K L] [FiniteDimensional K L] (EL : GLOps n K L) (hEL : IsGLRep EL) (lam : Fin n → ℤ)
    (v0 : L) (hv0 : IsHWV EL lam v0) (hcyc : cyclicSubmodule EL v0 = ⊤)
    (P0 : Module.End K (L →ₗ[K] L)) (hP0 : IsInvProj (homRepresentation EL EL) P0) (g : L →ₗ[K] L) :
    (Module.finrank K L : K) • P0 g = (LinearMap.trace K L g) • (LinearMap.id : L →ₗ[K] L) := by
  have hψ := invariant_projection_equivariant D h2 EL EL hEL hEL P0 hP0 g
  have hw : P0 g v0 ∈ weightSp EL lam := by
    rw [mem_weightSp_iff_diagonal_apply]
    intro a
    rw [← hψ, (mem_weightSp_iff_diagonal_apply EL lam v0).1 hv0.2.1 a, map_smul]
  obtain ⟨c, hc⟩ := cyclic_highest_weightSpace_line EL hEL lam v0 hv0 (P0 g v0) (by rw [hcyc]; trivial) hw
  have hid : P0 g = c • (LinearMap.id : L →ₗ[K] L) := by
    have hT : IsEquivariantMap EL EL (P0 g - c • (LinearMap.id : L →ₗ[K] L)) := by
      intro a b x
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, map_sub, map_smul]
      rw [hψ]
    have h0 : (P0 g - c • (LinearMap.id : L →ₗ[K] L)) v0 = 0 := by
      simp [hc]
    ext x
    have := equivariant_kills_cyclic_of_zero EL EL _ hT v0 h0 x (by rw [hcyc]; trivial)
    exact sub_eq_zero.1 this
  have htr : IsEquivariantMap (homRepresentation EL EL) (trivialRepresentation n K) (LinearMap.trace K L) := by
    intro a b f
    have : homRepresentation EL EL a b f = EL a b * f - f * EL a b := by
      ext x; simp
    rw [this, map_sub, LinearMap.trace_mul_comm, sub_self]
    rfl
  have h3 := equivariant_commutes_isotypic D h2 n K _ K (homRepresentation EL EL) (trivialRepresentation n K) (homRepresentation_isRep EL EL hEL hEL)
    (trivialRepresentation_isRep n K) (LinearMap.trace K L) htr P0 1 hP0 (trivialRep_invariant_projection n K) g
  rw [Module.End.one_apply, hid, map_smul, LinearMap.trace_id, smul_eq_mul] at h3
  rw [hid, smul_smul, ← h3, mul_comm]

end Formalism.MainNotions.G.GLWeightTheory
end
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.RootWeights.IsotypicProjectorTraceFormula

section

@[expose] public section

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

def smulRightLinear {K L W : Type} [Field K] [AddCommGroup L] [Module K L] [AddCommGroup W] [Module K W]
    (ξ : L →ₗ[K] K) : W →ₗ[K] (L →ₗ[K] W) where
  toFun := fun m => ξ.smulRight m
  map_add' := fun m m' => by ext x; simp
  map_smul' := fun c m => by
    ext x
    simp only [LinearMap.smulRight_apply, RingHom.id_apply, LinearMap.smul_apply]
    exact smul_comm _ _ _

theorem isotypic_projector_trace_formula (D : Formalism.BasicNotions.D7) (h2 : adm2 D) : IsotypicProjectorTraceFormula := by
  intro n K W _ _ _ _ _ E hE lam e he v0 hv0 hL P hP ι _ b m
  have hEL := restrictRepresentation_isRep E hE _ hL
  have hv0' := highest_vector_restrict E _ hL lam v0 (self_mem_cyclicSubmodule E v0) hv0
  have hcyc := cyclicSubmodule_restrict_eq_top E v0 hL
  have hPe := fun g => invariant_projection_equivariant D h2 (restrictRepresentation E _ hL) E hEL hE P hP g

  let Θ : W →ₗ[K] W := ∑ i, (LinearMap.applyₗ (b i)) ∘ₗ P ∘ₗ smulRightLinear (b.coord i)
  have hΘ : ∀ m, Θ m = ∑ i, P ((b.coord i).smulRight m) (b i) := by
    intro m
    simp only [Θ, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.applyₗ_apply_apply]
    rfl
  have hle : (⨆ mu, isoSub E mu) ≤ LinearMap.eqLocus ((Fintype.card ι : K) • Θ) e := by
    refine iSup_le fun mu => ?_
    by_cases hmu : mu = lam
    · subst hmu
      refine Submodule.span_le.2 ?_
      rintro y ⟨u, hu, v, hv, rfl⟩
      have hy : u v ∈ isoSub E mu := Submodule.subset_span ⟨u, hu, v, hv, rfl⟩
      obtain ⟨φ, hφ, hφv⟩ := exists_equivariant_cyclic_to_hwv D h2 E hE mu v0 v hv0 hv hL
      obtain ⟨uL, _, huL⟩ := equivariant_lifts_monoid (restrictRepresentation E _ hL) E φ hφ hu
      have hm : u v = φ (uL ⟨v0, self_mem_cyclicSubmodule E v0⟩) := by rw [huL, hφv]
      obtain ⟨P0, hP0⟩ := invariant_projection_exists D h2 n K _ _ (homRepresentation_isRep _ _ hEL hEL)
      have hT : IsEquivariantMap (homRepresentation (restrictRepresentation E _ hL) (restrictRepresentation E _ hL)) (homRepresentation (restrictRepresentation E _ hL) E)
          (LinearMap.llcomp K _ _ W φ) := by
        intro a c g
        ext x
        simp only [LinearMap.llcomp_apply, homRepresentation_apply, map_sub]
        rw [hφ]
      change ((Fintype.card ι : K) • Θ) (u v) = e (u v)
      rw [he.1 _ hy, LinearMap.smul_apply, hΘ, hm, Finset.smul_sum]
      set l := uL ⟨v0, self_mem_cyclicSubmodule E v0⟩ with hl
      have hterm : ∀ i, (Fintype.card ι : K) • P ((b.coord i).smulRight (φ l)) (b i) = (b.repr l i) • φ (b i) := by
        intro i
        have h3 : (b.coord i).smulRight (φ l) = LinearMap.llcomp K _ _ W φ ((b.coord i).smulRight l) := by
          ext x; simp
        have h4 := equivariant_commutes_isotypic D h2 n K _ _ _ _ (homRepresentation_isRep _ _ hEL hEL) (homRepresentation_isRep _ _ hEL hE)
          (LinearMap.llcomp K _ _ W φ) hT P0 P hP0 hP ((b.coord i).smulRight l)
        have h5 := schur_invariant_projection_trace D h2 _ hEL mu _ hv0' hcyc P0 hP0 ((b.coord i).smulRight l)
        rw [Module.finrank_eq_card_basis b, LinearMap.trace_smulRight] at h5
        rw [h3, ← h4, LinearMap.llcomp_apply, ← map_smul, ← LinearMap.smul_apply, h5]
        simp [Module.Basis.coord_apply]
      rw [Finset.sum_congr rfl fun i _ => hterm i]
      conv_rhs => rw [← b.sum_repr l]

      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => (map_smul _ _ _).symm
    · intro y hy
      have hWm : IsSubrepresentation E (isoSub E mu) := fun a c => isotypic_stable_under_gl_operator E mu a c
      have hEm := restrictRepresentation_isRep E hE _ hWm
      obtain ⟨P1, hP1⟩ := invariant_projection_exists D h2 n K _ _ (homRepresentation_isRep _ _ hEL hEm)
      have hT : IsEquivariantMap (homRepresentation (restrictRepresentation E _ hL) (restrictRepresentation E _ hWm)) (homRepresentation (restrictRepresentation E _ hL) E)
          (LinearMap.llcomp K _ _ W (isoSub E mu).subtype) := by
        intro a c g
        ext x
        simp
      have hzero : ∀ ξ : cyclicSubmodule E v0 →ₗ[K] K, P (ξ.smulRight y) = 0 := by
        intro ξ
        have h3 : ξ.smulRight y = LinearMap.llcomp K _ _ W (isoSub E mu).subtype
            (ξ.smulRight (⟨y, hy⟩ : isoSub E mu)) := by
          ext x; simp
        have h4 := equivariant_commutes_isotypic D h2 n K _ _ _ _ (homRepresentation_isRep _ _ hEL hEm) (homRepresentation_isRep _ _ hEL hE)
          (LinearMap.llcomp K _ _ W (isoSub E mu).subtype) hT P1 P hP1 hP (ξ.smulRight (⟨y, hy⟩ : isoSub E mu))
        have hmem : ∀ x, P (ξ.smulRight y) x ∈ isoSub E mu := by
          intro x
          rw [h3, ← h4]
          simp
        have hv00 : P (ξ.smulRight y) ⟨v0, self_mem_cyclicSubmodule E v0⟩ = 0 := by
          by_contra h0
          have h6 := highest_vector_mem_isotypic E lam _ (equivariant_image_highest_vector _ E _ (hPe _) lam _ hv0' h0)
          exact h0 ((he.1 _ h6).symm.trans (he.2 mu hmu _ (hmem _)))
        ext x
        exact equivariant_kills_cyclic_of_zero _ E _ (hPe _) _ hv00 x (by rw [hcyc]; trivial)
      change ((Fintype.card ι : K) • Θ) y = e y
      rw [he.2 mu hmu y hy, LinearMap.smul_apply, hΘ]
      simp [hzero]
  have hm : m ∈ (⨆ mu, isoSub E mu) := by rw [isotypic_submodules_span_top D h2 n K W E hE]; trivial
  have := hle hm
  change ((Fintype.card ι : K) • Θ) m = e m at this
  rw [LinearMap.smul_apply, hΘ] at this
  exact this

end Formalism.MainNotions.G.GLWeightTheory
end
end
end
