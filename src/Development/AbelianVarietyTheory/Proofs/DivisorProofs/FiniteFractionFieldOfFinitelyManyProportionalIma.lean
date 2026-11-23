module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgHomAlgebraicClosureApplyEqPowStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StalkSpecializesCompatRingMap
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
public import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteFieldEmbeddingStalkOfFiniteStalkMap

section

@[expose] public section

open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.StalkField

theorem exists_stalk_field_hom : ∀ (Ω : Type) [Field Ω] (X : Scheme.{0}) (p : Sp Ω ⟶ X), (p.stalkMap (genericPoint (Sp Ω))).hom.Finite → ∃ φ : X.presheaf.stalk (p.base (genericPoint (Sp Ω))) →+* Ω, φ.Finite ∧ ∀ (K : Type) [Field K] (τ₁ τ₂ : Ω →+* K), spMap τ₁ ≫ p = spMap τ₂ ≫ p → τ₁.comp φ = τ₂.comp φ := by
  intro Ω _ X p hfin
  have hpt : genericPoint (Sp Ω) = IsLocalRing.closedPoint Ω := Subsingleton.elim _ _
  rw [hpt] at hfin ⊢
  refine ⟨(Scheme.stalkClosedPointTo p).hom, ?_, ?_⟩
  · have e : Scheme.stalkClosedPointTo p = p.stalkMap _ ≫ (stalkClosedPointIso (CommRingCat.of Ω)).hom := rfl
    rw [e, CommRingCat.hom_comp]
    exact RingHom.Finite.comp (RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (stalkClosedPointIso (CommRingCat.of Ω)).hom).2) hfin
  · intro K _ τ₁ τ₂ h
    have hs : ∀ τ : Ω →+* K, (spMap τ ≫ p) (IsLocalRing.closedPoint K) ⤳ p (IsLocalRing.closedPoint Ω) := by
      intro τ
      apply specializes_of_eq
      exact congrArg p (Subsingleton.elim ((spMap τ).base (IsLocalRing.closedPoint K)) (IsLocalRing.closedPoint Ω))
    have H : ∀ (q₁ q₂ : Sp K ⟶ X), q₁ = q₂ → ∀ (h₁ : q₁ (IsLocalRing.closedPoint K) ⤳ p (IsLocalRing.closedPoint Ω))
        (h₂ : q₂ (IsLocalRing.closedPoint K) ⤳ p (IsLocalRing.closedPoint Ω)) a,
        (Scheme.stalkClosedPointTo q₁).hom ((X.presheaf.stalkSpecializes h₁).hom a) =
          (Scheme.stalkClosedPointTo q₂).hom ((X.presheaf.stalkSpecializes h₂).hom a) := by
      rintro _ _ rfl _ _ _; rfl
    ext a
    simp only [RingHom.comp_apply]
    rw [← GlobalTheory.TorRef.stalkClosedPointTo_comp_spMap_specializes X p τ₁ (hs τ₁) a,
      ← GlobalTheory.TorRef.stalkClosedPointTo_comp_spMap_specializes X p τ₂ (hs τ₂) a]
    exact H _ _ h _ _ a

end GlobalTheory.StalkField
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteFieldEmbeddingStalkOfFiniteStalkMapStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.exists_finite_fieldEmbedding_stalk_of_finite_stalkMap : ∀ (Ω : Type) [Field Ω] (X : Scheme.{0}) (p : Sp Ω ⟶ X), (p.stalkMap (genericPoint (Sp Ω))).hom.Finite → ∃ φ : X.presheaf.stalk (p.base (genericPoint (Sp Ω))) →+* Ω, φ.Finite ∧ ∀ (K : Type) [Field K] (τ₁ τ₂ : Ω →+* K), spMap τ₁ ≫ p = spMap τ₂ ≫ p → τ₁.comp φ = τ₂.comp φ := by
  first | exact @GlobalTheory.StalkField.exists_stalk_field_hom | exact GlobalTheory.StalkField.exists_stalk_field_hom | (intros; apply GlobalTheory.StalkField.exists_stalk_field_hom <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSetOfRingHomCompEqOfFinite

section

@[expose] public section

open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem finite_setOf_ringHom_comp_eq_of_finite : ∀ (A Ω K : Type) [CommRing A] [CommRing Ω] [Field K]
    (φ : A →+* Ω) (ρ : A →+* K), φ.Finite → Set.Finite {τ : Ω →+* K | τ.comp φ = ρ} := by
  intro A Ω K _ _ _ φ ρ hφ
  classical
  letI : Algebra A Ω := φ.toAlgebra
  haveI : Module.Finite A Ω := hφ
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := A) (M := Ω)
  haveI : Algebra.IsIntegral A Ω := Algebra.IsIntegral.of_finite A Ω
  have hint : ∀ g : Ω, ∃ p : Polynomial A, p.Monic ∧ p.eval₂ φ g = 0 := fun g => by
    obtain ⟨q, hq, he⟩ := Algebra.IsIntegral.isIntegral (R := A) g
    exact ⟨q, hq, he⟩
  choose p hpm hpe using hint
  let F : (Ω →+* K) → (s → K) := fun τ g => τ g
  apply Set.Finite.of_finite_image (f := F)
  · refine Set.Finite.subset (Set.Finite.pi (t := fun g : s => (((p g).map ρ).roots.toFinset : Set K))
      (fun _ => Finset.finite_toSet _)) ?_
    rintro _ ⟨τ, hτ, rfl⟩ g _
    have hτ' : τ.comp φ = ρ := hτ
    simp only [Finset.mem_coe, Multiset.mem_toFinset]
    rw [Polynomial.mem_roots ((hpm g).map ρ).ne_zero, Polynomial.IsRoot, Polynomial.eval_map,
      ← hτ', ← Polynomial.hom_eval₂, hpe, map_zero]
  · intro τ₁ h₁ τ₂ h₂ he
    have h₁' : τ₁.comp φ = ρ := h₁
    have h₂' : τ₂.comp φ = ρ := h₂
    ext x
    have hx : x ∈ Submodule.span A (s : Set Ω) := hs ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy => exact congrFun he ⟨y, hy⟩
    | zero => simp
    | add y z _ _ hy hz => simp [hy, hz]
    | smul a y _ hy =>
      rw [Algebra.smul_def, map_mul, map_mul, hy]
      congr 1
      exact (RingHom.congr_fun h₁' a).trans (RingHom.congr_fun h₂' a).symm

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSetOfRingHomCompEqOfFiniteStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.finite_setOf_ringHom_comp_eq_of_finite' : ∀ (A Ω K : Type) [CommRing A] [CommRing Ω] [Field K] (φ : A →+* Ω) (ρ : A →+* K), φ.Finite → Set.Finite {τ : Ω →+* K | τ.comp φ = ρ} := by
  first | exact @GlobalTheory.finite_setOf_ringHom_comp_eq_of_finite | exact GlobalTheory.finite_setOf_ringHom_comp_eq_of_finite | (intros; apply GlobalTheory.finite_setOf_ringHom_comp_eq_of_finite <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFractionFieldOfFinitelyManyProportionalIma

section

@[expose] public section

open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem GlobalTheory.LevelFinite.finite_of_isAlgebraic : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) (K0 : Subfield Ω), R.FG → (∀ z : Ω, ∃ a ∈ R, ∃ c ∈ R, z = a / c) → (∀ a : o, algebraMap o Ω a ∈ K0) → Algebra.IsAlgebraic K0 Ω → Module.Finite K0 Ω := by
  intro o Ω _ _ _ R K0 hfg hfrac ho halg
  obtain ⟨s, hs⟩ := hfg
  have hL : FiniteDimensional K0 (IntermediateField.adjoin K0 (s : Set Ω)) :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => (halg.isAlgebraic x).isIntegral)
  have hR : ∀ a ∈ R, a ∈ IntermediateField.adjoin K0 (s : Set Ω) := by
    intro a ha
    rw [← hs] at ha
    induction ha using Algebra.adjoin_induction with
    | mem x hx => exact IntermediateField.subset_adjoin K0 _ hx
    | algebraMap r => exact IntermediateField.algebraMap_mem _ (⟨_, ho r⟩ : K0)
    | add x y _ _ hx hy => exact add_mem hx hy
    | mul x y _ _ hx hy => exact mul_mem hx hy
  have htop : IntermediateField.adjoin K0 (s : Set Ω) = ⊤ := by
    rw [eq_top_iff]
    intro z _
    obtain ⟨a, ha, c, hc, rfl⟩ := hfrac z
    exact div_mem (hR a ha) (hR c hc)
  rw [htop] at hL
  exact (IntermediateField.topEquiv (F := K0) (E := Ω)).toLinearEquiv.finiteDimensional

private theorem spMap_comp_moduli_spaces {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B)
    (g : B →+* C) : spMap (g.comp f) = spMap g ≫ spMap f := by
  first
  | rfl
  | simp [spMap, ← Spec.map_comp]
  | (simp only [spMap]; rw [← Spec.map_comp]; rfl)

private theorem pow_injective_of_transcendental {Ω : Type} [Field Ω] (K0 : Subfield Ω) (z : Ω) (hz : Transcendental K0 z) :
    Function.Injective (fun m : ℕ => z ^ m) := by
  have h0 : z ≠ 0 := fun h => hz (h ▸ isAlgebraic_zero)
  have h1 : ∀ k : ℕ, 0 < k → z ^ k ≠ 1 := by
    intro k hk hzk
    apply hz
    refine ⟨Polynomial.X ^ k - Polynomial.C 1, Polynomial.X_pow_sub_C_ne_zero hk 1, ?_⟩
    simp [hzk]
  have key : ∀ m m' : ℕ, m < m' → z ^ m = z ^ m' → False := by
    intro m m' h hmm
    apply h1 (m' - m) (Nat.sub_pos_of_lt h)
    have : z ^ m * z ^ (m' - m) = z ^ m * 1 := by
      rw [← pow_add, Nat.add_sub_cancel' h.le, mul_one, hmm]
    exact mul_left_cancel₀ (pow_ne_zero _ h0) this
  intro m m' hmm
  simp only at hmm
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact key m m' h hmm
  · exact key m' m h hmm.symm

theorem GlobalTheory.LevelFinite.finite_ratio_field : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) (X : Scheme.{0}) (x : Sp R ⟶ X) (I : Type) [Finite I] (v : I → R), R.FG → (∀ z : Ω, ∃ a ∈ R, ∃ c ∈ R, z = a / c) → ((spMap R.val.toRingHom ≫ x).stalkMap (genericPoint (Sp Ω))).hom.Finite → (∀ (K : Type) [Field K] [IsAlgClosed K] (c : I → K), Set.Finite {y : Sp K ⟶ X | ∃ σ : R →+* K, spMap σ ≫ x = y ∧ ∃ u : K, u ≠ 0 ∧ ∀ i, σ (v i) = u * c i}) → Module.Finite (Subfield.closure (Set.range (algebraMap o Ω) ∪ {z | ∃ i i', z = (v i : Ω) / (v i' : Ω)})) Ω := by
  intro o Ω _ _ _ R X x I _ v hfg hfrac hfin hpts
  refine GlobalTheory.LevelFinite.finite_of_isAlgebraic o Ω R _ hfg hfrac
    (fun a => Subfield.subset_closure (Or.inl ⟨a, rfl⟩)) ⟨fun z => ?_⟩
  by_contra hz
  obtain ⟨φ, hφ, hφeq⟩ := GlobalTheory.T.exists_finite_fieldEmbedding_stalk_of_finite_stalkMap Ω X (spMap R.val.toRingHom ≫ x) hfin
  have hτ : ∀ m : ℕ, ∃ τ : Ω →ₐ[Subfield.closure (Set.range (algebraMap o Ω) ∪
      {z | ∃ i i', z = (v i : Ω) / (v i' : Ω)})] AlgebraicClosure Ω,
      τ z = algebraMap Ω (AlgebraicClosure Ω) z ^ (m + 1) :=
    fun m => GlobalTheory.T.exists_algHom_algebraicClosure_apply_eq_pow' Ω _ z hz (m + 1) m.succ_pos
  choose τ hτ using hτ
  have hfib : ∀ y : Sp (AlgebraicClosure Ω) ⟶ X,
      Set.Finite {τ' : Ω →+* AlgebraicClosure Ω | spMap τ' ≫ spMap R.val.toRingHom ≫ x = y} := by
    intro y
    by_cases hne : ∃ τ0 : Ω →+* AlgebraicClosure Ω, spMap τ0 ≫ spMap R.val.toRingHom ≫ x = y
    · obtain ⟨τ0, hτ0⟩ := hne
      refine (GlobalTheory.T.finite_setOf_ringHom_comp_eq_of_finite' _ Ω _ φ (τ0.comp φ) hφ).subset ?_
      intro τ' hτ'
      exact hφeq _ τ' τ0 (hτ'.trans hτ0.symm)
    · apply Set.Finite.subset Set.finite_empty
      intro τ' hτ'
      exact (hne ⟨τ', hτ'⟩).elim
  have hS := hpts (AlgebraicClosure Ω) (fun i => algebraMap Ω (AlgebraicClosure Ω) (v i))
  have hinj : Function.Injective (fun m : ℕ => ((τ m : Ω →ₐ[_] AlgebraicClosure Ω) : Ω →+* AlgebraicClosure Ω)) := by
    intro m m' hmm
    have h1 : τ m z = τ m' z := by
      simpa using congrArg (fun f : Ω →+* AlgebraicClosure Ω => f z) hmm
    rw [hτ, hτ, ← map_pow, ← map_pow] at h1
    exact Nat.succ_injective (pow_injective_of_transcendental _ z hz ((algebraMap Ω (AlgebraicClosure Ω)).injective h1))
  apply Set.infinite_range_of_injective hinj
  refine (hS.biUnion (fun y _ => hfib y)).subset ?_
  rintro _ ⟨m, rfl⟩
  refine Set.mem_biUnion (x := spMap ((τ m : Ω →+* AlgebraicClosure Ω)) ≫ spMap R.val.toRingHom ≫ x) ?_ rfl
  refine ⟨((τ m : Ω →+* AlgebraicClosure Ω)).comp R.val.toRingHom, by rw [spMap_comp_moduli_spaces, Category.assoc], ?_⟩
  by_cases h : ∃ i, (v i : Ω) ≠ 0
  · obtain ⟨i0, hi0⟩ := h
    have hc0 : algebraMap Ω (AlgebraicClosure Ω) (v i0) ≠ 0 := by
      exact (map_ne_zero _).mpr hi0
    have hτ0 : τ m (v i0) ≠ 0 := by
      exact (map_ne_zero _).mpr hi0
    refine ⟨τ m (v i0) / algebraMap Ω (AlgebraicClosure Ω) (v i0), div_ne_zero hτ0 hc0, fun i => ?_⟩
    have hr : (v i : Ω) / (v i0 : Ω) ∈ Subfield.closure (Set.range (algebraMap o Ω) ∪
        {z | ∃ i i', z = (v i : Ω) / (v i' : Ω)}) := Subfield.subset_closure (Or.inr ⟨i, i0, rfl⟩)
    have hfix : τ m ((v i : Ω) / (v i0 : Ω)) = algebraMap Ω (AlgebraicClosure Ω) ((v i : Ω) / (v i0 : Ω)) := by
      have := (τ m).commutes ⟨_, hr⟩
      rw [IsScalarTower.algebraMap_apply _ Ω (AlgebraicClosure Ω)] at this
      exact this
    have key : τ m (v i) = τ m ((v i : Ω) / (v i0 : Ω)) * τ m (v i0) := by
      rw [← map_mul, div_mul_cancel₀ _ hi0]
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.coe_toRingHom]
    rw [show (R.val.toRingHom (v i) : Ω) = v i from rfl, key, hfix, map_div₀]
    ring
  · push_neg at h
    refine ⟨1, one_ne_zero, fun i => ?_⟩
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.coe_toRingHom]
    rw [show (R.val.toRingHom (v i) : Ω) = v i from rfl, h i]
    simp
end
end
