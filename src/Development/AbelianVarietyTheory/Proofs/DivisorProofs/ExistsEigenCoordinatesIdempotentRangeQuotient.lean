module

public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.Ideal.Span
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Std.Tactic.BVDecide.Normalize.BitVec
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoordsRangeIdempotentOfRetractStatement
import Mathlib.Tactic.Linter.Style
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.RingTheory.Finiteness.Cardinality
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.InfUniv
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIdempotentsOfComaximal

section

@[expose] public section

universe u

namespace GlobalTheory

theorem eigenIdempotents_of_comaximal
    {C : Type} [CommRing C] {A : Type} [CommRing A] {W : Type u} [AddCommGroup W] [Module C W]
    (σ : A →+* Module.End C W) (a : ℕ) (χ : Fin a → A →+* C) :
    (∀ i j, i ≠ j → Ideal.span (Set.range fun x => χ i x - χ j x) = ⊤) →
    ∃ e : Fin a → Module.End C W,
      (∀ i (T : Module.End C W), (∀ c, T * σ c = σ c * T) → T * e i = e i * T) ∧
      (∀ i w, (∀ c, σ c w = χ i c • w) → e i w = w) ∧
      (∀ i j w, j ≠ i → (∀ c, σ c w = χ j c • w) → e i w = 0) := by
  classical
  intro hcom
  have hc : ∀ i j, ∃ c : A →₀ C, i ≠ j → (c.sum fun x r => r * (χ i x - χ j x)) = 1 := by
    intro i j
    by_cases h : i = j
    · exact ⟨0, fun h' => absurd h h'⟩
    · have h1 : (1 : C) ∈ Ideal.span (Set.range fun x => χ i x - χ j x) := by
        rw [hcom i j h]; trivial
      obtain ⟨c, hc⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 h1
      exact ⟨c, fun _ => by simpa [smul_eq_mul] using hc⟩
  choose c hc using hc
  let Z : Fin a → Fin a → Module.End C W := fun i j =>
    (c i j).sum fun x r => r • (σ x - χ j x • (1 : Module.End C W))
  have hZ : ∀ i j k (w : W), (∀ x, σ x w = χ k x • w) →
      Z i j w = ((c i j).sum fun x r => r * (χ k x - χ j x)) • w := by
    intro i j k w hw
    simp only [Z, Finsupp.sum, LinearMap.sum_apply, Finset.sum_smul]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp [hw, sub_smul, mul_smul, smul_sub]
  have hZc : ∀ i j (T : Module.End C W), (∀ c, T * σ c = σ c * T) → Commute T (Z i j) := by
    intro i j T hT
    simp only [Z, Finsupp.sum]
    refine Commute.sum_right _ _ _ fun x _ => ?_
    exact ((show Commute T (σ x) from hT x).sub_right ((Commute.one_right T).smul_right _)).smul_right _
  have hlist : ∀ (i : Fin a) (s : Fin a → C) (w : W) (L : List (Fin a)),
      (∀ j ∈ L, Z i j w = s j • w) → (L.map (Z i)).prod w = (L.map s).prod • w := by
    intro i s w L hL
    induction L with
    | nil => simp
    | cons j L ih =>
      have ih' := ih (fun k hk => hL k (List.mem_cons_of_mem _ hk))
      simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, ih', map_smul,
        hL j List.mem_cons_self, smul_smul]
      rw [mul_comm]
  refine ⟨fun i => (((List.finRange a).filter (· ≠ i)).map (Z i)).prod, ?_, ?_, ?_⟩
  · intro i T hT
    exact (Commute.list_prod_right _ _ fun y hy => by
      obtain ⟨j, _, rfl⟩ := List.mem_map.1 hy
      exact hZc i j T hT).eq
  · intro i w hw
    rw [hlist i (fun j => (c i j).sum fun x r => r * (χ i x - χ j x)) w _
      (fun j _ => hZ i j i w hw)]
    rw [List.prod_eq_one, one_smul]
    intro y hy
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hy
    have hji : j ≠ i := by simpa using (List.mem_filter.1 hj).2
    exact hc i j (Ne.symm hji)
  · intro i j w hji hw
    rw [hlist i (fun k => (c i k).sum fun x r => r * (χ j x - χ k x)) w _
      (fun k _ => hZ i k j w hw)]
    rw [List.prod_eq_zero, zero_smul]
    refine List.mem_map.2 ⟨j, ?_, ?_⟩
    · exact List.mem_filter.2 ⟨List.mem_finRange j, by simpa using hji⟩
    · simp

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIdempotentsOfComaximalStatement

section

@[expose] public section

universe u

theorem _root_.GlobalTheory.T.exists_eigen_idempotents_of_comaximal : ∀ {C : Type} [CommRing C] {A : Type} [CommRing A] {W : Type u} [AddCommGroup W] [Module C W]
  (σ : A →+* Module.End C W) (a : ℕ) (χ : Fin a → A →+* C),
  (∀ i j, i ≠ j → Ideal.span (Set.range fun x => χ i x - χ j x) = ⊤) →
  ∃ e : Fin a → Module.End C W,
    (∀ i (T : Module.End C W), (∀ c, T * σ c = σ c * T) → T * e i = e i * T) ∧
    (∀ i w, (∀ c, σ c w = χ i c • w) → e i w = w) ∧
    (∀ i j w, j ≠ i → (∀ c, σ c w = χ j c • w) → e i w = 0) := by
  first | exact @GlobalTheory.eigenIdempotents_of_comaximal | exact GlobalTheory.eigenIdempotents_of_comaximal | (intros; apply GlobalTheory.eigenIdempotents_of_comaximal <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientRetractPiQuotientOfSummand

section

@[expose] public section

universe u

namespace GlobalTheory

theorem quotient_retract_pi_quotient :
    ∀ {C : Type} [CommRing C] [IsLocalRing C] (I : Ideal C) {H : Type u} [AddCommGroup H] [Module C H]
      [Module.Finite C H] [Module.Projective C H] (F : Submodule C H), I • ⊤ ≤ F →
      (∃ E' M : Submodule C H, IsCompl E' M ∧ E' ⊔ I • ⊤ = F) →
      ∃ (m : ℕ) (s : (H ⧸ F) →ₗ[C] (Fin m → C ⧸ I)) (r : (Fin m → C ⧸ I) →ₗ[C] (H ⧸ F)),
        r ∘ₗ s = LinearMap.id := by
  intro C _ _ I H _ _ _ _ F hIF hEx
  obtain ⟨E', M, hc, hF⟩ := hEx
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' C H
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property π LinearMap.id hπ
  let P : H →ₗ[C] M := Submodule.linearProjOfIsCompl M E' hc.symm
  let q : H →ₗ[C] H := M.subtype ∘ₗ P
  have hPq : ∀ x, P (q x) = P x := fun x => Submodule.linearProjOfIsCompl_apply_left hc.symm (P x)
  have hqq : ∀ x, q (q x) = q x := fun x => congrArg Subtype.val (hPq x)
  have hqE : ∀ x ∈ E', q x = 0 := fun x hx => by
    have h0 : P x = 0 := (Submodule.linearProjOfIsCompl_apply_eq_zero_iff hc.symm).2 hx
    show ((P x : M) : H) = 0
    rw [h0]; rfl
  have hxq : ∀ x, x - q x ∈ F := by
    intro x
    rw [← hF]
    apply Submodule.mem_sup_left
    have h0 : P (x - q x) = 0 := by rw [map_sub, hPq, sub_self]
    exact (Submodule.linearProjOfIsCompl_apply_eq_zero_iff hc.symm).1 h0
  have hσπ : ∀ x, π (σ x) = x := fun x => LinearMap.congr_fun hσ x
  let s0 : H →ₗ[C] (Fin n → C ⧸ I) :=
    (LinearMap.pi fun k => (Submodule.mkQ I) ∘ₗ LinearMap.proj k) ∘ₗ σ ∘ₗ q
  have hs0 : F ≤ LinearMap.ker s0 := by
    rw [← hF]
    refine sup_le (fun x hx => ?_) ?_
    · rw [LinearMap.mem_ker]
      show (LinearMap.pi fun k => (Submodule.mkQ I) ∘ₗ LinearMap.proj k) (σ (q x)) = 0
      rw [hqE x hx, map_zero, map_zero]
    · refine Submodule.smul_le.2 (fun c hcI y _ => ?_)
      rw [LinearMap.mem_ker, map_smul]
      funext k
      show c • (Submodule.mkQ I (σ (q y) k)) = 0
      rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact I.mul_mem_right _ hcI
  let s : (H ⧸ F) →ₗ[C] (Fin n → C ⧸ I) := F.liftQ s0 hs0
  let e : Fin n → (Fin n → C) := fun k j => if k = j then 1 else 0
  have hk : ∀ k, I ≤ LinearMap.ker (LinearMap.toSpanSingleton C (H ⧸ F) (F.mkQ (q (π (e k))))) := by
    intro k c hcI
    rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, ← map_smul, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    exact hIF (Submodule.smul_mem_smul hcI Submodule.mem_top)
  let g : Fin n → ((C ⧸ I) →ₗ[C] (H ⧸ F)) := fun k => I.liftQ _ (hk k)
  let r : (Fin n → C ⧸ I) →ₗ[C] (H ⧸ F) := ∑ k, g k ∘ₗ LinearMap.proj k
  refine ⟨n, s, r, ?_⟩
  apply Submodule.linearMap_qext
  ext x
  have h1 : r (s (F.mkQ x)) = F.mkQ (q (π (σ (q x)))) := by

    rw [LinearMap.pi_apply_eq_sum_univ π (σ (q x)), map_sum, map_sum]
    simp only [r, s, g, LinearMap.sum_apply, LinearMap.comp_apply,
      LinearMap.proj_apply, Submodule.liftQ_apply, Submodule.mkQ_apply, s0, LinearMap.pi_apply]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [LinearMap.toSpanSingleton_apply, map_smul, ← Submodule.Quotient.mk_smul]
  rw [LinearMap.comp_apply, LinearMap.comp_apply, h1, hσπ, hqq]
  show F.mkQ (q x) = F.mkQ x
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, eq_comm, Submodule.Quotient.eq]
  exact hxq x

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientRetractPiQuotientOfSummandStatement

section

@[expose] public section

universe u

theorem _root_.GlobalTheory.T.quotient_retract_pi_quotient_of_summand : ∀ {C : Type} [CommRing C] [IsLocalRing C] (I : Ideal C) {H : Type u} [AddCommGroup H] [Module C H]
  [Module.Finite C H] [Module.Projective C H] (F : Submodule C H), I • ⊤ ≤ F →
  (∃ E' M : Submodule C H, IsCompl E' M ∧ E' ⊔ I • ⊤ = F) →
  ∃ (m : ℕ) (s : (H ⧸ F) →ₗ[C] (Fin m → C ⧸ I)) (r : (Fin m → C ⧸ I) →ₗ[C] (H ⧸ F)),
    r ∘ₗ s = LinearMap.id := by
  first | exact @GlobalTheory.quotient_retract_pi_quotient | exact GlobalTheory.quotient_retract_pi_quotient | (intros; apply GlobalTheory.quotient_retract_pi_quotient <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEigenCoordinatesIdempotentRangeQuotient

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
open IsLocalRing
universe u

namespace GlobalTheory

theorem exists_eigen_coordinates_range_quot : ∀ {C : Type} [CommRing C] [IsLocalRing C] (I : Ideal C), I ^ 2 = ⊥ →
  ∀ {A : Type} [CommRing A] {H : Type u} [AddCommGroup H] [Module C H] [Module.Finite C H] [Module.Projective C H]
  (σ : A →+* Module.End C H) (a : ℕ) (χ : Fin a → A →+* C),
  (∀ i j, i ≠ j → Ideal.span (Set.range fun x => χ i x - χ j x) = ⊤) →
  ∀ (π : Module.End C H), π * π = π → (∀ c, σ c * π = π * σ c) →
  ∀ (F : Submodule C H), I • ⊤ ≤ F → (∀ c, ∀ x ∈ F, σ c x ∈ F) → (∀ x ∈ F, π x ∈ F) →
  (∃ E' M : Submodule C H, IsCompl E' M ∧ E' ⊔ I • ⊤ = F) →
  (∀ d ∈ LinearMap.range π, ∃ w : Fin a → H, (∀ i c, σ c (w i) - χ i c • w i ∈ F) ∧ d - ∑ i, w i ∈ F) →
  ∃ (n : ℕ) (κ : Fin n → Fin a) (ℓ : Fin n → H →ₗ[C] C ⧸ I) (y : Fin n → H),
    (∀ k c x, ℓ k (σ c x) = Ideal.Quotient.mk I (χ (κ k) c) * ℓ k x) ∧
    (∀ x ∈ LinearMap.range π, x ∈ F ↔ ∀ k, ℓ k x = 0) ∧
    (∀ k, y k ∈ LinearMap.range π) ∧ ∀ j k, ℓ j (y k) = if j = k then 1 else 0 := by
  intro C _ _ I hI2 A _ H _ _ _ _ σ a χ hχ π hπ hσπ F hIF hσF hπF hEM hdec
  have hItop : I ≠ ⊤ := by
    rintro rfl
    rw [Ideal.top_pow] at hI2
    exact top_ne_bot hI2
  obtain ⟨m, s, r, hrs⟩ := GlobalTheory.T.quotient_retract_pi_quotient_of_summand I F hIF hEM
  let σb : A →+* Module.End C (H ⧸ F) :=
    { toFun := fun c => F.mapQ F (σ c) (fun x hx => hσF c x hx)
      map_one' := Submodule.linearMap_qext _ (LinearMap.ext fun x => by simp)
      map_mul' := fun c d => Submodule.linearMap_qext _ (LinearMap.ext fun x => by simp)
      map_zero' := Submodule.linearMap_qext _ (LinearMap.ext fun x => by simp)
      map_add' := fun c d => Submodule.linearMap_qext _ (LinearMap.ext fun x => by simp) }
  have hσb : ∀ c x, σb c (F.mkQ x) = F.mkQ (σ c x) := fun c x => rfl
  let πb : Module.End C (H ⧸ F) := F.mapQ F π (fun x hx => hπF x hx)
  have hπb : ∀ x, πb (F.mkQ x) = F.mkQ (π x) := fun x => rfl
  have hπσ : ∀ c, πb * σb c = σb c * πb := fun c => Submodule.linearMap_qext _ (LinearMap.ext fun x => by
    simp only [LinearMap.comp_apply, Module.End.mul_apply, hσb, hπb]
    rw [← Module.End.mul_apply, ← hσπ c, Module.End.mul_apply])
  have hσσ : ∀ c d, σb c * σb d = σb d * σb c := fun c d => by
    rw [← map_mul, ← map_mul, mul_comm]
  obtain ⟨e, he1, he2, he3⟩ := GlobalTheory.T.exists_eigen_idempotents_of_comaximal σb a χ hχ
  have heπ : ∀ i, πb * e i = e i * πb := fun i => he1 i πb hπσ
  have heσ : ∀ i c, σb c * e i = e i * σb c := fun i c => he1 i (σb c) (hσσ c)
  have hππ : πb * πb = πb := Submodule.linearMap_qext _ (LinearMap.ext fun x => by
    simp only [LinearMap.comp_apply, Module.End.mul_apply, hπb]
    rw [← Module.End.mul_apply, hπ])

  have hD : ∀ x ∈ LinearMap.range π, ∃ u : Fin a → H ⧸ F, (∀ i c, σb c (u i) = χ i c • u i) ∧
      F.mkQ x = ∑ i, u i := by
    intro x hx
    obtain ⟨w, hw1, hw2⟩ := hdec x hx
    refine ⟨fun i => F.mkQ (w i), fun i c => ?_, ?_⟩
    · rw [hσb, ← map_smul, ← sub_eq_zero, ← map_sub]
      exact (Submodule.Quotient.mk_eq_zero F).2 (hw1 i c)
    · set_option synthInstance.maxHeartbeats 100000 in
        rw [← map_sum, ← sub_eq_zero, ← map_sub]
      exact (Submodule.Quotient.mk_eq_zero F).2 hw2
  have hEu : ∀ x ∈ LinearMap.range π, ∀ u : Fin a → H ⧸ F, (∀ i c, σb c (u i) = χ i c • u i) →
      F.mkQ x = ∑ i, u i → ∀ i, e i (F.mkQ x) = u i := by
    intro x hx u hu hxu i

    rw [hxu, map_sum, Finset.sum_eq_single i]
    · exact he2 i (u i) (hu i)
    · intro j _ hji; exact he3 i j (u j) hji (hu j)
    · simp
  let p : Fin a → Module.End C (H ⧸ F) := fun i => e i * πb
  have hpx : ∀ i x, p i (F.mkQ x) = e i (F.mkQ (π x)) := fun i x => rfl
  have hpσ : ∀ i c, p i * σb c = σb c * p i := fun i c => by
    simp only [p]; rw [_root_.mul_assoc, hπσ, ← _root_.mul_assoc, ← heσ, _root_.mul_assoc]

  have hpE : ∀ i w, ∀ c, σb c (p i w) = χ i c • p i w := by
    intro i w c
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective F w
    obtain ⟨u, hu, hxu⟩ := hD (π x) (LinearMap.mem_range_self π x)
    rw [hpx, hEu _ (LinearMap.mem_range_self π x) u hu hxu]
    exact hu i c
  have hpe : ∀ i w, (∀ c, σb c w = χ i c • w) → e i (p i w) = p i w := fun i w _ => he2 i _ (hpE i w)
  have hpπ : ∀ i w, πb (p i w) = p i w := by
    intro i w
    simp only [p]
    rw [← Module.End.mul_apply, ← _root_.mul_assoc, heπ, _root_.mul_assoc, hππ]
  have hpp : ∀ i j w, p j (p i w) = if j = i then p i w else 0 := by
    intro i j w
    show e j (πb (p i w)) = _
    rw [hpπ]
    split_ifs with h
    · subst h; exact he2 j _ (hpE j w)
    · exact he3 j i _ (Ne.symm h) (hpE i w)
  have hidem : ∀ i, p i * p i = p i := fun i => LinearMap.ext fun w => by
    rw [Module.End.mul_apply, hpp]; simp
  choose n b f hb hfp hδ hinj using fun i => GlobalTheory.T.exists_coords_range_idempotent_of_retract I hItop m s r hrs (p i) (hidem i)
  obtain ⟨eqv⟩ : Nonempty ((Σ i, Fin (n i)) ≃ Fin (∑ i, n i)) := ⟨finSigmaFinEquiv⟩
  have hlift : ∀ i t, ∃ z ∈ LinearMap.range π, F.mkQ z = b i t := by
    intro i t
    obtain ⟨w, hw⟩ := hb i t
    obtain ⟨h', hh'⟩ := Submodule.mkQ_surjective F (e i w)
    refine ⟨π h', LinearMap.mem_range_self π h', ?_⟩
    rw [← hw, ← hπb, hh']
    show πb (e i w) = (e i * πb) w
    rw [← Module.End.mul_apply, heπ]
  choose z hz hzb using hlift
  let L : (Σ i, Fin (n i)) → H →ₗ[C] C ⧸ I := fun q => f q.1 q.2 ∘ₗ F.mkQ
  let Z : (Σ i, Fin (n i)) → H := fun q => z q.1 q.2
  have hL : ∀ i t x, L ⟨i, t⟩ x = f i t (F.mkQ x) := fun _ _ _ => rfl
  have hZ : ∀ i t, Z ⟨i, t⟩ = z i t := fun _ _ => rfl
  refine ⟨∑ i, n i, fun k => (eqv.symm k).1, fun k => L (eqv.symm k),
    fun k => Z (eqv.symm k), ?_, ?_, fun k => hz _ _, ?_⟩
  · intro k c x
    obtain ⟨⟨i, t⟩, rfl⟩ := eqv.surjective k
    simp only [Equiv.symm_apply_apply, hL]
    rw [← hσb, ← hfp i t, ← Module.End.mul_apply, hpσ, Module.End.mul_apply, hpE, map_smul, hfp,
      Algebra.smul_def, Ideal.Quotient.algebraMap_eq]
  · intro x hx
    constructor
    · intro hxF k
      have h0 : F.mkQ x = 0 := (Submodule.Quotient.mk_eq_zero F).2 hxF
      simp only [L, LinearMap.comp_apply, h0, map_zero]
    · intro hk
      obtain ⟨u, hu, hxu⟩ := hD x hx
      have hpu : ∀ i, p i (F.mkQ x) = u i := by
        intro i
        obtain ⟨x', rfl⟩ := hx
        have hx' : π (π x') = π x' := by rw [← Module.End.mul_apply, hπ]
        rw [hpx, hx']
        exact hEu _ (LinearMap.mem_range_self π x') u hu hxu i
      have h0 : ∀ i, u i = 0 := by
        intro i
        rw [← hpu i]
        refine hinj i _ (LinearMap.mem_range_self _ _) fun t => ?_
        rw [hfp]
        simpa [hL] using hk (eqv ⟨i, t⟩)
      rw [← Submodule.Quotient.mk_eq_zero F]
      change F.mkQ x = 0
      rw [hxu]; simp [h0]
  · intro j k
    obtain ⟨⟨i', t'⟩, rfl⟩ := eqv.surjective j
    obtain ⟨⟨i, t⟩, rfl⟩ := eqv.surjective k
    simp only [Equiv.symm_apply_apply, hL, hZ, hzb, eqv.injective.eq_iff]
    by_cases hii : i' = i
    · subst hii
      rw [hδ]
      simp
    · have : f i' t' (b i t) = 0 := by
        obtain ⟨w, hw⟩ := hb i t
        rw [← hfp, ← hw, hpp, if_neg hii, map_zero]
      rw [this, if_neg]
      intro h; exact hii (congrArg Sigma.fst h)

end GlobalTheory
end
end
