module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LinkExactAff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TensorHomCubes.StabDirectedSystem
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ExactAtLinkInUniMOfExactAtMapLinearEquiv
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.LinkInUniMEqShorterOfFormEqOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.SeqComplexExactAtOfAllLinksExactAt
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.SubClosedAndPermAndLinearEquivInvariantUniM
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ExactAtLinkSuccUnionTranslateOfCoordOne

section

@[expose] public section

open GlobalTheory.SeqCx Matrix

namespace GlobalTheory.SeqCx

theorem low_aff_subset_succ (R : Type) [CommRing R] (n j : ℕ) :
    low R n ∪ aff R n j ⊆ low R (n + 1) ∪ aff R (n + 1) j := by
  rintro x (hx | hx)
  · exact Or.inl fun i hi => hx i (by omega)
  · exact Or.inr fun i hi => hx i (by omega)

theorem coord_vanish_low_aff (R : Type) [CommRing R] (n j : ℕ) (hj : n + 1 ≤ j) :
    ∀ x ∈ low R n ∪ aff R n j, (Finsupp.lapply n : (ℕ →₀ R) →ₗ[R] R) x = 0 := by
  intro x hx
  rw [Finsupp.lapply_apply]
  rcases hx with hx | hx
  · exact hx n le_rfl
  · have := hx n le_rfl
    simpa [Finsupp.single_apply, show j ≠ n by omega] using this

theorem linkIn_exactAt_of_coord_one : ∀ (R : Type) [CommRing R] (s n : ℕ), LinkExactAff R s n →
    ∀ j : ℕ, n + 1 ≤ j → ∀ τ ∈ uniM R (ℕ →₀ R), ∀ v ∈ τ, v n = 1 → ∀ p : ℕ,
    p + s + τ.length ≤ n + 2 →
    ExactAt (linkIn (uniM R (ℕ →₀ R)) (low R (n + 1) ∪ aff R (n + 1) j) τ) p := by
  intro R _ s n h j hj τ hτ v hv hvn p hp
  have hsub : SubClosed (uniM R (ℕ →₀ R)) := (T.subClosed_and_perm_and_linearEquiv_invariant_uniM R (ℕ →₀ R)).1
  have hlenpos := List.length_pos_of_mem hv
  apply exactAt_of_links (ℕ →₀ R) _ (low R n ∪ aff R n j)
  · intro l hl l' hl'
    refine ⟨fun x hx => hl.1 x (hl'.subset hx), hsub _ hl.2 _ ?_⟩
    simpa using hl'
  · intro τ1 hτ1 hlen
    have heq : linkIn (linkIn (uniM R (ℕ →₀ R)) (low R (n + 1) ∪ aff R (n + 1) j) τ)
        (low R n ∪ aff R n j) τ1 = linkIn (uniM R (ℕ →₀ R)) (low R n ∪ aff R n j) (τ ++ τ1) := by
      ext w
      constructor
      · rintro ⟨hw, -, h2⟩
        refine ⟨hw, ?_⟩
        rw [List.append_assoc]
        exact h2
      · rintro ⟨hw, h2⟩
        refine ⟨hw, fun x hx => ?_, ?_⟩
        · rcases List.mem_append.mp hx with hx | hx
          · exact hτ1.1 x hx
          · exact low_aff_subset_succ R n j (hw x hx)
        · rw [← List.append_assoc]
          exact h2
    rw [heq]
    obtain ⟨τ', hτ', hl', heq'⟩ := T.linkIn_uniM_eq_shorter_of_form_eq_one R (ℕ →₀ R) (Finsupp.lapply n) (low R n ∪ aff R n j)
      (coord_vanish_low_aff R n j hj) (τ ++ τ1) hτ1.2 v (List.mem_append_left _ hv)
      (by rw [Finsupp.lapply_apply]; exact hvn)
    rw [heq']
    rw [List.length_append] at hl'
    exact h j (by omega) τ' hτ' (p - τ1.length) (by omega)

end GlobalTheory.SeqCx

section
open GlobalTheory.SeqCx Matrix
theorem _root_.GlobalTheory.T.exactAt_link_succ_union_translate_of_coord_one : ∀ (R : Type) [CommRing R] (s n : ℕ), LinkExactAff R s n → ∀ j : ℕ, n + 1 ≤ j → ∀ τ ∈ uniM R (ℕ →₀ R), ∀ v ∈ τ, v n = 1 → ∀ p : ℕ, p + s + τ.length ≤ n + 2 → ExactAt (linkIn (uniM R (ℕ →₀ R)) (low R (n + 1) ∪ aff R (n + 1) j) τ) p := by
  first
  | exact @GlobalTheory.SeqCx.linkIn_exactAt_of_coord_one
  | exact @GlobalTheory.SeqCx.coord_vanish_low_aff
  | exact @GlobalTheory.SeqCx.low_aff_subset_succ
end
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ExistsTransvectionPreservingLowAndAff

section

@[expose] public section

open GlobalTheory.SeqCx Matrix

namespace GlobalTheory.ShearLow

theorem main : ∀ (R : Type) [CommRing R] (n : ℕ) (h : (ℕ →₀ R) →ₗ[R] R) (t : ℕ →₀ R), t ∈ low R n → h t = 0 → ∃ ψ : (ℕ →₀ R) ≃ₗ[R] (ℕ →₀ R), (∀ x, ψ x = x + h x • t) ∧ (∀ x, ψ x ∈ low R n ↔ x ∈ low R n) ∧ ∀ j x, ψ x ∈ aff R n j ↔ x ∈ aff R n j := by
  intro R _ n h t ht hht
  have key : ∀ x y : ℕ →₀ R, y ∈ low R n → (x + y ∈ low R n ↔ x ∈ low R n) := by
    intro x y hy
    simp only [low, Set.mem_setOf_eq, Finsupp.add_apply] at hy ⊢
    constructor
    · intro hx i hi
      have hxi := hx i hi
      rw [hy i hi, add_zero] at hxi
      exact hxi
    · intro hx i hi
      rw [hx i hi, hy i hi, add_zero]
  have hts : ∀ c : R, c • t ∈ low R n := by
    intro c
    simp only [low, Set.mem_setOf_eq, Finsupp.smul_apply] at ht ⊢
    intro i hi
    rw [ht i hi, smul_zero]
  let ψ : (ℕ →₀ R) ≃ₗ[R] (ℕ →₀ R) :=
    { toFun := fun x => x + h x • t
      invFun := fun x => x - h x • t
      map_add' := by
        intro x y
        simp only [map_add (f := _), add_smul]
        abel
      map_smul' := by
        intro c x
        simp only [map_smul, smul_eq_mul, mul_smul, RingHom.id_apply, smul_add]
      left_inv := by
        intro x
        simp only [map_add (f := _), map_smul, hht, smul_eq_mul, mul_zero, add_zero, add_sub_cancel_right]
      right_inv := by
        intro x
        simp only [map_sub, map_smul, hht, smul_eq_mul, mul_zero, sub_zero, sub_add_cancel] }
  have hψ : ∀ x, ψ x = x + h x • t := fun x => rfl
  refine ⟨ψ, hψ, ?_, ?_⟩
  · intro x
    rw [hψ]
    exact key x _ (hts _)
  · intro j x
    rw [hψ]
    simp only [aff, Set.mem_setOf_eq]
    have e : x + h x • t - (Finsupp.single j 1) = (x - Finsupp.single j 1) + h x • t := by abel
    rw [e]
    exact key _ _ (hts _)

end GlobalTheory.ShearLow

section
open GlobalTheory.SeqCx Matrix
theorem _root_.GlobalTheory.T.exists_transvection_preserving_low_and_aff : ∀ (R : Type) [CommRing R] (n : ℕ) (h : (ℕ →₀ R) →ₗ[R] R) (t : ℕ →₀ R), t ∈ low R n → h t = 0 → ∃ ψ : (ℕ →₀ R) ≃ₗ[R] (ℕ →₀ R), (∀ x, ψ x = x + h x • t) ∧ (∀ x, ψ x ∈ low R n ↔ x ∈ low R n) ∧ ∀ j x, ψ x ∈ aff R n j ↔ x ∈ aff R n j := by
  first
  | exact @GlobalTheory.ShearLow.main
end
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ExistsAutomorphismPreservingTranslatesCoordOne

section

@[expose] public section

open GlobalTheory.SeqCx Matrix UpperTheory.V.KL

namespace GlobalTheory

theorem unimodular_to_coord_one : ∀ (R : Type) [CommRing R] (s : ℕ), StableRangeLe R s → ∀ (n : ℕ), s ≤ n →
    ∀ v : ℕ →₀ R, [v] ∈ uniM R (ℕ →₀ R) → ∃ ψ : (ℕ →₀ R) ≃ₗ[R] (ℕ →₀ R),
      (∀ x, ψ x ∈ low R (n + 1) ↔ x ∈ low R (n + 1)) ∧ (∀ j x, ψ x ∈ aff R (n + 1) j ↔ x ∈ aff R (n + 1) j) ∧
      ψ v n = 1 := by
  intro R _ s hs n hn v hv
  obtain ⟨F, hF⟩ := hv
  let f := F ⟨0, by simp⟩
  have hfv : f v = 1 := by
    have := hF ⟨0, by simp⟩ ⟨0, by simp⟩
    simpa [f] using this
  let a : Fin n → R := fun i => f (Finsupp.single (i : ℕ) 1)
  let h : (ℕ →₀ R) →ₗ[R] R := f - ∑ i : Fin n, a i • Finsupp.lapply (i : ℕ)
  have hh : ∀ x, h x = f x - ∑ i : Fin n, a i * x i := by
    intro x; simp [h]
  let r : Fin (n + 1) → R := Fin.snoc (fun i : Fin n => v i) (h v)
  have hr : Unimodular R r := by
    rw [Unimodular, Ideal.eq_top_iff_one]
    have e : (1:R) = ∑ i : Fin n, a i * r i.castSucc + 1 * r (Fin.last n) := by
      simp only [r, Fin.snoc_castSucc, Fin.snoc_last, hh, hfv, one_mul]
      ring
    rw [e]
    refine Ideal.add_mem _ (Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨_, rfl⟩))
      (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨_, rfl⟩))
  obtain ⟨t', ht'⟩ := hs n hn r hr
  simp only [r, Fin.snoc_castSucc, Fin.snoc_last] at ht'
  let t : ℕ →₀ R := ∑ j : Fin n, Finsupp.single (j : ℕ) (t' j)
  have htapp : ∀ k, t k = if hk : k < n then t' ⟨k, hk⟩ else 0 := by
    intro k
    simp only [t, Finsupp.finsetSum_apply, Finsupp.single_apply]
    split_ifs with hk
    · rw [Finset.sum_eq_single ⟨k, hk⟩]
      · simp
      · intro b _ hb; rw [if_neg]; intro e; apply hb; ext; exact e
      · simp
    · apply Finset.sum_eq_zero; intro b _; rw [if_neg]; intro e; apply hk; rw [← e]; exact b.2
  have htlow : t ∈ low R n := fun k hk => by rw [htapp, dite_eq_right (by omega)]
  have htlow' : t ∈ low R (n + 1) := fun k hk => htlow k (by omega)
  have hht : h t = 0 := by
    rw [hh]
    have h1 : f t = ∑ j : Fin n, t' j * a j := by

      simp only [t, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Finsupp.smul_single_one, map_smul, smul_eq_mul]
    have h2 : ∑ i : Fin n, a i * t i = ∑ j : Fin n, t' j * a j := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [htapp, dite_eq_left j.2, mul_comm]
    rw [h1, h2, sub_self]
  obtain ⟨ψ1, hψ1, hψ1l, hψ1a⟩ := GlobalTheory.T.exists_transvection_preserving_low_and_aff R (n + 1) h t htlow' hht
  have hv' : ∀ i : Fin n, ψ1 v i = v i + t' i * h v := by
    intro i
    rw [hψ1, Finsupp.add_apply, Finsupp.smul_apply, htapp, dite_eq_left i.2, smul_eq_mul, mul_comm]
  have hv'n : ψ1 v n = v n := by
    rw [hψ1, Finsupp.add_apply, Finsupp.smul_apply, htapp, dite_eq_right (lt_irrefl n), smul_zero, add_zero]
  have hmem : (1 - v n) ∈ Ideal.span (Set.range fun i : Fin n => v i + t' i * h v) := by
    rw [ht']; trivial
  obtain ⟨c, hc⟩ := (Ideal.mem_span_range_iff_exists_fun).1 hmem
  let h2 : (ℕ →₀ R) →ₗ[R] R := ∑ i : Fin n, c i • Finsupp.lapply (i : ℕ)
  have hh2 : ∀ x, h2 x = ∑ i : Fin n, c i * x i := by
    intro x; simp [h2]
  have ht2low : Finsupp.single n (1 : R) ∈ low R (n + 1) := fun k hk => by
    rw [Finsupp.single_apply, if_neg (by omega)]
  have hht2 : h2 (Finsupp.single n 1) = 0 := by
    rw [hh2]
    refine Finset.sum_eq_zero fun i _ => ?_
    have := i.2
    rw [Finsupp.single_apply, if_neg (by omega), mul_zero]
  obtain ⟨ψ2, hψ2, hψ2l, hψ2a⟩ := GlobalTheory.T.exists_transvection_preserving_low_and_aff R (n + 1) h2 _ ht2low hht2
  refine ⟨ψ1.trans ψ2, fun x => ?_, fun j x => ?_, ?_⟩
  · rw [LinearEquiv.trans_apply, hψ2l, hψ1l]
  · rw [LinearEquiv.trans_apply, hψ2a, hψ1a]
  · rw [LinearEquiv.trans_apply, hψ2, Finsupp.add_apply, Finsupp.smul_apply, Finsupp.single_eq_same,
      smul_eq_mul, mul_one, hh2, hv'n]
    have : ∑ i : Fin n, c i * ψ1 v i = 1 - v n := by
      rw [← hc]; exact Finset.sum_congr rfl fun i _ => by rw [hv' i]
    rw [this]; ring

end GlobalTheory

section
open GlobalTheory.SeqCx Matrix UpperTheory.V.KL
theorem _root_.GlobalTheory.T.exists_automorphism_preserving_translates_coord_one : ∀ (R : Type) [CommRing R] (s : ℕ), StableRangeLe R s → ∀ (n : ℕ), s ≤ n → ∀ v : ℕ →₀ R, [v] ∈ uniM R (ℕ →₀ R) → ∃ ψ : (ℕ →₀ R) ≃ₗ[R] (ℕ →₀ R), (∀ x, ψ x ∈ low R (n + 1) ↔ x ∈ low R (n + 1)) ∧ (∀ j x, ψ x ∈ aff R (n + 1) j ↔ x ∈ aff R (n + 1) j) ∧ ψ v n = 1 := by
  first
  | exact @GlobalTheory.unimodular_to_coord_one
end
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ExactAtLinkInSuccUnionTranslateOfNeNil

section

@[expose] public section

open GlobalTheory.SeqCx Matrix UpperTheory.V.KL

namespace GlobalTheory

theorem uniM_map_equiv {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (ψ : M ≃ₗ[R] M)
    {τ : List M} (hτ : τ ∈ uniM R M) : τ.map ψ ∈ uniM R M := by
  exact ((T.subClosed_and_perm_and_linearEquiv_invariant_uniM R M).2.2 ψ τ).mpr hτ

theorem linkExact_low_union_aff_of_ne_nil : ∀ (R : Type) [CommRing R] (s : ℕ), StableRangeLe R s → ∀ n : ℕ, s ≤ n →
    LinkExactAff R s n → ∀ j : ℕ, n + 1 ≤ j → ∀ τ ∈ uniM R (ℕ →₀ R), τ ≠ [] → ∀ p : ℕ,
    p + s + τ.length ≤ n + 2 →
    ExactAt (linkIn (uniM R (ℕ →₀ R)) (low R (n + 1) ∪ aff R (n + 1) j) τ) p := by
  intro R _ s hs n hn hL j hj τ hτ hne p hp
  obtain ⟨v, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
  have hv : [v] ∈ uniM R (ℕ →₀ R) := (T.subClosed_and_perm_and_linearEquiv_invariant_uniM R (ℕ →₀ R)).1 _ hτ [v] (by simp)
  obtain ⟨ψ, hlow, haff, hψv⟩ := T.exists_automorphism_preserving_translates_coord_one R s hs n hn v hv
  refine T.exactAt_linkIn_uniM_of_exactAt_map_linearEquiv R (ℕ →₀ R) ψ (low R (n + 1) ∪ aff R (n + 1) j) ?_ _ p ?_
  · intro x
    simp only [Set.mem_union, hlow, haff]
  · refine T.exactAt_link_succ_union_translate_of_coord_one R s n hL j hj _ (uniM_map_equiv ψ hτ) (ψ v) (by simp) hψv p ?_
    simpa using hp

end GlobalTheory

section
open GlobalTheory.SeqCx Matrix UpperTheory.V.KL
theorem _root_.GlobalTheory.T.exactAt_linkIn_succ_union_translate_of_ne_nil : ∀ (R : Type) [CommRing R] (s : ℕ), StableRangeLe R s → ∀ n : ℕ, s ≤ n → LinkExactAff R s n → ∀ j : ℕ, n + 1 ≤ j → ∀ τ ∈ uniM R (ℕ →₀ R), τ ≠ [] → ∀ p : ℕ, p + s + τ.length ≤ n + 2 → ExactAt (linkIn (uniM R (ℕ →₀ R)) (low R (n + 1) ∪ aff R (n + 1) j) τ) p := by
  first
  | exact @GlobalTheory.linkExact_low_union_aff_of_ne_nil
  | exact @GlobalTheory.uniM_map_equiv
end
end
end
