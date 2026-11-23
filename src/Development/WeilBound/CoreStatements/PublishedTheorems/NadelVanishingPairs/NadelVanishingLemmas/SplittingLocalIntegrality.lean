module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFlatLift
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Data.Nat.Prime.Factorial
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechAntisymmetrizedCupProductLeadingTermStatement
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CupProductFiltrationBound
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsFrobeniusSplittingDatumStatement
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.FrobeniusSplittingClosedStatement
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SplittingIntegralFormsBoundStatement
import Mathlib.Order.CompletePartialOrder

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierPropertyAtSignMulFactorialScaling

section

@[expose] public section

open GlobalTheory GlobalTheory.DI

namespace GlobalTheory.DI

theorem exists_inv_signFactorial {E : Type} [AddCommGroup E] (p : ℕ) [hp : Fact p.Prime]
    (hE : ∀ x : E, p • x = 0) (a : ℕ) (ha : a < p) :
    ∃ u : ℤ, ∀ y : E, (u * ((-1 : ℤ) ^ a * (a.factorial : ℤ))) • y = y := by
  have hcop : IsCoprime ((-1 : ℤ) ^ a * (a.factorial : ℤ)) (p : ℤ) := by
    apply IsCoprime.mul_left
    · exact IsCoprime.pow_left (isCoprime_one_left.neg_left)
    · rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
      exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp.out).2
        (fun h => absurd ((Nat.Prime.dvd_factorial hp.out).1 h) (by omega)))
  obtain ⟨u, v, huv⟩ := hcop
  refine ⟨u, fun y => ?_⟩
  have h1 : u * ((-1 : ℤ) ^ a * (a.factorial : ℤ)) = 1 - v * p := by linarith
  rw [h1, sub_smul, one_smul, mul_smul, natCast_zsmul, hE, smul_zero, sub_zero]

theorem cartierAt_signFactorial : ∀ {E : Type} [AddCommGroup E] (p : ℕ) [Fact p.Prime] (d γ : E →+ E) (γ' : E → E)
    (N T : ℕ → AddSubgroup E), (∀ x : E, p • x = 0) → (∀ a, p ≤ a → N a = ⊥) →
    (∀ a, ∀ x ∈ N a, γ' x = ((-1 : ℤ) ^ a * (a.factorial : ℤ)) • γ x) → CartierAt d γ N T → CartierAt d γ' N T := by
  intro E _ p hp d γ γ' N T hE hN hγ hC
  have hp0 : 0 < p := hp.out.pos
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx h0
    rw [hγ 0 x hx] at h0
    simp at h0
    exact hC.inj_zero x hx h0
  · intro a x hx z hz h
    by_cases hpa : p ≤ a + 1
    · rw [hN _ hpa] at hx; exact (AddSubgroup.mem_bot.1 hx)
    · obtain ⟨u, hu⟩ := exists_inv_signFactorial (E := E) p hE (a + 1) (by omega)
      apply hC.inj_succ a x hx (u • z) (AddSubgroup.zsmul_mem _ hz u)
      rw [hγ _ x hx] at h
      rw [map_zsmul, ← h, ← mul_smul, hu]
  · intro y hy hd
    obtain ⟨x, hx, rfl⟩ := hC.surj_zero y hy hd
    exact ⟨x, hx, by rw [hγ 0 x hx]; simp⟩
  · intro a y hy hd
    obtain ⟨x, hx, z, hz, rfl⟩ := hC.surj_succ a y hy hd
    by_cases hpa : p ≤ a + 1
    · have hx0 : x = 0 := by rw [hN _ hpa] at hx; exact AddSubgroup.mem_bot.1 hx
      subst hx0
      refine ⟨0, AddSubgroup.zero_mem _, z, hz, ?_⟩
      rw [hγ (a + 1) 0 (AddSubgroup.zero_mem _)]; simp
    · obtain ⟨u, hu⟩ := exists_inv_signFactorial (E := E) p hE (a + 1) (by omega)
      refine ⟨u • x, AddSubgroup.zsmul_mem _ hx u, z, hz, ?_⟩
      rw [hγ _ _ (AddSubgroup.zsmul_mem _ hx u), map_zsmul, ← mul_smul, mul_comm, hu]

end GlobalTheory.DI
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierPropertyAtSignMulFactorialScalingStatement

section

@[expose] public section

open GlobalTheory GlobalTheory.DI

theorem _root_.GlobalTheory.T.cartierPropertyAt_sign_mul_factorial_scaling : ∀ {E : Type} [AddCommGroup E] (p : ℕ) [Fact p.Prime] (d γ : E →+ E) (γ' : E → E) (N T : ℕ → AddSubgroup E), (∀ x : E, p • x = 0) → (∀ a, p ≤ a → N a = ⊥) → (∀ a, ∀ x ∈ N a, γ' x = ((-1 : ℤ) ^ a * (a.factorial : ℤ)) • γ x) → CartierAt d γ N T → CartierAt d γ' N T := by
  first | exact @GlobalTheory.DI.cartierAt_signFactorial | exact GlobalTheory.DI.cartierAt_signFactorial | (intros; apply GlobalTheory.DI.cartierAt_signFactorial <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechAntisymmetrizedCupProductVanishAboveDegree

section

@[expose] public section

open GlobalTheory GlobalTheory.DI

namespace GlobalTheory.DI

theorem prodL_eq_zero_of_card {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type}
    [LinearOrder ι] (f : ι → V →+ V) (h : ι → ι → V →+ K) (vs : List V) (t : Finset ι)
    (ht : vs.length + 1 < t.card) : prodL f h vs t = 0 := by
  induction vs generalizing t with
  | nil =>
    simp only [prodL, List.foldr_nil, oneC]
    simp only [List.length_nil] at ht
    rw [if_neg (by omega)]
  | cons v vs ih =>
    change Lop f h v (prodL f h vs) t = 0
    simp only [List.length_cons] at ht
    unfold Lop
    split_ifs with h1 h2
    · have e1 := ih t (by omega)
      have e2 := ih (t.erase (t.min' h1))
        (by rw [Finset.card_erase_of_mem (Finset.min'_mem _ _)]; omega)
      rw [e1, e2, mul_zero, smul_zero, smul_zero, add_zero]
    · have e1 := ih t (by omega)
      rw [e1, mul_zero, smul_zero, add_zero]
    · rfl

theorem alt_and_phi_vanish_above_degree : ∀ {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι] (p : ℕ) (f : ι → V →+ V) (h : ι → ι → V →+ K), (∀ (a : ℕ) (v : Fin a → V) (t : Finset ι), a + 1 < t.card → alt f h a v t = 0) ∧ ∀ (Φ : ExteriorAlgebra K V →+ (Finset ι → ExteriorAlgebra K V)), IsPhi p f h Φ → ∀ a, ∀ x ∈ forms (Set.univ : Set K) (Set.univ : Set V) a, ∀ t : Finset ι, a + 1 < t.card → Φ x t = 0 := by
  intro K _ V _ _ ι _ p f h
  have halt : ∀ (a : ℕ) (v : Fin a → V) (t : Finset ι), a + 1 < t.card → alt f h a v t = 0 := by
    intro a v t ht
    simp only [alt, Finset.sum_apply, Pi.smul_apply]
    apply Finset.sum_eq_zero
    intro σ _
    rw [prodL_eq_zero_of_card f h _ t (by simpa using ht), smul_zero]
  refine ⟨halt, ?_⟩
  intro Φ hΦ a x hx t ht
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨b, -, v, -, rfl⟩ := hx
    rw [hΦ, Pi.smul_apply, halt a v t ht, smul_zero]
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | neg x _ hx => simp [hx]

end GlobalTheory.DI
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechAntisymmetrizedCupProductVanishAboveDegreeStatement

section

@[expose] public section

open GlobalTheory GlobalTheory.DI

theorem _root_.GlobalTheory.T.cechAntisymmetrizedCupProduct_vanish_above_degree : ∀ {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι] (p : ℕ) (f : ι → V →+ V) (h : ι → ι → V →+ K), (∀ (a : ℕ) (v : Fin a → V) (t : Finset ι), a + 1 < t.card → alt f h a v t = 0) ∧ ∀ (Φ : ExteriorAlgebra K V →+ (Finset ι → ExteriorAlgebra K V)), IsPhi p f h Φ → ∀ a, ∀ x ∈ forms (Set.univ : Set K) (Set.univ : Set V) a, ∀ t : Finset ι, a + 1 < t.card → Φ x t = 0 := by
  first | exact @GlobalTheory.DI.alt_and_phi_vanish_above_degree | exact GlobalTheory.DI.alt_and_phi_vanish_above_degree | (intros; apply GlobalTheory.DI.alt_and_phi_vanish_above_degree <;> assumption)
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CupProductFiltrationBoundStatement

section

@[expose] public section

open GlobalTheory GlobalTheory.DI
theorem _root_.GlobalTheory.T.cechZero_of_hypZero_of_cartier : ∀ {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E] (d : E →+ E) (N T : ℕ → Finset ι → AddSubgroup E) (Φ : E →+ (Finset ι → E)), (∀ x, d (d x) = 0) → (∀ q s t, s.Nonempty → s ⊆ t → N q s ≤ N q t) → (∀ q s t, s.Nonempty → s ⊆ t → T q s ≤ T q t) → (∀ q s x, x ∈ T q s → d x ∈ T (q + 1) s) → (∀ x, Φ x ∅ = 0) → (∀ x, Dtot d (Φ x) = 0) → (∀ a u t x, u.Nonempty → t ⊆ u → x ∈ N a u → (∀ q, q + t.card = a + 1 → Φ x t ∈ T q u) ∧ (a + 1 < t.card → Φ x t = 0)) → (∀ s, ∀ j ∈ s, CartierAt d (fun x => Φ x {j}) (fun a => N a s) (fun a => T a s)) → ∀ a b, HypZero d T (a + b) → CechZero (N a) b := by
  first | exact @_root_.GlobalTheory.DI.cechZero_of_hypZero_of_closed_map | exact _root_.GlobalTheory.DI.cechZero_of_hypZero_of_closed_map | (intros; apply _root_.GlobalTheory.DI.cechZero_of_hypZero_of_closed_map <;> assumption)
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SplittingLocalIntegrality

section

@[expose] public section

open GlobalTheory GlobalTheory.DI

namespace GlobalTheory.DI

private theorem forms_mono' {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V]
    {B B' : Set K} {L L' : Set V} (hB : B ⊆ B') (hL : L ⊆ L') (q : ℕ) :
    forms B L q ≤ forms B' L' q := by
  unfold forms
  apply AddSubgroup.closure_mono
  rintro x ⟨b, hb, v, hv, rfl⟩
  exact ⟨b, hB hb, v, fun k => hL (hv k), rfl⟩

private theorem iota_mem_forms_one' {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V]
    (A : Subring K) (w : V) : ExteriorAlgebra.ι K w ∈ forms (A : Set K) (Set.univ : Set V) 1 := by
  unfold forms
  apply AddSubgroup.subset_closure
  refine ⟨1, A.one_mem, fun _ => w, fun _ => trivial, ?_⟩
  rw [one_smul, ExteriorAlgebra.ιMulti_apply]
  simp

private theorem psmul_zero' {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V]
    (p : ℕ) [CharP K p] (x : ExteriorAlgebra K V) : p • x = 0 := by
  rw [nsmul_eq_mul, ← map_natCast (algebraMap K (ExteriorAlgebra K V)), CharP.cast_eq_zero, map_zero,
    zero_mul]

theorem decomp_pointwise : ∀ {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι] (p : ℕ) [Fact p.Prime] [CharP K p] (d : ExteriorAlgebra K V →+ ExteriorAlgebra K V) (f : ι → V →+ V) (h : ι → ι → V →+ K) (γ : ι → ExteriorAlgebra K V →+* ExteriorAlgebra K V) {P : Type} (U : Finset ι → Set P) (A : P → Subring K) (B : P → Set K) (L : P → Set V) (N T : ℕ → Finset ι → AddSubgroup (ExteriorAlgebra K V)), IsOddDer d → IsDatum p d f h → (∀ i, IsGamma p (f i) (γ i)) → (∀ q s t, s.Nonempty → s ⊆ t → N q s ≤ N q t) → (∀ q s t, s.Nonempty → s ⊆ t → T q s ≤ T q t) → (∀ q s x, x ∈ T q s → d x ∈ T (q + 1) s) → (∀ a s, s.Nonempty → N a s ≤ forms (Set.univ : Set K) (Set.univ : Set V) a) → (∀ a s, s.Nonempty → p ≤ a → N a s = ⊥) → (∀ a s, s.Nonempty → ∀ y ∈ U s, N a s ≤ forms (B y) (L y) a) → (∀ q s x, s.Nonempty → x ∈ forms (Set.univ : Set K) (Set.univ : Set V) q → (∀ y ∈ U s, x ∈ forms {z | ∃ c ∈ B y, ∃ b ∈ A y, z = c ^ p * b} (L y) q) → x ∈ T q s) → (∀ s, ∀ y ∈ U s, ∀ i ∈ s, ∀ v ∈ L y, ExteriorAlgebra.ι K (f i v) ∈ forms (A y : Set K) (L y) 1) → (∀ s, ∀ y ∈ U s, ∀ i ∈ s, ∀ j ∈ s, ∀ v ∈ L y, h i j v ∈ A y) → (∀ s, ∀ j ∈ s, CartierAt d (γ j) (fun a => N a s) (fun a => T a s)) → ∀ a b, HypZero d T (a + b) → CechZero (N a) b := by
  intro K _ V _ _ ι _ p _ _ d f h γ P U A B L N T hd hD hγ hNm hTm hTd hNu hNp hNU hT hfA hhA hC
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.exists_frobenius_splitting_datum p d f h hD
  obtain ⟨h0, hcl⟩ := GlobalTheory.T.frobenius_splitting_closed p d f h Φ hd hD hΦ
  have hvan := (GlobalTheory.T.cechAntisymmetrizedCupProduct_vanish_above_degree p f h).2 Φ hΦ
  apply GlobalTheory.T.cechZero_of_hypZero_of_cartier d N T Φ hd.sq hNm hTm hTd h0 hcl
  · intro a u t x hu htu hx
    have hxu : x ∈ forms (Set.univ : Set K) (Set.univ : Set V) a := hNu a u hu hx
    refine ⟨fun q hq => ?_, fun hlt => hvan a x hxu t hlt⟩
    apply hT q u _ hu
    · have := GlobalTheory.T.splitting_integral_forms_bound p f h Φ (⊤ : Subring K) Set.univ Set.univ t hΦ
        (fun i _ v _ => iota_mem_forms_one' ⊤ (f i v)) (fun _ _ _ _ _ _ => Subring.mem_top _) a q t
        subset_rfl hq x hxu
      exact forms_mono' (Set.subset_univ _) subset_rfl q this
    · intro y hy
      exact GlobalTheory.T.splitting_integral_forms_bound p f h Φ (A y) (B y) (L y) u hΦ (hfA u y hy) (hhA u y hy) a q t htu hq x
        (hNU a u hu y hy hx)
  · intro s j hj
    have hs : s.Nonempty := ⟨j, hj⟩
    exact GlobalTheory.T.cartierPropertyAt_sign_mul_factorial_scaling p d (γ j).toAddMonoidHom (fun x => Φ x {j}) (fun a => N a s) (fun a => T a s)
      (psmul_zero' p) (fun a ha => hNp a s hs ha)
      (fun a x hx => (GlobalTheory.T.cechAntisymmetrizedCupProduct_leading_term p f h).2 Φ j (γ j) hΦ (hγ j) a x (hNu a s hs hx)) (hC s j hj)

end GlobalTheory.DI
end
end
