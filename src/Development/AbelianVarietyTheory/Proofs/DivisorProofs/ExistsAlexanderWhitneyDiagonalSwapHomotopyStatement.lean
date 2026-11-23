module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FaceSubMid
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.TypeStar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrismChainComplexBoundaryIdentitiesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardSimplexFacePairsAcyclicPositiveDegreeStatement
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlexanderWhitneyDiagonalAndSwapChainMaps

section

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.AWChain

open GlobalTheory.EtC.CupSpec (sub_δ_val δ_sub_val sub_val hom_ext_val)

def cm (N j l : ℕ) : SimplexCategory.mk l ⟶ SimplexCategory.mk N :=
  if h : j + l ≤ N then SimplexCategory.subinterval j l h else SimplexCategory.const _ _ 0

theorem cm_eq (N j l : ℕ) (h : j + l ≤ N) : cm N j l = SimplexCategory.subinterval j l h := dif_pos h

section
variable {N : ℕ}

theorem cm_δ_le (j l : ℕ) (h : j + l ≤ N) (i : Fin (N + 2)) (hi : (i : ℕ) ≤ j) : cm N j l ≫ SimplexCategory.δ i = cm (N + 1) (j + 1) l := by
  rw [cm_eq N j l h, cm_eq (N + 1) (j + 1) l (by omega)]
  refine hom_ext_val _ _ fun v => ?_
  rw [sub_δ_val, sub_val]
  split_ifs <;> omega

theorem cm_δ_gt (j l : ℕ) (h : j + l ≤ N) (i : Fin (N + 2)) (hi : j + l < (i : ℕ)) : cm N j l ≫ SimplexCategory.δ i = cm (N + 1) j l := by
  rw [cm_eq N j l h, cm_eq (N + 1) j l (by omega)]
  refine hom_ext_val _ _ fun v => ?_
  rw [sub_δ_val, sub_val]
  split_ifs <;> omega

theorem cm_δ_mid (j l : ℕ) (h : j + l ≤ N) (i : Fin (N + 2)) (i' : Fin (l + 2)) (hi : (i : ℕ) = j + i') :
    cm N j l ≫ SimplexCategory.δ i = SimplexCategory.δ i' ≫ cm (N + 1) j (l + 1) := by
  rw [cm_eq N j l h, cm_eq (N + 1) j (l + 1) (by omega)]
  refine hom_ext_val _ _ fun v => ?_
  rw [sub_δ_val, δ_sub_val]
  split_ifs <;> omega

end

theorem telescope {N : ℕ} {A : Type*} [AddCommGroup A] {p r : ℕ} (hN : p + r = N)
    (φ : (SimplexCategory.mk p ⟶ SimplexCategory.mk (N + 1)) → (SimplexCategory.mk r ⟶ SimplexCategory.mk (N + 1)) → A) :
    ∑ i : Fin (N + 2), (-1 : ℤ) ^ (i : ℕ) • φ (cm N 0 p ≫ SimplexCategory.δ i) (cm N p r ≫ SimplexCategory.δ i) =
      ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • φ (SimplexCategory.δ i ≫ cm (N + 1) 0 (p + 1)) (cm (N + 1) (p + 1) r) +
      (-1 : ℤ) ^ p • ∑ j : Fin (r + 2), (-1 : ℤ) ^ (j : ℕ) •
        φ (cm (N + 1) 0 p) (SimplexCategory.δ j ≫ cm (N + 1) p (r + 1)) := by
  have e1 : SimplexCategory.δ (Fin.last (p + 1)) ≫ cm (N + 1) 0 (p + 1) = cm (N + 1) 0 p := by
    rw [cm_eq (N + 1) 0 (p + 1) (by omega), cm_eq (N + 1) 0 p (by omega)]
    refine hom_ext_val _ _ fun v => ?_
    rw [δ_sub_val, sub_val]
    have := v.2
    simp only [Fin.val_last]
    split_ifs <;> omega
  have e2 : SimplexCategory.δ 0 ≫ cm (N + 1) p (r + 1) = cm (N + 1) (p + 1) r := by
    rw [cm_eq (N + 1) p (r + 1) (by omega), cm_eq (N + 1) (p + 1) r (by omega)]
    refine hom_ext_val _ _ fun v => ?_
    rw [δ_sub_val, sub_val]
    simp; omega
  rw [← Fin.sum_congr' _ (show (p + 1) + (r + 1) = N + 2 by omega), Fin.sum_univ_add,
    Fin.sum_univ_castSucc (n := p + 1), Fin.sum_univ_succ (n := r + 1), e1, e2, smul_add, Finset.smul_sum]
  have c : (-1 : ℤ) ^ ((Fin.last (p + 1) : Fin (p + 2)) : ℕ) • φ (cm (N + 1) 0 p) (cm (N + 1) (p + 1) r) +
      (-1 : ℤ) ^ p • (-1 : ℤ) ^ ((0 : Fin (r + 2)) : ℕ) • φ (cm (N + 1) 0 p) (cm (N + 1) (p + 1) r) = 0 := by
    simp [pow_succ]
  have key : ∀ a b c d e f : A, c + d = 0 → a = e → b = f → a + b = e + c + (d + f) := by
    rintro a b c d _ _ h rfl rfl
    rw [add_assoc, ← add_assoc c, h, zero_add]
  refine key _ _ _ _ _ _ c (Finset.sum_congr rfl fun i _ => ?_) (Finset.sum_congr rfl fun j _ => ?_)
  · have := i.2
    rw [cm_δ_mid 0 p (by omega) _ i.castSucc (by simp), cm_δ_le p r (by omega) _ (by simp; omega)]
    rfl
  · have := j.2
    rw [cm_δ_mid p r (by omega) _ j.succ (by simp; omega), cm_δ_gt 0 p (by omega) _ (by simp; omega), smul_smul, ← pow_add]
    congr 2
    simp; omega

theorem aw_eq (N : ℕ) : Pr.aw N = ∑ q ∈ Finset.HasAntidiagonal.antidiagonal N,
    Finsupp.single (⟨q.1, q.2, cm N 0 q.1, cm N q.1 q.2⟩ : Pr N) (1 : ℤ) := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range, Pr.aw]
  refine Finset.sum_congr rfl fun p _ => ?_
  have := p.2
  rw [cm_eq N 0 p (by omega), cm_eq N p (N - p) (by omega)]

theorem d₁_zero {N r : ℕ} (a : SimplexCategory.mk 0 ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk r ⟶ SimplexCategory.mk N) :
    Pr.d₁ (⟨0, r, a, b⟩ : Pr N) = 0 := rfl

theorem d₂_zero {N p : ℕ} (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk 0 ⟶ SimplexCategory.mk N) :
    Pr.d₂ (⟨p, 0, a, b⟩ : Pr N) = 0 := rfl

theorem d₁_succ {N p r : ℕ} (a : SimplexCategory.mk (p + 1) ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk r ⟶ SimplexCategory.mk N) :
    Pr.d₁ (⟨p + 1, r, a, b⟩ : Pr N) =
      ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • Finsupp.single (⟨p, r, SimplexCategory.δ i ≫ a, b⟩ : Pr N) (1 : ℤ) := by
  simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
  rfl

theorem d₂_succ {N p r : ℕ} (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk (r + 1) ⟶ SimplexCategory.mk N) :
    Pr.d₂ (⟨p, r + 1, a, b⟩ : Pr N) =
      ∑ j : Fin (r + 2), (-1 : ℤ) ^ (j : ℕ) • Finsupp.single (⟨p, r, a, SimplexCategory.δ j ≫ b⟩ : Pr N) (1 : ℤ) := by
  simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
  rfl

theorem d_aw (N : ℕ) : Pr.d (N + 1) (Pr.aw (N + 1)) = Pr.bd (Pr.aw N) := by

  rw [aw_eq, aw_eq, map_sum]
  simp only [Pr.d, Finsupp.linearCombination_single, one_smul, Finset.sum_add_distrib]
  rw [Finset.Nat.sum_antidiagonal_succ, Finset.Nat.sum_antidiagonal_succ']
  simp only [d₁_zero, d₂_zero, smul_zero, zero_add, d₁_succ, d₂_succ]

  simp only [Pr.bd, map_sum, Pr.push, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, Finset.smul_sum]
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hN : q.1 + q.2 = N := by simpa using hq
  symm
  refine (telescope hN (fun a b => Finsupp.single (⟨q.1, q.2, a, b⟩ : Pr (N + 1)) (1 : ℤ))).trans ?_
  rw [Finset.smul_sum]

theorem wa_eq (N : ℕ) : Pr.wa N = ∑ q ∈ Finset.HasAntidiagonal.antidiagonal N,
    (-1 : ℤ) ^ (q.1 * q.2) • Finsupp.single (⟨q.2, q.1, cm N q.1 q.2, cm N 0 q.1⟩ : Pr N) (1 : ℤ) := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range, Pr.wa]
  refine Finset.sum_congr rfl fun p _ => ?_
  have := p.2
  rw [cm_eq N 0 p (by omega), cm_eq N p (N - p) (by omega), Finsupp.smul_single, smul_eq_mul, mul_one]

theorem d_wa (N : ℕ) : Pr.d (N + 1) (Pr.wa (N + 1)) = Pr.bd (Pr.wa N) := by

  rw [wa_eq, wa_eq, map_sum]
  simp only [map_zsmul, Pr.d, Finsupp.linearCombination_single, one_smul, smul_add, Finset.sum_add_distrib]
  rw [Finset.Nat.sum_antidiagonal_succ', Finset.Nat.sum_antidiagonal_succ]
  simp only [d₁_zero, d₂_zero, smul_zero, zero_add, d₁_succ, d₂_succ]

  simp only [Pr.bd, map_sum, map_zsmul, Pr.push, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, Finset.smul_sum]
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hN : q.1 + q.2 = N := by simpa using hq
  obtain ⟨p, r⟩ := q
  dsimp only at hN ⊢
  have T := telescope hN (fun a b => Finsupp.single (⟨r, p, b, a⟩ : Pr (N + 1)) (1 : ℤ))
  conv_rhs => arg 2; ext x; rw [smul_comm]
  rw [← Finset.smul_sum (r := (-1 : ℤ) ^ (p * r)), T, smul_add, Finset.smul_sum, Finset.smul_sum, Finset.smul_sum]
  conv_rhs => rw [add_comm]
  have s1 : (-1 : ℤ) ^ (p * (r + 1)) = (-1) ^ (p * r) * (-1) ^ p := by ring
  have s2 : (-1 : ℤ) ^ ((p + 1) * r) * (-1) ^ r = (-1) ^ (p * r) := by
    rw [← pow_add, show (p + 1) * r + r = p * r + 2 * r by ring, pow_add, pow_mul]
    norm_num
  congr 1 <;> refine Finset.sum_congr rfl fun x _ => ?_
  · simp only [smul_smul, s1, mul_assoc]
  · simp only [smul_smul]
    rw [← mul_assoc, s2]

theorem aw_wa_chain : ∀ N, Pr.d (N + 1) (Pr.aw (N + 1)) = Pr.bd (Pr.aw N) ∧
    Pr.d (N + 1) (Pr.wa (N + 1)) = Pr.bd (Pr.wa N) :=
  fun N => ⟨d_aw N, d_wa N⟩

end GlobalTheory.EtC.AWChain

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlexanderWhitneyDiagonalAndSwapChainMapsStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.alexanderWhitneyDiagonal_and_swap_chain_maps : ∀ N, Pr.d (N + 1) (Pr.aw (N + 1)) = Pr.bd (Pr.aw N) ∧ Pr.d (N + 1) (Pr.wa (N + 1)) = Pr.bd (Pr.wa N) := by
  first | exact @GlobalTheory.EtC.AWChain.aw_wa_chain | exact GlobalTheory.EtC.AWChain.aw_wa_chain | (intros; apply GlobalTheory.EtC.AWChain.aw_wa_chain <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlexanderWhitneyDiagonalSwapHomotopy

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.PrHomotopy

lemma deg_sub {N k : ℕ} {a b : Pr N →₀ ℤ} (ha : Pr.Deg k a) (hb : Pr.Deg k b) : Pr.Deg k (a - b) := by
  intro z hz
  rcases Finset.mem_union.1 (Finsupp.support_sub hz) with h | h
  · exact ha z h
  · exact hb z h

lemma deg_zero {N k : ℕ} : Pr.Deg k (0 : Pr N →₀ ℤ) := by
  intro z hz; simp at hz

lemma bd_sub {N : ℕ} (a b : Pr N →₀ ℤ) : Pr.bd (a - b) = Pr.bd a - Pr.bd b := by
  simp [Pr.bd, map_sub, smul_sub, Finset.sum_sub_distrib]

lemma aw_zero_eq_wa_zero : Pr.aw 0 = Pr.wa 0 := by
  simp [Pr.aw, Pr.wa]


open Classical in
noncomputable def step (N : ℕ) (c : Pr N →₀ ℤ) : Pr (N + 1) →₀ ℤ :=
  if H : ∃ e, Pr.Deg (N + 2) e ∧ Pr.d (N + 1) e = Pr.aw (N + 1) - Pr.wa (N + 1) - Pr.bd c then H.choose else 0

noncomputable def hom : ∀ N, Pr N →₀ ℤ
  | 0 => 0
  | N + 1 => step N (hom N)

lemma step_spec (N : ℕ) (c : Pr N →₀ ℤ) (hc : Pr.Deg (N + 1) c)
    (hd : Pr.bd (Pr.d N c) = Pr.bd (Pr.aw N - Pr.wa N)) :
    Pr.Deg (N + 2) (step N c) ∧ Pr.d (N + 1) (step N c) = Pr.aw (N + 1) - Pr.wa (N + 1) - Pr.bd c := by
  obtain ⟨-, -, -, hbdeg, -, hdbd, haw⟩ := GlobalTheory.T.prism_chain_complex_boundary_identities
  have H : ∃ e, Pr.Deg (N + 2) e ∧ Pr.d (N + 1) e = Pr.aw (N + 1) - Pr.wa (N + 1) - Pr.bd c := by
    apply GlobalTheory.T.standardSimplexFacePairs_acyclic_positive_degree (N + 1) N
    · exact deg_sub (deg_sub (haw (N + 1)).1 (haw (N + 1)).2) (hbdeg _ _ _ hc)
    · obtain ⟨h1, h2⟩ := GlobalTheory.T.alexanderWhitneyDiagonal_and_swap_chain_maps N
      rw [map_sub, map_sub, h1, h2, hdbd, hd, bd_sub, sub_self]
  unfold step
  rw [dite_eq_left H]
  exact H.choose_spec

lemma hom_spec (N : ℕ) : Pr.Deg (N + 1) (hom N) ∧ Pr.bd (Pr.d N (hom N)) = Pr.bd (Pr.aw N - Pr.wa N) := by
  induction N with
  | zero => exact ⟨deg_zero, by simp [hom, aw_zero_eq_wa_zero]⟩
  | succ N ih =>
    obtain ⟨h1, h2⟩ := step_spec N (hom N) ih.1 ih.2
    obtain ⟨-, -, -, -, hbb, -, -⟩ := GlobalTheory.T.prism_chain_complex_boundary_identities
    refine ⟨h1, ?_⟩
    show Pr.bd (Pr.d (N + 1) (step N (hom N))) = _
    rw [h2, bd_sub, hbb, sub_zero]

end GlobalTheory.EtC.PrHomotopy

theorem GlobalTheory.EtC.pr_aw_wa_homotopy :
    ∃ h : ∀ N, Pr N →₀ ℤ, (∀ N, Pr.Deg (N + 1) (h N)) ∧ Pr.d 0 (h 0) = Pr.aw 0 - Pr.wa 0 ∧
      ∀ N, Pr.d (N + 1) (h (N + 1)) + Pr.bd (h N) = Pr.aw (N + 1) - Pr.wa (N + 1) := by
  refine ⟨PrHomotopy.hom, fun N => (PrHomotopy.hom_spec N).1, ?_, fun N => ?_⟩
  · simp [PrHomotopy.hom, PrHomotopy.aw_zero_eq_wa_zero]
  · have := (PrHomotopy.step_spec N (PrHomotopy.hom N) (PrHomotopy.hom_spec N).1 (PrHomotopy.hom_spec N).2).2
    show Pr.d (N + 1) (PrHomotopy.step N (PrHomotopy.hom N)) + _ = _
    rw [this, sub_add_cancel]
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlexanderWhitneyDiagonalSwapHomotopyStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.exists_alexanderWhitneyDiagonal_swap_homotopy : ∃ h : ∀ N, Pr N →₀ ℤ, (∀ N, Pr.Deg (N + 1) (h N)) ∧ Pr.d 0 (h 0) = Pr.aw 0 - Pr.wa 0 ∧ ∀ N, Pr.d (N + 1) (h (N + 1)) + Pr.bd (h N) = Pr.aw (N + 1) - Pr.wa (N + 1) := by
  first | exact @GlobalTheory.EtC.pr_aw_wa_homotopy | exact GlobalTheory.EtC.pr_aw_wa_homotopy | (intros; apply GlobalTheory.EtC.pr_aw_wa_homotopy <;> assumption)
end
end
