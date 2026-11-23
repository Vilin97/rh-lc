module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.NotIsGenericDetRepTwo
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EsymmMulSchurPolynomialJacobiTrudiStatement
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Fintype.Powerset
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalWhittakerTorusHeckeRecursionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhittakerEqZeroOfNotAntitoneStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PieriRecursionUnique

section

@[expose] public section

open scoped Classical

namespace GlobalTheory

theorem pieri_recursion_zero (n : ℕ) (c : ℕ → ℂ) (D : (Fin n → ℕ) → ℂ)
    (hD : ∀ l, ¬ Antitone l → D l = 0)
    (hr : ∀ l, Antitone l → ∀ j ≤ n, ∑ J ∈ (Finset.univ : Finset (Finset (Fin n))).filter
      (fun J => J.card = j), D (l + (fun i => if i ∈ J then 1 else 0)) = c j * D l)
    (h0 : D 0 = 0) : ∀ μ, D μ = 0 := by
  have main : ∀ s k (μ : Fin n → ℕ), ∑ i, μ i = s →
      n - (Finset.univ.filter (fun i => μ i ≠ 0)).card = k → D μ = 0 := by
    intro s
    refine Nat.strong_induction_on s ?_
    intro s ihs k
    refine Nat.strong_induction_on k ?_
    intro k ihk μ hs hk
    by_cases hμ : Antitone μ
    swap
    · exact hD μ hμ
    by_cases hz : μ = 0
    · subst hz; exact h0
    set J0 : Finset (Fin n) := Finset.univ.filter (fun i => μ i ≠ 0) with hJ0
    set l : Fin n → ℕ := fun i => μ i - 1 with hl
    have hla : Antitone l := fun a b hab => Nat.sub_le_sub_right (hμ hab) 1
    have hj : J0.card ≤ n := by simpa using Finset.card_le_univ J0
    have hlμ : l + (fun i => if i ∈ J0 then 1 else 0) = μ := by
      funext i
      simp only [Pi.add_apply, hl, hJ0, Finset.mem_filter, Finset.mem_univ, true_and]
      split_ifs with h <;> omega
    have hsum : ∀ J : Finset (Fin n),
        ∑ i, ((l + (fun i => if i ∈ J then 1 else 0) : Fin n → ℕ)) i = ∑ i, l i + J.card := by
      intro J
      simp [Finset.sum_add_distrib, Finset.sum_boole]
    have hDl : D l = 0 := by
      have hlt : ∑ i, l i < s := by
        rw [← hs]
        obtain ⟨i, hi⟩ : ∃ i, μ i ≠ 0 := by
          by_contra h
          push_neg at h
          exact hz (funext h)
        exact Finset.sum_lt_sum (fun i _ => Nat.sub_le _ _)
          ⟨i, Finset.mem_univ _, by simp only [hl]; omega⟩
      exact ihs _ hlt _ l rfl rfl
    have hsingle : ∑ J ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun J => J.card = J0.card),
        D (l + (fun i => if i ∈ J then 1 else 0)) = D (l + (fun i => if i ∈ J0 then 1 else 0)) := by
      refine Finset.sum_eq_single_of_mem J0 (by simp) ?_
      intro J hJ hne
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hJ
      set ν : Fin n → ℕ := l + (fun i => if i ∈ J then 1 else 0) with hν
      by_cases hνa : Antitone ν
      swap
      · exact hD ν hνa
      have hnsub : ¬ J ⊆ J0 := fun h => hne (Finset.eq_of_subset_of_card_le h (by omega))
      obtain ⟨i, hiJ, hiJ0⟩ := Finset.not_subset.mp hnsub
      have hμi : μ i = 0 := by simpa [hJ0] using hiJ0
      have hνi : 1 ≤ ν i := by simp [hν, hiJ]
      have hsub : insert i J0 ⊆ Finset.univ.filter (fun k => ν k ≠ 0) := by
        intro k hk
        rw [Finset.mem_insert] at hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rcases hk with rfl | hk
        · omega
        · have hk' : μ k ≠ 0 := by simpa [hJ0] using hk
          have hki : k ≤ i := by
            by_contra h
            push_neg at h
            have := hμ h.le
            omega
          have := hνa hki
          omega
      have hcard := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem hiJ0] at hcard
      have hcn : (Finset.univ.filter (fun k => ν k ≠ 0)).card ≤ n := by
        simpa using Finset.card_le_univ (Finset.univ.filter (fun k => ν k ≠ 0))
      refine ihk (n - (Finset.univ.filter (fun k => ν k ≠ 0)).card) ?_ ν ?_ rfl
      · omega
      · have h1 := hsum J
        have h2 := hsum J0
        rw [hlμ] at h2
        rw [hν, h1, hJ, ← h2, hs]
    have hrec := hr l hla J0.card hj
    rw [hsingle, hDl, mul_zero, hlμ] at hrec
    exact hrec
  intro μ
  exact main _ _ μ rfl rfl

theorem pieri_recursion_unique : ∀ (n : ℕ) (c : ℕ → ℂ) (V U : (Fin n → ℕ) → ℂ),
    (∀ l, ¬ Antitone l → V l = 0) → (∀ l, ¬ Antitone l → U l = 0) →
    (∀ l, Antitone l → ∀ j ≤ n, ∑ J ∈ (Finset.univ : Finset (Finset (Fin n))).filter
      (fun J => J.card = j), V (l + (fun i => if i ∈ J then 1 else 0)) = c j * V l) →
    (∀ l, Antitone l → ∀ j ≤ n, ∑ J ∈ (Finset.univ : Finset (Finset (Fin n))).filter
      (fun J => J.card = j), U (l + (fun i => if i ∈ J then 1 else 0)) = c j * U l) →
    V 0 = U 0 → V = U := by
  intro n c V U hV hU hrV hrU h0
  have h := pieri_recursion_zero n c (fun l => V l - U l)
    (fun l hl => by simp [hV l hl, hU l hl])
    (fun l hl j hj => by
      simp only [Finset.sum_sub_distrib, hrV l hl j hj, hrU l hl j hj, mul_sub])
    (by simp [h0])
  funext μ
  exact sub_eq_zero.mp (h μ)

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PieriRecursionUniqueStatement

section

@[expose] public section

open scoped Classical

theorem _root_.GlobalTheory.T.eq_of_pieri_recursion_of_eq_zero : ∀ (n : ℕ) (c : ℕ → ℂ) (V U : (Fin n → ℕ) → ℂ), (∀ l, ¬ Antitone l → V l = 0) → (∀ l, ¬ Antitone l → U l = 0) → (∀ l, Antitone l → ∀ j ≤ n, ∑ J ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun J => J.card = j), V (l + (fun i => if i ∈ J then 1 else 0)) = c j * V l) → (∀ l, Antitone l → ∀ j ≤ n, ∑ J ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun J => J.card = j), U (l + (fun i => if i ∈ J then 1 else 0)) = c j * U l) → V 0 = U 0 → V = U := by
  first | exact @GlobalTheory.pieri_recursion_unique | exact GlobalTheory.pieri_recursion_unique | (intros; apply GlobalTheory.pieri_recursion_unique <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShintaniFormula

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.UG GlobalTheory.PRep GlobalTheory.LFun
open scoped Classical

open GlobalTheory.JSW

theorem GlobalTheory.JSW.shintani_formula : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (ψ : AddChar (w.adicCompletion E) ℂ), (∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, ψ (x * y) = 1) ↔ x ∈ Ov E w) → ∀ (W : GL (Fin n) (w.adicCompletion E) → ℂ) (α : Fin n → ℂˣ), (∀ u ∈ GlobalTheory.SmGL.unipB (w.adicCompletion E) (Fin n), ∀ g, W (u * g) = ψ (GlobalTheory.Whittaker.superDiag u) * W g) → (∀ g, ∀ k ∈ KGL w (n := n), W (g * k) = W g) → (∀ ϖ, IsUnifV E w ϖ → ∀ j ≤ n, heckeVec (rightReg ℂ (GL (Fin n) (w.adicCompletion E)) ℂ) (KGL w (n := n)) (Tj ℂ n (Ov E w) ϖ j) W = satEig (qV E w) n (Finset.univ.val.map α) j • W) → ∀ (ϖ : (w.adicCompletion E)ˣ), IsUnifV E w (ϖ : w.adicCompletion E) → ∀ l : Fin n → ℕ, W (Units.map (Matrix.diagonalRingHom (Fin n) (w.adicCompletion E)).toMonoidHom (MulEquiv.piUnits.symm fun i => ϖ ^ l i)) = GlobalTheory.JSW.sphW (qV E w) (fun i => (α i : ℂ)) l * W 1 := by
  intro E _ _ w n ψ hψ W α hN hK hH ϖ hϖ l
  have hvan := GlobalTheory.T.whittaker_diagonal_eq_zero_of_not_antitone E w n ψ hψ W hN hK ϖ hϖ
  have hrec := GlobalTheory.T.sphericalWhittaker_torus_hecke_recursion E w n ψ hψ W α hN hK hH ϖ hϖ
  have hq : ((qV E w : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (GlobalTheory.LFun.qV_ne_zero w)
  have hes : ∀ j, MvPolynomial.eval₂ (Int.castRingHom ℂ) (fun i => (α i : ℂ)) (MvPolynomial.esymm (Fin n) ℤ j) =
      (Finset.univ.val.map fun i => (α i : ℂ)).esymm j := fun j => by
    rw [← MvPolynomial.aeval_esymm_eq_multiset_esymm (Fin n) ℤ]
    rfl
  let V : (Fin n → ℕ) → ℂ := fun m =>
    (qV E w : ℂ) ^ ((∑ k : Fin n, (((n : ℂ) - 1 - 2 * (k : ℕ)) * (((m) k : ℕ) : ℂ))) / 2) *
      W (Units.map (Matrix.diagonalRingHom (Fin n) (w.adicCompletion E)).toMonoidHom
        (MulEquiv.piUnits.symm fun i => ϖ ^ (m) i))
  let U : (Fin n → ℕ) → ℂ := fun m => if Antitone m then schurAt m (fun i => (α i : ℂ)) * W 1 else 0
  have hVU : V = U := by
    refine GlobalTheory.T.eq_of_pieri_recursion_of_eq_zero n (fun j => (Finset.univ.val.map fun i => (α i : ℂ)).esymm j) V U
      (fun m hm => by simp only [V, hvan m hm, mul_zero]) (fun m hm => by simp only [U, if_neg hm])
      (fun m hm j hj => hrec m hm j hj) (fun m hm j hj => ?_) ?_
    · have hp := congrArg (MvPolynomial.eval₂ (Int.castRingHom ℂ) (fun i => (α i : ℂ))) (GlobalTheory.T.esymm_mul_schurPolynomialJacobiTrudi n m hm j hj)
      rw [MvPolynomial.eval₂_mul, hes, MvPolynomial.eval₂_sum] at hp
      simp only [U, if_pos hm]
      rw [← Finset.sum_filter, Finset.filter_filter, ← Finset.sum_mul, ← mul_assoc]
      simp only [schurAt]
      rw [hp]
    · have h1 : (Units.map (Matrix.diagonalRingHom (Fin n) (w.adicCompletion E)).toMonoidHom
          (MulEquiv.piUnits.symm fun i => ϖ ^ (0 : Fin n → ℕ) i)) = 1 := by
        ext i j
        simp [Matrix.one_apply, Matrix.diagonal_apply]
      have h0 : (0 : Fin n → ℕ) = fun _ => 0 := rfl
      have ha0 : Antitone (0 : Fin n → ℕ) := antitone_const
      have hs : schurAt (0 : Fin n → ℕ) (fun i => (α i : ℂ)) = 1 := by
        rw [h0, schurAt, GlobalTheory.JSW.schur_zero, MvPolynomial.eval₂_one]
      have hU : U 0 = W 1 := by
        change (if Antitone (0 : Fin n → ℕ) then schurAt 0 (fun i => (α i : ℂ)) * W 1 else 0) = W 1
        rw [if_pos ha0, hs, one_mul]
      rw [hU]
      change _ * W _ = W 1
      rw [h1]
      simp
  have hl := congrFun hVU l
  simp only [V, U] at hl
  by_cases ha : Antitone l
  · rw [if_pos ha] at hl
    have hne : (qV E w : ℂ) ^ ((∑ k : Fin n, (((n : ℂ) - 1 - 2 * (k : ℕ)) * (((l) k : ℕ) : ℂ))) / 2) ≠ 0 := by
      rw [Complex.cpow_def_of_ne_zero hq]; exact Complex.exp_ne_zero _
    rw [sphW, if_pos ha, neg_div, Complex.cpow_neg, mul_assoc, ← hl, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  · rw [hvan l ha, GlobalTheory.JSW.sphW_of_not_antitone _ _ ha, zero_mul]
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShintaniFormulaStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.UG GlobalTheory.PRep GlobalTheory.LFun
open scoped Classical

theorem _root_.GlobalTheory.T.shintani_formula_alt : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (ψ : AddChar (w.adicCompletion E) ℂ), (∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, ψ (x * y) = 1) ↔ x ∈ Ov E w) → ∀ (W : GL (Fin n) (w.adicCompletion E) → ℂ) (α : Fin n → ℂˣ), (∀ u ∈ GlobalTheory.SmGL.unipB (w.adicCompletion E) (Fin n), ∀ g, W (u * g) = ψ (GlobalTheory.Whittaker.superDiag u) * W g) → (∀ g, ∀ k ∈ KGL w (n := n), W (g * k) = W g) → (∀ ϖ, IsUnifV E w ϖ → ∀ j ≤ n, heckeVec (rightReg ℂ (GL (Fin n) (w.adicCompletion E)) ℂ) (KGL w (n := n)) (Tj ℂ n (Ov E w) ϖ j) W = satEig (qV E w) n (Finset.univ.val.map α) j • W) → ∀ (ϖ : (w.adicCompletion E)ˣ), IsUnifV E w (ϖ : w.adicCompletion E) → ∀ l : Fin n → ℕ, W (Units.map (Matrix.diagonalRingHom (Fin n) (w.adicCompletion E)).toMonoidHom (MulEquiv.piUnits.symm fun i => ϖ ^ l i)) = GlobalTheory.JSW.sphW (qV E w) (fun i => (α i : ℂ)) l * W 1 := by
  first | exact @GlobalTheory.JSW.shintani_formula | exact GlobalTheory.JSW.shintani_formula | (intros; apply GlobalTheory.JSW.shintani_formula <;> assumption)
end
end
