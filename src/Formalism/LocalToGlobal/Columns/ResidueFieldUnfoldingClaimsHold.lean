module

public import Formalism.LocalToGlobal.Columns.ChainOneB
public import Formalism.PeriodIntegrals.OneCosetSharp
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.projection2.AllowColLt
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.projection2.KappaZero
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.projection2.MemFlagUnipotent
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Matrix.Block
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.projection2.EntryEmbedMatrix
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.projection2.GaStep
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.projection2.KappaZeroAlt
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.Tactic.Polynomial.Basic
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.projection2.EmbedMatrixBasisVecApplyOfNotFree

section

@[expose] public section

noncomputable section

namespace PI.OneCosetSharp.W

open Loc LocE

variable {k : Type} [Field k] {n' c n : ℕ}

theorem embedMatrix_basisVec_apply_of_not_free (xj : (Fin n' → k) →ₗ[k] (Fin n → k)) (tt : FC n' (c + 1) n c → k) (i : ℕ) (hi : i < c)
    (l : Fin (n + c)) (hf : ¬ IsFree n' n c l.1 (n' + i)) :
    xx1 xj tt (eN k (n' + (c + 1)) (n' + i)) l = if l.1 = n + i then 1 else 0 := by
  have hs : n' + i < n' + (c + 1) := by omega
  have he : eN k (n' + (c + 1)) (n' + i) = Pi.single (⟨n' + i, hs⟩ : Fin (n' + (c + 1))) 1 := by
    funext s
    unfold eN
    by_cases h : (s : ℕ) = n' + i
    · have : s = ⟨n' + i, hs⟩ := Fin.ext h
      subst this
      simp
    · have : s ≠ ⟨n' + i, hs⟩ := fun e => h (by rw [e])
      simp [h, this]
  have key : ∀ (A : Matrix (Fin (n + c)) (Fin (n' + (c + 1))) k) (j : Fin (n' + (c + 1))),
      Matrix.toLin' A (Pi.single j 1) l = A l j := by
    intro A j
    rw [Matrix.toLin'_apply, Matrix.mulVec_single_one]
    rfl
  rw [he]
  unfold xx1
  rw [key, Matrix.of_apply,
    dite_eq_right (show ¬ IsFree n' n c l.1 (⟨n' + i, hs⟩ : Fin (n' + (c + 1))).1 from hf),
    dite_eq_right (show ¬ ((⟨n' + i, hs⟩ : Fin (n' + (c + 1))).1 < n') by show ¬ (n' + i < n'); omega)]
  show (if l.1 = n + (n' + i - n') then (1 : k) else 0) = _
  rw [Nat.add_sub_cancel_left]

theorem nElem : NElem := by
  intro k _ n' c n xj tt
  classical

  have heN : ∀ (N j : ℕ) (hj : j < N), eN k N j = Pi.single (⟨j, hj⟩ : Fin N) 1 := by
    intro N j hj
    funext s
    unfold eN
    by_cases h : (s : ℕ) = j
    · have : s = ⟨j, hj⟩ := Fin.ext h
      subst this
      simp
    · have : s ≠ ⟨j, hj⟩ := fun e => h (by rw [e])
      simp [h, this]
  have hnf : ∀ (l : Fin (n + c)) (i : ℕ), i < c → (i = 0 ∨ n + i ≤ l.1) →
      ¬ IsFree n' n c l.1 (n' + i) := by
    intro l i hi h
    unfold IsFree
    omega

  let M : Matrix (Fin (n + c)) (Fin (n + c)) k := Matrix.of fun l s =>
    if s.1 < n then (if l = s then 1 else 0)
    else xx1 xj tt (eN k (n' + (c + 1)) (n' + (s.1 - n))) l
  have hM_lt : ∀ l s : Fin (n + c), s.1 < n → M l s = if l = s then 1 else 0 := by
    intro l s hs
    simp [M, hs]
  have hM_ge : ∀ (l : Fin (n + c)) (j : ℕ) (hj : j < n + c), ¬ j < n →
      M l ⟨j, hj⟩ = xx1 xj tt (eN k (n' + (c + 1)) (n' + (j - n))) l := by
    intro l j hj hn
    simp [M, hn]
  have hT : ∀ l s : Fin (n + c), s < l → M l s = 0 := by
    intro l s hsl
    have hsl' : s.1 < l.1 := hsl
    by_cases hs : s.1 < n
    · rw [hM_lt l s hs, if_neg (fun h => by rw [h] at hsl'; exact lt_irrefl _ hsl')]
    · have hsc := s.2
      rw [show s = ⟨s.1, s.2⟩ from rfl, hM_ge l s.1 s.2 hs,
        embedMatrix_basisVec_apply_of_not_free xj tt (s.1 - n) (by omega) l (hnf l (s.1 - n) (by omega) (Or.inr (by omega))),
        if_neg (by omega)]
  have hD : ∀ s : Fin (n + c), M s s = 1 := by
    intro s
    by_cases hs : s.1 < n
    · rw [hM_lt s s hs, if_pos rfl]
    · have hsc := s.2
      rw [show s = ⟨s.1, s.2⟩ from rfl, hM_ge _ s.1 s.2 hs,
        embedMatrix_basisVec_apply_of_not_free xj tt (s.1 - n) (by omega) _ (hnf _ (s.1 - n) (by omega) (Or.inr (by simp; omega))),
        if_pos (by simp; omega)]
  have hUT : M.BlockTriangular id := fun i j hij => hT i j hij
  have hdet : IsUnit M.det := by
    rw [Matrix.det_of_upperTriangular hUT]
    simp [hD]
  let hinv : Invertible M := Matrix.invertibleOfIsUnitDet M hdet
  let ν := M.toLinearEquiv' hinv
  have hν : ∀ x, ν x = M.mulVec x := by
    intro x
    show (↑(M.toLinearEquiv' hinv) : (Fin (n + c) → k) →ₗ[k] (Fin (n + c) → k)) x = _
    rw [Matrix.toLinearEquiv'_apply, Matrix.toLin'_apply]
  have hcol : ∀ (j : ℕ) (hj : j < n + c), M.mulVec (eN k (n + c) j) = fun l => M l ⟨j, hj⟩ := by
    intro j hj
    rw [heN _ j hj, Matrix.mulVec_single_one]
    rfl
  have hνcol : ∀ i, i < c → ν (eN k (n + c) (n + i)) = xx1 xj tt (eN k (n' + (c + 1)) (n' + i)) := by
    intro i hi
    rw [hν, hcol (n + i) (by omega)]
    funext l
    rw [hM_ge l (n + i) (by omega) (by omega), Nat.add_sub_cancel_left]
  have hinX : ∀ (v : Fin n → k) (s : Fin (n + c)), ¬ s.1 < n → inX k n c v s = 0 := by
    intro v s hs
    simp [inX, hs]
  have hzero : ∀ i, ¬ i < c → eN k (n + c) (n + i) = 0 := by
    intro i hi
    funext l
    unfold eN
    split_ifs with h
    · have := l.2
      omega
    · rfl
  refine ⟨ν, mem_flagUnipotent ⟨?_, ?_, ?_⟩, ?_, hνcol⟩
  · intro i v hv
    have hv' : ∀ l : Fin (n + c), l.1 ∉ ({x : ℕ | x < n + i} : Set ℕ) → v l = 0 := hv
    show ∀ l : Fin (n + c), l.1 ∉ ({x : ℕ | x < n + i} : Set ℕ) → (ν v) l = 0
    intro l hl
    have hl' : n + i ≤ l.1 := by simpa using hl
    rw [hν]
    simp only [Matrix.mulVec, dotProduct]
    apply Finset.sum_eq_zero
    intro s _
    by_cases hs : s.1 < n + i
    · rw [hT l s (show s.1 < l.1 by omega), zero_mul]
    · rw [hv' s (by simpa using hs), mul_zero]
  · rcases Nat.eq_zero_or_pos c with hc | hc
    · rw [show eN k (n + c) n = 0 from by simpa using hzero 0 (by omega), map_zero]
    · have h0 := hνcol 0 hc
      have e1 : xx1 xj tt (eN k (n' + (c + 1)) (n' + 0)) = eN k (n + c) (n + 0) := by
        funext l
        rw [embedMatrix_basisVec_apply_of_not_free xj tt 0 hc l (hnf l 0 hc (Or.inl rfl))]
        rfl
      exact h0.trans e1
  · intro i
    show ∀ l : Fin (n + c), l.1 ∉ ({x : ℕ | x < n + i} : Set ℕ) →
      (ν (eN k (n + c) (n + i)) - eN k (n + c) (n + i)) l = 0
    intro l hl
    have hl' : n + i ≤ l.1 := by simpa using hl
    by_cases hi : i < c
    · rw [hνcol i hi, Pi.sub_apply, embedMatrix_basisVec_apply_of_not_free xj tt i hi l (hnf l i hi (Or.inr hl'))]
      show (if l.1 = n + i then (1 : k) else 0) - (if l.1 = n + i then 1 else 0) = 0
      exact sub_self _
    · rw [hzero i hi, map_zero, sub_zero]
      rfl
  · intro v
    rw [hν]
    funext l
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single l]
    · rw [hD l, one_mul]
    · intro s _ hsl
      by_cases hs : s.1 < n
      · rw [hM_lt l s hs, if_neg (fun h => hsl h.symm), zero_mul]
      · rw [hinX v s hs, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ l) h

end PI.OneCosetSharp.W
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.projection2.Assemble

section

@[expose] public section

noncomputable section

namespace PI.OneCosetSharp.W

open Loc LocE

theorem eN_eq_single {k : Type} [Field k] {N : ℕ} (i : ℕ) (hi : i < N) :
    eN k N i = Pi.single (⟨i, hi⟩ : Fin N) 1 := by
  ext l
  simp only [eN, Pi.single_apply, Fin.ext_iff]

theorem inX_apply {k : Type} [Field k] {n c : ℕ} (v : Fin n → k) (l : Fin (n + c)) :
    inX k n c v l = if h : l.1 < n then v ⟨l.1, h⟩ else 0 := by
  simp only [inX, LinearMap.pi_apply]
  split_ifs <;> rfl

theorem inX_of_zero {k : Type} [Field k] {n c : ℕ} (w : Fin (n + c) → k) (hw : ∀ l : Fin (n + c), n ≤ l.1 → w l = 0) :
    ∃ v, inX k n c v = w := by
  refine ⟨fun i => w ⟨i.1, by omega⟩, ?_⟩
  ext l
  rw [inX_apply]
  split_ifs with h
  · rfl
  · exact (hw l (not_lt.mp h)).symm

theorem embedMatrix_basisVec_apply_of_le {k : Type} [Field k] {n' c n : ℕ} (xj : (Fin n' → k) →ₗ[k] (Fin n → k))
    (tt : FC n' (c + 1) n c → k) (s : ℕ) (hs : s < n') (l : Fin (n + c)) (hl : n ≤ l.1) :
    xx1 xj tt (eN k (n' + (c + 1)) s) l = 0 := by
  have hl' : ¬ l.1 < n := not_lt.mpr hl
  rw [eN_eq_single s (by omega)]
  simp [xx1, Matrix.mulVec_single, IsFree, hs, hl', not_le.mpr hs]

theorem sum_step {k : Type} [Field k] [Fintype k] (ψ₀ : AddChar k ℂ) (χ : ℕ → kˣ →* ℂˣ) (k₀ m t j n' c n : ℕ)
    (h : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) (xj : (Fin n' → k) →ₗ[k] (Fin n → k))
    (hE : E1 (n' := n') (c' := c + 1) (n := n) (c := c) (fun u => ψ₀ u) Finset.univ 1
            (om (fun _ => 1) (fun _ => 0) 1 (LinearEquiv.refl k _) h (PhiS ψ₀ χ k₀ m t j n' c n)) xj ≠ 0) :
    ∃ tt, PhiS ψ₀ χ k₀ m t j n' c n (h.symm.toLinearMap ∘ₗ xx1 xj tt) ≠ 0 := by
  by_contra H
  simp only [not_exists, not_not] at H
  apply hE
  simp [E1, om, H]

theorem fIdx_add_of_lt (k₀ c n i : ℕ) (hi : i < c) : fIdx k₀ c n (k₀ + i) = n + i := by
  unfold fIdx
  rw [if_neg (by omega), if_pos (by omega)]
  omega

theorem Nums.n'_ge {k₀ m t j n' c n : ℕ} (hn : Nums k₀ m t j n' c n) : k₀ ≤ n' := by
  obtain ⟨-, -, h4, hj1, hj2, hc, h7, -⟩ := hn
  generalize (j - 1) * t = X at h7
  omega

theorem claim1_of (hP : PatClosed) (hK : KappaZero) (hN : NElem) (hG : GaStep) : Claim1 := by
  intro k _ _ ψ₀ χ k₀ m t j n' c n hnum h ⟨xj, hE⟩
  obtain ⟨tt, htt⟩ := sum_step ψ₀ χ k₀ m t j n' c n h xj hE
  obtain ⟨κ, hκ, hκe⟩ := hK k ψ₀ χ k₀ m t j n' c n hnum _ htt
  obtain ⟨ν, hνR, hνX, hνe⟩ := hN k n' c n xj tt
  have hk₀ := Nums.n'_ge hnum
  have hνinv : ∀ y z, ν z = y → ν⁻¹ y = z := by
    intro y z hz
    rw [← hz]
    show (ν⁻¹ * ν) z = z
    rw [inv_mul_cancel]
    rfl
  have g1 : ∀ i < c, (ν⁻¹ * h * κ) (eN k (n + c) (n + i)) = eN k (n + c) (n + i) := by
    intro i hi
    have e1 := hκe (k₀ + i) (by omega)
    rw [fIdx_add_of_lt k₀ c n i hi, fIdx_add_of_lt k₀ (c + 1) n' i (by omega)] at e1
    show ν⁻¹ (h (κ (eN k (n + c) (n + i)))) = eN k (n + c) (n + i)
    rw [e1]
    apply hνinv
    rw [hνe i hi]
    simp
  have g2 : ∀ p < n' + (c + 1), (p < k₀ ∨ k₀ + c < p) →
      ∃ v, (ν⁻¹ * h * κ) (eN k (n + c) (fIdx k₀ c n p)) = inX k n c v := by
    intro p hp hcase
    have hs : fIdx k₀ (c + 1) n' p < n' := by
      unfold fIdx
      split_ifs <;> omega
    obtain ⟨v, hv⟩ := inX_of_zero (xx1 xj tt (eN k (n' + (c + 1)) (fIdx k₀ (c + 1) n' p)))
      (fun l hl => embedMatrix_basisVec_apply_of_le xj tt _ hs l hl)
    refine ⟨v, ?_⟩
    show ν⁻¹ (h (κ (eN k (n + c) (fIdx k₀ c n p)))) = inX k n c v
    rw [hκe p hp]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    rw [← hv]
    exact hνinv _ _ (hνX v)
  obtain ⟨γ, hγ, κ', hκ', hg⟩ := hG k k₀ m t j n' c n hnum (ν⁻¹ * h * κ) g1 g2
  have hκinv := (hP k k₀ m t j n' c n hnum κ κ hκ hκ).2
  refine ⟨ν * γ, mul_mem hνR hγ, κ' * κ⁻¹,
    (hP k k₀ m t j n' c n hnum κ' κ⁻¹ hκ' hκinv).1, ?_⟩
  calc h = ν * (ν⁻¹ * h * κ) * κ⁻¹ := by group
    _ = ν * γ * (κ' * κ⁻¹) := by rw [hg]; group

end PI.OneCosetSharp.W
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.projection2.OneCosetSharpOfPatClosed

section

@[expose] public section

namespace PI.OneCosetSharp.W

theorem oneCosetSharp_of (h1 : Claim1) (h2 : Claim2) : OneCosetSharp := by
  intro k _ _ ψ₀ χ k₀ m t j n' c n hk hm hm4 hj1 hj2 hc ha hb
  exact ⟨h1 k ψ₀ χ k₀ m t j n' c n ⟨hk, hm, hm4, hj1, hj2, hc, ha, hb⟩ ,
    h2 k ψ₀ χ k₀ m t j n' c n ⟨hk, hm, hm4, hj1, hj2, hc, ha, hb⟩⟩

theorem oneCosetSharp_of_patClosed (hP : PatClosed) (hK : KappaZero) (hN : NElem) (hG : GaStep) (h2 : Claim2) :
    OneCosetSharp :=
  oneCosetSharp_of (claim1_of hP hK hN hG) h2

end PI.OneCosetSharp.W
end
end

-- Source module: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.OneCosetSharp

section

@[expose] public section

theorem support_oneCoset : PI.OneCosetSharp.OneCosetSharp :=
  PI.OneCosetSharp.W.oneCosetSharp_of_patClosed PI.OneCosetSharp.W.patClosed PI.OneCosetSharp.W.kappaZero
    PI.OneCosetSharp.W.nElem PI.OneCosetSharp.W.gaStep PI.OneCosetSharp.W.C2.claim2
end
end

-- Source module: Formalism.LocalToGlobal.Columns.ResidueFieldUnfoldingClaimsHold

section

@[expose] public section

namespace Formalism.L2.Col

theorem residueFieldUnfolding_claims_hold : ResidueFieldUnfoldingSupport ∧ ResidueFieldUnfoldingNonzero := by
  refine ⟨?_, ?_⟩
  · intro k _ _ ψ₀ χ k₀ m t j n' c n _ hr h hne
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hr
    exact (support_oneCoset k ψ₀ χ k₀ m t j n' c n h1 h2 h3 h4 h5 h6 h7 h8).1 h hne
  · intro k _ _ ψ₀ χ k₀ m t j n' c n _ hr
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hr
    exact (support_oneCoset k ψ₀ χ k₀ m t j n' c n h1 h2 h3 h4 h5 h6 h7 h8).2

end Formalism.L2.Col
end
end
