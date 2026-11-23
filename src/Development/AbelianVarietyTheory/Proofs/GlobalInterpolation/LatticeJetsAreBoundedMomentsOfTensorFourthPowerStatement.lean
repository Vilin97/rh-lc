module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.IsSemiChar
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MahlerCoefficientNormLeOneIffJetsBoundedMeasureMStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MahlerJetCoefficientMulStatement
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Taylor
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MahlerJetCoefficientMulOfDisjointSupport

section

@[expose] public section

open GlobalTheory.MomN

namespace GlobalTheory

theorem mahler_mul_of_disjoint_support :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (ι' : Type) [Fintype ι'] [DecidableEq ι']
      (u : ι' → V) (F H : V → ℂ), ContDiff ℂ ⊤ F → ContDiff ℂ ⊤ H → ∀ (S T : Finset ι'), Disjoint S T →
      (∀ k : ι' → ℕ, (∃ p, p ∉ S ∧ k p ≠ 0) → GlobalTheory.MomN.mahler u F k = 0) →
      (∀ k : ι' → ℕ, (∃ p, p ∉ T ∧ k p ≠ 0) → GlobalTheory.MomN.mahler u H k = 0) →
      (∀ N : ι' → ℕ, (∃ p, p ∉ S ∪ T ∧ N p ≠ 0) → GlobalTheory.MomN.mahler u (fun z => F z * H z) N = 0) ∧
      (∀ N : ι' → ℕ, (∀ p, p ∉ S ∪ T → N p = 0) →
        GlobalTheory.MomN.mahler u (fun z => F z * H z) N =
          GlobalTheory.MomN.mahler u F (fun p => if p ∈ S then N p else 0) *
            GlobalTheory.MomN.mahler u H (fun p => if p ∈ T then N p else 0)) := by
  intro V _ _ ι' _ _ u F H hF hH S T hST hFS hHT
  constructor
  · intro N ⟨p, hp, hNp⟩
    rw [GlobalTheory.T.mahlerJetCoefficient_mul V ι' u F H hF hH N]
    apply Finset.sum_eq_zero
    intro k _
    have hpS : p ∉ S := fun h => hp (Finset.mem_union_left _ h)
    have hpT : p ∉ T := fun h => hp (Finset.mem_union_right _ h)
    by_cases hk : k p = 0
    · rw [hHT _ ⟨p, hpT, by simp [hk, hNp]⟩, mul_zero]
    · rw [hFS _ ⟨p, hpS, hk⟩, zero_mul]
  · intro N hN
    rw [GlobalTheory.T.mahlerJetCoefficient_mul V ι' u F H hF hH N]
    rw [Finset.sum_eq_single (fun p => if p ∈ S then N p else 0)]
    · have hfun : (fun i => N i - (fun p => if p ∈ S then N p else 0) i) =
          (fun p => if p ∈ T then N p else 0) := by
        funext p
        by_cases hS : p ∈ S
        · have hT : p ∉ T := Finset.disjoint_left.mp hST hS
          simp only [hS, hT, if_true, if_false, Nat.sub_self]
        · by_cases hT : p ∈ T
          · simp only [hS, hT, if_true, if_false, Nat.sub_zero]
          · have h0 : N p = 0 := hN p (by simp [hS, hT])
            simp only [hS, hT, if_false, h0, Nat.sub_zero]
      exact congrArg (fun g => GlobalTheory.MomN.mahler u F (fun p => if p ∈ S then N p else 0) *
        GlobalTheory.MomN.mahler u H g) hfun
    · intro k hk hne
      by_contra hprod
      have h1 : GlobalTheory.MomN.mahler u F k ≠ 0 := left_ne_zero_of_mul hprod
      have h2 : GlobalTheory.MomN.mahler u H (fun i => N i - k i) ≠ 0 := right_ne_zero_of_mul hprod
      apply hne
      funext p
      rw [Fintype.mem_piFinset] at hk
      have hkp : k p ≤ N p := Nat.lt_succ_iff.mp (Finset.mem_range.mp (hk p))
      by_cases hS : p ∈ S
      · have hT : p ∉ T := Finset.disjoint_left.mp hST hS
        have : N p - k p = 0 := by
          by_contra h
          exact h2 (hHT _ ⟨p, hT, h⟩)
        simp only [hS, if_true]
        omega
      · simp only [hS, if_false]
        by_contra h
        exact h1 (hFS _ ⟨p, hS, h⟩)
    · intro h
      exfalso
      apply h
      rw [Fintype.mem_piFinset]
      intro p
      rw [Finset.mem_range]
      split_ifs <;> omega

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MahlerJetCoefficientMulOfDisjointSupportStatement

section

@[expose] public section

open GlobalTheory.MomN

theorem _root_.GlobalTheory.T.mahlerJetCoefficient_mul_of_disjoint_support : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (ι' : Type) [Fintype ι'] [DecidableEq ι'] (u : ι' → V) (F H : V → ℂ), ContDiff ℂ ⊤ F → ContDiff ℂ ⊤ H → ∀ (S T : Finset ι'), Disjoint S T → (∀ k : ι' → ℕ, (∃ p, p ∉ S ∧ k p ≠ 0) → GlobalTheory.MomN.mahler u F k = 0) → (∀ k : ι' → ℕ, (∃ p, p ∉ T ∧ k p ≠ 0) → GlobalTheory.MomN.mahler u H k = 0) → (∀ N : ι' → ℕ, (∃ p, p ∉ S ∪ T ∧ N p ≠ 0) → GlobalTheory.MomN.mahler u (fun z => F z * H z) N = 0) ∧ (∀ N : ι' → ℕ, (∀ p, p ∉ S ∪ T → N p = 0) → GlobalTheory.MomN.mahler u (fun z => F z * H z) N = GlobalTheory.MomN.mahler u F (fun p => if p ∈ S then N p else 0) * GlobalTheory.MomN.mahler u H (fun p => if p ∈ T then N p else 0)) := by
  first | exact @GlobalTheory.mahler_mul_of_disjoint_support | exact GlobalTheory.mahler_mul_of_disjoint_support | (intros; apply GlobalTheory.mahler_mul_of_disjoint_support <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MahlerJetCoefficientOfFamilyZeroOffEmbedding

section

@[expose] public section

open GlobalTheory.MomN
open scoped ContDiff

noncomputable section

namespace GlobalTheory.MomEmbed

open MvPolynomial

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem monoJet_eq_listJet {κ : Type} [Fintype κ] (v : κ → V) (G : V → ℂ) (m : κ →₀ ℕ) :
    monoJet v G m = ReciprocityTheory.ChartRestriction.G.PullbackSections.lD G 0 (m.toMultiset.toList.map v) := by
  unfold monoJet
  rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.lD_eq G 0 _ (List.length_map _)]
  congr 1
  funext i
  simp [List.get_eq_getElem]

theorem monoJet_mapDomain {κ ι' : Type} [Fintype κ] [Fintype ι'] (e : κ ↪ ι') (w : κ → V) (u : ι' → V)
    (G : V → ℂ) (hG : ContDiff ℂ ⊤ G) (hw : ∀ i, u (e i) = w i) (m : κ →₀ ℕ) :
    monoJet u G (Finsupp.mapDomain e m) = monoJet w G m := by
  rw [monoJet_eq_listJet, monoJet_eq_listJet]
  apply ReciprocityTheory.ChartRestriction.G.PullbackSections.lD_perm (hG.contDiffAt)
  rw [← Multiset.coe_eq_coe, ← Multiset.map_coe, ← Multiset.map_coe, Multiset.coe_toList,
    Multiset.coe_toList, ← Finsupp.toMultiset_map m e, Multiset.map_map]
  congr 1
  funext i
  exact hw i

theorem mahler_embed : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (κ ι' : Type) [Fintype κ] [Fintype ι']
    (e : κ ↪ ι') (w : κ → V) (u : ι' → V) (G : V → ℂ), ContDiff ℂ ⊤ G → (∀ i, u (e i) = w i) →
    (∀ p, p ∉ Set.range e → u p = 0) →
    (∀ k : ι' → ℕ, (∃ p, p ∉ Set.range e ∧ k p ≠ 0) → GlobalTheory.MomN.mahler u G k = 0) ∧
    (∀ k : ι' → ℕ, (∀ p, p ∉ Set.range e → k p = 0) → GlobalTheory.MomN.mahler u G k = GlobalTheory.MomN.mahler w G (fun i => k (e i))) := by
  intro V _ _ κ ι' _ _ e w u G hG hw hu
  classical
  constructor
  · rintro k ⟨p, hp, hkp⟩
    simp only [GlobalTheory.MomN.mahler]
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hkp
    have hP : (∏ i, C (((k i).factorial : ℂ)⁻¹) * Polynomial.aeval (X i : MvPolynomial ι' ℂ) (descPochhammer ℂ (k i))) =
        X p * (C (((k p).factorial : ℂ)⁻¹) *
          Polynomial.aeval (X p : MvPolynomial ι' ℂ) ((descPochhammer ℂ n).comp (Polynomial.X - 1)) *
          ∏ i ∈ Finset.univ.erase p, C (((k i).factorial : ℂ)⁻¹) *
            Polynomial.aeval (X i : MvPolynomial ι' ℂ) (descPochhammer ℂ (k i))) := by
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ p)]
      simp only [hn, descPochhammer_succ_left, map_mul, Polynomial.aeval_X]
      ring
    rw [hP]
    apply Finset.sum_eq_zero
    intro m hm
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_X_mul'] at hm
    have hpm : p ∈ m.support := by
      by_contra h
      exact hm (if_neg h)
    have hmem : p ∈ m.toMultiset.toList := by
      rw [Multiset.mem_toList]
      simpa using hpm
    obtain ⟨idx, hidx⟩ := List.get_of_mem hmem
    have hz : monoJet u G m = 0 := by
      unfold monoJet
      exact ContinuousMultilinearMap.map_coord_zero _ idx (by
        show u ((Finsupp.toMultiset m).toList.get idx) = 0
        rw [hidx]
        exact hu p hp)
    rw [hz, mul_zero]
  · intro k hk
    simp only [GlobalTheory.MomN.mahler]
    have hprod : (∏ p : ι', C (((k p).factorial : ℂ)⁻¹) *
        Polynomial.aeval (X p : MvPolynomial ι' ℂ) (descPochhammer ℂ (k p))) =
        rename e (∏ i : κ, C (((k (e i)).factorial : ℂ)⁻¹) *
          Polynomial.aeval (X i : MvPolynomial κ ℂ) (descPochhammer ℂ (k (e i)))) := by
      rw [map_prod]
      symm
      apply Fintype.prod_of_injective e e.injective
      · intro b hb
        simp [hk b hb]
      · intro a
        simp [← Polynomial.aeval_algHom_apply, rename_X]
    rw [hprod, MvPolynomial.support_rename_of_injective e.injective,
      Finset.sum_image (fun a _ b _ h => Finsupp.mapDomain_injective e.injective h)]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [MvPolynomial.coeff_rename_mapDomain _ e.injective, monoJet_mapDomain e w u G hG hw]

end GlobalTheory.MomEmbed
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MahlerJetCoefficientOfFamilyZeroOffEmbeddingStatement

section

@[expose] public section

open GlobalTheory.MomN

theorem _root_.GlobalTheory.T.mahlerJetCoefficient_of_family_zero_off_embedding : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (κ ι' : Type) [Fintype κ] [Fintype ι'] (e : κ ↪ ι') (w : κ → V) (u : ι' → V) (G : V → ℂ), ContDiff ℂ ⊤ G → (∀ i, u (e i) = w i) → (∀ p, p ∉ Set.range e → u p = 0) → (∀ k : ι' → ℕ, (∃ p, p ∉ Set.range e ∧ k p ≠ 0) → GlobalTheory.MomN.mahler u G k = 0) ∧ (∀ k : ι' → ℕ, (∀ p, p ∉ Set.range e → k p = 0) → GlobalTheory.MomN.mahler u G k = GlobalTheory.MomN.mahler w G (fun i => k (e i))) := by
  first | exact @GlobalTheory.MomEmbed.mahler_embed | exact GlobalTheory.MomEmbed.mahler_embed | (intros; apply GlobalTheory.MomEmbed.mahler_embed <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LatticeJetsAreBoundedMomentsOfTensorFourthPower

section

@[expose] public section

open GlobalTheory.MomN Formalism.L2.Th1.H

noncomputable section

namespace GlobalTheory.MomRoot

theorem mahler_comp_clm (E V : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup V] [NormedSpace ℂ V]
    (κ : Type) [Fintype κ] (L : E →L[ℂ] V) (u : κ → E) (G : V → ℂ) (hG : ContDiff ℂ ⊤ G) (k : κ → ℕ) :
    mahler u (fun z => G (L z)) k = mahler (fun i => L (u i)) G k := by
  unfold GlobalTheory.MomN.mahler
  refine Finset.sum_congr rfl fun m _ => ?_
  congr 1
  unfold GlobalTheory.MomN.monoJet
  have h := L.iteratedFDeriv_comp_right hG (0 : E) (i := m.toMultiset.toList.length) le_top
  change iteratedFDeriv ℂ _ (G ∘ L) 0 _ = _
  rw [h, ContinuousMultilinearMap.compContinuousLinearMap_apply, map_zero]

theorem mahler_embed (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (κ ι' : Type) [Fintype κ] [Fintype ι']
    (e : κ ↪ ι') (w : κ → V) (u : ι' → V) (G : V → ℂ) (hG : ContDiff ℂ ⊤ G)
    (hu : ∀ i, u (e i) = w i) (hz : ∀ p, p ∉ Set.range e → u p = 0) :
    (∀ k : ι' → ℕ, (∃ p, p ∉ Set.range e ∧ k p ≠ 0) → mahler u G k = 0) ∧
    (∀ k : ι' → ℕ, (∀ p, p ∉ Set.range e → k p = 0) → mahler u G k = mahler w G (fun i => k (e i))) :=
  GlobalTheory.T.mahlerJetCoefficient_of_family_zero_off_embedding V κ ι' e w u G hG hu hz

theorem mahler_mul_disj (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (ι' : Type) [Fintype ι'] [DecidableEq ι']
    (u : ι' → V) (F H : V → ℂ) (hF : ContDiff ℂ ⊤ F) (hH : ContDiff ℂ ⊤ H) (S T : Finset ι') (hST : Disjoint S T)
    (hFS : ∀ k : ι' → ℕ, (∃ p, p ∉ S ∧ k p ≠ 0) → mahler u F k = 0)
    (hHT : ∀ k : ι' → ℕ, (∃ p, p ∉ T ∧ k p ≠ 0) → mahler u H k = 0) :
    (∀ N : ι' → ℕ, (∃ p, p ∉ S ∪ T ∧ N p ≠ 0) → mahler u (fun z => F z * H z) N = 0) ∧
    (∀ N : ι' → ℕ, (∀ p, p ∉ S ∪ T → N p = 0) → mahler u (fun z => F z * H z) N =
      mahler u F (fun p => if p ∈ S then N p else 0) * mahler u H (fun p => if p ∈ T then N p else 0)) :=
  GlobalTheory.T.mahlerJetCoefficient_mul_of_disjoint_support V ι' u F H hF hH S T hST hFS hHT

variable {n : Type} [Fintype n]

def sliceL (a : Fin 4) : (Fin 4 × n → ℂ) →L[ℂ] (n → ℂ) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (a, i)

theorem sliceL_apply (a : Fin 4) (z : Fin 4 × n → ℂ) : sliceL a z = slice a z := rfl

def fourBlockInclusionVector (b : Fin 4) (x : n → ℂ) : Fin 4 × n → ℂ := fun z => if z.1 = b then x z.2 else 0

theorem slice_fourBlockInclusionVector (a b : Fin 4) (x : n → ℂ) : slice a (fourBlockInclusionVector b x) = if a = b then x else 0 := by
  funext i; by_cases h : a = b <;> simp [slice, fourBlockInclusionVector, h]

end GlobalTheory.MomRoot

namespace GlobalTheory.MomRoot

theorem jets_root : ∀ (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (n : Type) [Fintype n] (ω : ℂ_[q]) (Λ : AddSubgroup (n → ℂ))
    (G : (n → ℂ) → ℂ), ContDiff ℂ ⊤ G → LatInt ι ω (pow4 Λ) (tens4 G) → LatInt ι ω Λ G := by
  intro q _ ι n _ ω Λ G hG hL κ _ v hv
  classical
  set c := ι.symm ω
  rw [GlobalTheory.T.mahlerCoefficient_norm_le_one_iff_jets_boundedMeasureMoments q ι (n → ℂ) κ _ G hG]
  intro m
  let U : Fin 4 × κ → (Fin 4 × n → ℂ) := fun p => c • fourBlockInclusionVector p.1 (v p.2)
  have hU : MomInt ι U (tens4 G) := hL (Fin 4 × κ) (fun p => fourBlockInclusionVector p.1 (v p.2)) (fun p a => by
    show slice a (fourBlockInclusionVector p.1 (v p.2)) ∈ Λ
    rw [slice_fourBlockInclusionVector]; split_ifs
    · exact hv _
    · exact Λ.zero_mem)
  have hGa : ∀ a, ContDiff ℂ ⊤ (fun z => G (slice a z)) := fun a => by
    have h : ContDiff ℂ ⊤ (sliceL (n := n) a) := ContinuousLinearMap.contDiff _
    exact hG.comp h
  have ht : tens4 G = fun z => G (slice 0 z) * G (slice 1 z) * G (slice 2 z) * G (slice 3 z) := by
    funext z; simp [tens4, Fin.prod_univ_four]
  have hcd : ContDiff ℂ ⊤ (tens4 G) := by
    rw [ht]; exact (((hGa 0).mul (hGa 1)).mul (hGa 2)).mul (hGa 3)
  have hb := ((GlobalTheory.T.mahlerCoefficient_norm_le_one_iff_jets_boundedMeasureMoments q ι _ _ U (tens4 G) hcd).1 hU) (fun p => m p.2)
  let S : Fin 4 → Finset (Fin 4 × κ) := fun a => Finset.univ.filter (fun p => p.1 = a)
  let e : Fin 4 → κ ↪ Fin 4 × κ := fun a => ⟨fun i => (a, i), fun i j h => (Prod.mk.inj h).2⟩
  have hposition : ∀ a, (∀ k : Fin 4 × κ → ℕ, (∃ p, p ∉ S a ∧ k p ≠ 0) → mahler U (fun z => G (slice a z)) k = 0) ∧
      (∀ k : Fin 4 × κ → ℕ, (∀ p, p ∉ S a → k p = 0) →
        mahler U (fun z => G (slice a z)) k = mahler (fun i => c • v i) G (fun i => k (a, i))) := by
    intro a
    have he : ∀ i, e a i = (a, i) := fun _ => rfl
    have hcomp : ∀ k, mahler U (fun z => G (slice a z)) k = mahler (fun p => sliceL a (U p)) G k :=
      fun k => by
        have h := mahler_comp_clm _ _ _ (sliceL a) U G hG k
        simp only [sliceL_apply] at h
        exact h
    have hrange : ∀ p : Fin 4 × κ, p ∈ Set.range (e a) ↔ p ∈ S a := by
      rintro ⟨b, i⟩; simp [Set.mem_range, he, S, eq_comm]
    obtain ⟨h1, h2⟩ := mahler_embed (n → ℂ) κ (Fin 4 × κ) (e a) (fun i => c • v i) (fun p => sliceL a (U p)) G hG
      (fun i => by simp [U, he, sliceL_apply, slice_fourBlockInclusionVector])
      (fun p hp => by
        have : p.1 ≠ a := fun h => hp ((hrange p).2 (by simp [S, h]))
        simp [U, sliceL_apply, slice_fourBlockInclusionVector, Ne.symm this])
    refine ⟨fun k hk => ?_, fun k hk => ?_⟩
    · rw [hcomp]; obtain ⟨p, hp, hk⟩ := hk; exact h1 k ⟨p, by rwa [hrange], hk⟩
    · rw [hcomp]; exact h2 k (fun p hp => hk p (by rwa [← hrange]))
  have dj : ∀ (A : Finset (Fin 4)) (b : Fin 4), b ∉ A → Disjoint (A.biUnion S) (S b) := by
    intro A b hb
    rw [Finset.disjoint_left]; intro p hp hq
    simp only [Finset.mem_biUnion, S, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
    obtain ⟨a, ha, rfl⟩ := hp; exact hb (hq ▸ ha)
  have u1 : ({0} : Finset (Fin 4)).biUnion S = S 0 := by simp
  have u2 : ({0, 1} : Finset (Fin 4)).biUnion S = S 0 ∪ S 1 := by simp [Finset.biUnion_insert]
  have u3 : ({0, 1, 2} : Finset (Fin 4)).biUnion S = S 0 ∪ S 1 ∪ S 2 := by
    simp [Finset.biUnion_insert, Finset.union_assoc]
  have d1 := dj {0} 1 (by decide)
  have d2 := dj {0, 1} 2 (by decide)
  have d3 := dj {0, 1, 2} 3 (by decide)
  rw [u1] at d1; rw [u2] at d2; rw [u3] at d3
  obtain ⟨A1v, A1⟩ := mahler_mul_disj _ _ U _ _ (hGa 0) (hGa 1) (S 0) (S 1) d1 (hposition 0).1 (hposition 1).1
  obtain ⟨A2v, A2⟩ := mahler_mul_disj _ _ U _ _ ((hGa 0).mul (hGa 1)) (hGa 2) (S 0 ∪ S 1) (S 2) d2 A1v (hposition 2).1
  obtain ⟨-, A3⟩ := mahler_mul_disj _ _ U _ _ (((hGa 0).mul (hGa 1)).mul (hGa 2)) (hGa 3)
    (S 0 ∪ S 1 ∪ S 2) (S 3) d3 A2v (hposition 3).1
  have key : mahler U (tens4 G) (fun p => m p.2) = (mahler (fun i => c • v i) G m) ^ 4 := by
    rw [ht, A3 _ ?_, A2 _ ?_, A1 _ ?_, (hposition 0).2 _ ?_, (hposition 1).2 _ ?_, (hposition 2).2 _ ?_, (hposition 3).2 _ ?_]
    · simp only [S, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      norm_num
      ring
    all_goals
      intro p hp
      rcases p with ⟨b, i⟩
      simp only [S, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      fin_cases b <;> simp at hp ⊢
  rw [key, map_pow, norm_pow] at hb
  exact (pow_le_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 hb
end GlobalTheory.MomRoot
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LatticeJetsAreBoundedMomentsOfTensorFourthPowerStatement

section

@[expose] public section

open GlobalTheory.MomN Formalism.L2.Th1.H

theorem _root_.GlobalTheory.T.latticeJetsAreBoundedMoments_of_tensorFourthPower : ∀ (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (n : Type) [Fintype n] (ω : ℂ_[q]) (Λ : AddSubgroup (n → ℂ)) (G : (n → ℂ) → ℂ), ContDiff ℂ ⊤ G → LatInt ι ω (pow4 Λ) (tens4 G) → LatInt ι ω Λ G := by
  first | exact @GlobalTheory.MomRoot.jets_root | exact GlobalTheory.MomRoot.jets_root | (intros; apply GlobalTheory.MomRoot.jets_root <;> assumption)
end
end
