module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DiagHermitianTrivialOfSumFourSquares
public import Development.AbelianVarietyTheory.Definitions.Divisors.MarkedSumIrr
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
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MarkWeightedFixedPointEqDefinitePairOdd
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.FinitelyManyMarkedClassesTermDegreeOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFormNegOnOrthogonalOfPositiveIndexOne
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.TwOrbMEqTwOrbUOfNormal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudePairHermitianFormInvertibleSimilitudeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudePairGramInvCongruentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudePairHermitianFormInvertibleSimilitudeStatement
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MarkedFieldPairsEquivDefiniteFieldPairsOdd
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.TotallySplit

-- Source module: Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DPairOneIrr

section

@[expose] public section

noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid
open scoped TensorProduct Classical

namespace GlobalTheory.LKDef

def MoveDefInv : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → Odd G.n → ∀ (wt sel : Polynomial G.F → ℂ), IsSel G sel →
    ∀ (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (r : ℕ) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ),
      0 < r → (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → (∀ k ∈ K, ∀ g, φ (k⁻¹ * g * sigG G r k) = φ g) →
      markedSumIrr G wt sel Kf f r K φ = dSumIrr G wt Kf f r K φ

namespace MoveEx

open GlobalTheory.LKTrip.Example GlobalTheory.LKMid.Example

end MoveEx

end GlobalTheory.LKDef
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFormNegOnOrthogonalOfPositiveIndexOneStatement

section

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.hermitianForm_neg_on_orthogonal_of_positiveIndex_one : ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian), A.det ≠ 0 → sigPosH hA = 1 → ∀ x y : Fin n → ℂ, 0 < (star x ⬝ᵥ A *ᵥ x).re → star x ⬝ᵥ A *ᵥ y = 0 → y ≠ 0 → (star y ⬝ᵥ A *ᵥ y).re < 0 := by
  first | exact @GlobalTheory.re_form_neg_of_orth_of_sigPosH_eq_one | exact GlobalTheory.re_form_neg_of_orth_of_sigPosH_eq_one | (intros; apply GlobalTheory.re_form_neg_of_orth_of_sigPosH_eq_one <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MarkNormSqEqSimilitudeFactor

section

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid

theorem Pair.mark_norm_sq : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (μ : ℂ), P.Mark μ →
    ‖μ‖ ^ 2 = ((P.c : ℚ) : ℝ) := by
  intro p _ G P μ hμ
  obtain ⟨v, _, x, hx, hpos⟩ := hμ
  obtain ⟨_, _, hlaw⟩ := GlobalTheory.T.similitudePair_hermitianForm_invertible_similitude p G P v
  set H := G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C) with hH
  set A := G.psi v (P.γ : G.C) with hA
  set q : ℂ := star x ⬝ᵥ (H *ᵥ x) with hq
  have hq0 : q ≠ 0 := by
    intro h0; rw [h0] at hpos; simp at hpos
  have key : star x ⬝ᵥ ((Aᴴ * H * A) *ᵥ x) = (star μ * μ) * q := by
    rw [← mulVec_mulVec, ← mulVec_mulVec, hx, dotProduct_mulVec, ← star_mulVec, hx, mulVec_smul, star_smul,
      smul_dotProduct, dotProduct_smul, hq]
    simp only [smul_eq_mul]; ring
  rw [hlaw, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] at key
  have hc : star μ * μ = ((P.c : ℚ) : ℂ) := by
    have := mul_right_cancel₀ hq0 key.symm
    exact this
  have h2 : ((‖μ‖ ^ 2 : ℝ) : ℂ) = ((((P.c : ℚ) : ℝ)) : ℂ) := by
    rw [Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
    push_cast
    exact hc
  exact_mod_cast h2

end GlobalTheory.LKMid
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MarkNormSqEqSimilitudeFactorStatement

section

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.mark_norm_sq_eq_similitudeFactor : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (μ : ℂ), P.Mark μ → ‖μ‖ ^ 2 = ((P.c : ℚ) : ℝ) := by
  first | (exact @GlobalTheory.LKMid.Pair.mark_norm_sq) | (exact GlobalTheory.LKMid.Pair.mark_norm_sq) | (intros; apply GlobalTheory.LKMid.Pair.mark_norm_sq  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DotConjTransposeMulMul

section

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid.Pair

theorem dot_conjTranspose_mul_mul {n : ℕ} (M N : Matrix (Fin n) (Fin n) ℂ) (y z : Fin n → ℂ) :
    star y ⬝ᵥ (Mᴴ * N * M) *ᵥ z = star (M *ᵥ y) ⬝ᵥ N *ᵥ (M *ᵥ z) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.star_mulVec]

theorem mark_unique : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (μ μ' : ℂ), G.a = 1 →
    P.Mark μ → P.Mark μ' → μ = μ' := by
  intro p _ G P μ μ' ha hm hm'
  obtain ⟨v, hv, x, hx, hxp⟩ := hm
  obtain ⟨v', hv', x', hx', hxp'⟩ := hm'
  have hvv : v = v' := by
    have hc : Fintype.card {w : InfinitePlace G.F // sigPosH (G.gram_herm w) = 1} = 1 := ha
    rw [Fintype.card_eq_one_iff] at hc
    obtain ⟨w, hw⟩ := hc
    exact congrArg Subtype.val ((hw ⟨v, hv⟩).trans (hw ⟨v', hv'⟩).symm)
  subst hvv
  by_contra hne
  have hn := GlobalTheory.T.mark_norm_sq_eq_similitudeFactor p G P μ ⟨v, hv, x, hx, hxp⟩
  obtain ⟨-, -, hlaw⟩ := GlobalTheory.T.similitudePair_hermitianForm_invertible_similitude p G P v

  have e := dot_conjTranspose_mul_mul (G.psi v P.γ) (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) x x'
  rw [hlaw, hx, hx', Matrix.mulVec_smul, Matrix.smul_mulVec, star_smul, smul_dotProduct,
    dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul] at e
  have hc0 : ((P.c : ℚ) : ℝ) ≠ 0 := by exact_mod_cast P.c.ne_zero
  have hμ : star μ * μ = (((P.c : ℚ) : ℂ)) := by
    rw [show star μ = (starRingEnd ℂ) μ from rfl, Complex.conj_mul', ← Complex.ofReal_pow, hn, Complex.ofReal_ratCast]
  have hμ0 : star μ ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hμ
    exact hc0 (by exact_mod_cast hμ.symm)
  have horth : star x ⬝ᵥ (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) *ᵥ x' = 0 := by
    by_contra hne0
    have h1 : (((P.c : ℚ) : ℂ)) = star μ * μ' := by
      rw [← mul_assoc] at e; exact mul_right_cancel₀ hne0 e
    exact hne (mul_left_cancel₀ hμ0 (hμ.trans h1))

  obtain ⟨Z, hZ⟩ := GlobalTheory.T.similitudePair_gram_inv_congruent p G P v
  rw [hZ, dot_conjTranspose_mul_mul] at horth hxp hxp'
  have hx'0 : x' ≠ 0 := by
    rintro rfl; simp at hxp'
  have hY : (Z : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ x' ≠ 0 := by
    intro h0
    apply hx'0
    have := congrArg (fun w => ((Z⁻¹ : GL (Fin G.n) ℂ) : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ w) h0
    simpa [Matrix.mulVec_mulVec] using this
  have hneg := GlobalTheory.T.hermitianForm_neg_on_orthogonal_of_positiveIndex_one (G.gram v) (G.gram_herm v) (G.gram_det v) hv _ _ hxp horth hY
  exact absurd hxp' (not_lt.mpr hneg.le)

end GlobalTheory.LKMid.Pair
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MarkedRootRealSignatureOne

section

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid

theorem eval_eq_zero_of_eigenvector {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) (μ : ℂ) (hx : x ≠ 0)
    (hM : M *ᵥ x = μ • x) (q : Polynomial ℂ) (hq : Polynomial.aeval M q = 0) : q.eval μ = 0 := by
  have hv : Module.End.HasEigenvector (Matrix.toLin' M) μ x :=
    ⟨Module.End.mem_eigenspace_iff.2 (by rw [Matrix.toLin'_apply]; exact hM), hx⟩
  have h1 := Module.End.aeval_apply_of_hasEigenvector hv (p := q)
  have h2 : Polynomial.aeval (Matrix.toLin' M) q = Matrix.toLin' (Polynomial.aeval M q) := by
    exact Polynomial.aeval_algHom_apply (Matrix.toLinAlgEquiv' (R := ℂ) (n := Fin n)).toAlgHom M q
  rw [h2, hq, map_zero, LinearMap.zero_apply] at h1
  exact (smul_eq_zero.1 h1.symm).resolve_right hx

theorem mark_isRoot_pol : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (μ : ℂ), G.a = 1 → P.Mark μ →
    ∀ v : InfinitePlace G.F, sigPosH (G.gram_herm v) = 1 → P.pol.eval₂ v.embedding μ = 0 := by
  intro p _ G P μ ha hm v hv
  obtain ⟨v₀, hv₀, x, hx, hpos⟩ := hm
  have hvv : v = v₀ := by
    unfold HTGroup.a at ha
    obtain ⟨w, hw⟩ := Fintype.card_eq_one_iff.1 ha
    have e1 := hw ⟨v, hv⟩
    have e2 := hw ⟨v₀, hv₀⟩
    exact congrArg Subtype.val (e1.trans e2.symm)
  subst hvv
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hpos
  have hq : Polynomial.aeval (G.psi v (P.γ : G.C)) (P.pol.map v.embedding) = 0 := by
    have h0 : G.psi v (Polynomial.aeval (P.γ : G.C) P.pol) = 0 := by
      rw [Pair.pol, minpoly.aeval, map_zero]
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    rw [Polynomial.aeval_def, Polynomial.hom_eval₂] at h0
    have e : (algebraMap ℂ (Matrix (Fin G.n) (Fin G.n) ℂ)).comp v.embedding = (G.psi v).comp (algebraMap G.F G.C) := by
      apply RingHom.ext
      intro a
      simp only [RingHom.comp_apply, G.psi_F, Matrix.algebraMap_eq_diagonal, Matrix.scalar_apply]
      rfl
    rw [e]
    exact h0
  have := eval_eq_zero_of_eigenvector _ x μ hx0 hx _ hq
  rwa [Polynomial.eval_map] at this

end GlobalTheory.LKMid
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MarkWeightedFixedPointDefinitePairOddOfCounts

section

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.LKDef
open scoped TensorProduct Classical

namespace GlobalTheory.RootSumWeights

theorem exists_root_enum {F : Type} [Field F] (τ : F →+* ℂ) (n : ℕ) :
    ∃ sel : Fin n → Polynomial F → ℂ, ∀ P : Polynomial F, P.Monic → P.natDegree = n →
      (P.map τ).roots = Finset.univ.val.map fun i => sel i P := by
  have key : ∀ P : Polynomial F, ∃ g : Fin n → ℂ, P.Monic → P.natDegree = n →
      (P.map τ).roots = Finset.univ.val.map g := by
    intro P
    by_cases h : P.Monic ∧ P.natDegree = n
    · have hc : (P.map τ).roots.toList.length = n := by
        rw [Multiset.length_toList, ← (IsAlgClosed.splits (P.map τ)).natDegree_eq_card_roots,
          h.1.natDegree_map, h.2]
      obtain ⟨l, hl, hl'⟩ : ∃ l : List ℂ, l.length = n ∧ (P.map τ).roots = (l : Multiset ℂ) :=
        ⟨_, hc, (Multiset.coe_toList _).symm⟩
      subst hl
      exact ⟨l.get, fun _ _ => by rw [Fin.univ_val_map, List.ofFn_get, hl']⟩
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose g hg using key
  exact ⟨fun i P => g P i, hg⟩

theorem markWeightedFixedPoint_definitePair_odd_of_counts : GlobalTheory.LKDef.MoveDefInv → GlobalTheory.RootSumWeights.CxCountRegMark → GlobalTheory.RootSumWeights.FinitelyManyMarkedClassesTermDegreeOne → GlobalTheory.RootSumWeights.MarkWeightedFixedPointEqDefinitePairOdd := by
  intro hmove hcount hfin p _ G ha hn v hv c L f hf hreg K' f' hf' h0
  rw [hcount p G ha v hv c L f hf hreg K' f' hf']
  obtain ⟨sel, hsel⟩ := exists_root_enum v.embedding G.n
  have hmon : ∀ x : G.C, (minpoly G.F x).Monic := fun x => minpoly.monic (Algebra.IsIntegral.isIntegral x)
  have hmem : ∀ P : Polynomial G.F, P.Monic → P.natDegree = G.n → ∀ μ : ℂ,
      P.eval₂ v.embedding μ = 0 ↔ ∃ i, sel i P = μ := by
    intro P hm hd μ
    rw [← Polynomial.eval_map, ← Polynomial.IsRoot.def, ← Polynomial.mem_roots (hm.map _).ne_zero, hsel P hm hd]
    simp
  have hIs : ∀ i, IsSel G (sel i) := by
    intro i w hw P hm hd
    have hc : Fintype.card {w : InfinitePlace G.F // sigPosH (G.gram_herm w) = 1} = 1 := ha
    obtain ⟨u, hu⟩ := Fintype.card_eq_one_iff.1 hc
    have hwv : w = v := congrArg Subtype.val ((hu ⟨w, hw⟩).trans (hu ⟨v, hv⟩).symm)
    subst hwv
    exact (hmem P hm hd _).2 ⟨i, rfl⟩
  have hF := hfin p G ha L f K' f' hf hf'

  have hL : markSumC G c L.K.toSubgroup f K' f' =
      ∑ i, markedSumIrr G (fun P => c P (sel i P)) (sel i) L.K.toSubgroup f 1 K' f' := by
    unfold markSumC markedSumIrr
    rw [← finsum_sum_comm]
    · refine finsum_congr fun q => ?_
      set P : Pair G := Quot.out q
      by_cases hm : ∃ μ, P.Mark μ
      · rw [dite_eq_left hm]
        by_cases hi : Irreducible P.pol
        · have hμ := hm.choose_spec
          obtain ⟨j, hj⟩ := (hmem P.pol (hmon _) P.reg.1 _).1 (mark_isRoot_pol p G P _ ha hμ v hv)
          have hnd : (Finset.univ.val.map fun i => sel i P.pol).Nodup := by
            rw [← hsel P.pol (hmon _) P.reg.1]
            exact Polynomial.nodup_roots (P.reg.2.map)
          have hinj := Multiset.inj_on_of_nodup_map hnd
          rw [Finset.sum_eq_single j]
          · rw [if_pos ⟨hi, hj ▸ hμ⟩]
            beta_reduce
            rw [hj]
          · intro i _ hij
            rw [if_neg]
            rintro ⟨-, hi'⟩
            exact hij (hinj i (Finset.mem_univ_val i) j (Finset.mem_univ_val j)
              ((Pair.mark_unique p G P _ _ ha hi' hμ).trans hj.symm))
          · intro h; exact absurd (Finset.mem_univ _) h
        · rw [h0 P hm hi, mul_zero]
          exact (Finset.sum_eq_zero fun i _ => if_neg fun h => hi h.1).symm
      · rw [dite_eq_right hm]
        exact (Finset.sum_eq_zero fun i _ => if_neg fun h => hm ⟨_, h.2⟩).symm
    · intro i _
      refine hF.subset fun q hq => ?_
      rw [Function.mem_support] at hq
      split_ifs at hq with h
      · exact ⟨⟨_, h.2⟩, right_ne_zero_of_mul hq⟩
      · exact absurd rfl hq

  have hD : {q : DCls G | Irreducible (Quot.out q).pol ∧ (Quot.out q).term L.K.toSubgroup f 1 K' f' ≠ 0}.Finite := by
    obtain ⟨e, he⟩ := cls_equiv_dcls_irr p G ha hn _ (hIs ⟨0, G.n_pos⟩)
    have h1 := (hF.preimage (f := fun q : {q : Cls G // Irreducible (Quot.out q).pol ∧
      (Quot.out q).Mark (sel ⟨0, G.n_pos⟩ (Quot.out q).pol)} => q.1) Subtype.val_injective.injOn).image
      fun q => (e q).1
    refine h1.subset fun d hd => ⟨e.symm ⟨d, hd.1⟩, ⟨⟨_, (e.symm ⟨d, hd.1⟩).2.2⟩, ?_⟩, by simp⟩
    rw [← (he _).2 L.K.toSubgroup f 1 K' f' one_pos hf.2.2.1 hf'.2.2.1, Equiv.apply_symm_apply]
    exact hd.2
  rw [hL, Finset.sum_congr rfl fun i _ =>
    hmove p G ha hn _ _ (hIs i) L.K.toSubgroup f 1 K' f' one_pos hf.2.2.1 hf'.2.2.1]
  unfold dSumIrr
  rw [← finsum_sum_comm]
  · refine finsum_congr fun q => ?_
    set Q : DPair G := Quot.out q
    by_cases hi : Irreducible Q.pol
    · simp only [if_pos hi]
      rw [← Finset.sum_mul, rootSum, hsel Q.pol (hmon _) Q.reg.1, Multiset.map_map]
      rfl
    · simp only [if_neg hi, Finset.sum_const_zero]
  · intro i _
    refine hD.subset fun q hq => ?_
    rw [Function.mem_support] at hq
    split_ifs at hq with h
    · exact ⟨h, right_ne_zero_of_mul hq⟩
    · exact absurd rfl hq

end GlobalTheory.RootSumWeights
end
end
