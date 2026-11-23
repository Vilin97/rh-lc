module

public import Formalism.PeriodIntegrals.OrbAddOne
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitJetLogarithm.ProdRenameExpJetSeries
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitPowerSeriesCoefficients.JetMul
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitJetLogarithm.ApplyAt0EqZeroOfOrder

section

@[expose] public section

noncomputable section

open scoped BigOperators
open Classical

namespace PI.OrbJet.OJ

section Lin

variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] {N0 N1 : ℕ} (l : ℕ) [Fact l.Prime]

theorem applyTerm_addT (T1 T2 : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) (μ : XZ Lt N0 N1 →₀ ℕ) (c : ℤ) :
    applyTerm l (T1 + T2) μ c = applyTerm l T1 μ c + applyTerm l T2 μ c := by
  simp [applyTerm, mul_add, map_add (f := _)]

theorem applyAt0_addT (T1 T2 : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) (P : MvPolynomial (XZ Lt N0 N1) ℤ) :
    applyAt0 N0 N1 l (T1 + T2) P = applyAt0 N0 N1 l T1 P + applyAt0 N0 N1 l T2 P := by
  simp only [applyAt0_eq_sum, applyTerm_addT, Finset.sum_add_distrib]

theorem applyAt0_zeroT (P : MvPolynomial (XZ Lt N0 N1) ℤ) :
    applyAt0 N0 N1 l (0 : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) P = 0 := by
  simp [applyAt0_eq_sum, applyTerm]

theorem applyAt0_smulT (a : ℂ_[l]) (T : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l])
    (P : MvPolynomial (XZ Lt N0 N1) ℤ) :
    applyAt0 N0 N1 l (a • T) P = a • applyAt0 N0 N1 l T P := by
  simp only [applyAt0_eq_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  simp only [applyTerm, MvPolynomial.smul_monomial, map_smul, smul_eq_mul]
  congr 1
  ring

theorem applyAt0_sumT {ι : Type*} (s : Finset ι) (T : ι → MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l])
    (P : MvPolynomial (XZ Lt N0 N1) ℤ) :
    applyAt0 N0 N1 l (∑ i ∈ s, T i) P = ∑ i ∈ s, applyAt0 N0 N1 l (T i) P := by
  induction s using Finset.induction_on with
  | empty => simp [applyAt0_zeroT]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, applyAt0_addT, ih]

theorem degree_snd_le (μ : XZ Lt N0 N1 →₀ ℕ) :
    Finsupp.degree (Finsupp.sumFinsuppEquivProdFinsupp μ).2 ≤ Finsupp.degree μ := by
  rw [Finsupp.degree_apply, Finsupp.degree_apply]
  calc ∑ j ∈ (Finsupp.sumFinsuppEquivProdFinsupp μ).2.support, (Finsupp.sumFinsuppEquivProdFinsupp μ).2 j
      = ∑ j ∈ (Finsupp.sumFinsuppEquivProdFinsupp μ).2.support, μ (Sum.inr j) := by
        simp [Finsupp.snd_sumFinsuppEquivProdFinsupp]
    _ = ∑ i ∈ (Finsupp.sumFinsuppEquivProdFinsupp μ).2.support.map Function.Embedding.inr, μ i := by
        rw [Finset.sum_map]; rfl
    _ ≤ ∑ i ∈ μ.support, μ i := by
        refine Finset.sum_le_sum_of_subset ?_
        intro i hi
        simp only [Finset.mem_map, Finsupp.mem_support_iff, Finsupp.snd_sumFinsuppEquivProdFinsupp] at hi
        obtain ⟨j, hj, rfl⟩ := hi
        simpa using hj

theorem applyAt0_eq_zero_of_order (T : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) (P : MvPolynomial (XZ Lt N0 N1) ℤ)
    (h : (P.totalDegree : ℕ∞) < T.order) : applyAt0 N0 N1 l T P = 0 := by
  rw [applyAt0_eq_sum]
  refine Finset.sum_eq_zero fun μ hμ => ?_
  have hd : Finsupp.degree (Finsupp.sumFinsuppEquivProdFinsupp μ).2 ≤ P.totalDegree :=
    (degree_snd_le μ).trans (by rw [Finsupp.degree_apply]; exact MvPolynomial.le_totalDegree hμ)
  have : MvPowerSeries.coeff (Finsupp.sumFinsuppEquivProdFinsupp μ).2 T = 0 :=
    MvPowerSeries.coeff_of_lt_order (lt_of_le_of_lt (by exact_mod_cast hd) h)
  unfold applyTerm
  rw [this, mul_zero, map_zero]

end Lin

section Trunc

variable {σ : Type*} [Finite σ] {K : Type*} [Field K]

theorem trunc_split (n : ℕ) (U : MvPowerSeries σ K) :
    ∃ (S : Finset (σ →₀ ℕ)) (V : MvPowerSeries σ K),
      U = (∑ k ∈ S, MvPowerSeries.monomial k (MvPowerSeries.coeff k U)) + V ∧ (n : ℕ∞) < V.order := by
  let Q := MvPowerSeries.truncTotal (n + 1) U
  refine ⟨Q.support, U - (Q : MvPowerSeries σ K), ?_, ?_⟩
  · have hQ : (Q : MvPowerSeries σ K) = ∑ k ∈ Q.support, MvPowerSeries.monomial k (MvPowerSeries.coeff k U) := by
      conv_lhs => rw [Q.as_sum]

      rw [show ((∑ k ∈ Q.support, MvPolynomial.monomial k (AddMonoidAlgebra.coeff Q k) : MvPolynomial σ K) :
        MvPowerSeries σ K) = ∑ k ∈ Q.support, ((MvPolynomial.monomial k (AddMonoidAlgebra.coeff Q k) :
        MvPolynomial σ K) : MvPowerSeries σ K) from map_sum (MvPolynomial.coeToMvPowerSeries.ringHom) _ _]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [MvPolynomial.coe_monomial]
      congr 1
      rw [MvPowerSeries.coeff_truncTotal_eq_ite]
      split_ifs with h
      · rfl
      · exact absurd hk (by rw [MvPolynomial.mem_support_iff, MvPowerSeries.coeff_truncTotal_eq_ite, if_neg h]; simp)
    rw [← hQ]; ring
  · have h1 : ((n + 1 : ℕ) : ℕ∞) ≤ (U - (Q : MvPowerSeries σ K)).order := by
      refine MvPowerSeries.le_order fun d hd => ?_
      rw [map_sub, MvPolynomial.coeff_coe, MvPowerSeries.coeff_truncTotal_eq_ite, if_pos, sub_self]
      exact_mod_cast hd
    exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self n) h1

end Trunc

end PI.OrbJet.OJ

end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitJetLogarithm.OrbitsAddAtConjugate

section

@[expose] public section

noncomputable section

open scoped BigOperators
open Classical

namespace PI.OrbJet.AO

open MvPowerSeries Formalism.BasicNotions Formalism.MainNotions.G PI.OrbJet.OJ

variable {p : ℕ} [Fact p.Prime]

theorem bound_place {D : D7} (E : Ent D) (h5 : 5 ≤ p) (u : D.what₂.Word) (i : ℕ) (β : Pl D → ℝ)
    (hβ : ∀ z, OneGe E p h5 u i z (β z)) (c : ℂ_[p]) (hc : ‖c‖ = 1) (ep sg : Pl D → ℂ_[p])
    (hep : ∀ z, ‖ep z‖ = 1) (hsg : ∀ z, sg z = 1 ∨ sg z = -1) (be : Pl D → MvPowerSeries (ZMod 2) ℂ_[p])
    (hbe : ∀ z, OJ.B1 p 2 (be z) ∧ OJ.B2 p 2 (be z) ∧ OJ.B3 p 2 (be z) ∧ OJ.B4 p 2 (be z))
    (I : ColChoice (D.R.N (i + 1)) (E.nu u i)) (k : Pl D × Fin (D.R.N i) × Fin (D.R.N (i + 1)) →₀ ℕ)
    (z : Pl D) (m' : Pl D × ℕ × Fin (D.R.N i) →₀ ℕ) :
    ‖AddMonoidAlgebra.coeff (applyAt0 (D.R.N i) (D.R.N (i + 1)) p
      (rename (pEmb (ptE D z) (Fin (D.R.N i) × Fin (D.R.N (i + 1))))
        (T1 (D.R.N i) (D.R.N (i + 1)) c (ep z) (sg z) (be z) (kz D z k)))
      (∏ c' : Fin ((E.nu u i z).rowLen 0), minorXZ (D.R.N i) (D.R.N (i + 1)) z ((E.nu u i z).colLen c') (I z c'))) m'‖
      ≤ (p : ℝ) ^ (-β z) := by
  have hadm := admissible_jet_term E h5 u i z c hc (ep z) (sg z) (hep z) (hsg z) (be z) (hbe z) (kz D z k)
  have hK := hβ z _ hadm
  have hP : MvPolynomial.rename (xzMap (N0 := D.R.N i) (N1 := D.R.N (i + 1)) (ptE D z))
      (Gxz (D.R.N i) (D.R.N (i + 1)) (fun _ : ZMod 1 => E.nu u i z) (fun _ c' => I z c')) =
      ∏ c' : Fin ((E.nu u i z).rowLen 0),
        minorXZ (D.R.N i) (D.R.N (i + 1)) z ((E.nu u i z).colLen c') (I z c') := by
    simp only [Gxz, map_prod, rename_minorXZ, ptE_apply, Finset.prod_const, Finset.card_univ,
      ZMod.card, pow_one]
  rw [← hP, applyAt0_rename]
  exact norm_coeff_rename_le _ _ (Real.rpow_nonneg (Nat.cast_nonneg _) _) (fun m => hK _ m) m'

theorem order_psi_gt (c : ℂ_[p]) {τ : Type*} [Finite τ] (n : ℕ) (V X : MvPowerSeries τ ℂ_[p])
    (hV : (n : ℕ∞) < V.order) : (n : ℕ∞) < (subst (psiA p c) (V * X)).order := by
  have hs := hs_psiA (p := p) c (τ := τ)
  have h1 : (1 : ℕ∞) ≤ ⨅ v : τ, (psiA p c v).order := by
    refine le_iInf fun v => ?_
    refine MvPowerSeries.le_order fun d hd => ?_
    have hd1 : Finsupp.degree d < 1 := by exact_mod_cast hd
    have hd0 : d = 0 := (Finsupp.degree_eq_zero_iff d).mp (Nat.lt_one_iff.mp hd1)
    rw [hd0, MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact cc_psubst (p := p) _ (by simp) _ (Ep_const (p := p))
  have h2 : V.order ≤ (V * X).order :=
    le_trans le_self_add MvPowerSeries.le_order_mul
  calc (n : ℕ∞) < V.order := hV
    _ ≤ (V * X).order := h2
    _ = 1 * (V * X).order := (one_mul _).symm
    _ ≤ (⨅ v : τ, (psiA p c v).order) * (V * X).order :=
      mul_le_mul_of_nonneg_right h1 (by simp)
    _ ≤ (subst (psiA p c) (V * X)).order := MvPowerSeries.le_order_subst hs _

theorem orbitsAddAtConjugate (D : D7) (E : Ent D) : OrbitsAddAtConjugate E := by
  intro p _ h5 hn u i _ β hβ Th hB I m
  obtain ⟨ep0, hep0, be, hbe, ep, hep, sg, hsg, U, hU, hEq⟩ := hB
  have hep0' : ep0 ≠ 0 := by
    rintro rfl
    simp at hep0
  have hcc : ∀ z, constantCoeff (be z) = 0 := fun z => constantCoeff_zero_of_bound_two (be z) (hbe z).2.2.1
  have hphi : (fun v : Pl D × Fin (D.R.N i) × Fin (D.R.N (i + 1)) =>
      MvPowerSeries.C ep0 * logPl D p v) = phiA p ep0 := by
    funext v
    rw [logPl_one (p := p) D hn v]
    rfl
  have hEq' : subst (phiA p ep0) Th =
      U * subst (logPl D p (β := Fin (D.R.N i) × Fin (D.R.N (i + 1))))
        (OJ.expS ℂ_[p] (fAll D (D.R.N i) (D.R.N (i + 1)) ep sg be)) := by
    rw [← hphi]
    exact hEq
  have hTh : Th = subst (psiA p ep0)
      (U * subst (logPl D p (β := Fin (D.R.N i) × Fin (D.R.N (i + 1))))
        (OJ.expS ℂ_[p] (fAll D (D.R.N i) (D.R.N (i + 1)) ep sg be))) := by
    rw [← hEq', psi_phi (p := p) ep0 hep0' Th]
  have hdisj : ((Finset.univ : Finset (Pl D)) : Set (Pl D)).PairwiseDisjoint
      (fun z : Pl D => ({z} : Set (Pl D))) := by
    intro x _ y _ hxy
    exact Set.disjoint_singleton.mpr hxy
  have hprod : ∀ (k : Pl D × Fin (D.R.N i) × Fin (D.R.N (i + 1)) →₀ ℕ)
      (m' : Pl D × ℕ × Fin (D.R.N i) →₀ ℕ),
      ‖AddMonoidAlgebra.coeff (applyAt0 (D.R.N i) (D.R.N (i + 1)) p
        (∏ z, rename (pEmb (ptE D z) (Fin (D.R.N i) × Fin (D.R.N (i + 1))))
          (T1 (D.R.N i) (D.R.N (i + 1)) ep0 (ep z) (sg z) (be z) (kz D z k)))
        (Gxz (D.R.N i) (D.R.N (i + 1)) (E.nu u i) I)) m'‖ ≤ (p : ℝ) ^ (-∑ z, β z) := by
    intro k m'
    have hT : ∀ z ∈ (Finset.univ : Finset (Pl D)),
        SerIn {v : Pl D × Fin (D.R.N i) × Fin (D.R.N (i + 1)) | v.1 ∈ ({z} : Set (Pl D))}
          (rename (pEmb (ptE D z) (Fin (D.R.N i) × Fin (D.R.N (i + 1))))
            (T1 (D.R.N i) (D.R.N (i + 1)) ep0 (ep z) (sg z) (be z) (kz D z k))) := by
      intro z _
      refine SerIn.mono ?_ (serIn_rename (ptE D z) _)
      rintro v ⟨s, hs⟩
      rw [ptE_apply] at hs
      exact hs.symm
    have hP : ∀ z ∈ (Finset.univ : Finset (Pl D)),
        (∏ c' : Fin ((E.nu u i z).rowLen 0),
          minorXZ (D.R.N i) (D.R.N (i + 1)) z ((E.nu u i z).colLen c') (I z c')) ∈
        MvPolynomial.supported ℤ (xzLetter ⁻¹' ({z} : Set (Pl D))) := by
      intro z _
      exact Subalgebra.prod_mem _ fun c' _ => minorXZ_supported _ _ _
    have hG : Gxz (D.R.N i) (D.R.N (i + 1)) (E.nu u i) I = ∏ z ∈ (Finset.univ : Finset (Pl D)),
        ∏ c' : Fin ((E.nu u i z).rowLen 0),
          minorXZ (D.R.N i) (D.R.N (i + 1)) z ((E.nu u i z).colLen c') (I z c') := rfl
    have happ : applyAt0 (D.R.N i) (D.R.N (i + 1)) p
        (∏ z, rename (pEmb (ptE D z) (Fin (D.R.N i) × Fin (D.R.N (i + 1))))
          (T1 (D.R.N i) (D.R.N (i + 1)) ep0 (ep z) (sg z) (be z) (kz D z k)))
        (∏ z ∈ (Finset.univ : Finset (Pl D)), ∏ c' : Fin ((E.nu u i z).rowLen 0),
          minorXZ (D.R.N i) (D.R.N (i + 1)) z ((E.nu u i z).colLen c') (I z c')) =
        ∏ z ∈ (Finset.univ : Finset (Pl D)), applyAt0 (D.R.N i) (D.R.N (i + 1)) p
          (rename (pEmb (ptE D z) (Fin (D.R.N i) × Fin (D.R.N (i + 1))))
            (T1 (D.R.N i) (D.R.N (i + 1)) ep0 (ep z) (sg z) (be z) (kz D z k)))
          (∏ c' : Fin ((E.nu u i z).rowLen 0),
            minorXZ (D.R.N i) (D.R.N (i + 1)) z ((E.nu u i z).colLen c') (I z c')) :=
      applyAt0_prod (l := p) _ _ hdisj _ _ hT hP
    rw [hG, happ, ← Finset.sum_neg_distrib,
      Real.rpow_sum_of_pos (by exact_mod_cast (Fact.out : p.Prime).pos)]
    refine norm_coeff_prod_le _ ?_ ?_ m'
    · intro z _
      exact Real.rpow_nonneg (Nat.cast_nonneg _) _
    · intro z _ m''
      exact bound_place E h5 u i β hβ ep0 hep0 ep sg hep hsg be hbe I k z m''
  have hfac := factor D hn (D.R.N i) (D.R.N (i + 1)) ep0 hep0' ep sg be hcc
  generalize subst (logPl D p (β := Fin (D.R.N i) × Fin (D.R.N (i + 1))))
      (OJ.expS ℂ_[p] (fAll D (D.R.N i) (D.R.N (i + 1)) ep sg be)) = L at hTh hfac
  obtain ⟨Sk, V, hUV, hV⟩ := trunc_split
    (Gxz (D.R.N i) (D.R.N (i + 1)) (E.nu u i) I).totalDegree U
  have hs := hs_psiA (p := p) ep0 (τ := Pl D × Fin (D.R.N i) × Fin (D.R.N (i + 1)))
  have hmon : ∀ k, MvPowerSeries.monomial k (MvPowerSeries.coeff k U) * L =
      MvPowerSeries.coeff k U • (MvPowerSeries.monomial k (1 : ℂ_[p]) * L) := by
    intro k
    rw [← smul_mul_assoc]
    congr 1
    have h := map_smul (MvPowerSeries.monomial k :
      ℂ_[p] →ₗ[ℂ_[p]] MvPowerSeries (Pl D × Fin (D.R.N i) × Fin (D.R.N (i + 1))) ℂ_[p])
      (MvPowerSeries.coeff k U) (1 : ℂ_[p])
    rw [smul_eq_mul, mul_one] at h
    exact h
  have hsplit : subst (psiA p ep0) (U * L) =
      ∑ k ∈ Sk, MvPowerSeries.coeff k U •
          subst (psiA p ep0) (MvPowerSeries.monomial k (1 : ℂ_[p]) * L)
        + subst (psiA p ep0) (V * L) := by
    conv_lhs => rw [hUV]

    rw [add_mul, Finset.sum_mul, ← MvPowerSeries.coe_substAlgHom (R := ℂ_[p]) hs, map_add (f := _), map_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hmon k, map_smul]
  have hord := order_psi_gt ep0 _ V L hV
  rw [hTh, hsplit, applyAt0_addT, applyAt0_sumT, applyAt0_eq_zero_of_order (h := hord), add_zero]
  simp only [applyAt0_smulT, hfac]
  rw [MvPolynomial.coeff_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (Real.rpow_nonneg (Nat.cast_nonneg _) _) fun k _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul, norm_mul]
  calc _ ≤ 1 * (p : ℝ) ^ (-∑ z, β z) := mul_le_mul (hU k) (hprod k m) (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

end PI.OrbJet.AO

end
end
end

-- Source module: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.OrbAddOne

section

@[expose] public section

theorem PI.OrbAddOne : ∀ (D : Formalism.BasicNotions.D7) (E : PI.OrbJet.Ent D), PI.OrbJet.OrbitsAddAtConjugate E :=
  PI.OrbJet.AO.orbitsAddAtConjugate
end
end
