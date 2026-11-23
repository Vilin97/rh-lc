module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensHI
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensFF
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensFFIn
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensFFS
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.Tactic.Linter.HaveILetI
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
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensHF
import Mathlib.Tactic.Polynomial.Basic
public import ReciprocityTheory.Automorphisms.InstMainA
public import ReciprocityTheory.ResidueCardinality.ArtinOntoB
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensHL

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensFFT

section

@[expose] public section

noncomputable section

namespace PI.VolStabS

namespace FiniteFieldCounting

theorem prod_bound {ι : Type} (δ : ι → ℝ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (h : ∀ j, |δ j| ≤ t) (s : Finset ι) :
    |∏ j ∈ s, (1 + δ j) - 1| ≤ t * (2 ^ s.card - 1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    have h1 : |∏ j ∈ s, (1 + δ j)| ≤ 1 + t * (2 ^ s.card - 1) := by
      have := abs_sub_abs_le_abs_sub (∏ j ∈ s, (1 + δ j)) 1
      rw [abs_one] at this
      linarith
    have hpow : (1 : ℝ) ≤ 2 ^ s.card := one_le_pow₀ (by norm_num)
    have h2 : |δ a * ∏ j ∈ s, (1 + δ j)| ≤ t * (1 + t * (2 ^ s.card - 1)) := by
      rw [abs_mul]
      exact mul_le_mul (h a) h1 (abs_nonneg _) ht0
    have h3 : (1 + δ a) * ∏ j ∈ s, (1 + δ j) - 1 =
        (∏ j ∈ s, (1 + δ j) - 1) + δ a * ∏ j ∈ s, (1 + δ j) := by ring
    rw [h3]
    have h4 : t * (t * (2 ^ s.card - 1)) ≤ t * (2 ^ s.card - 1) := by
      apply mul_le_mul_of_nonneg_left _ ht0
      nlinarith
    calc |(∏ j ∈ s, (1 + δ j) - 1) + δ a * ∏ j ∈ s, (1 + δ j)|
        ≤ |∏ j ∈ s, (1 + δ j) - 1| + |δ a * ∏ j ∈ s, (1 + δ j)| := abs_add_le _ _
      _ ≤ t * (2 ^ s.card - 1) + t * (1 + t * (2 ^ s.card - 1)) := add_le_add ih h2
      _ ≤ t * (2 ^ (s.card + 1) - 1) := by
          rw [pow_succ]
          nlinarith

theorem ratio_bound (M a : ℕ) (ha : a ≤ M) (q : ℝ) (hq : 1 ≤ q) (δ : Fin a → ℝ)
    (h : ∀ j, |δ j| ≤ (q⁻¹) ^ 2) : |∏ j, (1 + δ j) - 1| ≤ 2 ^ M * (q⁻¹) ^ 2 := by
  have hq0 : 0 ≤ q⁻¹ := inv_nonneg.mpr (by linarith)
  have hq1 : q⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hq
  have ht0 : 0 ≤ (q⁻¹) ^ 2 := by positivity
  have ht1 : (q⁻¹) ^ 2 ≤ 1 := pow_le_one₀ hq0 hq1
  have h1 := prod_bound δ _ ht0 ht1 h Finset.univ
  rw [Finset.card_univ, Fintype.card_fin] at h1
  have h2 : (2 : ℝ) ^ a ≤ 2 ^ M := pow_le_pow_right₀ (by norm_num) ha
  nlinarith

theorem inv_pow_le (q : ℝ) (hq : 1 ≤ q) (m : ℕ) (hm : 2 ≤ m) : (q⁻¹) ^ m ≤ (q⁻¹) ^ 2 := pow_le_pow_of_le_one (inv_nonneg.mpr (by linarith)) (inv_le_one_of_one_le₀ hq) hm

theorem exp_id (M a : ℕ) (ha : a ≤ M) : M * a + a * (M - a) = 2 * M * a - a ^ 2 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le ha
  rw [Nat.add_sub_cancel_left]
  symm
  apply Nat.sub_eq_of_eq_add
  ring

theorem sum_exp (M : ℕ) : ∀ a, a ≤ M →
    ∑ j ∈ Finset.range a, (2 * (M - j) - 1) = 2 * M * a - a ^ 2 := by
  intro a
  induction a with
  | zero => intro _; simp
  | succ a ih =>
    intro ha
    rw [Finset.sum_range_succ, ih (by omega)]
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le ha
    have e1 : a + 1 + d - a = d + 1 := by omega
    rw [e1]
    have e2 : 2 * (a + 1 + d) * a - a ^ 2 = a ^ 2 + 2 * a * (d + 1) := by
      apply Nat.sub_eq_of_eq_add
      ring
    have e3 : 2 * (a + 1 + d) * (a + 1) - (a + 1) ^ 2 = (a + 1) ^ 2 + 2 * (a + 1) * d := by
      apply Nat.sub_eq_of_eq_add
      ring
    rw [e2, e3]
    have e4 : 2 * (d + 1) - 1 = 2 * d + 1 := by omega
    rw [e4]
    ring

theorem split_ratio (M a : ℕ) (ha : a ≤ M) (q : ℝ) (hq : q ≠ 0) :
    (∏ i : Fin a, (q ^ M - q ^ (i : ℕ))) * q ^ (a * (M - a)) / q ^ (2 * M * a - a ^ 2) =
      ∏ i : Fin a, (1 + -(q ^ (i : ℕ) / q ^ M)) := by
  have hqM : q ^ M ≠ 0 := pow_ne_zero _ hq
  rw [← exp_id M a ha, pow_add]
  have h1 : ∀ i : Fin a, q ^ M - q ^ (i : ℕ) = q ^ M * (1 + -(q ^ (i : ℕ) / q ^ M)) := by
    intro i
    field_simp
    ring
  simp_rw [h1]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
  have hA : q ^ (M * a) ≠ 0 := pow_ne_zero _ hq
  have hB : q ^ (a * (M - a)) ≠ 0 := pow_ne_zero _ hq
  rw [mul_comm (q ^ (M * a)), mul_assoc, mul_div_assoc, div_self (mul_ne_zero hA hB), mul_one]

theorem inert_ratio (M a : ℕ) (ha : a ≤ M) (q : ℝ) (hq : q ≠ 0) :
    (∏ j : Fin a, (q ^ (2 * (M - j) - 1) - (-1) ^ (M - j) * q ^ (M - j - 1))) /
        q ^ (2 * M * a - a ^ 2) =
      ∏ j : Fin a, (1 + -((-1) ^ (M - j) * q ^ (M - j - 1) / q ^ (2 * (M - j) - 1))) := by
  have hs : ∑ j : Fin a, (2 * (M - (j : ℕ)) - 1) = 2 * M * a - a ^ 2 :=
    (Fin.sum_univ_eq_sum_range (fun j => 2 * (M - j) - 1) a).trans (sum_exp M a ha)
  have hden : q ^ (2 * M * a - a ^ 2) = ∏ j : Fin a, q ^ (2 * (M - (j : ℕ)) - 1) := by
    rw [Finset.prod_pow_eq_pow_sum, hs]
  rw [hden, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  have hB : q ^ (2 * (M - (j : ℕ)) - 1) ≠ 0 := pow_ne_zero _ hq
  rw [sub_div, div_self hB]
  ring

theorem split_delta (M a : ℕ) (ha : a + 2 ≤ M) (q : ℝ) (hq : 1 ≤ q) (i : Fin a) :
    |-(q ^ (i : ℕ) / q ^ M)| ≤ (q⁻¹) ^ 2 := by
  have hq0 : 0 < q := by linarith
  have hi := i.isLt
  rw [abs_neg, abs_of_nonneg (div_nonneg (pow_nonneg hq0.le _) (pow_nonneg hq0.le _))]
  have hM : M = (i : ℕ) + (M - i) := by omega
  have h1 : q ^ (i : ℕ) / q ^ M = (q⁻¹) ^ (M - i) := by
    conv_lhs => rw [hM, pow_add]
    rw [div_mul_eq_div_div, div_self (pow_ne_zero _ hq0.ne'), inv_pow, one_div]
  rw [h1]
  exact inv_pow_le q hq (M - i) (by omega)

theorem inert_delta (M a : ℕ) (ha : a + 2 ≤ M) (q : ℝ) (hq : 1 ≤ q) (j : Fin a) :
    |-((-1) ^ (M - j) * q ^ (M - j - 1) / q ^ (2 * (M - j) - 1))| ≤ (q⁻¹) ^ 2 := by
  have hq0 : 0 < q := by linarith
  have hj := j.isLt
  rw [abs_neg, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_pos (pow_pos hq0 _), abs_of_pos (pow_pos hq0 _)]
  have he : 2 * (M - (j : ℕ)) - 1 = (M - (j : ℕ) - 1) + (M - (j : ℕ)) := by omega
  rw [he, pow_add, div_mul_eq_div_div, div_self (pow_ne_zero _ hq0.ne'), one_div, ← inv_pow]
  exact inv_pow_le q hq _ (by omega)

theorem card_transport {k K : Type} [Field k] [CommRing K] [Algebra k K] (σ : K ≃ₐ[k] K)
    (e : K ≃ₐ[k] k × k) (he : ∀ x, e (σ x) = (e x).swap) {M a : ℕ}
    (J : Matrix (Fin M) (Fin M) K) (T : Matrix (Fin a) (Fin a) K) :
    Nat.card {X : Fin a → Fin M → K // ffGram (σ : K →+* K) J X = T} =
      Nat.card {Y : Fin a → Fin M → k × k //
        ffGram (FiniteFieldSplitting.swapR k) (J.map e) Y = T.map e} := by
  apply Nat.card_congr
  refine Equiv.subtypeEquiv (Equiv.piCongrRight fun _ => Equiv.piCongrRight fun _ => e.toEquiv) ?_
  intro X
  have key : ffGram (FiniteFieldSplitting.swapR k) (J.map e)
      ((Equiv.piCongrRight fun _ => Equiv.piCongrRight fun _ => e.toEquiv) X) =
        (ffGram (σ : K →+* K) J X).map e := by
    funext i j
    show ∑ a', ∑ b, (e (X i a')).swap * e (J a' b) * e (X j b) =
      e (∑ a', ∑ b, σ (X i a') * J a' b * X j b)

    rw [map_sum]
    refine Finset.sum_congr rfl fun a' _ => ?_

    rw [map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_mul, map_mul, he]
  rw [key]
  constructor
  · intro h
    rw [h]
  · intro h
    ext i j
    exact e.injective (congrFun (congrFun h i) j)

end FiniteFieldCounting

theorem fFCount_of (hS : FFSplit) (hI : FFInert) : FFCount := by
  intro M
  refine ⟨2 ^ M, ?_⟩
  intro k K _ _ _ _ σ hσ h2 J hJ hJd a ha T hT hTd
  have hq1 : (1 : ℝ) ≤ (Nat.card k : ℝ) := by exact_mod_cast Nat.card_pos
  have hq0 : (Nat.card k : ℝ) ≠ 0 := by linarith
  have haM : a ≤ M := by omega
  rcases hσ.2 with ⟨hF, hrank, hne⟩ | ⟨e, he⟩
  · letI : Field K := hF.toField
    have hc := hI k K σ hσ.1 hrank hne h2 M a haM J hJ hJd T hT hTd
    rw [hc, FiniteFieldCounting.inert_ratio M a haM _ hq0]
    exact FiniteFieldCounting.ratio_bound M a haM _ hq1 _ (fun j => FiniteFieldCounting.inert_delta M a ha _ hq1 j)
  · have hc := FiniteFieldCounting.card_transport σ e he J T
    have hJ' : ∀ i j, ((J.map e) j i).swap = (J.map e) i j := by
      intro i j
      simp only [Matrix.map_apply]
      rw [← he, hJ]
    have hT' : ∀ i j, ((T.map e) j i).swap = (T.map e) i j := by
      intro i j
      simp only [Matrix.map_apply]
      rw [← he, hT]
    have hJd' : IsUnit (J.map e).det := by
      have h := hJd.map (e : K →+* k × k)
      rwa [RingHom.map_det] at h
    have hTd' : IsUnit (T.map e).det := by
      have h := hTd.map (e : K →+* k × k)
      rwa [RingHom.map_det] at h
    have hs : (Nat.card {Y : Fin a → Fin M → k × k //
        ffGram (FiniteFieldSplitting.swapR k) (J.map e) Y = T.map e} : ℝ) =
        (∏ i : Fin a, ((Nat.card k : ℝ) ^ M - (Nat.card k : ℝ) ^ (i : ℕ))) *
          (Nat.card k : ℝ) ^ (a * (M - a)) := hS k M a haM (J.map e) hJ' hJd' (T.map e) hT' hTd'
    rw [hc, hs, FiniteFieldCounting.split_ratio M a haM _ hq0]
    exact FiniteFieldCounting.ratio_bound M a haM _ hq1 _ (fun i => FiniteFieldCounting.split_delta M a ha _ hq1 i)

theorem fFCount_of_inert (hI : FFInert) : FFCount := fFCount_of fFSplit_holds hI

end PI.VolStabS
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensFFAll

section

@[expose] public section

namespace PI.VolStabS

theorem fFCount_holds : FFCount := fFCount_of_inert FFHS.fFInert_holds

end PI.VolStabS
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensHIL

section

@[expose] public section

noncomputable section

namespace PI.VolStabS

namespace IdxLW

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsLocalRing

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem index_maxIdeal :
    (maximalIdeal (v.adicCompletionIntegers F)).toAddSubgroup.index = Nat.card (𝓞 F ⧸ v.asIdeal) := by
  rw [← ReciprocityTheory.Bridge.ResidueFieldCardinality.card_residue v]
  rfl

variable {E : Type} [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E) (a M : ℕ)

def crdL : latSub b v a M →+ (Fin a × Fin M × Fin d → v.adicCompletionIntegers F) where
  toFun x q := ⟨(Algebra.TensorProduct.basis (Fv F v) b).repr ((x : Fin a → Fin M → Fv F v ⊗[F] E)
    q.1 q.2.1) q.2.2, x.2 q.1 q.2.1 q.2.2⟩
  map_zero' := by
    funext q
    apply Subtype.ext
    simp
  map_add' x y := by
    funext q
    apply Subtype.ext
    simp

theorem crdL_surj : Function.Surjective (crdL v b a M) := by
  intro c
  let x : Fin a → Fin M → Fv F v ⊗[F] E := fun i j =>
    (Algebra.TensorProduct.basis (Fv F v) b).repr.symm
      (Finsupp.equivFunOnFinite.symm fun k => (c (i, j, k) : Fv F v))
  have hx : ∀ i j k, (Algebra.TensorProduct.basis (Fv F v) b).repr (x i j) k = c (i, j, k) := by
    intro i j k
    simp [x]
  refine ⟨⟨x, fun i j k => by rw [hx]; exact (c (i, j, k)).2⟩, ?_⟩
  funext q
  apply Subtype.ext
  exact hx q.1 q.2.1 q.2.2

theorem crd_smul' (s : Fv F v) (y : Fv F v ⊗[F] E) (k : Fin d) :
    (Algebra.TensorProduct.basis (Fv F v) b).repr (s • y) k =
      s * (Algebra.TensorProduct.basis (Fv F v) b).repr y k := by
  simp [map_smul, Finsupp.smul_apply, smul_eq_mul]

theorem addSubgroupOf_eq :
    (lamF b v a M 0).addSubgroupOf (latSub b v a M) =
      (AddSubgroup.pi Set.univ fun _ : Fin a × Fin M × Fin d =>
        (maximalIdeal (v.adicCompletionIntegers F)).toAddSubgroup).comap (crdL v b a M) := by
  have hv := unifV_val v
  have h0 := (unifV_spec v).1
  ext x
  rw [AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_comap, AddSubgroup.mem_pi]
  simp only [Set.mem_univ, true_implies, Submodule.mem_toAddSubgroup, ReciprocityTheory.Aut.mem_maxIdeal_iff]
  constructor
  · intro hx q
    simp only [lamF, mem_smulSub, zero_add, pow_one] at hx
    obtain ⟨p, hp, hpx⟩ := hx
    show Valued.v ((Algebra.TensorProduct.basis (Fv F v) b).repr
      ((x : Fin a → Fin M → Fv F v ⊗[F] E) q.1 q.2.1) q.2.2) < 1
    rw [← hpx]
    simp only [Pi.smul_apply]
    rw [crd_smul', map_mul, hv]
    have hp' : Valued.v ((Algebra.TensorProduct.basis (Fv F v) b).repr (p q.1 q.2.1) q.2.2) ≤ 1 := by
      have h := hp q.1 q.2.1 q.2.2
      rwa [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] at h
    calc WithZero.exp (-1 : ℤ) * Valued.v ((Algebra.TensorProduct.basis (Fv F v) b).repr
          (p q.1 q.2.1) q.2.2) ≤ WithZero.exp (-1 : ℤ) * 1 := by gcongr
      _ < 1 := by rw [mul_one]; decide
  · intro hx
    simp only [lamF, mem_smulSub, zero_add, pow_one]
    refine ⟨(unifV v)⁻¹ • (x : Fin a → Fin M → Fv F v ⊗[F] E), ?_, ?_⟩
    · intro i j k
      rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
      simp only [Pi.smul_apply]
      rw [crd_smul', map_mul, map_inv₀, hv]
      have := ReciprocityTheory.Aut.val_le_exp_neg_one_of_lt_one v (hx (i, j, k))
      calc (WithZero.exp (-1 : ℤ))⁻¹ * Valued.v ((Algebra.TensorProduct.basis (Fv F v) b).repr
            ((x : Fin a → Fin M → Fv F v ⊗[F] E) i j) k)
          ≤ (WithZero.exp (-1 : ℤ))⁻¹ * WithZero.exp (-1 : ℤ) := by gcongr; exact this
        _ = 1 := inv_mul_cancel₀ (WithZero.exp_ne_zero)
    · rw [smul_smul, mul_inv_cancel₀ h0, one_smul]

end IdxLW

open IdxLW

theorem idxL_holds : IdxL := by
  intro F E _ _ _ _ _ σ hCM M J hJ _ _ a _ _ X0 hT _ d b v
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have hd : d = 2 := by
    have := Module.finrank_eq_card_basis b
    rw [hCM.2.2.1, Fintype.card_fin] at this
    exact this.symm
  unfold AddSubgroup.relIndex
  rw [addSubgroupOf_eq, AddSubgroup.index_comap_of_surjective _ (crdL_surj v b a M),
    AddSubgroup.index_pi]
  simp only [index_maxIdeal, Finset.prod_const, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin]
  subst hd
  ring_nf

end PI.VolStabS
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensHTop

section

@[expose] public section

namespace PI.VolStabS

theorem densAA_of_open (hV : VolAA) (hH : HensAA) (hI : IdxH) (hC : CntAA) : DensAA :=
  densAA_of fibLat_holds fFCount_holds
    (resAA_of hV latFacts_holds hH (idxAA_of idxL_holds hI) hC)

end PI.VolStabS
end
end
