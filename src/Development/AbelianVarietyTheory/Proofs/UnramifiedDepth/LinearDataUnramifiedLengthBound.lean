module

public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.DualNumberPointPreimageTopOfReduction
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EigenbasisRestrictionSurjectiveEquivariant
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EigenspaceDimAddSplitExactTranspose
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsEigenIdem
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsFreeGenerators
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.HasLenExistsMonoFp
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PadicPlaceBasisOfIdempotent
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PadicUnitQuotientPrincipalBasis
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TateModuleEigenspaceDimEqLieAlgebraSum
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.DualLattices.EmbeddingSeparatingGroupStatement
public import ReciprocityTheory.DualLattices.LiftMonomialDeterminantStatement
public import ReciprocityTheory.DualLattices.UnramifiedCokernelLowerBoundOf
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.DualLattices.EigenLengthProductStatementHolds
public import ReciprocityTheory.DualLattices.EigenLiftsFrobenius
public import ReciprocityTheory.DualLattices.ElementaryDivisorStatement
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
public import ReciprocityTheory.DualLattices.EigPowEqOne
public import ReciprocityTheory.DualLattices.SgAlgebraMap
public import ReciprocityTheory.DualLattices.EqZeroOfIsoZero
public import ReciprocityTheory.DualLattices.FrobeniusBlock
public import ReciprocityTheory.DualLattices.LenEx
import ReciprocityTheory.DualLattices.LiftMonomialDeterminantStatementHolds
public import ReciprocityTheory.DualLattices.MatEquivApply
public import ReciprocityTheory.DualLattices.MonomialsSpanOfProdEq
public import ReciprocityTheory.DualLattices.RankEqRankOfPermAndZero
public import ReciprocityTheory.DualLattices.SumX
import ReciprocityTheory.DualLattices.UnramifiedCokernelLengthOfLengthEigenLengthProduct
import ReciprocityTheory.DualLattices.LenEx
public import ReciprocityTheory.DualLattices.LengthDegreeAbelianVariety

-- Source module: ReciprocityTheory.DualLattices.EmbeddingSeparatingGroup

section

@[expose] public section

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

theorem embeddingSeparatingGroup : EmbeddingSeparatingGroupStatement := by
  intro p _ g C _ _ _ v R _ _ _ O _ _ σ cp hp2 hS H U
  have hv : v.Integers R := hS.integers
  have hpv : v (algebraMap R C (p : R)) < 1 := hS.p_lt
  have hp : p.Prime := Fact.out

  have hvnat : ∀ n : ℕ, ¬ p ∣ n → v (algebraMap R C (n : R)) = 1 := by
    intro n hn
    by_contra hne
    have hlt : v (algebraMap R C (n : R)) < 1 := lt_of_le_of_ne (hv.map_le_one _) hne
    have hcop : Nat.Coprime p n := (Nat.Prime.coprime_iff_not_dvd hp).2 hn
    have h1 : ((p : ℤ) * Nat.gcdA p n + (n : ℤ) * Nat.gcdB p n) = 1 := by
      rw [← Nat.gcd_eq_gcd_ab, Nat.Coprime.gcd_eq_one hcop, Nat.cast_one]
    have h2 : (p : R) * (Nat.gcdA p n : R) + (n : R) * (Nat.gcdB p n : R) = 1 := by
      have := congrArg (fun z : ℤ => (z : R)) h1
      push_cast at this
      exact this
    have h3 : v (algebraMap R C ((p : R) * (Nat.gcdA p n : R) + (n : R) * (Nat.gcdB p n : R))) < 1 := by
      rw [map_add (f := _)]
      refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ?_)
      · rw [map_mul, Valuation.map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_right zero_le (hv.map_le_one _)) hpv
      · rw [map_mul, Valuation.map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_right zero_le (hv.map_le_one _)) hlt
    rw [h2, map_one, Valuation.map_one] at h3
    exact lt_irrefl _ h3
  have hunit : ∀ n : ℕ, ¬ p ∣ n → IsUnit (n : R) := by
    intro n hn
    have hn0 : (n : C) ≠ 0 := by
      have : n ≠ 0 := fun h => hn (h ▸ dvd_zero p)
      exact_mod_cast this
    exact hv.isUnit_of_one (isUnit_iff_ne_zero.2 (by rw [map_natCast]; exact hn0)) (hvnat n hn)
  have hp2' : ¬ p ∣ 2 := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h)
  have heig : ∀ a j, (H.ρ a).map (algebraMap ℤ_[p] R) * U.εT j = U.sg j a • U.εT j := U.εT_eig
  have hres1 : FrobeniusGroupField.res hv 1 ≠ 0 := (FrobeniusGroupField.res_ne_zero hv 1).2 (by simp)

  have hex : ∀ t : Option (Fin U.m × Fin U.m × Bool), ∃ (b : O) (m : ℕ), 0 < m ∧ ¬ p ∣ m ∧
      H.ρ b ^ m = 1 ∧
      (match t with
        | none => ∀ j, U.εT j ≠ 0 → v (algebraMap R C (U.sg j b - 1)) = 1
        | some (i, k, e) => U.εT i ≠ 0 → U.εT k ≠ 0 → cond e (k ≠ U.φ i) (i ≠ k) →
            FrobeniusGroupField.res hv (U.sg k b) ≠ FrobeniusGroupField.res hv (U.sg i b) ^ p ^ e.toNat) := by
    intro t
    rcases t with _ | ⟨i, k, e⟩
    · obtain ⟨b, m, s, hm, hmp, hbm, hb⟩ := FrobeniusGroupField.seed p hv hpv H.ρ U.εT U.sg heig 0 2
      refine ⟨b, m, hm, hmp, hbm, ?_⟩
      intro j hj
      have h2 : FrobeniusGroupField.res hv (U.sg j 0 + ((2 : ℤ) : R)) = FrobeniusGroupField.res hv 2 := by simp
      have hr2 : FrobeniusGroupField.res hv 2 ≠ 0 := (FrobeniusGroupField.res_ne_zero hv 2).2 (by simpa using hvnat 2 hp2')
      have hfer : ∀ s : ℕ, FrobeniusGroupField.res hv 2 ^ p ^ s = FrobeniusGroupField.res hv 2 := by
        intro s
        induction s with
        | zero => simp
        | succ s ih =>
          have hf := FrobeniusGroupField.fermat p hv hpv (2 : ℤ_[p])
          rw [map_ofNat] at hf
          rw [pow_succ, pow_mul, ih, hf]
      have hbj := hb j hj (by rw [h2]; exact hr2)
      rw [h2, hfer] at hbj
      apply (FrobeniusGroupField.res_ne_zero hv _).1
      rw [map_sub, hbj, map_one]
      have h21 : FrobeniusGroupField.res hv 2 - 1 = FrobeniusGroupField.res hv 1 := by
        rw [← map_one (FrobeniusGroupField.res hv), ← map_sub]
        norm_num
      rw [h21]
      exact hres1
    · by_cases hall : U.εT i ≠ 0 ∧ U.εT k ≠ 0 ∧ cond e (k ≠ U.φ i) (i ≠ k)
      · obtain ⟨hi, hk, hik⟩ := hall
        have ha : ∃ a, FrobeniusGroupField.res hv (U.sg k a) ≠ FrobeniusGroupField.res hv (U.sg i a) ^ p ^ e.toNat := by
          cases e
          · simp only [cond_false, Bool.toNat_false, pow_zero, pow_one] at hik ⊢
            obtain ⟨a, ha⟩ := U.distinct i k hik
            refine ⟨a, fun heq => ?_⟩
            have h0 : FrobeniusGroupField.res hv (U.sg i a - U.sg k a) = 0 := by rw [map_sub, heq, sub_self]
            exact ((FrobeniusGroupField.res_ne_zero hv _).2 ha) h0
          · simp only [cond_true, Bool.toNat_true, pow_one] at hik ⊢
            obtain ⟨a, ha⟩ := U.distinct k (U.φ i) hik
            refine ⟨a, ?_⟩
            have hfr : FrobeniusGroupField.res hv (U.sg (U.φ i) a) = FrobeniusGroupField.res hv (U.sg i a) ^ p := by
              have h0 := (FrobeniusGroupField.res_eq_zero hv _).2 (U.frob i a)
              rw [map_sub, map_pow, sub_eq_zero] at h0
              exact h0
            rw [← hfr]
            intro heq
            have h0 : FrobeniusGroupField.res hv (U.sg k a - U.sg (U.φ i) a) = 0 := by rw [map_sub, heq, sub_self]
            exact ((FrobeniusGroupField.res_ne_zero hv _).2 ha) h0
        obtain ⟨a, ha⟩ := ha
        obtain ⟨b, m, hm, hmp, hbm, hb⟩ :=
          FrobeniusGroupField.pair p hp2 hv hpv H.ρ U.εT U.sg heig a e.toNat i k hi hk ha
        exact ⟨b, m, hm, hmp, hbm, fun _ _ _ => hb⟩
      · exact ⟨1, 1, one_pos, hp.not_dvd_one, by simp, fun hi hk hik => absurd ⟨hi, hk, hik⟩ hall⟩
  choose b m0 hm0 hmp0 hbm0 hQ using hex

  let m : Option (Fin U.m × Fin U.m × Bool) → ℕ := fun t => 2 * m0 t
  have hm : ∀ t, 0 < m t := fun t => by
    have := hm0 t
    show 0 < 2 * m0 t
    omega
  have hmp : ∀ t, ¬ p ∣ m t := fun t h => ((Nat.Prime.dvd_mul hp).1 h).elim hp2' (hmp0 t)
  have hbm : ∀ t, H.ρ (b t) ^ m t = 1 := fun t => by
    show H.ρ (b t) ^ (2 * m0 t) = 1
    rw [mul_comm, pow_mul, hbm0 t, one_pow]
  haveI : ∀ t, NeZero (m t) := fun t => ⟨(hm t).ne'⟩
  have hone : ∀ t, (1 : ZMod (m t)).val = 1 := fun t => by
    rw [ZMod.val_one_eq_one_mod]
    exact Nat.mod_eq_of_lt (by have := hm0 t; show 1 < 2 * m0 t; omega)
  let G := ∀ t : Option (Fin U.m × Fin U.m × Bool), Multiplicative (ZMod (m t))
  let β : G → O := fun γ => ∏ t, b t ^ (Multiplicative.toAdd (γ t)).val
  have key : ∀ (s : Finset (Option (Fin U.m × Fin U.m × Bool)))
      (n : Option (Fin U.m × Fin U.m × Bool) → ℕ),
      H.ρ (∏ t ∈ s, b t ^ n t) = H.ρ (∏ t ∈ s, b t ^ (n t % m t)) := by
    intro s n
    refine Finset.induction_on s (by simp) ?_
    intro a s ha ih
    rw [Finset.prod_insert ha, Finset.prod_insert ha, map_mul, map_mul, ih, map_pow, map_pow,
      ← pow_eq_pow_mod _ (hbm a)]
  have hmul : ∀ γ γ' : G, H.ρ (β (γ * γ')) = H.ρ (β γ) * H.ρ (β γ') := by
    intro γ γ'
    have e1 : β (γ * γ') = ∏ t, b t ^ (((Multiplicative.toAdd (γ t)).val +
        (Multiplicative.toAdd (γ' t)).val) % m t) := by
      refine Finset.prod_congr rfl fun t _ => ?_
      rw [Pi.mul_apply, toAdd_mul, ZMod.val_add]
    have k2 := key Finset.univ
      (fun t => (Multiplicative.toAdd (γ t)).val + (Multiplicative.toAdd (γ' t)).val)
    beta_reduce at k2
    rw [e1, ← k2, ← map_mul]
    congr 1
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun t _ => pow_add _ _ _
  have h1 : H.ρ (β 1) = 1 := by
    have hb1 : β 1 = 1 := by
      refine (Finset.prod_congr rfl fun t _ => ?_).trans Finset.prod_const_one
      show b t ^ (Multiplicative.toAdd ((1 : G) t)).val = 1
      rw [Pi.one_apply, toAdd_one, ZMod.val_zero, pow_zero]
    rw [hb1, map_one]
  have hcard : IsUnit (Fintype.card G : R) := by
    rw [Fintype.card_pi, Nat.cast_prod]
    refine Finset.prod_induction _ IsUnit (fun x y hx hy => hx.mul hy) isUnit_one fun t _ => ?_
    have hc : Fintype.card (Multiplicative (ZMod (m t))) = m t := by simp
    rw [hc]
    exact hunit _ (hmp t)
  let gen : Option (Fin U.m × Fin U.m × Bool) → G := fun t =>
    Pi.mulSingle (M := fun t => Multiplicative (ZMod (m t))) t (Multiplicative.ofAdd (1 : ZMod (m t)))
  have hgen : ∀ t, β (gen t) = b t := by
    intro t
    show ∏ u, b u ^ (Multiplicative.toAdd
      (Pi.mulSingle (M := fun t => Multiplicative (ZMod (m t))) t (Multiplicative.ofAdd (1 : ZMod (m t))) u)).val
      = b t
    rw [Finset.prod_eq_single t]
    · rw [Pi.mulSingle_eq_same, toAdd_ofAdd, hone, pow_one]
    · intro u _ hu
      rw [Pi.mulSingle_eq_of_ne hu, toAdd_one, ZMod.val_zero, pow_zero]
    · intro h
      exact absurd (Finset.mem_univ t) h
  have hsep' : ∀ i k, U.εT i ≠ 0 → U.εT k ≠ 0 → i ≠ k →
      FrobeniusGroupField.res hv (U.sg k (b (some (i, k, false)))) ≠ FrobeniusGroupField.res hv (U.sg i (b (some (i, k, false)))) := by
    intro i k hi hk hik
    have hq := hQ (some (i, k, false)) hi hk (by simpa using hik)
    simpa using hq
  have hsepψ : ∀ j k, U.εT j ≠ 0 → U.εT k ≠ 0 → j ≠ k → ∃ γ : G, U.sg j (β γ) ≠ U.sg k (β γ) := by
    intro j k hj hk hjk
    refine ⟨gen (some (j, k, false)), ?_⟩
    rw [hgen]
    intro heq
    exact hsep' j k hj hk hjk (by rw [heq])
  refine ⟨G, inferInstance, inferInstance, β, hmul, h1, hcard, ?_, ?_, ?_⟩
  · intro i γ hi
    obtain ⟨j, hj, hψ⟩ := FrobeniusGroupField.proj p hv hpv hcard (fun γ => H.ρ (β γ)) hmul h1 U.εT U.εT_orth
      U.εT_sum (fun j γ => U.sg j (β γ)) (fun j γ => U.εT_eig (β γ) j)
      (fun j k hj hk hjk => hsepψ j k hj hk hjk) i hi
    have hjφ : j = U.φ i := by
      by_contra hne
      have hq := hQ (some (i, j, true)) hi hj (by simpa using hne)
      simp only [Bool.toNat_true, pow_one] at hq
      have h2 := hψ (gen (some (i, j, true)))
      simp only [hgen] at h2
      exact hq (by rw [h2, map_pow])
    rw [← hjφ]
    exact hψ γ
  · intro i k hi hk hik
    refine ⟨gen (some (i, k, false)), ?_⟩
    rw [hgen]
    apply (FrobeniusGroupField.res_ne_zero hv _).1
    rw [map_sub, sub_ne_zero]
    exact (hsep' i k hi hk hik).symm
  · intro i hi
    exact ⟨gen none, by rw [hgen]; exact hQ none i hi⟩

end ReciprocityTheory.PGsh.Up
end
end
end

-- Source module: ReciprocityTheory.DualLattices.FrobeniusOfGroupDivisorsRank

section

@[expose] public section

namespace ReciprocityTheory.PGsh.Up

theorem frobenius_of_length_lifts (hLen : LenIdStatement) (hEx : LenExStatement) (hTot : EigenLengthProductStatement)
    (hG : EmbeddingSeparatingGroupStatement) (hE : EigenElementaryDivisorStatement) (hR : EigenRankStatement)
    (hB : EigenLiftsBasisStatement) (hF : EigenLiftsFrobeniusStatement) : UnramifiedCokernelLengthStatement :=
  unramifiedCokernelLength_of_length_eigenLengthProduct hLen hEx hTot (core_of (lifts_of hG hE hR) hB hF)

theorem unramifiedCokernelLength_of_eigen_elementaryDivisor_rank_lifts (hG : EmbeddingSeparatingGroupStatement) (hE : EigenElementaryDivisorStatement)
    (hR : EigenRankStatement) (hB : EigenLiftsBasisStatement) (hF : EigenLiftsFrobeniusStatement) : UnramifiedCokernelLengthStatement :=
  frobenius_of_length_lifts lenId lenEx eigenLengthProductStatement_holds hG hE hR hB hF

theorem frobenius_of_group_divisors_rank (hG : EmbeddingSeparatingGroupStatement) (hE : EigenElementaryDivisorStatement) (hR : EigenRankStatement)
    (hF1 : LiftMonomialDeterminantStatement) (hF2 : FrobeniusBlockStatement) (hF3 : FrobeniusLengthBoundStatement) : UnramifiedCokernelLengthStatement :=
  unramifiedCokernelLength_of_eigen_elementaryDivisor_rank_lifts hG hE hR monomials_span_of_prod_eq (frob_of hF1 hF2 hF3)

theorem unramifiedCokernelLength_of_monomialDeterminant_frobeniusBlock_lengthBound (hG : EmbeddingSeparatingGroupStatement) (hF1 : LiftMonomialDeterminantStatement) (hF2 : FrobeniusBlockStatement)
    (hF3 : FrobeniusLengthBoundStatement) : UnramifiedCokernelLengthStatement :=
  frobenius_of_group_divisors_rank hG elementary_divisor_statement rank_eq_rank_of_perm_and_zero hF1 hF2 hF3

theorem unramifiedCokernelLength_of_frobeniusLengthBound (hG : EmbeddingSeparatingGroupStatement) (hF3 : FrobeniusLengthBoundStatement) : UnramifiedCokernelLengthStatement :=
  unramifiedCokernelLength_of_monomialDeterminant_frobeniusBlock_lengthBound hG liftMonomialDeterminantStatement_holds frobeniusBlock hF3

theorem frobenius_of_group (hG : EmbeddingSeparatingGroupStatement) : UnramifiedCokernelLengthStatement :=
  unramifiedCokernelLength_of_frobeniusLengthBound hG u7F3

theorem u7 : UnramifiedCokernelLengthStatement :=
  frobenius_of_group embeddingSeparatingGroup

end ReciprocityTheory.PGsh.Up
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LinearDataUnramifiedLengthBound

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private theorem ofNat_succ_fin (n : ℕ) [NeZero n] (k : ℕ) :
    Fin.ofNat n (k + 1) = Fin.ofNat n k + 1 := by
  ext
  simp [Fin.add_def, Fin.ofNat]

private theorem exp_bound (p : ℕ) [Fact p.Prime] (h : ℕ) (a b c : ℕ → ℕ) (D : ℕ)
    (hab : ∀ n, a n + b n = h) (hbc : ∀ n, b n ≤ c n) (hD : ∀ n, c n ≤ D) :
    (h : ℝ) / (p - 1) - ∑' n : ℕ, (p : ℝ) ^ (-((n : ℝ) + 1)) * (a n : ℝ) ≤
      ∑' n : ℕ, (p : ℝ) ^ (-((n : ℝ) + 1)) * (c n : ℝ) := by
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg _
  have sa := summable_geom_p (p := p) (fun n => (a n : ℝ)) (fun _ => Nat.cast_nonneg _) h
    (fun n => by exact_mod_cast (hab n ▸ Nat.le_add_right _ _ : a n ≤ h))
  have sc := summable_geom_p (p := p) (fun n => (c n : ℝ)) (fun _ => Nat.cast_nonneg _) D
    (fun n => by exact_mod_cast hD n)
  have sh := summable_geom_p (p := p) (fun _ => (h : ℝ)) (fun _ => Nat.cast_nonneg _) h
    (fun _ => le_rfl)
  have e : (h : ℝ) / (p - 1) = ∑' n : ℕ, (p : ℝ) ^ (-((n : ℝ) + 1)) * (h : ℝ) := by
    rw [tsum_mul_right, tsum_geom_p]; ring
  rw [e, ← Summable.tsum_sub sh sa]
  refine Summable.tsum_le_tsum (fun n => ?_) (sh.sub sa) sc
  rw [← mul_sub]
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hp0 _)
  have h1 : (a n : ℝ) + b n = h := by exact_mod_cast hab n
  have h2 : (b n : ℝ) ≤ c n := by exact_mod_cast hbc n
  linarith

private theorem eigDim_le (C : Type) [Field C] {O OE : Type} [CommRing O] [Algebra O C] [CommRing OE]
    {d : ℕ} (ρ : OE → Matrix (Fin d) (Fin d) O) (τ : OE →+* C) : eigDim C ρ τ ≤ d := by
  unfold eigDim
  simpa using Submodule.finrank_le (⨅ a : OE, Module.End.eigenspace
    (Matrix.toLin' ((ρ a).map (algebraMap O C))) (τ a))

theorem linDat_unram_bound : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] [StarRing OE] (cp : O), HodgeTateSetting p v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp → ∀ (g : ℕ) (H : HodgeTateDatum p g v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) (d r m : ℕ) (A : Matrix (Fin d) (Fin r) O) (B : Matrix (Fin g) (Fin d) O) (ρG : OE →+* Matrix (Fin d) (Fin d) O) (N : OE →+* Matrix (Fin r) (Fin r) ℤ) (s : Fin m → Fin d → O), LinDat H A B ρG N s → ∀ [IsLocalRing O], p ≠ 2 → ¬ ((p : ℤ) ∣ Algebra.discr ℤ (Module.Free.chooseBasis ℤ OE)) → ∀ (w : PlaceU p OE) [NeZero w.n] (t : Fin w.n ≃ Emb (O := O) w.e), (∀ (j : Fin w.n) (a : OE), ((t (j + 1) : Emb (O := O) w.e) : OE →+* O) a - (((t j : Emb (O := O) w.e) : OE →+* O) a) ^ p ∈ IsLocalRing.maximalIdeal O) → ∀ (rk : (OE →+* O) → ℕ) (W : ∀ τ : OE →+* O, Fin (rk τ) → Fin d → O), (∀ τ, EigB ρG τ (W τ)) → ∀ j : Fin w.n, ∃ xs : NNReal, HasLen v O ((Fin (rk ((t j : Emb (O := O) w.e) : OE →+* O)) → O) ⧸ Submodule.span O (Set.range fun k => Pdiv.ChartF.res (W ((t j : Emb (O := O) w.e) : OE →+* O)) (s k))) xs ∧ v (algebraMap O C (p : O)) ^ (∑' n : ℕ, ((p : ℝ) ^ (-((n : ℝ) + 1))) * (rk (((t (j + Fin.ofNat w.n (n + 1)) : Emb (O := O) w.e) : OE →+* O).comp ((starRingAut : RingAut OE) : OE ≃+* OE).toRingHom) : ℝ)) ≤ xs := by
  intro p _ C _ _ _ v O _ _ hv _ _ _ OE _ _ _ _ _ _ cp hS g H d r m A B ρG N s hL _ hp2 hdisc w _ t ht
    rk W hW j
  obtain ⟨U, τ, ε, hsg, hr, -, -, hcj, hφ⟩ :=
    GlobalTheory.ChF.exists_unramData p C v O hv OE cp hS g H hL.noPad.1 hL.noPad.2 hdisc
  obtain ⟨hex, hmono, -⟩ := GlobalTheory.ChF.hasLen_exists_mono_fp C v O hv
  set ix : Fin w.n → Fin U.m := fun k => τ.symm ((t k : Emb (O := O) w.e) : OE →+* O) with hix
  have hτ : ∀ k, τ (ix k) = ((t k : Emb (O := O) w.e) : OE →+* O) := fun k => τ.apply_symm_apply _
  have hφ1 : ∀ k, U.φ (ix k) = ix (k + 1) := fun k => hφ _ _ (fun a => by rw [hτ, hτ]; exact ht k a)
  have hφn : ∀ n : ℕ, (U.φ ^ n) (ix j) = ix (j + Fin.ofNat w.n n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', Equiv.Perm.mul_apply, ih, hφ1, ofNat_succ_fin, add_assoc]

  obtain ⟨-, -, α, b, -⟩ := GlobalTheory.PlaceMono.place_monogenic p OE w
  obtain ⟨h, y, hy1, hy2⟩ := GlobalTheory.LocalFactorFree.exists_free_generators p OE w b (Ix g) H.ρ
  have hh : ∀ k, U.r (ix k) + U.r (U.cj (ix k)) = h := by
    intro k
    have e1 := GlobalTheory.ChF.eigDim_eq_of_basis p C v O hv OE w b (Ix g) H.ρ h y hy1 hy2 _ (t k).2
    have e2 := GlobalTheory.ChF.eigDim_tate p C v O hv OE cp hS g H
      ((algebraMap O C).comp ((t k : Emb (O := O) w.e) : OE →+* O))
    rw [hr, hr, hcj, hτ, ← e1, e2, RingHom.comp_assoc]

  have hrk : ∀ σ : OE →+* O, eigDim C ρG ((algebraMap O C).comp σ) = rk σ := fun σ =>
    (GlobalTheory.ChF.eigB_res_surjective C v O hv OE d (rk σ) ρG σ (W σ) (hW σ)).2.2
  have hle : ∀ i, U.r i ≤ rk (τ i) := by
    intro i
    have e := (GlobalTheory.EigAdd.eigDim_add_transpose C O OE d r g A B hL.exact ρG
      ((Int.castRingHom O).mapMatrix.comp N)
      (H.ρL.comp (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℤ_[p]) (B := OE)).toRingHom)
      hL.eqB hL.eqA ((algebraMap O C).comp (τ i))).1
    rw [hr, ← hrk, e]
    exact Nat.le_add_left _ _
  have hD : ∀ σ, rk σ ≤ d := fun σ => hrk σ ▸ eigDim_le C _ _

  obtain ⟨V1, hV1⟩ := lenEx C v O hv g H.Ht (U.εL (ix j)) (U.εT (U.cj (ix j)))
  obtain ⟨f, hf⟩ := GlobalTheory.ChF.cokE_surj_res_quot p C v O hv OE cp hS g H d r m A B ρG N s hL U (ix j)
    ((t j : Emb (O := O) w.e) : OE →+* O) (fun x => by rw [hsg, hτ]) _ _ (hW _)
  obtain ⟨xs, hxs⟩ := hex ((Fin (rk ((t j : Emb (O := O) w.e) : OE →+* O)) → O) ⧸ Submodule.span O
      (Set.range fun k => Pdiv.ChartF.res (W ((t j : Emb (O := O) w.e) : OE →+* O)) (s k)))
    (Module.finitePresentation_of_surjective (Submodule.mkQ _) (Submodule.mkQ_surjective _)
      (by rw [Submodule.ker_mkQ]; exact Submodule.fg_span (Set.finite_range _)))
  refine ⟨xs, hxs, ?_⟩
  have h1 := hmono _ _ f V1 xs hf hV1 hxs
  have h2 := up_full u7 p g C v O _ _ cp hp2 hS H U (ix j) _ (LinearEquiv.refl _ _) V1 hV1
  refine le_trans ?_ h1
  rw [← NNReal.coe_le_coe, NNReal.coe_rpow]
  refine le_trans ?_ h2
  refine Real.rpow_le_rpow_of_exponent_ge ?_ ?_ ?_
  · exact_mod_cast pos_iff_ne_zero.2 hS.p_ne
  · exact_mod_cast hS.p_lt.le
  · have e : ((U.r (ix j) : ℝ) + U.r (U.cj (ix j))) = h := by exact_mod_cast hh j
    rw [e]
    unfold frobSum
    refine exp_bound p h (fun n => U.r ((U.φ ^ (n + 1)) (ix j)))
      (fun n => U.r (U.cj (ix (j + Fin.ofNat w.n (n + 1))))) _ d (fun n => ?_) (fun n => ?_)
      (fun n => hD _)
    · rw [hφn]; exact hh _
    · have := hle (U.cj (ix (j + Fin.ofNat w.n (n + 1))))
      rwa [hcj, hτ] at this

end GlobalTheory.ChF
end
end
