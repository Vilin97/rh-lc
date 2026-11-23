module

public import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.SumSatUnit
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.GaloisGenerators.IsGalGen
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
import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.NewtonLow
public import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.AbsCount2
public import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.BcSumD
public import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.ClassChar2
public import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.CoverEx
import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.Decomp
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.Imports
public import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.LogAsym
public import Development.AbelianVarietyTheory.BlockTheory.AdelicCMFields.UnitaryHeckeCharacterIdele
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.GelfandKazhdanReal
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.JacquetShalikaBound
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.JacquetShalikaRigidity
import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.ConjugateAnalyticity.RankinSelbergUnitaryOfPole
import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.DeterminantCharacterSplit.NormExponentEquality
import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.DeterminantOneCharacters.DeterminantOneConditionHolds
import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.PrimeNonSummability.PrimeSumConvergesAndDiverges
import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.RigidityCriterion.JacquetShalikaRigidityOfBound
import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.SatakeTwists.SatakeTwistHolds
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Basify
public import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.UnitOfPow
public import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.OrderAsym
public import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.SubtypeIteSums.CommonOfLandauEuler
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.AnalyticSeries.AnalyticAtTsum
import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.DiagonalTermNorms.ConvergenceOfLandauEuler
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.JacquetShalikaRigidity

-- Source module: Development.WeilBound.RepresentationTheoryGL.TwistedFactors.GaloisGenerators.LocRoots

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep PositivityTheory.RgJS

namespace PositivityTheory.Rg.Tf.ChR

def PartA : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n : ℕ) (P : CG E n) (ι : Type) [Fintype ι] (m : ι → ℕ)
    (Ps : ∀ i, CG E (m i)), 1 ≤ n → (∀ i, 1 ≤ m i) → 2 ≤ Fintype.card ι → ¬ IsIso P Ps

end PositivityTheory.Rg.Tf.ChR
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.FibreCG

section

@[expose] public section

open UpperTheory.ConvolutionTheory.R

open GlobalTheory.CuspRep Formalism.L2.Host

theorem UpperTheory.ConvolutionTheory.R.fibreCG :
    ClassChar → Count → NormCharPow → FibreCG := by
  intro hC hN hP K M _ _ _ _ _ _ _ _ hl n π P hn hπ
  classical
  obtain ⟨η, hη⟩ := hC K M hl
  obtain ⟨hp1, hp2⟩ := hP K M hl η hη
  have key : ∀ π₁ : CG K n, UpperTheory.V.Published.WeakBC π₁.HasSat P.HasSat →
      ((Finset.range (Module.finrank K M)).filter fun j => π₁ = π.twist (η ^ j)).card = 1 := by
    intro π₁ h₁
    have := hN K M hl η hη n π π₁ Unit (fun _ => n) (fun _ => P) hn (fun _ => hn)
      (by rw [sumSat_unit]; exact hπ) (by rw [sumSat_unit]; exact h₁)
    convert this using 1
    simp
  refine ⟨fun χ hχ he => ?_, fun π₁ h₁ => ?_⟩
  · obtain ⟨j, hj0, hjl, rfl⟩ := hp1 χ hχ
    obtain ⟨a, ha⟩ := Finset.card_eq_one.1 (key π hπ)
    have h0 : 0 ∈ (Finset.range (Module.finrank K M)).filter fun j => π = π.twist (η ^ j) := by
      rw [Finset.mem_filter, Finset.mem_range, pow_zero, CG.twist_one]
      exact ⟨hl.pos, rfl⟩
    have h1 : j ∈ (Finset.range (Module.finrank K M)).filter fun j => π = π.twist (η ^ j) := by
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨hjl, he.symm⟩
    rw [ha, Finset.mem_singleton] at h0 h1
    omega
  · obtain ⟨a, ha⟩ := Finset.card_eq_one.1 (key π₁ h₁)
    have h1 : a ∈ (Finset.range (Module.finrank K M)).filter fun j => π₁ = π.twist (η ^ j) := by
      rw [ha]; exact Finset.mem_singleton_self a
    rw [Finset.mem_filter, Finset.mem_range] at h1
    refine ⟨η ^ a, ?_, h1.2.symm⟩
    rcases Nat.eq_zero_or_pos a with rfl | h
    · exact Or.inl (pow_zero _)
    · exact Or.inr (hp2 a h h1.1)
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.NormCharPow

section

@[expose] public section

open UpperTheory.ConvolutionTheory.R

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.L2.Host UpperTheory.V.Published

theorem UpperTheory.ConvolutionTheory.R.normCharPow :
    Count → NormCharPow := by
  classical
  intro hN K M _ _ _ _ _ _ _ _ hl η hη
  have hp : ∀ (n : ℕ) (v : HeightOneSpectrum (𝓞 K)), (η ^ n).val v = η.val v ^ n :=
    fun n v => MonoidHom.pow_apply η.1 n _
  refine ⟨fun χ hχ => ?_, fun j hj0 hjl => ⟨fun h => ?_, ?_, ?_⟩⟩
  · have hW : ∀ ψ : HChar K, (∀ᶠ w : HeightOneSpectrum (𝓞 M) in Filter.cofinite, ∀ f : ℕ,
        Formalism.ConjugateSelfDual.normV w = Formalism.ConjugateSelfDual.normV (w.under (𝓞 K)) ^ f → ψ.val (w.under (𝓞 K)) ^ f = 1) →
        WeakBC (CG.ofChar ψ).HasSat (sumSat (m := fun _ : Unit => 1) fun _ => CG.ofChar (1 : HChar M)) := by
      intro ψ h
      rw [sumSat_unit]
      filter_upwards [h, (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under K M).eventually
        (Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.finite_ramified ψ))] with w h1 h2 f hf
      refine ⟨_, CG.hasSat_ofChar h2, ?_⟩
      rw [Multiset.map_singleton, h1 f hf]
      exact CG.hasSat_ofChar (χ := 1) (w := w) fun _ _ => rfl
    have h1 := hN K M hl η hη 1 (CG.ofChar 1) (CG.ofChar χ) Unit (fun _ => 1) (fun _ => CG.ofChar 1) le_rfl
      (fun _ => le_rfl) (hW 1 (Filter.Eventually.of_forall fun w f _ => one_pow f)) (hW χ hχ.2.2)
    have h2 : 0 < ((Finset.range (Module.finrank K M)).filter
        fun j => CG.ofChar χ = (CG.ofChar 1).twist (η ^ j)).card := by
      rw [h1]
      exact Finset.card_pos.2 ⟨((), ()), by simp⟩
    obtain ⟨j, hj⟩ := Finset.card_pos.1 h2
    rw [Finset.mem_filter, Finset.mem_range, CG.twist_ofChar, one_mul] at hj
    have e := CG.ofChar_injective hj.2
    refine ⟨j, Nat.pos_of_ne_zero ?_, hj.1, e⟩
    rintro rfl
    exact hχ.1 (e.trans (pow_zero _))
  · haveI := Fact.mk hl
    have ho := orderOf_eq_prime hη.1.2.1 hη.1.1
    have := Nat.le_of_dvd hj0 (orderOf_dvd_of_pow_eq_one h)
    omega
  · rw [← pow_mul, mul_comm, pow_mul, hη.1.2.1, one_pow]
  · refine hη.1.2.2.mono fun w hw f hf => ?_
    rw [hp, ← pow_mul, mul_comm, pow_mul, hw f hf, one_pow]
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.SysEx

section

@[expose] public section

open UpperTheory.ConvolutionTheory.R

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep PositivityTheory.RgJS in
theorem UpperTheory.ConvolutionTheory.R.sysEx :
    SysEx := by
  intro E _ _ _ X hfin hX
  classical
  have hRSU : RSU := rankin_selberg_unitary_of_pole norm_exponent_equality satake_twist_holds PositivityTheory.AdelicQuotientData.rsPole
  have hBd : GlobalTheory.Published.JacquetShalikaBound := PositivityTheory.JacquetShalikaLocal.jacquetShalikaBound
  have hDO : DetOne := determinant_one_condition_holds
  have hPO : PrimeOff := prime_sum_converges_and_diverges
  have : Fintype X := hfin.fintype
  choose S0 hS0 using fun x y : X =>
    hRSU E x.1.1 y.1.1 x.1.2 y.1.2 (hX x x.2).1 (hX y y.2).1 (hX x x.2).2.1 (hX y y.2).2.1
  have hw : ∀ᶠ w in Filter.cofinite, ∀ x : X, ∃ B, x.1.2.HasSat w B :=
    Filter.eventually_all.2 fun x => (hX x x.2).2.2
  refine ⟨(Filter.eventually_cofinite.1 hw).toFinset ∪ Finset.univ.biUnion (fun p : X × X => S0 p.1 p.2), fun S hS => ?_⟩
  have hex : ∀ (x : X) (w : Off E S), ∃ f : Fin x.1.1 → ℂˣ, x.1.2.HasSat w.1 (Finset.univ.val.map f) := by
    intro x w
    have h : ∀ x : X, ∃ B, x.1.2.HasSat w.1 B := by
      by_contra h
      exact w.2 (hS (Finset.mem_union_left _ (by rw [Set.Finite.mem_toFinset]; exact h)))
    obtain ⟨B, hB⟩ := h x
    obtain ⟨f, hf⟩ := RigidityLemmas.exists_fin _ hB.card
    exact ⟨f, hf ▸ hB⟩
  choose α hα using hex
  have hsub : ∀ x y : X, S0 x y ⊆ S := fun x y z hz =>
    hS (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨(x, y), Finset.mem_univ _, hz⟩))
  refine ⟨α, hα, hPO E S, fun x => (hX x x.2).1, fun x w a => ?_, fun x w => ?_, fun x y => ?_⟩
  · have h := (hBd E x.1.1 x.1.2 (hX x x.2).2.1 w.1 _ (hα x w) (α x w a)
      (Multiset.mem_map_of_mem _ (Finset.mem_univ_val _))).2
    show ‖((α x w a : ℂˣ) : ℂ)‖ ≤ Real.sqrt ((Ideal.absNorm w.1.asIdeal : ℕ) : ℝ)
    rw [Real.sqrt_eq_rpow]
    exact h.le
  · have h := hDO E x.1.1 x.1.2 w.1 _ (hX x x.2).2.1 (hα x w)
    rw [← Finset.prod_eq_multiset_prod, Units.coe_prod] at h
    exact h
  · obtain ⟨F, σ₀, hF, hFe⟩ := hS0 x y S (hsub x y) (α x) (α y) (hα x) (hα y)
    refine ⟨F, σ₀, hF, fun σ hσ => ?_⟩
    rw [hFe σ hσ]
    by_cases hxy : x = y
    · subst hxy
      rw [if_pos rfl, if_pos rfl]
      rfl
    · rw [if_neg (fun h => hxy (Subtype.ext (by simpa using h))), if_neg hxy]
      rfl
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.TwoParts

section

@[expose] public section

open UpperTheory.ConvolutionTheory.R

theorem UpperTheory.ConvolutionTheory.R.twoParts :
    ClassChar → Count → NormCharPow → TwoParts := by
  classical
  intro hC hCount hN K M _ _ _ _ _ _ _ _ hp n π ι _ m P hn hm hι hW
  obtain ⟨η, hη⟩ := hC K M hp
  have h1 := hCount K M hp η hη n π π ι m P hn hm hW hW
  obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card (show 1 < Fintype.card ι from hι)
  have h2 : 1 < ((Finset.range (Module.finrank K M)).filter fun j => π = π.twist (η ^ j)).card := by
    rw [h1, Finset.one_lt_card]
    refine ⟨(a, a), by simp, (b, b), by simp, fun h => hab (congrArg Prod.fst h)⟩
  obtain ⟨j, hj, hj0⟩ := Finset.exists_mem_ne h2 0
  rw [Finset.mem_filter, Finset.mem_range] at hj
  exact ⟨η ^ j, (hN K M hp η hη).2 j (Nat.pos_of_ne_zero hj0) hj.1, hj.2.symm⟩
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.ZeroExp

section

@[expose] public section

open UpperTheory.ConvolutionTheory.R

open PositivityTheory.RgJS PositivityTheory.RgJS.Common0Aux in
theorem UpperTheory.ConvolutionTheory.R.zeroExp :
    ZeroExp := by
  classical
  intro W q X d A hS ι _ x hw hsm
  by_contra hne
  push Not at hne
  obtain ⟨i₁, hi₁⟩ := hne
  have hq := hS.primes.two
  have hC := UpperTheory.ConvolutionTheory.Rs.conv1 W q X d A hS
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_min_image Finset.univ (fun i => (x i).2) ⟨i₁, Finset.mem_univ _⟩
  set m : ℝ := (x i₀).2 with hm
  have ht : ∀ i, m ≤ (x i).2 := fun i => hi₀ i (Finset.mem_univ _)
  have hm0 : m < 0 := by
    by_contra h
    push Not at h
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
      mul_nonneg (Nat.cast_nonneg (d (x i).1)) (h.trans (ht i)))).1 hw i₁ (Finset.mem_univ _)
    rcases mul_eq_zero.1 h1 with h2 | h2
    · have := hS.pos (x i₁).1
      have h3 : d (x i₁).1 = 0 := by exact_mod_cast h2
      omega
    · exact hi₁ h2
  set α : W → (Σ i, Fin (d (x i).1)) → ℂ :=
    fun w a => A (x a.1).1 w a.2 * (q w : ℂ) ^ (-((x a.1).2 : ℂ)) with hα
  have hxx : ∀ (σ : ℝ) (p : W × ℕ),
      ∑ i, ∑ j, lterm q (A (x i).1) (A (x j).1) (((σ + (x i).2 + (x j).2 : ℝ)) : ℂ) p = lterm q α α σ p := fun σ p => by
    rw [sum_lterm q hq A x x σ p]
    simp only [lterm, Pw, hα, Fintype.sum_sigma]
  obtain ⟨τ, hτ, -, hτle⟩ := exists_pos_le (fun i => (x i).2 - m) (fun i => (x i).2 ≠ m)
    (fun i hi => sub_pos.2 (lt_of_le_of_ne (ht i) (Ne.symm hi)))
  choose M hM using fun i i' : ι => (hC (x i).1 (x i').1).2 (1 + τ) (by linarith)
  have : Nonempty {i // (x i).2 = m} := ⟨⟨i₀, rfl⟩⟩
  refine UpperTheory.ConvolutionTheory.Rs.unb W q X d A hS {i // (x i).2 = m} (fun i => (x i.1).1)
    ⟨(∑' p, ‖lterm q α α ((1 - 2 * m : ℝ) : ℂ) p‖) + ∑ i, ∑ i', |M i i'|, fun σ hσ1 hσ2 => ?_⟩
  have hs : ∀ i j, Summable fun p => lterm q (A (x i).1) (A (x j).1) (((σ - 2 * m + (x i).2 + (x j).2 : ℝ)) : ℂ) p :=
    fun i j => ((hC _ _).1 _ (by linarith [ht i, ht j])).of_norm
  have hform : ∑ i : {i // (x i).2 = m}, ∑ j : {i // (x i).2 = m}, ∑' p, lterm q (A (x i.1).1) (A (x j.1).1) (σ : ℂ) p =
      ∑ i : {i // (x i).2 = m}, ∑ j : {i // (x i).2 = m},
        ∑' p, lterm q (A (x i.1).1) (A (x j.1).1) (((σ - 2 * m + (x i.1).2 + (x j.1).2 : ℝ)) : ℂ) p := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [i.2, j.2, show σ - 2 * m + m + m = σ by ring]
  have htot : ∑ i, ∑ j, ∑' p, lterm q (A (x i).1) (A (x j).1) (((σ - 2 * m + (x i).2 + (x j).2 : ℝ)) : ℂ) p =
      ∑' p, lterm q α α ((σ - 2 * m : ℝ) : ℂ) p := by
    calc ∑ i, ∑ j, ∑' p, lterm q (A (x i).1) (A (x j).1) (((σ - 2 * m + (x i).2 + (x j).2 : ℝ)) : ℂ) p
        = ∑ i, ∑' p, ∑ j, lterm q (A (x i).1) (A (x j).1) (((σ - 2 * m + (x i).2 + (x j).2 : ℝ)) : ℂ) p :=
          Finset.sum_congr rfl fun i _ => (Summable.tsum_finsetSum fun j _ => hs i j).symm
      _ = ∑' p, ∑ i, ∑ j, lterm q (A (x i).1) (A (x j).1) (((σ - 2 * m + (x i).2 + (x j).2 : ℝ)) : ℂ) p :=
          (Summable.tsum_finsetSum fun i _ => summable_sum (s := Finset.univ) fun j _ => hs i j).symm
      _ = _ := tsum_congr fun p => hxx _ p
  rw [hform, dsum_subtype (fun i => (x i).2 = m)
    (fun i j => ∑' p, lterm q (A (x i).1) (A (x j).1) (((σ - 2 * m + (x i).2 + (x j).2 : ℝ)) : ℂ) p)]
  set f : ι → ι → ℂ :=
    fun i j => ∑' p, lterm q (A (x i).1) (A (x j).1) (((σ - 2 * m + (x i).2 + (x j).2 : ℝ)) : ℂ) p with hf
  have hsplit : ∑ i, ∑ j, f i j = (∑ i, ∑ j, if (x i).2 = m ∧ (x j).2 = m then f i j else 0) +
      ∑ i, ∑ j, if (x i).2 = m ∧ (x j).2 = m then 0 else f i j := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  have hrest : ‖∑ i, ∑ j, if (x i).2 = m ∧ (x j).2 = m then (0 : ℂ) else f i j‖ ≤ ∑ i, ∑ i', |M i i'| := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => (norm_sum_le _ _).trans
      (Finset.sum_le_sum fun j _ => ?_))
    split_ifs with hij
    · simp
    · have hge : 1 + τ ≤ σ - 2 * m + (x i).2 + (x j).2 := by
        rcases not_and_or.1 hij with h | h
        · linarith [hτle i h, ht j]
        · linarith [hτle j h, ht i]
      exact (hM i j _ hge).trans (le_abs_self _)
  have hDle : ‖∑' p, lterm q α α ((σ - 2 * m : ℝ) : ℂ) p‖ ≤ ∑' p, ‖lterm q α α ((1 - 2 * m : ℝ) : ℂ) p‖ :=
    tsum_of_norm_bounded (hsm (1 - 2 * m) (by linarith)).hasSum fun p =>
      DiagonalEntryNormBounds.norm_lterm_anti q hq α α (by linarith) p
  have heq : (∑ i, ∑ j, if (x i).2 = m ∧ (x j).2 = m then f i j else 0) =
      (∑' p, lterm q α α ((σ - 2 * m : ℝ) : ℂ) p) -
        ∑ i, ∑ j, if (x i).2 = m ∧ (x j).2 = m then 0 else f i j := by
    rw [← htot, hsplit]
    ring
  rw [heq]
  exact (norm_sub_le _ _).trans (add_le_add hDle hrest)
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.NormCharPowHolds

section

@[expose] public section

open PositivityTheory.Rg.Tf.ChR

namespace UpperTheory.ConvolutionTheory.R

theorem count_holds : Count := count (absCount2 bcSum_holds zeroExp logAsym) sysEx (coverEx decomp)

theorem normCharPow_holds : NormCharPow := normCharPow count_holds

theorem fibreCG_holds : FibreCG := fibreCG classChar2 count_holds normCharPow_holds

theorem fibre_holds : Fibre := fibre fibreCG_holds

theorem twoParts_holds : TwoParts := twoParts classChar2 count_holds normCharPow_holds

theorem partA_holds : PartA := by
  intro E _ _ _ n P ι _ m Ps hn hm hι h
  obtain ⟨s, -⟩ := PositivityTheory.AdelicQuotientData.jacquetShalikaRigidity E Unit ι (fun _ => n) m (fun _ => P) Ps (fun _ => hn) hm
    (h.mono fun w ⟨C, B, h1, h2, h3⟩ => ⟨fun _ => C, B, fun _ => h1, h2, by simp [h3]⟩)
  have := Fintype.card_congr s
  simp at this
  omega

end UpperTheory.ConvolutionTheory.R
end
end
