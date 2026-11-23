module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.TwSingle
public import Mathlib.NumberTheory.MulChar.Basic
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
public import Mathlib.NumberTheory.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.TwSingle
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Coprime.Basic
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.RingTheory.Nilpotent.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.EvenTot
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.GcNeg
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.GcShift
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.CategoryTheory.Category.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.SepPair
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.SinLem
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.SinMap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.SinSupp
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.TwCoef
import Mathlib.Algebra.Order.Star.Int
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.CharPer

section

@[expose] public section

open UpperTheory.V.FW

theorem UpperTheory.V.FW.charPer :
    ∀ (l : ℕ) [Fact l.Prime] (f n : ℕ) [NeZero (f * l ^ n)] (k : Type) [Field k] [CharP k l] (χ : (ZMod (f * l ^ n))ˣ →* kˣ) (s : ZMod (f * l ^ n)), f.Coprime l → 1 ≤ n → MulChar.ofUnitHom χ (s + ((f * l : ℕ) : ZMod (f * l ^ n))) = MulChar.ofUnitHom χ s := by
  intro l hl f n _ k _ _ χ s hf hn
  set M : ZMod (f * l ^ n) := ((f * l : ℕ) : ZMod (f * l ^ n)) with hM
  have hnil : IsNilpotent M := by
    refine ⟨n, ?_⟩
    rw [hM, ← Nat.cast_pow, CharP.cast_eq_zero_iff (ZMod (f * l ^ n)) (f * l ^ n), mul_pow]
    exact Nat.mul_dvd_mul_right (dvd_pow_self f (by omega)) _
  by_cases hs : IsUnit s
  swap
  · have hs' : ¬ IsUnit (s + M) := by
      intro h
      apply hs
      simpa using hnil.neg.isUnit_add_right_of_commute h (Commute.all _ _)
    rw [MulChar.map_nonunit _ hs, MulChar.map_nonunit _ hs']
  obtain ⟨u, rfl⟩ := hs
  set t : ℤ := ((((u⁻¹ : (ZMod (f * l ^ n))ˣ) : ZMod (f * l ^ n)).val : ℕ) : ℤ) with ht
  set w : ZMod (f * l ^ n) := 1 + M * ((u⁻¹ : (ZMod (f * l ^ n))ˣ) : ZMod (f * l ^ n)) with hw
  have hsplit : (u : ZMod (f * l ^ n)) + M = u * w := by
    rw [hw, mul_add, mul_one, mul_left_comm, Units.mul_inv, mul_one]
  have hwint : w = ((1 + (f : ℤ) * l * t : ℤ) : ZMod (f * l ^ n)) := by
    rw [hw, hM, ht]
    push_cast
    rw [ZMod.natCast_zmod_val]
  have hdvd : ((f * l ^ n : ℕ) : ℤ) ∣ (1 + (f : ℤ) * l * t) ^ (l ^ (n - 1)) - 1 := by
    have h1 : ((l : ℕ) : ℤ) ^ (n - 1 + 1) ∣ (1 + (f : ℤ) * l * t) ^ (l ^ (n - 1)) - 1 ^ (l ^ (n - 1)) :=
      dvd_sub_pow_of_dvd_sub (by simp only [add_sub_cancel_left]; exact ⟨f * t, by ring⟩) _
    rw [Nat.sub_add_cancel hn, one_pow] at h1
    have h2 : (f : ℤ) ∣ (1 + (f : ℤ) * l * t) ^ (l ^ (n - 1)) - 1 := by
      have := sub_dvd_pow_sub_pow (1 + (f : ℤ) * l * t) 1 (l ^ (n - 1))
      rw [one_pow] at this
      exact dvd_trans ⟨l * t, by ring⟩ this
    have hcop : IsCoprime (f : ℤ) ((l : ℤ) ^ n) := by
      have := Nat.isCoprime_iff_coprime.mpr (Nat.Coprime.pow_right n hf)
      simpa using this
    push_cast
    exact hcop.mul_dvd h2 h1
  have hwpow : w ^ (l ^ (n - 1)) = 1 := by
    have h0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hdvd
    rw [hwint]
    push_cast at h0 ⊢
    linear_combination h0
  have hcw : MulChar.ofUnitHom χ w = 1 := by
    have hp : (MulChar.ofUnitHom χ w) ^ (l ^ (n - 1)) = 1 := by
      rw [← map_pow, hwpow, map_one]
    have : (MulChar.ofUnitHom χ w - 1) ^ (l ^ (n - 1)) = 0 := by
      rw [sub_pow_char_pow, hp, one_pow, sub_self]
    exact sub_eq_zero.mp ((pow_eq_zero_iff (pow_ne_zero _ hl.out.ne_zero)).mp this)
  rw [hsplit, map_mul, hcw, mul_one]
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.PushDiff

section

@[expose] public section

open UpperTheory.V.FW

theorem UpperTheory.V.FW.pushDiff :
    ∀ (k : Type) [CommRing k] (M m : ℕ) [NeZero M] (h : m ∣ M) (N : ℕ) (P : ℕ → k) (g : ZMod M → k), (∀ s, g s - g (s - N) = ∑ j ∈ Finset.range N, if (j : ZMod M) = s then P j else 0) → ∀ y : ZMod m, push h g y - push h g (y - N) = ∑ j ∈ Finset.range N, if (j : ZMod m) = y then P j else 0 := by
  intro k _ M m _ h N P g hg y
  simp only [push]
  have shift : (∑ s ∈ Finset.univ.filter (fun s : ZMod M => ZMod.castHom h (ZMod m) s = y - N), g s)
      = ∑ s ∈ Finset.univ.filter (fun s : ZMod M => ZMod.castHom h (ZMod m) s = y), g (s - N) := by
    apply Finset.sum_nbij' (fun s : ZMod M => s + (N : ZMod M)) (fun s : ZMod M => s - (N : ZMod M))
    · intro s hs
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
      rw [map_add (f := _), hs, map_natCast]
      ring
    · intro s hs
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
      rw [map_sub, hs, map_natCast]
    · intro s _
      ring
    · intro s _
      ring
    · intro s _
      congr 1
      ring
  rw [shift, ← Finset.sum_sub_distrib]
  simp_rw [hg]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_ite_eq]
  have key : (j : ZMod M) ∈ Finset.univ.filter
      (fun s : ZMod M => ZMod.castHom h (ZMod m) s = y) ↔ (j : ZMod m) = y := by
    rw [Finset.mem_filter, ZMod.castHom_apply, ZMod.cast_natCast h]
    simp
  by_cases hj : (j : ZMod m) = y
  · rw [if_pos (key.mpr hj), if_pos hj]
  · rw [if_neg (fun t => hj (key.mp t)), if_neg hj]
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.SinFin

section

@[expose] public section

open UpperTheory.V.FW

theorem UpperTheory.V.FW.sinFin :
    ∀ (k ι : Type) [CommRing k] [Fintype ι] [DecidableEq ι] (m : ℕ) [NeZero m] (η : ι → (ZMod m)ˣ) (N : ℕ) (P : ℕ → k) (α : ZMod m → k), (∀ y, α y - α (y - N) = ∑ s ∈ Finset.range N, if (s : ZMod m) = y then P s else 0) → (∀ y, ∑ i, α (((η i)⁻¹ : (ZMod m)ˣ) * y) = 0) → sinE (fun i => (η i : ZMod m)) N P = 0 := by
  intro k ι _ _ _ m _ η N P α hα hsum
  have hsingSum : ∀ (z : ZMod m) (t : Finset ℕ) (g : ℕ → k),
      AddMonoidAlgebra.single z (∑ s ∈ t, g s) = ∑ s ∈ t, AddMonoidAlgebra.single z (g s) :=
    fun z t g => map_sum (AddMonoidAlgebra.singleAddHom z) g t
  have hsingSumι : ∀ (z : ZMod m) (g : ι → k),
      AddMonoidAlgebra.single z (∑ i, g i) = ∑ i, AddMonoidAlgebra.single z (g i) :=
    fun z g => map_sum (AddMonoidAlgebra.singleAddHom z) g Finset.univ
  have hsingSub : ∀ (z : ZMod m) (a b : k),
      AddMonoidAlgebra.single z (a - b) = AddMonoidAlgebra.single z a - AddMonoidAlgebra.single z b :=
    fun z a b => map_sub (AddMonoidAlgebra.singleAddHom z) a b
  set A : ι → AddMonoidAlgebra k (ZMod m) :=
    fun i => ∑ y : ZMod m, AddMonoidAlgebra.single ((η i : ZMod m) * y) (α y) with hA
  have hS : ∀ i, (∑ s ∈ Finset.range N, AddMonoidAlgebra.single (s • (η i : ZMod m)) (P s)) =
      (1 - AddMonoidAlgebra.single (N • (η i : ZMod m)) 1) * A i := by
    intro i
    have hone : ∀ s : ℕ, ∑ y : ZMod m, AddMonoidAlgebra.single ((η i : ZMod m) * y)
        (if (s : ZMod m) = y then P s else 0) = AddMonoidAlgebra.single (s • (η i : ZMod m)) (P s) := by
      intro s
      rw [Finset.sum_eq_single (s : ZMod m)]
      · simp [nsmul_eq_mul, mul_comm]
      · intro b _ hb
        simp [Ne.symm hb]
      · simp
    have e1 : ∑ s ∈ Finset.range N, AddMonoidAlgebra.single (s • (η i : ZMod m)) (P s) =
        ∑ y : ZMod m, AddMonoidAlgebra.single ((η i : ZMod m) * y) (α y - α (y - N)) := by
      simp_rw [hα, hsingSum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun s _ => (hone s).symm
    have e2 : ∑ y : ZMod m, AddMonoidAlgebra.single ((η i : ZMod m) * y) (α (y - N)) =
        ∑ y : ZMod m, AddMonoidAlgebra.single ((η i : ZMod m) * (y + N)) (α y) := by
      rw [← Equiv.sum_comp (Equiv.addRight (N : ZMod m))]
      simp
    have e3 : AddMonoidAlgebra.single (N • (η i : ZMod m)) (1 : k) * A i =
        ∑ y : ZMod m, AddMonoidAlgebra.single ((η i : ZMod m) * (y + N)) (α y) := by
      rw [hA, Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [AddMonoidAlgebra.single_mul_single, one_mul, nsmul_eq_mul]
      congr 1
      ring
    rw [e1, sub_mul, one_mul, e3, ← e2, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun y _ => hsingSub _ _ _
  have hA0 : ∑ i, A i = 0 := by
    have hre : ∀ i, A i = ∑ z : ZMod m,
        AddMonoidAlgebra.single z (α (((η i)⁻¹ : (ZMod m)ˣ) * z)) := by
      intro i
      rw [hA, ← Equiv.sum_comp (Units.mulLeft (η i))]
      refine Finset.sum_congr rfl fun y _ => ?_
      simp
    simp_rw [hre]
    rw [Finset.sum_comm]
    simp_rw [← hsingSumι, hsum]
    simp
  unfold sinE
  dsimp only
  rw [Finset.sum_congr rfl (fun i _ => by
    rw [hS i, mul_assoc, mul_left_comm, Finset.mul_prod_erase Finset.univ
      (fun j => 1 - AddMonoidAlgebra.single (N • (η j : ZMod m)) (1 : k)) (Finset.mem_univ i)])]
  rw [← Finset.sum_mul, hA0, zero_mul]
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.Sinnott

section

@[expose] public section

open UpperTheory.V.FW

theorem UpperTheory.V.FW.sinnott :
    ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [Nonempty ι] (η : ι → ℤ_[l]ˣ) (N : ℕ), N ≠ 0 → (∀ i j, i ≠ j → ∀ a b : ℤ, (a : ℤ_[l]) * η i = (b : ℤ_[l]) * η j → a = 0) → ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ (k : Type) [CommRing k] (P : ℕ → k) (α : ZMod (l ^ n) → k), (∀ y, α y - α (y - N) = ∑ s ∈ Finset.range N, if (s : ZMod (l ^ n)) = y then P s else 0) → (∀ y, ∑ i, α (((redU l n (η i))⁻¹ : (ZMod (l ^ n))ˣ) * y) = 0) → ∀ s < N, P s = 0 := by
  intro l _ ι _ _ η N hN hind
  classical
  obtain ⟨S, hS⟩ := sinSupp ℤ_[l] ι (fun i => (η i : ℤ_[l])) N
  obtain ⟨n₀, hn₀⟩ := sep l S
  refine ⟨n₀, fun n hn k _ P α h1 h2 => ?_⟩
  have hl : l.Prime := Fact.out
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ hl.ne_zero⟩
  have h3 := sinFin k ι (l ^ n) (fun i => redU l n (η i)) N P α h1 h2
  have h4 := sinMap k ℤ_[l] (ZMod (l ^ n)) ι
    (PadicInt.toZModPow n : ℤ_[l] →+* ZMod (l ^ n)).toAddMonoidHom (fun i => (η i : ℤ_[l])) N P
  have h5 : AddMonoidAlgebra.mapDomainRingHom k
      (PadicInt.toZModPow n : ℤ_[l] →+* ZMod (l ^ n)).toAddMonoidHom
      (sinE (fun i => (η i : ℤ_[l])) N P) = 0 := h4.trans h3
  have h6 : Finsupp.mapDomain (PadicInt.toZModPow n : ℤ_[l] → ZMod (l ^ n))
      (sinE (fun i => (η i : ℤ_[l])) N P).coeff = 0 := by
    have := congrArg AddMonoidAlgebra.coeff h5
    simpa using this
  have h7 : (sinE (fun i => (η i : ℤ_[l])) N P).coeff = 0 := by
    apply Finsupp.mapDomain_injOn (S : Set ℤ_[l]) (hn₀ n hn)
    · intro a ha
      exact hS k P a (Finsupp.mem_support_iff.mp ha)
    · simp
    · simpa using h6
  refine sinLem k ℤ_[l] ι (fun i => (η i : ℤ_[l])) N P hN ?_ ?_ ?_
  · intro i m hm
    simp only [zsmul_eq_mul] at hm
    have := (Units.mul_left_eq_zero (η i)).mp hm
    exact_mod_cast this
  · intro i j hij a b hab
    simp only [zsmul_eq_mul] at hab
    exact hind i j hij a b hab
  · ext a
    simp [h7]
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.Nonvan

section

@[expose] public section

open UpperTheory.V.FW

theorem UpperTheory.V.FW.nonvan :
    ∀ (l : ℕ) [Fact l.Prime] (f c : ℕ), f.Coprime l → Odd c → 1 < c → c.Coprime (f * l) → ∃ n₀ : ℕ, 2 ≤ n₀ ∧ ∀ (n : ℕ) [NeZero (f * l ^ n)] (h : l ^ n₀ ∣ f * l ^ n), n₀ ≤ n → ∀ (k : Type) [Field k] [CharP k l] (χ : (ZMod (f * l ^ n))ˣ →* kˣ), χ (-1) = -1 → tw χ (piQ l n₀ h) (toK k _ (thetaH (f * l ^ n) c)) ≠ 0 := by
  intro l _ f c hf hc1 hc hcop
  obtain ⟨R, hRne, hRW, hRind, hRneg, hRcov, -, -⟩ := reps l
  have hl := (Fact.out : l.Prime)
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hl.one_lt.ne' (Nat.coprime_zero_left l |>.mp hf)
  have hN0 : c * (f * l) ≠ 0 :=
    Nat.mul_ne_zero (by omega) (Nat.mul_ne_zero hf0 hl.ne_zero)
  haveI : Nonempty R := hRne.to_subtype
  obtain ⟨n₁, hn₁⟩ := sinnott l R (fun r => (r : ℤ_[l]ˣ)) (c * (f * l)) hN0
    (fun i j hij a b hab => hRind i i.2 j j.2 (fun e => hij (Subtype.ext e)) a b hab)
  refine ⟨max n₁ 2, le_max_right _ _, ?_⟩
  intro n _ h hn k _ _ χ hχ htw
  have hcf := Nat.coprime_mul_iff_right.mp hcop
  have hcM : c.Coprime (f * l ^ n) :=
    Nat.coprime_mul_iff_right.mpr ⟨hcf.1, Nat.Coprime.pow_right n hcf.2⟩
  have hn1 : 1 ≤ n := le_trans (by omega) (le_trans (le_max_right n₁ 2) hn)
  have hn2 : 2 ≤ n := le_trans (le_max_right n₁ 2) hn
  haveI : Fact (1 < f * l ^ n) := ⟨by
    have h1 : 1 < l ^ n := Nat.one_lt_pow (by omega) hl.one_lt
    have h2 : 1 ≤ f := Nat.one_le_iff_ne_zero.mpr hf0
    calc 1 < l ^ n := h1
      _ ≤ f * l ^ n := Nat.le_mul_of_pos_left _ h2⟩
  have hodd : ∀ s : (ZMod (f * l ^ n))ˣ,
      gc (f * l ^ n) c (-(s : ZMod (f * l ^ n))) = -gc (f * l ^ n) c s :=
    fun s => gcNeg _ c _ hcM hc1 s.ne_zero
  have hsum := twCoef l (f * l ^ n) (max n₁ 2) h k χ (gc (f * l ^ n) c) R
    (le_max_right _ _) hχ hodd hRW hRneg hRcov htw
  set Ψ : ZMod (f * l ^ n) → k := ⇑(MulChar.ofUnitHom χ) with hΨ
  have hper : ∀ x : ZMod (f * l ^ n), Ψ (x + ↑(f * l)) = Ψ x :=
    fun x => charPer l f n k χ x hf hn1
  have hshift := fun s => gcShift (f * l ^ n) c (f * l) k Ψ s hcM hper
  have hpush := pushDiff k (f * l ^ n) (l ^ max n₁ 2) h (c * (f * l))
    (fun j => Ψ ↑j * (1 - if c ∣ j then (c : k) else 0))
    (fun s => ((gc (f * l ^ n) c s : ℤ) : k) * Ψ s) hshift
  have hP := hn₁ (max n₁ 2) (le_max_left _ _) k
    (fun j => Ψ ↑j * (1 - if c ∣ j then (c : k) else 0))
    (push h fun s => ((gc (f * l ^ n) c s : ℤ) : k) * Ψ s) hpush hsum 1
    (by
      have : 1 ≤ f * l := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hf0 hl.ne_zero)
      nlinarith)
  have hndvd : ¬ c ∣ 1 := by
    intro hd
    have := Nat.le_of_dvd one_pos hd
    omega
  simp only [hndvd, if_false, sub_zero, mul_one, Nat.cast_one, hΨ, map_one] at hP
  exact one_ne_zero hP
end
end
