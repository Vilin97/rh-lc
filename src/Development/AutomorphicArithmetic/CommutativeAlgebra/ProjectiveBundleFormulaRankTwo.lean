module

public import Development.AutomorphicArithmetic.CupPullbacks.TwoChart
public import Development.AutomorphicArithmetic.CommutativeAlgebra.BijectiveCohomologyGmProductKummerCup
public import Development.AutomorphicArithmetic.CommutativeAlgebra.KummerCocycleMayerVietorisOfCover
public import Development.AutomorphicArithmetic.CommutativeAlgebra.ProjectiveBundleFormulaRankOneOfHomotopyInvarian
public import Development.AutomorphicArithmetic.CommutativeAlgebra.TateTwistAffineLineProjectionEquiv
public import Development.AutomorphicArithmetic.CupPullbacks.ConstCompSingle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupHypercohomologyPullbackStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCupProductGradedCommStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCupUnitAndPrimitiveRootClassesStatement
public import Development.AutomorphicArithmetic.CommutativeAlgebra.MayerVietorisConnectingCupPullback
public import Development.AutomorphicArithmetic.CommutativeAlgebra.MayerVietorisConnectingExistsUniqueAdditiveExact
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
import Mathlib.CategoryTheory.Limits.Types.Pushouts
import Mathlib.CategoryTheory.Presentable.Type

-- Source module: Development.AutomorphicArithmetic.CupPullbacks.TwoCore

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf

namespace UpperTheory.P2
variable {q : ℕ} [NeZero q]

theorem pull_cup {E E' : Spc} (f : E ⟶ E') {n m i j : ℤ} (a : Ht q E' n i) (b : Ht q E' m j) :
    pull _ f _ _ (cup q a b) = cup q (pull _ f _ _ a) (pull _ f _ _ b) :=
  GlobalTheory.T.cup_hypercohomologyPullback _ (twPair q i j) f rfl a b

theorem cast_smul {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (ε : ℤˣ) (x : Ht q E n i) :
    (ε • x).cast hn hi = ε • x.cast hn hi := by
  subst hn hi; rfl

theorem cast_cast {E : Spc} {n i n' i' n'' i'' : ℤ} (hn : n = n') (hi : i = i') (hn' : n' = n'') (hi' : i' = i'')
    (x : Ht q E n i) : (x.cast hn hi).cast hn' hi' = x.cast (hn.trans hn') (hi.trans hi') := by
  subst hn hi hn' hi'; rfl

theorem cast_self {E : Spc} {n i : ℤ} (hn : n = n) (hi : i = i) (x : Ht q E n i) : x.cast hn hi = x := rfl

theorem cast_neg {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht q E n i) :
    (-x).cast hn hi = -x.cast hn hi := by
  subst hn hi; rfl

theorem gc {E : Spc} {n m i j : ℤ} (a : Ht q E n i) (b : Ht q E m j) (hn : n + m = m + n) (hi : i + j = j + i) :
    (cup q a b).cast hn hi = (n * m).negOnePow • cup q b a := by
  rw [GlobalTheory.T.tateTwistCupProduct_graded_comm q E a b, cast_smul, cast_cast, cast_self]

theorem mvd_cast {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E) {n n' i i' : ℤ} (hn : n = n') (hi : i = i') (hn1 : n + 1 = n' + 1)
    {c : Ht q (pullback f g) n i} {x : Ht q E (n + 1) i} (h : IsMVd f g (tw q i) n c x) :
    IsMVd f g (tw q i') n' (c.cast hn hi) (x.cast hn1 hi) := by
  subst hn hi; exact h

theorem mvd_neg {R : Type} [CommRing R] {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E) (hc : Cover2 R f g) (F : Shv R) (n : ℤ)
    {c : H R (pullback f g) F n} {x : H R E F (n + 1)} (h : IsMVd f g F n c x) : IsMVd f g F n (-c) (-x) := by
  have M := ((UpperTheory.mayerVietorisConnecting_exists_unique_additive_exact R F n).1 f g hc)
  obtain ⟨y, hy⟩ := M.1 (-c)
  have h0 := M.2.2.1 _ _ _ _ h hy
  rw [add_neg_cancel] at h0
  have h1 : x + y = 0 := (M.2.2.2.1 _ _ h0).2 ⟨0, 0, by simp⟩
  rwa [eq_neg_of_add_eq_zero_right h1] at hy

section Core
variable {E X W₁ W₂ : Spc} (π : X ⟶ E) (f₁ : W₁ ⟶ X) (f₂ : W₂ ⟶ X)

theorem bd (hc : Cover2 (ZMod q) f₁ f₂) (ξ : Ht q X (1 + 1) 1) (κ : Ht q (pullback f₁ f₂) 1 1)
    (hd : IsMVd f₁ f₂ (tw q 1) 1 κ ξ ∨ IsMVd f₁ f₂ (tw q 1) 1 κ (-ξ)) {m j : ℤ} (b : Ht q E m j) :
    IsMVd f₁ f₂ (tw q (j + 1)) (m + 1) (cup q (pull _ (pullback.fst f₁ f₂ ≫ f₁ ≫ π) _ _ b) κ)
        ((cup q (pull _ π _ _ b) ξ).cast (by ring) rfl) ∨
      IsMVd f₁ f₂ (tw q (j + 1)) (m + 1) (cup q (pull _ (pullback.fst f₁ f₂ ≫ f₁ ≫ π) _ _ b) κ)
        (-(cup q (pull _ π _ _ b) ξ).cast (by ring) rfl) := by
  have hB : pull _ (pullback.fst f₁ f₂ ≫ f₁) _ _ (pull _ π _ _ b) = pull _ (pullback.fst f₁ f₂ ≫ f₁ ≫ π) _ _ b := by
    rw [← pull_comp, Category.assoc]
  set B := pull _ (pullback.fst f₁ f₂ ≫ f₁ ≫ π) _ _ b
  set P := pull _ π _ _ b
  have key : ∀ x : Ht q X (1 + 1) 1, IsMVd f₁ f₂ (tw q 1) 1 κ x →
      IsMVd f₁ f₂ (tw q (j + 1)) (m + 1) ((1 * m).negOnePow • cup q B κ) ((cup q P x).cast (by ring) rfl) := by
    intro x hx
    have h := UpperTheory.mayerVietorisConnecting_cup_pullback q f₁ f₂ hc 1 m 1 j κ x P hx
    rw [hB] at h
    have h' := mvd_cast (q := q) f₁ f₂ (n := 1 + m) (n' := m + 1) (i := 1 + j) (i' := j + 1) (by ring) (by ring) (by ring) h
    rw [gc, cast_cast, ← cast_cast (hn := (by ring : 1 + 1 + m = m + (1 + 1))) (hi := (by ring : 1 + j = j + 1)), gc, show ((1 + 1) * m).negOnePow = 1 from ?_, one_smul] at h'
    · exact h'
    · exact Int.negOnePow_even _ ⟨m, by ring⟩
  have neg_both : ∀ {c : Ht q (pullback f₁ f₂) (m + 1) (j + 1)} {x : Ht q X (m + 1 + 1) (j + 1)},
      IsMVd f₁ f₂ (tw q (j + 1)) (m + 1) (-c) x → IsMVd f₁ f₂ (tw q (j + 1)) (m + 1) c (-x) := by
    intro c x h
    simpa using mvd_neg f₁ f₂ hc _ _ h
  set Y : Ht q X (m + 1 + 1) (j + 1) := (cup q P ξ).cast (by ring) rfl with hY
  have hY' : ((cup q P (-ξ)).cast (by ring) rfl : Ht q X (m + 1 + 1) (j + 1)) = -Y := by
    rw [map_neg, cast_neg]
  rcases Int.units_eq_one_or (1 * m).negOnePow with hs | hs <;> rcases hd with hd | hd
  · have := key _ hd; rw [hs, one_smul] at this; exact Or.inl this
  · have := key _ hd; rw [hs, one_smul, hY'] at this; exact Or.inr this
  · have := key _ hd; rw [hs, Units.neg_smul, one_smul] at this; exact Or.inr (neg_both this)
  · have := key _ hd; rw [hs, Units.neg_smul, one_smul, hY'] at this
    have h2 := neg_both this
    rw [neg_neg] at h2
    exact Or.inl h2

theorem cast_add' {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x y : Ht q E n i) :
    (x + y).cast hn hi = x.cast hn hi + y.cast hn hi := by
  subst hn hi; rfl

theorem cast_zero' {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') :
    (0 : Ht q E n i).cast hn hi = 0 := by
  subst hn hi; rfl

theorem pull_cast {E E' : Spc} (f : E ⟶ E') {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht q E' n i) :
    pull _ f _ _ (x.cast hn hi) = Ht.cast hn hi (pull _ f _ _ x) := by
  subst hn hi; rfl

theorem core' (hc : Cover2 (ZMod q) f₁ f₂) (ξ : Ht q X (1 + 1) 1) (κ : Ht q (pullback f₁ f₂) 1 1)
    (h₁ : ∀ i, Eqv _ (f₁ ≫ π) (tw q i)) (h₂ : ∀ i, Eqv _ (f₂ ≫ π) (tw q i))
    (hK : ∀ m j : ℤ, Function.Bijective fun p : Ht q E (m + 1) (j + 1) × Ht q E m j =>
      pull _ (pullback.fst f₁ f₂ ≫ f₁ ≫ π) _ _ p.1 + cup q (pull _ (pullback.fst f₁ f₂ ≫ f₁ ≫ π) _ _ p.2) κ)
    (hd : IsMVd f₁ f₂ (tw q 1) 1 κ ξ ∨ IsMVd f₁ f₂ (tw q 1) 1 κ (-ξ)) (m j : ℤ) (hm : m + (1 + 1) = m + 1 + 1) :
    Function.Bijective fun p : Ht q E (m + 1 + 1) (j + 1) × Ht q E m j =>
      pull _ π _ _ p.1 + (cup q (pull _ π _ _ p.2) ξ).cast hm rfl := by
  set r := pullback.fst f₁ f₂ ≫ f₁ ≫ π with hr
  have hr2 : pullback.snd f₁ f₂ ≫ f₂ ≫ π = r := by
    rw [hr, ← Category.assoc, ← Category.assoc, pullback.condition]
  have M1 := (UpperTheory.mayerVietorisConnecting_exists_unique_additive_exact (ZMod q) (tw q 1) 1).1 f₁ f₂ hc
  have M2 := (UpperTheory.mayerVietorisConnecting_exists_unique_additive_exact (ZMod q) (tw q (j + 1)) (m + 1)).1 f₁ f₂ hc
  have hξ : pull _ f₁ _ _ ξ = 0 ∧ pull _ f₂ _ _ ξ = 0 := by
    rcases hd with hd | hd
    · exact (M1.2.2.2.2.1 _).2 ⟨_, hd⟩
    · have := (M1.2.2.2.2.1 _).2 ⟨_, hd⟩
      simpa using this
  set C : Ht q E m j → Ht q X (m + 1 + 1) (j + 1) := fun b => (cup q (pull _ π _ _ b) ξ).cast hm rfl with hC
  have Cadd : ∀ b b', C (b + b') = C b + C b' := by
    intro b b'
    simp only [hC, map_add (f := _), AddMonoidHom.add_apply, cast_add']
  have Cneg : ∀ b, C (-b) = - C b := by
    intro b
    simp only [hC, map_neg, AddMonoidHom.neg_apply, cast_neg]
  have hres₁ : ∀ b, pull _ f₁ _ _ (C b) = 0 := by
    intro b; simp only [hC]; rw [pull_cast, pull_cup, hξ.1, map_zero, cast_zero']
  have hres₂ : ∀ b, pull _ f₂ _ _ (C b) = 0 := by
    intro b; simp only [hC]; rw [pull_cast, pull_cup, hξ.2, map_zero, cast_zero']
  have hinjr : Function.Injective (pull (ZMod q) r (tw q (j + 1)) (m + 1 + 1)) := by
    intro a a' h
    have := (hK (m + 1) j).1 (a₁ := (a, 0)) (a₂ := (a', 0)) (by simpa using h)
    exact congrArg Prod.fst this
  have pr₁ : ∀ {n i} (a : Ht q E n i), pull _ (pullback.fst f₁ f₂) _ _ (pull _ (f₁ ≫ π) _ _ a) = pull _ r _ _ a := by
    intro n i a; rw [← pull_comp]
  have pr₂ : ∀ {n i} (a : Ht q E n i), pull _ (pullback.snd f₁ f₂) _ _ (pull _ (f₂ ≫ π) _ _ a) = pull _ r _ _ a := by
    intro n i a; rw [← pull_comp, hr2]
  have bdC : ∀ b, IsMVd f₁ f₂ (tw q (j + 1)) (m + 1) (cup q (pull _ r _ _ b) κ) (C b) ∨
      IsMVd f₁ f₂ (tw q (j + 1)) (m + 1) (cup q (pull _ r _ _ b) κ) (-C b) := fun b => bd π f₁ f₂ hc ξ κ hd b
  constructor
  ·
    have ker : ∀ a b, pull _ π _ _ a + C b = 0 → a = 0 ∧ b = 0 := by
      intro a b h
      have h1 := congrArg (pull _ f₁ _ _) h
      rw [map_add (f := _), hres₁, add_zero, map_zero, ← pull_comp] at h1
      have ha : a = 0 := (injective_iff_map_eq_zero _).1 ((h₁ (j + 1) (m + 1 + 1)).1) a h1
      subst ha
      rw [map_zero, zero_add] at h
      refine ⟨rfl, ?_⟩
      have hz : ∃ α β, cup q (pull _ r _ _ b) κ = pull _ (pullback.fst f₁ f₂) _ _ α - pull _ (pullback.snd f₁ f₂) _ _ β := by
        rcases bdC b with hb | hb
        · exact (M2.2.2.2.1 _ _ hb).1 h
        · exact (M2.2.2.2.1 _ _ hb).1 (by rw [h, neg_zero])
      obtain ⟨α, β, hαβ⟩ := hz
      obtain ⟨α', rfl⟩ := (h₁ (j + 1) (m + 1)).2 α
      obtain ⟨β', rfl⟩ := (h₂ (j + 1) (m + 1)).2 β
      rw [pr₁, pr₂, ← map_sub] at hαβ
      have := (hK m j).1 (a₁ := (0, b)) (a₂ := (α' - β', 0)) (by simpa using hαβ)
      exact congrArg Prod.snd this
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    simp only at h
    have h0 : pull _ π _ _ (a - a') + C (b + -b') = 0 := by
      rw [map_sub, Cadd, Cneg]
      change pull _ π _ _ a + C b = pull _ π _ _ a' + C b' at h
      calc _ = (pull _ π _ _ a + C b) - (pull _ π _ _ a' + C b') := by abel
        _ = 0 := by rw [h, sub_self]
    obtain ⟨e1, e2⟩ := ker _ _ h0
    exact Prod.ext (sub_eq_zero.1 e1) (by simpa [← sub_eq_add_neg, sub_eq_zero] using e2)
  ·
    intro y
    obtain ⟨a₁, ha₁⟩ := (h₁ (j + 1) (m + 1 + 1)).2 (pull _ f₁ _ _ y)
    obtain ⟨a₂, ha₂⟩ := (h₂ (j + 1) (m + 1 + 1)).2 (pull _ f₂ _ _ y)
    have e : a₁ = a₂ := by
      apply hinjr
      rw [← pr₁, ← pr₂, ha₁, ha₂, ← pull_comp, ← pull_comp, pullback.condition]
    subst e
    have hz₁ : pull _ f₁ _ _ (y - pull _ π _ _ a₁) = 0 := by
      rw [map_sub, ← pull_comp, ha₁, sub_self]
    have hz₂ : pull _ f₂ _ _ (y - pull _ π _ _ a₁) = 0 := by
      rw [map_sub, ← pull_comp, ha₂, sub_self]
    obtain ⟨c, hcz⟩ := (M2.2.2.2.2.1 _).1 ⟨hz₁, hz₂⟩
    obtain ⟨⟨a', b⟩, hab⟩ := (hK m j).2 c
    simp only at hab
    obtain ⟨x₀, hx₀⟩ := M2.1 (pull _ r _ _ a')
    have hx0 : x₀ = 0 := (M2.2.2.2.1 _ _ hx₀).2 ⟨pull _ (f₁ ≫ π) _ _ a', 0, by rw [pr₁, map_zero, sub_zero]⟩
    subst hx0
    rcases bdC b with hb | hb
    · have h3 := M2.2.2.1 _ _ _ _ hx₀ hb
      rw [hab, zero_add] at h3
      have h4 := M2.2.1 _ _ _ hcz h3
      exact ⟨(a₁, b), by simp only; rw [show (cup q (pull _ π _ _ b) ξ).cast hm rfl = C b from rfl, ← h4]; abel⟩
    · have h3 := M2.2.2.1 _ _ _ _ hx₀ hb
      rw [hab, zero_add] at h3
      have h4 := M2.2.1 _ _ _ hcz h3
      exact ⟨(a₁, -b), by simp only; rw [show (cup q (pull _ π _ _ (-b)) ξ).cast hm rfl = C (-b) from rfl, Cneg, ← h4]; abel⟩

theorem core (hc : Cover2 (ZMod q) f₁ f₂) (ξ : Ht q X (1 + 1) 1) (κ : Ht q (pullback f₁ f₂) 1 1)
    (h₁ : ∀ i, Eqv _ (f₁ ≫ π) (tw q i)) (h₂ : ∀ i, Eqv _ (f₂ ≫ π) (tw q i))
    (hK : ∀ m j : ℤ, Function.Bijective fun p : Ht q E (m + 1) (j + 1) × Ht q E m j =>
      pull _ (pullback.fst f₁ f₂ ≫ f₁ ≫ π) _ _ p.1 + cup q (pull _ (pullback.fst f₁ f₂ ≫ f₁ ≫ π) _ _ p.2) κ)
    (hd : IsMVd f₁ f₂ (tw q 1) 1 κ ξ ∨ IsMVd f₁ f₂ (tw q 1) 1 κ (-ξ)) (m j : ℤ) :
    Function.Bijective fun p : Ht q E (m + (1 + 1)) (j + 1) × Ht q E m j =>
      pull _ π _ _ p.1 + cup q (pull _ π _ _ p.2) ξ := by
  have key : ∀ (D : ℤ) (hD : m + (1 + 1) = D), Function.Bijective (fun p : Ht q E D (j + 1) × Ht q E m j =>
      pull _ π _ _ p.1 + (cup q (pull _ π _ _ p.2) ξ).cast hD rfl) →
      Function.Bijective fun p : Ht q E (m + (1 + 1)) (j + 1) × Ht q E m j =>
      pull _ π _ _ p.1 + cup q (pull _ π _ _ p.2) ξ := by
    intro D hD h
    subst hD
    exact h
  exact key _ (by ring) (core' π f₁ f₂ hc ξ κ h₁ h₂ hK hd m j _)

theorem cup_cast_right {E : Spc} {n m i j m' j' : ℤ} (x : Ht q E n i) (y : Ht q E m j) (hm : m = m') (hj : j = j')
    (h1 : n + m = n + m') (h2 : i + j = i + j') : cup q x (y.cast hm hj) = (cup q x y).cast h1 h2 := by
  subst hm hj; rfl

theorem cup_cast_left {E : Spc} {n m i j n' i' : ℤ} (x : Ht q E n i) (y : Ht q E m j) (hn : n = n') (hi : i = i')
    (h1 : n + m = n' + m) (h2 : i + j = i' + j) : cup q (x.cast hn hi) y = (cup q x y).cast h1 h2 := by
  subst hn hi; rfl

theorem cup_one {E : Spc} (hE : Inv q E) {n i : ℤ} (x : Ht q E n i) (h1 : n + 0 = n) (h2 : i + 0 = i) :
    (cup q x (one q E)).cast h1 h2 = x := by
  have e := gc x (one q E) (by ring : n + 0 = 0 + n) (by ring : i + 0 = 0 + i)
  rw [show (n * 0).negOnePow = 1 by simp, one_smul, (GlobalTheory.T.tateTwistCup_unit_and_primitiveRoot_classes q).1 E hE x] at e
  have e2 := congrArg (Ht.cast (by ring : 0 + n = n) (by ring : 0 + i = i)) e
  rw [cast_cast, cast_cast] at e2
  exact e2

theorem cpow_one' {E : Spc} (hE : Inv q E) (ξ : Ht q E 2 1) (k : ℕ) (hk : k = 1) (hn : 2 = 2 * (k : ℤ)) (hi : 1 = (k : ℤ)) :
    cpow q ξ k = ξ.cast hn hi := by
  subst hk
  rw [cpow_succ, cpow_zero, cup_cast_left (h1 := by simp) (h2 := by simp), (GlobalTheory.T.tateTwistCup_unit_and_primitiveRoot_classes q).1 E hE ξ, cast_cast, cast_cast]

theorem term0 {E X : Spc} (hX : Inv q X) (π : X ⟶ E) (ξ : Ht q X 2 1) (k : ℕ) (hk : k = 0) {N I N' I' : ℤ}
    (a : Ht q E N I) (h1 : N + 2 * (k : ℤ) = N') (h2 : I + (k : ℤ) = I') (h3 : N = N') (h4 : I = I') :
    (cup q (pull _ π _ _ a) (cpow q ξ k)).cast h1 h2 = pull _ π _ _ (a.cast h3 h4) := by
  subst hk h3 h4
  rw [cpow_zero, cup_cast_right (h1 := by simp) (h2 := by simp), cast_cast]
  exact cup_one hX _ _ _

theorem term1 {E X : Spc} (hX : Inv q X) (π : X ⟶ E) (ξ : Ht q X 2 1) (k : ℕ) (hk : k = 1) {N I N' I' : ℤ}
    (a : Ht q E N I) (h1 : N + 2 * (k : ℤ) = N') (h2 : I + (k : ℤ) = I') (h3 : N + 2 = N') (h4 : I + 1 = I') :
    (cup q (pull _ π _ _ a) (cpow q ξ k)).cast h1 h2 = (cup q (pull _ π _ _ a) ξ).cast h3 h4 := by
  subst hk h3 h4
  rw [cpow_one' hX ξ 1 rfl (by simp) (by simp), cup_cast_right (h1 := by simp) (h2 := by simp), cast_cast]

theorem cast_inj {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') {x y : Ht q E n i}
    (h : x.cast hn hi = y.cast hn hi) : x = y := by
  subst hn hi; exact h

theorem cup_pull_cast {E X : Spc} (π : X ⟶ E) (ξ : Ht q X 2 1) {N I N₂ I₂ : ℤ} (a : Ht q E N I) (hN : N = N₂) (hI : I = I₂)
    (h1 : N + 2 = N₂ + 2) (h2 : I + 1 = I₂ + 1) :
    (cup q (pull _ π _ _ a) ξ).cast h1 h2 = cup q (pull _ π _ _ (a.cast hN hI)) ξ := by
  subst hN hI; rfl

theorem lh2 {E X : Spc} (hX : Inv q X) (π : X ⟶ E) (ξ : Ht q X 2 1)
    (h : ∀ m j : ℤ, Function.Bijective fun p : Ht q E (m + 2) (j + 1) × Ht q E m j =>
      pull _ π _ _ p.1 + cup q (pull _ π _ _ p.2) ξ) :
    LH q π (fun j : Fin 2 => 2 * (((j : ℕ) : ℤ))) (fun j : Fin 2 => ((j : ℕ) : ℤ)) (fun j => cpow q ξ j) := by
  intro n i
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by ring⟩
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by ring⟩
  have e0 : ∀ a : ∀ t : Fin 2, Ht q E (m + 2 - 2 * (((t : ℕ) : ℤ))) (j + 1 - (((t : ℕ) : ℤ))),
      ∑ t : Fin 2, ((cup q (pull _ π _ _ (a t)) (cpow q ξ t)).cast (by ring) (by ring) : Ht q X (m + 2) (j + 1)) =
      pull _ π _ _ ((a 0).cast (by simp) (by simp)) +
        cup q (pull _ π _ _ ((a 1).cast (by simp) (by simp))) ξ := by
    intro a
    rw [Fin.sum_univ_two, term0 hX π ξ ((0 : Fin 2) : ℕ) (by simp) (N' := m + 2) (I' := j + 1) (a 0) _ _ (by simp) (by simp),
      term1 hX π ξ ((1 : Fin 2) : ℕ) (by simp) (N' := m + 2) (I' := j + 1) (a 1) _ _ (by simp) (by simp)]
    congr 1
    exact cup_pull_cast π ξ _ _ _ _ _
  constructor
  · intro a a' e
    simp only at e
    rw [e0, e0] at e
    have := (h m j).1 (a₁ := (_, _)) (a₂ := (_, _)) e
    have t0 := cast_inj _ _ (congrArg Prod.fst this)
    have t1 := cast_inj _ _ (congrArg Prod.snd this)
    funext t
    fin_cases t
    · exact t0
    · exact t1
  · intro y
    obtain ⟨⟨a₀, b₀⟩, hy⟩ := (h m j).2 y
    simp only at hy
    refine ⟨fun t => match t with
      | ⟨0, _⟩ => a₀.cast (by simp) (by simp)
      | ⟨1, _⟩ => b₀.cast (by simp) (by simp), ?_⟩
    simp only
    rw [e0]
    rw [← hy]
    congr 1
    · change pull _ π _ _ (Ht.cast _ _ (Ht.cast _ _ a₀)) = _
      rw [cast_cast]
      rfl
    · change cup q (pull _ π _ _ (Ht.cast _ _ (Ht.cast _ _ b₀))) ξ = _
      rw [cast_cast]
      rfl

end Core
end UpperTheory.P2
end
end

-- Source module: Development.AutomorphicArithmetic.CommutativeAlgebra.ProjectiveBundleFormulaRankTwo

section

@[expose] public section

set_option synthInstance.maxHeartbeats 100000

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf

namespace UpperTheory.P2
variable {q : ℕ} [NeZero q]

private theorem inv_of_map {Y E : Spc} (f : Y ⟶ E) (hE : Inv q E) : Inv q Y :=
  fun U ⟨y⟩ => hE U ⟨y.map f⟩

private theorem eqv_iso {R : Type} [CommRing R] {A B : Spc} (f : A ⟶ B) [IsIso f] (F : Shv R) : Eqv R f F := by
  intro n
  constructor
  · intro a b h
    have := congrArg (pull R (inv f) F n) h
    rwa [← pull_comp, ← pull_comp, IsIso.inv_hom_id, pull_id, pull_id] at this
  · intro x
    refine ⟨pull R (inv f) F n x, ?_⟩
    rw [← pull_comp, IsIso.hom_inv_id, pull_id]

private theorem eqv_comp {R : Type} [CommRing R] {A B C : Spc} {f : A ⟶ B} {g : B ⟶ C} {F : Shv R} (hf : Eqv R f F) (hg : Eqv R g F) :
    Eqv R (f ≫ g) F := by
  intro n
  have := (hf n).comp (hg n)
  convert this using 1
  funext x
  exact pull_comp R f g F n x

private theorem cover_comp {R : Type} [CommRing R] {U V E E' : Spc} {f : U ⟶ E} {g : V ⟶ E} (h : E ⟶ E') [IsIso h]
    (hc : Cover2 R f g) : Cover2 R (f ≫ h) (g ≫ h) := by
  obtain ⟨m1, m2, he⟩ := hc
  refine ⟨mono_comp _ _, mono_comp _ _, fun n => ?_⟩
  have := he n
  have e : biprod.desc ((free R).map ((f ≫ h).app n)) ((free R).map ((g ≫ h).app n)) =
      biprod.desc ((free R).map (f.app n)) ((free R).map (g.app n)) ≫ (free R).map (h.app n) := by
    have e1 : (f ≫ h).app n = f.app n ≫ h.app n := rfl
    have e2 : (g ≫ h).app n = g.app n ≫ h.app n := rfl
    rw [e1, e2, Functor.map_comp, Functor.map_comp]
    exact biprod.hom_ext' _ _ (by simp) (by simp)
  rw [e]
  exact epi_comp _ _

private theorem eqv_fst {Y : Spc} (hY : Inv q Y) (i : ℤ) : Eqv _ (prod.fst : Y ⨯ Dv 1 ⟶ Y) (tw q i) := by
  have hP := tri_pullback Y 1
  have e : (prod.fst : Y ⨯ Dv 1 ⟶ Y) = hP.isoPullback.hom ≫ pullback.fst (triv Y 1) (PGL.pr 1) := by
    rw [IsPullback.isoPullback_hom_fst]
  rw [e]
  refine eqv_comp (eqv_iso _ _) ?_
  have hX : Inv q (pullback (triv Y 1) (PGL.pr 1)) := inv_of_map (pullback.fst _ _) hY
  set π := pullback.fst (triv Y 1) (PGL.pr 1)
  set ξ := c1 q (pullback.snd (triv Y 1) (PGL.pr 1) ≫ PGL.line 1)
  intro n
  have h : Function.Bijective _ := UpperTheory.projectiveBundleFormula_rank_one_of_homotopyInvariant q Y hY n i
  have h0 : ∀ j : Fin 1, n - 2 * (((j : ℕ) : ℤ)) = n := by
    intro j
    obtain rfl : j = 0 := Subsingleton.elim _ _
    simp
  have h1 : ∀ j : Fin 1, i - (((j : ℕ) : ℤ)) = i := by
    intro j
    obtain rfl : j = 0 := Subsingleton.elim _ _
    simp
  have ev : ∀ a : ∀ j : Fin 1, Ht q Y (n - 2 * (((j : ℕ) : ℤ))) (i - (((j : ℕ) : ℤ))),
      ∑ j : Fin 1, ((cup q (pull _ π _ _ (a j)) (cpow q ξ j)).cast (by ring) (by ring) : Ht q _ n i) =
        pull _ π _ _ ((a 0).cast (h0 0) (h1 0)) := by
    intro a
    rw [Fin.sum_univ_one]
    exact term0 hX π ξ _ (by simp) (a 0) _ _ _ _
  constructor
  · intro a b hab
    have := h.1 (a₁ := fun j => Ht.cast (h0 j).symm (h1 j).symm a) (a₂ := fun j => Ht.cast (h0 j).symm (h1 j).symm b) (by
      simp only
      rw [ev, ev, cast_cast, cast_cast]
      exact hab)
    exact cast_inj _ _ (congrFun this 0)
  · intro y
    obtain ⟨a, ha⟩ := h.2 y
    exact ⟨_, (ev a).symm.trans ha⟩

private theorem kun {E : Spc} (hE : Inv q E) (m j : ℤ) :
    Function.Bijective fun p : Ht q E (m + 1) (j + 1) × Ht q E m j =>
      pull _ (prod.snd : sch.obj (Gq q) ⨯ E ⟶ E) _ _ p.1 +
        cup q (pull _ (prod.snd : sch.obj (Gq q) ⨯ E ⟶ E) _ _ p.2) (pull _ (prod.fst : sch.obj (Gq q) ⨯ E ⟶ _) _ _ (kappa q)) := by
  have key : ∀ (n i m j : ℤ) (hm : n - 1 = m) (hj : i - 1 = j) (h : m + 1 = n) (h' : j + 1 = i),
      Function.Bijective fun p : Ht q E n i × Ht q E m j =>
        pull _ (prod.snd : sch.obj (Gq q) ⨯ E ⟶ E) _ _ p.1 +
          (cup q (pull _ (prod.snd : sch.obj (Gq q) ⨯ E ⟶ E) _ _ p.2)
            (pull _ (prod.fst : sch.obj (Gq q) ⨯ E ⟶ _) _ _ (kappa q))).cast h h' := by
    intro n i m j hm hj h h'
    subst hm hj
    exact UpperTheory.bijective_cohomology_gm_product_kummer_cup q E hE n i
  exact key (m + 1) (j + 1) m j (by ring) (by ring) rfl rfl

end UpperTheory.P2

open UpperTheory.P2 in
theorem UpperTheory.projectiveBundleFormula_rank_two :
    ∀ (q : ℕ) [NeZero q] (E : Spc), Inv q E → PBF q E 2 := by
  intro q _ E hE
  have hP := tri_pullback E 2
  set θ := hP.isoPullback with hθ
  set π := pullback.fst (triv E 2) (PGL.pr 2) with hπ
  set L := pullback.snd (triv E 2) (PGL.pr 2) ≫ PGL.line 2 with hL
  have hX : Inv q (pullback (triv E 2) (PGL.pr 2)) := inv_of_map π hE
  have hθπ : θ.hom ≫ π = prod.fst := hP.isoPullback_hom_fst
  have hθs : θ.hom ≫ pullback.snd (triv E 2) (PGL.pr 2) = prod.snd ≫ Dv.toPGL 2 := hP.isoPullback_hom_snd
  let f : Fin 2 → (WS E A1 ⟶ pullback (triv E 2) (PGL.pr 2)) := fun b => gch b ≫ θ.hom
  have hfπ : ∀ b, f b ≫ π = pe := by
    intro b
    simp only [f, Category.assoc, hθπ]
    exact prod.lift_fst _ _
  have hfL : ∀ b, f b ≫ L = (gch b ≫ prod.snd) ≫ Dv.line 2 := by
    intro b
    simp only [f, hL, Category.assoc]
    rw [← Category.assoc θ.hom, hθs]
    simp [Dv.line]
  have hcov : Cover2 (ZMod q) (f 0) (f 1) := cover_comp θ.hom (gch_cover (ZMod q))
  have hpb : IsPullback (cA (E := E) q) (cB q) (f 0) (f 1) :=
    (over_pullback hE).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) θ (by simp) (by simp) (by simp [f]) (by simp [f])
  set ψ := hpb.isoPullback with hψ
  have hψ1 : ψ.inv ≫ cA q = pullback.fst (f 0) (f 1) := by
    rw [Iso.inv_comp_eq]; exact hpb.isoPullback_hom_fst.symm
  have hψ2 : ψ.inv ≫ cB q = pullback.snd (f 0) (f 1) := by
    rw [Iso.inv_comp_eq]; exact hpb.isoPullback_hom_snd.symm
  let u : pullback (f 0) (f 1) ⟶ sch.obj (Gq q) := ψ.inv ≫ ps
  let ρ : pullback (f 0) (f 1) ⟶ sch.obj (Gq q) ⨯ E := ψ.inv ≫ prod.fst
  have hρ1 : ρ ≫ prod.fst = u := by simp only [ρ, u, ps, Category.assoc]
  have hρ2 : pullback.fst (f 0) (f 1) ≫ f 0 ≫ π = ρ ≫ prod.snd := by
    rw [hfπ 0, ← hψ1, Category.assoc, cA, mkW_pe]
    simp only [ρ, pe, Category.assoc]
  have hρE : ∀ i, Eqv _ ρ (tw q i) := fun i => eqv_comp (eqv_iso _ _) (eqv_fst (inv_of_map prod.snd hE) i)
  have hK : ∀ m j : ℤ, Function.Bijective fun p : Ht q E (m + 1) (j + 1) × Ht q E m j =>
      pull _ (pullback.fst (f 0) (f 1) ≫ f 0 ≫ π) _ _ p.1 +
        cup q (pull _ (pullback.fst (f 0) (f 1) ≫ f 0 ≫ π) _ _ p.2) (pull _ u _ _ (kappa q)) := by
    intro m j
    have := ((hρE (j + 1)) (m + 1)).comp (kun hE m j)
    convert this using 1
    have a1 : ∀ {n i : ℤ} (x : Ht q E n i), pull _ (pullback.fst (f 0) (f 1) ≫ f 0 ≫ π) _ _ x =
        pull _ ρ _ _ (pull _ prod.snd _ _ x) := by
      intro n i x
      rw [hρ2, pull_comp]
    have a2 : pull _ u _ _ (kappa q) = pull _ ρ _ _ (pull _ prod.fst _ _ (kappa q)) := by
      rw [← hρ1, pull_comp]
    funext p
    simp only [Function.comp]
    rw [a1, a1, a2, map_add (f := _), pull_cup]
  have t0 : IsTrivBy (f 0 ≫ L) wc := by rw [hfL]; exact gch_triv 0
  have t1 : IsTrivBy (f 1 ≫ L) wc := by rw [hfL]; exact gch_triv 1
  have uc : ∀ (T : Scheme.{0}) (y : Sx (pullback (f 0) (f 1)) 0 T),
      Units.map (show T ⟶ Gq q from y.map u).appTop.hom.toMonoidHom (tq q) =
        wc T (y.map (pullback.fst (f 0) (f 1))) * (wc T (y.map (pullback.snd (f 0) (f 1))))⁻¹ := by
    intro T y
    have e1 : y.map (pullback.fst (f 0) (f 1)) = (y.map ψ.inv).map (cA q) := by rw [← hψ1]; rfl
    have e2 : y.map (pullback.snd (f 0) (f 1)) = (y.map ψ.inv).map (cB q) := by rw [← hψ2]; rfl
    have w1 : wc T ((y.map ψ.inv).map (cA q)) = tv q (y.map ψ.inv) * wc T (y.map ψ.inv) :=
      Units.ext (cu_cA (y.map ψ.inv) 0)
    have w2 : wc T ((y.map ψ.inv).map (cB q)) = wc T (y.map ψ.inv) := Units.ext (cu_cB (y.map ψ.inv) 0)
    rw [e1, e2, w1, w2, mul_inv_cancel_right]
    rfl
  have hd := UpperTheory.kummer_cocycle_mayerVietoris_of_cover q (f 0) (f 1) L wc wc u hX hcov t0 t1 uc
  have h₁ : ∀ b i, Eqv _ (f b ≫ π) (tw q i) := by
    intro b i
    rw [hfπ]
    exact eqv_comp (eqv_fst (inv_of_map prod.snd hE) i) (UpperTheory.tateTwist_affineLine_projection_equiv q E i hE)
  exact lh2 hX π (c1 q L) fun m j => core π (f 0) (f 1) hcov _ _ (h₁ 0) (h₁ 1) hK hd m j
end
end
