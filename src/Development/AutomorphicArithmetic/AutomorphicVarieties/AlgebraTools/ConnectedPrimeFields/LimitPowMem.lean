module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.IsWeaklyRegularPairModOneLeft
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.Imports

section

@[expose] public section

open IsLocalRing UpperTheory.V.AlgebraTools.Conn

theorem UpperTheory.V.AlgebraTools.Conn.level :
    ∀ {A R : Type} [CommRing A] [CommRing R] [Algebra A R] (J : Ideal A) (u v : A) (b c : Ideal R), Reg2 J u v → b * c ≤ J.map (algebraMap A R) →
      algebraMap A R u ∈ b ⊔ c → algebraMap A R v ∈ b ⊔ c → ∀ l : Module.Dual A R,
        ∃ a : A, ∀ (y : A) (β γ : R), β ∈ b → γ ∈ c → algebraMap A R y = β + γ → l β - y * a ∈ J := by
  intro A R _ _ _ J u v b c hreg hbc hu hv l
  have hl : ∀ x ∈ J.map (algebraMap A R), ∀ r : R, l (r * x) ∈ J := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, hj, rfl⟩ := hx
      intro r
      rw [mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul]
      exact J.mul_mem_right _ hj
    | zero => intro r; simp
    | add x y _ _ hx hy => intro r; rw [mul_add, map_add (f := _)]; exact J.add_mem (hx r) (hy r)
    | smul s x _ hx => intro r; rw [smul_eq_mul, ← mul_assoc]; exact hx _
  have key : ∀ (y y' : A) (β γ β' γ' : R), β ∈ b → γ ∈ c → β' ∈ b → γ' ∈ c →
      algebraMap A R y = β + γ → algebraMap A R y' = β' + γ' → y' * l β - y * l β' ∈ J := by
    intro y y' β γ β' γ' hβ hγ hβ' hγ' hy hy'
    have h1 : algebraMap A R y' * β - algebraMap A R y * β' ∈ J.map (algebraMap A R) := by
      apply hbc
      have e : algebraMap A R y' * β - algebraMap A R y * β' = β * γ' - β' * γ := by
        rw [hy, hy']; ring
      rw [e]
      exact Ideal.sub_mem _ (Ideal.mul_mem_mul hβ hγ') (Ideal.mul_mem_mul hβ' hγ)
    have h2 := hl _ h1 1
    rwa [one_mul, map_sub, ← Algebra.smul_def, ← Algebra.smul_def, map_smul, map_smul,
      smul_eq_mul, smul_eq_mul] at h2
  obtain ⟨βu, hβu, γu, hγu, hu'⟩ := Submodule.mem_sup.mp hu
  obtain ⟨βv, hβv, γv, hγv, hv'⟩ := Submodule.mem_sup.mp hv
  have k := key u v βu γu βv γv hβu hγu hβv hγv hu'.symm hv'.symm
  have hm : v * l βu ∈ J ⊔ Ideal.span {u} := by
    have e : v * l βu = (v * l βu - u * l βv) + u * l βv := by ring
    rw [e]
    exact Ideal.add_mem _ (Ideal.mem_sup_left k)
      (Ideal.mem_sup_right (Ideal.mem_span_singleton'.mpr ⟨l βv, mul_comm _ _⟩))
  obtain ⟨j, hj, s, hs, hjs⟩ := Submodule.mem_sup.mp (hreg.2 _ hm)
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hs
  refine ⟨a, fun y β γ hβ hγ hy => hreg.1 _ ?_⟩
  have k2 := key y u β γ βu γu hβ hγ hβu hγu hy hu'.symm
  have e : u * (l β - y * a) = (u * l β - y * l βu) + y * j := by
    rw [← hjs]; ring
  rw [e]
  exact J.add_mem k2 (J.mul_mem_left _ hj)
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.LimitPowMem

section

@[expose] public section

open IsLocalRing UpperTheory.V.AlgebraTools.Conn

private theorem UpperTheory.V.AlgebraTools.Conn.limit_pow_mem {R : Type} [CommRing R] (b c : Ideal R) (x : R)
    (hx : x ∈ (b ⊔ c).radical) (M : ℕ) : ∃ K₀, ∀ K, K₀ ≤ K → x ^ K ∈ b ^ M ⊔ c ^ M := by
  obtain ⟨n, hn⟩ := hx
  refine ⟨n * (M + M), fun K hK => ?_⟩
  have h1 : x ^ (n * (M + M)) ∈ b ^ M ⊔ c ^ M := by
    rw [pow_mul]
    exact Ideal.sup_pow_add_le_pow_sup_pow (Ideal.pow_mem_pow hn _)
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hK
  rw [pow_add]
  exact Ideal.mul_mem_right _ _ h1

private theorem smodEq_ideal_pow_iff_sub_mem {A : Type} [CommRing A] (I : Ideal A) (n : ℕ) (x y : A) :
    x ≡ y [SMOD (I ^ n • ⊤ : Submodule A A)] ↔ x - y ∈ I ^ n := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]

theorem UpperTheory.V.AlgebraTools.Conn.limit :
    ∀ {A R : Type} [CommRing A] [CommRing R] [Algebra A R] (I : Ideal A) [IsAdicComplete I A] (J : ℕ → Ideal A) (u v : A) (b c : Ideal R),
      Antitone J → (∀ m, J m ≤ I ^ m) → (∀ m K, Reg2 (J m) (u ^ K) (v ^ K)) →
      (∀ m, ∃ N, I ^ N ≤ J m) → b * c ≤ (I.map (algebraMap A R)).radical → b.FG → c.FG →
      algebraMap A R u ∈ (b ⊔ c).radical → algebraMap A R v ∈ (b ⊔ c).radical →
      ∃ a : Module.Dual A (Module.Dual A R), ∀ m, ∃ N, m ≤ N ∧ ∀ (y : A) (β γ : R), β ∈ b ^ N → γ ∈ c ^ N →
        algebraMap A R y = β + γ → ∀ l : Module.Dual A R, l β - y * a l ∈ I ^ m := by
  intro A R _ _ _ I _ J u v b c hJ hJI hreg hIJ hbc hb hc hu hv
  let P : ℕ → ℕ → Module.Dual A R → A → Prop := fun m N l a =>
    ∀ (y : A) (β γ : R), β ∈ b ^ N → γ ∈ c ^ N → algebraMap A R y = β + γ → l β - y * a ∈ J m
  have weak : ∀ m m' N N' l a, m ≤ m' → N ≤ N' → P m' N l a → P m N' l a := by
    intro m m' N N' l a hm hN h y β γ hβ hγ hy
    exact hJ hm (h y β γ (Ideal.pow_le_pow_right hN hβ) (Ideal.pow_le_pow_right hN hγ) hy)
  have uniq : ∀ m N l a a', P m N l a → P m N l a' → a - a' ∈ J m := by
    intro m N l a a' h h'
    obtain ⟨K, hK⟩ := limit_pow_mem b c (algebraMap A R u) hu N
    have hmem := hK K le_rfl
    rw [← map_pow] at hmem
    obtain ⟨β, hβ, γ, hγ, hsum⟩ := Submodule.mem_sup.mp hmem
    have e1 := h (u ^ K) β γ hβ hγ hsum.symm
    have e2 := h' (u ^ K) β γ hβ hγ hsum.symm
    apply (hreg m K).1
    have e3 := Ideal.sub_mem _ e2 e1
    convert e3 using 1
    ring
  have exist : ∀ m, ∃ N, m ≤ N ∧ ∀ l, ∃ a, P m N l a := by
    intro m
    obtain ⟨N₁, hN₁⟩ := hIJ m
    obtain ⟨P₀, hP₀⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hbc (Submodule.FG.mul hb hc)
    refine ⟨max m (P₀ * N₁), le_max_left _ _, fun l => ?_⟩
    obtain ⟨Ku, hKu⟩ := limit_pow_mem b c (algebraMap A R u) hu (max m (P₀ * N₁))
    obtain ⟨Kv, hKv⟩ := limit_pow_mem b c (algebraMap A R v) hv (max m (P₀ * N₁))
    have hprod : b ^ (max m (P₀ * N₁)) * c ^ (max m (P₀ * N₁)) ≤ Ideal.map (algebraMap A R) (J m) := by
      calc b ^ (max m (P₀ * N₁)) * c ^ (max m (P₀ * N₁)) = (b * c) ^ (max m (P₀ * N₁)) := (mul_pow b c _).symm
        _ ≤ (b * c) ^ (P₀ * N₁) := Ideal.pow_le_pow_right (le_max_right _ _)
        _ = ((b * c) ^ P₀) ^ N₁ := pow_mul _ _ _
        _ ≤ (I.map (algebraMap A R)) ^ N₁ := Ideal.pow_right_mono hP₀ N₁
        _ = (I ^ N₁).map (algebraMap A R) := (Ideal.map_pow _ _ _).symm
        _ ≤ (J m).map (algebraMap A R) := Ideal.map_mono hN₁
    have hu' : algebraMap A R (u ^ (max Ku Kv)) ∈ b ^ (max m (P₀ * N₁)) ⊔ c ^ (max m (P₀ * N₁)) := by
      rw [map_pow]
      exact hKu _ (le_max_left _ _)
    have hv' : algebraMap A R (v ^ (max Ku Kv)) ∈ b ^ (max m (P₀ * N₁)) ⊔ c ^ (max m (P₀ * N₁)) := by
      rw [map_pow]
      exact hKv _ (le_max_right _ _)
    obtain ⟨a, ha⟩ := level (J m) (u ^ (max Ku Kv)) (v ^ (max Ku Kv)) _ _ (hreg m _) hprod hu' hv' l
    exact ⟨a, ha⟩
  choose N hNm hN using exist
  choose a ha using hN
  have hcauchy : ∀ l m n, m ≤ n → a m l - a n l ∈ J m := by
    intro l m n hmn
    apply uniq m (max (N m) (N n)) l
    · exact weak m m (N m) _ l _ le_rfl (le_max_left _ _) (ha m l)
    · exact weak m n (N n) _ l _ hmn (le_max_right _ _) (ha n l)
  have hlim : ∀ l, ∃ L : A, ∀ n, a n l - L ∈ I ^ n := by
    intro l
    obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := I) (M := A) inferInstance (f := fun n => a n l)
      (fun {m n} hmn => by
        rw [smodEq_ideal_pow_iff_sub_mem]
        exact hJI m (hcauchy l m n hmn))
    exact ⟨L, fun n => (smodEq_ideal_pow_iff_sub_mem I n _ _).mp (hL n)⟩
  choose L hL using hlim
  have haus : ∀ x : A, (∀ n, x ∈ I ^ n) → x = 0 := by
    intro x hx
    apply IsHausdorff.haus (I := I) inferInstance x
    intro n
    rw [smodEq_ideal_pow_iff_sub_mem, sub_zero]
    exact hx n
  have hadd : ∀ m l l', a m (l + l') - a m l - a m l' ∈ J m := by
    intro m l l'
    have h3 : P m (N m) (l + l') (a m l + a m l') := by
      intro y β γ hβ hγ hy
      have e := Ideal.add_mem _ (ha m l y β γ hβ hγ hy) (ha m l' y β γ hβ hγ hy)
      convert e using 1
      simp only [LinearMap.add_apply]
      ring
    have e := uniq m (N m) (l + l') _ _ (ha m (l + l')) h3
    convert e using 1
    ring
  have hsmul : ∀ m (r : A) l, a m (r • l) - r * a m l ∈ J m := by
    intro m r l
    have h3 : P m (N m) (r • l) (r * a m l) := by
      intro y β γ hβ hγ hy
      have e := Ideal.mul_mem_left _ r (ha m l y β γ hβ hγ hy)
      convert e using 1
      simp only [LinearMap.smul_apply, smul_eq_mul]
      ring
    exact uniq m (N m) (r • l) _ _ (ha m (r • l)) h3
  let Φ : Module.Dual A (Module.Dual A R) :=
    { toFun := L
      map_add' := by
        intro l l'
        have h0 := haus (L (l + l') - (L l + L l')) (fun n => by
          have e := Ideal.sub_mem _ (Ideal.sub_mem _ (hL (l + l') n) (hL l n)) (hL l' n)
          have e2 := hJI n (hadd n l l')
          have e3 := Ideal.sub_mem _ e2 e
          convert e3 using 1
          ring)
        exact sub_eq_zero.mp h0
      map_smul' := by
        intro r l
        have h0 := haus (L (r • l) - r * L l) (fun n => by
          have e := Ideal.sub_mem _ (hL (r • l) n) (Ideal.mul_mem_left _ r (hL l n))
          have e2 := hJI n (hsmul n r l)
          have e3 := Ideal.sub_mem _ e2 e
          convert e3 using 1
          ring)
        rw [sub_eq_zero] at h0
        simpa using h0 }
  refine ⟨Φ, fun m => ⟨N m, hNm m, fun y β γ hβ hγ hy l => ?_⟩⟩
  have e1 := hJI m (ha m l y β γ hβ hγ hy)
  have e2 := Ideal.mul_mem_left _ y (hL l m)
  have e3 := Ideal.add_mem _ e1 e2
  show l β - y * L l ∈ I ^ m
  convert e3 using 1
  ring
end
end
