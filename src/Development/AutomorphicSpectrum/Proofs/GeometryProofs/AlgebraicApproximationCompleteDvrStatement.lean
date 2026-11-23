module

public import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
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
import Mathlib.Tactic.Linter.HaveILetI
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
public import Mathlib.Algebra.Module.SpanRank
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.Identities
public import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Development.WeilBound.CoreStatements.CommonZeroEvaluation.IsAlgebraicStd
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
public import Development.WeilBound.CoreStatements.CommonZeroEvaluation.EventuallyRoot

-- Source module: Development.WeilBound.CoreStatements.CommonZeroEvaluation.ExistsRootAdicComplete

section

@[expose] public section

open Polynomial

namespace ModelDimension.Alg

theorem exists_root_adic_complete {V : Type} [CommRing V] (I : Ideal V) [IsAdicComplete I V] (e : V) (he : e ∈ I)
    (q : V[X]) : ∃ y ∈ I, e + y + y ^ 2 * q.eval y = 0 := by
  let c : ℕ → V := fun n => Nat.rec 0 (fun _ b => -e - b ^ 2 * q.eval b) n
  have hc : ∀ n, c (n + 1) = -e - c n ^ 2 * q.eval (c n) := fun n => rfl
  have hI : ∀ n, c n ∈ I := by
    intro n
    induction n with
    | zero => exact I.zero_mem
    | succ n ih =>
      rw [hc]
      exact I.sub_mem (I.neg_mem he) (I.mul_mem_right _ (I.pow_mem_of_mem ih 2 (by norm_num)))
  have key : ∀ (y z : V) (n : ℕ), y ∈ I → z ∈ I → y - z ∈ I ^ n →
      y ^ 2 * q.eval y - z ^ 2 * q.eval z ∈ I ^ (n + 1) := by
    intro y z n hy hz h
    obtain ⟨k, hk⟩ := Polynomial.sub_dvd_eval_sub y z q
    have : y ^ 2 * q.eval y - z ^ 2 * q.eval z = (y - z) * ((y + z) * q.eval y + z * (z * k)) := by
      linear_combination z ^ 2 * hk
    rw [this, pow_succ]
    exact Ideal.mul_mem_mul h (I.add_mem (I.mul_mem_right _ (I.add_mem hy hz)) (I.mul_mem_right _ hz))
  have hstep : ∀ n, c (n + 1) - c n ∈ I ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have := key _ _ n (hI (n + 1)) (hI n) ih
      have e2 : c (n + 1 + 1) - c (n + 1) =
          -(c (n + 1) ^ 2 * q.eval (c (n + 1)) - c n ^ 2 * q.eval (c n)) := by
        rw [hc (n + 1)]
        linear_combination -(hc n)
      rw [e2]
      exact (I ^ (n + 1)).neg_mem this
  have aux : ∀ m n, m ≤ n → c m ≡ c n [SMOD (I ^ m • ⊤ : Ideal V)] := by
    intro m n hmn
    rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one, SModEq.sub_mem]
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have : c m - c (n + 1) = (c m - c n) - (c (n + 1) - c n) := by ring
      rw [this]
      exact (I ^ m).sub_mem ih (Ideal.pow_le_pow_right hmn (hstep n))
  obtain ⟨a, ha⟩ := IsPrecomplete.prec' c (aux _ _)
  have ha' : ∀ n, c n - a ∈ I ^ n := fun n => by
    have := ha n
    rwa [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one, SModEq.sub_mem] at this
  have haI : a ∈ I := by
    have h1 := ha' 1
    rw [pow_one] at h1
    have : a = c 1 - (c 1 - a) := by ring
    rw [this]
    exact I.sub_mem (hI 1) h1
  refine ⟨a, haI, IsHausdorff.haus' (I := I) _ fun n => ?_⟩
  rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one, SModEq.zero]
  have h1 := key _ _ n (hI n) haI (ha' n)
  have h2 := ha' (n + 1)
  have : e + a + a ^ 2 * q.eval a = -(c (n + 1) - a) - (c n ^ 2 * q.eval (c n) - a ^ 2 * q.eval a) := by
    rw [hc]; ring
  rw [this]
  exact Ideal.pow_le_pow_right (Nat.le_succ n) ((I ^ (n + 1)).sub_mem ((I ^ (n + 1)).neg_mem h2) h1)

theorem exists_root {V : Type} [CommRing V] [IsLocalRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V]
    (f : V[X]) (α e : V) (he : e ∈ IsLocalRing.maximalIdeal V)
    (h : f.eval α = (f.derivative.eval α) ^ 2 * e) : ∃ β, f.eval β = 0 ∧ e ∣ β - α := by
  set d := f.derivative.eval α with hd
  obtain ⟨k, hk⟩ := (f.map (C : V →+* V[X])).binomExpansion (C α) (C d * X)
  obtain ⟨y, hy, hq⟩ := exists_root_adic_complete _ e he k
  have h1 := congrArg (Polynomial.evalRingHom y) hk
  have hev : ∀ (p : V[X]) (z : V[X]), (evalRingHom y) ((p.map (C : V →+* V[X])).eval z) = p.eval (z.eval y) := by
    intro p z
    rw [eval_map, hom_eval₂]
    have : (evalRingHom y).comp (C : V →+* V[X]) = RingHom.id V := by ext; simp
    rw [this]
    rfl
  rw [derivative_map] at h1
  simp only [map_add (f := _), map_mul, map_pow, hev] at h1
  simp only [coe_evalRingHom, eval_C, eval_X, eval_add, eval_mul, ← hd] at h1
  refine ⟨α + d * y, ?_, ?_⟩
  · rw [h1, h]
    linear_combination d ^ 2 * hq
  · have hu : IsUnit (1 + y * k.eval y) := by
      have := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits (-(y * k.eval y))
        ((IsLocalRing.mem_maximalIdeal _).1 (Submodule.neg_mem _ (Ideal.mul_mem_right _ _ hy)))
      simpa using this
    have : e ∣ y * (1 + y * k.eval y) := ⟨-1, by linear_combination hq⟩
    rw [add_sub_cancel_left]
    exact Dvd.dvd.mul_left ((hu.dvd_mul_right).1 this) d

theorem exists_monic {V : Type} [CommRing V] (N : ℕ) [Finite (V ⧸ Ideal.span {(N : V)})] :
    ∃ m : ℕ, ∀ (α : V) (k : ℕ), ∃ P : ℤ[X], P.Monic ∧ P.natDegree = m ∧ (N : V) ^ k ∣ aeval α P := by
  classical
  let s : Set V := Set.range (Function.surjInv (Ideal.Quotient.mk_surjective (I := Ideal.span {(N : V)})))
  have hs : s.Finite := Set.finite_range _
  have hsp : ∀ (k : ℕ) (x : V), ∃ y ∈ Submodule.span ℤ s, (N : V) ^ k ∣ x - y := by
    intro k
    induction k with
    | zero => exact fun x => ⟨0, Submodule.zero_mem _, by simp⟩
    | succ k ih =>
      intro x
      obtain ⟨y, hy, z, hz⟩ := ih x
      let w := Function.surjInv (Ideal.Quotient.mk_surjective (I := Ideal.span {(N : V)})) (Ideal.Quotient.mk _ z)
      have hw : Ideal.Quotient.mk (Ideal.span {(N : V)}) w = Ideal.Quotient.mk _ z := Function.surjInv_eq _ _
      obtain ⟨u, hu⟩ := Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 hw.symm)
      refine ⟨y + ((N : ℤ) ^ k) • w, Submodule.add_mem _ hy
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)), u, ?_⟩
      rw [zsmul_eq_mul]
      push_cast
      linear_combination hz + (N : V) ^ k * hu
  refine ⟨s.ncard, fun α k => ?_⟩
  let J : Ideal V := Ideal.span {(N : V) ^ k}
  have htop : Submodule.span ℤ (Ideal.Quotient.mk J '' s) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, hy, hd⟩ := hsp k x
    have : Ideal.Quotient.mk J x = Ideal.Quotient.mk J y := Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 hd)
    rw [this]
    have := Submodule.mem_map_of_mem (f := (Ideal.Quotient.mkₐ ℤ J).toLinearMap) hy
    rwa [Submodule.map_span] at this
  haveI : Module.Finite ℤ (V ⧸ J) := ⟨htop ▸ Submodule.fg_span (hs.image _)⟩
  obtain ⟨p, hp, hdeg, h0⟩ := LinearMap.exists_monic_and_natDegree_eq_and_aeval_eq_zero ℤ
    (Algebra.lmul ℤ (V ⧸ J) (Ideal.Quotient.mk J α))
  have hle : p.natDegree ≤ s.ncard := by
    rw [hdeg, ← htop]
    exact (Submodule.spanFinrank_span_le_ncard_of_finite (hs.image _)).trans (Set.ncard_image_le hs)
  have h1 : aeval (Ideal.Quotient.mk J α) p = 0 := by
    rw [aeval_algHom_apply] at h0
    exact Algebra.lmul_injective (h0.trans (map_zero _).symm)
  have h2 : (N : V) ^ k ∣ aeval α p := by
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]
    exact (aeval_algHom_apply (Ideal.Quotient.mkₐ ℤ J) α p).symm.trans h1
  refine ⟨p * X ^ (s.ncard - p.natDegree), hp.mul (monic_X_pow _), ?_, ?_⟩
  · rw [hp.natDegree_mul (monic_X_pow _), natDegree_X_pow]; omega
  · rw [map_mul]; exact h2.mul_right _

end ModelDimension.Alg
end
end

-- Source module: Development.WeilBound.CoreStatements.CommonZeroEvaluation.AlgebraicApproximationValued

section

@[expose] public section

open Formalism.L2.Pj

open Polynomial IsDedekindDomain

theorem ModelDimension.Alg.approx_dvr (F : Type) [Field F] [NumberField F] (R : Type) [CommRing R] [IsDomain R] [Algebra F R]
    [Algebra.Smooth F R] (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [CharZero V] [Field K] [Algebra V K] [IsFractionRing V K]
    (hT : Finite (IsLocalRing.ResidueField V)) (io : F →+* K) (ψ : R →+* K) (hψ : ψ.comp (algebraMap F R) = io)
    (S : Finset R) (n : ℕ) (g : R) (hg : g ≠ 0) : ∃ ψ' : R →+* K, ψ'.comp (algebraMap F R) = io ∧
      (∀ x, IsAlgebraic ℤ (ψ' x)) ∧ (∀ s ∈ S, ψ' s = ψ s ∨ (n : ℤ) ≤ vV V (ψ' s - ψ s)) ∧ ψ' g ≠ 0 := by
  classical
  set P := IsDiscreteValuationRing.maximalIdeal V with hP
  have hb : (1 : NNReal) < 2 := one_lt_two
  letI nK : NormedField K := (P.adicAbv (K := K) hb).toNormedField
  have hnorm : ∀ x : K, ‖x‖ = (WithZeroMulInt.toNNReal (ne_zero_of_lt hb) (valV V x) : ℝ) :=
    fun x => rfl
  haveI : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective V K)
  have hint : ∀ a : V, ‖algebraMap V K a‖ ≤ 1 := by
    intro a
    rw [hnorm]
    exact_mod_cast (WithZeroMulInt.toNNReal_le_one_iff hb).mpr (P.valuation_le_one (K := K) a)
  have hintlt : ∀ a : V, ‖algebraMap V K a‖ < 1 ↔ a ∈ IsLocalRing.maximalIdeal V := by
    intro a
    rw [hnorm]
    have h := WithZeroMulInt.toNNReal_lt_one_iff (m := P.valuation K (algebraMap V K a)) hb
    rw [P.valuation_lt_one_iff_mem] at h
    exact_mod_cast h
  have hmem : ∀ x : K, ‖x‖ ≤ 1 → ∃ a : V, algebraMap V K a = x := by
    intro x hx
    have hv : P.valuation K x ≤ 1 := by
      rw [hnorm] at hx
      exact (WithZeroMulInt.toNNReal_le_one_iff hb).mp (by exact_mod_cast hx)
    have huniq : ∀ w : HeightOneSpectrum V, w = P := by
      intro w
      ext1
      exact IsLocalRing.eq_maximalIdeal w.isMaximal
    obtain ⟨a, ha⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one K x
      (fun w => by rw [huniq w]; exact hv)
    exact ⟨a, ha⟩
  have hev : ∀ (q : Polynomial V) (a : V),
      Polynomial.eval (algebraMap V K a) (q.map (algebraMap V K)) = algebraMap V K (Polynomial.eval a q) := by
    intro q a
    rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]
  have hH : ModelDimension.Alg.HenselN K := by
    intro h α hco hα hlt
    obtain ⟨f, rfl⟩ : ∃ f : Polynomial V, f.map (algebraMap V K) = h := by
      have hl : h ∈ Polynomial.lifts (algebraMap V K) :=
        (Polynomial.lifts_iff_coeff_lifts h).mpr (fun k => hmem _ (hco k))
      exact Polynomial.mem_lifts h |>.mp hl
    obtain ⟨a, rfl⟩ := hmem α hα
    rw [Polynomial.derivative_map, hev, hev] at hlt
    rw [Polynomial.derivative_map, hev, hev]
    set y := Polynomial.eval a f
    set d := Polynomial.eval a (Polynomial.derivative f)
    have hd : algebraMap V K d ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hlt
      have := norm_nonneg (algebraMap V K y)
      nlinarith
    have hdpos : 0 < ‖algebraMap V K d‖ ^ 2 := by positivity
    have hq : ‖algebraMap V K y / algebraMap V K d ^ 2‖ < 1 := by
      rw [norm_div, norm_pow, div_lt_one hdpos]
      exact hlt
    obtain ⟨e, he⟩ := hmem _ hq.le
    have hem : e ∈ IsLocalRing.maximalIdeal V := (hintlt e).mp (by rw [he]; exact hq)
    have hy : y = d ^ 2 * e := by
      apply IsFractionRing.injective V K
      rw [map_mul, map_pow, he]
      field_simp
    obtain ⟨β, hβ, c, hc⟩ := ModelDimension.Alg.exists_root f a e hem hy
    refine ⟨algebraMap V K β, ?_, ?_⟩
    · rw [hev, hβ, map_zero]
    · rw [← map_sub, hc, map_mul, norm_mul, he, norm_div, norm_pow]
      calc ‖algebraMap V K y‖ / ‖algebraMap V K d‖ ^ 2 * ‖algebraMap V K c‖
          ≤ ‖algebraMap V K y‖ / ‖algebraMap V K d‖ ^ 2 * 1 := by
            gcongr
            exact hint c
        _ = _ := mul_one _
  obtain ⟨N, hN0, hNm, hNf⟩ : ∃ N : ℕ, N ≠ 0 ∧ (N : V) ∈ IsLocalRing.maximalIdeal V ∧
      Finite (V ⧸ Ideal.span {(N : V)}) := by
    haveI : CharP (IsLocalRing.ResidueField V) (ringChar (IsLocalRing.ResidueField V)) :=
      ringChar.charP _
    refine ⟨ringChar (IsLocalRing.ResidueField V),
      CharP.char_ne_zero_of_finite (IsLocalRing.ResidueField V) _, ?_, ?_⟩
    · rw [← IsLocalRing.residue_eq_zero_iff, map_natCast]
      exact ringChar.Nat.cast_ringChar
    · have hne : Ideal.span {((ringChar (IsLocalRing.ResidueField V) : ℕ) : V)} ≠ ⊥ := by
        rw [Ne, Ideal.span_singleton_eq_bot]
        exact Nat.cast_ne_zero.mpr (CharP.char_ne_zero_of_finite (IsLocalRing.ResidueField V) _)
      obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
      obtain ⟨k, hk⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hne hϖ
      haveI : Finite (V ⧸ IsLocalRing.maximalIdeal V) := hT
      have hfin := Ideal.finite_quotient_pow (IsNoetherian.noetherian (IsLocalRing.maximalIdeal V)) k
      rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, ← hk] at hfin
      exact hfin
  have hNK : ‖(N : K)‖ < 1 := by
    have := (hintlt (N : V)).mpr hNm
    simpa using this
  have hNne : (N : K) ≠ 0 := Nat.cast_ne_zero.mpr hN0
  have hdense : Dense {x : K | IsAlgebraic ℤ x} := by
    refine ModelDimension.Alg.dense_algebraic hH (fun z => ?_) N hN0 hNK (fun α hα => ?_)
    · simpa using hint (z : V)
    · haveI := hNf
      obtain ⟨m, hm⟩ := ModelDimension.Alg.exists_monic (V := V) N
      refine ⟨m, fun δ hδ => ?_⟩
      obtain ⟨a, rfl⟩ := hmem α hα
      obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hδ hNK
      obtain ⟨Q, hQm, hQd, c, hc⟩ := hm a k
      refine ⟨Q, hQm, hQd, ?_⟩
      rw [Polynomial.aeval_algebraMap_apply, hc, map_mul, norm_mul, map_pow, norm_pow, map_natCast]
      calc ‖(N : K)‖ ^ k * ‖algebraMap V K c‖ ≤ ‖(N : K)‖ ^ k * 1 := by
            gcongr
            exact hint c
        _ < δ := by rw [mul_one]; exact hk
  letI : Algebra F K := io.toAlgebra
  have hdF : Dense {x : K | IsAlgebraic F x} :=
    hdense.mono (fun x hx => IsAlgebraic.extendScalars (algebraMap ℤ F).injective_int hx)
  let ψa : R →ₐ[F] K := { ψ with commutes' := fun r => by exact RingHom.congr_fun hψ r }
  have hFZ : Algebra.IsAlgebraic ℤ F :=
    (IsFractionRing.comap_isAlgebraic_iff (K := ℚ)).mpr inferInstance
  obtain ⟨ε, hε, hεn⟩ : ∃ ε : ℝ, 0 < ε ∧ ∀ d : K, ‖d‖ < ε → d = 0 ∨ (n : ℤ) ≤ vV V d := by
    refine ⟨(WithZeroMulInt.toNNReal (ne_zero_of_lt hb) (WithZero.exp (-(n : ℤ))) : ℝ), ?_, ?_⟩
    · exact_mod_cast WithZeroMulInt.toNNReal_pos _ WithZero.exp_ne_zero
    · intro d hd
      by_cases h0 : d = 0
      · exact Or.inl h0
      right
      rw [hnorm] at hd
      have hlt : valV V d < WithZero.exp (-(n : ℤ)) :=
        (WithZeroMulInt.toNNReal_strictMono hb).lt_iff_lt.mp (by exact_mod_cast hd)
      have hne : valV V d ≠ 0 := (Valuation.ne_zero_iff _).mpr h0
      rw [← WithZero.exp_log hne, WithZero.exp_lt_exp] at hlt
      show (n : ℤ) ≤ -(valV V d).log
      omega
  obtain ⟨ψ', h1, h2, h3⟩ := ModelDimension.Alg.approx_smooth hH hNne hNK hdF ψa S ε hε g hg
  refine ⟨ψ'.toRingHom, ?_, fun x => ?_, fun s hs => ?_, h3⟩
  · ext r
    exact ψ'.commutes r
  · exact (h1 x).restrictScalars ℤ
  · rcases hεn _ (h2 s hs) with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr h

theorem ModelDimension.algebraic_approximation_valued : ∀ (F : Type) [Field F] [NumberField F] (R : Type) [CommRing R] [IsDomain R] [Algebra F R] [Algebra.Smooth F R] (T : CDVR), T.FinRes → ∀ (io : F →+* T.Fr) (ψ : R →+* T.Fr), ψ.comp (algebraMap F R) = io → ∀ (S : Finset R) (n : ℕ) (g : R), g ≠ 0 → ∃ ψ' : R →+* T.Fr, ψ'.comp (algebraMap F R) = io ∧ (∀ x, IsAlgebraic ℤ (ψ' x)) ∧ (∀ s ∈ S, ψ' s = ψ s ∨ (n : ℤ) ≤ vV T.V (ψ' s - ψ s)) ∧ ψ' g ≠ 0 := by
  intro F _ _ R _ _ _ _ T hT io ψ hψ S n g hg
  letI := T.cr; letI := T.dom; letI := T.dvr; letI := T.cpl; letI := T.ch0
  obtain ⟨ψ', h1, h2, h3, h4⟩ :=
    ModelDimension.Alg.approx_dvr F R T.V (FractionRing T.V) hT io ψ hψ S n g hg
  refine ⟨ψ', h1, fun x => ?_, h3, h4⟩
  obtain ⟨p, hp, hpx⟩ := h2 x
  refine ⟨p, hp, ?_⟩
  simp only [Polynomial.aeval_def, algebraMap_int_eq] at hpx
  rw [Polynomial.aeval_def, show algebraMap ℤ T.Fr = Int.castRingHom T.Fr from RingHom.ext_int _ _]
  exact hpx
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.AlgebraicApproximationCompleteDvr

section

@[expose] public section

open Formalism.L2.Pj


theorem _root_.GlobalTheory.CompanionTheory.Relay.algebraic_approximation_complete_dvr : ∀ (F : Type) [Field F] [NumberField F] (R : Type) [CommRing R] [IsDomain R] [Algebra F R] [Algebra.Smooth F R] (T : CDVR), T.FinRes → ∀ (io : F →+* T.Fr) (ψ : R →+* T.Fr), ψ.comp (algebraMap F R) = io → ∀ (S : Finset R) (n : ℕ) (g : R), g ≠ 0 → ∃ ψ' : R →+* T.Fr, ψ'.comp (algebraMap F R) = io ∧ (∀ x, IsAlgebraic ℤ (ψ' x)) ∧ (∀ s ∈ S, ψ' s = ψ s ∨ (n : ℤ) ≤ vV T.V (ψ' s - ψ s)) ∧ ψ' g ≠ 0 := by
  first | exact @ModelDimension.algebraic_approximation_valued | exact ModelDimension.algebraic_approximation_valued
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.AlgebraicApproximationCompleteDvrStatement

section

@[expose] public section

open Formalism.L2.Pj


theorem _root_.GlobalTheory.T.algebraic_approximation_complete_dvr : ∀ (F : Type) [Field F] [NumberField F] (R : Type) [CommRing R] [IsDomain R] [Algebra F R] [Algebra.Smooth F R] (T : CDVR), T.FinRes → ∀ (io : F →+* T.Fr) (ψ : R →+* T.Fr), ψ.comp (algebraMap F R) = io → ∀ (S : Finset R) (n : ℕ) (g : R), g ≠ 0 → ∃ ψ' : R →+* T.Fr, ψ'.comp (algebraMap F R) = io ∧ (∀ x, IsAlgebraic ℤ (ψ' x)) ∧ (∀ s ∈ S, ψ' s = ψ s ∨ (n : ℤ) ≤ vV T.V (ψ' s - ψ s)) ∧ ψ' g ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Relay.algebraic_approximation_complete_dvr | exact GlobalTheory.CompanionTheory.Relay.algebraic_approximation_complete_dvr | (intros; apply GlobalTheory.CompanionTheory.Relay.algebraic_approximation_complete_dvr <;> assumption)
end
end
