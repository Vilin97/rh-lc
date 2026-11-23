module

public import Formalism.LocalRingCardinality.DataSpaces
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
public import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.T2SpaceIsNonarchimedeanLocalFieldSingleBlock
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.FinprodPsiEEqExpTrace

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.S.Loc ValuativeRel
open scoped nonZeroDivisors

namespace GlobalTheory.AddCharProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem main_prime_pow (h2 : Module.finrank F E = 2) {sig : E →ₐ[F] E}
    (A : ∀ p : HeightOneSpectrum (𝓞 F), LocAt F E sig p) {l : ℕ} (hl : l.Prime) (y : E)
    (hy : IsIntegral ℤ y) (k : ℕ) :
    (Function.mulSupport fun p => (A p).psiE ((A p).ιE (y / (l : E) ^ k))).Finite ∧
      ∏ᶠ p, (A p).psiE ((A p).ιE (y / (l : E) ^ k)) =
        Complex.exp (2 * Real.pi * Complex.I * (((Algebra.trace ℚ E (y / (l : E) ^ k) : ℚ) : ℂ))) :=
  _root_.GlobalTheory.ResidueCharacterDense.prod_psi h2 A hl y hy k

theorem finprod_psiE_eq_exp_trace : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E], Formalism.BasicNotions.CMData F E → ∀ (sig : E →ₐ[F] E), (∀ x, sig x = star x) → ∀ (A : ∀ p : HeightOneSpectrum (𝓞 F), LocAt F E sig p), ∀ x : E, (Function.mulSupport fun p => (A p).psiE ((A p).ιE x)).Finite ∧ ∏ᶠ p, (A p).psiE ((A p).ιE x) = Complex.exp (2 * Real.pi * Complex.I * (((Algebra.trace ℚ E x : ℚ) : ℂ))) := by
  intro F E _ _ _ _ _ _ hc sig _ A x
  let P : E → Prop := fun x => (Function.mulSupport fun p => (A p).psiE ((A p).ιE x)).Finite ∧
    ∏ᶠ p, (A p).psiE ((A p).ιE x) =
      Complex.exp (2 * Real.pi * Complex.I * (((Algebra.trace ℚ E x : ℚ) : ℂ)))
  have hadd : ∀ u v, P u → P v → P (u + v) := by
    rintro u v ⟨hu, hu'⟩ ⟨hv, hv'⟩
    have e : (fun p => (A p).psiE ((A p).ιE (u + v))) =
        fun p => (A p).psiE ((A p).ιE u) * (A p).psiE ((A p).ιE v) := by
      funext p
      rw [map_add (f := _), AddChar.map_add_eq_mul]
    refine ⟨?_, ?_⟩
    · rw [e]
      exact (hu.union hv).subset (Function.mulSupport_mul _ _)
    · rw [e, finprod_mul_distrib hu hv, hu', hv', ← Complex.exp_add, map_add (f := _), Rat.cast_add, mul_add]
  have key : ∀ N : ℕ, N ≠ 0 → ∀ y : E, IsIntegral ℤ y → P (y / (N : E)) := by
    intro N
    induction N using Nat.recOnPosPrimePosCoprime with
    | prime_pow l k hl _ =>
      intro _ y hy
      have := main_prime_pow hc.deg2 A hl y hy k
      simpa only [Nat.cast_pow] using this
    | zero => intro h; exact absurd rfl h
    | one =>
      intro _ y hy
      have := main_prime_pow hc.deg2 A Nat.prime_two y hy 0
      simpa only [pow_zero, Nat.cast_one] using this
    | coprime a b ha hb hab iha ihb =>
      intro _ y hy
      obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hab
      have ha0 : (a : E) ≠ 0 := by exact_mod_cast (by omega : a ≠ 0)
      have hb0 : (b : E) ≠ 0 := by exact_mod_cast (by omega : b ≠ 0)
      have huv' : (u : E) * a + v * b = 1 := by exact_mod_cast huv
      have e : y / ((a * b : ℕ) : E) = (v * y) / a + (u * y) / b := by
        push_cast
        field_simp
        linear_combination (-y) * huv'
      rw [e]
      exact hadd _ _ (iha (by omega) _ ((isIntegral_algebraMap (x := v)).mul hy))
        (ihb (by omega) _ ((isIntegral_algebraMap (x := u)).mul hy))
  have halg : IsAlgebraic ℤ x := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic x)
  obtain ⟨n, hn, hi⟩ := halg.exists_integral_multiple
  have hi' : IsIntegral ℤ ((n * n : ℤ) • x) := by
    rw [mul_smul]; exact hi.smul n
  have h := key (n * n).natAbs (by simpa using hn) _ hi'
  have e : ((n * n : ℤ) • x) / (((n * n).natAbs : ℕ) : E) = x := by
    have h1 : (((n * n).natAbs : ℕ) : E) = ((n * n : ℤ) : E) := by
      rw [← Int.cast_natCast, Int.natAbs_of_nonneg (mul_self_nonneg n)]
    have h0 : ((n * n : ℤ) : E) ≠ 0 := by exact_mod_cast mul_ne_zero hn hn
    rw [h1, zsmul_eq_mul, mul_div_cancel_left₀ _ h0]
  rw [e] at h
  exact h

end GlobalTheory.AddCharProduct
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.PsiOfEq

section

@[expose] public section

noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.PhaseProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}

theorem coef_eq (A : Places F E sig) {r k : ℕ} (G : GFrames A r k) (p : HeightOneSpectrum (𝓞 F))
    (n : G.GLV) (m : (G.S p).GLV) (hx : A.Ext p n m)
    (sf : Fin (r + 1) → (G.S p).V) (se : Fin r → (G.S p).V)
    (f : Fin (r + 1) → G.V) (es : Fin r → G.V)
    (hsf : ∀ a : Fin (r + 1), algebraMap (A.loc p).Fp (A.loc p).Ep
      ((G.c p : (A.loc p).Fp) ^ (r - (a : ℕ))) • sf a = A.bc p (f a))
    (hse : ∀ a : Fin r, se a = algebraMap (A.loc p).Fp (A.loc p).Ep
      ((G.c p : (A.loc p).Fp) ^ (r - (a : ℕ))) • A.bc p (es a)) (a : Fin r) :
    (G.S p).coef sf se m a = algebraMap (A.loc p).Fp (A.loc p).Ep (G.c p : (A.loc p).Fp) *
      (A.loc p).ιE (∑ i, ∑ j, n (f a.succ) i * G.Hm i j * sig (es a j)) := by
  have hexp : r - (a : ℕ) = (r - ((a.succ : Fin (r + 1)) : ℕ)) + 1 := by
    have := a.isLt
    simp only [Fin.val_succ]
    omega
  set t := algebraMap (A.loc p).Fp (A.loc p).Ep
    ((G.c p : (A.loc p).Fp) ^ (r - ((a.succ : Fin (r + 1)) : ℕ))) with ht
  set u := algebraMap (A.loc p).Fp (A.loc p).Ep (G.c p : (A.loc p).Fp) with hu
  have key : ∀ i, t * m (sf a.succ) i = (A.loc p).ιE (n (f a.succ) i) := by
    intro i
    have h1 := congrArg m (hsf a.succ)
    rw [map_smul, hx] at h1
    exact congrFun h1 i
  have hcj : ∀ j, (A.L p).cj (se a j) = t * u * (A.loc p).ιE (sig (es a j)) := by
    intro j
    rw [A.L_cj p, hse a]
    change (A.loc p).cj (algebraMap (A.loc p).Fp (A.loc p).Ep
      ((G.c p : (A.loc p).Fp) ^ (r - (a : ℕ))) * (A.loc p).ιE (es a j)) = _
    rw [map_mul, AlgEquiv.commutes, (A.loc p).cj_ιE, hexp, pow_succ, map_mul]

  simp only [Frames.coef, Frames.h, hf, map_sum, Finset.mul_sum, map_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hcj j, (G.Hm_eq p), Matrix.map_apply]
  linear_combination (u * (A.loc p).ιE (G.Hm i j) * (A.loc p).ιE (sig (es a j))) * key i

theorem psiOf_eq (A : Places F E sig) {r k : ℕ} (G : GFrames A r k) (p : HeightOneSpectrum (𝓞 F))
    (δ : ((A.loc p).Fp)ˣ) (g : ℕ) (hg : g ≠ 0)
    (h1 : ∀ y, (A.L p).psi0 y = (A.loc p).psiE
      (-(y * algebraMap (A.loc p).Fp (A.loc p).Ep ((δ : (A.loc p).Fp))⁻¹)))
    (h2 : (G.c p : (A.loc p).Fp) * g = δ * (G.S p).th)
    (n : G.GLV) (m : (G.S p).GLV) (hx : A.Ext p n m)
    (sf : Fin (r + 1) → (G.S p).V) (se : Fin r → (G.S p).V)
    (f : Fin (r + 1) → G.V) (es : Fin r → G.V)
    (hsf : ∀ a : Fin (r + 1), algebraMap (A.loc p).Fp (A.loc p).Ep
      ((G.c p : (A.loc p).Fp) ^ (r - (a : ℕ))) • sf a = A.bc p (f a))
    (hse : ∀ a : Fin r, se a = algebraMap (A.loc p).Fp (A.loc p).Ep
      ((G.c p : (A.loc p).Fp) ^ (r - (a : ℕ))) • A.bc p (es a)) :
    (G.S p).psiOf sf se m = (A.loc p).psiE ((A.loc p).ιE
      (-((∑ a : Fin r, ∑ i, ∑ j, n (f a.succ) i * G.Hm i j * sig (es a j)) / g))) := by
  have hth : (G.S p).th ≠ 0 := by
    unfold Frames.th
    split_ifs
    · exact fun h => (G.S p).ϖ_irr.ne_zero (Subtype.ext h)
    · exact one_ne_zero
  have hgE : (g : E) ≠ 0 := Nat.cast_ne_zero.mpr hg
  set X : E := ∑ a : Fin r, ∑ i, ∑ j, n (f a.succ) i * G.Hm i j * sig (es a j) with hX
  have hXg : (A.loc p).ιE X = (A.loc p).ιE (X / g) * algebraMap (A.loc p).Fp (A.loc p).Ep (g : (A.loc p).Fp) := by
    rw [map_natCast, ← map_natCast (A.loc p).ιE g, ← map_mul, div_mul_cancel₀ _ hgE]
  have hsc : (G.S p).th⁻¹ * ((G.c p : (A.loc p).Fp) * g) * (δ : (A.loc p).Fp)⁻¹ = 1 := by
    rw [h2]
    field_simp
  have hsum : ∑ j, (G.S p).coef sf se m j =
      algebraMap (A.loc p).Fp (A.loc p).Ep (G.c p : (A.loc p).Fp) * (A.loc p).ιE X := by

    rw [hX, map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => coef_eq A G p n m hx sf se f es hsf hse a
  have harg : algebraMap (A.loc p).Fp (A.loc p).Ep (G.S p).th⁻¹ *
      (algebraMap (A.loc p).Fp (A.loc p).Ep (G.c p : (A.loc p).Fp) * (A.loc p).ιE X) *
      algebraMap (A.loc p).Fp (A.loc p).Ep ((δ : (A.loc p).Fp))⁻¹ = (A.loc p).ιE (X / g) := by
    have h3 := congrArg (algebraMap (A.loc p).Fp (A.loc p).Ep) hsc
    simp only [map_mul, map_one] at h3
    rw [hXg]
    linear_combination ((A.loc p).ιE (X / g)) * h3
  unfold Frames.psiOf
  rw [hsum, h1, harg, map_neg (A.loc p).ιE]

theorem main {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
    (A : Places F E sig) (r k : ℕ) (G : GFrames A r k) [StarRing E] (hCM : Formalism.BasicNotions.CMData F E)
    (hsig : ∀ x, sig x = star x) (δ : ∀ p, ((A.loc p).Fp)ˣ) (g : ℕ) (hg : g ≠ 0)
    (h1 : ∀ p y, (A.L p).psi0 y = (A.loc p).psiE
      (-(y * algebraMap (A.loc p).Fp (A.loc p).Ep ((δ p : (A.loc p).Fp))⁻¹)))
    (h2 : ∀ p, (G.c p : (A.loc p).Fp) * g = δ p * (G.S p).th)
    (n : G.GLV) (m : ∀ p, (G.S p).GLV) (hx : ∀ p, A.Ext p n (m p)) :
    (∏ᶠ p, (G.S p).psi (m p) = Complex.exp (-(2 * Real.pi * Complex.I *
      ((Algebra.trace ℚ E ((∑ a : Fin r, ∑ i, ∑ j, n (G.f a.succ) i * G.Hm i j * sig (G.es a j)) / g) : ℚ) : ℂ)))) ∧
    (∏ᶠ p, (G.S p).psi' (m p) = Complex.exp (-(2 * Real.pi * Complex.I *
      ((Algebra.trace ℚ E ((∑ a : Fin r, ∑ i, ∑ j, n (G.f' a.succ) i * G.Hm i j * sig (G.es' a j)) / g) : ℚ) : ℂ)))) ∧
    {p | (G.S p).psi (m p) ≠ 1 ∨ (G.S p).psi' (m p) ≠ 1}.Finite := by
  have hp : ∀ p, (G.S p).psi (m p) = (A.loc p).psiE ((A.loc p).ιE
      (-((∑ a : Fin r, ∑ i, ∑ j, n (G.f a.succ) i * G.Hm i j * sig (G.es a j)) / g))) := fun p =>
    psiOf_eq A G p (δ p) g hg (h1 p) (h2 p) n (m p) (hx p) (G.S p).f (G.S p).es G.f G.es
      (G.f_eq p) (G.es_eq p)
  have hp' : ∀ p, (G.S p).psi' (m p) = (A.loc p).psiE ((A.loc p).ιE
      (-((∑ a : Fin r, ∑ i, ∑ j, n (G.f' a.succ) i * G.Hm i j * sig (G.es' a j)) / g))) := fun p =>
    psiOf_eq A G p (δ p) g hg (h1 p) (h2 p) n (m p) (hx p) (G.S p).f' (G.S p).es' G.f' G.es'
      (G.f'_eq p) (G.es'_eq p)
  obtain ⟨s1, e1⟩ := GlobalTheory.AddCharProduct.finprod_psiE_eq_exp_trace hCM sig hsig A.loc
    (-((∑ a : Fin r, ∑ i, ∑ j, n (G.f a.succ) i * G.Hm i j * sig (G.es a j)) / g))
  obtain ⟨s2, e2⟩ := GlobalTheory.AddCharProduct.finprod_psiE_eq_exp_trace hCM sig hsig A.loc
    (-((∑ a : Fin r, ∑ i, ∑ j, n (G.f' a.succ) i * G.Hm i j * sig (G.es' a j)) / g))
  refine ⟨?_, ?_, ?_⟩
  · simp only [hp]
    rw [e1, map_neg, Rat.cast_neg, mul_neg]
  · simp only [hp']
    rw [e2, map_neg, Rat.cast_neg, mul_neg]
  · refine (s1.union s2).subset ?_
    intro p hq
    rcases hq with hq | hq
    · left
      simpa [Function.mem_mulSupport, hp p] using hq
    · right
      simpa [Function.mem_mulSupport, hp' p] using hq

end GlobalTheory.HL.PhaseProduct
end
end
end
