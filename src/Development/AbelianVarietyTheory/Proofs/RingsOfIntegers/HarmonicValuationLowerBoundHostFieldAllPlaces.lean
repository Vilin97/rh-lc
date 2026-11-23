module

public import Development.AutomorphicArithmetic.PrimeDiscriminants.SlopeTestRemainingChoices
public import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.BiextChangeSecondFactor
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ConnectionKillsSeries
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsRamifiedEigenLiftsOfChartDirectionsStatement
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HarmonicValueBoundOfColumnProducts
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
import Mathlib.Tactic.Basify
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ChartValJ
public import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.Divisibility.WeightAlgebra
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HarmonicValueIntegralOfUnitDiscriminantStatement
public import Formalism.LocalToGlobal.ProjectiveLattices.PartitionExtendByZeroAntitone
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HostFieldGaloisDegreeDiscrConjMovesPrimes
import Development.AbelianVarietyTheory.Definitions.Jets.ExistsSecTieFOfTies
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndSt
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts

-- Source module: Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HarmonicValueBoundOfColumnProductsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

theorem _root_.GlobalTheory.T.harmonicValue_bound_of_column_products : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), ∀ (e : ℕ) (ρ : ℝ) (w : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), (∀ (k : ℕ) (P : MvPolynomial (LtN Dw n) T.Fr), P ∈ FFV (Dw := Dw) T w n → ∀ f : Fin n → PS T.Fr 1 (chD C.ch), (∀ b, IsIntPS T (f b)) → letI := io.toAlgebra; ((-ρ : ℝ) : EReal) ≤ nval T.V e (∑ mo ∈ P.support, P.coeff mo * ∏ b, C.ch.B.nabVal T.Fr C.ch.h H.w0 k (f b) C.ch.uvec (MvPolynomial.monomial (colOf mo b) 1))) → ChBound C e ρ w n := by
  first | exact @GlobalTheory.PlaceInt.chBound_of_columns | exact GlobalTheory.PlaceInt.chBound_of_columns | (intros; apply GlobalTheory.PlaceInt.chBound_of_columns <;> assumption)
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ChartValueRamifiedOfLifts

section

@[expose] public section

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Jv

variable (T : CDVR) (e : ℕ)

theorem nval_alg_nonneg (r : T.V) : (0 : EReal) ≤ nval T.V e (algebraMap T.V T.Fr r) := by
  by_cases hr : algebraMap T.V T.Fr r = 0
  · rw [hr, nval_zero]
    exact le_top
  · rw [nval_of_ne hr]
    have hv0 : 0 ≤ vV T.V (algebraMap T.V T.Fr r) := by
      unfold Formalism.L2.Pj.vV Formalism.L2.Pj.valV
      have hle := IsDedekindDomain.HeightOneSpectrum.valuation_le_one (K := T.Fr)
        (IsDiscreteValuationRing.maximalIdeal T.V) r
      have hne : (IsDedekindDomain.HeightOneSpectrum.valuation T.Fr (IsDiscreteValuationRing.maximalIdeal T.V))
          (algebraMap T.V T.Fr r) ≠ 0 := (Valuation.ne_zero_iff _).mpr hr
      have hlog := (WithZero.log_le_log hne one_ne_zero).mpr hle
      rw [WithZero.log_one] at hlog
      linarith
    have hv : (0 : ℝ) ≤ (vV T.V (algebraMap T.V T.Fr r) : ℝ) := by exact_mod_cast hv0
    exact EReal.coe_nonneg.mpr (div_nonneg hv (Nat.cast_nonneg e))

def Jv (c : ℝ) : Submodule T.V T.Fr where
  carrier := {x | (((-c : ℝ)) : EReal) ≤ nval T.V e x}
  add_mem' := fun {a b} ha hb => le_trans (le_min ha hb) (nval_add e a b)
  zero_mem' := by
    show _ ≤ nval T.V e 0
    rw [nval_zero]
    exact le_top
  smul_mem' := fun r x hx => by
    show _ ≤ nval T.V e (r • x)
    rw [Algebra.smul_def, nval_mul]
    exact hx.trans (le_add_of_nonneg_left (nval_alg_nonneg T e r))

theorem one_mem_Jv {c : ℝ} (hc : 0 ≤ c) : (1 : T.Fr) ∈ Jv T e c := by
  show ((-c : ℝ) : EReal) ≤ nval T.V e 1
  have h1 := Formalism.L2.Pj.vV_mul (V := T.V) (K' := T.Fr) (x := 1) (y := 1) one_ne_zero one_ne_zero
  rw [mul_one] at h1
  have h0 : vV T.V (1 : T.Fr) = 0 := by omega
  rw [nval_of_ne one_ne_zero, h0]
  simp only [Int.cast_zero, zero_div]
  exact_mod_cast neg_nonpos.mpr hc

theorem mem_Jv_pow {c : ℝ} (_hc : 0 ≤ c) : ∀ (m : ℕ) (x : T.Fr), x ∈ Jv T e c ^ m →
    (((-((m : ℝ) * c)) : ℝ) : EReal) ≤ nval T.V e x := by
  intro m
  induction m with
  | zero =>
    intro x hx
    rw [pow_zero] at hx
    obtain ⟨r, rfl⟩ := Submodule.mem_one.mp hx
    simp only [Nat.cast_zero, zero_mul, neg_zero, EReal.coe_zero]
    exact nval_alg_nonneg T e r
  | succ m ih =>
    intro x hx
    rw [pow_succ] at hx
    refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) (fun y z hy hz => ?_)
    · rw [nval_mul]
      have h1 := ih a ha
      have h2 : ((-c : ℝ) : EReal) ≤ nval T.V e b := hb
      calc (((-(((m + 1 : ℕ) : ℝ) * c)) : ℝ) : EReal)
          = (((-((m : ℝ) * c)) : ℝ) : EReal) + ((-c : ℝ) : EReal) := by
            rw [← EReal.coe_add]
            congr 1
            push_cast
            ring
        _ ≤ _ := add_le_add h1 h2
    · exact le_trans (le_min hy hz) (nval_add e y z)

end Jv

theorem two_pairMin_le {ι π : Type} [Fintype ι] [Fintype π] [DecidableEq π] (c : ι → π) (s : ι → Bool)
    (x : ι →₀ ℕ) : 2 * pairMin c s x ≤ ∑ l, x l := by
  unfold pairMin
  rw [Finset.mul_sum]
  calc ∑ q : π, 2 * min (∑ l ∈ Finset.univ.filter (fun l => c l = q ∧ s l = true), x l)
        (∑ l ∈ Finset.univ.filter (fun l => c l = q ∧ s l = false), x l)
      ≤ ∑ q : π, ((∑ l ∈ Finset.univ.filter (fun l => c l = q ∧ s l = true), x l) +
        (∑ l ∈ Finset.univ.filter (fun l => c l = q ∧ s l = false), x l)) := by
        refine Finset.sum_le_sum (fun q _ => ?_)
        have h1 := min_le_left (∑ l ∈ Finset.univ.filter (fun l => c l = q ∧ s l = true), x l)
          (∑ l ∈ Finset.univ.filter (fun l => c l = q ∧ s l = false), x l)
        have h2 := min_le_right (∑ l ∈ Finset.univ.filter (fun l => c l = q ∧ s l = true), x l)
          (∑ l ∈ Finset.univ.filter (fun l => c l = q ∧ s l = false), x l)
        omega
    _ = ∑ l, x l := by
        simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun l _ => ?_)
        rw [Finset.sum_eq_single (c l)]
        · cases s l <;> simp
        · intro b _ hb
          have hb' : c l ≠ b := fun h => hb h.symm
          simp [hb']
        · intro h
          exact absurd (Finset.mem_univ _) h

theorem sum_pairMin_le {T : Type} [Fintype T] (rr : T → ℕ) (n : ℕ) {π : Type} [Fintype π] [DecidableEq π]
    (c : T → π) (s : T → Bool) (a : T → ℕ → ℕ) (mo : Formalism.L2.Pj.Letter T rr n →₀ ℕ)
    (hrow : ∀ (σ : T) (i : Fin (rr σ)), ∑ b : Fin n, mo ⟨σ, i, b⟩ = a σ i) :
    ∑ b, pairMin (fun ℓ : (Σ τ : T, Fin (rr τ)) => c ℓ.1) (fun ℓ => s ℓ.1) (colL rr n mo b) ≤
      (∑ σ, ∑ i : Fin (rr σ), a σ i) / 2 := by
  have h2 : 2 * ∑ b, pairMin (fun ℓ : (Σ τ : T, Fin (rr τ)) => c ℓ.1) (fun ℓ => s ℓ.1) (colL rr n mo b) ≤
      ∑ σ, ∑ i : Fin (rr σ), a σ i := by
    rw [Finset.mul_sum]
    calc _ ≤ ∑ b : Fin n, ∑ ℓ : (Σ τ : T, Fin (rr τ)), colL rr n mo b ℓ :=
          Finset.sum_le_sum (fun b _ => two_pairMin_le _ _ _)
      _ = ∑ ℓ : (Σ τ : T, Fin (rr τ)), ∑ b : Fin n, mo ⟨ℓ.1, ℓ.2, b⟩ := by
          rw [Finset.sum_comm]
          rfl
      _ = ∑ σ, ∑ i : Fin (rr σ), a σ i := by
          rw [Fintype.sum_sigma]
          exact Finset.sum_congr rfl (fun σ _ => Finset.sum_congr rfl (fun i _ => hrow σ i))
  omega

end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HarmonicValueBoundIntegralChartRamified

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
open ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf

namespace GlobalTheory.PlaceInt.ChartRam

theorem isRQ_of_not_isUnit (T : CDVR) (N : ℕ) (hN0 : N ≠ 0) (hNu : ¬ IsUnit (N : T.V)) :
    TB.IsRQ (R := T.V) T.Fr := by
  refine ⟨IsFractionRing.injective T.V T.Fr, fun y => ?_⟩
  have hNV0 : (N : T.V) ≠ 0 := by exact_mod_cast hN0
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible T.V
  obtain ⟨m, hm⟩ := IsDiscreteValuationRing.associated_pow_irreducible hNV0 hϖ
  have hϖN : ϖ ∣ (N : T.V) := by
    rcases m with _ | m
    · exact absurd (hm.isUnit_iff.2 (by simp)) hNu
    · exact (dvd_pow_self ϖ (Nat.succ_ne_zero m)).trans hm.symm.dvd
  obtain ⟨a, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := T.V) y
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible hs0 hϖ
  have hsd : s ∣ (N : T.V) ^ n := hn.dvd.trans (pow_dvd_pow_of_dvd hϖN n)
  obtain ⟨c, hc⟩ := hsd
  refine ⟨c * a, N ^ n, pow_pos (Nat.pos_of_ne_zero hN0) n, ?_⟩
  have hsK : algebraMap T.V T.Fr s ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective T.V T.Fr)]; exact hs0
  have hcast : ((N ^ n : ℕ) : T.Fr) = algebraMap T.V T.Fr ((N : T.V) ^ n) := by
    rw [map_pow, map_natCast]; push_cast; rfl
  rw [hcast, hc, map_mul, map_mul]
  field_simp

theorem vV_natCast_nonneg (T : CDVR) (N : ℕ) (hN0 : N ≠ 0) : 0 ≤ vV T.V (N : T.Fr) := by
  have hr : algebraMap T.V T.Fr (N : T.V) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective T.V T.Fr)]
    exact_mod_cast hN0
  have h1 := (IsDiscreteValuationRing.maximalIdeal T.V).valuation_le_one (K := T.Fr) (N : T.V)
  have h2 : valV T.V (algebraMap T.V T.Fr (N : T.V)) ≠ 0 := valV_ne_zero hr
  have h3 := (WithZero.log_le_log h2 one_ne_zero).mpr h1
  rw [WithZero.log_one, map_natCast] at h3
  unfold vV
  omega



theorem chBound_ramified : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), IsGalois ℚ E → ∀ (p a m : ℕ), p.Prime → ¬ IsUnit (p : T.V) → ¬ p ∣ m → (NumberField.discr E).natAbs = p ^ a * m → (∀ 𝔭 : Ideal (𝓞 E), 𝔭.IsPrime → (p : 𝓞 E) ∈ 𝔭 → ∃ x ∈ 𝔭, H.bar x ∉ 𝔭) → ∀ e : ℕ, 0 < e → ∀ (w : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ChBound C e ((vV T.V (p : T.Fr) : ℝ) / e * ((a : ℝ) / Module.finrank ℚ E) * (Formalism.L2.Pj.DF Dw w : ℝ) / 2) w n := by
  intro E _ _ _ H Dw l Xo c _ hstar T io y C hG p a m hp hpu hpm hd hmv e he w n
  refine GlobalTheory.T.harmonicValue_bound_of_column_products E H Dw l Xo c hstar T io y C e _ w n ?_
  intro k P hP f hf
  let _ := io.toAlgebra
  obtain ⟨π, _, _, cc, s, hcs, φ, ψ, hψ, heig, h21a, h21b, h21c⟩ :=
    GlobalTheory.T.exists_ramified_eigen_lifts_of_chart_directions E H Dw l Xo c hstar T io y C hG p a m hp hpu hpm hd hmv e he
  obtain ⟨hF, hA, h1, h2, hs, had, hu⟩ := C.gen.1
  have hinj : Function.Injective (algebraMap T.V T.Fr) := IsFractionRing.injective T.V T.Fr
  let t : CVA.IntTie (algebraMap T.V T.Fr) C.ch.B :=
    ⟨C.FT, C.actT, C.ph1T, C.ph2T, C.syT, C.adT, funext fun i => (hF i).symm, fun a => funext fun i => (hA a i).symm,
      h1.symm, h2.symm, hs.symm, fun a => (had a).symm⟩
  have huv : C.ch.uvec = fun ℓ i => algebraMap T.V T.Fr (C.uvecT ℓ i) := funext fun ℓ => funext fun i => hu ℓ i
  simp only [huv] at heig h21a h21b h21c
  set cJ : ℝ := (vV T.V (p : T.Fr) : ℝ) / e * ((a : ℝ) / Module.finrank ℚ E) with hcJ
  have hv : (0 : ℝ) ≤ (vV T.V (p : T.Fr) : ℝ) := by exact_mod_cast vV_natCast_nonneg T p hp.ne_zero
  have hcJ0 : 0 ≤ cJ := by rw [hcJ]; positivity
  have hw0 : H.w0 + star H.w0 = 1 := by rw [hstar]; exact CVA.cmHostUnit_add_conj_eq_one H
  have hpmin : ∀ mo ∈ P.support, ∑ b, TB.pairMin (fun ℓ : Lt1 Dw => cc ℓ.1) (fun ℓ => s ℓ.1)
      (colL Dw.mult n mo b) ≤ Formalism.L2.Pj.DF Dw w / 2 := fun mo hmo =>
    sum_pairMin_le Dw.mult n cc s (fun τ i => w (τ, i)) mo (hP.1.2.2 mo hmo)
  have hmem := chartValJ (isRQ_of_not_isUnit T p hp.ne_zero hpu) (Jv T e cJ) (one_mem_Jv T e hcJ0)
    (CVA.fbOf t hinj) C.ch.h (CVA.fbOf_canon t hinj C.ch.h C.ch.gauge) H.w0 hw0 k
    Dw.mult ComplexEmbedding.conjugate (fun τ => by ext x; simp) (InPsi H)
    (CVA.inPsi_or H) cc s hcs C.uvecT φ ψ hψ heig h21a h21b h21c n (fun τ i => w (τ, i)) P hP
    (Formalism.L2.Pj.DF Dw w / 2) hpmin f hf
  have hval := mem_Jv_pow T e hcJ0 _ _ hmem
  simp only [CVA.fbOf_nabVal] at hval
  rw [huv]
  refine le_trans ?_ hval
  apply EReal.coe_le_coe_iff.2
  have hdiv : ((Formalism.L2.Pj.DF Dw w / 2 : ℕ) : ℝ) ≤ (Formalism.L2.Pj.DF Dw w : ℝ) / 2 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    exact_mod_cast Nat.div_mul_le_self _ 2
  nlinarith

end GlobalTheory.PlaceInt.ChartRam
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HarmonicValueBoundIntegralChartRamifiedStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

theorem _root_.GlobalTheory.T.harmonicValue_bound_integralChart_ramified : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), IsGalois ℚ E → ∀ (p a m : ℕ), p.Prime → ¬ IsUnit (p : T.V) → ¬ p ∣ m → (NumberField.discr E).natAbs = p ^ a * m → (∀ 𝔭 : Ideal (𝓞 E), 𝔭.IsPrime → (p : 𝓞 E) ∈ 𝔭 → ∃ x ∈ 𝔭, H.bar x ∉ 𝔭) → ∀ e : ℕ, 0 < e → ∀ (w : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ChBound C e ((vV T.V (p : T.Fr) : ℝ) / e * ((a : ℝ) / Module.finrank ℚ E) * (Formalism.L2.Pj.DF Dw w : ℝ) / 2) w n := by
  first | exact @GlobalTheory.PlaceInt.ChartRam.chBound_ramified | exact GlobalTheory.PlaceInt.ChartRam.chBound_ramified | (intros; apply GlobalTheory.PlaceInt.ChartRam.chBound_ramified <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HostFieldGaloisDegreeDiscrConjMovesPrimesStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
open Formalism.BasicNotions Formalism.MainNotions IsDedekindDomain

theorem _root_.GlobalTheory.T.hostField_galois_degree_discr_conj_moves_primes : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E), IsGalois ℚ D.host.E ∧ Module.finrank ℚ D.host.E = 4 * D.R.ord ∧ (∀ p : ℕ, p.Prime → (p : ℤ) ∣ NumberField.discr D.host.E → p ∣ D.host.condN) ∧ ∀ p ∈ D.host.condN.primeFactors, p.Prime ∧ ∀ 𝔭 : Ideal (𝓞 D.host.E), 𝔭.IsPrime → (p : 𝓞 D.host.E) ∈ 𝔭 → ∃ x ∈ 𝔭, H.bar x ∉ 𝔭 := by
  first | exact @GlobalTheory.PlaceInt.host_galois_discr_moves | exact GlobalTheory.PlaceInt.host_galois_discr_moves | (intros; apply GlobalTheory.PlaceInt.host_galois_discr_moves <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HarmonicValuationLowerBoundHostFieldAllPlaces

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
open Formalism.BasicNotions Formalism.MainNotions IsDedekindDomain

namespace GlobalTheory.PlaceInt.HostChart

theorem vV_nat_nonneg (T : CDVR) (p : ℕ) : 0 ≤ vV T.V (p : T.Fr) := by
  rw [← map_natCast (algebraMap T.V T.Fr)]
  unfold vV
  by_cases ha : valV T.V (algebraMap T.V T.Fr p) = 0
  · rw [ha]; simp
  have h1 : valV T.V (algebraMap T.V T.Fr p) ≤ 1 :=
    IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ _
  have := (WithZero.log_le_log ha one_ne_zero).2 h1
  simp only [WithZero.log_one] at this
  omega

theorem chBound_mono {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)] {T : CDVR} {io : c.F →+* T.Fr}
    {y : IntFr Xo c T io} {C : IntegralChartA3 Xo c T io y} {e : ℕ} {ρ ρ' : ℝ} {w : (E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    (h : ChBound C e ρ w n) (hle : ρ ≤ ρ') : ChBound C e ρ' w n :=
  fun k => le_trans (EReal.coe_le_coe_iff.2 (neg_le_neg hle)) (h k)

theorem chBound_host : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 D.host.E)], (∀ a : 𝓞 D.host.E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y) (e : ℕ), 0 < e → ∀ (w : (D.host.E →+* ℂ) × ℕ → ℕ) (n DFw : ℕ), Formalism.L2.Pj.DF Dw w ≤ DFw → ChBound C e (∑ p ∈ D.host.condN.primeFactors, (vV T.V (p : T.Fr) : ℝ) / e * D.host.vdH p * (DFw : ℝ) / 2) w n := by
  intro D H Dw l Xo c _ hstar T io y C e he w n DFw hDF
  obtain ⟨hG, -, hD, hP⟩ := GlobalTheory.T.hostField_galois_degree_discr_conj_moves_primes D H
  have hd0 : (NumberField.discr D.host.E).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero _)
  have hnn : ∀ p ∈ D.host.condN.primeFactors, (0 : ℝ) ≤ (vV T.V (p : T.Fr) : ℝ) / e * D.host.vdH p * (DFw : ℝ) / 2 := by
    intro p _
    have h1 : (0 : ℝ) ≤ (vV T.V (p : T.Fr) : ℝ) := by exact_mod_cast vV_nat_nonneg T p
    have h2 := D.host.vdH_nonneg p
    positivity
  by_cases hu : ∀ p ∈ D.host.condN.primeFactors, IsUnit (p : T.V)
  · refine chBound_mono (GlobalTheory.T.harmonic_value_integral_of_unit_discriminant D.host.E H Dw l Xo c hstar T io y C ?_ e w n) (Finset.sum_nonneg hnn)
    have h1 : IsUnit (((NumberField.discr D.host.E).natAbs : ℕ) : T.V) := by
      rw [← Nat.prod_factorization_pow_eq_self hd0, Finsupp.prod, Nat.cast_prod]
      refine IsUnit.prod_iff.2 fun p hp => ?_
      have hp' := Nat.mem_primeFactors.1 (Nat.support_factorization _ ▸ hp)
      rw [Nat.cast_pow]
      exact (hu p (Nat.mem_primeFactors.2 ⟨hp'.1, hD p hp'.1 (Int.natCast_dvd.2 hp'.2.1), D.host.condN_ne_zero⟩)).pow _
    rcases Int.natAbs_eq (NumberField.discr D.host.E) with h | h
    · rw [h, Int.cast_natCast]; exact h1
    · rw [h, Int.cast_neg, Int.cast_natCast]; exact h1.neg
  · push Not at hu
    obtain ⟨p, hp, hpu⟩ := hu
    have hpp := (hP p hp).1
    haveI : Fact p.Prime := ⟨hpp⟩
    have hm : ¬ p ∣ ordCompl[p] (NumberField.discr D.host.E).natAbs := Nat.not_dvd_ordCompl hpp hd0
    have hDa := (Nat.ordProj_mul_ordCompl_eq_self (NumberField.discr D.host.E).natAbs p).symm
    refine chBound_mono (GlobalTheory.T.harmonicValue_bound_integralChart_ramified D.host.E H Dw l Xo c hstar T io y C hG p _ _ hpp hpu hm hDa
      (hP p hp).2 e he w n) (le_trans ?_ (Finset.single_le_sum hnn hp))
    rw [Nat.factorization_def _ hpp]
    have h1 : (0 : ℝ) ≤ (vV T.V (p : T.Fr) : ℝ) := by exact_mod_cast vV_nat_nonneg T p
    have h2 := D.host.vdH_nonneg p
    have h3 : (Formalism.L2.Pj.DF Dw w : ℝ) ≤ DFw := by exact_mod_cast hDF
    simp only [Formalism.HC.HostRaw.vdH, Nat.padicValNat_def] at h2 ⊢
    gcongr

end GlobalTheory.PlaceInt.HostChart
end
end
