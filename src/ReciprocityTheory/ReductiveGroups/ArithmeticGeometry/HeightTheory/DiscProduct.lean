module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscBDefs
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Tactic.Linter.HaveILetI
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.GoodPrimesProperties
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HHINDA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ValUFD
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HHINDC
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.LogHeightDivMultihomogeneous
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HintIntOfBounds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HHINDA
import ReciprocityTheory.SemistableReduction.LagrangeIdealLiftsFact
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FiniteHeightFractionRepr

section

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.Closed MeasureTheory IsDedekindDomain
  ReciprocityTheory.ChartRestriction.G.T0.HeightMultiplicativity

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem gen_ne_zero_of_mem_htOne {p : Ideal (KTp K d.D d.N)} (hp : p ∈ d.HtOne) : d.gen p ≠ 0 := by
  obtain ⟨hpr, hh⟩ := hp
  haveI := hpr
  obtain ⟨g, hg, hpg⟩ := ValUFD.heightOne_principal p hh
  have hPr : p.IsPrincipal := ⟨⟨g, hpg⟩⟩
  unfold gen
  rw [dite_eq_left hPr]
  intro h0
  have hbot : p = ⊥ := (Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero p).2 h0
  rw [hbot] at hpg
  exact hg.ne_zero (Ideal.span_singleton_eq_bot.1 hpg.symm)

theorem finite_height_fraction_repr (hd : d.AxH 𝒜) (h : d.S1) :
    ∃ U V : KTp K d.D d.N, U ≠ 0 ∧ V ≠ 0 ∧ (∃ eU, IsMultiHomogeneous eU U) ∧
      (∃ eV, IsMultiHomogeneous eV V) ∧
      d.fDivE hd h * algebraMap (KTp K d.D d.N) (KTf K d.D d.N) V =
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) U ∧
      d.h0f h d.wF hd.a4.choose = h0 U - h0 V := by
  classical
  have hspec : ∀ c, hd.a4.choose c ∈ 𝒜 c d.wF ∧ hd.a4.choose c ≠ 0 := hd.a4.choose_spec.1
  have hfin : ∀ c, {p | p ∈ d.HtOne ∧ d.nP h c d.wF (hd.a4.choose c) p ≠ 0}.Finite := fun c =>
    (d.good_primes_properties hd h c).2.2.1 d.wF (hd.a4.choose c) (hspec c).1 (hspec c).2
  obtain ⟨T, hmemT⟩ : ∃ T : ι → Finset (Ideal (KTp K d.D d.N)),
      ∀ c p, p ∈ T c ↔ p ∈ d.HtOne ∧ d.nP h c d.wF (hd.a4.choose c) p ≠ 0 :=
    ⟨fun c => (hfin c).toFinset, fun c p => by simp⟩
  have hmemS : ∀ x ∈ Finset.univ.sigma T,
      x.2 ∈ d.HtOne ∧ d.nP h x.1 d.wF (hd.a4.choose x.1) x.2 ≠ 0 := by
    intro x hx
    rw [Finset.mem_sigma] at hx
    exact (hmemT _ _).1 hx.2
  have hne : ∀ x ∈ Finset.univ.sigma T, d.gen x.2 ≠ 0 := fun x hx => d.gen_ne_zero_of_mem_htOne (hmemS x hx).1
  have hmh : ∀ x ∈ Finset.univ.sigma T,
      IsMultiHomogeneous (fun b : Fin (d.D + 1) => if b = 0 then 0 else d.dg (d.gen x.2)) (d.gen x.2) := by
    intro x hx
    obtain ⟨hp, hn⟩ := hmemS x hx
    refine (d.good_primes_properties hd h x.1).2.1 x.2 hp ?_
    by_contra hw
    push_neg at hw
    apply hn
    simp [nP, hw]
  have halg : ∀ x ∈ Finset.univ.sigma T,
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen x.2) ≠ 0 := fun x hx =>
    (map_ne_zero_iff _ (IsFractionRing.injective (KTp K d.D d.N) (KTf K d.D d.N))).2 (hne x hx)
  have key : ∀ (a : KTf K d.D d.N), a ≠ 0 → ∀ m : ℤ, a ^ m * a ^ (-m).toNat = a ^ m.toNat := by
    intro a ha m
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ ha]
    congr 1
    omega
  refine ⟨∏ x ∈ Finset.univ.sigma T, d.gen x.2 ^ (d.nP h x.1 d.wF (hd.a4.choose x.1) x.2).toNat,
    ∏ x ∈ Finset.univ.sigma T, d.gen x.2 ^ (-d.nP h x.1 d.wF (hd.a4.choose x.1) x.2).toNat,
    Finset.prod_ne_zero_iff.2 fun x hx => pow_ne_zero _ (hne x hx),
    Finset.prod_ne_zero_iff.2 fun x hx => pow_ne_zero _ (hne x hx),
    ⟨_, HeightMultiplicativity.multi_prod _ _ _ fun x hx => HeightMultiplicativity.multi_pow (hmh x hx) _⟩,
    ⟨_, HeightMultiplicativity.multi_prod _ _ _ fun x hx => HeightMultiplicativity.multi_pow (hmh x hx) _⟩, ?_, ?_⟩
  · have hfac : ∀ c, (∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ d.nP h c d.wF (hd.a4.choose c) p) =
        ∏ p ∈ T c, algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^
          d.nP h c d.wF (hd.a4.choose c) p := by
      intro c
      apply finprod_mem_eq_prod_of_subset
      · rintro p ⟨hp, hp1⟩
        rw [Function.mem_mulSupport] at hp1
        rw [Finset.mem_coe, hmemT]
        exact ⟨hp, fun h0' => hp1 (by rw [h0', zpow_zero])⟩
      · intro p hp
        exact ((hmemT c p).1 hp).1
    have hf : d.fDivE hd h = ∏ x ∈ Finset.univ.sigma T,
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen x.2) ^ d.nP h x.1 d.wF (hd.a4.choose x.1) x.2 := by
      rw [Finset.prod_sigma]
      unfold fDivE
      exact Finset.prod_congr rfl fun c _ => hfac c
    rw [hf, map_prod, map_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun x hx => ?_
    rw [map_pow, map_pow]
    exact key _ (halg x hx) _
  · have hsum : ∀ c, (∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
        (d.nP h c d.wF (hd.a4.choose c) p : ℝ) * h0 (d.gen p)) =
        ∑ p ∈ T c, (d.nP h c d.wF (hd.a4.choose c) p : ℝ) * h0 (d.gen p) := by
      intro c
      apply finsum_mem_eq_sum_of_subset
      · rintro p ⟨hp, hp1⟩
        rw [Function.mem_support] at hp1
        rw [Finset.mem_coe, hmemT]
        exact ⟨hp, fun h0' => hp1 (by rw [h0', Int.cast_zero, zero_mul])⟩
      · intro p hp
        exact ((hmemT c p).1 hp).1
    have hn0 : 0 < d.N + 1 := Nat.succ_pos _
    have hU : h0 (∏ x ∈ Finset.univ.sigma T,
        d.gen x.2 ^ (d.nP h x.1 d.wF (hd.a4.choose x.1) x.2).toNat) =
        ∑ x ∈ Finset.univ.sigma T,
          ((d.nP h x.1 d.wF (hd.a4.choose x.1) x.2).toNat : ℝ) * h0 (d.gen x.2) :=
      HeightMultiplicativity.logHeight_prod_pow (B := d.D + 1) (n := d.N + 1) hn0 (Finset.univ.sigma T)
        (fun x b => if b = 0 then 0 else d.dg (d.gen x.2)) (fun x => d.gen x.2) _ hne hmh
    have hV : h0 (∏ x ∈ Finset.univ.sigma T,
        d.gen x.2 ^ (-d.nP h x.1 d.wF (hd.a4.choose x.1) x.2).toNat) =
        ∑ x ∈ Finset.univ.sigma T,
          ((-d.nP h x.1 d.wF (hd.a4.choose x.1) x.2).toNat : ℝ) * h0 (d.gen x.2) :=
      HeightMultiplicativity.logHeight_prod_pow (B := d.D + 1) (n := d.N + 1) hn0 (Finset.univ.sigma T)
        (fun x b => if b = 0 then 0 else d.dg (d.gen x.2)) (fun x => d.gen x.2) _ hne hmh
    rw [hU, hV, ← Finset.sum_sub_distrib, Finset.sum_sigma]
    unfold h0f
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hsum c]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← sub_mul]
    congr 1
    exact_mod_cast (Int.toNat_sub_toNat_neg _).symm

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.SphereMeanSubArchimedean

section

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.Closed MeasureTheory IsDedekindDomain
  ReciprocityTheory.ChartRestriction.G.T0.HeightMultiplicativity

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem eval_indep_of_first_block (q : KTp K d.D d.N) (m : Fin (d.D + 1) → ℕ) (hm0 : m 0 = 0)
    (hq : IsMultiHomogeneous m q) (sg : K →+* ℂ) (t0 : Fin (d.N + 1) → ℂ)
    (t : Fin d.D → Fin (d.N + 1) → ℂ) : d.evT sg t0 t q = d.evT sg 0 t q := by
  unfold evT
  rw [MvPolynomial.eval₂_eq', MvPolynomial.eval₂_eq']
  apply Finset.sum_congr rfl
  intro s hs
  congr 1
  apply Finset.prod_congr rfl
  rintro ⟨b, j⟩ _
  have hsum : ∑ j : Fin (d.N + 1), s (0, j) = 0 := by
    rw [hq s hs 0, hm0]
  cases b using Fin.cases with
  | zero =>
    have h0 : s (0, j) = 0 := (Finset.sum_eq_zero_iff.mp hsum) j (Finset.mem_univ _)
    simp [h0]
  | succ i => rfl

theorem sphereMean_sub_archimedean (a b : KTp K d.D d.N) (m : Fin (d.D + 1) → ℕ) (hm0 : m 0 = 0)
    (ha : a ≠ 0) (hb : b ≠ 0) (hma : IsMultiHomogeneous m a) (hmb : IsMultiHomogeneous m b)
    (sg : K →+* ℂ) :
    blockSphereMean (d.D + 1) (d.N + 1) (MvPolynomial.map sg a) -
      blockSphereMean (d.D + 1) (d.N + 1) (MvPolynomial.map sg b) = d.mSgP sg a b := by
  have hn : 0 < d.N + 1 := Nat.succ_pos _
  have hmp := hint_mpTail d.D (d.N + 1) hn
  have key : ∀ q : KTp K d.D d.N, q ≠ 0 → IsMultiHomogeneous m q →
      blockSphereMean (d.D + 1) (d.N + 1) (MvPolynomial.map sg q) =
        ∫ w, Real.log ‖d.evT sg 0 (d.tOf w) q‖ ∂(ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1)) ∧
      Integrable (fun w => Real.log ‖d.evT sg 0 (d.tOf w) q‖)
        (ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1)) := by
    intro q hq0 hq
    have hq0' : MvPolynomial.map sg q ≠ 0 := fun h =>
      hq0 (MvPolynomial.map_injective _ sg.injective (by rw [h, map_zero]))
    have hq' : IsMultiHomogeneous m (MvPolynomial.map sg q) :=
      fun s hs => hq s (MvPolynomial.support_map_subset _ _ hs)
    have hI := hint_logInt_tail hn hq0' hq' hm0 0
    have heq : ∀ w, d.evT sg 0 (d.tOf w) q =
        MvPolynomial.eval (hintPt 0 w) (MvPolynomial.map sg q) := by
      intro w
      rw [MvPolynomial.eval_map]
      rfl
    have hI' : Integrable (fun w => Real.log ‖d.evT sg 0 (d.tOf w) q‖)
        (ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1)) := by
      simp only [heq]
      exact hI
    refine ⟨?_, hI'⟩
    have hpt : ∀ z : ReciprocityTheory.MultiplicativeHeights.BlockSphere (d.D + 1) (d.N + 1),
        Real.log ‖MvPolynomial.eval (ReciprocityTheory.MultiplicativeHeights.blockPoint z) (MvPolynomial.map sg q)‖ =
          Real.log ‖d.evT sg 0 (d.tOf (fun i : Fin d.D => z i.succ)) q‖ := by
      intro z
      have h1 : MvPolynomial.eval (ReciprocityTheory.MultiplicativeHeights.blockPoint z) (MvPolynomial.map sg q) =
          d.evT sg (fun j => ReciprocityTheory.MultiplicativeHeights.spherePoint (z 0) j)
            (d.tOf (fun i : Fin d.D => z i.succ)) q := by
        rw [MvPolynomial.eval_map]
        unfold evT
        congr 1
        funext v
        rcases v with ⟨b, j⟩
        cases b using Fin.cases with
        | zero => rfl
        | succ i => rfl
      rw [h1, d.eval_indep_of_first_block q m hm0 hq sg]
    unfold ReciprocityTheory.MultiplicativeHeights.blockSphereMean
    simp only [hpt]
    have h2 := MeasureTheory.integral_map (μ := ReciprocityTheory.MultiplicativeHeights.blockSphereProb (d.D + 1) (d.N + 1))
      hmp.measurable.aemeasurable (f := fun w => Real.log ‖d.evT sg 0 (d.tOf w) q‖)
      (by rw [hmp.map_eq]; exact hI'.aestronglyMeasurable)
    rw [hmp.map_eq] at h2
    exact h2.symm
  obtain ⟨ha1, ha2⟩ := key a ha hma
  obtain ⟨hb1, hb2⟩ := key b hb hmb
  rw [ha1, hb1, ← integral_sub ha2 hb2]
  rfl

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.DiscProduct

section

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField ReciprocityTheory.ChartRestriction.G.T0.HeightMultiplicativity

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem disc_product (hd : d.AxH 𝒜) (h : d.S1) (hI2be : d.HeightIntegralBoundEstimate) (a b : KTp K d.D d.N)
    (hab : d.IsPres hd h a b) (Om : KTp K d.D d.N)
    (hOm : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) Om = d.omE hd h) :
    (Function.support fun la => d.gOrd la (d.De hd h)).Finite ∧
    (Function.support fun la => d.NlaG h d.wF hd.a4.choose la).Finite ∧
    (∑ᶠ la, ((d.gOrd la (d.De hd h) : ℝ) + 2 * d.NlaG h d.wF hd.a4.choose la) * logNorm la) /
        (Module.finrank ℚ K : ℝ) =
      meanK (fun sg => d.mSgP sg a b - 2 * d.Nsg d.wF hd.a4.choose sg) -
        ReciprocityTheory.MultiplicativeHeights.h0 Om + 2 * d.Hgt h d.wF hd.a4.choose := by
  classical
  set e := hd.a4.choose with hedef
  have he := hd.a4.choose_spec.1
  obtain ⟨hb0, hab', m, hm0, hma, hmb⟩ := hab
  have hDe : d.De hd h ≠ 0 := (d.disc_lattice hd h).1
  have hinj := IsFractionRing.injective (KTp K d.D d.N) (KTf K d.D d.N)
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at hab'
    exact mul_ne_zero hDe ((map_ne_zero_iff _ hinj).2 hb0) hab'.symm
  have hn : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have hcard : (Fintype.card (K →+* ℂ) : ℝ) = Module.finrank ℚ K := by
    exact_mod_cast NumberField.Embeddings.card K ℂ

  have hla : ∀ la, Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs (FinitePlace.mk la) a) -
      Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs (FinitePlace.mk la) b) =
        -((d.gOrd la (d.De hd h) : ℝ) * logNorm la) :=
    fun la => d.log_gaussAbs_sub_of_fraction la a b ha0 hb0 _ hab'
  have hlog : ∀ la : IsDedekindDomain.HeightOneSpectrum (𝓞 K), logNorm la ≠ 0 := fun la => by
    have h1 := NumberField.HeightOneSpectrum.one_lt_absNorm la
    exact (Real.log_pos (by exact_mod_cast h1)).ne'
  have hgfin : (Function.support fun la => d.gOrd la (d.De hd h)).Finite := by
    refine (((ReciprocityTheory.MultiplicativeHeights.gauss_abs_log_support_finite a ha0).union
      (ReciprocityTheory.MultiplicativeHeights.gauss_abs_log_support_finite b hb0)).preimage
      (FinitePlace.equivHeightOneSpectrum (K := K)).symm.injective.injOn).subset ?_
    intro la hla0
    have h1 : Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs (FinitePlace.mk la) a) -
        Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs (FinitePlace.mk la) b) ≠ 0 := by
      rw [hla]
      exact neg_ne_zero.2 (mul_ne_zero (by exact_mod_cast hla0) (hlog la))
    by_contra hn'
    apply h1
    simp only [Set.mem_preimage, Set.mem_union, Function.mem_support, not_or, not_not] at hn'
    change Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs (FinitePlace.mk la) a) = 0 ∧
      Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs (FinitePlace.mk la) b) = 0 at hn'
    rw [hn'.1, hn'.2, sub_zero]
  have hNfin : (Function.support fun la => d.NlaG h d.wF e la).Finite :=
    (Set.finite_iUnion fun c => d.la_fin hd h c (fun v => d.ord c v d.wF (e c))
      (hd.a3' c (he c).1 (he c).2)).subset (d.aNla_supp hd h (fun c v f => d.ord c v d.wF f) e)
  refine ⟨hgfin, hNfin, ?_⟩

  obtain ⟨U, V, hU0, hV0, ⟨eU, hUm⟩, ⟨eV, hVm⟩, hpres, hh0f⟩ := d.finite_height_fraction_repr hd h
  have hpoly : Om * (b * V ^ 2) = a * U ^ 2 := by
    apply hinj
    simp only [map_mul, map_pow]
    rw [hOm, omE, hab', ← hpres]
    ring
  have hOm0 : Om ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hpoly
    exact mul_ne_zero ha0 (pow_ne_zero _ hU0) hpoly.symm
  have hnp : 0 < d.N + 1 := Nat.succ_pos _
  have E1 : ReciprocityTheory.MultiplicativeHeights.h0 Om = ReciprocityTheory.MultiplicativeHeights.h0 a + 2 * ReciprocityTheory.MultiplicativeHeights.h0 U -
      (ReciprocityTheory.MultiplicativeHeights.h0 b + 2 * ReciprocityTheory.MultiplicativeHeights.h0 V) := by
    rw [logHeight_div_multihomogeneous _ _ hOm0 (mul_ne_zero hb0 (pow_ne_zero _ hV0))
      (multi_mul hmb (multi_pow hVm 2)) (multi_mul hma (multi_pow hUm 2)) hpoly,
      (ReciprocityTheory.MultiplicativeHeights.Closed.gauss_height_additivity K (d.D + 1) (d.N + 1) _ _ a (U ^ 2) hnp ha0 (pow_ne_zero _ hU0) hma
        (multi_pow hUm 2)).1,
      (ReciprocityTheory.MultiplicativeHeights.Closed.gauss_height_additivity K (d.D + 1) (d.N + 1) _ _ b (V ^ 2) hnp hb0 (pow_ne_zero _ hV0) hmb
        (multi_pow hVm 2)).1,
      h0_pow_of_isMultiHomogeneous hnp hU0 hUm, h0_pow_of_isMultiHomogeneous hnp hV0 hVm]
    push_cast; ring
  have E2 : ReciprocityTheory.MultiplicativeHeights.h0 a - ReciprocityTheory.MultiplicativeHeights.h0 b =
      (-(∑ᶠ la, (d.gOrd la (d.De hd h) : ℝ) * logNorm la) + ∑ sg, d.mSgP sg a b) /
        (Module.finrank ℚ K : ℝ) := by
    have hfinp : (∑ᶠ w : FinitePlace K, Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs w a)) -
        ∑ᶠ w : FinitePlace K, Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs w b) =
        -(∑ᶠ la, (d.gOrd la (d.De hd h) : ℝ) * logNorm la) := by
      rw [← finsum_sub_distrib (ReciprocityTheory.MultiplicativeHeights.gauss_abs_log_support_finite a ha0)
        (ReciprocityTheory.MultiplicativeHeights.gauss_abs_log_support_finite b hb0)]
      have := finsum_comp_equiv (FinitePlace.equivHeightOneSpectrum (K := K)).symm
        (f := fun w => Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs w a) - Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs w b))
      rw [← this, ← finsum_neg_distrib]
      exact finsum_congr fun la => hla la
    have harch : ∑ sg : K →+* ℂ, ReciprocityTheory.MultiplicativeHeights.blockSphereMean (d.D + 1) (d.N + 1) (MvPolynomial.map sg a) -
        ∑ sg : K →+* ℂ, ReciprocityTheory.MultiplicativeHeights.blockSphereMean (d.D + 1) (d.N + 1) (MvPolynomial.map sg b) =
        ∑ sg, d.mSgP sg a b := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun sg _ => d.sphereMean_sub_archimedean a b m hm0 ha0 hb0 hma hmb sg
    unfold ReciprocityTheory.MultiplicativeHeights.h0
    rw [← hfinp, ← harch]
    ring
  have E4 : meanK (fun sg => d.mSgP sg a b - 2 * d.Nsg d.wF e sg) =
      (∑ sg, d.mSgP sg a b) / (Module.finrank ℚ K : ℝ) - 2 * meanK (d.Nsg d.wF e) := by
    unfold meanK
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hcard]
    ring
  have hsG : (Function.support fun la => (d.gOrd la (d.De hd h) : ℝ) * logNorm la).Finite :=
    hgfin.subset fun la hla0 => by
      intro h0; apply hla0; simp [h0]
  have hsN : (Function.support fun la => d.NlaG h d.wF e la * logNorm la).Finite :=
    hNfin.subset fun la hla0 => by
      intro h0; apply hla0; simp [h0]
  have E5 : (∑ᶠ la, ((d.gOrd la (d.De hd h) : ℝ) + 2 * d.NlaG h d.wF e la) * logNorm la) =
      (∑ᶠ la, (d.gOrd la (d.De hd h) : ℝ) * logNorm la) +
        2 * ∑ᶠ la, d.NlaG h d.wF e la * logNorm la := by
    rw [mul_finsum, ← finsum_add_distrib hsG (hsN.subset fun la hla0 => by
      intro h0; apply hla0; simp [h0])]
    exact finsum_congr fun la => by ring
  rw [E5, E4, Hgt, hh0f]
  have hn0 : (Module.finrank ℚ K : ℝ) ≠ 0 := hn.ne'
  linear_combination E1 + E2

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end
end
