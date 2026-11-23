module

public import Formalism.ThetaLogCoordinates.SandwichModelDomains.SpreadSquare
import Formalism.ThetaLogCoordinates.SandwichModelDomains.SpreadSquare
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FinalC
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LDlatLemmas
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FinalB
import Formalism.GradedWeylDivisibility.FinalD
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LClosedeqLemmas
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
public import Formalism.ThetaLogCoordinates.SandwichModelDomains.SandwichModelProofs.GlFirstLineDividedPowers
public import Formalism.ThetaLogCoordinates.SandwichModelDomains.SandwichModelProofs.Spread
import Formalism.ThetaLogCoordinates.SandwichModelDomains.SandwichModelProofs.SwappedHighestWeightNeZero
import Mathlib.RingTheory.SimpleRing.Principal

-- Source module: Formalism.ThetaLogCoordinates.SandwichModelDomains.SandwichModelProofs.Ascent

section

section

open MvPolynomial

namespace Formalism.InvariantFactorPaths.INST

open Formalism.GradedWeylDivisibility

theorem asc_map_weyl (O : Type) [CommRing O] {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ)
    (f : MvPolynomial (Fin r × Fin n) ℤ) (hf : f ∈ weyl ℤ r n hn ν) :
    map (Int.castRingHom O) f ∈ weyl O r n hn ν := by
  set φ : ℤ →+* O := Int.castRingHom O with hφ
  have hrow : ∀ (a b : Fin r) (g : MvPolynomial (Fin r × Fin n) ℤ),
      rowGen O a b (map φ g) = Polynomial.map (map φ) (rowGen ℤ a b g) := by
    intro a b g
    have key : ((rowGen O a b).toRingHom.comp (map φ) :
          MvPolynomial (Fin r × Fin n) ℤ →+* Polynomial (MvPolynomial (Fin r × Fin n) O)) =
        (Polynomial.mapRingHom (map φ)).comp (rowGen ℤ a b).toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro c
        rw [← RingHom.comp_apply, eq_intCast, ← RingHom.comp_apply, eq_intCast]
      · intro v
        simp only [RingHom.comp_apply]
        (simp [rowGen]) <;> (try split_ifs) <;> (try simp)
    exact RingHom.congr_fun key g
  have hdiv : ∀ (a b : Fin r) (k : ℕ) (g : MvPolynomial (Fin r × Fin n) ℤ),
      map φ (rowDiv ℤ a b k g) = rowDiv O a b k (map φ g) := by
    intro a b k g
    unfold rowDiv
    rw [hrow, Polynomial.coeff_map]
  have hword : ∀ (w : List (Fin r × Fin r × ℕ)) (g : MvPolynomial (Fin r × Fin n) ℤ),
      map φ (applyWord ℤ w g) = applyWord O w (map φ g) := by
    intro w g
    induction w with
    | nil => rfl
    | cons x w ih =>
      show map φ (rowDiv ℤ x.1 x.2.1 x.2.2 (applyWord ℤ w g)) =
        rowDiv O x.1 x.2.1 x.2.2 (applyWord O w (map φ g))
      rw [hdiv, ih]
  have hhw : map φ (hw ℤ hn ν) = hw O hn ν := by
    unfold hw
    rw [map_prod]
    refine Finset.prod_congr rfl (fun s _ => ?_)
    rw [map_pow]
    congr 1
    unfold lpMinor
    rw [RingHom.map_det]
    congr 1
    ext i j
    simp [RingHom.mapMatrix_apply, Matrix.map_apply]
  unfold weyl at hf ⊢
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    refine Submodule.subset_span ⟨w, ?_⟩
    try dsimp only
    rw [hword, hhw]
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add (f := _)]
    exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [map_zsmul]
    first
      | exact zsmul_mem hx c
      | exact Submodule.smul_of_tower_mem _ c hx

theorem ascent_domain_holds : AscentDomain := by
  intro p r n hn ν e h O _ _ hO x hx
  rw [standardMonomialSpanDomain O r n ν] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨K, sz, hsz, I, hsh, rfl⟩ := hy
    have hZ : bideterminant ℤ sz hsz I ∈ dualWeyl ℤ r n ν := by
      rw [← hsh]; exact bidetMem ℤ r n K sz hsz I
    obtain ⟨c, hc, hm⟩ := h _ hZ
    have h2 := asc_map_weyl O hn ν _ hm
    have e2 : map (Int.castRingHom O) ((c * (p : ℤ) ^ e) • bideterminant ℤ sz hsz I) =
        ((c : ℤ) : O) • (((p : O) ^ e) • bideterminant O sz hsz I) := by
      rw [smul_eq_C_mul, map_mul, map_C, ldlat_map_bidet, smul_smul, smul_eq_C_mul]
      simp
    rw [e2] at h2
    obtain ⟨u, hu⟩ := hO c hc
    have h3 := Submodule.smul_mem _ ((u⁻¹ : Oˣ) : O) h2
    rwa [smul_smul, ← hu, Units.inv_mul, one_smul] at h3
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [smul_add]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy => rw [smul_comm]; exact Submodule.smul_mem _ _ hy

end Formalism.InvariantFactorPaths.INST
end
end

-- Source module: Formalism.ThetaLogCoordinates.SandwichModelDomains.SandwichModelProofs.Assemble

section

@[expose] public section

open MvPolynomial

namespace Formalism.InvariantFactorPaths.INST

open Formalism.GradedWeylDivisibility

theorem sandwichDomain_of (h : SandwichZ) (hA : AscentDomain) : SandwichDomain := by
  intro p _ r n hn ν hν l hl O _ _ hO
  exact ⟨hA p r n hn ν _ (h p r n hn ν hν l hl) O hO, weylLeDual O r n hn ν hν⟩

end Formalism.InvariantFactorPaths.INST
end
end

-- Source module: Formalism.ThetaLogCoordinates.SandwichModelDomains.SandwichModelProofs.Descent

section

section

open MvPolynomial

noncomputable section

namespace Formalism.InvariantFactorPaths.INST

open Formalism.GradedWeylDivisibility

theorem dsc_denominator (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ) (hν : Antitone ν) :
    ∃ N : ℤ, N ≠ 0 ∧ ∀ g ∈ dualWeyl ℤ r n ν, N • g ∈ weyl ℤ r n hn ν := by
  obtain ⟨b, ⟨_, hspan, _⟩, _⟩ := sSBasis ℤ r n ν
  have : Fintype (ssIdx r n ν) := (sSIdxFinite r n ν).fintype
  have hb : ∀ i, b i ∈ dualWeyl ℤ r n ν := fun i => hspan ▸ Submodule.subset_span ⟨i, rfl⟩
  choose c hc0 hc using fun i => weylRational r n hn ν hν (b i) (hb i)
  refine ⟨∏ i, c i, Finset.prod_ne_zero_iff.mpr fun i _ => hc0 i, fun g hg => ?_⟩
  rw [← hspan] at hg
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    rw [← Finset.mul_prod_erase Finset.univ c (Finset.mem_univ i), mul_comm, mul_smul]
    exact Submodule.smul_mem _ _ (hc i)
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ _ hx

theorem dsc_split (p : ℕ) [hp : Fact p.Prime] (N : ℤ) (hN : N ≠ 0) :
    ∃ (k : ℕ) (c : ℤ), N = (p : ℤ) ^ k * c ∧ ¬ (p : ℤ) ∣ c := by
  have hfin : FiniteMultiplicity (p : ℤ) N :=
    Int.finiteMultiplicity_iff.mpr ⟨by simpa using hp.out.ne_one, hN⟩
  obtain ⟨c, h1, h2⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  exact ⟨_, c, h1, h2⟩

theorem dsc_approx (p : ℕ) [Fact p.Prime] (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ) (k : ℕ)
    (y : MvPolynomial (Fin r × Fin n) ℤ_[p]) (hy : y ∈ weyl ℤ_[p] r n hn ν) :
    ∃ d ∈ weyl ℤ r n hn ν, ∃ z : MvPolynomial (Fin r × Fin n) ℤ_[p],
      y = map (Int.castRingHom ℤ_[p]) d + ((p : ℤ_[p]) ^ k) • z := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    refine ⟨applyWord ℤ w (hw ℤ hn ν), Submodule.subset_span ⟨w, rfl⟩, 0, ?_⟩
    simp only [smul_zero, add_zero]
    rw [← lclosedeq_applyWord_map, lclosedeq_hw_map]
  | zero => exact ⟨0, Submodule.zero_mem _, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨d1, hd1, z1, rfl⟩ := hx
    obtain ⟨d2, hd2, z2, rfl⟩ := hy
    refine ⟨d1 + d2, Submodule.add_mem _ hd1 hd2, z1 + z2, ?_⟩
    rw [map_add (f := _), smul_add]; abel
  | smul a x _ hx =>
    obtain ⟨d, hd, z, rfl⟩ := hx
    obtain ⟨a', ha'⟩ := Ideal.mem_span_singleton.mp (PadicInt.appr_spec k a)
    have ha : a = ((PadicInt.appr a k : ℕ) : ℤ_[p]) + (p : ℤ_[p]) ^ k * a' := by
      rw [← ha']; ring
    refine ⟨((PadicInt.appr a k : ℕ) : ℤ) • d, Submodule.smul_mem _ _ hd,
      a' • map (Int.castRingHom ℤ_[p]) d + a • z, ?_⟩
    have hm : map (Int.castRingHom ℤ_[p]) (((PadicInt.appr a k : ℕ) : ℤ) • d) =
        ((PadicInt.appr a k : ℕ) : ℤ_[p]) • map (Int.castRingHom ℤ_[p]) d := by
      rw [smul_eq_C_mul, smul_eq_C_mul, map_mul, map_C]; simp
    have h1 : a • map (Int.castRingHom ℤ_[p]) d =
        ((PadicInt.appr a k : ℕ) : ℤ_[p]) • map (Int.castRingHom ℤ_[p]) d +
          ((p : ℤ_[p]) ^ k * a') • map (Int.castRingHom ℤ_[p]) d := by
      rw [← add_smul, ← ha]
    rw [hm, smul_add, smul_add, smul_smul, smul_smul, smul_smul, mul_comm a, h1, add_assoc]

theorem dsc_divide (p : ℕ) [Fact p.Prime] {σ : Type*} (k : ℕ) (g : MvPolynomial σ ℤ)
    (z : MvPolynomial σ ℤ_[p]) (h : map (Int.castRingHom ℤ_[p]) g = ((p : ℤ_[p]) ^ k) • z) :
    ∃ g1 : MvPolynomial σ ℤ, g = ((p : ℤ) ^ k) • g1 := by
  have hd : C ((p : ℤ) ^ k) ∣ g := by
    rw [C_dvd_iff_dvd_coeff]
    intro m
    rw [← PadicInt.pow_p_dvd_int_iff]
    have := congrArg (AddMonoidAlgebra.coeff · m) h
    rw [coeff_map, MvPolynomial.coeff_smul] at this
    exact ⟨AddMonoidAlgebra.coeff z m, by simpa using this⟩
  obtain ⟨g1, rfl⟩ := hd
  exact ⟨g1, by rw [smul_eq_C_mul]⟩

theorem descent_over_integers : DescentZ := by
  intro p _ r n hn ν hν e hyp f hf
  obtain ⟨N, hN0, hN⟩ := dsc_denominator r n hn ν hν
  obtain ⟨k, c, hNc, hc⟩ := dsc_split p N hN0
  have hmf : map (Int.castRingHom ℤ_[p]) f ∈ dualWeyl ℤ_[p] r n ν :=
    dualWeylMap ℤ ℤ_[p] (Int.castRingHom ℤ_[p]) r n ν f hf
  obtain ⟨d, hd, z, hz⟩ := dsc_approx p r n hn ν k _ (hyp _ hmf)
  have hmap : map (Int.castRingHom ℤ_[p]) (((p : ℤ) ^ e) • f - d) = ((p : ℤ_[p]) ^ k) • z := by
    rw [map_sub, smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul]
    have : (Int.castRingHom ℤ_[p]) ((p : ℤ) ^ e) = (p : ℤ_[p]) ^ e := by simp
    rw [this, hz]; abel
  obtain ⟨g1, hg1⟩ := dsc_divide p k _ z hmap
  have hg0 : ((p : ℤ) ^ e) • f - d ∈ dualWeyl ℤ r n ν :=
    Submodule.sub_mem _ (Submodule.smul_mem _ _ hf) (weylLeDual ℤ r n hn ν hν hd)
  have hpk : ((p : ℤ) ^ k) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  have hg1m : g1 ∈ dualWeyl ℤ r n ν := dualWeylSat ℤ r n ν _ g1 hpk (hg1 ▸ hg0)
  refine ⟨c, hc, ?_⟩
  have key : (c * (p : ℤ) ^ e) • f = c • d + N • g1 := by
    rw [hNc, mul_comm ((p : ℤ) ^ k) c, mul_smul, mul_smul, ← hg1, smul_sub]; abel
  rw [key]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ hd) (hN g1 hg1m)

end Formalism.InvariantFactorPaths.INST
end
end
end

-- Source module: Formalism.ThetaLogCoordinates.SandwichModelDomains.FinalW

section

@[expose] public section

namespace Formalism.InvariantFactorPaths.INST.Top

theorem spreadTop : SpreadTop := spread_top_holds
theorem spreadSquare : SpreadSquare := spread_square_holds
theorem rowGlOne : RowGlOne := gl_one_first_line_action
theorem rowGlDiv : RowGlDiv := gl_first_line_divided_powers
theorem swpWt : SwpWt := swap_weight_compat
theorem swpPol : SwpPol := swap_polynomial_compat
theorem swpInt : SwpInt := swpInt_statement
theorem coreQp : CoreQp := coreQp_of rowGlOne rowGlDiv swpWt swpPol swpInt
theorem descentZ : DescentZ := descent_over_integers
theorem ascentDomain : AscentDomain := ascent_domain_holds
theorem unitsOfLocal : UnitsOfLocal := by
  intro p hp O _ _ hpu c hc
  by_contra hcu
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  have hcop : IsCoprime (p : ℤ) c := by
    first
    | exact (Irreducible.coprime_iff_not_dvd hpz.irreducible).2 hc
    | exact (Prime.coprime_iff_not_dvd hpz).2 hc
  obtain ⟨u, v, huv⟩ := hcop
  have h1 : (u : O) * (p : O) + (v : O) * (c : O) = 1 := by
    have := congrArg (fun z : ℤ => (z : O)) huv
    push_cast at this
    exact this
  have hmp : (p : O) ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).2 hpu
  have hmc : (c : O) ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).2 hcu
  have h1m : (1 : O) ∈ IsLocalRing.maximalIdeal O := by
    rw [← h1]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hmp) (Ideal.mul_mem_left _ _ hmc)
  exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 h1m)
theorem sandwichZp : SandwichZp := by
  intro p hp r n hn ν hν l hL x hx
  have hS : Spread (Padic p) r n ν l := by
    rcases hL with h | ⟨rfl, h⟩
    · exact spreadTop _ r n ν l h
    · exact spreadSquare _ _ ν l h
  exact coreQp p r n hn ν hν l hS x hx
theorem sandwichZ : SandwichZ := by
  intro p hp r n hn ν hν l hL f hf
  exact descentZ p r n hn ν hν (sExp p r l) (sandwichZp p r n hn ν hν l hL) f hf
theorem sandwichDomain : SandwichDomain := sandwichDomain_of sandwichZ ascentDomain
theorem sandwichLocal : SandwichLocal := by
  intro p hp r n hn ν hν l hL O _ _ _ hpu
  exact sandwichDomain p r n hn ν hν l hL O (unitsOfLocal p O hpu)

end Formalism.InvariantFactorPaths.INST.Top
end
end
