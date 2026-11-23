module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.Letter
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GlTwoPosRatMobiusBasicLaws
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GlTwoPosRatMobiusBasicLaws
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.Gamma1CapGamma0LevelActsFreelyUpperHalfPlane

section

@[expose] public section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups

namespace GlobalTheory.KZ.FreeAct

theorem ent_ofSL (γ : SL(2, ℤ)) (i j : Fin 2) :
    ent (ofSL γ) i j = ((γ : Matrix (Fin 2) (Fin 2) ℤ) i j : ℚ) := by
  simp [ent, ofSL]

theorem key (a b c d x y : ℝ) (h1 : a - d = 2 * c * x) (h2 : c * (x ^ 2 - y ^ 2) + (d - a) * x - b = 0)
    (hdet : a * d - b * c = 1) : 4 * c ^ 2 * y ^ 2 = 4 - (a + d) ^ 2 := by
  linear_combination (-4 * c) * h2 + 4 * hdet + (a - d - 2 * c * x) * h1

theorem no_small (N : ℕ) (hN : 4 ≤ N) (t k : ℤ) (hk : t - 2 = (N : ℤ) * k) (ht : t ^ 2 < 4) : False := by
  have h1 : -1 ≤ t := by nlinarith
  have h2 : t ≤ 1 := by nlinarith
  have hN' : (4 : ℤ) ≤ N := by exact_mod_cast hN
  rcases lt_trichotomy k 0 with hk0 | hk0 | hk0
  · nlinarith
  · subst hk0; omega
  · nlinarith

end GlobalTheory.KZ.FreeAct

namespace GlobalTheory.KZ


open FreeAct in
theorem gam_free : ∀ (N l : ℕ), 4 ≤ N → ∀ γ ∈ Gam N l, ∀ z ∈ Hs, mob (ofSL γ) z = z → γ = 1 := by
  intro N l hN γ hγ z hz hfix
  have hγ1 : γ ∈ CongruenceSubgroup.Gamma1 N := hγ.1
  rw [CongruenceSubgroup.Gamma1_mem] at hγ1
  obtain ⟨ha1, hd1, -⟩ := hγ1
  set A := (γ : Matrix (Fin 2) (Fin 2) ℤ) with hA
  have hdet : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
    have := γ.2; rw [Matrix.det_fin_two] at this; exact this
  have hden := GlobalTheory.KZ.MobLaws.den_ne (ofSL γ) hz
  simp only [ent_ofSL] at hden
  unfold mob at hfix
  simp only [ent_ofSL] at hfix
  rw [div_eq_iff hden] at hfix
  have hy : 0 < z.im := hz
  have hre := congrArg Complex.re hfix
  have him := congrArg Complex.im hfix
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.intCast_re,
    Complex.intCast_im, Complex.ratCast_re, Complex.ratCast_im] at hre him
  push_cast at hre him
  simp at hre him
  obtain ⟨k, hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub 1 (A 0 0) N).1 (by simpa using ha1.symm)
  obtain ⟨m, hm⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub 1 (A 1 1) N).1 (by simpa using hd1.symm)
  have hN' : (4 : ℤ) ≤ N := by exact_mod_cast hN
  simp only [← hA] at hre him
  generalize e00 : A 0 0 = a at *
  generalize e01 : A 0 1 = b at *
  generalize e10 : A 1 0 = c at *
  generalize e11 : A 1 1 = d at *
  have h1 : (a : ℝ) - d = 2 * c * z.re := by
    have : ((a : ℝ) - d - 2 * c * z.re) * z.im = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · linarith
  have h2 : (c : ℝ) * (z.re ^ 2 - z.im ^ 2) + (d - a) * z.re - b = 0 := by linarith
  have hdetR : (a : ℝ) * d - b * c = 1 := by exact_mod_cast hdet
  have hk4 := key a b c d z.re z.im h1 h2 hdetR
  by_cases hc : c = 0
  · subst hc
    have had : a = d := by
      have : (a : ℝ) = d := by simp at h1; linarith
      exact_mod_cast this
    subst had
    have hb : b = 0 := by
      have : (b : ℝ) = 0 := by simpa using h2
      exact_mod_cast this
    subst hb
    have haa : a * a = 1 := by simpa using hdet
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' haa with ⟨ha, -⟩ | ⟨ha, -⟩
    · subst ha
      ext i j
      fin_cases i <;> fin_cases j <;> simp [← hA, e00, e01, e10, e11]
    · exfalso
      subst ha
      rcases lt_trichotomy k 0 with hk0 | hk0 | hk0
      · nlinarith
      · subst hk0; omega
      · nlinarith
  · exfalso
    have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast hc
    have hpos : 0 < 4 * (c : ℝ) ^ 2 * z.im ^ 2 := by positivity
    have ht : (a + d) ^ 2 < 4 := by
      have : ((a : ℝ) + d) ^ 2 < 4 := by linarith
      exact_mod_cast this
    exact no_small N hN (a + d) (k + m) (by linear_combination hk + hm) ht

end GlobalTheory.KZ
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.Gamma1CapGamma0LevelActsFreelyUpperHalfPlaneStatement

section

@[expose] public section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups

theorem _root_.GlobalTheory.T.gamma1CapGamma0Level_acts_freely_upperHalfPlane : ∀ (N l : ℕ), 4 ≤ N → ∀ γ ∈ Gam N l, ∀ z ∈ Hs, mob (ofSL γ) z = z → γ = 1 := by
  first | exact @GlobalTheory.KZ.gam_free | exact GlobalTheory.KZ.gam_free | (intros; apply GlobalTheory.KZ.gam_free <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsEichlerShimuraPotentialOfHomogeneousPolyCo

section

@[expose] public section

noncomputable section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups

namespace GlobalTheory.KZ.H3.PotCoc

def orbSetoid (Γ : Subgroup SL(2, ℤ)) : Setoid Hs where
  r a b := ∃ γ ∈ Γ, mob (ofSL γ) a.1 = b.1
  iseqv := by
    obtain ⟨-, hmul, hone, -⟩ := GlobalTheory.KZ.mob_laws
    refine ⟨fun a => ⟨1, Γ.one_mem, by simp [hone]⟩, ?_, ?_⟩
    · rintro a b ⟨γ, hγ, h⟩
      refine ⟨γ⁻¹, Γ.inv_mem hγ, ?_⟩
      rw [← h, ← hmul _ _ _ a.2, ← map_mul, inv_mul_cancel, map_one, hone]
    · rintro a b c ⟨γ, hγ, h⟩ ⟨δ, hδ, h'⟩
      refine ⟨δ * γ, Γ.mul_mem hδ hγ, ?_⟩
      rw [map_mul, hmul _ _ _ a.2, h, h']

def rep (Γ : Subgroup SL(2, ℤ)) (a : Hs) : Hs := (Quotient.mk (orbSetoid Γ) a).out

theorem rep_rel (Γ : Subgroup SL(2, ℤ)) (a : Hs) : ∃ γ ∈ Γ, mob (ofSL γ) (rep Γ a).1 = a.1 :=
  Quotient.mk_out (s := orbSetoid Γ) a


open Classical in
def gel (Γ : Subgroup SL(2, ℤ)) (τ : ℂ) : SL(2, ℤ) :=
  if h : τ ∈ Hs then (rep_rel Γ ⟨τ, h⟩).choose else 1

theorem gel_spec (Γ : Subgroup SL(2, ℤ)) {τ : ℂ} (h : τ ∈ Hs) :
    gel Γ τ ∈ Γ ∧ mob (ofSL (gel Γ τ)) (rep Γ ⟨τ, h⟩).1 = τ := by
  simp only [gel, dif_pos h]
  exact (rep_rel Γ ⟨τ, h⟩).choose_spec

theorem rep_eq (Γ : Subgroup SL(2, ℤ)) {δ : SL(2, ℤ)} (hδ : δ ∈ Γ) {τ : ℂ} (h : τ ∈ Hs)
    (h' : mob (ofSL δ) τ ∈ Hs) : rep Γ ⟨mob (ofSL δ) τ, h'⟩ = rep Γ ⟨τ, h⟩ := by
  unfold rep
  congr 1
  exact Quotient.sound (s := orbSetoid Γ) ⟨δ⁻¹, Γ.inv_mem hδ, by
    obtain ⟨-, hmul, hone, -⟩ := GlobalTheory.KZ.mob_laws
    show mob (ofSL δ⁻¹) (mob (ofSL δ) τ) = τ
    rw [← hmul _ _ _ h, ← map_mul, inv_mul_cancel, map_one, hone]⟩

theorem slPS {R : Type} [CommRing R] (a c : SL(2, ℤ)) (p : MvPolynomial (Fin 2) R) :
    slP (c : Matrix (Fin 2) (Fin 2) ℤ) (slP (a : Matrix (Fin 2) (Fin 2) ℤ) p) =
      slP ((a * c : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) p := by
  rw [GlobalTheory.KZ.Betti.polySlash_polySlash, Matrix.SpecialLinearGroup.coe_mul]

def potOf {R : Type} [CommRing R] (Γ : Subgroup SL(2, ℤ)) (z : SL(2, ℤ) → MvPolynomial (Fin 2) R) (τ : ℂ) :
    MvPolynomial (Fin 2) R :=
  slP (((gel Γ τ)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) (z (gel Γ τ))

end GlobalTheory.KZ.H3.PotCoc


open GlobalTheory.KZ.H3.PotCoc GlobalTheory.KZ.Betti in
theorem GlobalTheory.KZ.H3.exists_pot_of_isCoc : ∀ (R : Type) [CommRing R] (w N l : ℕ), 4 ≤ N →
    ∀ z : SL(2, ℤ) → MvPolynomial (Fin 2) R, IsCoc w (Gam N l) z → ∃ F ∈ Pot R w (Gam N l),
      ∀ γ ∈ Gam N l, ∀ τ ∈ Hs, slP (γ : Matrix (Fin 2) (Fin 2) ℤ) (F (mob (ofSL γ) τ)) - F τ = z γ := by
  intro R _ w N l hN z hz
  obtain ⟨hmem, hmul, hone, -⟩ := GlobalTheory.KZ.mob_laws
  set Γ := Gam N l
  have key : ∀ γ ∈ Γ, ∀ τ ∈ Hs, slP (γ : Matrix (Fin 2) (Fin 2) ℤ) (potOf Γ z (mob (ofSL γ) τ)) - potOf Γ z τ = z γ := by
    intro δ hδ τ hτ
    have hτ' : mob (ofSL δ) τ ∈ Hs := hmem _ _ hτ
    obtain ⟨hg1, hg2⟩ := gel_spec Γ hτ
    obtain ⟨hg1', hg2'⟩ := gel_spec Γ hτ'
    rw [rep_eq Γ hδ hτ hτ'] at hg2'
    set g := gel Γ τ
    set g' := gel Γ (mob (ofSL δ) τ)
    have hg : g' = δ * g := by
      have hfree := GlobalTheory.T.gamma1CapGamma0Level_acts_freely_upperHalfPlane N l hN (g'⁻¹ * (δ * g)) (Γ.mul_mem (Γ.inv_mem hg1') (Γ.mul_mem hδ hg1))
        _ (rep Γ ⟨τ, hτ⟩).2 (by
          rw [map_mul, hmul _ _ _ (rep Γ ⟨τ, hτ⟩).2, map_mul, hmul _ _ _ (rep Γ ⟨τ, hτ⟩).2, hg2, ← hg2',
            ← hmul _ _ _ (rep Γ ⟨τ, hτ⟩).2, ← map_mul, inv_mul_cancel, map_one, hone])
      exact (inv_mul_eq_one.mp hfree)
    show slP (δ : Matrix (Fin 2) (Fin 2) ℤ) (slP ((g'⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) (z g')) -
      slP ((g⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) (z g) = z δ
    rw [hg, (hz.2 δ hδ g hg1)]
    have e1 : (δ * g)⁻¹ * δ = g⁻¹ := by group
    have e2 : g * (δ * g)⁻¹ * δ = 1 := by rw [mul_assoc, e1]; group
    simp only [map_add (f := _), slPS, e1, e2, Matrix.SpecialLinearGroup.coe_one, polySlash_one]
    abel
  refine ⟨potOf Γ z, ⟨fun τ => ?_, fun γ hγ => ⟨z γ, key γ hγ⟩⟩, key⟩
  by_cases hτ : τ ∈ Hs
  · exact polySlash_isHomogeneous _ (hz.1 _ (gel_spec Γ hτ).1)
  · have : gel Γ τ = 1 := by simp [gel, dif_neg hτ]
    unfold potOf
    rw [this]
    exact polySlash_isHomogeneous _ (hz.1 _ Γ.one_mem)
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsEichlerShimuraPotentialOfHomogeneousPolyCoStatement

section

@[expose] public section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups

theorem _root_.GlobalTheory.T.exists_eichlerShimuraPotential_of_homogeneousPolyCocycle : ∀ (R : Type) [CommRing R] (w N l : ℕ), 4 ≤ N → ∀ z : SL(2, ℤ) → MvPolynomial (Fin 2) R, IsCoc w (Gam N l) z → ∃ F ∈ Pot R w (Gam N l), ∀ γ ∈ Gam N l, ∀ τ ∈ Hs, slP (γ : Matrix (Fin 2) (Fin 2) ℤ) (F (mob (ofSL γ) τ)) - F τ = z γ := by
  first | exact @GlobalTheory.KZ.H3.exists_pot_of_isCoc | exact GlobalTheory.KZ.H3.exists_pot_of_isCoc | (intros; apply GlobalTheory.KZ.H3.exists_pot_of_isCoc <;> assumption)
end
end
