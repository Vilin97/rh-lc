module

public import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveStrongApproximationAvoidingFinsetStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalPureQuaternionSqOfAdelicStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrthogonalIdempotentsAdeleUnitCombinationStatement
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuaternionNormOneTraceOpenAdeles
import Mathlib.RingTheory.PiTensorProduct
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitIntertwinerAdelicQuaternion

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

namespace GlobalTheory.QSA

theorem nrm_smul_eq_sq_mul {R : Type*} [CommRing R] {a b : R} (t : R) (x : ℍ[R, a, b]) :
    nrm (t • x) = t ^ 2 * nrm x := by
  simp [nrm]; ring

theorem nrm_sum_orthIdem_smul {R : Type*} [CommRing R] {a b : R} {ι : Type} [Fintype ι] (η : ι → R)
    (y : ι → ℍ[R, a, b]) (h1 : ∀ i, η i * η i = η i) (h2 : ∀ i j, i ≠ j → η i * η j = 0)
    (h3 : ∑ i, η i = 1) : nrm (∑ i, η i • y i) = ∑ i, η i * nrm (y i) := by
  classical
  have key : ∀ i, η i * nrm (∑ j, η j • y j) = η i * nrm (y i) := by
    intro i
    have hs : η i • (∑ j, η j • y j) = η i • y i := by
      rw [Finset.smul_sum, Finset.sum_eq_single i]
      · rw [smul_smul, h1]
      · intro j _ hj
        rw [smul_smul, h2 i j (Ne.symm hj), zero_smul]
      · simp
    have := congrArg nrm hs
    rwa [nrm_smul_eq_sq_mul, nrm_smul_eq_sq_mul, sq, h1] at this
  calc nrm (∑ i, η i • y i) = ∑ i, η i * nrm (∑ j, η j • y j) := by
        rw [← Finset.sum_mul, h3, one_mul]
    _ = _ := Finset.sum_congr rfl fun i _ => key i

def quatStdBasis {R : Type*} [CommRing R] (a b : R) : Fin 4 → ℍ[R, a, b] :=
  ![⟨1, 0, 0, 0⟩, ⟨0, 1, 0, 0⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 1⟩]

theorem nrm_intertwiner_comb {R : Type*} [CommRing R] {a b c : R} (p q : ℍ[R, a, b]) (hp : p.re = 0) (hq : q.re = 0)
    (hpp : p * p = algebraMap R ℍ[R, a, b] c) (hqq : q * q = algebraMap R ℍ[R, a, b] c) :
    ∑ i, (![a * b, -b, -a, 1] : Fin 4 → R) i * nrm (p * quatStdBasis a b i + quatStdBasis a b i * q)
      = -8 * a * b * c := by
  have h1 := congrArg QuaternionAlgebra.re hpp
  have h2 := congrArg QuaternionAlgebra.re hqq
  simp [QuaternionAlgebra.algebraMap_eq, hp, hq] at h1 h2
  simp [Fin.sum_univ_four, quatStdBasis, nrm, hp, hq]
  linear_combination (-4 * a * b) * h1 + (-4 * a * b) * h2

theorem exists_unit_intertwiner : ∀ (F : Type) [Field F] [NumberField F] (a b : F), a ≠ 0 → b ≠ 0 → ∀ c : F, c ≠ 0 → ∀ p q : DA F a b, p.re = 0 → q.re = 0 → p * p = algebraMap (AF F) (DA F a b) (algebraMap F (AF F) c) → q * q = algebraMap (AF F) (DA F a b) (algebraMap F (AF F) c) → ∃ y : DA F a b, IsUnit (nrm y) ∧ y * q = p * y := by
  intro F _ _ a b ha hb c hc p q hp hq hpp hqq
  have hcomb := nrm_intertwiner_comb p q hp hq hpp hqq
  have hu : IsUnit (-8 * algebraMap F (AF F) a * algebraMap F (AF F) b * algebraMap F (AF F) c) := by
    have h : IsUnit (-8 * a * b * c) := by
      refine Ne.isUnit ?_
      have : (-8 : F) ≠ 0 := by norm_num
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero this ha) hb) hc
    have h' := h.map (algebraMap F (AF F))
    rwa [map_mul, map_mul, map_mul, map_neg, map_ofNat] at h'
  rw [← hcomb] at hu
  obtain ⟨η, h1, h2, h3, h4⟩ := GlobalTheory.T.exists_orthogonal_idempotents_adele_unit_combination F (Fin 4) _ _ hu
  refine ⟨∑ i, η i • (p * quatStdBasis _ _ i + quatStdBasis _ _ i * q), ?_, ?_⟩
  · rw [nrm_sum_orthIdem_smul η _ h1 h2 h3]; exact h4
  · rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_mul_assoc, mul_smul_comm]
    congr 1
    rw [add_mul, mul_add, mul_assoc _ q q, hqq, ← mul_assoc p p, hpp, add_comm, mul_assoc,
      Algebra.commutes]

end GlobalTheory.QSA
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitIntertwinerAdelicQuaternionStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

theorem _root_.GlobalTheory.T.exists_unit_intertwiner_adelicQuaternion : ∀ (F : Type) [Field F] [NumberField F] (a b : F), a ≠ 0 → b ≠ 0 → ∀ c : F, c ≠ 0 → ∀ p q : DA F a b, p.re = 0 → q.re = 0 → p * p = algebraMap (AF F) (DA F a b) (algebraMap F (AF F) c) → q * q = algebraMap (AF F) (DA F a b) (algebraMap F (AF F) c) → ∃ y : DA F a b, IsUnit (nrm y) ∧ y * q = p * y := by
  first | exact @GlobalTheory.QSA.exists_unit_intertwiner | exact GlobalTheory.QSA.exists_unit_intertwiner | (intros; apply GlobalTheory.QSA.exists_unit_intertwiner <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuaternionNormOneTraceOpenAdelesStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

theorem _root_.GlobalTheory.T.quaternion_norm_one_trace_open_adeles : ∀ (F : Type) [Field F] [NumberField F] (a b : F), a ≠ 0 → b ≠ 0 → ∀ g : DA F a b, nrm g = 1 → ∀ W : Set (DA F a b), W ∈ 𝓝 g → ∃ O : Set (AF F), IsOpen O ∧ O.Nonempty ∧ ∀ t ∈ O, ∃ u ∈ W, nrm u = 1 ∧ u.re = t := by
  first | exact @GlobalTheory.QSA.traceOpen_adele | exact GlobalTheory.QSA.traceOpen_adele | (intros; apply GlobalTheory.QSA.traceOpen_adele <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormOneQuaternionNearConjRationalTimesSupported

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

noncomputable section

namespace GlobalTheory.QSAStep

theorem idem_of_isPlacesIdem {F : Type} [Field F] [NumberField F] {S₁ : Finset (InfinitePlace F)}
    {S₂ : Finset (HeightOneSpectrum (𝓞 F))} {ε : AF F} (h : IsPlacesIdem S₁ S₂ ε) : ε * ε = ε := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine Prod.ext ?_ ?_
  · funext w
    change fstA F ε w * fstA F ε w = fstA F ε w
    by_cases hw : w ∈ S₁
    · rw [h1 w hw, one_mul]
    · rw [h2 w hw, zero_mul]
  · apply RestrictedProduct.ext
    intro v
    change evalV F v (sndA F ε) * evalV F v (sndA F ε) = evalV F v (sndA F ε)
    by_cases hv : v ∈ S₂
    · rw [h3 v hv, one_mul]
    · rw [h4 v hv, zero_mul]

variable {R : Type*} [CommRing R] {a b : R}

theorem nrm_split (x y : ℍ[R, a, b]) (e : R) (he : e * e = e) :
    nrm ((1 - e) • x + e • y) = (1 - e) * nrm x + e * nrm y := by
  simp only [nrm, QuaternionAlgebra.re_add, QuaternionAlgebra.imI_add, QuaternionAlgebra.imJ_add,
    QuaternionAlgebra.imK_add, QuaternionAlgebra.re_smul, QuaternionAlgebra.imI_smul, QuaternionAlgebra.imJ_smul,
    QuaternionAlgebra.imK_smul, smul_eq_mul]
  linear_combination ((x.re - y.re) ^ 2 - a * (x.imI - y.imI) ^ 2 - b * (x.imJ - y.imJ) ^ 2 +
    a * b * (x.imK - y.imK) ^ 2) * he

theorem nrm_star (x : ℍ[R, a, b]) : nrm (star x) = nrm x := by
  simp [nrm]

theorem nrm_one : nrm (1 : ℍ[R, a, b]) = 1 := by simp [nrm]

theorem pure_sq (u : ℍ[R, a, b]) (t : R) (hn : nrm u = 1) (hr : u.re = t) :
    (u - algebraMap R ℍ[R, a, b] t).re = 0 ∧
      (u - algebraMap R ℍ[R, a, b] t) * (u - algebraMap R ℍ[R, a, b] t) = algebraMap R ℍ[R, a, b] (t ^ 2 - 1) := by
  unfold nrm at hn
  refine ⟨by simp [hr], ?_⟩
  ext <;> simp [QuaternionAlgebra.algebraMap_eq, hr]
  · linear_combination (-1 : R) * hn + (u.re + t) * hr
  all_goals ring

end GlobalTheory.QSAStep

namespace GlobalTheory.QSAStep

variable {F : Type} [Field F] [NumberField F] {a b : F}

theorem rat_mul (x y : ℍ[F, a, b]) : rat (x * y) = rat x * rat y := by
  ext <;> simp [rat]

theorem rat_add (x y : ℍ[F, a, b]) : rat (x + y) = rat x + rat y := by
  ext <;> simp [rat]

theorem rat_algebraMap (c : F) :
    rat (algebraMap F ℍ[F, a, b] c) = algebraMap (AF F) (DA F a b) (algebraMap F (AF F) c) := by
  ext <;> simp [rat, QuaternionAlgebra.algebraMap_eq]

theorem continuous_affine (ε : AF F) :
    Continuous fun x : DA F a b => (1 - ε) • x + ε • (1 : DA F a b) := by
  apply continuous_induced_rng.2
  have e : (coords ∘ fun x : DA F a b => (1 - ε) • x + ε • (1 : DA F a b)) =
      fun x => (1 - ε) • coords x + coords (ε • (1 : DA F a b)) := by
    funext x i
    fin_cases i <;> simp [coords]
  rw [e]
  have hc : Continuous (coords : DA F a b → Fin 4 → AF F) := continuous_induced_dom
  exact ((continuous_const (y := (1 - ε : AF F))).smul hc).add continuous_const

end GlobalTheory.QSAStep

namespace GlobalTheory.QSAStep

theorem key_step : ∀ (F : Type) [Field F] [NumberField F] (a b : F), a ≠ 0 → b ≠ 0 → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → (S₁.Nonempty ∨ S₂.Nonempty) → (∀ t : AF F, ∃ h : DA F a b, nrm h = 1 ∧ ε * h.re = ε * t) → ∀ g : DA F a b, nrm g = 1 → ε • (g - 1) = 0 → ∀ W : Set (DA F a b), W ∈ 𝓝 g → ∃ w ∈ W, ∃ y : DA F a b, IsUnit (nrm y) ∧ ∃ γ : ℍ[F, a, b], nrm γ = 1 ∧ ∃ h : DA F a b, nrm h = 1 ∧ ε • (h - 1) = h - 1 ∧ y * w = rat γ * y * h := by
  classical
  intro F _ _ a b ha hb S₁ S₂ ε hε hS hsplit g hg hg1 W hW
  have hee : ε * ε = ε := idem_of_isPlacesIdem hε
  have h11 : (1 - ε) * (1 - ε) = 1 - ε := by linear_combination hee
  have h10 : (1 - ε) * ε = 0 := by linear_combination -hee
  have h01 : ε * (1 - ε) = 0 := by linear_combination -hee
  set ι := algebraMap F (AF F) with hι
  set φ : DA F a b → DA F a b := fun x => (1 - ε) • x + ε • (1 : DA F a b) with hφ
  have hφg : φ g = g := by
    have : φ g = g - ε • (g - 1) := by
      simp only [hφ, sub_smul, one_smul, smul_sub]; abel
    rw [this, hg1, sub_zero]
  have hW' : φ ⁻¹' W ∈ 𝓝 g :=
    (continuous_affine ε).continuousAt.preimage_mem_nhds (by change W ∈ 𝓝 (φ g); rw [hφg]; exact hW)
  obtain ⟨O, hO, ⟨x, hx⟩, hOu⟩ := GlobalTheory.T.quaternion_norm_one_trace_open_adeles F a b ha hb g hg _ hW'
  obtain ⟨t, htZ, s, hts⟩ := GlobalTheory.T.additive_strongApproximation_avoiding_finset F S₁ S₂ ε hε hS x O (hO.mem_nhds hx) {1, -1}
  obtain ⟨u₀, hu₀W, hu₀n, hu₀r⟩ := hOu _ hts
  obtain ⟨h₁, hh₁n, hh₁r⟩ := hsplit (ι t)
  have hc : t ^ 2 - 1 ≠ 0 := by
    have h1 : t ≠ 1 := fun h => htZ (by simp [h])
    have h2 : t ≠ -1 := fun h => htZ (by simp [h])
    have : t ^ 2 - 1 = (t - 1) * (t + 1) := by ring
    rw [this]
    exact mul_ne_zero (sub_ne_zero.2 h1) (fun h => h2 (eq_neg_of_add_eq_zero_left h))
  obtain ⟨u, hu⟩ : ∃ u : DA F a b, u = (1 - ε) • u₀ + ε • h₁ := ⟨_, rfl⟩
  have hun : nrm u = 1 := by
    rw [hu, nrm_split _ _ _ hee, hu₀n, hh₁n]; ring
  have hur : u.re = ι t := by
    rw [hu]
    simp only [QuaternionAlgebra.re_add, QuaternionAlgebra.re_smul, smul_eq_mul, hu₀r]
    linear_combination hh₁r - s * hee
  obtain ⟨hq0, hqq⟩ := pure_sq u (ι t) hun hur
  set q := u - algebraMap (AF F) (DA F a b) (ι t) with hq
  have hqq' : q * q = algebraMap (AF F) (DA F a b) (ι (t ^ 2 - 1)) := by
    rw [hqq]; simp [hι]
  obtain ⟨p, hp0, hpp⟩ := GlobalTheory.T.exists_rational_pure_quaternion_sq_of_adelic F a b ha hb _ hc q hq0 hqq'
  have hrp0 : (rat p).re = 0 := by simp [rat, hp0]
  have hrpp : rat p * rat p = algebraMap (AF F) (DA F a b) (ι (t ^ 2 - 1)) := by
    rw [← rat_mul, hpp, rat_algebraMap]
  obtain ⟨y, hy, hyq⟩ := GlobalTheory.T.exists_unit_intertwiner_adelicQuaternion F a b ha hb _ hc (rat p) q hrp0 hq0 hrpp hqq'
  set γ : ℍ[F, a, b] := algebraMap F ℍ[F, a, b] t + p with hγ
  have hγn : nrm γ = 1 := by
    have hre := congrArg QuaternionAlgebra.re hpp
    simp [QuaternionAlgebra.algebraMap_eq, hp0] at hre
    simp [hγ, nrm, QuaternionAlgebra.algebraMap_eq, hp0]
    linear_combination -hre
  have hyu : y * u = rat γ * y := by
    have : u = q + algebraMap (AF F) (DA F a b) (ι t) := by rw [hq]; abel
    rw [this, mul_add, hyq, hγ, rat_add, rat_algebraMap, add_mul, ← Algebra.commutes, add_comm]
  set h' : DA F a b := (1 - ε) • (1 : DA F a b) + ε • h₁ with hh'
  set h'' : DA F a b := (1 - ε) • (1 : DA F a b) + ε • star h₁ with hh''
  have hwh : φ u₀ * h' = u := by
    simp only [hφ, hh', hu, add_mul, mul_add, smul_mul_smul_comm, h11, h10, h01, hee, zero_smul, mul_one, one_mul,
      add_zero, zero_add]
  have hhh : h' * h'' = 1 := by
    simp only [hh', hh'', add_mul, mul_add, smul_mul_smul_comm, h11, h10, h01, hee, zero_smul, mul_one, one_mul,
      add_zero, zero_add, mul_star_eq, hh₁n, map_one]
    rw [← add_smul, sub_add_cancel, one_smul]
  refine ⟨φ u₀, hu₀W, y, hy, γ, hγn, h'', ?_, ?_, ?_⟩
  · rw [hh'', nrm_split _ _ _ hee, nrm_one, nrm_star, hh₁n]; ring
  · have e1 : h'' - 1 = ε • (star h₁ - 1) := by
      simp only [hh'', sub_smul, one_smul, smul_sub]; abel
    rw [e1, smul_smul, hee]
  · calc y * φ u₀ = y * φ u₀ * (h' * h'') := by rw [hhh, mul_one]
      _ = y * (φ u₀ * h') * h'' := by simp only [mul_assoc]
      _ = rat γ * y * h'' := by rw [hwh, hyu]

end GlobalTheory.QSAStep
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormOneQuaternionNearConjRationalTimesSupportedStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

theorem _root_.GlobalTheory.T.normOneQuaternion_near_conj_rational_times_supported : ∀ (F : Type) [Field F] [NumberField F] (a b : F), a ≠ 0 → b ≠ 0 → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → (S₁.Nonempty ∨ S₂.Nonempty) → (∀ t : AF F, ∃ h : DA F a b, nrm h = 1 ∧ ε * h.re = ε * t) → ∀ g : DA F a b, nrm g = 1 → ε • (g - 1) = 0 → ∀ W : Set (DA F a b), W ∈ 𝓝 g → ∃ w ∈ W, ∃ y : DA F a b, IsUnit (nrm y) ∧ ∃ γ : ℍ[F, a, b], nrm γ = 1 ∧ ∃ h : DA F a b, nrm h = 1 ∧ ε • (h - 1) = h - 1 ∧ y * w = rat γ * y * h := by
  first | exact @GlobalTheory.QSAStep.key_step | exact GlobalTheory.QSAStep.key_step | (intros; apply GlobalTheory.QSAStep.key_step <;> assumption)
end
end
