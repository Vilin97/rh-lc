module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorModOfTmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentSeparabilityAverageStatement
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.RingTheory.Ideal.Span
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSeparabilityElementOfTraceNondegenerateStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorOrderTraceFormNondegenerateStatement
public import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Development.AbelianVarietyTheory.Definitions.Divisors.InfUniv

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrthogonalEigenIdempotentsOfSeparability

section

@[expose] public section

open scoped TensorProduct

namespace GlobalTheory.LieIdempotents

theorem balanced_apply {K : Type} {M : Type*} [CommRing K] [AddCommGroup M] (k : ℕ) (u v : Fin k → K)
    (hyp : ∀ c : K, ∑ j, (c * u j) ⊗ₜ[ℤ] v j = ∑ j, u j ⊗ₜ[ℤ] (v j * c))
    (B : K →+ K →+ M) (c : K) : ∑ j, B (c * u j) (v j) = ∑ j, B (u j) (v j * c) := by
  have hB : ∀ (r : ℤ) (m n : K), B (r • m) n = B m (r • n) := by
    intro r m n; rw [map_zsmul, map_zsmul]; rfl
  have := congrArg (TensorProduct.liftAddHom B hB) (hyp c)

  simpa [map_sum, TensorProduct.liftAddHom_tmul] using this

end GlobalTheory.LieIdempotents

open GlobalTheory.LieIdempotents in
theorem GlobalTheory.lie_idempotents : ∀ (R C K : Type) [CommRing R] [CommRing C] [CommRing K] (tR : R →+* C) (a : ℕ) (t : Fin a → (K →+* R)), (∀ i j, i ≠ j → Ideal.span (Set.range fun x => t i x - t j x) = ⊤) → ∀ (N : ℤ) (k : ℕ) (u v : Fin k → K), ∑ j, u j * v j = (N : K) → (∀ c : K, ∑ j, (c * u j) ⊗ₜ[ℤ] v j = ∑ j, u j ⊗ₜ[ℤ] (v j * c)) → IsUnit (N : C) → ∀ (H : Type*) [AddCommGroup H] [Module C H] (ρF : K →+* Module.End C H), ∃ φ : Fin a → Module.End C H, (∀ i c, ρF c * φ i = tR (t i c) • φ i) ∧ (∀ i j, φ i * φ j = if i = j then φ i else 0) ∧ (∀ g : Module.End C H, (∀ c, g * ρF c = ρF c * g) → ∀ i, g * φ i = φ i * g) ∧ (∀ F : Submodule C H, (∀ c, ∀ x ∈ F, ρF c x ∈ F) → ∀ i, ∀ x ∈ F, φ i x ∈ F) ∧ (∀ F : Submodule C H, (∀ c, ∀ x ∈ F, ρF c x ∈ F) → ∀ i w, (∀ c, ρF c w - tR (t i c) • w ∈ F) → ∀ j, φ j w - (if j = i then w else 0) ∈ F) := by
  intro R C K _ _ _ tR a t hcom N k u v huv hyp hN H _ _ ρF
  set n : C := ((hN.unit⁻¹ : Cˣ) : C) with hn
  have hnN : n * (N : C) = 1 := hN.val_inv_mul

  have hS : ∀ p q, ∑ j, t p (u j) * t q (v j) = if p = q then (N : R) else 0 := by
    intro p q
    split_ifs with hpq
    · subst hpq

      simp only [← map_mul, ← map_sum, huv, map_intCast]
    · set S := ∑ j, t p (u j) * t q (v j) with hSdef
      let B : K →+ K →+ R := AddMonoidHom.mk' (fun x => AddMonoidHom.mk' (fun y => t p x * t q y)
        (by intro y y'; simp [mul_add])) (by intro x x'; ext y; simp [add_mul])
      have hc : ∀ c, t p c * S = S * t q c := by
        intro c
        have := balanced_apply k u v hyp B c
        simp only [B, AddMonoidHom.mk'_apply, map_mul] at this
        rw [hSdef, Finset.mul_sum, Finset.sum_mul]
        convert this using 2 <;> ring
      have hle : Ideal.span (Set.range fun x => t p x - t q x) ≤ LinearMap.ker (LinearMap.mulLeft R S) := by
        rw [Ideal.span_le]
        rintro _ ⟨x, rfl⟩
        simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.mulLeft_apply]
        rw [mul_sub, mul_comm S, hc, sub_self]
      rw [hcom p q hpq] at hle
      have h1 : (1 : R) ∈ LinearMap.ker (LinearMap.mulLeft R S) := hle Submodule.mem_top
      simpa using h1
  have hSC : ∀ p q, ∑ j, tR (t p (u j)) * tR (t q (v j)) = if p = q then (N : C) else 0 := by
    intro p q
    have := congrArg tR (hS p q)

    simp only [map_sum, map_mul] at this
    rw [this]; split_ifs <;> simp
  have hnNx : ∀ x : Module.End C H, n • (N : C) • x = x := by
    intro x; rw [smul_smul, hnN, one_smul]
  have heig : ∀ i c, ρF c * (n • ∑ j, tR (t i (v j)) • ρF (u j)) = tR (t i c) • (n • ∑ j, tR (t i (v j)) • ρF (u j)) := by
    intro i c
    let B : K →+ K →+ Module.End C H := AddMonoidHom.mk' (fun x => AddMonoidHom.mk' (fun y => tR (t i y) • ρF x)
        (by intro y y'; simp [add_smul])) (by intro x x'; ext y : 1; simp [smul_add])
    have hb := balanced_apply k u v hyp B c
    simp only [B, AddMonoidHom.mk'_apply, map_mul] at hb
    rw [mul_smul_comm, Finset.mul_sum]
    simp only [mul_smul_comm]
    rw [hb, smul_comm (tR (t i c)) n]
    simp only [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    rw [smul_smul, mul_comm]
  refine ⟨fun i => n • ∑ j, tR (t i (v j)) • ρF (u j), heig, ?_, ?_, ?_, ?_⟩
  ·
    intro i j
    dsimp only
    generalize hΦ : n • ∑ l, tR (t j (v l)) • ρF (u l) = Φ at heig
    have hj := heig j
    rw [hΦ] at hj
    rw [smul_mul_assoc, Finset.sum_mul]
    simp only [smul_mul_assoc, hj, smul_smul, ← Finset.sum_smul]
    have hsum : ∑ l, tR (t i (v l)) * tR (t j (u l)) = ∑ l, tR (t j (u l)) * tR (t i (v l)) :=
      Finset.sum_congr rfl fun _ _ => mul_comm _ _
    rw [hsum, hSC j i]
    by_cases hij : i = j
    · subst hij; rw [if_pos rfl, if_pos rfl, hnN, one_smul]; exact hΦ.symm
    · simp [hij, Ne.symm hij]
  · intro g hg i
    simp only [mul_smul_comm, smul_mul_assoc, Finset.mul_sum, Finset.sum_mul, hg]
  · intro F hF i x hx
    simp only [LinearMap.smul_apply, LinearMap.sum_apply]
    exact F.smul_mem _ (F.sum_mem fun l _ => F.smul_mem _ (hF _ _ hx))
  · intro F hF i w hw j
    have e : (n • ∑ l, tR (t j (v l)) • ρF (u l)) w - (if j = i then w else 0)
        = n • ∑ l, tR (t j (v l)) • (ρF (u l) w - tR (t i (u l)) • w) := by
      have hite : (if j = i then w else 0) = n • (∑ l, tR (t i (u l)) * tR (t j (v l))) • w := by
        rw [hSC i j]; by_cases hij : i = j
        · subst hij; simp [smul_smul, hnN]
        · simp [hij, Ne.symm hij]
      rw [hite]
      simp only [LinearMap.smul_apply, LinearMap.sum_apply, smul_sub, Finset.sum_sub_distrib, Finset.sum_smul, Finset.smul_sum, smul_smul]
      congr 1
      refine Finset.sum_congr rfl fun l _ => ?_
      ring_nf
    rw [e]
    exact F.smul_mem _ (F.sum_mem fun l _ => F.smul_mem _ (hw _))
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrthogonalEigenIdempotentsOfSeparabilityStatement

section

@[expose] public section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_orthogonal_eigen_idempotents_of_separability : ∀ (R C K : Type) [CommRing R] [CommRing C] [CommRing K] (tR : R →+* C) (a : ℕ) (t : Fin a → (K →+* R)), (∀ i j, i ≠ j → Ideal.span (Set.range fun x => t i x - t j x) = ⊤) → ∀ (N : ℤ) (k : ℕ) (u v : Fin k → K), ∑ j, u j * v j = (N : K) → (∀ c : K, ∑ j, (c * u j) ⊗ₜ[ℤ] v j = ∑ j, u j ⊗ₜ[ℤ] (v j * c)) → IsUnit (N : C) → ∀ (H : Type*) [AddCommGroup H] [Module C H] (ρF : K →+* Module.End C H), ∃ φ : Fin a → Module.End C H, (∀ i c, ρF c * φ i = tR (t i c) • φ i) ∧ (∀ i j, φ i * φ j = if i = j then φ i else 0) ∧ (∀ g : Module.End C H, (∀ c, g * ρF c = ρF c * g) → ∀ i, g * φ i = φ i * g) ∧ (∀ F : Submodule C H, (∀ c, ∀ x ∈ F, ρF c x ∈ F) → ∀ i, ∀ x ∈ F, φ i x ∈ F) ∧ (∀ F : Submodule C H, (∀ c, ∀ x ∈ F, ρF c x ∈ F) → ∀ i w, (∀ c, ρF c w - tR (t i c) • w ∈ F) → ∀ j, φ j w - (if j = i then w else 0) ∈ F) := by
  first | exact @GlobalTheory.lie_idempotents | exact GlobalTheory.lie_idempotents | (intros; apply GlobalTheory.lie_idempotents <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingOfIntegersTraceMulLeftNondegenerate

section

@[expose] public section

open NumberField
open scoped TensorProduct

namespace GlobalTheory

theorem ringOfIntegers_trace_mulLeft_nondegenerate :
    ∀ (K : Type) [Field K] [NumberField K] (x : 𝓞 K),
      (∀ y : 𝓞 K, LinearMap.trace ℤ (𝓞 K) (LinearMap.mulLeft ℤ (x * y)) = 0) → x = 0 := by
  intro K _ _ x hx
  by_contra hne
  have hxK : (x : K) ≠ 0 := by
    intro h; exact hne (RingOfIntegers.coe_eq_zero_iff.mp h)
  have halg : IsAlgebraic ℤ ((x : K)⁻¹) :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ K).2 (Algebra.IsAlgebraic.isAlgebraic _)
  obtain ⟨d, hd0, hdi⟩ := halg.exists_integral_multiple
  let y : 𝓞 K := ⟨d • (x : K)⁻¹, hdi⟩
  have hxy : x * y = algebraMap ℤ (𝓞 K) d := by
    apply RingOfIntegers.coe_injective
    show (x : K) * (d • (x : K)⁻¹) = ((algebraMap ℤ (𝓞 K) d : 𝓞 K) : K)
    rw [eq_intCast, zsmul_eq_mul]
    push_cast
    field_simp
    first | exact (map_intCast (algebraMap (𝓞 K) K) d).symm | norm_cast | simp
  have h := hx y
  rw [hxy] at h
  have h2 : LinearMap.trace ℤ (𝓞 K) (LinearMap.mulLeft ℤ (algebraMap ℤ (𝓞 K) d))
      = Algebra.trace ℤ (𝓞 K) (algebraMap ℤ (𝓞 K) d) := by
    rw [Algebra.trace_apply]; rfl
  rw [h2, Algebra.trace_algebraMap] at h
  have hpos : 0 < Module.finrank ℤ (𝓞 K) := Module.finrank_pos
  rw [nsmul_eq_mul] at h
  rcases mul_eq_zero.mp h with h | h
  · exact absurd (by exact_mod_cast h) hpos.ne'
  · exact hd0 h

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingOfIntegersTraceMulLeftNondegenerateStatement

section

@[expose] public section

open NumberField
open scoped TensorProduct

theorem _root_.GlobalTheory.T.ringOfIntegers_eq_zero_of_trace_mulLeft_eq_zero : ∀ (K : Type) [Field K] [NumberField K] (x : 𝓞 K), (∀ y : 𝓞 K, LinearMap.trace ℤ (𝓞 K) (LinearMap.mulLeft ℤ (x * y)) = 0) → x = 0 := by
  first | (exact @GlobalTheory.ringOfIntegers_trace_mulLeft_nondegenerate) | (exact GlobalTheory.ringOfIntegers_trace_mulLeft_nondegenerate) | (intros; apply GlobalTheory.ringOfIntegers_trace_mulLeft_nondegenerate  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftSummandLieResidueCharZero

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct

set_option autoImplicit false

namespace GlobalTheory.HTSummand

theorem liftSummand_residueCharZero : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (C : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] (I : Ideal C), I ^ 2 = ⊥ → IsUnit (p : C) → ∀ (tR : R →+* C) (H : Type 1) [AddCommGroup H] [Module C H] [Module.Finite C H] [Module.Projective C H] (ρ : D.O →+* Module.End C H), (letI := GlobalTheory.HTSummand.tensorModOf (ρ.comp (algebraMap (𝓞 D.F) D.O)); Module.Projective (C ⊗[ℤ] 𝓞 D.F) H) → ∀ (e : Module.End C H), e * e = e → (∀ c, ρ c * e = e * ρ c) → (∀ x, ρ (algebraMap (𝓞 D.F) D.O D.ω) (e x) = tR b.ρ • e x) → ∀ (F : Submodule C H), I • ⊤ ≤ F → (∀ (c : D.O), ∀ x ∈ F, ρ c x ∈ F) → (∀ x ∈ F, e x ∈ F) → (∃ E' M : Submodule C H, IsCompl E' M ∧ E' ⊔ I • ⊤ = F) → (∀ d ∈ LinearMap.range e, ∃ w : Fin D.a → H, (∀ i (c : 𝓞 D.F), ρ (algebraMap (𝓞 D.F) D.O c) (w i) - tR (b.t i c) • w i ∈ F) ∧ d - ∑ i, w i ∈ F) → ∃ G M : Submodule C H, G ⊓ M = ⊥ ∧ G ⊔ M = LinearMap.range e ∧ (∀ (c : D.O), ∀ x ∈ G, ρ c x ∈ G) ∧ G ⊔ (I • ⊤ ⊓ LinearMap.range e) = F ⊓ LinearMap.range e ∧ ∀ d ∈ LinearMap.range e, ∃ w : Fin D.a → H, (∀ i (c : 𝓞 D.F), ρ (algebraMap (𝓞 D.F) D.O c) (w i) - tR (b.t i c) • w i ∈ G) ∧ d - ∑ i, w i ∈ G := by

  intro p _ D R _ b C _ _ _ I hI hp tR H _ _ _ _ ρ _ e he heρ hω F hIF hFO heF hE' hLie
  have hunitN : ∀ n : ℕ, n ≠ 0 → IsUnit (n : C) := by
    intro n hn
    obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p (Fact.out : p.Prime).one_lt.ne'
    have hcop : m.Coprime p := Nat.coprime_comm.mp (((Fact.out : p.Prime).coprime_iff_not_dvd).2 hm)
    have h2 : IsUnit (tR (m : R)) := (b.unit m hcop).map tR
    rw [map_natCast] at h2
    push_cast
    exact (hp.pow k).mul h2
  have hunitZ : ∀ N : ℤ, N ≠ 0 → IsUnit (N : C) := by
    intro N hN
    obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg N
    · exact_mod_cast hunitN n (by rintro rfl; simp at hN)
    · push_cast; exact (hunitN n (by rintro rfl; simp at hN)).neg
  obtain ⟨NF, kF, u, v, hNF, huv, hcomF⟩ := GlobalTheory.T.exists_separability_element_of_trace_nondegenerate' (𝓞 D.F) (GlobalTheory.T.ringOfIntegers_eq_zero_of_trace_mulLeft_eq_zero D.F)
  haveI := D.freeO; haveI := D.finO
  obtain ⟨NO, kO, x, y, hNO, hxy, hcomO⟩ := GlobalTheory.T.exists_separability_element_of_trace_nondegenerate' D.O (GlobalTheory.T.harrisTaylorOrder_traceForm_nondegenerate p D)
  obtain ⟨φ, hφc, hφφ, hφcomm, hφF, hφmod⟩ := GlobalTheory.T.exists_orthogonal_eigen_idempotents_of_separability R C (𝓞 D.F) tR D.a b.t b.comax NF kF u v huv hcomF
    (hunitZ NF hNF) H (ρ.comp (algebraMap (𝓞 D.F) D.O))
  have hFO' : ∀ c, ∀ z ∈ F, (ρ.comp (algebraMap (𝓞 D.F) D.O)) c z ∈ F := fun c z hz => hFO _ z hz
  set f : Module.End C H := ∑ i, φ i with hfdef
  have hfapp : ∀ z, f z = ∑ i, φ i z := fun z => by rw [hfdef, LinearMap.sum_apply]
  have hf : f * f = f := by
    rw [hfdef, Finset.sum_mul_sum]
    simp only [hφφ]
    exact Finset.sum_congr rfl fun i _ => by simp
  have hcommF : ∀ g : Module.End C H, (∀ c : 𝓞 D.F, g * ρ (algebraMap _ D.O c) = ρ (algebraMap _ D.O c) * g) → g * f = f * g := by
    intro g hg
    have hg' : ∀ c, g * (ρ.comp (algebraMap (𝓞 D.F) D.O)) c = (ρ.comp (algebraMap (𝓞 D.F) D.O)) c * g :=
      fun c => hg _
    rw [hfdef, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => hφcomm g hg' i
  have hef : e * f = f * e := hcommF e fun c => (heρ _).symm
  have hρf : ∀ c : D.O, ρ c * f = f * ρ c := fun c => hcommF (ρ c) fun c' => by
    rw [← map_mul, ← map_mul, Algebra.commutes]
  have hfF : ∀ z ∈ F, f z ∈ F := fun z hz => by
    rw [hfapp]; exact Submodule.sum_mem F fun i _ => hφF F hFO' i z hz
  set ε : Module.End C H := f * e with hεdef
  have hεapp : ∀ z, ε z = f (e z) := fun z => rfl
  have hε : ε * ε = ε := by
    calc f * e * (f * e) = f * ((e * f) * e) := by simp only [_root_.mul_assoc]
      _ = f * ((f * e) * e) := by rw [hef]
      _ = (f * f) * (e * e) := by simp only [_root_.mul_assoc]
      _ = f * e := by rw [hf, he]
  have hρε : ∀ c, ρ c * ε = ε * ρ c := fun c => by
    calc ρ c * (f * e) = (ρ c * f) * e := by rw [_root_.mul_assoc]
      _ = f * (ρ c * e) := by rw [hρf, _root_.mul_assoc]
      _ = f * e * ρ c := by rw [heρ, _root_.mul_assoc]
  have hFε : ∀ z ∈ F, ε z ∈ F := fun z hz => hfF _ (heF z hz)
  obtain ⟨π, hππ, hπρ, hπε, hεπ, hA, hB⟩ := GlobalTheory.T.exists_idempotent_separability_average C D.O I hI NO kO x y hxy hcomO (hunitZ NO hNO) H ρ ε hε hρε
    F hIF hFO hFε hE'
  have hεε : ∀ z, ε (ε z) = ε z := fun z => LinearMap.congr_fun hε z
  have hπε' : ∀ z, π (ε z) = π z := fun z => LinearMap.congr_fun hπε z
  have hεπ' : ∀ z, ε (π z) = π z := fun z => LinearMap.congr_fun hεπ z
  have hππ' : ∀ z, π (π z) = π z := fun z => LinearMap.congr_fun hππ z
  have hfπ : ∀ z, f (π z) = π z := fun z => by
    rw [← hεπ' z, hεapp, ← hεapp]
    have := LinearMap.congr_fun hf (e (π z))
    simp only [Module.End.mul_apply] at this
    rw [hεapp, this]
  have hπP : ∀ z, π z ∈ LinearMap.range e := fun z => ⟨f (π z), by
    have := LinearMap.congr_fun hef (π z)
    simp only [Module.End.mul_apply] at this
    exact this.trans (hεπ' z)⟩
  have heP : ∀ d ∈ LinearMap.range e, e d = d := by
    rintro d ⟨z, rfl⟩
    exact LinearMap.congr_fun he z
  have hfP : ∀ d ∈ LinearMap.range e, d - f d ∈ F := by
    intro d hd
    obtain ⟨w, hw1, hw2⟩ := hLie d hd
    have hfw : ∀ i, f (w i) - w i ∈ F := by
      intro i
      have hs := Submodule.sum_mem F fun j (_ : j ∈ Finset.univ) => hφmod F hFO' i (w i) (hw1 i) j
      rw [Finset.sum_sub_distrib, Finset.sum_ite_eq'] at hs
      simpa [hfapp] using hs
    have key : d - f d = (d - ∑ i, w i) - f (d - ∑ i, w i) - ∑ i, (f (w i) - w i) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sub, map_sum, Finset.sum_sub_distrib]; abel
    rw [key]
    exact F.sub_mem (F.sub_mem hw2 (hfF _ hw2)) (Submodule.sum_mem F fun i _ => hfw i)
  have hGmem : ∀ d ∈ LinearMap.range e, d - π d ∈ LinearMap.range e ⊓ LinearMap.ker π := fun d hd =>
    ⟨Submodule.sub_mem _ hd (hπP d), by simp [hππ']⟩
  refine ⟨LinearMap.range e ⊓ LinearMap.ker π, LinearMap.range π, ?_, ?_, ?_, ?_, ?_⟩
  · rw [eq_bot_iff]
    intro z hz
    obtain ⟨⟨-, hz1⟩, ⟨w, rfl⟩⟩ := hz
    replace hz1 : π (π w) = 0 := hz1
    rw [Submodule.mem_bot, ← hππ' w]; exact hz1
  · apply le_antisymm
    · exact sup_le inf_le_left (by rintro _ ⟨z, rfl⟩; exact hπP z)
    · intro d hd
      exact Submodule.mem_sup.2 ⟨d - π d, hGmem d hd, π d, ⟨d, rfl⟩, sub_add_cancel d (π d)⟩
  · rintro c z ⟨⟨w, rfl⟩, hz⟩
    refine Submodule.mem_inf.2 ⟨LinearMap.mem_range.2 ⟨ρ c w, ?_⟩, ?_⟩
    · have := LinearMap.congr_fun (heρ c) w
      simp only [Module.End.mul_apply] at this
      exact this.symm
    · replace hz : π (e w) = 0 := hz
      show π (ρ c (e w)) = 0
      have := LinearMap.congr_fun (hπρ c) (e w)
      simp only [Module.End.mul_apply] at this
      rw [← this, hz, map_zero]
  · apply le_antisymm
    · refine sup_le ?_ (inf_le_inf_right _ hIF)
      rintro z ⟨hzP, hz⟩
      replace hz : π z = 0 := hz
      refine Submodule.mem_inf.2 ⟨?_, hzP⟩
      have h1 := hfP z hzP
      have h2 := hA (ε z) (hεε z)
      rw [hπε', hz, sub_zero] at h2
      have : z = (z - f z) + ε z := by rw [hεapp, heP z hzP]; abel
      rw [this]; exact F.add_mem h1 h2
    · rintro z ⟨hzF, hzP⟩
      refine Submodule.mem_sup.2 ⟨z - π z, hGmem z hzP, π z, Submodule.mem_inf.2 ⟨?_, hπP z⟩, sub_add_cancel z (π z)⟩
      rw [← hπε']; exact hB (ε z) (hFε z hzF) (hεε z)
  · intro d hd
    refine ⟨fun i => φ i (π d), fun i c => ?_, ?_⟩
    · have := LinearMap.congr_fun (hφc i c) (π d)
      simp only [Module.End.mul_apply, LinearMap.smul_apply, RingHom.comp_apply] at this
      rw [this, sub_self]; exact Submodule.zero_mem _
    · have : ∑ i, φ i (π d) = π d := by rw [← hfapp]; exact hfπ d
      rw [this]; exact hGmem d hd

end GlobalTheory.HTSummand
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftSummandLieResidueCharZeroStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_liftSummand_lie_residueCharZero : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (C : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] (I : Ideal C), I ^ 2 = ⊥ → IsUnit (p : C) → ∀ (tR : R →+* C) (H : Type 1) [AddCommGroup H] [Module C H] [Module.Finite C H] [Module.Projective C H] (ρ : D.O →+* Module.End C H), (letI := GlobalTheory.HTSummand.tensorModOf (ρ.comp (algebraMap (𝓞 D.F) D.O)); Module.Projective (C ⊗[ℤ] 𝓞 D.F) H) → ∀ (e : Module.End C H), e * e = e → (∀ c, ρ c * e = e * ρ c) → (∀ x, ρ (algebraMap (𝓞 D.F) D.O D.ω) (e x) = tR b.ρ • e x) → ∀ (F : Submodule C H), I • ⊤ ≤ F → (∀ (c : D.O), ∀ x ∈ F, ρ c x ∈ F) → (∀ x ∈ F, e x ∈ F) → (∃ E' M : Submodule C H, IsCompl E' M ∧ E' ⊔ I • ⊤ = F) → (∀ d ∈ LinearMap.range e, ∃ w : Fin D.a → H, (∀ i (c : 𝓞 D.F), ρ (algebraMap (𝓞 D.F) D.O c) (w i) - tR (b.t i c) • w i ∈ F) ∧ d - ∑ i, w i ∈ F) → ∃ G M : Submodule C H, G ⊓ M = ⊥ ∧ G ⊔ M = LinearMap.range e ∧ (∀ (c : D.O), ∀ x ∈ G, ρ c x ∈ G) ∧ G ⊔ (I • ⊤ ⊓ LinearMap.range e) = F ⊓ LinearMap.range e ∧ ∀ d ∈ LinearMap.range e, ∃ w : Fin D.a → H, (∀ i (c : 𝓞 D.F), ρ (algebraMap (𝓞 D.F) D.O c) (w i) - tR (b.t i c) • w i ∈ G) ∧ d - ∑ i, w i ∈ G := by
  first | exact @GlobalTheory.HTSummand.liftSummand_residueCharZero | exact GlobalTheory.HTSummand.liftSummand_residueCharZero | (intros; apply GlobalTheory.HTSummand.liftSummand_residueCharZero <;> assumption)
end
end
