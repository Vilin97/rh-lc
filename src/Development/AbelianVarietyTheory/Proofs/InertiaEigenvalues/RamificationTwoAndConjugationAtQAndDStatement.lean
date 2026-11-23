module

public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
public import Formalism.LocalRingCardinality.DataHost
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AutomorphicArithmetic.CyclotomicBounds.ImageMemOfGens

section

@[expose] public section

namespace UpperTheory.Small

open Formalism.BasicNotions NumberField IsDedekindDomain Ideal
open scoped Pointwise

variable {R : Ranks} (H : Host R)

theorem exists_unit_neg : ∃ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ 1 [MOD H.QS * H.d] ∧ (H.art u).1.1 = -1 := by
  obtain ⟨hq, hd, hq8, hd16, -⟩ := H.hyp
  have hdq : Nat.Coprime H.d H.q := (Nat.coprime_primes hd hq).2 (by omega)
  have hsq : Nat.Coprime H.QS H.q := Nat.Coprime.coprime_dvd_right (dvd_mul_right _ _) H.QS_coprime
  have hcop : Nat.Coprime (H.QS * H.d) H.q := Nat.Coprime.mul_left hsq hdq
  obtain ⟨x, hx1, hx2⟩ := Nat.chineseRemainder hcop 1 (H.q - 1)
  have hq2 : 2 ≤ H.q := hq.two_le
  have hxm : Nat.Coprime x (H.QS * H.d) := by
    unfold Nat.Coprime; rw [Nat.ModEq.gcd_eq hx1]; simp
  have hxq : Nat.Coprime x H.q := by
    unfold Nat.Coprime; rw [Nat.ModEq.gcd_eq hx2]
    have : H.q - 1 + 1 = H.q := by omega
    rw [← this, Nat.gcd_comm]; simp
  have hxN : Nat.Coprime x H.condN := by
    have e : H.condN = H.QS * H.d * H.q := by simp only [Formalism.HC.HostRaw.condN]; ring
    rw [e]; exact Nat.Coprime.mul_right hxm hxq
  refine ⟨ZMod.unitOfCoprime x hxN, ?_, ?_⟩
  · rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast]
    refine Nat.ModEq.trans ?_ hx1
    refine Nat.ModEq.of_dvd ?_ (Nat.mod_modEq x _)
    exact ⟨H.q, by simp only [Formalism.HC.HostRaw.condN]; ring⟩
  · have h := H.flPS (ZMod.unitOfCoprime x hxN)
    rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast] at h
    have hJ : jacobiSym ((x % H.condN : ℕ) : ℤ) H.q = -1 := by
      rw [jacobiSym.mod_left]
      have h3 : ((x % H.condN : ℕ) : ℤ) % (H.q : ℤ) = (-1 : ℤ) % (H.q : ℤ) := by
        have hqN : H.q ∣ H.condN := ⟨H.QS * H.d, by simp only [Formalism.HC.HostRaw.condN]; ring⟩
        have h4 : x % H.condN % H.q = H.q - 1 := by
          rw [Nat.mod_mod_of_dvd _ hqN, hx2, Nat.mod_eq_of_lt (by omega)]
        rw [← Int.natCast_mod, h4]
        push_cast [Nat.cast_sub (by omega : 1 ≤ H.q)]
        rw [show (-1 : ℤ) = ((H.q : ℤ) - 1) + (-1) * (H.q : ℤ) by ring, Int.add_mul_emod_self_right,
          Int.emod_eq_of_lt] <;> omega
      rw [h3, ← jacobiSym.mod_left, jacobiSym.at_neg_one (hq.odd_of_ne_two (by omega))]
      exact ZMod.χ₄_nat_three_mod_four (by omega)
    rw [hJ] at h
    exact Units.ext (by simpa using h)

theorem inertia_q : ∃ g : R.GG, g ≠ 1 ∧ ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(H.q : ℤ)})]
    (σ : H.E ≃ₐ[ℚ] H.E), (∀ x : 𝓞 H.E, σ • x - x ∈ P) ↔ (H.gal σ = 1 ∨ H.gal σ = g) := by
  obtain ⟨hq, hd, hq8, hd16, -⟩ := H.hyp
  haveI : Fact (Nat.Prime H.q) := ⟨hq⟩
  obtain ⟨u0, hu0, hneg⟩ := exists_unit_neg H
  have hdq : Nat.Coprime H.d H.q := (Nat.coprime_primes hd hq).2 (by omega)
  have hsq : Nat.Coprime H.QS H.q := Nat.Coprime.coprime_dvd_right (dvd_mul_right _ _) H.QS_coprime
  have hcop : Nat.Coprime (H.QS * H.d) H.q := Nat.Coprime.mul_left hsq hdq
  have hN : H.condN = H.QS * H.d * H.q := by simp only [Formalism.HC.HostRaw.condN]; ring
  have hNpos : 0 < H.condN := by
    rw [hN]; exact Nat.mul_pos (Nat.mul_pos H.QS_pos hd.pos) hq.pos
  haveI : NeZero H.condN := ⟨hNpos.ne'⟩
  have hfq : H.condN.factorization H.q = 1 := by
    rw [hN, Nat.factorization_mul (Nat.mul_pos H.QS_pos hd.pos).ne' hq.ne_zero, Finsupp.add_apply,
      Nat.Prime.factorization_self hq, Nat.factorization_eq_zero_of_not_dvd]
    intro h
    exact hq.one_lt.ne' (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.symm hcop) h)
  have hfac : H.condN / H.q ^ H.condN.factorization H.q = H.QS * H.d := by
    rw [hfq, pow_one, hN, Nat.mul_div_cancel _ hq.pos]
  have hmN : H.QS * H.d ∣ H.condN := ⟨H.q, hN⟩
  have hqN : H.q ∣ H.condN := ⟨H.QS * H.d, by rw [hN]; ring⟩
  let f : (ZMod H.condN)ˣ →* (ZMod (H.QS * H.d))ˣ :=
    Units.map (ZMod.castHom hmN (ZMod (H.QS * H.d))).toMonoidHom
  have hmem : ∀ u : (ZMod H.condN)ˣ, u ∈ f.ker ↔ (u : ZMod H.condN).val ≡ 1 [MOD H.QS * H.d] := by
    intro u
    rw [MonoidHom.mem_ker, Units.ext_iff]
    change ((u : ZMod H.condN).cast : ZMod (H.QS * H.d)) = 1 ↔ _
    rw [ZMod.cast_eq_val, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff]
  let fq : f.ker →* (ZMod H.q)ˣ :=
    (Units.map (ZMod.castHom hqN (ZMod H.q)).toMonoidHom).comp f.ker.subtype
  have hinj : Function.Injective fq := by
    intro a b hab
    have ha := (hmem a).1 a.2
    have hb := (hmem b).1 b.2
    have hab' : ((a.1 : (ZMod H.condN)ˣ) : ZMod H.condN).val ≡ ((b.1 : (ZMod H.condN)ˣ) : ZMod H.condN).val [MOD H.q] := by
      rw [← ZMod.natCast_eq_natCast_iff]
      have := congrArg (fun x : (ZMod H.q)ˣ => (x : ZMod H.q)) hab
      change (((a.1 : (ZMod H.condN)ˣ) : ZMod H.condN).cast : ZMod H.q) = ((b.1 : (ZMod H.condN)ˣ) : ZMod H.condN).cast at this
      rwa [ZMod.cast_eq_val, ZMod.cast_eq_val] at this
    have hall : ((a.1 : (ZMod H.condN)ˣ) : ZMod H.condN).val ≡ ((b.1 : (ZMod H.condN)ˣ) : ZMod H.condN).val [MOD H.condN] := by
      have h0 := (Nat.modEq_and_modEq_iff_modEq_mul hcop).1 ⟨ha.trans hb.symm, hab'⟩
      rwa [← hN] at h0
    apply Subtype.ext; apply Units.ext
    rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at hall
    exact hall
  haveI : IsCyclic f.ker := isCyclic_of_injective fq hinj
  obtain ⟨c, hc⟩ := IsCyclic.exists_generator (α := f.ker)
  have hc2 : H.art (c : (ZMod H.condN)ˣ) ^ 2 = 1 := H.art_q _ ((hmem _).1 c.2)
  have key : ∀ u : (ZMod H.condN)ˣ, u ∈ f.ker → H.art u = 1 ∨ H.art u = H.art c := by
    intro u hu
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hc ⟨u, hu⟩)
    have hu' : u = (c : (ZMod H.condN)ˣ) ^ k := by
      rw [← Subgroup.coe_zpow, hk]
    rw [hu', map_zpow]
    have hc2' : H.art (c : (ZMod H.condN)ˣ) ^ (2 : ℤ) = 1 := by rw [zpow_ofNat]; exact hc2
    rcases Int.even_or_odd' k with ⟨j, rfl | rfl⟩
    · left; rw [zpow_mul, hc2', one_zpow]
    · right; rw [zpow_add, zpow_mul, hc2', one_zpow, one_mul, zpow_one]
  have hu0k : u0 ∈ f.ker := (hmem u0).2 hu0
  have hg : H.art u0 = H.art c := by
    rcases key u0 hu0k with h | h
    · rw [h, Prod.fst_one, Prod.fst_one] at hneg; exact absurd hneg (by decide)
    · exact h
  refine ⟨H.art u0, ?_, ?_⟩
  · intro h; rw [h, Prod.fst_one, Prod.fst_one] at hneg; exact absurd hneg (by decide)
  · intro P _ _ σ
    rw [H.der.inertia H.q P σ, hfac]
    constructor
    · rintro ⟨u, hu, he⟩
      rw [he]
      rcases key u ((hmem u).2 hu) with h | h
      · exact Or.inl h
      · exact Or.inr (h.trans hg.symm)
    · rintro (h | h)
      · exact ⟨1, (hmem 1).1 (one_mem _), by rw [h, map_one]⟩
      · exact ⟨u0, hu0, h⟩

end UpperTheory.Small
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RamificationTwoAndConjugationAtQAndD

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.PrimesQD

open Formalism.FrobeniusOrbits Formalism.MainNotions.EmbeddingTypeJumps
open scoped Pointwise

theorem liesOver_span {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime)
    {v : HeightOneSpectrum (𝓞 E)} (hv : v ∈ placesOver E p) :
    v.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := by
  constructor
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  have hle : Ideal.span {(p : ℤ)} ≤ Ideal.comap (algebraMap ℤ (𝓞 E)) v.asIdeal := by
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
    simpa [placesOver] using hv
  exact hmax.eq_of_le (Ideal.comap_ne_top _ v.isPrime.ne_top) hle

theorem ramIdx_eq_two (D : D7) {l : ℕ} (hl : l.Prime) (v : HeightOneSpectrum (𝓞 D.host.E))
    (hv : v ∈ placesOver D.host.E l) (g : D.R.GG) (hg : g ≠ 1)
    (hin : ∀ σ : D.host.E ≃ₐ[ℚ] D.host.E, σ ∈ ineG D v ↔
      (D.host.galE σ = 1 ∨ D.host.galE σ = g)) :
    v.asIdeal.ramificationIdx ℤ = 2 := by
  have hgal := D.host.hostE_isGalois
  have : IsGaloisGroup Gal(D.host.E/ℚ) ℤ (𝓞 D.host.E) :=
    IsGaloisGroup.of_isFractionRing _ _ _ ℚ D.host.E
  have := liesOver_span hl hv
  have := v.isPrime
  have : Fact l.Prime := ⟨hl⟩
  have hp : (Ideal.span {(l : ℤ)}).IsPrime :=
    (PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hl).irreducible).isPrime
  have hIn : Nat.card (v.asIdeal.inertia Gal(D.host.E/ℚ)) = 2 := by
    have e1 : (v.asIdeal.inertia Gal(D.host.E/ℚ)) ≃ (({1, g} : Set (D.R.GG))) :=
      Equiv.subtypeEquiv (D.host.gal).toEquiv (fun σ => by
        rw [show σ ∈ v.asIdeal.inertia Gal(D.host.E/ℚ) ↔ σ ∈ ineG D v from Iff.rfl, hin σ]
        simp [Formalism.HC.HostRaw.galE])
    rw [Nat.card_congr e1, Nat.card_coe_set_eq, Set.ncard_pair hg.symm]
  rw [← Ideal.ramificationIdxIn_eq_ramificationIdx (Ideal.span {(l : ℤ)}) v.asIdeal Gal(D.host.E/ℚ),
    ← Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(D.host.E/ℚ)) (Ideal.span {(l : ℤ)}) v.asIdeal, hIn]

theorem bE_sq (D : D7) : (D.host.sqd) ^ 2 = -(D.host.d : D.host.E) := D.host.sqd_sq

theorem neg_mem_iff (D : D7) (φ : D.host.E →+* ℂ) :
    (-φ (D.host.sqd) = Complex.I * (Real.sqrt D.host.d : ℂ)) ↔
      ¬ φ (D.host.sqd) = Complex.I * (Real.sqrt D.host.d : ℂ) := by
  set z := φ (D.host.sqd)
  set s : ℂ := (Real.sqrt D.host.d : ℂ)
  have hd0 : (0 : ℝ) < Real.sqrt D.host.d :=
    Real.sqrt_pos.2 (by exact_mod_cast D.host.hyp.2.1.pos)
  have hs : s ^ 2 = (D.host.d : ℂ) := by
    simp only [s, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    simp
  have hz : z ^ 2 = -(D.host.d : ℂ) := by
    simp only [z, ← map_pow, bE_sq, map_neg, map_natCast]
  have hs0 : Complex.I * s ≠ 0 := mul_ne_zero Complex.I_ne_zero
    (by simpa [s] using hd0.ne')
  have hfac : (z - Complex.I * s) * (z + Complex.I * s) = 0 := by
    have : (z - Complex.I * s) * (z + Complex.I * s) = z ^ 2 - Complex.I ^ 2 * s ^ 2 := by ring
    rw [this, hz, hs, Complex.I_sq]; ring
  constructor
  · intro h1 h2
    apply hs0
    have : (2 : ℂ) * (Complex.I * s) = 0 := by linear_combination -(h1 + h2)
    simpa using this
  · intro h
    rcases mul_eq_zero.1 hfac with h1 | h1
    · exact absurd (sub_eq_zero.1 h1) h
    · linear_combination -h1

theorem ramification_two_and_conjugation_at_q_and_d : ∀ D : D7, EmbeddingTypeJumps.Conclusion1 D := by
  intro D
  have hH := D.host.hyp
  obtain ⟨hq, hd, hq8, hd16, -⟩ := hH
  intro l hl
  have hl' : l = D.host.q ∨ l = D.host.d := by simpa using hl
  have hlp : l.Prime := by rcases hl' with rfl | rfl <;> assumption
  refine ⟨by rcases hl' with rfl | rfl <;> omega, ?_⟩
  intro v hv
  have hlo := liesOver_span hlp hv
  have := v.isPrime
  have hmemI : ∀ σ : D.host.E ≃ₐ[ℚ] D.host.E, σ ∈ ineG D v ↔ ∀ x : 𝓞 D.host.E, σ • x - x ∈ v.asIdeal :=
    fun σ => AddSubgroup.mem_inertia
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    rcases hl' with rfl | rfl
    · obtain ⟨g, hg, hin⟩ := UpperTheory.Small.inertia_q D.host
      exact ramIdx_eq_two D hlp v hv g hg fun σ => (hmemI σ).trans (hin v.asIdeal σ)
    · refine ramIdx_eq_two D hlp v hv D.R.iod (fun h => ?_)
        fun σ => (hmemI σ).trans (D.host.der.inertia_d v.asIdeal σ)
      have h' := congrArg (fun g : D.R.GG => g.1.2) h
      exact absurd (show (-1 : ℤˣ) = 1 from h') (by decide)
  ·
    intro h
    refine D.host.der.decompConj l hlp ?_ v.asIdeal (MulAction.mem_stabilizer_iff.mpr h)
    rcases hl' with rfl | rfl
    · exact (dvd_mul_left _ _).mul_right _
    · exact dvd_mul_left _ _
  ·
    rintro rfl σ hσ φ
    have hb : σ (D.host.sqd) = D.host.sqd :=
      (D.host.galE_mem_Psi_iff σ).1 (D.host.der.decomp_typeI _ hlp (dvd_mul_left _ _) v.asIdeal σ hσ)
    simp only [InPhi, Formalism.HC.HostRaw.cmType, Set.mem_setOf_eq, RingHom.coe_comp, Function.comp_apply]
    rw [show ((σ : D.host.E →+* D.host.E) (D.host.sqd)) = D.host.sqd from hb]
  ·
    rintro rfl σ hσ hσ1 φ
    have h2 := (D.host.der.inertia_d v.asIdeal σ).1 ((hmemI σ).1 hσ)
    have hg : D.host.galE σ = D.R.iod := h2.resolve_left fun h => hσ1 ((D.host.galE_eq_one_iff σ).1 h)
    have hb : σ (D.host.sqd) = -D.host.sqd := by
      rw [D.host.galE_bE σ, hg, show D.R.iod.1.2 = -1 from rfl]
      simp
    simp only [InPhi, Formalism.HC.HostRaw.cmType, Set.mem_setOf_eq, RingHom.coe_comp, Function.comp_apply]
    rw [show ((σ : D.host.E →+* D.host.E) (D.host.sqd)) = -D.host.sqd from hb,
      map_neg]
    exact neg_mem_iff D φ

end GlobalTheory.PrimesQD
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RamificationTwoAndConjugationAtQAndDStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.aux_statement : ∀ D : D7, EmbeddingTypeJumps.Conclusion1 D := by
  first | exact @GlobalTheory.PrimesQD.ramification_two_and_conjugation_at_q_and_d | exact GlobalTheory.PrimesQD.ramification_two_and_conjugation_at_q_and_d | (intros; apply GlobalTheory.PrimesQD.ramification_two_and_conjugation_at_q_and_d <;> assumption)
end
end
