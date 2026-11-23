module

public import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCharacterPrimeConductorDegreePrimePow
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.DecActRoots
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormNatCastOfCoprime
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InertiaTorsionQuotientConjInvariantDecomposition
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.CyclotomicCharCongruentOneOnDecompositionGroup

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2.EpsDec

theorem natCast_eq_of_pow_eq {M : Type} [CommMonoid M] {ζ : M} {N : ℕ} (hζ : IsPrimitiveRoot ζ N) (hN : N ≠ 0)
    {a b : ℕ} (h : ζ ^ a = ζ ^ b) : (a : ZMod N) = b := by
  rw [ZMod.natCast_eq_natCast_iff' a b N]
  rw [pow_eq_pow_mod a hζ.pow_eq_one, pow_eq_pow_mod b hζ.pow_eq_one] at h
  exact hζ.pow_inj (Nat.mod_lt _ (Nat.pos_of_ne_zero hN)) (Nat.mod_lt _ (Nat.pos_of_ne_zero hN)) h

theorem eps_dec_cong : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (n : ℕ) (w : Pl)
    (B : ValuationSubring Ω), IsPlaceOver B w → l ^ n ∣ normV w - 1 → 1 ≤ n →
    ∀ σ ∈ Dec (F := ℚ) B, Cg n (eps l σ) 1 := by
  intro l _ Ω _ _ _ n w B hB hdiv hn σ hσ
  have hl : l.Prime := Fact.out
  have hl2 := hl.two_le
  set p := normV w with hpdef
  have hp : p.Prime := GlobalTheory.Ord2.PrimeChar.normV_prime w
  haveI : Fact p.Prime := ⟨hp⟩
  have hA : B.valuation (p : Ω) < 1 := GlobalTheory.Ord2.PrimeChar.val_normV_lt_one hB
  have hpl : p ≠ l := by
    intro e
    have h1 : l ∣ p - 1 := (dvd_pow_self l (by omega)).trans hdiv
    rw [e] at h1
    have h2 := Nat.le_of_dvd (by omega) h1
    omega
  have hcop : (l ^ n).Coprime p :=
    Nat.Coprime.pow_left n ((Nat.coprime_primes hl hp).2 hpl.symm)
  obtain ⟨k, hk⟩ := UpperTheory.V.LDataCardLeFinrank.decActRoots ℚ Ω p B hA (l ^ n) hcop σ hσ
  have hp1 : (p : ZMod (l ^ n)) = 1 := by
    have h1 : 1 ≤ p := hp.one_lt.le
    have : ((p - 1 : ℕ) : ZMod (l ^ n)) = 0 := (CharP.cast_eq_zero_iff (ZMod (l ^ n)) (l ^ n) _).2 hdiv
    rw [Nat.cast_sub h1, Nat.cast_one, sub_eq_zero] at this
    exact this
  have hIAC : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr hl.ne_zero⟩
  have hN0 : l ^ n ≠ 0 := pow_ne_zero _ hl.ne_zero
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ n)
  have hspec := cyclotomicCharacter.spec (L := Ω) l
    (MulSemiringAction.toRingAut (G ℚ Ω) Ω σ) ζ hζ.pow_eq_one
  set c : ℤ_[l] := ((cycZ ℚ Ω l σ : ℤ_[l]ˣ) : ℤ_[l]) with hc
  have hσζ : σ ζ = ζ ^ (PadicInt.toZModPow n c).val := hspec
  have hζp : ζ ^ (p ^ k) = ζ ^ 1 := by
    rw [pow_eq_pow_mod (p ^ k) hζ.pow_eq_one, pow_eq_pow_mod 1 hζ.pow_eq_one]
    congr 1
    rw [← ZMod.natCast_eq_natCast_iff', Nat.cast_pow, hp1, one_pow, Nat.cast_one]
  have hm : PadicInt.toZModPow n c = 1 := by
    have h1 : ζ ^ (PadicInt.toZModPow n c).val = ζ ^ 1 := by rw [← hσζ, hk ζ hζ.pow_eq_one, hζp]
    have h2 := natCast_eq_of_pow_eq hζ hN0 h1
    rwa [ZMod.natCast_zmod_val, Nat.cast_one] at h2
  have hker : c - 1 ∈ Ideal.span {((l : ℤ_[l])) ^ n} := by
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, hm, map_one, sub_self]
  have hnorm := (PadicInt.norm_le_pow_iff_mem_span_pow (c - 1) n).2 hker
  have e1 : eps l σ - 1 = algebraMap ℚ_[l] (Qbar l) ((c : ℚ_[l]) - 1) := by
    rw [map_sub, map_one]; rfl
  unfold Cg
  rw [e1, norm_algebraMap', norm_pow]
  have e2 : ((l : ℕ) : Qbar l) = algebraMap ℚ_[l] (Qbar l) (l : ℚ_[l]) := by simp
  rw [e2, norm_algebraMap', Padic.norm_p]
  have e3 : ‖(c : ℚ_[l]) - 1‖ = ‖c - 1‖ := by
    rw [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_one]
  rw [e3]
  refine hnorm.trans (le_of_eq ?_)
  rw [zpow_neg, zpow_natCast, inv_pow]

end GlobalTheory.Ord2.EpsDec
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.CyclotomicCharCongruentOneOnDecompositionGroupStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

theorem _root_.GlobalTheory.T.cyclotomicChar_congruent_one_on_decompositionGroup : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (n : ℕ) (w : Pl) (B : ValuationSubring Ω), IsPlaceOver B w → l ^ n ∣ normV w - 1 → 1 ≤ n → ∀ σ ∈ Dec (F := ℚ) B, Cg n (eps l σ) 1 := by
  first | exact @GlobalTheory.Ord2.EpsDec.eps_dec_cong | exact GlobalTheory.Ord2.EpsDec.eps_dec_cong | (intros; apply GlobalTheory.Ord2.EpsDec.eps_dec_cong <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ImportsAlt

section

@[expose] public section

namespace GlobalTheory.IntegralNormLeOne

open Polynomial

theorem norm_le_one_of_isIntegral {l : ℕ} [inst : Fact (Nat.Prime l)] (x : PadicAlgCl l)
    (hx : IsIntegral ℤ_[l] x) : ‖x‖ ≤ (1 : ℝ) := by
  apply GlobalTheory.PadicNormCastBounds.norm_le_one_of_isIntegral <;> assumption

end GlobalTheory.IntegralNormLeOne
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.InertiaTorsionQuotientConjInvariantDecompositionStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

theorem _root_.GlobalTheory.T.inertiaTorsionQuotient_conj_invariant_decomposition : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (n : ℕ) (w : Pl) (B : ValuationSubring Ω) (M : Type) [AddCommGroup M] (u : G ℚ Ω → M), IsPlaceOver B w → l ^ n ∣ normV w - 1 → 1 ≤ n → (∀ x : M, l ^ n • x = 0) → IsLocallyConstant (fun s : Ine (F := ℚ) B => u s) → (∀ s ∈ Ine (F := ℚ) B, ∀ t ∈ Ine (F := ℚ) B, u (s * t) = u s + u t) → ∀ g ∈ Dec (F := ℚ) B, ∀ s ∈ Ine (F := ℚ) B, u (g * s * g⁻¹) = u s := by
  first | exact @GlobalTheory.TameConjInv.conj_invariant | exact GlobalTheory.TameConjInv.conj_invariant | (intros; apply GlobalTheory.TameConjInv.conj_invariant <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.TameCochainCocycleExtension

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.BrTame

variable {l : ℕ} [Fact l.Prime]

def ballSub (r : ℝ) (hr : 0 ≤ r) : AddSubgroup (PadicAlgCl l) where
  carrier := {x | ‖x‖ ≤ r}
  zero_mem' := by simpa using hr
  add_mem' := fun {a b} ha hb => (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  neg_mem' := fun {a} ha => by simpa [Set.mem_setOf_eq, norm_neg] using ha

theorem mem_ballSub {r : ℝ} {hr : 0 ≤ r} {x : PadicAlgCl l} : x ∈ ballSub r hr ↔ ‖x‖ ≤ r := Iff.rfl

theorem cg_iff {n : ℕ} {a b : Qbar l} : Cg n a b ↔ a - b ∈ ballSub (l := l) ‖((l : ℕ) : Qbar l) ^ n‖ (norm_nonneg _) := Iff.rfl

theorem mul_mem_ballSub {r : ℝ} {hr : 0 ≤ r} {k x : PadicAlgCl l} (hk : ‖k‖ ≤ 1) (hx : x ∈ ballSub r hr) :
    k * x ∈ ballSub r hr := by
  rw [mem_ballSub, norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) hk).trans hx

theorem norm_le_one_of_int (x : PadicAlgCl l) (hx : IsIntegral ℤ_[l] x) : ‖x‖ ≤ 1 := by
  first
  | exact @_root_.GlobalTheory.IntegralNormLeOne.norm_le_one_of_isIntegral
  | exact _root_.GlobalTheory.IntegralNormLeOne.norm_le_one_of_isIntegral
  | (apply _root_.GlobalTheory.IntegralNormLeOne.norm_le_one_of_isIntegral <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralNormLeOne.norm_le_one_of_isIntegral <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralNormLeOne.norm_le_one_of_isIntegral <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralNormLeOne.norm_le_one_of_isIntegral ..)

theorem norm_le_one_of_mem (c : Coef l) {x : Qbar l} (hx : x ∈ c.O) : ‖x‖ ≤ 1 :=
  norm_le_one_of_int x ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) (⟨x, hx⟩ : c.O)).map c.O.val)

end GlobalTheory.BrTame


open GlobalTheory.BrTame in
theorem GlobalTheory.br_tame : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (c : Coef l) (n : ℕ) (w : Pl) (B : ValuationSubring Ω) (ψ : G ℚ Ω →* Multiplicative (ZMod (l ^ n))) (h : G ℚ Ω → Qbar l) (σ : G ℚ Ω), 1 ≤ n → IsPlaceOver B w → l ^ n ∣ normV w - 1 → (∃ τ ∈ Ine (F := ℚ) B, (ψ τ).toAdd = 1) → (∀ s, h s ∈ c.O) → (∀ s ∈ Dec (F := ℚ) B, ∀ t ∈ Dec (F := ℚ) B, Cg n (h (s * t)) (h s + h t)) → (∀ s ∈ Ine (F := ℚ) B, Cg n (h s) 0) → Cob2 c n (Dec (F := ℚ) B) (fun s t => (((ψ s).toAdd.val : ℕ) : Qbar l) * h t) → σ ∈ Dec (F := ℚ) B → Cg n (h σ) 0 := by
  intro l _ Ω _ _ _ c n w B ψ h σ hn hB hdiv ⟨τ, hτ, hψτ⟩ hO _ hIne ⟨u, hucont, huO, hu⟩ hσ
  set S := ballSub (l := l) ‖((l : ℕ) : Qbar l) ^ n‖ (norm_nonneg _) with hS
  have hu1 : ∀ s, ‖u s‖ ≤ 1 := fun s => norm_le_one_of_mem c (huO s)
  have heps : ∀ s ∈ Dec (F := ℚ) B, eps l s - 1 ∈ S := fun s hs => GlobalTheory.T.cyclotomicChar_congruent_one_on_decompositionGroup l Ω n w B hB hdiv hn s hs
  have hnat : ∀ k : ℕ, ‖((k : ℕ) : Qbar l)‖ ≤ 1 := fun k => IsUltrametricDist.norm_natCast_le_one _ k
  have hmul : ∀ k x : Qbar l, ‖k‖ ≤ 1 → x ∈ S → k * x ∈ S := fun k x hk hx => mul_mem_ballSub hk hx
  have hIne' : ∀ s ∈ Ine (F := ℚ) B, h s ∈ S := fun s hs => by
    have := cg_iff.1 (hIne s hs)
    rwa [sub_zero] at this
  have hIneDec : ∀ s ∈ Ine (F := ℚ) B, s ∈ Dec (F := ℚ) B := fun s hs => Ine_le_Dec B hs

  set T := ballSub (l := l) 1 zero_le_one with hT
  let M := T ⧸ S.comap T.subtype
  let f : G ℚ Ω → M := fun s => QuotientAddGroup.mk ⟨u s, hu1 s⟩
  have hf : ∀ s t, f s = f t ↔ u s - u t ∈ S := fun s t => by
    show (QuotientAddGroup.mk _ : M) = QuotientAddGroup.mk _ ↔ _
    rw [QuotientAddGroup.eq, AddSubgroup.mem_comap]
    change -u s + u t ∈ S ↔ _
    have e : -u s + u t = -(u s - u t) := by ring
    rw [e, S.neg_mem_iff]
  have hlpos : 0 < ‖((l : ℕ) : Qbar l) ^ n‖ := norm_pos_iff.2 (pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero))
  have htors : ∀ x : M, l ^ n • x = 0 := by
    intro x
    induction x using QuotientAddGroup.induction_on with
    | H y =>
      rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_comap, AddSubgroup.coe_subtype,
        AddSubgroup.coe_nsmul, nsmul_eq_mul, mem_ballSub, norm_mul, Nat.cast_pow]
      exact mul_le_of_le_one_right (norm_nonneg _) y.2
  have hloc : IsLocallyConstant (fun s : Ine (F := ℚ) B => f s) := by
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    have hc : Continuous (fun s : Ine (F := ℚ) B => u s) :=
      (hucont.mono (fun s hs => hIneDec s hs)).comp_continuous continuous_subtype_val (fun s => s.2)
    refine ⟨(fun s : Ine (F := ℚ) B => u s) ⁻¹' Metric.ball (u x) ‖((l : ℕ) : Qbar l) ^ n‖,
      Metric.isOpen_ball.preimage hc, Metric.mem_ball_self hlpos, fun y hy => ?_⟩
    rw [hf, mem_ballSub]
    have := Metric.mem_ball.1 hy
    rw [dist_eq_norm] at this
    exact this.le
  have hadd : ∀ s ∈ Ine (F := ℚ) B, ∀ t ∈ Ine (F := ℚ) B, f (s * t) = f s + f t := by
    intro s hs t ht
    have e : f s + f t = QuotientAddGroup.mk (⟨u s, hu1 s⟩ + ⟨u t, hu1 t⟩ : T) := rfl
    rw [e]
    show (QuotientAddGroup.mk _ : M) = QuotientAddGroup.mk _
    rw [QuotientAddGroup.eq, AddSubgroup.mem_comap]
    change -u (s * t) + (u s + u t) ∈ S
    have h1 := hu s (hIneDec s hs) t (hIneDec t ht)
    have h2 := hmul _ _ (hnat ((ψ s).toAdd.val)) (hIne' t ht)
    have h3 := hmul _ _ (hu1 t) (heps s (hIneDec s hs))
    rw [cg_iff] at h1
    have e2 : -u (s * t) + (u s + u t) =
        -((((ψ s).toAdd.val : ℕ) : Qbar l) * h t - (eps l s * u t - u (s * t) + u s))
          + (((ψ s).toAdd.val : ℕ) : Qbar l) * h t - u t * (eps l s - 1) := by ring
    rw [e2]
    exact S.sub_mem (S.add_mem (S.neg_mem h1) h2) h3
  have hconj := GlobalTheory.T.inertiaTorsionQuotient_conj_invariant_decomposition l Ω n w B M f hB hdiv hn htors hloc hadd σ hσ τ hτ
  rw [hf] at hconj
  set τ' := σ * τ * σ⁻¹ with hτ'
  have hτ'I : τ' ∈ Ine (F := ℚ) B := conj_mem_Ine hσ hτ
  have hprod : τ' * σ = σ * τ := by rw [hτ']; group
  have hψ' : ((ψ τ').toAdd.val : Qbar l) = 1 := by
    have e : ψ τ' = ψ τ := by rw [hτ', map_mul, map_mul, mul_comm (ψ σ), mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
    have hl1 : 1 < l ^ n := Nat.one_lt_pow (by omega) (Fact.out : l.Prime).one_lt
    rw [e, hψτ, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt hl1, Nat.cast_one]
  have hA := hu τ' (hIneDec τ' hτ'I) σ hσ
  have hB' := hu σ hσ τ (hIneDec τ hτ)
  dsimp only at hA hB'
  rw [cg_iff, hprod, hψ', one_mul] at hA
  rw [cg_iff] at hB'
  have hC := hmul _ _ (hnat ((ψ σ).toAdd.val)) (hIne' τ hτ)
  have hD := hmul _ _ (hu1 σ) (heps τ' (hIneDec τ' hτ'I))
  have hF := hmul _ _ (hu1 τ) (heps σ hσ)
  rw [cg_iff, sub_zero]
  have e : h σ = (h σ - (eps l τ' * u σ - u (σ * τ) + u τ')) + u σ * (eps l τ' - 1) + (u τ' - u τ)
      - ((((ψ σ).toAdd.val : ℕ) : Qbar l) * h τ - (eps l σ * u τ - u (σ * τ) + u σ))
      + (((ψ σ).toAdd.val : ℕ) : Qbar l) * h τ - u τ * (eps l σ - 1) := by ring
  rw [e]
  exact S.sub_mem (S.add_mem (S.sub_mem (S.add_mem (S.add_mem hA hD) hconj) hB') hC) hF
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.TameCochainCocycleExtensionStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

theorem _root_.GlobalTheory.T.tame_cochain_cocycle_extension : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (c : Coef l) (n : ℕ) (w : Pl) (B : ValuationSubring Ω) (ψ : G ℚ Ω →* Multiplicative (ZMod (l ^ n))) (h : G ℚ Ω → Qbar l) (σ : G ℚ Ω), 1 ≤ n → IsPlaceOver B w → l ^ n ∣ normV w - 1 → (∃ τ ∈ Ine (F := ℚ) B, (ψ τ).toAdd = 1) → (∀ s, h s ∈ c.O) → (∀ s ∈ Dec (F := ℚ) B, ∀ t ∈ Dec (F := ℚ) B, Cg n (h (s * t)) (h s + h t)) → (∀ s ∈ Ine (F := ℚ) B, Cg n (h s) 0) → Cob2 c n (Dec (F := ℚ) B) (fun s t => (((ψ s).toAdd.val : ℕ) : Qbar l) * h t) → σ ∈ Dec (F := ℚ) B → Cg n (h σ) 0 := by
  first | exact @GlobalTheory.br_tame | exact GlobalTheory.br_tame | (intros; apply GlobalTheory.br_tame <;> assumption)
end
end
