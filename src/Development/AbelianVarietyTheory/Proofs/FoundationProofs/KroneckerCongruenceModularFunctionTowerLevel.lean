module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiagMod
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPrimitiveQuotientLevelPrimeTo
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
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeTranslateNormProductEqOfDvdStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HahnSeriesCoeffRingHomMapCoeff
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPrimitiveQuotientLevelPrimeToStatement

section

@[expose] public section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

theorem _root_.GlobalTheory.T.exists_primitive_quotient_level_prime_to : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (l M₀ : ℕ), l.Prime → 0 < M₀ → ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S → ∀ V : ValuationSubring Ω, ((q : ℕ) : Ω) ∈ V.nonunits → ∀ (k : ℕ) (f : X.K), f ≠ 0 → Lev X (M₀ * l ^ k) f → ∃ (M' : ℕ) (a b : X.K) (c : Ω), 0 < M' ∧ Nat.Coprime q M' ∧ M₀ * l ^ k ∣ M' ∧ Lev X M' a ∧ Lev X M' b ∧ Prim X V a ∧ Prim X V b ∧ c ≠ 0 ∧ f * b = algebraMap Ω X.K c * a := by
  first | exact @GlobalTheory.KZ.ES.Quot.quot_prim | exact GlobalTheory.KZ.ES.Quot.quot_prim | (intros; apply GlobalTheory.KZ.ES.Quot.quot_prim <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.KroneckerCongruenceFrobeniusDiag

section

@[expose] public section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

noncomputable section

namespace GlobalTheory.KZ.ES


open GlobalTheory.KroneckerCongruence in
theorem kron_frob_diag : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε),
    ∀ (q : ℕ), q.Prime → ∀ (V : ValuationSubring Ω) (s : Ω ≃ₐ[ℚ] Ω), FrobV V q s → ∀ a : X.K, IntC X V a →
    SmallC X V (X.sl (toGQ !![(q : ℤ), 0; 0, 1]) a - (X.gal s.symm a) ^ q) := by
  intro Ω _ _ _ ε X q hq V s hs a ha r
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  have hε : Function.Injective ε := ε.injective
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne_zero
  set ρ := IsLocalRing.residue V with hρ_def
  have hρ0 : ∀ x : V, ρ x = 0 ↔ V.valuation (x : Ω) < 1 := fun x => by
    rw [hρ_def, IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
  haveI : CharP (IsLocalRing.ResidueField V) q := (CharP.charP_iff_prime_eq_zero hq).2 (by
    have : ρ (q : V) = 0 := (hρ0 _).2 (by simpa [ValuationSubring.mem_nonunits_iff] using hs.1)
    simpa using this)
  have hfrob : ∀ x : V, ρ ⟨s x, (hs.2 x x.2).1⟩ = ρ x ^ q := by
    intro x
    rw [← sub_eq_zero, ← map_pow, ← map_sub, hρ0]
    simpa using (hs.2 x x.2).2.2
  set c := X.exp a with hc
  have hdq : 0 < (!![(q : ℤ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ).det := by
    simp [Matrix.det_fin_two]; exact_mod_cast hq.pos
  have hA : (X.exp (X.sl (toGQ !![(q : ℤ), 0; 0, 1]) a)).coeff r = c.coeff (r / q) := by
    have h := X.exp_upper (toGQ !![(q : ℤ), 0; 0, 1]) (by rw [ent_toGQ _ hdq]; simp) a (r / q)
    rw [ent_toGQ _ hdq, ent_toGQ _ hdq, ent_toGQ _ hdq] at h
    simp [eOm_zero hε, hq0] at h
    rw [← h]
  set B := X.exp (X.gal s.symm a) with hB
  have hBc : ∀ t, B.coeff t = s.symm (c.coeff t) := fun t => by rw [hB, X.gal_exp]
  have hBV : ∀ t, B.coeff t ∈ V := fun t => by rw [hBc]; exact (hs.2 _ (ha t)).2.1
  have hBq : X.exp ((X.gal s.symm a) ^ q) = hahnSeriesCoeffRingHomMap V.subtype (liftV V B hBV ^ q) := by
    rw [map_pow, map_pow, map_liftV]
  set y : V := (liftV V B hBV ^ q).coeff r with hy_def
  have hy : (X.exp ((X.gal s.symm a) ^ q)).coeff r = (y : Ω) := by rw [hBq, hahnSeriesCoeffRingHomMap_coeff]; rfl
  have hρy : ρ y = ρ ⟨c.coeff (r / q), ha _⟩ := by
    have h1 : ρ y = (hahnSeriesCoeffRingHomMap ρ (liftV V B hBV ^ q)).coeff r := by rw [hahnSeriesCoeffRingHomMap_coeff]
    rw [h1, map_pow, coeff_pow_char q, hahnSeriesCoeffRingHomMap_coeff]
    have h2 : (liftV V B hBV).coeff (r / q) = ⟨s.symm (c.coeff (r / q)), (hs.2 _ (ha _)).2.1⟩ :=
      Subtype.ext (hBc _)
    rw [h2, ← hfrob]
    congr 1
    apply Subtype.ext
    simp
  rw [map_sub, HahnSeries.coeff_sub, hA, hy]
  have hmem : c.coeff (r / q) - (y : Ω) = ((⟨c.coeff (r / q), ha _⟩ - y : V) : Ω) := rfl
  rw [hmem, ValuationSubring.mem_nonunits_iff, ← hρ0, map_sub, hρy, sub_self]

end GlobalTheory.KZ.ES
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.KroneckerCongruenceFrobeniusDiagStatement

section

@[expose] public section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

theorem _root_.GlobalTheory.T.kronecker_congruence_frobenius_diag : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), ∀ (q : ℕ), q.Prime → ∀ (V : ValuationSubring Ω) (s : Ω ≃ₐ[ℚ] Ω), FrobV V q s → ∀ a : X.K, IntC X V a → SmallC X V (X.sl (toGQ !![(q : ℤ), 0; 0, 1]) a - (X.gal s.symm a) ^ q) := by
  first | exact @GlobalTheory.KZ.ES.kron_frob_diag | exact GlobalTheory.KZ.ES.kron_frob_diag | (intros; apply GlobalTheory.KZ.ES.kron_frob_diag <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.NqSubGalSmall

section

@[expose] public section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

noncomputable section

namespace GlobalTheory.KZ.ES


open GlobalTheory.KroneckerCongruence in
theorem nq_sub_gal_small : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε),
    ∀ (M q : ℕ), 0 < M → q.Prime → ∀ (V : ValuationSubring Ω) (s : Ω ≃ₐ[ℚ] Ω), FrobV V q s →
    ∀ a : X.K, Lev X M a → IntC X V a → SmallC X V (Nq X M q a - X.gal s a) := by
  intro Ω _ _ _ ε X M q hM hq V s hFr f hf hfV
  obtain ⟨hqV, hs⟩ := hFr
  have hε : Function.Injective ε := ε.injective
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne_zero
  set ρ := IsLocalRing.residue V with hρ_def
  have hρ0 : ∀ x : V, ρ x = 0 ↔ V.valuation (x : Ω) < 1 := fun x => by
    rw [hρ_def, IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
  haveI : CharP (IsLocalRing.ResidueField V) q := (CharP.charP_iff_prime_eq_zero hq).2 (by
    have : ρ (q : V) = 0 := (hρ0 _).2 (by simpa [ValuationSubring.mem_nonunits_iff] using hqV)
    simpa using this)
  have hfrob : ∀ x : V, ρ ⟨s x, (hs x x.2).1⟩ = ρ x ^ q := by
    intro x
    rw [← sub_eq_zero, ← map_pow, ← map_sub, hρ0]
    simpa using (hs x x.2).2.2
  set c := X.exp f with hc
  have hdet : ∀ j : ℕ, 0 < (!![1, ((j : ℤ) * M : ℤ); 0, (q : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ).det := by
    intro j; simp [Matrix.det_fin_two]; exact_mod_cast hq.pos
  have hFj : ∀ (j : ℕ) (t : ℚ), (X.exp (X.sl (toGQ !![1, ((j : ℤ) * M : ℤ); 0, (q : ℤ)]) f)).coeff t =
      eOm ε (t * j * M) * c.coeff (t * q) := by
    intro j t
    have h := X.exp_upper (toGQ !![1, ((j : ℤ) * M : ℤ); 0, (q : ℤ)]) (by rw [ent_toGQ _ (hdet j)]; simp) f (t * q)
    rw [ent_toGQ _ (hdet j), ent_toGQ _ (hdet j), ent_toGQ _ (hdet j)] at h
    simp at h
    convert h using 2 <;> first | field_simp | (congr 1; field_simp)
  have hw : ∀ (j : ℕ) (t : ℚ), c.coeff (t * q) ≠ 0 → ∃ h : eOm ε (t * j * M) ∈ V, ρ ⟨_, h⟩ = 1 := by
    intro j t ht
    have h1 : eOm ε (t * j * M) ^ q = 1 := by
      rw [← eOm_mul_nat hε, show (q : ℚ) * (t * j * M) = j * (t * q * M) by ring, eOm_mul_nat hε,
        eOm_level X M f hf _ ht, one_pow]
    have hmem : eOm ε (t * j * M) ∈ V := mem_of_pow_eq_one V hq.ne_zero h1
    refine ⟨hmem, ?_⟩
    have h2 : (⟨_, hmem⟩ : V) ^ q = 1 := Subtype.ext (by simpa using h1)
    have h3 : (ρ ⟨_, hmem⟩ - 1) ^ q = 0 := by rw [sub_pow_char, ← map_pow, h2, map_one, one_pow, sub_self]
    exact sub_eq_zero.1 (pow_eq_zero_iff hq.ne_zero |>.1 h3)
  have memF : ∀ (j : ℕ) (t : ℚ), (X.exp (X.sl (toGQ !![1, ((j : ℤ) * M : ℤ); 0, (q : ℤ)]) f)).coeff t ∈ V := by
    intro j t
    rw [hFj]
    by_cases h0 : c.coeff (t * q) = 0
    · rw [h0, mul_zero]; exact zero_mem V
    · exact mul_mem (hw j t h0).1 (hfV _)
  have redF : ∀ (j : ℕ) (t : ℚ), ρ ⟨_, memF j t⟩ = ρ ⟨_, hfV (t * q)⟩ := by
    intro j t
    by_cases h0 : c.coeff (t * q) = 0
    · exact congrArg ρ (Subtype.ext (by simp only; rw [hFj, h0, mul_zero]))
    · obtain ⟨hm, h1⟩ := hw j t h0
      have e : (⟨_, memF j t⟩ : V) = ⟨_, hm⟩ * ⟨_, hfV (t * q)⟩ :=
        Subtype.ext (by simp only [MulMemClass.mk_mul_mk]; rw [hFj])
      rw [e, map_mul, h1, one_mul]
  have memC : ∀ t : ℚ, (X.exp (X.gal s f)).coeff t ∈ V := by
    intro t; rw [X.gal_exp]; exact (hs _ (hfV t)).1
  set LF : ℕ → HahnSeries ℚ V := fun j => liftV V _ (memF j) with hLF
  set LC := liftV V _ memC with hLC
  have h1 : ∀ j, hahnSeriesCoeffRingHomMap ρ (LF j) = hahnSeriesCoeffRingHomMap ρ (LF 0) := by
    intro j; ext t; rw [hahnSeriesCoeffRingHomMap_coeff, hahnSeriesCoeffRingHomMap_coeff]; exact (redF j t).trans (redF 0 t).symm
  have h2 : hahnSeriesCoeffRingHomMap ρ (LF 0) ^ q = hahnSeriesCoeffRingHomMap ρ LC := by
    ext t
    rw [coeff_pow_char q, hahnSeriesCoeffRingHomMap_coeff, hahnSeriesCoeffRingHomMap_coeff]
    show ρ ⟨_, memF 0 (t / q)⟩ ^ q = ρ ⟨_, memC t⟩
    rw [redF 0 (t / q), ← hfrob]
    exact congrArg ρ (Subtype.ext (by simp only; rw [X.gal_exp, div_mul_cancel₀ t hq0]))
  have hexp : X.exp ((∏ j ∈ Finset.range q, X.sl (toGQ !![1, ((j : ℤ) * M : ℤ); 0, (q : ℤ)]) f) - X.gal s f) =
      hahnSeriesCoeffRingHomMap V.subtype ((∏ j ∈ Finset.range q, LF j) - LC) := by
    simp only [map_sub, map_prod, hLF, hLC, map_liftV]
  have hW : hahnSeriesCoeffRingHomMap ρ ((∏ j ∈ Finset.range q, LF j) - LC) = 0 := by
    rw [map_sub, map_prod, Finset.prod_congr rfl (fun j _ => h1 j), Finset.prod_const, Finset.card_range, h2, sub_self]
  intro r
  unfold Nq
  rw [hexp, hahnSeriesCoeffRingHomMap_coeff, ValuationSubring.mem_nonunits_iff]
  refine (hρ0 (((∏ j ∈ Finset.range q, LF j) - LC).coeff r)).1 ?_
  rw [← hahnSeriesCoeffRingHomMap_coeff, hW]
  rfl

end GlobalTheory.KZ.ES
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.KroneckerCongruenceModularFunctionTowerLevel

section

@[expose] public section

noncomputable section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

namespace GlobalTheory.KZ.ES

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem kc_val_one_of_inv {V : ValuationSubring Ω} {x : Ω} (hx : x ∈ V) (hi : x⁻¹ ∈ V) (h0 : x ≠ 0) :
    V.valuation x = 1 := by
  have h1 := (V.valuation_le_one_iff x).2 hx
  have h2 := (V.valuation_le_one_iff x⁻¹).2 hi
  rw [map_inv₀] at h2
  have hne : V.valuation x ≠ 0 := by simpa using h0
  exact le_antisymm h1 ((inv_le_one₀ (zero_lt_iff.2 hne)).1 h2)

theorem kc_inv_of_val_one {V : ValuationSubring Ω} {x : Ω} (h : V.valuation x = 1) :
    x ∈ V ∧ x⁻¹ ∈ V ∧ x ≠ 0 := by
  have h0 : x ≠ 0 := by rintro rfl; simp at h
  refine ⟨(V.valuation_le_one_iff x).1 h.le, (V.valuation_le_one_iff x⁻¹).1 ?_, h0⟩
  rw [map_inv₀, h, inv_one]

theorem kc_prim_gal (X : Tower Ω ε) (V : ValuationSubring Ω) (s : Ω ≃ₐ[ℚ] Ω) (hs : ∀ x ∈ V, s x ∈ V)
    {a : X.K} (ha : Prim X V a) : Prim X V (X.gal s a) := by
  obtain ⟨hI, r, hr⟩ := ha
  refine ⟨fun r' => by rw [X.gal_exp]; exact hs _ (hI r'), r, ?_⟩
  rw [X.gal_exp]
  obtain ⟨h1, h2, h3⟩ := kc_inv_of_val_one hr
  exact kc_val_one_of_inv (hs _ h1) (by rw [← map_inv₀]; exact hs _ h2) (by simpa using h3)

theorem kc_ne_zero_of_prim {X : Tower Ω ε} {V : ValuationSubring Ω} {a : X.K} (ha : Prim X V a) : a ≠ 0 := by
  rintro rfl
  obtain ⟨_, r, hr⟩ := ha
  simp at hr

theorem kc_Nq_mul (X : Tower Ω ε) (M q : ℕ) (f g : X.K) : Nq X M q (f * g) = Nq X M q f * Nq X M q g := by
  simp only [Nq, map_mul, Finset.prod_mul_distrib]

theorem kc_Nq_const (X : Tower Ω ε) (M q : ℕ) (c : Ω) (a : X.K) :
    Nq X M q (algebraMap Ω X.K c * a) = algebraMap Ω X.K c ^ q * Nq X M q a := by
  simp only [Nq, map_mul, AlgEquiv.commutes, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]

theorem kc_Nq_ne_zero (X : Tower Ω ε) (M q : ℕ) {f : X.K} (hf : f ≠ 0) : Nq X M q f ≠ 0 := by
  simp only [Nq]
  exact Finset.prod_ne_zero_iff.2 fun j _ => by simpa using hf

theorem kc_gal_const (X : Tower Ω ε) (s : Ω ≃ₐ[ℚ] Ω) (c : Ω) :
    X.gal s (algebraMap Ω X.K c) = algebraMap Ω X.K (s c) := by
  apply (X.exp : X.K →+* HahnSeries ℚ Ω).injective
  ext r
  show (X.exp (X.gal s (algebraMap Ω X.K c))).coeff r = (X.exp (algebraMap Ω X.K (s c))).coeff r
  rw [X.gal_exp, AlgHom.commutes, AlgHom.commutes]
  have e : ∀ x : Ω, (algebraMap Ω (HahnSeries ℚ Ω) x).coeff r = if r = 0 then x else 0 := by
    intro x
    rw [HahnSeries.algebraMap_apply']
    have : algebraMap Ω (PowerSeries Ω) x = PowerSeries.C x := rfl
    rw [this, HahnSeries.ofPowerSeries_C, HahnSeries.C_apply, HahnSeries.coeff_single]
    simp
  rw [e, e]
  split_ifs <;> simp

theorem kc_div_sub_one {L : Type} [Field L] (W : ValuationSubring L) {x y : L} (hy : W.valuation y = 1)
    (h : W.valuation (x - y) < 1) : W.valuation (x / y - 1) < 1 := by
  have hy0 : y ≠ 0 := by rintro rfl; simp at hy
  rw [show x / y - 1 = (x - y) / y by field_simp, map_div₀, hy, div_one]
  exact h

theorem kc_quot_one {L : Type} [Field L] (W : ValuationSubring L) {x y : L} (hx : W.valuation (x - 1) < 1)
    (hy : W.valuation (y - 1) < 1) : W.valuation (x / y - 1) < 1 := by
  have hy1 : W.valuation y = 1 := by
    have := Valuation.map_one_add_of_lt W.valuation hy
    simpa using this
  apply kc_div_sub_one W hy1
  have e : x - y = (x - 1) - (y - 1) := by ring
  rw [e]
  exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt hx hy)

theorem kron_cong_level : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (l M₀ : ℕ), l.Prime → 0 < M₀ → ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S → ∀ (V : ValuationSubring Ω) (s : Ω ≃ₐ[ℚ] Ω), FrobV V q s → ∀ W : ValuationSubring X.K, Dom X V W → ∀ (k : ℕ) (f : X.K), f ≠ 0 → Lev X (M₀ * l ^ k) f → (∃ c : Ω, W.valuation (algebraMap Ω X.K c * Nq X (M₀ * l ^ k) q f / X.gal s f - 1) < 1) ∧ ∃ c : Ω, W.valuation (algebraMap Ω X.K c * X.sl (toGQ !![(q : ℤ), 0; 0, 1]) f / (X.gal s.symm f) ^ q - 1) < 1 := by
  intro Ω _ _ _ ε X hj l M₀ hl hM₀
  obtain ⟨S, hS⟩ := GlobalTheory.T.exists_primitive_quotient_level_prime_to ε X hj l M₀ hl hM₀
  refine ⟨S, fun q hq hqS V s hF W hD k f hf hlev => ?_⟩
  obtain ⟨M', a, b, c, hM', hcop, hdvd, hla, hlb, hpa, hpb, hc, hfb⟩ := hS q hq hqS V hF.1 k f hf hlev
  have ha0 := kc_ne_zero_of_prim hpa
  have hb0 := kc_ne_zero_of_prim hpb
  have hsV : ∀ x ∈ V, s x ∈ V := fun x hx => (hF.2 x hx).1
  have hsV' : ∀ x ∈ V, s.symm x ∈ V := fun x hx => (hF.2 x hx).2.1
  have hC : algebraMap Ω X.K c ≠ 0 := (_root_.map_ne_zero _).2 hc
  have hgal : ∀ (t : Ω ≃ₐ[ℚ] Ω) (g : X.K), g ≠ 0 → X.gal t g ≠ 0 := fun t g hg => by simpa using hg
  have hE : ∀ t : Ω ≃ₐ[ℚ] Ω, X.gal t f = algebraMap Ω X.K (t c) * X.gal t a / X.gal t b := fun t => by
    rw [eq_div_iff (hgal t b hb0), ← map_mul, hfb, map_mul, kc_gal_const]
  have hC' : ∀ t : Ω ≃ₐ[ℚ] Ω, algebraMap Ω X.K (t c) ≠ 0 := fun t => (_root_.map_ne_zero _).2 (by simpa using hc)
  constructor
  · refine ⟨s c / c ^ q, ?_⟩
    have hN : Nq X (M₀ * l ^ k) q f = Nq X M' q f := GlobalTheory.T.heckeTranslateNormProduct_eq_of_dvd ε X _ _ q f hq.pos hdvd hcop hlev
    have A1 := kc_div_sub_one W (hD.2.2 _ (kc_prim_gal X V s hsV hpa))
      (hD.2.1 _ (GlobalTheory.KZ.ES.nq_sub_gal_small ε X M' q hM' hq V s hF a hla hpa.1))
    have B1 := kc_div_sub_one W (hD.2.2 _ (kc_prim_gal X V s hsV hpb))
      (hD.2.1 _ (GlobalTheory.KZ.ES.nq_sub_gal_small ε X M' q hM' hq V s hF b hlb hpb.1))
    have hNb := kc_Nq_ne_zero X M' q hb0
    have E1 : Nq X M' q f = algebraMap Ω X.K c ^ q * Nq X M' q a / Nq X M' q b := by
      rw [eq_div_iff hNb, ← kc_Nq_mul, hfb, kc_Nq_const]
    have key : algebraMap Ω X.K (s c / c ^ q) * Nq X (M₀ * l ^ k) q f / X.gal s f
        = (Nq X M' q a / X.gal s a) / (Nq X M' q b / X.gal s b) := by
      have h1 := hgal s a ha0
      have h2 := hgal s b hb0
      have h3 := hC' s
      rw [hN, E1, hE s, map_div₀, map_pow]
      field_simp
    rw [key]
    exact kc_quot_one W A1 B1
  · refine ⟨(s.symm c) ^ q / c, ?_⟩
    have A1 := kc_div_sub_one W (by rw [map_pow, hD.2.2 _ (kc_prim_gal X V s.symm hsV' hpa), one_pow])
      (hD.2.1 _ (GlobalTheory.T.kronecker_congruence_frobenius_diag ε X q hq V s hF a hpa.1))
    have B1 := kc_div_sub_one W (by rw [map_pow, hD.2.2 _ (kc_prim_gal X V s.symm hsV' hpb), one_pow])
      (hD.2.1 _ (GlobalTheory.T.kronecker_congruence_frobenius_diag ε X q hq V s hF b hpb.1))
    generalize toGQ !![(q : ℤ), 0; 0, 1] = T at A1 B1 ⊢
    have hTb : X.sl T b ≠ 0 := by simpa using hb0
    have E1 : X.sl T f = algebraMap Ω X.K c * X.sl T a / X.sl T b := by
      rw [eq_div_iff hTb, ← map_mul, hfb, map_mul, AlgEquiv.commutes]
    have key : algebraMap Ω X.K ((s.symm c) ^ q / c) * X.sl T f / (X.gal s.symm f) ^ q
        = (X.sl T a / (X.gal s.symm a) ^ q) / (X.sl T b / (X.gal s.symm b) ^ q) := by
      have h1 := hgal s.symm a ha0
      have h2 := hgal s.symm b hb0
      have h3 := hC' s.symm
      rw [E1, hE s.symm, map_div₀, map_pow, div_pow, mul_pow]
      field_simp
    rw [key]
    exact kc_quot_one W A1 B1

end GlobalTheory.KZ.ES
end
end
end
