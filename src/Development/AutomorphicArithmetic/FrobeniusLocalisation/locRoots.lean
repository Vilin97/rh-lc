module

public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AutomorphicArithmetic.FrobeniusLocalisation.LocStab
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ZsmulGeneratorEqZeroOfProjection
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Decomp
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.CycLift
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.RootEqOfSubMem
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.TypeStar
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.EqZeroOfNegEq
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.CycBasic

-- Source module: Development.AutomorphicArithmetic.FrobeniusLocalisation.locOnto

section

@[expose] public section

open UpperTheory.HF

open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

theorem UpperTheory.HF.loc_onto :
    ∀ (l : ℕ) [Fact l.Prime] (L : Type) [Field L] [NumberField L] [IsGalois ℚ L] (J : L →+* PadicAlgCl l), ∃ P : Ideal (𝓞 L), P.IsPrime ∧ P.LiesOver (span {(l : ℤ)}) ∧ (∀ x : 𝓞 L, x ∈ P ↔ ‖J (x : L)‖ < 1) ∧ (∀ τ : L ≃ₐ[ℚ] L, τ ∈ MulAction.stabilizer _ P ↔ ∃ σ : (PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l), ∀ x : L, σ (J x) = J (τ x)) ∧ (∀ σ : (PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l), ∃ τ : L ≃ₐ[ℚ] L, ∀ x : L, σ (J x) = J (τ x)) ∧ Module.finrank ℚ_[l] (IntermediateField.adjoin ℚ_[l] (Set.range J)) = Nat.card (MulAction.stabilizer (L ≃ₐ[ℚ] L) P) := by
  intro l _ L _ _ _ J
  obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ L
  have hl : ‖(l : PadicAlgCl l)‖ < 1 := by
    rw [← PadicAlgCl.valuation_coe, PadicAlgCl.valuation_p l]
    have h1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
    simp only [one_div, NNReal.coe_inv, NNReal.coe_natCast]
    exact inv_lt_one_of_one_lt₀ h1
  let I : Ideal (𝓞 L) :=
    { carrier := {x : 𝓞 L | ‖J (x : L)‖ < 1}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        show ‖J ((a : L) + (b : L))‖ < 1
        rw [map_add (f := _)]
        exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
      zero_mem' := by simp
      smul_mem' := by
        intro c x hx
        simp only [Set.mem_setOf_eq] at hx ⊢
        show ‖J ((c : L) * (x : L))‖ < 1
        rw [map_mul, norm_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) (LocStab.norm_int_le J c)) hx }
  have hmem : ∀ x : 𝓞 L, x ∈ I ↔ ‖J (x : L)‖ < 1 := fun x => Iff.rfl
  have hIp : I.IsPrime := by
    refine ⟨?_, ?_⟩
    · rw [Ideal.ne_top_iff_one, hmem]
      simp
    · intro a b hab
      rw [hmem] at hab
      rw [hmem, hmem]
      have hab' : ‖J (a : L)‖ * ‖J (b : L)‖ < 1 := by
        rw [← norm_mul, ← map_mul]
        exact hab
      by_contra h
      push_neg at h
      nlinarith [h.1, h.2]
  have hlI : ((l : ℤ) : 𝓞 L) ∈ I := by
    rw [hmem]
    simpa using hl
  have hIne : I ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hlI
    have hne : ((l : ℤ) : 𝓞 L) ≠ 0 := by
      simp [(Fact.out : l.Prime).ne_zero]
    exact hne hlI
  let v : IsDedekindDomain.HeightOneSpectrum (𝓞 L) := ⟨I, hIp, hIne⟩
  have hlo : I.LiesOver (Ideal.span {(l : ℤ)}) := by
    constructor
    have hmax : (Ideal.span {(l : ℤ)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible
        (Nat.prime_iff_prime_int.mp (Fact.out : l.Prime)).irreducible
    refine hmax.eq_of_le (Ideal.comap_ne_top _ hIp.ne_top) ?_
    rw [Ideal.span_le, Set.singleton_subset_iff]
    show algebraMap ℤ (𝓞 L) (l : ℤ) ∈ I
    rw [eq_intCast]
    exact hlI
  refine ⟨I, hIp, hlo, hmem, ?_, ?_, ?_⟩
  · intro τ
    rw [MulAction.mem_stabilizer_iff]
    constructor
    · intro hτ
      have hr := LocStab.root_of_stab J α τ v hmem hτ
      have hint := (Algebra.IsAlgebraic.isAlgebraic (R := ℚ_[l]) (J α)).isIntegral
      have hmin : minpoly ℚ_[l] (J (τ α)) = minpoly ℚ_[l] (J α) :=
        (minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hint) hr (minpoly.monic hint)).symm
      obtain ⟨σ, hσ⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := ℚ_[l]) (E := PadicAlgCl l)).mp hmin
      refine ⟨σ, fun x => ?_⟩
      have hext := LocStab.ringHom_ext hα ((σ : PadicAlgCl l →+* PadicAlgCl l).comp J)
        (J.comp (τ : L →+* L)) (by simpa [AlgEquiv.smul_def] using hσ)
      exact RingHom.congr_fun hext x
    · rintro ⟨σ, hσ⟩
      apply LocStab.stab_of_root J hα τ v hmem
      rw [← hσ α]
      simp [Polynomial.aeval_algEquiv]
  · intro σ
    obtain ⟨s, hs⟩ := LocStab.exists_aut_of_root J α (r := σ (J α)) (by simp [Polynomial.aeval_algEquiv])
    refine ⟨s, fun x => ?_⟩
    have hext := LocStab.ringHom_ext hα ((σ : PadicAlgCl l →+* PadicAlgCl l).comp J)
      (J.comp (s : L →+* L)) (by simpa using hs.symm)
    exact RingHom.congr_fun hext x
  · exact LocStab.finrank_adjoin_range_eq_card_stabilizer l L J v hmem
end
end

-- Source module: Development.AutomorphicArithmetic.FrobeniusLocalisation.locRoots

section

@[expose] public section

open UpperTheory.HF

open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

section
open Formalism.HC.Der Formalism.TwoAdicCyclotomicDecomposition

private theorem stab_iff (N : ℕ) [NeZero N] (l : ℕ) [Fact l.Prime] (Q : Ideal (𝓞 (Cond.Cyc N))) [Q.IsPrime]
    [Q.LiesOver (span {(l : ℤ)})] (u : (ZMod N)ˣ) :
    tauN N u ∈ MulAction.stabilizer _ Q ↔ ∃ k : ℕ, (u : ZMod N).val ≡ l ^ k [MOD ordCompl[l] N] := by
  set M := ordCompl[l] N with hM
  have hMN : M ∣ N := Nat.ordCompl_dvd N l
  have hlM : l.Coprime M := Nat.coprime_ordCompl (Fact.out : l.Prime) (NeZero.ne N)
  obtain ⟨u0, hu0⟩ := exists_unit_modEq (N := N) hMN l hlM
  have hF : IsArithFrobAt ℤ (tauN N u0) Q := tauN_frob N l Q u0 hu0
  have hu0' : ((ZMod.unitsMap hMN u0 : (ZMod M)ˣ) : ZMod M) = (l : ZMod M) :=
    (val_modEq_iff hMN u0 l).mp hu0
  constructor
  · intro hs
    obtain ⟨k, ρ, hρ, hρeq⟩ := Decomp.stab_eq_inertia_mul l Q (tauN N u0) (tauN N u) hF hs
    obtain ⟨w, rfl⟩ := (tauN N).surjective ρ
    refine ⟨k, ?_⟩
    have hw1 : ZMod.unitsMap hMN w = 1 :=
      (val_modEq_one_iff hMN w).mp ((tauN_inertia_iff N l Q w).mp hρ)
    have huw : u = w * u0 ^ k := (tauN N).injective (by rw [map_mul, map_pow]; exact hρeq)
    rw [val_modEq_iff hMN, huw, map_mul, map_pow, hw1, one_mul, Units.val_pow_eq_pow_val, hu0',
      Nat.cast_pow]
  · rintro ⟨k, hk⟩
    have hw1 : ZMod.unitsMap hMN (u * (u0 ^ k)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_pow, mul_inv_eq_one]
      apply Units.ext
      rw [(val_modEq_iff hMN u _).mp hk, Units.val_pow_eq_pow_val, hu0', Nat.cast_pow]
    have hwin := (tauN_inertia_iff N l Q (u * (u0 ^ k)⁻¹)).mpr ((val_modEq_one_iff hMN _).mpr hw1)
    have hwst := Decomp.mem_stab_of _ Q (smul_mem_of_inertia _ Q hwin)
    have hFst := IsArithFrobAt.mem_stabilizer hF
    have hu : u = (u * (u0 ^ k)⁻¹) * u0 ^ k := by rw [inv_mul_cancel_right]
    rw [hu, map_mul, map_pow]
    exact Subgroup.mul_mem _ hwst (Subgroup.pow_mem _ hFst k)

private theorem act_of (N : ℕ) [NeZero N] {K : Type*} [Field K] (J : Cond.Cyc N →+* K) (σ : K →+* K) (u : (ZMod N)ˣ)
    (h : ∀ x, σ (J x) = J (tauN N u x)) (x : K) (hx : x ^ N = 1) : σ x = x ^ (u : ZMod N).val := by
  have hζ := (zO_prim N).map_of_injective (f := algebraMap (𝓞 (Cond.Cyc N)) (Cond.Cyc N))
    (FaithfulSMul.algebraMap_injective _ _)
  have hJ := hζ.map_of_injective J.injective
  obtain ⟨i, -, rfl⟩ := hJ.eq_pow_of_pow_eq_one hx
  have hg : IsCyclotomicExtension.Rat.galEquivZMod N (Cond.Cyc N) (tauN N u) = u :=
    MulEquiv.apply_symm_apply _ _
  have hτ : tauN N u (algebraMap (𝓞 (Cond.Cyc N)) (Cond.Cyc N) (zO N)) =
      (algebraMap (𝓞 (Cond.Cyc N)) (Cond.Cyc N) (zO N)) ^ (u : ZMod N).val := by
    rw [IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq N (Cond.Cyc N) (tauN N u) hζ.pow_eq_one,
      hg]
  rw [map_pow, h, hτ, map_pow]
  ring

end

theorem UpperTheory.HF.loc_roots :
    ∀ (l : ℕ) [Fact l.Prime] (M : ℕ), 0 < M → (∀ σ : (PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l), ∃ (u : (ZMod M)ˣ) (j : ℕ), (u : ZMod M).val ≡ l ^ j [MOD ordCompl[l] M] ∧ ∀ x : PadicAlgCl l, x ^ M = 1 → σ x = x ^ (u : ZMod M).val) ∧ ∀ (u : (ZMod M)ˣ) (j : ℕ), (u : ZMod M).val ≡ l ^ j [MOD ordCompl[l] M] → ∃ σ : (PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l), ∀ x : PadicAlgCl l, x ^ M = 1 → σ x = x ^ (u : ZMod M).val := by
  intro l _ M hM
  haveI : NeZero M := ⟨hM.ne'⟩
  haveI := Formalism.HC.Der.cyc_isGalois M
  let J : Cond.Cyc M →+* PadicAlgCl l := (IsAlgClosed.lift : Cond.Cyc M →ₐ[ℚ] PadicAlgCl l).toRingHom
  obtain ⟨P, hPp, hPlo, -, hstab, hsurj, -⟩ := UpperTheory.HF.loc_onto l (Cond.Cyc M) J
  haveI := hPp
  haveI := hPlo
  constructor
  · intro σ
    obtain ⟨τ, hτ⟩ := hsurj σ
    obtain ⟨u, rfl⟩ := (Formalism.HC.Der.tauN M).surjective τ
    have hst : Formalism.HC.Der.tauN M u ∈ MulAction.stabilizer _ P := (hstab _).mpr ⟨σ, hτ⟩
    obtain ⟨k, hk⟩ := (stab_iff M l P u).mp hst
    exact ⟨u, k, hk, fun x hx => act_of M J (σ : PadicAlgCl l →+* PadicAlgCl l) u hτ x hx⟩
  · intro u j hj
    obtain ⟨σ, hσ⟩ := (hstab (Formalism.HC.Der.tauN M u)).mp ((stab_iff M l P u).mpr ⟨j, hj⟩)
    exact ⟨σ, fun x hx => act_of M J (σ : PadicAlgCl l →+* PadicAlgCl l) u hσ x hx⟩
end
end
