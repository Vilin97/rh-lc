module

public import Development.AbelianVarietyTheory.Definitions.Foundations.EeProd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CompletedLaurentIsDVRStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlgebraMapZpInjective
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.Integral
public import Mathlib.RingTheory.AdicCompletion.Completeness
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlgebraMapZpInjective
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralOfExpansionSumEqPrimePowMulIsEvalStatement
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.Foundations.EeProd
import Development.AbelianVarietyTheory.Definitions.Foundations.ExpUpper
public import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCombinationMulEqReparametrizationImage

section

@[expose] public section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois GlobalTheory.GeoFix

namespace GlobalTheory.GeoFix

theorem inR_algebraMap {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]
    {T : Tower p Ω} {n : ℕ} {ψ : O0 p →+* Ω} (h : IsReb T n ψ) (c : O0 p) :
    ∃ c' : O0 p, ψ c' = algebraMap (O0 p) Ω c := by
  have hmem : algebraMap (O0 p) Ω c ∈ ψ.range := by
    rw [h.rng]
    exact Subalgebra.algebraMap_mem _ c
  exact hmem

theorem inR_pow {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]
    {ψ : O0 p →+* Ω} {x : Ω} (hx : InR ψ x) (k : ℕ) : InR ψ (x ^ k) := by
  induction k with
  | zero => simpa using inR_psi ψ 1
  | succ k ih => rw [pow_succ]; exact inR_mul ih hx

theorem exists_inR_mul_eq_psi : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ (T : Tower p Ω) (n : ℕ) (ψ : O0 p →+* Ω), IsReb T n ψ → ∀ N : Ω, GlobalTheory.GeoFix.InR ψ N → N ≠ 0 →
    ∃ (N' : Ω) (D : O0 p), GlobalTheory.GeoFix.InR ψ N' ∧ D ≠ 0 ∧ N * N' = ψ D := by
  intro p _ Ω _ _ hc T n ψ h N hN hN0
  obtain ⟨f, hfm, hf⟩ : IsIntegral (O0 p) N := hN.isInt h
  have key : ∀ k : ℕ, ∀ f : Polynomial (O0 p), f.natDegree = k → f.Monic → Polynomial.eval₂ (algebraMap (O0 p) Ω) N f = 0 →
      ∃ (N' : Ω) (D : O0 p), InR ψ N' ∧ D ≠ 0 ∧ N * N' = ψ D := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro f hk hfm hf
      by_cases h0 : f.coeff 0 = 0
      · obtain ⟨g, rfl⟩ := Polynomial.X_dvd_iff.2 h0
        have hgm : g.Monic := Polynomial.Monic.of_mul_monic_left Polynomial.monic_X hfm
        have hgdeg : g.natDegree < k := by
          rw [← hk, Polynomial.natDegree_X_mul hgm.ne_zero]; omega
        refine ih _ hgdeg g rfl hgm ?_
        rw [Polynomial.eval₂_mul, Polynomial.eval₂_X] at hf
        exact (mul_eq_zero.1 hf).resolve_left hN0
      · obtain ⟨g, hg⟩ := Polynomial.X_dvd_iff.2 (show (f - Polynomial.C (f.coeff 0)).coeff 0 = 0 by simp)
        obtain ⟨D, hD⟩ := inR_algebraMap h (-f.coeff 0)
        refine ⟨Polynomial.eval₂ (algebraMap (O0 p) Ω) N g, D, ?_, ?_, ?_⟩
        · rw [Polynomial.eval₂_eq_sum_range]
          refine inR_sum _ _ fun i _ => ?_
          obtain ⟨c', hc'⟩ := inR_algebraMap h (g.coeff i)
          rw [← hc']
          exact inR_mul (inR_psi ψ c') (inR_pow hN i)
        · rintro rfl
          rw [map_zero, map_neg] at hD
          apply h0
          apply hc.inj
          rw [map_zero (algebraMap (O0 p) Ω)]
          exact neg_eq_zero.mp hD.symm
        · have hf' : f = Polynomial.X * g + Polynomial.C (f.coeff 0) := by
            rw [← hg]; ring
          rw [hf', Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_X, Polynomial.eval₂_C] at hf
          rw [hD, map_neg]
          linear_combination hf
  exact key _ f rfl hfm hf

end GlobalTheory.GeoFix
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCombinationMulEqReparametrizationImageStatement

section

@[expose] public section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois GlobalTheory.GeoFix

theorem _root_.GlobalTheory.T.exists_combination_mul_eq_reparametrization_image : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω) (n : ℕ) (ψ : O0 p →+* Ω), IsReb T n ψ → ∀ N : Ω, GlobalTheory.GeoFix.InR ψ N → N ≠ 0 → ∃ (N' : Ω) (D : O0 p), GlobalTheory.GeoFix.InR ψ N' ∧ D ≠ 0 ∧ N * N' = ψ D := by
  first | exact @GlobalTheory.GeoFix.exists_inR_mul_eq_psi | exact GlobalTheory.GeoFix.exists_inR_mul_eq_psi | (intros; apply GlobalTheory.GeoFix.exists_inR_mul_eq_psi <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLaurentSeriesSumCongruentModPPow

section

@[expose] public section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois GlobalTheory.GeoFix

noncomputable section

namespace GlobalTheory.GeoFix

theorem exists_lau_approx (p : ℕ) [Fact p.Prime] (K : ℕ) (x : O0 p) :
    ∃ (a : Lau p) (c : O0 p), x = algebraMap (Lau p) (O0 p) a + (p : O0 p) ^ K * c := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ (pI p) K x)
  have hker : RingHom.ker (AdicCompletion.evalₐ (pI p) K) = (pI p ^ K).map (algebraMap (Lau p) (O0 p)) := by
    ext y
    rw [RingHom.mem_ker, ← Submodule.restrictScalars_mem (Lau p), ← Ideal.smul_top_eq_map,
      AdicCompletion.pow_smul_top_eq_ker_eval (Submodule.fg_span_singleton _), LinearMap.mem_ker]
    have hle : (pI p ^ K • ⊤ : Ideal (Lau p)) ≤ pI p ^ K := by intro z hz; simpa using hz
    rw [← AdicCompletion.factor_eval_eq_evalₐ (pI p) y hle]
    constructor
    · intro h
      obtain ⟨b, hb⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval (pI p) (Lau p) K y)
      rw [← hb] at h ⊢
      have : b ∈ pI p ^ K := Ideal.Quotient.eq_zero_iff_mem.mp h
      exact (Submodule.Quotient.mk_eq_zero _).mpr (by simpa using this)
    · intro h; rw [h, map_zero]
  have hmem : x - algebraMap (Lau p) (O0 p) a ∈ RingHom.ker (AdicCompletion.evalₐ (pI p) K) := by
    rw [RingHom.mem_ker, map_sub, AlgHom.commutes, Ideal.Quotient.algebraMap_eq, ha, sub_self]
  rw [hker, Ideal.span_singleton_pow, Ideal.map_span, Set.image_singleton, map_pow, map_natCast,
    Ideal.mem_span_singleton'] at hmem
  obtain ⟨c, hc⟩ := hmem
  exact ⟨a, c, by rw [mul_comm, hc]; ring⟩

theorem exists_cong_lau :
    ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω]
      (T : Tower p Ω) (n : ℕ) (ψ : O0 p →+* Ω), IsReb T n ψ →
      ∀ (d : ℕ) (e : Fin d → Ω) (b : Fin d → O0 p), (∀ t, IsInt (p := p) (e t)) →
      ∀ K : ℕ, ∃ a : Fin d → Lau p,
        Cong (p := p) K (∑ t, e t * ψ (b t))
          (∑ t, e t * ψ (algebraMap (Lau p) (O0 p) (a t))) := by
  intro p hp Ω _ _ T n ψ h d e b he K
  choose a c hac using fun t => exists_lau_approx p K (b t)
  have hq : IsIntegral (O0 p) (T.qq n) :=
    IsIntegral.of_pow (pow_pos hp.out.pos n) (by rw [Basic.qq_pow]; exact isIntegral_algebraMap)
  have hψ (x : O0 p) : IsIntegral (O0 p) (ψ x) := by
    have hx : ψ x ∈ ψ.range := ⟨x, rfl⟩
    rw [h.rng] at hx
    exact adjoin_le_integralClosure hq hx
  refine ⟨a, ∑ t, e t * ψ (c t), IsIntegral.sum _ fun t _ => IsIntegral.mul (he t) (hψ (c t)), ?_⟩
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [hac t, map_add (f := _), map_mul, map_pow, map_natCast]
  ring

end GlobalTheory.GeoFix
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLaurentSeriesSumCongruentModPPowStatement

section

@[expose] public section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois GlobalTheory.GeoFix

theorem _root_.GlobalTheory.T.exists_laurentSeries_sum_congruent_mod_p_pow :
    ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω]
      (T : Tower p Ω) (n : ℕ) (ψ : O0 p →+* Ω), IsReb T n ψ →
    ∀ (d : ℕ) (e : Fin d → Ω) (b : Fin d → O0 p), (∀ t, IsInt (p := p) (e t)) →
    ∀ K : ℕ, ∃ a : Fin d → Lau p,
      Cong (p := p) K (∑ t, e t * ψ (b t))
        (∑ t, e t * ψ (algebraMap (Lau p) (O0 p) (a t))) := by
  intro p hp Ω _ _ T n ψ h d e b he K
  have hq : IsIntegral (O0 p) (T.qq n) := by
    refine ⟨Polynomial.X ^ (p ^ n) - Polynomial.C (qO p),
      Polynomial.monic_X_pow_sub_C _ (pow_ne_zero _ hp.out.ne_zero), ?_⟩
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C,
      GlobalTheory.K5.Basic.qq_pow, sub_self]
  have hψ (x : O0 p) : IsIntegral (O0 p) (ψ x) := by
    have hx : ψ x ∈ ψ.range := ⟨x, rfl⟩
    rw [h.rng] at hx
    exact adjoin_le_integralClosure hq hx
  choose a c hac using fun t => GlobalTheory.GeoFix.exists_lau_approx p K (b t)
  refine ⟨a, ∑ t, e t * ψ (c t), IsIntegral.sum _ fun t _ => (he t).mul (hψ (c t)), ?_⟩
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [hac t, map_add (f := ψ), map_mul, map_pow, map_natCast]
  ring
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemSubfieldOfFixedByGeometricTowerGaloisStatement

section

@[expose] public section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois GlobalTheory.GeoFix

theorem _root_.GlobalTheory.T.mem_subfield_of_fixed_by_geometric_tower_galois : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω) (n : ℕ) (F : Subfield Ω), (∀ c : O0 p, algebraMap (O0 p) Ω c ∈ F) → (∀ x : Ω, IsAlgZp (p := p) x → x ∈ F) → T.qq n ∈ F → ∀ o : Ω, (∀ g ∈ Ggeo (p := p) Ω ⊓ Gn T n, g o = o) → o ∈ F := by
  intro p hp Ω _ _ hc T n F hO hA hq o ho
  have : CharZero Ω := GlobalTheory.K5.Basic.charZero_of_isClo hc
  have : IsAlgClosed Ω := hc.clo
  let f : O0 p →+* F := (algebraMap (O0 p) Ω).codRestrict F hO
  let : Algebra (O0 p) F := f.toAlgebra
  have : IsScalarTower (O0 p) F Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hf : Function.Injective (algebraMap (O0 p) F) :=
    fun _ _ h => hc.inj (congrArg Subtype.val h)
  have : Algebra.IsAlgebraic (O0 p) Ω := hc.alg
  have : Algebra.IsAlgebraic F Ω := Algebra.IsAlgebraic.extendScalars (R := O0 p) hf
  have : IsAlgClosure F Ω := ⟨hc.clo, inferInstance⟩
  have : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  have hζ : IsAlgZp (p := p) (T.ζ n) := by
    refine ⟨Polynomial.X ^ (p ^ n) - 1, ?_, ?_⟩
    · exact (Polynomial.monic_X_pow_sub_C (1 : ℤ_[p]) (pow_ne_zero _ hp.out.ne_zero)).ne_zero
    · simp [(T.prim n).pow_eq_one]
  have ho' : o ∈ Set.range (algebraMap F Ω) := by
    refine (InfiniteGalois.mem_range_algebraMap_iff_fixed o).2 fun σ => ?_
    let g : Gal p Ω := AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) fun c => σ.commutes (f c)
    have hg : g ∈ Ggeo (p := p) Ω ⊓ Gn T n := by
      refine ⟨fun x hx => σ.commutes ⟨x, hA x hx⟩, ?_, ?_⟩
      · show g • T.ζ n = T.ζ n
        exact σ.commutes ⟨T.ζ n, hA _ hζ⟩
      · show g • T.qq n = T.qq n
        exact σ.commutes ⟨T.qq n, hq⟩
    exact ho g hg
  obtain ⟨x, rfl⟩ := ho'
  exact x.2
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.Geofix

section

@[expose] public section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois GlobalTheory.GeoFix

namespace GlobalTheory.GeoFix

theorem geofix : ∀ (p : ℕ) [Fact p.Prime], ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : GlobalTheory.K5.Tower p Ω) (n : ℕ), ∀ (ψ : O0 p →+* Ω), IsReb T n ψ → ∀ (k : ℕ) (o : Ω), IsInt (p := p) o → (∀ g ∈ (Ggeo p Ω ⊓ Gn T n), g o = o) → ∃ (c : ℤ → Ω) (x x' : Ω), Ev ψ c x x' ∧ Cong (p := p) k o x := by
  intro p _ Ω _ _ hc T n ψ h k o ho hfix

  let F : Subfield Ω :=
    { carrier := {y | ∃ (N : Ω) (D : O0 p), InR ψ N ∧ D ≠ 0 ∧ y * ψ D = N}
      zero_mem' := ⟨0, 1, inR_zero ψ, one_ne_zero, by simp⟩
      one_mem' := ⟨ψ 1, 1, inR_psi ψ 1, one_ne_zero, by simp⟩
      add_mem' := by
        rintro a b ⟨N, D, hN, hD, ha⟩ ⟨N', D', hN', hD', hb⟩
        exact ⟨N * ψ D' + N' * ψ D, D * D', inR_add (inR_mul hN (inR_psi ψ D')) (inR_mul hN' (inR_psi ψ D)),
          mul_ne_zero hD hD', by rw [map_mul, ← ha, ← hb]; ring⟩
      mul_mem' := by
        rintro a b ⟨N, D, hN, hD, ha⟩ ⟨N', D', hN', hD', hb⟩
        exact ⟨N * N', D * D', inR_mul hN hN', mul_ne_zero hD hD', by rw [map_mul, ← ha, ← hb]; ring⟩
      neg_mem' := by
        rintro a ⟨N, D, hN, hD, ha⟩
        exact ⟨-N, D, inR_neg hN, hD, by rw [neg_mul, ha]⟩
      inv_mem' := by
        rintro a ⟨N, D, hN, hD, ha⟩
        by_cases ha0 : a = 0
        · rw [ha0, inv_zero]
          exact ⟨0, 1, inR_zero ψ, one_ne_zero, by simp⟩
        · have hψD : ψ D ≠ 0 := fun h0 => hD (h.inj (by rw [h0, map_zero]))
          have hN0 : N ≠ 0 := by rw [← ha]; exact mul_ne_zero ha0 hψD
          obtain ⟨N', D', hN', hD', hNN⟩ := GlobalTheory.T.exists_combination_mul_eq_reparametrization_image p Ω hc T n ψ h N hN hN0
          refine ⟨ψ D * N', D', inR_mul (inR_psi ψ D) hN', hD', ?_⟩
          rw [← hNN, ← ha]
          field_simp }
  have hF1 : ∀ c : O0 p, algebraMap (O0 p) Ω c ∈ F := by
    intro c
    have hmem : algebraMap (O0 p) Ω c ∈ ψ.range := by
      rw [h.rng]; exact Subalgebra.algebraMap_mem _ c
    obtain ⟨c', hc'⟩ := hmem
    exact ⟨ψ c', 1, inR_psi ψ c', one_ne_zero, by rw [map_one, mul_one, hc']⟩
  have hF2 : ∀ x : Ω, IsAlgZp p x → x ∈ F := by
    intro x hx
    obtain ⟨D, hD, hxD⟩ := exists_inR_of_isAlgZp hc h hx
    exact ⟨x * ψ D, D, hxD, hD, rfl⟩
  have hF3 : T.qq n ∈ F := ⟨ψ (qO p), 1, inR_psi ψ _, one_ne_zero, by rw [map_one, mul_one, h.par]⟩
  obtain ⟨N, D, hN, hD, hoD⟩ := GlobalTheory.T.mem_subfield_of_fixed_by_geometric_tower_galois p Ω hc T n F hF1 hF2 hF3 o hfix

  obtain ⟨_, hdvr, hirr⟩ := completed_laurent_isDVR p
  obtain ⟨v, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hD hirr
  have hN1 : InR ψ (N * ψ (↑u⁻¹ : O0 p)) := inR_mul hN (inR_psi ψ _)
  have hpo : (p : Ω) ^ v * o = N * ψ (↑u⁻¹ : O0 p) := by
    rw [← hoD, hu, map_mul, map_pow, map_natCast]
    have : ψ (↑u : O0 p) * ψ (↑u⁻¹ : O0 p) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
    linear_combination (-(↑p ^ v * o)) * this
  obtain ⟨d, e, b, he, hNe⟩ := hN1
  obtain ⟨a, z, hz, hza⟩ := GlobalTheory.T.exists_laurentSeries_sum_congruent_mod_p_pow p Ω T n ψ h d e b (fun t => (he t).1) (v + k)
  have hsum : ∑ t, e t * ψ (algebraMap (Lau p) (O0 p) (a t)) = (p : Ω) ^ v * (o - (p : Ω) ^ k * z) := by
    rw [← hNe] at hza
    rw [pow_add] at hza
    linear_combination -hpo - hza
  have hpi : IsInt (p := p) ((p : Ω) ^ k) := by
    rw [IsInt, ← map_natCast (algebraMap (O0 p) Ω), ← map_pow]; exact isIntegral_algebraMap
  have ho' : IsInt (p := p) (o - (p : Ω) ^ k * z) := IsIntegral.sub ho (IsIntegral.mul hpi hz)
  obtain ⟨c, x', hEv⟩ := GlobalTheory.T.integral_of_expansionSum_eq_primePow_mul_isEval p Ω hc T n ψ h d e a he v _ ho' hsum
  exact ⟨c, _, x', hEv, z, hz, by ring⟩

end GlobalTheory.GeoFix
end
end
