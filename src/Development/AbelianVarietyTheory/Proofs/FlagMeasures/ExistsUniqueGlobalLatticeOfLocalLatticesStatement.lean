module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsNatBoundLocalLatticesStandardAeStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsNatMulMemIntegersQuadraticCompletionStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsIntegralOfIntegralAllQuadraticCompletions
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
public import Mathlib.Algebra.Module.Lattice.Basic
public import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalLatticeBetweenScaledStandardLatticesStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalLatticeLeCompletionGluedLatticeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemSpanSingleIff
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NumberFieldLatticeDeterminedByLocalLatticesStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StrongApproximationAdditiveQuadraticExtensionStatement
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsIntegralOfIntegralAllQuadraticCompletionsStatement

section

@[expose] public section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.isIntegral_of_integral_all_quadraticCompletions : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (y : E), (∀ p, (A.loc p).ιE y ∈ (A.L p).O) → IsIntegral ℤ y := by
  first | exact @GlobalTheory.HL.isIntegral_of_forall_mem_O | exact GlobalTheory.HL.isIntegral_of_forall_mem_O | (intros; apply GlobalTheory.HL.isIntegral_of_forall_mem_O <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsLatticeOfSqueezedBetweenNatMultiples

section

@[expose] public section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

theorem GlobalTheory.glue_latt_isLattice {E : Type} [Field E] [NumberField E] (n : ℕ) (Γ : Submodule (𝓞 E) (Fin n → E)) (N : ℕ) (hN : N ≠ 0)
    (hlow : ∀ x : Fin n → E, (∀ i, IsIntegral ℤ (x i)) → (N : E) • x ∈ Γ)
    (hup : ∀ x ∈ Γ, ∀ i, IsIntegral ℤ ((N : E) * x i)) : Submodule.IsLattice E Γ := by
  have hNE : (N : E) ≠ 0 := Nat.cast_ne_zero.mpr hN
  let f : (Fin n → 𝓞 E) →ₗ[𝓞 E] (Fin n → E) :=
    ((N : E)⁻¹ • (LinearMap.pi fun i => (Algebra.linearMap (𝓞 E) E).comp (LinearMap.proj i)))
  have hle : Γ ≤ LinearMap.range f := by
    intro x hx
    refine ⟨fun i => ⟨(N : E) * x i, hup x hx i⟩, ?_⟩
    ext i
    change (N : E)⁻¹ * ((N : E) * x i) = x i
    rw [← mul_assoc, inv_mul_cancel₀ hNE, one_mul]
  refine ⟨?_, ?_⟩
  · rw [← Submodule.map_comap_eq_self hle]
    exact (IsNoetherian.noetherian _).map f
  · intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsLatticeOfSqueezedBetweenNatMultiplesStatement

section

@[expose] public section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.isLattice_of_squeezed_between_nat_multiples : ∀ {E : Type} [Field E] [NumberField E], ∀ (n : ℕ) (Γ : Submodule (𝓞 E) (Fin n → E)) (N : ℕ), N ≠ 0 → (∀ x : Fin n → E, (∀ i, IsIntegral ℤ (x i)) → (N : E) • x ∈ Γ) → (∀ x ∈ Γ, ∀ i, IsIntegral ℤ ((N : E) * x i)) → Submodule.IsLattice E Γ := by
  first | exact @GlobalTheory.glue_latt_isLattice | exact GlobalTheory.glue_latt_isLattice | (intros; apply GlobalTheory.glue_latt_isLattice <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.NatCastIsUnitQuadraticCompletionAlmostAll

section

@[expose] public section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.Glue

theorem natCast_isUnit_ae {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} (A : Places F E sig) (N : ℕ) (hN : N ≠ 0) :
    {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = (N : (A.loc p).Fp)}.Finite := by
  have hx : ((N : 𝓞 F)) ≠ 0 := Nat.cast_ne_zero.2 hN
  have hI : Ideal.span {((N : 𝓞 F))} ≠ ⊥ := by simpa using hx
  refine (Ideal.finite_factors hI).subset ?_
  intro p hp
  simp only [Set.mem_setOf_eq] at hp ⊢
  rw [Ideal.dvd_span_singleton]
  by_contra hmem
  apply hp
  have hv : p.valuation F (N : F) = 1 := by
    have : ((N : F)) = algebraMap (𝓞 F) F (N : 𝓞 F) := by simp
    rw [this, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
    exact hmem
  have hι : (A.loc p).ιF (N : F) = (N : (A.loc p).Fp) := map_natCast _ _
  have h1 : (N : (A.loc p).Fp) ≤ᵥ 1 := by
    rw [← hι, ← map_one (A.loc p).ιF, (A.loc p).val, hv, map_one]
  have h2 : (1 : (A.loc p).Fp) ≤ᵥ (N : (A.loc p).Fp) := by
    rw [← hι, ← map_one (A.loc p).ιF, (A.loc p).val, hv, map_one]
  have hmem1 : (N : (A.loc p).Fp) ∈ 𝒪[(A.loc p).Fp] := by
    rw [Valuation.mem_integer_iff]; exact (Valuation.vle_one_iff (v := valuation _)).1 h1
  have hN0 : (N : (A.loc p).Fp) ≠ 0 := by
    haveI := (A.loc p).char0; exact Nat.cast_ne_zero.2 hN
  have hmem2 : (N : (A.loc p).Fp)⁻¹ ∈ 𝒪[(A.loc p).Fp] := by
    rw [Valuation.mem_integer_iff, map_inv₀, inv_le_one₀]
    · have := (Valuation.vle_iff_le (v := valuation _)).1 h2; rwa [map_one] at this
    · exact (Valuation.pos_iff _).2 hN0
  refine ⟨⟨⟨_, hmem1⟩, ⟨_, hmem2⟩, ?_, ?_⟩, rfl⟩
  · ext; simp [mul_inv_cancel₀ hN0]
  · ext; simp [inv_mul_cancel₀ hN0]

end GlobalTheory.HL.Glue
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.NatCastIsUnitQuadraticCompletionAlmostAllStatement

section

@[expose] public section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.natCast_isUnit_quadraticCompletion_almost_all : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (N : ℕ), N ≠ 0 → {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = (N : (A.loc p).Fp)}.Finite := by
  first | exact @GlobalTheory.HL.Glue.natCast_isUnit_ae | exact GlobalTheory.HL.Glue.natCast_isUnit_ae | (intros; apply GlobalTheory.HL.Glue.natCast_isUnit_ae <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUniqueGlobalLatticeOfLocalLattices

section

@[expose] public section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.Glue

theorem glue : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (n : ℕ) (Λ : ∀ p, Submodule (A.L p).O (Fin n → (A.loc p).Ep)), (∀ p, IsLat (A.L p) (Λ p)) → {p | Λ p ≠ Submodule.span (A.L p).O (Set.range fun i => (Pi.single i 1 : Fin n → (A.loc p).Ep))}.Finite → ∃! Γ : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E Γ ∧ ∀ p, A.lat p Γ = Λ p := by
  intro F E _ _ _ _ _ sig A n Λ hlat hfin
  refine existsUnique_of_exists_of_unique ?_ ?_
  · have happ1 := (GlobalTheory.T.strong_approximation_additive_quadratic_extension A (fun _ => 1)
      (Set.finite_empty.subset fun p hp => hp ⟨1, by simp⟩)).2.1
    have h3 : ∀ p (y : (A.loc p).Ep), ∃ m : ℕ, m ≠ 0 ∧ (m : (A.loc p).Ep) * y ∈ (A.L p).O :=
      GlobalTheory.T.exists_nat_mul_mem_integers_quadraticCompletion A (fun y hy => by
        obtain ⟨x, hx⟩ := happ1 y hy
        exact ⟨x, fun p => by simpa using hx p⟩)
    obtain ⟨N, hN, hb⟩ := GlobalTheory.T.exists_nat_bound_localLattices_standard_ae A n Λ hfin fun p => GlobalTheory.T.local_lattice_between_scaled_standard_lattices A p n (Λ p) (hlat p) (h3 p)
    let Γ : Submodule (𝓞 E) (Fin n → E) :=
      { carrier := {x | ∀ p, A.bc p x ∈ Λ p}
        add_mem' := by
          intro x y hx hy p
          have : A.bc p (x + y) = A.bc p x + A.bc p y := by funext i; simp [Places.bc]
          rw [this]; exact (Λ p).add_mem (hx p) (hy p)
        zero_mem' := by
          intro p
          have : A.bc p (0 : Fin n → E) = 0 := by funext i; simp [Places.bc]
          rw [this]; exact (Λ p).zero_mem
        smul_mem' := by
          intro a x hx p
          have ha : (A.loc p).ιE (a : E) ∈ (A.L p).O := ιE_mem A p _ a.isIntegral_coe
          have : A.bc p (a • x) = (⟨_, ha⟩ : (A.L p).O) • A.bc p x := by
            funext i; simp [Places.bc, Subring.smul_def, Algebra.smul_def]; rfl
          rw [this]; exact (Λ p).smul_mem _ (hx p) }
    have hΓ : ∀ x, x ∈ Γ ↔ ∀ p, A.bc p x ∈ Λ p := fun x => Iff.rfl
    have hL : Submodule.IsLattice E Γ := by
      refine GlobalTheory.T.isLattice_of_squeezed_between_nat_multiples n Γ N hN (fun x hx p => ?_) (fun x hx i => ?_)
      · have : A.bc p ((N : E) • x) = (N : (A.loc p).Ep) • A.bc p x := by
          funext i; simp [Places.bc]
        rw [this]
        exact (hb p).1 _ fun i => ιE_mem A p _ (hx i)
      · refine GlobalTheory.T.isIntegral_of_integral_all_quadraticCompletions A _ fun p => ?_
        have := (hb p).2 _ (hx p) i
        simpa [Places.bc] using this
    refine ⟨Γ, hL, fun p => le_antisymm ?_ ?_⟩
    · exact Submodule.span_le.2 (by rintro _ ⟨x, hx, rfl⟩; exact hx p)
    · haveI := (A.loc p).char0
      refine GlobalTheory.T.localLattice_le_completion_glued_lattice A n Λ Γ N hΓ (fun q => (hb q).1) ?_ p
      have hc : ∀ q, (N : (A.loc q).Fp) ≠ 0 := fun q => by
        haveI := (A.loc q).char0; exact_mod_cast hN
      have happN := (GlobalTheory.T.strong_approximation_additive_quadratic_extension A (fun q => Units.mk0 _ (hc q))
        (by simpa using GlobalTheory.T.natCast_isUnit_quadraticCompletion_almost_all A N hN)).2.1
      intro y hy
      obtain ⟨x, hx⟩ := happN y hy
      exact ⟨x, fun q => by simpa using hx q⟩
  · have full (Γ : Submodule (𝓞 E) (Fin n → E)) (hΓ : Submodule.IsLattice E Γ)
        (e : ∀ p, A.lat p Γ = Λ p) : Submodule.IsFullLattice E Γ := by
      refine { toIsLattice := hΓ, span_eq_top := ?_ }
      by_contra hspan
      obtain ⟨φ, hφ, hker⟩ := (Submodule.span E (Γ : Set (Fin n → E))).exists_le_ker_of_lt_top
        (lt_top_iff_ne_top.mpr hspan)
      obtain ⟨p⟩ := GlueInt.nonempty_place' (F := F)
      have := GlueInt.nontrivial_Ep A p
      -- A functional annihilating the global span extends by mapping its coefficients.
      let ψ : (Fin n → (A.loc p).Ep) →ₗ[(A.loc p).Ep] (A.loc p).Ep :=
        ∑ i, (A.loc p).ιE (φ (Pi.single i 1)) • LinearMap.proj i
      have hψ (x : Fin n → E) : ψ (A.bc p x) = (A.loc p).ιE (φ x) := by
        have hx : φ x = ∑ i, x i * φ (Pi.single i 1) := by
          have hi (i : Fin n) : (fun j : Fin n => if i = j then (1 : E) else 0) =
              Pi.single i 1 := by
            funext j
            simp [Pi.single_apply, eq_comm]
          simpa only [hi, smul_eq_mul] using LinearMap.pi_apply_eq_sum_univ φ x
        simp only [hx, ψ, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply,
          smul_eq_mul, map_sum, map_mul, mul_comm, Places.bc]
      have htop : Submodule.span (A.loc p).Ep (A.bc p '' (Γ : Set (Fin n → E))) = ⊤ := by
        simpa only [← e p, Places.lat, Submodule.span_span_of_tower] using (hlat p).2
      have hle : Submodule.span (A.loc p).Ep (A.bc p '' (Γ : Set (Fin n → E))) ≤
          LinearMap.ker ψ := by
        refine Submodule.span_le.2 ?_
        rintro _ ⟨x, hx, rfl⟩
        change ψ (A.bc p x) = 0
        rw [hψ, LinearMap.mem_ker.mp (hker (Submodule.subset_span hx)), map_zero]
      rw [htop] at hle
      apply hφ
      apply LinearMap.ext
      intro x
      have hz : A.bc p x ∈ LinearMap.ker ψ := hle Submodule.mem_top
      apply (A.loc p).ιE.injective
      simpa only [LinearMap.mem_ker, hψ, LinearMap.zero_apply, map_zero] using hz
    rintro Γ₁ Γ₂ ⟨h1, e1⟩ ⟨h2, e2⟩
    ext x
    rw [(GlobalTheory.T.numberField_lattice_determined_by_local_lattices A n Γ₁ (full Γ₁ h1 e1)).1 x,
      (GlobalTheory.T.numberField_lattice_determined_by_local_lattices A n Γ₂ (full Γ₂ h2 e2)).1 x]
    simp only [e1, e2]

end GlobalTheory.HL.Glue
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUniqueGlobalLatticeOfLocalLatticesStatement

section

@[expose] public section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.exists_unique_global_lattice_of_local_lattices : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (n : ℕ) (Λ : ∀ p, Submodule (A.L p).O (Fin n → (A.loc p).Ep)), (∀ p, IsLat (A.L p) (Λ p)) → {p | Λ p ≠ Submodule.span (A.L p).O (Set.range fun i => (Pi.single i 1 : Fin n → (A.loc p).Ep))}.Finite → ∃! Γ : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E Γ ∧ ∀ p, A.lat p Γ = Λ p := by
  first | exact @GlobalTheory.HL.Glue.glue | exact GlobalTheory.HL.Glue.glue | (intros; apply GlobalTheory.HL.Glue.glue <;> assumption)
end
end
