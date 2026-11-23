module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.JordanExists
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.JordanExists
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.JordanSplittingExists
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.CountCoeEqMultiplicity
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DeterminantLocal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.ProdAbsNormDifferentIdealPowers
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Linter.Style

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.NMPseudoOf

section

@[expose] public section

open NumberField Module IsDedekindDomain Formalism.L2.SG.Pf.Cnt
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.R6

open Formalism.HermitianLattices.Ext.L3

theorem nMPseudo_of (hE : JordanExists) (hD : DetLocal) (hC : CountExt) (hA : NormAssembly) : NMPseudo := by
  intro K F V ι _ _ _ _ _ _ _ _ _ _ _ _ _ h X x 𝔞 hcm hfix h2 hsymm hstar hne hind hspan hdet hint
  have hJ0 : (∏ i, 𝔞 i ^ 2) * FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (gram h x).det ≠ 0 :=
    mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (hne i))
      (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hdet)
  have key : ∀ (𝔭 : Ideal (𝓞 F)) (P : HeightOneSpectrum (𝓞 K)), 𝔭.IsMaximal →
      P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 K)) = 𝔭 →
        FractionalIdeal.count K P ((∏ i, 𝔞 i ^ 2) *
            FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (gram h x).det) =
          ((P.asIdeal.ramificationIdx (𝓞 F) * vJ h X (pbLat x 𝔞) 𝔭 : ℕ) : ℤ) := by
    intro 𝔭 P h𝔭 hP
    obtain ⟨b, a, hba⟩ := hE K F V ι h X x 𝔞 hcm hfix h2 hsymm hstar hne hind hspan hdet hint 𝔭 h𝔭
    have hcount : ∀ b' a', IsJordanIn h X (pbLat x 𝔞) 𝔭 b' a' →
        FractionalIdeal.count K P ((∏ i, 𝔞 i ^ 2) *
            FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (gram h x).det) =
          ((P.asIdeal.ramificationIdx (𝓞 F) * vJof 𝔭 a' : ℕ) : ℤ) := by
      intro b' a' h'
      rw [hD K F V ι h X x 𝔞 hfix hstar hne hind hspan hdet 𝔭 b' a' h𝔭 h' P hP,
        hC K F _ 𝔭 P a' h𝔭 hP h'.2.2.2.2]
      rfl
    have he : P.asIdeal.ramificationIdx (𝓞 F) ≠ 0 := by
      haveI := P.isPrime
      exact (Ideal.ramificationIdx_pos (R := 𝓞 F) P.asIdeal).ne'
    have hv : vJ h X (pbLat x 𝔞) 𝔭 = vJof 𝔭 a := by
      unfold vJ
      have hset : {v | ∃ b a, IsJordanIn h X (pbLat x 𝔞) 𝔭 b a ∧ v = vJof 𝔭 a} = {vJof 𝔭 a} := by
        ext v
        constructor
        · rintro ⟨b', a', h', rfl⟩
          have h3 := (hcount b' a' h').symm.trans (hcount b a hba)
          have h4 : P.asIdeal.ramificationIdx (𝓞 F) * vJof 𝔭 a' = P.asIdeal.ramificationIdx (𝓞 F) * vJof 𝔭 a := by
            exact_mod_cast h3
          exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero he) h4
        · rintro rfl
          exact ⟨b, a, hba, rfl⟩
      rw [hset, csInf_singleton]
    rw [hv]
    exact hcount b a hba
  exact hA K F h2 _ (vJ h X (pbLat x 𝔞)) hJ0 key

end PI.UnitaryGroupMassFormula.CntFormula.R6
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.VFEqEmultiplicity

section

@[expose] public section

open NumberField Module IsDedekindDomain Formalism.HermitianLattices.Ext.L3

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.R6

section

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

theorem vF_eq_emultiplicity {F : Type} [Field F] [NumberField F] (𝔭 : Ideal (𝓞 F)) (h𝔭 : 𝔭.IsPrime)
    (h0 : 𝔭 ≠ ⊥) (α : 𝓞 F) (hα : α ≠ 0) :
    ((vF 𝔭 α : ℕ) : ℕ∞) = emultiplicity 𝔭 (Ideal.span {α}) := by
  have hs : Ideal.span {α} ≠ ⊥ := by simpa using hα
  have hfm : FiniteMultiplicity 𝔭 (Ideal.span {α}) :=
    FiniteMultiplicity.of_prime_left (Ideal.prime_of_isPrime h0 h𝔭) hs
  rw [hfm.emultiplicity_eq_multiplicity]
  congr 1
  unfold vF
  have hset : {e : ℕ | α ∈ 𝔭 ^ e} = Set.Iic (multiplicity 𝔭 (Ideal.span {α})) := by
    ext e
    simp only [Set.mem_ofPred_eq, Set.mem_Iic]
    rw [← hfm.pow_dvd_iff_le_multiplicity, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  rw [hset, csSup_Iic]

end

theorem countExt_single (K F : Type) [Field K] [NumberField K] [Field F] [NumberField F] [Algebra F K]
    (𝔭 : Ideal (𝓞 F)) (P : HeightOneSpectrum (𝓞 K)) (α : 𝓞 F) (h𝔭 : 𝔭.IsMaximal)
    (hP : P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 K)) = 𝔭) (hα : α ≠ 0) :
    FractionalIdeal.count K P (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (algebraMap F K (α : F))) =
      ((P.asIdeal.ramificationIdx (𝓞 F) * vF 𝔭 α : ℕ) : ℤ) := by
  have h0 : 𝔭 ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (NumberField.RingOfIntegers.not_isField F)
  haveI : P.asIdeal.LiesOver 𝔭 := ⟨by rw [Ideal.under_def, hP]⟩
  set β : 𝓞 K := algebraMap (𝓞 F) (𝓞 K) α
  have hβ : β ≠ 0 := by
    intro h
    apply hα
    exact (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K)) (by rw [map_zero]; exact h)
  have hsβ : Ideal.span {β} ≠ ⊥ := by simpa using hβ
  have hsα : Ideal.span {α} ≠ ⊥ := by simpa using hα
  have hK : algebraMap F K (α : F) = algebraMap (𝓞 K) K β := rfl
  rw [hK, ← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe K P hsβ,
    Ideal.count_associates_factors_eq hsβ P.isPrime P.ne_bot,
    HeightOneSpectrum.count_normalizedFactors_eq_multiplicity hsβ P]
  congr 1
  have hfmP : FiniteMultiplicity P.asIdeal (Ideal.span {β}) :=
    FiniteMultiplicity.of_prime_left P.prime hsβ
  have hmap : Ideal.span {β} = (Ideal.span {α}).map (algebraMap (𝓞 F) (𝓞 K)) := by
    rw [Ideal.map_span, Set.image_singleton]
  have he := Ideal.IsDedekindDomain.emultiplicity_map_eq_ramificationIdx'_mul hsα
    (Ideal.prime_of_isPrime h0 h𝔭.isPrime).irreducible P.irreducible P.ne_bot
  rw [← hmap, hfmP.emultiplicity_eq_multiplicity, ← vF_eq_emultiplicity 𝔭 h𝔭.isPrime h0 α hα,
    Ideal.ramificationIdx'_eq_ramificationIdx 𝔭 P.asIdeal h0] at he
  exact_mod_cast he

theorem count_extension : CountExt := by
  intro K F _ _ _ _ _ n 𝔭 P α h𝔭 hP hα
  have h0 : 𝔭 ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (NumberField.RingOfIntegers.not_isField F)
  have hprod : (∏ j, ((α j : 𝓞 F) : F)) = ((∏ j, α j : 𝓞 F) : F) := by simp
  have hne : (∏ j, α j) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => hα j
  rw [hprod, countExt_single K F 𝔭 P _ h𝔭 hP hne]
  congr 2
  have key : ((vF 𝔭 (∏ j, α j) : ℕ) : ℕ∞) = ((∑ j, vF 𝔭 (α j) : ℕ) : ℕ∞) := by
    rw [vF_eq_emultiplicity 𝔭 h𝔭.isPrime h0 _ hne, ← Ideal.prod_span_singleton, Nat.cast_sum]
    rw [Finset.emultiplicity_prod (Ideal.prime_of_isPrime h0 h𝔭.isPrime)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [vF_eq_emultiplicity 𝔭 h𝔭.isPrime h0 _ (hα j)]
  exact_mod_cast key

end PI.UnitaryGroupMassFormula.CntFormula.R6
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.NormMMOfJD

section

@[expose] public section

namespace PI.UnitaryGroupMassFormula.CntFormula.R6

theorem normMM_of_JD (hE : JordanExists) (hD : DetLocal) : Formalism.L2.SG.Pf.Cnt.NormMM :=
  normMM_of_NM (nMPseudo_of hE hD count_extension norm_mass_assembly)

theorem normMM_of_J (hE : JordanExists) : Formalism.L2.SG.Pf.Cnt.NormMM :=
  normMM_of_JD hE determinant_local

end PI.UnitaryGroupMassFormula.CntFormula.R6
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.JordanDecompositionExists

section

@[expose] public section

open NumberField Module

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.R6

section Bridge

variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]

theorem nondegOn_of_gram (h : V →ₗ⋆[K] V →ₗ[K] K) (x : ι → V) (hdet : (gram h x).det ≠ 0) :
    Formalism.L2.SG.Pf.Cnt.NondegOn h (Submodule.span K (Set.range x)) := by
  intro v hv hv0
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hv
  have hvec : Matrix.vecMul (fun i => star (c i)) (gram h x) = 0 := by
    funext j
    have := hv0 (x j) (Submodule.subset_span ⟨j, rfl⟩)

    simpa [gram, Matrix.vecMul, dotProduct, map_sum, LinearMap.map_smulₛₗ, starRingEnd_apply] using this
  have h0 := Matrix.eq_zero_of_vecMul_eq_zero hdet hvec
  have hc : c = 0 := by
    funext i
    have := congrFun h0 i
    simpa using this
  simp [hc]

theorem isLatIn_pb (x : ι → V) (𝔞 : ι → FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (hne : ∀ i, 𝔞 i ≠ 0) :
    Formalism.L2.SG.Pf.Cnt.IsLatIn (Submodule.span K (Set.range x)) (pbLat x 𝔞) := by
  refine ⟨?_, ?_⟩
  ·
    have hden : ∀ i, ∃ d : 𝓞 K, d ≠ 0 ∧ ∀ c ∈ 𝔞 i, ∃ o : 𝓞 K, (o : K) = (d : K) * c := by
      intro i
      obtain ⟨d, hd, hdi⟩ := (𝔞 i).isFractional
      refine ⟨d, nonZeroDivisors.ne_zero hd, fun c hc => ?_⟩
      obtain ⟨o, ho⟩ := hdi c hc
      exact ⟨o, by rw [← Algebra.smul_def]; exact ho⟩
    choose d hd0 hd using hden
    set N : Submodule (𝓞 K) V := Submodule.span (𝓞 K) (Set.range fun i => ((d i : K))⁻¹ • x i)
    have hNfg : N.FG := Submodule.fg_span (Set.finite_range _)
    have hle : pbLat x 𝔞 ≤ N := by
      refine Submodule.span_le.mpr ?_
      rintro v ⟨i, c, hc, rfl⟩
      obtain ⟨o, ho⟩ := hd i c hc
      have hdi : ((d i : K)) ≠ 0 := by exact_mod_cast hd0 i
      have : c • x i = o • (((d i : K))⁻¹ • x i) := by
        rw [← algebraMap_smul K o, smul_smul]
        show c • x i = ((o : K) * ((d i : K))⁻¹) • x i
        rw [ho, mul_comm (d i : K), mul_assoc, mul_inv_cancel₀ hdi, mul_one]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    haveI : IsNoetherian (𝓞 K) N := isNoetherian_of_fg_of_noetherian N hNfg
    have hfg := IsNoetherian.noetherian ((pbLat x 𝔞).comap N.subtype)
    have hmap := hfg.map N.subtype
    rwa [Submodule.map_comap_eq_of_le (by rw [Submodule.range_subtype]; exact hle)] at hmap
  · apply le_antisymm
    · rw [Submodule.span_le]
      intro v hv
      have hle' : pbLat x 𝔞 ≤ (Submodule.span K (Set.range x)).restrictScalars (𝓞 K) := by
        refine Submodule.span_le.mpr ?_
        rintro w ⟨i, c, hc, rfl⟩
        exact Submodule.smul_mem _ c (Submodule.subset_span ⟨i, rfl⟩)
      exact hle' hv
    · rw [Submodule.span_le]
      rintro v ⟨i, rfl⟩
      obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
        (fun hb => hne i (FractionalIdeal.coeToSubmodule_eq_bot.mp hb))
      have hm : c • x i ∈ pbLat x 𝔞 := Submodule.subset_span ⟨i, c, hc, rfl⟩
      have : x i = c⁻¹ • (c • x i) := by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span hm)

end Bridge

theorem jordan_decomposition_exists : JordanExists := by
  intro K F V ι _ _ _ _ _ _ _ _ _ _ _ _ _ h X x 𝔞 hcm hfix _ hsymm _ hne _ hspan hdet hint 𝔭 h𝔭
  subst hspan
  exact (Formalism.L2.SG.Pf.Cnt.jordan_splitting_exists K F V hcm hfix h hsymm).1 _ _ (nondegOn_of_gram h x hdet)
    (isLatIn_pb x 𝔞 hne) hint 𝔭 h𝔭

theorem norm_mass_of_jordan : Formalism.L2.SG.Pf.Cnt.NormMM :=
  normMM_of_J jordan_decomposition_exists

end PI.UnitaryGroupMassFormula.CntFormula.R6
end
end
end
