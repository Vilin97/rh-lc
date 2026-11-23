module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
public import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardMulFinrankCharacterSpaceOfFreePermutedSumman
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbedsInRegularRepresentationCopiesOfFreePermute
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBalancedFrameCMUnitaryProofStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUpperArithmeticGroupUnipotentUnitaryStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalCuspFormsDefiniteUnitaryFlagDomStatement
public import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.TwoLevelLogarithm
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.BigStatementPfA
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallUnipotentUnitaryElementIsOneProofStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLevelCuspFiniteOfComponentsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLevelCuspFormsDirectSumComponentsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryMatrixMajorantOperatorNormLeDefiniteStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardMulFinrankCharacterSpaceOfFreePermutedSummanStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module

theorem _root_.GlobalTheory.T.card_mul_finrank_characterSpace_of_free_permuted_summands : ∀ (K Γ V X : Type) [Field K] [CharZero K] [Group Γ] [Finite Γ] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype X] [DecidableEq X] (ρ : Representation K Γ V) (H : Subgroup Γ) [MulAction H X], (∀ (h : H) (x : X), h • x = x → h = 1) → ∀ (A : X → Submodule K V), DirectSum.IsInternal A → (∀ (h : H) (x : X), ∀ v ∈ A x, ρ h v ∈ A (h • x)) → ∀ (Hb : Subgroup Γ), Hb ≤ H → ∀ lam : Hb →* Kˣ, Nat.card Hb * finrank K (eig ρ Hb lam) = finrank K V := by
  first | exact @GlobalTheory.BadCount.card_mul_finrank_eig_of_free | exact GlobalTheory.BadCount.card_mul_finrank_eig_of_free | (intros; apply GlobalTheory.BadCount.card_mul_finrank_eig_of_free <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbedsInRegularRepresentationCopiesOfFreePermuteStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module

theorem _root_.GlobalTheory.T.embedsInRegularRepresentationCopies_of_free_permuted_summands : ∀ (K Γ V X : Type) [Field K] [Group Γ] [Finite Γ] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype X] [DecidableEq X] (ρ : Representation K Γ V) (H : Subgroup Γ) [MulAction H X], (∀ (h : H) (x : X), h • x = x → h = 1) → ∀ (A : X → Submodule K V), DirectSum.IsInternal A → (∀ (h : H) (x : X), ∀ v ∈ A x, ρ h v ∈ A (h • x)) → ∃ n : ℕ, EmbReg ρ H n ∧ n * Nat.card H = finrank K V := by
  first | exact @GlobalTheory.BadCount.embReg_of_free_permuted_summands | exact GlobalTheory.BadCount.embReg_of_free_permuted_summands | (intros; apply GlobalTheory.BadCount.embReg_of_free_permuted_summands <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTotallySplitRationalPrimeOfSplitsCompletely

section

@[expose] public section

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

namespace GlobalTheory.SplitLevelsBall

theorem setOf_prime_mem_eq_primesOver (E : Type) [Field E] [NumberField E] (g : ℕ) (hg : g.Prime) :
    {P : Ideal (𝓞 E) | P.IsPrime ∧ (g : 𝓞 E) ∈ P} = (Ideal.span {(g : ℤ)}).primesOver (𝓞 E) := by
  ext P
  simp only [Set.mem_setOf_eq, Ideal.primesOver, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hP, hgP⟩
    refine ⟨hP, ⟨?_⟩⟩
    have hmax : (Ideal.span {(g : ℤ)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hg).irreducible
    have hle : Ideal.span {(g : ℤ)} ≤ P.under ℤ := by
      rw [Ideal.span_le, Set.singleton_subset_iff]
      show (g : ℤ) ∈ Ideal.comap (algebraMap ℤ (𝓞 E)) P
      rw [Ideal.mem_comap, map_natCast]
      exact hgP
    have hne : P.under ℤ ≠ ⊤ := (Ideal.IsPrime.comap (f := algebraMap ℤ (𝓞 E)) (hK := hP)).ne_top
    exact hmax.eq_of_le hne hle
  · rintro ⟨hP, hlo⟩
    refine ⟨hP, ?_⟩
    have : (g : ℤ) ∈ P.under ℤ := by
      rw [← hlo.over]; exact Ideal.mem_span_singleton_self _
    simpa [Ideal.under, Ideal.mem_comap] using this

theorem isTotallySplitPrime_of_splitsCompletely :
    ∀ (E : Type) [Field E] [NumberField E] (g : ℕ), SplitsCompletely E g → GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.IsTotallySplitPrime E g := by
  intro E _ _ g ⟨hg, hc⟩
  exact ⟨hg, by rw [← setOf_prime_mem_eq_primesOver E g hg]; exact hc⟩

end GlobalTheory.SplitLevelsBall
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTotallySplitRationalPrimeOfSplitsCompletelyStatement

section

@[expose] public section

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

theorem _root_.GlobalTheory.T.isTotallySplitRationalPrime_of_splitsCompletely : ∀ (E : Type) [Field E] [NumberField E] (g : ℕ), SplitsCompletely E g → GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.IsTotallySplitPrime E g := by
  first | exact @GlobalTheory.SplitLevelsBall.isTotallySplitPrime_of_splitsCompletely | exact GlobalTheory.SplitLevelsBall.isTotallySplitPrime_of_splitsCompletely | (intros; apply GlobalTheory.SplitLevelsBall.isTotallySplitPrime_of_splitsCompletely <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteCuspFormsFiniteRegularRepresentation

section

@[expose] public section

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

namespace GlobalTheory.ShareOn.Definite

theorem free_of_definite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.BalancedPointStatement E → GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.SmallElementStatement E → ∀ (r : ℕ) (U C : Type) [Group U] [MulAction U C] (M : TwoLevels E r U C), (M.p0 = 0 ∨ M.p0 = r) → LevelHyp M → ∀ (u : U) (c : C), u • c = c → u = 1 := by
  intro E _ _ _ hbal hsmall r U C _ _ M hdef hlev u c huc
  obtain ⟨g, hsplit, hg, hunip⟩ := hlev
  obtain ⟨Γo, hst, hun, hmem⟩ := GlobalTheory.T.exists_upperArithmeticGroup_unipotentUnitary E r U C M c g hunip
  obtain ⟨x, hx, hnc, -⟩ := hbal r (M.comp c)
  have h1 : M.tr u c = 1 :=
    hsmall r (M.comp c) g (GlobalTheory.T.isTotallySplitRationalPrime_of_splitsCompletely E g hsplit) hg Γo hst hun x hx hnc (M.tr u c) (hmem u huc)
      (fun τ => GlobalTheory.T.unitaryMatrix_majorantOperatorNorm_le_definite E r (M.comp c).toData (by rw [M.comp_basePoint c]; exact hdef) x hx _
        (hst _ (hmem u huc)).1 τ)
  exact M.tr_faithful u c huc (by rw [h1]; exact (M.comp c).Γ.one_mem)

theorem share_definite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [Finite U] [Finite C] [MulAction U C] (M : TwoLevels E r U C), (M.p0 = 0 ∨ M.p0 = r) → ∀ (ka : Wt M.Ψ r) (ρ : Representation ℂ U (M.cusp ka)), IsPullRep M ka ρ → Module.Finite ℂ (M.cusp ka) ∧ ∀ H : Subgroup U, LevelHyp (sub M H) → (∃ n : ℕ, GlobalTheory.BadCount.EmbReg ρ H n ∧ n * Nat.card H = finrank ℂ (M.cusp ka)) ∧ ∀ lam : H →* ℂˣ, Nat.card H * finrank ℂ (GlobalTheory.BadCount.eig ρ H lam) = finrank ℂ (M.cusp ka) := by
  intro E _ _ _ r U C _ _ _ _ M hdef ka ρ hρ
  classical
  haveI : Fintype C := Fintype.ofFinite C
  have hfin : Module.Finite ℂ (M.cusp ka) :=
    GlobalTheory.T.twoLevelCusp_finite_of_components E r U C M ka (fun c =>
      GlobalTheory.T.finiteDimensional_cuspForms_definiteUnitaryFlagDomain E r (M.comp c).toData (by rw [M.comp_basePoint c]; exact hdef) _)
  refine ⟨hfin, fun H hH => ?_⟩
  haveI : FiniteDimensional ℂ (M.cusp ka) := hfin
  have hfree : ∀ (h : H) (c : C), h • c = c → h = 1 :=
    free_of_definite E (GlobalTheory.T.existsBalancedFrameCMUnitary_proof E) (GlobalTheory.T.smallUnipotentUnitaryElementIsOne_proof E) r H C (sub M H) hdef hH
  obtain ⟨A, hA, hAρ⟩ := GlobalTheory.T.twoLevelCuspForms_directSum_components E r U C M ka ρ hρ
  have hAρH : ∀ (h : H) (x : C), ∀ v ∈ A x, ρ h v ∈ A (h • x) := fun h x v hv => hAρ h x v hv
  exact ⟨GlobalTheory.T.embedsInRegularRepresentationCopies_of_free_permuted_summands ℂ U (M.cusp ka) C ρ H hfree A hA hAρH,
    fun lam => GlobalTheory.T.card_mul_finrank_characterSpace_of_free_permuted_summands ℂ U (M.cusp ka) C ρ H hfree A hA hAρH H le_rfl lam⟩

end GlobalTheory.ShareOn.Definite
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteCuspFormsFiniteRegularRepresentationStatement

section

@[expose] public section

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

theorem _root_.GlobalTheory.T.definite_cuspForms_finite_regularRepresentation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [Finite U] [Finite C] [MulAction U C] (M : TwoLevels E r U C), (M.p0 = 0 ∨ M.p0 = r) → ∀ (ka : Wt M.Ψ r) (ρ : Representation ℂ U (M.cusp ka)), IsPullRep M ka ρ → Module.Finite ℂ (M.cusp ka) ∧ ∀ H : Subgroup U, LevelHyp (sub M H) → (∃ n : ℕ, GlobalTheory.BadCount.EmbReg ρ H n ∧ n * Nat.card H = finrank ℂ (M.cusp ka)) ∧ ∀ lam : H →* ℂˣ, Nat.card H * finrank ℂ (GlobalTheory.BadCount.eig ρ H lam) = finrank ℂ (M.cusp ka) := by
  first | exact @GlobalTheory.ShareOn.Definite.share_definite | exact GlobalTheory.ShareOn.Definite.share_definite | (intros; apply GlobalTheory.ShareOn.Definite.share_definite <;> assumption)
end
end
