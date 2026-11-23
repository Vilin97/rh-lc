module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
public import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Hypotheses2
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.Adjoin.FG
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEmbeddingsAgreeOnSubfieldNe
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
public import Mathlib.RingTheory.FiniteType
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroForallComplexPointExtend
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Definitions.Divisors.Multiplier
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CuspRatioFieldEqTopOfToroidalCompactification
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPositivityPrincipalisation

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEmbeddingsAgreeOnSubfieldNeStatement

section

@[expose] public section

open TensorProduct

theorem _root_.GlobalTheory.T.exists_ringHom_pair_eq_on_subfield_ne_of_not_mem_range : ∀ (L Ω : Type) [Field L] [Field Ω] [Algebra L Ω] [CharZero L] (a : Ω), a ∉ Set.range (algebraMap L Ω) → ∃ (F : Type) (_ : Field F) (i₁ i₂ : Ω →+* F), i₁.comp (algebraMap L Ω) = i₂.comp (algebraMap L Ω) ∧ i₁ a ≠ i₂ a := by
  first | exact @GlobalTheory.exists_embeddings_agree_on_subfield_ne | exact GlobalTheory.exists_embeddings_agree_on_subfield_ne | (intros; apply GlobalTheory.exists_embeddings_agree_on_subfield_ne <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroForallComplexPointSeparate

section

@[expose] public section

namespace GlobalTheory

theorem exists_ne_zero_forall_complexPoint_separate
    (B A F : Type) [CommRing B] [IsDomain B] [IsNoetherianRing B] [CommRing A] [Algebra B A]
    [Algebra.FiniteType B A] [Field F] (j₁ j₂ : A →+* F)
    (h : j₁.comp (algebraMap B A) = j₂.comp (algebraMap B A))
    (hinj : Function.Injective (j₁.comp (algebraMap B A))) (a : A) (ha : j₁ a ≠ j₂ a) :
    ∃ q : B, q ≠ 0 ∧ ∀ φ : B →+* ℂ, φ q ≠ 0 → ∃ y₁ y₂ : A →+* ℂ,
      y₁.comp (algebraMap B A) = φ ∧ y₂.comp (algebraMap B A) = φ ∧ y₁ a ≠ y₂ a := by
  classical
  letI : Algebra B F := (j₁.comp (algebraMap B A)).toAlgebra
  let J₁ : A →ₐ[B] F := { j₁ with commutes' := fun _ => rfl }
  let J₂ : A →ₐ[B] F := { j₂ with commutes' := fun b => (RingHom.congr_fun h b).symm }
  let u : F := (j₁ a - j₂ a)⁻¹
  let D : Subalgebra B F := (Subalgebra.map J₁ ⊤ ⊔ Subalgebra.map J₂ ⊤) ⊔
    Algebra.adjoin B (({u} : Finset F) : Set F)
  have hA : (⊤ : Subalgebra B A).FG := Algebra.FiniteType.out
  have hD : D.FG := ((hA.map J₁).sup (hA.map J₂)).sup (Subalgebra.fg_adjoin_finset _)
  haveI : Algebra.FiniteType B D := (Subalgebra.fg_iff_finiteType D).1 hD
  have h1 : ∀ x, J₁ x ∈ D := fun x =>
    (le_sup_left.trans le_sup_left : Subalgebra.map J₁ ⊤ ≤ D) ⟨x, trivial, rfl⟩
  have h2 : ∀ x, J₂ x ∈ D := fun x =>
    (le_sup_right.trans le_sup_left : Subalgebra.map J₂ ⊤ ≤ D) ⟨x, trivial, rfl⟩
  have hu : u ∈ D := (le_sup_right : _ ≤ D) (Algebra.subset_adjoin (by simp))
  have hBD : Function.Injective (algebraMap B D) := fun x y hxy =>
    hinj (congrArg Subtype.val hxy)
  obtain ⟨q, hq, H⟩ := GlobalTheory.exists_ne_zero_forall_complexPoint_extend B D hBD
  refine ⟨q, hq, fun φ hφ => ?_⟩
  obtain ⟨ψ, hψ⟩ := H φ hφ
  let K₁ : A →ₐ[B] D := J₁.codRestrict D h1
  let K₂ : A →ₐ[B] D := J₂.codRestrict D h2
  refine ⟨ψ.comp (K₁ : A →+* D), ψ.comp (K₂ : A →+* D), ?_, ?_, ?_⟩
  · rw [RingHom.comp_assoc, AlgHom.comp_algebraMap, hψ]
  · rw [RingHom.comp_assoc, AlgHom.comp_algebraMap, hψ]
  · intro heq
    have hone : (⟨u, hu⟩ : D) * (K₁ a - K₂ a) = 1 :=
      Subtype.ext (inv_mul_cancel₀ (sub_ne_zero.2 ha))
    have h3 := congrArg ψ hone
    have heq' : ψ (K₁ a) = ψ (K₂ a) := heq
    rw [map_mul, map_sub, heq', sub_self, mul_zero, map_one] at h3
    exact zero_ne_one h3

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroForallComplexPointSeparateStatement

section

@[expose] public section

open TensorProduct

theorem _root_.GlobalTheory.T.exists_ne_zero_forall_complexPoint_separate' : ∀ (B A F : Type) [CommRing B] [IsDomain B] [IsNoetherianRing B] [CommRing A] [Algebra B A] [Algebra.FiniteType B A] [Field F] (j₁ j₂ : A →+* F), j₁.comp (algebraMap B A) = j₂.comp (algebraMap B A) → Function.Injective (j₁.comp (algebraMap B A)) → ∀ a : A, j₁ a ≠ j₂ a → ∃ q : B, q ≠ 0 ∧ ∀ φ : B →+* ℂ, φ q ≠ 0 → ∃ y₁ y₂ : A →+* ℂ, y₁.comp (algebraMap B A) = φ ∧ y₂.comp (algebraMap B A) = φ ∧ y₁ a ≠ y₂ a := by
  first | exact @GlobalTheory.exists_ne_zero_forall_complexPoint_separate | exact GlobalTheory.exists_ne_zero_forall_complexPoint_separate | (intros; apply GlobalTheory.exists_ne_zero_forall_complexPoint_separate <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulEqOfGenericUniqueComplexPoint

section

@[expose] public section

open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp GlobalTheory.DegVal GlobalTheory.CovTop ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped ENNReal NNReal

namespace GlobalTheory.DegVal

theorem exists_mul_eq_of_generic_unique_complexPoint : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (σ : K →+* ℂ) (A B : Subalgebra K Ω), A.FG → B.FG → B ≤ A → (∀ b ∈ B, b ≠ 0 → ∃ x : A →+* ℂ, (∀ k : K, x (algebraMap K A k) = σ k) ∧ (∀ hb : b ∈ A, x ⟨b, hb⟩ ≠ 0) ∧ ∀ y : A →+* ℂ, (∀ k : K, y (algebraMap K A k) = σ k) → (∀ a : A, (a : Ω) ∈ B → y a = x a) → y = x) → ∀ a ∈ A, ∃ p ∈ B, ∃ q ∈ B, q ≠ 0 ∧ a * q = p := by
  intro K Ω _ _ _ σ A B hA hB hBA H a haA
  by_contra hne
  haveI : CharZero K := ⟨fun m n h => Nat.cast_injective (R := ℂ) (by simpa using congrArg σ h)⟩
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  let L := IntermediateField.adjoin K (B : Set Ω)
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  have haL : a ∉ Set.range (algebraMap L Ω) := by
    rintro ⟨l, hl⟩
    have hmem : a ∈ L := hl ▸ l.2
    obtain ⟨r, hr, s, hs, rfl⟩ := IntermediateField.mem_adjoin_iff_div.1 hmem
    rw [Algebra.adjoin_eq] at hr hs
    apply hne
    by_cases hs0 : s = 0
    · exact ⟨0, B.zero_mem, 1, B.one_mem, one_ne_zero, by simp [hs0]⟩
    · exact ⟨r, hr, s, hs, hs0, div_mul_cancel₀ r hs0⟩
  obtain ⟨F, _, i₁, i₂, hi, hne2⟩ := GlobalTheory.T.exists_ringHom_pair_eq_on_subfield_ne_of_not_mem_range L Ω a haL
  letI : Algebra B A := (Subalgebra.inclusion hBA).toRingHom.toAlgebra
  haveI : IsScalarTower K B A := IsScalarTower.of_algebraMap_eq fun k => rfl
  haveI : Algebra.FiniteType K A := (Subalgebra.fg_iff_finiteType A).1 hA
  haveI : Algebra.FiniteType K B := (Subalgebra.fg_iff_finiteType B).1 hB
  haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing K B
  haveI : Algebra.FiniteType B A := Algebra.FiniteType.of_restrictScalars_finiteType K B A
  let j₁ : A →+* F := i₁.comp A.val.toRingHom
  let j₂ : A →+* F := i₂.comp A.val.toRingHom
  have hBL : ∀ b : B, (b : Ω) = algebraMap L Ω ⟨b, IntermediateField.subset_adjoin K _ b.2⟩ := fun b => rfl
  have hj : j₁.comp (algebraMap B A) = j₂.comp (algebraMap B A) := by
    ext b
    change i₁ (b : Ω) = i₂ (b : Ω)
    rw [hBL b]
    exact congrArg (fun f : L →+* F => f _) hi
  have hinj : Function.Injective (j₁.comp (algebraMap B A)) := by
    intro b c h
    exact Subtype.ext (i₁.injective h)
  obtain ⟨q, hq, Hq⟩ := GlobalTheory.T.exists_ne_zero_forall_complexPoint_separate' B A F j₁ j₂ hj hinj ⟨a, haA⟩ hne2
  obtain ⟨x, hxσ, hxq, hxu⟩ := H q q.2 (fun h => hq (Subtype.ext h))
  let φ : B →+* ℂ := x.comp (algebraMap B A)
  have hφq : φ q ≠ 0 := hxq (hBA q.2)
  obtain ⟨y₁, y₂, h₁, h₂, hy⟩ := Hq φ hφq
  have key : ∀ y : A →+* ℂ, y.comp (algebraMap B A) = φ → y = x := by
    intro y hy
    refine hxu y (fun k => ?_) (fun a' ha' => ?_)
    · have e1 : algebraMap K A k = algebraMap B A (algebraMap K B k) := rfl
      rw [e1, ← hxσ k, e1]
      exact congrArg (fun f : B →+* ℂ => f (algebraMap K B k)) hy
    · have e1 : a' = algebraMap B A ⟨a', ha'⟩ := rfl
      rw [e1]
      exact congrArg (fun f : B →+* ℂ => f ⟨a', ha'⟩) hy
  exact hy (by rw [key y₁ h₁, key y₂ h₂])

end GlobalTheory.DegVal
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsCentreCuspGenericValueNeZero

section

@[expose] public section

section
set_option autoImplicit false

noncomputable section
namespace GlobalTheory.CentreCusp
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine
  GlobalTheory.CompHt GlobalTheory.FlatCore
section Zeros
open Filter Topology
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
end Zeros
section Cancel
open Filter Topology
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ}
  {Z : Comp Xo c} {G : WTZ E} {f : Rul Xo c}
end Cancel
section SlopeTestRemainingChoices
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}
end SlopeTestRemainingChoices
section General
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ}
end General
section Cover
open GlobalTheory.CovTop GlobalTheory.PrincCore Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {T : CoreJ D} {j : ℕ} {Y : Deep T.toCore j} {e : ℕ} {o : ℝ}
end Cover
end GlobalTheory.CentreCusp
open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp GlobalTheory.DegVal GlobalTheory.CovTop ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped ENNReal NNReal
namespace GlobalTheory.CentreCusp
theorem exists_cusp_with_generic_value_ne_zero : GlobalTheory.CovTop.HypothesesX → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.NadelVanishingAndNonKltDivisor → GlobalTheory.Published.Principalisation → ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ (u : GlobalTheory.AllWt.Weight (T.Q.Dw j)), (∀ τ (a b : Fin ((T.Q.Dw j).p + (T.Q.Dw j).q)), (b : ℕ) = a + 1 → (((dimFlag (T.Q.Dw j) + 3) ^ 2 + 2 * ((T.Q.Dw j).p + (T.Q.Dw j).q) : ℕ) : ℤ) ≤ u τ a - u τ b) → ∀ Z : Comp Y.d.Xo₂ Y.d.c₂, ∃ f ∈ cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0), genVal Z f ≠ 0 :=
  fun _ _ _ _ _ _ _ D T hT j hp hq Y e o hY u hu Z => exists_cusp_genVal_ne_zero' D T hT j hp hq Y e o hY u hu Z
end GlobalTheory.CentreCusp
end
end

section
open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp GlobalTheory.DegVal GlobalTheory.CovTop ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped ENNReal NNReal

theorem _root_.GlobalTheory.T.exists_centre_cusp_generic_value_ne_zero : GlobalTheory.CovTop.HypothesesX → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.NadelVanishingAndNonKltDivisor → GlobalTheory.Published.Principalisation → ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ (u : GlobalTheory.AllWt.Weight (T.Q.Dw j)), (∀ τ (a b : Fin ((T.Q.Dw j).p + (T.Q.Dw j).q)), (b : ℕ) = a + 1 → (((dimFlag (T.Q.Dw j) + 3) ^ 2 + 2 * ((T.Q.Dw j).p + (T.Q.Dw j).q) : ℕ) : ℤ) ≤ u τ a - u τ b) → ∀ Z : Comp Y.d.Xo₂ Y.d.c₂, ∃ f ∈ cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0), genVal Z f ≠ 0 := by
  first | exact @_root_.GlobalTheory.CentreCusp.exists_cusp_with_generic_value_ne_zero | exact _root_.GlobalTheory.CentreCusp.exists_cusp_with_generic_value_ne_zero | (intros; apply _root_.GlobalTheory.CentreCusp.exists_cusp_with_generic_value_ne_zero <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.WeightPrincipalisationBound

section

@[expose] public section

section
open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp GlobalTheory.DegVal GlobalTheory.CovTop ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped ENNReal NNReal
set_option autoImplicit false
namespace GlobalTheory.DegVal
theorem birOn_of_weight_gaps_large : GlobalTheory.CovTop.HypothesesX → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.NadelVanishingAndNonKltDivisor → GlobalTheory.Published.Principalisation → ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ (u : GlobalTheory.AllWt.Weight (T.Q.Dw j)), (∀ τ (a b : Fin ((T.Q.Dw j).p + (T.Q.Dw j).q)), (b : ℕ) = a + 1 → (((dimFlag (T.Q.Dw j) + 3) ^ 2 + 2 * ((T.Q.Dw j).p + (T.Q.Dw j).q) : ℕ) : ℤ) ≤ u τ a - u τ b) → ∀ Z : Comp Y.d.Xo₂ Y.d.c₂, BirOn Y.U Z (wtOf (T.Q.Dw j) u 0) := by
  intro hX hG hQ hS hP hN hPr D T hT j hp hq Y e o hY u hu Z
  obtain ⟨f₀, hf₀, hne⟩ := _root_.GlobalTheory.T.exists_centre_cusp_generic_value_ne_zero hX hG hQ hS hP hN hPr D T hT j hp hq Y e o hY u hu Z
  obtain ⟨σ, A, B, hA, hB, hBA, hBr, hAtop, hsep⟩ := _root_.GlobalTheory.T.cusp_values_separate_generic_points hX hG hQ hS hP hN hPr D T hT j hp hq Y e o hY u hu Z
  have key := exists_mul_eq_of_generic_unique_complexPoint _ _ σ A B hA hB hBA hsep
  refine ⟨fun h => hne ?_, eq_top_iff.2 ?_⟩
  · have := LinearMap.congr_fun h ⟨f₀, hf₀⟩
    simpa [genPoint] using this
  · rw [← hAtop, IntermediateField.adjoin_le_iff]
    intro a ha
    obtain ⟨p, hp', q, hq', hq0, hpq⟩ := key a ha
    rw [eq_div_of_mul_eq hq0 hpq]
    exact IntermediateField.div_mem _ (hBr p hp') (hBr q hq')
end GlobalTheory.DegVal
end

section
open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp GlobalTheory.DegVal GlobalTheory.CovTop ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped ENNReal NNReal

theorem _root_.GlobalTheory.T.birOn_wtOf_of_consecutive_gap_bound : GlobalTheory.CovTop.HypothesesX → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.NadelVanishingAndNonKltDivisor → GlobalTheory.Published.Principalisation → ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ (u : GlobalTheory.AllWt.Weight (T.Q.Dw j)), (∀ τ (a b : Fin ((T.Q.Dw j).p + (T.Q.Dw j).q)), (b : ℕ) = a + 1 → (((dimFlag (T.Q.Dw j) + 3) ^ 2 + 2 * ((T.Q.Dw j).p + (T.Q.Dw j).q) : ℕ) : ℤ) ≤ u τ a - u τ b) → ∀ Z : Comp Y.d.Xo₂ Y.d.c₂, BirOn Y.U Z (wtOf (T.Q.Dw j) u 0) := by
  first | exact @_root_.GlobalTheory.DegVal.birOn_of_weight_gaps_large | exact _root_.GlobalTheory.DegVal.birOn_of_weight_gaps_large | (intros; apply _root_.GlobalTheory.DegVal.birOn_of_weight_gaps_large <;> assumption)
end
end
end
