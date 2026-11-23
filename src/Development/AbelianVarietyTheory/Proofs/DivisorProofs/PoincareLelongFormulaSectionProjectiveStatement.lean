module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoheightEqOneIffClosureDimProjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCoheightOneNotMemOpen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNonzeroLocusFormMap
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogResolutionProjectiveOfPrincipalisationStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullbackSectionZerosNormMultiplicitiesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoheightEqOneIffClosureDimProjectiveStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernIntegralPointClosurePullbackStatement
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumOrdPullbackMulResidueDegreeCodimOneStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernFormSignedPartMeasureEqOfIsometricProjStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedIntegralPullbackGenericallyFiniteStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareLelongNormalCrossingsSmoothProjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothWeightedLineBundleIsometryCalculusStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothWeightedLineBundleLogSectionNormPropertiesStatement
import Mathlib.Algebra.Azumaya.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFiniteRestrictNearCodimOne

section

@[expose] public section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.FiniteNearCodimOne

theorem le_one_of_add_eq {c : ℕ∞} {s t : WithBot ℕ∞} {D : ℕ} (h₁ : (c : WithBot ℕ∞) + s = D)
    (h₂ : ((1 : ℕ∞) : WithBot ℕ∞) + t = D) (hts : t ≤ s) : c ≤ 1 := by
  induction t using WithBot.recBotCoe with
  | bot => rw [WithBot.add_bot] at h₂; exact absurd h₂.symm (WithBot.natCast_ne_bot _)
  | coe t =>
    have h₃ : (c : WithBot ℕ∞) + t ≤ ((1 : ℕ∞) : WithBot ℕ∞) + t :=
      (add_le_add le_rfl hts).trans (h₁.trans h₂.symm).le
    have h₄ : 1 + t = (D : ℕ∞) := by exact_mod_cast h₂
    have ht : t ≠ ⊤ := by rintro rfl; rw [add_top] at h₄; exact ENat.natCast_ne_top _ h₄.symm
    have h₅ : c + t ≤ 1 + t := by exact_mod_cast h₃
    exact (ENat.add_le_add_iff_right ht).1 h₅

theorem coheight_eq_zero_iff {X : Scheme.{0}} [IsIntegral X] (x : X) :
    Order.coheight x = 0 ↔ x = genericPoint X := by
  rw [Order.coheight_eq_zero]
  constructor
  · intro h
    have h' : x ⤳ genericPoint X := h (show x ≤ genericPoint X from genericPoint_specializes x)
    exact (h'.antisymm (genericPoint_specializes x)).eq
  · rintro rfl b _
    exact genericPoint_specializes b

theorem exists_isFinite_restrict_of_coheight_eq_one : ∀ (F : Type) [Field F] (X Y : Scheme.{0})
    [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp F) (q : Y ⟶ Sp F) (D : ℕ), IsProjOver p →
    topologicalKrullDim X = (D : ℕ) → IsProjOver q → topologicalKrullDim Y = D →
    ∀ π : Y ⟶ X, π ≫ p = q → π (genericPoint Y) = genericPoint X → ∀ z : X,
    Order.coheight z = 1 → ∃ U : X.Opens, z ∈ U ∧ IsFinite (π ∣_ U) := by
  intro F _ X Y _ _ p q D hp hX hq hY π hπ hη z hz
  have : IsProper p := by
    obtain ⟨N, c, hc, rfl⟩ := hp
    have := isProper_str F N
    infer_instance
  have : IsProper q := by
    obtain ⟨N, c, hc, rfl⟩ := hq
    have := isProper_str F N
    infer_instance
  have : IsProper (π ≫ p) := by rw [hπ]; infer_instance
  have : IsProper π := IsProper.of_comp π p
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian q
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace q
  have : IsNoetherian Y := {}
  have hzne : z ≠ genericPoint X := fun h => by
    rw [(coheight_eq_zero_iff z).2 h] at hz
    exact zero_ne_one hz
  have hw : ∀ w : Y, π w = z → Order.coheight w = 1 := by
    intro w hwz
    have h₁ := (FieldDimCoheight.coheight_add_dim_closure_eq F Y q w).trans hY
    have h₂ := (FieldDimCoheight.coheight_add_dim_closure_eq F X p z).trans hX
    rw [hz] at h₂
    have h₃ := PosBaseChange.dim_image_le π.isClosedMap (isClosed_closure (s := ({w} : Set Y)))
    rw [← π.isClosedMap.closure_image_eq_of_continuous π.continuous, Set.image_singleton, hwz] at h₃
    refine le_antisymm (le_one_of_add_eq h₁ h₂ h₃) (Order.one_le_iff_ne_zero.2 fun h0 => ?_)
    rw [(coheight_eq_zero_iff w).1 h0] at hwz
    exact hzne (hwz.symm.trans hη)
  have hfin : (π ⁻¹' {z}).Finite := by
    let U : Y.Opens := π ⁻¹ᵁ ⟨(closure ({z} : Set X))ᶜ, isClosed_closure.isOpen_compl⟩
    have hU : genericPoint Y ∈ U := by
      show π (genericPoint Y) ∈ (closure ({z} : Set X))ᶜ
      rw [hη]
      intro hc
      exact hzne ((specializes_iff_mem_closure.2 hc).antisymm (genericPoint_specializes z)).eq
    refine (Mix.finite_coheight_one_notMem_open Y U hU).subset fun w hwz => ⟨hw w hwz, fun hwU => ?_⟩
    have hwU' : π w ∈ (closure ({z} : Set X))ᶜ := hwU
    exact hwU' (by rw [show π w = z from hwz]; exact subset_closure rfl)
  exact exists_isFinite_morphismRestrict_of_finite_preimage_singleton π z hfin

end GlobalTheory.FiniteNearCodimOne
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFiniteRestrictNearCodimOneStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

theorem _root_.GlobalTheory.T.exists_isFinite_restrict_near_codimOne : ∀ (F : Type) [Field F] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp F) (q : Y ⟶ Sp F) (D : ℕ), IsProjOver p → topologicalKrullDim X = (D : ℕ) → IsProjOver q → topologicalKrullDim Y = D → ∀ π : Y ⟶ X, π ≫ p = q → π (genericPoint Y) = genericPoint X → ∀ z : X, Order.coheight z = 1 → ∃ U : X.Opens, z ∈ U ∧ IsFinite (π ∣_ U) := by
  first | exact @GlobalTheory.FiniteNearCodimOne.exists_isFinite_restrict_of_coheight_eq_one | exact GlobalTheory.FiniteNearCodimOne.exists_isFinite_restrict_of_coheight_eq_one | (intros; apply GlobalTheory.FiniteNearCodimOne.exists_isFinite_restrict_of_coheight_eq_one <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumDivisorIntegralPushforward

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.Mix

theorem finsum_weighted_regroup_along_fibres {A B : Type} (π : A → B) (m : A → ℤ) (n : B → ℤ) (d : A → ℕ) (g : A → ℝ) (h : B → ℝ)
    (P : B → Prop) (hm : (Function.support m).Finite) (hn : (Function.support n).Finite)
    (hP : ∀ z, n z ≠ 0 → P z) (hs : ∀ z, P z → ∑ᶠ (w : A) (_ : π w = z), m w * (d w : ℤ) = n z)
    (h₁ : ∀ w, m w ≠ 0 → P (π w) → g w = d w * h (π w)) (h₀ : ∀ w, m w ≠ 0 → ¬ P (π w) → g w = 0) :
    ∑ᶠ w, (m w : ℝ) * g w = ∑ᶠ z, (n z : ℝ) * h z := by
  classical
  set S := hm.toFinset with hS
  set T := hn.toFinset ∪ S.image π with hT
  have hmS : ∀ w, m w ≠ 0 ↔ w ∈ S := fun w => by simp [hS]
  rw [finsum_eq_sum_of_support_subset (s := S) _ (fun w hw => by
      have : m w ≠ 0 := fun h0 => hw (by simp [h0])
      exact Finset.mem_coe.2 ((hmS w).1 this)),
    finsum_eq_sum_of_support_subset (s := T) _ (fun z hz => by
      have : n z ≠ 0 := fun h0 => hz (by simp [h0])
      simp [hT, this]),
    ← Finset.sum_fiberwise_of_maps_to (s := S) (t := T) (g := π) (fun w hw => by
      simp only [hT, Finset.mem_union]; exact Or.inr (Finset.mem_image_of_mem _ hw))]
  refine Finset.sum_congr rfl fun z _ => ?_
  by_cases hz : P z
  · have e : ∑ᶠ (w : A) (_ : π w = z), m w * (d w : ℤ) = ∑ w ∈ S.filter (fun w => π w = z), m w * (d w : ℤ) := by
      refine finsum_mem_eq_sum_of_inter_support_eq (s := {w | π w = z}) _ ?_
      ext w
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Function.mem_support, Finset.coe_filter]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨⟨(hmS w).1 (left_ne_zero_of_mul h2), h1⟩, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1.2, h2⟩
    rw [← hs z hz, e]
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun w hw => ?_
    obtain ⟨hw', rfl⟩ := Finset.mem_filter.1 hw
    rw [h₁ w ((hmS w).2 hw') hz, mul_assoc]
  · have e : n z = 0 := by
      by_contra h'
      exact hz (hP z h')
    rw [e, Int.cast_zero, zero_mul]
    refine Finset.sum_eq_zero fun w hw => ?_
    obtain ⟨hw', rfl⟩ := Finset.mem_filter.1 hw
    rw [h₀ w ((hmS w).2 hw') hz, mul_zero]

theorem finsum_cycInt_push : ∀ (F : Type) [Field F] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (p : X ⟶ Sp F) (q : Y ⟶ Sp F) (σ : F →+* ℂ) (e : ℕ), IsProjOver p → topologicalKrullDim X = (e + 1 : ℕ) → IsProjOver q → topologicalKrullDim Y = (e + 1 : ℕ) → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) = genericPoint X → ∀ (Δ : CartierDiv X) (Δ' : CartierDiv Y), (∀ z : X, Order.coheight z = 1 → ∑ᶠ (w : Y) (_ : π w = z), Δ'.mult w * (π.residueDegree w : ℤ) = Δ.mult z) → ∀ (L : Fin e → MLine p σ) (f : CxPts p σ → ℝ), Measurable f → ∑ᶠ w, (Δ'.mult w : ℝ) * cycInt (fun i => (L i).pull π hπ) (fun y => f (ptMap π hπ σ y)) w = ∑ᶠ z, (Δ.mult z : ℝ) * cycInt L f z := by
  intro F _ X Y _ _ _ _ p q σ e hp hX hq hY π hπ _ Δ Δ' hΔ L f hf
  have hc : ∀ {Z : Scheme.{0}} {s : Z ⟶ Sp F}, IsProjOver s → CompactSpace Z := by
    rintro Z _ ⟨m, i, hi, rfl⟩
    have := isProper_str F m
    have : IsProper (i ≫ PSpace.str F m) := inferInstance
    exact QuasiCompact.compactSpace_of_compactSpace (i ≫ PSpace.str F m)
  haveI := hc hp
  haveI := hc hq
  have key := fun (w : Y) (hw : Δ'.mult w ≠ 0) => GlobalTheory.T.mixedChernIntegral_pointClosure_pullback F X Y p q σ hp hq π hπ e L f hf w
    ((GlobalTheory.T.coheight_eq_one_iff_closure_dim_projective F Y q e hq hY w).1 (CartierDiv.coheight_eq_one_of_mult_ne_zero (D := Δ') hw))
  exact finsum_weighted_regroup_along_fibres π Δ'.mult Δ.mult (fun w => π.residueDegree w) _ _ (fun z => Order.coheight z = 1)
    Δ'.finite_support_mult Δ.finite_support_mult
    (fun z hz => CartierDiv.coheight_eq_one_of_mult_ne_zero (D := Δ) hz) hΔ
    (fun w hw h => (key w hw).1 ((GlobalTheory.T.coheight_eq_one_iff_closure_dim_projective F X p e hp hX _).1 h))
    (fun w hw h => (key w hw).2 fun h' => h ((GlobalTheory.T.coheight_eq_one_iff_closure_dim_projective F X p e hp hX _).2 h'))

end GlobalTheory.Mix
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumDivisorIntegralPushforwardStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

theorem _root_.GlobalTheory.T.finsum_divisorIntegral_pushforward : ∀ (F : Type) [Field F] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (p : X ⟶ Sp F) (q : Y ⟶ Sp F) (σ : F →+* ℂ) (e : ℕ), IsProjOver p → topologicalKrullDim X = (e + 1 : ℕ) → IsProjOver q → topologicalKrullDim Y = (e + 1 : ℕ) → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) = genericPoint X → ∀ (Δ : CartierDiv X) (Δ' : CartierDiv Y), (∀ z : X, Order.coheight z = 1 → ∑ᶠ (w : Y) (_ : π w = z), Δ'.mult w * (π.residueDegree w : ℤ) = Δ.mult z) → ∀ (L : Fin e → MLine p σ) (f : CxPts p σ → ℝ), Measurable f → ∑ᶠ w, (Δ'.mult w : ℝ) * cycInt (fun i => (L i).pull π hπ) (fun y => f (ptMap π hπ σ y)) w = ∑ᶠ z, (Δ.mult z : ℝ) * cycInt L f z := by
  first | exact @GlobalTheory.Mix.finsum_cycInt_push | exact GlobalTheory.Mix.finsum_cycInt_push | (intros; apply GlobalTheory.Mix.finsum_cycInt_push <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareLelongNormalCrossingsSmoothProjectiveStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

theorem _root_.GlobalTheory.T.poincareLelong_normalCrossings_smoothProjective : ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (e : ℕ), IsProjOver p → SmoothOfRelativeDimension (e + 1) p → ∀ (L : Fin e → MLine p σ) (M : MLine p σ) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s), FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal (nonzeroLocus s).compl) → ∀ (u : CxPts p σ → ℝ) (hu : ∀ y, CInfAt u y), 2 * Mix.int (Fin.cons (MLine.ofFun u hu) L : Fin (e + 1) → MLine p σ) (M.logSec s) = ∑ᶠ z, ((divOfSec M.φ.isLB s hs).mult z : ℝ) * cycInt L u z - Mix.int (Fin.cons M L : Fin (e + 1) → MLine p σ) u := by
  first | exact @GlobalTheory.Mix.PLSnc.poincareLelong_snc | exact GlobalTheory.Mix.PLSnc.poincareLelong_snc | (intros; apply GlobalTheory.Mix.PLSnc.poincareLelong_snc <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareLelongFormulaSectionProjective

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory

theorem poincareLelong_sec : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (e : ℕ), IsProjOver p → topologicalKrullDim X = (e + 1 : ℕ) → ∀ (L : Fin e → MLine p σ) (M : MLine p σ) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (u : CxPts p σ → ℝ) (hu : ∀ y, CInfAt u y), 2 * Mix.int (Fin.cons (MLine.ofFun u hu) L : Fin (e + 1) → MLine p σ) (M.logSec s) = ∑ᶠ z, ((divOfSec M.φ.isLB s hs).mult z : ℝ) * cycInt L u z - Mix.int (Fin.cons M L : Fin (e + 1) → MLine p σ) u := by
  intro hP F _ X _ _ p σ e hX hdim L M s hs u hu
  haveI : CharZero F := RingHom.charZero σ
  obtain ⟨Y, hYi, π, hsm, hproj, hdimY, hgen, hdeg, hsnc⟩ :=
    GlobalTheory.T.exists_logResolution_projective_of_principalisation hP F X p (e + 1) hX hdim (nonzeroLocus s).compl (fun h => h hs)
  haveI := hYi
  haveI : IsLocallyNoetherian Y := by
    haveI := SmoothOfRelativeDimension.smooth (e + 1) (π ≫ p)
    exact LocallyOfFiniteType.isLocallyNoetherian (π ≫ p)
  have hη : π (genericPoint Y) ⤳ genericPoint X := by rw [hgen]
  obtain ⟨s', hnz, hnsq, hmult⟩ := GlobalTheory.T.exists_pullback_section_zeros_norm_multiplicities F X Y p (π ≫ p) σ π rfl M s
  have hs' : genericPoint Y ∈ nonzeroLocus s' := by
    rw [hnz]; show π (genericPoint Y) ∈ nonzeroLocus s; rw [hgen]; exact hs
  have hsnc' : FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal (nonzeroLocus s').compl) := by
    convert hsnc using 2
    ext x
    simp [hnz]
  have hPL := GlobalTheory.T.poincareLelong_normalCrossings_smoothProjective F Y (π ≫ p) σ e hproj hsm (fun i => (L i).pull π rfl) (M.pull π rfl) s' hs' hsnc'
    (fun y => u (ptMap π rfl σ y)) (fun z => (hu _).pull π rfl)
  have hmu : Measurable u := (continuous_iff_continuousAt.2 fun y => (hu y).continuousAt).measurable
  have hml : Measurable (M.logSec s) := (GlobalTheory.T.smoothWeightedLineBundle_logSectionNorm_properties F X p σ M s).1
  have hiso := GlobalTheory.T.smoothWeightedLineBundle_isometry_calculus F X Y p (π ≫ p) σ π rfl
  have hrefl := (GlobalTheory.T.smoothWeightedLineBundle_isometry_calculus F Y Y (π ≫ p) (π ≫ p) σ (𝟙 Y) (Category.id_comp _)).1
  have hdeg' : π.residueDegree (genericPoint Y) ≠ 0 := by rw [hdeg]; exact one_ne_zero
  have intEq : ∀ (A B : Fin (e + 1) → MLine (π ≫ p) σ), (∀ i, (A i).Isom (B i)) → ∀ f, Mix.int A f = Mix.int B f := by
    intro A B h f
    simp only [Mix.int, GlobalTheory.T.mixedChernFormSignedPartMeasure_eq_of_isometric_projOver F Y (π ≫ p) σ hproj (e + 1) A B h]
  have hlog : (M.pull π rfl).logSec s' = fun y => M.logSec s (ptMap π rfl σ y) := by
    funext y; simp only [MLine.logSec, hnsq]

  have hA : Mix.int (Fin.cons (MLine.ofFun (fun y => u (ptMap π rfl σ y)) (fun z => (hu _).pull π rfl)) (fun i => (L i).pull π rfl) : Fin (e + 1) → MLine (π ≫ p) σ) ((M.pull π rfl).logSec s')
      = Mix.int (Fin.cons (MLine.ofFun u hu) L : Fin (e + 1) → MLine p σ) (M.logSec s) := by
    rw [hlog, ← intEq (fun i => ((Fin.cons (MLine.ofFun u hu) L : Fin (e + 1) → MLine p σ) i).pull π rfl)]
    · rw [(GlobalTheory.T.mixedIntegral_pullback_genericallyFinite F X Y p (π ≫ p) σ (e + 1) hX hdim hproj π rfl hgen hdeg' _ _ hml).2, hdeg]
      simp
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hiso.2.2.2.1 u hu
      · simpa using hrefl ((L j).pull π rfl)
  have hB : Mix.int (Fin.cons (M.pull π rfl) (fun i => (L i).pull π rfl) : Fin (e + 1) → MLine (π ≫ p) σ) (fun y => u (ptMap π rfl σ y))
      = Mix.int (Fin.cons M L : Fin (e + 1) → MLine p σ) u := by
    rw [← intEq (fun i => ((Fin.cons M L : Fin (e + 1) → MLine p σ) i).pull π rfl)]
    · rw [(GlobalTheory.T.mixedIntegral_pullback_genericallyFinite F X Y p (π ≫ p) σ (e + 1) hX hdim hproj π rfl hgen hdeg' _ _ hmu).2, hdeg]
      simp
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hrefl (M.pull π rfl)
      · simpa using hrefl ((L j).pull π rfl)
  have hS := GlobalTheory.T.finsum_divisorIntegral_pushforward F X Y p (π ≫ p) σ e hX hdim hproj hdimY π rfl hgen
    (divOfSec M.φ.isLB s hs) (divOfSec (M.pull π rfl).φ.isLB s' hs') (by
      intro z hz
      obtain ⟨i, hi⟩ := exists_chart M.φ.isLB z
      have hfin := GlobalTheory.T.exists_isFinite_restrict_near_codimOne F X Y p (π ≫ p) (e + 1) hX hdim hproj hdimY π rfl hgen z hz
      have hord := GlobalTheory.T.finsum_ord_pullback_mul_residueDegree_codim_one X Y π hη z hz hfin (ratOfSec s hs i : X.functionField) (Units.ne_zero _)
      calc _ = ∑ᶠ (w : Y) (_ : π w = z), Scheme.ord (TrueGeo.SmallSec.fnMap π hη (ratOfSec s hs i : X.functionField)) w * (π.residueDegree w : ℤ) :=
            finsum_congr fun w => finsum_congr fun hw => by
              rw [hmult hη hs hs' w i (hw ▸ hi)]
        _ = _ := hord
        _ = _ := by
          rw [hdeg, Nat.cast_one, one_mul, ((presents_divOfRatSec M.φ.isLB _).isEqn i z hi).mult_eq])
    L u hmu
  rw [hA, hB, hS] at hPL
  exact hPL

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareLelongFormulaSectionProjectiveStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

theorem _root_.GlobalTheory.T.poincareLelong_formula_section_projective : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (e : ℕ), IsProjOver p → topologicalKrullDim X = (e + 1 : ℕ) → ∀ (L : Fin e → MLine p σ) (M : MLine p σ) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (u : CxPts p σ → ℝ) (hu : ∀ y, CInfAt u y), 2 * Mix.int (Fin.cons (MLine.ofFun u hu) L : Fin (e + 1) → MLine p σ) (M.logSec s) = ∑ᶠ z, ((divOfSec M.φ.isLB s hs).mult z : ℝ) * cycInt L u z - Mix.int (Fin.cons M L : Fin (e + 1) → MLine p σ) u := by
  first | exact @GlobalTheory.poincareLelong_sec | exact GlobalTheory.poincareLelong_sec | (intros; apply GlobalTheory.poincareLelong_sec <;> assumption)
end
end
