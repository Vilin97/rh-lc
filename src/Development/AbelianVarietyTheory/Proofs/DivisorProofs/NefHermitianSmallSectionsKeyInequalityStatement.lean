module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithSelfIntersectionMonoOfIsNefStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxFamilyMovingPartsChainBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBirationalModelTotallyOrderedFamilyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFubiniStudyOfTotallyOrderedRatFnFamilyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FubiniStudyBundleIsNefOfNonnegWeightsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FubiniStudyLeShiftOfSmallSectionsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLBLeBySmallSectionTensorIsometricTransShiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLineBundleIsNefPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLineBundleIsNefShiftOfNonneg
public import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernLeviEqConstant
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices
import Development.AbelianVarietyTheory.Definitions.Foundations.CurveCl
import Formalism.DegreeFormula.FlagDegFormula
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BirationalModelRegularUnitValuesStatement
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Basify

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricDegreePullBirationalModel

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSNef

theorem isometric_pull_shiftC {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k}
    (L : HermLB p) (t : ℝ) (π : Y ⟶ X) (hπ : π ≫ p = q) :
    ((L.shift (fun _ => t) fun _ => rfl).pull π hπ).Isometric ((L.pull π hπ).shift (fun _ => t) fun _ => rfl) :=
  HermLB.isometric_of_eqOn fun σ a y _ => by
    exact (congrArg (· + 2 * t) (Weight.pull_φ (L.φ σ) π hπ a y)).trans
      (Weight.pull_φ ((L.φ σ).addFn fun _ => 2 * t) π hπ a y).symm

theorem gdeg_pull_model : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y]
    (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D : ℕ), IsArithVar p D → IsArithVar q D → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q)
    (φ : X.functionField →+* Y.functionField), IsModel π φ → ∀ L : HermLB p, gdeg (L.pull π hπ) D = gdeg L D ∧
    ∀ (a t : ℝ), L.IsSelfInter a →
      ((L.pull π hπ).shift (fun _ => t) fun _ => rfl).IsSelfInter (a + ((D : ℝ) + 1) * t * gdeg L D) := by
  intro hC k _ X Y _ _ p q D hX hY π hπ φ hM L
  have hdeg : π.residueDegree (genericPoint Y) ≠ 0 := by rw [hM.deg]; exact one_ne_zero
  have hP := ((hC.arProj k X Y p q D hX hY π hπ hM.gen hdeg).1)
  have hP1 : ∀ (M : HermLB p) (a : ℝ), M.IsSelfInter a → (M.pull π hπ).IsSelfInter a := fun M a h => by
    have := hP M a h
    rwa [hM.deg, Nat.cast_one, one_mul] at this
  have hS := hC.arShift
  have hg : gdeg (L.pull π hπ) D = gdeg L D := by
    obtain ⟨h, hh⟩ := ((hC.arExists k X p D hX).1 L)
    have ha : L.IsSelfInter (h (genericPoint X)) := ⟨h, hh, rfl⟩
    set a := h (genericPoint X)

    have h1 := hP1 _ _ (hS k X p D hX L a 1 ha)
    have h1' := (isometric_pull_shiftC L 1 π hπ).isSelfInter hY h1
    have h2 := hS k Y q D hY (L.pull π hπ) a 1 (hP1 L a ha)
    have e := HermLB.IsSelfInter.unique hY h1' h2
    have hD : ((D : ℝ) + 1) ≠ 0 := by positivity
    have : ((D : ℝ) + 1) * gdeg L D = ((D : ℝ) + 1) * gdeg (L.pull π hπ) D := by linarith
    exact (mul_left_cancel₀ hD this).symm
  refine ⟨hg, fun a t ha => ?_⟩
  have := hS k Y q D hY (L.pull π hπ) a t (hP1 L a ha)
  rwa [hg] at this

end GlobalTheory.HSNef
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometricShiftOfIsometric

section

@[expose] public section

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CovTest.GeoSwap

open HermLB

section Shift

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k}



theorem gdeg_shift_const (L : HermLB p) (t : (k →+* ℂ) → ℝ) (ht : ∀ σ, t ((starRingEnd ℂ).comp σ) = t σ) (D : ℕ) :
    gdeg (L.shift t ht) D = gdeg L D := by
  simp only [gdeg, chInt, HermLB.shift, Weight.chernInt, Weight.chernPart_addFn_const]

end Shift

end GlobalTheory.CovTest.GeoSwap

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatFnFamilySmallPullbackBirationalModel

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

namespace GlobalTheory.HSNef

theorem smallFam_pull : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (π : Y ⟶ X) (hπ : π ≫ p = q) (φ : X.functionField →+* Y.functionField), IsModel π φ → ∀ (B : HermLB p) (J : Type) (f : J → X.functionField) (w : J → ℝ), SmallFam B f w → SmallFam (B.pull π hπ) (fun j => φ (f j)) w := by
  intro k _ X Y _ _ p q π hπ φ hM B J f w hs
  obtain ⟨β, hβ, hreg, hnorm⟩ := hs
  obtain ⟨hR, -, hF, hV⟩ := GlobalTheory.T.birationalModel_regular_unit_values k X Y p q π hπ φ hM
  refine ⟨fun c => Units.map φ.toMonoidHom (β (c PUnit.unit)), ?_, ?_, ?_⟩
  · intro i j h
    have hi : genericPoint Y ∈ π ⁻¹ᵁ B.B.U (i PUnit.unit) :=
      LB.wchart_le B.B (fun _ : PUnit => π) i PUnit.unit h.1
    have hj : genericPoint Y ∈ π ⁻¹ᵁ B.B.U (j PUnit.unit) :=
      LB.wchart_le B.B (fun _ : PUnit => π) j PUnit.unit h.2
    have hX : genericPoint X ∈ B.B.U (i PUnit.unit) ⊓ B.B.U (j PUnit.unit) := by
      rw [← hM.gen]; exact ⟨hi, hj⟩
    have eg : ((B.B.pull π).g i j).val = resG Y (fun _ hy => ⟨LB.wchart_le B.B (fun _ : PUnit => π) i PUnit.unit hy.1, LB.wchart_le B.B (fun _ : PUnit => π) j PUnit.unit hy.2⟩ : (B.B.pull π).U i ⊓ (B.B.pull π).U j ≤ π ⁻¹ᵁ (B.B.U (i PUnit.unit) ⊓ B.B.U (j PUnit.unit)))
        (π.app _ (B.B.g (i PUnit.unit) (j PUnit.unit)).val) := by
      dsimp only [LB.pull, LB.LinComb]
      simp only [Fintype.prod_unique, zpow_one, LB.val_res, pullU, Units.coe_map]
      rfl
    show φ (β (i PUnit.unit)) = fnOf _ h ((B.B.pull π).g i j).val * φ (β (j PUnit.unit))
    rw [hβ (i PUnit.unit) (j PUnit.unit) hX, map_mul, hF _ hX ⟨hi, hj⟩, eg]
    exact congrArg (· * φ (β (j PUnit.unit))) (fnOf_resG (X := Y) (U := π ⁻¹ᵁ (B.B.U (i PUnit.unit) ⊓ B.B.U (j PUnit.unit))) (fun _ hy => ⟨LB.wchart_le B.B (fun _ : PUnit => π) i PUnit.unit hy.1, LB.wchart_le B.B (fun _ : PUnit => π) j PUnit.unit hy.2⟩ : (B.B.pull π).U i ⊓ (B.B.pull π).U j ≤ π ⁻¹ᵁ (B.B.U (i PUnit.unit) ⊓ B.B.U (j PUnit.unit))) h (π.app _ (B.B.g (i PUnit.unit) (j PUnit.unit)).val)).symm
  · intro y c hy j
    show RegAt y (φ (f j) * φ (β (c PUnit.unit)))
    rw [← map_mul]
    exact hR y _ (hreg (π y) (c PUnit.unit) (LB.wchart_le B.B (fun _ : PUnit => π) c PUnit.unit hy) j)
  · intro σ z c hz j
    have hm := mem_of_mem_linComb (m := fun _ => GlobalTheory.Points.PtsOver.map π hπ _ z) (fun _ => rfl) hz
      PUnit.unit
    have hr := hreg (π (under z)) (c PUnit.unit) (mem_ptsIn.1 hm) j
    have e2 : ((B.φ σ).pull π hπ).φ c z = (B.φ σ).φ (c PUnit.unit) (GlobalTheory.Points.PtsOver.map π hπ _ z) :=
      (B.φ σ).pull_φ π hπ c z
    show ‖ratVal (φ (f j) * φ (β (c PUnit.unit))) z‖ * Real.exp (-((B.φ σ).pull π hπ).φ c z / 2) ≤ _
    rw [← map_mul, hV σ z _ hr, e2]
    exact hnorm σ _ (c PUnit.unit) hm j

end GlobalTheory.HSNef
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatFnFamilySmallPullbackBirationalModelStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem _root_.GlobalTheory.T.ratFnFamilySmall_pullback_birationalModel : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (π : Y ⟶ X) (hπ : π ≫ p = q) (φ : X.functionField →+* Y.functionField), IsModel π φ → ∀ (B : HermLB p) (J : Type) (f : J → X.functionField) (w : J → ℝ), SmallFam B f w → SmallFam (B.pull π hπ) (fun j => φ (f j)) w := by
  first | exact @GlobalTheory.HSNef.smallFam_pull | exact GlobalTheory.HSNef.smallFam_pull | (intros; apply GlobalTheory.HSNef.smallFam_pull <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefHermitianSmallSectionsKeyInequality

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSNefCore

theorem key_ineq : GlobalTheory.Published.ArCalc → AmpleHS → SemiPull → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (B : HermLB p) (β : ℝ), B.IsNef D → B.IsSelfInter β → ∀ (x : Fin D → X.functionField) (Δ : ℝ), AlgebraicIndependent ℤ x → 0 < Δ → ∀ (J : Type) [Fintype J] [Nonempty J] (e : J → X.functionField) (n : J → ℕ), LinearIndependent ℤ e → SmallFam B (boxFam e x) (fun c => n c.1 * Δ) → ((D + 1).factorial : ℝ) * Δ * ((∑ j, (n j + 1) : ℕ) : ℝ) ≤ β + ((D : ℝ) + 1) * (Δ + D * Real.log 2 / 2 + Real.log (Fintype.card J) / 2) * gdeg B D := by
  intro hA hAmp hSP k _ X _ p D hX B β hB hβ x Δ hx hΔ J _ _ e n he hsm

  have hne : ∀ c, boxFam e x c ≠ 0 := by
    intro c
    simp only [boxFam]
    refine mul_ne_zero (he.ne_zero c.1) ?_
    exact Finset.prod_ne_zero_iff.2 fun i _ => hx.ne_zero i
  obtain ⟨Y, hY, π, φ, hvarY, hmod, htot⟩ := GlobalTheory.T.exists_birationalModel_totallyOrdered_family k X p D hX (J × Finset (Fin D)) (boxFam e x) hne
  haveI := hY
  set q := π ≫ p with hq
  set f : J × Finset (Fin D) → Y.functionField := fun c => φ (boxFam e x c) with hf
  have hbox : f = boxFam (φ ∘ e) (φ ∘ x) := by
    funext c
    simp [hf, boxFam, map_mul, map_prod]
  have hx' : AlgebraicIndependent ℤ (φ ∘ x) := hx.map' (f := φ.toIntAlgHom) φ.injective
  have he' : LinearIndependent ℤ (φ ∘ e) :=
    he.map' φ.toIntAlgHom.toLinearMap (LinearMap.ker_eq_bot.2 φ.injective)
  set w : J × Finset (Fin D) → ℝ := fun c => n c.1 * Δ with hw
  obtain ⟨M, hM⟩ := GlobalTheory.T.exists_fubiniStudy_of_totallyOrdered_ratFnFamily k Y q (J × Finset (Fin D)) f w htot
  obtain ⟨μ, hμ⟩ : ∃ μ, M.IsSelfInter μ := by
    obtain ⟨Φ, hΦ⟩ := ((hA.arExists k Y q D hvarY).2 PUnit fun _ => M).1
    exact ⟨_, ((hA.arIso k Y q D hvarY).2 PUnit _ Φ hΦ).1 PUnit.unit⟩

  have hN : ∀ j, n j ≤ ∑ i, n i := fun j => Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  have hchain := GlobalTheory.HSNef.chain_moving_parts hA hAmp hSP k Y q D hvarY (φ ∘ x) Δ hx' hΔ (∑ i, n i) J (φ ∘ e) n M μ he' hN
    (hbox ▸ htot) (hbox ▸ hM) hμ

  set s : ℝ := Real.log (Fintype.card (J × Finset (Fin D))) / 2 with hs
  set B' := B.pull π rfl with hB'
  have hsmall : SmallFam B' f w := GlobalTheory.T.ratFnFamilySmall_pullback_birationalModel k X Y p q π rfl φ hmod B _ (boxFam e x) w hsm
  have hle : Le M (B'.shift (fun _ => s) fun _ => rfl) := GlobalTheory.T.fubiniStudy_le_shift_of_smallSections k Y q M B' _ f w hM hsmall
  have hle' := (GlobalTheory.T.hermLBLeBySmallSection_tensor_isometric_trans_shift k Y q (B'.shift (fun _ => s) fun _ => rfl) M M).2.2.2 Δ hle

  have hs0 : 0 ≤ s := by
    rw [hs]
    have : (1 : ℝ) ≤ Fintype.card (J × Finset (Fin D)) := by exact_mod_cast Fintype.card_pos
    have := Real.log_nonneg this
    linarith
  have hMnef : M.IsNef D := GlobalTheory.T.fubiniStudy_bundle_isNef_of_nonneg_weights hA k Y q D hvarY M _ f w hM fun c => by
    simp only [hw]; exact mul_nonneg (Nat.cast_nonneg _) hΔ.le
  have hB'nef : B'.IsNef D := GlobalTheory.T.hermitianLineBundle_isNef_pullback hA hSP k X Y p q D D hX hvarY π rfl B hB
  have hA1 := GlobalTheory.NefShift.isNef_shift_nonneg k Y q D hvarY B' s hs0 hB'nef
  have hA2 := GlobalTheory.NefShift.isNef_shift_nonneg k Y q D hvarY _ Δ hΔ.le hA1
  have hM2 := GlobalTheory.NefShift.isNef_shift_nonneg k Y q D hvarY M Δ hΔ.le hMnef

  obtain ⟨hg, hgs⟩ := GlobalTheory.HSNef.gdeg_pull_model hA k X Y p q D hX hvarY π rfl φ hmod B
  have h1 := hgs β s hβ
  have h2 := hA.arShift k Y q D hvarY _ _ Δ h1
  have h3 := hA.arShift k Y q D hvarY M μ Δ hμ
  have hmono := GlobalTheory.T.arithSelfIntersection_mono_of_isNef hA hAmp hSP k Y q D hvarY _ _ _ _ hA2 hM2 hle' h2 h3
  rw [GlobalTheory.CovTest.GeoSwap.gdeg_shift_const, hg] at hmono

  have hcard : s = Real.log (Fintype.card J) / 2 + D * Real.log 2 / 2 := by
    rw [hs, Fintype.card_prod, Fintype.card_finset, Fintype.card_fin]
    push_cast
    rw [Real.log_mul (by exact_mod_cast Fintype.card_ne_zero) (by positivity), Real.log_pow]
    ring
  rw [hcard] at hmono
  nlinarith [hchain, hmono]

end GlobalTheory.HSNefCore
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefHermitianSmallSectionsKeyInequalityStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem _root_.GlobalTheory.T.nef_hermitian_small_sections_key_inequality : GlobalTheory.Published.ArCalc → AmpleHS → SemiPull → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (B : HermLB p) (β : ℝ), B.IsNef D → B.IsSelfInter β → ∀ (x : Fin D → X.functionField) (Δ : ℝ), AlgebraicIndependent ℤ x → 0 < Δ → ∀ (J : Type) [Fintype J] [Nonempty J] (e : J → X.functionField) (n : J → ℕ), LinearIndependent ℤ e → SmallFam B (boxFam e x) (fun c => n c.1 * Δ) → ((D + 1).factorial : ℝ) * Δ * ((∑ j, (n j + 1) : ℕ) : ℝ) ≤ β + ((D : ℝ) + 1) * (Δ + D * Real.log 2 / 2 + Real.log (Fintype.card J) / 2) * gdeg B D := by
  first | exact @GlobalTheory.HSNefCore.key_ineq | exact GlobalTheory.HSNefCore.key_ineq | (intros; apply GlobalTheory.HSNefCore.key_ineq <;> assumption)
end
end
