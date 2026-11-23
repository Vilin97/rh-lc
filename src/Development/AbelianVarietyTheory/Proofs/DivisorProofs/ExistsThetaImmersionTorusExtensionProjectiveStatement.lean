module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueLbIsoPullEqOfCoheightLeOne
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegExp
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsAmpleTensorAmplePowProjective
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
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusPt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVeryAmpleBySecBZero
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitSvalIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubringEqTopOfWeightUnits
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SvalEqSecRatioMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionSmoothAffineSurjectiveFourierTerms
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSecBGenerating

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CechPic

namespace GlobalTheory.Mum

theorem exists_secB_generating : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (D : DegPre R) (α : D.X),
    ∃ k₀ : ℕ, ∀ k ≥ k₀, ∃ (n : ℕ) (b : Fin n → D.SecB k α), ⨆ j, nonzeroLocus (b j) = ⊤ := by
  intro R _ _ _ D α
  have hL := D.P.isLB
  have := D.P.isAb.proper
  have hA : IsAmpleLB D.P.L := (relAmple_iff_isAmpleLB_of_isAffine D.P.A hL).1 D.P.ample
  have hN : ∀ k, (LB.LinComb D.P.L (D.famφB α) (DegPre.famε k)).IsLB := fun k => LB.isLB_linComb hL _ _
  obtain ⟨k₀, hk⟩ := eventually_atTop.1 (hA.eventually_isGenerated_tens_lbPow (hN 0))
  refine ⟨k₀, fun k h => ?_⟩
  have hP := isLB_lbPow hL k
  have hT := isLB_tens (hN 0) hP
  refine (hk k h).of_lbIso (hN k) (iso_of_chart hT ⟨fun j => (j, fun _ => j 0), fun _ _ hj => ⟨hj, ?_⟩, ?_⟩)
  · exact Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hj 0
  · intro y p q hp hq

    refine (gm_linComb D.P.L (D.famφB α) (DegPre.famε k) (𝟙 _) y p q hp hq).trans ?_
    refine ((gm_tens (LB.LinComb D.P.L (D.famφB α) (DegPre.famε 0)) (lbPow D.P.L k) (𝟙 _) y (p, fun _ => p 0) (q, fun _ => q 0) ⟨hp, Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hp 0⟩ ⟨hq, Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hq 0⟩).trans ?_).symm
    refine (congrArg₂ (· * ·) (gm_linComb D.P.L (D.famφB α) (DegPre.famε 0) (𝟙 _) y p q hp hq) (gm_linComb D.P.L (fun _ : PUnit => 𝟙 _) (fun _ => (k : ℤ)) (𝟙 _) y (fun _ => p 0) (fun _ => q 0) (Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hp 0) (Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hq 0))).trans ?_
    simp only [Fin.prod_univ_four, Fintype.prod_unique, DegPre.famφB, DegPre.famε, Matrix.cons_val, Category.id_comp, zpow_sub, zpow_one]
    simp only [Nat.cast_zero, zpow_zero, one_mul]
    ac_rfl

end GlobalTheory.Mum
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GermPullbackRestrictEq

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem germPullback_restrict_eq {X Z : Scheme.{0}} (f : Z ⟶ X) (z : Z) {U V : X.Opens} (hle : V ≤ U) (h : f z ∈ V)
    (a : Γ(X, U)) : gs f z V (resG X hle a) = gs f z U a := gs_res f z hle h a


open GlobalTheory.ProjSpace in
theorem secRatio_isTermOf_zero : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (Y : Ext D) (k : ℕ) (b₀ b : D.SecB k 0) (τ₀ τ : SecK D.P.L Y.q.left k), IsTermOf Y b₀ τ₀ → IsTermOf Y b τ → ∀ (W : Y.H.left.Opens) (h₁ : W ≤ Y.q.left ⁻¹ᵁ nonzeroLocus b₀) (h₂ : W ≤ nonzeroLocus τ₀), (Y.q.left.appLE (nonzeroLocus b₀) W h₁).hom (GlobalTheory.ProjSpace.secRatio b₀ b) = resG Y.H.left h₂ (GlobalTheory.ProjSpace.secRatio τ₀ τ) := by
  intro R _ _ D Y k b₀ b τ₀ τ h₀ h W h₁ h₂
  apply fn_ext
  intro y hy
  rw [gs_appLE Y.q.left (nonzeroLocus b₀) W h₁ (𝟙 _) y hy, Category.id_comp,
    germPullback_restrict_eq (𝟙 Y.H.left) y h₂ hy]
  choose J hJ using fun ψ : Y.H.left ⟶ D.P.A.left => ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart D.P.isLB (ψ y)
  have hG : Good D.P.L y J := hJ
  have e := h Y.H (𝟙 _) y J hG
  have e₀ := h₀ Y.H (𝟙 _) y J hG
  rw [Category.id_comp] at e e₀

  have hqy : Y.q.left y ∈ nonzeroLocus b₀ ⊓ LB.wchart D.P.L (D.famφB 0) (fun κ => J (Y.q.left ≫ D.famφB 0 κ)) :=
    ⟨h₁ hy, hG.mem (D.famφB 0) Y.q.left⟩
  have sb := congrArg (gs Y.q.left y _) (secRatio_on b₀ b (fun κ => J (Y.q.left ≫ D.famφB 0 κ))
    (W := nonzeroLocus b₀ ⊓ LB.wchart D.P.L (D.famφB 0) (fun κ => J (Y.q.left ≫ D.famφB 0 κ))) inf_le_left inf_le_right)
  rw [gs_mul _ y _ hqy] at sb
  erw [germPullback_restrict_eq _ y _ hqy, germPullback_restrict_eq _ y _ hqy, germPullback_restrict_eq _ y _ hqy] at sb

  have hyτ : (𝟙 Y.H.left) y ∈ nonzeroLocus τ₀ ⊓ LB.wchart D.P.L (fun _ : Fin 1 => Y.q.left) (fun _ : Fin 1 => J (𝟙 Y.H.left ≫ Y.q.left)) :=
    ⟨h₂ hy, hG.mem (fun _ : Fin 1 => Y.q.left) (𝟙 Y.H.left)⟩
  have sτ := congrArg (gs (𝟙 Y.H.left) y _) (secRatio_on τ₀ τ (fun _ : Fin 1 => J (𝟙 Y.H.left ≫ Y.q.left))
    (W := nonzeroLocus τ₀ ⊓ LB.wchart D.P.L (fun _ : Fin 1 => Y.q.left) (fun _ : Fin 1 => J (𝟙 Y.H.left ≫ Y.q.left))) inf_le_left inf_le_right)
  rw [gs_mul _ y _ hyτ] at sτ
  erw [germPullback_restrict_eq _ y _ hyτ, germPullback_restrict_eq _ y _ hyτ, germPullback_restrict_eq _ y _ hyτ] at sτ
  have hu : IsUnit (sval τ₀ (𝟙 Y.H.left) y J) :=
    (GlobalTheory.AmpleSpan.mem_nonzeroLocus_iff_gs τ₀ (𝟙 Y.H.left) y hyτ.2).1 hyτ.1
  change sval τ (𝟙 Y.H.left) y J = _ * sval τ₀ (𝟙 Y.H.left) y J at sτ
  change sval b Y.q.left y J = _ * sval b₀ Y.q.left y J at sb
  change sval τ (𝟙 Y.H.left) y J = _ at e
  change sval τ₀ (𝟙 Y.H.left) y J = _ at e₀
  refine hu.mul_right_cancel ?_
  rw [← sτ, e, sb, e₀]
  exact (_root_.mul_assoc _ _ _).symm
end GlobalTheory.Mum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsImmersionOfForallAffineSurjectiveAppLE

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory

theorem isImmersion_of_forall_affine_surjective_appLE : ∀ (Y Z : Scheme.{0}) (φ : Y ⟶ Z), (∀ y : Y, ∃ (U : Z.Opens) (W : Y.Opens) (h : W ≤ φ ⁻¹ᵁ U), IsAffineOpen U ∧ φ y ∈ U ∧ φ ⁻¹ᵁ U ≤ W ∧ IsAffineOpen W ∧ Function.Surjective (φ.appLE U W h).hom) → IsImmersion φ := by
  intro Y Z φ H
  have H' : ∀ y : Y, ∃ U : Z.Opens, φ y ∈ U ∧ IsClosedImmersion (φ ∣_ U) := by
    intro y
    obtain ⟨U, W, h, hU, hy, hW, hWa, hs⟩ := H y
    obtain rfl : W = φ ⁻¹ᵁ U := le_antisymm h hW
    refine ⟨U, hy, ?_⟩
    have : IsAffine U := hU
    have : IsAffine (φ ⁻¹ᵁ U) := hWa
    rw [MorphismProperty.arrow_mk_iso_iff @IsClosedImmersion
      (Arrow.isoMk hWa.isoSpec hU.isoSpec (Scheme.Opens.toSpecΓ_naturality φ _) :
        Arrow.mk (φ ∣_ U) ≅ Arrow.mk (Spec.map (φ.app U)))]
    rw [Scheme.Hom.app_eq_appLE]
    exact IsClosedImmersion.spec_of_surjective _ hs
  choose U hyU hU using H'
  have : MorphismProperty.RespectsRight @IsImmersion @IsOpenImmersion :=
    ⟨fun i hi g hg => by
      have : IsOpenImmersion i := hi
      have : IsImmersion g := hg
      infer_instance⟩
  refine IsZariskiLocalAtTarget.of_range_subset_iSup (P := @IsImmersion) U ?_ fun y => ?_
  · rintro _ ⟨y, rfl⟩
    exact (le_iSup U y : U y ≤ ⨆ i, U i) (hyU y)
  · have := hU y
    infer_instance

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaImmersionTorusExtensionProjective

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.ThetaImm

open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs

theorem isUnit_resG_of_le {X : Scheme.{0}} {U V : X.Opens} (r : Γ(X, U)) (h : V ≤ X.basicOpen r) :
    IsUnit (resG X (h.trans (X.basicOpen_le r)) r) := by
  have := (X.toRingedSpace.isUnit_res_basicOpen r).map (resG X h)
  exact (congrArg IsUnit (resG_resG (X.basicOpen_le r) h r)).mp this

theorem exists_immersion : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (Y : Ext D.toPre), ∃ (S : Finset D.toPre.X) (k₁ : ℕ), ∀ k ≥ k₁, ∃ (N : ℕ) (α : Fin (N + 1) → D.toPre.X) (b : ∀ i, D.toPre.SecB k (α i)) (τ : Fin (N + 1) → SecK D.toPre.P.L Y.q.left k) (hτ : ⨆ i, nonzeroLocus (τ i) = ⊤), (∀ i, α i ∈ S ∧ IsTermOf Y (b i) (τ i)) ∧ IsImmersion (GlobalTheory.ProjSpace.toProj Y.H.hom τ hτ) := by
  intro R _ _ _ hR D Y
  classical
  have : IsNoetherianRing R := hR.1.1
  obtain ⟨-, hqa, -, -, hterm⟩ := GlobalTheory.Mum.ext_smooth_affine_surj_terms R D.toPre Y
  obtain ⟨i, hi₁, hi₂, hi₃⟩ := GlobalTheory.Mum.ext_torus R D.toPre Y
  let bs := Module.Free.chooseBasis ℤ D.toPre.X
  choose k₀ hk₀ using fun c => GlobalTheory.Mum.exists_secB_generating R D.toPre (bs c)
  refine ⟨insert 0 (Finset.univ.image bs), max 4 (Finset.univ.sup k₀), fun k hk => ?_⟩
  obtain ⟨m, s, hs⟩ := GlobalTheory.Mum.WeightZero.exists_veryAmpleBy_secB_zero R D.toPre k (le_of_max_le_left hk)
  choose n bb hbb using fun c => hk₀ c k ((Finset.le_sup (Finset.mem_univ c)).trans (le_of_max_le_right hk))
  let J := Fin (m + 1) ⊕ Σ c, Fin (n c)
  let αJ : J → D.toPre.X := Sum.elim (fun _ => 0) (fun p => bs p.1)
  let bJ : ∀ j : J, D.toPre.SecB k (αJ j) := fun j => match j with
    | .inl a => s a
    | .inr p => bb p.1 p.2
  choose τJ hτJ using fun j : J => hterm k (αJ j) (bJ j)
  have hcard : Fintype.card J = (Fintype.card J - 1) + 1 :=
    (Nat.succ_pred_eq_of_pos (Fintype.card_pos_iff.2 ⟨.inl 0⟩)).symm
  let e : Fin (Fintype.card J - 1 + 1) ≃ J := (Fintype.equivFinOfCardEq hcard).symm
  have ht₀ : ∀ a, IsTermOf Y (s a) (τJ (e (e.symm (.inl a)))) := fun a => by
    rw [e.apply_symm_apply]; exact hτJ (.inl a)
  have htc : ∀ c l, IsTermOf Y (bb c l) (τJ (e (e.symm (.inr ⟨c, l⟩)))) := fun c l => by
    rw [e.apply_symm_apply]; exact hτJ (.inr ⟨c, l⟩)
  obtain ⟨hs₁, hsc⟩ := (veryAmpleBy_iff _ s).1 hs
  have hsi := (isClosedImmersion_toProj_iff _ s hs₁).1 hsc
  have hτ : ⨆ i, nonzeroLocus (τJ (e i)) = ⊤ := top_le_iff.1 fun y _ => by
    obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.1 (hs₁.ge (Set.mem_univ (Y.q.left y)))
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨e.symm (.inl a), ?_⟩
    rw [GlobalTheory.Mum.TermLocus.nonzeroLocus_eq R D.toPre Y k 0 _ _ (ht₀ a)]
    exact ha
  refine ⟨_, fun i => αJ (e i), fun i => bJ (e i), fun i => τJ (e i), hτ, fun i => ⟨?_, hτJ (e i)⟩, ?_⟩
  · show αJ (e i) ∈ _
    generalize e i = j
    rcases j with a | p
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem bs (Finset.mem_univ p.1))
  refine GlobalTheory.isImmersion_of_forall_affine_surjective_appLE _ _ _ fun y => ?_
  set φ := toProj Y.H.hom (fun i => τJ (e i)) hτ with hφ
  let q := Y.q.left
  obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.1 (hs₁.ge (Set.mem_univ (q y)))
  choose l hl using fun c => TopologicalSpace.Opens.mem_iSup.1 ((hbb c).ge (Set.mem_univ (q y)))

  let V₀ := nonzeroLocus (s a)
  have hV₀ : IsAffineOpen V₀ := (hsi a).1
  let O : D.toPre.P.A.left.Opens := V₀ ⊓ Finset.univ.inf fun c => nonzeroLocus (bb c (l c))
  have hyO : q y ∈ O := by
    refine ⟨ha, ?_⟩
    show q y ∈ ((Finset.univ.inf fun c => nonzeroLocus (bb c (l c)) : D.toPre.P.A.left.Opens) : Set _)
    rw [TopologicalSpace.Opens.coe_finset_inf]
    simp only [Finset.inf_eq_iInf, Finset.mem_univ, iInf_true, Set.iInf_eq_iInter, Set.mem_iInter, Function.comp_apply]
    exact fun c => hl c
  obtain ⟨f, hfO, hyf⟩ := hV₀.exists_basicOpen_le (V := O) ⟨q y, hyO⟩ ha
  let V := D.toPre.P.A.left.basicOpen f
  have hV : IsAffineOpen V := hV₀.basicOpen f
  have hVV₀ : V ≤ V₀ := D.toPre.P.A.left.basicOpen_le f
  have hVc : ∀ c, V ≤ nonzeroLocus (bb c (l c)) := fun c x hx => by
    have h := (hfO hx).2
    change x ∈ ((Finset.univ.inf fun c => nonzeroLocus (bb c (l c)) : D.toPre.P.A.left.Opens) : Set _) at h
    rw [TopologicalSpace.Opens.coe_finset_inf] at h
    simp only [Finset.inf_eq_iInf, Finset.mem_univ, iInf_true, Set.iInf_eq_iInter, Set.mem_iInter, Function.comp_apply] at h
    exact h c
  let i₀ := e.symm (.inl a)
  let iκ := fun c =>  e.symm (.inr ⟨c, l c⟩)
  have hloc₀ : nonzeroLocus (τJ (e i₀)) = q ⁻¹ᵁ V₀ := GlobalTheory.Mum.TermLocus.nonzeroLocus_eq R D.toPre Y k 0 _ _ (ht₀ a)
  have hlocc : ∀ c, nonzeroLocus (τJ (e (iκ c))) = q ⁻¹ᵁ nonzeroLocus (bb c (l c)) := fun c =>
    GlobalTheory.Mum.TermLocus.nonzeroLocus_eq R D.toPre Y k _ _ _ (htc c (l c))
  have hch₀ : φ ⁻¹ᵁ chart R _ i₀ = q ⁻¹ᵁ V₀ := (toProj_preimage_chart _ _ hτ i₀).trans hloc₀

  let base := (baseRingHom (PSpace.str R _) (chart R _ i₀)).hom
  let rat : Fin (m + 1) → Γ(PSpace R _, chart R _ i₀) := fun j => ratio R _ i₀ (e.symm (.inl j))
  have hW₀ : ∀ {W' : Y.H.left.Opens}, W' ≤ q ⁻¹ᵁ V₀ → W' ≤ φ ⁻¹ᵁ chart R _ i₀ := fun h => h.trans hch₀.ge
  have hpoly : ∀ (W' : Y.H.left.Opens) (hq : W' ≤ q ⁻¹ᵁ V₀) (P : MvPolynomial (Fin (m + 1)) R),
      (φ.appLE (chart R _ i₀) W' (hW₀ hq)).hom (MvPolynomial.eval₂Hom base rat P) =
      (q.appLE V₀ W' hq).hom (MvPolynomial.eval₂Hom (baseRingHom D.toPre.P.A.hom V₀).hom
        (fun j => secRatio (s a) (s j)) P) := by
    intro W' hq P
    have e1 : (φ.appLE (chart R _ i₀) W' (hW₀ hq)).hom.comp (MvPolynomial.eval₂Hom base rat) =
        (q.appLE V₀ W' hq).hom.comp (MvPolynomial.eval₂Hom (baseRingHom D.toPre.P.A.hom V₀).hom
          (fun j => secRatio (s a) (s j))) := by
      rw [MvPolynomial.comp_eval₂Hom, MvPolynomial.comp_eval₂Hom]
      congr 1
      · rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, baseRingHom_appLE, baseRingHom_appLE, toProj_str]
        exact congrArg (fun g => (baseRingHom g W').hom) (Over.w Y.q).symm
      · funext j
        show pullRatio φ W' i₀ _ _ = _
        rw [pullRatio_toProj_on]
        exact (GlobalTheory.Mum.secRatio_isTermOf_zero R D.toPre Y k (s a) (s j) _ _ (ht₀ a) (ht₀ j) W' hq _).symm
    exact RingHom.congr_fun e1 P
  let W := q ⁻¹ᵁ V
  have hWV₀ : W ≤ q ⁻¹ᵁ V₀ := q.preimage_mono hVV₀
  obtain ⟨p, hp⟩ := (hsi a).2 f
  let F₀ := MvPolynomial.eval₂Hom base rat p
  let G := F₀ * ∏ c, ratio R _ i₀ (iκ c)
  let U := (PSpace R _).basicOpen G
  have hU : IsAffineOpen U := (isAffineOpen_chart R _ i₀).basicOpen G
  have hUc : U ≤ chart R _ i₀ := (PSpace R _).basicOpen_le G
  have hF : ∀ (W' : Y.H.left.Opens) (hq : W' ≤ q ⁻¹ᵁ V₀),
      (φ.appLE (chart R _ i₀) W' (hW₀ hq)).hom F₀ = (q.appLE V₀ W' hq).hom f := fun W' hq => by
    rw [hpoly W' hq p, hp]
  have hUW : φ ⁻¹ᵁ U ≤ W := by
    intro x hx
    have hx₀ : x ∈ q ⁻¹ᵁ V₀ := hch₀.le (φ.preimage_mono hUc hx)
    have h1 : x ∈ Y.H.left.basicOpen ((φ.appLE (chart R _ i₀) (q ⁻¹ᵁ V₀) (hW₀ le_rfl)).hom G) := by
      rw [Scheme.basicOpen_appLE]; exact ⟨hx₀, hx⟩
    rw [map_mul, Scheme.basicOpen_mul, hF _ le_rfl, Scheme.basicOpen_appLE] at h1
    exact h1.1.2
  have hWU : W ≤ φ ⁻¹ᵁ U := by
    intro x hx
    have hx₀ : x ∈ q ⁻¹ᵁ V₀ := hWV₀ hx
    have h1 : x ∈ Y.H.left.basicOpen ((φ.appLE (chart R _ i₀) (q ⁻¹ᵁ V₀) (hW₀ le_rfl)).hom G) := by
      rw [map_mul, Scheme.basicOpen_mul, hF _ le_rfl, Scheme.basicOpen_appLE, map_prod]
      refine ⟨⟨hx₀, hx⟩, ?_⟩
      refine Finset.prod_induction _ (fun r => x ∈ Y.H.left.basicOpen r)
        (fun r r' h h' => by rw [Scheme.basicOpen_mul]; exact ⟨h, h'⟩)
        (by rw [Scheme.basicOpen_of_isUnit _ isUnit_one]; trivial) fun c _ => ?_
      show x ∈ Y.H.left.basicOpen (pullRatio φ _ i₀ _ (iκ c))
      rw [basicOpen_pullRatio, toProj_preimage_chart]
      refine ⟨hx₀, ?_⟩
      show x ∈ nonzeroLocus (τJ (e (iκ c)))
      rw [hlocc c]
      exact hVc c hx
    rw [Scheme.basicOpen_appLE] at h1
    exact h1.2
  haveI := hqa
  refine ⟨U, W, hWU, hU, hWU hyf, hUW, hV.preimage q, ?_⟩

  let S := (φ.appLE U W hWU).hom.range
  have hS_chart : ∀ r : Γ(PSpace R _, chart R _ i₀), (φ.appLE (chart R _ i₀) W (hW₀ hWV₀)).hom r ∈ S :=
    fun r => ⟨resG _ hUc r, appLE_resG φ hUc hWU r⟩
  have hS_unit : ∀ r : Γ(PSpace R _, chart R _ i₀), U ≤ (PSpace R _).basicOpen r →
      ∃ w ∈ S, (φ.appLE (chart R _ i₀) W (hW₀ hWV₀)).hom r * w = 1 := by
    intro r hr
    obtain ⟨v, hv⟩ := isUnit_resG_of_le r hr
    refine ⟨(φ.appLE U W hWU).hom ↑v⁻¹, ⟨_, rfl⟩, ?_⟩
    rw [← appLE_resG φ hUc hWU r, ← map_mul]
    have : resG _ hUc r = ↑v := hv.symm
    rw [this, Units.mul_inv, map_one]
  have hUF : U ≤ (PSpace R _).basicOpen F₀ := fun x hx => by
    have := hx
    change x ∈ (PSpace R _).basicOpen G at this
    rw [Scheme.basicOpen_mul] at this
    exact this.1
  have hUr : ∀ c, U ≤ (PSpace R _).basicOpen (ratio R _ i₀ (iκ c)) := fun c x hx => by
    have := hx
    change x ∈ (PSpace R _).basicOpen G at this
    rw [Scheme.basicOpen_mul, ← Finset.mul_prod_erase _ _ (Finset.mem_univ c), Scheme.basicOpen_mul] at this
    exact this.2.1
  have hS_q : ∀ x : Γ(D.toPre.P.A.left, V₀), (q.appLE V₀ W hWV₀).hom x ∈ S := fun x => by
    obtain ⟨P, rfl⟩ := (hsi a).2 x
    rw [← hpoly W hWV₀ P]
    exact hS_chart _
  have hWτ₀ : W ≤ nonzeroLocus (τJ (e i₀)) := hWV₀.trans hloc₀.ge
  have hWb : ∀ c, W ≤ Y.H.left.basicOpen (secRatio (τJ (e i₀)) (τJ (e (iκ c)))) := fun c x hx => by
    rw [basicOpen_secRatio]
    refine ⟨hWτ₀ hx, ?_⟩
    rw [hlocc c]
    exact hVc c hx
  let u : _ → Γ(Y.H.left, W)ˣ := fun c => (isUnit_resG_of_le _ (hWb c)).unit
  have hu : ∀ c, (u c).val = resG _ hWτ₀ (secRatio (τJ (e i₀)) (τJ (e (iκ c)))) := fun c =>
    (isUnit_resG_of_le _ (hWb c)).unit_spec
  have hupr : ∀ c, (u c).val = (φ.appLE (chart R _ i₀) W (hW₀ hWV₀)).hom (ratio R _ i₀ (iκ c)) := fun c => by
    rw [hu c]
    exact (pullRatio_toProj_on _ _ hτ i₀ (iκ c) (hW₀ hWV₀)).symm
  have hSt : S = ⊤ := by
    refine GlobalTheory.Mum.subring_eq_top_of_weight_units R D.toPre Y i hi₁ hi₂ bs V hV u (fun c => ?_) S (fun c => ?_) (fun c => ?_)
    · rw [hu c]
      exact (GlobalTheory.Mum.TermWeight.isWt_secRatio R D.toPre Y i hi₃ hi₂ k (bs c) (s a) (bb c (l c)) _ _ (ht₀ a) (htc c (l c))).res hWτ₀
    · have := hV₀.isLocalization_basicOpen f
      obtain ⟨⟨a', _, n', rfl⟩, ha'⟩ := IsLocalization.surj (Submonoid.powers f) c
      have ha'' : c * resG _ hVV₀ (f ^ n') = resG _ hVV₀ a' := ha'
      have happ : ∀ x : Γ(D.toPre.P.A.left, V₀), (q.app V).hom (resG _ hVV₀ x) = (q.appLE V₀ W hWV₀).hom x := fun x => by
        rw [Scheme.Hom.app_eq_appLE]
        exact appLE_resG q hVV₀ le_rfl x
      obtain ⟨w, hw, hfw⟩ := hS_unit F₀ hUF
      rw [hF W hWV₀] at hfw
      have key := congrArg (q.app V).hom ha''
      rw [map_mul, happ, happ, map_pow] at key
      have : (q.app V).hom c = (q.appLE V₀ W hWV₀).hom a' * w ^ n' := by
        rw [← key, _root_.mul_assoc, ← mul_pow, hfw, one_pow, _root_.mul_one]
      rw [this]
      exact S.mul_mem (hS_q a') (S.pow_mem hw n')
    · refine ⟨(hupr c).symm ▸ hS_chart _, ?_⟩
      obtain ⟨w, hw, hrw⟩ := hS_unit _ (hUr c)
      rw [← hupr c] at hrw
      rw [Units.mul_eq_one_iff_inv_eq.1 hrw]
      exact hw
  intro x
  have hx : x ∈ S := hSt ▸ Subring.mem_top x
  exact hx

end GlobalTheory.Mum.ThetaImm
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaImmersionTorusExtensionProjectiveStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_theta_immersion_torus_extension_projective : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (Y : Ext D.toPre), ∃ (S : Finset D.toPre.X) (k₁ : ℕ), ∀ k ≥ k₁, ∃ (N : ℕ) (α : Fin (N + 1) → D.toPre.X) (b : ∀ i, D.toPre.SecB k (α i)) (τ : Fin (N + 1) → SecK D.toPre.P.L Y.q.left k) (hτ : ⨆ i, nonzeroLocus (τ i) = ⊤), (∀ i, α i ∈ S ∧ IsTermOf Y (b i) (τ i)) ∧ IsImmersion (GlobalTheory.ProjSpace.toProj Y.H.hom τ hτ) := by
  first | exact @GlobalTheory.Mum.ThetaImm.exists_immersion | exact GlobalTheory.Mum.ThetaImm.exists_immersion | (intros; apply GlobalTheory.Mum.ThetaImm.exists_immersion <;> assumption)
end
end
