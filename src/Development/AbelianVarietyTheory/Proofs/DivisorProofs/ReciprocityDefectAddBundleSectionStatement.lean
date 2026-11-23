module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoheightEqOneIffClosureDimProjectiveStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogNormSectionIntegrableMixedChernProjectiveStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernFormFiniteIntegrablePointClosureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernFormSignedPartMeasureComplOpenGenericPStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernIntegralAdditiveInFactorStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEffectivePicClassAddIntegral
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import Mathlib.AlgebraicGeometry.QuasiAffine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorProductSectionsZerosMultiplicitiesNorms

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Mix

theorem nonzeroLocus_prodSec {X : Scheme.{0}} {A B : LB X} (s : A.Sec) (t : B.Sec) :
    nonzeroLocus (EffBound.tensSec s t) = nonzeroLocus s ⊓ nonzeroLocus t := by
  have e (c : A.ι × B.ι) : X.basicOpen ((EffBound.tensSec s t).f c) =
      (A.U c.1 ⊓ B.U c.2) ⊓ X.basicOpen (s.f c.1) ⊓ ((A.U c.1 ⊓ B.U c.2) ⊓ X.basicOpen (t.f c.2)) :=
    (X.basicOpen_mul _ _).trans (congrArg₂ (· ⊓ ·) (X.basicOpen_res _ _) (X.basicOpen_res _ _))
  refine le_antisymm (iSup_le fun c => (e c).le.trans (inf_le_inf
    (inf_le_right.trans (le_iSup (fun i => X.basicOpen (s.f i)) c.1))
    (inf_le_right.trans (le_iSup (fun i => X.basicOpen (t.f i)) c.2)))) fun x hx => ?_
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 hx.1
  obtain ⟨j, hj⟩ := Opens.mem_iSup.1 hx.2
  have h : x ∈ A.U i ⊓ B.U j := ⟨X.basicOpen_le _ hi, X.basicOpen_le _ hj⟩
  exact Opens.mem_iSup.2 ⟨(i, j), (e (i, j)).ge ⟨⟨h, hi⟩, h, hj⟩⟩

theorem secVal_prodSec {k : Type} [CommRing k] {X : Scheme.{0}} (p : X ⟶ Sp k) (σ : k →+* ℂ) {A B : LB X}
    (s : A.Sec) (t : B.Sec) :
    secVal p σ (EffBound.tensSec s t) = secTens (secVal p σ s) (secVal p σ t) := by
  funext c y
  by_cases h : y ∈ ptsIn p σ (A.U c.1 ⊓ B.U c.2)
  · exact (ev_mul _ _ y).trans (congrArg₂ (· * ·) (ev_res inf_le_left h _) (ev_res inf_le_right h _))
  · exact (ev_of_notMem h _).trans ((secTens_mem (secVal_mem s) (secVal_mem t)).2 c y h).symm

theorem mult_prodSec {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] {A B : LB X} (hA : A.IsLB)
    (hB : B.IsLB) (hAB : (tens A B).IsLB) (s : A.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (t : B.Sec)
    (ht : genericPoint X ∈ nonzeroLocus t) (h : genericPoint X ∈ nonzeroLocus (EffBound.tensSec s t)) (z : X) :
    (divOfSec hAB _ h).mult z = (divOfSec hA s hs).mult z + (divOfSec hB t ht).mult z := by
  obtain ⟨i, hi⟩ := Geo.Tor.exists_chart hA z
  obtain ⟨j, hj⟩ := Geo.Tor.exists_chart hB z
  have hij : z ∈ (tens A B).U (i, j) := ⟨hi, hj⟩
  rw [((presents_divOfRatSec hAB _).isEqn (i, j) z hij).mult_eq,
    ((presents_divOfRatSec hA _).isEqn i z hi).mult_eq, ((presents_divOfRatSec hB _).isEqn j z hj).mult_eq,
    val_ratOfSec (gen_mem hij), val_ratOfSec (gen_mem hi), val_ratOfSec (gen_mem hj),
    ← Scheme.ord_mul (fnOf_sec_ne_zero hs (gen_mem hi)) (fnOf_sec_ne_zero ht (gen_mem hj))]
  exact congrArg (Scheme.ord · z) ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (fnOf_resG inf_le_left _ _) (fnOf_resG inf_le_right _ _)))

theorem exists_sec_tens : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp k) (σ : k →+* ℂ) (M A : MLine p σ) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (a : A.B.Sec) (ha : genericPoint X ∈ nonzeroLocus a), ∃ (s₁ : (M.tens A).B.Sec) (h₁ : genericPoint X ∈ nonzeroLocus s₁), nonzeroLocus s₁ = nonzeroLocus s ⊓ nonzeroLocus a ∧ (∀ z, (divOfSec (M.tens A).φ.isLB s₁ h₁).mult z = (divOfSec M.φ.isLB s hs).mult z + (divOfSec A.φ.isLB a ha).mult z) ∧ ∀ y ∈ ptsIn p σ (nonzeroLocus s₁), (M.tens A).logSec s₁ y = M.logSec s y + A.logSec a y := by
  intro k _ X _ _ p σ M A s hs a ha
  have e := nonzeroLocus_prodSec s a
  refine ⟨EffBound.tensSec s a, e.ge ⟨hs, ha⟩, e, mult_prodSec _ _ _ s hs a ha _, fun y hy => ?_⟩
  have hy' : y ∈ ptsIn p σ (nonzeroLocus s ⊓ nonzeroLocus a) := ptsIn_mono e.le hy
  have h0 (N : MLine p σ) (u : N.B.Sec) (hu : y ∈ ptsIn p σ (nonzeroLocus u)) : N.φ.nsq (secVal p σ u) y ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (norm_ne_zero_iff.2 ((secVal_ne_zero_iff u (mem_pick _ y)).2 hu)))
      (Real.exp_ne_zero _)
  have h : (M.φ.tens A.φ).nsq (secVal p σ (EffBound.tensSec s a)) y =
      M.φ.nsq (secVal p σ s) y * A.φ.nsq (secVal p σ a) y := by
    rw [secVal_prodSec]
    exact Weight.nsq_tens _ _ (secVal_mem s) (secVal_mem a) y
  refine (congrArg (Real.log · / 2) h).trans ?_
  rw [Real.log_mul (h0 M s (mem_ptsIn_inf.1 hy').1) (h0 A a (mem_ptsIn_inf.1 hy').2), add_div]
  rfl

end GlobalTheory.Mix
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorProductSectionsZerosMultiplicitiesNormsStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

theorem _root_.GlobalTheory.T.tensor_product_sections_zeros_multiplicities_norms : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp k) (σ : k →+* ℂ) (M A : MLine p σ) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (a : A.B.Sec) (ha : genericPoint X ∈ nonzeroLocus a), ∃ (s₁ : (M.tens A).B.Sec) (h₁ : genericPoint X ∈ nonzeroLocus s₁), nonzeroLocus s₁ = nonzeroLocus s ⊓ nonzeroLocus a ∧ (∀ z, (divOfSec (M.tens A).φ.isLB s₁ h₁).mult z = (divOfSec M.φ.isLB s hs).mult z + (divOfSec A.φ.isLB a ha).mult z) ∧ ∀ y ∈ ptsIn p σ (nonzeroLocus s₁), (M.tens A).logSec s₁ y = M.logSec s y + A.logSec a y := by
  first | exact @GlobalTheory.Mix.exists_sec_tens | exact GlobalTheory.Mix.exists_sec_tens | (intros; apply GlobalTheory.Mix.exists_sec_tens <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReciprocityDefectAddBundleSection

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DefectAdd

theorem compactSpace_of_projOver {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R}
    (h : IsProjOver f) : CompactSpace X := by
  obtain ⟨m, i, hi, rfl⟩ := h
  have := isProper_str R m
  have : IsProper (i ≫ PSpace.str R m) := inferInstance
  exact QuasiCompact.compactSpace_of_compactSpace (i ≫ PSpace.str R m)

theorem int_eq_add_of_ae {k : Type} [CommRing k] {Y : Scheme.{0}} {q : Y ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}
    (L : Fin D → MLine q σ) {f g h : CxPts q σ → ℝ} (hf : Intg L f) (hg : Intg L g)
    (hh : ∀ ε : ℤˣ, ∀ᵐ y ∂part L ε, h y = f y + g y) :
    Mix.int L h = Mix.int L f + Mix.int L g := by
  simp only [Mix.int]
  rw [integral_congr_ae (hh 1), integral_congr_ae (hh (-1)), integral_add hf.1 hg.1, integral_add hf.2 hg.2]
  ring

theorem defect_add : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (e : ℕ), IsProjOver p → topologicalKrullDim X = (e + 1 : ℕ) → ∀ (L : Fin e → MLine p σ) (M A N : MLine p σ) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (a : A.B.Sec) (ha : genericPoint X ∈ nonzeroLocus a) (t : N.B.Sec) (ht : genericPoint X ∈ nonzeroLocus t), (∀ z : X, Order.coheight z = 1 → z ∈ nonzeroLocus s ⊓ nonzeroLocus a ∨ z ∈ nonzeroLocus t) → ∃ (s₁ : (M.tens A).B.Sec) (h₁ : genericPoint X ∈ nonzeroLocus s₁), nonzeroLocus s₁ = nonzeroLocus s ⊓ nonzeroLocus a ∧ side N L ((M.tens A).logSec s₁) (N.logSec t) (divOfSec (M.tens A).φ.isLB s₁ h₁) - side (M.tens A) L (N.logSec t) ((M.tens A).logSec s₁) (divOfSec N.φ.isLB t ht) = (side N L (M.logSec s) (N.logSec t) (divOfSec M.φ.isLB s hs) - side M L (N.logSec t) (M.logSec s) (divOfSec N.φ.isLB t ht)) + (side N L (A.logSec a) (N.logSec t) (divOfSec A.φ.isLB a ha) - side A L (N.logSec t) (A.logSec a) (divOfSec N.φ.isLB t ht)) := by
  intro hP F _ X _ _ p σ e hproj hdim L M A N s hs a ha t ht hcod
  obtain ⟨s₁, h₁, hloc, hmult, hlog⟩ := GlobalTheory.T.tensor_product_sections_zeros_multiplicities_norms F X p σ M A s hs a ha
  refine ⟨s₁, h₁, hloc, ?_⟩
  have hσ : Function.Injective σ := σ.injective
  haveI : CompactSpace X := compactSpace_of_projOver hproj
  have iM := GlobalTheory.T.log_norm_section_integrable_mixedChern_projective hP F X p σ (e + 1) hproj hdim (Fin.cons N L) M s hs
  have iA := GlobalTheory.T.log_norm_section_integrable_mixedChern_projective hP F X p σ (e + 1) hproj hdim (Fin.cons N L) A a ha
  have iMh := GlobalTheory.T.log_norm_section_integrable_mixedChern_projective hP F X p σ (e + 1) hproj hdim (Fin.cons M L) N t ht
  have iAh := GlobalTheory.T.log_norm_section_integrable_mixedChern_projective hP F X p σ (e + 1) hproj hdim (Fin.cons A L) N t ht
  have e1 : Mix.int (Fin.cons N L : Fin (e + 1) → MLine p σ) ((M.tens A).logSec s₁) =
      Mix.int (Fin.cons N L : Fin (e + 1) → MLine p σ) (M.logSec s) +
        Mix.int (Fin.cons N L : Fin (e + 1) → MLine p σ) (A.logSec a) := by
    refine int_eq_add_of_ae _ iM iA fun ε => ?_
    have h0 := GlobalTheory.T.mixedChernFormSignedPartMeasure_compl_open_genericPoint_eq_zero F X p σ hσ hproj (e + 1) (Fin.cons N L) ε (nonzeroLocus s₁) h₁
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with y hy
    exact hlog y (by simpa using hy)
  have e2 : Mix.int (Fin.cons (M.tens A) L : Fin (e + 1) → MLine p σ) (N.logSec t) =
      Mix.int (Fin.cons M L : Fin (e + 1) → MLine p σ) (N.logSec t) +
        Mix.int (Fin.cons A L : Fin (e + 1) → MLine p σ) (N.logSec t) := by
    have key := GlobalTheory.T.mixedChernIntegral_additive_in_factor F X p σ hproj (e + 1) (Fin.cons M L) 0 M A (N.logSec t)
      (by simpa only [Fin.update_cons_zero] using iMh) (by simpa only [Fin.update_cons_zero] using iAh)
    simpa only [Fin.update_cons_zero] using key.2
  have e3 : ∑ᶠ z, ((divOfSec (M.tens A).φ.isLB s₁ h₁).mult z : ℝ) * cycInt L (N.logSec t) z =
      ∑ᶠ z, ((divOfSec M.φ.isLB s hs).mult z : ℝ) * cycInt L (N.logSec t) z +
        ∑ᶠ z, ((divOfSec A.φ.isLB a ha).mult z : ℝ) * cycInt L (N.logSec t) z := by
    rw [← finsum_add_distrib]
    · refine finsum_congr fun z => ?_
      rw [hmult z]
      push_cast
      ring
    · exact (divOfSec M.φ.isLB s hs).finite_support_mult.subset fun z hz h0 => hz (by simp [h0])
    · exact (divOfSec A.φ.isLB a ha).finite_support_mult.subset fun z hz h0 => hz (by simp [h0])
  have e4 : ∑ᶠ z, ((divOfSec N.φ.isLB t ht).mult z : ℝ) * cycInt L ((M.tens A).logSec s₁) z =
      ∑ᶠ z, ((divOfSec N.φ.isLB t ht).mult z : ℝ) * cycInt L (M.logSec s) z +
        ∑ᶠ z, ((divOfSec N.φ.isLB t ht).mult z : ℝ) * cycInt L (A.logSec a) z := by
    rw [← finsum_add_distrib]
    · refine finsum_congr fun z => ?_
      by_cases hz : (divOfSec N.φ.isLB t ht).mult z = 0
      · simp [hz]
      · rw [← mul_add]
        congr 1
        have hco := CartierDiv.coheight_eq_one_of_mult_ne_zero hz
        have hzt : z ∉ nonzeroLocus t := fun h =>
          (notMem_supp_divOfSec.2 h) (CartierDiv.mem_supp_of_mult_ne_zero hz)
        have hz1 : z ∈ nonzeroLocus s ⊓ nonzeroLocus a := (hcod z hco).resolve_right hzt
        have hz1' := TopologicalSpace.Opens.mem_inf.1 hz1
        have hzs₁ : z ∈ nonzeroLocus s₁ := hloc ▸ hz1
        have hdimz := (GlobalTheory.T.coheight_eq_one_iff_closure_dim_projective F X p e hproj hdim z).1 hco
        obtain ⟨-, -, hnull, hint⟩ := GlobalTheory.T.mixedChernForm_finite_integrable_pointClosure hP F X p σ hproj e L z hdimz
        refine int_eq_add_of_ae _ (hint M s hz1'.1) (hint A a hz1'.2) fun ε => ?_
        filter_upwards [measure_eq_zero_iff_ae_notMem.1 (hnull _ hzs₁ ε)] with y hy
        exact hlog _ (by simpa using hy)
    · exact (divOfSec N.φ.isLB t ht).finite_support_mult.subset fun z hz h0 => hz (by simp [h0])
    · exact (divOfSec N.φ.isLB t ht).finite_support_mult.subset fun z hz h0 => hz (by simp [h0])
  simp only [side]
  rw [e1, e2, e3, e4]
  ring

end GlobalTheory.DefectAdd
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReciprocityDefectAddBundleSectionStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

theorem _root_.GlobalTheory.T.reciprocityDefect_add_bundleSection : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (e : ℕ), IsProjOver p → topologicalKrullDim X = (e + 1 : ℕ) → ∀ (L : Fin e → MLine p σ) (M A N : MLine p σ) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (a : A.B.Sec) (ha : genericPoint X ∈ nonzeroLocus a) (t : N.B.Sec) (ht : genericPoint X ∈ nonzeroLocus t), (∀ z : X, Order.coheight z = 1 → z ∈ nonzeroLocus s ⊓ nonzeroLocus a ∨ z ∈ nonzeroLocus t) → ∃ (s₁ : (M.tens A).B.Sec) (h₁ : genericPoint X ∈ nonzeroLocus s₁), nonzeroLocus s₁ = nonzeroLocus s ⊓ nonzeroLocus a ∧ side N L ((M.tens A).logSec s₁) (N.logSec t) (divOfSec (M.tens A).φ.isLB s₁ h₁) - side (M.tens A) L (N.logSec t) ((M.tens A).logSec s₁) (divOfSec N.φ.isLB t ht) = (side N L (M.logSec s) (N.logSec t) (divOfSec M.φ.isLB s hs) - side M L (N.logSec t) (M.logSec s) (divOfSec N.φ.isLB t ht)) + (side N L (A.logSec a) (N.logSec t) (divOfSec A.φ.isLB a ha) - side A L (N.logSec t) (A.logSec a) (divOfSec N.φ.isLB t ht)) := by
  first | exact @GlobalTheory.DefectAdd.defect_add | exact GlobalTheory.DefectAdd.defect_add | (intros; apply GlobalTheory.DefectAdd.defect_add <;> assumption)
end
end
