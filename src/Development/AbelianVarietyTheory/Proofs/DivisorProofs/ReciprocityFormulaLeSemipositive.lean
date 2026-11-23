module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogNormSectionIntegrableMixedChernProjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernFormSignedPartMeasureComplOpenGenericPStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernFormSignedPartMeasureEqOfIsometricProjStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Matrix.Hermitian
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
import Mathlib.Tactic.Basify
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
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.CommFderivApply
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.DifferentiableAtChart
public import ReciprocityTheory.AnalyticForms.MaIntEmpty
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernIntegralAdditiveInFactorStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernMeasureFiniteIntegrableProjectiveStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogResolutionProjectiveOfPrincipalisationStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernIntegralEqMongeAmpereIntegralCompactStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedIntegralPullbackGenericallyFiniteStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothWeightedLineBundleIsometryCalculusStatement
public import ReciprocityTheory.AnalyticForms.PotentialTheory.IntegrableOnTargetOfTsupport
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PotentialContDiffAt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareLelongFormulaSectionProjectiveStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiPosAddLogNormSqSectionAddPosStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothWeightedLineBundleIsometryCalculusStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothWeightedLineBundleLogSectionNormPropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoRegularisedLogNormMixedMeasureDivisorsStatement
import Mathlib.Algebra.Order.Star.Real

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernFormSignedPartMeasureNegEqZeroSemiPosi

section

@[expose] public section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.Mix

section
open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open scoped ComplexOrder ComplexConjugate

theorem cHess_posSemidef_of_levi {n : ℕ} {f : ReciprocityTheory.L2DbarEstimates.V n → ℝ} {x : ReciprocityTheory.L2DbarEstimates.V n} (hf : ContDiffAt ℝ 2 f x)
    (hL : ∀ ξ : Fin n → ℂ, 0 ≤ (leviV n (fun v => ((f v : ℝ) : ℂ)) x ξ).re) :
    (cHess n (fun v => ((f v : ℝ) : ℂ)) x).PosSemidef := by
  classical
  set g : ReciprocityTheory.L2DbarEstimates.V n → ℂ := fun v => ((f v : ℝ) : ℂ) with hg
  have hg2 : ContDiffAt ℝ 2 g x := Complex.ofRealCLM.contDiff.contDiffAt.comp x hf
  have hgc : (fun w => conj (g w)) = g := funext fun w => by simp [g]
  have hH : (cHess n g x).IsHermitian := by
    ext j k
    simp only [Matrix.conjTranspose_apply, cHess, Matrix.of_apply]
    show conj (wd n k (wdb n j g) x) = wd n j (wdb n k g) x
    have h1 : (fun w => conj (wdb n j g w)) = wd n j g := by
      funext w
      rw [← ChartWirtingerDerivatives.wd_conj' n j g w, hgc]
    rw [← ChartWirtingerDerivatives.wdb_conj' n k (wdb n j g) x, h1, comm_wd_wdb g x hg2 j k]
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH fun y => ?_
  have hre : dotProduct (star y) (Matrix.mulVec (cHess n g x) y) = leviV n g x (fun k => conj (y k)) := by
    simp only [dotProduct, Matrix.mulVec, leviV, cHess, Matrix.of_apply, Finset.mul_sum,
      Pi.star_apply, Complex.conj_conj]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    simp only [Complex.star_def]
    ring
  have him := hH.im_star_dotProduct_mulVec_self y
  refine Complex.le_def.2 ⟨?_, ?_⟩
  · rw [hre]; exact hL _
  · simpa using him.symm

theorem re_sum_perm_det_nonneg {D : ℕ} (A : Fin D → Matrix (Fin D) (Fin D) ℂ) (hA : ∀ i, (A i).PosSemidef) :
    0 ≤ (∑ τ : Equiv.Perm (Fin D), (Matrix.of fun j l => A (τ l) j l).det).re := by
  have h := (ReciprocityTheory.AnForm.A.mdisc_nonneg_of_posSemidef A hA).2
  have h0 : (D.factorial : ℂ) ≠ 0 := by exact_mod_cast D.factorial_ne_zero
  have e : (∑ τ : Equiv.Perm (Fin D), (Matrix.of fun j l => A (τ l) j l).det) =
      ((D.factorial : ℝ) : ℂ) * ReciprocityTheory.AnForm.mdisc A := by
    rw [ReciprocityTheory.AnForm.A.mdisc_eq_sum_perm, Complex.ofReal_natCast, ← mul_assoc, mul_one_div_cancel h0, one_mul]
  rw [e, Complex.re_ofReal_mul]
  exact mul_nonneg (Nat.cast_nonneg _) h

end

theorem dens_nonneg_of_semiPosReg {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}
    {L : Fin D → MLine p σ} (h : ∀ i, (L i).φ.SemiPosReg D) (c : AlgChart p σ D) {y : CxPts p σ}
    (hy : y ∈ c.e.source) : 0 ≤ dens L c y :=
  mul_nonneg (by positivity) (re_sum_perm_det_nonneg (fun i => c.hess (L i).φ (pick (L i).φ.isLB y) y) fun i =>
    cHess_posSemidef_of_levi ((L i).cInf.contDiffAt c hy (mem_pick _ y)) (h i _ c y ⟨hy, mem_pick _ y⟩))

theorem part_neg_eq_zero_of_semiPosReg : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) [SecondCountableTopology (CxPts p σ)] (D : ℕ) (L : Fin D → MLine p σ), (∀ i, (L i).φ.SemiPosReg D) → part L (-1) = 0 := by
  intro k _ X p σ _ D L h
  refine le_antisymm (iSup_le fun c => le_of_eq (Measure.measure_univ_eq_zero.1 ?_)) bot_le
  rw [chartMeas_apply _ _ MeasurableSet.univ, inter_univ, c.e.image_source_eq_target]
  refine setLIntegral_eq_zero c.e.open_target.measurableSet fun v hv => ?_
  have := dens_nonneg_of_semiPosReg h c (c.e.map_target hv)
  exact ENNReal.ofReal_eq_zero.2 (by simpa using this)

end GlobalTheory.Mix
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernFormSignedPartMeasureNegEqZeroSemiPosiStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

theorem _root_.GlobalTheory.T.mixedChernFormSignedPartMeasure_neg_eq_zero_semiPositive : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) [SecondCountableTopology (CxPts p σ)] (D : ℕ) (L : Fin D → MLine p σ), (∀ i, (L i).φ.SemiPosReg D) → part L (-1) = 0 := by
  first | exact @GlobalTheory.Mix.part_neg_eq_zero_of_semiPosReg | exact GlobalTheory.Mix.part_neg_eq_zero_of_semiPosReg | (intros; apply GlobalTheory.Mix.part_neg_eq_zero_of_semiPosReg <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedIntegralDdcPairingSymmProjective

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.Mix

theorem mInt_half {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X)
    (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i)) (g : X → ℝ) (hg : Continuous g) :
    mInt A Φ (fun x => g x / 2) = mInt A Φ g / 2 := by
  have h0 := mIntegrableCont A Φ hΦ (fun _ => 0) continuous_const
  have h1 := mIntLinear A Φ hΦ 1 (fun _ => 0) (fun _ => 0) h0 h0
  have h2 := mIntLinear A Φ hΦ (1 / 2) g (fun _ => 0) (mIntegrableCont A Φ hΦ g hg) h0
  have e1 : (fun x => 1 / 2 * g x + 0) = fun x => g x / 2 := funext fun x => by ring
  simp only [mul_zero, add_zero] at h1
  rw [e1] at h2
  linarith

theorem mInt_cons_ofFun_symm {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {e : ℕ}
    [CompactSpace (CxPts p σ)] [T2Space (CxPts p σ)] {A : FinHolAtlas (e + 1) (CxPts p σ)} (hA : IsAlgAtlas A)
    (L : Fin e → MLine p σ) (u v : CxPts p σ → ℝ) (hu : ∀ y, CInfAt u y) (hv : ∀ y, CInfAt v y) :
    mInt A (fun i => ((Fin.cons (MLine.ofFun u hu) L : Fin (e + 1) → MLine p σ) i).φ.locPot) v =
      mInt A (fun i => ((Fin.cons (MLine.ofFun v hv) L : Fin (e + 1) → MLine p σ) i).φ.locPot) u := by
  have hpot (N : MLine p σ) : IsPotential A N.φ.locPot :=
    ((Weight.isCInf_iff_isSmooth hA.anRead).1 N.cInf).isPotential hA
  have hsm (a : CxPts p σ → ℝ) (ha : ∀ y, CInfAt a y) : A.Smooth fun y => a y / 2 := fun j =>
    ((hA.smooth_iff hA.anRead).2 ((cInfAt_iff_smoothOn hA.anRead isOpen_univ).1 fun y _ => ha y) j).div_const 2
  have key (a b : CxPts p σ → ℝ) (ha : ∀ y, CInfAt a y) (hb : ∀ y, CInfAt b y) :
      mInt A (Fin.cons (LocPot.ofFun fun y => a y / 2) fun i => (L i).φ.locPot) (fun y => b y / 2) =
      mInt A (fun i => ((Fin.cons (MLine.ofFun a ha) L : Fin (e + 1) → MLine p σ) i).φ.locPot) b / 2 := by
    rw [← mInt_half A _ (fun i => hpot _) b (continuous_iff_continuousAt.2 fun y => (hb y).continuousAt)]
    refine SameForm.mInt_eq (fun i => ?_) _
    refine Fin.cases ?_ (fun j => ?_) i
    · exact fun _ _ _ => rfl
    · exact fun _ _ _ => rfl
  have h := byPartsSymm A _ _ (hsm v hv) (hsm u hu) (fun i => (L i).φ.locPot) fun i => hpot _
  rw [key u v hu hv, key v u hv hu] at h
  linarith

theorem int_cons_ofFun_symm : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (e : ℕ), IsProjOver p → topologicalKrullDim X = (e + 1 : ℕ) → ∀ (L : Fin e → MLine p σ) (u v : CxPts p σ → ℝ) (hu : ∀ y, CInfAt u y) (hv : ∀ y, CInfAt v y), Mix.int (Fin.cons (MLine.ofFun u hu) L : Fin (e + 1) → MLine p σ) v = Mix.int (Fin.cons (MLine.ofFun v hv) L : Fin (e + 1) → MLine p σ) u := by
  intro hP F _ X _ _ p σ e hproj hdim L u v hu hv
  haveI : CharZero F := RingHom.charZero σ
  obtain ⟨Y, hY, π, hsm, hprojY, -, hgen, hdeg, -⟩ :=
    GlobalTheory.T.exists_logResolution_projective_of_principalisation hP F X p (e + 1) hproj hdim ⊥
      (by rw [← SetLike.mem_coe, TopologicalSpace.Closeds.coe_bot]; exact Set.notMem_empty _)
  haveI := hsm
  haveI : CompactSpace (CxPts (π ≫ p) σ) := CxPts.compactSpace σ hprojY
  haveI : T2Space (CxPts (π ≫ p) σ) := CxPts.t2Space_cxPts_of_isProjOver σ hprojY
  haveI : SecondCountableTopology (CxPts (π ≫ p) σ) := CxPts.secondCountableTopology_of_isProjOver σ hprojY
  have hA : IsAlgAtlas (AnRead.all (π ≫ p) σ (e + 1)).finAtlas := AnRead.isAlgAtlas_finAtlas _
  have hiso := GlobalTheory.T.smoothWeightedLineBundle_isometry_calculus F X Y p (π ≫ p) σ π rfl
  have hisoY := GlobalTheory.T.smoothWeightedLineBundle_isometry_calculus F Y Y (π ≫ p) (π ≫ p) σ (𝟙 Y) (Category.id_comp _)
  have key (a b : CxPts p σ → ℝ) (ha : ∀ y, CInfAt a y) (hb : ∀ y, CInfAt b y) :
      Mix.int (Fin.cons (MLine.ofFun a ha) L : Fin (e + 1) → MLine p σ) b =
      mInt (AnRead.all (π ≫ p) σ (e + 1)).finAtlas (fun i => ((Fin.cons (MLine.ofFun (fun z => a (ptMap π rfl σ z))
        fun z => (ha _).pull π rfl) fun i => (L i).pull π rfl : Fin (e + 1) → MLine (π ≫ p) σ) i).φ.locPot)
        (fun z => b (ptMap π rfl σ z)) := by
    have hbc : Continuous b := continuous_iff_continuousAt.2 fun y => (hb y).continuousAt
    have hbc' : Continuous fun z : CxPts (π ≫ p) σ => b (ptMap π rfl σ z) :=
      continuous_iff_continuousAt.2 fun z => ((hb _).pull π rfl).continuousAt
    have h1 := (GlobalTheory.T.mixedIntegral_pullback_genericallyFinite F X Y p (π ≫ p) σ (e + 1) hproj hdim hprojY π rfl hgen
      (by rw [hdeg]; exact one_ne_zero) (Fin.cons (MLine.ofFun a ha) L) b hbc.measurable).2
    rw [hdeg, Nat.cast_one, one_mul] at h1
    have h2 := GlobalTheory.T.mixedChernFormSignedPartMeasure_eq_of_isometric_projOver F Y (π ≫ p) σ hprojY (e + 1)
      (fun i => ((Fin.cons (MLine.ofFun a ha) L : Fin (e + 1) → MLine p σ) i).pull π rfl)
      (Fin.cons (MLine.ofFun (fun z => a (ptMap π rfl σ z)) fun z => (ha _).pull π rfl) fun i => (L i).pull π rfl)
      (fun i => Fin.cases (hiso.2.2.2.1 a ha) (fun j => hisoY.1 _) i)
    have h3 := GlobalTheory.T.mixedChernIntegral_eq_mongeAmpereIntegral_compact F Y (π ≫ p) σ (e + 1) _ hA
      (Fin.cons (MLine.ofFun (fun z => a (ptMap π rfl σ z)) fun z => (ha _).pull π rfl) fun i => (L i).pull π rfl)
      _ hbc'.measurable
    rw [← h1, ← h3.2 (h3.1.2 (mIntegrableCont _ _
      (fun i => ((Weight.isCInf_iff_isSmooth hA.anRead).1 (MLine.cInf _)).isPotential hA) _ hbc'))]
    simp only [Mix.int, h2]
  rw [key u v hu hv, key v u hv hu]
  exact mInt_cons_ofFun_symm hA _ _ _ _ _

end GlobalTheory.Mix
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedIntegralDdcPairingSymmProjectiveStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

theorem _root_.GlobalTheory.T.mixedIntegral_ddc_pairing_symm_projective : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (e : ℕ), IsProjOver p → topologicalKrullDim X = (e + 1 : ℕ) → ∀ (L : Fin e → MLine p σ) (u v : CxPts p σ → ℝ) (hu : ∀ y, CInfAt u y) (hv : ∀ y, CInfAt v y), Mix.int (Fin.cons (MLine.ofFun u hu) L : Fin (e + 1) → MLine p σ) v = Mix.int (Fin.cons (MLine.ofFun v hv) L : Fin (e + 1) → MLine p σ) u := by
  first | exact @GlobalTheory.Mix.int_cons_ofFun_symm | exact GlobalTheory.Mix.int_cons_ofFun_symm | (intros; apply GlobalTheory.Mix.int_cons_ofFun_symm <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReciprocityFormulaLeSemipositive

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CycPair

theorem cInfAt_log_nsq_add : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (M : MLine p σ) (s : M.B.Sec) (δ : ℝ), 0 < δ → ∀ y, CInfAt (fun y => Real.log (M.φ.nsq (secVal p σ s) y + δ)) y := by
  intro k _ X p σ M s δ hδ y
  obtain ⟨W, ι, _, g, F, O, h₁, h₂, h₃, h₄, h₅⟩ := (GlobalTheory.T.smoothWeightedLineBundle_logSectionNorm_properties k X p σ M s).2.2.1 y
  refine ⟨W, ι, inferInstance, g, fun w => Real.log (F w + δ), O ∩ F ⁻¹' Set.Ioi (-δ), h₁,
    h₄.continuousOn.isOpen_inter_preimage h₂ isOpen_Ioi, ⟨h₃, ?_⟩, ?_, ?_⟩
  · have h0 := M.φ.nsq_nonneg (secVal p σ s) y
    rw [h₅.eq_of_nhds] at h0
    exact lt_of_lt_of_le (neg_neg_of_pos hδ) h0
  · refine ((h₄.mono Set.inter_subset_left).add contDiffOn_const).log fun w hw => ?_
    have : -δ < F w := hw.2
    linarith
  · filter_upwards [h₅] with z hz
    rw [hz]

theorem int_cons_addFn : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ), IsProjOver p → ∀ (e : ℕ) (L : Fin e → MLine p σ) (A : MLine p σ) (u : CxPts p σ → ℝ) (hu : ∀ y, CInfAt u y) (f : CxPts p σ → ℝ), Intg (Fin.cons A L : Fin (e + 1) → MLine p σ) f → Intg (Fin.cons (MLine.ofFun u hu) L : Fin (e + 1) → MLine p σ) f → Intg (Fin.cons (A.addFn u hu) L : Fin (e + 1) → MLine p σ) f ∧ Mix.int (Fin.cons (A.addFn u hu) L : Fin (e + 1) → MLine p σ) f = Mix.int (Fin.cons A L : Fin (e + 1) → MLine p σ) f + Mix.int (Fin.cons (MLine.ofFun u hu) L : Fin (e + 1) → MLine p σ) f := by
  intro k _ X p σ hp e L A u hu f hA hU
  have hc := GlobalTheory.T.smoothWeightedLineBundle_isometry_calculus k X X p p σ (𝟙 X) (Category.id_comp p)
  have hpart := GlobalTheory.T.mixedChernFormSignedPartMeasure_eq_of_isometric_projOver k X p σ hp (e + 1) (Fin.cons (A.addFn u hu) L)
    (Fin.cons (A.tens (MLine.ofFun u hu)) L) (Fin.cases (hc.2.2.2.2.1 A u hu) fun i => hc.1 (L i))
  have h := GlobalTheory.T.mixedChernIntegral_additive_in_factor k X p σ hp (e + 1) (Fin.cons A L) 0 A (MLine.ofFun u hu) f
  simp only [Fin.update_cons_zero] at h
  have h' := h hA hU
  rw [← h'.2]
  have h1 := h'.1
  simp only [Intg, Mix.int, hpart] at h1 ⊢
  exact ⟨h1, trivial⟩

theorem int_logSec_le : ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp F) (σ : F →+* ℂ), IsProjOver p → ∀ (D : ℕ) (L : Fin D → MLine p σ), (∀ i, (L i).φ.SemiPosReg D) → ∀ (M : MLine p σ) (s : M.B.Sec), genericPoint X ∈ nonzeroLocus s → ∀ δ : ℝ, 0 < δ → Intg L (M.logSec s) → Intg L (fun y => Real.log (M.φ.nsq (secVal p σ s) y + δ)) → Mix.int L (M.logSec s) ≤ Mix.int L (fun y => Real.log (M.φ.nsq (secVal p σ s) y + δ)) / 2 := by
  intro F _ X _ p σ hp D L hL M s hs δ hδ h₁ h₂
  haveI : SecondCountableTopology (CxPts p σ) := CxPts.secondCountableTopology_of_isProjOver σ hp
  have hneg := GlobalTheory.T.mixedChernFormSignedPartMeasure_neg_eq_zero_semiPositive F X p σ D L hL
  have hnull := GlobalTheory.T.mixedChernFormSignedPartMeasure_compl_open_genericPoint_eq_zero F X p σ σ.injective hp D L 1 _ hs
  have hpos := (GlobalTheory.T.smoothWeightedLineBundle_logSectionNorm_properties F X p σ M s).2.1
  simp only [Mix.int, hneg, integral_zero_measure, sub_zero]
  rw [← integral_div]
  refine integral_mono_ae h₁.1 (h₂.1.div_const 2) ?_
  have hae : ∀ᵐ y ∂part L 1, y ∈ ptsIn p σ (nonzeroLocus s) := hnull
  filter_upwards [hae] with y hy
  have h0 := (hpos y).2 hy
  have := Real.log_le_log h0 (le_add_of_nonneg_right hδ.le)
  simp only [MLine.logSec]
  linarith

theorem mem_of_mult_divOfSec_ne_zero {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] {A : LB X} (hA : A.IsLB) (s : A.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (U : X.Opens) (h : ∀ z : X, Order.coheight z = 1 → z ∈ nonzeroLocus s ∨ z ∈ U) (z : X) (hz : (divOfSec hA s hs).mult z ≠ 0) : z ∈ U :=
  (h z (CartierDiv.coheight_eq_one_of_mult_ne_zero hz)).resolve_left fun h' =>
    notMem_supp_divOfSec.2 h' (CartierDiv.mem_supp_of_mult_ne_zero hz)

theorem side_le : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (e : ℕ), IsProjOver p → topologicalKrullDim X = (e + 1 : ℕ) → ∀ (L : Fin e → MLine p σ) (M N : MLine p σ) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (t : N.B.Sec) (ht : genericPoint X ∈ nonzeroLocus t), (∀ z : X, Order.coheight z = 1 → z ∈ nonzeroLocus s ∨ z ∈ nonzeroLocus t) → (∀ i, (L i).φ.SemiPosReg (e + 1)) → N.φ.SemiPosReg (e + 1) → side N L (M.logSec s) (N.logSec t) (divOfSec M.φ.isLB s hs) ≤ side M L (N.logSec t) (M.logSec s) (divOfSec N.φ.isLB t ht) := by
  intro hP F _ X _ _ p σ e hproj hdim L M N s hs t ht hcod hL hN
  let δ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hδ : ∀ n, 0 < δ n := fun n => by positivity
  let v : ℕ → CxPts p σ → ℝ := fun n y => Real.log (N.φ.nsq (secVal p σ t) y + δ n)
  let u : ℕ → CxPts p σ → ℝ := fun m y => Real.log (M.φ.nsq (secVal p σ s) y + δ m)
  have hv : ∀ n y, CInfAt (v n) y := fun n => cInfAt_log_nsq_add F X p σ N t (δ n) (hδ n)
  have hu : ∀ m y, CInfAt (u m) y := fun m => cInfAt_log_nsq_add F X p σ M s (δ m) (hδ m)
  have cu : ∀ m, Continuous (u m) := fun m => continuous_iff_continuousAt.2 fun y => (hu m y).continuousAt
  have fin : ∀ (L' : Fin (e + 1) → MLine p σ) (f : CxPts p σ → ℝ), Continuous f → Intg L' f :=
    fun L' => (GlobalTheory.T.mixedChernMeasure_finite_integrable_projective hP F X p σ (e + 1) hproj hdim L').2
  have lint : ∀ L' : Fin (e + 1) → MLine p σ, Intg L' (M.logSec s) :=
    fun L' => GlobalTheory.T.log_norm_section_integrable_mixedChern_projective hP F X p σ (e + 1) hproj hdim L' M s hs
  have supS : ∀ z, (divOfSec M.φ.isLB s hs).mult z ≠ 0 → z ∈ nonzeroLocus t :=
    mem_of_mult_divOfSec_ne_zero M.φ.isLB s hs _ hcod
  have supT : ∀ z, (divOfSec N.φ.isLB t ht).mult z ≠ 0 → z ∈ nonzeroLocus s :=
    mem_of_mult_divOfSec_ne_zero N.φ.isLB t ht _ fun z hz => (hcod z hz).symm
  have key : ∀ m n, Mix.int (Fin.cons N L : Fin (e + 1) → MLine p σ) (M.logSec s)
      + Mix.int (Fin.cons (MLine.ofFun (v n) (hv n)) L : Fin (e + 1) → MLine p σ) (M.logSec s) ≤
      (Mix.int (Fin.cons N L : Fin (e + 1) → MLine p σ) (u m)
        + Mix.int (Fin.cons (MLine.ofFun (u m) (hu m)) L : Fin (e + 1) → MLine p σ) (v n)) / 2 := by
    intro m n
    obtain ⟨-, h1⟩ := int_cons_addFn F X p σ hproj e L N (v n) (hv n) (M.logSec s) (lint _) (lint _)
    obtain ⟨-, h2⟩ := int_cons_addFn F X p σ hproj e L N (v n) (hv n) (u m) (fin _ _ (cu m)) (fin _ _ (cu m))
    have hsp : ∀ i, ((Fin.cons (N.addFn (v n) (hv n)) L : Fin (e + 1) → MLine p σ) i).φ.SemiPosReg (e + 1) :=
      Fin.cases (GlobalTheory.T.semiPos_add_log_normSq_section_add_pos F X p σ (e + 1) N hN t (δ n) (hδ n)).2 hL
    have h3 := int_logSec_le F X p σ hproj (e + 1) _ hsp M s hs (δ m) (hδ m) (lint _) (fin _ _ (cu m))
    have h4 := GlobalTheory.T.mixedIntegral_ddc_pairing_symm_projective hP F X p σ e hproj hdim L (v n) (u m) (hv n) (hu m)
    rw [← h1]
    refine h3.trans (le_of_eq ?_)
    change Mix.int _ (u m) / 2 = _
    rw [h2, h4]
  have ps : ∀ n, 2 * Mix.int (Fin.cons (MLine.ofFun (v n) (hv n)) L : Fin (e + 1) → MLine p σ) (M.logSec s) =
      ∑ᶠ z, ((divOfSec M.φ.isLB s hs).mult z : ℝ) * cycInt L (v n) z
        - Mix.int (Fin.cons M L : Fin (e + 1) → MLine p σ) (v n) :=
    fun n => GlobalTheory.T.poincareLelong_formula_section_projective hP F X p σ e hproj hdim L M s hs (v n) (hv n)
  have pt : ∀ m, 2 * Mix.int (Fin.cons (MLine.ofFun (u m) (hu m)) L : Fin (e + 1) → MLine p σ) (N.logSec t) =
      ∑ᶠ z, ((divOfSec N.φ.isLB t ht).mult z : ℝ) * cycInt L (u m) z
        - Mix.int (Fin.cons N L : Fin (e + 1) → MLine p σ) (u m) :=
    fun m => GlobalTheory.T.poincareLelong_formula_section_projective hP F X p σ e hproj hdim L N t ht (u m) (hu m)
  have limT := GlobalTheory.T.tendsto_regularisedLogNorm_mixedMeasure_divisors hP F X p σ e hproj hdim N t
  have limS := GlobalTheory.T.tendsto_regularisedLogNorm_mixedMeasure_divisors hP F X p σ e hproj hdim M s
  have l1 : Tendsto (fun n => ∑ᶠ z, ((divOfSec M.φ.isLB s hs).mult z : ℝ) * cycInt L (v n) z) atTop
      (𝓝 (2 * ∑ᶠ z, ((divOfSec M.φ.isLB s hs).mult z : ℝ) * cycInt L (N.logSec t) z)) :=
    limT.2 L _ supS
  have l2 : Tendsto (fun n => Mix.int (Fin.cons M L : Fin (e + 1) → MLine p σ) (v n)) atTop
      (𝓝 (2 * Mix.int (Fin.cons M L : Fin (e + 1) → MLine p σ) (N.logSec t))) := limT.1 ht _
  have l3 : ∀ m, Tendsto (fun n => Mix.int (Fin.cons (MLine.ofFun (u m) (hu m)) L : Fin (e + 1) → MLine p σ) (v n))
      atTop (𝓝 (2 * Mix.int (Fin.cons (MLine.ofFun (u m) (hu m)) L : Fin (e + 1) → MLine p σ) (N.logSec t))) :=
    fun m => limT.1 ht _
  have l4 : Tendsto (fun m => ∑ᶠ z, ((divOfSec N.φ.isLB t ht).mult z : ℝ) * cycInt L (u m) z) atTop
      (𝓝 (2 * ∑ᶠ z, ((divOfSec N.φ.isLB t ht).mult z : ℝ) * cycInt L (M.logSec s) z)) :=
    limS.2 L _ supT
  have step : ∀ m, side N L (M.logSec s) (N.logSec t) (divOfSec M.φ.isLB s hs)
      - Mix.int (Fin.cons M L : Fin (e + 1) → MLine p σ) (N.logSec t) ≤
      (∑ᶠ z, ((divOfSec N.φ.isLB t ht).mult z : ℝ) * cycInt L (u m) z) / 2 := by
    intro m
    have lim1 : Tendsto (fun n => Mix.int (Fin.cons N L : Fin (e + 1) → MLine p σ) (M.logSec s)
        + Mix.int (Fin.cons (MLine.ofFun (v n) (hv n)) L : Fin (e + 1) → MLine p σ) (M.logSec s)) atTop
        (𝓝 (side N L (M.logSec s) (N.logSec t) (divOfSec M.φ.isLB s hs)
          - Mix.int (Fin.cons M L : Fin (e + 1) → MLine p σ) (N.logSec t))) := by
      have e1 : (fun n => Mix.int (Fin.cons N L : Fin (e + 1) → MLine p σ) (M.logSec s)
          + Mix.int (Fin.cons (MLine.ofFun (v n) (hv n)) L : Fin (e + 1) → MLine p σ) (M.logSec s)) =
          fun n => Mix.int (Fin.cons N L : Fin (e + 1) → MLine p σ) (M.logSec s)
            + (∑ᶠ z, ((divOfSec M.φ.isLB s hs).mult z : ℝ) * cycInt L (v n) z
              - Mix.int (Fin.cons M L : Fin (e + 1) → MLine p σ) (v n)) / 2 :=
        funext fun n => by rw [← ps n]; ring
      rw [e1]
      convert tendsto_const_nhds.add ((l1.sub l2).div_const 2) using 2
      simp only [side]
      ring
    have lim2 := (tendsto_const_nhds (x := Mix.int (Fin.cons N L : Fin (e + 1) → MLine p σ) (u m))).add (l3 m)
    have h := le_of_tendsto_of_tendsto' lim1 (lim2.div_const 2) (key m)
    have := pt m
    linarith
  have h := ge_of_tendsto' (l4.div_const 2) step
  simp only [side] at h ⊢
  linarith

end GlobalTheory.CycPair
end
end
end
