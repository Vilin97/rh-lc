module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoheightEqOneIffClosureDimProjectiveStatement
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratingSecsOfClsEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiPosFubiniStudyPowerAddSmoothFnStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothSemipositiveWeightOfGenerated
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocExt
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConjFsBasisOfUnitary
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
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
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.HoloSmooth
import ReciprocityTheory.L2DbarEstimates.LeviForms.EventuallyDifferentiableAtOfContDiffAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.RhGradFPfA
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemipositiveNonnegCombination
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothWeightsDifferBySmoothFunctionStatement
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecOfLeChart
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOfQuasiAffine
import Mathlib.Tactic.Basify
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratedBundlesReciprocitySemiPositiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogNormSectionIntegrableMixedChernProjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernFormFiniteIntegrablePointClosureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernIntegralAdditiveInFactorStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernFormSignedPartMeasureEqOfIsometricProjStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernIntegralAdditiveInFactorStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothWeightedLineBundleIsometryCalculusStatement
import Mathlib.AlgebraicGeometry.QuasiAffine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiPosRegPull

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Weight

open ReciprocityTheory.L2DbarEstimates (V leviV)

theorem semiPosReg_pull : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ) (π : Y ⟶ X) (hπ : π ≫ p = q) (D D' : ℕ), SmoothOfRelativeDimension D p → ∀ (B : LB X) (φ : Weight p σ B), φ.IsCInf → φ.SemiPosReg D → (φ.pull π hπ).SemiPosReg D' := by
  intro k _ X Y p q σ π hπ D D' hs B φ hC hSP
  haveI := hs
  intro i c y hy ξ
  set m := PtsOver.map π hπ (spMap σ)
  have hm : ∀ z, (m z).1 = z.1 ≫ π := fun _ => rfl
  obtain ⟨c0, h0⟩ := AlgChart.exists_mem_source (p := p) (σ := σ) (D := D) (m y)
  have him : m y ∈ ptsIn p σ (B.U (i PUnit.unit)) :=
    mem_of_mem_linComb (m := fun _ => m y) (fun _ => rfl) hy.2 PUnit.unit
  set F : V D' → V D := c0.e ∘ m ∘ c.e.symm with hFdef
  set U := c.e.target ∩ c.e.symm ⁻¹' (m ⁻¹' c0.e.source)
  have hU : IsOpen U := GlobalTheory.ChartGlue.isOpen_over c.e (c0.e.open_source.preimage (continuous_of_comp hm))
  have hyU : c.e y ∈ U := GlobalTheory.ChartGlue.mem_over c.e hy.1 h0
  have hF0 : DifferentiableOn ℂ F U := AlgChart.holo_map hm c c0
  have hF : ContDiffOn ℂ 2 F U := (contDiffOn_piLp 2).2 fun a =>
    (ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn D' _ U hU
      (differentiableOn_euclidean.1 hF0 a)).of_le (by norm_cast)
  have hFy : F (c.e y) = c0.e (m y) := by
    simp only [hFdef, Function.comp_apply, c.e.left_inv hy.1]
  set g : V D → ℂ := fun v => (φ.φ (i PUnit.unit) (c0.e.symm v) : ℂ) with hgdef
  have hg : ContDiffAt ℝ 2 g (F (c.e y)) := hFy ▸
    Complex.ofRealCLM.contDiff.contDiffAt.comp _ (hC.contDiffAt c0 h0 him)
  have e : (fun v => ((φ.pull π hπ).φ i (c.e.symm v) : ℂ)) =ᶠ[𝓝 (c.e y)] g ∘ F := by
    filter_upwards [hU.mem_nhds hyU] with v hv
    have := Weight.pull_φ φ π hπ i (c.e.symm v)
    simp only [g, hFdef, Function.comp_apply, c0.e.left_inv hv.2]
    exact congrArg _ this
  rw [ReciprocityTheory.L2DbarEstimates.leviV_congr e,
    ReciprocityTheory.ChartRestriction.G.AR.Up.RGF.gc_leviV_comp D' D g F U hU _ hyU hF hg ξ, hFy]
  exact hSP (i PUnit.unit) c0 (m y) ⟨h0, him⟩ _

end GlobalTheory.Weight
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiPosTwistMetrisedLineBundle

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

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}

theorem semiPosReg_of_eqOn_charts {E E' : LB X} (χ : Weight p σ E) {χ' : Weight p σ E'}
    (h : χ'.SemiPosReg D) (j : E.ι → E'.ι)
    (hj : ∀ i y, y ∈ ptsIn p σ (E.U i) → y ∈ ptsIn p σ (E'.U (j i)))
    (he : ∀ i y, y ∈ ptsIn p σ (E.U i) → χ.φ i y = χ'.φ (j i) y) : χ.SemiPosReg D := fun i c y hy ξ => by
  have ho := isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (E.U i))
  have e : (fun v => (χ.φ i (c.e.symm v) : ℂ)) =ᶠ[𝓝 (c.e y)] fun v => (χ'.φ (j i) (c.e.symm v) : ℂ) :=
    eventually_of_mem (ho.mem_nhds (mem_over c.e hy.1 hy.2)) fun v hv => by
      simp only [he i _ hv.2]
  rw [ReciprocityTheory.L2DbarEstimates.leviV_congr e]
  exact h (j i) c y ⟨hy.1, hj i y hy.2⟩ ξ

theorem exists_generating_secs_tens_lbPow {H L : LB X} (hH : H.IsLB) (hL : L.IsLB) {N : ℕ}
    {s : Fin (N + 1) → H.Sec} (hs : AbLaw.VeryAmpleBy p H s) :
    ∃ (m n : ℕ) (u : Fin n → (CechPic.tens L (lbPow H m)).Sec), ⨆ i, nonzeroLocus (u i) = ⊤ := by
  obtain ⟨t₀, ht⟩ := GlobalTheory.TwistGen.twist_generated k X p H _ s hH hs L hL
  obtain ⟨m, hm⟩ : ∃ m : ℕ, t₀ ≤ m := ⟨t₀.toNat, by omega⟩
  obtain ⟨n, u, hu⟩ := ht m hm
  have hP : (lbPow H m).IsLB := DVR.linComb_isLB H hH _ _
  have hT : (CechPic.tens L (lbPow H m)).IsLB := isLB_tens hL hP
  have e : cls (AbLaw.tw L H m) (AbLaw.isLB_tw hL hH _) =
      cls L hL - cls (AbLaw.pw H (-(m : ℤ))) (AbLaw.isLB_pw hH _) :=
    cls_div hL (AbLaw.isLB_pw hH _) (AbLaw.isLB_tw hL hH _)
  have e' : cls (AbLaw.tw L H m) (AbLaw.isLB_tw hL hH _) = cls _ hT := by
    rw [e, GlobalTheory.AmpleStabFinite.cls_pw hH, cls_tens hL hP, cls_lbPow hH, neg_zsmul, natCast_zsmul, sub_neg_eq_add]
  obtain ⟨v, hv⟩ := exists_generating_secs_of_cls_eq _ _ _ _ hT e' _ u hu
  exact ⟨m, _, v, hv⟩

theorem exists_semiPosReg_tens : ∀ (F : Type) [Field F] (X : Scheme.{0}) (p : X ⟶ Sp F) (σ : F →+* ℂ), IsProjOver p → ∀ (D : ℕ) (A : MLine p σ), ∃ Q : MLine p σ, Q.φ.SemiPosReg D ∧ (A.tens Q).φ.SemiPosReg D := by
  rintro F _ X p σ ⟨N, ι, hι, hp⟩ D A
  let O : MLine (PSpace.str F N) σ := MLine.ofHerm (ProjSpace.hermitianTwistingSheaf F N) σ
  have hO : O.φ.SemiPosReg N := Weight.semiPosReg_fsBasis (ProjSpace.O1_isLB F N) _
    (ProjSpace.iSup_nonzeroLocus_coord F N) 1 (by simp)
  have hsm : SmoothOfRelativeDimension N (PSpace.str F N) := inferInstance
  let H : MLine p σ := O.pull ι hp
  have hH : H.φ.SemiPosReg D := GlobalTheory.Weight.semiPosReg_pull F _ _ _ _ σ ι hp N D hsm _ _ O.cInf hO
  have hpow (m : ℕ) : (H.φ.pow m).SemiPosReg D :=
    Weight.SemiPosReg.of_mul _ H.cInf hH ((m : ℤ) : ℝ) (by positivity) (fun j => j PUnit.unit)
      (fun _ _ h => mem_pow_iff.1 h) fun j y => H.φ.zpow_φ (m : ℤ) j y
  have hva : ∃ s : Fin (N + 1) → H.B.Sec, AbLaw.VeryAmpleBy p H.B s := by
    dsimp [H, O, MLine.pull, MLine.ofHerm, ProjSpace.hermitianTwistingSheaf, HermLB.fs]
    subst hp
    exact ⟨_, ProjSpace.veryAmpleBy_secPull_coord ι⟩
  obtain ⟨s, hs⟩ := hva
  obtain ⟨m, hgen⟩ := exists_generating_secs_tens_lbPow H.φ.isLB A.φ.isLB hs
  obtain ⟨φ₁, hφ₁, hφ₁'⟩ := GlobalTheory.weight_cInf_semiPos_of_generated F X p σ _ (A.φ.tens (H.φ.pow m)).isLB hgen
  obtain ⟨u, hu, hu'⟩ := GlobalTheory.T.smooth_weights_differ_by_smooth_function F X p σ _ φ₁ (A.φ.tens (H.φ.pow m)) hφ₁ (A.cInf.tens (H.cInf.zpow m))
  obtain ⟨v, hv, hv'⟩ := GlobalTheory.ClosedExt.exists_extension F _ X (PSpace.str F N) p σ ⟨N, 𝟙 _, inferInstance, Category.id_comp _⟩ ι hp u hu
  obtain ⟨m', hm'⟩ := GlobalTheory.T.exists_semiPos_fubiniStudy_power_add_smooth_fn F σ N v hv
  have hwc : ((O.φ.pow m').addFn v).IsCInf := (O.cInf.zpow m').addFn hv
  have hw : (((O.φ.pow m').addFn v).pull ι hp).SemiPosReg D :=
    GlobalTheory.Weight.semiPosReg_pull F _ _ _ _ σ ι hp N D hsm _ _ hwc (hm' m' le_rfl)
  refine ⟨⟨_, (H.φ.pow m).tens (H.φ.pow m'), (H.cInf.zpow m).tens (H.cInf.zpow m')⟩,
    Weight.SemiPosReg.tens (H.cInf.zpow m) (H.cInf.zpow m') (hpow m) (hpow m'), ?_⟩
  refine semiPosReg_of_eqOn_charts (A.φ.tens ((H.φ.pow m).tens (H.φ.pow m')))
    (Weight.SemiPosReg.tens hφ₁ (hwc.pull ι hp) (hφ₁' D) hw)
    (fun i => ((i.1, i.2.1), i.2.2)) (fun i y hy => ?_) fun i y hy => ?_
  · obtain ⟨h₁, h₂⟩ := mem_ptsIn_inf.1 hy
    obtain ⟨h₂, h₃⟩ := mem_ptsIn_inf.1 h₂
    refine mem_ptsIn_inf.2 ⟨mem_ptsIn_inf.2 ⟨h₁, h₂⟩, ?_⟩
    have h₄ := mem_pow_iff.1 h₃
    exact mem_ptsIn.2 (Set.mem_iInter.2 fun _ => Set.mem_iInter.2 fun b => Set.mem_iInter.1 (mem_ptsIn.1 h₄) b)
  · obtain ⟨h₁, h₂⟩ := mem_ptsIn_inf.1 hy
    obtain ⟨h₂, h₃⟩ := mem_ptsIn_inf.1 h₂
    have e₁ : A.φ.φ i.1 y + (H.φ.pow m).φ i.2.1 y = φ₁.φ (i.1, i.2.1) y + u y :=
      hu' (i.1, i.2.1) y (mem_ptsIn_inf.2 ⟨h₁, h₂⟩)
    have e₂ : (H.φ.pow m').φ i.2.2 y = (O.φ.pow m').φ (i.2.2 PUnit.unit) (ptMap ι hp σ y) :=
      (H.φ.zpow_φ m' i.2.2 y).trans ((congrArg (_ * ·) (O.φ.pull_φ ι hp (i.2.2 PUnit.unit) y)).trans
        (O.φ.zpow_φ m' (i.2.2 PUnit.unit) _).symm)
    have e₃ : (((O.φ.pow m').addFn v).pull ι hp).φ i.2.2 y =
        (O.φ.pow m').φ (i.2.2 PUnit.unit) (ptMap ι hp σ y) + v (ptMap ι hp σ y) :=
      ((O.φ.pow m').addFn v).pull_φ ι hp i.2.2 y
    change A.φ.φ i.1 y + ((H.φ.pow m).φ i.2.1 y + (H.φ.pow m').φ i.2.2 y) =
      φ₁.φ (i.1, i.2.1) y + (((O.φ.pow m').addFn v).pull ι hp).φ i.2.2 y
    rw [e₃, hv', e₂, ← add_assoc, e₁]
    ring

end GlobalTheory.Mix
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiPosTwistMetrisedLineBundleStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

theorem _root_.GlobalTheory.T.exists_semiPos_twist_metrisedLineBundle : ∀ (F : Type) [Field F] (X : Scheme.{0}) (p : X ⟶ Sp F) (σ : F →+* ℂ), IsProjOver p → ∀ (D : ℕ) (A : MLine p σ), ∃ Q : MLine p σ, Q.φ.SemiPosReg D ∧ (A.tens Q).φ.SemiPosReg D := by
  first | exact @GlobalTheory.Mix.exists_semiPosReg_tens | exact GlobalTheory.Mix.exists_semiPosReg_tens | (intros; apply GlobalTheory.Mix.exists_semiPosReg_tens <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointClosureIntegralUpdateTensorAdditive

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

namespace GlobalTheory.Mix.CycAdd

theorem isProjOver_clos {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} (hp : IsProjOver p) (z : X) :
    IsProjOver (closι z ≫ p) := by
  obtain ⟨N, i, hi, h⟩ := hp
  exact ⟨N, closι z ≫ i, inferInstance, by rw [Category.assoc, h]⟩

theorem int_congr {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}
    {L M : Fin D → MLine p σ} (h : ∀ ε, part L ε = part M ε) (f : CxPts p σ → ℝ) : Mix.int L f = Mix.int M f := by
  simp only [Mix.int, h]

theorem pull_update {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}
    (L : Fin D → MLine p σ) (i : Fin D) (A : MLine p σ) (z : X) :
    (fun j => (Function.update L i A j).pull (closι z) rfl) =
      Function.update (fun j => (L j).pull (closι z) rfl) i (A.pull (closι z) rfl) := by
  funext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [Function.update_of_ne hj]

end GlobalTheory.Mix.CycAdd


open GlobalTheory.Mix.CycAdd in
theorem GlobalTheory.Mix.cycInt_update_tens : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ), IsProjOver p → ∀ (D : ℕ) (L : Fin D → MLine p σ) (i : Fin D) (A B : MLine p σ) (f : CxPts p σ → ℝ) (z : X), CycIntg (Function.update L i A) f z → CycIntg (Function.update L i B) f z → cycInt (Function.update L i (A.tens B)) f z = cycInt (Function.update L i A) f z + cycInt (Function.update L i B) f z := by
  intro k _ X p σ hp D L i A B f z hA hB
  have hq := isProjOver_clos hp z
  have hI := GlobalTheory.T.smoothWeightedLineBundle_isometry_calculus k X (clos z) p (closι z ≫ p) σ (closι z) rfl
  have hparts : ∀ ε, part (fun j => (Function.update L i (A.tens B) j).pull (closι z) rfl) ε =
      part (Function.update (fun j => (L j).pull (closι z) rfl) i
        ((A.pull (closι z) rfl).tens (B.pull (closι z) rfl))) ε := by
    intro ε
    refine GlobalTheory.T.mixedChernFormSignedPartMeasure_eq_of_isometric_projOver k (clos z) (closι z ≫ p) σ hq D _ _ (fun j => ?_) ε
    by_cases hj : j = i
    · subst hj; simpa using hI.2.2.1 A B
    · simpa [Function.update_of_ne hj] using (GlobalTheory.T.smoothWeightedLineBundle_isometry_calculus k (clos z) (clos z) (closι z ≫ p) (closι z ≫ p) σ (𝟙 _) (Category.id_comp _)).1 ((L j).pull (closι z) rfl)
  unfold CycIntg at hA hB
  unfold cycInt
  rw [int_congr hparts, pull_update, pull_update]
  rw [pull_update] at hA hB
  exact (GlobalTheory.T.mixedChernIntegral_additive_in_factor k (clos z) (closι z ≫ p) σ hq D _ i _ _ _ hA hB).2
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointClosureIntegralUpdateTensorAdditiveStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

theorem _root_.GlobalTheory.T.pointClosureIntegral_update_tensor_additive : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ), IsProjOver p → ∀ (D : ℕ) (L : Fin D → MLine p σ) (i : Fin D) (A B : MLine p σ) (f : CxPts p σ → ℝ) (z : X), CycIntg (Function.update L i A) f z → CycIntg (Function.update L i B) f z → cycInt (Function.update L i (A.tens B)) f z = cycInt (Function.update L i A) f z + cycInt (Function.update L i B) f z := by
  first | exact @GlobalTheory.Mix.cycInt_update_tens | exact GlobalTheory.Mix.cycInt_update_tens | (intros; apply GlobalTheory.Mix.cycInt_update_tens <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReciprocitySectionsGeneratedBundles

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

namespace GlobalTheory.RecSec

theorem compactSpace_of_projOver {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R}
    (h : IsProjOver f) : CompactSpace X := by
  obtain ⟨m, i, hi, rfl⟩ := h
  have := isProper_str R m
  have : IsProper (i ≫ PSpace.str R m) := inferInstance
  exact QuasiCompact.compactSpace_of_compactSpace (i ≫ PSpace.str R m)

theorem finsum_update_tens (P : GlobalTheory.Published.Principalisation) {F : Type} [Field F] {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] {p : X ⟶ Sp F} {σ : F →+* ℂ} {e : ℕ} (hp : IsProjOver p)
    (hdim : topologicalKrullDim X = (e + 1 : ℕ)) (Δ : CartierDiv X) (B : MLine p σ) (b : B.B.Sec)
    (hb : ∀ z, Δ.mult z ≠ 0 → z ∈ nonzeroLocus b) (L : Fin e → MLine p σ) (i : Fin e) (A C : MLine p σ) :
    ∑ᶠ z, (Δ.mult z : ℝ) * cycInt (Function.update L i (A.tens C)) (B.logSec b) z =
      ∑ᶠ z, (Δ.mult z : ℝ) * cycInt (Function.update L i A) (B.logSec b) z +
        ∑ᶠ z, (Δ.mult z : ℝ) * cycInt (Function.update L i C) (B.logSec b) z := by
  have : CompactSpace X := compactSpace_of_projOver hp
  have hfin := Δ.finite_support_mult
  have hsub (G : X → ℝ) : (Function.support fun z => (Δ.mult z : ℝ) * G z).Finite :=
    hfin.subset fun z hz => by
      simp only [Function.mem_support] at hz ⊢
      intro h0; exact hz (by simp [h0])
  rw [← finsum_add_distrib (hsub _) (hsub _)]
  refine finsum_congr fun z => ?_
  by_cases h0 : Δ.mult z = 0
  · simp [h0]
  have hz1 : Order.coheight z = 1 := CartierDiv.coheight_eq_one_of_mult_ne_zero h0
  have hcl : topologicalKrullDim (closure ({z} : Set X)) = e :=
    (GlobalTheory.T.coheight_eq_one_iff_closure_dim_projective F X p e hp hdim z).1 hz1
  have h₁ := (GlobalTheory.T.mixedChernForm_finite_integrable_pointClosure P F X p σ hp e (Function.update L i A) z hcl).2.2.2 B b (hb z h0)
  have h₂ := (GlobalTheory.T.mixedChernForm_finite_integrable_pointClosure P F X p σ hp e (Function.update L i C) z hcl).2.2.2 B b (hb z h0)
  rw [GlobalTheory.T.pointClosureIntegral_update_tensor_additive F X p σ hp e L i A C (B.logSec b) z h₁ h₂, mul_add]

theorem side_update_tens (P : GlobalTheory.Published.Principalisation) {F : Type} [Field F] {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] {p : X ⟶ Sp F} {σ : F →+* ℂ} {e : ℕ} (hp : IsProjOver p)
    (hdim : topologicalKrullDim X = (e + 1 : ℕ)) (N M : MLine p σ) (s : M.B.Sec)
    (hs : genericPoint X ∈ nonzeroLocus s) (Δ : CartierDiv X) (B : MLine p σ) (b : B.B.Sec)
    (hb : ∀ z, Δ.mult z ≠ 0 → z ∈ nonzeroLocus b) (L : Fin e → MLine p σ) (i : Fin e) (A C : MLine p σ) :
    side N (Function.update L i (A.tens C)) (M.logSec s) (B.logSec b) Δ =
      side N (Function.update L i A) (M.logSec s) (B.logSec b) Δ +
        side N (Function.update L i C) (M.logSec s) (B.logSec b) Δ := by
  simp only [side, Fin.cons_update]
  have hA := GlobalTheory.T.log_norm_section_integrable_mixedChern_projective P F X p σ (e + 1) hp hdim (Function.update (Fin.cons N L) i.succ A) M s hs
  have hC := GlobalTheory.T.log_norm_section_integrable_mixedChern_projective P F X p σ (e + 1) hp hdim (Function.update (Fin.cons N L) i.succ C) M s hs
  rw [(GlobalTheory.T.mixedChernIntegral_additive_in_factor F X p σ hp (e + 1) (Fin.cons N L) i.succ A C (M.logSec s) hA hC).2,
    finsum_update_tens P hp hdim Δ B b hb L i A C]
  ring

theorem reciprocity_sec : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (e : ℕ), IsProjOver p → topologicalKrullDim X = (e + 1 : ℕ) → ∀ (L : Fin e → MLine p σ) (M N : MLine p σ) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (t : N.B.Sec) (ht : genericPoint X ∈ nonzeroLocus t), (∀ z : X, Order.coheight z = 1 → z ∈ nonzeroLocus s ∨ z ∈ nonzeroLocus t) → (∃ (n : ℕ) (u : Fin n → M.B.Sec), ⨆ i, nonzeroLocus (u i) = ⊤) → (∃ (n : ℕ) (u : Fin n → N.B.Sec), ⨆ i, nonzeroLocus (u i) = ⊤) → side N L (M.logSec s) (N.logSec t) (divOfSec M.φ.isLB s hs) = side M L (N.logSec t) (M.logSec s) (divOfSec N.φ.isLB t ht) := by
  intro P F _ X _ _ p σ e hp hdim L M N s hs t ht hcod hgM hgN
  classical
  let Df : (Fin e → MLine p σ) → ℝ := fun L =>
    side N L (M.logSec s) (N.logSec t) (divOfSec M.φ.isLB s hs) -
      side M L (N.logSec t) (M.logSec s) (divOfSec N.φ.isLB t ht)
  have hbt : ∀ z, (divOfSec M.φ.isLB s hs).mult z ≠ 0 → z ∈ nonzeroLocus t := fun z h0 =>
    (hcod z (CartierDiv.coheight_eq_one_of_mult_ne_zero h0)).resolve_left fun hz =>
      (notMem_supp_divOfSec.2 hz) (CartierDiv.mem_supp_of_mult_ne_zero h0)
  have hbs : ∀ z, (divOfSec N.φ.isLB t ht).mult z ≠ 0 → z ∈ nonzeroLocus s := fun z h0 =>
    (hcod z (CartierDiv.coheight_eq_one_of_mult_ne_zero h0)).resolve_right fun hz =>
      (notMem_supp_divOfSec.2 hz) (CartierDiv.mem_supp_of_mult_ne_zero h0)
  have hadd : ∀ (L : Fin e → MLine p σ) (i : Fin e) (A C : MLine p σ),
      Df (Function.update L i (A.tens C)) = Df (Function.update L i A) + Df (Function.update L i C) := by
    intro L i A C
    simp only [Df, side_update_tens P hp hdim N M s hs _ N t hbt L i A C,
      side_update_tens P hp hdim M N t ht _ M s hbs L i A C]
    ring
  have hpos : ∀ L : Fin e → MLine p σ, (∀ i, (L i).φ.SemiPosReg (e + 1)) → Df L = 0 := fun L hL =>
    sub_eq_zero.2 (GlobalTheory.T.generatedBundles_reciprocity_semiPositive P F X p σ e hp hdim L M N s hs t ht hcod hL hgM hgN)
  have key : ∀ (S : Finset (Fin e)) (L : Fin e → MLine p σ),
      (∀ i, i ∉ S → (L i).φ.SemiPosReg (e + 1)) → Df L = 0 := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact fun L hL => hpos L fun i => hL i (Finset.notMem_empty i)
    | insert a S ha ih =>
      intro L hL
      obtain ⟨Q, hQ, hAQ⟩ := GlobalTheory.T.exists_semiPos_twist_metrisedLineBundle F X p σ hp (e + 1) (L a)
      have hgood : ∀ R : MLine p σ, R.φ.SemiPosReg (e + 1) → Df (Function.update L a R) = 0 := by
        intro R hR
        refine ih _ fun i hi => ?_
        by_cases hia : i = a
        · subst hia; rw [Function.update_self]; exact hR
        · rw [Function.update_of_ne hia]
          exact hL i (by simp [hia, hi])
      have h := hadd L a (L a) Q
      rw [hgood _ hAQ, hgood _ hQ, Function.update_eq_self] at h
      linarith
  have := key Finset.univ L fun i hi => absurd (Finset.mem_univ i) hi
  exact sub_eq_zero.1 this

end GlobalTheory.RecSec
end
end
