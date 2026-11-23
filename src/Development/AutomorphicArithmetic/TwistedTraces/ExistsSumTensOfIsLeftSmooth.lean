module

public import Development.AutomorphicArithmetic.Foundations.Convolution.TensFun
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.CuspDecayHeights.HeightLe
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.TensApply
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Topology.ContinuousMap.CompactlySupported
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.TensCont
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.CuspidalMultiplicityOneTotallyComplex
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.CuspDecayHeights.HeightLe
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Archimedean
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.Counting
import GroundTheory.AutomorphicForms.QuotientMeasure
import GroundTheory.AutomorphicForms.ReductionBlock
import GroundTheory.AutomorphicForms.WhittakerRelevance
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Development.AutomorphicArithmetic.TwistedTraces.ExistsSmoothArchCutoffKbarEqOne
import Mathlib.Tactic.Linter.HaveILetI
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SummandsAreCuspForms

-- Source module: Development.AutomorphicArithmetic.TwistedTraces.ExistsFiniteBasisLeftInvariantCompactSupport

section

@[expose] public section

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum PositivityTheory.Rg.Tf.Core UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped ContDiff

theorem UpperTheory.exists_finite_basis_leftInvariant_compactSupport :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] (V : Subgroup G),
        IsOpen (V : Set G) → IsCompact (V : Set G) → ∀ S : Set G, IsCompact S →
        ∃ (m : ℕ) (b : Fin m → G) (e : Fin m → CompactlySupportedContinuousMap G ℂ),
          (∀ j, ∀ v ∈ V, ∀ h, e j (v * h) = e j h) ∧
          ∀ f : G → ℂ, (∀ v ∈ V, ∀ h, f (v * h) = f h) → (∀ h, h ∉ S → f h = 0) →
            ∀ h, f h = ∑ j, e j h * f (b j) := by
  intro G _ _ _ _ V hVo hVc S hS
  classical
  have hVcl : IsClosed (V : Set G) := Subgroup.isClosed_of_isOpen V hVo

  let W : G → Set G := fun b => {h | b * h⁻¹ ∈ V}
  have hWpre : ∀ b, W b = (fun h : G => b * h⁻¹) ⁻¹' (V : Set G) := fun b => rfl
  have hcont : ∀ b : G, Continuous (fun h : G => b * h⁻¹) := fun b =>
    continuous_const.mul continuous_inv
  have hWo : ∀ b, IsOpen (W b) := fun b => by
    rw [hWpre]; exact hVo.preimage (hcont b)
  have hWcl : ∀ b, IsClosed (W b) := fun b => by
    rw [hWpre]; exact hVcl.preimage (hcont b)
  have hWself : ∀ b, b ∈ W b := fun b => by
    show b * b⁻¹ ∈ V
    simpa using V.one_mem
  have hWK : ∀ b, W b ⊆ (fun v : G => v⁻¹ * b) '' (V : Set G) := fun b h hh =>
    ⟨b * h⁻¹, hh, by group⟩
  have hKc : ∀ b, IsCompact ((fun v : G => v⁻¹ * b) '' (V : Set G)) := fun b =>
    hVc.image (continuous_inv.mul continuous_const)
  have hWinv : ∀ b, ∀ v ∈ V, ∀ h, v * h ∈ W b ↔ h ∈ W b := fun b v hv h => by
    show b * (v * h)⁻¹ ∈ V ↔ b * h⁻¹ ∈ V
    have : b * (v * h)⁻¹ = b * h⁻¹ * v⁻¹ := by group
    rw [this]
    exact V.mul_mem_cancel_right (V.inv_mem hv)

  let E : G → CompactlySupportedContinuousMap G ℂ := fun b =>
    { toFun := (W b).indicator (fun _ => (1 : ℂ))
      continuous_toFun := (IsClopen.continuous_indicator ⟨hWcl b, hWo b⟩ continuous_const)
      hasCompactSupport' := by
        refine HasCompactSupport.intro (hKc b) (fun x hx => ?_)
        exact Set.indicator_of_notMem (fun hxW => hx (hWK b hxW)) _ }
  have hE : ∀ b h, E b h = (W b).indicator (fun _ => (1 : ℂ)) h := fun _ _ => rfl

  let q : G → Quotient (QuotientGroup.rightRel V) := fun h => Quotient.mk _ h
  have hq : ∀ x y : G, q x = q y ↔ x ∈ W y := fun x y => by
    show Quotient.mk _ x = Quotient.mk _ y ↔ y * x⁻¹ ∈ V
    rw [Quotient.eq]
    exact QuotientGroup.rightRel_apply
  obtain ⟨t, -, ht⟩ := hS.elim_nhds_subcover W (fun x _ => (hWo x).mem_nhds (hWself x))
  let T : Finset (Quotient (QuotientGroup.rightRel V)) := t.image q
  let ε := T.equivFin
  let b : Fin T.card → G := fun j => (ε.symm j).1.out
  have hqb : ∀ j, q (b j) = (ε.symm j).1 := fun j => Quotient.out_eq _
  refine ⟨T.card, b, fun j => E (b j), ?_, ?_⟩
  · intro j v hv h
    rw [hE, hE]
    by_cases hh : h ∈ W (b j)
    · rw [Set.indicator_of_mem hh, Set.indicator_of_mem ((hWinv _ v hv h).2 hh)]
    · rw [Set.indicator_of_notMem hh,
        Set.indicator_of_notMem (fun h' => hh ((hWinv _ v hv h).1 h'))]
  · intro f hfV hfS h
    have hfW : ∀ c x, x ∈ W c → f x = f c := fun c x hx => by
      have := hfV (c * x⁻¹) hx x
      simpa using this.symm
    by_cases hT : q h ∈ T
    · let j0 : Fin T.card := ε ⟨q h, hT⟩
      have hj0 : q (b j0) = q h := by
        rw [hqb]; simp [j0]
      have hmem : h ∈ W (b j0) := (hq _ _).1 hj0.symm
      rw [Finset.sum_eq_single j0]
      · rw [hE, Set.indicator_of_mem hmem, one_mul]
        exact hfW _ _ hmem
      · intro j _ hj
        have hnot : h ∉ W (b j) := fun hm => by
          apply hj
          have h1 : (ε.symm j).1 = q h := by rw [← hqb]; exact ((hq _ _).2 hm).symm
          have h2 : ε.symm j = ⟨q h, hT⟩ := Subtype.ext h1
          simp [j0, ← h2]
        rw [hE, Set.indicator_of_notMem hnot, zero_mul]
      · intro hj; exact absurd (Finset.mem_univ _) hj
    · have hhS : h ∉ S := fun hs => by
        have := ht hs
        simp only [Set.mem_iUnion] at this
        obtain ⟨x, hx, hxW⟩ := this
        exact hT (Finset.mem_image.2 ⟨x, hx, ((hq _ _).2 hxW).symm⟩)
      rw [hfS h hhS]
      symm
      refine Finset.sum_eq_zero (fun j _ => ?_)
      have hnot : h ∉ W (b j) := fun hm => hT (by
        rw [(hq _ _).2 hm, hqb]; exact (ε.symm j).2)
      rw [hE, Set.indicator_of_notMem hnot, zero_mul]
end
end

-- Source module: Development.AutomorphicArithmetic.TwistedTraces.ExistsSmoothTKbarEqRestriction

section

@[expose] public section

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum PositivityTheory.Rg.Tf.Core UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped ContDiff

theorem UpperTheory.exists_smoothT_kbar_eq_restriction :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 0 < n → ∀ (a : CC K n) (x₀ : G1 K n),
        (isExpLieAlgebra K n).IsSmoothFun (fun A : archGroup K n => a (archP K n A * x₀)) →
        ∃ F : TI K n, SmoothT F ∧ ∀ A, kbar F A = a (archP K n A * x₀) := by
  intro K _ _ n hn a x₀ ha
  obtain ⟨χ, hχs, hχ1, hχc⟩ := UpperTheory.exists_smooth_archCutoff_kbar_eq_one K n hn
  have hχcont : Continuous fun A : archGroup K n => (χ A : ℂ) := by
    letI := (isExpLieAlgebra K n).chartedSpace
    exact ContMDiff.continuous hχs
  have hcont : Continuous fun A : archGroup K n => (χ A : ℂ) * a (archP K n A * x₀) :=
    hχcont.mul (a.continuous.comp (continuous_archP.mul continuous_const))
  have hC : IsCompact ((fun g : G1 K n => g * x₀⁻¹) '' tsupport a) :=
    a.hasCompactSupport.isCompact.image (continuous_id.mul continuous_const)
  obtain ⟨D, hD, hDm⟩ := hχc _ hC
  have hcs : HasCompactSupport fun A : archGroup K n => (χ A : ℂ) * a (archP K n A * x₀) := by
    refine HasCompactSupport.intro hD fun A hA => ?_
    by_contra hne
    have h1 : χ A ≠ 0 := fun h0 => hne (by rw [h0, Complex.ofReal_zero, zero_mul])
    have h2 : a (archP K n A * x₀) ≠ 0 := fun h0 => hne (by rw [h0, mul_zero])
    exact hA (hDm A h1 ⟨archP K n A * x₀, subset_tsupport _ h2, by simp⟩)
  refine ⟨⟨⟨_, hcont⟩, hcs⟩, ?_, fun A => ?_⟩
  · refine ((isExpLieAlgebra K n).isSmoothFun_iff).2 fun g => ?_
    exact ContDiff.mul (((isExpLieAlgebra K n).isSmoothFun_iff).1 hχs g)
      (((isExpLieAlgebra K n).isSmoothFun_iff).1 ha g)
  · have h1 := hχ1 A
    unfold kbar at h1 ⊢
    have h2 : ∀ s, (χ (A * zInf K n s) : ℂ) * a (archP K n (A * zInf K n s) * x₀) =
        (χ (A * zInf K n s) : ℂ) * a (archP K n A * x₀) := fun s => by
      rw [archimedeanProjection_mul_positiveScalar hn]
    show ∫ s, (χ (A * zInf K n s) : ℂ) * a (archP K n (A * zInf K n s) * x₀) ∂_ = _
    simp_rw [h2]
    rw [integral_mul_const, h1, one_mul]
end
end

-- Source module: Development.AutomorphicArithmetic.TwistedTraces.ExistsSumTensOfIsLeftSmooth

section

@[expose] public section

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum PositivityTheory.Rg.Tf.Core UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped ContDiff

private theorem split_pt {K : Type} [Field K] [NumberField K] {n : ℕ} (x : G1 K n) :
    x = archP K n (infPart K n (x : AdelicGLn.AdelicGL K n)) *
      MultiplicityOne.finProj K n (finPart K n (x : AdelicGLn.AdelicGL K n)) := by
  have h1 : retractOne (finEmb K n (finPart K n (x : AdelicGLn.AdelicGL K n))) =
      MultiplicityOne.finProj K n (finPart K n (x : AdelicGLn.AdelicGL K n)) := by
    ext1
    rfl
  rw [← h1, ← retract_infEmb, ← retractOne_mul, infEmb_infPart_mul_finEmb_finPart, retractOne_coe]

private theorem finPart_split {K : Type} [Field K] [NumberField K] {n : ℕ} (A : archGroup K n)
    (h : AdelicGLn.FiniteAdelicGL K n) :
    finPart K n ((archP K n A * MultiplicityOne.finProj K n h : G1 K n) : AdelicGLn.AdelicGL K n) = h := by
  have h1 : retractOne (finEmb K n h) = MultiplicityOne.finProj K n h := by
    ext1
    rfl
  rw [Subgroup.coe_mul, map_mul, finPart_archP, one_mul, ← h1, finPart_retract, finPart_finEmb]

theorem UpperTheory.exists_sum_tens_of_isLeftSmooth :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 0 < n → ∀ a : CC K n, IsLeftSmooth a →
        ∃ (U : Subgroup (AdelicGLn.integralFiniteGL K n)) (_ : IsOpen (U : Set (AdelicGLn.integralFiniteGL K n)))
          (m : ℕ) (F : Fin m → TI K n) (e : Fin m → TF K n), (∀ j, SmoothT (F j)) ∧
          (∀ j, ∀ u ∈ U, ∀ h, e j ((u : AdelicGLn.FiniteAdelicGL K n) * h) = e j h) ∧ a = ∑ j, tens (F j) (e j) := by
  intro K _ _ n hn a ha
  obtain ⟨hsm, U, hU, hinv⟩ := ha
  have hVo : IsOpen (((finOpenSubgroup U hU).toSubgroup : Subgroup _) : Set (AdelicGLn.FiniteAdelicGL K n)) :=
    (finOpenSubgroup U hU).isOpen
  have hVc : IsCompact (((finOpenSubgroup U hU).toSubgroup : Subgroup _) : Set (AdelicGLn.FiniteAdelicGL K n)) :=
    isCompact_openSubgroupOf U hU
  have hS : IsCompact ((fun x : G1 K n => finPart K n (x : AdelicGLn.AdelicGL K n)) '' tsupport a) :=
    a.hasCompactSupport.isCompact.image (continuous_finPart.comp continuous_subtype_val)
  obtain ⟨m, b, e, heV, hE⟩ := UpperTheory.exists_finite_basis_leftInvariant_compactSupport _ (finOpenSubgroup U hU).toSubgroup hVo hVc _ hS
  choose F hF hFk using fun j => UpperTheory.exists_smoothT_kbar_eq_restriction K n hn a (MultiplicityOne.finProj K n (b j)) (hsm _)
  refine ⟨U, hU, m, F, e, hF, fun j u hu h => heV j _ (coe_mem_openSubgroupOf U hU hu) h, ?_⟩
  ext x
  have hsum : ∀ (s : Finset (Fin m)), (∑ j ∈ s, tens (F j) (e j)) x = ∑ j ∈ s, tens (F j) (e j) x := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, CompactlySupportedContinuousMap.add_apply, ih]
  rw [hsum Finset.univ]
  simp only [(UpperTheory.ConvolutionTheory.Tf.tensApply K n hn _ _).1, tensFun, hFk]
  have hfV : ∀ v ∈ (finOpenSubgroup U hU).toSubgroup, ∀ h,
      a (archP K n (infPart K n (x : AdelicGLn.AdelicGL K n)) * MultiplicityOne.finProj K n (v * h)) =
        a (archP K n (infPart K n (x : AdelicGLn.AdelicGL K n)) * MultiplicityOne.finProj K n h) := by
    intro v hv h
    have hv' : v ∈ (finOpenSubgroup U hU : Set (AdelicGLn.FiniteAdelicGL K n)) := hv
    rw [coe_openSubgroupOf] at hv'
    obtain ⟨u, hu, rfl⟩ := hv'
    rw [map_mul (MultiplicityOne.finProj K n), MultiplicityOne.finProj_eq_finOne, ← mul_assoc, archimedeanProjection_mul_finiteEmbedding_comm, mul_assoc, hinv u hu]
  have hfS : ∀ h, h ∉ (fun x : G1 K n => finPart K n (x : AdelicGLn.AdelicGL K n)) '' tsupport a →
      a (archP K n (infPart K n (x : AdelicGLn.AdelicGL K n)) * MultiplicityOne.finProj K n h) = 0 := by
    intro h hh
    by_contra hne
    exact hh ⟨_, subset_tsupport _ hne, finPart_split _ h⟩
  have key := hE (fun h => a (archP K n (infPart K n (x : AdelicGLn.AdelicGL K n)) * MultiplicityOne.finProj K n h))
    hfV hfS (finPart K n (x : AdelicGLn.AdelicGL K n))
  simp only [← split_pt x] at key
  rw [key]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm]
end
end
