module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntegrandPeriodic
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Dimension.Finrank
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralFundamentalDomainEqIteratedDecomp
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.PartsOrth
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdaptedFrameOfIsotropicColumns

section

@[expose] public section

namespace GlobalTheory

open Matrix

theorem exists_adapted_frame_of_isotropic_columns :
    ∀ (E : Type) [Field E] (r : ℕ) (Y : Submodule E ((Fin r → E) × (Fin r → E))),
      Module.finrank E Y = r →
      ∀ (C : Matrix (Fin r) (Fin r) E × Matrix (Fin r) (Fin r) E),
        Submodule.span E (Set.range fun j => ((fun a => C.1 a j), (fun a => C.2 a j))) = Y →
        ∀ (s : ℕ) (I : Matrix (Fin r) (Fin s) E), LinearIndependent E I.transpose →
          (∀ j, ((fun a => I a j), (0 : Fin r → E)) ∈ Y) →
          ∃ (t : ℕ) (J : Matrix (Fin r) (Fin s) E) (K : Matrix (Fin r) (Fin t) E)
            (L : Matrix (Fin s) (Fin r) E) (M : Matrix (Fin t) (Fin r) E),
            C.1 * J = I ∧ C.2 * J = 0 ∧ L * J = 1 ∧ L * K = 0 ∧ M * J = 0 ∧ M * K = 1 ∧
              J * L + K * M = 1 := by
  intro E _ r Y _ C hspan s I hI hmem

  have hc : ∀ j, ∃ c : Fin r → E,
      ∑ k, c k • ((fun a => C.1 a k), (fun a => C.2 a k)) = ((fun a => I a j), (0 : Fin r → E)) := by
    intro j
    have := hmem j
    rw [← hspan] at this
    exact (Submodule.mem_span_range_iff_exists_fun E).mp this
  choose c hc using hc
  let J : Matrix (Fin r) (Fin s) E := Matrix.of fun k j => c j k
  have h1 : C.1 * J = I := by
    ext a j
    have := congrFun (congrArg Prod.fst (hc j)) a
    simp only [Prod.fst_sum, Prod.smul_fst, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    simp only [Matrix.mul_apply, J, Matrix.of_apply]
    rw [← this]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have h2 : C.2 * J = 0 := by
    ext a j
    have := congrFun (congrArg Prod.snd (hc j)) a
    simp only [Prod.snd_sum, Prod.smul_snd, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply] at this
    simp only [Matrix.mul_apply, J, Matrix.of_apply, Matrix.zero_apply]
    rw [← this]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _

  have hIinj : Function.Injective I.mulVec := Matrix.mulVec_injective_iff.mpr hI
  have hJinj : Function.Injective J.mulVec := by
    intro x y hxy
    apply hIinj
    rw [← h1, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hxy]
  let jL : (Fin s → E) →ₗ[E] (Fin r → E) := Matrix.toLin' J
  have hker : LinearMap.ker jL = ⊥ := LinearMap.ker_eq_bot.mpr (by
    intro x y hxy; exact hJinj (by simpa [jL, Matrix.toLin'_apply] using hxy))
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective jL hker
  let Wk := LinearMap.ker g
  let b := Module.finBasis E Wk
  let kL : (Fin (Module.finrank E Wk) → E) →ₗ[E] (Fin r → E) :=
    Wk.subtype ∘ₗ b.equivFun.symm.toLinearMap
  have hgP : ∀ x, g (x - jL (g x)) = 0 := by
    intro x
    rw [map_sub]
    have := LinearMap.congr_fun hg (g x)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
    rw [this, sub_self]
  let ψ : (Fin r → E) →ₗ[E] Wk :=
    LinearMap.codRestrict Wk (LinearMap.id - jL ∘ₗ g) (fun x => by
      simpa [Wk, LinearMap.mem_ker] using hgP x)
  let mL : (Fin r → E) →ₗ[E] (Fin (Module.finrank E Wk) → E) := b.equivFun.toLinearMap ∘ₗ ψ
  have hJ : J = LinearMap.toMatrix' jL := by simp [jL]
  refine ⟨Module.finrank E Wk, J, LinearMap.toMatrix' kL, LinearMap.toMatrix' g,
    LinearMap.toMatrix' mL, h1, h2, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hJ, ← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]
  · rw [← LinearMap.toMatrix'_comp]
    have : g ∘ₗ kL = 0 := by
      refine LinearMap.ext fun y => ?_
      simp only [LinearMap.comp_apply, LinearMap.zero_apply, kL]
      exact (b.equivFun.symm y).2
    rw [this, map_zero]
  · rw [hJ, ← LinearMap.toMatrix'_comp]
    have : mL ∘ₗ jL = 0 := by
      refine LinearMap.ext fun x => ?_
      simp only [LinearMap.comp_apply, LinearMap.zero_apply, mL]
      have : ψ (jL x) = 0 := by
        apply Subtype.ext
        simp only [ψ, LinearMap.codRestrict_apply, LinearMap.sub_apply, LinearMap.id_apply,
          LinearMap.comp_apply, ZeroMemClass.coe_zero]
        have := LinearMap.congr_fun hg x
        simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
        rw [this, sub_self]
      rw [this, map_zero]
    rw [this, map_zero]
  · rw [← LinearMap.toMatrix'_comp]
    have : mL ∘ₗ kL = LinearMap.id := by
      refine LinearMap.ext fun y => ?_
      simp only [LinearMap.comp_apply, LinearMap.id_apply, mL]
      have : ψ (kL y) = b.equivFun.symm y := by
        apply Subtype.ext
        have hk : g (kL y) = 0 := (b.equivFun.symm y).2
        simp only [ψ, LinearMap.codRestrict_apply, LinearMap.sub_apply, LinearMap.id_apply,
          LinearMap.comp_apply, hk, map_zero, sub_zero]
        rfl
      rw [this]
      exact b.equivFun.apply_symm_apply y
    rw [this, LinearMap.toMatrix'_id]
  · rw [hJ, ← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_comp, ← map_add (f := _),
      ← LinearMap.toMatrix'_id]
    congr 1
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply, mL, kL]
    simp only [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, Submodule.coe_subtype, ψ,
      LinearMap.codRestrict_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply]
    abel

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdaptedFrameOfIsotropicColumnsStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.exists_adapted_frame_of_isotropic_columns' : ∀ (E : Type) [Field E] (r : ℕ) (Y : Submodule E ((Fin r → E) × (Fin r → E))), Module.finrank E Y = r → ∀ (C : Matrix (Fin r) (Fin r) E × Matrix (Fin r) (Fin r) E), Submodule.span E (Set.range fun j => ((fun a => C.1 a j), (fun a => C.2 a j))) = Y → ∀ (s : ℕ) (I : Matrix (Fin r) (Fin s) E), LinearIndependent E I.transpose → (∀ j, ((fun a => I a j), (0 : Fin r → E)) ∈ Y) → ∃ (t : ℕ) (J : Matrix (Fin r) (Fin s) E) (K : Matrix (Fin r) (Fin t) E) (L : Matrix (Fin s) (Fin r) E) (M : Matrix (Fin t) (Fin r) E), C.1 * J = I ∧ C.2 * J = 0 ∧ L * J = 1 ∧ L * K = 0 ∧ M * J = 0 ∧ M * K = 1 ∧ J * L + K * M = 1 := by
  first | exact @GlobalTheory.exists_adapted_frame_of_isotropic_columns | exact GlobalTheory.exists_adapted_frame_of_isotropic_columns | (intros; apply GlobalTheory.exists_adapted_frame_of_isotropic_columns <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralFundamentalDomainEqIteratedRationalSplit

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.CoordUnfold




theorem integral_fundamentalDomain_eq_iterated_split : ∀ (D : D7) (r m s t : ℕ) (J : Matrix (Fin r) (Fin s) D.host.E) (K : Matrix (Fin r) (Fin t) D.host.E) (L : Matrix (Fin s) (Fin r) D.host.E) (M : Matrix (Fin t) (Fin r) D.host.E), L * J = 1 → L * K = 0 → M * J = 0 → M * K = 1 → J * L + K * M = 1 → ∀ (μ : Measure (Mx D r m)) (𝓕 : Set (Mx D r m)), IsCovolOne (GlobalTheory.MixModel.ratMx D r m) μ 𝓕 → ∀ (ν : Measure (Mx D s m)) (𝓨 : Set (Mx D s m)), IsCovolOne (GlobalTheory.MixModel.ratMx D s m) ν 𝓨 → ∀ (η : Measure (Mx D t m)) (𝓥 : Set (Mx D t m)), IsCovolOne (GlobalTheory.MixModel.ratMx D t m) η 𝓥 → ∃ κ : ℝ, ∀ T : Mx D r m → ℂ, Continuous T → (∀ γ ∈ GlobalTheory.MixModel.ratMx D r m, ∀ u, T (γ + u) = T u) → ∫ u in 𝓕, T u ∂μ = κ * ∫ v in 𝓥, (∫ y in 𝓨, T (HMul.hMul (J.map (incA D)) y + HMul.hMul (K.map (incA D)) v) ∂ν) ∂η := by
  intro D r m s t J K L M hLJ hLK hMJ hMK hJLKM μ 𝓕 hμ ν 𝓨 hν η 𝓥 hη
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.MixModel.lattice_Mx D s m
  obtain ⟨j1, j2, j3, j4, j5, -⟩ := GlobalTheory.MixModel.lattice_Mx D t m
  obtain ⟨l1, l2, l3, l4, l5, KK, hKK, hKKc⟩ := GlobalTheory.MixModel.lattice_Mx D r m
  haveI : BorelSpace (Mx D s m) := ⟨rfl⟩
  haveI : BorelSpace (Mx D t m) := ⟨rfl⟩
  haveI : BorelSpace (Mx D r m) := ⟨rfl⟩
  haveI : Countable (GlobalTheory.MixModel.ratMx D s m) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI : Countable (GlobalTheory.MixModel.ratMx D t m) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI : Countable (GlobalTheory.MixModel.ratMx D r m) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI := hμ.1
  haveI := hν.1
  haveI := hη.1
  haveI : IsFiniteMeasure (ν.restrict 𝓨) := ⟨by rw [Measure.restrict_apply_univ, hν.2.2]; exact ENNReal.one_lt_top⟩
  haveI : IsFiniteMeasure (η.restrict 𝓥) := ⟨by rw [Measure.restrict_apply_univ, hη.2.2]; exact ENNReal.one_lt_top⟩
  set rJ : Mx D r s := J.map (incA D) with hrJ
  set rK : Mx D r t := K.map (incA D) with hrK
  set rL : Mx D s r := L.map (incA D) with hrL
  set rM : Mx D t r := M.map (incA D) with hrM
  have hLJ' : rL * rJ = 1 := by rw [hrL, hrJ, ← Matrix.map_mul, hLJ]; exact GlobalTheory.MixModel.rat_one
  have hLK' : rL * rK = 0 := by rw [hrL, hrK, ← Matrix.map_mul, hLK]; exact GlobalTheory.MixModel.rat_zero
  have hMJ' : rM * rJ = 0 := by rw [hrM, hrJ, ← Matrix.map_mul, hMJ]; exact GlobalTheory.MixModel.rat_zero
  have hMK' : rM * rK = 1 := by rw [hrM, hrK, ← Matrix.map_mul, hMK]; exact GlobalTheory.MixModel.rat_one
  have hJLKM' : rJ * rL + rK * rM = 1 := by
    rw [hrJ, hrL, hrK, hrM, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add (f := _), hJLKM]
    · exact GlobalTheory.MixModel.rat_one
    · exact fun a b => map_add (incA D) a b
  let Ec : (Mx D t m × Mx D s m) ≃ₜ+ Mx D r m :=
    { toFun := fun p => rJ * p.2 + rK * p.1
      invFun := fun u => (rM * u, rL * u)
      left_inv := by
        rintro ⟨v, y⟩
        simp only [Matrix.mul_add, ← Matrix.mul_assoc, hLJ', hLK', hMJ', hMK', Matrix.one_mul, Matrix.zero_mul,
          add_zero, zero_add]
      right_inv := by
        intro u
        show rJ * (rL * u) + rK * (rM * u) = u
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.add_mul, hJLKM', Matrix.one_mul]
      map_add' := by
        rintro ⟨v, y⟩ ⟨v', y'⟩
        simp only [Prod.mk_add_mk, Matrix.mul_add]
        abel
      continuous_toFun := ((continuous_const.matrix_mul continuous_snd).add (continuous_const.matrix_mul continuous_fst))
      continuous_invFun := (continuous_const.matrix_mul continuous_id).prodMk (continuous_const.matrix_mul continuous_id) }
  have hEapp : ∀ v y, Ec (v, y) = rJ * y + rK * v := fun _ _ => rfl
  let Me : (Mx D t m × Mx D s m) ≃ᵐ Mx D r m := Ec.toHomeomorph.toMeasurableEquiv
  have hMe : ∀ p, Me p = Ec p := fun _ => rfl
  set lam : Measure (Mx D t m × Mx D s m) := η.prod ν with hlam
  haveI : lam.IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  set mm : Measure (Mx D r m) := lam.map Me with hm
  haveI : mm.IsAddHaarMeasure := Ec.isAddHaarMeasure_map lam
  have hμm := Measure.isAddLeftInvariant_eq_smul μ mm
  set c := Measure.addHaarScalarFactor μ mm with hcdef
  have hc : 0 < c := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ mm
  set Γ : AddSubgroup (Mx D t m × Mx D s m) :=
    (GlobalTheory.MixModel.ratMx D t m).prod (GlobalTheory.MixModel.ratMx D s m) with hΓ
  have hmemΓ : ∀ p, p ∈ Γ ↔ Ec p ∈ GlobalTheory.MixModel.ratMx D r m := by
    rintro ⟨v, y⟩
    rw [hEapp]
    simp only [Γ, AddSubgroup.mem_prod]
    constructor
    · rintro ⟨hv, hy⟩
      exact add_mem (GlobalTheory.MixModel.ratMx_mul (GlobalTheory.MixModel.rat_mem J) hy)
        (GlobalTheory.MixModel.ratMx_mul (GlobalTheory.MixModel.rat_mem K) hv)
    · intro h
      have h1 : rM * (rJ * y + rK * v) = v := by
        simp only [Matrix.mul_add, ← Matrix.mul_assoc, hMJ', hMK', Matrix.one_mul, Matrix.zero_mul, zero_add]
      have h2 : rL * (rJ * y + rK * v) = y := by
        simp only [Matrix.mul_add, ← Matrix.mul_assoc, hLJ', hLK', Matrix.one_mul, Matrix.zero_mul, add_zero]
      refine ⟨?_, ?_⟩
      · rw [← h1]; exact GlobalTheory.MixModel.ratMx_mul (GlobalTheory.MixModel.rat_mem M) h
      · rw [← h2]; exact GlobalTheory.MixModel.ratMx_mul (GlobalTheory.MixModel.rat_mem L) h
  have hFDP : IsAddFundamentalDomain Γ (𝓥 ×ˢ 𝓨) lam := isAddFundamentalDomain_prod hη.2.1 hν.2.1
  have hac : lam.map Me ≪ μ := by
    intro A hA
    rw [hμm, Measure.smul_apply] at hA
    exact (smul_eq_zero.1 hA).resolve_left hc.ne'
  have hqmp : Measure.QuasiMeasurePreserving Me lam μ := ⟨Me.measurable.aemeasurable, hac⟩
  let eΓ : GlobalTheory.MixModel.ratMx D r m → Γ := fun g => ⟨Ec.symm g, (hmemΓ _).2 (by simpa using g.2)⟩
  have heΓ : Function.Bijective eΓ := by
    refine ⟨fun g g' h => Subtype.ext ?_, fun p => ⟨⟨Ec p, (hmemΓ p).1 p.2⟩, Subtype.ext ?_⟩⟩
    · have := congrArg (fun q : Γ => Ec q.1) h
      simpa [eΓ] using this
    · simp [eΓ]
  haveI : Countable Γ := heΓ.2.countable
  have hFDE : IsAddFundamentalDomain Γ (Me ⁻¹' 𝓕) lam :=
    hμ.2.1.preimage_of_equiv hqmp heΓ (fun g p => by
      show Me ((Ec.symm g : _) + p) = (g : Mx D r m) + Me p
      rw [hMe, hMe, map_add (f := _), Ec.apply_symm_apply])
  refine ⟨(c : ℝ), fun T hT hper => ?_⟩
  obtain ⟨C, hC⟩ := hKK.exists_bound_of_continuousOn hT.continuousOn
  have hbd : ∀ x, ‖T x‖ ≤ C := fun x => by
    obtain ⟨γ, hγ, hx⟩ := hKKc x
    rw [← hper γ hγ x]
    exact hC _ hx
  have hTE : Continuous fun p => T (Me p) := hT.comp Ec.continuous
  have e1 : ∫ u in 𝓕, T u ∂μ = (c : ℝ) • ∫ u in 𝓕, T u ∂mm := by
    rw [hμm, Measure.restrict_smul, integral_smul_nnreal_measure, NNReal.smul_def]
  have e2 : ∫ u in 𝓕, T u ∂mm = ∫ p in Me ⁻¹' 𝓕, T (Me p) ∂lam := setIntegral_map_equiv Me T 𝓕
  have e3 : ∫ p in Me ⁻¹' 𝓕, T (Me p) ∂lam = ∫ p in 𝓥 ×ˢ 𝓨, T (Me p) ∂lam :=
    hFDE.setIntegral_eq hFDP (fun g p => by
      show T (Me ((g : _) + p)) = T (Me p)
      rw [hMe, hMe, map_add (f := _)]
      exact hper _ ((hmemΓ _).1 g.2) _)
  have e4 : lam.restrict (𝓥 ×ˢ 𝓨) = (η.restrict 𝓥).prod (ν.restrict 𝓨) := by
    rw [Measure.prod_restrict]
  rw [e1, e2, e3, e4, integral_prod _ (Integrable.of_bound hTE.aestronglyMeasurable C (ae_of_all _ fun p => hbd _)),
    Complex.real_smul]
  rfl

end GlobalTheory.CoordUnfold

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralFundamentalDomainEqIteratedRationalSplitStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift


theorem _root_.GlobalTheory.T.integral_fundamentalDomain_eq_iterated_rationalSplitting : ∀ (D : D7) (r m s t : ℕ) (J : Matrix (Fin r) (Fin s) D.host.E) (K : Matrix (Fin r) (Fin t) D.host.E) (L : Matrix (Fin s) (Fin r) D.host.E) (M : Matrix (Fin t) (Fin r) D.host.E), L * J = 1 → L * K = 0 → M * J = 0 → M * K = 1 → J * L + K * M = 1 → ∀ (μ : Measure (Mx D r m)) (𝓕 : Set (Mx D r m)), IsCovolOne (GlobalTheory.MixModel.ratMx D r m) μ 𝓕 → ∀ (ν : Measure (Mx D s m)) (𝓨 : Set (Mx D s m)), IsCovolOne (GlobalTheory.MixModel.ratMx D s m) ν 𝓨 → ∀ (η : Measure (Mx D t m)) (𝓥 : Set (Mx D t m)), IsCovolOne (GlobalTheory.MixModel.ratMx D t m) η 𝓥 → ∃ κ : ℝ, ∀ T : Mx D r m → ℂ, Continuous T → (∀ γ ∈ GlobalTheory.MixModel.ratMx D r m, ∀ u, T (γ + u) = T u) → ∫ u in 𝓕, T u ∂μ = κ * ∫ v in 𝓥, (∫ y in 𝓨, T (HMul.hMul (J.map (incA D)) y + HMul.hMul (K.map (incA D)) v) ∂ν) ∂η := by
  first | exact @GlobalTheory.CoordUnfold.integral_fundamentalDomain_eq_iterated_split | exact GlobalTheory.CoordUnfold.integral_fundamentalDomain_eq_iterated_split | (intros; apply GlobalTheory.CoordUnfold.integral_fundamentalDomain_eq_iterated_split <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DoubledLagrangianTermDependsOnlyOnIsotropicMeans

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section
namespace GlobalTheory.LagMeans



theorem lagTerm_eq_of_means : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V W : HSp D) (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), IsCovolOne (ratL W V) μ 𝓕 → ∀ (Y : Lag W) (C : Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E), IsLagFrame W Y C → ∀ (s : ℕ) (I : Matrix (Fin W.rank) (Fin s) D.host.E), IsIsoFrame W I → Submodule.span D.host.E (Set.range I.transpose) = Y.1.comap (LinearMap.inl D.host.E _ _) → ∀ (ν : Measure (Mx D s V.rank)) (𝓨 : Set (Mx D s V.rank)), IsCovolOne (GlobalTheory.MixModel.ratMx D s V.rank) ν 𝓨 → ∀ f₁ f₁' f₂ : WO V W → ℂ, IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₁' → IsThetaFunO ψ V W f₂ → (∀ x : WO V W, HMul.hMul ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) I * W.gram).map (incA D)) x = (0 : Mx D s V.rank) → ∫ y in 𝓨, f₁ (HMul.hMul (I.map (incA D)) y + x) ∂ν = ∫ y in 𝓨, f₁' (HMul.hMul (I.map (incA D)) y + x) ∂ν) → lagTerm μ 𝓕 C f₁ f₂ = lagTerm μ 𝓕 C f₁' f₂ := by
  intro D ψ hψ V W μ 𝓕 hμ Y C hC s I hI hspan ν 𝓨 hν f₁ f₁' f₂ h₁ h₁' h₂ hmean
  have hmem : ∀ j, ((fun a => I a j), (0 : Fin W.rank → D.host.E)) ∈ Y.1 := fun j => by
    have : (fun a => I a j) ∈ Y.1.comap (LinearMap.inl D.host.E _ _) := hspan ▸ Submodule.subset_span ⟨j, rfl⟩
    exact this
  have mcol : ∀ k, ((fun a => C.1 a k), (fun a => C.2 a k)) ∈ Y.1 := fun k => hC ▸ Submodule.subset_span ⟨k, rfl⟩
  obtain ⟨t, J, K, L, M, e1, e2, e3, e4, e5, e6, e7⟩ := GlobalTheory.T.exists_adapted_frame_of_isotropic_columns' D.host.E W.rank Y.1 Y.2.1 C hC s I hI.2.1 hmem
  obtain ⟨η, 𝓥, hη⟩ := GlobalTheory.MixModel.exists_isCovolOne D t V.rank
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.integral_fundamentalDomain_eq_iterated_rationalSplitting D W.rank V.rank s t J K L M e3 e4 e5 e6 e7 μ 𝓕 hμ ν 𝓨 hν η 𝓥 hη
  have hB : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) I * W.gram * C.1 = 0 := by
    rw [Matrix.mul_assoc]
    funext j k
    have := Y.2.2 _ (hmem j) _ (mcol k)
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Pi.zero_apply, star_zero, zero_mul, Finset.sum_const_zero] at this
    simpa only [Matrix.mul_apply, GlobalTheory.MixModel.cT_sig, Matrix.conjTranspose_apply, Matrix.zero_apply] using this
  have hψ' : ∀ x, ‖ψ x‖ = 1 := hψ.1.2.1
  have per : ∀ f, IsThetaFunO ψ V W f → ∀ γ ∈ GlobalTheory.MixModel.ratMx D W.rank V.rank, ∀ u : Mx D W.rank V.rank,
      f (ratMul C.1 (γ + u)) * star (f₂ (ratMul C.2 (γ + u))) = f (ratMul C.1 u) * star (f₂ (ratMul C.2 u)) := by
    rintro f hf _ ⟨γ, rfl⟩ u
    exact GlobalTheory.RawLift.Model.integrand_periodic hψ' hC hf h₂ γ u
  have cont : ∀ f, IsThetaFunO ψ V W f → Continuous fun u : Mx D W.rank V.rank => f (ratMul C.1 u) * star (f₂ (ratMul C.2 u)) :=
    fun f hf => (hf.cont.comp (continuous_const.matrix_mul continuous_id)).mul
      (continuous_star.comp (h₂.cont.comp (continuous_const.matrix_mul continuous_id)))
  unfold lagTerm
  rw [hκ _ (cont f₁ h₁) (per f₁ h₁), hκ _ (cont f₁' h₁') (per f₁' h₁')]
  congr 1
  congr 1
  funext v
  have r1 : ∀ y : Mx D s V.rank, ratMul C.1 (HMul.hMul (J.map (incA D)) y + HMul.hMul (K.map (incA D)) v) =
      HMul.hMul (I.map (incA D)) y + HMul.hMul ((C.1 * K).map (incA D)) v := fun y => by
    unfold ratMul
    rw [Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.map_mul, ← Matrix.map_mul, e1]
  have r2 : ∀ y : Mx D s V.rank, ratMul C.2 (HMul.hMul (J.map (incA D)) y + HMul.hMul (K.map (incA D)) v) =
      HMul.hMul ((C.2 * K).map (incA D)) v := fun y => by
    unfold ratMul
    rw [Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.map_mul, ← Matrix.map_mul, e2,
      Matrix.map_zero (incA D) (map_zero (incA D))]
    simp only [Matrix.zero_mul, zero_add]
  simp only [r1, r2]
  rw [integral_mul_const, integral_mul_const]
  congr 1
  refine hmean _ ?_
  rw [← Matrix.mul_assoc, ← Matrix.map_mul, ← Matrix.mul_assoc, hB, Matrix.zero_mul, Matrix.map_zero (incA D) (map_zero (incA D))]
  exact Matrix.zero_mul _

end GlobalTheory.LagMeans
end
end
end
