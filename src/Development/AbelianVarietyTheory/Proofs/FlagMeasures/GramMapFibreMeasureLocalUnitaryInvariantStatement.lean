module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FibreFamilyUnique
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.CjDefs
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.BVRApply
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.GlGeneratedTransvectionsDiag
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.NnrealEqOneOfMulSelf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.TraceGramNondegenerate
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.UniHaar
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAF
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.MapPhiOfModM
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalUnitaryGroupTuplesTopologicalFacts
import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.LevelIntersectParabolic
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalUnitaryGroupTupleHaarInvariant

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

noncomputable section

namespace GlobalTheory.LocalUnitaryHaar

open PI.VolSemiDirect.W.Cj Measure
open scoped NNReal Matrix

theorem stableRankOne_field (K : Type) [Field K] : HasStableRangeOne K := by
  intro a b x y h
  by_cases ha : a = 0
  · refine ⟨1, ?_⟩
    subst ha
    have hb : b ≠ 0 := by
      rintro rfl
      simp at h
    simpa using isUnit_iff_ne_zero.2 hb
  · exact ⟨0, by simpa using isUnit_iff_ne_zero.2 ha⟩

theorem map_mulVec_eq_of_preserves_form {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [LocallyCompactSpace A] [SecondCountableTopology A] [T2Space A] [MeasurableSpace A]
    [BorelSpace A] (hA : HasStableRangeOne A) (k : ℕ) (G X : Matrix (Fin k) (Fin k) A)
    (hG : IsUnit G.det) (hXG : X.transpose * G * X = G)
    (μ : Measure (Fin k → A)) [μ.IsAddHaarMeasure] : μ.map X.mulVec = μ := by
  have hd := congrArg Matrix.det hXG
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at hd
  have hdd : X.det * X.det = 1 := by
    have : (X.det * X.det) * G.det = 1 * G.det := by
      calc (X.det * X.det) * G.det = X.det * G.det * X.det := by ring
        _ = 1 * G.det := by rw [hd, one_mul]
    exact hG.mul_left_inj.1 this
  have hX : IsUnit X.det := ⟨⟨X.det, X.det, hdd, hdd⟩, rfl⟩
  let Xu : GL (Fin k) A := Matrix.nonsingInvUnit X hX
  let Gu : GL (Fin k) A := Matrix.nonsingInvUnit G hG
  have hrel : trG Xu * Gu * Xu = Gu := by
    ext1
    exact hXG
  have hm := congrArg modM hrel
  rw [modM_mul, modM_mul, modM_tr_of_mem transvection_preserves_haar Xu (gl_generated_transvections_diag A hA k Xu)] at hm
  have hpos : 0 < modM Gu := addEquivAddHaarChar_pos (phi Gu)
  have hsq : modM Xu * modM Xu = 1 := by
    have : (modM Xu * modM Xu) * modM Gu = 1 * modM Gu := by
      calc (modM Xu * modM Xu) * modM Gu = modM Xu * modM Gu * modM Xu := by ring
        _ = 1 * modM Gu := by rw [hm, one_mul]
    exact mul_right_cancel₀ hpos.ne' this
  have hmod := nnreal_eq_one_of_mul_self hsq
  have e := map_phi_of_modM Xu hmod μ
  have e2 : (phi Xu : (Fin k → A) → (Fin k → A)) = Matrix.mulVec X := by
    funext v
    rfl
  rw [e2] at e
  exact e

theorem map_lin_eq_of_stableRankOne (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
    (hJ : IsHermND σ J) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R]
    [MeasurableSpace R] [BorelSpace R] (hR1 : HasStableRangeOne R) (g : HA R σ J)
    (μ : Measure (Fin M → R ⊗[F] E)) [μ.IsAddHaarMeasure] :
    μ.map (lin R σ J g) = μ := by
  classical
  have : FiniteDimensional F E := Module.finite_of_finrank_eq_succ hCM.2.2.1
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (R ⊗[F] E) := IsModuleTopology.isTopologicalRing R _
  obtain ⟨eh⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) R
  haveI : LocallyCompactSpace (R ⊗[F] E) := eh.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (R ⊗[F] E) := eh.secondCountableTopology
  haveI : T2Space (R ⊗[F] E) := eh.isEmbedding.t2Space
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  set k := Fintype.card (Σ _ : Fin M, Fin (Module.finrank F E))
  set b := bV F E M
  set bR := bVR F E M R
  set e : (Fin M → R ⊗[F] E) ≃ₗ[R] (Fin k → R) := bR.equivFun
  have c1 : Continuous e.toLinearMap := IsModuleTopology.continuous_of_linearMap (R := R) _
  have c2 : Continuous e.symm.toLinearMap :=
    IsModuleTopology.continuous_of_linearMap (R := R) _
  let ec : (Fin M → R ⊗[F] E) ≃ₜ+ (Fin k → R) :=
    { e.toAddEquiv with
      continuous_toFun := by simpa using c1
      continuous_invFun := by simpa using c2 }
  have hec : ∀ u, ec u = e u := fun _ => rfl
  have hecs : ∀ x, ec.symm x = e.symm x := fun _ => rfl
  set μ' := μ.map ec
  have hμ' : μ'.IsAddHaarMeasure := ec.isAddHaarMeasure_map μ
  let L : (Fin k → R) →ₗ[R] (Fin k → R) :=
    e.toLinearMap ∘ₗ ((lin R σ J g).restrictScalars R) ∘ₗ e.symm.toLinearMap
  set X := LinearMap.toMatrix' L
  have hX : ∀ x, X.mulVec x = e (lin R σ J g (e.symm x)) := fun x =>
    LinearMap.toMatrix'_mulVec L x
  set G0 : Matrix (Fin k) (Fin k) F := Matrix.of fun i j => Algebra.trace F E (hE σ J (b i) (b j))
  set G := G0.map (algebraMap F R)
  have hGu : IsUnit G.det := by
    have hd : G.det = algebraMap F R G0.det := by
      rw [RingHom.map_det]
      rfl
    rw [hd]
    exact (isUnit_iff_ne_zero.2 (trace_gram_nondegenerate F E σ hCM M J hJ k b)).map _
  have hBG : ∀ i j, Bf σ J (bR i) (bR j) = G i j := by
    intro i j
    rw [bVR_apply, bVR_apply, Bf, trace_basis_holds F E R σ M J]
    rfl
  have key : ∀ x y : Fin k → R, Bf σ J (e.symm x) (e.symm y) = x ⬝ᵥ (G *ᵥ y) := by
    intro x y
    rw [Module.Basis.equivFun_symm_apply, Module.Basis.equivFun_symm_apply, Bf_expand]
    simp only [hBG, dotProduct, Matrix.mulVec, Finset.mul_sum]
    rfl
  have e1 : ∀ u w : Fin k → R, u ⬝ᵥ ((X.transpose * G * X) *ᵥ w) = u ⬝ᵥ (G *ᵥ w) := by
    intro u w
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      Matrix.vecMul_transpose, ← key, hX, hX, LinearEquiv.symm_apply_apply,
      LinearEquiv.symm_apply_apply, Bf_lin, key]
  have hXG : X.transpose * G * X = G := by
    ext i j
    simpa using e1 (Pi.single i 1) (Pi.single j 1)
  have hinv := map_mulVec_eq_of_preserves_form hR1 k G X hGu hXG μ'
  have hlin : (lin R σ J g : (Fin M → R ⊗[F] E) → (Fin M → R ⊗[F] E)) =
      ec.symm ∘ X.mulVec ∘ ec := by
    funext u
    simp only [Function.comp_apply, hec, hecs, hX, LinearEquiv.symm_apply_apply]
  have mec : Measurable ec := ec.continuous.measurable
  have mecs : Measurable ec.symm := ec.symm.continuous.measurable
  have mX : Measurable X.mulVec := (continuous_const.matrix_mulVec continuous_id).measurable
  rw [hlin, ← Measure.map_map mecs (mX.comp mec), ← Measure.map_map mX mec, hinv,
    Measure.map_map mecs mec]
  have : (ec.symm ∘ ec : (Fin M → R ⊗[F] E) → _) = id := by
    funext u
    simp
  rw [this, Measure.map_id]

theorem haar_tuple_invariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ (a : ℕ) (μ : Measure (Fin a → Fin n → Fv F v ⊗[F] E)), μ.IsAddHaarMeasure → ∀ g : HA (Fv F v) σ J, μ.map (fun X => g • X) = μ := by
  intro F E _ _ _ _ _ σ hCM n J hJ v a μ hμ g
  have := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F v
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  have : FiniteDimensional F E := Module.finite_of_finrank_eq_succ hCM.2.2.1
  haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Fv F v ⊗[F] E) := IsModuleTopology.isTopologicalRing (Fv F v) _
  obtain ⟨eh⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (Fv F v)
  haveI : LocallyCompactSpace (Fv F v ⊗[F] E) := eh.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (Fv F v ⊗[F] E) := eh.secondCountableTopology
  haveI : T2Space (Fv F v ⊗[F] E) := eh.isEmbedding.t2Space
  haveI : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  let ν : Measure (Fin n → Fv F v ⊗[F] E) := addHaar
  have hmeas : Measurable (lin (Fv F v) σ J g : (Fin n → Fv F v ⊗[F] E) → _) :=
    (continuous_const.matrix_mulVec continuous_id).measurable
  have hν : ∀ _ : Fin a, MeasurePreserving (lin (Fv F v) σ J g : (Fin n → Fv F v ⊗[F] E) → _) ν ν :=
    fun _ => ⟨hmeas, map_lin_eq_of_stableRankOne F E σ hCM n J hJ (Fv F v) (stableRankOne_field _) g ν⟩
  have hpi := measurePreserving_pi (fun _ : Fin a => ν) (fun _ => ν) hν
  have e1 : (fun X : Fin a → Fin n → Fv F v ⊗[F] E => g • X) =
      fun X i => lin (Fv F v) σ J g (X i) := rfl
  rw [isAddLeftInvariant_eq_smul μ (Measure.pi fun _ : Fin a => ν), Measure.map_smul, e1,
    hpi.map_eq]
  rw [e1]
  exact hpi.measurable.aemeasurable

end GlobalTheory.LocalUnitaryHaar
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalUnitaryGroupTupleHaarInvariantStatement

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

theorem _root_.GlobalTheory.T.localUnitaryGroup_tuple_haar_invariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ (a : ℕ) (μ : Measure (Fin a → Fin n → Fv F v ⊗[F] E)), μ.IsAddHaarMeasure → ∀ g : HA (Fv F v) σ J, μ.map (fun X => g • X) = μ := by
  first | exact @GlobalTheory.LocalUnitaryHaar.haar_tuple_invariant | exact GlobalTheory.LocalUnitaryHaar.haar_tuple_invariant | (intros; apply GlobalTheory.LocalUnitaryHaar.haar_tuple_invariant <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramMapFibreMeasureLocalUnitaryInvariant

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

namespace GlobalTheory.LocalFibreInvariant

theorem fibre_invariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ a : ℕ, ∀ (μ : Measure (Fin a → Fin n → Fv F v ⊗[F] E)) (ν : Measure (HermR (Fv F v) σ a)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → ∀ fib : HermR (Fv F v) σ a → Measure (Fin a → Fin n → Fv F v ⊗[F] E), IsFibreFamily μ (gramR (Fv F v) σ J) Subtype.val {X | LinearIndependent (Fv F v ⊗[F] E) X} ν Set.univ fib → ∀ (S : HermR (Fv F v) σ a) (g : HA (Fv F v) σ J), (fib S).map (fun X => g • X) = fib S := by
  intro F E _ _ _ _ _ σ hCM n J hJ v a μ ν hμ hν fib hfib S g
  obtain ⟨-, -, -, h4, -, -, -, -, ha⟩ := GlobalTheory.LocalUnitaryTop.top_facts F E σ hCM n J hJ v
  obtain ⟨-, hact⟩ := ha a
  haveI := h4
  haveI : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  have hc : ∀ k : HA (Fv F v) σ J,
      Continuous (fun X : Fin a → Fin n → Fv F v ⊗[F] E => k • X) :=
    fun k => hact.comp (Continuous.prodMk continuous_const continuous_id)
  let T : (Fin a → Fin n → Fv F v ⊗[F] E) ≃ₜ (Fin a → Fin n → Fv F v ⊗[F] E) :=
    { toFun := fun X => g • X
      invFun := fun X => g⁻¹ • X
      left_inv := fun X => inv_smul_smul g X
      right_inv := fun X => smul_inv_smul g X
      continuous_toFun := hc g
      continuous_invFun := hc g⁻¹ }
  let Tm := T.toMeasurableEquiv
  have hTm : ∀ X, Tm X = g • X := fun X => rfl
  have hgram : ∀ X : Fin a → Fin n → Fv F v ⊗[F] E,
      gramR (Fv F v) σ J (g • X) = gramR (Fv F v) σ J X := by
    intro X
    funext i j
    exact hR_lin g (X i) (X j)
  have hli : ∀ (k : HA (Fv F v) σ J) (X : Fin a → Fin n → Fv F v ⊗[F] E),
      LinearIndependent (Fv F v ⊗[F] E) X → LinearIndependent (Fv F v ⊗[F] E) (k • X) := by
    intro k X hX
    have hinj : Function.Injective (lin (Fv F v) σ J k) :=
      Function.LeftInverse.injective (g := lin (Fv F v) σ J k⁻¹) (fun x => lin_inv_lin (g := k) (x := x))
    exact hX.map' (lin (Fv F v) σ J k) (LinearMap.ker_eq_bot.mpr hinj)
  have hpre : ∀ b : HermR (Fv F v) σ a,
      Tm ⁻¹' (gramR (Fv F v) σ J ⁻¹' {Subtype.val b} ∩ {X | LinearIndependent (Fv F v ⊗[F] E) X}) =
        gramR (Fv F v) σ J ⁻¹' {Subtype.val b} ∩ {X | LinearIndependent (Fv F v ⊗[F] E) X} := by
    intro b
    ext X
    simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_setOf_eq, hTm, hgram]
    refine and_congr_right fun _ => ⟨fun h => ?_, hli g X⟩
    have := hli g⁻¹ _ h
    rwa [inv_smul_smul] at this
  have hU : Tm ⁻¹' {X | LinearIndependent (Fv F v ⊗[F] E) X} =
      {X | LinearIndependent (Fv F v ⊗[F] E) X} := by
    ext X
    simp only [Set.mem_preimage, Set.mem_setOf_eq, hTm]
    refine ⟨fun h => ?_, hli g X⟩
    have := hli g⁻¹ _ h
    rwa [inv_smul_smul] at this
  have hμT : μ.map Tm = μ := GlobalTheory.T.localUnitaryGroup_tuple_haar_invariant F E σ hCM n J hJ v a μ hμ g
  let fib' : HermR (Fv F v) σ a → Measure (Fin a → Fin n → Fv F v ⊗[F] E) := fun b => (fib b).map Tm
  have hfib' : IsFibreFamily μ (gramR (Fv F v) σ J) Subtype.val
      {X | LinearIndependent (Fv F v ⊗[F] E) X} ν Set.univ fib' := by
    refine ⟨fun b => ?_, fun φ hφ => ?_, fun φ hφc hφs hφU => ?_⟩
    · show (fib b).map Tm _ = 0
      rw [Tm.map_apply, Set.preimage_compl, hpre]
      exact hfib.1 b
    · have e1 : ∀ b, ∫⁻ x, φ x ∂(fib' b) = ∫⁻ x, φ (Tm x) ∂(fib b) := fun b =>
        lintegral_map_equiv φ Tm (μ := fib b)
      simp only [e1]
      rw [← hfib.2.1 (fun x => φ (Tm x)) (hφ.comp Tm.measurable)]
      conv_lhs => rw [← hμT]
      rw [Tm.restrict_map, lintegral_map_equiv, hU]
    · have h3 := hfib.2.2 (φ ∘ Tm) (hφc.comp T.continuous) (hφs.comp_homeomorph T) (by
        show tsupport (φ ∘ T) ⊆ _
        rw [tsupport_comp_eq_preimage φ T]
        intro X hX
        have : Tm X ∈ {X | LinearIndependent (Fv F v ⊗[F] E) X} := hφU hX
        rw [← Set.mem_preimage, hU] at this
        exact this)
      refine ⟨fun b hb => (integrable_map_equiv Tm φ).mpr (h3.1 b hb), ?_⟩
      refine h3.2.congr fun b _ => ?_
      exact MeasureTheory.integral_map_equiv Tm φ
  have hu := GlobalTheory.LocalFibreUnique.fibre_family_unique F E σ hCM n J hJ v a μ ν hμ hν fib hfib fib' hfib'
  show (fib S).map Tm = fib S
  exact (congrFun hu S).symm

end GlobalTheory.LocalFibreInvariant
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramMapFibreMeasureLocalUnitaryInvariantStatement

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

theorem _root_.GlobalTheory.T.gramMap_fibreMeasure_localUnitary_invariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ a : ℕ, ∀ (μ : Measure (Fin a → Fin n → Fv F v ⊗[F] E)) (ν : Measure (HermR (Fv F v) σ a)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → ∀ fib : HermR (Fv F v) σ a → Measure (Fin a → Fin n → Fv F v ⊗[F] E), IsFibreFamily μ (gramR (Fv F v) σ J) Subtype.val {X | LinearIndependent (Fv F v ⊗[F] E) X} ν Set.univ fib → ∀ (S : HermR (Fv F v) σ a) (g : HA (Fv F v) σ J), (fib S).map (fun X => g • X) = fib S := by
  first | exact @GlobalTheory.LocalFibreInvariant.fibre_invariant | exact GlobalTheory.LocalFibreInvariant.fibre_invariant | (intros; apply GlobalTheory.LocalFibreInvariant.fibre_invariant <;> assumption)
end
end
