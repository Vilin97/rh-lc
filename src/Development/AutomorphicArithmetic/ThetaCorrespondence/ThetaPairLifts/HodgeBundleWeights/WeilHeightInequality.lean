module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsModelOf
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.VuSelfKnownTheorem
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalProjectiveModel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.VolumeLeSelfIntersection
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeightIffOfDegreeEq
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsHomOpenPart
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfIsGenerated
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XXgzHeightRVolUpModelNef
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.ValFFromSpecStalk
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.ValFUnitNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
public import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Algebra.Order.Star.Real
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.TotallySplit
import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernLeviEqConstant
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OnbPerp
import Mathlib.Algebra.Azumaya.Basic

-- Source module: Development.WeilBound.CoreStatements.HomogeneousNonvanishing.MulEqOneOfComb

section

@[expose] public section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CxPts GlobalTheory.ZH GlobalTheory.ZH.RatModel GlobalTheory.CompHt

namespace PositivityTheory.UnitarySelfGeneration.UnitProductCombination

theorem mul_eq_one_of_comb {K V : Type} [Field K] [AddCommGroup V] [Module K V] {N n : ℕ}
    (b : Module.Basis (Fin N) K V) (g : Matrix (Fin N) (Fin n) K) (c : Matrix (Fin n) (Fin N) K)
    (h : ∀ j, b j = ∑ k, c k j • ∑ i, g i k • b i) : g * c = 1 := by
  ext i j
  have e := congrArg (fun v => b.repr v i) (h j)

  simp only [map_sum, map_smul, Module.Basis.repr_self, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_smul,
  Pi.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
  Finset.mem_univ, if_true] at e
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [mul_comm (g i _), ← e, eq_comm]

theorem sum_eq {K : Type} [Field K] (σ : K →+* ℂ) {N n : ℕ} {g : Matrix (Fin N) (Fin n) K}
    {c : Matrix (Fin n) (Fin N) K} (h : g * c = 1) (A : Matrix (Fin N) (Fin N) ℂ) (x : Fin N → ℂ) (a : Fin N) :
    ∑ k, (∑ m, σ (c k m) * A m a) * ∑ j, σ (g j k) * x j = ∑ m, A m a * x m := by
  have e : ∀ j m, ∑ k, σ (g j k) * σ (c k m) = if j = m then 1 else 0 := fun j m => by
    have := congrArg σ (congrFun (congrFun h j) m)

    rw [Matrix.mul_apply, map_sum, Matrix.one_apply, apply_ite σ, map_one, map_zero] at this
    simpa only [map_mul] using this
  calc ∑ k, (∑ m, σ (c k m) * A m a) * ∑ j, σ (g j k) * x j
      = ∑ j, ∑ m, (∑ k, σ (g j k) * σ (c k m)) * (A m a * x j) := by
        simp only [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
    _ = _ := by simp [e]

theorem isometric_fs {K V Ω : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] (M : RatModel (𝓞 K) Ω) (L : HermLB M.s)
    (ev : V →ₗ[K] Ω) {W : Submodule (𝓞 K) V} (s : W → L.B.Sec) {e : L.B.ι → Ω}
    (hv : ∀ w : W, M.HasVal e (s w) (ev w)) (hW : Submodule.span K (W : Set V) = ⊤) {N n : ℕ}
    (b : Module.Basis (Fin N) K V) (g : Matrix (Fin N) (Fin n) K) (A : (K →+* ℂ) → Matrix (Fin N) (Fin N) ℂ)
    (c : Matrix (Fin n) (Fin N) K) (gw : Fin n → W) (hgw : ∀ k, (gw k : V) = ∑ j, g j k • b j)
    (hcb : ∀ j, b j = ∑ k, c k j • (gw k : V))
    (hφ : ∀ (σ : K →+* ℂ) (i : L.B.ι) (y : CxPts M.s (σ.comp (algebraMap (𝓞 K) K))),
      (L.φ (σ.comp (algebraMap (𝓞 K) K))).φ i y =
        Real.log (∑ a, ‖∑ k, (∑ m, σ (c k m) * A σ m a) * valR y.1 (L.B.U i) ((s (gw k)).f i)‖ ^ 2))
    (hs : ⨆ k, nonzeroLocus (s (gw k)) = ⊤) (Mt : (𝓞 K →+* ℂ) → Matrix (Fin n) (Fin n) ℂ) (hdet hcc)
    (hMt : ∀ (σ : K →+* ℂ) (x : Fin N → ℂ),
      ∑ a, ‖∑ k, Mt (σ.comp (algebraMap (𝓞 K) K)) k a * ∑ j, σ (g j k) * x j‖ ^ 2 = GlobalTheory.Adelic.archSize (A σ) x ^ 2)
    (t : ℝ) :
    ((HermLB.fs M.s L.isLB (fun k => s (gw k)) hs Mt hdet hcc).shift (fun _ => t) (fun _ => rfl)).Isometric
      (L.shift (fun _ => t) (fun _ => rfl)) := by
  have hgc := mul_eq_one_of_comb b g c fun j => by simpa only [hgw] using hcb j
  refine HermLB.isometric_of_eqOn fun σ' l y hl => ?_
  obtain ⟨σ, rfl⟩ : ∃ σ : K →+* ℂ, σ.comp (algebraMap (𝓞 K) K) = σ' := ⟨_, GlobalTheory.TrueGeo.OfLattice.extEmb_comp σ'⟩
  replace hl : y ∈ ptsIn M.s _ (L.B.U l) := hl
  have hz := mem_ptsIn.1 hl
  obtain ⟨x, hx⟩ := PositivityTheory.Xgn.A_xgz_height_r_vol_up_model_nef.exists_coord y.2 ev (e l) b hW fun v hvW => by
    rw [← hv ⟨v, hvW⟩ l ⟨_, hz⟩]
    exact valF_mem_O hz _
  have hr : Set.range y.1 ⊆ L.B.U l := (GlobalTheory.ZH.top_le_preimage_iff _ _).1 hl
  have hsk : ∀ k, valR y.1 (L.B.U l) ((s (gw k)).f l) = ∑ j, σ (g j k) * x j := fun k => by
    refine ((val_eq hr (hv (gw k) l ⟨_, hz⟩)).symm.trans (hx _)).trans ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hgw, b.repr_sum_self]
  refine congrArg (· + 2 * t) ((hφ σ l y).trans (Eq.trans ?_
    (Weight.fsBasis_φ L.isLB (fun k => s (gw k)) hs _ (hdet _) l y).symm))
  simp only [hsk, hMt, sum_eq σ hgc]
  rw [GlobalTheory.Adelic.archSize, Real.sq_sqrt (by positivity)]

end PositivityTheory.UnitarySelfGeneration.UnitProductCombination
end
end

-- Source module: Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XXgzHeightRVolUpModelMat

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

namespace PositivityTheory.Xgn.A_xgz_height_r_vol_up_model_mat

theorem exists_ext (K : Type) [Field K] [NumberField K] (τ : 𝓞 K →+* ℂ) :
    ∃ σ : K →+* ℂ, σ.comp (algebraMap (𝓞 K) K) = τ := by
  have hinj : Function.Injective τ := by
    rw [RingHom.injective_iff_ker_eq_bot]
    apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
    have h : Function.Injective (τ.comp (algebraMap ℤ (𝓞 K))) := RingHom.injective_int _
    rw [RingHom.injective_iff_ker_eq_bot] at h
    exact (RingHom.comap_ker τ (algebraMap ℤ (𝓞 K))).trans h
  refine ⟨IsFractionRing.lift (A := 𝓞 K) (K := K) (L := ℂ) (g := τ) hinj, ?_⟩
  ext x
  exact IsFractionRing.lift_algebraMap (K := K) hinj x

theorem ext_unique (K : Type) [Field K] [NumberField K] {σ σ' : K →+* ℂ}
    (h : σ.comp (algebraMap (𝓞 K) K) = σ'.comp (algebraMap (𝓞 K) K)) : σ = σ' :=
  IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 K)) h

theorem unitary_of_norm {N : ℕ} (W : Matrix (Fin N) (Fin N) ℂ)
    (h : ∀ y : Fin N → ℂ, Real.sqrt (∑ i, ‖W.mulVec y i‖ ^ 2) = Real.sqrt (∑ i, ‖y i‖ ^ 2)) :
    W ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  have h1 : ∀ y : EuclideanSpace ℂ (Fin N), ‖Matrix.toEuclideanLin W y‖ = ‖y‖ := fun y => by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    exact h y.ofLp
  have h2 := (LinearMap.norm_map_iff_inner_map_map (Matrix.toEuclideanLin W)).1 h1
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  have := h2 (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
  rw [EuclideanSpace.inner_single_left] at this
  simp only [PiLp.inner_apply] at this
  simpa [Matrix.mul_apply, Matrix.one_apply, Matrix.toEuclideanLin, mul_comm, eq_comm] using this

theorem exists_unitary {N : ℕ} (A B : Matrix (Fin N) (Fin N) ℂ) (hA : A.det ≠ 0) (hB : B.det ≠ 0)
    (h : ∀ x : Fin N → ℂ, GlobalTheory.ChowHt.frameNorm B (fun j => (starRingEnd ℂ) (x j)) = GlobalTheory.ChowHt.frameNorm A x) :
    ∃ U ∈ Matrix.unitaryGroup (Fin N) ℂ, B = A.map (starRingEnd ℂ) * U := by
  have hW : B⁻¹ * A.map (starRingEnd ℂ) ∈ Matrix.unitaryGroup (Fin N) ℂ := by
    refine unitary_of_norm _ fun y => ?_
    have := h (A.mulVec fun j => (starRingEnd ℂ) (y j))
    unfold GlobalTheory.ChowHt.frameNorm at this
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hA.isUnit, Matrix.one_mulVec] at this
    have e : (fun j => (starRingEnd ℂ) (A.mulVec (fun j => (starRingEnd ℂ) (y j)) j)) =
        (A.map (starRingEnd ℂ)).mulVec y := by
      funext j
      simp [Matrix.mulVec, dotProduct]
    rw [e, Matrix.mulVec_mulVec] at this
    simpa using this
  refine ⟨star (B⁻¹ * A.map (starRingEnd ℂ)), Unitary.star_mem hW, ?_⟩
  have h1 := Matrix.mem_unitaryGroup_iff.1 hW
  calc B = B * ((B⁻¹ * A.map (starRingEnd ℂ)) * star (B⁻¹ * A.map (starRingEnd ℂ))) := by rw [h1, mul_one]
    _ = _ := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hB.isUnit, Matrix.one_mul]

theorem exists_P {K : Type} [Field K] {N m : ℕ} (g : Matrix (Fin N) (Fin m) K)
    (hg : Submodule.span K (Set.range g.col) = ⊤) :
    ∃ (r : ℕ) (e : Fin m ≃ Fin N ⊕ Fin r) (P : Matrix (Fin m) (Fin m) K), P.det ≠ 0 ∧
      g * P = (Matrix.fromCols (1 : Matrix (Fin N) (Fin N) K) (0 : Matrix (Fin N) (Fin r) K)).submatrix id e := by
  have hs : LinearMap.range g.mulVecLin = ⊤ := by
    rw [Matrix.range_mulVecLin]; exact hg
  obtain ⟨s, hs'⟩ := LinearMap.exists_rightInverse_of_surjective _ hs
  have hs2 : ∀ x, g.mulVecLin (s x) = x := fun x => LinearMap.congr_fun hs' x
  set r := Module.finrank K (LinearMap.ker g.mulVecLin) with hr
  have hdim : N + r = m := by
    have := LinearMap.finrank_range_add_finrank_ker g.mulVecLin
    rw [hs, finrank_top, Module.finrank_fin_fun, Module.finrank_fin_fun] at this
    exact this
  let e : Fin m ≃ Fin N ⊕ Fin r := (finCongr hdim.symm).trans finSumFinEquiv.symm
  let c : (Fin r → K) ≃ₗ[K] LinearMap.ker g.mulVecLin := (Module.finBasis K _).equivFun.symm
  let φ : (Fin m → K) →ₗ[K] (Fin m → K) :=
    s ∘ₗ LinearMap.funLeft K K (fun i => e.symm (Sum.inl i)) +
      (LinearMap.ker g.mulVecLin).subtype ∘ₗ c.toLinearMap ∘ₗ LinearMap.funLeft K K (fun i => e.symm (Sum.inr i))
  have hφ : ∀ v, φ v = s (fun i => v (e.symm (Sum.inl i))) + (c (fun i => v (e.symm (Sum.inr i))) : Fin m → K) :=
    fun v => rfl
  have hgφ : ∀ v, g.mulVecLin (φ v) = fun i => v (e.symm (Sum.inl i)) := fun v => by
    rw [hφ, map_add (f := _), hs2, LinearMap.mem_ker.1 (c _).2, add_zero]
  refine ⟨r, e, LinearMap.toMatrix' φ, ?_, ?_⟩
  · intro h0
    obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    rw [LinearMap.toMatrix'_mulVec] at hv0
    have h1 : (fun i => v (e.symm (Sum.inl i))) = 0 := by rw [← hgφ, hv0, map_zero]
    have h2 : (fun i => v (e.symm (Sum.inr i))) = 0 := by
      rw [hφ, h1, map_zero, zero_add] at hv0
      exact c.map_eq_zero_iff.1 (Subtype.ext hv0)
    refine hv (funext fun a => ?_)
    obtain ⟨a, rfl⟩ := e.symm.surjective a
    rcases a with i | i
    · exact congrFun h1 i
    · exact congrFun h2 i
  · ext j a
    have := congrFun (hgφ (Pi.single a 1)) j
    rw [Matrix.mulVecLin_apply, ← LinearMap.toMatrix'_mulVec φ, Matrix.mulVec_mulVec, Matrix.mulVec_single_one] at this
    rw [show (g * LinearMap.toMatrix' φ) j a = _ from this]
    obtain ⟨a, rfl⟩ := e.symm.surjective a
    rcases a with i | i <;> simp [Pi.single_apply, Matrix.one_apply]

end PositivityTheory.Xgn.A_xgz_height_r_vol_up_model_mat

theorem PositivityTheory.Xgn.t_xgz_height_r_vol_up_model_mat : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] (Nm : (K →+* ℂ) → V → ℝ) (L : Submodule (𝓞 K) V) (N m : ℕ) (b : Module.Basis (Fin N) K V) (g : Matrix (Fin N) (Fin m) K) (A : (K →+* ℂ) → Matrix (Fin N) (Fin N) ℂ), IsFrame Nm L b g A → ∃ Mt : (𝓞 K →+* ℂ) → Matrix (Fin m) (Fin m) ℂ, (∀ σ, (Mt σ).det ≠ 0) ∧ (∀ σ, ∃ U ∈ Matrix.unitaryGroup (Fin m) ℂ, Mt ((starRingEnd ℂ).comp σ) = (Mt σ).map (starRingEnd ℂ) * U) ∧ ∀ (σ : K →+* ℂ) (x : Fin N → ℂ), ∑ a, ‖∑ k, Mt (σ.comp (algebraMap (𝓞 K) K)) k a * ∑ j, σ (g j k) * x j‖ ^ 2 = GlobalTheory.Adelic.archSize (A σ) x ^ 2 := by
  intro K V _ _ _ _ _ Nm L N m b g A hF
  obtain ⟨r, e, P, hP, hgP⟩ := PositivityTheory.Xgn.A_xgz_height_r_vol_up_model_mat.exists_P g hF.full
  choose ext hext using PositivityTheory.Xgn.A_xgz_height_r_vol_up_model_mat.exists_ext K
  have hu : ∀ σ : K →+* ℂ, ext (σ.comp (algebraMap (𝓞 K) K)) = σ := fun σ =>
    PositivityTheory.Xgn.A_xgz_height_r_vol_up_model_mat.ext_unique K (hext _)
  have hc : ∀ τ, ext ((starRingEnd ℂ).comp τ) = (starRingEnd ℂ).comp (ext τ) := fun τ =>
    PositivityTheory.Xgn.A_xgz_height_r_vol_up_model_mat.ext_unique K (by rw [hext, RingHom.comp_assoc, hext])
  refine ⟨fun τ => P.map (ext τ) * (Matrix.fromBlocks (A (ext τ)) 0 0 (1 : Matrix (Fin r) (Fin r) ℂ)).submatrix e e,
    fun τ => ?_, fun τ => ?_, fun σ x => ?_⟩
  · rw [Matrix.det_mul, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]
    refine mul_ne_zero ?_ (hF.herm _)
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero _).2 hP
  · obtain ⟨U, hU, hB⟩ := PositivityTheory.Xgn.A_xgz_height_r_vol_up_model_mat.exists_unitary (A (ext τ))
      (A ((starRingEnd ℂ).comp (ext τ))) (hF.herm _) (hF.herm _) (hF.conj _)
    refine ⟨(Matrix.fromBlocks U 0 0 (1 : Matrix (Fin r) (Fin r) ℂ)).submatrix e e, ?_, ?_⟩
    · rw [Matrix.mem_unitaryGroup_iff] at hU ⊢
      rw [Matrix.star_eq_conjTranspose] at hU ⊢
      rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_conjTranspose,
        Matrix.fromBlocks_multiply]
      simp [hU]
    · simp only []
      rw [hc, hB, Matrix.map_mul, Matrix.mul_assoc, ← Matrix.submatrix_map, Matrix.submatrix_mul_equiv,
        Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.map_map]
      simp
  · simp only [hu]
    have key : g.map σ * (P.map σ * (Matrix.fromBlocks (A σ) 0 0 (1 : Matrix (Fin r) (Fin r) ℂ)).submatrix e e) =
        (Matrix.fromCols (A σ) (0 : Matrix (Fin N) (Fin r) ℂ)).submatrix id e := by
      rw [← Matrix.mul_assoc, ← Matrix.map_mul, hgP, ← Matrix.submatrix_map, Matrix.submatrix_mul_equiv,
        Matrix.fromCols_map, Matrix.fromCols_mul_fromBlocks]
      simp
    have k2 : ∀ a, ∑ k, (P.map σ * (Matrix.fromBlocks (A σ) 0 0 (1 : Matrix (Fin r) (Fin r) ℂ)).submatrix e e) k a *
        ∑ j, σ (g j k) * x j = ∑ j, Matrix.fromCols (A σ) (0 : Matrix (Fin N) (Fin r) ℂ) j (e a) * x j := by
      intro a
      generalize P.map σ * (Matrix.fromBlocks (A σ) 0 0 (1 : Matrix (Fin r) (Fin r) ℂ)).submatrix e e = M at key
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      have := congrFun (congrFun key j) a
      rw [Matrix.submatrix_apply, id, Matrix.mul_apply] at this
      rw [← this, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Matrix.map_apply]; ring
    simp only [k2]
    rw [GlobalTheory.Adelic.archSize, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _),
      Equiv.sum_comp e (fun a => ‖∑ j, Matrix.fromCols (A σ) (0 : Matrix (Fin N) (Fin r) ℂ) j a * x j‖ ^ 2),
      Fintype.sum_sum_type]
    simp
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.WeilHeightInequality

section

@[expose] public section

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open PositivityTheory.UnitarySelfGeneration.UnitProductCombination
theorem PositivityTheory.UnitarySelfGeneration.weil_height_inequality : PositivityTheory.UnitarySelfGeneration.ChowFormHeight → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (K V Ω : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] (Nm : (K →+* ℂ) → V → ℝ) (W : Submodule (𝓞 K) V) (ev : V →ₗ[K] Ω) (D : ℕ) (X : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral X] (p : X ⟶ Sp (𝓞 K)) (L : GlobalTheory.HermLB p) (ψ : Ω →+* X.functionField) (s : W → L.B.Sec) (t a : ℝ), (∀ σ : K →+* ℂ, (starRingEnd ℂ).comp σ ≠ σ) → HasGram Nm → (∀ σ x, Nm ((starRingEnd ℂ).comp σ) x = Nm σ x) → W.FG → Submodule.span K (W : Set V) = ⊤ → GlobalTheory.DegVal.GenRatios ev → 0 < imageDeg ev D → GlobalTheory.ImageModel.IsModelOf Nm W ev D p L ψ s → (L.shift (fun _ => t) (fun _ => rfl)).IsSelfInter a → a ≤ (Module.finrank ℚ K : ℝ) * ((D : ℝ) + 1) * ((imageDeg ev D : ℝ) * (imageHeight Nm W ev D + t)) := by
  intro HP hP K V Ω _ _ _ _ _ _ _ _ Nm W ev D X _ p L ψ s t a _ _ _ _ hW hG hd hM ha
  obtain ⟨pt, h1, h2, h3, h4⟩ := exists_pt p ψ hM.bij hM.base
  have := GlobalTheory.CommonModel.isProper_of_isProjOver hM.arith.isProjOver
  let M : GlobalTheory.ZH.RatModel (𝓞 K) Ω :=
    { Z := X, s := p, sep := inferInstance, lft := inferInstance, qc := inferInstance, pt := pt, pt_s := h1,
      gen := h2, onto := h3 }
  obtain ⟨N, n, b, g, A, c, gw, hF, hgw, hcb, hφ⟩ := hM.fs
  obtain ⟨Mt, hdet, hcc, hMt⟩ := PositivityTheory.Xgn.t_xgz_height_r_vol_up_model_mat K V Nm W N n b g A hF
  obtain ⟨e, he, hv, hs, hdiv⟩ := gen_all M L.B L.isLB ev W s
    (fun w w' i hi => by
      obtain ⟨z, hz⟩ := hi
      have hg := GlobalTheory.Cartier.gen_mem (X := X) hz
      refine hM.bij.1 ?_
      rw [map_mul, map_mul]
      exact (congrArg _ (h4 _ hg _)).trans ((hM.ratio w w' i hg).trans (congrArg _ (h4 _ hg _).symm)))
    hM.bpf hG.1 hW gw (by simp only [hgw]; exact hF.span)
  have h5 := _root_.PositivityTheory.UnitarySelfGeneration.volume_le_self_intersection HP hP K V Ω Nm W ev D N n b g A t hF hG hd M (by simpa only [hgw] using hdiv)
    hM.arith L.B L.isLB e he (fun k => s (gw k)) (fun k => hgw k ▸ hv (gw k)) hs Mt hdet hcc hMt
  have h6 := (isometric_fs M L ev s hv hW b g A c gw hgw hcb hφ hs Mt hdet hcc hMt t).isSelfInter hM.arith h5
  rw [ha.unique hM.arith h6]
  exact le_of_eq (by ring)
end
end
end
