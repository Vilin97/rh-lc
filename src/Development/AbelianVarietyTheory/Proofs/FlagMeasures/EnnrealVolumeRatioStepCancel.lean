module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GaugeUnfold
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutInstDegreeRootDiscriminantRankStatement
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutomorphicInstanceExistsFundamentalDomain
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFrameOfHasSignature
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LamXEquivariant
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFiniteAdelicPointLatticeEqSelfDualStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianSpacesSameSignatureIsometricStatement
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GaussianQuadricDensityExistsPosContinuousStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GaussianSumStabiliserUnfolding
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeftQuotientCovolumeEqFundamentalDomainInterStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassRatioRankFactorStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NegLogProdLValEtaLeAndPosStatement
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutomorphicInstanceExistsFundamentalDomainStatement

section

@[expose] public section

open MeasureTheory Formalism.MainNotions.S
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.automorphicInstance_exists_fundamental_domain : ∀ (I : AutInst) (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf], ∃ fund, I.IsFundDom (I.muA μf) fund := by
  first | exact @GlobalTheory.FundExists.exists_isFundDom | exact GlobalTheory.FundExists.exists_isFundDom | (intros; apply GlobalTheory.FundExists.exists_isFundDom <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnitVectorOrthogonalInstanceRankThree

section

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.AutInhab

noncomputable section

namespace GlobalTheory.PerpInst

theorem exists_drop {n : ℕ} (ε : Fin n → Bool) (k : Fin n) :
    ∃ (m : ℕ) (f : Fin m → Fin n), m + 1 = n ∧ Function.Injective f ∧ (∀ i, f i ≠ k) ∧
      ∀ b, (univ.filter fun a => ε (f a) = b).card + (if ε k = b then 1 else 0) =
        (univ.filter fun a => ε a = b).card := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := k.2; omega⟩
  refine ⟨m, k.succAbove, rfl, Fin.succAbove_right_injective, k.succAbove_ne, fun b => ?_⟩
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succAbove _ k, add_comm]

theorem hform_eq {E : Type} [Field E] [StarRing E] {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (y x : Fin n → E) :
    Formalism.UG.hform (starRingEnd E) J y x = star y ⬝ᵥ (J *ᵥ x) := by
  simp [Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, mul_assoc, starRingEnd_apply]

theorem form_mulVec {E : Type} [Field E] [StarRing E] {n : ℕ} (J G : Matrix (Fin n) (Fin n) E)
    (y x : Fin n → E) : star (G *ᵥ y) ⬝ᵥ (J *ᵥ (G *ᵥ x)) = star y ⬝ᵥ ((Gᴴ * J * G) *ᵥ x) := by
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]

theorem hasSignature_all (I : AutInst) {P Q : ℕ} (h : HasSig I P Q) (φ : I.E →+* ℂ) :
    Formalism.UG.HasSignature (I.J.map φ) P Q := by
  have key : ∃ v, φ = I.φ v ∨ φ = ComplexEmbedding.conjugate (I.φ v) := by
    refine ⟨(InfinitePlace.mk φ).comap (algebraMap I.F I.E), ?_⟩
    rcases GlobalTheory.Count.Test.embedding_cases I (InfinitePlace.mk φ) with h | h <;>
      rcases InfinitePlace.embedding_mk_eq φ with h' | h'
    · exact Or.inl (h'.symm.trans h)
    · right
      rw [← h, h']; simp
    · exact Or.inr (h'.symm.trans h)
    · left
      exact star_injective (h'.symm.trans h)
  obtain ⟨v, rfl | rfl⟩ := key
  · rw [← (h v).1, ← (h v).2]; exact hasSignature_inst I v
  · rw [← (h v).1, ← (h v).2]
    refine hasSignature_of_frame (P := (I.P v).map (starRingEnd ℂ)) ((I.P_unit v).map (starRingEnd ℂ).mapMatrix) ?_
    have h1 := congrArg (fun M => Matrix.map M (starRingEnd ℂ)) (I.P_spec v)
    simp only [Matrix.map_mul] at h1
    have h2 : (Formalism.REAL.Jm (I.ε v)).map (starRingEnd ℂ) = Formalism.REAL.Jm (I.ε v) := by
      rw [Formalism.REAL.Jm, Matrix.diagonal_map (map_zero _)]
      congr 1
      funext a
      split_ifs <;> simp
    rw [h2] at h1
    exact h1

theorem exists_point (I : AutInst) (ε : Fin I.n → Bool) (γ : GL (Fin I.n) I.E)
    (hγ : (γ : Matrix (Fin I.n) (Fin I.n) I.E)ᴴ * I.J * (γ : Matrix (Fin I.n) (Fin I.n) I.E) = signMat I.E ε) :
    ∃ xf : I.Gf, ∀ z, (γ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ z ∈ lamX I (1, xf) ↔ z ∈ intLat I.E I.n := by
  set G : Matrix (Fin I.n) (Fin I.n) I.E := γ.val with hG
  have hsur : Function.Surjective G.mulVec := Matrix.mulVec_surjective_iff_isUnit.2 γ.isUnit
  have hinj : Function.Injective G.mulVec := Matrix.mulVec_injective_iff_isUnit.2 γ.isUnit
  let Λ : Submodule (𝓞 I.E) (Fin I.n → I.E) := (intLat I.E I.n).map (G.mulVecLin.restrictScalars (𝓞 I.E))
  have hΛ : ∀ z, G *ᵥ z ∈ Λ ↔ z ∈ intLat I.E I.n := fun z =>
    ⟨fun ⟨w, hw, e⟩ => (hinj e : w = z) ▸ hw, fun hz => ⟨z, hz, rfl⟩⟩
  obtain ⟨xf, hxf⟩ := GlobalTheory.T.exists_finiteAdelicPoint_lattice_eq_selfDual I Λ (Submodule.IsLattice.of_fg I.E ((intLat_fg _).map _)) (by
      intro x
      obtain ⟨x, rfl⟩ := hsur x
      rw [hΛ, intLat_dual ε]
      constructor
      · rintro h _ ⟨y, hy, rfl⟩
        have := h y hy
        rw [hform_eq, ← hγ, ← form_mulVec, ← hform_eq] at this
        exact this
      · intro h y hy
        have := h _ ((hΛ y).2 hy)
        rwa [hform_eq, form_mulVec, hγ, ← hform_eq] at this)
  exact ⟨xf, fun z => hxf ▸ hΛ z⟩

theorem exists_isPerpInst : ∀ (I : AutInst) (P Q : ℕ), HasSig I P Q → 3 ≤ I.n → ∀ s : Bool, (if s then 1 ≤ P else 1 ≤ Q) → ∃ (I' : AutInst) (e : I'.E ≃+* I.E) (x : Fin I.n → I.E) (A : Matrix (Fin I.n) (Fin I'.n) I.E) (xf : I.Gf), IsPerpInst I I' e s x A xf ∧ HasSig I' (if s then P - 1 else P) (if s then Q else Q - 1) := by
  intro I P Q h _ s hs
  obtain ⟨v⟩ : Nonempty (InfinitePlace I.F) := inferInstance
  set ε := I.ε v with hε
  have hP : (univ.filter fun a => ε a = true).card = P := (h v).1
  have hQ : (univ.filter fun a => ε a = false).card = Q := (h v).2
  obtain ⟨k, hk⟩ : ∃ k, ε k = s := by
    have : 0 < (univ.filter fun a => ε a = s).card := by
      cases s
      · rw [hQ]; exact hs
      · rw [hP]; exact hs
    obtain ⟨k, hk⟩ := Finset.card_pos.1 this
    exact ⟨k, (Finset.mem_filter.1 hk).2⟩
  obtain ⟨γ, hγ⟩ := GlobalTheory.T.hermitian_spaces_same_signature_isometric I.E I.cm.cmUnram I.n I.J (signMat I.E ε) I.J_herm (signMat_isHerm ε)
    I.J_det (signMat_det ε) ⟨I.L, Submodule.IsLattice.of_fg I.E I.L_fg, fun x => by simpa only [hform_eq] using I.L_dual x⟩
    ⟨intLat I.E I.n, Submodule.IsLattice.of_fg I.E (intLat_fg _), fun x => by simpa only [hform_eq] using intLat_dual ε x⟩
    (fun φ => ⟨P, Q, hasSignature_all I h φ, by
      rw [signMat_map, ← hP, ← hQ]
      exact hasSignature_of_frame (P := 1) isUnit_one (by simp)⟩)
  obtain ⟨xf, hxf⟩ := exists_point I ε γ hγ
  obtain ⟨m, f, hm, hf, hfk, hcard⟩ := exists_drop ε k
  set G : Matrix (Fin I.n) (Fin I.n) I.E := γ.val with hG
  let C : Matrix (Fin I.n) (Fin m) I.E := (1 : Matrix (Fin I.n) (Fin I.n) I.E).submatrix id f
  refine ⟨ofSigns I.cm (fun a => ε (f a)), RingEquiv.refl I.E, G *ᵥ Pi.single k 1, G * C, xf,
    ⟨fun _ => rfl, hm, ?_, ?_, ?_, ?_, ?_⟩, fun w => ⟨?_, ?_⟩⟩
  · rw [form_mulVec, hγ]
    simp [signMat, sgn, hk]
  · have : star (G *ᵥ Pi.single k 1) ᵥ* (I.J * (G * C)) = star (Pi.single k 1) ᵥ* ((Gᴴ * I.J * G) * C) := by
      rw [star_mulVec, vecMul_vecMul]; simp only [Matrix.mul_assoc]
    refine this.trans ?_
    rw [hγ]
    funext j
    simp [signMat, C, vecMul, dotProduct, Pi.single_apply, Matrix.one_apply, hfk j]
    rfl
  · have : (G * C)ᴴ * I.J * (G * C) = Cᴴ * (Gᴴ * I.J * G) * C := by
      rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
    refine this.trans ?_
    rw [hγ]
    change _ = signMat I.E fun a => ε (f a)
    ext i j
    rw [Matrix.mul_apply]
    simp [signMat, C, Matrix.one_apply, Matrix.diagonal_apply, hf.eq_iff]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]
  · exact (hxf _).2 (Submodule.subset_span ⟨k, by simp⟩)
  · change ∀ y : Fin m → I.E, y ∈ intLat I.E m ↔ (G * C) *ᵥ y ∈ lamX I (1, xf)
    intro y
    rw [← mulVec_mulVec, hxf, mem_intLat, mem_intLat]
    constructor
    · intro hy i
      change ∑ j, C i j * y j ∈ _
      refine sum_mem fun j _ => mul_mem ?_ (hy j)
      simp only [C, submatrix_apply, id, Matrix.one_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    · intro hy j
      have := hy (f j)
      simpa [C, mulVec, dotProduct, Matrix.one_apply, hf.eq_iff] using this
  · change (univ.filter fun a => ε (f a) = true).card = _
    have := hcard true
    rw [hP, hk] at this
    cases s <;> simp at this ⊢ <;> omega
  · change (univ.filter fun a => ε (f a) = false).card = _
    have := hcard false
    rw [hQ, hk] at this
    cases s <;> simp at this ⊢ <;> omega

end GlobalTheory.PerpInst
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnitVectorOrthogonalInstanceRankThreeStatement

section

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean

theorem _root_.GlobalTheory.T.exists_unit_vector_orthogonal_instance_rank_three : ∀ (I : AutInst) (P Q : ℕ), HasSig I P Q → 3 ≤ I.n → ∀ s : Bool, (if s then 1 ≤ P else 1 ≤ Q) → ∃ (I' : AutInst) (e : I'.E ≃+* I.E) (x : Fin I.n → I.E) (A : Matrix (Fin I.n) (Fin I'.n) I.E) (xf : I.Gf), IsPerpInst I I' e s x A xf ∧ HasSig I' (if s then P - 1 else P) (if s then Q else Q - 1) := by
  first | exact @GlobalTheory.PerpInst.exists_isPerpInst | exact GlobalTheory.PerpInst.exists_isPerpInst | (intros; apply GlobalTheory.PerpInst.exists_isPerpInst <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.GaussianSumStabiliserUnfoldingStatement

section

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean

theorem _root_.GlobalTheory.T.gaussianSum_stabiliserUnfolding : GaugeUnfold := by
  first | exact @GlobalTheory.StabUnfold.gaugeUnfold | exact GlobalTheory.StabUnfold.gaugeUnfold | (intros; apply GlobalTheory.StabUnfold.gaugeUnfold <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.EnnrealVolumeRatioStepCancel

section

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean

noncomputable section

namespace GlobalTheory.GaussMean.Step

theorem volU_pos (i : ℕ) : 0 < volU i := by
  have : 0 < sphV i := by
    unfold sphV
    exact Finset.prod_pos fun l _ => by have := Real.pi_pos; positivity
  unfold volU
  positivity

theorem vInv_pos (E : Type) [Field E] [NumberField E] : 0 < Formalism.HermitianLatticesTheory.vInv E := by
  unfold Formalism.HermitianLatticesTheory.vInv
  have : (0 : ℝ) < |(discr E : ℝ)| := abs_pos.2 (by exact_mod_cast discr_ne_zero E)
  positivity

theorem rankFac_mul_meanConst (E : Type) [Field E] [NumberField E] [StarRing E] (M : ℕ)
    (hL : 0 < Formalism.HermitianLatticesTheory.lValEta E M) :
    rankFac E M * meanConst E M = 2 ^ (M * Formalism.HermitianLatticesTheory.fDeg E) := by
  have hv := vInv_pos E
  unfold rankFac meanConst
  set v := Formalism.HermitianLatticesTheory.vInv E
  set f := Formalism.HermitianLatticesTheory.fDeg E
  set L := Formalism.HermitianLatticesTheory.lValEta E M
  have h2 : 0 < 2 * v := by positivity
  have key : (2 * v) ^ ((f : ℝ) * ((M : ℝ) - 1 / 2)) * (2 * v) ^ ((f : ℝ) / 2)
      = 2 ^ (M * f) * v ^ (M * f) := by
    rw [← Real.rpow_add h2, ← mul_pow, ← Real.rpow_natCast]
    congr 1
    push_cast
    ring
  have hp : 0 < v ^ (M * f) := by positivity
  calc (2 * v) ^ ((f : ℝ) * ((M : ℝ) - 1 / 2)) * L * ((2 * v) ^ ((f : ℝ) / 2) * (v ^ (M * f))⁻¹ / L)
      = ((2 * v) ^ ((f : ℝ) * ((M : ℝ) - 1 / 2)) * (2 * v) ^ ((f : ℝ) / 2)) * (v ^ (M * f))⁻¹ := by
        field_simp
    _ = 2 ^ (M * f) := by rw [key]; field_simp

theorem meanConst_pos (E : Type) [Field E] [NumberField E] [StarRing E] (M : ℕ)
    (hL : 0 < Formalism.HermitianLatticesTheory.lValEta E M) : 0 < meanConst E M := by
  have hv := vInv_pos E
  unfold meanConst
  positivity

theorem rankFac_pos (E : Type) [Field E] [NumberField E] [StarRing E] (M : ℕ)
    (hL : 0 < Formalism.HermitianLatticesTheory.lValEta E M) : 0 < rankFac E M := by
  have hv := vInv_pos E
  unfold rankFac
  positivity

theorem ennreal_volume_ratio_step_cancel (X Y : ENNReal) (m d t r a b ρ : ℝ) (hm : 0 < m) (hd : 0 < d) (hr : 0 < r)
    (ha : 0 < a) (hb : 0 < b) (ht : r * m = t) (hρ : ρ * a = r * b)
    (h : X * ENNReal.ofReal (m * d) = Y * ENNReal.ofReal (t * d)) :
    X / ENNReal.ofReal a = Y / ENNReal.ofReal b * ENNReal.ofReal ρ := by
  have hmd : 0 < m * d := mul_pos hm hd
  have h1 : X = Y * ENNReal.ofReal r := by
    have e : t * d = r * (m * d) := by rw [← ht]; ring
    rw [e, ENNReal.ofReal_mul hr.le, ← mul_assoc] at h
    exact (ENNReal.mul_left_inj (ENNReal.ofReal_pos.2 hmd).ne' ENNReal.ofReal_ne_top).1 h
  have e2 : ρ = b * (r / a) := by field_simp; linarith
  rw [h1, e2, ENNReal.ofReal_mul hb.le, ← mul_assoc,
    ENNReal.div_mul_cancel (ENNReal.ofReal_pos.2 hb).ne' ENNReal.ofReal_ne_top,
    ENNReal.ofReal_div_of_pos ha, mul_div_assoc]

theorem volumeStep_of_siegelMean : SiegelMean → VolumeStep := by
  intro hS I P Q hPQ hn s hs
  obtain ⟨I', e, x, A, xf, hperp, hsig⟩ := GlobalTheory.T.exists_unit_vector_orthogonal_instance_rank_three I P Q hPQ hn s hs
  refine ⟨I', e, x, A, hperp.1, hperp.2.1, hperp.2.2.1, hperp.2.2.2.1, hperp.2.2.2.2.1, hsig, ?_⟩
  intro c μf _ _ c' μf' _ _ hc hc'
  obtain ⟨fund, hfund⟩ := GlobalTheory.T.automorphicInstance_exists_fundamental_domain I μf
  have hU := GlobalTheory.T.gaussianSum_stabiliserUnfolding I I' e s x A xf hn hperp c μf c' μf' fund hc hc' hfund
  obtain ⟨-, hM⟩ := hS I hn s μf fund hfund
  have hcov := (GlobalTheory.T.leftQuotientCovolume_eq_fundamentalDomain_inter I μf fund Set.univ hfund MeasurableSet.univ
    (fun _ _ _ _ => Set.mem_univ _)).1
  rw [Set.univ_inter] at hcov
  have hf : Formalism.HermitianLatticesTheory.fDeg I.E = I.f := (GlobalTheory.T.autInst_degree_rootDiscriminant_rank I).1
  have hL : 0 < Formalism.HermitianLatticesTheory.lValEta I.E I.n := by
    have := (GlobalTheory.T.neg_log_prod_lValEta_le_and_pos I.E I.cm.cmUnram (I.n - 1) I.n (by omega)).2
    have hI : Finset.Ioc (I.n - 1) I.n = {I.n} := by
      ext k
      simp only [Finset.mem_Ioc, Finset.mem_singleton]
      omega
    rwa [hI, Finset.prod_singleton] at this
  have hd : 0 < ∏ v, gaussDens (I.ε v) (sgn ℝ s) := by
    refine Finset.prod_pos fun v _ => (GlobalTheory.T.gaussianQuadricDensity_exists_pos_continuous I.n (I.ε v)).2.2 s ?_
    obtain ⟨hp, hq⟩ := hPQ v
    cases s
    · have : 0 < I.qAt v := by
        have h1 : 1 ≤ Q := by simpa using hs
        omega
      obtain ⟨a, ha⟩ := Finset.card_pos.1 this
      exact ⟨a, (Finset.mem_filter.1 ha).2⟩
    · have : 0 < I.pAt v := by
        have h1 : 1 ≤ P := by simpa using hs
        omega
      obtain ⟨a, ha⟩ := Finset.card_pos.1 this
      exact ⟨a, (Finset.mem_filter.1 ha).2⟩
  have hR := GlobalTheory.T.mass_ratio_rank_factor I.E I.n (by omega)
  have hn' : I.n - 1 = I'.n := by have := hperp.2.1; omega
  rw [hf, hn'] at hR
  have hrm := rankFac_mul_meanConst I.E I.n hL
  rw [hf] at hrm
  refine ennreal_volume_ratio_step_cancel _ _ _ _ _ _ _ _ _ (meanConst_pos I.E I.n hL) hd (rankFac_pos I.E I.n hL)
    (pow_pos (volU_pos _) _) (pow_pos (volU_pos _) _) hrm hR ?_
  rw [← hU, hM, gaugeVol, hcov]
  simp only [div_eq_mul_inv]
  ring

end GlobalTheory.GaussMean.Step
end
end
end
