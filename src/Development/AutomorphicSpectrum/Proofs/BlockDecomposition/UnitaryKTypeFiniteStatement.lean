module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlkConjTranspose
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimensionalIsoPartOfSimple
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleOfLinearReductive
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.IwasawaUnitaryAdelic.IUAIwa
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ReduceModChar
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaOfLinearReductive
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsCompactOperatorOfIsHilbertSchmidt

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleUnitaryIrreducibleRep

section

@[expose] public section

open Matrix
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.admitted

theorem isAdmissible_of_unitary_irreducible : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)}, GlobalTheory.LinRed.IsLinRed G →
    PositivityTheory.Tls2.Iua.AdmG G → ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.MainNotions.S.IsURepOn G σ → Formalism.MainNotions.S.IsIrredOn G σ →
    GlobalTheory.LinRed.IsAdmOn G σ := by
  intro n G hG hA H _ _ _ σ hσ hirr
  refine ⟨hσ.1, hσ.2.2, fun k hk v => hσ.2.1 k hk.1 v, ?_⟩
  intro S hfd hS _
  haveI := hfd
  let b := Module.finBasis ℂ S
  choose Y hYfd _ hvY hY using fun i => hA H σ hσ hirr S hS (b i) (b i).2
  haveI : ∀ i, FiniteDimensional ℂ (Y i) := hYfd
  have hsup : FiniteDimensional ℂ (⨆ i, Y i : Submodule ℂ H) := Submodule.finiteDimensional_iSup Y
  refine Submodule.finiteDimensional_of_le (S₂ := ⨆ i, Y i) (sSup_le ?_)
  rintro _ ⟨Θ, rfl, hΘ⟩
  let T : H →L[ℂ] H := (LinearMap.toContinuousLinearMap (Θ.domRestrict S)).comp S.orthogonalProjectionOnto
  have hT : ∀ k ∈ GlobalTheory.LinRed.maxCpt G, ∀ u, T (σ k u) = σ k (T u) := by
    intro k hk u
    have hk1 : k * k.conjTranspose = 1 := Matrix.mem_unitaryGroup_iff.1 hk.2
    have hks : k.conjTranspose ∈ GlobalTheory.LinRed.maxCpt G := ⟨hG.star_mem k hk.1, Unitary.star_mem hk.2⟩
    have hiso : ∀ x y, ⟪σ k x, σ k y⟫_ℂ = ⟪x, y⟫_ℂ := fun x y =>
      (LinearIsometry.mk (σ k : H →ₗ[ℂ] H) (hσ.2.1 k hk.1)).inner_map_map x y
    have hP : ((S.orthogonalProjectionOnto (σ k u) : S) : H) = σ k (S.orthogonalProjectionOnto u : S) := by
      refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (hS k hk _ (S.orthogonalProjectionOnto u).2) ?_
      intro w hw
      have hw' : σ k (σ k.conjTranspose w) = w := by
        rw [← ContinuousLinearMap.comp_apply, ← hσ.1.2 _ hk.1 _ hks.1, hk1, hσ.1.1]
        rfl
      rw [← hw', ← map_sub, hiso]
      exact S.starProjection_inner_eq_zero u _ (hS _ hks w hw)
    have h := hΘ k hk _ (S.orthogonalProjectionOnto u).2
    simpa [T, hP] using h
  rintro _ ⟨v, hv, rfl⟩
  have hv' : v = ((⟨v, hv⟩ : S) : H) := rfl
  rw [hv', ← b.sum_repr ⟨v, hv⟩]

  simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.mem_iSup_of_mem i ?_)
  have := hY i T hT _ (hvY i)
  simpa [T] using this

end GlobalTheory.CompanionTheory.admitted

end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteSetOfDetLineEqZero

section

@[expose] public section

open Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.AdmGL

variable {ι : Type} [Fintype ι] [DecidableEq ι] {a n : ℕ}

theorem isClosed_range_blk (e : Fin a × ι ≃ Fin n) : IsClosed {g | blk e (unblk e g) = g} :=
  isClosed_eq ((continuous_blk e).comp (continuous_unblk e)) continuous_id

theorem blk_unblk_of_mem_closure (e : Fin a × ι ≃ Fin n) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ closure (blkG e)) : blk e (unblk e g) = g :=
  (closure_minimal (fun _ h => ((mem_blkG_iff e).1 h).2) (isClosed_range_blk e)) hg

theorem finite_setOf_det_line_eq_zero {A B : Matrix (Fin n) (Fin n) ℂ} (hA : IsUnit A) :
    {z : ℂ | ((1 - z) • A + z • B).det = 0}.Finite := by
  let P : Polynomial ℂ := Matrix.det ((1 - Polynomial.X : Polynomial ℂ) • A.map Polynomial.C
    + (Polynomial.X : Polynomial ℂ) • B.map Polynomial.C)
  have hev : ∀ z : ℂ, P.eval z = ((1 - z) • A + z • B).det := by
    intro z
    have := RingHom.map_det (Polynomial.evalRingHom z) ((1 - Polynomial.X : Polynomial ℂ) • A.map Polynomial.C
      + (Polynomial.X : Polynomial ℂ) • B.map Polynomial.C)
    simp only [Polynomial.coe_evalRingHom] at this
    rw [this]
    congr 1
    ext i j
    simp
    exact mul_comm _ _
  have hP : P ≠ 0 := by
    intro h
    have := hev 0
    rw [h] at this
    simp only [Polynomial.eval_zero, sub_zero, one_smul, zero_smul, add_zero] at this
    exact ((Matrix.isUnit_iff_isUnit_det A).1 hA).ne_zero this.symm
  refine (P.rootSet_finite ℂ).subset ?_
  intro z hz
  rw [Polynomial.mem_rootSet]
  refine ⟨hP, ?_⟩
  simpa [hev] using hz

theorem isPreconnected_blkG (e : Fin a × ι ≃ Fin n) : IsPreconnected (blkG e) := by
  refine isPreconnected_of_forall_pair ?_
  rintro _ ⟨M, hM, rfl⟩ _ ⟨N, hN, rfl⟩
  have hA : IsUnit (blk e M) := (isUnit_blk_iff e M).2 hM
  have hB : IsUnit (blk e N) := (isUnit_blk_iff e N).2 hN
  set A := blk e M
  set B := blk e N
  let Z : Set ℂ := {z | ((1 - z) • A + z • B).det = 0}
  have hZ : Z.Finite := finite_setOf_det_line_eq_zero hA
  have hconn : IsPathConnected Zᶜ := hZ.countable.isPathConnected_compl_of_one_lt_rank (by
    rw [Complex.rank_real_complex]; norm_num)
  let γ : ℂ → Matrix (Fin n) (Fin n) ℂ := fun z => (1 - z) • A + z • B
  have hγ : Continuous γ := by fun_prop
  refine ⟨γ '' Zᶜ, ?_, ⟨0, ?_, by simp [γ]⟩, ⟨1, ?_, by simp [γ]⟩, hconn.isConnected.isPreconnected.image _ hγ.continuousOn⟩
  · rintro _ ⟨z, hz, rfl⟩
    refine (mem_blkG_iff e).2 ⟨(Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hz), ?_⟩
    have : γ z = blk e ((1 - z) • M + z • N) := by simp [γ, A, B]
    rw [this, unblk_blk]
  · simpa [Z] using ((Matrix.isUnit_iff_isUnit_det A).1 hA).ne_zero
  · simpa [Z] using ((Matrix.isUnit_iff_isUnit_det B).1 hB).ne_zero

theorem blk_inv (e : Fin a × ι ≃ Fin n) {M : Matrix (Fin a) (Fin a) (ι → ℂ)} (hM : IsUnit M) :
    (blk e M)⁻¹ = blk e M⁻¹ := by
  refine Matrix.inv_eq_right_inv ?_
  rw [← blk_mul, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hM), blk_one]

theorem isLinRed_blkG (e : Fin a × ι ≃ Fin n) : GlobalTheory.LinRed.IsLinRed (blkG e) := by
  refine
    { one_mem := ⟨1, isUnit_one, blk_one e⟩
      mul_mem := ?_
      isUnit := fun g hg => ((mem_blkG_iff e).1 hg).1
      inv_mem := ?_
      closed := fun g hg hcl => (mem_blkG_iff e).2 ⟨hg, blk_unblk_of_mem_closure e hcl⟩
      connected := isPreconnected_blkG e
      star_mem := ?_ }
  · rintro _ ⟨M, hM, rfl⟩ _ ⟨N, hN, rfl⟩
    exact ⟨M * N, IsUnit.mul hM hN, blk_mul e M N⟩
  · rintro _ ⟨M, hM, rfl⟩
    refine ⟨M⁻¹, ?_, (blk_inv e hM).symm⟩
    exact (Matrix.isUnit_nonsing_inv_iff).2 hM
  · rintro _ ⟨M, hM, rfl⟩
    refine ⟨Mᴴ, ?_, blk_conjTranspose e M⟩
    have : IsUnit (star M) := IsUnit.star hM
    exact this

end GlobalTheory.CompanionTheory.AdmGL

end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryKTypeFinite

section

@[expose] public section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

noncomputable section

namespace GlobalTheory.CompanionTheory.AdmGL

variable {ι : Type} [Fintype ι] [DecidableEq ι] {a n : ℕ}


open scoped Classical in
def toGL (M : Matrix (Fin a) (Fin a) (ι → ℂ)) : GL (Fin a) (ι → ℂ) :=
  if h : IsUnit M then h.unit else 1

theorem coe_toGL {M : Matrix (Fin a) (Fin a) (ι → ℂ)} (h : IsUnit M) : (toGL M : Matrix (Fin a) (Fin a) (ι → ℂ)) = M := by
  simp [toGL, h]

theorem toGL_coe (u : GL (Fin a) (ι → ℂ)) : toGL (u : Matrix (Fin a) (Fin a) (ι → ℂ)) = u :=
  Units.ext (coe_toGL u.isUnit)

def blkRep {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (e : Fin a × ι ≃ Fin n)
    (σ : GL (Fin a) (ι → ℂ) →* (H →L[ℂ] H)) (g : Matrix (Fin n) (Fin n) ℂ) : H →L[ℂ] H :=
  σ (toGL (unblk e g))

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem blkRep_blk (e : Fin a × ι ≃ Fin n) (σ : GL (Fin a) (ι → ℂ) →* (H →L[ℂ] H)) (u : GL (Fin a) (ι → ℂ)) :
    blkRep e σ (blk e (u : Matrix (Fin a) (Fin a) (ι → ℂ))) = σ u := by
  rw [blkRep, unblk_blk, toGL_coe]

theorem blk_coe_mem (e : Fin a × ι ≃ Fin n) (u : GL (Fin a) (ι → ℂ)) :
    blk e (u : Matrix (Fin a) (Fin a) (ι → ℂ)) ∈ blkG e := ⟨_, u.isUnit, rfl⟩

theorem exists_gl_of_mem (e : Fin a × ι ≃ Fin n) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ blkG e) :
    ∃ u : GL (Fin a) (ι → ℂ), g = blk e (u : Matrix (Fin a) (Fin a) (ι → ℂ)) := by
  obtain ⟨M, hM, rfl⟩ := hg
  exact ⟨hM.unit, rfl⟩

theorem continuousOn_toGL_unblk (e : Fin a × ι ≃ Fin n) :
    ContinuousOn (fun g => toGL (unblk e g) : Matrix (Fin n) (Fin n) ℂ → GL (Fin a) (ι → ℂ)) (blkG e) := by
  rw [continuousOn_iff_continuous_restrict]
  have hval : ∀ g : blkG e, ((toGL (unblk e g.1) : GL (Fin a) (ι → ℂ)) : Matrix (Fin a) (Fin a) (ι → ℂ)) = unblk e g.1 := by
    rintro ⟨_, M, hM, rfl⟩
    rw [unblk_blk]
    exact coe_toGL hM
  have hinv : ∀ g : blkG e, (((toGL (unblk e g.1))⁻¹ : GL (Fin a) (ι → ℂ)) : Matrix (Fin a) (Fin a) (ι → ℂ)) =
      unblk e (g.1.det⁻¹ • g.1.adjugate) := by
    rintro ⟨_, M, hM, rfl⟩
    have h := blk_inv e hM
    rw [Matrix.inv_def, Ring.inverse_eq_inv'] at h
    simp only [h, unblk_blk]
    rw [Matrix.coe_units_inv, coe_toGL hM]
  have hdet : ∀ g : blkG e, g.1.det ≠ 0 := fun g =>
    ((Matrix.isUnit_iff_isUnit_det _).1 ((mem_blkG_iff e).1 g.2).1).ne_zero
  have hc : Continuous fun g : blkG e => g.1.det⁻¹ • g.1.adjugate :=
    (Continuous.inv₀ continuous_subtype_val.matrix_det hdet).smul continuous_subtype_val.matrix_adjugate
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact ((continuous_unblk e).comp continuous_subtype_val).congr fun g => (hval g).symm
  · exact ((continuous_unblk e).comp hc).congr fun g => (hinv g).symm

theorem isURepOn_blkRep (e : Fin a × ι ≃ Fin n) {σ : GL (Fin a) (ι → ℂ) →* (H →L[ℂ] H)} (hσ : IsUnitaryRep σ) :
    Formalism.MainNotions.S.IsURepOn (blkG e) (blkRep e σ) := by
  refine ⟨⟨?_, ?_⟩, fun g _ v => hσ.norm_apply _ v, fun v =>
    (hσ.continuous_apply v).comp_continuousOn (continuousOn_toGL_unblk e)⟩
  · have h := blkRep_blk e σ 1
    simpa using h
  · intro g hg h hh
    obtain ⟨u, rfl⟩ := exists_gl_of_mem e hg
    obtain ⟨v, rfl⟩ := exists_gl_of_mem e hh
    rw [← blk_mul, ← Units.val_mul, blkRep_blk, blkRep_blk, blkRep_blk, map_mul]
    rfl

theorem isIrredOn_blkRep (e : Fin a × ι ≃ Fin n) {σ : GL (Fin a) (ι → ℂ) →* (H →L[ℂ] H)}
    (hi : IsTopIrreducible σ) : Formalism.MainNotions.S.IsIrredOn (blkG e) (blkRep e σ) := fun S hS hinv =>
  hi.2 S ⟨hS, fun u v hv => by
    have h := hinv _ (blk_coe_mem e u) v hv
    rwa [blkRep_blk] at h⟩

theorem blk_mem_maxCpt (e : Fin a × ι ≃ Fin n) (k : Matrix.unitaryGroup (Fin a) (ι → ℂ)) :
    blk e k.1 ∈ GlobalTheory.LinRed.maxCpt (blkG e) := by
  refine ⟨blk_coe_mem e (Unitary.toUnits k), ?_⟩
  rw [SetLike.mem_coe, Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, ← blk_conjTranspose, ← blk_mul,
    ← Matrix.star_eq_conjTranspose, (Matrix.mem_unitaryGroup_iff).1 k.2, blk_one]

theorem exists_unitary_of_mem_maxCpt (e : Fin a × ι ≃ Fin n) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ GlobalTheory.LinRed.maxCpt (blkG e)) :
    ∃ k : Matrix.unitaryGroup (Fin a) (ι → ℂ), g = blk e k.1 := by
  obtain ⟨⟨M, -, rfl⟩, hu⟩ := hg
  refine ⟨⟨M, ?_⟩, rfl⟩
  rw [SetLike.mem_coe, Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, ← blk_conjTranspose, ← blk_mul,
    ← blk_one e, ← Matrix.star_eq_conjTranspose] at hu
  rw [Matrix.mem_unitaryGroup_iff]
  exact blk_injective e hu

theorem finiteDimensional_isoPart_gl [CompleteSpace H] {σ : GL (Fin a) (ι → ℂ) →* (H →L[ℂ] H)}
    (hσ : IsUnitaryRep σ) (hi : IsTopIrreducible σ) {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ (Matrix.unitaryGroup (Fin a) (ι → ℂ)) W) :
    FiniteDimensional ℂ (isoPart (σ.comp Unitary.toUnits) ρ) := by
  let e := Fintype.equivFin (Fin a × ι)
  have hLR : GlobalTheory.LinRed.IsLinRed (blkG e) := by
    refine
      { one_mem := ⟨1, isUnit_one, blk_one e⟩
        mul_mem := ?_
        isUnit := fun g hg => ((mem_blkG_iff e).1 hg).1
        inv_mem := ?_
        closed := fun g hg hcl => (mem_blkG_iff e).2 ⟨hg, blk_unblk_of_mem_closure e hcl⟩
        connected := isPreconnected_blkG e
        star_mem := ?_ }
    · rintro _ ⟨M, hM, rfl⟩ _ ⟨N, hN, rfl⟩
      exact ⟨M * N, IsUnit.mul hM hN, blk_mul e M N⟩
    · rintro _ ⟨M, hM, rfl⟩
      exact ⟨M⁻¹, (Matrix.isUnit_nonsing_inv_iff).2 hM, (blk_inv e hM).symm⟩
    · rintro _ ⟨M, hM, rfl⟩
      exact ⟨Mᴴ, IsUnit.star hM, blk_conjTranspose e M⟩
  have hA := GlobalTheory.CompanionTheory.admitted.isAdmissible_of_unitary_irreducible hLR
    (GlobalTheory.CompanionTheory.AdmIwa.RamifiedPrimeLengthBound hLR (GlobalTheory.CompanionTheory.IwaGen.iwaOn_of_isLinRed hLR)) H (blkRep e σ)
    (isURepOn_blkRep e hσ) (isIrredOn_blkRep e hi)
  have hrep : ∀ k : Matrix.unitaryGroup (Fin a) (ι → ℂ),
      blkRep e σ (blk e k.1) = (σ.comp Unitary.toUnits) k := fun k => blkRep_blk e σ (Unitary.toUnits k)
  refine finiteDimensional_isoPart (π := σ.comp Unitary.toUnits) (fun k v => hσ.norm_apply _ v) ?_ _ W ρ rfl
  intro S hfd hS hirr
  have hKS : GlobalTheory.LinRed.IsKStable (blkG e) (blkRep e σ) S := by
    intro g hg w hw
    obtain ⟨k, rfl⟩ := exists_unitary_of_mem_maxCpt e hg
    rw [hrep]
    exact hS k w hw
  have hirr' : ∀ S' : Submodule ℂ H, S' ≤ S → GlobalTheory.LinRed.IsKStable (blkG e) (blkRep e σ) S' → S' = ⊥ ∨ S' = S :=
    fun S' hle hst => hirr S' hle fun k w hw => by
      have h := hst _ (blk_mem_maxCpt e k) w hw
      rwa [hrep] at h
  have hfin := hA.2.2.2 S hfd hKS hirr'
  have heq : {S' : Submodule ℂ H | ∃ T : H →ₗ[ℂ] H, S' = S.map T ∧
      ∀ k, ∀ w ∈ S, T ((σ.comp Unitary.toUnits) k w) = (σ.comp Unitary.toUnits) k (T w)} =
      {S' | ∃ T : H →ₗ[ℂ] H, S' = S.map T ∧ ∀ k ∈ GlobalTheory.LinRed.maxCpt (blkG e), ∀ w ∈ S,
        T (blkRep e σ k w) = blkRep e σ k (T w)} := by
    ext S'
    constructor
    · rintro ⟨T, rfl, hT⟩
      refine ⟨T, rfl, fun g hg w hw => ?_⟩
      obtain ⟨k, rfl⟩ := exists_unitary_of_mem_maxCpt e hg
      rw [hrep]
      exact hT k w hw
    · rintro ⟨T, rfl, hT⟩
      refine ⟨T, rfl, fun k w hw => ?_⟩
      rw [← hrep]
      exact hT _ (blk_mem_maxCpt e k) w hw
  rw [heq]
  exact hfin

theorem admissible_GL_Cinf : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : GL (Fin a) (Cinf E) →* (H →L[ℂ] H)), IsUnitaryRep σ → IsTopIrreducible σ → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (Kinf E a) W), FiniteDimensional ℂ ↥(⨆ (T : W →ₗ[ℂ] H) (_ : ∀ k w, T (ρ k w) = σ (Unitary.toUnits k) (T w)), LinearMap.range T : Submodule ℂ H) := by
  intro E _ _ _ a H _ _ _ σ hσ hi W _ _ _ ρ
  classical
  exact finiteDimensional_isoPart_gl hσ hi ρ

end GlobalTheory.CompanionTheory.AdmGL

end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryKTypeFiniteStatement

section

@[expose] public section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

theorem _root_.GlobalTheory.T.unitary_K_type_finite : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : GL (Fin a) (Cinf E) →* (H →L[ℂ] H)), IsUnitaryRep σ → IsTopIrreducible σ → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (Kinf E a) W), FiniteDimensional ℂ ↥(⨆ (T : W →ₗ[ℂ] H) (_ : ∀ k w, T (ρ k w) = σ (Unitary.toUnits k) (T w)), LinearMap.range T : Submodule ℂ H) := by
  first | exact @GlobalTheory.CompanionTheory.AdmGL.admissible_GL_Cinf | exact GlobalTheory.CompanionTheory.AdmGL.admissible_GL_Cinf | (intros; apply GlobalTheory.CompanionTheory.AdmGL.admissible_GL_Cinf <;> assumption)
end
end
