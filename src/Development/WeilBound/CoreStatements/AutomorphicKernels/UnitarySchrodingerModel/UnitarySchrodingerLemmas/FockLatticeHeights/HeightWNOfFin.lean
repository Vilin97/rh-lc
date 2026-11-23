module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.FockLatticeHeights.HWDefs
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.SchrodingerMatching.PsiPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import GroundTheory.GlobalFields.CompletionAtPlace.Integers
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelParabolicUnnMatrixBlockUpperTriangular
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussMulUnitary
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CmTypeRestrictRealSubfieldInfinitePlaceBijective
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmDataIsCMExtAndGramIsHermND
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HalfPowerDetAbsRealDiagonalTorus
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StabiliserEqCentraliserCartan
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsArchEquivEq
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.BigCellDefs
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDecompositionUnitary

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.AlgebraMapEventually.LstdStd

section

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open NumberField IsDedekindDomain GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

namespace PositivityTheory.PfSWUS.SwsLstd

open PositivityTheory.PfSWUS.SwFockk

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem isCO_lstd (n : ℕ) (v : HeightOneSpectrum (𝓞 F)) : PositivityTheory.SiegelWeilFormula.Gen.IsCO (lstd F E n v) := by
  obtain ⟨hc, ho⟩ := GlobalTheory.ThK.isCompact_isOpen_intLoc (F := F) (E := E) v
  have e : (lstd F E n v : Set (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)) =
      Set.univ.pi fun _ => (GlobalTheory.AdelicU.intLoc F E v : Set (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)) := by
    ext y
    simp only [Set.mem_univ_pi]
    rfl
  refine ⟨?_, ?_⟩
  · rw [e]; exact isOpen_set_pi Set.finite_univ fun _ _ => ho
  · rw [e]; exact isCompact_univ_pi fun _ => hc

theorem eventually_algebraMap_mem (c : F) :
    ∀ᶠ v in Filter.cofinite, algebraMap F (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) c ∈ v.adicCompletionIntegers F :=
  (FiniteAdeleRing.algebraMap (𝓞 F) F c).2

theorem eventually_mem_intLoc_iff {d : ℕ} (bs : Module.Basis (Fin d) F E) :
    ∀ᶠ v in Filter.cofinite, ∀ z : HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E, z ∈ GlobalTheory.AdelicU.intLoc F E v ↔
      ∀ k, (Algebra.TensorProduct.basis (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) bs).repr z k ∈ v.adicCompletionIntegers F := by
  classical
  have hint : ∀ y : E, ∃ m : ℤ, m ≠ 0 ∧ IsIntegral ℤ ((m : F) • y) := fun y => by
    obtain ⟨m, hm, hi⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).2
      (Algebra.IsAlgebraic.isAlgebraic y)).exists_integral_multiple
    exact ⟨m, hm, by rwa [Int.cast_smul_eq_zsmul]⟩
  choose m hm hmi using hint
  let b := RingOfIntegers.basis E
  have h1 : ∀ᶠ v in Filter.cofinite, ∀ i k, algebraMap F (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v)
      (bs.repr ((b i : 𝓞 E) : E) k) ∈ v.adicCompletionIntegers F :=
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun k => eventually_algebraMap_mem _
  have h2 : ∀ᶠ v in Filter.cofinite, ∀ k, algebraMap F (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) ((m (bs k) : F))⁻¹ ∈
      v.adicCompletionIntegers F :=
    Filter.eventually_all.2 fun k => eventually_algebraMap_mem _
  filter_upwards [h1, h2] with v hv1 hv2 z
  set B := Algebra.TensorProduct.basis (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) bs
  constructor
  · intro hz
    refine GlobalTheory.AdelicU.intLoc_induction (p := fun y => ∀ k, B.repr y k ∈ v.adicCompletionIntegers F)
      ?_ ?_ ?_ ?_ hz
    · intro a ha x k
      rw [Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul]
      refine mul_mem ha ?_
      have hx : (x : E) = ∑ i, (b.repr x i) • ((b i : 𝓞 E) : E) := by
        conv_lhs => rw [← b.sum_repr x]

        simp only [map_sum, map_zsmul, RingOfIntegers.coe_eq_algebraMap]

      rw [hx, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply, map_sum]
      refine Subring.sum_mem _ fun i _ => ?_
      rw [map_zsmul, Finsupp.smul_apply, map_zsmul]
      exact zsmul_mem (hv1 i k) _
    · intro k; simp
    · intro y z hy hz k; rw [map_add (f := _), Finsupp.add_apply]; exact add_mem (hy k) (hz k)
    · intro y hy k; rw [map_neg, Finsupp.neg_apply]; exact neg_mem (hy k)
  · intro hz
    rw [← B.sum_repr z]
    refine Subring.sum_mem _ fun k _ => ?_
    have hm0 : ((m (bs k) : ℤ) : F) ≠ 0 := by exact_mod_cast hm (bs k)
    have e : B.repr z k • B k = (algebraMap F (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) ((m (bs k) : F))⁻¹ * B.repr z k) ⊗ₜ[F]
        ((⟨(m (bs k) : F) • bs k, hmi (bs k)⟩ : 𝓞 E) : E) := by
      rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one, ← Algebra.smul_def,
        TensorProduct.smul_tmul]
      congr 1
      change bs k = ((m (bs k) : F))⁻¹ • ((m (bs k) : F) • bs k)
      rw [smul_smul, inv_mul_cancel₀ hm0, one_smul]
    rw [e]
    exact GlobalTheory.AdelicU.tmul_mem_intLoc (E := E) (mul_mem (hv2 k) (hz k)) (⟨(m (bs k) : F) • bs k, hmi (bs k)⟩ : 𝓞 E)

theorem lstdStd : LstdStd := by
  intro F E _ _ _ _ _ n
  refine ⟨fun v => isCO_lstd n v, fun d bs => ?_⟩
  filter_upwards [eventually_mem_intLoc_iff bs] with v hv
  ext y
  change (∀ i, y i ∈ GlobalTheory.AdelicU.intLoc F E v) ↔ _
  simp only [PositivityTheory.PfSWUS.Loc.latO, Set.mem_ofPred_eq]
  exact forall_congr' fun a => hv (y a)

end PositivityTheory.PfSWUS.SwsLstd

end
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.BlockHeightDeterminants.HWInfA

section

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.PfSWUS.SwsHeight

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC NumberField IsDedekindDomain

variable {D : D7}

theorem blk4_map_alt {R S : Type} {n : ℕ} (f : R → S) (a b c d : Matrix (Fin n) (Fin n) R) :
    (blk4 a b c d).map f = blk4 (a.map f) (b.map f) (c.map f) (d.map f) := by
  unfold blk4
  rw [← Matrix.submatrix_map, Matrix.fromBlocks_map]

theorem block_matrix_conjTranspose {n : ℕ} (a b c d : Matrix (Fin n) (Fin n) ℂ) :
    (blk4 a b c d)ᴴ = blk4 aᴴ cᴴ bᴴ dᴴ := by
  unfold blk4
  rw [Matrix.conjTranspose_submatrix, Matrix.fromBlocks_conjTranspose]

theorem block_matrix_mul_comm_ring {R : Type} [CommRing R] {n : ℕ} (a b c d a' b' c' d' : Matrix (Fin n) (Fin n) R) :
    blk4 a b c d * blk4 a' b' c' d' =
      blk4 (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  unfold blk4
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem block_matrix_injective {R : Type} {n : ℕ} {a b c d a' b' c' d' : Matrix (Fin n) (Fin n) R}
    (h : blk4 a b c d = blk4 a' b' c' d') : a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  have := congrArg (fun M => Matrix.submatrix M finSumFinEquiv finSumFinEquiv) h
  simpa [blk4, Matrix.fromBlocks_inj] using this

theorem compAt_mul (θ : InfFam D) (τ : D.what₂.Tau) {k m n : ℕ} (x : Mx D k m) (y : Mx D m n) :
    compAt θ τ (x * y) = compAt θ τ x * compAt θ τ y :=
  Matrix.map_mul (f := (θ τ).comp (infPart D))

theorem compAt_one (θ : InfFam D) (τ : D.what₂.Tau) {k : ℕ} : compAt θ τ (1 : Mx D k k) = 1 :=
  Matrix.map_one _ (map_zero ((θ τ).comp (infPart D))) (map_one ((θ τ).comp (infPart D)))

theorem compAt_zero (θ : InfFam D) (τ : D.what₂.Tau) {k m : ℕ} : compAt θ τ (0 : Mx D k m) = 0 :=
  Matrix.map_zero _ (map_zero ((θ τ).comp (infPart D)))

theorem compAt_neg (θ : InfFam D) (τ : D.what₂.Tau) {k m : ℕ} (x : Mx D k m) : compAt θ τ (-x) = -compAt θ τ x :=
  Matrix.map_neg _ (map_neg ((θ τ).comp (infPart D))) x

theorem component_block_matrix (θ : InfFam D) (τ : D.what₂.Tau) {n : ℕ} (a b c d : Mx D n n) :
    compAt θ τ (blk4 a b c d) = blk4 (compAt θ τ a) (compAt θ τ b) (compAt θ τ c) (compAt θ τ d) :=
  blk4_map_alt _ a b c d

theorem compAt_K_unitary (θ : InfFam D) (hθ : IsInfFam θ) (n : ℕ) (k : G D n) (hk : k ∈ K D n) (τ : D.what₂.Tau) :
    (compAt θ τ (mat k))ᴴ * compAt θ τ (mat k) = 1 := by
  have e1 : compAt θ τ (mat k) = Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig (Jst D n) (θ τ) k := rfl
  have e2 : θ τ = GlobalTheory.AdelicU.infProj (embOverOf D τ) := GlobalTheory.AdelicU.eq_infProj hθ (embOverOf D τ) rfl
  have hk' : k ∈ GlobalTheory.AdelicU.levelAll D.sp.cm.sig (Jst D n) (stdLattice D.host.E (n + n)) 1 := hk
  have hw := (GlobalTheory.AdelicU.mem_levelAll.1 hk').2 (placeOf D τ)
  have hunit := (GlobalTheory.Doubling.mem_stabArch_iff_unitary (isCMExt_host D) (embOverOf D τ) (Jst D n) 1 k).1 hw
  rw [inv_one, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _),
    Matrix.map_one _ (map_zero _) (map_one _)] at hunit
  simp only [Matrix.one_mul, Matrix.mul_one] at hunit
  rw [← e2, ← e1] at hunit
  exact hunit

theorem local_det {n : ℕ} (α ai β β0 : Matrix (Fin n) (Fin n) ℂ) (U : Matrix (Fin (n + n)) (Fin (n + n)) ℂ)
    (hU : Uᴴ * U = 1) (hα : α * ai = 1) (hβ : βᴴ = β)
    (h : blk4 0 1 (-1) 0 * blk4 1 β 0 1 = blk4 α 0 0 aiᴴ * blk4 1 β0 0 1 * U) :
    ‖α.det‖ ^ 2 * (1 + β * β).det.re = 1 := by
  have hU' : U * Uᴴ = 1 := mul_eq_one_comm.1 hU
  have hM : (blk4 0 1 (-1) 0 * blk4 1 β 0 1 : Matrix (Fin (n + n)) (Fin (n + n)) ℂ) = blk4 0 1 (-1) (-β) := by
    rw [block_matrix_mul_comm_ring]; simp
  have hL : (blk4 α 0 0 aiᴴ * blk4 1 β0 0 1 : Matrix (Fin (n + n)) (Fin (n + n)) ℂ) = blk4 α (α * β0) 0 aiᴴ := by
    rw [block_matrix_mul_comm_ring]; simp
  rw [hM, hL] at h
  have hMM : blk4 0 1 (-1) (-β) * (blk4 0 1 (-1) (-β))ᴴ =
      blk4 α (α * β0) 0 aiᴴ * (blk4 α (α * β0) 0 aiᴴ)ᴴ := by
    rw [h, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc U, hU', Matrix.one_mul]
  rw [block_matrix_conjTranspose, block_matrix_conjTranspose, block_matrix_mul_comm_ring, block_matrix_mul_comm_ring] at hMM
  have h22 := (block_matrix_injective hMM).2.2.2
  have h22' : 1 + β * β = aiᴴ * ai := by
    simpa [hβ] using h22
  have hd : (1 + β * β).det = star ai.det * ai.det := by
    rw [h22', Matrix.det_mul, Matrix.det_conjTranspose]
  have hdet : α.det * ai.det = 1 := by rw [← Matrix.det_mul, hα, Matrix.det_one]
  have hre : (1 + β * β).det.re = ‖ai.det‖ ^ 2 := by
    rw [hd, Complex.star_def, Complex.conj_mul']
    norm_cast
  rw [hre, ← mul_pow, ← norm_mul, hdet, norm_one, one_pow]

end PositivityTheory.PfSWUS.SwsHeight

end
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.BlockHeightDeterminants.CompAtDet

section

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.PfSWUS.SwsHeight

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC NumberField IsDedekindDomain

variable {D : D7}

theorem prod_absEw {θ : InfFam D} (hθ : IsInfFam θ) (x : (AE D)ˣ) :
    ((∏ w' : InfinitePlace D.host.F, absEw D.host.F D.host.E w' (unitInf D.host.F D.host.E w' x) : ℝ≥0) : ℝ) =
      ∏ τ, ‖θ τ (infPart D (x : AE D))‖ ^ 2 := by
  have hcm := (GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm).1
  haveI := hcm.1
  have hw : ∀ τ : D.what₂.Tau, absEw D.host.F D.host.E
      (InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E)))
      (unitInf D.host.F D.host.E _ x) = ‖θ τ (infPart D (x : AE D))‖₊ ^ 2 := by
    intro τ
    let t' : GlobalTheory.AdelicU.EmbOver D.host.E (InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E))) :=
      ⟨tauE D τ, (InfinitePlace.embedding_mk_eq_of_isReal
        (InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal _))).symm⟩
    rw [absEw_eq_sq hcm t', GlobalTheory.AutFunCompare.isInfEmb_unique _ _ _ (hθ τ) (GlobalTheory.AdelicU.isInfEmb_infProj t')]
    exact congrArg (fun z : ℂ => ‖z‖₊ ^ 2) (GlobalTheory.HalfModTorus.compInf_eq _ t' _)
  rw [← (GlobalTheory.CMTypePlaces.places_bijective D).prod_comp
    (fun w => absEw D.host.F D.host.E w (unitInf D.host.F D.host.E w x))]
  simp only [hw]
  push_cast
  rfl

theorem compAt_det (θ : InfFam D) (τ : D.what₂.Tau) {n : ℕ} (a : GL (Fin n) (AE D)) :
    θ τ (infPart D ((Matrix.GeneralLinearGroup.det a : (AE D)ˣ) : AE D)) = (compAt θ τ a.1).det := by
  change ((θ τ).comp (infPart D)) a.1.det = _
  rw [RingHom.map_det]
  rfl

theorem hwInf : PositivityTheory.PfSWUS.SwFockk.HWInf := by
  intro D n θ hθ w hw nb hnb b p k hp hk hwk a ha
  obtain ⟨m, u, b0, rfl, hm, hu⟩ := GlobalTheory.StdUnn.LeftInvSect.exists_levi_unip hp a ha
  have hloc : ∀ τ, ‖(compAt θ τ a.1).det‖ ^ 2 * (1 + compAt θ τ b.1 * compAt θ τ b.1).det.re = 1 := by
    intro τ
    have e : compAt θ τ (mat w * mat (nb b)) = compAt θ τ (mat m * mat u * mat k) := by
      have := congrArg (fun g => compAt θ τ (mat g)) hwk
      exact this
    rw [compAt_mul, compAt_mul, compAt_mul, hw, hnb b, hm, hu] at e
    simp only [component_block_matrix, compAt_zero, compAt_one, compAt_neg, GlobalTheory.VacKInf.LeviFix.compAt_adj' hθ] at e
    refine local_det (compAt θ τ a.1) (compAt θ τ (a⁻¹).1) (compAt θ τ b.1) (compAt θ τ b0) (compAt θ τ (mat k))
      (compAt_K_unitary θ hθ n k hk τ) ?_ ?_ e
    · rw [← compAt_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, compAt_one]
    · have hb : adj b.1 = b.1 := b.2
      rw [← GlobalTheory.VacKInf.LeviFix.compAt_adj' hθ, hb]
  rw [prod_absEw hθ]
  unfold PositivityTheory.SiegelWeilFormula.Gen.nuInf
  have hm' : ∀ τ, (PositivityTheory.SiegelWeilFormula.Gen.matInf b.1).map (θ τ) = compAt θ τ b.1 := fun τ => by ext i j; rfl
  simp only [inv_one, Units.val_one, Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one, hm']
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun τ _ => by rw [compAt_det]; exact hloc τ

end PositivityTheory.PfSWUS.SwsHeight

end
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.FockLatticeHeights.HWGlue

section

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.PfSWUS.SwFockk

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC NumberField IsDedekindDomain



theorem heightWN_of (hF : HWFin) (hI : HWInf) (hL : LstdStd) : PositivityTheory.PfSWUS.SwMatch.HeightWN := by
  intro D n H hH θ hθ nb hnb w hw
  refine ⟨lstd D.host.F D.host.E n, (hL D.host.F D.host.E n).1, fun d bs => (hL D.host.F D.host.E n).2 d bs, ?_⟩
  intro lam hlam b
  obtain ⟨p, hp, k, hk, hpk⟩ := GlobalTheory.StdUnn.Iwasawa.exists_mul D n (w * nb b)
  obtain ⟨a, ha⟩ := GlobalTheory.StdUnn.LeftInvSect.exists_blkA hp
  have hH' : H (w * nb b) = absA D (Matrix.GeneralLinearGroup.det a) := by
    rw [hpk]; exact hH p hp a ha k hk
  have hX : ((H (w * nb b) : ℝ≥0) : ℝ) =
      ((∏ w' : NumberField.InfinitePlace D.host.F, GlobalTheory.Doubling.absEw D.host.F D.host.E w'
        (GlobalTheory.Doubling.unitInf D.host.F D.host.E w' (Matrix.GeneralLinearGroup.det a)) : ℝ≥0) : ℝ) *
      ∏ᶠ v, ((GlobalTheory.Doubling.absEv D.host.F D.host.E v (GlobalTheory.Doubling.unitFin D.host.F D.host.E v
        (Matrix.GeneralLinearGroup.det a)) : ℝ≥0) : ℝ) := by
    rw [hH']
    change ((GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det a) : ℝ≥0) : ℝ) = _
    rw [GlobalTheory.Doubling.absE_apply, NNReal.coe_mul]
    congr 1
    exact MonoidHom.map_finprod_of_injective NNReal.toRealHom.toMonoidHom NNReal.coe_injective _
  have h1 := hI D n θ hθ w hw nb hnb b p k hp hk hpk a ha
  have h2 := fun v => hF D n w hw nb hnb b p k hp hk hpk a ha v (lam v) (hlam v)
  rw [hX, PositivityTheory.SiegelWeilFormula.Gen.nuA, finprod_congr h2, finprod_inv_distrib, mul_inv]
  congr 1
  exact (eq_inv_of_mul_eq_one_right h1).symm

end PositivityTheory.PfSWUS.SwFockk

end
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.FockLatticeHeights.HeightWNOfFin

section

@[expose] public section

namespace PositivityTheory.PfSWUS.SwFockk

theorem heightWN_of_fin (h : HWFin) : PositivityTheory.PfSWUS.SwMatch.HeightWN :=
  heightWN_of h PositivityTheory.PfSWUS.SwsHeight.hwInf PositivityTheory.PfSWUS.SwsLstd.lstdStd

end PositivityTheory.PfSWUS.SwFockk
end
end
