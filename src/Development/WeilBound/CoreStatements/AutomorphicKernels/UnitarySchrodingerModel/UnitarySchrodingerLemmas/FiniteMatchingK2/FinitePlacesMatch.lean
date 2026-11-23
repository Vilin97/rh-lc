module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.SchrodingerMatching.PsiPlaces
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhitGenOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiplicityLevelFormula
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
import Mathlib.Topology.Sheaves.Init
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.FockLatticeHeights.IntAtEventually
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
import GroundTheory.GlobalFields.LocalFieldAtPlace
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensTop
import GroundTheory.GlobalFields.LocalAtPlace

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.FockLatticeHeights.LatticeNormMatrixConj

section

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory
open scoped Matrix ENNReal NNReal

namespace GlobalTheory.CompanionTheory.SwFinM

section Scale

variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R]
  [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R] {n : ℕ}

def mulVecHomeo (A Ai : Matrix (Fin n) (Fin n) R) (h1 : A * Ai = 1) (h2 : Ai * A = 1) : (Fin n → R) ≃ₜ (Fin n → R) where
  toFun x := A *ᵥ x
  invFun x := Ai *ᵥ x
  left_inv x := by simp [Matrix.mulVec_mulVec, h2]
  right_inv x := by simp [Matrix.mulVec_mulVec, h1]
  continuous_toFun := continuous_const.matrix_mulVec continuous_id
  continuous_invFun := continuous_const.matrix_mulVec continuous_id

def mulVecCAE (A Ai : Matrix (Fin n) (Fin n) R) (h1 : A * Ai = 1) (h2 : Ai * A = 1) : (Fin n → R) ≃ₜ+ (Fin n → R) :=
  { (mulVecHomeo A Ai h1 h2).toEquiv with
    map_add' := fun x y => Matrix.mulVec_add A x y
    continuous_toFun := (mulVecHomeo A Ai h1 h2).continuous
    continuous_invFun := (mulVecHomeo A Ai h1 h2).symm.continuous }

theorem image_eq_preimage (A Ai : Matrix (Fin n) (Fin n) R) (h1 : A * Ai = 1) (h2 : Ai * A = 1) (S : Set (Fin n → R)) :
    (fun x => A *ᵥ x) '' S = (fun x => Ai *ᵥ x) ⁻¹' S := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    show Ai *ᵥ (A *ᵥ y) ∈ S
    rwa [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]
  · intro hx
    refine ⟨Ai *ᵥ x, hx, ?_⟩
    show A *ᵥ (Ai *ᵥ x) = x
    rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]

theorem exists_scale (lam : Measure (Fin n → R)) [lam.IsAddHaarMeasure] (A Ai : Matrix (Fin n) (Fin n) R)
    (h1 : A * Ai = 1) (h2 : Ai * A = 1) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ S : Set (Fin n → R), lam ((fun x => A *ᵥ x) '' S) = c * lam S := by
  let e : (Fin n → R) ≃ₜ+ (Fin n → R) := mulVecCAE Ai A h2 h1
  have hcoc : Filter.Tendsto (e : (Fin n → R) → (Fin n → R)) (Filter.cocompact _) (Filter.cocompact _) :=
    (mulVecHomeo Ai A h2 h1).isClosedEmbedding.tendsto_cocompact
  have : (lam.map e).IsAddHaarMeasure :=
    Measure.isAddHaarMeasure_map lam (e : (Fin n → R) →+ (Fin n → R)) e.continuous e.surjective hcoc
  have hsm := Measure.isAddLeftInvariant_eq_smul (lam.map e) lam
  set c : ℝ≥0 := (lam.map e).addHaarScalarFactor lam
  have hmap : ∀ S : Set (Fin n → R), (lam.map e) S = lam ((fun x => Ai *ᵥ x) ⁻¹' S) := fun S =>
    MeasurableEquiv.map_apply (mulVecHomeo Ai A h2 h1).toMeasurableEquiv S
  have key : ∀ S : Set (Fin n → R), lam ((fun x => A *ᵥ x) '' S) = (c : ℝ≥0∞) * lam S := by
    intro S
    rw [image_eq_preimage A Ai h1 h2, ← hmap, hsm]
    rfl
  refine ⟨c, ?_, ENNReal.coe_ne_top, key⟩
  intro h0
  have hu := key Set.univ
  rw [h0, zero_mul, Set.image_univ_of_surjective (f := fun x => A *ᵥ x) (mulVecHomeo A Ai h1 h2).surjective] at hu
  exact isOpen_univ.measure_ne_zero lam Set.univ_nonempty hu

end Scale

section Index

variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R]
  [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R] {n : ℕ}

theorem lattice_norm_matrix_conj (lam : Measure (Fin n → R)) [lam.IsAddHaarMeasure] (L : AddSubgroup (Fin n → R))
    (A Ai A' C B : Matrix (Fin n) (Fin n) R) (h1 : A * Ai = 1) (h2 : Ai * A = 1) (hAC : A' * C = 1) :
    PositivityTheory.SiegelWeilFormula.Gen.nu2 lam (L.map (Matrix.mulVecLin A).toAddMonoidHom) (L.map (Matrix.mulVecLin C).toAddMonoidHom)
      (A * B * A') = PositivityTheory.SiegelWeilFormula.Gen.nu2 lam L L B := by
  obtain ⟨c, hc0, hct, hc⟩ := exists_scale lam A Ai h1 h2
  have hS : {x | ∃ y ∈ L.map (Matrix.mulVecLin A).toAddMonoidHom, ∃ y' ∈ L.map (Matrix.mulVecLin C).toAddMonoidHom,
      x = y + (A * B * A').mulVec y'} = (fun x => A *ᵥ x) '' {x | ∃ y ∈ L, ∃ y' ∈ L, x = y + B.mulVec y'} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_image, AddSubgroup.mem_map]
    constructor
    · rintro ⟨_, ⟨u, hu, rfl⟩, _, ⟨u', hu', rfl⟩, rfl⟩
      refine ⟨u + B *ᵥ u', ⟨u, hu, u', hu', rfl⟩, ?_⟩
      simp only [LinearMap.toAddMonoidHom_coe, Matrix.mulVecLin_apply, Matrix.mulVec_add, Matrix.mulVec_mulVec]
      rw [Matrix.mul_assoc A B A', Matrix.mul_assoc A (B * A') C, Matrix.mul_assoc B A' C, hAC, Matrix.mul_one]
    · rintro ⟨_, ⟨u, hu, u', hu', rfl⟩, rfl⟩
      refine ⟨A *ᵥ u, ⟨u, hu, rfl⟩, C *ᵥ u', ⟨u', hu', rfl⟩, ?_⟩
      simp only [Matrix.mulVec_add, Matrix.mulVec_mulVec]
      rw [Matrix.mul_assoc A B A', Matrix.mul_assoc A (B * A') C, Matrix.mul_assoc B A' C, hAC, Matrix.mul_one]
  have hL : ((L.map (Matrix.mulVecLin A).toAddMonoidHom : AddSubgroup (Fin n → R)) : Set (Fin n → R)) =
      (fun x => A *ᵥ x) '' (L : Set (Fin n → R)) := by
    rw [AddSubgroup.coe_map]
    rfl
  unfold PositivityTheory.SiegelWeilFormula.Gen.nu2
  rw [hS, hL, hc, hc, ENNReal.mul_div_mul_left _ _ hc0 hct]

end Index

end GlobalTheory.CompanionTheory.SwFinM

end
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.FockLatticeHeights.MemLatVIff

section

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.SwFinM

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem compV_apply (v : HeightOneSpectrum (𝓞 F)) (y : HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E) :
    compV v y = Algebra.TensorProduct.map (HeckeCharacterZeroLocus.SiegelWeilU.evalV F v) (AlgHom.id F E)
      (Algebra.TensorProduct.map (HeckeCharacterZeroLocus.SiegelWeilU.sndA F) (AlgHom.id F E) y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

section Tup

variable {d : ℕ} {bs : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)} {n M : ℕ}

theorem mem_latV_iff (Y : Fin n → Fin M → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) :
    Y ∈ HeckeCharacterZeroLocus.SiegelWeilU.latV (M := M) (n := n) bs v ↔ ∀ a i, Y a i ∈ PositivityTheory.SiegelWeilFormula.Gunr.Rv bs v := Iff.rfl

theorem mul_mem_latV {σ : E →ₐ[F] E} (h : PositivityTheory.SiegelWeilFormula.Gunr.IntAt v (PositivityTheory.SiegelWeilFormula.Gunr.basisSet σ bs))
    (X : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)) (hX : ∀ i j, X i j ∈ PositivityTheory.SiegelWeilFormula.Gunr.Rv bs v)
    (Y : Fin n → Fin M → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) (hY : Y ∈ HeckeCharacterZeroLocus.SiegelWeilU.latV (M := M) (n := n) bs v) :
    (HMul.hMul (α := Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E))
      (β := Matrix (Fin n) (Fin M) (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)) X Y : Fin n → Fin M → _) ∈
      HeckeCharacterZeroLocus.SiegelWeilU.latV (M := M) (n := n) bs v := by
  have hY' := (mem_latV_iff Y).1 hY
  refine (mem_latV_iff _).2 fun j i => ?_
  have e : (HMul.hMul (α := Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E))
      (β := Matrix (Fin n) (Fin M) (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)) X Y) j i = ∑ c, X j c * Y c i := rfl
  rw [e]
  have hs : (∑ c, X j c * Y c i) ∈ GlobalTheory.CompanionTheory.RvRingPf.ringOf h :=
    Subring.sum_mem _ fun c _ => Subring.mul_mem _ ((mem_ringOf h _).2 (hX j c)) ((mem_ringOf h _).2 (hY' c i))
  exact (mem_ringOf h _).1 hs

def lmulHomeo (X Xi : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)) (h1 : X * Xi = 1) (h2 : Xi * X = 1) :
    (Fin n → Fin M → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) ≃ₜ (Fin n → Fin M → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) where
  toFun Y := (HMul.hMul (α := Matrix (Fin n) (Fin n) _) (β := Matrix (Fin n) (Fin M) _) X Y : Matrix (Fin n) (Fin M) _)
  invFun Y := (HMul.hMul (α := Matrix (Fin n) (Fin n) _) (β := Matrix (Fin n) (Fin M) _) Xi Y : Matrix (Fin n) (Fin M) _)
  left_inv Y := by
    show HMul.hMul (α := Matrix (Fin n) (Fin n) _) (β := Matrix (Fin n) (Fin M) _) Xi
      (HMul.hMul (α := Matrix (Fin n) (Fin n) _) (β := Matrix (Fin n) (Fin M) _) X Y) = Y
    exact (Matrix.mul_assoc Xi X (Matrix.of Y)).symm.trans
      (by rw [h2, Matrix.one_mul] : (Xi * X) * Matrix.of Y = Matrix.of Y)
  right_inv Y := by
    show HMul.hMul (α := Matrix (Fin n) (Fin n) _) (β := Matrix (Fin n) (Fin M) _) X
      (HMul.hMul (α := Matrix (Fin n) (Fin n) _) (β := Matrix (Fin n) (Fin M) _) Xi Y) = Y
    exact (Matrix.mul_assoc X Xi (Matrix.of Y)).symm.trans
      (by rw [h1, Matrix.one_mul] : (X * Xi) * Matrix.of Y = Matrix.of Y)
  continuous_toFun := continuous_const.matrix_mul continuous_id
  continuous_invFun := continuous_const.matrix_mul continuous_id

end Tup

section Parts

variable {n M : ℕ}

theorem projV_lmul (v : HeightOneSpectrum (𝓞 F)) (A : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E))
    (X : Fin n → Fin M → HeckeCharacterZeroLocus.SiegelWeilU.Af F ⊗[F] E) :
    HeckeCharacterZeroLocus.SiegelWeilU.projV v (fun j i => ∑ c, Algebra.TensorProduct.map (HeckeCharacterZeroLocus.SiegelWeilU.sndA F) (AlgHom.id F E) (A c j) * X c i) =
      fun j i => ∑ c, PositivityTheory.SiegelWeilFormula.Gen.matV v A c j * HeckeCharacterZeroLocus.SiegelWeilU.projV v X c i := by
  funext j i

  simp only [HeckeCharacterZeroLocus.SiegelWeilU.projV, map_sum, map_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  exact (compV_apply v (A c j)).symm

theorem finPart_mul (x : Matrix (Fin M) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E))
    (A : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E)) :
    (fun i j => Algebra.TensorProduct.map (HeckeCharacterZeroLocus.SiegelWeilU.sndA F) (AlgHom.id F E) ((x * A) i j)) =
      fun i j => ∑ c, Algebra.TensorProduct.map (HeckeCharacterZeroLocus.SiegelWeilU.sndA F) (AlgHom.id F E) (A c j) *
        Algebra.TensorProduct.map (HeckeCharacterZeroLocus.SiegelWeilU.sndA F) (AlgHom.id F E) (x i c) := by
  funext i j

  rw [Matrix.mul_apply, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_mul, mul_comm]

end Parts

end GlobalTheory.CompanionTheory.SwFinM

end
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.FockLatticeHeights.FinMatchGen

section

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.SwFinM

section Gen

variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R]
  [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R] {n : ℕ}

theorem isCO_map (L : AddSubgroup (Fin n → R)) (hL : PositivityTheory.SiegelWeilFormula.Gen.IsCO L) (X Xi : Matrix (Fin n) (Fin n) R)
    (h1 : X * Xi = 1) (h2 : Xi * X = 1) : PositivityTheory.SiegelWeilFormula.Gen.IsCO (L.map (Matrix.mulVecLin X).toAddMonoidHom) := by
  have e : ((L.map (Matrix.mulVecLin X).toAddMonoidHom : AddSubgroup (Fin n → R)) : Set (Fin n → R)) =
      (mulVecHomeo X Xi h1 h2) '' (L : Set (Fin n → R)) := by
    rw [AddSubgroup.coe_map]
    rfl
  unfold PositivityTheory.SiegelWeilFormula.Gen.IsCO
  rw [e]
  exact ⟨(mulVecHomeo X Xi h1 h2).isOpenMap _ hL.1, hL.2.image (mulVecHomeo X Xi h1 h2).continuous⟩

end Gen

section Comp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem matV_mul (v : HeightOneSpectrum (𝓞 F)) (X Y : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E)) :
    PositivityTheory.SiegelWeilFormula.Gen.matV v (X * Y) = PositivityTheory.SiegelWeilFormula.Gen.matV v X * PositivityTheory.SiegelWeilFormula.Gen.matV v Y := by
  rw [matV_eq, matV_eq, matV_eq, map_mul]

theorem matV_one (v : HeightOneSpectrum (𝓞 F)) :
    PositivityTheory.SiegelWeilFormula.Gen.matV v (1 : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E)) = 1 := by
  rw [matV_eq, map_one]

theorem finMatchGen {M : ℕ} (a ai a' ai' : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E))
    (ha1 : a * ai = 1) (ha2 : ai * a = 1) (hc1 : a' * ai' = 1) (hc2 : ai' * a' = 1) {d : ℕ}
    (bs : Module.Basis (Fin d) F E) (g : (Fin M → Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Af F ⊗[F] E) → ℂ)
    (gv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) → ℂ)
    (hP : HeckeCharacterZeroLocus.SiegelWeilU.IsPureFin bs (fun X => g fun i j => X j i) gv)
    (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E))
    (L : ∀ v : HeightOneSpectrum (𝓞 F), AddSubgroup (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E))
    (hlam : ∀ v, (lam v).IsAddHaarMeasure) (hL : ∀ v, PositivityTheory.SiegelWeilFormula.Gen.IsCO (L v))
    (hstd : ∀ᶠ v in Filter.cofinite, (L v : Set (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)) = PositivityTheory.PfSWUS.Loc.latO bs v) :
    ∃ (L₁ L₂ : ∀ v : HeightOneSpectrum (𝓞 F), AddSubgroup (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E))
      (Φf : (Fin n → Fin M → HeckeCharacterZeroLocus.SiegelWeilU.Af F ⊗[F] E) → ℂ)
      (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) → ℂ),
      (∀ v, PositivityTheory.SiegelWeilFormula.Gen.IsCO (L₁ v) ∧ PositivityTheory.SiegelWeilFormula.Gen.IsCO (L₂ v)) ∧
      (∀ᶠ v in Filter.cofinite,
        (L₁ v : Set (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)) = PositivityTheory.PfSWUS.Loc.latO bs v ∧
        (L₂ v : Set (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)) = PositivityTheory.PfSWUS.Loc.latO bs v) ∧
      HeckeCharacterZeroLocus.SiegelWeilU.IsPureFin bs Φf Φv ∧
      (∀ x : Matrix (Fin M) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E),
        g (fun i j => Algebra.TensorProduct.map (HeckeCharacterZeroLocus.SiegelWeilU.sndA F) (AlgHom.id F E) ((x * a) i j)) =
          Φf (fun c i => Algebra.TensorProduct.map (HeckeCharacterZeroLocus.SiegelWeilU.sndA F) (AlgHom.id F E) (x i c))) ∧
      ∀ v (B : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E)),
        PositivityTheory.SiegelWeilFormula.Gen.nu2 (lam v) (L₁ v) (L₂ v) (PositivityTheory.SiegelWeilFormula.Gen.matV v (a * B * a')) =
          PositivityTheory.SiegelWeilFormula.Gen.nu2 (lam v) (L v) (L v) (PositivityTheory.SiegelWeilFormula.Gen.matV v B) := by
  have hA1 : ∀ v, PositivityTheory.SiegelWeilFormula.Gen.matV v a * PositivityTheory.SiegelWeilFormula.Gen.matV v ai = 1 := fun v => by
    rw [← matV_mul, ha1, matV_one]
  have hA2 : ∀ v, PositivityTheory.SiegelWeilFormula.Gen.matV v ai * PositivityTheory.SiegelWeilFormula.Gen.matV v a = 1 := fun v => by
    rw [← matV_mul, ha2, matV_one]
  have hC1 : ∀ v, PositivityTheory.SiegelWeilFormula.Gen.matV v a' * PositivityTheory.SiegelWeilFormula.Gen.matV v ai' = 1 := fun v => by
    rw [← matV_mul, hc1, matV_one]
  have hC2 : ∀ v, PositivityTheory.SiegelWeilFormula.Gen.matV v ai' * PositivityTheory.SiegelWeilFormula.Gen.matV v a' = 1 := fun v => by
    rw [← matV_mul, hc2, matV_one]
  have hT1 : ∀ v, (PositivityTheory.SiegelWeilFormula.Gen.matV v a)ᵀ * (PositivityTheory.SiegelWeilFormula.Gen.matV v ai)ᵀ = 1 := fun v => by
    rw [← Matrix.transpose_mul, hA2 v, Matrix.transpose_one]
  have hT2 : ∀ v, (PositivityTheory.SiegelWeilFormula.Gen.matV v ai)ᵀ * (PositivityTheory.SiegelWeilFormula.Gen.matV v a)ᵀ = 1 := fun v => by
    rw [← Matrix.transpose_mul, hA1 v, Matrix.transpose_one]
  refine ⟨fun v => (L v).map (Matrix.mulVecLin (PositivityTheory.SiegelWeilFormula.Gen.matV v a)).toAddMonoidHom,
    fun v => (L v).map (Matrix.mulVecLin (PositivityTheory.SiegelWeilFormula.Gen.matV v ai')).toAddMonoidHom,
    fun X => g (fun i j => ∑ c, Algebra.TensorProduct.map (HeckeCharacterZeroLocus.SiegelWeilU.sndA F) (AlgHom.id F E) (a c j) * X c i),
    fun v Y => gv v (fun j i => ∑ c, PositivityTheory.SiegelWeilFormula.Gen.matV v a c j * Y c i),
    ?_, ?_, ⟨fun v => ?_, ?_, fun X => ?_⟩, fun x => ?_, fun v B => ?_⟩
  ·
    intro v
    have := GlobalTheory.CompanionTheory.SiegLoc.NuIndex.secondCountable_tens bs v
    exact ⟨isCO_map (L v) (hL v) _ _ (hA1 v) (hA2 v), isCO_map (L v) (hL v) _ _ (hC2 v) (hC1 v)⟩
  ·
    filter_upwards [hstd, intAt_eventually bs, matV_mem_Rv bs a, matV_mem_Rv bs ai,
      matV_mem_Rv bs a', matV_mem_Rv bs ai'] with v hLv hI h1 h2 h3 h4
    constructor
    · refine (AddSubgroup.coe_map _ _).trans ?_
      show (fun y => PositivityTheory.SiegelWeilFormula.Gen.matV v a *ᵥ y) '' (L v : Set _) = _
      rw [hLv]
      exact image_latO hI _ _ h1 h2 (hA1 v)
    · refine (AddSubgroup.coe_map _ _).trans ?_
      show (fun y => PositivityTheory.SiegelWeilFormula.Gen.matV v ai' *ᵥ y) '' (L v : Set _) = _
      rw [hLv]
      exact image_latO hI _ _ h4 h3 (hC2 v)
  ·
    have := GlobalTheory.CompanionTheory.SiegLoc.NuIndex.secondCountable_tens bs v
    let T := lmulHomeo (M := M) (v := v) _ _ (hT1 v) (hT2 v)
    exact ⟨(hP.1 v).1.comp_continuous T.continuous, (hP.1 v).2.comp_homeomorph T⟩
  ·
    filter_upwards [hP.2.1, intAt_eventually bs, matV_mem_Rv bs a, matV_mem_Rv bs ai] with v hg hI h1 h2
    funext Y
    let T := lmulHomeo (M := M) (v := v) _ _ (hT1 v) (hT2 v)
    have hiff : T Y ∈ HeckeCharacterZeroLocus.SiegelWeilU.latV (M := M) (n := n) bs v ↔ Y ∈ HeckeCharacterZeroLocus.SiegelWeilU.latV (M := M) (n := n) bs v := by
      constructor
      · intro hy
        have := mul_mem_latV hI (PositivityTheory.SiegelWeilFormula.Gen.matV v ai)ᵀ (fun i j => h2 j i) (T Y) hy
        rwa [show (HMul.hMul (α := Matrix (Fin n) (Fin n) _) (β := Matrix (Fin n) (Fin M) _)
          (PositivityTheory.SiegelWeilFormula.Gen.matV v ai)ᵀ (T Y) : Fin n → Fin M → _) = Y from T.left_inv Y] at this
      · intro hy
        exact mul_mem_latV hI (PositivityTheory.SiegelWeilFormula.Gen.matV v a)ᵀ (fun i j => h1 j i) Y hy
    show gv v (T Y) = _
    rw [hg]
    by_cases hy : Y ∈ HeckeCharacterZeroLocus.SiegelWeilU.latV (M := M) (n := n) bs v
    · rw [Set.indicator_of_mem (hiff.2 hy), Set.indicator_of_mem hy]
      rfl
    · rw [Set.indicator_of_notMem (fun h => hy (hiff.1 h)), Set.indicator_of_notMem hy]
  ·
    refine (hP.2.2 (fun j i => ∑ c, Algebra.TensorProduct.map (HeckeCharacterZeroLocus.SiegelWeilU.sndA F) (AlgHom.id F E) (a c j) * X c i)).trans
      (finprod_congr fun v => ?_)
    exact congrArg (gv v) (projV_lmul v a X)
  ·
    exact congrArg g (finPart_mul x a)
  ·
    have := hlam v
    have := GlobalTheory.CompanionTheory.SiegLoc.NuIndex.secondCountable_tens bs v
    rw [matV_mul, matV_mul]
    exact lattice_norm_matrix_conj (lam v) (L v) _ _ _ _ _ (hA1 v) (hA2 v) (hC1 v)

end Comp

end GlobalTheory.CompanionTheory.SwFinM

end
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.FiniteMatchingK2.FinitePlacesMatch

section

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.PfSWUS.KFinMatch

theorem adj_one_k {D : D7} {n : ℕ} : adj (1 : Mx D n n) = 1 := by
  show ((1 : Matrix (Fin n) (Fin n) (AE D)).map (cA D))ᵀ = 1
  rw [Matrix.map_one (cA D) (map_zero (cA D)) (map_one (cA D)), Matrix.transpose_one]



theorem finite_places_match : PositivityTheory.PfSWUS.SwMatch.FinMatch := by
  intro D n M a d bs g gv hP lam L hlam hL hstd
  have ha1 : a.1 * (a⁻¹).1 = 1 := a.mul_inv
  have ha2 : (a⁻¹).1 * a.1 = 1 := a.inv_mul
  have hadj1 : adj (D := D) a.1 * adj (D := D) (a⁻¹).1 = 1 := by rw [← adj_mul, ha2, adj_one_k]
  have hadj2 : adj (D := D) (a⁻¹).1 * adj (D := D) a.1 = 1 := by rw [← adj_mul, ha1, adj_one_k]
  obtain ⟨L₁, L₂, Φf, Φv, h1, h2, h3, h4, h5⟩ := GlobalTheory.CompanionTheory.SwFinM.finMatchGen (F := D.host.F) (E := D.host.E) (M := M)
    a.1 (a⁻¹).1 (adj (D := D) a.1) (adj (D := D) (a⁻¹).1) ha1 ha2 hadj1 hadj2 bs g gv hP lam L hlam hL hstd
  exact ⟨L₁, L₂, Φf, Φv, h1, h2, h3, fun x => h4 x, fun v b => h5 v b.1⟩

end PositivityTheory.PfSWUS.KFinMatch

end
end
end
