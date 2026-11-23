module

public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Imports
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StArchCovolumeBound
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StComplementLattice
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StLineNormalForm
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StMajorantTransport
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StReducedBasisBound
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsAdelicLattices
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsArchUnimodular
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsComplementExtension
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsHaarParabolicCoordinates
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsLineStabHaar
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsMajorantStabCompact
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsSemidirectCovering
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsStabilizerCovolume
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsStabilizerLevi
public import Mathlib.Topology.Algebra.Group.Units
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Assembly
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PAdelicLatticeDictionary
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StCoordEmbedBasis
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StIntegralFormCovolume
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StTraceHermNondegenerate
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StDualLatticeMultiple
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StCoordLatticeFullRank
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PArchimedeanUnitaryEquiv
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PComplementExtension
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PComplementLattice
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PCoordEmbedBasis
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PDoubleCosetCovolume
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PDualLatticeMultiple
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PHaarParabolicCoordinates
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PIntegralFormCovolume
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PLatticePointsBelowFinite
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PLineNormalForm
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PMajorantTransport
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PReducedBasisBound
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PStabilizerCovolume
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnfoldAlongSubgroup

-- Source module: GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PArchCovolumeBound

section

@[expose] public section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module MeasureTheory

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]


omit [NumberField F] [IsTotallyReal F] [DecidableEq ι] in
theorem ArchCovolumeBound.proof (h : HermitianForm F E W) (v : Basis ι E W)
    (h₁ : CoordEmbedBasis.Statement E ι)
    (h₂ : IntegralFormCovolume.Statement (ι → E) (InfinitePlace E → ι → ℂ)
      (Σ _ : ι, Free.ChooseBasisIndex ℤ (𝓞 E)))
    (h₃ : TraceHermNondegenerate.Statement h v) (h₄ : DualLatticeMultiple.Statement h)
    (h₅ : CoordLatticeFullRank.Statement v) : ArchCovolumeBound.Statement h v := by
  intro D
  obtain ⟨k, hk0, hk⟩ := h₄ D
  let e := Pi.basis fun _ : ι => integralBasis E
  obtain ⟨C, hC⟩ := h₂ (coordEmbed E ι) e (traceHerm h v) volume (Measure.pi.isAddHaarMeasure _) h₃ h₁.1
    (by rw [h₁.2, finrank_eq_card_basis e])
  refine ⟨Real.sqrt (C * |(k : ℝ)| ^ Fintype.card (Σ _ : ι, Free.ChooseBasisIndex ℤ (𝓞 E))),
    fun La hLa => ?_⟩
  let φ : W →+ (ι → E) := (v.equivFun : W →ₗ[E] ι → E).toAddMonoidHom
  have hφ : ∀ x, v.equivFun.symm (φ x) = x := fun x => v.equivFun.symm_apply_apply x
  have hmem : ∀ y, y ∈ La.map φ ↔ v.equivFun.symm y ∈ La := by
    intro y
    rw [AddSubgroup.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rwa [hφ]
    · intro hy
      exact ⟨_, hy, v.equivFun.apply_symm_apply y⟩
  have harch : archLattice v La = AddSubgroup.toIntSubmodule ((La.map φ).map (coordEmbed E ι)) := by
    rw [archLattice, AddSubgroup.map_map]
    rfl
  obtain ⟨hfg, hspan⟩ := h₅ La hLa.isLattice
  obtain ⟨hint, hdual⟩ := hk La hLa
  obtain ⟨hD, hZ, hcov⟩ := hC (La.map φ) k hk0 hfg hspan
    (fun x hx y hy => hint _ ((hmem x).1 hx) _ ((hmem y).1 hy))
    (fun y hy => by
      rw [hmem, map_zsmul]
      refine hdual _ fun x hx => ?_
      obtain ⟨n, hn⟩ := hy (φ x) (AddSubgroup.mem_map_of_mem φ hx)
      exact ⟨n, by rw [traceHerm_apply, hφ] at hn; exact hn⟩)
  rw [harch]
  exact ⟨hD, hZ, (le_abs_self _).trans (Real.abs_le_sqrt hcov)⟩

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PCoordLatticeFullRank

section

@[expose] public section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField Module

noncomputable section

variable {E : Type*} [Field E] [NumberField E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι]

theorem CoordLatticeFullRank.proof (v : Basis ι E W) : CoordLatticeFullRank.Statement v := by
  intro La hL
  set f : W →ₗ[E] ι → E := (v.equivFun : W →ₗ[E] ι → E) with hf
  refine ⟨?_, ?_⟩
  · classical
    letI := hL.fg
    infer_instance
  set S : Set (ι → E) := ((La.map f.toAddMonoidHom : AddSubgroup (ι → E)) : Set (ι → E)) with hS
  set T : Submodule ℚ (ι → E) := Submodule.span ℚ S with hT

  have key : ∀ (a : E), ∀ s ∈ S, a • s ∈ T := by
    intro a s hs
    obtain ⟨d, hd, hint⟩ := exists_integral_multiples ℤ ℚ ({a} : Finset E)
    have hda : IsIntegral ℤ (d • a) := hint a (Finset.mem_singleton_self a)
    obtain ⟨x, hx, rfl⟩ := (AddSubgroup.mem_map).mp hs
    let b : 𝓞 E := ⟨d • a, hda⟩
    have hbx : ((b : E) • x) ∈ La := hL.smul_mem b x hx
    have hfb : f ((b : E) • x) ∈ S := (AddSubgroup.mem_map).mpr ⟨_, hbx, rfl⟩
    have hd' : ((d : ℚ)) ≠ 0 := by exact_mod_cast hd
    have heq : a • f.toAddMonoidHom x = ((d : ℚ)⁻¹) • f ((b : E) • x) := by
      rw [map_smul]
      show a • f x = ((d : ℚ)⁻¹) • ((d • a) • f x)
      rw [zsmul_eq_mul, mul_smul, Int.cast_smul_eq_zsmul E, ← Int.cast_smul_eq_zsmul ℚ,
        smul_smul, inv_mul_cancel₀ hd', one_smul]
    rw [heq]
    exact T.smul_mem _ (Submodule.subset_span hfb)

  have stable : ∀ (a : E), ∀ y ∈ T, a • y ∈ T := by
    intro a y hy
    induction hy using Submodule.span_induction with
    | mem s hs => exact key a s hs
    | zero => simp
    | add y z _ _ hy hz => rw [smul_add]; exact T.add_mem hy hz
    | smul q y _ hy =>
      rw [smul_comm]
      exact T.smul_mem q hy
  let T' : Submodule E (ι → E) :=
    { carrier := T
      add_mem' := fun hy hz => T.add_mem hy hz
      zero_mem' := T.zero_mem
      smul_mem' := fun a y hy => stable a y hy }
  have hspan : Submodule.span E S = ⊤ := by
    have hSim : S = f '' (La : Set W) := by
      rw [hS, AddSubgroup.coe_map]; rfl
    rw [hSim, Submodule.span_image, hL.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
    exact v.equivFun.surjective
  have hle : Submodule.span E S ≤ T' := Submodule.span_le.mpr fun s hs => Submodule.subset_span hs
  rw [hspan] at hle
  exact eq_top_iff.mpr fun y _ => hle (Submodule.mem_top)

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PTraceHermNondegenerate

section

@[expose] public section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module

variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι]


omit [NumberField E] in
theorem HermitianForm.eq_zero_of_toSesq_eq_zero (h : HermitianForm F E W) {x : W}
    (hx : ∀ w, h.toSesq x w = 0) : x = 0 := by
  apply h.nonsingular.1
  rw [map_zero]
  exact LinearMap.ext hx

theorem TraceHermNondegenerate.proof (h : HermitianForm F E W) (v : Basis ι E W) :
    TraceHermNondegenerate.Statement h v := by
  have hT := (traceForm_nondegenerate ℚ E).1
  constructor
  · intro y hy
    have key : ∀ w, h.toSesq (v.equivFun.symm y) w = 0 := by
      intro w
      apply hT
      intro a
      have := hy (v.equivFun (a • w))
      rw [traceHerm_apply, LinearEquiv.symm_apply_apply, LinearMap.map_smul, smul_eq_mul] at this
      rw [Algebra.traceForm_apply, mul_comm]
      exact this
    have h0 := HermitianForm.eq_zero_of_toSesq_eq_zero h key
    exact (map_eq_zero_iff _ v.equivFun.symm.injective).1 h0
  · intro z hz
    have key : ∀ w, h.toSesq w (v.equivFun.symm z) = 0 := by
      intro w
      apply hT
      intro a
      have := hz (v.equivFun (conj F E a • w))
      rw [traceHerm_apply, LinearEquiv.symm_apply_apply, LinearMap.map_smulₛₗ₂, smul_eq_mul] at this
      rw [Algebra.traceForm_apply, mul_comm]
      simpa [conj_conj] using this
    have key' : ∀ w, h.toSesq (v.equivFun.symm z) w = 0 := by
      intro w
      have e := (LinearMap.isSymm_def.1 h.isSymm) (v.equivFun.symm z) w
      rw [key w] at e
      exact (map_eq_zero_iff _ (conjHom F E).injective).1 e
    have h0 := HermitianForm.eq_zero_of_toSesq_eq_zero h key'
    exact (map_eq_zero_iff _ v.equivFun.symm.injective).1 h0

end GroundTheory.Heights₂.Heights.FiniteCovolume
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.OfUnfolding

section

@[expose] public section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory IsDedekindDomain
open scoped Pointwise ComplexOrder ENNReal NumberField.AdeleRing

noncomputable section

universe u

theorem ReducedBasisBound.full : ReducedBasisBound.Statement := ReducedBasisBound.proof

section Closed

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]

section OneSpace

variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (h : HermitianForm F E W) (v : Basis ι E W)


omit [NumberField F] [IsTotallyReal F] [DecidableEq ι] in
theorem ArchCovolumeBound.full : ArchCovolumeBound.Statement h v :=
  ArchCovolumeBound.proof h v (CoordEmbedBasis.proof E ι) (IntegralFormCovolume.proof _ _ _)
    (TraceHermNondegenerate.proof h v) (DualLatticeMultiple.proof h) (CoordLatticeFullRank.proof v)


omit [NumberField F] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem MajorantTransport.full : MajorantTransport.Statement h v := MajorantTransport.proof h v


omit [NumberField F] [NumberField E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem ComplementExtension.full : ComplementExtension.Statement h := ComplementExtension.proof h


omit [NumberField F] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem LineNormalForm.full : LineNormalForm.Statement h := LineNormalForm.proof h


omit [NumberField F] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem ComplementLattice.full [FiniteDimensional E W] : ComplementLattice.Statement h :=
  ComplementLattice.proof h


omit [NumberField F] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem LatticePointsBelowFinite.full : LatticePointsBelowFinite.Statement h v :=
  LatticePointsBelowFinite.proof h v

theorem ArchimedeanUnitaryEquiv.full : ArchimedeanUnitaryEquiv.Statement h v :=
  ArchimedeanUnitaryEquiv.proof h v

theorem AdelicLatticeDictionary.full : AdelicLatticeDictionary.Statement h v :=
  AdelicLatticeDictionary.proof h v

end OneSpace

theorem LatticeOrbitsFiniteBelow.full (N : ℕ) : LatticeOrbitsFiniteBelow.{u} F E N :=
  LatticeOrbitsFiniteBelow.of_steps ReducedBasisBound.full
    (fun _ _ _ _ h _ v => ArchCovolumeBound.full h v) (fun _ _ _ _ h _ v => MajorantTransport.full h v)
    (fun _ _ _ _ h => ComplementExtension.full h) (fun _ _ _ _ h => LineNormalForm.full h)
    (fun _ _ _ _ h => ComplementLattice.full h) N

section Dimension

variable {W : Type u} [AddCommGroup W] [Module E W] [FiniteDimensional E W]
variable (h : HermitianForm F E W)

theorem LatticeOrbitsFinite.full : LatticeOrbitsFinite.Statement h :=
  LatticeOrbitsFinite.step_of h (LatticeOrbitsFiniteBelow.full _) ReducedBasisBound.full
    (ArchCovolumeBound.full h _) (MajorantTransport.full h _) (ComplementExtension.full h)
    (LineNormalForm.full h) (ComplementLattice.full h)

theorem LinePairOrbitsFinite.full : LinePairOrbitsFinite.Statement h :=
  LinePairOrbitsFinite.full_of h (LatticeOrbitsFiniteBelow.full _) (ComplementExtension.full h)
    (LineNormalForm.full h) (ComplementLattice.full h)

theorem ScalingLaw.of_unfolding {ι : Type*} [Fintype ι] [DecidableEq ι] (v : Basis ι E W)
    (hU : UnfoldingIntegral.Statement h v) : ScalingLaw.Statement h v :=
  ScalingLaw.full_of h v (LinePairOrbitsFinite.full h) hU

end Dimension

end Closed

section Adelic

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AdelicCovolumeFinite.of_covolume (h : HermitianForm F E W) (v : Basis ι E W)
    (hC : ArithmeticCovolumeFinite.Statement h v) : AdelicCovolumeFinite.Statement h v :=
  haveI : FiniteDimensional E W := Module.Finite.of_basis v
  AdelicCovolumeFinite.full_of h v (LatticeOrbitsFinite.full h) hC (ArchimedeanUnitaryEquiv.full h v)
    (AdelicLatticeDictionary.full h v) (DoubleCosetCovolume.proof _ _ _)

theorem HaarParabolicCoordinates.of_open (h : HermitianForm F E W) (v : Basis ι E W)
    (hAU : ArchUnimodular.Statement h v) (hMS : MajorantStabCompact.Statement h v)
    (hLS : LineStabHaar.Statement h v) : HaarParabolicCoordinates.Statement h v :=
  HaarParabolicCoordinates.proof h v (ParabolicDecomposition.full h v) hAU hMS hLS

end Adelic

section Open

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]

variable
    (hAU : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W) (n : ℕ) (v : Basis (Fin n) E W), ArchUnimodular.Statement h v)
    (hMS : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W) (n : ℕ) (v : Basis (Fin n) E W), MajorantStabCompact.Statement h v)
    (hLS : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W) (n : ℕ) (v : Basis (Fin n) E W), LineStabHaar.Statement h v)
    (hSD : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W) (n : ℕ) (v : Basis (Fin n) E W) (x₀ w₀ : W)
      (h' : HermitianForm F E (hypComplement h x₀ w₀)) (m : ℕ)
      (v' : Basis (Fin m) E (hypComplement h x₀ w₀)),
      SemidirectCovering.Statement (vecFixGroup h v x₀) (archUnitary h' v') (unipRadical h v x₀))
    (hSL : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W) (n : ℕ) (v : Basis (Fin n) E W), StabilizerLevi.Statement h v)
    (hUM : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W) (n : ℕ) (v : Basis (Fin n) E W), UnipotentModulus.Statement h v)
    (hUC : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W) (n : ℕ) (v : Basis (Fin n) E W), UnipotentCocompact.Statement h v)
    (hCL : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W), CongruenceLift.Statement h)

include hAU hMS hLS hSD hSL hUM hUC hCL

theorem CovolumeFiniteBelow.of_open (N : ℕ) : CovolumeFiniteBelow.{u} F E N :=
  CovolumeFiniteBelow.of_steps ReducedBasisBound.full
    (fun _ _ _ _ h _ v => ArchCovolumeBound.full h v) (fun _ _ _ _ h _ v => MajorantTransport.full h v)
    (fun _ _ _ _ h => ComplementExtension.full h) (fun _ _ _ _ h => LineNormalForm.full h)
    (fun _ _ _ _ h => ComplementLattice.full h) (fun _ _ _ _ _ _ _ _ => UnfoldAlongSubgroup.proof _ _)
    (fun W _ _ _ h n v => HaarParabolicCoordinates.of_open h v (hAU W h n v) (hMS W h n v)
      (hLS W h n v))
    (fun W _ _ _ h n v hB => StabilizerCovolumeFinite.proof h v hB (hSD W h n v) (hSL W h n v)
      (hUM W h n v) (hUC W h n v) (hCL W h))
    (fun _ _ _ _ h _ v => LatticePointsBelowFinite.full h v) N

variable {W : Type u} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (h : HermitianForm F E W) (v : Basis ι E W)

variable (hSD' : ∀ (x₀ w₀ : W) (h' : HermitianForm F E (hypComplement h x₀ w₀)) (m : ℕ)
      (v' : Basis (Fin m) E (hypComplement h x₀ w₀)),
      SemidirectCovering.Statement (vecFixGroup h v x₀) (archUnitary h' v') (unipRadical h v x₀))
    (hSL' : StabilizerLevi.Statement h v) (hUM' : UnipotentModulus.Statement h v)
    (hUC' : UnipotentCocompact.Statement h v)

include hSD' hSL' hUM' hUC'

theorem StabilizerCovolumeFinite.of_open : StabilizerCovolumeFinite.Statement h v :=
  haveI : FiniteDimensional E W := Module.Finite.of_basis v
  StabilizerCovolumeFinite.proof h v
    (CovolumeFiniteBelow.of_open hAU hMS hLS hSD hSL hUM hUC hCL _) hSD' hSL' hUM' hUC' (hCL W h)

variable (hAU' : ArchUnimodular.Statement h v) (hMS' : MajorantStabCompact.Statement h v)
    (hLS' : LineStabHaar.Statement h v)

include hAU' hMS' hLS'

theorem UnfoldingIntegral.of_open : UnfoldingIntegral.Statement h v :=
  UnfoldingIntegral.full_of h v (fun _ => UnfoldAlongSubgroup.proof _ _)
    (HaarParabolicCoordinates.of_open h v hAU' hMS' hLS')
    (StabilizerCovolumeFinite.of_open hAU hMS hLS hSD hSL hUM hUC hCL h v hSD' hSL' hUM' hUC')

theorem ScalingLaw.of_open : ScalingLaw.Statement h v :=
  haveI : FiniteDimensional E W := Module.Finite.of_basis v
  ScalingLaw.of_unfolding h v
    (UnfoldingIntegral.of_open hAU hMS hLS hSD hSL hUM hUC hCL h v hSD' hSL' hUM' hUC' hAU' hMS' hLS')

theorem ArithmeticCovolumeFinite.of_open : ArithmeticCovolumeFinite.Statement h v :=
  haveI : FiniteDimensional E W := Module.Finite.of_basis v
  ArithmeticCovolumeFinite.step_of h v (LatticeOrbitsFiniteBelow.full _) ReducedBasisBound.full
    (ArchCovolumeBound.full h v) (MajorantTransport.full h v) (ComplementExtension.full h)
    (LineNormalForm.full h) (ComplementLattice.full h) (fun _ => UnfoldAlongSubgroup.proof _ _)
    (HaarParabolicCoordinates.of_open h v hAU' hMS' hLS')
    (StabilizerCovolumeFinite.of_open hAU hMS hLS hSD hSL hUM hUC hCL h v hSD' hSL' hUM' hUC')
    (LatticePointsBelowFinite.full h v)

theorem AdelicCovolumeFinite.of_open : AdelicCovolumeFinite.Statement h v :=
  AdelicCovolumeFinite.of_covolume h v
    (ArithmeticCovolumeFinite.of_open hAU hMS hLS hSD hSL hUM hUC hCL h v hSD' hSL' hUM' hUC' hAU' hMS'
      hLS')

end Open

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end
end
