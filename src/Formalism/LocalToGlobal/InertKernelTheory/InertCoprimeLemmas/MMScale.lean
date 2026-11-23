module

public import Formalism.LocalToGlobal.InertKernelTheory.OneCopyTh1S
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.ProductThetaMem
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharacterIdentityReformulated2
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharactersFactAltForm
public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.FinalFree
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.LocAbs
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.KappaSelfDualFourthPowerLattice
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.ReBase
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.BaseEx
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.IsTorsionPointStandardCM
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.StdOK
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.SubstSingleVar
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharacterIdentityReformulated2
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharactersFactTer
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.ConstantCoeffInVarEqZero
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OneLetterGaussSharpTranslateHolds
public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.RenameBlockSingleVariableSeries
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.CoeffSubstLgFOfDegreeOne
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: Formalism.LocalToGlobal.Divisibility.JetBounds.JetCounting.ScaledNorms.GcmHostPf

section

@[expose] public section

open scoped BigOperators ComplexConjugate

noncomputable section

namespace Formalism.L2.DIV.C.X

open Formalism.L2.DIV Formalism.L2.DIV.C
open Formalism.L2.Th1.H (Sesq IsHerm IsSemiChar altE opU alphaQ qOf fixedBy dualLat IsReps sumU inter relIdx imgLat pow4
  slice stdH stdLat matH blk4 F0 prodFn kernel4 tens4 Th IsSelfDual IsIsom cmL)
open Formalism.L2.Th1.F (scalePair)
open Formalism.L2.Th1.Top (kappa_integral local_kappa_shape_holds frameExistsH)

section Transport

variable {V : Type} [AddCommGroup V] [Module ℂ V] {c : ℂ}

theorem gcm_mem_map_smul (hc : c ≠ 0) (A : AddSubgroup V) (x : V) :
    x ∈ A.map (DistribSMul.toAddMonoidHom V c) ↔ c⁻¹ • x ∈ A := by
  rw [AddSubgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [DistribSMul.toAddMonoidHom_apply, inv_smul_smul₀ hc]
    exact hy
  · intro h
    exact ⟨c⁻¹ • x, h, by rw [DistribSMul.toAddMonoidHom_apply, smul_inv_smul₀ hc]⟩

theorem gcm_relIdx_map_smul (hc : c ≠ 0) (A B : AddSubgroup V) :
    relIdx (A.map (DistribSMul.toAddMonoidHom V c)) (B.map (DistribSMul.toAddMonoidHom V c)) = relIdx A B :=
  AddSubgroup.relIndex_map_map_of_injective A B fun _ _ hxy => smul_right_injective V hc hxy

variable {H H' : Sesq V}

theorem gcm_opU_scale (hH' : ∀ u v, H' u v = H (c⁻¹ • u) (c⁻¹ • v)) (x : V) (F : V → ℂ) (z : V) :
    opU H' x (fun w => F (c⁻¹ • w)) z = opU H (c⁻¹ • x) F (c⁻¹ • z) := by
  simp only [opU]
  rw [hH', hH', smul_add]

theorem gcm_alphaQ_scale (hH' : ∀ u v, H' u v = H (c⁻¹ • u) (c⁻¹ • v)) (r : ℝ) (x : V) :
    alphaQ r H' x = alphaQ r H (c⁻¹ • x) := by
  simp only [alphaQ, qOf]
  rw [hH']

theorem gcm_altE_scale (hH' : ∀ u v, H' u v = H (c⁻¹ • u) (c⁻¹ • v)) (x y : V) :
    altE H' x y = altE H (c⁻¹ • x) (c⁻¹ • y) := by
  simp only [altE]
  rw [hH']

theorem gcm_isHerm_scale (hH' : ∀ u v, H' u v = H (c⁻¹ • u) (c⁻¹ • v)) (hH : IsHerm H) : IsHerm H' := by
  intro x y
  rw [hH', hH', hH]

theorem gcm_semi_scale (hc : c ≠ 0) (hH' : ∀ u v, H' u v = H (c⁻¹ • u) (c⁻¹ • v)) {M : AddSubgroup V}
    {β : V → ℂ} (hβ : IsSemiChar H M β) :
    IsSemiChar H' (M.map (DistribSMul.toAddMonoidHom V c)) (fun x => β (c⁻¹ • x)) := by
  refine ⟨fun x hx => hβ.1 _ ((gcm_mem_map_smul hc M x).1 hx), fun x hx y hy => ?_⟩
  show β (c⁻¹ • (x + y)) = β (c⁻¹ • x) * β (c⁻¹ • y) * Complex.exp ((Real.pi : ℂ) * Complex.I * (altE H' x y : ℂ))
  rw [smul_add, gcm_altE_scale hH']
  exact hβ.2 _ ((gcm_mem_map_smul hc M x).1 hx) _ ((gcm_mem_map_smul hc M y).1 hy)

theorem gcm_fixed_scale (hc : c ≠ 0) (hH' : ∀ u v, H' u v = H (c⁻¹ • u) (c⁻¹ • v)) {S : AddSubgroup V}
    {β : V → ℂ} {F : V → ℂ} (hF : F ∈ fixedBy H β S) :
    (fun w => F (c⁻¹ • w)) ∈ fixedBy H' (fun x => β (c⁻¹ • x)) (S.map (DistribSMul.toAddMonoidHom V c)) := by
  intro x hx z
  show β (c⁻¹ • x) * opU H' x (fun w => F (c⁻¹ • w)) z = F (c⁻¹ • z)
  rw [gcm_opU_scale hH']
  exact hF _ ((gcm_mem_map_smul hc S x).1 hx) _

theorem gcm_reps_scale (hc : c ≠ 0) [DecidableEq V] {A B : AddSubgroup V} {R : Finset V} (hR : IsReps A B R) :
    IsReps (A.map (DistribSMul.toAddMonoidHom V c)) (B.map (DistribSMul.toAddMonoidHom V c))
      (R.image (fun x => c • x)) := by
  refine ⟨fun x hx => ?_, fun x hx y hy hxy => ?_, fun y hy => ?_⟩
  · obtain ⟨x', hx', rfl⟩ := Finset.mem_image.1 hx
    rw [gcm_mem_map_smul hc, inv_smul_smul₀ hc]
    exact hR.1 x' hx'
  · obtain ⟨x', hx', rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨y', hy', rfl⟩ := Finset.mem_image.1 hy
    rw [gcm_mem_map_smul hc, ← smul_sub, inv_smul_smul₀ hc] at hxy
    rw [hR.2.1 x' hx' y' hy' hxy]
  · obtain ⟨x, hx, hyx⟩ := hR.2.2 (c⁻¹ • y) ((gcm_mem_map_smul hc B y).1 hy)
    refine ⟨c • x, Finset.mem_image_of_mem _ hx, ?_⟩
    rw [gcm_mem_map_smul hc, smul_sub, inv_smul_smul₀ hc]
    exact hyx

theorem gcm_dualLat_scale (hc : c ≠ 0) (hH' : ∀ u v, H' u v = H (c⁻¹ • u) (c⁻¹ • v)) (Λ : AddSubgroup V) :
    dualLat H' (Λ.map (DistribSMul.toAddMonoidHom V c)) = (dualLat H Λ).map (DistribSMul.toAddMonoidHom V c) := by
  ext x
  rw [gcm_mem_map_smul hc]
  show (∀ y ∈ Λ.map (DistribSMul.toAddMonoidHom V c), ∃ m : ℤ, altE H' x y = (m : ℝ)) ↔
    (∀ y ∈ Λ, ∃ m : ℤ, altE H (c⁻¹ • x) y = (m : ℝ))
  constructor
  · intro hx y hy
    have := hx (c • y) ((gcm_mem_map_smul hc Λ _).2 (by rw [inv_smul_smul₀ hc]; exact hy))
    rwa [gcm_altE_scale hH', inv_smul_smul₀ hc] at this
  · intro hx y hy
    rw [gcm_altE_scale hH']
    exact hx _ ((gcm_mem_map_smul hc Λ y).1 hy)

theorem gcm_inter_scale (hc : c ≠ 0) (hH' : ∀ u v, H' u v = H (c⁻¹ • u) (c⁻¹ • v)) (hH : IsHerm H)
    {S M : AddSubgroup V} {β : V → ℂ} {F : V → ℂ} (hβ : IsSemiChar H M β) (hF : F ∈ fixedBy H β S)
    (hidx : relIdx S M ≠ 0) (w : V) :
    inter H' (fun x => β (c⁻¹ • x)) (S.map (DistribSMul.toAddMonoidHom V c)) (M.map (DistribSMul.toAddMonoidHom V c))
      (fun v => F (c⁻¹ • v)) w = inter H β S M F (c⁻¹ • w) := by
  classical
  obtain ⟨⟨R, hR⟩, -⟩ := Formalism.L2.Th1.H.repsExist V S M hidx
  rw [Formalism.L2.Th1.H.interReps V H' (gcm_isHerm_scale hH' hH) _ _ _ (gcm_semi_scale hc hH' hβ) _
      (gcm_fixed_scale hc hH' hF) _ (gcm_reps_scale hc hR) w,
    Formalism.L2.Th1.H.interReps V H hH S M β hβ F hF R hR (c⁻¹ • w), gcm_relIdx_map_smul hc]
  congr 1
  simp only [sumU]
  rw [Finset.sum_image fun _ _ _ _ hxy => smul_right_injective V hc hxy]
  refine Finset.sum_congr rfl fun x _ => ?_
  show β (c⁻¹ • c • x) * opU H' (c • x) (fun v => F (c⁻¹ • v)) w = β x * opU H x F (c⁻¹ • w)
  rw [gcm_opU_scale hH', inv_smul_smul₀ hc]

end Transport

section Forms

theorem gcm_inv_mul_conj (c : ℂ) : (c⁻¹ * conj c⁻¹ : ℂ) = ((Complex.normSq c : ℝ) : ℂ)⁻¹ := by
  rw [map_inv₀, ← mul_inv, Complex.mul_conj]

theorem gcm_matH_scale {m : Type} [Fintype m] (c : ℂ) (M : Matrix m m ℂ) (u v : m → ℂ) :
    matH (((Complex.normSq c : ℝ) : ℂ)⁻¹ • M) u v = matH M (c⁻¹ • u) (c⁻¹ • v) := by
  rw [(Formalism.L2.Th1.H.matHBasic m _).1, (Formalism.L2.Th1.H.matHBasic m M).1, ← gcm_inv_mul_conj c]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.smul_apply, smul_eq_mul, Pi.smul_apply, map_mul]
  ring

theorem blockFour_smul {n : Type} (k : ℂ) (h : Matrix n n ℂ) : blk4 (k • h) = k • blk4 h := by
  funext w w'
  simp only [blk4, Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> simp

theorem gcm_stdH_scale (L : PeriodPair) (c : ℂ) (hc : c ≠ 0) (m : Type) [Fintype m] [DecidableEq m]
    (u v : m → ℂ) : stdH (scalePair L c hc) m u v = stdH L m (c⁻¹ • u) (c⁻¹ • v) := by
  rw [(Formalism.L2.Th1.H.stdHBasic _ m).1, (Formalism.L2.Th1.H.stdHBasic L m).1]
  have hA := (Formalism.L2.Th1.F.homogeneity L c hc).2.2.2.2.2.1
  have key : (c⁻¹ * conj c⁻¹ : ℂ) = ((‖c‖ : ℂ) ^ 2)⁻¹ := by
    rw [map_inv₀, ← mul_inv, Complex.mul_conj']
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Formalism.L2.Th1.F.herm, hA, Pi.smul_apply, smul_eq_mul, map_mul, div_eq_mul_inv, Complex.ofReal_mul,
    Complex.ofReal_pow, mul_inv]
  rw [← key]
  ring

theorem gcm_stdLat_scale (L : PeriodPair) (c : ℂ) (hc : c ≠ 0) (m : Type) :
    stdLat (scalePair L c hc) m = (stdLat L m).map (DistribSMul.toAddMonoidHom (m → ℂ) c) := by
  ext x
  rw [gcm_mem_map_smul hc]
  simp only [stdLat, AddSubgroup.mem_pi, Submodule.mem_toAddSubgroup, (Formalism.L2.Th1.F.homogeneity L c hc).1,
    Pi.smul_apply, smul_eq_mul]

theorem gcm_imgLat_scale {W : Type} [AddCommGroup W] [Module ℂ W] {n : Type} (c : ℂ) (hc : c ≠ 0)
    (g : (Fin 4 × n → ℂ) →ₗ[ℂ] W) (Λ : AddSubgroup (n → ℂ)) :
    imgLat g (pow4 (Λ.map (DistribSMul.toAddMonoidHom (n → ℂ) c))) =
      (imgLat g (pow4 Λ)).map (DistribSMul.toAddMonoidHom W c) := by
  ext x
  rw [gcm_mem_map_smul hc]
  simp only [imgLat, AddSubgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : ∀ a, slice a y ∈ Λ.map (DistribSMul.toAddMonoidHom (n → ℂ) c) := hy
    refine ⟨c⁻¹ • y, fun a => (gcm_mem_map_smul hc Λ _).1 (hy' a), ?_⟩
    simp
  · rintro ⟨y, hy, hyx⟩
    have hy' : ∀ a, slice a y ∈ Λ := hy
    refine ⟨c • y, fun a => (gcm_mem_map_smul hc Λ _).2 ?_, ?_⟩
    · have : c⁻¹ • slice a (c • y) = slice a y := by
        funext i
        simp only [slice, Pi.smul_apply, smul_eq_mul, inv_mul_cancel_left₀ hc]
      rw [this]
      exact hy' a
    · simp only [LinearMap.toAddMonoidHom_coe] at hyx ⊢
      rw [map_smul, hyx, smul_inv_smul₀ hc]

theorem periodF0_scale (L : PeriodPair) (c : ℂ) (hc : c ≠ 0) (ω₀ : ℂ) (m : Type) [Fintype m]
    (w : m → ℂ) : F0 (scalePair L c hc) (c * ω₀) m w = F0 L ω₀ m (c⁻¹ • w) := by
  simp only [F0, prodFn]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h9 := (Formalism.L2.Th1.F.homogeneity L c hc).2.2.2.2.2.2.2.2.1 (ω₀ / 2) (c⁻¹ * w i)
  rw [mul_inv_cancel_left₀ hc] at h9
  rw [show c * ω₀ / 2 = c * (ω₀ / 2) by ring, h9]
  rfl

theorem gcm_scalePair_scalePair (L : PeriodPair) (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) :
    scalePair (scalePair L a ha) b hb = scalePair L (a * b) (mul_ne_zero ha hb) := by
  show PeriodPair.mk _ _ _ = PeriodPair.mk _ _ _
  congr 1
  · show b * (a * L.ω₁) = _
    ring
  · show b * (a * L.ω₂) = _
    ring

theorem gcm_kernel4_scale (L : PeriodPair) (c : ℂ) (hc : c ≠ 0) (ω₀ : ℂ) (r : ℝ) {n : Type} [Fintype n]
    [DecidableEq n] (Λ : AddSubgroup (n → ℂ)) (g : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ))
    (hβ : IsSemiChar (stdH L (Fin 4 × n)) (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ))
      (alphaQ r (stdH L (Fin 4 × n))))
    (hF : F0 L ω₀ (Fin 4 × n) ∈ fixedBy (stdH L (Fin 4 × n)) (alphaQ r (stdH L (Fin 4 × n))) (stdLat L (Fin 4 × n)))
    (hidx : relIdx (stdLat L (Fin 4 × n)) (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) ≠ 0)
    (z : Fin 4 × n → ℂ) :
    kernel4 (scalePair L c hc) (c * ω₀) (Λ.map (DistribSMul.toAddMonoidHom (n → ℂ) c))
      (alphaQ r (stdH (scalePair L c hc) (Fin 4 × n))) g z =
    kernel4 L ω₀ Λ (alphaQ r (stdH L (Fin 4 × n))) g (c⁻¹ • z) := by
  have hH' := gcm_stdH_scale L c hc (Fin 4 × n)
  have hα : alphaQ r (stdH (scalePair L c hc) (Fin 4 × n)) = fun x => alphaQ r (stdH L (Fin 4 × n)) (c⁻¹ • x) :=
    funext (gcm_alphaQ_scale hH' r)
  have hF0 : F0 (scalePair L c hc) (c * ω₀) (Fin 4 × n) = fun w => F0 L ω₀ (Fin 4 × n) (c⁻¹ • w) :=
    funext (periodF0_scale L c hc ω₀ (Fin 4 × n))
  simp only [kernel4]
  rw [gcm_stdLat_scale, gcm_imgLat_scale c hc, hα, hF0, map_smul]
  exact gcm_inter_scale hc hH' (Formalism.L2.Th1.H.stdHBasic L (Fin 4 × n)).2.1 hβ hF hidx _

end Forms

end Formalism.L2.DIV.C.X
end
end
end

-- Source module: Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.MMScale

section

@[expose] public section

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.KerInert

namespace MMScale

open NumberField Formalism.BasicNotions Formalism.L2.Ker Classical
open Formalism.InvariantFactorPaths.G7 (at1)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.H (CmOK cmL matH stdH stdLat blk4 pow4 imgLat relIdx IsIsom IsSelfDual StdData Th alphaQ kernel4 tens4)
open Formalism.L2.DIV.C.X (gcm_mem_map_smul gcm_relIdx_map_smul gcm_opU_scale gcm_alphaQ_scale gcm_dualLat_scale gcm_matH_scale
  blockFour_smul gcm_stdH_scale gcm_stdLat_scale gcm_imgLat_scale gcm_scalePair_scalePair gcm_kernel4_scale)

theorem thetaU_smul {K : Type} [Field K] (ι : ℂ →+* K) {lg : PowerSeries K}
    (hlg : PowerSeries.constantCoeff lg = 0) {n : Type} [Fintype n] [DecidableEq n] (B' : Matrix n n K)
    (s : ℂ) (G : (n → ℂ) → ℂ) (hG : AnalyticAt ℂ G 0) :
    Formalism.L2.Th1.H.thetaU ι lg B' (fun z => G (s • z)) =
      MvPowerSeries.subst (fun i => ∑ j, MvPowerSeries.C (ι s * B' i j) * (at1 j lg : MvPowerSeries n K))
        (MvPowerSeries.map ι (Formalism.L2.Th1.H.taylorMv G)) := by
  have ha : MvPowerSeries.HasSubst (fun i => ∑ j, MvPowerSeries.C (B' i j) * (at1 j lg : MvPowerSeries n K)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun i =>
      Formalism.L2.Th1.H.FormalGroupLawNegation.cc_lin (B' i) fun j => Formalism.L2.Th1.E.CompatibleChartOperations.constantCoeff_inVar_eq_zero j hlg
  have hb : MvPowerSeries.HasSubst (fun i => ∑ j, MvPowerSeries.C (((Matrix.diagonal fun _ : n => s).map ι) i j) *
      (MvPowerSeries.X j : MvPowerSeries n K)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun i =>
      Formalism.L2.Th1.H.FormalGroupLawNegation.cc_lin _ fun j => MvPowerSeries.constantCoeff_X _
  have hmv : (fun z : n → ℂ => G (s • z)) = fun w => G ((Matrix.diagonal fun _ : n => s).mulVec w) := by
    funext w
    congr 1
    funext i
    rw [Matrix.mulVec_diagonal]
    rfl
  unfold Formalism.L2.Th1.H.thetaU
  rw [hmv, Formalism.L2.Th1.H.taylorMvComp n n _ G hG, Formalism.L2.Th1.H.FormalGroupLawNegation.map_linSubst]
  unfold Formalism.L2.Th1.H.linSubst
  rw [MvPowerSeries.subst_comp_subst_apply hb ha]
  congr 1
  funext i

  rw [← MvPowerSeries.coe_substAlgHom ha, map_sum, Finset.sum_eq_single i]
  · rw [map_mul, MvPowerSeries.coe_substAlgHom ha, MvPowerSeries.subst_C, MvPowerSeries.subst_X ha, Matrix.map_apply,
      Matrix.diagonal_apply_eq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← mul_assoc, ← map_mul]
  · intro j _ hj
    rw [Matrix.map_apply, Matrix.diagonal_apply_ne _ (Ne.symm hj), map_zero, map_zero, zero_mul, map_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

theorem stdData_cm {a₀ : ℕ} {b₀ c₀ : ℤ} {d : ℕ} (ha : 0 < a₀) (hd : 0 < d) {lam : ℂ} (hlam : lam ≠ 0)
    (hcm : CmOK a₀ b₀ c₀ d) {L : PeriodPair} (hL : L.lattice = (cmL a₀ b₀ d ha hd lam hlam).lattice)
    {ω₀ : ℂ} (hω : (ω₀ - lam * a₀) / 2 ∈ (cmL a₀ b₀ d ha hd lam hlam).lattice) (hn : ω₀ / 2 ∉ L.lattice)
    {n : Type} [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ))
    (g : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ))
    (hiso : IsIsom (matH (blk4 h)) (stdH L (Fin 4 × n)) (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)))
    (hsd : IsSelfDual (matH h) Λ) (hst : ∀ x ∈ Λ, Formalism.L2.Th1.F.cmTheta b₀ d • x ∈ Λ)
    (i1 : relIdx (stdLat L (Fin 4 × n)) (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) ≠ 0)
    (i2 : relIdx (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) (stdLat L (Fin 4 × n)) ≠ 0) :
    StdData L ω₀ h Λ (alphaQ (Real.sqrt d / 2) (matH h)) (alphaQ (Real.sqrt d / 2) (stdH L (Fin 4 × n))) g := by
  rw [KS.stdH_congr hL] at hiso ⊢
  rw [ReBase.stdLat_congr hL] at i1 i2
  exact ReBase.stdData_congr hL hω hn
    (Formalism.L2.Th1.H.stdDataCm a₀ b₀ c₀ d ha hd lam hlam hcm.1 hcm.2.1 hcm.2.2.1 n h Λ g hiso hsd hst i1 i2)

end MMScale

open NumberField Formalism.BasicNotions Formalism.L2.Ker Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.H (CmOK cmL matH stdH stdLat blk4 pow4 imgLat relIdx IsIsom IsSelfDual StdData Th alphaQ kernel4 tens4)
open Formalism.L2.DIV.C.X (gcm_mem_map_smul gcm_relIdx_map_smul gcm_opU_scale gcm_alphaQ_scale gcm_dualLat_scale gcm_matH_scale
  blockFour_smul gcm_stdH_scale gcm_stdLat_scale gcm_imgLat_scale gcm_scalePair_scalePair gcm_kernel4_scale)

theorem scale_integrality : ScaleInt := by
  intro D cc δ B hcc hδ p _ h5 hj ι c hc g2 g3 ε s2 hLT hg2 hg3 hdisc hε hth g₁ e hI σ hσ hN γ B' hFr t N hN0 hpN ht
  obtain ⟨hiso, hndvd, i2, he, hten⟩ := hI
  obtain ⟨a₀, gg, b₀, c₀, ha, hd, hl, B'', hcm, -, hIs, hlat, -, -, -, hω, -, -⟩ :=
    ReBase.theta_change_of_base D cc δ B hcc
  have i1 : relIdx (stdLat B.L (Fin 4 × D.what₂.Tau))
      (imgLat (g₁ : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (pow4 B.lamM)) ≠ 0 := by
    intro h0
    exact hndvd (h0 ▸ dvd_zero p)

  have hLB : B.L.lattice = (cmL a₀ b₀ D.host.d ha hd ((gg : ℂ) * δ) hl).lattice := by
    rw [← hlat, hIs.1]
  have hωB : (B.ω₀ - (gg : ℂ) * δ * a₀) / 2 ∈ (cmL a₀ b₀ D.host.d ha hd ((gg : ℂ) * δ) hl).lattice := by
    rw [← hIs.2, ← hIs.1, hlat]
    exact hω
  have hsd := Kap.kap_selfDual_lamM B hcc hδ
  have hst := Kap.kap_stable_lamM B b₀ (Kap.kap_odd hcm)

  have S1 : StdData B.L B.ω₀ (hOne B.L D.what₂.Tau) B.lamM
      (alphaQ (Real.sqrt D.host.d / 2) (matH (hOne B.L D.what₂.Tau)))
      (alphaQ (Real.sqrt D.host.d / 2) (stdH B.L (Fin 4 × D.what₂.Tau))) g₁ :=
    MMScale.stdData_cm ha hd hl hcm hLB hωB (Base.half_not_mem B) _ _ g₁ hiso hsd hst i1 i2

  have hH' := gcm_matH_scale c (hOne B.L D.what₂.Tau)
  have hcmL : cmL a₀ b₀ D.host.d ha hd ((gg : ℂ) * δ * c) (mul_ne_zero hl hc) =
      Formalism.L2.Th1.F.scalePair (cmL a₀ b₀ D.host.d ha hd ((gg : ℂ) * δ) hl) c hc :=
    (gcm_scalePair_scalePair _ ((gg : ℂ) * δ) c hl hc).symm
  have hL2 : (Formalism.L2.Th1.F.scalePair B.L c hc).lattice =
      (cmL a₀ b₀ D.host.d ha hd ((gg : ℂ) * δ * c) (mul_ne_zero hl hc)).lattice := by
    rw [hcmL]
    ext z
    rw [(Formalism.L2.Th1.F.homogeneity _ c hc).1, (Formalism.L2.Th1.F.homogeneity _ c hc).1, hLB]
  have hω2 : (c * B.ω₀ - (gg : ℂ) * δ * c * a₀) / 2 ∈
      (cmL a₀ b₀ D.host.d ha hd ((gg : ℂ) * δ * c) (mul_ne_zero hl hc)).lattice := by
    rw [hcmL, (Formalism.L2.Th1.F.homogeneity _ c hc).1]
    have e1 : c⁻¹ * ((c * B.ω₀ - (gg : ℂ) * δ * c * a₀) / 2) = (B.ω₀ - (gg : ℂ) * δ * a₀) / 2 := by
      field_simp
    rw [e1]
    exact hωB
  have hn2 : c * B.ω₀ / 2 ∉ (Formalism.L2.Th1.F.scalePair B.L c hc).lattice := by
    rw [(Formalism.L2.Th1.F.homogeneity _ c hc).1]
    have e1 : c⁻¹ * (c * B.ω₀ / 2) = B.ω₀ / 2 := by
      field_simp
    rw [e1]
    exact Base.half_not_mem B
  have hiso2 : IsIsom (matH (blk4 (((Complex.normSq c : ℝ) : ℂ)⁻¹ • hOne B.L D.what₂.Tau)))
      (stdH (Formalism.L2.Th1.F.scalePair B.L c hc) (Fin 4 × D.what₂.Tau))
      (g₁ : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) := by
    intro x y
    rw [gcm_stdH_scale, blockFour_smul, gcm_matH_scale]
    have := hiso (c⁻¹ • x) (c⁻¹ • y)
    rw [map_smul (g₁ : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) c⁻¹ x,
      map_smul (g₁ : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) c⁻¹ y] at this
    exact this
  have hsd2 : IsSelfDual (matH (((Complex.normSq c : ℝ) : ℂ)⁻¹ • hOne B.L D.what₂.Tau))
      (B.lamM.map (DistribSMul.toAddMonoidHom (D.what₂.Tau → ℂ) c)) := by
    show Formalism.L2.Th1.H.dualLat _ _ = _
    rw [gcm_dualLat_scale hc hH', hsd]
  have hst2 : ∀ x ∈ B.lamM.map (DistribSMul.toAddMonoidHom (D.what₂.Tau → ℂ) c),
      Formalism.L2.Th1.F.cmTheta b₀ D.host.d • x ∈ B.lamM.map (DistribSMul.toAddMonoidHom (D.what₂.Tau → ℂ) c) := by
    intro x hx
    rw [gcm_mem_map_smul hc] at hx ⊢
    rw [smul_comm]
    exact hst _ hx
  have j1 : relIdx (stdLat (Formalism.L2.Th1.F.scalePair B.L c hc) (Fin 4 × D.what₂.Tau))
      (imgLat (g₁ : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ))
        (pow4 (B.lamM.map (DistribSMul.toAddMonoidHom (D.what₂.Tau → ℂ) c)))) =
      relIdx (stdLat B.L (Fin 4 × D.what₂.Tau))
        (imgLat (g₁ : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (pow4 B.lamM)) := by
    rw [gcm_stdLat_scale, gcm_imgLat_scale _ hc, gcm_relIdx_map_smul hc]
  have j2 : relIdx (imgLat (g₁ : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ))
        (pow4 (B.lamM.map (DistribSMul.toAddMonoidHom (D.what₂.Tau → ℂ) c))))
      (stdLat (Formalism.L2.Th1.F.scalePair B.L c hc) (Fin 4 × D.what₂.Tau)) =
      relIdx (imgLat (g₁ : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (pow4 B.lamM))
        (stdLat B.L (Fin 4 × D.what₂.Tau)) := by
    rw [gcm_stdLat_scale, gcm_imgLat_scale _ hc, gcm_relIdx_map_smul hc]
  have S2 := MMScale.stdData_cm ha hd (mul_ne_zero hl hc) hcm hL2 hω2 hn2 _ _ g₁ hiso2 hsd2 hst2
    (j1 ▸ i1) (j2 ▸ i2)

  have hspec := B.thMM_spec (B.stdOK hcc hδ)
  have hmem : B.thMM ∈ Th (matH (hOne B.L D.what₂.Tau)) (alphaQ (Real.sqrt D.host.d / 2) (matH (hOne B.L D.what₂.Tau)))
      B.lamM := hspec.1
  have hmem2 : (fun x => B.thMM (c⁻¹ • x)) ∈ Th (matH (((Complex.normSq c : ℝ) : ℂ)⁻¹ • hOne B.L D.what₂.Tau))
      (alphaQ (Real.sqrt D.host.d / 2) (matH (((Complex.normSq c : ℝ) : ℂ)⁻¹ • hOne B.L D.what₂.Tau)))
      (B.lamM.map (DistribSMul.toAddMonoidHom (D.what₂.Tau → ℂ) c)) := by
    refine ⟨fun z _ => ?_, fun x hx z => ?_⟩
    · have hlin : AnalyticAt ℂ (fun w : D.what₂.Tau → ℂ => c⁻¹ • w) z :=
        (analyticAt_id (𝕜 := ℂ)).const_smul (c := c⁻¹)
      exact AnalyticAt.comp (f := fun w : D.what₂.Tau → ℂ => c⁻¹ • w) (hmem.1 (c⁻¹ • z) (Set.mem_univ _)) hlin
    · show alphaQ _ (matH _) x * Formalism.L2.Th1.H.opU (matH _) x (fun w => B.thMM (c⁻¹ • w)) z = B.thMM (c⁻¹ • z)
      rw [gcm_alphaQ_scale hH', gcm_opU_scale hH']
      exact hmem.2 _ ((gcm_mem_map_smul hc B.lamM x).1 hx) _
  have hF1 := (Formalism.L2.Th1.H.product_theta_mem' _ B.ω₀ (Fin 4 × D.what₂.Tau) S1.per S1.half _ S1.betaStd).1.2
  have hten2 : tens4 (fun x => B.thMM (c⁻¹ • x)) = e • kernel4 (Formalism.L2.Th1.F.scalePair B.L c hc) (c * B.ω₀)
      (B.lamM.map (DistribSMul.toAddMonoidHom (D.what₂.Tau → ℂ) c))
      (alphaQ (Real.sqrt D.host.d / 2) (stdH (Formalism.L2.Th1.F.scalePair B.L c hc) (Fin 4 × D.what₂.Tau))) g₁ := by
    funext z
    have ht0 : tens4 (fun x => B.thMM (c⁻¹ • x)) z = tens4 B.thMM (c⁻¹ • z) := rfl
    rw [ht0, hten, Pi.smul_apply, Pi.smul_apply, gcm_kernel4_scale _ c hc _ _ B.lamM g₁ S1.betaSemi hF1 i1]
    rfl
  have ht2 : (N : ℂ) • (c • t) ∈ B.lamM.map (DistribSMul.toAddMonoidHom (D.what₂.Tau → ℂ) c) := by
    rw [gcm_mem_map_smul hc, smul_comm, inv_smul_smul₀ hc]
    exact ht

  have hK := Formalism.L2.Th1.Top.local_kappa_shape_holds p h5 _ ι g2 g3 ε s2 hLT hg2 hg3 hdisc hε hth (c * B.ω₀) S2.per S2.half
    D.what₂.Tau _ _ _ _ g₁ S2 (by rw [j1]; exact hndvd) e he _ hmem2 hten2 (c • t) N hN0 hpN ht2 σ γ B' hFr
  obtain ⟨σ0, F, -, -, -, -, -, hF, -⟩ := Formalism.L2.Th1.Top.InhA.joint p h5 1 0 0
  have hInt := Formalism.L2.Th1.Top.kappa_integral p h5 g2 g3 ε s2 hg2 hg3 hε hth σ hσ F hF hN D.what₂.Tau _ γ hFr.1 hK

  have hGan : AnalyticAt ℂ (Formalism.L2.Th1.H.opU (matH (hOne B.L D.what₂.Tau)) t B.thMM) 0 :=
    Formalism.L2.Th1.H.opUAnalytic (D.what₂.Tau → ℂ) (matH (hOne B.L D.what₂.Tau)) t B.thMM hmem.1 0 (Set.mem_univ _)
  have hfun : Formalism.L2.Th1.H.opU (matH (((Complex.normSq c : ℝ) : ℂ)⁻¹ • hOne B.L D.what₂.Tau)) (c • t)
      (fun x => B.thMM (c⁻¹ • x)) = fun z => Formalism.L2.Th1.H.opU (matH (hOne B.L D.what₂.Tau)) t B.thMM (c⁻¹ • z) := by
    funext z
    rw [gcm_opU_scale hH', inv_smul_smul₀ hc]
  have hread : Formalism.L2.Th1.Top.thetaH p ι B' (((Complex.normSq c : ℝ) : ℂ)⁻¹ • hOne B.L D.what₂.Tau) (c • t)
      (fun x => B.thMM (c⁻¹ • x)) =
      ReadTh1 p (fun τ j => (ι c)⁻¹ * B' τ j)
        (MvPowerSeries.map (ι : ℂ →+* ℂ_[p])
          (Formalism.L2.Th1.H.taylorMv (Formalism.L2.Th1.H.opU (matH (hOne B.L D.what₂.Tau)) t B.thMM))) := by
    unfold Formalism.L2.Th1.Top.thetaH ReadTh1
    rw [hfun, MMScale.thetaU_smul (ι : ℂ →+* ℂ_[p]) (Formalism.InvariantFactorPaths.G7.FormalGroupLaws.constantCoeff_lgF p (by omega)) B' c⁻¹ _ hGan]
    simp only [RingEquiv.coe_toRingHom, map_inv₀]
  rw [← hread]
  exact hInt

end Formalism.L2.KerInert
end
end
end
