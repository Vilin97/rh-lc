module

public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.IntegralSquareRoots.FinrankRow
public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.Reduction
public import Formalism.LocalRingCardinality.SpanPowerMembership.RelDet
public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.CharacterFactorUnitaryAction
public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.NormOneUnitIdeal
public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.PullIopOf
public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.ReductionOf
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
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.UnitaryConstant
import Formalism.LocalRingCardinality.SpanPowerMembership.RelDet
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.IntegralSquareRoots.MemImgLatIff
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.DiagIntegrable
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharacterIdentityReformulated2
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.SelfDualCovolume
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.NormOneUnitIdeal
import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.PullIopOf
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic

-- Source module: Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.IntegralSquareRoots.PullMulRight

section

@[expose] public section

noncomputable section
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.PairingIndexBounds.Eq.J

open Formalism.MainNotions Formalism.L2.Th1.H Formalism.L2.PairingIndexBounds.Eq

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

def J1at (B : Ker.Base D cc δ) (N N' : ℕ)
    (γ : letI := D.host.cmStar; Matrix.unitaryGroup (Fin N) D.host.E) : Prop :=
  letI := D.host.cmStar
  TaylorLogMetric.pull D B.tor (γ : Matrix (Fin N) (Fin N) D.host.E) (1 : Matrix (Fin N') (Fin N') D.host.E) (B.thZero N N') =
    (∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ (star (γ : Matrix (Fin N) (Fin N) D.host.E).det)) ^ (N' / 2) •
      B.thHalf N N' (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) (StandardLatticesGL3.stdL D N))

def J2at (B : Ker.Base D cc δ) (N N' : ℕ)
    (γ' : letI := D.host.cmStar; Matrix.unitaryGroup (Fin N') D.host.E) : Prop :=
  letI := D.host.cmStar
  TaylorLogMetric.pull D B.tor (1 : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E) (B.thZero N N') =
    (∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ (γ' : Matrix (Fin N') (Fin N') D.host.E).det) ^ (N / 2) •
      TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N'))
        (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) (StandardLatticesGL3.stdL D N')))
        (B.thZero N N')

theorem pull_mul_left {N N' : ℕ} (γ₁ γ₂ : Matrix (Fin N) (Fin N) D.host.E) (G : TaylorLogMetric.VC D N N' → ℂ) :
    TaylorLogMetric.pull D (TaylorLogMetric.tor0 D cc δ) (γ₁ * γ₂) (1 : Matrix (Fin N') (Fin N') D.host.E) G =
      TaylorLogMetric.pull D (TaylorLogMetric.tor0 D cc δ) γ₁ 1 (TaylorLogMetric.pull D (TaylorLogMetric.tor0 D cc δ) γ₂ 1 G) := by
  funext z
  simp only [TaylorLogMetric.pull, TaylorLogMetric.tor0]
  congr 1
  funext τ
  simp [Matrix.map_one, Matrix.map_mul]
  exact (Matrix.mul_assoc _ _ _).symm

theorem pull_mul_right {N N' : ℕ} (γ₁ γ₂ : Matrix (Fin N') (Fin N') D.host.E) (G : TaylorLogMetric.VC D N N' → ℂ) :
    TaylorLogMetric.pull D (TaylorLogMetric.tor0 D cc δ) (1 : Matrix (Fin N) (Fin N) D.host.E) (γ₁ * γ₂) G =
      TaylorLogMetric.pull D (TaylorLogMetric.tor0 D cc δ) 1 γ₁ (TaylorLogMetric.pull D (TaylorLogMetric.tor0 D cc δ) 1 γ₂ G) := by
  funext z
  simp only [TaylorLogMetric.pull, TaylorLogMetric.tor0]
  congr 1
  funext τ
  simp [Matrix.map_one, Matrix.map_mul, Matrix.mul_assoc, Matrix.conjTranspose_mul]
  rfl

variable {B : Ker.Base D cc δ}

theorem J1at_mul (hL : B.LatAll) (hTL : Tr0L D B.tor) {N N' : ℕ} (hN : Even N) (hN' : Even N')
    (h0 : B.ThZeroMem N N') :
    letI := D.host.cmStar
    ∀ γ₁ γ₂ : Matrix.unitaryGroup (Fin N) D.host.E, J1at B N N' γ₁ → J1at B N N' γ₂ → J1at B N N' (γ₁ * γ₂) := by
  letI := D.host.cmStar
  intro γ₁ γ₂ j1 j2
  have e1 : ((1 : Matrix.unitaryGroup (Fin N') D.host.E) : Matrix (Fin N') (Fin N') D.host.E) = 1 := rfl
  have em : ((γ₁ * γ₂ : Matrix.unitaryGroup (Fin N) D.host.E) : Matrix (Fin N) (Fin N) D.host.E) =
      (γ₁ : Matrix (Fin N) (Fin N) D.host.E) * (γ₂ : Matrix (Fin N) (Fin N) D.host.E) := rfl
  have s1 := smulSD D N (StandardLatticesGL3.stdL D N) γ₁ (sd0 N)
  have s2 := smulSD D N (StandardLatticesGL3.stdL D N) γ₂ (sd0 N)
  have s12 := smulSD D N _ γ₁ s2
  have p := (pullIop_of hL N N' (StandardLatticesGL3.stdL D N) (SDLat.smulLat (γ₂ : Matrix (Fin N) (Fin N) D.host.E) (StandardLatticesGL3.stdL D N))
    (StandardLatticesGL3.stdL D N') (StandardLatticesGL3.stdL D N') γ₁ 1 hN hN' (sd0 N) s2 (sd0 N') (sd0 N') (B.thZero N N')
    (mem_ThSp_of' _ _ _ _ h0)).2
  rw [e1, Formalism.BasicNotions.Examples₂.smulLat_one] at p
  have t := hTL N N' _ _ hN hN' s1 s12 _ (mem_ThSp_of' _ _ _ _ h0)
  unfold J1at at j1 j2 ⊢
  rw [em, pull_mul_left, j2, pull_smul]
  show _ • TaylorLogMetric.pull D B.tor _ _ (TaylorLogMetric.Iop D B.tor _ _ (B.thZero N N')) = _
  rw [p, j1, Iop_smulF]
  show _ • _ • TaylorLogMetric.Iop D B.tor _ _ (TaylorLogMetric.Iop D B.tor _ _ (B.thZero N N')) = _
  rw [t, smul_smul, Formalism.BasicNotions.Examples₂.smulLat_mul, Matrix.det_mul, star_mul']
  simp only [map_mul, Finset.prod_mul_distrib, mul_pow]
  rw [mul_comm]
  rfl

theorem J2at_mul (hL : B.LatAll) (hTR : Tr0R D B.tor) {N N' : ℕ} (hN : Even N) (hN' : Even N')
    (h0 : B.ThZeroMem N N') :
    letI := D.host.cmStar
    ∀ γ₁ γ₂ : Matrix.unitaryGroup (Fin N') D.host.E, J2at B N N' γ₁ → J2at B N N' γ₂ → J2at B N N' (γ₁ * γ₂) := by
  letI := D.host.cmStar
  intro γ₁ γ₂ j1 j2
  have e1 : ((1 : Matrix.unitaryGroup (Fin N) D.host.E) : Matrix (Fin N) (Fin N) D.host.E) = 1 := rfl
  have em : ((γ₁ * γ₂ : Matrix.unitaryGroup (Fin N') D.host.E) : Matrix (Fin N') (Fin N') D.host.E) =
      (γ₁ : Matrix (Fin N') (Fin N') D.host.E) * (γ₂ : Matrix (Fin N') (Fin N') D.host.E) := rfl
  have s1 := smulSD D N' (StandardLatticesGL3.stdL D N') γ₁ (sd0 N')
  have s2 := smulSD D N' (StandardLatticesGL3.stdL D N') γ₂ (sd0 N')
  have s12 := smulSD D N' _ γ₁ s2
  have p := (pullIop_of hL N N' (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')
    (SDLat.smulLat (γ₂ : Matrix (Fin N') (Fin N') D.host.E) (StandardLatticesGL3.stdL D N')) 1 γ₁ hN hN' (sd0 N) (sd0 N) (sd0 N') s2
    (B.thZero N N') (mem_ThSp_of' _ _ _ _ h0)).2
  rw [e1, Formalism.BasicNotions.Examples₂.smulLat_one] at p
  have t := hTR N N' _ _ hN hN' s1 s12 _ (mem_ThSp_of' _ _ _ _ h0)
  unfold J2at at j1 j2 ⊢
  rw [em, pull_mul_right, j2, pull_smul, p, j1, Iop_smulF, t, smul_smul, Formalism.BasicNotions.Examples₂.smulLat_mul, Matrix.det_mul]
  simp only [map_mul, Finset.prod_mul_distrib, mul_pow]
  rw [mul_comm]

end Formalism.L2.PairingIndexBounds.Eq.J
end
end
end

-- Source module: Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.IntegralSquareRoots.ConstCopies

section

@[expose] public section

noncomputable section
open scoped BigOperators ComplexConjugate
open Classical

namespace Formalism.L2.PairingIndexBounds.Eq.J

open Formalism.L2.Th1.H

variable {ι : Type} [Fintype ι] {V V₁ : Type}

section Idx

variable [AddCommGroup V] [Module ℂ V] [AddCommGroup V₁] [Module ℂ V₁]
  {e : V ≃ₗ[ℂ] (ι → V₁)} {H : Sesq V} {H₁ : Sesq V₁} {α : V → ℂ} {α₁ : V₁ → ℂ}
  {Λ : AddSubgroup V} {Λ₁ : AddSubgroup V₁} {δ Ae : V ≃ₗ[ℂ] V} {δ₁ Ae₁ : V₁ ≃ₗ[ℂ] V₁}

theorem Copies.idx (c : Copies e H H₁ α α₁ Λ Λ₁ δ Ae δ₁ Ae₁) (i₀ : ι) (h : relIdx (latA Λ δ Ae) Λ ≠ 0) :
    relIdx (latA Λ₁ δ₁ Ae₁) Λ₁ ≠ 0 := by
  obtain ⟨S, hS⟩ := (repsExist V _ _ h).1
  let f : S → Λ₁ ⧸ (latA Λ₁ δ₁ Ae₁).addSubgroupOf Λ₁ := fun x =>
    QuotientAddGroup.mk ⟨e x.1 i₀, (c.lat x.1).1 (hS.1 x.1 x.2) i₀⟩
  have hf : Function.Surjective f := by
    intro q
    induction q using QuotientAddGroup.induction_on with
    | H y =>
      have hY : e.symm (Pi.single i₀ (y : V₁)) ∈ Λ := by
        refine (c.lat _).2 fun i => ?_
        rw [LinearEquiv.apply_symm_apply]
        by_cases hi : i = i₀
        · subst hi; rw [Pi.single_eq_same]; exact y.2
        · rw [Pi.single_eq_of_ne hi]; exact Λ₁.zero_mem
      obtain ⟨x, hx, hxy⟩ := hS.2.2 _ hY
      refine ⟨⟨x, hx⟩, ?_⟩
      have h2 := (c.mem_latA _).1 hxy i₀
      rw [map_sub, LinearEquiv.apply_symm_apply, Pi.sub_apply, Pi.single_eq_same] at h2
      show (QuotientAddGroup.mk _ : Λ₁ ⧸ (latA Λ₁ δ₁ Ae₁).addSubgroupOf Λ₁) = QuotientAddGroup.mk y
      rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
      show -(e x i₀) + (y : V₁) ∈ _
      rwa [neg_add_eq_sub]
  haveI : Finite (Λ₁ ⧸ (latA Λ₁ δ₁ Ae₁).addSubgroupOf Λ₁) := Finite.of_surjective f hf
  exact AddSubgroup.index_ne_zero_of_finite

end Idx

theorem unit_sq (a : ℂ) (ha : a ≠ 0) : ((‖a‖ : ℂ) / a) ^ 2 = conj a / a := by
  have h : ((‖a‖ : ℂ)) ^ 2 = a * conj a := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; rfl
  rw [div_pow, h]
  field_simp

variable [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] [AddCommGroup V₁] [Module ℂ V₁]
  [FiniteDimensional ℂ V₁]
  {e : V ≃ₗ[ℂ] (ι → V₁)} {H : Sesq V} {H₁ : Sesq V₁} {α : V → ℂ} {α₁ : V₁ → ℂ}
  {Λ : AddSubgroup V} {Λ₁ : AddSubgroup V₁} {δ Ae : V ≃ₗ[ℂ] V} {δ₁ Ae₁ : V₁ ≃ₗ[ℂ] V₁}

theorem const_copies (hLat : IsLat Λ) (hU : UnitaryData H Λ α δ Ae) (hLine : AtMostLine H α Λ)
    (c : Copies e H H₁ α α₁ Λ Λ₁ δ Ae δ₁ Ae₁) (hH₁ : IsHerm H₁) (hP₁ : IsPosDef H₁)
    (hI₁ : IsIsom H₁ H₁ (δ₁ : V₁ →ₗ[ℂ] V₁)) (hA₁ : ∀ x, Ae₁ x = x - δ₁.symm x)
    (hn : Even (Fintype.card ι)) (hr : Even (Module.finrank ℂ V₁))
    (hG : ∀ S₁ : Finset V₁, IsReps (latA Λ₁ δ₁ Ae₁) Λ₁ S₁ → gaussC H₁ α₁ Ae₁ S₁ ^ 2 = 1)
    (θ : V → ℂ) (hθ : θ ∈ Th H α Λ) :
    pullInv δ θ = LinearMap.det (δ₁ : V₁ →ₗ[ℂ] V₁) ^ (Fintype.card ι / 2) •
      inter H α Λ (imgLat (δ : V →ₗ[ℂ] V) Λ) θ := by
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i₀⟩⟩
  · haveI : Subsingleton V := e.injective.subsingleton
    have h1 : imgLat (δ : V →ₗ[ℂ] V) Λ = Λ := by
      ext x
      rw [Subsingleton.elim x 0]
      exact ⟨fun _ => Λ.zero_mem, fun _ => AddSubgroup.zero_mem _⟩
    rw [h1, Formalism.L2.Ker.inter_self H hU.herm Λ α hU.semi hθ.2, Fintype.card_eq_zero, Nat.zero_div, pow_zero, one_smul]
    funext z
    show θ (δ.symm z) = θ z
    rw [Subsingleton.elim (δ.symm z) z]
  · obtain ⟨S₁, hS₁⟩ := (repsExist V₁ _ _ (c.idx i₀ (UC.latA_idx_ne hLat hU))).1
    have hc := unitaryConstant V H Λ α δ Ae hLat hU hLine (prodReps e S₁) (c.reps hS₁) θ hθ
    rw [hc]
    congr 1
    obtain ⟨k, hk⟩ := hn
    have hk2 : Fintype.card ι / 2 = k := by omega
    have hk' : Fintype.card ι = 2 * k := by omega
    have ha : LinearMap.det (Ae₁ : V₁ →ₗ[ℂ] V₁) ≠ 0 := (LinearEquiv.isUnit_det' Ae₁).ne_zero
    have hd := detCayley V₁ H₁ hH₁ hP₁ δ₁ Ae₁ hI₁ hA₁
    rw [hr.neg_one_pow, one_mul] at hd
    rw [c.gauss hS₁.1, det_copies e (Ae : V →ₗ[ℂ] V) (Ae₁ : V₁ →ₗ[ℂ] V₁) c.cay, hk2, hk', pow_mul (gaussC _ _ _ _),
      hG S₁ hS₁, one_pow, mul_one, norm_pow, Complex.ofReal_pow, ← div_pow, pow_mul, unit_sq _ ha, hd,
      mul_div_assoc, div_self ha, mul_one]

end Formalism.L2.PairingIndexBounds.Eq.J
end
end
end

-- Source module: Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.IntegralSquareRoots.LineOfSpans

section

@[expose] public section

noncomputable section
open NumberField Formalism.BasicNotions Classical Matrix

namespace Formalism.L2.PairingIndexBounds.Eq.J

open Formalism.MainNotions Formalism.L2.Th1.H Formalism.L2.PairingIndexBounds.Eq

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

def GaussRow (B : Ker.Base D cc δ) : Prop :=
  ∀ (N : ℕ) (γ : Matrix.unitaryGroup (Fin N) D.host.E) (Ae : TaylorLogMetric.VC D N 1 ≃ₗ[ℂ] TaylorLogMetric.VC D N 1), Even N →
    (∀ x, Ae x = x - (phiU γ 1 : TaylorLogMetric.VC D N 1 ≃ₗ[ℂ] TaylorLogMetric.VC D N 1).symm x) →
    ∀ S : Finset (TaylorLogMetric.VC D N 1), IsReps (latA (La0 B N 1) (phiU γ 1) Ae) (La0 B N 1) S →
      gaussC (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.tor0 D cc δ).abelian₂) D.what₂.Tau N 1) (TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ)) Ae S ^ 2 = 1

def Lat0IsLat (B : Ker.Base D cc δ) (N N' : ℕ) : Prop := IsLat (La0 B N N')

theorem exists_cay {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (φ : V ≃ₗ[ℂ] V)
    (h : ∀ x, φ.symm x = x → x = 0) : ∃ Ae : V ≃ₗ[ℂ] V, ∀ x, Ae x = x - φ.symm x := by
  have hinj : Function.Injective ((LinearMap.id - (φ.symm : V →ₗ[ℂ] V)) : V →ₗ[ℂ] V) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have : x - φ.symm x = 0 := hx
    exact h x (sub_eq_zero.mp this).symm
  exact ⟨LinearEquiv.ofInjectiveEndo _ hinj, fun x => rfl⟩

variable {B : Ker.Base D cc δ}

theorem line_of_spans {N N' : ℕ} (hSp : B.ThZeroSpans N N') :
    AtMostLine (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.tor0 D cc δ).abelian₂) D.what₂.Tau N N') (TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ)) (La0 B N N') := by
  intro θ hθ hθ0 F hF
  obtain ⟨a, ha⟩ := hSp θ hθ
  obtain ⟨b, hb⟩ := hSp F hF
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hθ0 (by rw [ha, zero_smul])
  exact ⟨b * a⁻¹, by rw [ha, hb, smul_smul, inv_mul_cancel_right₀ ha0]⟩

theorem unitaryData (hL : B.LatAll) {N N' : ℕ} (hN : Even N) (hN' : Even N')
    (γ : Matrix.unitaryGroup (Fin N) D.host.E) (γ' : Matrix.unitaryGroup (Fin N') D.host.E)
    (Ae : TaylorLogMetric.VC D N N' ≃ₗ[ℂ] TaylorLogMetric.VC D N N') (hA : ∀ x, Ae x = x - (phiU γ γ').symm x) :
    UnitaryData (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.tor0 D cc δ).abelian₂) D.what₂.Tau N N') (La0 B N N') (TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ))
      (phiU γ γ') Ae := by
  have a0 : TaylorLogMetric.admitted D N N' (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N') := admissible_of_integral_conj_le hN hN' (sd0 N) (sd0 N')
  have a1 : TaylorLogMetric.admitted D N N' (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) (StandardLatticesGL3.stdL D N))
      (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) (StandardLatticesGL3.stdL D N')) :=
    admissible_of_integral_conj_le hN hN' (smulSD D N _ γ (sd0 N)) (smulSD D N' _ γ' (sd0 N'))
  have hi : imgLat ((phiU γ γ' : TaylorLogMetric.VC D N N' ≃ₗ[ℂ] TaylorLogMetric.VC D N N') : TaylorLogMetric.VC D N N' →ₗ[ℂ] TaylorLogMetric.VC D N N') (La0 B N N') =
      TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) (StandardLatticesGL3.stdL D N))
        (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) (StandardLatticesGL3.stdL D N')) := la_img _ _ _ _ _ _ _ _
  exact
    { herm := formV_herm' _ _ _ _
      pos := formV_pos (area_pos' B) _ _ _
      selfDual := (hL.1 N N' _ _ a0).1
      semi := (hL.1 N N' _ _ a0).2
      isom := phiL_isom _ _ _ _ _ _ _
      semi' := by rw [hi]; exact (hL.1 N N' _ _ a1).2
      inv := fun x _ => al_phi _ _ _ _ _ _ x
      idx₁ := by rw [hi]; exact (hL.2 N N' _ _ _ _ a1 a0).1
      idx₂ := by rw [hi]; exact (hL.2 N N' _ _ _ _ a0 a1).1
      cay := hA }

theorem J1at_of_ne (hS : B.StdOK) (hL : B.LatAll) (hG : GaussRow B) {N N' : ℕ} (hN : Even N) (hN' : Even N')
    (hLat : Lat0IsLat B N N') (hSp : B.ThZeroSpans N N') (γ : Matrix.unitaryGroup (Fin N) D.host.E)
    (hγ : (1 - (γ : Matrix (Fin N) (Fin N) D.host.E)).det ≠ 0) : J1at B N N' γ := by
  obtain ⟨Ae, hA⟩ := exists_cay (phiU γ 1 : TaylorLogMetric.VC D N N' ≃ₗ[ℂ] TaylorLogMetric.VC D N N') (nofix γ hγ)
  obtain ⟨Ae₁, hA₁⟩ := exists_cay (phiU γ 1 : TaylorLogMetric.VC D N 1 ≃ₗ[ℂ] TaylorLogMetric.VC D N 1) (nofix γ hγ)
  have c : Copies (rowE D N N') (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.tor0 D cc δ).abelian₂) D.what₂.Tau N N')
      (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.tor0 D cc δ).abelian₂) D.what₂.Tau N 1) (TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ)) (TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ))
      (La0 B N N') (La0 B N 1) (phiU γ 1) Ae (phiU γ 1) Ae₁ :=
    { form := form_row _ N N'
      char := al_row B hS N N'
      lat := lat_row B N N'
      map := map_row γ
      cay := fun x i => by
        rw [hA, hA₁, map_sub, Pi.sub_apply, symm_coord (rowE D N N') _ _ (map_row γ)] }
  have h := const_copies hLat (unitaryData hL hN hN' γ 1 Ae hA) (line_of_spans hSp) c (formV_herm' _ _ _ _)
    (formV_pos (area_pos' B) _ _ _) (phiL_isom _ _ _ _ _ _ _) hA₁ (by rw [Fintype.card_fin]; exact hN')
    (by rw [finrank_row]; exact hN.mul_left _) (fun S₁ hS₁ => hG N γ Ae₁ hN hA₁ S₁ hS₁) (B.thZero N N')
    (B.thZeroMem hS N N')
  rw [det_row, Fintype.card_fin] at h
  have hi : imgLat ((phiU γ 1 : TaylorLogMetric.VC D N N' ≃ₗ[ℂ] TaylorLogMetric.VC D N N') : TaylorLogMetric.VC D N N' →ₗ[ℂ] TaylorLogMetric.VC D N N') (La0 B N N') =
      TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) (StandardLatticesGL3.stdL D N))
        (SDLat.smulLat (1 : Matrix (Fin N') (Fin N') D.host.E) (StandardLatticesGL3.stdL D N')) := la_img _ _ _ _ _ _ _ _
  rw [hi, Formalism.BasicNotions.Examples₂.smulLat_one] at h
  exact h

theorem J2at_of_ne (hS : B.StdOK) (hL : B.LatAll) (hG : GaussRow B) {N N' : ℕ} (hN : Even N) (hN' : Even N')
    (hLat : Lat0IsLat B N N') (hSp : B.ThZeroSpans N N') (γ' : Matrix.unitaryGroup (Fin N') D.host.E)
    (hγ : (1 - (γ' : Matrix (Fin N') (Fin N') D.host.E)).det ≠ 0) : J2at B N N' γ' := by
  have hfix₁ := nofix (N' := 1) (cjU γ') (ne_cjU γ' hγ)
  have hfix : ∀ x : TaylorLogMetric.VC D N N', (phiU 1 γ').symm x = x → x = 0 := by
    intro x hx
    apply (colE D N N').injective
    funext j
    rw [map_zero]
    refine hfix₁ _ ?_
    rw [← symm_coord (colE D N N') _ _ (map_col γ'), hx]
  obtain ⟨Ae, hA⟩ := exists_cay (phiU 1 γ' : TaylorLogMetric.VC D N N' ≃ₗ[ℂ] TaylorLogMetric.VC D N N') hfix
  obtain ⟨Ae₁, hA₁⟩ := exists_cay (phiU (cjU γ') 1 : TaylorLogMetric.VC D N' 1 ≃ₗ[ℂ] TaylorLogMetric.VC D N' 1) hfix₁
  have c : Copies (colE D N N') (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.tor0 D cc δ).abelian₂) D.what₂.Tau N N')
      (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.tor0 D cc δ).abelian₂) D.what₂.Tau N' 1) (TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ)) (TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ))
      (La0 B N N') (La0 B N' 1) (phiU 1 γ') Ae (phiU (cjU γ') 1) Ae₁ :=
    { form := form_col _ N N'
      char := al_col B hS N N'
      lat := lat_col B N N'
      map := map_col γ'
      cay := fun x i => by
        rw [hA, hA₁, map_sub, Pi.sub_apply, symm_coord (colE D N N') _ _ (map_col γ')] }
  have h := const_copies hLat (unitaryData hL hN hN' 1 γ' Ae hA) (line_of_spans hSp) c (formV_herm' _ _ _ _)
    (formV_pos (area_pos' B) _ _ _) (phiL_isom _ _ _ _ _ _ _) hA₁ (by rw [Fintype.card_fin]; exact hN)
    (by rw [finrank_row]; exact hN'.mul_left _) (fun S₁ hS₁ => hG N' (cjU γ') Ae₁ hN' hA₁ S₁ hS₁) (B.thZero N N')
    (B.thZeroMem hS N N')
  rw [det_row, Fintype.card_fin, det_cjU, star_star] at h
  have hi : imgLat ((phiU 1 γ' : TaylorLogMetric.VC D N N' ≃ₗ[ℂ] TaylorLogMetric.VC D N N') : TaylorLogMetric.VC D N N' →ₗ[ℂ] TaylorLogMetric.VC D N N') (La0 B N N') =
      TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (SDLat.smulLat (1 : Matrix (Fin N) (Fin N) D.host.E) (StandardLatticesGL3.stdL D N))
        (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) (StandardLatticesGL3.stdL D N')) := la_img _ _ _ _ _ _ _ _
  rw [hi, Formalism.BasicNotions.Examples₂.smulLat_one] at h
  exact h

end Formalism.L2.PairingIndexBounds.Eq.J
end
end
end
