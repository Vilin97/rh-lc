module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsNormalFr
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunKilled
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ColsAtBfOfNormalFrames
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompProjAnisotropicAnisotropicEmbedding
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
import Development.AbelianVarietyTheory.Definitions.Foundations.ValuedAlgebraMapEqOne
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnesRepresent
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselNormalFrameIsotropicColumnsPairing

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BesFrameCols

theorem cols_pair : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ρ : ℕ) (B : BesLev D ρ) (n : Type) [Fintype n] [DecidableEq n] (c : ℕ) (s : k) (FA : Frame k B.A.rank n) (F : Frame k B.V.rank (n ⊕ Fin c)), p.IsBesFrame B s FA F → ∀ i : Fin ρ, ∃ m₀ m₁ : n ⊕ Fin c, (∀ r, F.β r m₀ = s * p.xi ^ (ρ - i.val) * p.pr (B.d.e r i)) ∧ (∀ r, F.β r m₁ = s * (-p.hz B / p.xi) * (-1 / p.xi) ^ (ρ - 1 - i.val) * p.pr (B.d.e' r i)) ∧ ∀ m, m ≠ m₁ → ∑ r, ∑ r', p.pr (star (B.d.e r i)) * p.pr (B.V.gram r r') * F.β r' m = 0 := by
  intro D k _ _ _ _ p ρ B n _ _ c s FA F hF i
  obtain ⟨hc, h1, h2, h3, h4⟩ := hF
  subst hc
  set G := B.V.gram with hGdef
  have hGh : Gᴴ = G := by
    refine Matrix.ext fun a b => ?_
    simp only [G, Matrix.conjTranspose_apply]
    exact GlobalTheory.DualPairCheck.gram_star B.V b a
  have heG0 : (B.d.e)ᴴ * G * B.d.i₀ = 0 := by
    have h := congrArg Matrix.conjTranspose B.d.i₀e
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_zero] at h
    rw [← hGdef, hGh] at h
    rw [← h, Matrix.mul_assoc]
  have heGe : (B.d.e)ᴴ * G * B.d.e = 0 := B.d.ee
  have heGe' : (B.d.e)ᴴ * G * B.d.e' = 1 := by
    have h := congrArg Matrix.conjTranspose B.d.e'e
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_one] at h
    rw [← hGdef, hGh] at h
    rw [← h, Matrix.mul_assoc]
  have key : ∀ x : Fin B.V.rank → D.host.E, ∑ r, ∑ r', p.pr (star (B.d.e r i)) * p.pr (G r r') * p.pr (x r') =
      p.pr ((((B.d.e)ᴴ * G) *ᵥ x) i) := by
    intro x
    change ∑ r, ∑ r', LocMod.Witness.prH p _ * LocMod.Witness.prH p _ * LocMod.Witness.prH p _ = LocMod.Witness.prH p _

    simp only [← map_mul, ← map_sum]
    congr 1
    simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  have keyc : ∀ (a : k) (x : Fin B.V.rank → D.host.E), ∑ r, ∑ r', p.pr (star (B.d.e r i)) * p.pr (G r r') * (a * p.pr (x r')) =
      a * p.pr ((((B.d.e)ᴴ * G) *ᵥ x) i) := by
    intro a x
    rw [← key, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r' _ => ?_
    ring
  have colM : ∀ {κ : Type} (M : Matrix (Fin B.V.rank) κ D.host.E) (j : κ), (((B.d.e)ᴴ * G) *ᵥ fun r => M r j) i = ((B.d.e)ᴴ * G * M) i j := by
    intro κ M j
    simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply]
  refine ⟨Sum.inr ⟨i.val, by omega⟩, Sum.inr ⟨2 * ρ - i.val, by omega⟩, fun r => h2 i _ rfl r,
    fun r => h4 i _ (by simp only; omega) r, ?_⟩
  rintro (a | ⟨j, hj⟩) hm
  · have hM : ((B.d.e)ᴴ * G * (B.d.i₀ * B.o.iA)) = 0 := by rw [← Matrix.mul_assoc, heG0, Matrix.zero_mul]
    generalize B.d.i₀ * B.o.iA = M at h1 hM
    calc ∑ r, ∑ r', p.pr (star (B.d.e r i)) * p.pr (G r r') * F.β r' (Sum.inl a)
        = ∑ u, FA.β u a * ∑ r, ∑ r', p.pr (star (B.d.e r i)) * p.pr (G r r') * p.pr (M r' u) := by
          simp_rw [h1 _ a, Matrix.mul_apply, Matrix.map_apply, Finset.mul_sum]
          conv_rhs => rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun r _ => ?_
          conv_rhs => rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun r' _ => ?_
          refine Finset.sum_congr rfl fun u _ => ?_
          ring
      _ = 0 := by
          refine Finset.sum_eq_zero fun u _ => ?_
          rw [key (fun r' => M r' u), colM, hM]
          simp [LocMod.Place.pr]
  · have hne : j ≠ 2 * ρ - i.val := fun h => hm (by subst h; rfl)
    rcases lt_trichotomy j ρ with hlt | heq | hgt
    · simp_rw [h2 ⟨j, hlt⟩ ⟨j, hj⟩ rfl]
      refine (keyc _ (fun r' => B.d.e r' ⟨j, hlt⟩)).trans ?_
      rw [colM, heGe]
      simp [LocMod.Place.pr]
    · simp_rw [h3 ⟨j, hj⟩ heq]
      refine (keyc _ (B.d.i₀ *ᵥ vecB B.o B.ζ)).trans ?_
      rw [Matrix.mulVec_mulVec, heG0, Matrix.zero_mulVec]
      simp [LocMod.Place.pr]
    · have hlt' : 2 * ρ - j < ρ := by omega
      simp_rw [h4 ⟨2 * ρ - j, hlt'⟩ ⟨j, hj⟩ (by simp only; omega)]
      refine (keyc _ (fun r' => B.d.e' r' ⟨2 * ρ - j, hlt'⟩)).trans ?_
      rw [colM, heGe', Matrix.one_apply_ne (fun h => hne (by rw [Fin.ext_iff] at h; simp only at h; omega))]
      simp [LocMod.Place.pr]

end GlobalTheory.BesFrameCols
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselNormalFrameIsotropicColumnsPairingStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.besselNormalFrame_isotropicColumns_pairing : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ρ : ℕ) (B : BesLev D ρ) (n : Type) [Fintype n] [DecidableEq n] (c : ℕ) (s : k) (FA : Frame k B.A.rank n) (F : Frame k B.V.rank (n ⊕ Fin c)), p.IsBesFrame B s FA F → ∀ i : Fin ρ, ∃ m₀ m₁ : n ⊕ Fin c, (∀ r, F.β r m₀ = s * p.xi ^ (ρ - i.val) * p.pr (B.d.e r i)) ∧ (∀ r, F.β r m₁ = s * (-p.hz B / p.xi) * (-1 / p.xi) ^ (ρ - 1 - i.val) * p.pr (B.d.e' r i)) ∧ ∀ m, m ≠ m₁ → ∑ r, ∑ r', p.pr (star (B.d.e r i)) * p.pr (B.V.gram r r') * F.β r' m = 0 := by
  first | exact @GlobalTheory.BesFrameCols.cols_pair | exact GlobalTheory.BesFrameCols.cols_pair | (intros; apply GlobalTheory.BesFrameCols.cols_pair <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiNormalFrameIsotropicColumnsPairing

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocMod.JacCols

theorem cols_pair : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ρ : ℕ) (J : JacLev D ρ) (n : Type) [Fintype n] [DecidableEq n] (c : ℕ) (s hh : k) (F₀ : Frame k J.W₀.rank n) (F : Frame k J.W.rank (n ⊕ Fin c)), p.IsJacFrame J s hh F₀ F → ∀ i : Fin ρ, ∃ m₀ m₁ : n ⊕ Fin c, (∀ r, F.β r m₀ = s * p.xi ^ (ρ - i.val) * p.pr (J.d.e r i)) ∧ (∀ r, F.β r m₁ = s * (hh / p.xi) * (-1 / p.xi) ^ (ρ - 1 - i.val) * p.pr (J.d.e' r i)) ∧ ∀ m, m ≠ m₁ → ∑ r, ∑ r', p.pr (star (J.d.e r i)) * p.pr (J.W.gram r r') * F.β r' m = 0 := by
  intro D k _ _ _ _ p ρ J n _ _ c s hh F₀ F hF i
  obtain ⟨hc, h0, h1, h2⟩ := hF
  subst hc
  have hpr : ∀ a, p.pr a = Witness.prH p a := fun _ => rfl

  have hG : (J.W.gram)ᴴ = J.W.gram := by
    ext a b
    rw [Matrix.conjTranspose_apply]
    exact GlobalTheory.DualPairCheck.gram_star J.W b a

  have L : ∀ {Z : Type} [Fintype Z] (M : Matrix (Fin J.W.rank) Z k) (z : Z),
      ∑ r, ∑ r', p.pr (star (J.d.e r i)) * p.pr (J.W.gram r r') * M r' z =
        (((J.d.eᴴ * J.W.gram).map (Witness.prH p)) * M) i z := by
    intro Z _ M z
    rw [Finset.sum_comm, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun r' _ => ?_

    rw [← Finset.sum_mul, Matrix.map_apply, Matrix.mul_apply, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [map_mul, Matrix.conjTranspose_apply, hpr, hpr]
  have Ls : ∀ (M : Matrix (Fin J.W.rank) (Fin ρ) D.host.E) (j : Fin ρ) (t : k),
      ∑ r, ∑ r', p.pr (star (J.d.e r i)) * p.pr (J.W.gram r r') * (t * p.pr (M r' j)) =
        t * Witness.prH p ((J.d.eᴴ * J.W.gram * M) i j) := by
    intro M j t
    have := L (t • M.map (Witness.prH p)) j
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul] at this
    simp only [hpr] at this ⊢
    rw [this, Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul, ← Matrix.map_mul]
    rfl

  have eI : J.d.eᴴ * J.W.gram * J.d.i₀ = 0 := by
    have := congrArg Matrix.conjTranspose J.d.i₀e
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hG,
      Matrix.conjTranspose_zero, ← Matrix.mul_assoc] at this
  have eE' : J.d.eᴴ * J.W.gram * J.d.e' = 1 := by
    have := congrArg Matrix.conjTranspose J.d.e'e
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hG,
      Matrix.conjTranspose_one, ← Matrix.mul_assoc] at this
  refine ⟨Sum.inr ⟨i.val, by omega⟩, Sum.inr ⟨2 * ρ - 1 - i.val, by omega⟩, fun r => h1 i _ rfl r,
    fun r => h2 i _ (by simp only; omega) r, ?_⟩
  intro m hm
  rcases m with a | ⟨j, hj⟩
  · rw [L F.β (Sum.inl a)]
    have hcol : ∀ r, F.β r (Sum.inl a) = (J.d.i₀.map (Witness.prH p) * F₀.β) r a := fun r => h0 r a
    rw [Matrix.mul_apply]
    simp only [hcol]
    rw [← Matrix.mul_apply, ← Matrix.mul_assoc, ← Matrix.map_mul, eI, Matrix.map_zero _ (map_zero _), Matrix.zero_mul,
      Matrix.zero_apply]
  · by_cases hjρ : j < ρ
    · have hcol : ∀ r, F.β r (Sum.inr ⟨j, hj⟩) = s * p.xi ^ (ρ - j) * p.pr (J.d.e r ⟨j, hjρ⟩) :=
        fun r => h1 ⟨j, hjρ⟩ _ rfl r
      simp only [hcol]
      rw [Ls, J.d.ee, Matrix.zero_apply, map_zero, mul_zero]
    · set i' : Fin ρ := ⟨2 * ρ - 1 - j, by omega⟩ with hi'
      have hcol : ∀ r, F.β r (Sum.inr ⟨j, hj⟩) = s * (hh / p.xi) * (-1 / p.xi) ^ (ρ - 1 - i'.val) * p.pr (J.d.e' r i') :=
        fun r => h2 i' _ (by simp only [hi']; omega) r
      simp only [hcol]
      have hne : i ≠ i' := by
        intro h
        apply hm
        rw [h]
        simp only [hi', Sum.inr.injEq, Fin.mk.injEq]
        omega
      rw [Ls, eE', Matrix.one_apply_ne hne, map_zero, mul_zero]

end GlobalTheory.LocMod.JacCols
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiNormalFrameIsotropicColumnsPairingStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.fourierJacobiNormalFrame_isotropicColumns_pairing : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ρ : ℕ) (J : JacLev D ρ) (n : Type) [Fintype n] [DecidableEq n] (c : ℕ) (s hh : k) (F₀ : Frame k J.W₀.rank n) (F : Frame k J.W.rank (n ⊕ Fin c)), p.IsJacFrame J s hh F₀ F → ∀ i : Fin ρ, ∃ m₀ m₁ : n ⊕ Fin c, (∀ r, F.β r m₀ = s * p.xi ^ (ρ - i.val) * p.pr (J.d.e r i)) ∧ (∀ r, F.β r m₁ = s * (hh / p.xi) * (-1 / p.xi) ^ (ρ - 1 - i.val) * p.pr (J.d.e' r i)) ∧ ∀ m, m ≠ m₁ → ∑ r, ∑ r', p.pr (star (J.d.e r i)) * p.pr (J.W.gram r r') * F.β r' m = 0 := by
  first | exact @GlobalTheory.LocMod.JacCols.cols_pair | exact GlobalTheory.LocMod.JacCols.cols_pair | (intros; apply GlobalTheory.LocMod.JacCols.cols_pair <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittHyperbolicConjPairingEqOne

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DiagonalHyperbolic

theorem hyp_diag (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (i : Fin ρ) :
    ∑ r, ∑ r', star (d.e r i) * S.gram r r' * d.e' r' i = 1 := by
  have hG : S.gramᴴ = S.gram := Matrix.ext fun a b => GlobalTheory.LatVac.gram_star S b a
  have h := congrArg Matrix.conjTranspose d.e'e
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hG,
    Matrix.conjTranspose_one] at h
  have h2 := congrFun (congrFun h i) i
  rw [Matrix.one_apply_eq] at h2
  rw [← h2]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.mul_sum, mul_assoc]
end GlobalTheory.DiagonalHyperbolic
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittHyperbolicConjPairingEqOneStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.wittHyperbolic_conj_pairing_eq_one : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (i : Fin ρ), ∑ r, ∑ r', star (d.e r i) * S.gram r r' * d.e' r' i = 1 := by
  first | exact @GlobalTheory.DiagonalHyperbolic.hyp_diag | exact GlobalTheory.DiagonalHyperbolic.hyp_diag | (intros; apply GlobalTheory.DiagonalHyperbolic.hyp_diag <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiMapCarriesNormalFrameLines

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ColsXZeroNormal

theorem colsAt_xZero_of_normalFr : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ {a : XGeo D} (y : YRat a) {βT : GL (Fin D.sp.X'.rank) (Lev.EAf D)} {PP : Pl D.host.E} (l : LocX a βT PP) (FY : FYFam l) (sc : ℕ → l.k), IsNormalFr l y FY sc → (∀ j, j ≤ D.R.m → (a.x j).Is) → ∀ (N : ∀ j, GlobalTheory.FinPl.Lat (Yc D j)) (M : ∀ j ρ (h : j + 2 * ρ + 2 = D.R.m), GlobalTheory.FinPl.Lat (y.bes j ρ h).V₀), (∀ j, j < D.R.m → IsSelfDualC (Yc D j) (N j)) → (∀ j c (hc : j + c = l.s + 1), IntIn l.q (Yc D j) (FY j c hc) (N j)) → (∀ j ρ h, IsSelfDualC (y.bes j ρ h).V₀ (M j ρ h)) → (∀ j ρ h (hj : j ≤ l.s + 1) (F₀ : Frame l.k ((y.bes j ρ h).lev (a.x j).vol).V₀.rank (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Unit)), (ofSplit l.q).IsCoreFrame ((y.bes j ρ h).lev (a.x j).vol) (sc j) (l.FX j hj) F₀ → IntIn l.q _ F₀ (M j ρ h)) → ∀ j ρ (h : j + 2 * ρ + 2 = D.R.m), GlobalTheory.FinPl.ColsAt ((y.bes j ρ h).lev (a.x j).vol).d (xZero ((y.jac j ρ h).lev (a.x (j + 1)).vol).d) (N j) (N (j + 1)) ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) := by
  intro D ψ hψ a y βT PP l FY sc hN hx N M hNsd hNI hMsd hcore j ρ h
  rw [← l.under]
  intro i b hb
  rw [l.unit.2]
  have hs := l.hs
  have hdB : j + (2 * ρ + 1) = l.s + 1 := by omega
  have hdJ : j + 1 + 2 * ρ = l.s + 1 := by omega
  have hxi := GlobalTheory.ColsBFSplit.xi_unit l.q l.unit
  obtain ⟨hsc, -, hhz, hB, hJ, -⟩ := hN
  obtain ⟨m₀, m₁, h0, h1, hp⟩ := GlobalTheory.T.besselNormalFrame_isotropicColumns_pairing D l.k (ofSplit l.q) ρ ((y.bes j ρ h).lev (a.x j).vol)
    (XIx (Fin D.R.k) (Fin D.R.t) j) (2 * ρ + 1) (sc j) (l.FX j (by omega)) (FY j (2 * ρ + 1) hdB) (hB j ρ h (2 * ρ + 1) hdB) i
  obtain ⟨n₀, n₁, g0, g1, gp⟩ := GlobalTheory.T.fourierJacobiNormalFrame_isotropicColumns_pairing D l.k (ofSplit l.q) ρ ((y.jac j ρ h).lev (a.x (j + 1)).vol)
    (XIx (Fin D.R.k) (Fin D.R.t) (j + 1)) (2 * ρ) (sc j) ((ofSplit l.q).hz ((y.bes j ρ h).lev (a.x j).vol))
    (l.FX (j + 1) (by omega)) (FY (j + 1) (2 * ρ) hdJ) (hJ j ρ h (2 * ρ) hdJ) i
  have v0 : valuation l.k (sc j * (ofSplit l.q).xi ^ (ρ - i.val)) = 1 := by
    rw [map_mul, map_pow, hsc, hxi, one_pow, one_mul]
  have v1 : valuation l.k (sc j * (-(ofSplit l.q).hz ((y.bes j ρ h).lev (a.x j).vol) / (ofSplit l.q).xi) *
      (-1 / (ofSplit l.q).xi) ^ (ρ - 1 - i.val)) = 1 := by
    rw [map_mul, map_mul, map_pow, map_div₀, map_div₀, Valuation.map_neg, Valuation.map_neg, map_one, hsc, hhz, hxi]
    simp
  have w1 : valuation l.k (sc j * ((ofSplit l.q).hz ((y.bes j ρ h).lev (a.x j).vol) / (ofSplit l.q).xi) *
      (-1 / (ofSplit l.q).xi) ^ (ρ - 1 - i.val)) = 1 := by
    rw [map_mul, map_mul, map_pow, map_div₀, map_div₀, Valuation.map_neg, map_one, hsc, hhz, hxi]
    simp
  have eV := GlobalTheory.ColsBFSplit.line_crit l.q (FY j (2 * ρ + 1) hdB) (fun r => ((y.bes j ρ h).lev (a.x j).vol).d.e r i)
    (fun r => ((y.bes j ρ h).lev (a.x j).vol).d.e' r i) m₀ m₁ _ _ (hNsd j (by omega)) (hNI j _ hdB) v0 v1 h0 h1
    (GlobalTheory.T.wittHyperbolic_conj_pairing_eq_one D _ _ ρ ((y.bes j ρ h).lev (a.x j).vol).d i) hp b hb
  have eW := GlobalTheory.ColsBFSplit.line_crit l.q (FY (j + 1) (2 * ρ) hdJ) (fun r => ((y.jac j ρ h).lev (a.x (j + 1)).vol).d.e r i)
    (fun r => ((y.jac j ρ h).lev (a.x (j + 1)).vol).d.e' r i) n₀ n₁ _ _ (hNsd (j + 1) (by omega)) (hNI (j + 1) _ hdJ) v0 w1
    g0 g1 (GlobalTheory.T.wittHyperbolic_conj_pairing_eq_one D _ _ ρ ((y.jac j ρ h).lev (a.x (j + 1)).vol).d i) gp b hb
  exact eV.trans eW.symm

end GlobalTheory.ColsXZeroNormal

end
end
end
