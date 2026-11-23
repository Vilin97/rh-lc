module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ParabolicInductionFiniteLength
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import GroundTheory.AutomorphicForms.SupercuspidalCoefficients
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceLocalComponentExistsUniqueClass
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JhMultSubAddQuot
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityPos
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.JacquetModuleFiniteLength
public import GroundTheory.AutomorphicForms.CuspidalSplittingCoeff
public import GroundTheory.AutomorphicForms.CuspidalSplittingIsotypic
import GroundTheory.AutomorphicForms.CuspidalSplittingProjective
import GroundTheory.AutomorphicForms.SmoothRepSchur
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
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
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
import GroundTheory.LocalFields.PadicLogSeries
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm

-- Source module: GroundTheory.AutomorphicForms.CuspidalSplitting

section

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Automorphic

namespace Parabolic

open Function Iwasawa

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

theorem modularCharacter_eq_one_of_mem_center {H : Type*} [TopologicalSpace H] [Group H]
    [IsTopologicalGroup H] [LocallyCompactSpace H] {g : H} (hg : g ∈ Subgroup.center H) :
    MeasureTheory.Measure.modularCharacter g = 1 := by
  change MeasureTheory.Measure.modularCharacterFun g = 1
  borelize H
  rw [MeasureTheory.Measure.modularCharacterFun_eq_haarScalarFactor
    MeasureTheory.Measure.haar g]
  have hcomm : (fun x : H => x * g) = (fun x => g * x) :=
    funext fun x => Subgroup.mem_center_iff.1 hg x
  have key : MeasureTheory.Measure.map (fun x : H => x * g)
      (MeasureTheory.Measure.haar : MeasureTheory.Measure H) = MeasureTheory.Measure.haar := by
    rw [hcomm]
    exact MeasureTheory.map_mul_left_eq_self _ g
  calc MeasureTheory.Measure.haarScalarFactor
        (MeasureTheory.Measure.map (fun x : H => x * g)
          (MeasureTheory.Measure.haar : MeasureTheory.Measure H))
        (MeasureTheory.Measure.haar : MeasureTheory.Measure H)
      = MeasureTheory.Measure.haarScalarFactor
          (MeasureTheory.Measure.haar : MeasureTheory.Measure H)
          (MeasureTheory.Measure.haar : MeasureTheory.Measure H) := by congr 1
    _ = 1 := MeasureTheory.Measure.haarScalarFactor_self _


omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem center_le_levi {α : Type*} [LinearOrder α] (β : Fin n → α) :
    Subgroup.center (GL (Fin n) F) ≤ levi F n β := by
  intro z hz
  obtain ⟨a, ha⟩ := Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.1 hz
  rw [mem_levi]
  intro i j hij
  have hij' : i ≠ j := fun h => hij (h ▸ rfl)
  change (z : Matrix (Fin n) (Fin n) F) i j = 0
  rw [← ha, Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij']

theorem sqrtModular_of_mem_center {α : Type*} [LinearOrder α] {β : Fin n → α}
    {z : GL (Fin n) F} (hz : z ∈ Subgroup.center (GL (Fin n) F)) :
    sqrtModular F n β ⟨z, levi_le_blockUpper (center_le_levi β hz)⟩ = 1 := by
  have hc : (⟨z, levi_le_blockUpper (center_le_levi β hz)⟩ : blockUpper F n β) ∈
      Subgroup.center (blockUpper F n β) :=
    Subgroup.mem_center_iff.2 fun p => Subtype.ext (Subgroup.mem_center_iff.1 hz p)
  change ((NNReal.sqrt (MeasureTheory.Measure.modularCharacter _) : ℝ) : ℂ) = 1
  rw [modularCharacter_eq_one_of_mem_center hc]
  simp

theorem hasCentralChar_parabolicInd {α : Type*} [LinearOrder α] {β : Fin n → α}
    {W : Type*} [AddCommGroup W] [Module ℂ W] {τ : Representation ℂ (levi F n β) W}
    {ω : GL (Fin n) F → ℂ}
    (hτ : ∀ z (hz : z ∈ Subgroup.center (GL (Fin n) F)), ∀ w,
      τ ⟨z, center_le_levi β hz⟩ w = ω z • w) :
    HasCentralChar (parabolicInd F n β τ) ω := by
  intro z hz f
  apply Subtype.ext
  funext x
  have hf := ((mem_parabolicIndSpace τ).1 f.2).1 ⟨z, levi_le_blockUpper (center_le_levi β hz)⟩ x
  change (f : GL (Fin n) F → W) (x * z) = ω z • (f : GL (Fin n) F → W) x
  rw [Subgroup.mem_center_iff.1 hz x]
  change (f : GL (Fin n) F → W) (z * x) = _ at hf
  rw [hf, sqrtModular_of_mem_center hz, one_smul, leviProj_of_mem_levi (center_le_levi β hz),
    hτ z hz]

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin n) F) V}

theorem not_surjective_of_le_parabolicInd [π.IsIrreducible] (hπ : IsSmooth π)
    (hsc : IsSupercuspidal π) {β : Fin n → ℕ} (hβ : ∃ i j, β i ≠ β j) {W : Type*}
    [AddCommGroup W] [Module ℂ W] {τ : Representation ℂ (levi F n β) W}
    {ω : GL (Fin n) F → ℂ} (hωτ : HasCentralChar (parabolicInd F n β τ) ω)
    (A : Subrepresentation (parabolicInd F n β τ))
    (p : Representation.IntertwiningMap A.toRepresentation π) : ¬ Surjective p := by
  intro hp
  obtain ⟨u₀, hu₀⟩ := exists_ne_zero_of_isIrreducible (ρ := π)
  have hωπ : HasCentralChar π ω := by
    intro z hz x
    obtain ⟨a, rfl⟩ := hp x
    rw [← Representation.IntertwiningMap.isIntertwining, (hωτ.toRepresentation A) z hz a,
      map_smul]
  obtain ⟨s, hs⟩ := exists_lift_of_isSupercuspidal hπ hsc hωπ
    (isSmooth_toRepresentation (isSmooth_parabolicInd τ) A) (hωτ.toRepresentation A) p hp
    (Representation.IntertwiningMap.id π)
  let Φ := (subrepIncl A).comp s
  have hJ := hsc β hβ
  have h0 : frobeniusParabolic F n β τ hπ Φ = 0 :=
    Representation.IntertwiningMap.ext (LinearMap.ext fun x => by
      rw [Subsingleton.elim x 0, map_zero]
      rfl)
  have hΦ : Φ = 0 := (frobeniusParabolic F n β τ hπ).injective (h0.trans (map_zero _).symm)
  have h1 : p (s u₀) = u₀ := congrArg (fun φ : Representation.IntertwiningMap π π => φ u₀) hs
  have h2 : s u₀ = 0 := Subtype.ext (congrArg (fun φ : Representation.IntertwiningMap π
    (parabolicInd F n β τ) => φ u₀) hΦ)
  rw [h2, map_zero] at h1
  exact hu₀ h1.symm

theorem not_surjective_of_isIrreducible [π.IsIrreducible] (hπ : IsSmooth π)
    (hsc : IsSupercuspidal π) {β : Fin n → ℕ} (hβ : ∃ i j, β i ≠ β j) {W : Type*}
    [AddCommGroup W] [Module ℂ W] {τ : Representation ℂ (levi F n β) W} [τ.IsIrreducible]
    (hτ : IsSmooth τ) (A : Subrepresentation (parabolicInd F n β τ))
    (p : Representation.IntertwiningMap A.toRepresentation π) : ¬ Surjective p := by
  classical
  have hc : ∀ z (hz : z ∈ Subgroup.center (GL (Fin n) F)), ∃ c : ℂ, ∀ w,
      τ ⟨z, center_le_levi β hz⟩ w = c • w := fun z hz =>
    exists_central_character hτ (Subgroup.mem_center_iff.2 fun m =>
      Subtype.ext (Subgroup.mem_center_iff.1 hz m))
  let ω : GL (Fin n) F → ℂ := fun z =>
    if hz : z ∈ Subgroup.center (GL (Fin n) F) then (hc z hz).choose else 0
  have hωτ : ∀ z (hz : z ∈ Subgroup.center (GL (Fin n) F)), ∀ w,
      τ ⟨z, center_le_levi β hz⟩ w = ω z • w := fun z hz w => by
    simp only [ω, dif_pos hz]
    exact (hc z hz).choose_spec w
  exact not_surjective_of_le_parabolicInd hπ hsc hβ (hasCentralChar_parabolicInd hωτ) A p

end Parabolic

end GroundTheory.Automorphic
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalMultiplicityProductZero

section

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

namespace GlobalTheory.CompanionTheory.CuspNotInd

open GroundTheory.Automorphic.Parabolic (levi parabolicInd)
open GroundTheory.Automorphic.Iwasawa (blockUpper)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem unipotentRadical_ne_bot {n : ℕ} {γ : Fin n → ℕ} (hγ : ∃ i j, γ i ≠ γ j) :
    GroundTheory.Automorphic.Parabolic.unipotentRadical k n γ ≠ ⊥ := by
  have h : ∃ i j, γ i < γ j := by
    obtain ⟨i, j, hij⟩ := hγ
    rcases lt_or_gt_of_ne hij with h | h
    · exact ⟨i, j, h⟩
    · exact ⟨j, i, h⟩
  obtain ⟨i, j, hij⟩ := h
  have hne : i ≠ j := fun e => hij.ne (congrArg γ e)
  let g : GL (Fin n) k := Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.transvection i j 1)
    (by rw [Matrix.det_transvection_of_ne _ _ hne]; exact one_ne_zero)
  have hg : ∀ a b, (g : Matrix (Fin n) (Fin n) k) a b = (1 : Matrix (Fin n) (Fin n) k) a b +
      Matrix.single i j (1 : k) a b := fun a b => rfl
  intro hbot
  have hmem : g ∈ GroundTheory.Automorphic.Parabolic.unipotentRadical k n γ := by
    rw [GroundTheory.Automorphic.Parabolic.mem_unipotentRadical, GroundTheory.Automorphic.Iwasawa.mem_blockUpper]
    refine ⟨fun a b hab => ?_, fun a b hab => ?_⟩
    · rw [hg, Matrix.one_apply_ne (fun e => hab.ne (by rw [e])), Matrix.single_apply_of_ne, add_zero]
      rintro ⟨rfl, rfl⟩
      exact absurd hab hij.not_gt
    · rw [hg, Matrix.single_apply_of_ne, add_zero]
      rintro ⟨rfl, rfl⟩
      exact hij.ne hab
  rw [hbot, Subgroup.mem_bot] at hmem
  have h3 := congrArg (fun g : GL (Fin n) k => (g : Matrix (Fin n) (Fin n) k) i j) hmem
  simp only [hg, Matrix.one_apply_ne hne, Matrix.single_apply_same, zero_add, Units.val_one] at h3
  exact one_ne_zero h3

theorem isSupercuspidal_of_isCuspidal {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin n) k) V} (h : IsCuspidal π) :
    GroundTheory.Automorphic.Parabolic.IsSupercuspidal π := by
  intro γ hγ
  classical
  let s : ℕ := Finset.univ.sup γ + 1
  let r : Fin n → Fin s := fun i => ⟨γ i, Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ i))⟩
  let d : Fin s → ℕ := fun a => Fintype.card {i // r i = a}
  let e : (Σ a, Fin (d a)) ≃ Fin n :=
    (Equiv.sigmaCongrRight fun a => (Fintype.equivFin {i // r i = a}).symm).trans (Equiv.sigmaFiberEquiv r)
  have hblk : ∀ i, GlobalTheory.SmGL.blk e i = r i := fun i => by
    show (e.symm i).1 = r i
    rfl
  have hβ : ∀ i j, γ i < γ j ↔ GlobalTheory.SmGL.blk e i < GlobalTheory.SmGL.blk e j := fun i j => by
    rw [hblk, hblk]; exact Iff.rfl
  have hN : ∀ g, g ∈ GroundTheory.Automorphic.Parabolic.unipotentRadical k n γ ↔ g ∈ unipRad k e :=
    GlobalTheory.CompanionTheory.JacquetBridge.mem_unipotentRadical_iff e hβ
  have hne : unipRad k e ≠ ⊥ := fun hb => unipotentRadical_ne_bot (k := k) hγ
    (by rw [eq_bot_iff]; intro g hg; rw [← hb]; exact (hN g).1 hg)
  have htop := Submodule.Quotient.subsingleton_iff.1 (h.2 s d e hne)
  let ρ' := π.comp (GroundTheory.Automorphic.Parabolic.unipotentRadical k n γ).subtype
  have hle : twKer π (unipRad k e) 1 ≤ LinearMap.ker (Representation.Coinvariants.mk ρ') := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, v, rfl⟩
    have : Representation.Coinvariants.mk ρ' (ρ' ⟨u, (hN _).2 u.2⟩ v) = Representation.Coinvariants.mk ρ' v :=
      Representation.Coinvariants.mk_self_apply _ _ _
    simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, MonoidHom.one_apply, Units.val_one, one_smul]
    exact sub_eq_zero.2 this
  have hz : ∀ y : Representation.Coinvariants ρ', y = 0 := fun y => by
    obtain ⟨v, rfl⟩ := Representation.Coinvariants.mk_surjective ρ' y
    exact hle (htop ▸ Submodule.mem_top)
  exact ⟨fun a b => (hz a).trans (hz b).symm⟩

theorem isSubquotient_carry {r : ℕ} {d : Fin r → ℕ} {W V : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup V]
    [Module ℂ V] {π : Representation ℂ (GL (Fin (∑ a, d a)) k) V}
    (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W) (e : (Σ a, Fin (d a)) ≃ Fin (∑ a, d a))
    (he : e = GlobalTheory.CompanionTheory.BZInd.stdE d) (h : IsSubquotient π (parInd e ρ)) :
    IsSubquotient π (parabolicInd k (∑ a, d a) (GlobalTheory.CompanionTheory.BZInd.pos d) (GlobalTheory.CompanionTheory.BZInd.carry ρ)) := by
  subst he
  exact h.trans (.of_injective _ (GlobalTheory.CompanionTheory.BZInd.toIndMap_injective ρ))

theorem isIrreducible_carry {r : ℕ} {d : Fin r → ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W) (h : ρ.IsIrreducible) :
    (GlobalTheory.CompanionTheory.BZInd.carry ρ).IsIrreducible :=
  isIrreducible_twist (GlobalTheory.LocCompSplit.isIrreducible_comp_of_surjective ρ _ GlobalTheory.CompanionTheory.BZInd.leviTo_surjective h) _

theorem isSmooth_carry {r : ℕ} {d : Fin r → ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W) (h : IsSmooth ρ) :
    IsSmooth (GlobalTheory.CompanionTheory.BZInd.carry ρ) :=
  isSmooth_twist (isSmooth_comp h _ GlobalTheory.CompanionTheory.BZInd.continuous_leviTo) GlobalTheory.CompanionTheory.BZInd.isSmoothChar_adj

theorem exists_pos_ne {r : ℕ} {d : Fin r → ℕ} (h2 : 2 ≤ r) (hd : ∀ a, 0 < d a) :
    ∃ i j, GlobalTheory.CompanionTheory.BZInd.pos d i ≠ GlobalTheory.CompanionTheory.BZInd.pos d j := by
  let a : Fin r := ⟨0, by omega⟩
  let b : Fin r := ⟨1, by omega⟩
  refine ⟨GlobalTheory.CompanionTheory.BZInd.stdE d ⟨a, ⟨0, hd a⟩⟩, GlobalTheory.CompanionTheory.BZInd.stdE d ⟨b, ⟨0, hd b⟩⟩, ?_⟩
  rw [GlobalTheory.CompanionTheory.BZInd.pos_stdE, GlobalTheory.CompanionTheory.BZInd.pos_stdE]
  simp [a, b]

theorem jhMult_eq_zero_of_isCusp : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → ∀ (ρ : IrrGL (k := k)) {h : ℕ}
    (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = ρ.1), ρ.IsCusp → 2 ≤ h → (∀ a, 0 < (x a).1) →
    jhMult ρ.rep (prodIrr x hd) = 0 := by
  intro k _ _ _ _ hA ρ h x hd hc h2 hpos
  obtain ⟨N, c⟩ := ρ
  dsimp only at hd
  subst hd
  by_contra hne
  have hsub := jhMult_ne_zero_iff.1 hne
  let ρ₀ : IrrGL (k := k) := ⟨_, c⟩
  have hs2 := isSubquotient_carry (d := fun a => (x a).1) (piTensor fun a => (x a).rep) _
    (Equiv.ext fun y => by simp [stdBlocks, GlobalTheory.CompanionTheory.BZInd.stdE]) hsub
  obtain ⟨A, p, hp⟩ := hs2
  haveI : ρ₀.rep.IsIrreducible := ρ₀.2.rep.irr
  haveI := isIrreducible_carry (d := fun a => (x a).1) _ (GlobalTheory.CompanionTheory.FrobJm.piTensor_rep_isIrreducible hA x)
  exact GroundTheory.Automorphic.Parabolic.not_surjective_of_isIrreducible (π := ρ₀.rep) ρ₀.2.rep.smooth
    (isSupercuspidal_of_isCuspidal hc.2) (exists_pos_ne h2 hpos)
    (isSmooth_carry _ (isSmooth_piTensor fun a => (x a).2.rep.smooth)) A p hp

end GlobalTheory.CompanionTheory.CuspNotInd

end
end
end
