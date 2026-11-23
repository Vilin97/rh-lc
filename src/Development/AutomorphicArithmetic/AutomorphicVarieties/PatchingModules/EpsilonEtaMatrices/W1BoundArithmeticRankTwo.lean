module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.IsDualPair
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.Inertia
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.AdExExt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.DdSumZero
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.FinAm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.GaloisLiftMemFirstOrderDeformations
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.CommutingMatrixOffdiagZero
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.EpsilonEtaTensorDual
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.CCount
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.LcOfOpen
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.PolZCases
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.Descend
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.ExistsNcardAnnihilatedCocyclesLeCoboundariesMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.FinTwLc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.TwistedCocycleApplyOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.SecondSelmerSpanBoundAtAllLevels
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.ConjugateSelfDual.Statement
import ReciprocityTheory.GaloisValuations.GlobalA
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.EntryZero
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.FinrankCentralizerW1Le
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.OneLevel
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.Rho1MapReductionLevel
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.TwistedCocycleApplyOne
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.DualN

section

@[expose] public section

open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa


theorem UpperTheory.V.Pa.dualN :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (n : ℕ) (x : NP G0.frame n) (k : Kap x), l ≠ 2 → PhiCond G0.Γ l → (∀ g : G0.G₀, (g : G0.Γ) ∈ PL l T.H.toSubgroup → x.ρ g = 1) → Detects k (Set.range T.sg) → ∃ C : ℕ, ∀ m, ∀ᶠ N in atTop, ∀ rep' : Representation x.A (T.GN N).Γ (k.EpsilonEtaTensorDual (x.Am m)), IsAd (T.GN N).frame (fun g => k.ρ1 (x.Am m) ((T.h N).p₀ g)) (fun g => epsD k (x.Am m) ((T.h N).p g)) (k.EpsilonEtaTensorDual (x.Am m)) rep' → Finite (Zl rep') → {y | y ∈ Zl rep' ∧ ∀ j, ∃ Y, y (T.ph N j) = rep' (T.ph N j) Y - Y ∧ y (T.ta N j) = rep' (T.ta N j) Y - Y}.ncard ≤ Nat.card (Bl rep') * Nat.card x.K ^ C := by
  intro l _ L G0 T n x k hl hphi hρ hdet
  obtain ⟨C, hC⟩ := exists_ncard_annihilated_cocycles_le_coboundaries_mul l L G0 n x k T.q T.sg hphi T.sg_mem hdet
  refine ⟨C, fun m => ?_⟩
  filter_upwards [phEq l L G0 T n x k m hphi hρ] with N hN
  intro rep' hAd hfin
  classical
  have hfinM := finAm l G0.frame n x m k.g
  haveI : Finite (DD (x.Am m) k.g) := hfinM.2.2.1
  haveI : Finite (Matrix (Fin n) (Fin n) (DD (x.Am m) k.g)) :=
    inferInstanceAs (Finite (Fin n → Fin n → DD (x.Am m) k.g))
  haveI : Finite ↥(k.EpsilonEtaTensorDual (x.Am m)) :=
    Finite.of_injective (fun Y : ↥(k.EpsilonEtaTensorDual (x.Am m)) => (Y : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g)))
      Subtype.val_injective
  haveI := hfin
  have hrho1 := rho1 l G0.frame n x k (x.Am m)
  have hp0ta : ∀ j, (T.h N).p₀ (T.ta N j) = 1 := fun j =>
    Subtype.ext (by rw [Glob.Hom.coe_p₀, T.ta_ker]; rfl)
  have hta : ∀ j (Y : ↥(k.EpsilonEtaTensorDual (x.Am m))), rep' (T.ta N j) Y = Y := by
    intro j Y
    apply Subtype.ext
    rw [hAd.1]
    simp [map_inv, hp0ta, hrho1.1, T.ta_ker, epsD]
  have hZl : ∀ y, y ∈ Zl rep' ↔ IsLocallyConstant y ∧ ∀ g h, y (g * h) = y g + rep' g (y h) :=
    fun y => Iff.rfl
  let Z : AddSubgroup ((T.GN N).Γ → ↥(k.EpsilonEtaTensorDual (x.Am m))) :=
    { carrier := {y | y ∈ Zl rep' ∧ ∀ j, ∃ Y, y (T.ph N j) = rep' (T.ph N j) Y - Y ∧
        y (T.ta N j) = rep' (T.ta N j) Y - Y}
      add_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨add_mem ha hb, fun j => ?_⟩
        obtain ⟨Y1, h1, h2⟩ := ha' j
        obtain ⟨Y2, h3, h4⟩ := hb' j
        refine ⟨Y1 + Y2, ?_, ?_⟩ <;> simp only [Pi.add_apply, h1, h2, h3, h4, map_add (f := _)] <;> abel
      zero_mem' := ⟨zero_mem _, fun j => ⟨0, by simp, by simp⟩⟩
      neg_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨neg_mem ha, fun j => ?_⟩
        obtain ⟨Y, h1, h2⟩ := ha' j
        refine ⟨-Y, ?_, ?_⟩ <;> simp only [Pi.neg_apply, h1, h2, map_neg] <;> abel }
  haveI hZfin : Finite Z := Finite.of_injective (fun z : Z => (⟨z.1, z.2.1⟩ : Zl rep'))
    (fun a b h => Subtype.ext (by simpa using congrArg Subtype.val h))
  have hZlf : (Zl rep' : Set ((T.GN N).Γ → ↥(k.EpsilonEtaTensorDual (x.Am m)))).Finite := Set.toFinite _
  have hLC := lc1 l L (T.GN N) G0 (T.h N) n x k m
  have hLCr := hLC.2.2 _ _ rep' hLC.2.1 hAd
  have hBlZ : (Bl rep').toAddSubgroup ≤ Z := by
    intro y hy
    obtain ⟨Y, hY⟩ := (mem_Bl rep').1 hy
    refine ⟨(hZl y).2 ⟨?_, ?_⟩, fun j => ⟨Y, hY _, hY _⟩⟩
    · have hy' : y = fun g => rep' g Y - Y := funext hY
      rw [hy']
      exact (hLCr Y).sub (IsLocallyConstant.const _)
    · intro g h
      rw [hY, hY, hY, map_mul, Module.End.mul_apply, map_sub]
      abel
  have hcoc : ∀ z ∈ Z, ∀ g h, z (g * h) = z g + rep' g (z h) := fun z hz => ((hZl z).1 hz.1).2
  obtain ⟨hA, hB, hCc⟩ := cCount x.A (T.GN N).Γ ↥(k.EpsilonEtaTensorDual (x.Am m)) rep' (T.GN N).c (T.GN N).c_sq
    (hfinM.2.2.2.2.2.2.2.1 hl)
  have hA' := hA Z hZfin hBlZ hcoc
  let s := Function.surjInv (T.h N).p₀_surj
  have hs : ∀ g0, (T.h N).p₀ (s g0) = g0 := Function.surjInv_eq _
  let Ψ : ((T.GN N).Γ → ↥(k.EpsilonEtaTensorDual (x.Am m))) → (G0.frame.G₀ → Matrix (Fin n) (Fin n) (DD (x.Am m) k.g)) :=
    fun y g0 => ((y (s g0 : (T.GN N).Γ)) : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g))
  have hdesc : ∀ y ∈ Z, y (T.GN N).c = 0 → Ψ y ∈ TwZ k (x.Am m) ∧
      ∀ g : (T.GN N).G₀, ((y g : ↥(k.EpsilonEtaTensorDual (x.Am m))) : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g)) =
        Ψ y ((T.h N).p₀ g) := by
    intro y hy hc
    obtain ⟨z, hz, hyz⟩ := descend l L G0 T n x k m N rep' hρ hAd y hy.1 hc (fun j => by
      obtain ⟨Y, -, h2⟩ := hy.2 j
      rw [h2, hta, sub_self])
    have hΨ : Ψ y = z := funext fun g0 => by
      simp only [Ψ]
      rw [hyz, hs]
    rw [hΨ]
    exact ⟨hz, hyz⟩
  have hmaps : ∀ y ∈ {z | z ∈ Z ∧ z (T.GN N).c = 0},
      Ψ y ∈ {z | z ∈ TwZ k (x.Am m) ∧ ∀ j, ell k (x.Am m) (T.sg j) z = 0} := by
    rintro y ⟨hy, hc⟩
    obtain ⟨hz, hyz⟩ := hdesc y hy hc
    refine ⟨hz, fun j => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hN j
    obtain ⟨Y, hY, -⟩ := hy.2 j
    have hval : Ψ y (T.sg j) = k.ρ1 (x.Am m) ((T.h N).p₀ (T.ph N j)) * (Y : Matrix (Fin n) (Fin n) _) *
        k.ρ1 (x.Am m) ((T.h N).p₀ (T.ph N j)⁻¹) - (Y : Matrix (Fin n) (Fin n) _) := by
      rw [← h3 _ hz, ← hyz, hY, Submodule.coe_sub, hAd.1]
      simp only [h2, one_smul]
    have hinv : k.ρ1 (x.Am m) ((T.h N).p₀ (T.ph N j)⁻¹) * k.ρ1 (x.Am m) (T.sg j) = 1 := by
      rw [← h1, ← hrho1.2.1, map_inv, inv_mul_cancel, hrho1.1]
    have key : (Ψ y (T.sg j) * k.ρ1 (x.Am m) (T.sg j)).trace = 0 := by
      rw [hval, Matrix.sub_mul, Matrix.mul_assoc (k.ρ1 (x.Am m) ((T.h N).p₀ (T.ph N j)) * _), hinv,
        Matrix.mul_one, ← h1, Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]
    show (Ψ y (T.sg j) * k.ρ1 (x.Am m) (T.sg j)).trace.eta = 0
    rw [key]
    rfl
  have hinj : Set.InjOn Ψ {z | z ∈ Z ∧ z (T.GN N).c = 0} := by
    rintro y1 ⟨hy1, hc1⟩ y2 ⟨hy2, hc2⟩ heq
    obtain ⟨-, e1⟩ := hdesc y1 hy1 hc1
    obtain ⟨-, e2⟩ := hdesc y2 hy2 hc2
    have hpol := (polZ l (T.GN N).frame x.A (DD (x.Am m) k.g) n _ _ _ rep' hAd).2 (y1 - y2)
      (sub_mem hy1.1 hy2.1) (by
        show y1 (T.GN N).c - y2 (T.GN N).c = 0
        rw [hc1, hc2, sub_self])
    exact sub_eq_zero.1 (hpol.2 fun g => by
      rw [Pi.sub_apply, sub_eq_zero]
      exact Subtype.ext (by rw [e1, e2, heq]))
  have hSmf : {z | z ∈ TwZ k (x.Am m) ∧ ∀ j, ell k (x.Am m) (T.sg j) z = 0}.Finite :=
    (finTw l L G0 n x k m hphi).subset fun z hz => hz.1
  have hBcf : {z | z ∈ Bl rep' ∧ z (T.GN N).c = 0}.Finite :=
    hZlf.subset fun z hz => (hBlZ ((Submodule.mem_toAddSubgroup _).2 hz.1)).1
  have h1 := Set.ncard_le_ncard_of_injOn Ψ hmaps hinj hSmf
  have h2 := hC m
  have h3 : (TwB k (x.Am m)).ncard ≤ {z | z ∈ Bl rep' ∧ z (T.GN N).c = 0}.ncard := by
    have hsub : TwB k (x.Am m) ⊆ Ψ '' {z | z ∈ Bl rep' ∧ z (T.GN N).c = 0} := by
      rintro z ⟨Y, hYm, hYc, rfl⟩
      let Y' : ↥(k.EpsilonEtaTensorDual (x.Am m)) := ⟨Y, hYm⟩
      have hrepc : rep' (T.GN N).c Y' = Y' := Subtype.ext ((hAd.2 Y').trans (by
        show -(epsD k (x.Am m) ((T.h N).p (T.GN N).c) • Yᵀ) = Y
        rw [Glob.Hom.c]
        exact hYc))
      refine ⟨fun g => rep' g Y' - Y', ⟨(mem_Bl rep').2 ⟨Y', fun g => rfl⟩, by simp only [hrepc, sub_self]⟩, ?_⟩
      funext g0
      simp only [Ψ]
      rw [Submodule.coe_sub, hAd.1]
      simp only [map_inv, ← Glob.Hom.coe_p₀, hs]
      rfl
    calc (TwB k (x.Am m)).ncard ≤ (Ψ '' {z | z ∈ Bl rep' ∧ z (T.GN N).c = 0}).ncard :=
          Set.ncard_le_ncard hsub (hBcf.image _)
      _ ≤ _ := Set.ncard_image_le hBcf
  have hzc := h1.trans (h2.trans (Nat.mul_le_mul_right _ h3))
  have hi : 0 < Nat.card rep'.invariants := Nat.card_pos
  have hbc : 0 < {z | z ∈ Bl rep' ∧ z (T.GN N).c = 0}.ncard :=
    (Set.ncard_pos hBcf).2 ⟨0, Submodule.zero_mem _, rfl⟩
  have e : Nat.card Z * {z | z ∈ Bl rep' ∧ z (T.GN N).c = 0}.ncard =
      {z | z ∈ Z ∧ z (T.GN N).c = 0}.ncard * Nat.card (Bl rep') := by
    apply Nat.eq_of_mul_eq_mul_right hi
    rw [mul_assoc, hCc, hA', ← hB, mul_assoc]
  have hle : Nat.card Z * {z | z ∈ Bl rep' ∧ z (T.GN N).c = 0}.ncard ≤
      Nat.card (Bl rep') * Nat.card x.K ^ C * {z | z ∈ Bl rep' ∧ z (T.GN N).c = 0}.ncard := by
    rw [e]
    calc _ ≤ {z | z ∈ Bl rep' ∧ z (T.GN N).c = 0}.ncard * Nat.card x.K ^ C * Nat.card (Bl rep') :=
          Nat.mul_le_mul_right _ hzc
      _ = _ := by ring
  rw [← Nat.card_coe_set_eq]
  exact Nat.le_of_mul_le_mul_right hle hbc
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.W1BoundArithmeticRankTwo

section

@[expose] public section

open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem card_inv_le {A R Γ : Type} [CommRing A] [CommRing R] [Algebra A R] [Finite R] [Group Γ] {n : ℕ}
    {V : Submodule A (Matrix (Fin n) (Fin n) R)} (r : Representation A Γ V) (S : Set (Matrix (Fin n) (Fin n) R))
    (h : ∀ y : V, (∀ g, r g y = y) → (y : Matrix (Fin n) (Fin n) R) ∈ S) : Nat.card r.invariants ≤ S.ncard := by
  rw [← Nat.card_coe_set_eq]
  refine Nat.card_le_card_of_injective
    (fun y : r.invariants => (⟨((y : V) : Matrix (Fin n) (Fin n) R),
      h (y : V) ((Representation.mem_invariants r _).1 y.2)⟩ : S)) ?_
  intro a b hab
  have e := congrArg Subtype.val hab
  exact Subtype.ext (Subtype.ext e)

private theorem cancel_pow {s b K u w : ℕ} (hK : 0 < K) (h : s * K ^ u ≤ b * K ^ (w + u)) : s ≤ b * K ^ w := by
  rw [pow_add, ← mul_assoc] at h
  exact Nat.le_of_mul_le_mul_right h (pow_pos hK u)

private theorem sum_exp {V : Type} [Fintype V] (m n ν d q c₁ c₂ c₀ : ℕ) (d' dv C : V → ℕ) (Cq : Fin q → ℕ)
    (h1 : ∑ v, d' v = d) (h2 : ∑ v, dv v = d) :
    c₁ + c₂ + ∑ v, (m * (n * (d' v + 1) + ν * (1 + dv v)) + C v) +
      ∑ j : Option (Fin q), (j.elim c₀ fun i => m * n + Cq i) =
    (m * (n * d + n * q) + (c₁ + c₂ + c₀ + ∑ v, C v + ∑ j, Cq j)) + (m * (n + ν) * Fintype.card V + m * ν * d) := by
  rw [Fintype.sum_option]
  simp only [Option.elim, mul_add, add_mul, mul_one, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, smul_eq_mul, Fintype.card_fin, h1, h2]
  ring

theorem UpperTheory.V.Pa.W1_bound_arithmetic_rank_two :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (n : ℕ) (x : NP G0.frame n) (k : Kap x) (al : Fin T.q → Fin n → x.A) (d : ℕ) (D0 : Subgroup G0.G₀) (_ : ArSys T d D0) (d' : L.Vl → ℕ), l ≠ 2 → ∑ v, d' v = d → (∀ v, Nonempty (LocAb l (L.Gv v) (L.Iv v) (d' v))) → PhiCond G0.Γ l → (∀ g : G0.G₀, (g : G0.Γ) ∈ PL l T.H.toSubgroup → x.ρ g = 1) → x.N4 D0 → T.Eig x al → Detects k (Set.range T.sg) → T.B1 k (n * d + n * T.q) := by
  intro l _ L G0 T n x k al d D0 A d' hl hd' hLoc hphi hPL hN4 hEig hDet
  obtain ⟨c₁, hc₁⟩ := h0G l L G0 G0 (Glob.Hom.refl G0) n x k hl
  obtain ⟨c₂, hc₂⟩ := dualN l L G0 T n x k hl hphi hPL hDet
  obtain ⟨c₀, hc₀⟩ := h0v0 l G0.frame n x k D0 hN4
  have hq := fun j => h0q l G0.frame n x k (T.sg j) (al j) (hEig j).1 (hEig j).2
  choose Cq hCq using hq
  have hv : ∀ v, ∃ C, ∀ m, Finite (k.Zb (x.Am m) v) ∧ Nat.card (k.Zb (x.Am m) v) ≤
      Nat.card x.K ^ (m * (n * (d' v + 1) + nu n x.a k.g * (1 + A.dv v)) + C) := by
    intro v
    refine locV l G0.frame n x k v (A.dv v) (d' v) ?_ (hLoc v).some
    have h0 := (A.counts 0).locV v
    rw [A.dv_eq 0] at h0
    convert h0 using 2
    refine MonoidHom.ext fun g => ?_
    show G0.ε (G0.φ v g : G0.Γ) = (T.GN 0).ε ((T.GN 0).φ v g : (T.GN 0).Γ)
    rw [← (T.h 0).ε]
    exact congrArg G0.ε ((T.h 0).φ v g).symm
  choose Cv hCv using hv
  refine ⟨c₁ + c₂ + c₀ + ∑ v, Cv v + ∑ j, Cq j, fun m => ?_⟩
  filter_upwards [hc₂ m, phEq l L G0 T n x k m hphi hPL] with N hN2 hNph
  have r1 := rho1 l G0.frame n x k (x.Am m)
  have inv_eq : ∀ g σ : G0.G₀, k.ρ1 (x.Am m) g = k.ρ1 (x.Am m) σ →
      k.ρ1 (x.Am m) g⁻¹ = k.ρ1 (x.Am m) σ⁻¹ := by
    intro g σ e
    calc k.ρ1 (x.Am m) g⁻¹ = k.ρ1 (x.Am m) g⁻¹ * k.ρ1 (x.Am m) (σ * σ⁻¹) := by
          rw [mul_inv_cancel, r1.1, mul_one]
      _ = k.ρ1 (x.Am m) (g⁻¹ * g) * k.ρ1 (x.Am m) σ⁻¹ := by
          rw [r1.2.1, r1.2.1, e, mul_assoc]
      _ = k.ρ1 (x.Am m) σ⁻¹ := by
          rw [inv_mul_cancel, r1.1, one_mul]
  have hok1 := (ok1 l L (T.GN N) G0 (T.h N) n x k (x.Am m) 1).1
  simp only [MonoidHom.one_apply, map_one] at hok1
  obtain ⟨rep, hrep⟩ := adEx l (T.GN N).frame x.A (DD (x.Am m) k.g) n
    (fun g => k.ρ1 (x.Am m) ((T.h N).p₀ g)) (fun _ => 1) (k.M1 (x.Am m)) hok1
  let χ' : (T.GN N).Γ →* x.A := (algebraMap ℤ_[l] x.A : ℤ_[l] →* x.A).comp
    ((Units.coeHom ℤ_[l]).comp (G0.ε.comp (T.h N).p))
  obtain ⟨rep', hrep'⟩ := adEx l (T.GN N).frame x.A (DD (x.Am m) k.g) n
    (fun g => k.ρ1 (x.Am m) ((T.h N).p₀ g)) (fun g => epsD k (x.Am m) ((T.h N).p g)) (k.EpsilonEtaTensorDual (x.Am m))
    (ok1 l L (T.GN N) G0 (T.h N) n x k (x.Am m) χ').2.1
  have hKpos : 0 < Nat.card x.K := by
    haveI := x.fin
    exact Nat.card_pos
  haveI : Finite (DD (x.Am m) k.g) := (finAm l G0.frame n x m k.g).2.2.1
  have hsum : ∑ v, A.dv v = d := by
    rw [← A.dv_eq N]
    exact (A.a N).sum_dv
  have hsurj0 : ∀ g : G0.G₀, ∃ g' : (T.GN N).G₀, (T.h N).p₀ g' = g := by
    intro g
    obtain ⟨y, hy⟩ := (T.h N).surj (g : G0.Γ)
    have hy1 : y ∈ (T.GN N).η.ker := by
      rw [MonoidHom.mem_ker, ← (T.h N).η, hy]
      exact g.2
    exact ⟨⟨y, hy1⟩, Subtype.ext hy⟩
  have hinv : ∀ j : Option (Fin T.q),
      Nat.card (Representation.invariants (rep'.comp ((A.a N).ι (Sum.inr (Sum.inr j))))) ≤
        Nat.card x.K ^ (j.elim c₀ fun i => m * n + Cq i) := by
    intro j
    cases j with
    | none =>
      refine (card_inv_le _ {Y | Y ∈ k.EpsilonEtaTensorDual (x.Am m) ∧ ∀ g ∈ D0, epsD k (x.Am m) ↑g •
        (k.ρ1 (x.Am m) g * Y * k.ρ1 (x.Am m) g⁻¹) = Y} ?_).trans (hc₀ m)
      intro y hy
      refine ⟨y.2, fun g hg => ?_⟩
      rw [← A.d0 N] at hg
      obtain ⟨t, rfl⟩ := hg
      have hy' : rep' ((A.a N).φq none t : (T.GN N).Γ) y = y := hy t
      have e := hrep'.1 ((A.a N).φq none t) y
      rw [hy'] at e
      beta_reduce at e
      rw [map_inv] at e
      rw [MonoidHom.comp_apply]
      exact e.symm
    | some i =>
      refine (card_inv_le _ {Y | Y ∈ k.EpsilonEtaTensorDual (x.Am m) ∧
        k.ρ1 (x.Am m) (T.sg i) * Y * k.ρ1 (x.Am m) (T.sg i)⁻¹ = Y} ?_).trans (hCq i m)
      intro y hy
      refine ⟨y.2, ?_⟩
      obtain ⟨t, ht⟩ := A.ph N i
      have hy' : rep' ((A.a N).φq (some i) t : (T.GN N).Γ) y = y := hy t
      rw [ht] at hy'
      have e := hrep'.1 (T.ph N i) y
      rw [hy'] at e
      beta_reduce at e
      rw [map_inv, inv_eq _ _ (hNph i).1, (hNph i).1, (hNph i).2.1, one_smul] at e
      exact e.symm
  have h0inv : Nat.card rep.invariants ≤ Nat.card x.K ^ c₁ := by
    refine (card_inv_le rep {Y | Y ∈ k.M1 (x.Am m) ∧ Yᵀ = -Y ∧
      ∀ g : G0.G₀, k.ρ1 (x.Am m) g * Y * k.ρ1 (x.Am m) g⁻¹ = Y} ?_).trans (hc₁ m)
    intro y hy
    refine ⟨y.2, ?_, fun g => ?_⟩
    · have e := hrep.2 y
      rw [hy, one_smul] at e
      have e2 := congrArg Matrix.transpose e
      rw [Matrix.transpose_neg, Matrix.transpose_transpose] at e2
      exact e2
    · obtain ⟨g', rfl⟩ := hsurj0 g
      have e := hrep.1 g' y
      rw [hy] at e
      beta_reduce at e
      rw [one_smul, map_inv] at e
      exact e.symm
  have hdual : Finite (Zl rep') → {y | y ∈ Zl rep' ∧ ∀ j : Fin T.q,
      y ∘ ((A.a N).ι (Sum.inr (Sum.inr (some j)))) ∈
        Bl (rep'.comp ((A.a N).ι (Sum.inr (Sum.inr (some j)))))}.ncard ≤
      Nat.card (Bl rep') * Nat.card x.K ^ c₂ := by
    intro hfinZ
    refine le_trans (Set.ncard_le_ncard ?_ ?_) (hN2 rep' hrep' hfinZ)
    · intro y hy
      refine ⟨hy.1, fun j => ?_⟩
      obtain ⟨Y, hY⟩ := (mem_Bl _).1 (hy.2 j)
      obtain ⟨t1, ht1⟩ := A.ph N j
      obtain ⟨t2, ht2⟩ := A.ta N j
      refine ⟨Y, ?_, ?_⟩
      · rw [← ht1]
        exact hY t1
      · rw [← ht2]
        exact hY t2
    · exact (Set.toFinite (Zl rep' : Set _)).subset (fun y hy => hy.1)
  obtain ⟨hfin, hle⟩ := oneLevel l L (T.GN N) G0 (T.h N) n x k m T.q d (A.a N) rep rep'
    (fun v => m * (n * (d' v + 1) + nu n x.a k.g * (1 + A.dv v)) + Cv v)
    (fun j => j.elim c₀ fun i => m * n + Cq i) c₁ c₂ hl (A.counts N) hrep hrep'
    (fun v => hCv v m) hinv h0inv hdual
  rw [sum_exp m n (nu n x.a k.g) d T.q c₁ c₂ c₀ d' A.dv Cv Cq hd' hsum] at hle
  exact ⟨hfin, cancel_pow hKpos hle⟩
end
end
